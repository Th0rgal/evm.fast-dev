import InitECandidate.Solver.Wave8GuestInv.ContractParts.C07
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M05.WorldLemmas
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M08.wk_memcpy
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M08.wk_memzero
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M11.RlpMemcpyLemmas
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.Exec
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M26.rt_lst_new
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M26.rt_msg_new
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M19.htab_del_spec

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.Fast_C08WkShard04

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## Shared World-Step & Allocator Helpers -/

theorem not_resumes_error : ¬ Resumes (some (.error : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

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
  rw [hargs]; dsimp only; rw [hlookup]; dsimp only
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
        · injection h with h'; cases h'; exact hout.2.2 eid v hne rfl
      | «break» | «continue» | error | timeOut | finalFfi _ =>
        rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h

theorem alloc_body_resumes {F : Type}
    (state : PanSemStateFiniteExact 64 F) (p n : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (hp_lookup : state.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n))) :
    let out := evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_alloc)
    let q := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    Resumes out.1 →
      out.1 = some (.returned (.val (.word p))) ∧
      ¬ ((InitECandidate.Solver.HeapPotential.cMax - p).toNat < n.toNat) ∧
      ¬ (InitECandidate.Solver.HeapPotential.cMax.toNat < q.toNat) ∧
      out.2 = { state with
        globals := (state.globals.update (ofString "heap_ptr", .val (.word q)))
        locals := out.2.locals } := by
  dsimp only
  have hbody_eq : sourceFnBody Guest.Software.guestFn_alloc =
      .dec (ofString "p") .one (.var .global (ofString "heap_ptr"))
        (.seq
          (.ite (.cmp .lower (.op .sub [.const InitECandidate.Solver.HeapPotential.cMax, .var .local (ofString "p")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip)
          (.dec (ofString "q") .one
            (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
              .op .sub [.const 0, .const 8]])
            (.seq
              (.ite (.cmp .lower (.const InitECandidate.Solver.HeapPotential.cMax) (.var .local (ofString "q")))
                (.call (some (none, none)) (ofString "trap_with") [.const 1])
                .skip)
              (.seq
                (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "p"))))))) := rfl
  rw [hbody_eq, evaluateHOLFiniteState_dec_total]
  have hp_eval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.var .global (ofString "heap_ptr")) = some (.val (.word p)) := hp_lookup
  dsimp only; rw [hp_eval]
  have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only; rw [if_pos hsh_p]; dsimp only
  let pState := setVarHOLFinite (ofString "p") (.val (.word p)) state
  have hp_loc : pState.locals.lookup (ofString "p") = some (.val (.word p)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hn_loc : pState.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
      show ofString "p" ≠ ofString "n" by decide]
  rw [evaluateHOLFiniteState_seq_line780]
  have hev1 : @evalHOLExact 64 F _ pState.toExact
      (fun a => Classical.propDecidable (pState.memaddrs a))
      (.cmp .lower (.op .sub [.const InitECandidate.Solver.HeapPotential.cMax, .var .local (ofString "p")])
        (.var .local (ofString "n"))) =
      some (.val (.word (if (InitECandidate.Solver.HeapPotential.cMax - p).toNat < n.toNat then 1 else 0))) := by
    simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
      Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    rfl
  by_cases hcmp1 : (InitECandidate.Solver.HeapPotential.cMax - p).toNat < n.toNat
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.const InitECandidate.Solver.HeapPotential.cMax, .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 1])
          .skip) =
        evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_pos hcmp1]; simp
    rw [hite1]
    have hno_none := InitECandidate.Solver.HeapPotential.evaluate_call_trap_with_no_none pState 1 hcode
    have hno_res := evaluate_call_trap_with_not_resumes pState 1 hcode
    rcases htr : evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r1, s1⟩
    rw [htr] at hno_none hno_res
    cases r1 with
    | none => exact absurd rfl hno_none
    | some _ => intro hr; exact absurd hr hno_res
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.const InitECandidate.Solver.HeapPotential.cMax, .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 1])
          .skip) = (none, pState) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_neg hcmp1]; simp [evaluateHOLFiniteState_skip]
    rw [hite1]; dsimp only
    rw [evaluateHOLFiniteState_dec_total]
    let q : BitVec 64 := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    have hq_eval : @evalHOLExact 64 F _ pState.toExact
        (fun a => Classical.propDecidable (pState.memaddrs a))
        (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
          .op .sub [.const 0, .const 8]]) = some (.val (.word q)) := by
      simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
        wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
      exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word w)))
        (InitECandidate.Solver.HeapPotential.alloc_q_word_eq p n)
    dsimp only; rw [hq_eval]
    have hsh_q : shapeEqHOL .one (shapeOfHOLExact (.val (.word q))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    dsimp only; rw [if_pos hsh_q]; dsimp only
    let qState := setVarHOLFinite (ofString "q") (.val (.word q)) pState
    have hq_loc : qState.locals.lookup (ofString "q") = some (.val (.word q)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hp_loc_q : qState.locals.lookup (ofString "p") = some (.val (.word p)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_loc,
        show ofString "q" ≠ ofString "p" by decide]
    rw [evaluateHOLFiniteState_seq_line780]
    have hev2 : @evalHOLExact 64 F _ qState.toExact
        (fun a => Classical.propDecidable (qState.memaddrs a))
        (.cmp .lower (.const InitECandidate.Solver.HeapPotential.cMax) (.var .local (ofString "q"))) =
        some (.val (.word (if InitECandidate.Solver.HeapPotential.cMax.toNat < q.toNat then 1 else 0))) := by
      simp only [evalHOLExact, hq_loc, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    by_cases hcmp2 : InitECandidate.Solver.HeapPotential.cMax.toNat < q.toNat
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.const InitECandidate.Solver.HeapPotential.cMax) (.var .local (ofString "q")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip) =
          evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_pos hcmp2]; simp
      rw [hite2]
      have hno_none := InitECandidate.Solver.HeapPotential.evaluate_call_trap_with_no_none qState 1 hcode
      have hno_res := evaluate_call_trap_with_not_resumes qState 1 hcode
      rcases htr : evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r2, s2⟩
      rw [htr] at hno_none hno_res
      cases r2 with
      | none => exact absurd rfl hno_none
      | some _ => intro hr; exact absurd hr hno_res
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.const InitECandidate.Solver.HeapPotential.cMax) (.var .local (ofString "q")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip) = (none, qState) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_neg hcmp2]; simp [evaluateHOLFiniteState_skip]
      rw [hite2]; dsimp only
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

theorem Resumes.of_noExn {r : Option (PanSemResultExact 64)} (hr : Resumes r)
    (hno : ∀ eid ev, r ≠ some (.exception eid ev)) : ∃ v, r = some (.returned v) := by
  rcases hr with ⟨v, hv⟩ | ⟨eid, ev, hexn, _⟩
  · exact ⟨v, hv⟩
  · exact absurd hexn (hno eid ev)

theorem noExn_seq_store {F : Type} {s : PanSemStateFiniteExact 64 F} {d e : ExpHOL 64}
    {b : ProgHOL 64} {eid : MlS} {ev : ValueHOL 64}
    (hb : ∀ m : BitVec 64 → HolWordLab 64,
      (evaluateHOLFiniteState { s with memory := m } b).1 ≠ some (.exception eid ev)) :
    (evaluateHOLFiniteState s (.seq (.store d e) b)).1 ≠ some (.exception eid ev) := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store]
  split
  · split
    · split
      · exact hb _
      · simp
    · simp
  · simp

theorem noExn_return {F : Type} {s : PanSemStateFiniteExact 64 F} {e : ExpHOL 64}
    {eid : MlS} {ev : ValueHOL 64} :
    (evaluateHOLFiniteState s (.return e)).1 ≠ some (.exception eid ev) := by
  rw [evaluateHOLFiniteState_return]
  split
  · simp
  · split <;> simp

theorem noResumeExn_decCall_alloc {F : Type} {s : PanSemStateFiniteExact 64 F}
    {x : MlS} {arg : ExpHOL 64} {cont : ProgHOL 64} {eid : MlS} {ev : ValueHOL 64}
    (hcode : s.code = originalRuntimeCode) (hp : BitVec 64)
    (hhp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word hp)))
    (hne : eid ≠ ofString "TrapErr")
    (hcont : ∀ (nv q : BitVec 64) (clk : Nat),
      (evaluateHOLFiniteState
        (setVarHOLFinite x (.val (.word hp)) { s with
          globals := s.globals.update (ofString "heap_ptr", .val (.word q))
          clock := clk }) cont).1 ≠ some (.exception eid ev)) :
    (evaluateHOLFiniteState s (.decCall x .one (ofString "alloc") [arg] cont)).1 ≠ some (.exception eid ev) := by
  intro hexn
  rw [evaluateHOLFiniteState_decCall_total] at hexn
  rcases ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [arg] with _ | vals
  · rw [ha] at hexn; simp at hexn
  · rw [ha] at hexn; dsimp only at hexn
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "alloc") vals with _ | ⟨body', callee, ret'⟩
    · rw [hl] at hexn; simp at hexn
    · rw [hl] at hexn; dsimp only at hexn
      have hx := lookupCodeHOLFinite_eq_some s.code.lookup _ vals body' callee ret' hl
      rw [hcode] at hx
      simp only [lookupCodeHOLExact, lookup_alloc] at hx
      rcases vals with _ | ⟨v1, _ | _⟩ <;> try (simp at hx)
      rcases v1 with ⟨⟨nv⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hx
      rcases hx with ⟨rfl, hloc, rfl⟩
      split at hexn
      · simp at hexn
      · rw [fixClockHOLFinite_evaluateState] at hexn
        have hn : callee.lookup (ofString "n") = some (.val (.word nv)) := by
          have : callee.lookup = _ := hloc.symm
          rw [this]; simp
        have hal := alloc_body_resumes (callEntryStateHOLFinite s callee) hp nv hcode hhp hn
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
            (sourceFnBody Guest.Software.guestFn_alloc) with ⟨ar, ap⟩
        rw [hrun] at hal hexn
        cases ar with
        | none => simp at hexn
        | some ar' =>
          cases ar' with
          | returned av =>
            obtain ⟨hav, _, _, hap⟩ := hal (Or.inl ⟨av, rfl⟩)
            injection hav with hav'; injection hav' with hav''; subst hav''
            have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word hp) : ValueHOL 64)) .one &&
                shapeEqHOL (shapeOfHOLExact (.val (.word hp) : ValueHOL 64)) .one) = true := by
              simp [shapeOfHOLExact, shapeEqHOL]
            dsimp only at hexn; rw [if_pos hsh] at hexn; dsimp only at hexn
            have hst : { ap with locals := s.locals } = { s with
                globals := s.globals.update (ofString "heap_ptr", .val (.word ((hp + (nv + 7)) &&& ((0 : BitVec 64) - 8))))
                clock := s.clock - 1 } := by
              dsimp only at hap; rw [hap]; rfl
            rw [hst] at hexn
            exact hcont nv ((hp + (nv + 7)) &&& ((0 : BitVec 64) - 8)) (s.clock - 1) hexn
          | exception aeid aev =>
            dsimp only at hexn
            injection hexn with hexn'; injection hexn' with he1 he2; subst he1 he2
            have := hal (Or.inr ⟨aeid, aev, rfl, hne⟩)
            cases this.1
          | _ => simp at hexn

/-- Master W1 lemma for functions that only grow `heap_ptr` / shrink `scratch_ptr` (keeping all other
globals unchanged) and only modify memory inside `heapFree s` or `freeGap s` (and only in-domain cells). -/
theorem worldStep_of_free_writes {F : Type}
    {gw : List String}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)}
    (hWOK : WorldOK s)
    (hAp : ArenaReady post)
    (hag : AllocatorGrows s post)
    (hgw : GlobalsKept gw s post)
    (hnonheap : ∀ k : MlS, k ≠ ofString "heap_ptr" → k ≠ ofString "scratch_ptr" → k ≠ ofString "frame_mem_ptr" →
      s.globals.lookup k = post.globals.lookup k)
    (hbe : post.be = s.be)
    (hdom_wr : ∀ a : BitVec 64, post.memory a ≠ s.memory a → s.memaddrs a)
    (hfr_free : FrameOutside s post [freeGap s] (heapFree s))
    (hQ : ∀ S Nd, WorldTypedWith s S Nd → WorldTypedWith post S Nd →
      worldOwned post S Nd = worldOwned s S Nd → Q s r post S Nd) :
    WorldStep (fun _ => []) gw
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      Q s r post := by
  have hAs := hWOK.1
  have hrk : RecordsKept (fun _ => [])
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      s post :=
    InitECandidate.Solver.Wave8Contracts.M08.recordsKept_of_free_writes
      (R := fun _ => []) hWOK hfr_free
  refine ⟨hAp, hag.1, hgw, hrk, fun S Nd hWT _ => ?_⟩
  have hcell : InitECandidate.Solver.Wave8Contracts.M05.SameTypedCells s post S Nd := by
    refine ⟨hbe, hAp.1.memaddrs.trans hAs.1.memaddrs.symm, hAs.1.memaddrs, ?_, ?_, ?_⟩
    · intro a hna
      by_contra hne
      have hd := hdom_wr a hne
      rw [hAs.1.memaddrs] at hd
      exact hna hd
    · intro a ha ha8 ⟨i, hi, ha1, ha2⟩
      rcases InitECandidate.Solver.Wave8Contracts.M05.worldTypedIvls_allocated hWT hi with hi0 | hal
      · omega
      · have hdfg := InitECandidate.Solver.Wave8Contracts.M05.allocated_disj_freeGap hAs.2 hal
        have hdhf := InitECandidate.Solver.Wave8Contracts.M05.allocated_disj_heapFree hAs.2 hal
        have hbit : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
        apply hfr_free (BitVec.ofNat 64 a)
        · intro j hj
          simp only [List.mem_singleton] at hj; subst hj
          rw [hbit]
          intro ⟨hc1, hc2⟩
          rcases hdfg with h0 | h0 | h | h <;> dsimp only at * <;> omega
        · rw [hbit]
          intro ⟨hc1, hc2⟩
          rcases hdhf with h0 | h0 | h | h <;> dsimp only at * <;> omega
    · intro b hb ⟨i, hi, hb1, hb2⟩
      rcases InitECandidate.Solver.Wave8Contracts.M05.worldTypedIvls_allocated hWT hi with hi0 | hal
      · omega
      · have hdfg := InitECandidate.Solver.Wave8Contracts.M05.allocated_disj_freeGap hAs.2 hal
        have hdhf := InitECandidate.Solver.Wave8Contracts.M05.allocated_disj_heapFree hAs.2 hal
        have hal_b : (panByteAlignHOL (BitVec.ofNat 64 b)).toNat = b / 8 * 8 := by
          rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
        have hfg_al : (freeGap s).1 % 8 = 0 ∧ (freeGap s).2 % 8 = 0 := by
          unfold freeGap; have := hAs.2.2.2.2.2.2.1; have := hAs.2.2.2.2.2.2.2; dsimp only; omega
        have hhf_al : (heapFree s).1 % 8 = 0 ∧ (heapFree s).2 % 8 = 0 := by
          unfold heapFree; have := hAs.2.2.2.2.2.1; have : heapLimit % 8 = 0 := by decide
          dsimp only; omega
        have hm_eq : post.memory (panByteAlignHOL (BitVec.ofNat 64 b)) =
            s.memory (panByteAlignHOL (BitVec.ofNat 64 b)) := by
          apply hfr_free (panByteAlignHOL (BitVec.ofNat 64 b))
          · intro j hj
            simp only [List.mem_singleton] at hj; subst hj
            rw [hal_b]
            intro ⟨hc1, hc2⟩
            rcases hdfg with h0 | h0 | h | h <;> dsimp only at * <;> omega
          · rw [hal_b]
            intro ⟨hc1, hc2⟩
            rcases hdhf with h0 | h0 | h | h <;> dsimp only at * <;> omega
        unfold memB
        rw [hm_eq, hbe]
  have hg_ml : ∀ name, ofString name ≠ ofString "heap_ptr" → ofString name ≠ ofString "scratch_ptr" →
      ofString name ≠ ofString "frame_mem_ptr" → globN post name = globN s name :=
    fun n h1 h2 h3 => (InitECandidate.Solver.Wave8Contracts.M05.globN_eq_of_lookup_eq (hnonheap (ofString n) h1 h2 h3)).symm
  have hfeq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [InitECandidate.Solver.Wave8Contracts.M05.blockOutObjects_eq hAs.2 hWT.2.2.1 hcell
          (hg_ml "bo" (by decide) (by decide) (by decide)),
        InitECandidate.Solver.Wave8Contracts.M05.balObjects_eq hAs.2 hWT.1 hWT.2.2.1 hcell
          (hg_ml "bal_accounts" (by decide) (by decide) (by decide)),
        hg_ml "journal" (by decide) (by decide) (by decide),
        hg_ml "journal_cap" (by decide) (by decide) (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne : ofString gn.1 ≠ ofString "heap_ptr" ∧ ofString gn.1 ≠ ofString "scratch_ptr" ∧
        ofString gn.1 ≠ ofString "frame_mem_ptr" := by
      revert gn hgn; decide
    rw [hg_ml gn.1 hne.1 hne.2.1 hne.2.2]
  have hFT_post := InitECandidate.Solver.Wave8Contracts.M05.fixedTyped_of_eq
    hAp hWT.2.2.1 hag.1 hag.2 hfeq
  have hg_core : ∀ g ∈ InitECandidate.Solver.Wave8Contracts.M05.coreWorldGlobals, globN post g = globN s g := by
    intro g hg
    have hne : ofString g ≠ ofString "heap_ptr" ∧ ofString g ≠ ofString "scratch_ptr" ∧
        ofString g ≠ ofString "frame_mem_ptr" := by
      revert g hg; decide
    exact hg_ml g hne.1 hne.2.1 hne.2.2
  obtain ⟨hWT_post, hOG⟩ := InitECandidate.Solver.Wave8Contracts.M05.worldTypedWith_congr_w1
    hAs hAp hag.1 hag.2 hg_core hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hwo_eq : worldOwned post S Nd = worldOwned s S Nd := by
    unfold worldOwned
    have hfp : S.flatMap (htabFootprint post) = S.flatMap (htabFootprint s) := by
      apply List.flatMap_congr
      intro t ht
      exact InitECandidate.Solver.Wave8Contracts.M05.htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1
    have hne : nodeExtents post Nd = nodeExtents s Nd :=
      InitECandidate.Solver.Wave8Contracts.M05.nodeExtents_eq hWT.2.2.2.1 hcell
    rw [hfp, hfeq, hne]
  refine ⟨S, Nd, fun _ ht => ht, hWT_post, hOG, ?_, hQ S Nd hWT hWT_post hwo_eq⟩
  intro a hkeep hhf
  exact hfr_free a (fun j hj => by
    simp only [List.mem_singleton] at hj; subst hj
    exact hkeep (freeGap s) (List.mem_append_right _ List.mem_cons_self)) hhf

theorem freshHeap_ivlsDisj_worldOwned {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hAs : ArenaOK s) (hAp : ArenaOK post)
    (hWT : WorldTypedWith s S Nd)
    (hwo_eq : worldOwned post S Nd = worldOwned s S Nd)
    {B : List Ivl}
    (hB : ∀ b ∈ B, b.2 = 0 ∨ Inside b (globN s "heap_ptr") (globN post "heap_ptr")) :
    IvlsDisj B (worldOwned post S Nd) := by
  intro b hb o ho
  rw [hwo_eq] at ho
  rcases hB b hb with hb0 | hbin
  · exact Or.inl hb0
  · rcases InitECandidate.Solver.Wave8Contracts.M08.worldOwned_allocated hWT ho with ho0 | hoal
    · exact Or.inr (Or.inl ho0)
    · exact InitECandidate.Solver.Wave8Contracts.M08.disj_allocated_fresh_heap hAs hAp hoal hbin


theorem «wk_lst_new» :
    WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    (RetAvoidsIf (fun s => locN s "esz" * locN s "cap" < 2 ^ 64)
      (fun s post w => [(w, 24), (memW post w, locN s "esz" * locN s "cap")])) (ofString "lst_new") := by
  have hlook : originalRuntimeCode.lookup (ofString "lst_new") =
      some ([(ofString "esz", .one), (ofString "cap", .one)],
        sourceFnBody Guest.Software.guestFn_lst_new, .one) :=
    lookup_of_guestAst_getElem 408 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_lst_new) rfl
  refine ⟨_, _, _, hlook, ?_⟩
  intro F s hcode hWOK hlookup _ hres
  obtain ⟨hG, hA⟩ := hWOK.1
  obtain ⟨hp, _, _, hhp, hhp_eq, _, _, _, _⟩ :=
    InitECandidate.Solver.Wave8Contracts.M26.arenaOK_globals s hA
  obtain ⟨vals, hvals⟩ := hlookup
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup _ vals _ s.locals .one hvals
  have hparams : ∃ w_esz w_cap : BitVec 64,
      s.locals.lookup (ofString "esz") = some (.val (.word w_esz)) ∧
      s.locals.lookup (ofString "cap") = some (.val (.word w_cap)) := by
    simp only [lookupCodeHOLExact, hlook] at hx
    rcases vals with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩ <;> try (simp at hx)
    rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL] at hx
    obtain ⟨_, hL⟩ := hx
    exact ⟨w1, w2, by rw [← hL]; simp [show ofString "esz" ≠ ofString "cap" by decide],
      by rw [← hL]; simp⟩
  obtain ⟨w_esz, w_cap, hesz_s, hcap_s⟩ := hparams
  have hbody : sourceFnBody Guest.Software.guestFn_lst_new =
      .decCall (ofString "l") .one (ofString "alloc") [.const 24]
        (.decCall (ofString "p") .one (ofString "alloc")
          [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")]]
          (.seq (.store (.op .add [.var .local (ofString "l"), .const 0]) (.var .local (ofString "p")))
            (.seq (.store (.op .add [.var .local (ofString "l"), .const 8]) (.const 0))
              (.seq (.store (.op .add [.var .local (ofString "l"), .const 16]) (.var .local (ofString "cap")))
                (.return (.var .local (ofString "l"))))))) := rfl
  have hret_ex : ∃ rv, (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_lst_new)).1 =
      some (.returned rv) := by
    rcases hres with ⟨rv, hrv⟩ | ⟨eid, ev_val, hexn, hne⟩
    · exact ⟨rv, hrv⟩
    · exfalso
      rw [hbody] at hexn
      refine noResumeExn_decCall_alloc hcode hp hhp hne (fun _ q1 _ => ?_) hexn
      exact noResumeExn_decCall_alloc (by dsimp only [setVarHOLFinite]; exact hcode) q1
        (by dsimp only [setVarHOLFinite]; simp [HolFiniteMapExact.lookup_update, FUPDATE]) hne
        (fun _ _ _ => noExn_seq_store fun _ => noExn_seq_store fun _ => noExn_seq_store fun _ => noExn_return)
  obtain ⟨rv, hrv⟩ := hret_ex
  have hrun : InitECandidate.Solver.Wave8Contracts.M26.Ret s (sourceFnBody Guest.Software.guestFn_lst_new)
      (fun rval post => WorldStep (fun _ => []) ["heap_ptr"]
        [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
         ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
        (RetAvoidsIf (fun s => locN s "esz" * locN s "cap" < 2 ^ 64)
          (fun s post w => [(w, 24), (memW post w, locN s "esz" * locN s "cap")]))
        s (some (.returned rval)) post) := by
    rw [hbody]
    apply InitECandidate.Solver.Wave8Contracts.M26.Ret.of_NS
    refine InitECandidate.Solver.Wave8Contracts.M26.Ret.ns_alloc hcode 24 rfl hp hhp ?_
    intro hcmp1_1 hcmp2_1
    let q1 : BitVec 64 := (hp + (24 + 7)) &&& ((0 : BitVec 64) - 8)
    let L1 := s.locals.update (ofString "l", .val (.word hp))
    let G1 := s.globals.update (ofString "heap_ptr", .val (.word q1))
    have hmul1 : InitECandidate.Solver.Wave8Contracts.M26.ev
        (InitECandidate.Solver.Wave8Contracts.M26.NS s L1 G1 s.memory (s.clock - 1))
        (.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")]) =
        some (.val (.word (w_esz * w_cap))) := by
      have hesz1 : L1.lookup (ofString "esz") = some (.val (.word w_esz)) := by
        simp [L1, HolFiniteMapExact.lookup_update, FUPDATE, hesz_s, show ofString "l" ≠ ofString "esz" by decide]
      have hcap1 : L1.lookup (ofString "cap") = some (.val (.word w_cap)) := by
        simp [L1, HolFiniteMapExact.lookup_update, FUPDATE, hcap_s, show ofString "l" ≠ ofString "cap" by decide]
      simp [InitECandidate.Solver.Wave8Contracts.M26.ev, evalHOLExact, evalListHOLExact, hesz1, hcap1,
        valueIsWord, valueWord, panOpHOL]
    have hq1_g : G1.lookup (ofString "heap_ptr") = some (.val (.word q1)) := by
      simp [G1, HolFiniteMapExact.lookup_update, FUPDATE]
    refine InitECandidate.Solver.Wave8Contracts.M26.Ret.ns_alloc hcode (w_esz * w_cap) hmul1 q1 hq1_g ?_
    intro hcmp1_2 hcmp2_2
    let q2 : BitVec 64 := (q1 + ((w_esz * w_cap) + 7)) &&& ((0 : BitVec 64) - 8)
    let L2 := L1.update (ofString "p", .val (.word q1))
    let G2 := G1.update (ofString "heap_ptr", .val (.word q2))
    refine InitECandidate.Solver.Wave8Contracts.M26.Ret.ns_storeW (hp + 0) q1
      (by simp [InitECandidate.Solver.Wave8Contracts.M26.ev, evalHOLExact, evalListHOLExact, L2, L1,
        HolFiniteMapExact.lookup_update, FUPDATE, show ofString "p" ≠ ofString "l" by decide,
        valueIsWord, valueWord, wordOpHOL, wordOp])
      (by simp [InitECandidate.Solver.Wave8Contracts.M26.ev, evalHOLExact, L2, HolFiniteMapExact.lookup_update, FUPDATE])
      fun hdom0 => ?_
    let M1 := InitECandidate.Solver.Wave8Contracts.M26.updW s.memory (hp + 0) q1
    refine InitECandidate.Solver.Wave8Contracts.M26.Ret.ns_storeW (hp + 8) 0
      (by simp [InitECandidate.Solver.Wave8Contracts.M26.ev, evalHOLExact, evalListHOLExact, L2, L1,
        HolFiniteMapExact.lookup_update, FUPDATE, show ofString "p" ≠ ofString "l" by decide,
        valueIsWord, valueWord, wordOpHOL, wordOp])
      rfl fun hdom8 => ?_
    let M2 := InitECandidate.Solver.Wave8Contracts.M26.updW M1 (hp + 8) 0
    refine InitECandidate.Solver.Wave8Contracts.M26.Ret.ns_storeW (hp + 16) w_cap
      (by simp [InitECandidate.Solver.Wave8Contracts.M26.ev, evalHOLExact, evalListHOLExact, L2, L1,
        HolFiniteMapExact.lookup_update, FUPDATE, show ofString "p" ≠ ofString "l" by decide,
        valueIsWord, valueWord, wordOpHOL, wordOp])
      (by simp [InitECandidate.Solver.Wave8Contracts.M26.ev, evalHOLExact, L2, L1,
        HolFiniteMapExact.lookup_update, FUPDATE, hcap_s,
        show ofString "p" ≠ ofString "cap" by decide, show ofString "l" ≠ ofString "cap" by decide])
      fun hdom16 => ?_
    let M3 := InitECandidate.Solver.Wave8Contracts.M26.updW M2 (hp + 16) w_cap
    refine InitECandidate.Solver.Wave8Contracts.M26.Ret.ns_ret fun val hval => ?_
    have hval_eq : val = .val (.word hp) := by
      simp [InitECandidate.Solver.Wave8Contracts.M26.ev, evalHOLExact, L2, L1,
        HolFiniteMapExact.lookup_update, FUPDATE, show ofString "p" ≠ ofString "l" by decide] at hval
      exact hval.symm
    subst hval_eq
    set outerPost : PanSemStateFiniteExact 64 F :=
      { locals := HolFiniteMapExact.resVarEq
          (HolFiniteMapExact.resVarEq
            (emptyLocalsHOLFinite (InitECandidate.Solver.Wave8Contracts.M26.NS s L2 G2 M3 (s.clock - 1 - 1))).locals
            (ofString "p", L1.lookup (ofString "p")))
          (ofString "l", s.locals.lookup (ofString "l")),
        globals := G2, structs := s.structs, code := s.code, eshapes := s.eshapes,
        memory := M3, memaddrs := s.memaddrs, shMemaddrs := s.shMemaddrs,
        clock := s.clock - 1 - 1, be := s.be, ffi := s.ffi,
        baseAddr := s.baseAddr, topAddr := s.topAddr }
    change WorldStep (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoidsIf (fun s => locN s "esz" * locN s "cap" < 2 ^ 64)
        (fun s post w => [(w, 24), (memW post w, locN s "esz" * locN s "cap")]))
      s (some (.returned (.val (.word hp)))) outerPost
    have hhp_hi : hp.toNat ≤ heapLimit := by rw [hhp_eq]; exact hA.2.1
    have hhp_al : hp.toNat % 8 = 0 := by rw [hhp_eq]; exact hA.2.2.2.2.2.1
    obtain ⟨hq1_eq, hq1_hi, hq1_al, hp_le_q1⟩ :=
      InitECandidate.Solver.Wave8Contracts.M26.alloc_arith hp 24 hhp_hi hhp_al hcmp1_1 hcmp2_1
    change q1.toNat = _ at hq1_eq; change q1.toNat ≤ heapLimit at hq1_hi
    change q1.toNat % 8 = 0 at hq1_al; change hp.toNat ≤ q1.toNat at hp_le_q1
    have h24 : ((24 : BitVec 64).toNat + 7) / 8 * 8 = 24 := by decide
    rw [h24] at hq1_eq
    obtain ⟨hq2_eq, hq2_hi, hq2_al, hq1_le_q2⟩ :=
      InitECandidate.Solver.Wave8Contracts.M26.alloc_arith q1 (w_esz * w_cap) hq1_hi hq1_al hcmp1_2 hcmp2_2
    change q2.toNat = _ at hq2_eq; change q2.toNat ≤ heapLimit at hq2_hi
    change q2.toNat % 8 = 0 at hq2_al; change q1.toNat ≤ q2.toNat at hq1_le_q2
    have ho_hp : globN outerPost "heap_ptr" = q2.toNat := by
      simp [outerPost, G2, globN, HolFiniteMapExact.lookup_update, FUPDATE]
    have ho_fp : globN outerPost "frame_mem_ptr" = globN s "frame_mem_ptr" := by
      simp [outerPost, G2, G1, globN, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
    have ho_sp : globN outerPost "scratch_ptr" = globN s "scratch_ptr" := by
      simp [outerPost, G2, G1, globN, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
    have hG_post : GuestInv outerPost := ⟨hG.code, hG.memaddrs, hG.shMemaddrs, hG.baseAddr⟩
    have hA_post : ArenaOK outerPost := by
      unfold ArenaOK; rw [ho_hp, ho_fp, ho_sp]
      exact ⟨by have := hA.1; omega, hq2_hi, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1, hq2_al, hA.2.2.2.2.2.2.1, hA.2.2.2.2.2.2.2⟩
    have hag : AllocatorGrows s outerPost := ⟨by rw [← hhp_eq, ho_hp]; omega, by rw [ho_sp]⟩
    have hgw : GlobalsKept ["heap_ptr"] s outerPost := by
      intro k hk
      have hne : ofString "heap_ptr" ≠ k := fun heq => hk (by simp [heq])
      simp [outerPost, G2, G1, HolFiniteMapExact.lookup_update, FUPDATE, hne]
    have hnonheap : ∀ k : MlS, k ≠ ofString "heap_ptr" → k ≠ ofString "scratch_ptr" → k ≠ ofString "frame_mem_ptr" →
        s.globals.lookup k = outerPost.globals.lookup k :=
      fun k h1 _ _ => hgw k (by simp [h1])
    have hdom_wr : ∀ a : BitVec 64, outerPost.memory a ≠ s.memory a → s.memaddrs a := by
      intro a hne
      by_cases h16 : a = hp + 16
      · subst h16; exact hdom16
      · by_cases h8 : a = hp + 8
        · subst h8; exact hdom8
        · by_cases h0 : a = hp + 0
          · subst h0; exact hdom0
          · exfalso; apply hne
            change M3 a = s.memory a
            unfold M3 M2 M1 InitECandidate.Solver.Wave8Contracts.M26.updW
            rw [if_neg h16, if_neg h8, if_neg h0]
    have hfr_free : FrameOutside s outerPost [freeGap s] (heapFree s) := by
      intro a _ hhf
      have ha_ne : ∀ off : Nat, off ∈ ([0, 8, 16] : List Nat) → a ≠ hp + BitVec.ofNat 64 off := by
        intro off hoff heq; subst heq
        have hoff_lt : off ≤ 16 := by simp at hoff; omega
        have hhl264 : heapLimit < 2 ^ 64 := by decide
        have hadd : (hp + BitVec.ofNat 64 off).toNat = hp.toNat + off := by
          rw [← InitECandidate.Solver.Wave8Contracts.M26.ofNat_add_toNat_eq hp off,
            BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        apply hhf; unfold CellHits heapFree; rw [hadd, ← hhp_eq]; dsimp only; omega
      have h16 : a ≠ hp + 16 := ha_ne 16 (by simp)
      have h8 : a ≠ hp + 8 := ha_ne 8 (by simp)
      have h0 : a ≠ hp + 0 := ha_ne 0 (by simp)
      change M3 a = s.memory a
      unfold M3 M2 M1 InitECandidate.Solver.Wave8Contracts.M26.updW
      rw [if_neg h16, if_neg h8, if_neg h0]
    refine worldStep_of_free_writes hWOK ⟨hG_post, hA_post⟩ hag hgw hnonheap rfl hdom_wr hfr_free ?_
    intro S Nd hWT _ hwo_eq hmul_lt v hv
    injection hv with hv'; injection hv' with hv''; subst hv''
    refine ⟨hp, rfl, ?_⟩
    have hloc_esz : locN s "esz" = w_esz.toNat := by simp [locN, hesz_s]
    have hloc_cap : locN s "cap" = w_cap.toNat := by simp [locN, hcap_s]
    rw [hloc_esz, hloc_cap] at hmul_lt
    have hmul_toNat : (w_esz * w_cap).toNat = w_esz.toNat * w_cap.toNat := by
      rw [BitVec.toNat_mul, Nat.mod_eq_of_lt hmul_lt]
    rw [hmul_toNat] at hq2_eq
    have hp0_ne_8 : hp + 0 ≠ hp + 8 := by
      intro h; have h1 := congrArg BitVec.toNat h; simp [BitVec.toNat_add] at h1; omega
    have hp0_ne_16 : hp + 0 ≠ hp + 16 := by
      intro h; have h1 := congrArg BitVec.toNat h; simp [BitVec.toNat_add] at h1; omega
    have hp_eq_0 : BitVec.ofNat 64 hp.toNat = hp + 0 := by simp [BitVec.ofNat_toNat]
    have hmem0 : memW outerPost hp.toNat = q1.toNat := by
      unfold memW
      have : outerPost.memory (BitVec.ofNat 64 hp.toNat) = .word q1 := by
        change M3 (BitVec.ofNat 64 hp.toNat) = .word q1
        rw [hp_eq_0]; simp [M3, M2, M1, InitECandidate.Solver.Wave8Contracts.M26.updW, hp0_ne_16, hp0_ne_8]
      rw [this]
    refine freshHeap_ivlsDisj_worldOwned hA hA_post hWT hwo_eq ?_
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · right; rw [← hhp_eq, ho_hp]; exact ⟨le_rfl, by omega⟩
    · rw [hmem0, hloc_esz, hloc_cap]
      by_cases hz : w_esz.toNat * w_cap.toNat = 0
      · exact Or.inl hz
      · right; rw [← hhp_eq, ho_hp]; exact ⟨hp_le_q1, by omega⟩
  have hdone := hrun rv hrv
  dsimp only at hdone
  rwa [hrv]

theorem «wk_mpt_new» :
    WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    (RetAvoids (fun _ _ w => [(w, 16)])) (ofString "mpt_new") := by
  have hlook : originalRuntimeCode.lookup (ofString "mpt_new") =
      some ([(ofString "root_node", .one), (ofString "secured", .one)],
        sourceFnBody Guest.Software.guestFn_mpt_new, .one) :=
    lookup_of_guestAst_getElem 268 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_mpt_new) rfl
  refine ⟨_, _, _, hlook, ?_⟩
  intro F s hcode hWOK hlookup _ hres
  obtain ⟨hG, hA⟩ := hWOK.1
  obtain ⟨hp, _, _, hhp, hhp_eq, _, _, _, _⟩ :=
    InitECandidate.Solver.Wave8Contracts.M26.arenaOK_globals s hA
  obtain ⟨vals, hvals⟩ := hlookup
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup _ vals _ s.locals .one hvals
  have hparams : ∃ w_rn w_sec : BitVec 64,
      s.locals.lookup (ofString "root_node") = some (.val (.word w_rn)) ∧
      s.locals.lookup (ofString "secured") = some (.val (.word w_sec)) := by
    simp only [lookupCodeHOLExact, hlook] at hx
    rcases vals with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩ <;> try (simp at hx)
    rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL] at hx
    obtain ⟨_, hL⟩ := hx
    exact ⟨w1, w2, by rw [← hL]; simp [show ofString "root_node" ≠ ofString "secured" by decide],
      by rw [← hL]; simp⟩
  obtain ⟨w_rn, w_sec, hrn_s, hsec_s⟩ := hparams
  have hbody : sourceFnBody Guest.Software.guestFn_mpt_new =
      .decCall (ofString "m") .one (ofString "alloc") [.const 16]
        (.seq (.store (.op .add [.var .local (ofString "m"), .const 0]) (.var .local (ofString "root_node")))
          (.seq (.store (.op .add [.var .local (ofString "m"), .const 8]) (.var .local (ofString "secured")))
            (.return (.var .local (ofString "m"))))) := rfl
  have hret_ex : ∃ rv, (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_mpt_new)).1 =
      some (.returned rv) := by
    rcases hres with ⟨rv, hrv⟩ | ⟨eid, ev_val, hexn, hne⟩
    · exact ⟨rv, hrv⟩
    · exfalso
      rw [hbody] at hexn
      exact noResumeExn_decCall_alloc hcode hp hhp hne
        (fun _ _ _ => noExn_seq_store fun _ => noExn_seq_store fun _ => noExn_return) hexn
  obtain ⟨rv, hrv⟩ := hret_ex
  have hrun : InitECandidate.Solver.Wave8Contracts.M26.Ret s (sourceFnBody Guest.Software.guestFn_mpt_new)
      (fun rval post => WorldStep (fun _ => []) ["heap_ptr"]
        [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
         ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
        (RetAvoids (fun _ _ w => [(w, 16)])) s (some (.returned rval)) post) := by
    rw [hbody]
    apply InitECandidate.Solver.Wave8Contracts.M26.Ret.of_NS
    refine InitECandidate.Solver.Wave8Contracts.M26.Ret.ns_alloc hcode 16 rfl hp hhp ?_
    intro hcmp1 hcmp2
    let q : BitVec 64 := (hp + (16 + 7)) &&& ((0 : BitVec 64) - 8)
    let L1 := s.locals.update (ofString "m", .val (.word hp))
    let G1 := s.globals.update (ofString "heap_ptr", .val (.word q))
    refine InitECandidate.Solver.Wave8Contracts.M26.Ret.ns_storeW (hp + 0) w_rn
      (by simp [InitECandidate.Solver.Wave8Contracts.M26.ev, evalHOLExact, evalListHOLExact, L1,
        HolFiniteMapExact.lookup_update, FUPDATE, valueIsWord, valueWord, wordOpHOL, wordOp])
      (by simp [InitECandidate.Solver.Wave8Contracts.M26.ev, evalHOLExact, L1,
        HolFiniteMapExact.lookup_update, FUPDATE, hrn_s, show ofString "m" ≠ ofString "root_node" by decide])
      fun hdom0 => ?_
    let M1 := InitECandidate.Solver.Wave8Contracts.M26.updW s.memory (hp + 0) w_rn
    refine InitECandidate.Solver.Wave8Contracts.M26.Ret.ns_storeW (hp + 8) w_sec
      (by simp [InitECandidate.Solver.Wave8Contracts.M26.ev, evalHOLExact, evalListHOLExact, L1,
        HolFiniteMapExact.lookup_update, FUPDATE, valueIsWord, valueWord, wordOpHOL, wordOp])
      (by simp [InitECandidate.Solver.Wave8Contracts.M26.ev, evalHOLExact, L1,
        HolFiniteMapExact.lookup_update, FUPDATE, hsec_s, show ofString "m" ≠ ofString "secured" by decide])
      fun hdom8 => ?_
    let M2 := InitECandidate.Solver.Wave8Contracts.M26.updW M1 (hp + 8) w_sec
    refine InitECandidate.Solver.Wave8Contracts.M26.Ret.ns_ret fun val hval => ?_
    have hval_eq : val = .val (.word hp) := by
      simp [InitECandidate.Solver.Wave8Contracts.M26.ev, evalHOLExact, L1,
        HolFiniteMapExact.lookup_update, FUPDATE] at hval
      exact hval.symm
    subst hval_eq
    have hhp_hi : hp.toNat ≤ heapLimit := by rw [hhp_eq]; exact hA.2.1
    have hhp_al : hp.toNat % 8 = 0 := by rw [hhp_eq]; exact hA.2.2.2.2.2.1
    obtain ⟨hq_eq, hq_hi, hq_al, _⟩ :=
      InitECandidate.Solver.Wave8Contracts.M26.alloc_arith hp 16 hhp_hi hhp_al hcmp1 hcmp2
    change q.toNat = _ at hq_eq; change q.toNat ≤ heapLimit at hq_hi; change q.toNat % 8 = 0 at hq_al
    have h16 : ((16 : BitVec 64).toNat + 7) / 8 * 8 = 16 := by decide
    rw [h16] at hq_eq
    set outerPost : PanSemStateFiniteExact 64 F :=
      { locals := HolFiniteMapExact.resVarEq
          (emptyLocalsHOLFinite (InitECandidate.Solver.Wave8Contracts.M26.NS s L1 G1 M2 (s.clock - 1))).locals
          (ofString "m", s.locals.lookup (ofString "m")),
        globals := G1, structs := s.structs, code := s.code, eshapes := s.eshapes,
        memory := M2, memaddrs := s.memaddrs, shMemaddrs := s.shMemaddrs,
        clock := s.clock - 1, be := s.be, ffi := s.ffi,
        baseAddr := s.baseAddr, topAddr := s.topAddr }
    have ho_hp : globN outerPost "heap_ptr" = q.toNat := by
      simp [outerPost, G1, globN, HolFiniteMapExact.lookup_update, FUPDATE]
    have ho_fp : globN outerPost "frame_mem_ptr" = globN s "frame_mem_ptr" := by
      simp [outerPost, G1, globN, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
    have ho_sp : globN outerPost "scratch_ptr" = globN s "scratch_ptr" := by
      simp [outerPost, G1, globN, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
    have hG_post : GuestInv outerPost := ⟨hG.code, hG.memaddrs, hG.shMemaddrs, hG.baseAddr⟩
    have hA_post : ArenaOK outerPost := by
      unfold ArenaOK; rw [ho_hp, ho_fp, ho_sp]
      exact ⟨by have := hA.1; omega, hq_hi, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1, hq_al, hA.2.2.2.2.2.2.1, hA.2.2.2.2.2.2.2⟩
    have hag : AllocatorGrows s outerPost := ⟨by rw [← hhp_eq, ho_hp]; omega, by rw [ho_sp]⟩
    have hgw : GlobalsKept ["heap_ptr"] s outerPost := by
      intro k hk
      have hne : ofString "heap_ptr" ≠ k := fun heq => hk (by simp [heq])
      simp [outerPost, G1, HolFiniteMapExact.lookup_update, FUPDATE, hne]
    have hnonheap : ∀ k : MlS, k ≠ ofString "heap_ptr" → k ≠ ofString "scratch_ptr" → k ≠ ofString "frame_mem_ptr" →
        s.globals.lookup k = outerPost.globals.lookup k :=
      fun k h1 _ _ => hgw k (by simp [h1])
    have hdom_wr : ∀ a : BitVec 64, outerPost.memory a ≠ s.memory a → s.memaddrs a := by
      intro a hne
      by_cases h8 : a = hp + 8
      · subst h8; exact hdom8
      · by_cases h0 : a = hp + 0
        · subst h0; exact hdom0
        · exfalso; apply hne
          change M2 a = s.memory a
          unfold M2 M1 InitECandidate.Solver.Wave8Contracts.M26.updW
          rw [if_neg h8, if_neg h0]
    have hfr_free : FrameOutside s outerPost [freeGap s] (heapFree s) := by
      intro a _ hhf
      have ha_ne : ∀ off : Nat, off ∈ ([0, 8] : List Nat) → a ≠ hp + BitVec.ofNat 64 off := by
        intro off hoff heq; subst heq
        have hoff_lt : off ≤ 8 := by simp at hoff; omega
        have hhl264 : heapLimit < 2 ^ 64 := by decide
        have hadd : (hp + BitVec.ofNat 64 off).toNat = hp.toNat + off := by
          rw [← InitECandidate.Solver.Wave8Contracts.M26.ofNat_add_toNat_eq hp off,
            BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        apply hhf; unfold CellHits heapFree; rw [hadd, ← hhp_eq]; dsimp only; omega
      have h8 : a ≠ hp + 8 := ha_ne 8 (by simp)
      have h0 : a ≠ hp + 0 := ha_ne 0 (by simp)
      change M2 a = s.memory a
      unfold M2 M1 InitECandidate.Solver.Wave8Contracts.M26.updW
      rw [if_neg h8, if_neg h0]
    refine worldStep_of_free_writes hWOK ⟨hG_post, hA_post⟩ hag hgw hnonheap rfl hdom_wr hfr_free ?_
    intro S Nd hWT _ hwo_eq v hv
    injection hv with hv'; injection hv' with hv''; subst hv''
    refine ⟨hp, rfl, freshHeap_ivlsDisj_worldOwned hA hA_post hWT hwo_eq ?_⟩
    intro b hb
    simp only [List.mem_singleton] at hb; subst hb
    right; rw [← hhp_eq, ho_hp]; exact ⟨le_rfl, by omega⟩
  have hdone := hrun rv hrv
  dsimp only at hdone
  rwa [hrv]

theorem «wk_msg_new» :
    WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    (RetAvoids (fun _ _ w => [(w, 176)])) (ofString "msg_new") := by
  have hlook : originalRuntimeCode.lookup (ofString "msg_new") =
      some ([], sourceFnBody Guest.Software.guestFn_msg_new, .one) :=
    lookup_of_guestAst_getElem 465 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_msg_new) rfl
  refine ⟨_, _, _, hlook, ?_⟩
  intro F s hcode hWOK _ hnt hres
  obtain ⟨hG, hA⟩ := hWOK.1
  obtain ⟨hp, _, _, hhp, hhp_eq, _, _, _, _⟩ :=
    InitECandidate.Solver.Wave8Contracts.M26.arenaOK_globals s hA
  have hbody : sourceFnBody Guest.Software.guestFn_msg_new =
      .decCall (ofString "m") .one (ofString "alloc") [.const 176]
        (.seq (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "m"), .const 176])
          (.return (.var .local (ofString "m")))) := rfl
  rw [hbody] at hnt hres ⊢
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres ⊢
  have ha1 : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.const 176] =
      some [.val (.word 176)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have hl1 := pan_one_word_lookup s.code.lookup (ofString "alloc") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_alloc) 176 (by rw [hcode]; exact lookup_alloc)
  simp only [ha1, hl1] at hnt hres ⊢
  by_cases hc0 : s.clock = 0
  · simp [hc0] at hnt
  · simp only [hc0, ↓reduceIte] at hnt hres ⊢
    have hal1 := alloc_body_resumes
      (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word 176))))
      hp 176 hcode hhp (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    rcases hr1 : evaluateHOLFiniteState
        (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word 176))))
        (sourceFnBody Guest.Software.guestFn_alloc) with ⟨ar1, ap1⟩
    simp only [hr1] at hal1 hnt hres ⊢
    have har1_ret : ∃ av1, ar1 = some (.returned av1) := by
      cases ar1 with
      | none => exact False.elim (not_resumes_error hres)
      | some r =>
        cases r with
        | returned av1 => exact ⟨av1, rfl⟩
        | exception eid ev =>
          rcases hres with ⟨_, h⟩ | ⟨_, _, h, hne⟩
          · simp at h
          · dsimp only at h; injection h with h'; injection h' with he1 he2; subst he1 he2
            have := hal1 (Or.inr ⟨eid, ev, rfl, hne⟩)
            cases this.1
        | timeOut => simp at hnt
        | finalFfi _ => exfalso; rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
        | _ => exact False.elim (not_resumes_error hres)
    obtain ⟨av1, rfl⟩ := har1_ret
    obtain ⟨hav1, hcmp1, hcmp2, hap1⟩ := hal1 (Or.inl ⟨av1, rfl⟩)
    injection hav1 with hav1'; injection hav1' with hav1''; subst hav1''
    have hsh1 : (shapeEqHOL (shapeOfHOLExact (.val (.word hp) : ValueHOL 64)) .one &&
        shapeEqHOL (shapeOfHOLExact (.val (.word hp) : ValueHOL 64)) .one) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    simp only [hsh1, ↓reduceIte] at hnt hres ⊢
    set q : BitVec 64 := (hp + (176 + 7)) &&& ((0 : BitVec 64) - 8)
    set s1 := setVarHOLFinite (ofString "m") (.val (.word hp)) { ap1 with locals := s.locals }
    have hhp_hi : hp.toNat ≤ heapLimit := by rw [hhp_eq]; exact hA.2.1
    have hhp_al : hp.toNat % 8 = 0 := by rw [hhp_eq]; exact hA.2.2.2.2.2.1
    obtain ⟨hq_eq, hq_hi, hq_al, hp_le_q⟩ :=
      InitECandidate.Solver.Wave8Contracts.M26.alloc_arith hp 176 hhp_hi hhp_al hcmp1 hcmp2
    change q.toNat = _ at hq_eq; change q.toNat ≤ heapLimit at hq_hi
    change q.toNat % 8 = 0 at hq_al; change hp.toNat ≤ q.toNat at hp_le_q
    have h176 : ((176 : BitVec 64).toNat + 7) / 8 * 8 = 176 := by decide
    rw [h176] at hq_eq
    rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
    have hs1_code : s1.code = originalRuntimeCode := by dsimp only [s1, setVarHOLFinite]; rw [hap1]; exact hcode
    have hs1_G : GuestInv s1 := ⟨hs1_code, by dsimp only [s1, setVarHOLFinite]; rw [hap1]; exact hG.memaddrs,
      by dsimp only [s1, setVarHOLFinite]; rw [hap1]; exact hG.shMemaddrs,
      by dsimp only [s1, setVarHOLFinite]; rw [hap1]; exact hG.baseAddr⟩
    have ha_mz : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
        [.var .local (ofString "m"), .const 176] = some [.val (.word hp), .val (.word 176)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, s1, setVarHOLFinite,
        HolFiniteMapExact.lookup_update, FUPDATE]
    have hl_mz := pan_two_word_lookup s1.code.lookup (ofString "memzero")
      (ofString "dst") (ofString "n") (sourceFnBody Guest.Software.guestFn_memzero)
      hp 176 (by decide) (by rw [hs1_code]; exact lookup_memzero)
    rw [evaluateHOLFiniteState_call] at hnt hres ⊢
    simp only [ha_mz, hl_mz] at hnt hres ⊢
    by_cases hc1 : s1.clock = 0
    · simp [hc1] at hnt
    · simp only [hc1, ↓reduceIte] at hnt hres ⊢
      set centry := callEntryStateHOLFinite s1
        ((HolFiniteMapExact.empty.update (ofString "dst", .val (.word hp))).update
          (ofString "n", .val (.word 176)))
      have hG_ce : GuestInv centry := guestInv_callEntry s1 _ hs1_G
      rcases hmz : evaluateHOLFiniteState centry (sourceFnBody Guest.Software.guestFn_memzero) with ⟨rmz, smz⟩
      simp only [hmz] at hnt hres ⊢
      have hres_mz : Resumes rmz := by
        cases rmz with
        | none => exact False.elim (not_resumes_error hres)
        | some r =>
          cases r with
          | returned rv => exact Or.inl ⟨rv, rfl⟩
          | exception eid ev =>
            rcases hres with ⟨_, h⟩ | ⟨_, _, h, hne⟩
            · simp at h
            · dsimp only at h; injection h with h'; injection h' with he1 he2; subst he1 he2
              exact Or.inr ⟨eid, ev, rfl, hne⟩
          | timeOut => simp at hnt
          | finalFfi _ => exfalso; rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
          | _ => exact False.elim (not_resumes_error hres)
      have hmwf := InitECandidate.Solver.Wave8Contracts.M08.memzero_body_frame centry
        hs1_code hG_ce (by rw [hmz]; exact hres_mz)
      rw [hmz] at hmwf
      have hce_dst : locN centry "dst" = hp.toNat := by
        simp [centry, callEntryStateHOLFinite, locN, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "n" ≠ ofString "dst" by decide]
      have hce_n : locN centry "n" = 176 := by
        simp [centry, callEntryStateHOLFinite, locN, HolFiniteMapExact.lookup_update, FUPDATE]
      rw [hce_dst, hce_n] at hmwf
      -- Analyze `rmz` cases (`returned` or `exception`):
      cases rmz with
      | none => exact False.elim (not_resumes_error hres)
      | some rmz' =>
        cases rmz' with
        | timeOut => simp at hnt
        | finalFfi _ => exfalso; rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
        | «break» | «continue» | error => exact False.elim (not_resumes_error hres)
        | exception eid ev =>
          -- Exception propagates out of `call` and `seq` and `decCall`!
          dsimp only at hres ⊢
          set outerPost : PanSemStateFiniteExact 64 F :=
            { (emptyLocalsHOLFinite smz) with
              locals := HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite smz).locals
                (ofString "m", s.locals.lookup (ofString "m")) }
          have ho_glob : outerPost.globals = s.globals.update (ofString "heap_ptr", .val (.word q)) := by
            dsimp only [outerPost, emptyLocalsHOLFinite]; rw [hmwf.2.2.2.2.2.1]; dsimp only [centry, callEntryStateHOLFinite, s1, setVarHOLFinite]; rw [hap1]; rfl
          have ho_hp : globN outerPost "heap_ptr" = q.toNat := by
            unfold globN; rw [ho_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
          have ho_fp : globN outerPost "frame_mem_ptr" = globN s "frame_mem_ptr" := by
            unfold globN; rw [ho_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
          have ho_sp : globN outerPost "scratch_ptr" = globN s "scratch_ptr" := by
            unfold globN; rw [ho_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
          have hG_post : GuestInv outerPost := by
            refine ⟨?_, ?_, ?_, ?_⟩
            · dsimp only [outerPost, emptyLocalsHOLFinite]; rw [hmwf.1]; exact hs1_code
            · dsimp only [outerPost, emptyLocalsHOLFinite]; rw [hmwf.2.1]; exact hs1_G.memaddrs
            · dsimp only [outerPost, emptyLocalsHOLFinite]; rw [hmwf.2.2.1]; exact hs1_G.shMemaddrs
            · dsimp only [outerPost, emptyLocalsHOLFinite]; rw [hmwf.2.2.2.1]; exact hs1_G.baseAddr
          have hA_post : ArenaOK outerPost := by
            unfold ArenaOK; rw [ho_hp, ho_fp, ho_sp]
            exact ⟨by have := hA.1; omega, hq_hi, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1, hq_al, hA.2.2.2.2.2.2.1, hA.2.2.2.2.2.2.2⟩
          have hag : AllocatorGrows s outerPost := ⟨by rw [← hhp_eq, ho_hp]; omega, by rw [ho_sp]⟩
          have hgw : GlobalsKept ["heap_ptr"] s outerPost := by
            intro k hk
            have hne : ofString "heap_ptr" ≠ k := fun heq => hk (by simp [heq])
            rw [ho_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne]
          have hnonheap : ∀ k : MlS, k ≠ ofString "heap_ptr" → k ≠ ofString "scratch_ptr" → k ≠ ofString "frame_mem_ptr" →
              s.globals.lookup k = outerPost.globals.lookup k := by
            intro k h1 _ _; exact hgw k (by simp [h1])
          have hbe : outerPost.be = s.be := by
            dsimp only [outerPost, emptyLocalsHOLFinite]; rw [hmwf.2.2.2.2.1]; dsimp only [centry, callEntryStateHOLFinite, s1, setVarHOLFinite]; rw [hap1]; rfl
          have hce_mem : centry.memory = s.memory := by
            dsimp only [centry, callEntryStateHOLFinite, s1, setVarHOLFinite]; rw [hap1]; rfl
          have hce_ma : centry.memaddrs = s.memaddrs := by
            dsimp only [centry, callEntryStateHOLFinite, s1, setVarHOLFinite]; rw [hap1]; rfl
          have hdom_wr : ∀ a : BitVec 64, outerPost.memory a ≠ s.memory a → s.memaddrs a := by
            intro a hne
            have hd := hmwf.2.2.2.2.2.2.2.2 a (by rw [hce_mem]; exact hne)
            rwa [hce_ma] at hd
          have hfr_free : FrameOutside s outerPost [freeGap s] (heapFree s) := by
            intro a _ hhf
            have hm := hmwf.2.2.2.2.2.2.1 a
              (fun j hj => by
                simp only [List.mem_singleton] at hj; subst hj
                intro ⟨hc1, hc2⟩
                apply hhf
                unfold CellHits heapFree at *
                rw [← hhp_eq]; dsimp only at *; omega)
              (fun hc => by unfold CellHits at hc; omega)
            rw [hce_mem] at hm
            exact hm
          refine worldStep_of_free_writes hWOK ⟨hG_post, hA_post⟩ hag hgw hnonheap hbe hdom_wr hfr_free ?_
          intro _ _ _ _ _ _ hv; simp at hv
        | returned v_mz =>
          dsimp only at hres ⊢
          by_cases hsh_mz : shapeEqHOL (shapeOfHOLExact v_mz) .one = true
          · simp only [hsh_mz, ↓reduceIte] at hres ⊢
            have hret_m : evaluateHOLFiniteState { smz with locals := s1.locals }
                (.return (.var .local (ofString "m"))) =
                (some (.returned (.val (.word hp))),
                  emptyLocalsHOLFinite { smz with locals := s1.locals }) := by
              have hs1_m_lk : s1.locals.lookup (ofString "m") = some (.val (.word hp)) := by
                simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              rw [evaluateHOLFiniteState_return]
              simp only [evalHOLExact, hs1_m_lk, shapeOfHOLExact, sizeOfShapeWithContextHOL]
              rfl
            rw [hret_m]
            dsimp only
            set outerPost : PanSemStateFiniteExact 64 F :=
              { (emptyLocalsHOLFinite { smz with locals := s1.locals }) with
                locals := HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite { smz with locals := s1.locals }).locals
                  (ofString "m", s.locals.lookup (ofString "m")) }
            have ho_glob : outerPost.globals = s.globals.update (ofString "heap_ptr", .val (.word q)) := by
              dsimp only [outerPost, emptyLocalsHOLFinite]; rw [hmwf.2.2.2.2.2.1]; dsimp only [centry, callEntryStateHOLFinite, s1, setVarHOLFinite]; rw [hap1]; rfl
            have ho_hp : globN outerPost "heap_ptr" = q.toNat := by
              unfold globN; rw [ho_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
            have ho_fp : globN outerPost "frame_mem_ptr" = globN s "frame_mem_ptr" := by
              unfold globN; rw [ho_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
            have ho_sp : globN outerPost "scratch_ptr" = globN s "scratch_ptr" := by
              unfold globN; rw [ho_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
            have hG_post : GuestInv outerPost := by
              refine ⟨?_, ?_, ?_, ?_⟩
              · dsimp only [outerPost, emptyLocalsHOLFinite]; rw [hmwf.1]; exact hs1_code
              · dsimp only [outerPost, emptyLocalsHOLFinite]; rw [hmwf.2.1]; exact hs1_G.memaddrs
              · dsimp only [outerPost, emptyLocalsHOLFinite]; rw [hmwf.2.2.1]; exact hs1_G.shMemaddrs
              · dsimp only [outerPost, emptyLocalsHOLFinite]; rw [hmwf.2.2.2.1]; exact hs1_G.baseAddr
            have hA_post : ArenaOK outerPost := by
              unfold ArenaOK; rw [ho_hp, ho_fp, ho_sp]
              exact ⟨by have := hA.1; omega, hq_hi, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1, hq_al, hA.2.2.2.2.2.2.1, hA.2.2.2.2.2.2.2⟩
            have hag : AllocatorGrows s outerPost := ⟨by rw [← hhp_eq, ho_hp]; omega, by rw [ho_sp]⟩
            have hgw : GlobalsKept ["heap_ptr"] s outerPost := by
              intro k hk
              have hne : ofString "heap_ptr" ≠ k := fun heq => hk (by simp [heq])
              rw [ho_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne]
            have hnonheap : ∀ k : MlS, k ≠ ofString "heap_ptr" → k ≠ ofString "scratch_ptr" → k ≠ ofString "frame_mem_ptr" →
                s.globals.lookup k = outerPost.globals.lookup k := by
              intro k h1 _ _; exact hgw k (by simp [h1])
            have hbe : outerPost.be = s.be := by
              dsimp only [outerPost, emptyLocalsHOLFinite]; rw [hmwf.2.2.2.2.1]; dsimp only [centry, callEntryStateHOLFinite, s1, setVarHOLFinite]; rw [hap1]; rfl
            have hce_mem : centry.memory = s.memory := by
              dsimp only [centry, callEntryStateHOLFinite, s1, setVarHOLFinite]; rw [hap1]; rfl
            have hce_ma : centry.memaddrs = s.memaddrs := by
              dsimp only [centry, callEntryStateHOLFinite, s1, setVarHOLFinite]; rw [hap1]; rfl
            have hdom_wr : ∀ a : BitVec 64, outerPost.memory a ≠ s.memory a → s.memaddrs a := by
              intro a hne
              have hd := hmwf.2.2.2.2.2.2.2.2 a (by rw [hce_mem]; exact hne)
              rwa [hce_ma] at hd
            have hfr_free : FrameOutside s outerPost [freeGap s] (heapFree s) := by
              intro a _ hhf
              have hm := hmwf.2.2.2.2.2.2.1 a
                (fun j hj => by
                  simp only [List.mem_singleton] at hj; subst hj
                  intro ⟨hc1, hc2⟩
                  apply hhf
                  unfold CellHits heapFree at *
                  rw [← hhp_eq]; dsimp only at *; omega)
                (fun hc => by unfold CellHits at hc; omega)
              rw [hce_mem] at hm
              exact hm
            refine worldStep_of_free_writes hWOK ⟨hG_post, hA_post⟩ hag hgw hnonheap hbe hdom_wr hfr_free ?_
            intro S Nd hWT _ hwo_eq v hv
            injection hv with hv'; injection hv' with hv''; subst hv''
            refine ⟨hp, rfl, freshHeap_ivlsDisj_worldOwned hA hA_post hWT hwo_eq ?_⟩
            intro b hb
            simp only [List.mem_singleton] at hb; subst hb
            right; rw [← hhp_eq, ho_hp]; exact ⟨le_rfl, by omega⟩
          · simp only [hsh_mz, Bool.false_eq_true, ↓reduceIte] at hres
            exact False.elim (not_resumes_error hres)

end InitECandidate.Solver.Wave8GuestInv.Fast_C08WkShard04
