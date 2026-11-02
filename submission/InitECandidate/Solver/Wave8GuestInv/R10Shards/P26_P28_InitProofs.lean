import InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28_Inits

/-! `InitEff` combinators and proofs of all 11 init `wk_*` contracts:
`wk_sha256_init`, `wk_header_init`, `wk_keccak_init`, `wk_ripemd160_init`,
`wk_blake2_init`, `wk_bn254_init`, `wk_bls_precompiles_init`, `wk_ssz_init`,
`wk_mpt_init`, `wk_fork_init`, `wk_evm_init`. -/

set_option autoImplicit false
set_option maxRecDepth 300000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false

namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. `InitEff`: world-tier allocator + global-buffer + heap-free write effect -/

structure InitEff {F : Type} (s cur : PanSemStateFiniteExact 64 F)
    (Rl : List Ivl) (B : List (String × Nat)) (gw : List String) : Prop where
  arena      : ArenaReady cur
  code       : cur.code = originalRuntimeCode
  memaddrs   : cur.memaddrs = s.memaddrs
  be         : cur.be = s.be
  eshapes    : cur.eshapes = s.eshapes
  hp_word    : ∃ pw : BitVec 64, cur.globals.lookup (ofString "heap_ptr") = some (.val (.word pw))
  hp_lo      : globN s "heap_ptr" ≤ globN cur "heap_ptr"
  fmp_eq     : globN cur "frame_mem_ptr" = globN s "frame_mem_ptr"
  sp_eq      : globN cur "scratch_ptr" = globN s "scratch_ptr"
  gw_kept    : GlobalsKept gw s cur
  fresh_bufs : FreshBufsOK s cur
  out_dom    : ∀ a : BitVec 64, cur.memory a ≠ s.memory a → s.memaddrs a
  cell_frame : ∀ a : BitVec 64, cur.memory a ≠ s.memory a →
                 (∃ ivl ∈ Rl, CellHitsPos a.toNat ivl) ∨
                 (∃ gs ∈ B, CellHitsPos a.toNat (bufferRegion s gs)) ∨
                 CellHitsPos a.toNat (heapFree s)
  byte_frame : ∀ b : Nat, b < 2 ^ 64 → memB cur b ≠ memB s b →
                 (∃ ivl ∈ Rl, InIvl b ivl) ∨
                 (∃ gs ∈ B, InIvl b (bufferRegion s gs)) ∨
                 InIvl b (heapFree s)

theorem InitEff.refl {F : Type} (s : PanSemStateFiniteExact 64 F)
    (Rl : List Ivl) (B : List (String × Nat)) (gw : List String)
    (hA : ArenaReady s) (hc : s.code = originalRuntimeCode) :
    InitEff s s Rl B gw := by
  have hhp : ∃ pw : BitVec 64, s.globals.lookup (ofString "heap_ptr") = some (.val (.word pw)) := by
    have hlo := hA.2.1
    have hsb : 0 < sourceBase := by rw [sourceBase_val]; decide
    unfold globN at hlo
    rcases hg : s.globals.lookup (ofString "heap_ptr") with _ | v
    · simp [hg] at hlo; omega
    · rcases v with ⟨⟨pw⟩⟩ | _ | _ <;> simp [hg] at hlo
      · exact ⟨pw, rfl⟩
      · omega
      · omega
  refine ⟨hA, hc, rfl, rfl, rfl, hhp, le_rfl, rfl, rfl, fun _ _ => rfl, ?_,
    fun _ h => absurd rfl h, fun _ h => absurd rfl h, fun _ _ h => absurd rfl h⟩
  refine ⟨fun _ _ => Or.inl rfl, ?_⟩
  rw [List.pairwise_iff_getElem]
  intro i j _ _ _ h1 _; exact absurd rfl h1.1

theorem InitEff.locals_clock {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : InitEff s cur Rl B gw) (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    InitEff s { cur with locals := L, clock := k } Rl B gw :=
  ⟨⟨guestInv_with_locals_clock cur L k h.arena.1, h.arena.2⟩,
   h.code, h.memaddrs, h.be, h.eshapes, h.hp_word, h.hp_lo, h.fmp_eq, h.sp_eq,
   h.gw_kept, h.fresh_bufs, h.out_dom, h.cell_frame, h.byte_frame⟩

theorem InitEff.of_byteEff {F : Type} {s cur next : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String} {Sub : List Ivl}
    (h : InitEff s cur Rl B gw) (hb : ByteEff cur next Sub)
    (hsub : ∀ iv ∈ Sub, 0 < iv.2 →
      (∃ j ∈ Rl, j.1 ≤ iv.1 ∧ iv.1 + iv.2 ≤ j.1 + j.2) ∨
      (∃ gs ∈ B, (bufferRegion s gs).1 ≤ iv.1 ∧ iv.1 + iv.2 ≤ (bufferRegion s gs).1 + (bufferRegion s gs).2) ∨
      (globN s "heap_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ heapLimit)) :
    InitEff s next Rl B gw := by
  have hGn : GuestInv next :=
    guestInv_congr hb.code hb.memaddrs hb.shMemaddrs hb.baseAddr h.arena.1
  have hAn : ArenaReady next := ⟨hGn, by simpa [ArenaOK, globN, hb.globals] using h.arena.2⟩
  refine ⟨hAn, hb.code.trans h.code, hb.memaddrs.trans h.memaddrs, hb.be.trans h.be, hb.eshapes.trans h.eshapes,
    by rw [hb.globals]; exact h.hp_word,
    by simpa [globN, hb.globals] using h.hp_lo,
    by simpa [globN, hb.globals] using h.fmp_eq,
    by simpa [globN, hb.globals] using h.sp_eq,
    fun k hk => (h.gw_kept k hk).trans (by rw [hb.globals]),
    by simpa [FreshBufsOK, globN, hb.globals] using h.fresh_bufs, ?_, ?_, ?_⟩
  · intro a hne
    by_cases hnc : next.memory a = cur.memory a
    · rw [hnc] at hne; exact h.out_dom a hne
    · rw [← h.memaddrs]; exact hb.out_dom a hnc
  · intro a hne
    by_cases hnc : next.memory a = cur.memory a
    · rw [hnc] at hne; exact h.cell_frame a hne
    · obtain ⟨iv, hiv, hpos, hc1, hc2⟩ := hb.cell_frame a hnc
      rcases hsub iv hiv hpos with ⟨j, hj, h1, h2⟩ | ⟨gs, hgs, h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨j, hj, by omega, by omega, by omega⟩
      · exact Or.inr (Or.inl ⟨gs, hgs, by omega, by omega, by omega⟩)
      · exact Or.inr (Or.inr ⟨by dsimp [heapFree]; omega, by dsimp [heapFree]; omega, by dsimp [heapFree]; omega⟩)
  · intro b hb64 hne
    by_cases hnc : memB next b = memB cur b
    · rw [hnc] at hne; exact h.byte_frame b hb64 hne
    · obtain ⟨iv, hiv, hb1, hb2⟩ := hb.byte_frame b hb64 hnc
      rcases hsub iv hiv (by omega) with ⟨j, hj, h1, h2⟩ | ⟨gs, hgs, h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨j, hj, by omega, by omega⟩
      · exact Or.inr (Or.inl ⟨gs, hgs, by omega, by omega⟩)
      · exact Or.inr (Or.inr ⟨by dsimp [heapFree]; omega, by dsimp [heapFree]; omega⟩)

theorem InitEff.to_worldStep {F : Type}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {B : List (String × Nat)} {gw : List String}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hWOK : WorldOK s)
    (hB_ok : ∀ gs ∈ B, gs ∈ globalBuffers ∧ gs.1 ∉ typedRecords.map Prod.fst)
    (hcore_out : ∀ g ∈ coreWorldGlobals, ofString g ∉ gw.map ofString)
    (heff : InitEff s post (R s) B gw) :
    WorldStep R gw stdKeep NoExtra s r post := by
  refine worldStep_master B hB_ok hWOK heff.arena ⟨heff.hp_lo, by rw [heff.sp_eq]⟩
    heff.gw_kept hcore_out heff.fresh_bufs
    (fun a hne => ⟨heff.out_dom a hne, ?_⟩)
    (fun b hb64 hne => ?_)
    (fun _ _ _ _ _ _ _ _ => trivial)
  · rcases heff.cell_frame a hne with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inr h3))
  · rcases heff.byte_frame b hb64 hne with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inr h3))

/-! ## 2. Exact `alloc`, `heap_mark`, `heap_release` behavior -/

theorem lookup_heap_mark :
    originalRuntimeCode.lookup (ofString "heap_mark") =
      some ([], sourceFnBody Guest.Software.guestFn_heap_mark, .one) :=
  lookup_of_guestAst_getElem 8 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_heap_mark) rfl

theorem lookup_heap_release :
    originalRuntimeCode.lookup (ofString "heap_release") =
      some ([(ofString "m", .one)], sourceFnBody Guest.Software.guestFn_heap_release, .one) :=
  lookup_of_guestAst_getElem 9 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_heap_release) rfl

theorem evaluate_call_trap_with_no_resumes {F : Type}
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
  · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h
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
      | exception eid ev =>
        rintro (⟨_, h⟩ | ⟨e', v', h, hne⟩)
        · simp at h
        · simp at h; obtain ⟨rfl, rfl⟩ := h; exact hout.2.2 eid ev hne rfl
      | «break» | «continue» | error | timeOut | finalFfi _ =>
        rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h

theorem evaluate_alloc_body_resumes {F : Type}
    (state : PanSemStateFiniteExact 64 F) (p n : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (hp_lookup : state.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (hres : Resumes (evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_alloc)).1) :
    let out := evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_alloc)
    let q := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    out.1 = some (.returned (.val (.word p))) ∧
    out.2 =
      { state with
        locals := out.2.locals
        globals := state.globals.update (ofString "heap_ptr", .val (.word q))
        clock := out.2.clock } ∧
    ¬ (cMax.toNat < q.toNat) := by
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
  rw [hbody_eq, evaluateHOLFiniteState_dec_total] at hres ⊢
  have hp_eval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.var .global (ofString "heap_ptr")) = some (.val (.word p)) := hp_lookup
  dsimp only at hres ⊢
  rw [hp_eval] at hres ⊢
  have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only at hres ⊢
  rw [if_pos hsh_p] at hres ⊢
  dsimp only at hres ⊢
  let pState := setVarHOLFinite (ofString "p") (.val (.word p)) state
  have hp_loc : pState.locals.lookup (ofString "p") = some (.val (.word p)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hn_loc : pState.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
      show ofString "p" ≠ ofString "n" by decide]
  rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
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
    rw [hite1] at hres
    have hno_none := evaluate_call_trap_with_no_none pState 1 hcode
    have hno_res := evaluate_call_trap_with_no_resumes pState 1 hcode
    rcases htr : evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r1, s1⟩
    rw [htr] at hno_none hno_res hres
    cases r1 with
    | none => exact absurd rfl hno_none
    | some _ => exact False.elim (hno_res hres)
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 1])
          .skip) = (none, pState) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_neg hcmp1]; simp [evaluateHOLFiniteState_skip]
    rw [hite1] at hres ⊢
    dsimp only at hres ⊢
    rw [evaluateHOLFiniteState_dec_total] at hres ⊢
    let q : BitVec 64 := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    have hq_eval : @evalHOLExact 64 F _ pState.toExact
        (fun a => Classical.propDecidable (pState.memaddrs a))
        (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
          .op .sub [.const 0, .const 8]]) = some (.val (.word q)) := by
      simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
        wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
      exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word w))) (alloc_q_word_eq p n)
    dsimp only at hres ⊢
    rw [hq_eval] at hres ⊢
    have hsh_q : shapeEqHOL .one (shapeOfHOLExact (.val (.word q))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    dsimp only at hres ⊢
    rw [if_pos hsh_q] at hres ⊢
    dsimp only at hres ⊢
    let qState := setVarHOLFinite (ofString "q") (.val (.word q)) pState
    have hq_loc : qState.locals.lookup (ofString "q") = some (.val (.word q)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hp_loc_q : qState.locals.lookup (ofString "p") = some (.val (.word p)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_loc,
        show ofString "q" ≠ ofString "p" by decide]
    rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
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
      rw [hite2] at hres
      have hno_none := evaluate_call_trap_with_no_none qState 1 hcode
      have hno_res := evaluate_call_trap_with_no_resumes qState 1 hcode
      rcases htr : evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r2, s2⟩
      rw [htr] at hno_none hno_res hres
      cases r2 with
      | none => exact absurd rfl hno_none
      | some _ => exact False.elim (hno_res hres)
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
      exact ⟨rfl, rfl, hcmp2⟩

theorem alloc_bounds_general (p n : BitVec 64)
    (hp_lt : p.toNat ≤ heapLimit) (hp8 : p.toNat % 8 = 0)
    (hn_hi : n.toNat ≤ 8192)
    (hcmp2 : ¬ (cMax.toNat < ((p + (n + 7)) &&& ((0 : BitVec 64) - 8)).toNat)) :
    let q := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    p.toNat + n.toNat ≤ q.toNat ∧ q.toNat ≤ heapLimit ∧ q.toNat % 8 = 0 ∧ p.toNat % 8 = 0 := by
  intro q
  have hhl : heapLimit = 2952790016 := by decide
  have hcMax : cMax.toNat = 2952790016 := rfl
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
  have hq_eq : q.toNat = (p + (n + 7)).toNat / 8 * 8 := and_neg8_toNat (p + (n + 7))
  have h7 : (7 : BitVec 64).toNat = 7 := rfl
  have hp_isLt := p.isLt; have hn_isLt := n.isLt
  have hn7 : (n + 7).toNat = n.toNat + 7 := BitVec.toNat_add_of_lt (by omega)
  have hsum : (p + (n + 7)).toNat = p.toNat + n.toNat + 7 :=
    by rw [BitVec.toNat_add_of_lt (by rw [hn7]; omega), hn7, Nat.add_assoc]
  have hdiv8 : q.toNat ≥ p.toNat + n.toNat := by
    have hp_div : p.toNat = p.toNat / 8 * 8 := by omega
    rw [hq_eq, hsum, hp_div]
    omega
  have hq_le : q.toNat ≤ heapLimit := by
    have hnot : q.toNat ≤ cMax.toNat := Nat.le_of_not_lt hcmp2
    rwa [hcMax, ← hhl] at hnot
  exact ⟨hdiv8, hq_le, by rw [hq_eq]; omega, hp8⟩

theorem FreshBufsOK.update_fresh {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    (gname : String) (sz : Nat) (pw q : BitVec 64)
    (hfb : FreshBufsOK s cur)
    (hhp_cur : cur.globals.lookup (ofString "heap_ptr") = some (.val (.word pw)))
    (hhp_lo : globN s "heap_ptr" ≤ pw.toNat)
    (hpw8 : pw.toNat % 8 = 0)
    (hq_lo : pw.toNat + sz ≤ q.toNat)
    (hgb_mem : (gname, sz) ∈ globalBuffers)
    (hgn_ne_hp : ofString gname ≠ ofString "heap_ptr") :
    let nextG := HolFiniteMapExact.update
      (HolFiniteMapExact.update cur.globals (ofString "heap_ptr", .val (.word q)))
      (ofString gname, .val (.word pw))
    let next : PanSemStateFiniteExact 64 F := { cur with globals := nextG }
    FreshBufsOK s next := by
  intro nextG next
  have hpw_glob : globN cur "heap_ptr" = pw.toNat := by simp [globN, hhp_cur]
  have hq_glob : globN next "heap_ptr" = q.toNat := by
    have h1 : (ofString gname == ofString "heap_ptr") = false := beq_eq_false_iff_ne.2 hgn_ne_hp
    simp [next, nextG, globN, HolFiniteMapExact.lookup_update, FUPDATE, h1]
  have hg_next : globN next gname = pw.toNat := by
    simp [next, nextG, globN, HolFiniteMapExact.lookup_update, FUPDATE]
  have hother_next : ∀ k : String, ofString k ≠ ofString gname → ofString k ≠ ofString "heap_ptr" →
      globN next k = globN cur k := by
    intro k hk1 hk2
    have h1 : (ofString gname == ofString k) = false := beq_eq_false_iff_ne.2 (Ne.symm hk1)
    have h2 : (ofString "heap_ptr" == ofString k) = false := beq_eq_false_iff_ne.2 (Ne.symm hk2)
    simp [next, nextG, globN, HolFiniteMapExact.lookup_update, FUPDATE, h1, h2]
  have hgb_nd : (globalBuffers.map (fun p => ofString p.1)).Nodup := by decide
  have hgb_uniq : ∀ k n, (k, n) ∈ globalBuffers → ofString k = ofString gname → k = gname ∧ n = sz := by
    intro k n hkn heq
    have : ∀ l : List (String × Nat), (l.map (fun p => ofString p.1)).Nodup →
        ∀ a1 b1 a2 b2, (a1, b1) ∈ l → (a2, b2) ∈ l → ofString a1 = ofString a2 → a1 = a2 ∧ b1 = b2 := by
      intro l hl a1 b1 a2 b2 h1 h2 heqm
      induction l with
      | nil => cases h1
      | cons hd tl ih =>
        simp only [List.map_cons, List.nodup_cons] at hl
        rcases List.mem_cons.1 h1 with rfl | h1' <;> rcases List.mem_cons.1 h2 with h2eq | h2'
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2eq; exact ⟨rfl, rfl⟩
        · exfalso; apply hl.1; rw [heqm]; exact List.mem_map.2 ⟨_, h2', rfl⟩
        · subst h2eq; exfalso; apply hl.1; rw [← heqm]; exact List.mem_map.2 ⟨_, h1', rfl⟩
        · exact ih hl.2 h1' h2'
    exact this globalBuffers hgb_nd k n gname sz hkn hgb_mem heq
  have hgb_not_hp : ∀ k n, (k, n) ∈ globalBuffers → ofString k ≠ ofString "heap_ptr" := by
    have hall : ∀ p ∈ globalBuffers, ofString p.1 ≠ ofString "heap_ptr" := by decide
    exact fun k n hkn => hall (k, n) hkn
  refine ⟨?_, ?_⟩
  · intro ⟨k, n⟩ hkn
    by_cases hkg : ofString k = ofString gname
    · obtain ⟨rfl, rfl⟩ := hgb_uniq k n hkn hkg
      right; right
      rw [hg_next, hq_glob]
      exact ⟨hpw8, hhp_lo, hq_lo⟩
    · rw [hother_next k hkg (hgb_not_hp k n hkn), hq_glob]
      rcases hfb.1 (k, n) hkn with h1 | h2 | ⟨h8, hin1, hin2⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · rw [hpw_glob] at hin2
        exact Or.inr (Or.inr ⟨h8, hin1, by dsimp at hin2 ⊢; omega⟩)
  · rw [List.pairwise_iff_getElem]
    have hpw_old := List.pairwise_iff_getElem.1 hfb.2
    intro i j hi hj hlt ha hb
    let a := globalBuffers[i]
    let b := globalBuffers[j]
    have ha_mem : a ∈ globalBuffers := List.getElem_mem hi
    have hb_mem : b ∈ globalBuffers := List.getElem_mem hj
    have hab_ne : ofString a.1 ≠ ofString b.1 := by
      have hpw_fst := List.pairwise_iff_getElem.1 hgb_nd
      have := hpw_fst i j (by simpa using hi) (by simpa using hj) hlt
      simpa [a, b] using this
    by_cases hag : ofString a.1 = ofString gname
    · obtain ⟨hag_eq, _⟩ := hgb_uniq a.1 a.2 ha_mem hag
      have hbg : ofString b.1 ≠ ofString gname := fun h => hab_ne (hag.trans h.symm)
      have hb_eq := hother_next b.1 hbg (hgb_not_hp b.1 b.2 hb_mem)
      rcases hfb.1 b hb_mem with h1 | h2 | ⟨_, _, hin_b2⟩
      · rw [hb_eq] at hb; exact absurd h1 hb.1
      · rw [hb_eq] at hb; exact absurd h2 hb.2
      · rw [hpw_glob] at hin_b2
        right; right; right
        dsimp at hin_b2 ⊢
        rw [hb_eq, hag_eq, hg_next]
        exact hin_b2
    · by_cases hbg : ofString b.1 = ofString gname
      · obtain ⟨hbg_eq, _⟩ := hgb_uniq b.1 b.2 hb_mem hbg
        have ha_eq := hother_next a.1 hag (hgb_not_hp a.1 a.2 ha_mem)
        rcases hfb.1 a ha_mem with h1 | h2 | ⟨_, _, hin_a2⟩
        · rw [ha_eq] at ha; exact absurd h1 ha.1
        · rw [ha_eq] at ha; exact absurd h2 ha.2
        · rw [hpw_glob] at hin_a2
          right; right; left
          dsimp at hin_a2 ⊢
          rw [ha_eq, hbg_eq, hg_next]
          exact hin_a2
      · have ha_eq := hother_next a.1 hag (hgb_not_hp a.1 a.2 ha_mem)
        have hb_eq := hother_next b.1 hbg (hgb_not_hp b.1 b.2 hb_mem)
        rw [ha_eq] at ha ⊢
        rw [hb_eq] at hb ⊢
        exact hpw_old i j hi hj hlt ha hb

theorem step_call_alloc_global {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (gname : String) (sz : Nat) (szExp : ExpHOL 64)
    (heff : InitEff s cur Rl B gw)
    (hsz_bound : 0 < sz ∧ sz ≤ 8192)
    (hsz_ev : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) szExp =
      some (.val (.word (BitVec.ofNat 64 sz))))
    (hgb_mem : (gname, sz) ∈ globalBuffers)
    (hgw_hp : ofString "heap_ptr" ∈ gw.map ofString)
    (hgw_mem : ofString gname ∈ gw.map ofString)
    (hnt : (evaluateHOLFiniteState cur
      (.call (some (some (.global, ofString gname), none)) (ofString "alloc") [szExp])).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState cur
      (.call (some (some (.global, ofString gname), none)) (ofString "alloc") [szExp])).1 = none ∨
      Resumes (evaluateHOLFiniteState cur
        (.call (some (some (.global, ofString gname), none)) (ofString "alloc") [szExp])).1) :
    let out := evaluateHOLFiniteState cur
      (.call (some (some (.global, ofString gname), none)) (ofString "alloc") [szExp])
    out.1 = none ∧
    out.2.locals = cur.locals ∧
    InitEff s out.2 Rl B gw ∧
    (∀ k : MlS, k ≠ ofString gname → k ≠ ofString "heap_ptr" →
      out.2.globals.lookup k = cur.globals.lookup k) ∧
    ∃ pw : BitVec 64,
      out.2.globals.lookup (ofString gname) = some (.val (.word pw)) ∧
      pw.toNat % 8 = 0 ∧
      globN s "heap_ptr" ≤ pw.toNat ∧
      pw.toNat + sz ≤ globN out.2 "heap_ptr" := by
  dsimp only
  obtain ⟨pw, hpw⟩ := heff.hp_word
  have hgn_ne_hp : ofString gname ≠ ofString "heap_ptr" :=
    (by decide : ∀ p ∈ globalBuffers, ofString p.1 ≠ ofString "heap_ptr") (gname, sz) hgb_mem
  have hgn_ne_fmp : ofString gname ≠ ofString "frame_mem_ptr" :=
    (by decide : ∀ p ∈ globalBuffers, ofString p.1 ≠ ofString "frame_mem_ptr") (gname, sz) hgb_mem
  have hgn_ne_sp : ofString gname ≠ ofString "scratch_ptr" :=
    (by decide : ∀ p ∈ globalBuffers, ofString p.1 ≠ ofString "scratch_ptr") (gname, sz) hgb_mem
  have hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) [szExp] =
      some [.val (.word (BitVec.ofNat 64 sz))] := by
    simp [evalListHOLFinite, evalListHOLExact, hsz_ev]
  have hl_al := pan_one_word_lookup cur.code.lookup (ofString "alloc") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_alloc) (BitVec.ofNat 64 sz)
    (by rw [heff.code]; exact lookup_alloc)
  rw [evaluateHOLFiniteState_call, hargs] at hnt hor ⊢
  dsimp only at hnt hor ⊢
  rw [hl_al] at hnt hor ⊢
  dsimp only at hnt hor ⊢
  by_cases hclk : cur.clock = 0
  · rw [if_pos hclk] at hnt; exact absurd rfl hnt
  · rw [if_neg hclk] at hnt hor ⊢
    let entry := callEntryStateHOLFinite cur
      (HolFiniteMapExact.empty.update (ofString "n", .val (.word (BitVec.ofNat 64 sz))))
    have hres_entry : Resumes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_alloc)).1 := by
      rcases hb : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_alloc) with ⟨rb, pb⟩
      dsimp only [entry] at hb
      rw [hb] at hor
      cases rb with
      | none => rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      | some rb' =>
        cases rb' with
        | returned rv => exact Or.inl ⟨rv, rfl⟩
        | exception eid ev =>
          rcases hor with h | ⟨_, h⟩ | ⟨e', v', h, hne_t⟩
          · simp at h
          · simp at h
          · simp at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨eid, ev, rfl, hne_t⟩
        | _ => rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
    have hal := evaluate_alloc_body_resumes entry pw (BitVec.ofNat 64 sz) heff.code hpw
      (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      hres_entry
    dsimp only at hal
    rcases hb : evaluateHOLFiniteState
        (callEntryStateHOLFinite cur (HolFiniteMapExact.empty.update (ofString "n", .val (.word (BitVec.ofNat 64 sz)))))
        (sourceFnBody Guest.Software.guestFn_alloc) with ⟨rb, pb⟩
    dsimp only [entry] at hal
    have hor' := hor
    rw [hb] at hal hor'
    obtain ⟨rfl, hpb_eq, hcmp2⟩ := hal
    dsimp only at hpb_eq hor' ⊢
    have hsh_ok : shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hsh_ok] at hor' ⊢
    by_cases hvalid : isValidValueHOLExact cur.toExact .global (ofString gname) (.val (.word pw)) = true
    · rw [if_pos hvalid]
      let q := (pw + (BitVec.ofNat 64 sz + 7)) &&& ((0 : BitVec 64) - 8)
      have hpw_glob : globN cur "heap_ptr" = pw.toNat := by simp [globN, hpw]
      have hsz_toNat : (BitVec.ofNat 64 sz).toNat = sz := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hbnds := alloc_bounds_general pw (BitVec.ofNat 64 sz)
        (by rw [← hpw_glob]; exact heff.arena.2.2.1)
        (by rw [← hpw_glob]; exact heff.arena.2.2.2.2.2.2.1)
        (by rw [hsz_toNat]; exact hsz_bound.2) hcmp2
      dsimp only at hbnds
      rw [hsz_toNat] at hbnds
      let post0 : PanSemStateFiniteExact 64 F :=
        { locals := cur.locals, globals := pb.globals, structs := pb.structs, code := pb.code,
          eshapes := pb.eshapes, memory := pb.memory, memaddrs := pb.memaddrs, shMemaddrs := pb.shMemaddrs,
          clock := pb.clock, be := pb.be, ffi := pb.ffi, baseAddr := pb.baseAddr, topAddr := pb.topAddr }
      let outSt := setKvarHOLFinite .global (ofString gname) (.val (.word pw)) post0
      let newGlobals := HolFiniteMapExact.update
        (HolFiniteMapExact.update cur.globals (ofString "heap_ptr", .val (.word q)))
        (ofString gname, .val (.word pw))
      have hout_eq : outSt = { cur with globals := newGlobals, clock := pb.clock } := by
        dsimp only [outSt, post0, setKvarHOLFinite, setGlobalHOLFinite, newGlobals]
        rw [hpb_eq]
        rfl
      change (none, outSt).1 = none ∧ outSt.locals = cur.locals ∧ InitEff s outSt Rl B gw ∧
        (∀ k : MlS, k ≠ ofString gname → k ≠ ofString "heap_ptr" →
          outSt.globals.lookup k = cur.globals.lookup k) ∧
        ∃ pw' : BitVec 64,
          outSt.globals.lookup (ofString gname) = some (.val (.word pw')) ∧
          pw'.toNat % 8 = 0 ∧
          globN s "heap_ptr" ≤ pw'.toNat ∧
          pw'.toNat + sz ≤ globN outSt "heap_ptr"
      rw [hout_eq]
      have hfmp_out : globN { cur with globals := newGlobals, clock := pb.clock } "frame_mem_ptr" =
          globN cur "frame_mem_ptr" := by
        have h1 : (ofString gname == ofString "frame_mem_ptr") = false := beq_eq_false_iff_ne.2 hgn_ne_fmp
        have h2 : (ofString "heap_ptr" == ofString "frame_mem_ptr") = false := by decide
        simp [newGlobals, globN, HolFiniteMapExact.lookup_update, FUPDATE, h1, h2]
      have hsp_out : globN { cur with globals := newGlobals, clock := pb.clock } "scratch_ptr" =
          globN cur "scratch_ptr" := by
        have h1 : (ofString gname == ofString "scratch_ptr") = false := beq_eq_false_iff_ne.2 hgn_ne_sp
        have h2 : (ofString "heap_ptr" == ofString "scratch_ptr") = false := by decide
        simp [newGlobals, globN, HolFiniteMapExact.lookup_update, FUPDATE, h1, h2]
      have hhp_out_lookup : newGlobals.lookup (ofString "heap_ptr") = some (.val (.word q)) := by
        have h1 : (ofString gname == ofString "heap_ptr") = false := beq_eq_false_iff_ne.2 hgn_ne_hp
        simp [newGlobals, HolFiniteMapExact.lookup_update, FUPDATE, h1]
      have hhp_out : globN { cur with globals := newGlobals, clock := pb.clock } "heap_ptr" = q.toNat := by
        simp [globN, hhp_out_lookup]
      have hq_ge_pw : pw.toNat ≤ q.toNat := le_trans (Nat.le_add_right _ _) hbnds.1
      refine ⟨rfl, rfl, ?_, ?_, pw, ?_, hbnds.2.2.2, by rw [← hpw_glob]; exact heff.hp_lo,
        by rw [hhp_out]; exact hbnds.1⟩
      · refine ⟨⟨guestInv_congr (s := cur) rfl rfl rfl rfl heff.arena.1, ?_⟩,
          heff.code, heff.memaddrs, heff.be, heff.eshapes,
          ⟨q, hhp_out_lookup⟩, ?_, hfmp_out.trans heff.fmp_eq, hsp_out.trans heff.sp_eq,
          ?_, ?_, heff.out_dom, heff.cell_frame, heff.byte_frame⟩
        · obtain ⟨ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8⟩ := heff.arena.2
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hhp_out]; rw [hpw_glob] at ha1; exact le_trans ha1 hq_ge_pw
          · rw [hhp_out]; exact hbnds.2.1
          · rw [hfmp_out]; exact ha3
          · rw [hfmp_out, hsp_out]; exact ha4
          · rw [hsp_out]; exact ha5
          · rw [hhp_out]; exact hbnds.2.2.1
          · rw [hfmp_out]; exact ha7
          · rw [hsp_out]; exact ha8
        · rw [hhp_out]; have := heff.hp_lo; rw [hpw_glob] at this; exact le_trans this hq_ge_pw
        · intro k hk
          have hk_ne_gn : (ofString gname == k) = false :=
            beq_eq_false_iff_ne.2 (fun h => hk (by subst h; exact hgw_mem))
          have hk_ne_hp : (ofString "heap_ptr" == k) = false :=
            beq_eq_false_iff_ne.2 (fun h => hk (by subst h; exact hgw_hp))
          simp only [newGlobals, HolFiniteMapExact.lookup_update, FUPDATE, hk_ne_gn, hk_ne_hp,
            Bool.false_eq_true, ↓reduceIte]
          exact heff.gw_kept k hk
        · have hfb' := FreshBufsOK.update_fresh gname sz pw q heff.fresh_bufs hpw
            (by rw [← hpw_glob]; exact heff.hp_lo) hbnds.2.2.2 hbnds.1 hgb_mem hgn_ne_hp
          simpa [FreshBufsOK, globN, newGlobals] using hfb'
      · intro k hk1 hk2
        have h1 : (ofString gname == k) = false := beq_eq_false_iff_ne.2 (Ne.symm hk1)
        have h2 : (ofString "heap_ptr" == k) = false := beq_eq_false_iff_ne.2 (Ne.symm hk2)
        simp [newGlobals, HolFiniteMapExact.lookup_update, FUPDATE, h1, h2]
      · simp [newGlobals, HolFiniteMapExact.lookup_update, FUPDATE]
    · exfalso
      rw [if_neg hvalid] at hor'
      rcases hor' with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h

/-! ## 3. Declarative Global-Buffer Constant-Store Checker & Combinators -/

/-- Check that `prog` is a tree of `.seq`, `.skip`, `.return`, `.store`, `.storeByte` writing only
to `G:gname + off` within `[0, sz)` (`sz ≤ 8192`) using constant words or 4-word `rStruct`s of
constants. Covers `bls_consts_init` (892 stores), `bls_precompiles_init` (256 stores),
`ssz_init` (256 stores), `bn254_init` (`rStruct` + word stores), `keccak_init`, `ripemd160_init`,
`blake2_init`, etc. in O(1) kernel reduction! -/
def isConstWordList : List (ExpHOL 64) → Bool
  | [] => true
  | .const _ :: rest => isConstWordList rest
  | _ => false

def checkGlobalConstStores (gname : MlS) (sz : Nat) : ProgHOL 64 → Bool
  | .seq a b => checkGlobalConstStores gname sz a && checkGlobalConstStores gname sz b
  | .skip | .return _ => true
  | .store (.var .global nm) (.const _) => (nm == gname) && decide (8 ≤ sz)
  | .store (.op .add [.var .global nm, .const off]) (.const _) =>
      (nm == gname) && decide (off.toNat + 8 ≤ sz)
  | .store (.var .global nm) (.rstruct es) =>
      (nm == gname) && isConstWordList es && decide (8 * es.length ≤ sz)
  | .store (.op .add [.var .global nm, .const off]) (.rstruct es) =>
      (nm == gname) && isConstWordList es && decide (off.toNat + 8 * es.length ≤ sz)
  | .storeByte (.var .global nm) (.const _) => (nm == gname) && decide (1 ≤ sz)
  | .storeByte (.op .add [.var .global nm, .const off]) (.const _) =>
      (nm == gname) && decide (off.toNat < sz)
  | _ => false

private theorem evalList_constWordList {F : Type} (s : PanSemStateFiniteExact 64 F) :
    ∀ (es : List (ExpHOL 64)), isConstWordList es = true →
      ∃ ws : List (HolWordLab 64),
        @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) es =
          some (ws.map ValueHOL.val) ∧
        ws.length = es.length
  | [], _ => ⟨[], rfl, rfl⟩
  | e :: rest, h => by
    cases e with
    | const c =>
      have hr : isConstWordList rest = true := by simpa [isConstWordList] using h
      obtain ⟨ws, hws, hlen⟩ := evalList_constWordList s rest hr
      refine ⟨.word c :: ws, ?_, by simp [hlen]⟩
      simp [evalListHOLExact, evalHOLExact, hws]
    | _ => simp [isConstWordList] at h

private theorem flattenHOL_vals :
    ∀ (ws : List (HolWordLab 64)), flattenHOL (.rStruct (ws.map ValueHOL.val)) = ws
  | [] => by simp [flattenHOL]
  | w :: rest => by
    have ih := flattenHOL_vals rest
    simp only [flattenHOL, List.map_cons, List.flatten_cons] at ih ⊢
    rw [ih]; simp [flattenHOL]

private theorem panMemStores_eff
    (dom : BitVec 64 → Prop) [DecidablePred dom] (be : Bool)
    (hdom_ord : dom = ordinaryDomain) :
    ∀ (ws : List (HolWordLab 64)) (addr : BitVec 64)
      (mem mem' : BitVec 64 → HolWordLab 64),
      addr.toNat + 8 * ws.length < 2 ^ 64 →
      panMemStoresHOL addr ws dom mem = some mem' →
      (∀ x : BitVec 64, mem' x ≠ mem x →
        dom x ∧ addr.toNat ≤ x.toNat ∧ x.toNat + 8 ≤ addr.toNat + 8 * ws.length) ∧
      (∀ b : Nat, b < 2 ^ 64 →
        (memByteAt mem' be (BitVec.ofNat 64 b)).toNat ≠ (memByteAt mem be (BitVec.ofNat 64 b)).toNat →
        addr.toNat ≤ b ∧ b < addr.toNat + 8 * ws.length)
  | [], _, mem, mem', _, hst => by
    simp [panMemStoresHOL] at hst; subst hst
    exact ⟨fun _ h => absurd rfl h, fun _ _ h => absurd rfl h⟩
  | w :: rest, addr, mem, mem', hlt, hst => by
    simp only [panMemStoresHOL, panMemStoreHOL] at hst
    by_cases hd : dom addr
    · simp only [hd, ↓reduceIte] at hst
      have hbw : (panBytesInWord 64 : BitVec 64).toNat = 8 := rfl
      have hnext_add : (addr + panBytesInWord 64).toNat = addr.toNat + 8 := by
        apply BitVec.toNat_add_of_lt
        rw [hbw]; simp [List.length_cons] at hlt; omega
      have hlt_rest : (addr + panBytesInWord 64).toNat + 8 * rest.length < 2 ^ 64 := by
        rw [hnext_add]; simp [List.length_cons] at hlt; omega
      let mid := fun current => if current = addr then w else mem current
      obtain ⟨ih_c, ih_b⟩ := panMemStores_eff dom be hdom_ord rest (addr + panBytesInWord 64) mid mem' hlt_rest hst
      have hd_ord : addr.toNat % 8 = 0 := by
        rw [hdom_ord, ordinaryDomain_iff] at hd; exact hd.1
      refine ⟨?_, ?_⟩
      · intro x hne
        by_cases hxm : mem' x = mid x
        · rw [hxm] at hne
          by_cases hxa : x = addr
          · subst hxa; simp only [List.length_cons]; exact ⟨hd, le_rfl, by omega⟩
          · simp [mid, hxa] at hne
        · obtain ⟨hdx, hx1, hx2⟩ := ih_c x hxm
          rw [hnext_add] at hx1 hx2
          simp only [List.length_cons]; exact ⟨hdx, by omega, by omega⟩
      · intro b hb64 hne
        by_cases hbm : (memByteAt mem' be (BitVec.ofNat 64 b)).toNat =
            (memByteAt mid be (BitVec.ofNat 64 b)).toNat
        · rw [hbm] at hne
          by_cases hal : panByteAlignHOL (BitVec.ofNat 64 b) = addr
          · have hc_nat := panByteAlign_toNat64 (BitVec.ofNat 64 b)
            rw [hal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb64] at hc_nat
            simp only [List.length_cons]; omega
          · unfold memByteAt memWordAt at hne; simp [mid, hal] at hne
        · obtain ⟨hb1, hb2⟩ := ih_b b hb64 hbm
          rw [hnext_add] at hb1 hb2
          simp only [List.length_cons]; omega
    · simp [hd] at hst

private theorem byteEff_store_rstruct_at {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hG : GuestInv s) (dstExp : ExpHOL 64) (es : List (ExpHOL 64))
    (base : BitVec 64) (off sz : Nat)
    (hcw : isConstWordList es = true)
    (hbase_hi : base.toNat + sz ≤ heapEnd)
    (hoff : off + 8 * es.length ≤ sz)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word (base + BitVec.ofNat 64 off)))) :
    ByteEff s (evaluateHOLFiniteState s (.store dstExp (.rstruct es))).2 [(base.toNat, sz)] := by
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  rw [evaluateHOLFiniteState_store]
  rw [hdst]
  dsimp only
  obtain ⟨ws, hws, hlen⟩ := evalList_constWordList s es hcw
  have hrst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.rstruct es) =
      some (.rStruct (ws.map ValueHOL.val)) := by
    simp [evalHOLExact, hws]
  rw [hrst]; dsimp only
  rw [flattenHOL_vals ws]
  split
  · rename_i mem' hmem
    have hadd : (base + BitVec.ofNat 64 off).toNat = base.toNat + off := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hlt : (base + BitVec.ofNat 64 off).toNat + 8 * ws.length < 2 ^ 64 := by omega
    obtain ⟨hc, hb⟩ := @panMemStores_eff s.memaddrs (fun a => Classical.propDecidable (s.memaddrs a))
      s.be hG.memaddrs ws (base + BitVec.ofNat 64 off) s.memory mem' hlt hmem
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      fun a hne => (hc a hne).1,
      fun a hne => ?_,
      fun b hb64 hne => ?_⟩
    · obtain ⟨_, h1, h2⟩ := hc a hne
      exact ⟨(base.toNat, sz), List.mem_singleton.2 rfl, by omega, by omega, by omega⟩
    · rw [memB_eq_memByteAt, memB_eq_memByteAt] at hne
      obtain ⟨h1, h2⟩ := hb b hb64 hne
      exact ⟨(base.toNat, sz), List.mem_singleton.2 rfl, by omega, by omega⟩
  · exact ByteEff.refl s _

theorem checkGlobalConstStores_sound {F : Type} (gname : MlS) (sz : Nat) (hsz : sz ≤ 8192)
    (prog : ProgHOL 64) (hok : checkGlobalConstStores gname sz prog = true)
    (s : PanSemStateFiniteExact 64 F) (p : BitVec 64)
    (hG : GuestInv s) (hp_hi : p.toNat + sz ≤ heapEnd)
    (hp : s.globals.lookup gname = some (.val (.word p))) :
    ByteEff s (evaluateHOLFiniteState s prog).2 [(p.toNat, sz)] := by
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  cases shape : prog with
  | seq a b =>
    have h12 : checkGlobalConstStores gname sz a = true ∧ checkGlobalConstStores gname sz b = true := by
      simpa [shape, checkGlobalConstStores, Bool.and_eq_true] using hok
    have effa := checkGlobalConstStores_sound gname sz hsz a h12.1 s p hG hp_hi hp
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hra : evaluateHOLFiniteState s a with ⟨r1, m⟩
    rw [hra] at effa
    cases r1 with
    | some _ => exact effa
    | none =>
      have hGm := guestInv_congr effa.code effa.memaddrs effa.shMemaddrs effa.baseAddr hG
      have hpm : m.globals.lookup gname = some (.val (.word p)) := by rw [effa.globals]; exact hp
      exact effa.trans (checkGlobalConstStores_sound gname sz hsz b h12.2 m p hGm hp_hi hpm)
  | skip => exact byteEff_skip s _
  | «return» e => exact byteEff_return s e _
  | store dst vexp =>
    have hin_sz : 0 < sz → ∃ i ∈ [(p.toNat, sz)], i.1 ≤ p.toNat ∧ p.toNat + sz ≤ i.1 + i.2 :=
      fun _ => ⟨(p.toNat, sz), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩
    cases dst with
    | var vk nm =>
      cases vk with
      | «local» => simp [shape, checkGlobalConstStores] at hok
      | global =>
        cases vexp with
        | const c =>
          have h12 : nm = gname ∧ 8 ≤ sz := by
            simpa [shape, checkGlobalConstStores, Bool.and_eq_true] using hok
          rcases h12 with ⟨rfl, h8⟩
          exact byteEff_store_at hG _ _ p 0 sz hp_hi hin_sz
            (fun _ hv => by simp [evalHOLExact] at hv; exact ⟨c, hv.symm⟩) h8
            (by simpa [BitVec.add_zero, evalHOLExact] using hp)
        | rstruct es =>
          have h123 : (nm = gname ∧ isConstWordList es = true) ∧ 8 * es.length ≤ sz := by
            simpa [shape, checkGlobalConstStores, Bool.and_eq_true] using hok
          rcases h123 with ⟨⟨rfl, hcw⟩, hlen⟩
          exact byteEff_store_rstruct_at hG _ es p 0 sz hcw hp_hi (by omega)
            (by simpa [BitVec.add_zero, evalHOLExact] using hp)
        | _ => simp [shape, checkGlobalConstStores] at hok
    | op bop args =>
      cases bop <;> try (simp [shape, checkGlobalConstStores] at hok)
      rcases args with _ | ⟨e1, _ | ⟨e2, _ | _⟩⟩ <;> try (simp [shape, checkGlobalConstStores] at hok)
      cases e1 with
      | var vk1 nm1 =>
        cases vk1 <;> try (simp [shape, checkGlobalConstStores] at hok)
        cases e2 with
        | const off =>
          have hoff_eq : BitVec.ofNat 64 off.toNat = off := BitVec.eq_of_toNat_eq (by simp)
          cases vexp with
          | const c =>
            have h12 : nm1 = gname ∧ off.toNat + 8 ≤ sz := by
              simpa [shape, checkGlobalConstStores, Bool.and_eq_true] using hok
            rcases h12 with ⟨rfl, hoff⟩
            refine byteEff_store_at hG _ _ p off.toNat sz hp_hi hin_sz
              (fun _ hv => by simp [evalHOLExact] at hv; exact ⟨c, hv.symm⟩) hoff ?_
            simp [evalHOLExact, evalListHOLExact, hp, valueIsWord, valueWord, wordOpHOL, wordOp, hoff_eq]
          | rstruct es =>
            have h123 : (nm1 = gname ∧ isConstWordList es = true) ∧ off.toNat + 8 * es.length ≤ sz := by
              simpa [shape, checkGlobalConstStores, Bool.and_eq_true] using hok
            rcases h123 with ⟨⟨rfl, hcw⟩, hoff⟩
            refine byteEff_store_rstruct_at hG _ es p off.toNat sz hcw hp_hi hoff ?_
            simp [evalHOLExact, evalListHOLExact, hp, valueIsWord, valueWord, wordOpHOL, wordOp, hoff_eq]
          | _ => simp [shape, checkGlobalConstStores] at hok
        | _ => simp [shape, checkGlobalConstStores] at hok
      | _ => simp [shape, checkGlobalConstStores] at hok
    | _ => simp [shape, checkGlobalConstStores] at hok
  | storeByte dst vexp =>
    have hin_sz : 0 < sz → ∃ i ∈ [(p.toNat, sz)], i.1 ≤ p.toNat ∧ p.toNat + sz ≤ i.1 + i.2 :=
      fun _ => ⟨(p.toNat, sz), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩
    cases dst with
    | var vk nm =>
      cases vk with
      | «local» => simp [shape, checkGlobalConstStores] at hok
      | global =>
        cases vexp with
        | const c =>
          have h12 : nm = gname ∧ 1 ≤ sz := by
            simpa [shape, checkGlobalConstStores, Bool.and_eq_true] using hok
          rcases h12 with ⟨rfl, h1⟩
          exact byteEff_storeByte_at hG _ _ p 0 sz hp_hi hin_sz h1
            (by simpa [BitVec.add_zero, evalHOLExact] using hp)
        | _ => simp [shape, checkGlobalConstStores] at hok
    | op bop args =>
      cases bop <;> try (simp [shape, checkGlobalConstStores] at hok)
      rcases args with _ | ⟨e1, _ | ⟨e2, _ | _⟩⟩ <;> try (simp [shape, checkGlobalConstStores] at hok)
      cases e1 with
      | var vk1 nm1 =>
        cases vk1 <;> try (simp [shape, checkGlobalConstStores] at hok)
        cases e2 with
        | const off =>
          have hoff_eq : BitVec.ofNat 64 off.toNat = off := BitVec.eq_of_toNat_eq (by simp)
          cases vexp with
          | const c =>
            have h12 : nm1 = gname ∧ off.toNat < sz := by
              simpa [shape, checkGlobalConstStores, Bool.and_eq_true] using hok
            rcases h12 with ⟨rfl, hoff⟩
            refine byteEff_storeByte_at hG _ _ p off.toNat sz hp_hi hin_sz hoff ?_
            simp [evalHOLExact, evalListHOLExact, hp, valueIsWord, valueWord, wordOpHOL, wordOp, hoff_eq]
          | _ => simp [shape, checkGlobalConstStores] at hok
        | _ => simp [shape, checkGlobalConstStores] at hok
      | _ => simp [shape, checkGlobalConstStores] at hok
    | _ => simp [shape, checkGlobalConstStores] at hok
  | _ => simp [shape, checkGlobalConstStores] at hok
termination_by sizeOf prog
decreasing_by
  all_goals
    subst shape
    simp_wf
    try omega

/-! ## 4. `InitEff` Statement Combinators & First 10 Init `wk_*` Proofs -/

theorem seq_nt_or {F : Type} (cur : PanSemStateFiniteExact 64 F) (a b : ProgHOL 64)
    (hnt : (evaluateHOLFiniteState cur (.seq a b)).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState cur (.seq a b)).1 = none ∨
      Resumes (evaluateHOLFiniteState cur (.seq a b)).1) :
    (evaluateHOLFiniteState cur a).1 ≠ some .timeOut ∧
    ((evaluateHOLFiniteState cur a).1 = none ∨ Resumes (evaluateHOLFiniteState cur a).1) := by
  rw [evaluateHOLFiniteState_seq_line780] at hnt hor
  rcases ha : evaluateHOLFiniteState cur a with ⟨ra, ma⟩
  rw [ha] at hnt hor
  refine ⟨fun h => by subst h; simp at hnt, ?_⟩
  cases ra with
  | none => exact Or.inl rfl
  | some _ =>
    right
    rcases hor with h | h
    · simp at h
    · exact h

theorem initEff_seq {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    {a b : ProgHOL 64}
    (hnt : (evaluateHOLFiniteState cur (.seq a b)).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState cur (.seq a b)).1 = none ∨
      Resumes (evaluateHOLFiniteState cur (.seq a b)).1)
    (ha : (evaluateHOLFiniteState cur a).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState cur a).1 = none ∨ Resumes (evaluateHOLFiniteState cur a).1) →
      InitEff s (evaluateHOLFiniteState cur a).2 Rl B gw)
    (hb : ∀ mid, evaluateHOLFiniteState cur a = (none, mid) →
      InitEff s mid Rl B gw →
      (evaluateHOLFiniteState mid b).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState mid b).1 = none ∨ Resumes (evaluateHOLFiniteState mid b).1) →
      InitEff s (evaluateHOLFiniteState mid b).2 Rl B gw) :
    InitEff s (evaluateHOLFiniteState cur (.seq a b)).2 Rl B gw := by
  obtain ⟨hnt_a, hor_a⟩ := seq_nt_or cur a b hnt hor
  have effa := ha hnt_a hor_a
  rw [evaluateHOLFiniteState_seq_line780] at hnt hor ⊢
  rcases hra : evaluateHOLFiniteState cur a with ⟨ra, mid⟩
  rw [hra] at hnt hor effa
  cases ra with
  | some _ => exact effa
  | none => exact hb mid hra effa hnt hor

theorem initEff_ite {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (cond : ExpHOL 64) {yes no : ProgHOL 64}
    (heff : InitEff s cur Rl B gw)
    (hnt : (evaluateHOLFiniteState cur (.ite cond yes no)).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState cur (.ite cond yes no)).1 = none ∨
      Resumes (evaluateHOLFiniteState cur (.ite cond yes no)).1)
    (hy : (evaluateHOLFiniteState cur yes).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState cur yes).1 = none ∨ Resumes (evaluateHOLFiniteState cur yes).1) →
      InitEff s (evaluateHOLFiniteState cur yes).2 Rl B gw)
    (hn : (evaluateHOLFiniteState cur no).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState cur no).1 = none ∨ Resumes (evaluateHOLFiniteState cur no).1) →
      InitEff s (evaluateHOLFiniteState cur no).2 Rl B gw) :
    InitEff s (evaluateHOLFiniteState cur (.ite cond yes no)).2 Rl B gw := by
  rw [evaluateHOLFiniteState_ite] at hnt hor ⊢
  rcases hc : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) cond with _ | cv
  · exact heff
  · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try exact heff
    rw [hc] at hnt hor
    dsimp only at hnt hor ⊢
    by_cases h0 : cw = 0
    · rw [if_pos h0] at hnt hor ⊢; exact hn hnt hor
    · rw [if_neg h0] at hnt hor ⊢; exact hy hnt hor

theorem initEff_return {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (e : ExpHOL 64) (heff : InitEff s cur Rl B gw) :
    InitEff s (evaluateHOLFiniteState cur (.return e)).2 Rl B gw := by
  rw [evaluateHOLFiniteState_return]
  split
  · exact heff
  · split
    · exact heff.locals_clock _ cur.clock
    · exact heff

theorem initEff_skip {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (heff : InitEff s cur Rl B gw) :
    InitEff s (evaluateHOLFiniteState cur .skip).2 Rl B gw := by
  rw [evaluateHOLFiniteState_skip]; exact heff

theorem initEff_seq_alloc_global {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (gname : String) (sz : Nat) (szExp : ExpHOL 64) {rest : ProgHOL 64}
    (heff : InitEff s cur Rl B gw)
    (hsz_bound : 0 < sz ∧ sz ≤ 8192)
    (hsz_ev : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) szExp =
      some (.val (.word (BitVec.ofNat 64 sz))))
    (hgb_mem : (gname, sz) ∈ globalBuffers)
    (hgw_hp : ofString "heap_ptr" ∈ gw.map ofString)
    (hgw_mem : ofString gname ∈ gw.map ofString)
    (hnt : (evaluateHOLFiniteState cur
      (.seq (.call (some (some (.global, ofString gname), none)) (ofString "alloc") [szExp]) rest)).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState cur
      (.seq (.call (some (some (.global, ofString gname), none)) (ofString "alloc") [szExp]) rest)).1 = none ∨
      Resumes (evaluateHOLFiniteState cur
        (.seq (.call (some (some (.global, ofString gname), none)) (ofString "alloc") [szExp]) rest)).1)
    (hrest : ∀ (mid : PanSemStateFiniteExact 64 F) (pw : BitVec 64),
      mid.locals = cur.locals →
      (∀ k : MlS, k ≠ ofString gname → k ≠ ofString "heap_ptr" →
        mid.globals.lookup k = cur.globals.lookup k) →
      InitEff s mid Rl B gw →
      mid.globals.lookup (ofString gname) = some (.val (.word pw)) →
      pw.toNat % 8 = 0 →
      globN s "heap_ptr" ≤ pw.toNat →
      pw.toNat + sz ≤ globN mid "heap_ptr" →
      (evaluateHOLFiniteState mid rest).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState mid rest).1 = none ∨ Resumes (evaluateHOLFiniteState mid rest).1) →
      InitEff s (evaluateHOLFiniteState mid rest).2 Rl B gw) :
    InitEff s (evaluateHOLFiniteState cur
      (.seq (.call (some (some (.global, ofString gname), none)) (ofString "alloc") [szExp]) rest)).2 Rl B gw := by
  obtain ⟨hnt1, hor1⟩ := seq_nt_or cur _ rest hnt hor
  obtain ⟨hnone, hloc, heff1, hg_keep, pw, hpw_g, hpw8, hpw_lo, hpw_hi⟩ :=
    step_call_alloc_global gname sz szExp heff hsz_bound hsz_ev hgb_mem hgw_hp hgw_mem hnt1 hor1
  rw [evaluateHOLFiniteState_seq_line780] at hnt hor ⊢
  rcases hc : evaluateHOLFiniteState cur
      (.call (some (some (.global, ofString gname), none)) (ofString "alloc") [szExp]) with ⟨r1, mid⟩
  rw [hc] at hnone hloc heff1 hg_keep hpw_g hpw_hi hnt hor
  subst hnone
  exact hrest mid pw hloc hg_keep heff1 hpw_g hpw8 hpw_lo hpw_hi hnt hor

theorem initEff_fresh_constStores {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (gname : String) (sz : Nat) (pw : BitVec 64) (prog : ProgHOL 64)
    (heff : InitEff s cur Rl B gw)
    (hsz : sz ≤ 8192)
    (hok : checkGlobalConstStores (ofString gname) sz prog = true)
    (hpw_g : cur.globals.lookup (ofString gname) = some (.val (.word pw)))
    (hpw_lo : globN s "heap_ptr" ≤ pw.toNat)
    (hpw_hi : pw.toNat + sz ≤ heapLimit) :
    InitEff s (evaluateHOLFiniteState cur prog).2 Rl B gw ∧
    (evaluateHOLFiniteState cur prog).2.globals = cur.globals := by
  have hhl_he : heapLimit ≤ heapEnd := by decide
  have hb := checkGlobalConstStores_sound (ofString gname) sz hsz prog hok cur pw
    heff.arena.1 (le_trans hpw_hi hhl_he) hpw_g
  refine ⟨heff.of_byteEff hb (fun iv hiv _ => ?_), hb.globals⟩
  simp at hiv; subst hiv
  exact Or.inr (Or.inr ⟨hpw_lo, hpw_hi⟩)

theorem evaluate_seq_assoc {F : Type} (s : PanSemStateFiniteExact 64 F) (a b c : ProgHOL 64) :
    evaluateHOLFiniteState s (.seq (.seq a b) c) = evaluateHOLFiniteState s (.seq a (.seq b c)) := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_seq_line780,
      evaluateHOLFiniteState_seq_line780]
  rcases evaluateHOLFiniteState s a with ⟨ra, ma⟩
  cases ra with
  | none => dsimp only; rw [evaluateHOLFiniteState_seq_line780]
  | some _ => rfl

def seqList : List (ProgHOL 64) → ProgHOL 64 → ProgHOL 64
  | [], tail => tail
  | p :: ps, tail => .seq p (seqList ps tail)

def seqBlock : List (ProgHOL 64) → ProgHOL 64
  | [] => .skip
  | [p] => p
  | p :: ps => .seq p (seqBlock ps)

theorem evaluate_seqList_eq {F : Type} (ps : List (ProgHOL 64)) (tail : ProgHOL 64)
    (s : PanSemStateFiniteExact 64 F) :
    evaluateHOLFiniteState s (seqList ps tail) =
      evaluateHOLFiniteState s (.seq (seqBlock ps) tail) := by
  induction ps generalizing s with
  | nil => simp [seqList, seqBlock, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_skip]
  | cons p ps ih =>
    cases ps with
    | nil => rfl
    | cons q qs =>
      change evaluateHOLFiniteState s (.seq p (seqList (q :: qs) tail)) =
        evaluateHOLFiniteState s (.seq (.seq p (seqBlock (q :: qs))) tail)
      rw [evaluate_seq_assoc, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_seq_line780]
      rcases evaluateHOLFiniteState s p with ⟨rp, mp⟩
      cases rp with
      | none => exact ih mp
      | some _ => rfl

theorem eval_panOp_mul_const {F : Type} (s : PanSemStateFiniteExact 64 F) (a b : BitVec 64) :
    @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
      (.panop .mul [.const a, .const b]) = some (.val (.word (a * b))) := by
  rfl

-- 1. `wk_sha256_init`
theorem wk_sha256_init :
    WorldKeeps WorldOK (fun _ => []) ["heap_ptr", "sha_pad", "sha_st"] stdKeep
      NoExtra (ofString "sha256_init") := by
  have hlook : originalRuntimeCode.lookup (ofString "sha256_init") =
      some ([], sourceFnBody Guest.Software.guestFn_sha256_init, .one) :=
    lookup_of_guestAst_getElem 91 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_sha256_init) rfl
  refine ⟨_, _, _, hlook, fun s hc hWOK _ hnt hres => ?_⟩
  refine InitEff.to_worldStep (B := []) hWOK (by simp) (by decide) ?_
  have hbody : sourceFnBody Guest.Software.guestFn_sha256_init =
      .seq (.call (some (some (.global, ofString "sha_st"), none)) (ofString "alloc") [.const 64])
        (.seq (.call (some (some (.global, ofString "sha_pad"), none)) (ofString "alloc") [.const 128])
          (.return (.const 0))) := rfl
  rw [hbody] at hnt hres ⊢
  refine initEff_seq_alloc_global "sha_st" 64 (.const 64)
    (InitEff.refl s [] [] _ hWOK.1 hc) ⟨by omega, by omega⟩ rfl
    (by decide) (by decide) (by decide) hnt (Or.inr hres)
    (fun s1 _ _ _ heff1 _ _ _ _ hnt1 hor1 => ?_)
  refine initEff_seq_alloc_global "sha_pad" 128 (.const 128)
    heff1 ⟨by omega, by omega⟩ rfl
    (by decide) (by decide) (by decide) hnt1 hor1
    (fun s2 _ _ _ heff2 _ _ _ _ _ _ => initEff_return _ heff2)

-- 2. `wk_u256_ws_init`
theorem wk_u256_ws_init :
    WorldKeeps WorldOK (fun _ => []) ["heap_ptr", "u256_ws"] stdKeep
      NoExtra (ofString "u256_ws_init") := by
  have hlook_fn : originalRuntimeCode.lookup (ofString "u256_ws_init") =
      some ([], sourceFnBody Guest.Software.guestFn_u256_ws_init, .one) :=
    lookup_of_guestAst_getElem 38 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_u256_ws_init) rfl
  refine ⟨_, _, _, hlook_fn, fun s hc hWOK _ hnt hres => ?_⟩
  refine InitEff.to_worldStep (B := []) hWOK (by simp) (by decide) ?_
  have hbody : sourceFnBody Guest.Software.guestFn_u256_ws_init =
      .seq (.ite (.cmp .equal (.var .global (ofString "u256_ws")) (.const 0))
          (.call (some (some (.global, ofString "u256_ws"), none)) (ofString "alloc") [.const 640])
          .skip)
        (.return (.const 0)) := rfl
  rw [hbody] at hnt hres ⊢
  have heff0 := InitEff.refl s [] [] ["heap_ptr", "u256_ws"] hWOK.1 hc
  refine initEff_seq hnt (Or.inr hres)
    (fun hnt_i hor_i => initEff_ite _ heff0 hnt_i hor_i
      (fun hnt_y hor_y => (step_call_alloc_global "u256_ws" 640 (.const 640) heff0
        ⟨by omega, by omega⟩ rfl (by decide) (by decide) (by decide) hnt_y hor_y).2.2.1)
      (fun _ _ => initEff_skip heff0))
    (fun mid _ heff1 _ _ => initEff_return _ heff1)

-- 3. `wk_header_init`
theorem wk_header_init :
    WorldKeeps WorldOK (fun s => [(globN s "hdr_zero8", if globN s "hdr_zero8" = 0 then 0 else 8)])
      ["hdr_zero8", "heap_ptr"] stdKeep NoExtra (ofString "header_init") := by
  have hlook : originalRuntimeCode.lookup (ofString "header_init") =
      some ([], sourceFnBody Guest.Software.guestFn_header_init, .one) :=
    lookup_of_guestAst_getElem 238 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_header_init) rfl
  refine ⟨_, _, _, hlook, fun s hc hWOK _ hnt hres => ?_⟩
  refine InitEff.to_worldStep (B := []) hWOK (by simp) (by decide) ?_
  have hbody : sourceFnBody Guest.Software.guestFn_header_init =
      .seq (.ite (.cmp .notEqual (.var .global (ofString "hdr_zero8")) (.const 0))
          (.return (.const 0)) .skip)
        (.seq (.call (some (some (.global, ofString "hdr_zero8"), none)) (ofString "alloc") [.const 8])
          (.seq (.call (some (none, none)) (ofString "memzero") [.var .global (ofString "hdr_zero8"), .const 8])
            (.return (.const 0)))) := rfl
  rw [hbody] at hnt hres ⊢
  have heff0 := InitEff.refl s [(globN s "hdr_zero8", if globN s "hdr_zero8" = 0 then 0 else 8)]
    [] ["hdr_zero8", "heap_ptr"] hWOK.1 hc
  refine initEff_seq hnt (Or.inr hres)
    (fun hnt_i hor_i => initEff_ite _ heff0 hnt_i hor_i
      (fun _ _ => initEff_return _ heff0)
      (fun _ _ => initEff_skip heff0))
    (fun s1 _ heff1 hnt1 hor1 => ?_)
  refine initEff_seq_alloc_global "hdr_zero8" 8 (.const 8) heff1
    ⟨by omega, by omega⟩ rfl (by decide) (by decide) (by decide) hnt1 hor1
    (fun s2 pw _ _ heff2 hpw_g _ hpw_lo hpw_hi hnt2 hor2 => ?_)
  refine initEff_seq hnt2 hor2 (fun hnt_m hor_m => ?_) (fun s3 _ heff3 _ _ => initEff_return _ heff3)
  have hargs : evalListHOLFinite s2 (h := fun a => Classical.propDecidable (s2.memaddrs a))
      [.var .global (ofString "hdr_zero8"), .const 8] = some [.val (.word pw), .val (.word 8)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hpw_g]
  have hb := call0_byteEff funByteEff_memzero s2 _ [(pw.toNat, 8)] heff2.code heff2.arena.1
    (fun vs hvs i hi _ => by
      rw [hargs] at hvs; injection hvs with hvs; subst hvs
      simp [valWordNat] at hi; subst hi
      exact ⟨(pw.toNat, 8), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
    hnt_m hor_m
  exact heff2.of_byteEff hb (fun iv hiv _ => by
    simp at hiv; subst hiv
    exact Or.inr (Or.inr ⟨hpw_lo, le_trans hpw_hi heff2.arena.2.2.1⟩))

-- 4. `wk_keccak_init`
theorem wk_keccak_init :
    WorldKeeps WorldOK (fun s => [(globN s "keccak_rc", if globN s "keccak_rc" = 0 then 0 else 192)])
      ["heap_ptr", "keccak_pad", "keccak_rc", "keccak_st"] stdKeep
      NoExtra (ofString "keccak_init") := by
  have hlook : originalRuntimeCode.lookup (ofString "keccak_init") =
      some ([], sourceFnBody Guest.Software.guestFn_keccak_init, .one) :=
    lookup_of_guestAst_getElem 100 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_keccak_init) rfl
  refine ⟨_, _, _, hlook, fun s hc hWOK _ hnt hres => ?_⟩
  refine InitEff.to_worldStep (B := []) hWOK (by simp) (by decide) ?_
  let tail : ProgHOL 64 := match sourceFnBody Guest.Software.guestFn_keccak_init with
    | .seq _ (.seq _ (.seq _ t)) => t
    | _ => .skip
  have hbody : sourceFnBody Guest.Software.guestFn_keccak_init =
      .seq (.call (some (some (.global, ofString "keccak_rc"), none)) (ofString "alloc") [.const 192])
        (.seq (.call (some (some (.global, ofString "keccak_st"), none)) (ofString "alloc") [.const 200])
          (.seq (.call (some (some (.global, ofString "keccak_pad"), none)) (ofString "alloc") [.const 136])
            tail)) := rfl
  rw [hbody] at hnt hres ⊢
  refine initEff_seq_alloc_global "keccak_rc" 192 (.const 192)
    (InitEff.refl s _ [] _ hWOK.1 hc) ⟨by omega, by omega⟩ rfl
    (by decide) (by decide) (by decide) hnt (Or.inr hres)
    (fun s1 prc _ _ heff1 hprc1 _ hprc_lo hprc_hi hnt1 hor1 => ?_)
  have hrc_lim : prc.toNat + 192 ≤ heapLimit := le_trans hprc_hi heff1.arena.2.2.1
  refine initEff_seq_alloc_global "keccak_st" 200 (.const 200)
    heff1 ⟨by omega, by omega⟩ rfl
    (by decide) (by decide) (by decide) hnt1 hor1
    (fun s2 _ _ hg2 heff2 _ _ _ _ hnt2 hor2 => ?_)
  refine initEff_seq_alloc_global "keccak_pad" 136 (.const 136)
    heff2 ⟨by omega, by omega⟩ rfl
    (by decide) (by decide) (by decide) hnt2 hor2
    (fun s3 _ _ hg3 heff3 _ _ _ _ _ _ => ?_)
  have hprc3 : s3.globals.lookup (ofString "keccak_rc") = some (.val (.word prc)) := by
    rw [hg3 _ (by decide) (by decide), hg2 _ (by decide) (by decide)]; exact hprc1
  exact (initEff_fresh_constStores "keccak_rc" 192 prc tail heff3 (by omega) rfl hprc3 hprc_lo hrc_lim).1

-- 5. `wk_ripemd160_init`
theorem wk_ripemd160_init :
    WorldKeeps WorldOK (fun s => [(globN s "rmd_tab", if globN s "rmd_tab" = 0 then 0 else 160)])
      ["heap_ptr", "rmd_h", "rmd_pad", "rmd_tab", "rmd_x"] stdKeep
      NoExtra (ofString "ripemd160_init") := by
  have hlook : originalRuntimeCode.lookup (ofString "ripemd160_init") =
      some ([], sourceFnBody Guest.Software.guestFn_ripemd160_init, .one) :=
    lookup_of_guestAst_getElem 612 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_ripemd160_init) rfl
  refine ⟨_, _, _, hlook, fun s hc hWOK _ hnt hres => ?_⟩
  refine InitEff.to_worldStep (B := []) hWOK (by simp) (by decide) ?_
  let tail : ProgHOL 64 := match sourceFnBody Guest.Software.guestFn_ripemd160_init with
    | .seq _ (.seq _ (.seq _ (.seq _ (.seq _ t)))) => t
    | _ => .skip
  have hbody : sourceFnBody Guest.Software.guestFn_ripemd160_init =
      .seq (.ite (.cmp .notEqual (.var .global (ofString "rmd_tab")) (.const 0)) (.return (.const 0)) .skip)
        (.seq (.call (some (some (.global, ofString "rmd_tab"), none)) (ofString "alloc") [.const 160])
          (.seq (.call (some (some (.global, ofString "rmd_x"), none)) (ofString "alloc") [.const 128])
            (.seq (.call (some (some (.global, ofString "rmd_h"), none)) (ofString "alloc") [.const 40])
              (.seq (.call (some (some (.global, ofString "rmd_pad"), none)) (ofString "alloc") [.const 128])
                tail)))) := rfl
  rw [hbody] at hnt hres ⊢
  have heff0 := InitEff.refl s [(globN s "rmd_tab", if globN s "rmd_tab" = 0 then 0 else 160)]
    [] ["heap_ptr", "rmd_h", "rmd_pad", "rmd_tab", "rmd_x"] hWOK.1 hc
  refine initEff_seq hnt (Or.inr hres)
    (fun hnt_i hor_i => initEff_ite _ heff0 hnt_i hor_i
      (fun _ _ => initEff_return _ heff0)
      (fun _ _ => initEff_skip heff0))
    (fun s0 _ heff_s0 hnt0 hor0 => ?_)
  refine initEff_seq_alloc_global "rmd_tab" 160 (.const 160) heff_s0
    ⟨by omega, by omega⟩ rfl (by decide) (by decide) (by decide) hnt0 hor0
    (fun s1 ptab _ _ heff1 hptab1 _ hptab_lo hptab_hi hnt1 hor1 => ?_)
  have htab_lim : ptab.toNat + 160 ≤ heapLimit := le_trans hptab_hi heff1.arena.2.2.1
  refine initEff_seq_alloc_global "rmd_x" 128 (.const 128) heff1
    ⟨by omega, by omega⟩ rfl (by decide) (by decide) (by decide) hnt1 hor1
    (fun s2 _ _ hg2 heff2 _ _ _ _ hnt2 hor2 => ?_)
  refine initEff_seq_alloc_global "rmd_h" 40 (.const 40) heff2
    ⟨by omega, by omega⟩ rfl (by decide) (by decide) (by decide) hnt2 hor2
    (fun s3 _ _ hg3 heff3 _ _ _ _ hnt3 hor3 => ?_)
  refine initEff_seq_alloc_global "rmd_pad" 128 (.const 128) heff3
    ⟨by omega, by omega⟩ rfl (by decide) (by decide) (by decide) hnt3 hor3
    (fun s4 _ _ hg4 heff4 _ _ _ _ _ _ => ?_)
  have hptab4 : s4.globals.lookup (ofString "rmd_tab") = some (.val (.word ptab)) := by
    rw [hg4 _ (by decide) (by decide), hg3 _ (by decide) (by decide), hg2 _ (by decide) (by decide)]
    exact hptab1
  exact (initEff_fresh_constStores "rmd_tab" 160 ptab tail heff4 (by omega) rfl hptab4 hptab_lo htab_lim).1

-- 6. `wk_blake2_init`
theorem wk_blake2_init :
    WorldKeeps WorldOK
      (fun s => [(globN s "b2_iv", if globN s "b2_iv" = 0 then 0 else 64),
                 (globN s "b2_sigma", if globN s "b2_sigma" = 0 then 0 else 80)])
      ["b2_iv", "b2_sigma", "b2_v", "heap_ptr"] stdKeep
      NoExtra (ofString "blake2_init") := by
  have hlook : originalRuntimeCode.lookup (ofString "blake2_init") =
      some ([], sourceFnBody Guest.Software.guestFn_blake2_init, .one) :=
    lookup_of_guestAst_getElem 621 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_blake2_init) rfl
  refine ⟨_, _, _, hlook, fun s hc hWOK _ hnt hres => ?_⟩
  refine InitEff.to_worldStep (B := []) hWOK (by simp) (by decide) ?_
  -- `blake2_init` allocates `b2_sigma` (80), `b2_iv` (64), `b2_v` (128), then 10 stores to `b2_sigma` and 8 stores to `b2_iv`!
  let tail0 : ProgHOL 64 := match sourceFnBody Guest.Software.guestFn_blake2_init with
    | .seq _ (.seq _ (.seq _ (.seq _ t))) => t
    | _ => .skip
  let sigmaStores : ProgHOL 64 := match tail0 with
    | .seq s0 (.seq s1 (.seq s2 (.seq s3 (.seq s4 (.seq s5 (.seq s6 (.seq s7 (.seq s8 (.seq s9 _))))))))) =>
        .seq s0 (.seq s1 (.seq s2 (.seq s3 (.seq s4 (.seq s5 (.seq s6 (.seq s7 (.seq s8 s9))))))))
    | _ => .skip
  let ivStores : ProgHOL 64 := match tail0 with
    | .seq _ (.seq _ (.seq _ (.seq _ (.seq _ (.seq _ (.seq _ (.seq _ (.seq _ (.seq _ t))))))))) => t
    | _ => .skip
  have hbody : sourceFnBody Guest.Software.guestFn_blake2_init =
      .seq (.ite (.cmp .notEqual (.var .global (ofString "b2_sigma")) (.const 0)) (.return (.const 0)) .skip)
        (.seq (.call (some (some (.global, ofString "b2_sigma"), none)) (ofString "alloc") [.const 80])
          (.seq (.call (some (some (.global, ofString "b2_iv"), none)) (ofString "alloc") [.const 64])
            (.seq (.call (some (some (.global, ofString "b2_v"), none)) (ofString "alloc") [.const 128])
              tail0))) := rfl
  rw [hbody] at hnt hres ⊢
  have heff0 := InitEff.refl s
    [(globN s "b2_iv", if globN s "b2_iv" = 0 then 0 else 64),
     (globN s "b2_sigma", if globN s "b2_sigma" = 0 then 0 else 80)]
    [] ["b2_iv", "b2_sigma", "b2_v", "heap_ptr"] hWOK.1 hc
  refine initEff_seq hnt (Or.inr hres)
    (fun hnt_i hor_i => initEff_ite _ heff0 hnt_i hor_i
      (fun _ _ => initEff_return _ heff0)
      (fun _ _ => initEff_skip heff0))
    (fun s0 _ heff_s0 hnt0 hor0 => ?_)
  refine initEff_seq_alloc_global "b2_sigma" 80 (.const 80) heff_s0
    ⟨by omega, by omega⟩ rfl (by decide) (by decide) (by decide) hnt0 hor0
    (fun s1 psig _ _ heff1 hpsig1 _ hpsig_lo hpsig_hi hnt1 hor1 => ?_)
  have hsig_lim : psig.toNat + 80 ≤ heapLimit := le_trans hpsig_hi heff1.arena.2.2.1
  refine initEff_seq_alloc_global "b2_iv" 64 (.const 64) heff1
    ⟨by omega, by omega⟩ rfl (by decide) (by decide) (by decide) hnt1 hor1
    (fun s2 piv _ hg2 heff2 hpiv2 _ hpiv_lo hpiv_hi hnt2 hor2 => ?_)
  have hiv_lim : piv.toNat + 64 ≤ heapLimit := le_trans hpiv_hi heff2.arena.2.2.1
  refine initEff_seq_alloc_global "b2_v" 128 (.const 128) heff2
    ⟨by omega, by omega⟩ rfl (by decide) (by decide) (by decide) hnt2 hor2
    (fun s3 _ _ hg3 heff3 _ _ _ _ _ _ => ?_)
  have hpsig3 : s3.globals.lookup (ofString "b2_sigma") = some (.val (.word psig)) := by
    rw [hg3 _ (by decide) (by decide), hg2 _ (by decide) (by decide)]; exact hpsig1
  have hpiv3 : s3.globals.lookup (ofString "b2_iv") = some (.val (.word piv)) := by
    rw [hg3 _ (by decide) (by decide)]; exact hpiv2
  -- Split `tail0` into `sigmaStores` followed by `ivStores`:
  let sigmaList : List (ProgHOL 64) := match tail0 with
    | .seq s0 (.seq s1 (.seq s2 (.seq s3 (.seq s4 (.seq s5 (.seq s6 (.seq s7 (.seq s8 (.seq s9 _))))))))) =>
        [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9]
    | _ => []
  have htail_eq : tail0 = seqList sigmaList ivStores := rfl
  rw [htail_eq, evaluate_seqList_eq, evaluateHOLFiniteState_seq_line780]
  have hs_eff := initEff_fresh_constStores "b2_sigma" 80 psig (seqBlock sigmaList) heff3 (by omega) rfl hpsig3 hpsig_lo hsig_lim
  rcases hrun_s : evaluateHOLFiniteState s3 (seqBlock sigmaList) with ⟨rs, ms⟩
  rw [hrun_s] at hs_eff
  cases rs with
  | some _ => exact hs_eff.1
  | none =>
    have hpiv_ms : ms.globals.lookup (ofString "b2_iv") = some (.val (.word piv)) := by
      rw [hs_eff.2]; exact hpiv3
    exact (initEff_fresh_constStores "b2_iv" 64 piv ivStores hs_eff.1 (by omega) rfl hpiv_ms hpiv_lo hiv_lim).1

-- 7. `wk_ssz_init`
theorem wk_ssz_init :
    WorldKeeps WorldOK
      (fun s => [(globN s "zero_hashes", if globN s "zero_hashes" = 0 then 0 else 2048)])
      ["heap_ptr", "ssz_len_chunk", "ssz_offs", "zero_hashes"] stdKeep
      NoExtra (ofString "ssz_init") := by
  have hlook : originalRuntimeCode.lookup (ofString "ssz_init") =
      some ([], sourceFnBody Guest.Software.guestFn_ssz_init, .one) :=
    lookup_of_guestAst_getElem 185 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_ssz_init) rfl
  refine ⟨_, _, _, hlook, fun s hc hWOK _ hnt hres => ?_⟩
  refine InitEff.to_worldStep (B := []) hWOK (by simp) (by decide) ?_
  let tail : ProgHOL 64 := match sourceFnBody Guest.Software.guestFn_ssz_init with
    | .seq _ (.seq _ (.seq _ (.seq _ t))) => t
    | _ => .skip
  have hbody : sourceFnBody Guest.Software.guestFn_ssz_init =
      .seq (.ite (.cmp .notEqual (.var .global (ofString "zero_hashes")) (.const 0)) (.return (.const 0)) .skip)
        (.seq (.call (some (some (.global, ofString "ssz_len_chunk"), none)) (ofString "alloc") [.const 32])
          (.seq (.call (some (some (.global, ofString "ssz_offs"), none)) (ofString "alloc") [.const 64])
            (.seq (.call (some (some (.global, ofString "zero_hashes"), none)) (ofString "alloc")
                [.panop .mul [.const 64, .const 32]])
              tail))) := rfl
  rw [hbody] at hnt hres ⊢
  have heff0 := InitEff.refl s [(globN s "zero_hashes", if globN s "zero_hashes" = 0 then 0 else 2048)]
    [] ["heap_ptr", "ssz_len_chunk", "ssz_offs", "zero_hashes"] hWOK.1 hc
  refine initEff_seq hnt (Or.inr hres)
    (fun hnt_i hor_i => initEff_ite _ heff0 hnt_i hor_i
      (fun _ _ => initEff_return _ heff0)
      (fun _ _ => initEff_skip heff0))
    (fun s0 _ heff_s0 hnt0 hor0 => ?_)
  refine initEff_seq_alloc_global "ssz_len_chunk" 32 (.const 32) heff_s0
    ⟨by omega, by omega⟩ rfl (by decide) (by decide) (by decide) hnt0 hor0
    (fun s1 _ _ _ heff1 _ _ _ _ hnt1 hor1 => ?_)
  refine initEff_seq_alloc_global "ssz_offs" 64 (.const 64) heff1
    ⟨by omega, by omega⟩ rfl (by decide) (by decide) (by decide) hnt1 hor1
    (fun s2 _ _ _ heff2 _ _ _ _ hnt2 hor2 => ?_)
  refine initEff_seq_alloc_global "zero_hashes" 2048 (.panop .mul [.const 64, .const 32]) heff2
    ⟨by omega, by omega⟩ rfl (by decide) (by decide) (by decide) hnt2 hor2
    (fun s3 pzh _ _ heff3 hpzh3 _ hpzh_lo hpzh_hi _ _ => ?_)
  have hzh_lim : pzh.toNat + 2048 ≤ heapLimit := le_trans hpzh_hi heff3.arena.2.2.1
  exact (initEff_fresh_constStores "zero_hashes" 2048 pzh tail heff3 (by omega) rfl hpzh3 hpzh_lo hzh_lim).1

-- 8. `wk_bn254_init`
theorem wk_bn254_init :
    WorldKeeps WorldOK
      (fun s => [(globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352),
                 (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384)])
      ["bn_expw", "bn_gamma", "heap_ptr"] stdKeep
      NoExtra (ofString "bn254_init") := by
  have hlook : originalRuntimeCode.lookup (ofString "bn254_init") =
      some ([], sourceFnBody Guest.Software.guestFn_bn254_init, .one) :=
    lookup_of_guestAst_getElem 648 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_bn254_init) rfl
  refine ⟨_, _, _, hlook, fun s hc hWOK _ hnt hres => ?_⟩
  refine InitEff.to_worldStep (B := []) hWOK (by simp) (by decide) ?_
  -- `bn254_init` has: `ite`, `alloc bn_gamma (6*64)`, 12 `rStruct` stores to `bn_gamma`, `alloc bn_expw (44*8)`, 44 stores to `bn_expw`!
  let afterIte : ProgHOL 64 := match sourceFnBody Guest.Software.guestFn_bn254_init with
    | .seq _ t => t
    | _ => .skip
  let afterAllocGamma : ProgHOL 64 := match afterIte with
    | .seq _ t => t
    | _ => .skip
  let gammaStores : ProgHOL 64 := match afterAllocGamma with
    | .seq g0 (.seq g1 (.seq g2 (.seq g3 (.seq g4 (.seq g5 (.seq g6 (.seq g7 (.seq g8 (.seq g9 (.seq g10 (.seq g11 _))))))))))) =>
        .seq g0 (.seq g1 (.seq g2 (.seq g3 (.seq g4 (.seq g5 (.seq g6 (.seq g7 (.seq g8 (.seq g9 (.seq g10 g11))))))))))
    | _ => .skip
  let fromAllocExpw : ProgHOL 64 := match afterAllocGamma with
    | .seq _ (.seq _ (.seq _ (.seq _ (.seq _ (.seq _ (.seq _ (.seq _ (.seq _ (.seq _ (.seq _ (.seq _ t))))))))))) => t
    | _ => .skip
  let expwStores : ProgHOL 64 := match fromAllocExpw with
    | .seq _ t => t
    | _ => .skip
  have hbody : sourceFnBody Guest.Software.guestFn_bn254_init =
      .seq (.ite (.cmp .notEqual (.var .global (ofString "bn_gamma")) (.const 0)) (.return (.const 0)) .skip)
        (.seq (.call (some (some (.global, ofString "bn_gamma"), none)) (ofString "alloc")
            [.panop .mul [.const 6, .const 64]])
          afterAllocGamma) := rfl
  have hfrom : fromAllocExpw =
      .seq (.call (some (some (.global, ofString "bn_expw"), none)) (ofString "alloc")
          [.panop .mul [.const 44, .const 8]])
        expwStores := rfl
  rw [hbody] at hnt hres ⊢
  have heff0 := InitEff.refl s
    [(globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352),
     (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384)]
    [] ["bn_expw", "bn_gamma", "heap_ptr"] hWOK.1 hc
  refine initEff_seq hnt (Or.inr hres)
    (fun hnt_i hor_i => initEff_ite _ heff0 hnt_i hor_i
      (fun _ _ => initEff_return _ heff0)
      (fun _ _ => initEff_skip heff0))
    (fun s0 _ heff_s0 hnt0 hor0 => ?_)
  refine initEff_seq_alloc_global "bn_gamma" 384 (.panop .mul [.const 6, .const 64]) heff_s0
    ⟨by omega, by omega⟩ rfl (by decide) (by decide) (by decide) hnt0 hor0
    (fun s1 pgam _ _ heff1 hpgam1 _ hpgam_lo hpgam_hi hnt1 hor1 => ?_)
  have hgam_lim : pgam.toNat + 384 ≤ heapLimit := le_trans hpgam_hi heff1.arena.2.2.1
  let gammaList : List (ProgHOL 64) := match afterAllocGamma with
    | .seq g0 (.seq g1 (.seq g2 (.seq g3 (.seq g4 (.seq g5 (.seq g6 (.seq g7 (.seq g8 (.seq g9 (.seq g10 (.seq g11 _))))))))))) =>
        [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11]
    | _ => []
  have hafter_eq : afterAllocGamma = seqList gammaList fromAllocExpw := rfl
  rw [hafter_eq, evaluate_seqList_eq] at hnt1 hor1 ⊢
  refine initEff_seq hnt1 hor1
    (fun _ _ => (initEff_fresh_constStores "bn_gamma" 384 pgam (seqBlock gammaList) heff1 (by omega) rfl hpgam1 hpgam_lo hgam_lim).1)
    (fun s2 _ heff2 hnt2 hor2 => ?_)
  rw [hfrom] at hnt2 hor2 ⊢
  refine initEff_seq_alloc_global "bn_expw" 352 (.panop .mul [.const 44, .const 8]) heff2
    ⟨by omega, by omega⟩ rfl (by decide) (by decide) (by decide) hnt2 hor2
    (fun s3 pexp _ _ heff3 hpexp3 _ hpexp_lo hpexp_hi _ _ => ?_)
  have hexp_lim : pexp.toNat + 352 ≤ heapLimit := le_trans hpexp_hi heff3.arena.2.2.1
  exact (initEff_fresh_constStores "bn_expw" 352 pexp expwStores heff3 (by omega) rfl hpexp3 hpexp_lo hexp_lim).1

-- 9. `wk_bls_precompiles_init`
theorem bls_consts_init_eff {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (heff : InitEff s cur Rl B gw)
    (hgw_hp : ofString "heap_ptr" ∈ gw.map ofString)
    (hgw_c : ofString "bls_c" ∈ gw.map ofString)
    (hnt : (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_bls_consts_init)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_bls_consts_init)).1) :
    InitEff s (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_bls_consts_init)).2 Rl B gw := by
  let tail : ProgHOL 64 := match sourceFnBody Guest.Software.guestFn_bls_consts_init with
    | .seq _ (.seq _ t) => t
    | _ => .skip
  have hbody : sourceFnBody Guest.Software.guestFn_bls_consts_init =
      .seq (.ite (.cmp .notEqual (.var .global (ofString "bls_c")) (.const 0)) (.return (.const 0)) .skip)
        (.seq (.call (some (some (.global, ofString "bls_c"), none)) (ofString "alloc") [.const 7136])
          tail) := rfl
  rw [hbody] at hnt hres ⊢
  refine initEff_seq hnt (Or.inr hres)
    (fun hnt_i hor_i => initEff_ite _ heff hnt_i hor_i
      (fun _ _ => initEff_return _ heff)
      (fun _ _ => initEff_skip heff))
    (fun s1 _ heff1 hnt1 hor1 => ?_)
  refine initEff_seq_alloc_global "bls_c" 7136 (.const 7136) heff1
    ⟨by omega, by omega⟩ rfl (by decide) hgw_hp hgw_c hnt1 hor1
    (fun s2 pc _ _ heff2 hpc2 _ hpc_lo hpc_hi _ _ => ?_)
  have hc_lim : pc.toNat + 7136 ≤ heapLimit := le_trans hpc_hi heff2.arena.2.2.1
  exact (initEff_fresh_constStores "bls_c" 7136 pc tail heff2 (by omega) rfl hpc2 hpc_lo hc_lim).1

theorem call0_zero_arg_initEff {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (fname : MlS) (body : ProgHOL 64)
    (hlook : originalRuntimeCode.lookup fname = some ([], body, .one))
    (heff : InitEff s cur Rl B gw)
    (hspec : ∀ entry : PanSemStateFiniteExact 64 F,
      InitEff s entry Rl B gw →
      (evaluateHOLFiniteState entry body).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState entry body).1 →
      InitEff s (evaluateHOLFiniteState entry body).2 Rl B gw)
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) fname [])).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState cur (.call (some (none, none)) fname [])).1 = none ∨
      Resumes (evaluateHOLFiniteState cur (.call (some (none, none)) fname [])).1) :
    InitEff s (evaluateHOLFiniteState cur (.call (some (none, none)) fname [])).2 Rl B gw := by
  have hl := pan_zero_arg_lookup cur.code.lookup fname body .one (by rw [heff.code]; exact hlook)
  have hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) [] = some [] := rfl
  rw [evaluateHOLFiniteState_call, hargs] at hnt hor ⊢
  dsimp only at hnt hor ⊢
  rw [hl] at hnt hor ⊢
  dsimp only at hnt hor ⊢
  by_cases hz : cur.clock = 0
  · rw [if_pos hz] at hnt; exact absurd rfl hnt
  · rw [if_neg hz] at hnt hor ⊢
    let entry := callEntryStateHOLFinite cur HolFiniteMapExact.empty
    have heff_e : InitEff s entry Rl B gw := heff.locals_clock _ _
    rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite cur HolFiniteMapExact.empty) body with ⟨res, post⟩
    have hnt' := hnt; have hor' := hor
    rw [hrun] at hnt' hor'
    have hnt_b : res ≠ some .timeOut := by intro h; subst h; simp at hnt'
    cases res with
    | none => exfalso; rcases hor' with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
    | some r =>
      cases r with
      | returned v =>
        dsimp only at hor' ⊢
        split
        · have hb := hspec entry heff_e (by dsimp only [entry]; rw [hrun]; exact hnt_b)
            (by dsimp only [entry]; rw [hrun]; exact Or.inl ⟨v, rfl⟩)
          dsimp only [entry] at hb; rw [hrun] at hb
          exact hb.locals_clock _ _
        · rename_i hbad; rw [if_neg hbad] at hor'
          exfalso; rcases hor' with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      | exception eid ev =>
        have hnot_trap : eid ≠ ofString "TrapErr" := by
          rcases hor' with h | ⟨_, h⟩ | ⟨_, _, h, hne⟩
          · simp at h
          · simp at h
          · simp at h; obtain ⟨rfl, _⟩ := h; exact hne
        have hb := hspec entry heff_e (by dsimp only [entry]; rw [hrun]; exact hnt_b)
          (by dsimp only [entry]; rw [hrun]; exact Or.inr ⟨eid, ev, rfl, hnot_trap⟩)
        dsimp only [entry] at hb; rw [hrun] at hb
        exact hb.locals_clock _ _
      | _ => exfalso; rcases hor' with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h

theorem wk_bls_precompiles_init :
    WorldKeeps WorldOK
      (fun s => [(globN s "bls_c", if globN s "bls_c" = 0 then 0 else 7136),
                 (globN s "bls_discount", if globN s "bls_discount" = 0 then 0 else 2048)])
      ["bls_c", "bls_discount", "heap_ptr"] stdKeep
      NoExtra (ofString "bls_precompiles_init") := by
  have hlook_c : originalRuntimeCode.lookup (ofString "bls_consts_init") =
      some ([], sourceFnBody Guest.Software.guestFn_bls_consts_init, .one) :=
    lookup_of_guestAst_getElem 696 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_bls_consts_init) rfl
  have hlook_l : originalRuntimeCode.lookup (ofString "bls_lib_init") =
      some ([], sourceFnBody Guest.Software.guestFn_bls_lib_init, .one) :=
    lookup_of_guestAst_getElem 801 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_bls_lib_init) rfl
  have hlook : originalRuntimeCode.lookup (ofString "bls_precompiles_init") =
      some ([], sourceFnBody Guest.Software.guestFn_bls_precompiles_init, .one) :=
    lookup_of_guestAst_getElem 811 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_bls_precompiles_init) rfl
  refine ⟨_, _, _, hlook, fun s hc hWOK _ hnt hres => ?_⟩
  refine InitEff.to_worldStep (B := []) hWOK (by simp) (by decide) ?_
  let tail : ProgHOL 64 := match sourceFnBody Guest.Software.guestFn_bls_precompiles_init with
    | .seq _ (.seq _ (.seq _ t)) => t
    | _ => .skip
  have hbody : sourceFnBody Guest.Software.guestFn_bls_precompiles_init =
      .seq (.ite (.cmp .notEqual (.var .global (ofString "bls_discount")) (.const 0)) (.return (.const 0)) .skip)
        (.seq (.call (some (none, none)) (ofString "bls_lib_init") [])
          (.seq (.call (some (some (.global, ofString "bls_discount"), none)) (ofString "alloc")
              [.panop .mul [.const 256, .const 8]])
            tail)) := rfl
  have hbody_l : sourceFnBody Guest.Software.guestFn_bls_lib_init =
      .seq (.call (some (none, none)) (ofString "bls_consts_init") []) (.return (.const 0)) := rfl
  rw [hbody] at hnt hres ⊢
  have heff0 := InitEff.refl s
    [(globN s "bls_c", if globN s "bls_c" = 0 then 0 else 7136),
     (globN s "bls_discount", if globN s "bls_discount" = 0 then 0 else 2048)]
    [] ["bls_c", "bls_discount", "heap_ptr"] hWOK.1 hc
  refine initEff_seq hnt (Or.inr hres)
    (fun hnt_i hor_i => initEff_ite _ heff0 hnt_i hor_i
      (fun _ _ => initEff_return _ heff0)
      (fun _ _ => initEff_skip heff0))
    (fun s0 _ heff_s0 hnt0 hor0 => ?_)
  refine initEff_seq hnt0 hor0
    (fun hnt_l hor_l => call0_zero_arg_initEff _ _ hlook_l heff_s0
      (fun entry heff_e hnt_el hres_el => by
        rw [hbody_l] at hnt_el hres_el ⊢
        refine initEff_seq hnt_el (Or.inr hres_el)
          (fun hnt_c hor_c => call0_zero_arg_initEff _ _ hlook_c heff_e
            (fun e2 he2 hnt_c2 hres_c2 => bls_consts_init_eff he2 (by decide) (by decide) hnt_c2 hres_c2)
            hnt_c hor_c)
          (fun _ _ heff_after _ _ => initEff_return _ heff_after))
      hnt_l hor_l)
    (fun s1 _ heff1 hnt1 hor1 => ?_)
  refine initEff_seq_alloc_global "bls_discount" 2048 (.panop .mul [.const 256, .const 8]) heff1
    ⟨by omega, by omega⟩ rfl (by decide) (by decide) (by decide) hnt1 hor1
    (fun s2 pdisc _ _ heff2 hpdisc2 _ hpdisc_lo hpdisc_hi _ _ => ?_)
  have hdisc_lim : pdisc.toNat + 2048 ≤ heapLimit := le_trans hpdisc_hi heff2.arena.2.2.1
  exact (initEff_fresh_constStores "bls_discount" 2048 pdisc tail heff2 (by omega) rfl hpdisc2 hpdisc_lo hdisc_lim).1

-- 10. `wk_mpt_init`
theorem wk_mpt_init :
    WorldKeeps WorldOK
      (fun s => [(globN s "empty_code_hash", if globN s "empty_code_hash" = 0 then 0 else 32),
                 (globN s "empty_trie_root", if globN s "empty_trie_root" = 0 then 0 else 32),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)])
      ["empty_code_hash", "empty_trie_root", "heap_ptr", "mpt_hash_scratch", "mpt_key_scratch", "mpt_nib_scratch"]
      stdKeep NoExtra (ofString "mpt_init") := by
  have hlook : originalRuntimeCode.lookup (ofString "mpt_init") =
      some ([], sourceFnBody Guest.Software.guestFn_mpt_init, .one) :=
    lookup_of_guestAst_getElem 247 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_mpt_init) rfl
  refine ⟨_, _, _, hlook, fun {F} s hc hWOK _ hnt hres => ?_⟩
  let Bmpt : List (String × Nat) := [("keccak_st", 200), ("keccak_pad", 136)]
  let Rlmpt : List Ivl :=
    [(globN s "empty_code_hash", if globN s "empty_code_hash" = 0 then 0 else 32),
     (globN s "empty_trie_root", if globN s "empty_trie_root" = 0 then 0 else 32),
     (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
     (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
     (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)]
  let gwmpt : List String :=
    ["empty_code_hash", "empty_trie_root", "heap_ptr", "mpt_hash_scratch", "mpt_key_scratch", "mpt_nib_scratch"]
  refine InitEff.to_worldStep (B := Bmpt) hWOK (by decide) (by decide) ?_
  have hbody : sourceFnBody Guest.Software.guestFn_mpt_init =
      .seq (.call (some (some (.global, ofString "empty_trie_root"), none)) (ofString "alloc") [.const 32])
      (.seq (.call (some (some (.global, ofString "empty_code_hash"), none)) (ofString "alloc") [.const 32])
      (.seq (.call (some (some (.global, ofString "mpt_nib_scratch"), none)) (ofString "alloc") [.const 64])
      (.seq (.call (some (some (.global, ofString "mpt_hash_scratch"), none)) (ofString "alloc") [.const 40])
      (.seq (.call (some (some (.global, ofString "mpt_key_scratch"), none)) (ofString "alloc") [.const 16])
      (.seq (.storeByte (.var .global (ofString "mpt_hash_scratch")) (.const 128))
      (.seq (.call (some (none, none)) (ofString "keccak256")
          [.var .global (ofString "mpt_hash_scratch"), .const 1, .var .global (ofString "empty_trie_root")])
      (.seq (.call (some (none, none)) (ofString "keccak256")
          [.var .global (ofString "mpt_hash_scratch"), .const 0, .var .global (ofString "empty_code_hash")])
        (.return (.const 0))))))))) := rfl
  rw [hbody] at hnt hres ⊢
  have heff0 := InitEff.refl s Rlmpt Bmpt gwmpt hWOK.1 hc
  refine initEff_seq_alloc_global "empty_trie_root" 32 (.const 32) heff0
    ⟨by omega, by omega⟩ rfl (by decide) (by decide) (by decide) hnt (Or.inr hres)
    (fun s1 ptr _ _ heff1 hptr1 _ hptr_lo hptr_hi hnt1 hor1 => ?_)
  have htr_lim : ptr.toNat + 32 ≤ heapLimit := le_trans hptr_hi heff1.arena.2.2.1
  refine initEff_seq_alloc_global "empty_code_hash" 32 (.const 32) heff1
    ⟨by omega, by omega⟩ rfl (by decide) (by decide) (by decide) hnt1 hor1
    (fun s2 pch _ hg2 heff2 hpch2 _ hpch_lo hpch_hi hnt2 hor2 => ?_)
  have hch_lim : pch.toNat + 32 ≤ heapLimit := le_trans hpch_hi heff2.arena.2.2.1
  refine initEff_seq_alloc_global "mpt_nib_scratch" 64 (.const 64) heff2
    ⟨by omega, by omega⟩ rfl (by decide) (by decide) (by decide) hnt2 hor2
    (fun s3 _ _ hg3 heff3 _ _ _ _ hnt3 hor3 => ?_)
  refine initEff_seq_alloc_global "mpt_hash_scratch" 40 (.const 40) heff3
    ⟨by omega, by omega⟩ rfl (by decide) (by decide) (by decide) hnt3 hor3
    (fun s4 phs _ hg4 heff4 hphs4 _ hphs_lo hphs_hi hnt4 hor4 => ?_)
  have hhs_lim : phs.toNat + 40 ≤ heapLimit := le_trans hphs_hi heff4.arena.2.2.1
  refine initEff_seq_alloc_global "mpt_key_scratch" 16 (.const 16) heff4
    ⟨by omega, by omega⟩ rfl (by decide) (by decide) (by decide) hnt4 hor4
    (fun s5 _ _ hg5 heff5 _ _ _ _ hnt5 hor5 => ?_)
  have hptr5 : s5.globals.lookup (ofString "empty_trie_root") = some (.val (.word ptr)) := by
    rw [hg5 _ (by decide) (by decide), hg4 _ (by decide) (by decide),
        hg3 _ (by decide) (by decide), hg2 _ (by decide) (by decide)]; exact hptr1
  have hpch5 : s5.globals.lookup (ofString "empty_code_hash") = some (.val (.word pch)) := by
    rw [hg5 _ (by decide) (by decide), hg4 _ (by decide) (by decide),
        hg3 _ (by decide) (by decide)]; exact hpch2
  have hphs5 : s5.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word phs)) := by
    rw [hg5 _ (by decide) (by decide)]; exact hphs4
  have hhl_he : heapLimit ≤ heapEnd := by decide
  -- Step 6: `storeByte (G:"mpt_hash_scratch") (#128)`
  refine initEff_seq hnt5 hor5
    (fun _ _ => by
      have hb := byteEff_storeByte_at (Rl := [(phs.toNat, 40)]) heff5.arena.1
        (.var .global (ofString "mpt_hash_scratch")) (.const 128) phs 0 40
        (le_trans hhs_lim hhl_he)
        (fun _ => ⟨(phs.toNat, 40), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
        (by omega) (by simpa [BitVec.add_zero, evalHOLExact] using hphs5)
      exact heff5.of_byteEff hb (fun iv hiv _ => by
        simp at hiv; subst hiv; exact Or.inr (Or.inr ⟨hphs_lo, hhs_lim⟩)))
    (fun s6 hs6 heff6 hnt6 hor6 => ?_)
  have hs6_glob : s6.globals = s5.globals := by
    have := (evaluate_storeByte_control_frame s5 (.var .global (ofString "mpt_hash_scratch")) (.const 128)).2.2.2.1
    rwa [hs6] at this
  have hptr6 : s6.globals.lookup (ofString "empty_trie_root") = some (.val (.word ptr)) := by
    rw [hs6_glob]; exact hptr5
  have hpch6 : s6.globals.lookup (ofString "empty_code_hash") = some (.val (.word pch)) := by
    rw [hs6_glob]; exact hpch5
  have hphs6 : s6.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word phs)) := by
    rw [hs6_glob]; exact hphs5
  -- Helper for `keccak256` call writing to a fresh 32-byte buffer `(pout, 32)`:
  have keccak_step : ∀ (curK : PanSemStateFiniteExact 64 F) (narg pout : BitVec 64),
      InitEff s curK Rlmpt Bmpt gwmpt →
      curK.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word phs)) →
      curK.globals.lookup (ofString "keccak_st") = s.globals.lookup (ofString "keccak_st") →
      curK.globals.lookup (ofString "keccak_pad") = s.globals.lookup (ofString "keccak_pad") →
      globN s "heap_ptr" ≤ pout.toNat → pout.toNat + 32 ≤ heapLimit →
      ∀ outExp : ExpHOL 64,
      @evalHOLExact 64 F _ curK.toExact (fun a => Classical.propDecidable (curK.memaddrs a)) outExp =
        some (.val (.word pout)) →
      (evaluateHOLFiniteState curK (.call (some (none, none)) (ofString "keccak256")
        [.var .global (ofString "mpt_hash_scratch"), .const narg, outExp])).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState curK (.call (some (none, none)) (ofString "keccak256")
        [.var .global (ofString "mpt_hash_scratch"), .const narg, outExp])).1 = none ∨
        Resumes (evaluateHOLFiniteState curK (.call (some (none, none)) (ofString "keccak256")
          [.var .global (ofString "mpt_hash_scratch"), .const narg, outExp])).1) →
      ByteEff curK (evaluateHOLFiniteState curK (.call (some (none, none)) (ofString "keccak256")
        [.var .global (ofString "mpt_hash_scratch"), .const narg, outExp])).2
        [bufferRegion s ("keccak_st", 200), bufferRegion s ("keccak_pad", 136), (pout.toNat, 32)] := by
    intro curK narg pout heffK hhsK hkstK hkpadK _ _ outExp houtK hntK horK
    have hargsK : evalListHOLFinite curK (h := fun a => Classical.propDecidable (curK.memaddrs a))
        [.var .global (ofString "mpt_hash_scratch"), .const narg, outExp] =
        some [.val (.word phs), .val (.word narg), .val (.word pout)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hhsK, houtK]
    exact call0_byteEff funByteEff_keccak256 curK _ _ heffK.code heffK.arena.1
      (fun vs hvs iv hiv _ => by
        rw [hargsK] at hvs; injection hvs with hvs; subst hvs
        have hst_eq : globBufIvl curK.globals "keccak_st" 200 = bufferRegion s ("keccak_st", 200) := by
          unfold globBufIvl bufferRegion globMapN globN; dsimp only; rw [hkstK]; rfl
        have hpad_eq : globBufIvl curK.globals "keccak_pad" 136 = bufferRegion s ("keccak_pad", 136) := by
          unfold globBufIvl bufferRegion globMapN globN; dsimp only; rw [hkpadK]; rfl
        simp only [List.mem_cons, List.not_mem_nil, or_false, valWordNat, List.getElem?_cons_succ,
          List.getElem?_cons_zero, Option.getD_some, hst_eq, hpad_eq] at hiv
        rcases hiv with rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self, le_rfl, le_rfl⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, le_rfl, le_rfl⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), le_rfl, le_rfl⟩)
      hntK horK
  -- Step 7: `keccak256(mpt_hash_scratch, 1, empty_trie_root)`
  have hkst6 : s6.globals.lookup (ofString "keccak_st") = s.globals.lookup (ofString "keccak_st") :=
    (heff6.gw_kept (ofString "keccak_st") (by decide)).symm
  have hkpad6 : s6.globals.lookup (ofString "keccak_pad") = s.globals.lookup (ofString "keccak_pad") :=
    (heff6.gw_kept (ofString "keccak_pad") (by decide)).symm
  have hb7 := keccak_step s6 1 ptr heff6 hphs6 hkst6 hkpad6 hptr_lo htr_lim
    (.var .global (ofString "empty_trie_root")) hptr6
  refine initEff_seq hnt6 hor6
    (fun hnt_k1 hor_k1 => heff6.of_byteEff (hb7 hnt_k1 hor_k1) (fun iv hiv _ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hiv
      rcases hiv with rfl | rfl | rfl
      · exact Or.inr (Or.inl ⟨("keccak_st", 200), by simp [Bmpt], le_rfl, le_rfl⟩)
      · exact Or.inr (Or.inl ⟨("keccak_pad", 136), by simp [Bmpt], le_rfl, le_rfl⟩)
      · exact Or.inr (Or.inr ⟨hptr_lo, htr_lim⟩)))
    (fun s7 hs7 heff7 hnt7 hor7 => ?_)
  have hs7_glob : s7.globals = s6.globals := by
    obtain ⟨hnt_k1, hor_k1⟩ := seq_nt_or s6 _ _ hnt6 hor6
    have hb7' := hb7 hnt_k1 hor_k1
    rw [hs7] at hb7'; exact hb7'.globals
  -- Step 8: `keccak256(mpt_hash_scratch, 0, empty_code_hash)`
  have hpch7 : s7.globals.lookup (ofString "empty_code_hash") = some (.val (.word pch)) := by
    rw [hs7_glob]; exact hpch6
  have hb8 := keccak_step s7 0 pch heff7 (by rw [hs7_glob]; exact hphs6)
    (by rw [hs7_glob]; exact hkst6) (by rw [hs7_glob]; exact hkpad6) hpch_lo hch_lim
    (.var .global (ofString "empty_code_hash")) hpch7
  refine initEff_seq hnt7 hor7
    (fun hnt_k2 hor_k2 => heff7.of_byteEff (hb8 hnt_k2 hor_k2) (fun iv hiv _ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hiv
      rcases hiv with rfl | rfl | rfl
      · exact Or.inr (Or.inl ⟨("keccak_st", 200), by simp [Bmpt], le_rfl, le_rfl⟩)
      · exact Or.inr (Or.inl ⟨("keccak_pad", 136), by simp [Bmpt], le_rfl, le_rfl⟩)
      · exact Or.inr (Or.inr ⟨hpch_lo, hch_lim⟩)))
    (fun s8 _ heff8 _ _ => initEff_return _ heff8)

end InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28
