import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.Common

/-!
# R16e `u256_ws` Division & Taylor Exponential Frame

Proves that `u256_divmod`, `u256_div`, `taylor_exponential`, and
`calculate_blob_gas_price` only touch `[(globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)]`
on resuming paths (and preserve all globals and typed world state).
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## Section 1: `FunLocFrame` and `ReadOnlyFn` for pure u256 arithmetic helpers -/

theorem flf_u256_from_word : M13.FunLocFrame (ofString "u256_from_word") :=
  M13.funLocFrame_of_locOnlyW 39 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_from_word rfl rfl

theorem flf_u256_is_zero : M13.FunLocFrame (ofString "u256_is_zero") :=
  M13.funLocFrame_of_locOnlyW 42 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_is_zero rfl rfl

theorem flf_u256_lt : M13.FunLocFrame (ofString "u256_lt") :=
  M13.funLocFrame_of_locOnlyW 46 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_lt rfl rfl

theorem flf_u256_add : M13.FunLocFrame (ofString "u256_add") :=
  M13.funLocFrame_of_locOnlyW 56 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_add rfl rfl

theorem flf_mul64x64 : M13.FunLocFrame (ofString "mul64x64") :=
  M13.funLocFrame_of_locOnlyW 59 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_mul64x64 rfl rfl

theorem flf_nlz32 : M13.FunLocFrame (ofString "nlz32") :=
  M13.funLocFrame_of_locOnlyW 62 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_nlz32 rfl rfl

theorem flf_div64by32 : M13.FunLocFrame (ofString "div64by32") :=
  M13.funLocFrame_of_locOnlyW 63 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_div64by32 rfl rfl

theorem flf_digits_to_u256 : M13.FunLocFrame (ofString "digits_to_u256") :=
  M13.funLocFrame_of_locOnlyW 65 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_digits_to_u256 rfl rfl

theorem flf_digits_len : M13.FunLocFrame (ofString "digits_len") :=
  M13.funLocFrame_of_locOnlyW 66 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_digits_len rfl rfl

theorem ro_udivmod : InitECandidate.Solver.Wave8Contracts.M18.ReadOnlyFn (ofString "udivmod") :=
  InitECandidate.Solver.Wave8Contracts.M18.readOnlyFn_of_guestAst 33 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_udivmod rfl
    (fun _ => false) (fun _ h => by cases h) rfl

theorem ro_u256_mul : InitECandidate.Solver.Wave8Contracts.M18.ReadOnlyFn (ofString "u256_mul") :=
  InitECandidate.Solver.Wave8Contracts.M18.readOnlyFn_of_guestAst 60 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_mul rfl
    InitECandidate.Solver.Wave8Contracts.M18.m18Callees
    InitECandidate.Solver.Wave8Contracts.M18.m18Callees_good rfl

theorem ro_u256_mul_full : InitECandidate.Solver.Wave8Contracts.M18.ReadOnlyFn (ofString "u256_mul_full") :=
  InitECandidate.Solver.Wave8Contracts.M18.readOnlyFn_of_guestAst 61 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_mul_full rfl
    InitECandidate.Solver.Wave8Contracts.M18.m18Callees
    InitECandidate.Solver.Wave8Contracts.M18.m18Callees_good rfl

/-! ## Section 2: `WsByteEff` conversion & call helpers -/

abbrev WsByteEff {F : Type} (s post : PanSemStateFiniteExact 64 F) (Rl : List Ivl) : Prop :=
  R13Shards.Keccak256.ByteEff s post Rl

theorem wsByteEff_of_locFrame {F : Type} {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (h : M13.LocFrame s post) : WsByteEff s post Rl := by
  unfold M13.LocFrame at h
  refine ⟨by rw [h], by rw [h], by rw [h], by rw [h], by rw [h], by rw [h], by rw [h],
    fun _ hne => False.elim (hne (by rw [h])),
    fun _ hne => False.elim (hne (by rw [h])),
    fun b _ hne => False.elim (hne ?_)⟩
  unfold memB; rw [h]

theorem wsByteEff_to_m11_bre {F : Type} {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (h : WsByteEff s post Rl) : M11.ByteRegionEffect s post Rl := by
  refine ⟨h.code, h.memaddrs, h.shMemaddrs, h.baseAddr, h.be, h.globals, ?_, ?_, ?_⟩
  · intro a hna; by_contra hne; exact hna (h.out_dom a hne)
  · intro a hno; by_contra hne
    obtain ⟨i, hi, _, hc1, hc2⟩ := h.cell_frame a hne
    exact hno i hi ⟨hc1, hc2⟩
  · intro b hb hno; by_contra hne
    obtain ⟨i, hi, hin⟩ := h.byte_frame b hb hne
    exact hno i hi hin

theorem flf_call_local_wsByteEff {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hcode : s.code = originalRuntimeCode) {fname : MlS} (hf : M13.FunLocFrame fname)
    (dest : Option (VarKind × MlS)) (hdest : ∀ k n, dest = some (k, n) → k = .local)
    (args : List (ExpHOL 64)) :
    WsByteEff s (evaluateHOLFiniteState s (.call (some (dest, none)) fname args)).2 Rl :=
  wsByteEff_of_locFrame (M13.locFrame_call_local hcode hf dest hdest args)

private theorem guestInv_of_locFrame {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (hlf : M13.LocFrame s t) (hG : GuestInv s) : GuestInv t :=
  ⟨by unfold M13.LocFrame at hlf; rw [hlf]; exact hG.code,
   by unfold M13.LocFrame at hlf; rw [hlf]; exact hG.memaddrs,
   by unfold M13.LocFrame at hlf; rw [hlf]; exact hG.shMemaddrs,
   by unfold M13.LocFrame at hlf; rw [hlf]; exact hG.baseAddr⟩

theorem ro_call_local_eff {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hG : GuestInv s) {fname : MlS}
    (hf : InitECandidate.Solver.Wave8Contracts.M18.ReadOnlyFn fname)
    (dest : Option (VarKind × MlS)) (hdest : ∀ k n, dest = some (k, n) → k = .local)
    (args : List (ExpHOL 64)) :
    let out := evaluateHOLFiniteState s (.call (some (dest, none)) fname args)
    out.1 ≠ some .timeOut →
      (out.1 = none ∨ Resumes out.1) →
      GuestInv out.2 ∧ WsByteEff s out.2 Rl := by
  intro out hnt hres
  dsimp only [out] at hnt hres ⊢
  rcases hf with ⟨params, fbody, ret, hlook, hspec⟩
  rw [evaluateHOLFiniteState_call] at hnt hres ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · rw [hargs] at hres
    exact absurd (hres.resolve_left (by simp)) not_resumes_error
  · rw [hargs] at hnt hres
    dsimp only at hnt hres ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · rw [hl] at hres
      exact absurd (hres.resolve_left (by simp)) not_resumes_error
    · rw [hl] at hnt hres
      dsimp only at hnt hres ⊢
      have hcode := hG.code
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fname params fbody body'
        ret ret' values callee (by rw [hcode]; exact hlook) hl
      by_cases hcz : s.clock = 0
      · rw [if_pos hcz] at hnt; exact absurd rfl hnt
      · rw [if_neg hcz] at hnt hres ⊢
        let ent := callEntryStateHOLFinite s callee
        have hentG : GuestInv ent := guestInv_callEntry s callee hG
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
            some (body', ent.locals, ret') := by
          simpa [ent, callEntryStateHOLFinite, hcode] using hl
        have hl_ret : ret' = ret := by
          have hl_tmp := hl_orig
          unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl_tmp
          split at hl_tmp
          · cases hl_tmp
          · rename_i fb fl fs hfound
            simp only [Option.some.injEq, Prod.mk.injEq] at hl_tmp
            unfold lookupCodeHOLExact at hfound
            rw [hlook] at hfound
            dsimp only at hfound
            split at hfound
            · simp only [Option.some.injEq, Prod.mk.injEq] at hfound
              exact hl_tmp.2.2.symm.trans hfound.2.2.symm
            · cases hfound
        have hbody_eq : fbody = body' := hsame.symm
        subst hbody_eq
        subst hl_ret
        cases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) fbody with
        | mk rb sb =>
          rw [hrun] at hnt hres
          have hnt_b : rb ≠ some .timeOut := by
            rintro rfl; simp at hnt
          have hsp := hspec ent hcode hentG ⟨values, hl_orig⟩ (by dsimp only [ent]; rw [hrun]; exact hnt_b)
          dsimp only [ent] at hsp
          rw [hrun] at hsp
          dsimp only at hsp hnt hres ⊢
          cases rb with
          | none => exact absurd (hres.resolve_left (by simp)) not_resumes_error
          | some r =>
            cases r with
            | timeOut => exact absurd rfl hnt_b
            | returned v =>
              have hlf : sb = { ent with locals := sb.locals, clock := sb.clock } :=
                hsp (Or.inl ⟨v, rfl⟩)
              have hlf_s : M13.LocFrame s sb := by
                unfold M13.LocFrame; rw [hlf]; rfl
              dsimp only at hres ⊢
              by_cases hsh : shapeEqHOL (shapeOfHOLExact v) ret' = true
              · rw [if_pos hsh] at hres ⊢
                rcases dest with _ | ⟨k, nm⟩
                · exact ⟨guestInv_of_locFrame (hlf_s.locals _) hG,
                    (wsByteEff_of_locFrame hlf_s).locals_clock _ _⟩
                · have hk := hdest k nm rfl; subst hk
                  dsimp only at hres ⊢
                  by_cases hval : isValidValueHOLExact s.toExact .local nm v = true
                  · rw [if_pos hval]
                    have hlf2 : M13.LocFrame s (setVarHOLFinite nm v { sb with locals := s.locals }) :=
                      (hlf_s.locals s.locals).setVar nm v
                    exact ⟨guestInv_of_locFrame hlf2 hG, wsByteEff_of_locFrame hlf2⟩
                  · rw [if_neg hval] at hres ⊢
                    exact absurd (hres.resolve_left (by simp)) not_resumes_error
              · rw [if_neg hsh] at hres ⊢
                exact absurd (hres.resolve_left (by simp)) not_resumes_error
            | exception eid ev =>
              dsimp only at hres ⊢
              rcases hres with hnone | hres'
              · simp at hnone
              · rcases hres' with ⟨_, h⟩ | ⟨e, w, h, hne⟩
                · simp at h
                · injection h with h'; injection h' with he hw; subst he hw
                  have hlf : sb = { ent with locals := sb.locals, clock := sb.clock } :=
                    hsp (Or.inr ⟨eid, ev, rfl, hne⟩)
                  have hlf_s : M13.LocFrame s sb := by
                    unfold M13.LocFrame; rw [hlf]; rfl
                  have hlf_e : M13.LocFrame s sb.emptyLocalsHOLFinite := hlf_s.emptyLocals
                  exact ⟨guestInv_of_locFrame hlf_e hG, wsByteEff_of_locFrame hlf_e⟩
            | «break» | «continue» | error =>
              exact absurd (hres.resolve_left (by simp)) not_resumes_error
            | finalFfi _ =>
              rcases hres with hnone | ⟨_, h⟩ | ⟨_, _, h, _⟩
              · simp at hnone
              · simp at h
              · simp at h

theorem ro_decCall_eff {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hG : GuestInv s) {fname : MlS}
    (hf : InitECandidate.Solver.Wave8Contracts.M18.ReadOnlyFn fname)
    (vname : MlS) (sh : ShapeHOL) (args : List (ExpHOL 64)) (cont : ProgHOL 64)
    (hcont : ∀ m : PanSemStateFiniteExact 64 F, GuestInv m →
      (evaluateHOLFiniteState m cont).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState m cont).1 = none ∨ Resumes (evaluateHOLFiniteState m cont).1) →
      GuestInv (evaluateHOLFiniteState m cont).2 ∧ WsByteEff m (evaluateHOLFiniteState m cont).2 Rl) :
    let out := evaluateHOLFiniteState s (.decCall vname sh fname args cont)
    out.1 ≠ some .timeOut →
      (out.1 = none ∨ Resumes out.1) →
      GuestInv out.2 ∧ WsByteEff s out.2 Rl := by
  intro out hnt hres
  dsimp only [out] at hnt hres ⊢
  rcases hf with ⟨params, fbody, ret, hlook, hspec⟩
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · rw [hargs] at hres
    exact absurd (hres.resolve_left (by simp)) not_resumes_error
  · rw [hargs] at hnt hres
    dsimp only at hnt hres ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · rw [hl] at hres
      exact absurd (hres.resolve_left (by simp)) not_resumes_error
    · rw [hl] at hnt hres
      dsimp only at hnt hres ⊢
      have hcode := hG.code
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fname params fbody body'
        ret ret' values callee (by rw [hcode]; exact hlook) hl
      by_cases hcz : s.clock = 0
      · rw [if_pos hcz] at hnt; exact absurd rfl hnt
      · rw [if_neg hcz] at hnt hres ⊢
        let ent := callEntryStateHOLFinite s callee
        have hentG : GuestInv ent := guestInv_callEntry s callee hG
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
            some (body', ent.locals, ret') := by
          simpa [ent, callEntryStateHOLFinite, hcode] using hl
        have hl_ret : ret' = ret := by
          have hl_tmp := hl_orig
          unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl_tmp
          split at hl_tmp
          · cases hl_tmp
          · rename_i fb fl fs hfound
            simp only [Option.some.injEq, Prod.mk.injEq] at hl_tmp
            unfold lookupCodeHOLExact at hfound
            rw [hlook] at hfound
            dsimp only at hfound
            split at hfound
            · simp only [Option.some.injEq, Prod.mk.injEq] at hfound
              exact hl_tmp.2.2.symm.trans hfound.2.2.symm
            · cases hfound
        have hbody_eq : fbody = body' := hsame.symm
        subst hbody_eq
        subst hl_ret
        cases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) fbody with
        | mk rb sb =>
          have hrun1 : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) fbody).1 = rb := by
            rw [hrun]
          have hrun2 : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) fbody).2 = sb := by
            rw [hrun]
          rw [hrun1, hrun2] at hnt hres
          have hnt_b : rb ≠ some .timeOut := by
            rintro rfl; simp at hnt
          have hsp := hspec ent hcode hentG ⟨values, hl_orig⟩ (by dsimp only [ent]; rw [hrun]; exact hnt_b)
          dsimp only [ent] at hsp
          rw [hrun] at hsp
          dsimp only at hsp hnt hres ⊢
          cases rb with
          | none => exact absurd (hres.resolve_left (by simp)) not_resumes_error
          | some r =>
            cases r with
            | timeOut => exact absurd rfl hnt_b
            | returned v =>
              have hlf : sb = { ent with locals := sb.locals, clock := sb.clock } :=
                hsp (Or.inl ⟨v, rfl⟩)
              have hlf_s : M13.LocFrame s sb := by
                unfold M13.LocFrame; rw [hlf]; rfl
              dsimp only at hnt hres ⊢
              by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) sh && shapeEqHOL (shapeOfHOLExact v) ret') = true
              · rw [if_pos hsh] at hnt hres ⊢
                let m := setVarHOLFinite vname v { sb with locals := s.locals }
                have hlf_m : M13.LocFrame s m := (hlf_s.locals s.locals).setVar vname v
                have hmG : GuestInv m := guestInv_of_locFrame hlf_m hG
                cases hc : evaluateHOLFiniteState m cont with
                | mk rc sc =>
                  have hc1 : (evaluateHOLFiniteState m cont).1 = rc := by rw [hc]
                  have hc2 : (evaluateHOLFiniteState m cont).2 = sc := by rw [hc]
                  change (evaluateHOLFiniteState m cont).1 ≠ _ at hnt
                  rw [hc1] at hnt
                  have hnt_c : rc ≠ some .timeOut := hnt
                  have hres_c : rc = none ∨ Resumes rc := by
                    simpa [m, hc1] using hres
                  have ⟨hscG, heff_c⟩ := hcont m hmG (by rw [hc1]; exact hnt_c) (by rw [hc1]; exact hres_c)
                  rw [hc2] at hscG heff_c
                  dsimp only
                  exact ⟨⟨hscG.code, hscG.memaddrs, hscG.shMemaddrs, hscG.baseAddr⟩,
                    ((wsByteEff_of_locFrame hlf_m).trans heff_c).locals_clock _ _⟩
              · rw [if_neg hsh] at hres ⊢
                exact absurd (hres.resolve_left (by simp)) not_resumes_error
            | exception eid ev =>
              dsimp only at hres ⊢
              rcases hres with hnone | hres'
              · simp at hnone
              · rcases hres' with ⟨_, h⟩ | ⟨e, w, h, hne⟩
                · simp at h
                · injection h with h'; injection h' with he hw; subst he hw
                  have hlf : sb = { ent with locals := sb.locals, clock := sb.clock } :=
                    hsp (Or.inr ⟨eid, ev, rfl, hne⟩)
                  have hlf_s : M13.LocFrame s sb := by
                    unfold M13.LocFrame; rw [hlf]; rfl
                  have hlf_e : M13.LocFrame s sb.emptyLocalsHOLFinite := hlf_s.emptyLocals
                  exact ⟨guestInv_of_locFrame hlf_e hG, wsByteEff_of_locFrame hlf_e⟩
            | «break» | «continue» | error =>
              exact absurd (hres.resolve_left (by simp)) not_resumes_error
            | finalFfi _ =>
              rcases hres with hnone | ⟨_, h⟩ | ⟨_, _, h, _⟩
              · simp at hnone
              · simp at h
              · simp at h

/-! ## Section 3: `u256_ws` Layout, `u256_to_digits`, `digits_len`, and Loop Combinator -/

abbrev wsIvl {F : Type} (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  [(globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)]

theorem wsIvl_eq_of_eff {F : Type} {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (h : WsByteEff s post Rl) : wsIvl post = wsIvl s := by
  have hg : globN post "u256_ws" = globN s "u256_ws" := by unfold globN; rw [h.globals]
  simp only [wsIvl, hg]

private theorem ws_word_lookup {F : Type} {s : PanSemStateFiniteExact 64 F} (hA : ArenaOK s) :
    ∃ ws : BitVec 64,
      s.globals.lookup (ofString "u256_ws") = some (.val (.word ws)) ∧
      globN s "u256_ws" = ws.toNat := by
  obtain ⟨ws, hws⟩ := hA.2.2.2.2.2.2.2.2 "u256_ws" (by decide)
  exact ⟨ws, hws, by unfold GlobalWord at hws; simp [globN, hws]⟩

private theorem ws_bounds_of_worldOK {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hW : WorldOK s) (hnz : globN s "u256_ws" ≠ 0) :
    sourceBase ≤ globN s "u256_ws" ∧ globN s "u256_ws" + 640 ≤ heapEnd ∧
    globN s "u256_ws" % 8 = 0 := by
  obtain ⟨hAR, S, _, _, hFT, _⟩ := hW
  have hmem : (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640) ∈ fixedObjects s := by
    unfold fixedObjects
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    exact List.mem_map.2 ⟨("u256_ws", 640), by decide, rfl⟩
  rw [if_neg hnz] at hmem
  rcases hFT.1 _ hmem with h0 | ⟨hal, hwok⟩
  · dsimp only at h0; omega
  · have hhl : heapLimit ≤ heapEnd := by rw [heapLimit_val, heapEnd_val]; decide
    have hse : scratchEnd ≤ heapEnd := by rw [scratchEnd_val, heapEnd_val]; decide
    have hsb_ss : sourceBase ≤ scratchStart := by rw [sourceBase_val, scratchStart_val]; decide
    obtain ⟨_, hhp_hi, hfp_lo, hfp_sp, _⟩ := hAR.2
    rcases hal with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
    · dsimp only at hlo hhi hwok
      exact ⟨hlo, by omega, hwok.1⟩
    · dsimp only at hlo hhi hwok
      exact ⟨by omega, by omega, hwok.1⟩

private theorem lookup_u256_to_digits :
    originalRuntimeCode.lookup (ofString "u256_to_digits") =
      some ([(ofString "p", .one), (ofString "a", .comb [.one, .one, .one, .one])],
            sourceFnBody Guest.Software.guestFn_u256_to_digits, .one) :=
  lookup_of_guestAst_getElem 64 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_to_digits) rfl

private theorem lookup_digits_len :
    originalRuntimeCode.lookup (ofString "digits_len") =
      some ([(ofString "p", .one), (ofString "n", .one)],
            sourceFnBody Guest.Software.guestFn_digits_len, .one) :=
  lookup_of_guestAst_getElem 66 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_digits_len) rfl

private theorem lookup_divmnu :
    originalRuntimeCode.lookup (ofString "divmnu") =
      some ([(ofString "q", .one), (ofString "r", .one), (ofString "u", .one),
             (ofString "m", .one), (ofString "v", .one), (ofString "n", .one)],
            sourceFnBody Guest.Software.guestFn_divmnu, .one) :=
  lookup_of_guestAst_getElem 67 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_divmnu) rfl

private theorem lookup_digits_divmod :
    originalRuntimeCode.lookup (ofString "digits_divmod") =
      some ([(ofString "u", .one), (ofString "m", .one),
             (ofString "d", .comb [.one, .one, .one, .one])],
            sourceFnBody Guest.Software.guestFn_digits_divmod,
            .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 68 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_digits_divmod) rfl

private theorem lookup_u256_divmod :
    originalRuntimeCode.lookup (ofString "u256_divmod") =
      some ([(ofString "a", .comb [.one, .one, .one, .one]),
             (ofString "b", .comb [.one, .one, .one, .one])],
            sourceFnBody Guest.Software.guestFn_u256_divmod,
            .comb [.one, .one, .one, .one, .one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 69 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_divmod) rfl

private theorem lookup_u256_div :
    originalRuntimeCode.lookup (ofString "u256_div") =
      some ([(ofString "a", .comb [.one, .one, .one, .one]),
             (ofString "b", .comb [.one, .one, .one, .one])],
            sourceFnBody Guest.Software.guestFn_u256_div,
            .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 70 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_div) rfl

private theorem lookup_taylor_exponential :
    originalRuntimeCode.lookup (ofString "taylor_exponential") =
      some ([(ofString "factor", .one), (ofString "numerator", .one), (ofString "denominator", .one)],
            sourceFnBody Guest.Software.guestFn_taylor_exponential,
            .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 232 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_taylor_exponential) rfl

private theorem lookup_calculate_blob_gas_price :
    originalRuntimeCode.lookup (ofString "calculate_blob_gas_price") =
      some ([(ofString "excess_blob_gas", .one)],
            sourceFnBody Guest.Software.guestFn_calculate_blob_gas_price,
            .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 233 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_calculate_blob_gas_price) rfl

private theorem eval_word_op {F : Type} (s : PanSemStateFiniteExact 64 F) (op : BinOp)
    (es : List (ExpHOL 64)) :
    ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op op es) = some v → ∃ w : BitVec 64, v = .val (.word w) := by
  intro v hv
  simp only [evalHOLExact] at hv
  split at hv
  · split at hv
    · simp only [Option.map_eq_some_iff] at hv
      obtain ⟨w, _, rfl⟩ := hv
      exact ⟨w, rfl⟩
    · simp at hv
  · simp at hv

private theorem eval_word_local {F : Type} (s : PanSemStateFiniteExact 64 F) (nm : MlS)
    (w0 : BitVec 64) (hlk : s.locals.lookup nm = some (.val (.word w0))) :
    ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local nm) = some v → ∃ w : BitVec 64, v = .val (.word w) := by
  intro v hv
  simp only [evalHOLExact, PanSemStateFiniteExact.toExact, hlk, Option.some.injEq] at hv
  exact ⟨w0, hv.symm⟩

private theorem eval_word_shift {F : Type} (s : PanSemStateFiniteExact 64 F) (sh : Shift)
    (e1 e2 : ExpHOL 64) :
    ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.shift sh e1 e2) = some v → ∃ w : BitVec 64, v = .val (.word w) := by
  intro v hv
  simp only [evalHOLExact] at hv
  split at hv
  · simp only [Option.map_eq_some_iff] at hv
    obtain ⟨w, _, rfl⟩ := hv
    exact ⟨w, rfl⟩
  · simp at hv

private theorem eval_word_const {F : Type} (s : PanSemStateFiniteExact 64 F) (c : BitVec 64) :
    ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.const c) = some v → ∃ w : BitVec 64, v = .val (.word w) := by
  intro v hv
  simp only [evalHOLExact, Option.some.injEq] at hv
  exact ⟨c, hv.symm⟩

private theorem eval_while_wsByteEff {F : Type}
    (cond : ExpHOL 64) (body : ProgHOL 64) (Rl : List Ivl)
    (P : PanSemStateFiniteExact 64 F → Prop)
    (hP_dec : ∀ t, P t → P (decClockHOLFinite t))
    (hbody : ∀ t, P t →
      (evaluateHOLFiniteState t body).1 ≠ some .timeOut →
        (((evaluateHOLFiniteState t body).1 = none ∨
          (evaluateHOLFiniteState t body).1 = some .continue) →
            P (evaluateHOLFiniteState t body).2 ∧
            WsByteEff t (evaluateHOLFiniteState t body).2 Rl) ∧
        ((evaluateHOLFiniteState t body).1 = some .break →
          P (evaluateHOLFiniteState t body).2 ∧
          WsByteEff t (evaluateHOLFiniteState t body).2 Rl) ∧
        (∀ r, (evaluateHOLFiniteState t body).1 = some r →
          r ≠ .continue → r ≠ .break → r ≠ .timeOut →
          ¬ Resumes (some r) ∧ WsByteEff t (evaluateHOLFiniteState t body).2 Rl)) :
    ∀ (k : Nat) (s : PanSemStateFiniteExact 64 F), s.clock = k → P s →
      (evaluateHOLFiniteState s (.while cond body)).1 ≠ some .timeOut →
        ((evaluateHOLFiniteState s (.while cond body)).1 = none →
          P (evaluateHOLFiniteState s (.while cond body)).2 ∧
          WsByteEff s (evaluateHOLFiniteState s (.while cond body)).2 Rl) ∧
        ((evaluateHOLFiniteState s (.while cond body)).1 ≠ none →
          ¬ Resumes (evaluateHOLFiniteState s (.while cond body)).1 ∧
          WsByteEff s (evaluateHOLFiniteState s (.while cond body)).2 Rl) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro s hclk hPs hnt
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    rcases hc : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) cond with
      _ | cv
    · simp only [hc] at hnt ⊢
      exact ⟨fun h => by simp at h, fun _ => ⟨not_resumes_error, R13Shards.Keccak256.ByteEff.refl s Rl⟩⟩
    · simp only [hc] at hnt ⊢
      rcases cv with ⟨⟨w⟩⟩ | _ | _
      · dsimp only at hnt ⊢
        by_cases hw : w = 0
        · subst hw
          exact ⟨fun _ => ⟨hPs, R13Shards.Keccak256.ByteEff.refl s Rl⟩, fun h => False.elim (h rfl)⟩
        · rw [if_pos hw] at hnt ⊢
          by_cases hk0 : s.clock = 0
          · simp [hk0] at hnt
          · rw [if_neg hk0] at hnt ⊢
            have hPd : P (decClockHOLFinite s) := hP_dec s hPs
            have heff_dec : WsByteEff s (decClockHOLFinite s) Rl :=
              (R13Shards.Keccak256.ByteEff.refl s Rl).locals_clock s.locals (s.clock - 1)
            have hb_clk := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
            have hd_clk : (decClockHOLFinite s).clock < k := by
              simp [decClockHOLFinite, hclk]; omega
            rcases hbo : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨rb, sb⟩
            simp only [hbo] at hnt hb_clk ⊢
            have hnt_b : rb ≠ some .timeOut := by
              rintro rfl; exact hnt rfl
            have hb_spec := hbody (decClockHOLFinite s) hPd (by rw [hbo]; exact hnt_b)
            rw [hbo] at hb_spec
            dsimp only at hb_spec
            cases rb with
            | none =>
              obtain ⟨hPsb, heff_b⟩ := hb_spec.1 (Or.inl rfl)
              have jih := ih sb.clock (lt_of_le_of_lt hb_clk hd_clk) sb rfl hPsb hnt
              exact ⟨fun hn => ⟨(jih.1 hn).1, (heff_dec.trans heff_b).trans (jih.1 hn).2⟩,
                fun hnn => ⟨(jih.2 hnn).1, (heff_dec.trans heff_b).trans (jih.2 hnn).2⟩⟩
            | some r =>
              cases r with
              | «continue» =>
                obtain ⟨hPsb, heff_b⟩ := hb_spec.1 (Or.inr rfl)
                have jih := ih sb.clock (lt_of_le_of_lt hb_clk hd_clk) sb rfl hPsb hnt
                exact ⟨fun hn => ⟨(jih.1 hn).1, (heff_dec.trans heff_b).trans (jih.1 hn).2⟩,
                  fun hnn => ⟨(jih.2 hnn).1, (heff_dec.trans heff_b).trans (jih.2 hnn).2⟩⟩
              | «break» =>
                obtain ⟨hPsb, heff_b⟩ := hb_spec.2.1 rfl
                exact ⟨fun _ => ⟨hPsb, heff_dec.trans heff_b⟩, fun h => absurd rfl h⟩
              | timeOut => exact absurd rfl hnt_b
              | error =>
                have ⟨hnr, heff_b⟩ := hb_spec.2.2 .error rfl (by simp) (by simp) (by simp)
                exact ⟨fun h => by simp at h, fun _ => ⟨hnr, heff_dec.trans heff_b⟩⟩
              | returned rv =>
                have ⟨hnr, heff_b⟩ := hb_spec.2.2 (.returned rv) rfl (by simp) (by simp) (by simp)
                exact ⟨fun h => by simp at h, fun _ => ⟨hnr, heff_dec.trans heff_b⟩⟩
              | exception eid ev =>
                have ⟨hnr, heff_b⟩ := hb_spec.2.2 (.exception eid ev) rfl (by simp) (by simp) (by simp)
                exact ⟨fun h => by simp at h, fun _ => ⟨hnr, heff_dec.trans heff_b⟩⟩
              | finalFfi ev =>
                have ⟨hnr, heff_b⟩ := hb_spec.2.2 (.finalFfi ev) rfl (by simp) (by simp) (by simp)
                exact ⟨fun h => by simp at h, fun _ => ⟨hnr, heff_dec.trans heff_b⟩⟩
      · exact ⟨fun h => by simp at h, fun _ => ⟨not_resumes_error, R13Shards.Keccak256.ByteEff.refl s Rl⟩⟩
      · exact ⟨fun h => by simp at h, fun _ => ⟨not_resumes_error, R13Shards.Keccak256.ByteEff.refl s Rl⟩⟩

private theorem eval_word_rField {F : Type} (s : PanSemStateFiniteExact 64 F) (idx : Nat)
    (nm : MlS) (w0 w1 : BitVec 64)
    (hlk : s.locals.lookup nm = some (.rStruct [.val (.word w0), .val (.word w1)]))
    (hidx : idx < 2) :
    ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.rfield idx (.var .local nm)) = some v → ∃ w : BitVec 64, v = .val (.word w) := by
  intro v hv
  match idx, hidx with
  | 0, _ =>
    simp only [evalHOLExact, PanSemStateFiniteExact.toExact, hlk, List.getElem?_cons_zero,
      Option.some.injEq] at hv
    exact ⟨w0, hv.symm⟩
  | 1, _ =>
    simp only [evalHOLExact, PanSemStateFiniteExact.toExact, hlk, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.some.injEq] at hv
    exact ⟨w1, hv.symm⟩

private theorem store_one_step_mem {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hG : GuestInv s) (dstExp valExp : ExpHOL 64) (addr wval : BitVec 64)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      dstExp = some (.val (.word addr)))
    (hval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      valExp = some (.val (.word wval)))
    (hin : s.memaddrs addr → ∃ i ∈ Rl, i.1 ≤ addr.toNat ∧ addr.toNat + 8 ≤ i.1 + i.2) :
    let out := evaluateHOLFiniteState s (.store dstExp valExp)
    (out.1 = none →
      GuestInv out.2 ∧ WsByteEff s out.2 Rl ∧ out.2.locals = s.locals ∧
      s.memaddrs addr ∧ out.2.memory addr = .word wval ∧
      (∀ x : BitVec 64, x ≠ addr → out.2.memory x = s.memory x)) ∧
    (out.1 ≠ none → out.1 = some .error ∧ WsByteEff s out.2 Rl) := by
  dsimp only
  rw [evaluateHOLFiniteState_store]
  rw [hdst]
  dsimp only
  rw [hval]
  dsimp only
  by_cases hdom : s.memaddrs addr
  · have hstores : @panMemStoresHOL 64 _ addr (flattenHOL (.val (.word wval))) s.memaddrs
        (fun a => Classical.propDecidable (s.memaddrs a)) s.memory =
        some (fun x => if x = addr then .word wval else s.memory x) := by
      simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom]
    rw [hstores]
    dsimp only
    obtain ⟨ivl, hivl, hi1, hi2⟩ := hin hdom
    have hdom_ord : addr.toNat % 8 = 0 ∧ sourceBase ≤ addr.toNat ∧ addr.toNat < heapEnd := by
      rw [hG.memaddrs, ordinaryDomain_iff] at hdom; exact hdom
    have hhe8 : heapEnd % 8 = 0 := by decide
    have heff : WsByteEff s { s with memory := fun x => if x = addr then .word wval else s.memory x } Rl := by
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · intro a hne; by_cases hax : a = addr
        · subst hax; exact hdom
        · simp [hax] at hne
      · intro a hne; by_cases hax : a = addr
        · subst hax; exact ⟨ivl, hivl, by omega, by omega, by omega⟩
        · simp [hax] at hne
      · intro b hb hne
        by_cases hal : panByteAlignHOL (BitVec.ofNat 64 b) = addr
        · have hc_nat := panByteAlign_toNat64 (BitVec.ofNat 64 b)
          rw [hal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb] at hc_nat
          exact ⟨ivl, hivl, by omega, by omega⟩
        · unfold memB at hne; simp [hal] at hne
    exact ⟨fun _ => ⟨guestInv_congr (s := s) rfl rfl rfl rfl hG, heff, rfl, hdom, by simp,
      fun x hx => by simp [hx]⟩, fun h => absurd rfl h⟩
  · have hstores : @panMemStoresHOL 64 _ addr (flattenHOL (.val (.word wval))) s.memaddrs
        (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = none := by
      simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom]
    rw [hstores]
    exact ⟨fun h => by simp at h, fun _ => ⟨rfl, R13Shards.Keccak256.ByteEff.refl s Rl⟩⟩

private theorem store_one_abort_lt_sourceBase {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hG : GuestInv s) (dstExp valExp : ExpHOL 64) (addr : BitVec 64)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      dstExp = some (.val (.word addr)))
    (hval_one : ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      valExp = some v → ∃ w : BitVec 64, v = .val (.word w))
    (hlt : addr.toNat < sourceBase) :
    let out := evaluateHOLFiniteState s (.store dstExp valExp)
    out.1 = some .error ∧ out.2 = s := by
  dsimp only
  rw [evaluateHOLFiniteState_store, hdst]
  dsimp only
  split
  · rename_i val hval
    obtain ⟨wval, rfl⟩ := hval_one val hval
    have hndom : ¬ s.memaddrs addr := by
      rw [hG.memaddrs, ordinaryDomain_iff]; omega
    have hstores : @panMemStoresHOL 64 _ addr (flattenHOL (.val (.word wval))) s.memaddrs
        (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = none := by
      simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hndom]
    rw [hstores]; exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-! ### `u256_to_digits` frame & stored digits -/

private def u256Digit (a0 a1 a2 a3 : BitVec 64) : Nat → BitVec 64
  | 0 => a0 &&& 4294967295#64
  | 1 => a0 >>> 32
  | 2 => a1 &&& 4294967295#64
  | 3 => a1 >>> 32
  | 4 => a2 &&& 4294967295#64
  | 5 => a2 >>> 32
  | 6 => a3 &&& 4294967295#64
  | _ => a3 >>> 32

private theorem u256Digit_nonzero_of_or_nonzero {a0 a1 a2 a3 : BitVec 64}
    (hnz : (a0 ||| a1 ||| a2 ||| a3) ≠ 0#64) :
    ∃ idx : Nat, idx < 8 ∧ u256Digit a0 a1 a2 a3 idx ≠ 0#64 := by
  by_contra hall
  have hall' : ∀ idx < 8, u256Digit a0 a1 a2 a3 idx = 0#64 := by
    intro idx hidx
    by_contra hne
    exact hall ⟨idx, hidx, hne⟩
  have h0 : a0 &&& 4294967295#64 = 0#64 := hall' 0 (by omega)
  have h1 : a0 >>> 32 = 0#64 := hall' 1 (by omega)
  have h2 : a1 &&& 4294967295#64 = 0#64 := hall' 2 (by omega)
  have h3 : a1 >>> 32 = 0#64 := hall' 3 (by omega)
  have h4 : a2 &&& 4294967295#64 = 0#64 := hall' 4 (by omega)
  have h5 : a2 >>> 32 = 0#64 := hall' 5 (by omega)
  have h6 : a3 &&& 4294967295#64 = 0#64 := hall' 6 (by omega)
  have h7 : a3 >>> 32 = 0#64 := hall' 7 (by omega)
  have split64 : ∀ x : BitVec 64, x &&& 4294967295#64 = 0#64 → x >>> 32 = 0#64 → x = 0#64 := by
    intro x hlo hhi
    apply BitVec.eq_of_toNat_eq
    have hx := x.isLt
    have hlo_n : (x &&& 4294967295#64).toNat = x.toNat % 4294967296 := by
      rw [BitVec.toNat_and]
      change x.toNat &&& (2 ^ 32 - 1) = x.toNat % 4294967296
      exact Nat.and_two_pow_sub_one_eq_mod x.toNat 32
    have hhi_n : (x >>> 32).toNat = x.toNat / 4294967296 := by
      change x.toNat >>> 32 = x.toNat / 4294967296
      rw [Nat.shiftRight_eq_div_pow]
    have hlo0 : x.toNat % 4294967296 = 0 := by rw [← hlo_n, hlo]; rfl
    have hhi0 : x.toNat / 4294967296 = 0 := by rw [← hhi_n, hhi]; rfl
    change x.toNat = 0
    omega
  have ha0 := split64 a0 h0 h1
  have ha1 := split64 a1 h2 h3
  have ha2 := split64 a2 h4 h5
  have ha3 := split64 a3 h6 h7
  subst ha0 ha1 ha2 ha3
  exact hnz (by decide)

private theorem u256_to_digits_body_spec {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hG : GuestInv s) (p a0 a1 a2 a3 : BitVec 64)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word p)))
    (ha : s.locals.lookup (ofString "a") =
      some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)]))
    (hcov : sourceBase ≤ p.toNat → p.toNat + 64 ≤ heapEnd ∧
      ∃ ivl ∈ Rl, ivl.1 ≤ p.toNat ∧ p.toNat + 64 ≤ ivl.1 + ivl.2) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_to_digits)
    out.1 ≠ some .timeOut ∧
    (p.toNat < sourceBase → out.1 = some .error ∧ WsByteEff s out.2 Rl) ∧
    (∀ rv, out.1 = some (.returned rv) →
      rv = .val (.word 0#64) ∧ GuestInv out.2 ∧ WsByteEff s out.2 Rl ∧
      sourceBase ≤ p.toNat ∧ p.toNat + 64 ≤ heapEnd ∧ p.toNat % 8 = 0 ∧
      ∀ idx : Nat, idx < 8 →
        out.2.memaddrs (p + BitVec.ofNat 64 (8 * idx)) ∧
        out.2.memory (p + BitVec.ofNat 64 (8 * idx)) = .word (u256Digit a0 a1 a2 a3 idx)) ∧
    ((∀ rv, out.1 ≠ some (.returned rv)) → ¬ Resumes out.1 ∧ WsByteEff s out.2 Rl) := by
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  have hbody : sourceFnBody Guest.Software.guestFn_u256_to_digits =
      .seq (.store (.var .local (ofString "p"))
          (.op .and [.rfield 0 (.var .local (ofString "a")), .const 4294967295#64]))
      (.seq (.store (.op .add [.var .local (ofString "p"), .const 8#64])
          (.shift .lsr (.rfield 0 (.var .local (ofString "a"))) (.const 32#64)))
      (.seq (.store (.op .add [.var .local (ofString "p"), .const 16#64])
          (.op .and [.rfield 1 (.var .local (ofString "a")), .const 4294967295#64]))
      (.seq (.store (.op .add [.var .local (ofString "p"), .const 24#64])
          (.shift .lsr (.rfield 1 (.var .local (ofString "a"))) (.const 32#64)))
      (.seq (.store (.op .add [.var .local (ofString "p"), .const 32#64])
          (.op .and [.rfield 2 (.var .local (ofString "a")), .const 4294967295#64]))
      (.seq (.store (.op .add [.var .local (ofString "p"), .const 40#64])
          (.shift .lsr (.rfield 2 (.var .local (ofString "a"))) (.const 32#64)))
      (.seq (.store (.op .add [.var .local (ofString "p"), .const 48#64])
          (.op .and [.rfield 3 (.var .local (ofString "a")), .const 4294967295#64]))
      (.seq (.store (.op .add [.var .local (ofString "p"), .const 56#64])
          (.shift .lsr (.rfield 3 (.var .local (ofString "a"))) (.const 32#64)))
        (.return (.const 0#64))))))))) := rfl
  dsimp only
  rw [hbody]
  by_cases hlt : p.toNat < sourceBase
  · rw [evaluateHOLFiniteState_seq_line780]
    have hdst0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.var .local (ofString "p")) = some (.val (.word p)) := by
      simp [evalHOLExact, PanSemStateFiniteExact.toExact, hp]
    have hab := store_one_abort_lt_sourceBase hG _
      (.op .and [.rfield 0 (.var .local (ofString "a")), .const 4294967295#64])
      p hdst0 (eval_word_op s .and _) hlt
    rcases hr0 : evaluateHOLFiniteState s _ with ⟨r0, s1⟩
    rw [hr0] at hab; dsimp only at hab ⊢
    rw [hab.1, hab.2]
    exact ⟨by simp, fun _ => ⟨rfl, R13Shards.Keccak256.ByteEff.refl s Rl⟩,
      fun _ h => by simp at h,
      fun _ => ⟨not_resumes_error, R13Shards.Keccak256.ByteEff.refl s Rl⟩⟩
  · have hge : sourceBase ≤ p.toNat := by omega
    obtain ⟨hphi, ivl, hivl, hi1, hi2⟩ := hcov hge
    have hhin : ∀ (t : PanSemStateFiniteExact 64 F) (off : Nat), off + 8 ≤ 64 →
        t.memaddrs (p + BitVec.ofNat 64 off) →
        ∃ i ∈ Rl, i.1 ≤ (p + BitVec.ofNat 64 off).toNat ∧ (p + BitVec.ofNat 64 off).toNat + 8 ≤ i.1 + i.2 := by
      intro t off hoff _
      have hadd : (p + BitVec.ofNat 64 off).toNat = p.toNat + off := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      exact ⟨ivl, hivl, by omega, by omega⟩
    have h32_nat : (32#64 : BitVec 64).toNat = 32 := rfl
    have mk_dst0 : ∀ (t : PanSemStateFiniteExact 64 F),
        t.locals.lookup (ofString "p") = some (.val (.word p)) →
        @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.var .local (ofString "p")) = some (.val (.word p)) := by
      intro t htp; simp [evalHOLExact, PanSemStateFiniteExact.toExact, htp]
    have mk_dst : ∀ (t : PanSemStateFiniteExact 64 F) (c : BitVec 64),
        t.locals.lookup (ofString "p") = some (.val (.word p)) →
        @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.op .add [.var .local (ofString "p"), .const c]) = some (.val (.word (p + c))) := by
      intro t c htp
      simp [evalHOLExact, evalListHOLExact, PanSemStateFiniteExact.toExact, htp,
        valueIsWord, valueWord, wordOpHOL, wordOp]
    have mk_and : ∀ (t : PanSemStateFiniteExact 64 F) (idx : Nat) (ak : BitVec 64),
        t.locals.lookup (ofString "a") =
          some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)]) →
        ([.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)] : List (ValueHOL 64))[idx]? =
          some (.val (.word ak)) →
        @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.op .and [.rfield idx (.var .local (ofString "a")), .const 4294967295#64]) =
          some (.val (.word (ak &&& 4294967295#64))) := by
      intro t idx ak hta hget
      simp [evalHOLExact, evalListHOLExact, PanSemStateFiniteExact.toExact, hta, hget,
        valueIsWord, valueWord, wordOpHOL, wordOp]
    have mk_lsr : ∀ (t : PanSemStateFiniteExact 64 F) (idx : Nat) (ak : BitVec 64),
        t.locals.lookup (ofString "a") =
          some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)]) →
        ([.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)] : List (ValueHOL 64))[idx]? =
          some (.val (.word ak)) →
        @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.shift .lsr (.rfield idx (.var .local (ofString "a"))) (.const 32#64)) =
          some (.val (.word (ak >>> 32))) := by
      intro t idx ak hta hget
      simp [evalHOLExact, PanSemStateFiniteExact.toExact, hta, hget, wordShiftHOL, h32_nat]
    rw [evaluateHOLFiniteState_seq_line780]
    have h0 := store_one_step_mem (Rl := Rl) hG _ _ p (a0 &&& 4294967295#64)
      (mk_dst0 s hp) (mk_and s 0 a0 ha rfl)
      (by simpa using hhin s 0 (by omega))
    rcases hr0 : evaluateHOLFiniteState s _ with ⟨r0, s1⟩
    rw [hr0] at h0; dsimp only at h0 ⊢
    cases r0 with
    | some r0 =>
      obtain ⟨herr, heff⟩ := h0.2 (by simp)
      injection herr with herr'; subst herr'
      exact ⟨by simp, fun h => absurd h hlt, fun _ h => by simp at h, fun _ => ⟨not_resumes_error, heff⟩⟩
    | none =>
      obtain ⟨hG1, heff1, hloc1, hdom0, hm0, hne1⟩ := h0.1 rfl
      have hp1 : s1.locals.lookup (ofString "p") = some (.val (.word p)) := hloc1 ▸ hp
      have ha1 : s1.locals.lookup (ofString "a") = _ := hloc1 ▸ ha
      have hp8 : p.toNat % 8 = 0 := by
        rw [hG.memaddrs, ordinaryDomain_iff] at hdom0; exact hdom0.1
      rw [evaluateHOLFiniteState_seq_line780]
      have h1 := store_one_step_mem (Rl := Rl) hG1 _ _ (p + 8#64) (a0 >>> 32)
        (mk_dst s1 8#64 hp1) (mk_lsr s1 0 a0 ha1 rfl) (hhin s1 8 (by omega))
      rcases hr1 : evaluateHOLFiniteState s1 _ with ⟨r1, s2⟩
      rw [hr1] at h1; dsimp only at h1 ⊢
      cases r1 with
      | some r1 =>
        obtain ⟨herr, heff⟩ := h1.2 (by simp)
        injection herr with herr'; subst herr'
        exact ⟨by simp, fun h => absurd h hlt, fun _ h => by simp at h,
          fun _ => ⟨not_resumes_error, heff1.trans heff⟩⟩
      | none =>
        obtain ⟨hG2, heff2, hloc2, hdom1, hm1, hne2⟩ := h1.1 rfl
        have hp2 : s2.locals.lookup (ofString "p") = some (.val (.word p)) := hloc2 ▸ hp1
        have ha2 : s2.locals.lookup (ofString "a") = _ := hloc2 ▸ ha1
        rw [evaluateHOLFiniteState_seq_line780]
        have h2 := store_one_step_mem (Rl := Rl) hG2 _ _ (p + 16#64) (a1 &&& 4294967295#64)
          (mk_dst s2 16#64 hp2) (mk_and s2 1 a1 ha2 rfl) (hhin s2 16 (by omega))
        rcases hr2 : evaluateHOLFiniteState s2 _ with ⟨r2, s3⟩
        rw [hr2] at h2; dsimp only at h2 ⊢
        cases r2 with
        | some r2 =>
          obtain ⟨herr, heff⟩ := h2.2 (by simp)
          injection herr with herr'; subst herr'
          exact ⟨by simp, fun h => absurd h hlt, fun _ h => by simp at h,
            fun _ => ⟨not_resumes_error, (heff1.trans heff2).trans heff⟩⟩
        | none =>
          obtain ⟨hG3, heff3, hloc3, hdom2, hm2, hne3⟩ := h2.1 rfl
          have hp3 : s3.locals.lookup (ofString "p") = some (.val (.word p)) := hloc3 ▸ hp2
          have ha3 : s3.locals.lookup (ofString "a") = _ := hloc3 ▸ ha2
          rw [evaluateHOLFiniteState_seq_line780]
          have h3 := store_one_step_mem (Rl := Rl) hG3 _ _ (p + 24#64) (a1 >>> 32)
            (mk_dst s3 24#64 hp3) (mk_lsr s3 1 a1 ha3 rfl) (hhin s3 24 (by omega))
          rcases hr3 : evaluateHOLFiniteState s3 _ with ⟨r3, s4⟩
          rw [hr3] at h3; dsimp only at h3 ⊢
          cases r3 with
          | some r3 =>
            obtain ⟨herr, heff⟩ := h3.2 (by simp)
            injection herr with herr'; subst herr'
            exact ⟨by simp, fun h => absurd h hlt, fun _ h => by simp at h,
              fun _ => ⟨not_resumes_error, ((heff1.trans heff2).trans heff3).trans heff⟩⟩
          | none =>
            obtain ⟨hG4, heff4, hloc4, hdom3, hm3, hne4⟩ := h3.1 rfl
            have hp4 : s4.locals.lookup (ofString "p") = some (.val (.word p)) := hloc4 ▸ hp3
            have ha4 : s4.locals.lookup (ofString "a") = _ := hloc4 ▸ ha3
            rw [evaluateHOLFiniteState_seq_line780]
            have h4 := store_one_step_mem (Rl := Rl) hG4 _ _ (p + 32#64) (a2 &&& 4294967295#64)
              (mk_dst s4 32#64 hp4) (mk_and s4 2 a2 ha4 rfl) (hhin s4 32 (by omega))
            rcases hr4 : evaluateHOLFiniteState s4 _ with ⟨r4, s5⟩
            rw [hr4] at h4; dsimp only at h4 ⊢
            cases r4 with
            | some r4 =>
              obtain ⟨herr, heff⟩ := h4.2 (by simp)
              injection herr with herr'; subst herr'
              exact ⟨by simp, fun h => absurd h hlt, fun _ h => by simp at h,
                fun _ => ⟨not_resumes_error, (((heff1.trans heff2).trans heff3).trans heff4).trans heff⟩⟩
            | none =>
              obtain ⟨hG5, heff5, hloc5, hdom4, hm4, hne5⟩ := h4.1 rfl
              have hp5 : s5.locals.lookup (ofString "p") = some (.val (.word p)) := hloc5 ▸ hp4
              have ha5 : s5.locals.lookup (ofString "a") = _ := hloc5 ▸ ha4
              rw [evaluateHOLFiniteState_seq_line780]
              have h5 := store_one_step_mem (Rl := Rl) hG5 _ _ (p + 40#64) (a2 >>> 32)
                (mk_dst s5 40#64 hp5) (mk_lsr s5 2 a2 ha5 rfl) (hhin s5 40 (by omega))
              rcases hr5 : evaluateHOLFiniteState s5 _ with ⟨r5, s6⟩
              rw [hr5] at h5; dsimp only at h5 ⊢
              cases r5 with
              | some r5 =>
                obtain ⟨herr, heff⟩ := h5.2 (by simp)
                injection herr with herr'; subst herr'
                exact ⟨by simp, fun h => absurd h hlt, fun _ h => by simp at h,
                  fun _ => ⟨not_resumes_error, ((((heff1.trans heff2).trans heff3).trans heff4).trans heff5).trans heff⟩⟩
              | none =>
                obtain ⟨hG6, heff6, hloc6, hdom5, hm5, hne6⟩ := h5.1 rfl
                have hp6 : s6.locals.lookup (ofString "p") = some (.val (.word p)) := hloc6 ▸ hp5
                have ha6 : s6.locals.lookup (ofString "a") = _ := hloc6 ▸ ha5
                rw [evaluateHOLFiniteState_seq_line780]
                have h6 := store_one_step_mem (Rl := Rl) hG6 _ _ (p + 48#64) (a3 &&& 4294967295#64)
                  (mk_dst s6 48#64 hp6) (mk_and s6 3 a3 ha6 rfl) (hhin s6 48 (by omega))
                rcases hr6 : evaluateHOLFiniteState s6 _ with ⟨r6, s7⟩
                rw [hr6] at h6; dsimp only at h6 ⊢
                cases r6 with
                | some r6 =>
                  obtain ⟨herr, heff⟩ := h6.2 (by simp)
                  injection herr with herr'; subst herr'
                  exact ⟨by simp, fun h => absurd h hlt, fun _ h => by simp at h,
                    fun _ => ⟨not_resumes_error, (((((heff1.trans heff2).trans heff3).trans heff4).trans heff5).trans heff6).trans heff⟩⟩
                | none =>
                  obtain ⟨hG7, heff7, hloc7, hdom6, hm6, hne7⟩ := h6.1 rfl
                  have hp7 : s7.locals.lookup (ofString "p") = some (.val (.word p)) := hloc7 ▸ hp6
                  have ha7 : s7.locals.lookup (ofString "a") = _ := hloc7 ▸ ha6
                  rw [evaluateHOLFiniteState_seq_line780]
                  have h7 := store_one_step_mem (Rl := Rl) hG7 _ _ (p + 56#64) (a3 >>> 32)
                    (mk_dst s7 56#64 hp7) (mk_lsr s7 3 a3 ha7 rfl) (hhin s7 56 (by omega))
                  rcases hr7 : evaluateHOLFiniteState s7 _ with ⟨r7, s8⟩
                  rw [hr7] at h7; dsimp only at h7 ⊢
                  cases r7 with
                  | some r7 =>
                    obtain ⟨herr, heff⟩ := h7.2 (by simp)
                    injection herr with herr'; subst herr'
                    exact ⟨by simp, fun h => absurd h hlt, fun _ h => by simp at h,
                      fun _ => ⟨not_resumes_error, ((((((heff1.trans heff2).trans heff3).trans heff4).trans heff5).trans heff6).trans heff7).trans heff⟩⟩
                  | none =>
                    obtain ⟨hG8, heff8, _, hdom7, hm7, hne8⟩ := h7.1 rfl
                    have heff_all : WsByteEff s s8 Rl :=
                      ((((((heff1.trans heff2).trans heff3).trans heff4).trans heff5).trans heff6).trans heff7).trans heff8
                    rw [evaluateHOLFiniteState_return]
                    simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL,
                      show (1 : Nat) ≤ 32 by decide, ↓reduceIte]
                    refine ⟨by simp, fun h => absurd h hlt, ?_, fun h => absurd rfl (h _)⟩
                    intro rv hrv
                    injection hrv with hrv'; injection hrv' with hrv''; subst hrv''
                    have hG_post : GuestInv s8.emptyLocalsHOLFinite :=
                      guestInv_congr (s := s8) rfl rfl rfl rfl hG8
                    have heff_post : WsByteEff s s8.emptyLocalsHOLFinite Rl :=
                      heff_all.locals_clock _ _
                    refine ⟨rfl, hG_post, heff_post, hge, hphi, hp8, ?_⟩
                    intro idx hidx
                    have hne_off : ∀ (o1 o2 : Nat), o1 + 8 ≤ 64 → o2 + 8 ≤ 64 → o1 ≠ o2 →
                        p + BitVec.ofNat 64 o1 ≠ p + BitVec.ofNat 64 o2 := by
                      intro o1 o2 ho1 ho2 hne heq
                      have h1n : (p + BitVec.ofNat 64 o1).toNat = p.toNat + o1 := by
                        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                      have h2n : (p + BitVec.ofNat 64 o2).toNat = p.toNat + o2 := by
                        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                      have := congrArg BitVec.toNat heq
                      omega
                    have hdom_idx : s8.emptyLocalsHOLFinite.memaddrs (p + BitVec.ofNat 64 (8 * idx)) := by
                      rw [hG_post.memaddrs, ordinaryDomain_iff]
                      have hadd : (p + BitVec.ofNat 64 (8 * idx)).toNat = p.toNat + 8 * idx := by
                        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                      exact ⟨by omega, by omega, by omega⟩
                    refine ⟨hdom_idx, ?_⟩
                    change s8.memory (p + BitVec.ofNat 64 (8 * idx)) = _
                    have hp0_eq : p + BitVec.ofNat 64 0 = p := by simp
                    match idx, hidx with
                    | 0, _ =>
                      rw [Nat.mul_zero, hne8 _ (hne_off 0 56 (by omega) (by omega) (by omega)),
                          hne7 _ (hne_off 0 48 (by omega) (by omega) (by omega)),
                          hne6 _ (hne_off 0 40 (by omega) (by omega) (by omega)),
                          hne5 _ (hne_off 0 32 (by omega) (by omega) (by omega)),
                          hne4 _ (hne_off 0 24 (by omega) (by omega) (by omega)),
                          hne3 _ (hne_off 0 16 (by omega) (by omega) (by omega)),
                          hne2 _ (hne_off 0 8 (by omega) (by omega) (by omega)),
                          hp0_eq, hm0]
                      rfl
                    | 1, _ =>
                      rw [show 8 * 1 = 8 from rfl,
                          hne8 _ (hne_off 8 56 (by omega) (by omega) (by omega)),
                          hne7 _ (hne_off 8 48 (by omega) (by omega) (by omega)),
                          hne6 _ (hne_off 8 40 (by omega) (by omega) (by omega)),
                          hne5 _ (hne_off 8 32 (by omega) (by omega) (by omega)),
                          hne4 _ (hne_off 8 24 (by omega) (by omega) (by omega)),
                          hne3 _ (hne_off 8 16 (by omega) (by omega) (by omega))]
                      exact hm1
                    | 2, _ =>
                      rw [show 8 * 2 = 16 from rfl,
                          hne8 _ (hne_off 16 56 (by omega) (by omega) (by omega)),
                          hne7 _ (hne_off 16 48 (by omega) (by omega) (by omega)),
                          hne6 _ (hne_off 16 40 (by omega) (by omega) (by omega)),
                          hne5 _ (hne_off 16 32 (by omega) (by omega) (by omega)),
                          hne4 _ (hne_off 16 24 (by omega) (by omega) (by omega))]
                      exact hm2
                    | 3, _ =>
                      rw [show 8 * 3 = 24 from rfl,
                          hne8 _ (hne_off 24 56 (by omega) (by omega) (by omega)),
                          hne7 _ (hne_off 24 48 (by omega) (by omega) (by omega)),
                          hne6 _ (hne_off 24 40 (by omega) (by omega) (by omega)),
                          hne5 _ (hne_off 24 32 (by omega) (by omega) (by omega))]
                      exact hm3
                    | 4, _ =>
                      rw [show 8 * 4 = 32 from rfl,
                          hne8 _ (hne_off 32 56 (by omega) (by omega) (by omega)),
                          hne7 _ (hne_off 32 48 (by omega) (by omega) (by omega)),
                          hne6 _ (hne_off 32 40 (by omega) (by omega) (by omega))]
                      exact hm4
                    | 5, _ =>
                      rw [show 8 * 5 = 40 from rfl,
                          hne8 _ (hne_off 40 56 (by omega) (by omega) (by omega)),
                          hne7 _ (hne_off 40 48 (by omega) (by omega) (by omega))]
                      exact hm5
                    | 6, _ =>
                      rw [show 8 * 6 = 48 from rfl,
                          hne8 _ (hne_off 48 56 (by omega) (by omega) (by omega))]
                      exact hm6
                    | 7, _ =>
                      rw [show 8 * 7 = 56 from rfl]
                      exact hm7

/-! ## Section 4: `u256_to_digits` call, `digits_len` bounds, and `divmnu` -/

private theorem two_arg_lookup {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name first second : MlS) (ps1 ps2 rs : ShapeHOL) (body : ProgHOL width) (v1 v2 : ValueHOL width)
    (different : first ≠ second)
    (hshape1 : shapeEqHOL ps1 (shapeOfHOLExact v1) = true)
    (hshape2 : shapeEqHOL ps2 (shapeOfHOLExact v2) = true)
    (lookup : code name = some ([(first, ps1), (second, ps2)], body, rs)) :
    PanSemStateFiniteExact.lookupCodeHOLFinite code name [v1, v2] =
      some (body, (HolFiniteMapExact.empty.update (first, v1)).update (second, v2), rs) := by
  have raw : lookupCodeHOLExact code name [v1, v2] =
      some (body, (fun key => if key = second then some v2 else if key = first then some v1 else none), rs) := by
    simp [lookupCodeHOLExact, lookup, hshape1, hshape2, different]
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i missing
    rw [raw] at missing
    cases missing
  · rename_i foundBody foundLocals foundShape found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun locals => some (foundBody, locals, foundShape))
    apply HolFiniteMapExact.ext
    funext key
    by_cases two : key = second
    · subst two
      simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty]
    · have backTwo : second ≠ key := Ne.symm two
      by_cases one : key = first
      · subst one
        simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, different, Ne.symm different]
      · have backOne : first ≠ key := Ne.symm one
        simp [one, two, backOne, backTwo, HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]

private theorem u256_to_digits_call_spec {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hG : GuestInv s) (pExp aExp : ExpHOL 64) (p a0 a1 a2 a3 : BitVec 64)
    (hp : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      pExp = some (.val (.word p)))
    (ha : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      aExp = some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)]))
    (hcov : sourceBase ≤ p.toNat → p.toNat + 64 ≤ heapEnd ∧
      ∃ ivl ∈ Rl, ivl.1 ≤ p.toNat ∧ p.toNat + 64 ≤ ivl.1 + ivl.2) :
    let out := evaluateHOLFiniteState s (.call (some (none, none)) (ofString "u256_to_digits") [pExp, aExp])
    out.1 ≠ some .timeOut →
      (p.toNat < sourceBase → out.1 = some .error ∧ WsByteEff s out.2 Rl) ∧
      (out.1 = none →
        GuestInv out.2 ∧ WsByteEff s out.2 Rl ∧ out.2.locals = s.locals ∧
        sourceBase ≤ p.toNat ∧ p.toNat + 64 ≤ heapEnd ∧ p.toNat % 8 = 0 ∧
        ∀ idx : Nat, idx < 8 →
          out.2.memaddrs (p + BitVec.ofNat 64 (8 * idx)) ∧
          out.2.memory (p + BitVec.ofNat 64 (8 * idx)) = .word (u256Digit a0 a1 a2 a3 idx)) ∧
      (out.1 ≠ none → ¬ Resumes out.1 ∧ WsByteEff s out.2 Rl) := by
  intro out hnt
  dsimp only [out] at hnt ⊢
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [pExp, aExp] =
      some [.val (.word p), .rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)]] := by
    simp [evalListHOLFinite, evalListHOLExact, hp, ha]
  rw [hargs] at hnt ⊢
  dsimp only at hnt ⊢
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "p", .val (.word p))).update
      (ofString "a", .rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)])
  have hlk : lookupCodeHOLFinite s.code.lookup (ofString "u256_to_digits")
      [.val (.word p), .rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)]] =
      some (sourceFnBody Guest.Software.guestFn_u256_to_digits, callee, .one) := by
    apply two_arg_lookup s.code.lookup (ofString "u256_to_digits")
      (ofString "p") (ofString "a") .one (.comb [.one, .one, .one, .one]) .one
      (sourceFnBody Guest.Software.guestFn_u256_to_digits)
      (.val (.word p)) (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)])
      (by decide)
    · simp [shapeOfHOLExact, shapeEqHOL]
    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
    · rw [hG.code]; exact lookup_u256_to_digits
  rw [hlk] at hnt ⊢
  dsimp only at hnt ⊢
  by_cases hcz : s.clock = 0
  · rw [if_pos hcz] at hnt; exact absurd rfl hnt
  · rw [if_neg hcz] at hnt ⊢
    let ent := callEntryStateHOLFinite s callee
    have hentG : GuestInv ent := guestInv_callEntry s callee hG
    have heff_ent : WsByteEff s ent Rl :=
      (R13Shards.Keccak256.ByteEff.refl s Rl).locals_clock callee (s.clock - 1)
    have hp_ent : ent.locals.lookup (ofString "p") = some (.val (.word p)) := by
      simp [ent, callEntryStateHOLFinite, callee, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "a" ≠ ofString "p" by decide]
    have ha_ent : ent.locals.lookup (ofString "a") =
        some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)]) := by
      simp [ent, callEntryStateHOLFinite, callee, HolFiniteMapExact.lookup_update, FUPDATE]
    have hsp := u256_to_digits_body_spec (Rl := Rl) hentG p a0 a1 a2 a3 hp_ent ha_ent hcov
    cases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
        (sourceFnBody Guest.Software.guestFn_u256_to_digits) with
    | mk rb sb =>
      dsimp only [ent] at hsp
      rw [hrun] at hsp
      dsimp only at hsp hnt ⊢
      cases rb with
      | none =>
        have ⟨hnr, heff_b⟩ := hsp.2.2.2 (fun _ h => by simp at h)
        exact ⟨fun hlt => by obtain ⟨herr, _⟩ := hsp.2.1 hlt; simp at herr,
          fun h => by simp at h,
          fun _ => ⟨not_resumes_error, heff_ent.trans heff_b⟩⟩
      | some r =>
        cases r with
        | timeOut => exact absurd rfl hsp.1
        | returned rv =>
          obtain ⟨rfl, hG_sb, heff_b, hge, hphi, hp8, hdigs⟩ := hsp.2.2.1 rv rfl
          dsimp only
          have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word 0#64) : ValueHOL 64)) .one = true := by
            simp [shapeOfHOLExact, shapeEqHOL]
          rw [if_pos hsh]
          exact ⟨fun hlt => absurd hlt (by omega),
            fun _ => ⟨guestInv_congr (s := sb) rfl rfl rfl rfl hG_sb,
              (heff_ent.trans heff_b).locals_clock s.locals sb.clock, rfl, hge, hphi, hp8, hdigs⟩,
            fun h => absurd rfl h⟩
        | error =>
          have ⟨_, heff_b⟩ := hsp.2.2.2 (fun _ h => by simp at h)
          exact ⟨fun _ => ⟨rfl, (heff_ent.trans heff_b).locals_clock _ _⟩,
            fun h => by simp at h,
            fun _ => ⟨not_resumes_error, (heff_ent.trans heff_b).locals_clock _ _⟩⟩
        | «break» | «continue» =>
          have ⟨_, heff_b⟩ := hsp.2.2.2 (fun _ h => by simp at h)
          exact ⟨fun hlt => by obtain ⟨herr, _⟩ := hsp.2.1 hlt; simp at herr,
            fun h => by simp at h,
            fun _ => ⟨not_resumes_error, heff_ent.trans heff_b⟩⟩
        | exception eid ev =>
          have ⟨hnr, heff_b⟩ := hsp.2.2.2 (fun _ h => by simp at h)
          exact ⟨fun hlt => by obtain ⟨herr, _⟩ := hsp.2.1 hlt; simp at herr,
            fun h => by simp at h,
            fun _ => ⟨hnr, (heff_ent.trans heff_b).locals_clock _ _⟩⟩
        | finalFfi ev =>
          have ⟨_, heff_b⟩ := hsp.2.2.2 (fun _ h => by simp at h)
          exact ⟨fun hlt => by obtain ⟨herr, _⟩ := hsp.2.1 hlt; simp at herr,
            fun h => by simp at h,
            fun _ => ⟨by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h,
              (heff_ent.trans heff_b).locals_clock _ _⟩⟩

/-! ### `digits_len` bounds (upper bound `≤ n`, and `≥ 1` when a nonzero digit exists) -/

private def digitsLenLoopProg : ProgHOL 64 :=
  .while (.cmp .lower (.const 0#64) (.var .local (ofString "n")))
    ((ProgHOL.ite (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "p"),
        .panop .mul [.op .sub [.var .local (ofString "n"), .const 1#64], .const 8#64]])) (.const 0#64))
      (.return (.var .local (ofString "n"))) .skip).seq
      (.assign .local (ofString "n") (.op .sub [.var .local (ofString "n"), .const 1#64])))

private theorem digitsLenStep_eval {F : Type} (s : PanSemStateFiniteExact 64 F) (p w : BitVec 64)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word p)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word w))) :
    let step := (ProgHOL.ite (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "p"),
        .panop .mul [.op .sub [.var .local (ofString "n"), .const 1#64], .const 8#64]])) (.const 0#64))
      (.return (.var .local (ofString "n"))) .skip).seq
      (.assign .local (ofString "n") (.op .sub [.var .local (ofString "n"), .const 1#64]))
    let addr := p + (w - 1#64) * 8#64
    (s.memaddrs addr ∧ s.memory addr = .word 0#64 ∧
      evaluateHOLFiniteState s step = (none, setVarHOLFinite (ofString "n") (.val (.word (w - 1#64))) s)) ∨
    (∃ post, evaluateHOLFiniteState s step = (some (.returned (.val (.word w))), post)) ∨
    (∃ post, evaluateHOLFiniteState s step = (some .error, post)) := by
  intro step addr
  dsimp only [step, addr]
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  have haddr : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "p"),
        .panop .mul [.op .sub [.var .local (ofString "n"), .const 1#64], .const 8#64]]) =
      some (.val (.word (p + (w - 1#64) * 8#64))) := by
    simp [evalHOLExact, evalListHOLExact, PanSemStateFiniteExact.toExact, hp, hn,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL]
  by_cases hdom : s.memaddrs (p + (w - 1#64) * 8#64)
  · generalize hm : s.memory (p + (w - 1#64) * 8#64) = mval
    rcases mval with ⟨mw⟩
    have hld : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "p"),
          .panop .mul [.op .sub [.var .local (ofString "n"), .const 1#64], .const 8#64]])) =
        some (.val (.word mw)) := by
      unfold evalHOLExact
      rw [haddr]
      simp [PanSemStateFiniteExact.toExact, isWfShapeExactHOL, memLoadHOLExact, hdom, hm]
    have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "p"),
          .panop .mul [.op .sub [.var .local (ofString "n"), .const 1#64], .const 8#64]])) (.const 0#64)) =
        some (.val (.word (if mw == 0#64 then 0#64 else 1#64))) := by
      unfold evalHOLExact
      rw [hld]
      by_cases hmw0 : mw = 0#64
      · subst hmw0; simp [evalHOLExact, Compiler.Encoders.Asm.wordCmpHOL]
      · have hbeq : (mw == 0#64) = false := beq_false_of_ne hmw0
        simp [evalHOLExact, Compiler.Encoders.Asm.wordCmpHOL, hmw0, hbeq]
    rw [hcond]
    dsimp only
    by_cases hmw0 : mw = 0#64
    · subst hmw0
      rw [if_pos (by simp)]
      rw [evaluateHOLFiniteState_skip]
      left
      refine ⟨hdom, rfl, ?_⟩
      simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact,
        PanSemStateFiniteExact.toExact, hn, wordOpHOL, wordOp, valueIsWord, valueWord,
        PanSemStateFiniteExact.isValidValueHOLFinite, isValidValueHOLExact,
        lookupKvarHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
    · have hbeq : (mw == 0#64) = false := beq_false_of_ne hmw0
      rw [if_neg (by simp [hbeq])]
      rw [evaluateHOLFiniteState_return]
      simp only [evalHOLExact, PanSemStateFiniteExact.toExact, hn, shapeOfHOLExact,
        sizeOfShapeWithContextHOL, show (1 : Nat) ≤ 32 by decide, ↓reduceIte]
      exact Or.inr (Or.inl ⟨_, rfl⟩)
  · have hld : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "p"),
          .panop .mul [.op .sub [.var .local (ofString "n"), .const 1#64], .const 8#64]])) = none := by
      unfold evalHOLExact
      rw [haddr]
      simp [PanSemStateFiniteExact.toExact, isWfShapeExactHOL, memLoadHOLExact, hdom]
    have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "p"),
          .panop .mul [.op .sub [.var .local (ofString "n"), .const 1#64], .const 8#64]])) (.const 0#64)) = none := by
      unfold evalHOLExact
      rw [hld]
    rw [hcond]
    exact Or.inr (Or.inr ⟨_, rfl⟩)

private theorem digitsLenLoop_spec :
    ∀ (fuel : Nat) {F : Type} (s : PanSemStateFiniteExact 64 F) (p w : BitVec 64) (N : Nat),
      w.toNat = fuel →
      fuel ≤ N →
      s.locals.lookup (ofString "p") = some (.val (.word p)) →
      s.locals.lookup (ofString "n") = some (.val (.word w)) →
      (∀ rv post, evaluateHOLFiniteState s digitsLenLoopProg = (some (.returned rv), post) →
        ∃ rw : BitVec 64, rv = .val (.word rw) ∧ 1 ≤ rw.toNat ∧ rw.toNat ≤ N) ∧
      (∀ post, evaluateHOLFiniteState s digitsLenLoopProg = (none, post) →
        ∀ idx : Nat, idx < fuel →
          s.memaddrs (p + BitVec.ofNat 64 idx * 8#64) →
          s.memory (p + BitVec.ofNat 64 idx * 8#64) = .word 0#64) := by
  intro fuel
  induction fuel with
  | zero =>
    intro F s p w N hfuel _ hp hn
    have hw0 : w = 0#64 := BitVec.eq_of_toNat_eq hfuel
    subst hw0
    unfold digitsLenLoopProg
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    have hc : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .lower (.const 0#64) (.var .local (ofString "n"))) = some (.val (.word 0#64)) := by
      simp [evalHOLFinite, evalHOLExact, PanSemStateFiniteExact.toExact, hn,
        Compiler.Encoders.Asm.wordCmpHOL]
    rw [hc]
    exact ⟨fun _ _ h => by simp at h, fun _ _ idx hidx => absurd hidx (by omega)⟩
  | succ k ih =>
    intro F s p w N hfuel hle hp hn
    unfold digitsLenLoopProg
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    have hc : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .lower (.const 0#64) (.var .local (ofString "n"))) = some (.val (.word 1#64)) := by
      simp [evalHOLFinite, evalHOLExact, PanSemStateFiniteExact.toExact, hn,
        Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
      omega
    rw [hc]
    dsimp only
    rw [if_pos (by decide)]
    by_cases hcz : s.clock = 0
    · rw [if_pos hcz]
      exact ⟨fun _ _ h => by simp at h, fun _ h => by simp at h⟩
    · rw [if_neg hcz]
      have hp_d : (decClockHOLFinite s).locals.lookup (ofString "p") = some (.val (.word p)) := hp
      have hn_d : (decClockHOLFinite s).locals.lookup (ofString "n") = some (.val (.word w)) := hn
      rcases digitsLenStep_eval (decClockHOLFinite s) p w hp_d hn_d with
        ⟨hdom_k, hm_k, hnext⟩ | ⟨post', hret⟩ | ⟨post', herr⟩
      · rw [hnext]
        dsimp only
        change (∀ rv post, evaluateHOLFiniteState _ digitsLenLoopProg = _ → _) ∧
               (∀ post, evaluateHOLFiniteState _ digitsLenLoopProg = _ → _)
        let s' := setVarHOLFinite (ofString "n") (.val (.word (w - 1#64))) (decClockHOLFinite s)
        have hwk : (w - 1#64).toNat = k := by
          have := w.isLt
          rw [BitVec.toNat_sub_of_le (by show (1#64).toNat ≤ w.toNat; change 1 ≤ w.toNat; omega)]
          change w.toNat - 1 = k; omega
        have hp' : s'.locals.lookup (ofString "p") = some (.val (.word p)) := by
          simp [s', setVarHOLFinite, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp]
        have hn' : s'.locals.lookup (ofString "n") = some (.val (.word (w - 1#64))) := by
          simp [s', setVarHOLFinite, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have jih := ih s' p (w - 1#64) N hwk (by omega) hp' hn'
        refine ⟨jih.1, ?_⟩
        intro post hnone idx hidx hdom_idx
        by_cases hik : idx = k
        · subst hik
          have heq_w : w - 1#64 = BitVec.ofNat 64 idx := BitVec.eq_of_toNat_eq (by
            rw [hwk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := w.isLt; omega)])
          rw [← heq_w]
          exact hm_k
        · exact jih.2 post hnone idx (by omega) hdom_idx
      · rw [hret]
        dsimp only
        exact ⟨fun rv _ h => by
          injection h with h1 _; injection h1 with h2; injection h2 with h3
          exact ⟨w, h3.symm, by omega, by omega⟩,
          fun _ h => by simp at h⟩
      · rw [herr]
        dsimp only
        exact ⟨fun _ _ h => by simp at h, fun _ h => by simp at h⟩

private theorem digits_len_body_spec {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p n : BitVec 64)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word p)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n))) :
    ∀ rv post, evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_digits_len) =
      (some (.returned rv), post) →
      ∃ rw : BitVec 64, rv = .val (.word rw) ∧ rw.toNat ≤ n.toNat ∧
        (rw = 0#64 → ∀ idx : Nat, idx < n.toNat →
          s.memaddrs (p + BitVec.ofNat 64 idx * 8#64) →
          s.memory (p + BitVec.ofNat 64 idx * 8#64) = .word 0#64) := by
  have hbody : sourceFnBody Guest.Software.guestFn_digits_len =
      .seq digitsLenLoopProg (.return (.const 0#64)) := rfl
  intro rv post hrun
  rw [hbody, evaluateHOLFiniteState_seq_line780] at hrun
  have hls := digitsLenLoop_spec n.toNat s p n n.toNat rfl (Nat.le_refl _) hp hn
  rcases hw : evaluateHOLFiniteState s digitsLenLoopProg with ⟨res, mid⟩
  rw [hw] at hrun
  cases res with
  | none =>
    dsimp only at hrun
    rw [evaluateHOLFiniteState_return] at hrun
    simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL,
      show (1 : Nat) ≤ 32 by decide, ↓reduceIte] at hrun
    injection hrun with h1 _; injection h1 with h2; injection h2 with h3
    exact ⟨0#64, h3.symm, Nat.zero_le _, fun _ => hls.2 mid hw⟩
  | some r =>
    dsimp only at hrun
    injection hrun with h1 h2; subst h2
    injection h1 with hr; subst hr
    obtain ⟨rw, rfl, hge1, hle⟩ := hls.1 rv mid hw
    refine ⟨rw, rfl, hle, fun hr0 => ?_⟩
    subst hr0; simp at hge1

private theorem digits_len_decCall_spec {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hG : GuestInv s) (vname : MlS) (pExp nExp : ExpHOL 64) (p n : BitVec 64) (cont : ProgHOL 64)
    (hp : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      pExp = some (.val (.word p)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      nExp = some (.val (.word n)))
    (hcont : ∀ (m : PanSemStateFiniteExact 64 F) (rw : BitVec 64),
      GuestInv m → M13.LocFrame s m →
      m.locals = (s.locals.update (vname, .val (.word rw))) →
      rw.toNat ≤ n.toNat →
      (rw = 0#64 → ∀ idx : Nat, idx < n.toNat →
        s.memaddrs (p + BitVec.ofNat 64 idx * 8#64) →
        s.memory (p + BitVec.ofNat 64 idx * 8#64) = .word 0#64) →
      (evaluateHOLFiniteState m cont).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState m cont).1 = none ∨ Resumes (evaluateHOLFiniteState m cont).1) →
      GuestInv (evaluateHOLFiniteState m cont).2 ∧ WsByteEff m (evaluateHOLFiniteState m cont).2 Rl) :
    let out := evaluateHOLFiniteState s (.decCall vname .one (ofString "digits_len") [pExp, nExp] cont)
    out.1 ≠ some .timeOut →
      (out.1 = none ∨ Resumes out.1) →
      GuestInv out.2 ∧ WsByteEff s out.2 Rl := by
  intro out hnt hres
  dsimp only [out] at hnt hres ⊢
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres ⊢
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [pExp, nExp] =
      some [.val (.word p), .val (.word n)] := by
    simp [evalListHOLFinite, evalListHOLExact, hp, hn]
  rw [hargs] at hnt hres ⊢
  dsimp only at hnt hres ⊢
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "p", ValueHOL.val (.word p))).update
      (ofString "n", ValueHOL.val (.word n))
  have hlk : lookupCodeHOLFinite s.code.lookup (ofString "digits_len")
      [.val (.word p), .val (.word n)] =
      some (sourceFnBody Guest.Software.guestFn_digits_len, callee, .one) := by
    apply two_arg_lookup s.code.lookup (ofString "digits_len")
      (ofString "p") (ofString "n") .one .one .one
      (sourceFnBody Guest.Software.guestFn_digits_len)
      (.val (.word p)) (.val (.word n)) (by decide)
    · simp [shapeOfHOLExact, shapeEqHOL]
    · simp [shapeOfHOLExact, shapeEqHOL]
    · rw [hG.code]; exact lookup_digits_len
  rw [hlk] at hnt hres ⊢
  dsimp only at hnt hres ⊢
  by_cases hcz : s.clock = 0
  · rw [if_pos hcz] at hnt; exact absurd rfl hnt
  · rw [if_neg hcz] at hnt hres ⊢
    let ent := callEntryStateHOLFinite s callee
    obtain ⟨params', body', ret', hlook', hflf⟩ := flf_digits_len
    have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "digits_len")
      params' body' (sourceFnBody Guest.Software.guestFn_digits_len) ret' .one
      [.val (.word p), .val (.word n)] callee (by rw [hG.code]; exact hlook') hlk
    subst hsame
    have hlf_body := hflf ent hG.code
    have hp_ent : ent.locals.lookup (ofString "p") = some (.val (.word p)) := by
      simp [ent, callEntryStateHOLFinite, callee, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "p" by decide]
    have hn_ent : ent.locals.lookup (ofString "n") = some (.val (.word n)) := by
      simp [ent, callEntryStateHOLFinite, callee, HolFiniteMapExact.lookup_update, FUPDATE]
    cases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
        (sourceFnBody Guest.Software.guestFn_digits_len) with
    | mk rb sb =>
      have hrun1 : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
        (sourceFnBody Guest.Software.guestFn_digits_len)).1 = rb := by rw [hrun]
      have hrun2 : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
        (sourceFnBody Guest.Software.guestFn_digits_len)).2 = sb := by rw [hrun]
      rw [hrun1, hrun2] at hnt hres
      dsimp only [ent] at hlf_body
      rw [hrun] at hlf_body
      have hlf_s : M13.LocFrame s sb := by
        unfold M13.LocFrame at hlf_body ⊢; dsimp only at hlf_body; rw [hlf_body]; rfl
      dsimp only at hnt hres ⊢
      cases rb with
      | none => exact absurd (hres.resolve_left (by simp)) not_resumes_error
      | some r =>
        cases r with
        | timeOut => exact absurd rfl hnt
        | returned rv =>
          obtain ⟨rw, rfl, hle, hzero⟩ := digits_len_body_spec ent p n hp_ent hn_ent rv sb hrun
          dsimp only at hnt hres ⊢
          have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word rw) : ValueHOL 64)) .one &&
              shapeEqHOL (shapeOfHOLExact (.val (.word rw) : ValueHOL 64)) .one) = true := by
            simp [shapeOfHOLExact, shapeEqHOL]
          rw [if_pos hsh] at hnt hres ⊢
          let m := setVarHOLFinite vname (.val (.word rw)) { sb with locals := s.locals }
          have hlf_m : M13.LocFrame s m := (hlf_s.locals s.locals).setVar vname (.val (.word rw))
          have hmG : GuestInv m := guestInv_of_locFrame hlf_m hG
          have heff_sm : WsByteEff s m Rl := wsByteEff_of_locFrame hlf_m
          have hc := hcont m rw hmG hlf_m rfl hle hzero hnt hres
          dsimp only
          exact ⟨⟨hc.1.code, hc.1.memaddrs, hc.1.shMemaddrs, hc.1.baseAddr⟩,
            (heff_sm.trans hc.2).locals_clock _ _⟩
        | exception _ _ =>
          exact ⟨guestInv_of_locFrame hlf_s.emptyLocals hG, wsByteEff_of_locFrame hlf_s.emptyLocals⟩
        | «break» | «continue» | error =>
          exact absurd (hres.resolve_left (by simp)) not_resumes_error
        | finalFfi _ =>
          rcases hres with hnone | ⟨_, h⟩ | ⟨_, _, h, _⟩
          · simp at hnone
          · simp at h
          · simp at h

/-! ## Section 5: Generic step & loop combinators + `divmnu` -/

private theorem three_arg_lookup {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name p1 p2 p3 : MlS) (s1 s2 s3 rs : ShapeHOL) (body : ProgHOL width)
    (v1 v2 v3 : ValueHOL width)
    (hd12 : p1 ≠ p2) (hd13 : p1 ≠ p3) (hd23 : p2 ≠ p3)
    (hsh1 : shapeEqHOL s1 (shapeOfHOLExact v1) = true)
    (hsh2 : shapeEqHOL s2 (shapeOfHOLExact v2) = true)
    (hsh3 : shapeEqHOL s3 (shapeOfHOLExact v3) = true)
    (lookup : code name = some ([(p1, s1), (p2, s2), (p3, s3)], body, rs)) :
    PanSemStateFiniteExact.lookupCodeHOLFinite code name [v1, v2, v3] =
      some (body, (((HolFiniteMapExact.empty.update (p1, v1)).update (p2, v2)).update (p3, v3)), rs) := by
  have raw : lookupCodeHOLExact code name [v1, v2, v3] =
      some (body, (fun key => if key = p3 then some v3 else if key = p2 then some v2
        else if key = p1 then some v1 else none), rs) := by
    simp [lookupCodeHOLExact, lookup, hsh1, hsh2, hsh3, hd12, hd13, hd23]
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i missing; rw [raw] at missing; cases missing
  · rename_i foundBody foundLocals foundShape found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun locals => some (foundBody, locals, foundShape))
    apply HolFiniteMapExact.ext
    funext key
    by_cases h3 : key = p3
    · subst h3; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty]
    · have hb3 : p3 ≠ key := Ne.symm h3
      by_cases h2 : key = p2
      · subst h2; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, h3, hb3]
      · have hb2 : p2 ≠ key := Ne.symm h2
        by_cases h1 : key = p1
        · subst h1; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, h3, hb3, h2, hb2]
        · have hb1 : p1 ≠ key := Ne.symm h1
          simp [h1, h2, h3, hb1, hb2, hb3, HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]

private theorem six_word_lookup {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name p1 p2 p3 p4 p5 p6 : MlS) (rs : ShapeHOL) (body : ProgHOL width)
    (w1 w2 w3 w4 w5 w6 : BitVec width)
    (hd : List.Pairwise (· ≠ ·) [p1, p2, p3, p4, p5, p6])
    (lookup : code name = some ([(p1, .one), (p2, .one), (p3, .one), (p4, .one), (p5, .one), (p6, .one)], body, rs)) :
    PanSemStateFiniteExact.lookupCodeHOLFinite code name
      [.val (.word w1), .val (.word w2), .val (.word w3), .val (.word w4), .val (.word w5), .val (.word w6)] =
      some (body, ((((((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update
        (p2, .val (.word w2))).update (p3, .val (.word w3))).update (p4, .val (.word w4))).update
        (p5, .val (.word w5))).update (p6, .val (.word w6))), rs) := by
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true] at hd
  obtain ⟨⟨h12, h13, h14, h15, h16⟩, ⟨h23, h24, h25, h26⟩, ⟨h34, h35, h36⟩, ⟨h45, h46⟩, h56⟩ := hd
  have hsh : ∀ w : BitVec width, shapeEqHOL .one (shapeOfHOLExact (.val (.word w) : ValueHOL width)) = true := by
    intro w; simp [shapeOfHOLExact, shapeEqHOL]
  have raw : lookupCodeHOLExact code name
      [.val (.word w1), .val (.word w2), .val (.word w3), .val (.word w4), .val (.word w5), .val (.word w6)] =
      some (body, (fun key =>
        if key = p6 then some (.val (.word w6))
        else if key = p5 then some (.val (.word w5))
        else if key = p4 then some (.val (.word w4))
        else if key = p3 then some (.val (.word w3))
        else if key = p2 then some (.val (.word w2))
        else if key = p1 then some (.val (.word w1))
        else none), rs) := by
    simp [lookupCodeHOLExact, lookup, hsh, h12, h13, h14, h15, h16, h23, h24, h25, h26, h34, h35, h36, h45, h46, h56]
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i missing; rw [raw] at missing; cases missing
  · rename_i foundBody foundLocals foundShape found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun locals => some (foundBody, locals, foundShape))
    apply HolFiniteMapExact.ext
    funext key
    by_cases c6 : key = p6
    · subst c6; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty]
    · have b6 : p6 ≠ key := Ne.symm c6
      by_cases c5 : key = p5
      · subst c5; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, c6, b6]
      · have b5 : p5 ≠ key := Ne.symm c5
        by_cases c4 : key = p4
        · subst c4; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, c6, b6, c5, b5]
        · have b4 : p4 ≠ key := Ne.symm c4
          by_cases c3 : key = p3
          · subst c3; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, c6, b6, c5, b5, c4, b4]
          · have b3 : p3 ≠ key := Ne.symm c3
            by_cases c2 : key = p2
            · subst c2; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, c6, b6, c5, b5, c4, b4, c3, b3]
            · have b2 : p2 ≠ key := Ne.symm c2
              by_cases c1 : key = p1
              · subst c1; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, c6, b6, c5, b5, c4, b4, c3, b3, c2, b2]
              · have b1 : p1 ≠ key := Ne.symm c1
                simp [c1, c2, c3, c4, c5, c6, b1, b2, b3, b4, b5, b6,
                  HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]

private def stepOk {F : Type} (s : PanSemStateFiniteExact 64 F) (Rl : List Ivl)
    (p : ProgHOL 64) (Q : PanSemStateFiniteExact 64 F → Prop) : Prop :=
  (evaluateHOLFiniteState s p).1 ≠ some .timeOut →
    ((evaluateHOLFiniteState s p).1 = none →
      GuestInv (evaluateHOLFiniteState s p).2 ∧
      WsByteEff s (evaluateHOLFiniteState s p).2 Rl ∧
      Q (evaluateHOLFiniteState s p).2) ∧
    ((evaluateHOLFiniteState s p).1 ≠ none →
      (evaluateHOLFiniteState s p).1 ≠ some .continue ∧
      (evaluateHOLFiniteState s p).1 ≠ some .break ∧
      (Resumes (evaluateHOLFiniteState s p).1 →
        GuestInv (evaluateHOLFiniteState s p).2 ∧ WsByteEff s (evaluateHOLFiniteState s p).2 Rl))

private def retOk {F : Type} (s : PanSemStateFiniteExact 64 F) (Rl : List Ivl)
    (p : ProgHOL 64) : Prop :=
  (evaluateHOLFiniteState s p).1 ≠ some .timeOut →
    ((evaluateHOLFiniteState s p).1 = none ∨ Resumes (evaluateHOLFiniteState s p).1) →
    GuestInv (evaluateHOLFiniteState s p).2 ∧ WsByteEff s (evaluateHOLFiniteState s p).2 Rl

private theorem retOk_of_stepOk_seq {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    {a b : ProgHOL 64} {Q : PanSemStateFiniteExact 64 F → Prop}
    (ha : stepOk s Rl a Q)
    (hb : ∀ m, GuestInv m → WsByteEff s m Rl → Q m → retOk m Rl b) :
    retOk s Rl (.seq a b) := by
  unfold retOk
  intro hnt hres
  rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
  dsimp only at hnt hres ⊢
  rcases hr : evaluateHOLFiniteState s a with ⟨ra, m⟩
  have hr1 : (evaluateHOLFiniteState s a).1 = ra := by rw [hr]
  have hr2 : (evaluateHOLFiniteState s a).2 = m := by rw [hr]
  rw [hr1] at hnt hres
  have hnta : ra ≠ some .timeOut := by
    rintro rfl; rw [hr] at hnt; exact hnt rfl
  have hsa := ha (by rw [hr1]; exact hnta)
  rw [hr] at hsa
  dsimp only at hsa hnt hres ⊢
  cases ra with
  | none =>
    rw [hr2] at hnt hres
    obtain ⟨hmG, heff1, hQm⟩ := hsa.1 rfl
    have ⟨hG2, heff2⟩ := hb m hmG heff1 hQm hnt hres
    exact ⟨hG2, heff1.trans heff2⟩
  | some r =>
    rw [hr] at hres
    obtain ⟨_, _, hres_a⟩ := hsa.2 (by simp)
    exact hres_a (hres.resolve_left (by simp))

private theorem stepOk_seq {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    {a b : ProgHOL 64} {Q1 Q2 : PanSemStateFiniteExact 64 F → Prop}
    (ha : stepOk s Rl a Q1)
    (hb : ∀ m, GuestInv m → WsByteEff s m Rl → Q1 m → stepOk m Rl b Q2) :
    stepOk s Rl (.seq a b) Q2 := by
  unfold stepOk
  intro hnt
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  dsimp only at hnt ⊢
  rcases hr : evaluateHOLFiniteState s a with ⟨ra, m⟩
  have hr1 : (evaluateHOLFiniteState s a).1 = ra := by rw [hr]
  have hr2 : (evaluateHOLFiniteState s a).2 = m := by rw [hr]
  rw [hr1] at hnt
  have hnta : ra ≠ some .timeOut := by
    rintro rfl; rw [hr] at hnt; exact hnt rfl
  have hsa := ha (by rw [hr1]; exact hnta)
  rw [hr] at hsa
  dsimp only at hsa hnt ⊢
  cases ra with
  | none =>
    rw [hr2] at hnt
    obtain ⟨hmG, heff1, hQm⟩ := hsa.1 rfl
    have hsb := hb m hmG heff1 hQm hnt
    exact ⟨fun hn => ⟨(hsb.1 hn).1, heff1.trans (hsb.1 hn).2.1, (hsb.1 hn).2.2⟩,
      fun hnn => ⟨(hsb.2 hnn).1, (hsb.2 hnn).2.1,
        fun hres => ⟨((hsb.2 hnn).2.2 hres).1, heff1.trans ((hsb.2 hnn).2.2 hres).2⟩⟩⟩
  | some r =>
    exact ⟨fun h => by simp at h, fun _ => hsa.2 (by simp)⟩

private theorem stepOk_skip {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hG : GuestInv s) {Q : PanSemStateFiniteExact 64 F → Prop} (hQ : Q s) :
    stepOk s Rl .skip Q := by
  unfold stepOk; intro _
  rw [evaluateHOLFiniteState_skip]
  exact ⟨fun _ => ⟨hG, R13Shards.Keccak256.ByteEff.refl s Rl, hQ⟩, fun h => absurd rfl h⟩

private theorem retOk_return {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hG : GuestInv s) (e : ExpHOL 64) :
    retOk s Rl (.return e) := by
  unfold retOk; intro _ _
  rw [evaluateHOLFiniteState_return]
  rcases he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | val
  · exact ⟨hG, R13Shards.Keccak256.ByteEff.refl s Rl⟩
  · dsimp only
    split
    · exact ⟨guestInv_congr (s := s) rfl rfl rfl rfl hG,
        (R13Shards.Keccak256.ByteEff.refl s Rl).locals_clock _ _⟩
    · exact ⟨hG, R13Shards.Keccak256.ByteEff.refl s Rl⟩

private theorem stepOk_return {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hG : GuestInv s) (e : ExpHOL 64) (Q : PanSemStateFiniteExact 64 F → Prop) :
    stepOk s Rl (.return e) Q := by
  unfold stepOk; intro _
  rw [evaluateHOLFiniteState_return]
  rcases he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | val
  · exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp, fun hr => absurd hr not_resumes_error⟩⟩
  · dsimp only
    split
    · exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp, fun _ =>
        ⟨guestInv_congr (s := s) rfl rfl rfl rfl hG,
         (R13Shards.Keccak256.ByteEff.refl s Rl).locals_clock _ _⟩⟩⟩
    · exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp, fun hr => absurd hr not_resumes_error⟩⟩

private theorem stepOk_ite {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (cond : ExpHOL 64) {yes no : ProgHOL 64} {Q : PanSemStateFiniteExact 64 F → Prop}
    (hyes : ∀ w : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond =
        some (.val (.word w)) → w ≠ 0#64 → stepOk s Rl yes Q)
    (hno : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond =
        some (.val (.word 0#64)) → stepOk s Rl no Q) :
    stepOk s Rl (.ite cond yes no) Q := by
  unfold stepOk; intro hnt
  rw [evaluateHOLFiniteState_ite] at hnt ⊢
  rcases hc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond with _ | cv
  · exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp, fun hr => absurd hr not_resumes_error⟩⟩
  · rcases cv with ⟨⟨w⟩⟩ | _ | _
    · rw [hc] at hnt; dsimp only at hnt ⊢
      by_cases hw : w = 0
      · have hw0 : w = 0#64 := hw
        rw [if_pos hw] at hnt ⊢
        rw [hw0] at hc
        exact hno hc hnt
      · have hw0 : w ≠ 0#64 := hw
        rw [if_neg hw] at hnt ⊢
        exact hyes w hc hw0 hnt
    · exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp, fun hr => absurd hr not_resumes_error⟩⟩
    · exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp, fun hr => absurd hr not_resumes_error⟩⟩

private theorem retOk_ite {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (cond : ExpHOL 64) {yes no : ProgHOL 64}
    (hyes : ∀ w : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond =
        some (.val (.word w)) → w ≠ 0#64 → retOk s Rl yes)
    (hno : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond =
        some (.val (.word 0#64)) → retOk s Rl no) :
    retOk s Rl (.ite cond yes no) := by
  unfold retOk; intro hnt hres
  rw [evaluateHOLFiniteState_ite] at hnt hres ⊢
  rcases hc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond with _ | cv
  · rw [hc] at hres; exact absurd (hres.resolve_left (by simp)) not_resumes_error
  · rcases cv with ⟨⟨w⟩⟩ | _ | _
    · rw [hc] at hnt hres; dsimp only at hnt hres ⊢
      by_cases hw : w = 0
      · have hw0 : w = 0#64 := hw
        rw [if_pos hw] at hnt hres ⊢
        rw [hw0] at hc
        exact hno hc hnt hres
      · have hw0 : w ≠ 0#64 := hw
        rw [if_neg hw] at hnt hres ⊢
        exact hyes w hc hw0 hnt hres
    · rw [hc] at hres; exact absurd (hres.resolve_left (by simp)) not_resumes_error
    · rw [hc] at hres; exact absurd (hres.resolve_left (by simp)) not_resumes_error

private theorem retOk_dec {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (_hG : GuestInv s) (vname : MlS) (sh : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64}
    (hbody : ∀ val : ValueHOL 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init = some val →
      shapeEqHOL sh (shapeOfHOLExact val) = true →
      retOk (setVarHOLFinite vname val s) Rl body) :
    retOk s Rl (.dec vname sh init body) := by
  unfold retOk; intro hnt hres
  rw [evaluateHOLFiniteState_dec_total] at hnt hres ⊢
  dsimp only at hnt hres ⊢
  rcases he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init with _ | val
  · rw [he] at hres; exact absurd (hres.resolve_left (by simp)) not_resumes_error
  · rw [he] at hnt hres; dsimp only at hnt hres ⊢
    by_cases hsh : shapeEqHOL sh (shapeOfHOLExact val) = true
    · rw [if_pos hsh] at hnt hres ⊢
      have hb := hbody val he hsh hnt hres
      exact ⟨⟨hb.1.code, hb.1.memaddrs, hb.1.shMemaddrs, hb.1.baseAddr⟩,
        (((R13Shards.Keccak256.ByteEff.refl s Rl).locals_clock _ _).trans hb.2).locals_clock _ _⟩
    · rw [if_neg hsh] at hres; exact absurd (hres.resolve_left (by simp)) not_resumes_error

private theorem stepOk_dec {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (_hG : GuestInv s) (vname : MlS) (sh : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64}
    {Q : PanSemStateFiniteExact 64 F → Prop}
    (hQ_res : ∀ m : PanSemStateFiniteExact 64 F, Q m →
      Q { m with locals := m.locals.resVarEq (vname, s.locals.lookup vname) })
    (hbody : ∀ val : ValueHOL 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init = some val →
      shapeEqHOL sh (shapeOfHOLExact val) = true →
      stepOk (setVarHOLFinite vname val s) Rl body Q) :
    stepOk s Rl (.dec vname sh init body) Q := by
  unfold stepOk; intro hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  rcases he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init with _ | val
  · exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp, fun hr => absurd hr not_resumes_error⟩⟩
  · rw [he] at hnt; dsimp only at hnt ⊢
    by_cases hsh : shapeEqHOL sh (shapeOfHOLExact val) = true
    · rw [if_pos hsh] at hnt ⊢
      have hb := hbody val he hsh hnt
      have heff0 : WsByteEff s (setVarHOLFinite vname val s) Rl :=
        (R13Shards.Keccak256.ByteEff.refl s Rl).locals_clock _ _
      refine ⟨fun hn => ?_, fun hnn => ?_⟩
      · obtain ⟨hGb, heffb, hQb⟩ := hb.1 hn
        exact ⟨⟨hGb.code, hGb.memaddrs, hGb.shMemaddrs, hGb.baseAddr⟩,
          (heff0.trans heffb).locals_clock _ _, hQ_res _ hQb⟩
      · obtain ⟨hnc, hnbr, hresb⟩ := hb.2 hnn
        refine ⟨hnc, hnbr, fun hres => ?_⟩
        obtain ⟨hGb, heffb⟩ := hresb hres
        exact ⟨⟨hGb.code, hGb.memaddrs, hGb.shMemaddrs, hGb.baseAddr⟩,
          (heff0.trans heffb).locals_clock _ _⟩
    · rw [if_neg hsh]; exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp, fun hr => absurd hr not_resumes_error⟩⟩

private theorem stepOk_assign_local {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hG : GuestInv s) (vname : MlS) (e : ExpHOL 64) {Q : PanSemStateFiniteExact 64 F → Prop}
    (hQ : ∀ val : ValueHOL 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some val →
      s.isValidValueHOLFinite .local vname val = true →
      Q (setVarHOLFinite vname val s)) :
    stepOk s Rl (.assign .local vname e) Q := by
  unfold stepOk; intro _
  rw [evaluateHOLFiniteState_assign]
  rcases he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | val
  · exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp, fun hr => absurd hr not_resumes_error⟩⟩
  · dsimp only
    by_cases hv : s.isValidValueHOLFinite .local vname val = true
    · rw [if_pos hv]
      exact ⟨fun _ => ⟨guestInv_setVar vname val s hG,
        (R13Shards.Keccak256.ByteEff.refl s Rl).locals_clock _ _, hQ val he hv⟩,
        fun h => absurd rfl h⟩
    · rw [if_neg hv]
      exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp, fun hr => absurd hr not_resumes_error⟩⟩

private theorem stepOk_store_one {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hG : GuestInv s) (dstExp valExp : ExpHOL 64)
    (hval_one : ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      valExp = some v → ∃ w : BitVec 64, v = .val (.word w))
    (hin : ∀ x : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        dstExp = some (.val (.word x)) →
      s.memaddrs x → ∃ i ∈ Rl, i.1 ≤ x.toNat ∧ x.toNat + 8 ≤ i.1 + i.2)
    {Q : PanSemStateFiniteExact 64 F → Prop}
    (hQ : ∀ m : PanSemStateFiniteExact 64 F, GuestInv m → WsByteEff s m Rl → m.locals = s.locals →
      (∃ x : BitVec 64,
        @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          dstExp = some (.val (.word x)) ∧
        sourceBase ≤ x.toNat ∧ x.toNat + 8 ≤ heapEnd ∧ x.toNat % 8 = 0) →
      Q m) :
    stepOk s Rl (.store dstExp valExp) Q := by
  intro _
  have hb := R13Shards.Keccak256.byteEff_store_one (Rl := Rl) hG dstExp valExp hval_one hin
  have hloc_err :
      ((evaluateHOLFiniteState s (.store dstExp valExp)).1 = none →
        (evaluateHOLFiniteState s (.store dstExp valExp)).2.locals = s.locals) ∧
      ((evaluateHOLFiniteState s (.store dstExp valExp)).1 ≠ none →
        (evaluateHOLFiniteState s (.store dstExp valExp)).1 = some .error) := by
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split
        · exact ⟨fun _ => rfl, fun h => absurd rfl h⟩
        · exact ⟨fun h => by simp at h, fun _ => rfl⟩
      · exact ⟨fun h => by simp at h, fun _ => rfl⟩
    · exact ⟨fun h => by simp at h, fun _ => rfl⟩
  refine ⟨fun hn => ?_, fun hnn => ?_⟩
  · have hmG : GuestInv (evaluateHOLFiniteState s (.store dstExp valExp)).2 :=
      guestInv_congr hb.1.code hb.1.memaddrs hb.1.shMemaddrs hb.1.baseAddr hG
    exact ⟨hmG, hb.1, hQ _ hmG hb.1 (hloc_err.1 hn) (hb.2 hn)⟩
  · have herr := hloc_err.2 hnn
    rw [herr]
    exact ⟨by simp, by simp, fun hr => absurd hr not_resumes_error⟩

private theorem stepOk_while {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (cond : ExpHOL 64) (body : ProgHOL 64)
    (P : PanSemStateFiniteExact 64 F → Prop)
    (hG : GuestInv s) (hPs : P s)
    (hP_dec : ∀ t, P t → P (decClockHOLFinite t))
    (hbody : ∀ t, GuestInv t → P t → stepOk t Rl body P)
    {Q : PanSemStateFiniteExact 64 F → Prop}
    (hExit : ∀ t, GuestInv t → P t →
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) cond =
        some (.val (.word 0#64)) → Q t) :
    stepOk s Rl (.while cond body) Q := by
  have hloop : ∀ (k : Nat) (u : PanSemStateFiniteExact 64 F), u.clock = k → GuestInv u → P u →
      stepOk u Rl (.while cond body) Q := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro u hclk hGu hPu hnt
      rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
      rcases hc : @evalHOLFinite 64 F _ u (fun a => Classical.propDecidable (u.memaddrs a)) cond with _ | cv
      · simp only [hc] at hnt ⊢
        exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp, fun hr => absurd hr not_resumes_error⟩⟩
      · simp only [hc] at hnt ⊢
        rcases cv with ⟨⟨w⟩⟩ | _ | _
        · dsimp only at hnt ⊢
          by_cases hw : w ≠ 0
          · rw [if_pos hw] at hnt ⊢
            by_cases hk0 : u.clock = 0
            · simp [hk0] at hnt
            · rw [if_neg hk0] at hnt ⊢
              have hGd : GuestInv (decClockHOLFinite u) :=
                guestInv_congr (s := u) rfl rfl rfl rfl hGu
              have hPd : P (decClockHOLFinite u) := hP_dec u hPu
              have heff_dec : WsByteEff u (decClockHOLFinite u) Rl :=
                (R13Shards.Keccak256.ByteEff.refl u Rl).locals_clock u.locals (u.clock - 1)
              have hb_clk := evaluateHOLFiniteState_clock_le (decClockHOLFinite u) body
              have hd_clk : (decClockHOLFinite u).clock < k := by
                simp [decClockHOLFinite, hclk]; omega
              rcases hbo : evaluateHOLFiniteState (decClockHOLFinite u) body with ⟨rb, sb⟩
              simp only [hbo] at hnt hb_clk ⊢
              have hnt_b : rb ≠ some .timeOut := by
                rintro rfl; exact hnt rfl
              have hb_spec := hbody (decClockHOLFinite u) hGd hPd (by rw [hbo]; exact hnt_b)
              rw [hbo] at hb_spec
              dsimp only at hb_spec
              cases rb with
              | none =>
                obtain ⟨hGsb, heff_b, hPsb⟩ := hb_spec.1 rfl
                have jih := ih sb.clock (lt_of_le_of_lt hb_clk hd_clk) sb rfl hGsb hPsb hnt
                exact ⟨fun hn => ⟨(jih.1 hn).1, (heff_dec.trans heff_b).trans (jih.1 hn).2.1, (jih.1 hn).2.2⟩,
                  fun hnn => ⟨(jih.2 hnn).1, (jih.2 hnn).2.1,
                    fun hres => ⟨((jih.2 hnn).2.2 hres).1, (heff_dec.trans heff_b).trans ((jih.2 hnn).2.2 hres).2⟩⟩⟩
              | some r =>
                obtain ⟨hnc, hnbr, hres_b⟩ := hb_spec.2 (by simp)
                cases r with
                | «continue» => exact absurd rfl hnc
                | «break» => exact absurd rfl hnbr
                | timeOut => exact absurd rfl hnt_b
                | returned rv =>
                  exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp,
                    fun hres => ⟨(hres_b hres).1, heff_dec.trans (hres_b hres).2⟩⟩⟩
                | exception eid ev =>
                  exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp,
                    fun hres => ⟨(hres_b hres).1, heff_dec.trans (hres_b hres).2⟩⟩⟩
                | error =>
                  exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp, fun hr => absurd hr not_resumes_error⟩⟩
                | finalFfi ev =>
                  exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp,
                    fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩⟩
          · rw [if_neg hw]
            have hw0 : w = 0#64 := Classical.not_not.mp hw
            rw [hw0] at hc
            exact ⟨fun _ => ⟨hGu, R13Shards.Keccak256.ByteEff.refl u Rl, hExit u hGu hPu hc⟩,
              fun h => absurd rfl h⟩
        · exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp, fun hr => absurd hr not_resumes_error⟩⟩
        · exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp, fun hr => absurd hr not_resumes_error⟩⟩
  exact hloop s.clock s rfl hG hPs

private theorem stepOk_decCall_flf {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hG : GuestInv s) {fname : MlS} (hf : M13.FunLocFrame fname)
    (vname : MlS) (sh : ShapeHOL) (args : List (ExpHOL 64)) {cont : ProgHOL 64}
    {Q : PanSemStateFiniteExact 64 F → Prop}
    (hQ_res : ∀ m : PanSemStateFiniteExact 64 F, Q m →
      Q { m with locals := m.locals.resVarEq (vname, s.locals.lookup vname) })
    (hcont : ∀ (m : PanSemStateFiniteExact 64 F) (rv : ValueHOL 64),
      GuestInv m → M13.LocFrame s m →
      (shapeEqHOL (shapeOfHOLExact rv) sh && shapeEqHOL (shapeOfHOLExact rv) sh) = true →
      m.locals = s.locals.update (vname, rv) →
      stepOk m Rl cont Q) :
    stepOk s Rl (.decCall vname sh fname args cont) Q := by
  obtain ⟨params, body, ret, hlook, hflf⟩ := hf
  unfold stepOk; intro hnt
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp, fun hr => absurd hr not_resumes_error⟩⟩
  · rw [hargs] at hnt; dsimp only at hnt ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp, fun hr => absurd hr not_resumes_error⟩⟩
    · rw [hl] at hnt; dsimp only at hnt ⊢
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
        ret ret' values callee (by rw [hG.code]; exact hlook) hl
      subst body'
      by_cases hcz : s.clock = 0
      · rw [if_pos hcz] at hnt; exact absurd rfl hnt
      · rw [if_neg hcz] at hnt ⊢
        let ent := callEntryStateHOLFinite s callee
        have hlf_b := hflf ent hG.code
        cases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
        | mk rb sb =>
          have hr1 : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1 = rb := by rw [hrun]
          have hr2 : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).2 = sb := by rw [hrun]
          rw [hr1, hr2] at hnt
          dsimp only [ent] at hlf_b; rw [hrun] at hlf_b
          have hlf_s : M13.LocFrame s sb := by
            unfold M13.LocFrame at hlf_b ⊢; dsimp only at hlf_b; rw [hlf_b]; rfl
          dsimp only at hnt ⊢
          cases rb with
          | none =>
            exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp, fun hr => absurd hr not_resumes_error⟩⟩
          | some r =>
            cases r with
            | timeOut => exact absurd rfl hnt
            | «break» | «continue» | error =>
              exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp, fun hr => absurd hr not_resumes_error⟩⟩
            | finalFfi _ =>
              exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp,
                fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩⟩
            | exception _ _ =>
              exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp,
                fun _ => ⟨guestInv_of_locFrame hlf_s.emptyLocals hG,
                  wsByteEff_of_locFrame hlf_s.emptyLocals⟩⟩⟩
            | returned rv =>
              dsimp only at hnt ⊢
              by_cases hsh : (shapeEqHOL (shapeOfHOLExact rv) sh && shapeEqHOL (shapeOfHOLExact rv) ret') = true
              · rw [if_pos hsh] at hnt ⊢
                have hsh_self : (shapeEqHOL (shapeOfHOLExact rv) sh && shapeEqHOL (shapeOfHOLExact rv) sh) = true := by
                  simp only [Bool.and_eq_true] at hsh ⊢; exact ⟨hsh.1, hsh.1⟩
                let m := setVarHOLFinite vname rv { sb with locals := s.locals }
                have hlf_m : M13.LocFrame s m := (hlf_s.locals s.locals).setVar vname rv
                have hmG : GuestInv m := guestInv_of_locFrame hlf_m hG
                have heff_sm : WsByteEff s m Rl := wsByteEff_of_locFrame hlf_m
                have hc := hcont m rv hmG hlf_m hsh_self rfl hnt
                refine ⟨fun hn => ?_, fun hnn => ?_⟩
                · obtain ⟨hGc, heffc, hQc⟩ := hc.1 hn
                  exact ⟨⟨hGc.code, hGc.memaddrs, hGc.shMemaddrs, hGc.baseAddr⟩,
                    (heff_sm.trans heffc).locals_clock _ _, hQ_res _ hQc⟩
                · obtain ⟨hnc, hnbr, hresc⟩ := hc.2 hnn
                  refine ⟨hnc, hnbr, fun hres => ?_⟩
                  obtain ⟨hGc, heffc⟩ := hresc hres
                  exact ⟨⟨hGc.code, hGc.memaddrs, hGc.shMemaddrs, hGc.baseAddr⟩,
                    (heff_sm.trans heffc).locals_clock _ _⟩
              · rw [if_neg hsh]
                exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp, fun hr => absurd hr not_resumes_error⟩⟩

private theorem retOk_decCall_flf {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hG : GuestInv s) {fname : MlS} (hf : M13.FunLocFrame fname)
    (vname : MlS) (sh : ShapeHOL) (args : List (ExpHOL 64)) {cont : ProgHOL 64}
    (hcont : ∀ (m : PanSemStateFiniteExact 64 F) (rv : ValueHOL 64),
      GuestInv m → M13.LocFrame s m →
      (shapeEqHOL (shapeOfHOLExact rv) sh && shapeEqHOL (shapeOfHOLExact rv) sh) = true →
      m.locals = s.locals.update (vname, rv) →
      retOk m Rl cont) :
    retOk s Rl (.decCall vname sh fname args cont) := by
  obtain ⟨params, body, ret, hlook, hflf⟩ := hf
  unfold retOk; intro hnt hres
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · rw [hargs] at hres; exact absurd (hres.resolve_left (by simp)) not_resumes_error
  · rw [hargs] at hnt hres; dsimp only at hnt hres ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · rw [hl] at hres; exact absurd (hres.resolve_left (by simp)) not_resumes_error
    · rw [hl] at hnt hres; dsimp only at hnt hres ⊢
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
        ret ret' values callee (by rw [hG.code]; exact hlook) hl
      subst body'
      by_cases hcz : s.clock = 0
      · rw [if_pos hcz] at hnt; exact absurd rfl hnt
      · rw [if_neg hcz] at hnt hres ⊢
        let ent := callEntryStateHOLFinite s callee
        have hlf_b := hflf ent hG.code
        cases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
        | mk rb sb =>
          have hr1 : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1 = rb := by rw [hrun]
          have hr2 : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).2 = sb := by rw [hrun]
          rw [hr1, hr2] at hnt hres
          dsimp only [ent] at hlf_b; rw [hrun] at hlf_b
          have hlf_s : M13.LocFrame s sb := by
            unfold M13.LocFrame at hlf_b ⊢; dsimp only at hlf_b; rw [hlf_b]; rfl
          dsimp only at hnt hres ⊢
          cases rb with
          | none => exact absurd (hres.resolve_left (by simp)) not_resumes_error
          | some r =>
            cases r with
            | timeOut => exact absurd rfl hnt
            | «break» | «continue» | error =>
              exact absurd (hres.resolve_left (by simp)) not_resumes_error
            | finalFfi _ =>
              rcases hres with hnone | ⟨_, h⟩ | ⟨_, _, h, _⟩
              · simp at hnone
              · simp at h
              · simp at h
            | exception _ _ =>
              exact ⟨guestInv_of_locFrame hlf_s.emptyLocals hG, wsByteEff_of_locFrame hlf_s.emptyLocals⟩
            | returned rv =>
              dsimp only at hnt hres ⊢
              by_cases hsh : (shapeEqHOL (shapeOfHOLExact rv) sh && shapeEqHOL (shapeOfHOLExact rv) ret') = true
              · rw [if_pos hsh] at hnt hres ⊢
                have hsh_self : (shapeEqHOL (shapeOfHOLExact rv) sh && shapeEqHOL (shapeOfHOLExact rv) sh) = true := by
                  simp only [Bool.and_eq_true] at hsh ⊢; exact ⟨hsh.1, hsh.1⟩
                let m := setVarHOLFinite vname rv { sb with locals := s.locals }
                have hlf_m : M13.LocFrame s m := (hlf_s.locals s.locals).setVar vname rv
                have hmG : GuestInv m := guestInv_of_locFrame hlf_m hG
                have heff_sm : WsByteEff s m Rl := wsByteEff_of_locFrame hlf_m
                have hc := hcont m rv hmG hlf_m hsh_self rfl hnt hres
                dsimp only
                exact ⟨⟨hc.1.code, hc.1.memaddrs, hc.1.shMemaddrs, hc.1.baseAddr⟩,
                  (heff_sm.trans hc.2).locals_clock _ _⟩
              · rw [if_neg hsh] at hres
                exact absurd (hres.resolve_left (by simp)) not_resumes_error

private theorem retOk_tailCall_flf {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hG : GuestInv s) {fname : MlS} (hf : M13.FunLocFrame fname)
    (args : List (ExpHOL 64)) :
    retOk s Rl (.call none fname args) := by
  unfold retOk; intro _ _
  have hlf := M13.locFrame_tailCall hG.code hf args
  exact ⟨guestInv_of_locFrame hlf hG, wsByteEff_of_locFrame hlf⟩

private theorem stepOk_tailCall_flf {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hG : GuestInv s) {fname : MlS} (hf : M13.FunLocFrame fname)
    (args : List (ExpHOL 64)) (Q : PanSemStateFiniteExact 64 F → Prop) :
    stepOk s Rl (.call none fname args) Q := by
  unfold stepOk; intro hnt
  have hlf := M13.locFrame_tailCall hG.code hf args
  have hG' : GuestInv (evaluateHOLFiniteState s (.call none fname args)).2 :=
    guestInv_of_locFrame hlf hG
  have heff' : WsByteEff s (evaluateHOLFiniteState s (.call none fname args)).2 Rl :=
    wsByteEff_of_locFrame hlf
  have hres_shape :
      (evaluateHOLFiniteState s (.call none fname args)).1 ≠ none ∧
      (evaluateHOLFiniteState s (.call none fname args)).1 ≠ some .continue ∧
      (evaluateHOLFiniteState s (.call none fname args)).1 ≠ some .break := by
    rw [evaluateHOLFiniteState_call]
    split
    · simp
    · split
      · simp
      · split
        · simp
        · dsimp only
          rcases evaluateHOLFiniteState _ _ with ⟨rb, sb⟩
          cases rb with
          | none => simp
          | some r =>
            cases r <;> simp
            split <;> simp
  exact ⟨fun hn => absurd hn hres_shape.1,
    fun _ => ⟨hres_shape.2.1, hres_shape.2.2, fun _ => ⟨hG', heff'⟩⟩⟩

private theorem stepOk_call_local_flf {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hG : GuestInv s) {fname : MlS} (hf : M13.FunLocFrame fname)
    (vname : MlS) (args : List (ExpHOL 64)) {Q : PanSemStateFiniteExact 64 F → Prop}
    (hQ : ∀ (m : PanSemStateFiniteExact 64 F) (rv : ValueHOL 64),
      GuestInv m → M13.LocFrame s m → m.locals = s.locals.update (vname, rv) → Q m) :
    stepOk s Rl (.call (some (some (.local, vname), none)) fname args) Q := by
  obtain ⟨params, body, ret, hlook, hflf⟩ := hf
  unfold stepOk; intro hnt
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp, fun hr => absurd hr not_resumes_error⟩⟩
  · rw [hargs] at hnt; dsimp only at hnt ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp, fun hr => absurd hr not_resumes_error⟩⟩
    · rw [hl] at hnt; dsimp only at hnt ⊢
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
        ret ret' values callee (by rw [hG.code]; exact hlook) hl
      subst body'
      by_cases hcz : s.clock = 0
      · rw [if_pos hcz] at hnt; exact absurd rfl hnt
      · rw [if_neg hcz] at hnt ⊢
        let ent := callEntryStateHOLFinite s callee
        have hlf_b := hflf ent hG.code
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rb, sb⟩
        dsimp only [ent] at hlf_b; rw [hrun] at hlf_b
        have hlf_s : M13.LocFrame s sb := by
          unfold M13.LocFrame at hlf_b ⊢; dsimp only at hlf_b; rw [hlf_b]; rfl
        cases rb with
        | none =>
          exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp, fun hr => absurd hr not_resumes_error⟩⟩
        | some r =>
          cases r with
          | timeOut => rw [hrun] at hnt; simp at hnt
          | «break» | «continue» | error =>
            exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp, fun hr => absurd hr not_resumes_error⟩⟩
          | finalFfi _ =>
            exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp,
              fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩⟩
          | exception _ _ =>
            exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp,
              fun _ => ⟨guestInv_of_locFrame hlf_s.emptyLocals hG,
                wsByteEff_of_locFrame hlf_s.emptyLocals⟩⟩⟩
          | returned rv =>
            dsimp only
            by_cases hsh : shapeEqHOL (shapeOfHOLExact rv) ret' = true
            · rw [if_pos hsh]
              have hv_eq : isValidValueHOLExact s.toExact .local vname rv =
                  ({ sb with locals := s.locals } : PanSemStateFiniteExact 64 F).isValidValueHOLFinite .local vname rv := rfl
              rw [hv_eq]
              by_cases hv : ({ sb with locals := s.locals } : PanSemStateFiniteExact 64 F).isValidValueHOLFinite .local vname rv = true
              · rw [if_pos hv]
                let m := setKvarHOLFinite .local vname rv { sb with locals := s.locals }
                have hm_eq : m = setVarHOLFinite vname rv { sb with locals := s.locals } := rfl
                have hlf_m : M13.LocFrame s m := by
                  rw [hm_eq]; exact (hlf_s.locals s.locals).setVar vname rv
                have hmG : GuestInv m := guestInv_of_locFrame hlf_m hG
                have heff_sm : WsByteEff s m Rl := wsByteEff_of_locFrame hlf_m
                exact ⟨fun _ => ⟨hmG, heff_sm, hQ m rv hmG hlf_m rfl⟩, fun h => absurd rfl h⟩
              · rw [if_neg hv]
                exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp, fun hr => absurd hr not_resumes_error⟩⟩
            · rw [if_neg hsh]
              exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp, fun hr => absurd hr not_resumes_error⟩⟩

private theorem ws_store_in_640 {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hG : GuestInv s) (ws : BitVec 64)
    (hws : s.globals.lookup (ofString "u256_ws") = some (.val (.word ws)))
    (off : Nat) (hoff : off + 8 ≤ 640)
    (x : BitVec 64) (hx : x = ws + BitVec.ofNat 64 off)
    (hm : s.memaddrs x) :
    ∃ ivl ∈ wsIvl s,
      ivl.1 ≤ x.toNat ∧ x.toNat + 8 ≤ ivl.1 + ivl.2 := by
  have hm' : ordinaryDomain x := by rw [← hG.memaddrs]; exact hm
  have hord := (ordinaryDomain_iff x).mp hm'
  have hsb : sourceBase = 2701131776 := rfl
  have hws_nat : ws.toNat = globN s "u256_ws" := by
    unfold globN; rw [hws]
  have hno_wrap : ws.toNat + off < 2 ^ 64 := by
    by_contra hge
    have hlt : x.toNat < off := by
      subst hx
      have h1 : (ws + BitVec.ofNat 64 off).toNat = (ws.toNat + (BitVec.ofNat 64 off).toNat) % 2^64 :=
        BitVec.toNat_add _ _
      have hoff_bv : (BitVec.ofNat 64 off).toNat = off := by simp; omega
      have hws_lt : ws.toNat < 2^64 := ws.isLt
      omega
    omega
  have hx_nat : x.toNat = ws.toNat + off := by
    subst hx
    have h1 : (ws + BitVec.ofNat 64 off).toNat = (ws.toNat + (BitVec.ofNat 64 off).toNat) % 2^64 :=
      BitVec.toNat_add _ _
    have hoff_bv : (BitVec.ofNat 64 off).toNat = off := by simp; omega
    rw [h1, hoff_bv, Nat.mod_eq_of_lt hno_wrap]
  have hws_pos : globN s "u256_ws" ≠ 0 := by omega
  unfold wsIvl
  rw [if_neg hws_pos]
  exact ⟨(globN s "u256_ws", 640), List.Mem.head _, by omega, by omega⟩

private theorem stepOk_locOnlyW {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hG : GuestInv s) (p : ProgHOL 64) (hp : M13.locOnlyW p = true)
    (hnbc : (evaluateHOLFiniteState s p).1 ≠ some .continue ∧
            (evaluateHOLFiniteState s p).1 ≠ some .break)
    {Q : PanSemStateFiniteExact 64 F → Prop}
    (hQ : ∀ m : PanSemStateFiniteExact 64 F, GuestInv m → M13.LocFrame s m →
      evaluateHOLFiniteState s p = (none, m) → Q m) :
    stepOk s Rl p Q := by
  unfold stepOk; intro _
  have hlf := M13.locFrameW_eval p hp s
  have hG' : GuestInv (evaluateHOLFiniteState s p).2 := guestInv_of_locFrame hlf hG
  have heff' : WsByteEff s (evaluateHOLFiniteState s p).2 Rl := wsByteEff_of_locFrame hlf
  refine ⟨fun hn => ⟨hG', heff', hQ _ hG' hlf (Prod.ext hn rfl)⟩,
    fun _ => ⟨hnbc.1, hnbc.2, fun _ => ⟨hG', heff'⟩⟩⟩

private theorem locOnlyW_while_no_bc {F : Type} (cond : ExpHOL 64) (body : ProgHOL 64)
    (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s (.while cond body)).1 ≠ some .continue ∧
    (evaluateHOLFiniteState s (.while cond body)).1 ≠ some .break := by
  have h : ∀ (k : Nat) (u : PanSemStateFiniteExact 64 F), u.clock = k →
      (evaluateHOLFiniteState u (.while cond body)).1 ≠ some .continue ∧
      (evaluateHOLFiniteState u (.while cond body)).1 ≠ some .break := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro u hclk
      rw [evaluateHOLFiniteState_while_fixClockRewrite]
      split
      · dsimp only
        split
        · split
          · simp
          · have hb_clk := evaluateHOLFiniteState_clock_le (decClockHOLFinite u) body
            have hd_clk : (decClockHOLFinite u).clock < k := by
              simp [decClockHOLFinite, hclk]; omega
            rcases hbo : evaluateHOLFiniteState (decClockHOLFinite u) body with ⟨rb, sb⟩
            simp only [hbo] at hb_clk ⊢
            cases rb with
            | none => exact ih sb.clock (lt_of_le_of_lt hb_clk hd_clk) sb rfl
            | some r =>
              cases r with
              | «continue» => exact ih sb.clock (lt_of_le_of_lt hb_clk hd_clk) sb rfl
              | «break» => simp
              | _ => simp
        · simp
      · simp
  exact h s.clock s rfl

end InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
