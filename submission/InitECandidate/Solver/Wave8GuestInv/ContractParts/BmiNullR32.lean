import InitECandidate.Solver.Wave8GuestInv.ContractParts.BmiBoundStrongR32

/-! Wave 8 R32 (`BmiNullR32`): Step B — `build_mpt_indexed` clock bound and
`WorldKeeps` contract extended to the empty/null slice-array case (`n = 0`),
including when `slice_arr = 0`.

When `locN s "n" = 0`, the loop condition `i < n` (`0 < 0`) is false on its
first evaluation, so the loop body never executes and the local variable
`"slice_arr"` is never read. Replacing `"slice_arr"` in the local environment
with `sourceBase` yields a state satisfying `BuildMptIndexedReadyStrong` whose
execution of `sourceFnBody Guest.Software.guestFn_build_mpt_indexed` is
identical to that of `s`. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
open InitECandidate.Solver.Wave8GuestInv.Fast_C08WkShard03

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12

set_option linter.unusedVariables false

private abbrev bmiNullRlpArgs : List (ExpHOL 64) :=
  [.var .global (ofString "mpt_key_scratch"), .var .local (ofString "i")]
private abbrev bmiNullSetArgs : List (ExpHOL 64) :=
  [.var .local (ofString "m"), .var .global (ofString "mpt_key_scratch"), .var .local (ofString "klen"),
   .load .one (.op .add [.var .local (ofString "slice_arr"), .panop .mul [.var .local (ofString "i"), .const 16]]),
   .load .one (.op .add [.var .local (ofString "slice_arr"), .panop .mul [.var .local (ofString "i"), .const 16], .const 8])]
private abbrev bmiNullLoopCond : ExpHOL 64 :=
  .cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))
private abbrev bmiNullLoopBody : ProgHOL 64 :=
  .decCall (ofString "klen") .one (ofString "rlp_encode_word") bmiNullRlpArgs
    (.seq (.call (some (none, none)) (ofString "mpt_set") bmiNullSetArgs)
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
private abbrev bmiNullTail : ProgHOL 64 :=
  .seq (.call (some (none, none)) (ofString "mpt_root") [.var .local (ofString "m"), .var .local (ofString "out")])
    (.seq (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")]) (.return (.const 0)))

/-- Entry guard for `build_mpt_indexed` when `n = 0` (allowing `slice_arr = 0`). -/
def BuildMptIndexedReadyNull : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧
    (∀ name ∈ (["slice_arr", "n", "out"] : List String),
      ∃ w : BitVec 64, s.locals.lookup (ofString name) = some (.val (.word w))) ∧
    locN s "n" = 0 ∧
    ∃ S Nd, WorldTypedWith s S Nd ∧
      IvlsDisj (bmiWkRti s) (worldTypedIvls s S Nd) ∧
      IvlsDisj [(locN s "out", 32)] (worldOwned s S Nd) ∧
      Inside (locN s "out", 32) sourceBase (globN s "heap_ptr") ∧
      globN s "mpt_key_scratch" ≠ 0

/-- Combined strong-or-null entry guard for `build_mpt_indexed`. -/
def BuildMptIndexedReadyStrongOrNull : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => BuildMptIndexedReadyStrong s ∨ BuildMptIndexedReadyNull s

/-- Patching `"slice_arr"` to `sourceBase` when `n = 0`. -/
private abbrev patchSliceArr {F : Type} (s : PanSemStateFiniteExact 64 F) :
    PanSemStateFiniteExact 64 F :=
  setVarHOLFinite (ofString "slice_arr") (.val (.word (BitVec.ofNat 64 sourceBase))) s

private theorem patchSliceArr_readyStrong {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : BuildMptIndexedReadyNull s) :
    BuildMptIndexedReadyStrong (patchSliceArr s) := by
  obtain ⟨hW, hlocs, hn0, S, Nd, hWT, hdjRti, hdjOut, hinOut, hkey⟩ := h
  let s' := patchSliceArr s
  have hloc_ne : ∀ name : String, ofString name ≠ ofString "slice_arr" →
      s'.locals.lookup (ofString name) = s.locals.lookup (ofString name) := by
    intro name hne
    simp [s', setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      Ne.symm hne]
  have hlocN_ne : ∀ name : String, ofString name ≠ ofString "slice_arr" →
      locN s' name = locN s name := by
    intro name hne
    simp [locN, hloc_ne name hne]
  have hn_s' : locN s' "n" = 0 := by
    rw [hlocN_ne "n" (by decide), hn0]
  have hout_s' : locN s' "out" = locN s "out" := hlocN_ne "out" (by decide)
  have hsa_lk : s'.locals.lookup (ofString "slice_arr") =
      some (.val (.word (BitVec.ofNat 64 sourceBase))) := by
    simp [s', setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hsa_s' : locN s' "slice_arr" = sourceBase := by
    simp [locN, hsa_lk, Fast_C08WkShard03.sourceBase_val]
  have hW' : WorldOK s' := localsFree_worldOK s s'.locals s.clock hW
  have hWT' : WorldTypedWith s' S Nd :=
    (worldTypedWith_build_locals s s'.locals s.clock S Nd).2 hWT
  have hhp_s' : globN s' "heap_ptr" = globN s "heap_ptr" := rfl
  have hsb_hp : sourceBase ≤ globN s "heap_ptr" := hW.1.2.1
  have hready' : BuildMptIndexedReady s' := by
    refine ⟨hW', ?_, by rw [hn_s']; decide, ?_, ?_, ?_, ?_⟩
    · intro name hname
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hname
      rcases hname with rfl | rfl | rfl
      · exact ⟨BitVec.ofNat 64 sourceBase, hsa_lk⟩
      · rw [hloc_ne "n" (by decide)]; exact hlocs "n" (by simp)
      · rw [hloc_ne "out" (by decide)]; exact hlocs "out" (by simp)
    · rw [hsa_s', hn_s', hhp_s']
      exact ⟨le_rfl, by dsimp only; omega⟩
    · rw [hsa_s', hn_s']
      refine ⟨by rw [Fast_C08WkShard03.sourceBase_val]; decide, by decide, ?_⟩
      intro k hk; dsimp only at hk; omega
    · rw [hsa_s', hn_s']
      intro x hx y hy
      simp only [List.mem_singleton] at hx; subst hx
      exact Or.inl rfl
    · intro i hi; rw [hn_s'] at hi; omega
  refine ⟨hready', S, Nd, hWT', ?_, ?_, ?_, ?_, hkey, ?_, ?_⟩
  · have hrti_eq : bmiWkRti s' = bmiWkRti s := by
      unfold bmiWkRti; simp only [hout_s']; rfl
    rw [hrti_eq, worldTypedIvls_locals]
    exact hdjRti
  · rw [hsa_s', hn_s', worldOwned_locals]
    intro x hx y hy
    simp only [List.mem_singleton] at hx; subst hx
    exact Or.inl rfl
  · rw [hout_s', hsa_s', hn_s', worldOwned_locals]
    intro x hx y hy
    simp only [List.mem_singleton] at hx; subst hx
    rcases List.mem_cons.1 hy with rfl | hy'
    · exact Or.inr (Or.inl rfl)
    · exact hdjOut (locN s "out", 32) (by simp) y hy'
  · rw [hout_s']; exact hinOut
  · intro i hi; rw [hn_s'] at hi; omega
  · intro i hi; rw [hn_s'] at hi; omega

/-- When `i = 0` and `n = 0`, `.while bmiNullLoopCond bmiNullLoopBody` exits immediately
in 0 steps without touching any other local or memory. -/
private theorem eval_while_bmi_zero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word 0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word 0))) :
    evaluateHOLFiniteState s (.while bmiNullLoopCond bmiNullLoopBody) = (none, s) := by
  have hw := evaluateHOLFiniteState_while_fixClockRewrite s bmiNullLoopCond bmiNullLoopBody
  have hc : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
      bmiNullLoopCond = some (.val (.word 0)) := by
    simp [bmiNullLoopCond, evalHOLFinite, evalHOLExact, hi, hn,
      Compiler.Encoders.Asm.wordCmpHOL]
  rw [hc] at hw
  simpa using hw

/-- Evaluating `sourceFnBody Guest.Software.guestFn_build_mpt_indexed` when `n = 0`
does not depend on `"slice_arr"`. -/
private theorem eval_bmi_body_patchSliceArr {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (hA : ArenaReady s)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word 0))) :
    let r1 := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_build_mpt_indexed)
    let r2 := evaluateHOLFiniteState (patchSliceArr s)
      (sourceFnBody Guest.Software.guestFn_build_mpt_indexed)
    r1.1 = r2.1 ∧
    r2.2 = { r1.2 with locals := r2.2.locals } := by
  have hbody : sourceFnBody Guest.Software.guestFn_build_mpt_indexed =
      .decCall (ofString "mark") .one (ofString "heap_mark") []
        (.decCall (ofString "m") .one (ofString "mpt_new") [.const 0, .const 0]
          (.dec (ofString "i") .one (.const 0)
            (.seq (.while bmiNullLoopCond bmiNullLoopBody) bmiNullTail))) := by
    simp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_build_mpt_indexed,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
      Option.map, List.map]
    rfl
  dsimp only
  rw [hbody]
  let s' := patchSliceArr s
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite s,
      evaluateHOLFiniteState_decCall_fixClockRewrite s']
  have hargs_mark : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [] =
      some [] := rfl
  have hargs_mark' : evalListHOLFinite s' (h := fun a => Classical.propDecidable (s'.memaddrs a)) [] =
      some [] := rfl
  rw [hargs_mark, hargs_mark']
  dsimp only
  have hl_mark : PanSemStateFiniteExact.lookupCodeHOLFinite s'.code.lookup (ofString "heap_mark") [] =
      PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup (ofString "heap_mark") [] := rfl
  rw [hl_mark]
  rcases hlm : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup (ofString "heap_mark") [] with _ | ⟨b1, c1, ret1⟩
  · simp [s', patchSliceArr, setVarHOLFinite]
  · dsimp only
    have hclk1 : s'.clock = s.clock := rfl
    rw [hclk1]
    split_ifs with hz1
    · simp [emptyLocalsHOLFinite, s', patchSliceArr, setVarHOLFinite]
    · have hce1 : callEntryStateHOLFinite s' c1 = callEntryStateHOLFinite s c1 := rfl
      rw [hce1]
      rcases hb1 : evaluateHOLFiniteState (callEntryStateHOLFinite s c1) b1 with ⟨r_m, p_m⟩
      cases r_m with
      | none => simp
      | some r_m' =>
        cases r_m' with
        | returned v_mark =>
          dsimp only
          split_ifs with hsh1
          · set s1 := setVarHOLFinite (ofString "mark") v_mark { p_m with locals := s.locals }
            set s1' := setVarHOLFinite (ofString "mark") v_mark { p_m with locals := s'.locals }
            rw [evaluateHOLFiniteState_decCall_fixClockRewrite s1,
                evaluateHOLFiniteState_decCall_fixClockRewrite s1']
            have hargs_new : evalListHOLFinite s1'
                (h := fun a => Classical.propDecidable (s1'.memaddrs a)) [.const 0, .const 0] =
                evalListHOLFinite s1
                (h := fun a => Classical.propDecidable (s1.memaddrs a)) [.const 0, .const 0] := rfl
            rw [hargs_new]
            rcases han : evalListHOLFinite s1
                (h := fun a => Classical.propDecidable (s1.memaddrs a)) [.const 0, .const 0] with _ | vs_new
            · simp [s1', s1, setVarHOLFinite]
            · dsimp only
              have hln_eq : PanSemStateFiniteExact.lookupCodeHOLFinite s1'.code.lookup (ofString "mpt_new") vs_new =
                  PanSemStateFiniteExact.lookupCodeHOLFinite s1.code.lookup (ofString "mpt_new") vs_new := rfl
              rw [hln_eq]
              rcases hln : PanSemStateFiniteExact.lookupCodeHOLFinite s1.code.lookup (ofString "mpt_new") vs_new with _ | ⟨b2, c2, ret2⟩
              · simp [s1', s1, setVarHOLFinite]
              · dsimp only
                have hclk2 : s1'.clock = s1.clock := rfl
                rw [hclk2]
                split_ifs with hz2
                · simp [emptyLocalsHOLFinite, s1', s1, setVarHOLFinite]
                · have hce2 : callEntryStateHOLFinite s1' c2 = callEntryStateHOLFinite s1 c2 := rfl
                  rw [hce2]
                  rcases hb2 : evaluateHOLFiniteState (callEntryStateHOLFinite s1 c2) b2 with ⟨r_n, p_n⟩
                  cases r_n with
                  | none => simp
                  | some r_n' =>
                    cases r_n' with
                    | returned v_m =>
                      dsimp only
                      split_ifs with hsh2
                      · set s2 := setVarHOLFinite (ofString "m") v_m { p_n with locals := s1.locals }
                        set s2' := setVarHOLFinite (ofString "m") v_m { p_n with locals := s1'.locals }
                        rw [evaluateHOLFiniteState_dec_total, evaluateHOLFiniteState_dec_total]
                        dsimp only
                        have he0 : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a)) (.const 0) =
                            some (.val (.word 0)) := rfl
                        have he0' : @evalHOLExact 64 F _ s2'.toExact (fun a => Classical.propDecidable (s2'.memaddrs a)) (.const 0) =
                            some (.val (.word 0)) := rfl
                        have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) = true := by
                          simp [shapeEqHOL, shapeOfHOLExact]
                        simp only [he0, he0', hsh0, ↓reduceIte]
                        set s3 := setVarHOLFinite (ofString "i") (.val (.word 0)) s2
                        set s3' := setVarHOLFinite (ofString "i") (.val (.word 0)) s2'
                        have hi3 : s3.locals.lookup (ofString "i") = some (.val (.word 0)) := by
                          simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                        have hi3' : s3'.locals.lookup (ofString "i") = some (.val (.word 0)) := by
                          simp [s3', setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                        have hn3 : s3.locals.lookup (ofString "n") = some (.val (.word 0)) := by
                          simp [s3, s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                            show ofString "i" ≠ ofString "n" by decide,
                            show ofString "m" ≠ ofString "n" by decide,
                            show ofString "mark" ≠ ofString "n" by decide, hn]
                        have hn3' : s3'.locals.lookup (ofString "n") = some (.val (.word 0)) := by
                          simp [s3', s2', s1', s', setVarHOLFinite,
                            HolFiniteMapExact.lookup_update, FUPDATE,
                            show ofString "i" ≠ ofString "n" by decide,
                            show ofString "m" ≠ ofString "n" by decide,
                            show ofString "mark" ≠ ofString "n" by decide,
                            show ofString "slice_arr" ≠ ofString "n" by decide, hn]
                        rw [evaluateHOLFiniteState_seq_line780 s3,
                            evaluateHOLFiniteState_seq_line780 s3',
                            eval_while_bmi_zero s3 hi3 hn3,
                            eval_while_bmi_zero s3' hi3' hn3']
                        dsimp only
                        have hm3 : s3'.locals.lookup (ofString "m") = s3.locals.lookup (ofString "m") := by
                          simp [s3', s3, s2', s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                            show ofString "i" ≠ ofString "m" by decide]
                        have hout3 : s3'.locals.lookup (ofString "out") = s3.locals.lookup (ofString "out") := by
                          simp [s3', s3, s2', s2, s1', s1, s', setVarHOLFinite,
                            HolFiniteMapExact.lookup_update, FUPDATE,
                            show ofString "i" ≠ ofString "out" by decide,
                            show ofString "m" ≠ ofString "out" by decide,
                            show ofString "mark" ≠ ofString "out" by decide,
                            show ofString "slice_arr" ≠ ofString "out" by decide]
                        have hmark3 : s3'.locals.lookup (ofString "mark") = s3.locals.lookup (ofString "mark") := by
                          simp [s3', s3, s2', s2, s1', s1, setVarHOLFinite,
                            HolFiniteMapExact.lookup_update, FUPDATE,
                            show ofString "i" ≠ ofString "mark" by decide,
                            show ofString "m" ≠ ofString "mark" by decide]
                        unfold bmiNullTail
                        rw [evaluateHOLFiniteState_seq_line780 s3,
                            evaluateHOLFiniteState_seq_line780 s3']
                        rw [evaluateHOLFiniteState_call s3, evaluateHOLFiniteState_call s3']
                        have hargs_rt : evalListHOLFinite s3'
                            (h := fun a => Classical.propDecidable (s3'.memaddrs a))
                            [.var .local (ofString "m"), .var .local (ofString "out")] =
                            evalListHOLFinite s3
                            (h := fun a => Classical.propDecidable (s3.memaddrs a))
                            [.var .local (ofString "m"), .var .local (ofString "out")] := by
                          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hm3, hout3]
                        rw [hargs_rt]
                        rcases hart : evalListHOLFinite s3
                            (h := fun a => Classical.propDecidable (s3.memaddrs a))
                            [.var .local (ofString "m"), .var .local (ofString "out")] with _ | vs_rt
                        · simp [s3', s3, s2', s2, s1', s1, setVarHOLFinite]
                        · dsimp only
                          have hlrt_eq : PanSemStateFiniteExact.lookupCodeHOLFinite s3'.code.lookup (ofString "mpt_root") vs_rt =
                              PanSemStateFiniteExact.lookupCodeHOLFinite s3.code.lookup (ofString "mpt_root") vs_rt := rfl
                          rw [hlrt_eq]
                          rcases hlrt : PanSemStateFiniteExact.lookupCodeHOLFinite s3.code.lookup (ofString "mpt_root") vs_rt with _ | ⟨b3, c3, ret3⟩
                          · simp [s3', s3, s2', s2, s1', s1, setVarHOLFinite]
                          · dsimp only
                            have hclk3 : s3'.clock = s3.clock := rfl
                            rw [hclk3]
                            split_ifs with hz3
                            · simp [emptyLocalsHOLFinite, s3', s3, s2', s2, s1', s1, setVarHOLFinite]
                            · have hce3 : callEntryStateHOLFinite s3' c3 = callEntryStateHOLFinite s3 c3 := rfl
                              rw [hce3]
                              rcases hb3 : evaluateHOLFiniteState (callEntryStateHOLFinite s3 c3) b3 with ⟨r_rt, p_rt⟩
                              cases r_rt with
                              | none => simp
                              | some r_rt' =>
                                cases r_rt' with
                                | returned v_rt =>
                                  dsimp only
                                  split_ifs with hsh3
                                  · dsimp only
                                    set s4 := { p_rt with locals := s3.locals }
                                    set s4' := { p_rt with locals := s3'.locals }
                                    rw [evaluateHOLFiniteState_seq_line780 s4,
                                        evaluateHOLFiniteState_seq_line780 s4']
                                    rw [evaluateHOLFiniteState_call s4, evaluateHOLFiniteState_call s4']
                                    have hargs_rel : evalListHOLFinite s4'
                                        (h := fun a => Classical.propDecidable (s4'.memaddrs a))
                                        [.var .local (ofString "mark")] =
                                        evalListHOLFinite s4
                                        (h := fun a => Classical.propDecidable (s4.memaddrs a))
                                        [.var .local (ofString "mark")] := by
                                      simp [s4', s4, evalListHOLFinite, evalListHOLExact, evalHOLExact, hmark3]
                                    rw [hargs_rel]
                                    rcases harel : evalListHOLFinite s4
                                        (h := fun a => Classical.propDecidable (s4.memaddrs a))
                                        [.var .local (ofString "mark")] with _ | vs_rel
                                    · simp [s4', s4]
                                    · dsimp only
                                      have hlrel_eq : PanSemStateFiniteExact.lookupCodeHOLFinite s4'.code.lookup (ofString "heap_release") vs_rel =
                                          PanSemStateFiniteExact.lookupCodeHOLFinite s4.code.lookup (ofString "heap_release") vs_rel := rfl
                                      rw [hlrel_eq]
                                      rcases hlrel : PanSemStateFiniteExact.lookupCodeHOLFinite s4.code.lookup (ofString "heap_release") vs_rel with _ | ⟨b4, c4, ret4⟩
                                      · simp [s4', s4]
                                      · dsimp only
                                        have hclk4 : s4'.clock = s4.clock := rfl
                                        rw [hclk4]
                                        split_ifs with hz4
                                        · simp [emptyLocalsHOLFinite, s4', s4]
                                        · have hce4 : callEntryStateHOLFinite s4' c4 = callEntryStateHOLFinite s4 c4 := rfl
                                          rw [hce4]
                                          rcases hb4 : evaluateHOLFiniteState (callEntryStateHOLFinite s4 c4) b4 with ⟨r_rel, p_rel⟩
                                          cases r_rel with
                                          | none => simp
                                          | some r_rel' =>
                                            cases r_rel' with
                                            | returned v_rel =>
                                              dsimp only
                                              split_ifs with hsh4
                                              · dsimp only
                                                rw [evaluateHOLFiniteState_return, evaluateHOLFiniteState_return]
                                                simp only [evalHOLFinite, evalHOLExact]
                                                split_ifs <;> simp [emptyLocalsHOLFinite, s4', s4]
                                              · simp [emptyLocalsHOLFinite]
                                            | _ => simp [emptyLocalsHOLFinite]
                                  · simp [emptyLocalsHOLFinite]
                                | _ => simp [emptyLocalsHOLFinite]
                      · simp [emptyLocalsHOLFinite]
                    | _ => simp [emptyLocalsHOLFinite]
          · simp [emptyLocalsHOLFinite]
        | _ => simp [emptyLocalsHOLFinite]

/-- Clock bound for `build_mpt_indexed` under `BuildMptIndexedReadyStrongOrNull`. -/
theorem fb_build_mpt_indexed_strong_or_null :
    TerminatingFunBoundedOn BuildMptIndexedReadyStrongOrNull
      (ofString "build_mpt_indexed") K.«build_mpt_indexed» := by
  obtain ⟨params, body, ret, hlook, hprog⟩ := BmiBound.fb_build_mpt_indexed_strong
  have hbody_eq : body = sourceFnBody Guest.Software.guestFn_build_mpt_indexed := by
    have := lookup_build_mpt_indexed_strong
    rw [hlook] at this
    cases Option.some.inj this
    rfl
  subst hbody_eq
  refine ⟨params, sourceFnBody Guest.Software.guestFn_build_mpt_indexed, ret, hlook, ?_⟩
  intro F s hcode hP
  rcases hP with hStrong | hNull
  · exact hprog s hcode hStrong
  · have hStrong' : BuildMptIndexedReadyStrong (patchSliceArr s) :=
      patchSliceArr_readyStrong hNull
    have hrun' := hprog (patchSliceArr s) hcode hStrong'
    obtain ⟨wn, hwn⟩ := hNull.2.1 "n" (by simp)
    have hwn0 : wn = 0 := by
      have hn0 := hNull.2.2.1
      simp only [locN, hwn] at hn0
      exact BitVec.eq_of_toNat_eq hn0
    subst hwn0
    have heq := eval_bmi_body_patchSliceArr s hcode hNull.1.1 hwn
    have hclk_eq : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_build_mpt_indexed)).2.clock =
        (evaluateHOLFiniteState (patchSliceArr s) (sourceFnBody Guest.Software.guestFn_build_mpt_indexed)).2.clock := by
      rw [heq.2]
    intro hnt
    rw [heq.1] at hnt
    rw [hclk_eq]
    exact hrun' hnt

/-- `WorldKeeps` contract for `build_mpt_indexed` under `BuildMptIndexedReadyStrongOrNull`. -/
theorem wk_build_mpt_indexed_strong_or_null :
    WorldKeeps BuildMptIndexedReadyStrongOrNull
      (fun s => [(locN s "out", 32),
        (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
        (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "build_mpt_indexed") := by
  refine ⟨[(ofString "slice_arr", .one), (ofString "n", .one), (ofString "out", .one)],
    sourceFnBody Guest.Software.guestFn_build_mpt_indexed, .one,
    lookup_build_mpt_indexed_strong, ?_⟩
  intro F s0 hcode hP ⟨values, hlook⟩ hnt hres
  rcases hP with hStrong | hNull
  · obtain ⟨params, body, ret, hlk, hspec⟩ := wk_build_mpt_indexed_strong
    have hinj : params = [(ofString "slice_arr", .one), (ofString "n", .one), (ofString "out", .one)] ∧
        body = sourceFnBody Guest.Software.guestFn_build_mpt_indexed ∧ ret = .one := by
      have := lookup_build_mpt_indexed_strong
      rw [hlk] at this
      cases Option.some.inj this
      exact ⟨rfl, rfl, rfl⟩
    rcases hinj with ⟨rfl, rfl, rfl⟩
    exact hspec s0 hcode hStrong ⟨values, hlook⟩ hnt hres
  · have hStrong' : BuildMptIndexedReadyStrong (patchSliceArr s0) :=
      patchSliceArr_readyStrong hNull
    obtain ⟨wn, hwn⟩ := hNull.2.1 "n" (by simp)
    have hwn0 : wn = 0 := by
      have hn0 := hNull.2.2.1
      simp only [locN, hwn] at hn0
      exact BitVec.eq_of_toNat_eq hn0
    subst hwn0
    obtain ⟨wo, hwo⟩ := hNull.2.1 "out" (by simp)
    have heq := eval_bmi_body_patchSliceArr s0 hcode hNull.1.1 hwn
    have hlook' : ∃ values', PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
        (ofString "build_mpt_indexed") values' =
        some (sourceFnBody Guest.Software.guestFn_build_mpt_indexed,
          (patchSliceArr s0).locals, .one) := by
      have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
        originalRuntimeCode.lookup (ofString "build_mpt_indexed") values
        (sourceFnBody Guest.Software.guestFn_build_mpt_indexed) s0.locals .one hlook
      simp only [lookupCodeHOLExact, lookup_build_mpt_indexed_strong] at hx
      rcases values with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩ <;> try simp at hx
      obtain ⟨hsh, hlEq⟩ := hx
      refine ⟨[.val (.word (BitVec.ofNat 64 sourceBase)), v2, v3], ?_⟩
      unfold PanSemStateFiniteExact.lookupCodeHOLFinite
      have hraw : lookupCodeHOLExact originalRuntimeCode.lookup (ofString "build_mpt_indexed")
          [.val (.word (BitVec.ofNat 64 sourceBase)), v2, v3] =
          some (sourceFnBody Guest.Software.guestFn_build_mpt_indexed,
            (patchSliceArr s0).locals.lookup, .one) := by
        simp only [lookupCodeHOLExact, lookup_build_mpt_indexed_strong,
          List.length, List.zip, List.zipWith, List.all, Bool.and_true, Bool.and_eq_true]
        have hsh' : ((List.map Prod.fst
            [(ofString "slice_arr", ShapeHOL.one), (ofString "n", ShapeHOL.one), (ofString "out", ShapeHOL.one)]).Nodup ∧
            True ∧
            (shapeEqHOL .one (shapeOfHOLExact (.val (.word (BitVec.ofNat 64 sourceBase)))) = true ∧
             shapeEqHOL .one (shapeOfHOLExact v2) = true ∧
             shapeEqHOL .one (shapeOfHOLExact v3) = true)) :=
          ⟨by decide, trivial, by simp [shapeEqHOL, shapeOfHOLExact], hsh.2.2.1, hsh.2.2.2⟩
        rw [if_pos hsh']
        congr 1; congr 1; congr 1
        simp only [patchSliceArr, setVarHOLFinite, emptyLocalsHOLFinite,
          List.foldl, List.map, List.zipWith]
        funext k
        simp only [HolFiniteMapExact.update, FUPDATE, ← hlEq]
        by_cases hk1 : k = ofString "slice_arr"
        · subst hk1
          simp [show ofString "slice_arr" ≠ ofString "out" by decide,
                show ofString "slice_arr" ≠ ofString "n" by decide]
        · simp [hk1, Ne.symm hk1]
      split
      · rename_i hnone
        rw [hraw] at hnone; cases hnone
      · rename_i b c r hsome
        rw [hraw] at hsome
        obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hsome)
        rfl
    obtain ⟨params, body, ret, hlk, hspec⟩ := wk_build_mpt_indexed_strong
    have hinj : params = [(ofString "slice_arr", .one), (ofString "n", .one), (ofString "out", .one)] ∧
        body = sourceFnBody Guest.Software.guestFn_build_mpt_indexed ∧ ret = .one := by
      have := lookup_build_mpt_indexed_strong
      rw [hlk] at this
      cases Option.some.inj this
      exact ⟨rfl, rfl, rfl⟩
    rcases hinj with ⟨rfl, rfl, rfl⟩
    have hnt' : (evaluateHOLFiniteState (patchSliceArr s0)
        (sourceFnBody Guest.Software.guestFn_build_mpt_indexed)).1 ≠ some .timeOut := by
      rw [← heq.1]; exact hnt
    have hres' : Resumes (evaluateHOLFiniteState (patchSliceArr s0)
        (sourceFnBody Guest.Software.guestFn_build_mpt_indexed)).1 := by
      rw [← heq.1]; exact hres
    have hws' := hspec (patchSliceArr s0) hcode hStrong' hlook' hnt' hres'
    set post := (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_build_mpt_indexed)).2
    set post' := (evaluateHOLFiniteState (patchSliceArr s0)
      (sourceFnBody Guest.Software.guestFn_build_mpt_indexed)).2
    have hout_eq : locN (patchSliceArr s0) "out" = locN s0 "out" := by
      simp [patchSliceArr, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "slice_arr" ≠ ofString "out" by decide]
    have hR_eq : ([(locN (patchSliceArr s0) "out", 32),
        (globN (patchSliceArr s0) "keccak_pad", if globN (patchSliceArr s0) "keccak_pad" = 0 then 0 else 136),
        (globN (patchSliceArr s0) "keccak_st", if globN (patchSliceArr s0) "keccak_st" = 0 then 0 else 200),
        (globN (patchSliceArr s0) "mpt_hash_scratch", if globN (patchSliceArr s0) "mpt_hash_scratch" = 0 then 0 else 40),
        (globN (patchSliceArr s0) "mpt_key_scratch", if globN (patchSliceArr s0) "mpt_key_scratch" = 0 then 0 else 16)]) =
      ([(locN s0 "out", 32),
        (globN s0 "keccak_pad", if globN s0 "keccak_pad" = 0 then 0 else 136),
        (globN s0 "keccak_st", if globN s0 "keccak_st" = 0 then 0 else 200),
        (globN s0 "mpt_hash_scratch", if globN s0 "mpt_hash_scratch" = 0 then 0 else 40),
        (globN s0 "mpt_key_scratch", if globN s0 "mpt_key_scratch" = 0 then 0 else 16)]) := by
      rw [hout_eq]; rfl
    have hpost_eq : post' = { post with locals := post'.locals } := heq.2
    have hpost_rev : post = { post' with locals := post.locals, clock := post'.clock } := by
      rw [hpost_eq]
    obtain ⟨hAp', hhp', hgk', hrk', hwt'⟩ := hws'
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hpost_rev]
      exact ⟨guestInv_with_locals_clock post' post.locals post'.clock hAp'.1, hAp'.2⟩
    · have : globN post "heap_ptr" = globN post' "heap_ptr" := by
        rw [hpost_eq]; rfl
      rw [this]; exact hhp'
    · intro k hk
      change s0.globals.lookup k = post.globals.lookup k
      have : post.globals = post'.globals := by rw [hpost_eq]
      rw [this]
      exact hgk' k hk
    · intro r hr hnz k hk hno
      have hmw : memW post (globN s0 r.1 + k) = memW post' (globN (patchSliceArr s0) r.1 + k) := by
        rw [hpost_eq]; rfl
      rw [hmw]
      exact hrk' r hr hnz k hk (by dsimp only; rw [hR_eq]; exact hno)
    · intro S Nd hWT hDisj
      have hWT_p : WorldTypedWith (patchSliceArr s0) S Nd :=
        (worldTypedWith_build_locals s0 (patchSliceArr s0).locals s0.clock S Nd).2 hWT
      have hDisj_p : IvlsDisj
          [(locN (patchSliceArr s0) "out", 32),
           (globN (patchSliceArr s0) "keccak_pad", if globN (patchSliceArr s0) "keccak_pad" = 0 then 0 else 136),
           (globN (patchSliceArr s0) "keccak_st", if globN (patchSliceArr s0) "keccak_st" = 0 then 0 else 200),
           (globN (patchSliceArr s0) "mpt_hash_scratch", if globN (patchSliceArr s0) "mpt_hash_scratch" = 0 then 0 else 40),
           (globN (patchSliceArr s0) "mpt_key_scratch", if globN (patchSliceArr s0) "mpt_key_scratch" = 0 then 0 else 16)]
          (worldTypedIvls (patchSliceArr s0) S Nd) := by
        rw [hR_eq]; exact hDisj
      obtain ⟨S', Nd', hsub, hWT_post', hOG', hFO', _⟩ := hwt' S Nd hWT_p hDisj_p
      refine ⟨S', Nd', hsub, ?_, ?_, ?_, trivial⟩
      · rw [hpost_rev]
        exact (worldTypedWith_build_locals post' post.locals post'.clock S' Nd').2 hWT_post'
      · intro o ho
        have ho' : o ∈ worldOwned post' S' Nd' := by
          rw [hpost_rev] at ho; exact ho
        rcases hOG' o ho' with rfl | ⟨j, hj, hin⟩ | hin_hp
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨j, hj, hin⟩)
        · refine Or.inr (Or.inr ?_)
          have : globN post "heap_ptr" = globN post' "heap_ptr" := by
            rw [hpost_eq]; rfl
          rw [this]; exact hin_hp
      · intro a hkeep hfresh
        have hmem_eq : post.memory = post'.memory := by rw [hpost_eq]
        rw [hmem_eq]
        exact hFO' a (by dsimp only; rw [hR_eq]; exact hkeep) hfresh

end InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12
