import InitECandidate.Solver.Wave8GuestInv.MemoryViews
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M27.rv_min

/-! Value contract `rv_common_prefix_length` for micro-shard `m27` (`wave8/contracts-m27`),
frozen revision 9 (`8a79d9f28`, tag `wave8-spec-frozen-r9`).

Imports only the light split module `InitECandidate.Solver.Wave8GuestInv.MemoryViews` and `rv_min`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8Contracts.M27

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

theorem lookup_common_prefix_length :
    originalRuntimeCode.lookup (ofString "common_prefix_length") =
      some ((sourceFunctionEntry Guest.Software.guestFn_common_prefix_length).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 251 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_common_prefix_length) rfl

private theorem pan_two_arg_lookup
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (name first second : MlS) (ps1 ps2 rs : ShapeHOL) (body : ProgHOL 64) (v1 v2 : ValueHOL 64)
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

private theorem two_arg_lookup_inv
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (name first second : MlS) (ps1 ps2 rs : ShapeHOL) (body : ProgHOL 64) (v1 v2 : ValueHOL 64)
    {foundBody : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)} {foundRs : ShapeHOL}
    (different : first ≠ second)
    (lookup : code name = some ([(first, ps1), (second, ps2)], body, rs))
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite code name [v1, v2] =
      some (foundBody, callee, foundRs)) :
    foundBody = body ∧
      callee = (HolFiniteMapExact.empty.update (first, v1)).update (second, v2) ∧
      shapeEqHOL ps1 (shapeOfHOLExact v1) = true ∧
      shapeEqHOL ps2 (shapeOfHOLExact v2) = true := by
  have hshapes : shapeEqHOL ps1 (shapeOfHOLExact v1) = true ∧ shapeEqHOL ps2 (shapeOfHOLExact v2) = true := by
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
    split at hfound
    · cases hfound
    · rename_i _ _ _ raw
      simp [lookupCodeHOLExact, lookup, different] at raw
      exact ⟨raw.1.1, raw.1.2⟩
  rw [pan_two_arg_lookup code name first second ps1 ps2 rs body v1 v2 different hshapes.1 hshapes.2 lookup] at hfound
  cases hfound
  exact ⟨rfl, rfl, hshapes.1, hshapes.2⟩

private theorem decCall_returned_inv_cpl {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {name function : MlS} {shape : ShapeHOL}
    {arguments : List (ExpHOL 64)} {continuation : ProgHOL 64} {retVal : ValueHOL 64}
    (hrun : evaluateHOLFiniteState s (.decCall name shape function arguments continuation) =
      (some (.returned retVal), post)) :
    ∃ (values : List (ValueHOL 64)) (body : ProgHOL 64)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
      (w : ValueHOL 64) (bodyPost inner : PanSemStateFiniteExact 64 F),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments =
        some values ∧
      lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
        (some (.returned w), bodyPost) ∧
      evaluateHOLFiniteState (setVarHOLFinite name w {bodyPost with locals := s.locals})
        continuation = (some (.returned retVal), inner) := by
  cases args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      arguments with
  | none =>
    rw [evaluateHOLFiniteState_decCall_args_none s name shape function arguments continuation args] at hrun
    simp at hrun
  | some values =>
    rw [evaluateHOLFiniteState_decCall_total, args] at hrun
    dsimp only at hrun
    cases lookup : lookupCodeHOLFinite s.code.lookup function values with
    | none => rw [lookup] at hrun; simp at hrun
    | some installed =>
      obtain ⟨body, callee, returnShape⟩ := installed
      rw [lookup] at hrun
      dsimp only at hrun
      split at hrun
      · simp at hrun
      · have remaining := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
        | mk r1 bodyPost =>
          rw [bodyRun] at hrun remaining
          have fixed : fixClockHOLFinite (callEntryStateHOLFinite s callee) (r1, bodyPost) =
              (r1, bodyPost) := by
            simp [fixClockHOLFinite, Nat.not_lt.mpr remaining]
          rw [fixed] at hrun
          dsimp only at hrun
          rcases r1 with _ | (_ | _ | _ | _ | w | _ | _)
          all_goals first
            | (simp at hrun; done)
            | skip
          simp only [] at hrun
          split at hrun
          · obtain ⟨e, _⟩ := Prod.mk.inj hrun
            exact ⟨values, body, callee, returnShape, w, bodyPost, _, rfl, lookup, bodyRun,
              Prod.ext e rfl⟩
          · simp at hrun

private theorem cpl_while_outcome {F : Type}
    (k : Nat) (st : PanSemStateFiniteExact 64 F) (nw : BitVec 64)
    (hn : st.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hclk : st.clock ≤ k) :
    let wbody : ProgHOL 64 :=
      .seq
        (.ite (.cmp .notEqual
            (.loadByte (.op .add [.var .local (ofString "a"), .var .local (ofString "i")]))
            (.loadByte (.op .add [.var .local (ofString "b"), .var .local (ofString "i")])))
          (.return (.var .local (ofString "i")))
          .skip)
        (.assign .local (ofString "i")
          (.op .add [.var .local (ofString "i"), .const 1#64]))
    let wprog : ProgHOL 64 :=
      .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) wbody
    ((evaluateHOLFiniteState st wprog).1 = none →
      (evaluateHOLFiniteState st wprog).2.locals.lookup (ofString "n") = some (.val (.word nw))) ∧
    (∀ rv : ValueHOL 64, (evaluateHOLFiniteState st wprog).1 = some (.returned rv) →
      ∃ iw : BitVec 64, rv = .val (.word iw) ∧ iw.toNat < nw.toNat) := by
  induction k generalizing st with
  | zero =>
    intro wbody wprog
    have hc0 : st.clock = 0 := by omega
    constructor
    · intro hnorm
      have hpres := evaluate_avoidsLocal_flowing (ofString "n") wprog (by decide) st (Or.inl hnorm)
      exact hpres.trans hn
    · intro rv hret
      dsimp only [wprog] at hret
      rw [evaluateHOLFiniteState_while_total] at hret
      split at hret
      · split at hret <;> simp [hc0] at hret
      · simp at hret
  | succ m ih =>
    intro wbody wprog
    constructor
    · intro hnorm
      have hpres := evaluate_avoidsLocal_flowing (ofString "n") wprog (by decide) st (Or.inl hnorm)
      exact hpres.trans hn
    · intro rv hret
      dsimp only [wprog] at hret
      rw [evaluateHOLFiniteState_while_total] at hret
      rcases hi_lk : st.locals.lookup (ofString "i") with _ | iv
      · have hcond : evalHOLFinite st (h := fun x => Classical.propDecidable (st.memaddrs x))
            (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) = none := by
          rw [evalHOLFinite_eq_toExact]
          simp [evalHOLExact, hi_lk]
        rw [hcond] at hret
        simp at hret
      · rcases iv with ⟨⟨iw⟩⟩ | _ | _
        · have hcond : evalHOLFinite st (h := fun x => Classical.propDecidable (st.memaddrs x))
              (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
              some (.val (.word (if iw.toNat < nw.toNat then 1#64 else 0#64))) := by
            rw [evalHOLFinite_eq_toExact]
            simp [evalHOLExact, hi_lk, hn, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def,
              decide_eq_true_eq]
          rw [hcond] at hret
          by_cases hlt : iw.toNat < nw.toNat
          · rw [if_pos hlt] at hret
            dsimp only at hret
            rw [if_pos (show (1#64 : BitVec 64) ≠ 0 by decide)] at hret
            split at hret
            · simp at hret
            · rw [fixClockHOLFinite_evaluateState] at hret
              have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) wbody
              have hframe_n := evaluate_avoidsLocal_flowing (ofString "n") wbody (by decide)
                (decClockHOLFinite st)
              rcases hbr : evaluateHOLFiniteState (decClockHOLFinite st) wbody with ⟨r1, mid⟩
              rw [hbr] at hret hrem hframe_n
              dsimp only at hframe_n
              have hmclk : mid.clock ≤ m := by
                change mid.clock ≤ st.clock - 1 at hrem
                omega
              cases r1 with
              | none =>
                have hmid_n : mid.locals.lookup (ofString "n") = some (.val (.word nw)) :=
                  (hframe_n (Or.inl rfl)).trans hn
                exact (ih mid hmid_n hmclk).2 rv hret
              | some r1' =>
                cases r1' with
                | «continue» =>
                  have hmid_n : mid.locals.lookup (ofString "n") = some (.val (.word nw)) :=
                    (hframe_n (Or.inr (Or.inr rfl))).trans hn
                  exact (ih mid hmid_n hmclk).2 rv hret
                | «break» => simp at hret
                | returned rv' =>
                  dsimp only at hret
                  simp only [Option.some.injEq, PanSemResultExact.returned.injEq] at hret
                  subst hret
                  -- Extract `rv' = .val (.word iw)` from `hbr`!
                  have hbr1 : (evaluateHOLFiniteState (decClockHOLFinite st) wbody).1 =
                      some (.returned rv') := by rw [hbr]
                  dsimp only [wbody] at hbr1
                  rw [evaluateHOLFiniteState_seq_line780] at hbr1
                  rcases hite : evaluateHOLFiniteState (decClockHOLFinite st)
                      (.ite (.cmp .notEqual
                          (.loadByte (.op .add [.var .local (ofString "a"), .var .local (ofString "i")]))
                          (.loadByte (.op .add [.var .local (ofString "b"), .var .local (ofString "i")])))
                        (.return (.var .local (ofString "i")))
                        .skip) with ⟨ri, mi⟩
                  rw [hite] at hbr1
                  cases ri with
                  | none =>
                    dsimp only at hbr1
                    rw [evaluateHOLFiniteState_assign] at hbr1
                    revert hbr1
                    split
                    · simp
                    · split <;> simp
                  | some ri' =>
                    dsimp only at hbr1
                    simp only [Option.some.injEq] at hbr1
                    subst hbr1
                    rw [evaluateHOLFiniteState_ite] at hite
                    revert hite
                    split
                    · split
                      · rw [evaluateHOLFiniteState_skip]; simp
                      · rw [evaluateHOLFiniteState_return]
                        have hi_dec : (decClockHOLFinite st).locals.lookup (ofString "i") =
                            some (.val (.word iw)) := hi_lk
                        simp [evalHOLExact, lookupKvarHOLExact, hi_dec, shapeOfHOLExact,
                          sizeOfShapeWithContextHOL]
                        intro h _
                        exact ⟨iw, h.symm, hlt⟩
                    · simp
                | _ => simp at hret
          · simp [hlt] at hret
        · have hcond : evalHOLFinite st (h := fun x => Classical.propDecidable (st.memaddrs x))
              (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) = none := by
            rw [evalHOLFinite_eq_toExact]
            simp [evalHOLExact, hi_lk]
          rw [hcond] at hret
          simp at hret
        · have hcond : evalHOLFinite st (h := fun x => Classical.propDecidable (st.memaddrs x))
              (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) = none := by
            rw [evalHOLFinite_eq_toExact]
            simp [evalHOLExact, hi_lk]
          rw [hcond] at hret
          simp at hret

/-- `common_prefix_length` (AST line 9903): returns at most `min(al, bl)` (value contract). -/
theorem rv_common_prefix_length :
    RetLe (fun s => min (locN s "al") (locN s "bl")) (ofString "common_prefix_length") := by
  refine ⟨_, (sourceFunctionEntry Guest.Software.guestFn_common_prefix_length).2.2.1, _,
    lookup_common_prefix_length, ?_⟩
  intro F state hcode _ _ _ v hv
  rcases hpair : evaluateHOLFiniteState state
      (sourceFunctionEntry Guest.Software.guestFn_common_prefix_length).2.2.1 with ⟨res, post⟩
  rw [hpair] at hv
  dsimp only at hv
  subst hv
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_common_prefix_length,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    List.map] at hpair
  obtain ⟨vs, bbody, blocals, brs, nv, bpost, inner, hargs, hlk, hb, hdec⟩ :=
    decCall_returned_inv_cpl hpair
  rw [evalListHOLFinite_eq_toExact] at hargs
  rcases hal : state.locals.lookup (ofString "al") with _ | alv
  · simp [evalListHOLExact, evalHOLExact, hal] at hargs
  · rcases hbl : state.locals.lookup (ofString "bl") with _ | blv
    · simp [evalListHOLExact, evalHOLExact, hal, hbl] at hargs
    · have hvs : vs = [alv, blv] := by
        simp [evalListHOLExact, evalHOLExact, hal, hbl] at hargs
        exact hargs.symm
      subst hvs
      obtain ⟨rfl, rfl, hsh1, hsh2⟩ := two_arg_lookup_inv originalRuntimeCode.lookup
        (ofString "min") (ofString "a") (ofString "b") .one .one .one
        (sourceFunctionEntry Guest.Software.guestFn_min).2.2.1 alv blv
        (by decide) lookup_min (by rw [hcode] at hlk; exact hlk)
      rcases alv with ⟨⟨alw⟩⟩ | _ | _
      · rcases blv with ⟨⟨blw⟩⟩ | _ | _
        · have hcal_a : locN (callEntryStateHOLFinite state
              ((HolFiniteMapExact.empty.update (ofString "a", .val (.word alw))).update
                (ofString "b", .val (.word blw)))) "a" = alw.toNat := by
            simp [locN, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "b" ≠ ofString "a" by decide]
          have hcal_b : locN (callEntryStateHOLFinite state
              ((HolFiniteMapExact.empty.update (ofString "a", .val (.word alw))).update
                (ofString "b", .val (.word blw)))) "b" = blw.toNat := by
            simp [locN, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          obtain ⟨nw, rfl, hnw_le⟩ := min_body_ret _ nv (by rw [hb])
          rw [hcal_a, hcal_b] at hnw_le
          have hl_al : locN state "al" = alw.toNat := by simp [locN, hal]
          have hl_bl : locN state "bl" = blw.toNat := by simp [locN, hbl]
          let s1 := setVarHOLFinite (ofString "n") (.val (.word nw))
            {bpost with locals := state.locals}
          rw [evaluateHOLFiniteState_dec_total] at hdec
          simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true] at hdec
          let s1i := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s1
          have hs1i_n : s1i.locals.lookup (ofString "n") = some (.val (.word nw)) := by
            simp [s1i, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "i" ≠ ofString "n" by decide]
          let wbody : ProgHOL 64 :=
            .seq
              (.ite (.cmp .notEqual
                  (.loadByte (.op .add [.var .local (ofString "a"), .var .local (ofString "i")]))
                  (.loadByte (.op .add [.var .local (ofString "b"), .var .local (ofString "i")])))
                (.return (.var .local (ofString "i")))
                .skip)
              (.assign .local (ofString "i")
                (.op .add [.var .local (ofString "i"), .const 1#64]))
          let wprog : ProgHOL 64 :=
            .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) wbody
          have hout := cpl_while_outcome s1i.clock s1i nw hs1i_n (le_refl _)
          dsimp only at hout
          have hseq : (evaluateHOLFiniteState s1i
              (.seq wprog (.return (.var .local (ofString "n"))))).1 =
              some (.returned v) := (Prod.mk.inj hdec).1
          rw [evaluateHOLFiniteState_seq_line780] at hseq
          rcases hwh : evaluateHOLFiniteState s1i wprog with ⟨rw, sw⟩
          have hwh' : evaluateHOLFiniteState s1i
              (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) wbody) =
              (rw, sw) := hwh
          rw [hwh] at hseq
          rw [hwh'] at hout
          cases rw with
          | none =>
            dsimp only at hseq hout
            have hsw_n : sw.locals.lookup (ofString "n") = some (.val (.word nw)) := hout.1 rfl
            rw [evaluateHOLFiniteState_return] at hseq
            simp [evalHOLExact, lookupKvarHOLExact, hsw_n, shapeOfHOLExact,
              sizeOfShapeWithContextHOL] at hseq
            refine ⟨nw, hseq.symm, ?_⟩
            dsimp only
            rw [hl_al, hl_bl]
            exact hnw_le
          | some rw' =>
            cases rw' with
            | returned rv' =>
              dsimp only at hseq hout
              simp only [Option.some.injEq, PanSemResultExact.returned.injEq] at hseq
              subst hseq
              obtain ⟨iw, rfl, hiw_lt⟩ := hout.2 rv' rfl
              refine ⟨iw, rfl, ?_⟩
              dsimp only
              rw [hl_al, hl_bl]
              omega
            | _ => simp at hseq
        · simp [shapeOfHOLExact, shapeEqHOL] at hsh2
        · simp [shapeOfHOLExact, shapeEqHOL] at hsh2
      · simp [shapeOfHOLExact, shapeEqHOL] at hsh1
      · simp [shapeOfHOLExact, shapeEqHOL] at hsh1

end InitECandidate.Solver.Wave8Contracts.M27
