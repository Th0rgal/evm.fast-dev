import InitECandidate.Solver.Wave8GuestInv.R16Shards.NibblesConcatHelper

/-! `nf__collapse_branch`: `_collapse_branch(node)` preserves typed node heaps
(`NodeFn ["node"]` under `NodeKind s Nd "node" 3`). -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.nameCheck false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R14Shards

private theorem signedLess_16 (wi : BitVec 64) (hlt : wi.toNat < 16) :
    Compiler.Encoders.Asm.holAsmSignedLess wi (BitVec.ofNat 64 16) = true := by
  unfold Compiler.Encoders.Asm.holAsmSignedLess
  have h263 : (2 ^ 63 : Nat) = 9223372036854775808 := by decide
  have h1 : wi.toNat < 2 ^ 63 := by omega
  have h16 : (BitVec.ofNat 64 16).toNat = 16 := rfl
  have h16_lt : 16 < 2 ^ 63 := by decide
  simp only [show 64 - 1 = 63 from rfl, h16, if_pos h1, if_pos h16_lt, decide_eq_true_eq]
  exact hlt

private def cbLoopBody : ProgHOL 64 :=
  .seq
    (.ite (.cmp .notEqual
        (.load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 32),
          .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]]))
        (.const (BitVec.ofNat 64 0)))
      (.seq
        (.assign .local (ofString "count") (.op .add [.var .local (ofString "count"), .const (BitVec.ofNat 64 1)]))
        (.assign .local (ofString "idx") (.var .local (ofString "i"))))
      .skip)
    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)]))

private def cbLoop : ProgHOL 64 :=
  .while (.cmp .less (.var .local (ofString "i")) (.const (BitVec.ofNat 64 16))) cbLoopBody

private def noResumesProg : ProgHOL 64 → Bool
  | .dec _ _ _ b => noResumesProg b
  | .seq a b => noResumesProg a && noResumesProg b
  | .ite _ a b => noResumesProg a && noResumesProg b
  | .while _ b => noResumesProg b
  | .assign _ _ _ | .store _ _ | .storeByte _ _ => true
  | .skip | .break | .continue | .annot _ _ => true
  | _ => false

private theorem evaluate_noResumesProg {F : Type} (p : ProgHOL 64) (hp : noResumesProg p = true)
    (s : PanSemStateFiniteExact 64 F) (r : PanSemResultExact 64) :
    (evaluateHOLFiniteState s p).1 = some r → ¬ Resumes (some r) := by
  cases shape : p with
  | skip => intro hr; rw [evaluateHOLFiniteState_skip] at hr; simp at hr
  | «break» =>
    intro hr; rw [evaluateHOLFiniteState_break] at hr; injection hr with h; subst h
    rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h
  | «continue» =>
    intro hr; rw [evaluateHOLFiniteState_continue] at hr; injection hr with h; subst h
    rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h
  | annot _ _ => intro hr; rw [evaluateHOLFiniteState_annot] at hr; simp at hr
  | assign k x e =>
    intro hr
    rcases hev : evaluateHOLFiniteState s (.assign k x e) with ⟨ro, t_out⟩
    rw [hev] at hr; dsimp only at hr; subst hr
    exact assign_res_not_resumes hev
  | store d e =>
    intro hr
    rcases hev : evaluateHOLFiniteState s (.store d e) with ⟨ro, t_out⟩
    rw [hev] at hr; dsimp only at hr; subst hr
    exact store_res_not_resumes hev
  | storeByte d e =>
    intro hr
    rcases hev : evaluateHOLFiniteState s (.storeByte d e) with ⟨ro, t_out⟩
    rw [hev] at hr; dsimp only at hr; subst hr
    exact storeByte_res_not_resumes hev
  | dec x sh init b =>
    intro hr
    have hb : noResumesProg b = true := by simpa [shape, noResumesProg] using hp
    rw [evaluateHOLFiniteState_dec_total] at hr
    dsimp only at hr
    split at hr
    · injection hr with h; subst h; exact not_resumes_error
    · split at hr
      · exact evaluate_noResumesProg b hb _ r hr
      · injection hr with h; subst h; exact not_resumes_error
  | seq a b =>
    intro hr
    have hab : noResumesProg a = true ∧ noResumesProg b = true := by
      simpa [shape, noResumesProg, Bool.and_eq_true] using hp
    have rem := evaluateHOLFiniteState_clock_le s a
    rw [evaluateHOLFiniteState_seq_line780] at hr
    rcases hra : evaluateHOLFiniteState s a with ⟨ra, m⟩
    rw [hra] at hr rem
    have mclk : m.clock ≤ s.clock := rem
    cases ra with
    | none => exact evaluate_noResumesProg b hab.2 m r hr
    | some ra' =>
      dsimp only at hr; injection hr with h; subst h
      exact evaluate_noResumesProg a hab.1 s ra' (congrArg Prod.fst hra)
  | ite _ a b =>
    intro hr
    have hab : noResumesProg a = true ∧ noResumesProg b = true := by
      simpa [shape, noResumesProg, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite] at hr
    split at hr
    · split at hr
      · exact evaluate_noResumesProg b hab.2 s r hr
      · exact evaluate_noResumesProg a hab.1 s r hr
    · injection hr with h; subst h; exact not_resumes_error
  | «while» cond body =>
    intro hr
    have hb : noResumesProg body = true := by simpa [shape, noResumesProg] using hp
    rw [evaluateHOLFiniteState_while_total] at hr
    split at hr
    · split at hr
      · split at hr
        · injection hr with h; subst h
          rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h
        · have dec_lt : (decClockHOLFinite s).clock < s.clock := by
            simp only [decClockHOLFinite]; omega
          dsimp only at hr
          rw [fixClockHOLFinite_evaluateState] at hr
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at hr rem
          have smaller : mid.clock < s.clock := by
            change mid.clock ≤ s.clock - 1 at rem; omega
          cases r1 with
          | none =>
            exact evaluate_noResumesProg (.while cond body) (by simpa [noResumesProg] using hb) mid r hr
          | some r1' =>
            cases r1' with
            | «continue» =>
              exact evaluate_noResumesProg (.while cond body) (by simpa [noResumesProg] using hb) mid r hr
            | «break» => simp at hr
            | _ =>
              dsimp only at hr; injection hr with h; subst h
              exact evaluate_noResumesProg body hb (decClockHOLFinite s) _ (congrArg Prod.fst hbr)
      · simp at hr
    · injection hr with h; subst h; exact not_resumes_error
  | _ => simp [shape, noResumesProg] at hp
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals
    subst shape
    simp_wf
    first
      | exact Prod.Lex.left _ _ dec_lt
      | exact Prod.Lex.left _ _ smaller
      | exact Prod.Lex.right _ (by omega)
      | (rcases Nat.lt_or_eq_of_le mclk with h | h
         · exact Prod.Lex.left _ _ h
         · rw [h]; exact Prod.Lex.right _ (by omega))

private def neverNoneProg : ProgHOL 64 → Bool
  | .call none _ _ => true
  | .dec _ _ _ b => neverNoneProg b
  | .decCall _ _ _ _ b => neverNoneProg b
  | .seq _ b => neverNoneProg b
  | _ => false

private theorem evaluate_neverNoneProg {F : Type} (p : ProgHOL 64) (hp : neverNoneProg p = true)
    (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s p).1 ≠ none := by
  cases shape : p with
  | call ret fname args =>
    cases ret with
    | none => exact call_none_ne_none s fname args
    | some _ => simp [shape, neverNoneProg] at hp
  | dec x sh init b =>
    have hb : neverNoneProg b = true := by simpa [shape, neverNoneProg] using hp
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · split
      · exact evaluate_neverNoneProg b hb _
      · simp
  | decCall x sh fn args b =>
    have hb : neverNoneProg b = true := by simpa [shape, neverNoneProg] using hp
    rw [evaluateHOLFiniteState_decCall_total]
    split
    · simp
    · split
      · simp
      · split
        · simp
        · dsimp only
          split
          · simp
          · simp
          · simp
          · split
            · exact evaluate_neverNoneProg b hb _
            · simp
          · simp
  | seq a b =>
    have hb : neverNoneProg b = true := by simpa [shape, neverNoneProg] using hp
    rw [evaluateHOLFiniteState_seq_line780]
    rcases evaluateHOLFiniteState s a with ⟨ra, sa⟩
    cases ra with
    | none => exact evaluate_neverNoneProg b hb sa
    | some _ => simp
  | _ => simp [shape, neverNoneProg] at hp
termination_by sizeOf p

private theorem nodeStep_of_locFrame {F : Type}
    {s t post : PanSemStateFiniteExact 64 F} {Nd Nd' : List Nat}
    (hfr : SoloHtabSet.LocFrame s t) (hst : NodeStep t post Nd Nd') :
    NodeStep s post Nd Nd' := by
  unfold SoloHtabSet.LocFrame at hfr
  rw [hfr] at hst
  exact NodeStep.from_locals_clock hst

/-- Invariant of the 16-slot counting loop in `_collapse_branch`:
- `SoloHtabSet.LocFrame s0 st` (only `locals` and `clock` change);
- `wi ≤ 16`, `widx < 16`;
- if `0 < wcount`, then `memW s0 (wnode + 32 + 8 * widx) ≠ 0`! -/
private theorem cb_loop_spec {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (wnode : BitVec 64)
    (hsz_nd : ∀ i < 16,
      wnode + BitVec.ofNat 64 32 + BitVec.ofNat 64 i * BitVec.ofNat 64 8 =
        BitVec.ofNat 64 (wnode.toNat + 32 + 8 * i) ∧
      WordAt s0 (wnode.toNat + 32 + 8 * i))
    (clk : Nat) (st mid : PanSemStateFiniteExact 64 F) (wcount widx wi : BitVec 64)
    (hclk : st.clock ≤ clk)
    (hfr : SoloHtabSet.LocFrame s0 st)
    (hnd : st.locals.lookup (ofString "node") = some (.val (.word wnode)))
    (hcnt : st.locals.lookup (ofString "count") = some (.val (.word wcount)))
    (hidx : st.locals.lookup (ofString "idx") = some (.val (.word widx)))
    (hi : st.locals.lookup (ofString "i") = some (.val (.word wi)))
    (hwi_le : wi.toNat ≤ 16)
    (hwcnt_le : wcount.toNat ≤ wi.toNat)
    (hwidx_lt : widx.toNat < 16)
    (hcnt_pos : 0 < wcount.toNat → memW s0 (wnode.toNat + 32 + 8 * widx.toNat) ≠ 0)
    (hrun : evaluateHOLFiniteState st cbLoop = (none, mid)) :
    ∃ wcount' widx' : BitVec 64,
      SoloHtabSet.LocFrame s0 mid ∧
      mid.locals.lookup (ofString "node") = some (.val (.word wnode)) ∧
      mid.locals.lookup (ofString "count") = some (.val (.word wcount')) ∧
      mid.locals.lookup (ofString "idx") = some (.val (.word widx')) ∧
      widx'.toNat < 16 ∧
      (0 < wcount'.toNat → memW s0 (wnode.toNat + 32 + 8 * widx'.toNat) ≠ 0) := by
  induction clk generalizing st wcount widx wi with
  | zero =>
    dsimp only [cbLoop] at hrun
    rw [evaluateHOLFiniteState_while_total] at hrun
    have hclk0 : st.clock = 0 := by omega
    by_cases hlt16 : wi.toNat < 16
    · have hc_ev : evalHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
          (.cmp .less (.var .local (ofString "i")) (.const (BitVec.ofNat 64 16))) =
          some (.val (.word 1)) := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, hi, Compiler.Encoders.Asm.wordCmpHOL, signedLess_16 wi hlt16]
      rw [hc_ev] at hrun; dsimp only at hrun
      have h1_ne0 : (1 : BitVec 64) ≠ 0 := by decide
      rw [if_pos h1_ne0, if_pos hclk0] at hrun; simp at hrun
    · have hwi16 : wi.toNat = 16 := by omega
      have hwi_eq : wi = 16 := BitVec.eq_of_toNat_eq hwi16
      subst hwi_eq
      have hc_ev : evalHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
          (.cmp .less (.var .local (ofString "i")) (.const (BitVec.ofNat 64 16))) =
          some (.val (.word 0)) := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, hi, Compiler.Encoders.Asm.wordCmpHOL, Compiler.Encoders.Asm.holAsmSignedLess]
      rw [hc_ev] at hrun; simp only [↓reduceIte] at hrun
      injection hrun with _ hmid; subst hmid
      exact ⟨wcount, widx, hfr, hnd, hcnt, hidx, hwidx_lt, hcnt_pos⟩
  | succ clk ih =>
    dsimp only [cbLoop] at hrun
    rw [evaluateHOLFiniteState_while_total] at hrun
    by_cases hlt16 : wi.toNat < 16
    · have hc_ev : evalHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
          (.cmp .less (.var .local (ofString "i")) (.const (BitVec.ofNat 64 16))) =
          some (.val (.word 1)) := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, hi, Compiler.Encoders.Asm.wordCmpHOL, signedLess_16 wi hlt16]
      rw [hc_ev] at hrun; dsimp only at hrun
      have h1_ne0 : (1 : BitVec 64) ≠ 0 := by decide
      have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
      rw [if_pos h1_ne0] at hrun
      by_cases hclk0 : st.clock = 0
      · rw [if_pos hclk0] at hrun; simp at hrun
      · rw [if_neg hclk0, fixClockHOLFinite_evaluateState] at hrun
        let sd := decClockHOLFinite st
        have hfr_sd : SoloHtabSet.LocFrame s0 sd := by
          unfold SoloHtabSet.LocFrame at hfr ⊢; dsimp only [sd, decClockHOLFinite]; rw [hfr]
        have hnd_sd : sd.locals.lookup (ofString "node") = some (.val (.word wnode)) := hnd
        have hcnt_sd : sd.locals.lookup (ofString "count") = some (.val (.word wcount)) := hcnt
        have hidx_sd : sd.locals.lookup (ofString "idx") = some (.val (.word widx)) := hidx
        have hi_sd : sd.locals.lookup (ofString "i") = some (.val (.word wi)) := hi
        have hsd_mem : sd.memory = s0.memory := by unfold SoloHtabSet.LocFrame at hfr_sd; rw [hfr_sd]
        have hsd_ma : sd.memaddrs = s0.memaddrs := by unfold SoloHtabSet.LocFrame at hfr_sd; rw [hfr_sd]
        obtain ⟨hslot_bv, wch_i, hdom_i, hmem_i⟩ := hsz_nd wi.toNat hlt16
        have hwi_bv : BitVec.ofNat 64 wi.toNat = wi := by simp
        rw [hwi_bv] at hslot_bv
        have hmw_i : wch_i.toNat = memW s0 (wnode.toNat + 32 + 8 * wi.toNat) := by
          unfold memW; rw [hmem_i]
        have hadd_ev : @evalHOLExact 64 F _ sd.toExact (fun a => Classical.propDecidable (sd.memaddrs a))
            (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 32),
              .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]]) =
            some (.val (.word (BitVec.ofNat 64 (wnode.toNat + 32 + 8 * wi.toNat)))) := by
          have hadd0 : ∀ u : BitVec 64, u + (0 : BitVec 64) = u := BitVec.add_zero
          simp only [evalHOLExact, evalListHOLExact, hnd_sd, hi_sd,
            valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, List.all, List.map, Option.map,
            Bool.and_self, ↓reduceIte, List.foldr, hadd0]
          congr 3
          rw [← BitVec.add_assoc, hslot_bv]
        have hld_ev : @evalHOLExact 64 F _ sd.toExact (fun a => Classical.propDecidable (sd.memaddrs a))
            (.load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 32),
              .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]])) =
            some (.val (.word wch_i)) := by
          have hdom_sd : sd.memaddrs (BitVec.ofNat 64 (wnode.toNat + 32 + 8 * wi.toNat)) := by
            rw [hsd_ma]; exact hdom_i
          have hmem_sd : sd.memory (BitVec.ofNat 64 (wnode.toNat + 32 + 8 * wi.toNat)) = .word wch_i := by
            rw [hsd_mem]; exact hmem_i
          conv_lhs => unfold evalHOLExact
          rw [hadd_ev]
          simp [isWfShapeExactHOL, memLoadHOLExact, hdom_sd, hmem_sd]
        have hcmp_ev : @evalHOLExact 64 F _ sd.toExact (fun a => Classical.propDecidable (sd.memaddrs a))
            (.cmp .notEqual
              (.load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 32),
                .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]]))
              (.const (BitVec.ofNat 64 0))) =
            some (.val (.word (if wch_i ≠ 0 then 1 else 0))) := by
          conv_lhs => unfold evalHOLExact
          rw [hld_ev]
          have hc0 : @evalHOLExact 64 F _ sd.toExact (fun a => Classical.propDecidable (sd.memaddrs a))
              (.const (BitVec.ofNat 64 0)) = some (.val (.word 0)) := rfl
          rw [hc0]
          simp [Compiler.Encoders.Asm.wordCmpHOL]
        by_cases hch_nz : wch_i ≠ 0
        · set s_body := setVarHOLFinite (ofString "i") (.val (.word (wi + 1)))
            (setVarHOLFinite (ofString "idx") (.val (.word wi))
              (setVarHOLFinite (ofString "count") (.val (.word (wcount + 1))) sd))
          have hbody_ev : evaluateHOLFiniteState sd cbLoopBody = (none, s_body) := by
            dsimp only [cbLoopBody]
            rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hcmp_ev, if_pos hch_nz]
            dsimp only
            rw [if_neg h10, evaluateHOLFiniteState_seq_line780]
            have ha1 : evaluateHOLFiniteState sd
                (.assign .local (ofString "count") (.op .add [.var .local (ofString "count"), .const (BitVec.ofNat 64 1)])) =
                (none, setVarHOLFinite (ofString "count") (.val (.word (wcount + 1))) sd) := by
              have hc_sd : sd.locals.lookup (ofString "count") = some (.val (.word wcount)) := hcnt
              simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hc_sd,
                valueIsWord, valueWord, wordOpHOL, wordOp, lookupKvarHOLExact, isValidValueHOLExact,
                setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
            rw [ha1]; dsimp only
            set sd1 := setVarHOLFinite (ofString "count") (.val (.word (wcount + 1))) sd
            have ha2 : evaluateHOLFiniteState sd1
                (.assign .local (ofString "idx") (.var .local (ofString "i"))) =
                (none, setVarHOLFinite (ofString "idx") (.val (.word wi)) sd1) := by
              have hi_sd1 : sd1.locals.lookup (ofString "i") = some (.val (.word wi)) := by
                simp [sd1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hi_sd,
                  show ofString "count" ≠ ofString "i" by decide]
              have hidx_sd1 : sd1.locals.lookup (ofString "idx") = some (.val (.word widx)) := by
                simp [sd1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hidx_sd,
                  show ofString "count" ≠ ofString "idx" by decide]
              simp [evaluateHOLFiniteState_assign, evalHOLExact, hi_sd1, hidx_sd1,
                lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
            rw [ha2]; dsimp only
            set sd2 := setVarHOLFinite (ofString "idx") (.val (.word wi)) sd1
            have hi_sd2 : sd2.locals.lookup (ofString "i") = some (.val (.word wi)) := by
              simp [sd2, sd1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hi_sd,
                show ofString "idx" ≠ ofString "i" by decide, show ofString "count" ≠ ofString "i" by decide]
            have ha3 : evaluateHOLFiniteState sd2
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])) =
                (none, setVarHOLFinite (ofString "i") (.val (.word (wi + 1))) sd2) := by
              simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hi_sd2,
                valueIsWord, valueWord, wordOpHOL, wordOp, lookupKvarHOLExact, isValidValueHOLExact,
                setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
            exact ha3
          rw [hbody_ev] at hrun; dsimp only at hrun
          have hwi1_nat : (wi + 1).toNat = wi.toNat + 1 :=
            BitVec.toNat_add_of_lt (by change wi.toNat + 1 < 2 ^ 64; omega)
          have hwcnt1_nat : (wcount + 1).toNat = wcount.toNat + 1 :=
            BitVec.toNat_add_of_lt (by change wcount.toNat + 1 < 2 ^ 64; omega)
          have hmw_nz : memW s0 (wnode.toNat + 32 + 8 * wi.toNat) ≠ 0 := by
            rw [← hmw_i]; intro hz; exact hch_nz (BitVec.eq_of_toNat_eq hz)
          exact ih s_body (wcount + 1) wi (wi + 1)
            (by change st.clock - 1 ≤ clk; omega)
            (hfr_sd.locals _)
            (by simp [s_body, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnd_sd,
                  show ofString "i" ≠ ofString "node" by decide,
                  show ofString "idx" ≠ ofString "node" by decide,
                  show ofString "count" ≠ ofString "node" by decide])
            (by simp [s_body, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "i" ≠ ofString "count" by decide,
                  show ofString "idx" ≠ ofString "count" by decide])
            (by simp [s_body, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "i" ≠ ofString "idx" by decide])
            (by simp [s_body, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
            (by omega) (by omega) hlt16 (fun _ => hmw_nz) hrun
        · set s_body := setVarHOLFinite (ofString "i") (.val (.word (wi + 1))) sd
          have hbody_ev : evaluateHOLFiniteState sd cbLoopBody = (none, s_body) := by
            dsimp only [cbLoopBody]
            rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hcmp_ev, if_neg hch_nz]
            simp only [↓reduceIte, evaluateHOLFiniteState_skip]
            simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hi_sd,
              valueIsWord, valueWord, wordOpHOL, wordOp, lookupKvarHOLExact, isValidValueHOLExact,
              setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL, s_body]
          rw [hbody_ev] at hrun; dsimp only at hrun
          have hwi1_nat : (wi + 1).toNat = wi.toNat + 1 :=
            BitVec.toNat_add_of_lt (by change wi.toNat + 1 < 2 ^ 64; omega)
          exact ih s_body wcount widx (wi + 1)
            (by change st.clock - 1 ≤ clk; omega)
            (hfr_sd.locals _)
            (by simp [s_body, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnd_sd,
                  show ofString "i" ≠ ofString "node" by decide])
            (by simp [s_body, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hcnt_sd,
                  show ofString "i" ≠ ofString "count" by decide])
            (by simp [s_body, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hidx_sd,
                  show ofString "i" ≠ ofString "idx" by decide])
            (by simp [s_body, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
            (by omega) (by omega) hwidx_lt hcnt_pos hrun
    · have hwi16 : wi.toNat = 16 := by omega
      have hwi_eq : wi = 16 := BitVec.eq_of_toNat_eq hwi16
      subst hwi_eq
      have hc_ev : evalHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
          (.cmp .less (.var .local (ofString "i")) (.const (BitVec.ofNat 64 16))) =
          some (.val (.word 0)) := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, hi, Compiler.Encoders.Asm.wordCmpHOL, Compiler.Encoders.Asm.holAsmSignedLess]
      rw [hc_ev] at hrun; simp only [↓reduceIte] at hrun
      injection hrun with _ hmid; subst hmid
      exact ⟨wcount, widx, hfr, hnd, hcnt, hidx, hwidx_lt, hcnt_pos⟩

/-- `_collapse_branch` (AST line 10674): typed nodes in, typed nodes out (MPT tier);
requirement: `NodeKind s Nd "node" 3`. -/
theorem «nf__collapse_branch» :
    NodeFn ["node"]
    (fun s Nd =>
      NodeKind s Nd "node" 3)
    (ofString "_collapse_branch") := by
  refine ⟨_, _, _, lookup__collapse_branch, ?_⟩
  intro F s hcode hP ⟨callVals, hcallL⟩ _hnt hres
  have hAR : ArenaReady s := hP.1
  obtain ⟨Nd_wit, hNd_wit, _hroots_wit, hnk_wit⟩ := hP.2
  obtain ⟨wnode, hlk_node, hloc_node⟩ := lookup_param_word lookup__collapse_branch hcallL
    [] "node" [] rfl (by decide)
  set res := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__collapse_branch)).1
  set post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__collapse_branch)).2
  suffices hmain : ∀ Nd, NodeHeap s Nd → NodeKind s Nd "node" 3 →
      ∃ Nd', NodeStep s post Nd Nd' ∧
        ∀ v, res = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧ RootIn Nd' w.toNat by
    obtain ⟨Nd0', hns0, _⟩ := hmain Nd_wit hNd_wit hnk_wit
    refine ⟨hns0.arena, hns0.hp_le, hns0.sp_le, ?_⟩
    intro Nd hNd _hroots hnk
    obtain ⟨Nd', hns, hret⟩ := hmain Nd hNd hnk
    exact ⟨Nd', hns.heap, hns.sub, hns.kinds, hns.fresh, hns.frame, hns.globals, hret⟩
  intro Nd hNd hnk
  have hnode_in : wnode.toNat ∈ Nd := by rw [← hloc_node s rfl]; exact hnk.1
  have hnode_k3 : memW s wnode.toNat = 3 := by rw [← hloc_node s rfl]; exact hnk.2
  have hp_node := hNd.1 wnode.toNat hnode_in
  have hsz_nd176 : nodeSize (memW s wnode.toNat) = 176 := by simp [nodeSize, hnode_k3]
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hnd_ins := hp_node.2.2.1
  have hnd_add : ∀ k : Nat, k < 176 →
      wnode + BitVec.ofNat 64 k = BitVec.ofNat 64 (wnode.toNat + k) ∧
      (wnode + BitVec.ofNat 64 k).toNat = wnode.toNat + k := by
    intro k hk
    have hlt : wnode.toNat + k < 2 ^ 64 := by
      dsimp [Inside, nodeIvl] at hnd_ins; rw [hsz_nd176] at hnd_ins; omega
    have heq : wnode + BitVec.ofNat 64 k = BitVec.ofNat 64 (wnode.toNat + k) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    exact ⟨heq, by rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]⟩
  have hsz_nd : ∀ i < 16,
      wnode + BitVec.ofNat 64 32 + BitVec.ofNat 64 i * BitVec.ofNat 64 8 =
        BitVec.ofNat 64 (wnode.toNat + 32 + 8 * i) ∧
      WordAt s (wnode.toNat + 32 + 8 * i) := by
    intro i hi
    have hlt : wnode.toNat + 32 + 8 * i < 2 ^ 64 := by
      dsimp [Inside, nodeIvl] at hnd_ins; rw [hsz_nd176] at hnd_ins; omega
    constructor
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
      omega
    · have hwa := hp_node.2.2.2.1.2.2 (4 + i) (by dsimp [nodeIvl]; rw [hsz_nd176]; omega)
      dsimp [nodeIvl] at hwa
      have hmul : wnode.toNat + 8 * (4 + i) = wnode.toNat + 32 + 8 * i := by omega
      rwa [hmul] at hwa
  have hload_nd_off : ∀ (st : PanSemStateFiniteExact 64 F) (k : Nat),
      SoloHtabSet.LocFrame s st →
      st.locals.lookup (ofString "node") = some (.val (.word wnode)) →
      k < 176 → k % 8 = 0 →
      @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 k)])) =
        some (.val (.word (BitVec.ofNat 64 (memW s (wnode.toNat + k))))) := by
    intro st k hfr hnd_lk hk hk8
    have hst_mem : st.memory = s.memory := by unfold SoloHtabSet.LocFrame at hfr; rw [hfr]
    have hst_ma : st.memaddrs = s.memaddrs := by unfold SoloHtabSet.LocFrame at hfr; rw [hfr]
    obtain ⟨w_at, hdom_at, hm_at⟩ := hp_node.2.2.2.1.2.2 (k / 8)
      (by dsimp [nodeIvl]; rw [hsz_nd176]; omega)
    dsimp [nodeIvl] at hdom_at hm_at
    have hmul : wnode.toNat + 8 * (k / 8) = wnode.toNat + k := by omega
    rw [hmul] at hdom_at hm_at
    have hdom_st : st.memaddrs (wnode + BitVec.ofNat 64 k) := by
      rw [hst_ma, (hnd_add k hk).1]; exact hdom_at
    have hm_st : st.memory (wnode + BitVec.ofNat 64 k) = .word w_at := by
      rw [hst_mem, (hnd_add k hk).1]; exact hm_at
    have hmw_eq : BitVec.ofNat 64 (memW s (wnode.toNat + k)) = w_at := by
      unfold memW; rw [hm_at]; simp
    simp [evalHOLExact, evalListHOLExact, hnd_lk, valueIsWord, valueWord, wordOpHOL, wordOp,
      isWfShapeExactHOL, memLoadHOLExact, hdom_st, hm_st, hmw_eq]
  set singleSlotBranch : ProgHOL 64 :=
    .dec (ofString "child") .one
      (.load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 32),
        .panop .mul [.var .local (ofString "idx"), .const (BitVec.ofNat 64 8)]]))
      (.dec (ofString "ck") .one
        (.load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 0)]))
        (.seq
          (.ite (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 0)))
            (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 2)])
            .skip)
          (.decCall (ofString "nib") .one (ofString "alloc") [.const (BitVec.ofNat 64 8)]
            (.seq
              (.storeByte (.var .local (ofString "nib")) (.var .local (ofString "idx")))
              (.seq
                (.ite (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 3)))
                  (.call none (ofString "node_new_ext")
                    [.var .local (ofString "nib"), .const (BitVec.ofNat 64 1), .var .local (ofString "child")])
                  .skip)
                (.decCall (ofString "cat") .one (ofString "nibbles_concat")
                  [.var .local (ofString "nib"), .const (BitVec.ofNat 64 1),
                   .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 32)]),
                   .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 40)])]
                  (.seq
                    (.ite (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 1)))
                      (.call none (ofString "node_new_leaf")
                        [.var .local (ofString "cat"),
                         .op .add [.const (BitVec.ofNat 64 1),
                           .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 40)])],
                         .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 48)]),
                         .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 56)])])
                      .skip)
                    (.call none (ofString "node_new_ext")
                      [.var .local (ofString "cat"),
                       .op .add [.const (BitVec.ofNat 64 1),
                         .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 40)])],
                       .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 48)])]))))))))
  set afterLoop : ProgHOL 64 :=
    .dec (ofString "vl") .one
      (.load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 168)]))
      (.seq
        (.ite (.cmp .equal (.var .local (ofString "count")) (.const (BitVec.ofNat 64 0)))
          (.seq
            (.ite (.cmp .equal (.var .local (ofString "vl")) (.const (BitVec.ofNat 64 0)))
              (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 12)])
              .skip)
            (.call none (ofString "node_new_leaf")
              [.var .local (ofString "node"), .const (BitVec.ofNat 64 0),
               .load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 160)]),
               .var .local (ofString "vl")]))
          .skip)
        (.seq
          (.ite (.op .and [
              .cmp .notEqual (.const (BitVec.ofNat 64 0))
                (.cmp .equal (.var .local (ofString "count")) (.const (BitVec.ofNat 64 1))),
              .cmp .notEqual (.const (BitVec.ofNat 64 0))
                (.cmp .equal (.var .local (ofString "vl")) (.const (BitVec.ofNat 64 0)))])
            singleSlotBranch
            .skip)
          (.return (.var .local (ofString "node")))))
  have hbody : sourceFnBody Guest.Software.guestFn__collapse_branch =
      .dec (ofString "count") .one (.const (BitVec.ofNat 64 0))
        (.dec (ofString "idx") .one (.const (BitVec.ofNat 64 0))
          (.dec (ofString "i") .one (.const (BitVec.ofNat 64 0))
            (.seq cbLoop afterLoop))) := rfl
  -- Step 1: peel `dec count := 0; dec idx := 0; dec i := 0`
  set s_c := setVarHOLFinite (ofString "count") (.val (.word 0)) s
  set s_ci := setVarHOLFinite (ofString "idx") (.val (.word 0)) s_c
  set s_init := setVarHOLFinite (ofString "i") (.val (.word 0)) s_ci
  have hdecs : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__collapse_branch)).1 =
      (evaluateHOLFiniteState s_init (.seq cbLoop afterLoop)).1 ∧
      ∃ L_outer, (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__collapse_branch)).2 =
        { (evaluateHOLFiniteState s_init (.seq cbLoop afterLoop)).2 with locals := L_outer } := by
    rw [hbody, evaluateHOLFiniteState_dec_total]
    simp only [evalHOLExact, shapeEqHOL, shapeOfHOLExact, ↓reduceIte]
    rw [evaluateHOLFiniteState_dec_total]
    simp only [evalHOLExact, shapeEqHOL, shapeOfHOLExact, ↓reduceIte]
    rw [evaluateHOLFiniteState_dec_total]
    simp only [evalHOLExact, shapeEqHOL, shapeOfHOLExact, ↓reduceIte]
    exact ⟨rfl, _, rfl⟩
  obtain ⟨hres_eq_init, L_outer, hpost_eq_init⟩ := hdecs
  have hinit_res : Resumes (evaluateHOLFiniteState s_init (.seq cbLoop afterLoop)).1 := by
    rwa [← hres_eq_init]
  -- Step 2: run `cbLoop` via `seq_noResumes_left` and `cb_loop_spec`!
  obtain ⟨mid, hloop_run, hseq_loop⟩ := seq_noResumes_left
    (fun r _ hr => evaluate_noResumesProg cbLoop (by decide) s_init r (congrArg Prod.fst hr))
    hinit_res
  have hfr_init : SoloHtabSet.LocFrame s s_init :=
    (((SoloHtabSet.LocFrame.refl s).locals _).locals _).locals _
  obtain ⟨wcount, widx, hfr_mid, hmid_node, hmid_cnt, hmid_idx, hwidx_lt, hcnt_pos⟩ :=
    cb_loop_spec s wnode hsz_nd s_init.clock s_init mid 0 0 0 le_rfl hfr_init
      (by simp [s_init, s_ci, s_c, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk_node,
            show ofString "i" ≠ ofString "node" by decide,
            show ofString "idx" ≠ ofString "node" by decide,
            show ofString "count" ≠ ofString "node" by decide])
      (by simp [s_init, s_ci, s_c, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "i" ≠ ofString "count" by decide,
            show ofString "idx" ≠ ofString "count" by decide])
      (by simp [s_init, s_ci, s_c, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "i" ≠ ofString "idx" by decide])
      (by simp [s_init, s_ci, s_c, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      (by decide) (by decide) (by decide) (by intro h; simp at h) hloop_run
  have hafter_res : Resumes (evaluateHOLFiniteState mid afterLoop).1 := by
    rwa [hseq_loop] at hinit_res
  -- Step 3: peel `dec vl := load(node + 168)` on `mid`!
  set wvl : BitVec 64 := BitVec.ofNat 64 (memW s (wnode.toNat + 168))
  have hwvl_lt40 : memW s (wnode.toNat + 168) < 2 ^ 40 :=
    hp_node.2.2.2.2.2.2.2.2.2 hnode_k3
  have hwvl_nat : wvl.toNat = memW s (wnode.toNat + 168) := by
    dsimp [wvl]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans hwvl_lt40 (by decide))]
  have hev_vl : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
      (.load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 168)])) =
      some (.val (.word wvl)) :=
    hload_nd_off mid 168 hfr_mid hmid_node (by decide) (by decide)
  set s_vl := setVarHOLFinite (ofString "vl") (.val (.word wvl)) mid
  set vl_body : ProgHOL 64 :=
    .seq
      (.ite (.cmp .equal (.var .local (ofString "count")) (.const (BitVec.ofNat 64 0)))
        (.seq
          (.ite (.cmp .equal (.var .local (ofString "vl")) (.const (BitVec.ofNat 64 0)))
            (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 12)])
            .skip)
          (.call none (ofString "node_new_leaf")
            [.var .local (ofString "node"), .const (BitVec.ofNat 64 0),
             .load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 160)]),
             .var .local (ofString "vl")]))
        .skip)
      (.seq
        (.ite (.op .and [
            .cmp .notEqual (.const (BitVec.ofNat 64 0))
              (.cmp .equal (.var .local (ofString "count")) (.const (BitVec.ofNat 64 1))),
            .cmp .notEqual (.const (BitVec.ofNat 64 0))
              (.cmp .equal (.var .local (ofString "vl")) (.const (BitVec.ofNat 64 0)))])
          singleSlotBranch
          .skip)
        (.return (.var .local (ofString "node"))))
  have hdec_vl : (evaluateHOLFiniteState mid afterLoop).1 = (evaluateHOLFiniteState s_vl vl_body).1 ∧
      ∃ L_vl, (evaluateHOLFiniteState mid afterLoop).2 =
        { (evaluateHOLFiniteState s_vl vl_body).2 with locals := L_vl } := by
    dsimp only [afterLoop]
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    rw [hev_vl]
    simp only [shapeEqHOL, shapeOfHOLExact, ↓reduceIte]
    exact ⟨rfl, _, rfl⟩
  obtain ⟨hvl_res_eq, L_vl, hvl_post_eq⟩ := hdec_vl
  have hsvl_res : Resumes (evaluateHOLFiniteState s_vl vl_body).1 := by
    rwa [← hvl_res_eq]
  have hfr_svl : SoloHtabSet.LocFrame s s_vl := hfr_mid.locals _
  have hsvl_code : s_vl.code = originalRuntimeCode := by
    unfold SoloHtabSet.LocFrame at hfr_svl; rw [hfr_svl]; exact hcode
  have hsvl_AR : ArenaReady s_vl := by
    unfold SoloHtabSet.LocFrame at hfr_svl; rw [hfr_svl]; exact localsFree_arenaReady s _ _ hAR
  have hsvl_Nd : NodeHeap s_vl Nd := by
    unfold SoloHtabSet.LocFrame at hfr_svl; rw [hfr_svl]; exact hNd
  have hsvl_vl : s_vl.locals.lookup (ofString "vl") = some (.val (.word wvl)) := by
    simp [s_vl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hsvl_node : s_vl.locals.lookup (ofString "node") = some (.val (.word wnode)) := by
    simp [s_vl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmid_node,
      show ofString "vl" ≠ ofString "node" by decide]
  have hsvl_cnt : s_vl.locals.lookup (ofString "count") = some (.val (.word wcount)) := by
    simp [s_vl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmid_cnt,
      show ofString "vl" ≠ ofString "count" by decide]
  have hsvl_idx : s_vl.locals.lookup (ofString "idx") = some (.val (.word widx)) := by
    simp [s_vl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmid_idx,
      show ofString "vl" ≠ ofString "idx" by decide]
  -- Helper to lift `NodeStep s_vl` back to `s`/`post`!
  suffices hvl_main : ∃ Nd',
      NodeStep s_vl (evaluateHOLFiniteState s_vl vl_body).2 Nd Nd' ∧
      ∀ v, (evaluateHOLFiniteState s_vl vl_body).1 = some (.returned v) →
        ∃ w : BitVec 64, v = .val (.word w) ∧ RootIn Nd' w.toNat by
    obtain ⟨Nd', hstep_vl, hret_vl⟩ := hvl_main
    refine ⟨Nd', ?_, ?_⟩
    · change NodeStep s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__collapse_branch)).2 Nd Nd'
      rw [hpost_eq_init, hseq_loop, hvl_post_eq]
      exact ((nodeStep_of_locFrame hfr_svl hstep_vl).with_locals_clock _ _).with_locals_clock _ _
    · intro v hv
      change (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__collapse_branch)).1 = _ at hv
      rw [hres_eq_init, hseq_loop, hvl_res_eq] at hv
      exact hret_vl v hv
  -- Step 4: check `count == 0`!
  have hc_cnt0 : @evalHOLExact 64 F _ s_vl.toExact (fun a => Classical.propDecidable (s_vl.memaddrs a))
      (.cmp .equal (.var .local (ofString "count")) (.const (BitVec.ofNat 64 0))) =
      some (.val (.word (if wcount = 0 then 1 else 0))) := by
    simp [evalHOLExact, hsvl_cnt, Compiler.Encoders.Asm.wordCmpHOL]
  by_cases hcnt0 : wcount = 0
  · -- Case 1: `count == 0`!
    have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    have hc_vl0 : @evalHOLExact 64 F _ s_vl.toExact (fun a => Classical.propDecidable (s_vl.memaddrs a))
        (.cmp .equal (.var .local (ofString "vl")) (.const (BitVec.ofNat 64 0))) =
        some (.val (.word (if wvl = 0 then 1 else 0))) := by
      simp [evalHOLExact, hsvl_vl, Compiler.Encoders.Asm.wordCmpHOL]
    by_cases hvl0 : wvl = 0
    · -- Subcase 1a: `count == 0` and `vl == 0` -> `mpt_fail(12)`!
      have hite_vl0 : evaluateHOLFiniteState s_vl
          (.ite (.cmp .equal (.var .local (ofString "vl")) (.const (BitVec.ofNat 64 0)))
            (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 12)])
            .skip) =
          evaluateHOLFiniteState s_vl
            (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 12)]) := by
        rw [evaluateHOLFiniteState_ite, hc_vl0, if_pos hvl0]; simp
      have hfail_nn := mpt_fail_ne_none s_vl hsvl_code (.const (BitVec.ofNat 64 12))
      rcases hfail_out : evaluateHOLFiniteState s_vl
          (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 12)]) with ⟨fr_o, fp_o⟩
      have hfail_out' : evaluateHOLFiniteState s_vl
          (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 12)]) = (fr_o, fp_o) := hfail_out
      rcases fr_o with _ | fr_some
      · exact absurd (congrArg Prod.fst hfail_out') hfail_nn
      · have hvl_eq : evaluateHOLFiniteState s_vl vl_body = (some fr_some, fp_o) := by
          dsimp only [vl_body]
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hc_cnt0, if_pos hcnt0]
          dsimp only
          rw [if_neg h10, evaluateHOLFiniteState_seq_line780, hite_vl0, hfail_out']
        rw [hvl_eq] at hsvl_res
        obtain ⟨eid, ev, hfail_exn, _, hstep_fail⟩ := mpt_fail_call_resumes hsvl_code hsvl_AR hsvl_Nd
          (by rw [hfail_out']; exact hsvl_res)
        rw [hfail_out'] at hfail_exn hstep_fail
        dsimp only at hfail_exn hstep_fail
        injection hfail_exn with hfr_eq; subst hfr_eq
        refine ⟨Nd, ?_, ?_⟩
        · rw [hvl_eq]; exact hstep_fail
        · intro v hv; rw [hvl_eq] at hv; cases hv
    · -- Subcase 1b: `count == 0` and `vl != 0` -> tail call `node_new_leaf(node, 0, load(node + 160), vl)`!
      have hite_vl_skip : evaluateHOLFiniteState s_vl
          (.ite (.cmp .equal (.var .local (ofString "vl")) (.const (BitVec.ofNat 64 0)))
            (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 12)])
            .skip) = (none, s_vl) := by
        rw [evaluateHOLFiniteState_ite, hc_vl0, if_neg hvl0]; simp [evaluateHOLFiniteState_skip]
      set lf0_call : ProgHOL 64 :=
        .call none (ofString "node_new_leaf")
          [.var .local (ofString "node"), .const (BitVec.ofNat 64 0),
           .load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 160)]),
           .var .local (ofString "vl")]
      have hnn_lf0 := call_none_ne_none s_vl (ofString "node_new_leaf")
        [.var .local (ofString "node"), .const (BitVec.ofNat 64 0),
         .load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 160)]),
         .var .local (ofString "vl")]
      have hvl_eq_lf0 : evaluateHOLFiniteState s_vl vl_body = evaluateHOLFiniteState s_vl lf0_call := by
        dsimp only [vl_body]
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hc_cnt0, if_pos hcnt0]
        dsimp only
        rw [if_neg h10, evaluateHOLFiniteState_seq_line780, hite_vl_skip]
        dsimp only
        rcases h_lc : evaluateHOLFiniteState s_vl lf0_call with ⟨lr, lp⟩
        cases lr with
        | none => exact absurd (congrArg Prod.fst h_lc) hnn_lf0
        | some _ => rfl
      rw [hvl_eq_lf0] at hsvl_res ⊢
      set wnd160 : BitVec 64 := BitVec.ofNat 64 (memW s (wnode.toNat + 160))
      have hlf0_args : evalListHOLFinite s_vl (h := fun a => Classical.propDecidable (s_vl.memaddrs a))
          [.var .local (ofString "node"), .const (BitVec.ofNat 64 0),
           .load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 160)]),
           .var .local (ofString "vl")] =
          some [.val (.word wnode), .val (.word 0), .val (.word wnd160), .val (.word wvl)] := by
        rw [evalListHOLFinite_eq_toExact]
        have h160 := hload_nd_off s_vl 160 hfr_svl hsvl_node (by decide) (by decide)
        have h1 : @evalHOLExact 64 F _ s_vl.toExact (fun a => Classical.propDecidable (s_vl.memaddrs a))
            (.var .local (ofString "node")) = some (.val (.word wnode)) := hsvl_node
        have h2 : @evalHOLExact 64 F _ s_vl.toExact (fun a => Classical.propDecidable (s_vl.memaddrs a))
            (.const (BitVec.ofNat 64 0)) = some (.val (.word 0)) := rfl
        have h4 : @evalHOLExact 64 F _ s_vl.toExact (fun a => Classical.propDecidable (s_vl.memaddrs a))
            (.var .local (ofString "vl")) = some (.val (.word wvl)) := hsvl_vl
        dsimp only [evalListHOLExact]
        rw [h1, h2, h160, h4]
      exact tail_call_node_new_leaf s_vl Nd _ _ _ _ wnode 0 wnd160 wvl
        hsvl_code hsvl_AR hsvl_Nd hlf0_args (Or.inl rfl) (by rw [hwvl_nat]; exact hwvl_lt40) hsvl_res
  · -- Case 2: `count != 0`!
    have hite_cnt0_skip : evaluateHOLFiniteState s_vl
        (.ite (.cmp .equal (.var .local (ofString "count")) (.const (BitVec.ofNat 64 0)))
          (.seq
            (.ite (.cmp .equal (.var .local (ofString "vl")) (.const (BitVec.ofNat 64 0)))
              (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 12)])
              .skip)
            (.call none (ofString "node_new_leaf")
              [.var .local (ofString "node"), .const (BitVec.ofNat 64 0),
               .load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 160)]),
               .var .local (ofString "vl")]))
          .skip) = (none, s_vl) := by
      rw [evaluateHOLFiniteState_ite, hc_cnt0, if_neg hcnt0]; simp [evaluateHOLFiniteState_skip]
    set vl_rest : ProgHOL 64 :=
      .seq
        (.ite (.op .and [
            .cmp .notEqual (.const (BitVec.ofNat 64 0))
              (.cmp .equal (.var .local (ofString "count")) (.const (BitVec.ofNat 64 1))),
            .cmp .notEqual (.const (BitVec.ofNat 64 0))
              (.cmp .equal (.var .local (ofString "vl")) (.const (BitVec.ofNat 64 0)))])
          singleSlotBranch
          .skip)
        (.return (.var .local (ofString "node")))
    have hvl_eq_rest : evaluateHOLFiniteState s_vl vl_body = evaluateHOLFiniteState s_vl vl_rest := by
      dsimp only [vl_body]
      rw [evaluateHOLFiniteState_seq_line780, hite_cnt0_skip]
    rw [hvl_eq_rest] at hsvl_res ⊢
    -- Evaluate the boolean conjunction `(count == 1) && (vl == 0)`
    by_cases hcond : wcount = 1 ∧ wvl = 0
    · -- Subcase 2a: `count == 1` and `vl == 0` -> `singleSlotBranch`!
      obtain ⟨hcnt1, hvl0⟩ := hcond
      have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
      have hand_ev : @evalHOLExact 64 F _ s_vl.toExact (fun a => Classical.propDecidable (s_vl.memaddrs a))
          (.op .and [
            .cmp .notEqual (.const (BitVec.ofNat 64 0))
              (.cmp .equal (.var .local (ofString "count")) (.const (BitVec.ofNat 64 1))),
            .cmp .notEqual (.const (BitVec.ofNat 64 0))
              (.cmp .equal (.var .local (ofString "vl")) (.const (BitVec.ofNat 64 0)))]) =
          some (.val (.word 1)) := by
        simp [evalHOLExact, evalListHOLExact, hsvl_cnt, hsvl_vl, hcnt1, hvl0,
          Compiler.Encoders.Asm.wordCmpHOL, valueIsWord, valueWord, wordOpHOL, wordOp,
          List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
      have hss_nn : (evaluateHOLFiniteState s_vl singleSlotBranch).1 ≠ none :=
        evaluate_neverNoneProg singleSlotBranch (by decide) s_vl
      have hrest_eq_ss : evaluateHOLFiniteState s_vl vl_rest =
          evaluateHOLFiniteState s_vl singleSlotBranch := by
        dsimp only [vl_rest]
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hand_ev]
        dsimp only
        rw [if_neg h10]
        rcases h_ss : evaluateHOLFiniteState s_vl singleSlotBranch with ⟨sr, sp⟩
        cases sr with
        | none => exact absurd (congrArg Prod.fst h_ss) hss_nn
        | some _ => rfl
      rw [hrest_eq_ss] at hsvl_res ⊢
      -- Load `child := load(node + 32 + idx * 8)`!
      obtain ⟨hslot_bv, wchild, hdom_ch_slot, hmem_ch_slot⟩ := hsz_nd widx.toNat hwidx_lt
      have hwidx_bv : BitVec.ofNat 64 widx.toNat = widx := by simp
      rw [hwidx_bv] at hslot_bv
      have hwch_mw : wchild.toNat = memW s (wnode.toNat + 32 + 8 * widx.toNat) := by
        unfold memW; rw [hmem_ch_slot]
      have hwch_nz_nat : wchild.toNat ≠ 0 := by
        rw [hwch_mw]
        exact hcnt_pos (by rw [hcnt1]; decide)
      have hwch_root : RootIn Nd wchild.toNat := by
        rw [hwch_mw]
        exact hp_node.2.2.2.2.2.1 hnode_k3 widx.toNat hwidx_lt
      have hchild_in : wchild.toNat ∈ Nd := hwch_root.resolve_left hwch_nz_nat
      have hp_ch := hNd.1 wchild.toNat hchild_in
      obtain ⟨hsz_ch32, _, _⟩ := nodeSize_bounds (memW s wchild.toNat)
      have hch_ins := hp_ch.2.2.1
      have hch_add : ∀ k : Nat, k < nodeSize (memW s wchild.toNat) →
          wchild + BitVec.ofNat 64 k = BitVec.ofNat 64 (wchild.toNat + k) ∧
          (wchild + BitVec.ofNat 64 k).toNat = wchild.toNat + k := by
        intro k hk
        have hlt : wchild.toNat + k < 2 ^ 64 := by dsimp [Inside, nodeIvl] at hch_ins; omega
        have heq : wchild + BitVec.ofNat 64 k = BitVec.ofNat 64 (wchild.toNat + k) := by
          apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
        exact ⟨heq, by rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]⟩
      have hload_ch_off : ∀ (st : PanSemStateFiniteExact 64 F) (k : Nat),
          (∀ c : BitVec 64, c.toNat < globN s "heap_ptr" → st.memory c = s.memory c) →
          st.memaddrs = s.memaddrs →
          st.locals.lookup (ofString "child") = some (.val (.word wchild)) →
          k < nodeSize (memW s wchild.toNat) → k % 8 = 0 →
          @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
            (.load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 k)])) =
            some (.val (.word (BitVec.ofNat 64 (memW s (wchild.toNat + k))))) := by
        intro st k hmem_lt hma hch_lk hk hk8
        have hch_in_hp : Inside (nodeIvl s wchild.toNat) sourceBase (globN s "heap_ptr") := by
          rcases hp_ch.2.1 with h1 | h2
          · exact h1
          · have := hp_ch.2.2.1.2; have := hAR.2.2.2.1; have := hAR.2.2.2.2.1
            have hsep : heapLimit ≤ scratchStart := by decide
            dsimp [nodeIvl, Inside] at *; omega
        obtain ⟨w_at, hdom_at, hm_at⟩ := hp_ch.2.2.2.1.2.2 (k / 8) (by dsimp [nodeIvl]; omega)
        dsimp [nodeIvl] at hdom_at hm_at
        have hmul : wchild.toNat + 8 * (k / 8) = wchild.toNat + k := by omega
        rw [hmul] at hdom_at hm_at
        have hdom_st : st.memaddrs (wchild + BitVec.ofNat 64 k) := by
          rw [hma, (hch_add k hk).1]; exact hdom_at
        have hm_st : st.memory (wchild + BitVec.ofNat 64 k) = .word w_at := by
          rw [hmem_lt _ (by rw [(hch_add k hk).2]; dsimp [nodeIvl, Inside] at hch_in_hp; omega),
              (hch_add k hk).1]
          exact hm_at
        have hmw_eq : BitVec.ofNat 64 (memW s (wchild.toNat + k)) = w_at := by
          unfold memW; rw [hm_at]; simp
        simp [evalHOLExact, evalListHOLExact, hch_lk, valueIsWord, valueWord, wordOpHOL, wordOp,
          isWfShapeExactHOL, memLoadHOLExact, hdom_st, hm_st, hmw_eq]
      -- Evaluate `dec child := load(node + 32 + idx * 8)` and `dec ck := load(child + 0)`
      have hsvl_mem : s_vl.memory = s.memory := by unfold SoloHtabSet.LocFrame at hfr_svl; rw [hfr_svl]
      have hsvl_ma : s_vl.memaddrs = s.memaddrs := by unfold SoloHtabSet.LocFrame at hfr_svl; rw [hfr_svl]
      have hev_child : @evalHOLExact 64 F _ s_vl.toExact (fun a => Classical.propDecidable (s_vl.memaddrs a))
          (.load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 32),
            .panop .mul [.var .local (ofString "idx"), .const (BitVec.ofNat 64 8)]])) =
          some (.val (.word wchild)) := by
        have hadd_ev : @evalHOLExact 64 F _ s_vl.toExact (fun a => Classical.propDecidable (s_vl.memaddrs a))
            (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 32),
              .panop .mul [.var .local (ofString "idx"), .const (BitVec.ofNat 64 8)]]) =
            some (.val (.word (BitVec.ofNat 64 (wnode.toNat + 32 + 8 * widx.toNat)))) := by
          have hadd0 : ∀ u : BitVec 64, u + (0 : BitVec 64) = u := BitVec.add_zero
          simp only [evalHOLExact, evalListHOLExact, hsvl_node, hsvl_idx,
            valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, List.all, List.map, Option.map,
            Bool.and_self, ↓reduceIte, List.foldr, hadd0]
          congr 3
          rw [← BitVec.add_assoc, hslot_bv]
        have hdom_svl : s_vl.memaddrs (BitVec.ofNat 64 (wnode.toNat + 32 + 8 * widx.toNat)) := by
          rw [hsvl_ma]; exact hdom_ch_slot
        have hmem_svl : s_vl.memory (BitVec.ofNat 64 (wnode.toNat + 32 + 8 * widx.toNat)) = .word wchild := by
          rw [hsvl_mem]; exact hmem_ch_slot
        conv_lhs => unfold evalHOLExact
        rw [hadd_ev]
        simp [isWfShapeExactHOL, memLoadHOLExact, hdom_svl, hmem_svl]
      set s_ch := setVarHOLFinite (ofString "child") (.val (.word wchild)) s_vl
      have hsch_ch : s_ch.locals.lookup (ofString "child") = some (.val (.word wchild)) := by
        simp [s_ch, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      set wck : BitVec 64 := BitVec.ofNat 64 (memW s (wchild.toNat + 0))
      have hwck_le3 : memW s wchild.toNat ≤ 3 := hp_ch.1
      have hwck_nat : wck.toNat = memW s wchild.toNat := by
        dsimp [wck]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hev_ck : @evalHOLExact 64 F _ s_ch.toExact (fun a => Classical.propDecidable (s_ch.memaddrs a))
          (.load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 0)])) =
          some (.val (.word wck)) :=
        hload_ch_off s_ch 0 (fun c _ => congrFun hsvl_mem c) hsvl_ma hsch_ch (by omega) (by decide)
      set s_ck := setVarHOLFinite (ofString "ck") (.val (.word wck)) s_ch
      set cont_nib : ProgHOL 64 :=
        .seq
          (.ite (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 3)))
            (.call none (ofString "node_new_ext")
              [.var .local (ofString "nib"), .const (BitVec.ofNat 64 1), .var .local (ofString "child")])
            .skip)
          (.decCall (ofString "cat") .one (ofString "nibbles_concat")
            [.var .local (ofString "nib"), .const (BitVec.ofNat 64 1),
             .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 32)]),
             .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 40)])]
            (.seq
              (.ite (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 1)))
                (.call none (ofString "node_new_leaf")
                  [.var .local (ofString "cat"),
                   .op .add [.const (BitVec.ofNat 64 1),
                     .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 40)])],
                   .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 48)]),
                   .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 56)])])
                .skip)
              (.call none (ofString "node_new_ext")
                [.var .local (ofString "cat"),
                 .op .add [.const (BitVec.ofNat 64 1),
                   .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 40)])],
                 .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 48)])])))
      set ck_body : ProgHOL 64 :=
        .seq
          (.ite (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 0)))
            (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 2)])
            .skip)
          (.decCall (ofString "nib") .one (ofString "alloc") [.const (BitVec.ofNat 64 8)]
            (.seq
              (.storeByte (.var .local (ofString "nib")) (.var .local (ofString "idx")))
              cont_nib))
      have hss_decs : (evaluateHOLFiniteState s_vl singleSlotBranch).1 =
          (evaluateHOLFiniteState s_ck ck_body).1 ∧
          ∃ L_ck, (evaluateHOLFiniteState s_vl singleSlotBranch).2 =
            { (evaluateHOLFiniteState s_ck ck_body).2 with locals := L_ck } := by
        dsimp only [singleSlotBranch]
        rw [evaluateHOLFiniteState_dec_total]; dsimp only
        rw [hev_child]; simp only [shapeEqHOL, shapeOfHOLExact, ↓reduceIte]
        rw [evaluateHOLFiniteState_dec_total]; dsimp only
        rw [hev_ck]; simp only [shapeEqHOL, shapeOfHOLExact, ↓reduceIte]
        exact ⟨rfl, _, rfl⟩
      obtain ⟨hss_res_eq, L_ck, hss_post_eq⟩ := hss_decs
      have hsck_res : Resumes (evaluateHOLFiniteState s_ck ck_body).1 := by
        rwa [← hss_res_eq]
      have hfr_sck : SoloHtabSet.LocFrame s_vl s_ck :=
        ((SoloHtabSet.LocFrame.refl s_vl).locals _).locals _
      have hsck_code : s_ck.code = originalRuntimeCode := hsvl_code
      have hsck_AR : ArenaReady s_ck := localsFree_arenaReady s_vl _ _ hsvl_AR
      have hsck_Nd : NodeHeap s_ck Nd := hsvl_Nd
      have hsck_ck : s_ck.locals.lookup (ofString "ck") = some (.val (.word wck)) := by
        simp [s_ck, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hsck_ch : s_ck.locals.lookup (ofString "child") = some (.val (.word wchild)) := by
        simp [s_ck, s_ch, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "ck" ≠ ofString "child" by decide]
      have hsck_idx : s_ck.locals.lookup (ofString "idx") = some (.val (.word widx)) := by
        simp [s_ck, s_ch, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsvl_idx,
          show ofString "ck" ≠ ofString "idx" by decide,
          show ofString "child" ≠ ofString "idx" by decide]
      -- Check `ck == 0`!
      have hc_ck0 : @evalHOLExact 64 F _ s_ck.toExact (fun a => Classical.propDecidable (s_ck.memaddrs a))
          (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 0))) =
          some (.val (.word (if wck = 0 then 1 else 0))) := by
        simp [evalHOLExact, hsck_ck, Compiler.Encoders.Asm.wordCmpHOL]
      by_cases hck0 : wck = 0
      · -- `ck == 0` -> `mpt_fail(2)`!
        have hite_ck0 : evaluateHOLFiniteState s_ck
            (.ite (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 0)))
              (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 2)])
              .skip) =
            evaluateHOLFiniteState s_ck
              (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 2)]) := by
          rw [evaluateHOLFiniteState_ite, hc_ck0, if_pos hck0]; simp
        have hfail_nn := mpt_fail_ne_none s_ck hsck_code (.const (BitVec.ofNat 64 2))
        rcases hfail_out : evaluateHOLFiniteState s_ck
            (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 2)]) with ⟨fr_o, fp_o⟩
        have hfail_out' : evaluateHOLFiniteState s_ck
            (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 2)]) = (fr_o, fp_o) := hfail_out
        rcases fr_o with _ | fr_some
        · exact absurd (congrArg Prod.fst hfail_out') hfail_nn
        · have hck_eq : evaluateHOLFiniteState s_ck ck_body = (some fr_some, fp_o) := by
            dsimp only [ck_body]
            rw [evaluateHOLFiniteState_seq_line780, hite_ck0, hfail_out']
          rw [hck_eq] at hsck_res
          obtain ⟨eid, ev, hfail_exn, _, hstep_fail⟩ := mpt_fail_call_resumes hsck_code hsck_AR hsck_Nd
            (by rw [hfail_out']; exact hsck_res)
          rw [hfail_out'] at hfail_exn hstep_fail
          dsimp only at hfail_exn hstep_fail
          injection hfail_exn with hfr_eq; subst hfr_eq
          refine ⟨Nd, ?_, ?_⟩
          · rw [hss_post_eq, hck_eq]
            exact (nodeStep_of_locFrame hfr_sck hstep_fail).with_locals_clock _ _
          · intro v hv; rw [hss_res_eq, hck_eq] at hv; cases hv
      · -- `ck != 0`: allocate 8-byte nibble buffer and `storeByte nib, idx`!
        have hite_ck0_skip : evaluateHOLFiniteState s_ck
            (.ite (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 0)))
              (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 2)])
              .skip) = (none, s_ck) := by
          rw [evaluateHOLFiniteState_ite, hc_ck0, if_neg hck0]; simp [evaluateHOLFiniteState_skip]
        have hck_eq_nib : evaluateHOLFiniteState s_ck ck_body =
            evaluateHOLFiniteState s_ck
              (.decCall (ofString "nib") .one (ofString "alloc") [.const 8]
                (.seq (.storeByte (.var .local (ofString "nib")) (.var .local (ofString "idx"))) cont_nib)) := by
          dsimp only [ck_body]
          rw [evaluateHOLFiniteState_seq_line780, hite_ck0_skip]
          rfl
        rw [hck_eq_nib] at hsck_res
        obtain ⟨wnib, s_nib, hs_nib_code, hstep_nib_ck, hKey_nib, hmem_lt_nib_ck, hs_nib_nib,
            hs_nib_other, hs_nib_res, hnib_r_eq, hnib_p_eq⟩ :=
          alloc8_storeByte_nibble_step s_ck Nd widx hsck_code hsck_AR hsck_Nd hwidx_lt hsck_idx cont_nib hsck_res
        have hstep_nib : NodeStep s_vl s_nib Nd Nd := nodeStep_of_locFrame hfr_sck hstep_nib_ck
        have hstep_nib_s : NodeStep s s_nib Nd Nd := nodeStep_of_locFrame hfr_svl hstep_nib
        have hmem_lt_nib : ∀ c : BitVec 64, c.toNat < globN s "heap_ptr" → s_nib.memory c = s.memory c := by
          intro c hlt
          have hhp_eq_ck : globN s_ck "heap_ptr" = globN s "heap_ptr" := by
            have hfr_all := hfr_svl.trans hfr_sck
            unfold SoloHtabSet.LocFrame at hfr_all; unfold globN; rw [hfr_all]
          have hmem_ck : s_ck.memory = s.memory := hsvl_mem
          rw [hmem_lt_nib_ck c (by omega), hmem_ck]
        have hs_nib_ma : s_nib.memaddrs = s.memaddrs :=
          hstep_nib_s.arena.1.memaddrs.trans hAR.1.memaddrs.symm
        have hs_nib_AR : ArenaReady s_nib := hstep_nib.arena
        have hs_nib_Nd : NodeHeap s_nib Nd := hstep_nib.heap
        have hs_nib_ck : s_nib.locals.lookup (ofString "ck") = some (.val (.word wck)) := by
          rw [hs_nib_other _ (by decide)]; exact hsck_ck
        have hs_nib_ch : s_nib.locals.lookup (ofString "child") = some (.val (.word wchild)) := by
          rw [hs_nib_other _ (by decide)]; exact hsck_ch
        -- Check `ck == 3`!
        have hc_ck3 : @evalHOLExact 64 F _ s_nib.toExact (fun a => Classical.propDecidable (s_nib.memaddrs a))
            (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 3))) =
            some (.val (.word (if wck = 3 then 1 else 0))) := by
          simp [evalHOLExact, hs_nib_ck, Compiler.Encoders.Asm.wordCmpHOL]
        by_cases hck3 : wck = 3
        · -- `ck == 3` -> tail call `node_new_ext(nib, 1, child)`!
          have hite_ck3 : evaluateHOLFiniteState s_nib
              (.ite (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 3)))
                (.call none (ofString "node_new_ext")
                  [.var .local (ofString "nib"), .const (BitVec.ofNat 64 1), .var .local (ofString "child")])
                .skip) =
              evaluateHOLFiniteState s_nib
                (.call none (ofString "node_new_ext")
                  [.var .local (ofString "nib"), .const (BitVec.ofNat 64 1), .var .local (ofString "child")]) := by
            rw [evaluateHOLFiniteState_ite, hc_ck3, if_pos hck3]; simp
          set ext3_call : ProgHOL 64 :=
            .call none (ofString "node_new_ext")
              [.var .local (ofString "nib"), .const (BitVec.ofNat 64 1), .var .local (ofString "child")]
          have hnn_ext3 := call_none_ne_none s_nib (ofString "node_new_ext")
            [.var .local (ofString "nib"), .const (BitVec.ofNat 64 1), .var .local (ofString "child")]
          have hcont_eq_ext3 : evaluateHOLFiniteState s_nib cont_nib =
              evaluateHOLFiniteState s_nib ext3_call := by
            dsimp only [cont_nib]
            rw [evaluateHOLFiniteState_seq_line780, hite_ck3]
            rcases h_ec : evaluateHOLFiniteState s_nib ext3_call with ⟨er, ep⟩
            cases er with
            | none => exact absurd (congrArg Prod.fst h_ec) hnn_ext3
            | some _ => rfl
          rw [hcont_eq_ext3] at hs_nib_res
          have hext3_args : evalListHOLFinite s_nib (h := fun a => Classical.propDecidable (s_nib.memaddrs a))
              [.var .local (ofString "nib"), .const (BitVec.ofNat 64 1), .var .local (ofString "child")] =
              some [.val (.word wnib), .val (.word 1), .val (.word wchild)] := by
            rw [evalListHOLFinite_eq_toExact]
            have h1 : @evalHOLExact 64 F _ s_nib.toExact (fun a => Classical.propDecidable (s_nib.memaddrs a))
                (.var .local (ofString "nib")) = some (.val (.word wnib)) := hs_nib_nib
            have h2 : @evalHOLExact 64 F _ s_nib.toExact (fun a => Classical.propDecidable (s_nib.memaddrs a))
                (.const (BitVec.ofNat 64 1)) = some (.val (.word 1)) := rfl
            have h3 : @evalHOLExact 64 F _ s_nib.toExact (fun a => Classical.propDecidable (s_nib.memaddrs a))
                (.var .local (ofString "child")) = some (.val (.word wchild)) := hs_nib_ch
            dsimp only [evalListHOLExact]
            rw [h1, h2, h3]
          obtain ⟨Nd_ext3, hstep_ext3, hret_ext3⟩ := tail_call_node_new_ext s_nib Nd
            _ _ _ wnib 1 wchild hs_nib_code hs_nib_AR hs_nib_Nd hext3_args
            (by simpa using hKey_nib) (Or.inr hchild_in) hs_nib_res
          refine ⟨Nd_ext3, ?_, ?_⟩
          · rw [hss_post_eq, hck_eq_nib, hnib_p_eq, hcont_eq_ext3]
            exact ((NodeStep.trans hsvl_AR hstep_nib hstep_ext3).with_locals_clock _ _).with_locals_clock _ _
          · intro v hv
            rw [hss_res_eq, hck_eq_nib, hnib_r_eq, hcont_eq_ext3] at hv
            exact hret_ext3 v hv
        · -- `ck ∈ {1, 2}`: `nibbles_concat(nib, 1, load(child+32), load(child+40))`!
          have hwck_12 : memW s wchild.toNat = 1 ∨ memW s wchild.toNat = 2 := by
            have hne0 : memW s wchild.toNat ≠ 0 := by
              intro h0; apply hck0; apply BitVec.eq_of_toNat_eq; rw [hwck_nat]; exact h0
            have hne3 : memW s wchild.toNat ≠ 3 := by
              intro h3; apply hck3; apply BitVec.eq_of_toNat_eq; rw [hwck_nat]; simpa using h3
            omega
          have hsz_ch56 : 56 ≤ nodeSize (memW s wchild.toNat) := by
            rcases hwck_12 with hk1 | hk2
            · simp [nodeSize, hk1]
            · simp [nodeSize, hk2]
          have hite_ck3_skip : evaluateHOLFiniteState s_nib
              (.ite (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 3)))
                (.call none (ofString "node_new_ext")
                  [.var .local (ofString "nib"), .const (BitVec.ofNat 64 1), .var .local (ofString "child")])
                .skip) = (none, s_nib) := by
            rw [evaluateHOLFiniteState_ite, hc_ck3, if_neg hck3]; simp [evaluateHOLFiniteState_skip]
          set cat_body : ProgHOL 64 :=
            .seq
              (.ite (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 1)))
                (.call none (ofString "node_new_leaf")
                  [.var .local (ofString "cat"),
                   .op .add [.const (BitVec.ofNat 64 1),
                     .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 40)])],
                   .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 48)]),
                   .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 56)])])
                .skip)
              (.call none (ofString "node_new_ext")
                [.var .local (ofString "cat"),
                 .op .add [.const (BitVec.ofNat 64 1),
                   .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 40)])],
                 .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 48)])])
          set dc_cat : ProgHOL 64 :=
            .decCall (ofString "cat") .one (ofString "nibbles_concat")
              [.var .local (ofString "nib"), .const (BitVec.ofNat 64 1),
               .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 32)]),
               .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 40)])]
              cat_body
          have hcont_eq_cat : evaluateHOLFiniteState s_nib cont_nib = evaluateHOLFiniteState s_nib dc_cat := by
            dsimp only [cont_nib]
            rw [evaluateHOLFiniteState_seq_line780, hite_ck3_skip]
          rw [hcont_eq_cat] at hs_nib_res
          set wch32 : BitVec 64 := BitVec.ofNat 64 (memW s (wchild.toNat + 32))
          set wch40 : BitVec 64 := BitVec.ofNat 64 (memW s (wchild.toNat + 40))
          have hwch32_nat : wch32.toNat = memW s (wchild.toNat + 32) := by
            dsimp [wch32]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold memW; rcases s.memory _ with ⟨w⟩; exact w.isLt)]
          have hwch40_nat : wch40.toNat = memW s (wchild.toNat + 40) := by
            dsimp [wch40]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold memW; rcases s.memory _ with ⟨w⟩; exact w.isLt)]
          have hkey_ch_s : KeyIn s Nd wch32.toNat wch40.toNat := by
            rw [hwch32_nat, hwch40_nat]
            exact hp_ch.2.2.2.2.2.2.1 hwck_12
          have hkey_ch_nib : KeyIn s_nib Nd wch32.toNat wch40.toNat :=
            NodeStep.keyIn hAR hNd hstep_nib_s hkey_ch_s
          have hcat_args_ev : evalListHOLFinite s_nib (h := fun a => Classical.propDecidable (s_nib.memaddrs a))
              [.var .local (ofString "nib"), .const (BitVec.ofNat 64 1),
               .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 32)]),
               .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 40)])] =
              some [.val (.word wnib), .val (.word 1), .val (.word wch32), .val (.word wch40)] := by
            rw [evalListHOLFinite_eq_toExact]
            have h32 := hload_ch_off s_nib 32 hmem_lt_nib hs_nib_ma hs_nib_ch (by omega) (by decide)
            have h40 := hload_ch_off s_nib 40 hmem_lt_nib hs_nib_ma hs_nib_ch (by omega) (by decide)
            have h1 : @evalHOLExact 64 F _ s_nib.toExact (fun a => Classical.propDecidable (s_nib.memaddrs a))
                (.var .local (ofString "nib")) = some (.val (.word wnib)) := hs_nib_nib
            have h2 : @evalHOLExact 64 F _ s_nib.toExact (fun a => Classical.propDecidable (s_nib.memaddrs a))
                (.const (BitVec.ofNat 64 1)) = some (.val (.word 1)) := rfl
            dsimp only [evalListHOLExact]
            rw [h1, h2, h32, h40]
          obtain ⟨cvals, cbody, ccallee, cret, _, hcargs, hcl, hcexn | ⟨crv, cpost, hcrun, _, hccont_res, hcr_eq, hcp_eq⟩⟩ :=
            decCall_resumes_inv hs_nib_res
          · obtain ⟨eid, ev, hc_exn, hne_tr, _⟩ := hcexn
            have hsame := lookupCodeHOLFinite_installed_body s_nib.code.lookup (ofString "nibbles_concat")
              _ _ _ _ _ cvals ccallee (by rw [hs_nib_code]; exact lookup_nibbles_concat) hcl
            subst hsame
            exact absurd (congrArg Prod.fst hc_exn)
              (nibbles_concat_no_nonTrap_exn (callEntryStateHOLFinite s_nib ccallee) hs_nib_code eid ev hne_tr)
          · have hcvals : cvals = [.val (.word wnib), .val (.word 1), .val (.word wch32), .val (.word wch40)] :=
              Option.some.inj (hcargs.symm.trans hcat_args_ev)
            subst hcvals
            have hcl_ex := pan_four_word_lookup s_nib.code.lookup (ofString "nibbles_concat")
              (ofString "a") (ofString "al") (ofString "b") (ofString "bl")
              (sourceFnBody Guest.Software.guestFn_nibbles_concat) wnib 1 wch32 wch40
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by rw [hs_nib_code]; exact lookup_nibbles_concat)
            rw [hcl_ex] at hcl
            obtain ⟨rfl, hrest_c⟩ := Prod.mk.inj (Option.some.inj hcl.symm)
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrest_c
            let centry := callEntryStateHOLFinite s_nib
              ((((HolFiniteMapExact.empty.update (ofString "a", .val (.word wnib))).update
                (ofString "al", .val (.word 1))).update (ofString "b", .val (.word wch32))).update
                (ofString "bl", .val (.word wch40)))
            have hc_spec := nibbles_concat_body_spec centry Nd wnib 1 wch32 wch40
              hs_nib_code (localsFree_arenaReady s_nib _ _ hs_nib_AR) hs_nib_Nd
              hKey_nib hkey_ch_nib
              (by simp [centry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                    show ofString "bl" ≠ ofString "a" by decide,
                    show ofString "b" ≠ ofString "a" by decide,
                    show ofString "al" ≠ ofString "a" by decide])
              (by simp [centry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                    show ofString "bl" ≠ ofString "al" by decide,
                    show ofString "b" ≠ ofString "al" by decide])
              (by simp [centry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                    show ofString "bl" ≠ ofString "b" by decide])
              (by simp [centry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
              crv (by rw [hcrun])
            rw [hcrun] at hc_spec
            obtain ⟨wcat, rfl, hcl_sum, hstep_cat_ent, hKey_cat, hmem_lt_cpost⟩ := hc_spec
            dsimp only at hstep_cat_ent hKey_cat hmem_lt_cpost
            have hstep_cat : NodeStep s_nib cpost Nd Nd := NodeStep.from_locals_clock hstep_cat_ent
            have hstep_nib_cat : NodeStep s_vl cpost Nd Nd := NodeStep.trans hsvl_AR hstep_nib hstep_cat
            set s_cat := setVarHOLFinite (ofString "cat") (.val (.word wcat)) { cpost with locals := s_nib.locals }
            have hscat_code : s_cat.code = originalRuntimeCode := hstep_cat.arena.1.code
            have hscat_ma : s_cat.memaddrs = s.memaddrs :=
              hstep_cat.arena.1.memaddrs.trans hAR.1.memaddrs.symm
            have hscat_AR : ArenaReady s_cat := localsFree_arenaReady cpost _ _ hstep_cat.arena
            have hscat_Nd : NodeHeap s_cat Nd := hstep_cat.heap
            have hmem_lt_scat : ∀ c : BitVec 64, c.toNat < globN s "heap_ptr" → s_cat.memory c = s.memory c := by
              intro c hlt
              have hle_hp : globN s "heap_ptr" ≤ globN centry "heap_ptr" := hstep_nib_s.hp_le
              change cpost.memory c = s.memory c
              rw [hmem_lt_cpost c (lt_of_lt_of_le hlt hle_hp)]
              exact hmem_lt_nib c hlt
            have hscat_cat : s_cat.locals.lookup (ofString "cat") = some (.val (.word wcat)) := by
              simp [s_cat, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have hscat_ck : s_cat.locals.lookup (ofString "ck") = some (.val (.word wck)) := by
              simp [s_cat, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs_nib_ck,
                show ofString "cat" ≠ ofString "ck" by decide]
            have hscat_ch : s_cat.locals.lookup (ofString "child") = some (.val (.word wchild)) := by
              simp [s_cat, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs_nib_ch,
                show ofString "cat" ≠ ofString "child" by decide]
            set wcl : BitVec 64 := (1 : BitVec 64) + wch40
            have hKey_cat_cl : KeyIn s_cat Nd wcat.toNat wcl.toNat := by
              dsimp only [wcl]; rw [hcl_sum]; exact hKey_cat
            have hev_cl : @evalHOLExact 64 F _ s_cat.toExact (fun a => Classical.propDecidable (s_cat.memaddrs a))
                (.op .add [.const (BitVec.ofNat 64 1),
                  .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 40)])]) =
                some (.val (.word wcl)) := by
              have h40 := hload_ch_off s_cat 40 hmem_lt_scat hscat_ma hscat_ch (by omega) (by decide)
              have hc1_ev : @evalHOLExact 64 F _ s_cat.toExact (fun a => Classical.propDecidable (s_cat.memaddrs a))
                  (.const (BitVec.ofNat 64 1)) = some (.val (.word 1)) := rfl
              have hlst : @evalListHOLExact 64 F _ s_cat.toExact (fun a => Classical.propDecidable (s_cat.memaddrs a))
                  [.const (BitVec.ofNat 64 1),
                   .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 40)])] =
                  some [.val (.word 1), .val (.word wch40)] := by
                dsimp only [evalListHOLExact]; rw [hc1_ev, h40]
              conv_lhs => unfold evalHOLExact
              rw [hlst]
              simp [wcl, valueIsWord, valueWord, wordOpHOL, wordOp]
            -- Branch on `ck == 1` vs `ck == 2`!
            have hc_ck1 : @evalHOLExact 64 F _ s_cat.toExact (fun a => Classical.propDecidable (s_cat.memaddrs a))
                (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 1))) =
                some (.val (.word (if wck = 1 then 1 else 0))) := by
              simp [evalHOLExact, hscat_ck, Compiler.Encoders.Asm.wordCmpHOL]
            by_cases hck1 : wck = 1
            · -- `ck == 1` -> tail call `node_new_leaf(cat, 1 + child+40, child+48, child+56)`!
              have hch_k1 : memW s wchild.toNat = 1 := by
                have := congrArg BitVec.toNat hck1; rw [hwck_nat] at this; simpa using this
              have hsz_ch64 : nodeSize (memW s wchild.toNat) = 64 := by simp [nodeSize, hch_k1]
              have hite_ck1 : evaluateHOLFiniteState s_cat
                  (.ite (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 1)))
                    (.call none (ofString "node_new_leaf")
                      [.var .local (ofString "cat"),
                       .op .add [.const (BitVec.ofNat 64 1),
                         .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 40)])],
                       .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 48)]),
                       .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 56)])])
                    .skip) =
                  evaluateHOLFiniteState s_cat
                    (.call none (ofString "node_new_leaf")
                      [.var .local (ofString "cat"),
                       .op .add [.const (BitVec.ofNat 64 1),
                         .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 40)])],
                       .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 48)]),
                       .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 56)])]) := by
                rw [evaluateHOLFiniteState_ite, hc_ck1, if_pos hck1]; simp
              set lf1_call : ProgHOL 64 :=
                .call none (ofString "node_new_leaf")
                  [.var .local (ofString "cat"),
                   .op .add [.const (BitVec.ofNat 64 1),
                     .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 40)])],
                   .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 48)]),
                   .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 56)])]
              have hnn_lf1 := call_none_ne_none s_cat (ofString "node_new_leaf")
                [.var .local (ofString "cat"),
                 .op .add [.const (BitVec.ofNat 64 1),
                   .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 40)])],
                 .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 48)]),
                 .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 56)])]
              have hcat_eq_lf1 : evaluateHOLFiniteState s_cat cat_body = evaluateHOLFiniteState s_cat lf1_call := by
                dsimp only [cat_body]
                rw [evaluateHOLFiniteState_seq_line780, hite_ck1]
                rcases h_lc : evaluateHOLFiniteState s_cat lf1_call with ⟨lr, lp⟩
                cases lr with
                | none => exact absurd (congrArg Prod.fst h_lc) hnn_lf1
                | some _ => rfl
              rw [hcat_eq_lf1] at hccont_res
              set wch48 : BitVec 64 := BitVec.ofNat 64 (memW s (wchild.toNat + 48))
              set wch56 : BitVec 64 := BitVec.ofNat 64 (memW s (wchild.toNat + 56))
              have hwch56_lt : wch56.toNat < 2 ^ 40 := by
                have h56 := hp_ch.2.2.2.2.2.2.2.2.1 hch_k1
                have hlt64 : memW s (wchild.toNat + 56) < 2 ^ 64 := lt_trans h56 (by decide)
                dsimp [wch56]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]; exact h56
              have hlf1_args : evalListHOLFinite s_cat (h := fun a => Classical.propDecidable (s_cat.memaddrs a))
                  [.var .local (ofString "cat"),
                   .op .add [.const (BitVec.ofNat 64 1),
                     .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 40)])],
                   .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 48)]),
                   .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 56)])] =
                  some [.val (.word wcat), .val (.word wcl), .val (.word wch48), .val (.word wch56)] := by
                rw [evalListHOLFinite_eq_toExact]
                have h48 := hload_ch_off s_cat 48 hmem_lt_scat hscat_ma hscat_ch (by omega) (by decide)
                have h56 := hload_ch_off s_cat 56 hmem_lt_scat hscat_ma hscat_ch (by omega) (by decide)
                have h1 : @evalHOLExact 64 F _ s_cat.toExact (fun a => Classical.propDecidable (s_cat.memaddrs a))
                    (.var .local (ofString "cat")) = some (.val (.word wcat)) := hscat_cat
                dsimp only [evalListHOLExact]
                rw [h1, hev_cl, h48, h56]
              obtain ⟨Nd_lf1, hstep_lf1, hret_lf1⟩ := tail_call_node_new_leaf s_cat Nd
                _ _ _ _ wcat wcl wch48 wch56 hscat_code hscat_AR hscat_Nd hlf1_args hKey_cat_cl hwch56_lt hccont_res
              refine ⟨Nd_lf1, ?_, ?_⟩
              · rw [hss_post_eq, hck_eq_nib, hnib_p_eq, hcont_eq_cat, hcp_eq, hcat_eq_lf1]
                exact (((NodeStep.trans hsvl_AR hstep_nib_cat (NodeStep.from_locals_clock hstep_lf1)).with_locals_clock _ _).with_locals_clock _ _).with_locals_clock _ _
              · intro v hv
                rw [hss_res_eq, hck_eq_nib, hnib_r_eq, hcont_eq_cat, hcr_eq, hcat_eq_lf1] at hv
                exact hret_lf1 v hv
            · -- `ck == 2` -> tail call `node_new_ext(cat, 1 + child+40, child+48)`!
              have hch_k2 : memW s wchild.toNat = 2 := by
                rcases hwck_12 with hk1 | hk2
                · exfalso; apply hck1; apply BitVec.eq_of_toNat_eq; rw [hwck_nat]; simpa using hk1
                · exact hk2
              have hite_ck1_skip : evaluateHOLFiniteState s_cat
                  (.ite (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 1)))
                    (.call none (ofString "node_new_leaf")
                      [.var .local (ofString "cat"),
                       .op .add [.const (BitVec.ofNat 64 1),
                         .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 40)])],
                       .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 48)]),
                       .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 56)])])
                    .skip) = (none, s_cat) := by
                rw [evaluateHOLFiniteState_ite, hc_ck1, if_neg hck1]; simp [evaluateHOLFiniteState_skip]
              set ext2_call : ProgHOL 64 :=
                .call none (ofString "node_new_ext")
                  [.var .local (ofString "cat"),
                   .op .add [.const (BitVec.ofNat 64 1),
                     .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 40)])],
                   .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 48)])]
              have hcat_eq_ext2 : evaluateHOLFiniteState s_cat cat_body = evaluateHOLFiniteState s_cat ext2_call := by
                dsimp only [cat_body]
                rw [evaluateHOLFiniteState_seq_line780, hite_ck1_skip]
              rw [hcat_eq_ext2] at hccont_res
              set wch48 : BitVec 64 := BitVec.ofNat 64 (memW s (wchild.toNat + 48))
              have hwch48_root : RootIn Nd wch48.toNat := by
                dsimp [wch48]
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold memW; rcases s.memory _ with ⟨w⟩; exact w.isLt)]
                exact hp_ch.2.2.2.2.1 hch_k2
              have hext2_args : evalListHOLFinite s_cat (h := fun a => Classical.propDecidable (s_cat.memaddrs a))
                  [.var .local (ofString "cat"),
                   .op .add [.const (BitVec.ofNat 64 1),
                     .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 40)])],
                   .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 48)])] =
                  some [.val (.word wcat), .val (.word wcl), .val (.word wch48)] := by
                rw [evalListHOLFinite_eq_toExact]
                have h48 := hload_ch_off s_cat 48 hmem_lt_scat hscat_ma hscat_ch (by omega) (by decide)
                have h1 : @evalHOLExact 64 F _ s_cat.toExact (fun a => Classical.propDecidable (s_cat.memaddrs a))
                    (.var .local (ofString "cat")) = some (.val (.word wcat)) := hscat_cat
                dsimp only [evalListHOLExact]
                rw [h1, hev_cl, h48]
              obtain ⟨Nd_ext2, hstep_ext2, hret_ext2⟩ := tail_call_node_new_ext s_cat Nd
                _ _ _ wcat wcl wch48 hscat_code hscat_AR hscat_Nd hext2_args hKey_cat_cl hwch48_root hccont_res
              refine ⟨Nd_ext2, ?_, ?_⟩
              · rw [hss_post_eq, hck_eq_nib, hnib_p_eq, hcont_eq_cat, hcp_eq, hcat_eq_ext2]
                exact (((NodeStep.trans hsvl_AR hstep_nib_cat (NodeStep.from_locals_clock hstep_ext2)).with_locals_clock _ _).with_locals_clock _ _).with_locals_clock _ _
              · intro v hv
                rw [hss_res_eq, hck_eq_nib, hnib_r_eq, hcont_eq_cat, hcr_eq, hcat_eq_ext2] at hv
                exact hret_ext2 v hv
    · -- Subcase 2b: `¬ (wcount = 1 ∧ wvl = 0)` -> skip `singleSlotBranch`, `return node`!
      have hand_ev0 : @evalHOLExact 64 F _ s_vl.toExact (fun a => Classical.propDecidable (s_vl.memaddrs a))
          (.op .and [
            .cmp .notEqual (.const (BitVec.ofNat 64 0))
              (.cmp .equal (.var .local (ofString "count")) (.const (BitVec.ofNat 64 1))),
            .cmp .notEqual (.const (BitVec.ofNat 64 0))
              (.cmp .equal (.var .local (ofString "vl")) (.const (BitVec.ofNat 64 0)))]) =
          some (.val (.word 0)) := by
        by_cases hc1 : wcount = BitVec.ofNat 64 1
        · have hvl_ne0 : wvl ≠ BitVec.ofNat 64 0 := fun hz => hcond ⟨hc1, hz⟩
          simp [evalHOLExact, evalListHOLExact, hsvl_cnt, hsvl_vl, hc1, hvl_ne0,
            Compiler.Encoders.Asm.wordCmpHOL, valueIsWord, valueWord, wordOpHOL, wordOp,
            List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
        · by_cases hvl0 : wvl = BitVec.ofNat 64 0 <;>
            simp [evalHOLExact, evalListHOLExact, hsvl_cnt, hsvl_vl, hc1, hvl0,
              Compiler.Encoders.Asm.wordCmpHOL, valueIsWord, valueWord, wordOpHOL, wordOp,
              List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
      have hrest_ret : evaluateHOLFiniteState s_vl vl_rest =
          (some (.returned (.val (.word wnode))), emptyLocalsHOLFinite s_vl) := by
        dsimp only [vl_rest]
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hand_ev0]
        simp [evaluateHOLFiniteState_skip, evaluateHOLFiniteState_return, evalHOLExact,
          hsvl_node, shapeOfHOLExact, sizeOfShapeWithContextHOL]
      refine ⟨Nd, ?_, ?_⟩
      · rw [hrest_ret]; exact (NodeStep.refl hsvl_AR hsvl_Nd).with_locals_clock _ _
      · intro v hv
        rw [hrest_ret] at hv; injection hv with h1; injection h1 with h2; subst h2
        exact ⟨wnode, rfl, Or.inr hnode_in⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards
