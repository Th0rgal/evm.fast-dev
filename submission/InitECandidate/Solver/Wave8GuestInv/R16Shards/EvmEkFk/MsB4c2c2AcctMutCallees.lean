import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.MsB4c2cAcctMut

/-!
# Scratch Rung B4c2c2: Account-Copy & Account-Mutation Callees as `WorldKeepsCodeSc`

Lifts `acct_copy_step` and the remaining account-mutation callees of `AccountWk`
(`clear_account_preserving_balance`, `create_ether`, `set_account_balance`,
`increment_nonce`) from `WorldKeepsSc` to `WorldKeepsCodeSc`.
-/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.EvmBase
open InitECandidate.Solver.Wave8GuestInv.EvmStepLemmas
open InitECandidate.Solver.Wave8GuestInv.EvmFrameSpecs
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8M19.Htab
open InitECandidate.Solver.Wave8GuestInv.HtabC00Ports
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

/-! ## 1. `acct_copy` Step & Combinators -/

private theorem flattenHOL_shape_u256 {v : ValueHOL 64}
    (hsh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact v) = true) :
    (flattenHOL v).length = 4 := by
  rcases v with _ | fs | _
  · simp [shapeOfHOLExact, shapeEqHOL] at hsh
  · rcases fs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩⟩ <;>
      try (simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh)
    rcases v0 with ⟨⟨a⟩⟩ | _ | _ <;> rcases v1 with ⟨⟨b⟩⟩ | _ | _ <;>
      rcases v2 with ⟨⟨c⟩⟩ | _ | _ <;> rcases v3 with ⟨⟨d⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh
    simp [flattenHOL]
  · simp [shapeOfHOLExact, shapeEqHOL] at hsh

theorem acct_copy_step_code {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hA : ArenaReady s)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
        [.var .local (ofString "a")])).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
        [.var .local (ofString "a")])).1) :
    let res := (evaluateHOLFiniteState s
      (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
        [.var .local (ofString "a")])).1
    let post := (evaluateHOLFiniteState s
      (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
        [.var .local (ofString "a")])).2
    WorldEff s post [] [] ["heap_ptr"] ∧
    (res = none → ∃ bw : BitVec 64,
      post.locals = s.locals.update (ofString "a", .val (.word bw)) ∧
      globN s "heap_ptr" ≤ bw.toNat ∧ bw.toNat + 56 ≤ heapLimit) := by
  dsimp only
  have hhl_he : heapLimit ≤ heapEnd := by decide
  have hhl_264 : heapLimit < 2 ^ 64 := by decide
  have heff0 : WorldEff s s [] [] ["heap_ptr"] := WorldEff.refl s [] [] ["heap_ptr"] hA hcode
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "a")] with _ | vals
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "acct_copy") vals with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        have hb_eq : body' = sourceFnBody Guest.Software.guestFn_acct_copy :=
          lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "acct_copy")
            _ _ body' _ ret' vals callee lookup_acct_copy (by rwa [← hcode])
        have hr_eq : ret' = .one :=
          lookupCodeHOLFinite_installed_return s (ofString "acct_copy")
            _ _ _ _ ret' vals callee (by rw [hcode]; exact lookup_acct_copy) hl
        subst hb_eq hr_eq
        obtain ⟨aw, rfl, haw_c⟩ := R10Shards.P26_P28.lookupCode_one_word lookup_acct_copy (by rwa [← hcode])
        let ent := callEntryStateHOLFinite s callee
        have hent_a : ent.locals.lookup (ofString "a") = some (.val (.word aw)) := haw_c
        have heff_ent : WorldEff s ent [] [] ["heap_ptr"] := heff0.locals_clock _ _
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) (sourceFnBody Guest.Software.guestFn_acct_copy) with ⟨rc, pc⟩
        have hrun_ent : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_acct_copy) = (rc, pc) := hrun
        have hnt_ent : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_acct_copy)).1 ≠ some .timeOut := by
          rw [hrun_ent]; rintro rfl; simp [hrun] at hnt
        simp only [hrun] at hnt hfr ⊢
        cases rc with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | exception eid ev =>
            dsimp only at hfr ⊢
            have hres_ex : Resumes (some (.exception eid ev)) := by
              rcases hfr with h | h | h | hr <;> try simp at h
              exact hr
            have heff_pc : WorldEff s pc [] [] ["heap_ptr"] := by
              have hbody_eq2 : sourceFnBody Guest.Software.guestFn_acct_copy =
                  .decCall (ofString "b") .one (ofString "alloc") [.const 56#64]
                    (.seq
                      (.call (some (none, none)) (ofString "memcpy")
                        [.var .local (ofString "b"), .var .local (ofString "a"), .const 56#64])
                      (.return (.var .local (ofString "b")))) := rfl
              have hex_ev : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_acct_copy)).1 =
                  some (.exception eid ev) := by dsimp only [ent]; rw [hrun]
              have hp_ev : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_acct_copy)).2 = pc := by
                dsimp only [ent]; rw [hrun]
              rw [← hp_ev, hbody_eq2]
              refine R16Shards.worldEff_decCall_alloc heff_ent (by decide) (ofString "b") (.const 56#64)
                (by rw [← hbody_eq2]; exact hnt_ent)
                (by rw [← hbody_eq2, hex_ev]; exact Or.inr (Or.inr (Or.inr hres_ex)))
                (fun bw nw m1 hsz_ev _ hm1_loc _ heff_m1 _ _ hbw_lo hbw_end _ _ hnt1 hcr1 => ?_)
              have hnw_eq : nw = 56#64 := by simp [evalHOLExact] at hsz_ev; exact hsz_ev.symm
              subst hnw_eq
              have hbw_hi : bw.toNat + 56 ≤ heapLimit := by
                change bw.toNat + (56 + 7) / 8 * 8 = globN m1 "heap_ptr" at hbw_end; omega
              have hm1_b : m1.locals.lookup (ofString "b") = some (.val (.word bw)) := by
                rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
              refine R16Shards.worldEff_seq hnt1 hcr1
                (fun hnt_mc hcr_mc => worldEff_call0_memcpy heff_m1 _ _ _ hnt_mc
                  (by rcases hcr_mc with h | h | h | hr
                      · exact Or.inl h
                      · exfalso
                        rw [evaluateHOLFiniteState_call] at h; split at h <;> try simp at h
                        split at h <;> try simp at h
                        split at h <;> try simp at h
                        split at h <;> try simp at h
                        · split at h <;> simp_all
                        · simp_all
                      · exfalso
                        rw [evaluateHOLFiniteState_call] at h; split at h <;> try simp at h
                        split at h <;> try simp at h
                        split at h <;> try simp at h
                        split at h <;> try simp at h
                        · split at h <;> simp_all
                        · simp_all
                      · exact Or.inr hr)
                  (fun dstw _ nw' hd _ hn _ => by
                    simp [evalHOLExact, toExact, hm1_b] at hd hn
                    subst hd hn
                    exact Or.inr (Or.inr (Or.inr ⟨hbw_lo, hbw_hi⟩))))
                (fun m2 _ heff_m2 _ _ => R16Shards.worldEff_return heff_m2 _)
            exact ⟨heff_pc.locals_clock _ _, fun h => by simp at h⟩
          | returned rv =>
            dsimp only at hfr ⊢
            split
            · rename_i hsh_rv
              split
              · have hbody_eq2 : sourceFnBody Guest.Software.guestFn_acct_copy =
                    .decCall (ofString "b") .one (ofString "alloc") [.const 56#64]
                      (.seq
                        (.call (some (none, none)) (ofString "memcpy")
                          [.var .local (ofString "b"), .var .local (ofString "a"), .const 56#64])
                        (.return (.var .local (ofString "b")))) := rfl
                rw [hbody_eq2] at hrun_ent
                rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun_ent
                have hargs56 : evalListHOLFinite ent (h := fun a => Classical.propDecidable (ent.memaddrs a))
                    [.const 56#64] = some [.val (.word 56#64)] := by
                  simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
                have hlk56 := pan_one_word_lookup ent.code.lookup (ofString "alloc") (ofString "n")
                  (sourceFnBody Guest.Software.guestFn_alloc) 56#64
                  (by rw [show ent.code = originalRuntimeCode from hcode]; exact lookup_alloc_r16)
                rw [hargs56] at hrun_ent; dsimp only at hrun_ent
                rw [hlk56] at hrun_ent; dsimp only at hrun_ent
                by_cases hcz_ent : ent.clock = 0
                · simp [hcz_ent] at hrun_ent
                rw [if_neg hcz_ent] at hrun_ent
                obtain ⟨pw, hpw_lk⟩ : ∃ pw : BitVec 64, ent.globals.lookup (ofString "heap_ptr") = some (.val (.word pw)) :=
                  globalWord_of_globN_pos ent "heap_ptr"
                    (by have := heff_ent.arena.2.1; rw [EvmBase.sourceBase_val] at this; omega)
                let ent_al := callEntryStateHOLFinite ent (HolFiniteMapExact.empty.update (ofString "n", .val (.word 56#64)))
                rcases hrun_al : evaluateHOLFiniteState ent_al (sourceFnBody Guest.Software.guestFn_alloc) with ⟨ral, pal⟩
                dsimp only [ent_al] at hrun_al
                rw [hrun_al] at hrun_ent
                have hres_al : Wave8Contracts.M18.Resumes ral := by
                  cases ral with
                  | none => simp at hrun_ent
                  | some c0 =>
                    cases c0 with
                    | returned r0 => exact Or.inl ⟨r0, rfl⟩
                    | exception e0 v0 => dsimp only at hrun_ent; injection hrun_ent with hr0 _; cases hr0
                    | _ => simp at hrun_ent
                have hal := R13.alloc_body_resumes ent_al pw hcode hpw_lk
                  (by dsimp only [ent_al]; rw [hrun_al]; exact hres_al)
                dsimp only [ent_al] at hal
                rw [hrun_al] at hal
                obtain ⟨nw', hnw'_lk, hral_eq, hcmp1, hcmp2, hpal_eq⟩ := hal
                have hnw56 : nw' = 56#64 := by
                  simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE] at hnw'_lk; exact hnw'_lk.symm
                subst hnw56
                dsimp only at hral_eq hpal_eq
                subst hral_eq
                dsimp only at hrun_ent
                have hsh_pw : (shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one &&
                    shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one) = true := by
                  simp [shapeOfHOLExact, shapeEqHOL]
                rw [if_pos hsh_pw] at hrun_ent
                set m1 := setVarHOLFinite (ofString "b") (.val (.word pw)) { pal with locals := ent.locals }
                have hm1_next : m1 = { ent with
                    globals := ent.globals.update (ofString "heap_ptr", .val (.word ((pw + (56#64 + 7)) &&& ((0 : BitVec 64) - 8)))),
                    locals := m1.locals, clock := m1.clock } := by
                  dsimp only [m1, setVarHOLFinite]; rw [hpal_eq]; rfl
                obtain ⟨heff_m1, _, _, _, hp_lo_s, hp_add, hp_hi, _⟩ :=
                  R16Shards.worldEff_alloc_step heff_ent (by decide) hpw_lk hcmp1 hcmp2 hm1_next
                have hpw_hi : pw.toNat + 56 ≤ heapLimit := by
                  change pw.toNat + (56 + 7) / 8 * 8 = globN m1 "heap_ptr" at hp_add; omega
                have hm1_b : m1.locals.lookup (ofString "b") = some (.val (.word pw)) := by
                  simp [m1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                rcases hseq_m1 : evaluateHOLFiniteState m1
                    (.seq
                      (.call (some (none, none)) (ofString "memcpy")
                        [.var .local (ofString "b"), .var .local (ofString "a"), .const 56#64])
                      (.return (.var .local (ofString "b")))) with ⟨rseq, pseq⟩
                rw [hseq_m1] at hrun_ent
                dsimp only at hrun_ent
                have hrseq_eq : rseq = some (.returned rv) := (Prod.mk.inj hrun_ent).1
                have hpc_pseq : pc = { pseq with locals := (HolFiniteMapExact.resVarEq pseq.locals
                    (ofString "b", ent.locals.lookup (ofString "b"))) } := ((Prod.mk.inj hrun_ent).2).symm
                rw [evaluateHOLFiniteState_seq_line780] at hseq_m1
                rcases hmc : evaluateHOLFiniteState m1
                    (.call (some (none, none)) (ofString "memcpy")
                      [.var .local (ofString "b"), .var .local (ofString "a"), .const 56#64]) with ⟨rmc, m2⟩
                rw [hmc] at hseq_m1
                cases rmc with
                | some cr_mc =>
                  exfalso
                  dsimp only at hseq_m1
                  have hcr_ret : some cr_mc = some (.returned rv) := (Prod.mk.inj hseq_m1).1.trans hrseq_eq
                  injection hcr_ret with hcr_eq; subst hcr_eq
                  rw [evaluateHOLFiniteState_call] at hmc
                  rcases ha_mc : evalListHOLFinite m1 (h := fun a => Classical.propDecidable (m1.memaddrs a))
                      [.var .local (ofString "b"), .var .local (ofString "a"), .const 56#64] with _ | vs_mc
                  · rw [ha_mc] at hmc; simp at hmc
                  · rw [ha_mc] at hmc; dsimp only at hmc
                    rcases hl_mc : lookupCodeHOLFinite m1.code.lookup (ofString "memcpy") vs_mc with _ | ⟨bmc, cmc, rmc'⟩
                    · rw [hl_mc] at hmc; simp at hmc
                    · rw [hl_mc] at hmc; dsimp only at hmc
                      by_cases hcz_m1 : m1.clock = 0
                      · simp [hcz_m1] at hmc
                      · rw [if_neg hcz_m1] at hmc
                        rcases hrun_mc : evaluateHOLFiniteState (callEntryStateHOLFinite m1 cmc) bmc with ⟨rmc0, pmc0⟩
                        rw [hrun_mc] at hmc
                        cases rmc0 with
                        | none => simp at hmc
                        | some c0 =>
                          cases c0 with
                          | returned v0 =>
                            dsimp only at hmc
                            by_cases hsh0 : shapeEqHOL (shapeOfHOLExact v0) rmc' = true
                            · simp [hsh0] at hmc
                            · simp [hsh0] at hmc
                          | exception _ _ => simp at hmc
                          | _ => simp at hmc
                | none =>
                  dsimp only at hseq_m1
                  have heff_m2 : WorldEff s m2 [] [] ["heap_ptr"] := by
                    have hw := worldEff_call0_memcpy heff_m1
                      (.var .local (ofString "b")) (.var .local (ofString "a")) (.const 56#64)
                      (by rw [hmc]; simp) (by rw [hmc]; exact Or.inl rfl)
                      (fun dstw _ nw' hd _ hn _ => by
                        simp [evalHOLExact, toExact, hm1_b] at hd hn
                        subst hd hn
                        exact Or.inr (Or.inr (Or.inr ⟨hp_lo_s, hpw_hi⟩)))
                    rw [hmc] at hw; exact hw
                  have hm2_loc : m2.locals = m1.locals := by
                    have hk := fun k => evaluate_avoidsLocal_flowing k
                      (.call (some (none, none)) (ofString "memcpy")
                        [.var .local (ofString "b"), .var .local (ofString "a"), .const 56#64])
                      rfl m1 (by rw [hmc]; exact Or.inl rfl)
                    apply HolFiniteMapExact.ext; funext k; simpa [hmc] using hk k
                  rw [evaluateHOLFiniteState_return] at hseq_m1
                  simp only [evalHOLExact, toExact, hm2_loc, hm1_b, shapeOfHOLExact, sizeOfShapeWithContextHOL,
                    show (1 : Nat) ≤ 32 by decide, ↓reduceIte, emptyLocalsHOLFinite] at hseq_m1
                  have hrv_pw_opt : (some (PanSemResultExact.returned (.val (.word pw))) : Option (PanSemResultExact 64)) =
                      some (PanSemResultExact.returned rv) :=
                    (Prod.mk.inj hseq_m1).1.trans hrseq_eq
                  injection hrv_pw_opt with hrv_eq
                  injection hrv_eq with hrv_eq'
                  subst hrv_eq'
                  have hpseq_eq : pseq = { m2 with locals := HolFiniteMapExact.empty } :=
                    ((Prod.mk.inj hseq_m1).2).symm
                  have hpc_m2 : pc = { m2 with locals := pc.locals, clock := pc.clock } := by
                    rw [hpc_pseq, hpseq_eq]
                  have heff_out : WorldEff s (setVarHOLFinite (ofString "a") (.val (.word pw)) { pc with locals := s.locals })
                      [] [] ["heap_ptr"] := by
                    rw [hpc_m2]; exact heff_m2.locals_clock _ _
                  exact ⟨heff_out, fun _ => ⟨pw, rfl, hp_lo_s, hpw_hi⟩⟩
              · rename_i hbad; simp only [hsh_rv, hbad, ↓reduceIte] at hfr; exact absurd hfr not_flowingOrResumes_error
            · rename_i hbad; simp only [hbad, Bool.false_eq_true, ↓reduceIte] at hfr; exact absurd hfr not_flowingOrResumes_error

private theorem progWStepCode_acctCopy_mut {B : BufList} {gw : List String}
    (hhp_in : "heap_ptr" ∈ gw) (mutProg : ProgHOL 64)
    (hmut : ∀ {F : Type} (s s1 : PanSemStateFiniteExact 64 F) (bw : BitVec 64),
      WorldEff s s1 [] [] ["heap_ptr"] →
      s1.locals = s.locals.update (ofString "a", .val (.word bw)) →
      s1.locals.lookup (ofString "a") = some (.val (.word bw)) →
      globN s "heap_ptr" ≤ bw.toNat → bw.toNat + 56 ≤ heapLimit →
      (evaluateHOLFiniteState s1 mutProg).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState s1 mutProg).1 →
      WorldEff s (evaluateHOLFiniteState s1 mutProg).2 [] [] ["heap_ptr"]) :
    ProgWStepCode B gw
      (.seq
        (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
          [.var .local (ofString "a")])
        mutProg) := by
  intro F s hc hW hnt hfr
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases h1 : evaluateHOLFiniteState s
      (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
        [.var .local (ofString "a")]) with ⟨r1, s1⟩
  simp only [h1] at hnt hfr ⊢
  cases r1 with
  | some cr1 =>
    have hac := acct_copy_step_code s hc hW.1 (by rw [h1]; exact hnt) (by rw [h1]; exact hfr)
    rw [h1] at hac
    have hws0 : WorldStepCodeSc [] ["heap_ptr"] s (some cr1) s1 :=
      worldEff_to_worldStepCodeSc (B := []) (r := some cr1) hW
        (by decide) (by intro _ hp; cases hp) (by decide) hac.1
    exact worldStepCodeSc_mono_bufs (fun _ h => by cases h) (by simp [hhp_in]) hws0
  | none =>
    dsimp only at hnt hfr ⊢
    have hac := acct_copy_step_code s hc hW.1 (by rw [h1]; simp) (by rw [h1]; exact Or.inl rfl)
    rw [h1] at hac; dsimp only at hac
    obtain ⟨bw, hs1_loc, hbw_lo, hbw_hi⟩ := hac.2 rfl
    have hs1_a : s1.locals.lookup (ofString "a") = some (.val (.word bw)) := by
      rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hcr : ContOrRes (evaluateHOLFiniteState s1 mutProg).1 := by
      rcases hfr with h | h | h | hr
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr hr))
    have heff2 := hmut s s1 bw hac.1 hs1_loc hs1_a hbw_lo hbw_hi hnt hcr
    have hws0 : WorldStepCodeSc [] ["heap_ptr"] s
        (evaluateHOLFiniteState s1 mutProg).1 (evaluateHOLFiniteState s1 mutProg).2 :=
      worldEff_to_worldStepCodeSc (B := []) (r := (evaluateHOLFiniteState s1 mutProg).1) hW
        (by decide) (by intro _ hp; cases hp) (by decide) heff2
    exact worldStepCodeSc_mono_bufs (fun _ h => by cases h) (by simp [hhp_in]) hws0

private theorem evaluateHOLFiniteState_seq_assoc_code {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p1 p2 p3 : ProgHOL 64) :
    evaluateHOLFiniteState s (.seq p1 (.seq p2 p3)) =
      evaluateHOLFiniteState s (.seq (.seq p1 p2) p3) := by
  simp only [evaluateHOLFiniteState_seq_line780]
  rcases evaluateHOLFiniteState s p1 with ⟨r1, s1⟩
  cases r1 <;> rfl

private theorem progWStepCode_acctCopy_mut_tail {B : BufList} {gw : List String}
    (hB : PosBufList B) (hgw : SafeStepGlobals gw)
    (hhp_in : "heap_ptr" ∈ gw) (mutProg tailProg : ProgHOL 64)
    (hmut : ∀ {F : Type} (s s1 : PanSemStateFiniteExact 64 F) (bw : BitVec 64),
      WorldEff s s1 [] [] ["heap_ptr"] →
      s1.locals = s.locals.update (ofString "a", .val (.word bw)) →
      s1.locals.lookup (ofString "a") = some (.val (.word bw)) →
      globN s "heap_ptr" ≤ bw.toNat → bw.toNat + 56 ≤ heapLimit →
      (evaluateHOLFiniteState s1 mutProg).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState s1 mutProg).1 →
      WorldEff s (evaluateHOLFiniteState s1 mutProg).2 [] [] ["heap_ptr"])
    (htail : ProgWStepCode B gw tailProg) :
    ProgWStepCode B gw
      (.seq
        (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
          [.var .local (ofString "a")])
        (.seq mutProg tailProg)) := by
  intro F s hc hW hnt hfr
  rw [evaluateHOLFiniteState_seq_assoc_code] at hnt hfr ⊢
  exact progWStepCode_seq hB hgw (progWStepCode_acctCopy_mut hhp_in mutProg hmut) htail s hc hW hnt hfr

private theorem safeStepGlobals_acctMut_code : SafeStepGlobals ["heap_ptr", "journal_n", "scratch_ptr"] := by
  intro g hg; simp at hg; rcases hg with rfl | rfl | rfl <;> simp

/-! ## 2. `clear_account_preserving_balance`, `create_ether`, `set_account_balance`, `increment_nonce` -/

theorem wkCodeSc_clear_account_preserving_balance :
    WorldKeepsCodeSc acctMutBufs ["heap_ptr", "journal_n", "scratch_ptr"]
      (ofString "clear_account_preserving_balance") := by
  have hB := posBufList_acctMutBufs
  have hgw := safeStepGlobals_acctMut_code
  have hhl_264 : heapLimit < 2 ^ 64 := by decide
  refine worldKeepsCodeSc_of_progWStepCode lookup_clear_account_preserving_balance ?_
  simp only [sourceFunctionEntry, Guest.Software.guestFn_clear_account_preserving_balance,
    FrontendCodecComputation.declToHOLStructural, FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural, FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, FrontendCodecComputation.shapeToHOLStructural,
    FrontendCodecComputation.shapeListToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStepCode_seq hB hgw
    (progWStepCode_call0 (by intro p hp; simp at hp; subst hp; simp [acctMutBufs])
      (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp) wkCodeSc_destroy_storage) ?_
  refine progWStepCode_decCall hB hgw
    (by intro p hp; simp [wsAcctBufs] at hp; rcases hp with rfl | rfl | rfl <;> simp [acctMutBufs])
    (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp)
    wkCodeSc_get_account ?_
  intro F s0 hc0 hW0 hnt0 hfr0
  have hassoc : evaluateHOLFiniteState s0
      (.seq (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy") [.var .local (ofString "a")])
        (.seq (.store (.op .add [.var .local (ofString "a"), .const 0#64]) (.const 0#64))
          (.seq (.store (.op .add [.var .local (ofString "a"), .const 48#64]) (.var .global (ofString "empty_code_hash")))
            (.seq (.call (some (none, none)) (ofString "modify_state_commit") [.var .local (ofString "addr"), .var .local (ofString "a")])
              (.return (.const 0#64)))))) =
      evaluateHOLFiniteState s0
      (.seq (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy") [.var .local (ofString "a")])
        (.seq
          (.seq (.store (.op .add [.var .local (ofString "a"), .const 0#64]) (.const 0#64))
            (.store (.op .add [.var .local (ofString "a"), .const 48#64]) (.var .global (ofString "empty_code_hash"))))
          (.seq (.call (some (none, none)) (ofString "modify_state_commit") [.var .local (ofString "addr"), .var .local (ofString "a")])
            (.return (.const 0#64))))) := by
    simp only [evaluateHOLFiniteState_seq_line780]
    rcases evaluateHOLFiniteState s0 _ with ⟨r1, s1⟩
    cases r1 with
    | some _ => rfl
    | none =>
      dsimp only
      rcases evaluateHOLFiniteState s1 _ with ⟨r2, _⟩
      cases r2 <;> rfl
  rw [hassoc] at hnt0 hfr0 ⊢
  refine progWStepCode_acctCopy_mut_tail hB hgw (by simp) _ _
    (fun s s1 bw heff1 _ hs1_a hbw_lo hbw_hi hnt1 hcr1 => ?_)
    (progWStepCode_seq hB hgw
      (progWStepCode_call0 (by intro p hp; simp at hp; subst hp; simp [acctMutBufs])
        (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp) wkCodeSc_modify_state_commit)
      (progWStepCode_return _ _ _))
    s0 hc0 hW0 hnt0 hfr0
  refine R16Shards.worldEff_seq hnt1 hcr1
    (fun _ _ => R16Shards.worldEff_store_word heff1 _ _
      (fun v hv => by simp [evalHOLExact] at hv; exact ⟨0#64, hv.symm⟩)
      (fun x hx _ => by
        simp [evalHOLExact, evalListHOLExact, toExact, hs1_a, panOpHOL, wordOpHOL, wordOp,
          valueIsWord, valueWord] at hx
        subst hx
        have hx0 : (bw + 0#64).toNat = bw.toNat := by simp
        exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))
    (fun m2 hm2 heff_m2 _ _ => ?_)
  have hm2_loc : m2.locals = s1.locals := by
    have hk := fun k => evaluate_avoidsLocal_flowing k
      (.store (.op .add [.var .local (ofString "a"), .const 0#64]) (.const 0#64))
      rfl s1 (by rw [hm2]; exact Or.inl rfl)
    apply HolFiniteMapExact.ext; funext k; simpa [hm2] using hk k
  exact R16Shards.worldEff_store_word heff_m2 _ _
    (fun v hv => by
      simp only [evalHOLExact, toExact] at hv
      obtain ⟨wech, hwech⟩ := heff_m2.arena.2.2.2.2.2.2.2.2.2 "empty_code_hash" (by decide)
      unfold GlobalWord at hwech
      rw [hwech] at hv; injection hv with hv'; exact ⟨wech, hv'.symm⟩)
    (fun x hx _ => by
      simp [evalHOLExact, evalListHOLExact, toExact, hm2_loc, hs1_a, panOpHOL, wordOpHOL, wordOp,
        valueIsWord, valueWord] at hx
      subst hx
      have hx48 : (bw + 48#64).toNat = bw.toNat + 48 := by
        apply BitVec.toNat_add_of_lt; change bw.toNat + 48 < 2 ^ 64; omega
      exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))

theorem wkCodeSc_create_ether :
    WorldKeepsCodeSc acctMutBufs ["heap_ptr", "journal_n", "scratch_ptr"]
      (ofString "create_ether") := by
  have hB := posBufList_acctMutBufs
  have hgw := safeStepGlobals_acctMut_code
  have hhl_he : heapLimit ≤ heapEnd := by decide
  have hhl_264 : heapLimit < 2 ^ 64 := by decide
  refine worldKeepsCodeSc_of_progWStepCode lookup_create_ether ?_
  simp only [sourceFunctionEntry, Guest.Software.guestFn_create_ether,
    FrontendCodecComputation.declToHOLStructural, FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural, FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, FrontendCodecComputation.shapeToHOLStructural,
    FrontendCodecComputation.shapeListToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStepCode_decCall hB hgw
    (by intro p hp; simp [wsAcctBufs] at hp; rcases hp with rfl | rfl | rfl <;> simp [acctMutBufs])
    (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp)
    wkCodeSc_get_account ?_
  intro F s0 hc0 hW0 hnt0 hfr0
  rw [evaluateHOLFiniteState_seq_line780] at hnt0 hfr0 ⊢
  rcases h1 : evaluateHOLFiniteState s0
      (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
        [.var .local (ofString "a")]) with ⟨r1, s1⟩
  simp only [h1] at hnt0 hfr0 ⊢
  cases r1 with
  | some cr1 =>
    have hac := acct_copy_step_code s0 hc0 hW0.1 (by rw [h1]; exact hnt0) (by rw [h1]; exact hfr0)
    rw [h1] at hac
    have hws0 : WorldStepCodeSc [] ["heap_ptr"] s0 (some cr1) s1 :=
      worldEff_to_worldStepCodeSc (B := []) (r := some cr1) hW0
        (by decide) (by intro _ hp; cases hp) (by decide) hac.1
    exact worldStepCodeSc_mono_bufs (fun _ h => by cases h) (by simp) hws0
  | none =>
    have hac := acct_copy_step_code s0 hc0 hW0.1 (by rw [h1]; simp) (by rw [h1]; exact Or.inl rfl)
    rw [h1] at hac; dsimp only at hac
    obtain ⟨bw, hs1_loc, hbw_lo, hbw_hi⟩ := hac.2 rfl
    have hs1_a : s1.locals.lookup (ofString "a") = some (.val (.word bw)) := by
      rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt0 hfr0 ⊢
    rcases hargs_nb : @evalListHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        [.load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "a"), .const 8#64]),
         .var .local (ofString "amount")] with _ | vnb_args
    · simp [evalListHOLFinite, hargs_nb] at hfr0; exact absurd hfr0 not_flowingOrResumes_error
    · simp only [evalListHOLFinite, hargs_nb] at hnt0 hfr0 ⊢
      rcases hl_nb : lookupCodeHOLFinite s1.code.lookup (ofString "u256_add") vnb_args with _ | ⟨bnb, cnb, rnb⟩
      · simp [hl_nb] at hfr0; exact absurd hfr0 not_flowingOrResumes_error
      · simp only [hl_nb] at hnt0 hfr0 ⊢
        by_cases hcz1 : s1.clock = 0
        · simp [hcz1] at hnt0
        rw [if_neg hcz1] at hnt0 hfr0 ⊢
        let ent_nb := callEntryStateHOLFinite s1 cnb
        rcases hrun_nb : evaluateHOLFiniteState (callEntryStateHOLFinite s1 cnb) bnb with ⟨res_nb, p_nb⟩
        have hrun_nb' : evaluateHOLFiniteState (callEntryStateHOLFinite s1 cnb) bnb = (res_nb, p_nb) := hrun_nb
        simp only [hrun_nb] at hnt0 hfr0 ⊢
        cases res_nb with
        | none => exact absurd hfr0 not_flowingOrResumes_error
        | some cr_nb =>
          cases cr_nb with
          | timeOut => simp at hnt0
          | error | «break» | «continue» => exact absurd hfr0 not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr0 not_flowingOrResumes_finalFfi
          | exception eid ev =>
            dsimp only at hfr0 ⊢
            have hres_ex : Wave8Contracts.M18.Resumes (some (.exception eid ev)) := by
              rcases hfr0 with h | h | h | ⟨_, h⟩ | ⟨_, _, h, hne⟩ <;> try simp at h
              obtain ⟨rfl, rfl⟩ := h
              exact Or.inr ⟨eid, ev, rfl, hne⟩
            have hro := FunSpec.at_lookup ro_u256_add s1 hac.1.code vnb_args bnb cnb rnb hl_nb
              (guestInv_callEntry s1 cnb hac.1.arena.1) (by rw [hrun_nb']; simp)
            have hro' : ((evaluateHOLFiniteState (callEntryStateHOLFinite s1 cnb) bnb).2) = _ :=
              hro (by rw [hrun_nb']; exact hres_ex)
            rw [hrun_nb'] at hro'; dsimp only at hro'
            have heff_ex : WorldEff s0 (emptyLocalsHOLFinite p_nb) [] [] ["heap_ptr"] :=
              (hac.1.of_readOnly hro').locals_clock _ p_nb.clock
            have hws0 : WorldStepCodeSc [] ["heap_ptr"] s0 (some (.exception eid ev)) (emptyLocalsHOLFinite p_nb) :=
              worldEff_to_worldStepCodeSc (B := []) (r := some (.exception eid ev)) hW0
                (by decide) (by intro _ hp; cases hp) (by decide) heff_ex
            exact worldStepCodeSc_mono_bufs (fun _ h => by cases h) (by simp) hws0
          | returned vnb =>
            dsimp only at hnt0 hfr0 ⊢
            by_cases hsh_nb : (shapeEqHOL (shapeOfHOLExact vnb) (.comb [.one, .one, .one, .one]) &&
                shapeEqHOL (shapeOfHOLExact vnb) rnb) = true
            · simp only [hsh_nb, ↓reduceIte] at hnt0 hfr0 ⊢
              have hsh_u256 : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact vnb) = true := by
                have h12 : shapeEqHOL (shapeOfHOLExact vnb) (.comb [.one, .one, .one, .one]) = true := by
                  revert hsh_nb
                  cases shapeEqHOL (shapeOfHOLExact vnb) (.comb [.one, .one, .one, .one]) <;> simp
                rcases vnb with _ | fs | _
                · simp [shapeOfHOLExact, shapeEqHOL] at h12
                · rcases fs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩⟩ <;>
                    try (simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h12; done)
                  rcases v0 with ⟨⟨_⟩⟩ | _ | _ <;> rcases v1 with ⟨⟨_⟩⟩ | _ | _ <;>
                    rcases v2 with ⟨⟨_⟩⟩ | _ | _ <;> rcases v3 with ⟨⟨_⟩⟩ | _ | _ <;>
                    simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h12 ⊢
                · simp [shapeOfHOLExact, shapeEqHOL] at h12
              have hro := FunSpec.at_lookup ro_u256_add s1 hac.1.code vnb_args bnb cnb rnb hl_nb
                (guestInv_callEntry s1 cnb hac.1.arena.1) (by rw [hrun_nb']; simp)
              have hro' : ((evaluateHOLFiniteState (callEntryStateHOLFinite s1 cnb) bnb).2) = _ :=
                hro (by rw [hrun_nb']; exact Or.inl ⟨vnb, rfl⟩)
              rw [hrun_nb'] at hro'; dsimp only at hro'
              set s2 := setVarHOLFinite (ofString "nb") vnb { p_nb with locals := s1.locals }
              have heff2 : WorldEff s0 s2 [] [] ["heap_ptr"] :=
                (hac.1.of_readOnly hro').locals_clock _ _
              have hs2_a : s2.locals.lookup (ofString "a") = some (.val (.word bw)) := by
                simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_a,
                  show ofString "nb" ≠ ofString "a" by decide]
              have hs2_nb : s2.locals.lookup (ofString "nb") = some vnb := by
                simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              rw [evaluateHOLFiniteState_seq_line780] at hnt0 hfr0 ⊢
              rcases hst : evaluateHOLFiniteState s2
                  (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "nb"))) with ⟨rst, s3⟩
              simp only [hst] at hnt0 hfr0 ⊢
              have heff3 : WorldEff s0 s3 [] [] ["heap_ptr"] := by
                have hs3_eq : s3 = (evaluateHOLFiniteState s2
                    (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "nb")))).2 := by
                  rw [hst]
                rw [hs3_eq]
                exact worldEff_store_multi heff2 _ _ 4 (by decide)
                  (fun v hv => by
                    simp [evalHOLExact, toExact, hs2_nb] at hv
                    subst hv
                    exact flattenHOL_shape_u256 hsh_u256)
                  (fun x hx => by
                    simp [evalHOLExact, evalListHOLExact, toExact, hs2_a, panOpHOL, wordOpHOL, wordOp,
                      valueIsWord, valueWord] at hx
                    subst hx
                    have hx8 : (bw + 8#64).toNat = bw.toNat + 8 := by
                      apply BitVec.toNat_add_of_lt; change bw.toNat + 8 < 2 ^ 64; omega
                    exact ⟨by omega, Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))⟩)
              have hstep03 : WorldStepCodeSc acctMutBufs ["heap_ptr", "journal_n", "scratch_ptr"] s0 rst s3 := by
                have hws0 : WorldStepCodeSc [] ["heap_ptr"] s0 rst s3 :=
                  worldEff_to_worldStepCodeSc (B := []) (r := rst) hW0
                    (by decide) (by intro _ hp; cases hp) (by decide) heff3
                exact worldStepCodeSc_mono_bufs (fun _ h => by cases h) (by simp) hws0
              cases rst with
              | some cr_st =>
                exact worldStepCodeSc_with_locals_clock hstep03 _ _
              | none =>
                dsimp only at hnt0 hfr0 ⊢
                have hWs3 : WorldOK s3 := hstep03.worldOK_bufs hB.1 hW0
                have htail_step := progWStepCode_seq hB hgw
                  (progWStepCode_call0 (by intro p hp; simp at hp; subst hp; simp [acctMutBufs])
                    (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp) wkCodeSc_modify_state_commit)
                  (progWStepCode_return _ _ _)
                  s3 heff3.code hWs3 hnt0 hfr0
                exact worldStepCodeSc_trans hB hgw hstep03 (worldStepCodeSc_with_locals_clock htail_step _ _)
            · simp [hsh_nb] at hfr0; exact absurd hfr0 not_flowingOrResumes_error

theorem wkCodeSc_set_account_balance :
    WorldKeepsCodeSc acctMutBufs ["heap_ptr", "journal_n", "scratch_ptr"]
      (ofString "set_account_balance") := by
  have hB := posBufList_acctMutBufs
  have hgw := safeStepGlobals_acctMut_code
  have hhl_he : heapLimit ≤ heapEnd := by decide
  have hhl_264 : heapLimit < 2 ^ 64 := by decide
  refine ⟨_, _, _, lookup_set_account_balance, ?_⟩
  intro F s0 hc0 hW0 ⟨vals, hl⟩ hnt0 hres0
  have hamt_ok : ∃ vamt : ValueHOL 64,
      s0.locals.lookup (ofString "amount") = some vamt ∧
      shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact vamt) = true := by
    have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "set_account_balance")
      vals _ s0.locals _ hl
    simp only [lookupCodeHOLExact, lookup_set_account_balance] at hx
    rcases vals with _ | ⟨va, _ | ⟨vamt, _ | _⟩⟩
    · simp at hx
    · simp at hx
    · rcases va with ⟨⟨wa⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hx; done)
      simp [shapeOfHOLExact, shapeEqHOL, show ofString "addr" ≠ ofString "amount" by decide] at hx
      obtain ⟨hsh_amt, hL⟩ := hx
      refine ⟨vamt, ?_, hsh_amt⟩
      have := congrFun hL (ofString "amount")
      simpa [FUPDATE, show ofString "amount" ≠ ofString "addr" by decide,
        show ofString "addr" ≠ ofString "amount" by decide] using this.symm
    · simp at hx
  obtain ⟨vamt, hs0_amt, hsh_amt⟩ := hamt_ok
  have hfr0 : FlowingOrResumes (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_set_account_balance)).1 :=
    Or.inr (Or.inr (Or.inr hres0))
  simp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_set_account_balance,
    FrontendCodecComputation.declToHOLStructural, FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural, FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, FrontendCodecComputation.shapeToHOLStructural,
    FrontendCodecComputation.shapeListToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil] at hnt0 hfr0 ⊢
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt0 hfr0 ⊢
  rcases hargs : @evalListHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a))
      [.var .local (ofString "addr")] with _ | vs
  · simp [evalListHOLFinite, hargs] at hfr0
    exact absurd hfr0 not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt0 hfr0 ⊢
    rcases hlk : lookupCodeHOLFinite s0.code.lookup (ofString "get_account") vs with _ | ⟨bga, cga, rga⟩
    · simp [hlk] at hfr0; exact absurd hfr0 not_flowingOrResumes_error
    · simp only [hlk] at hnt0 hfr0 ⊢
      by_cases hcz0 : s0.clock = 0
      · simp [hcz0] at hnt0
      rw [if_neg hcz0] at hnt0 hfr0 ⊢
      let ent_ga := callEntryStateHOLFinite s0 cga
      have hWent_ga : WorldOK ent_ga := localsFree_worldOK s0 cga (s0.clock - 1) hW0
      have hmeta_ga := (PanRunBounded.evaluateHOLFiniteState_metadata ent_ga bga).1
      rcases hrun_ga : evaluateHOLFiniteState ent_ga bga with ⟨res_ga, p_ga⟩
      simp only [ent_ga] at hrun_ga hmeta_ga
      simp only [hrun_ga] at hmeta_ga hnt0 hfr0 ⊢
      have hnt_ga : (evaluateHOLFiniteState ent_ga bga).1 ≠ some .timeOut := by
        simp only [ent_ga, hrun_ga]; rintro rfl; simp at hnt0
      cases res_ga with
      | none => exact absurd hfr0 not_flowingOrResumes_error
      | some cr_ga =>
        cases cr_ga with
        | timeOut => simp at hnt0
        | error | «break» | «continue» => exact absurd hfr0 not_flowingOrResumes_error
        | finalFfi _ => exact absurd hfr0 not_flowingOrResumes_finalFfi
        | exception eid ev =>
          dsimp only at hfr0 ⊢
          have hres_ex : Resumes (some (.exception eid ev)) := by
            rcases hfr0 with h | h | h | hr <;> try simp at h
            exact hr
          have hspec := FunSpec.at_lookup wkCodeSc_get_account s0 hc0 vs bga cga rga hlk hWent_ga hnt_ga
          simp only [ent_ga, hrun_ga] at hspec
          exact worldStepCodeSc_from_entry (callee := cga)
            (worldStepCodeSc_mono_bufs
              (by intro p hp; simp [wsAcctBufs] at hp; rcases hp with rfl | rfl | rfl <;> simp [acctMutBufs])
              (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp)
              (hspec hres_ex))
        | returned vga =>
          dsimp only at hnt0 hfr0 ⊢
          by_cases hsh_ga : (shapeEqHOL (shapeOfHOLExact vga) .one && shapeEqHOL (shapeOfHOLExact vga) rga) = true
          · simp only [hsh_ga, ↓reduceIte] at hnt0 hfr0 ⊢
            have hspec := FunSpec.at_lookup wkCodeSc_get_account s0 hc0 vs bga cga rga hlk hWent_ga hnt_ga
            simp only [ent_ga, hrun_ga] at hspec
            have hstep1 : WorldStepCodeSc acctMutBufs ["heap_ptr", "journal_n", "scratch_ptr"]
                (callEntryStateHOLFinite s0 cga) (some (.returned vga)) p_ga :=
              worldStepCodeSc_mono_bufs
                (by intro p hp; simp [wsAcctBufs] at hp; rcases hp with rfl | rfl | rfl <;> simp [acctMutBufs])
                (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp)
                (hspec (Or.inl ⟨vga, rfl⟩))
            set sa := setVarHOLFinite (ofString "a") vga { p_ga with locals := s0.locals }
            have hstep_ga : WorldStepCodeSc acctMutBufs ["heap_ptr", "journal_n", "scratch_ptr"] s0 none sa := by
              simpa only [sa, setVarHOLFinite] using
                (worldStepCodeSc_from_entry (r' := none) (callee := cga)
                  (L := s0.locals.update (ofString "a", vga)) (k := p_ga.clock) hstep1)
            have hWsa : WorldOK sa := hstep_ga.worldOK_bufs hB.1 hW0
            have hsa_code : sa.code = originalRuntimeCode := hmeta_ga.trans hc0
            have hsa_amt : sa.locals.lookup (ofString "amount") = some vamt := by
              simp [sa, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs0_amt,
                show ofString "a" ≠ ofString "amount" by decide]
            let sabTail : ProgHOL 64 :=
              .seq (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy") [.var .local (ofString "a")])
                (.seq (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "amount")))
                  (.seq (.call (some (none, none)) (ofString "modify_state_commit")
                    [.var .local (ofString "addr"), .var .local (ofString "a")])
                    (.return (.const 0#64))))
            have hcont_step : WorldStepCodeSc acctMutBufs ["heap_ptr", "journal_n", "scratch_ptr"]
                sa (evaluateHOLFiniteState sa sabTail).1 (evaluateHOLFiniteState sa sabTail).2 := by
              dsimp only [sabTail] at hnt0 hfr0 ⊢
              rw [evaluateHOLFiniteState_seq_assoc_code] at hnt0 hfr0 ⊢
              rw [evaluateHOLFiniteState_seq_line780] at hnt0 hfr0 ⊢
              have hm_step : WorldStepCodeSc acctMutBufs ["heap_ptr", "journal_n", "scratch_ptr"] sa
                  (evaluateHOLFiniteState sa
                    (.seq (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy") [.var .local (ofString "a")])
                      (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "amount"))))).1
                  (evaluateHOLFiniteState sa
                    (.seq (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy") [.var .local (ofString "a")])
                      (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "amount"))))).2 := by
                have hnt_m : (evaluateHOLFiniteState sa
                    (.seq (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy") [.var .local (ofString "a")])
                      (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "amount"))))).1 ≠ some .timeOut := by
                  rcases hm : evaluateHOLFiniteState sa _ with ⟨rm, sm⟩
                  rw [hm] at hnt0; cases rm with | none => simp | some cm => cases cm <;> simp at hnt0 ⊢
                have hfr_m : FlowingOrResumes (evaluateHOLFiniteState sa
                    (.seq (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy") [.var .local (ofString "a")])
                      (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "amount"))))).1 := by
                  rcases hm : evaluateHOLFiniteState sa _ with ⟨rm, sm⟩
                  rw [hm] at hfr0; cases rm with | none => exact Or.inl rfl | some cm => exact hfr0
                rw [evaluateHOLFiniteState_seq_line780] at hnt_m hfr_m ⊢
                rcases h1 : evaluateHOLFiniteState sa
                    (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
                      [.var .local (ofString "a")]) with ⟨r1, s1⟩
                simp only [h1] at hnt_m hfr_m ⊢
                cases r1 with
                | some cr1 =>
                  have hac := acct_copy_step_code sa hsa_code hWsa.1 (by rw [h1]; exact hnt_m) (by rw [h1]; exact hfr_m)
                  rw [h1] at hac
                  have hws0 : WorldStepCodeSc [] ["heap_ptr"] sa (some cr1) s1 :=
                    worldEff_to_worldStepCodeSc (B := []) (r := some cr1) hWsa
                      (by decide) (by intro _ hp; cases hp) (by decide) hac.1
                  exact worldStepCodeSc_mono_bufs (fun _ h => by cases h) (by simp) hws0
                | none =>
                  dsimp only at hnt_m hfr_m ⊢
                  have hac := acct_copy_step_code sa hsa_code hWsa.1 (by rw [h1]; simp) (by rw [h1]; exact Or.inl rfl)
                  rw [h1] at hac; dsimp only at hac
                  obtain ⟨bw, hs1_loc, hbw_lo, hbw_hi⟩ := hac.2 rfl
                  have hs1_a : s1.locals.lookup (ofString "a") = some (.val (.word bw)) := by
                    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
                  have hs1_amt : s1.locals.lookup (ofString "amount") = some vamt := by
                    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hsa_amt,
                      show ofString "a" ≠ ofString "amount" by decide]
                  have heff2 : WorldEff sa
                      (evaluateHOLFiniteState s1
                        (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "amount")))).2
                      [] [] ["heap_ptr"] :=
                    worldEff_store_multi hac.1 _ _ 4 (by decide)
                      (fun v hv => by
                        simp [evalHOLExact, toExact, hs1_amt] at hv
                        subst hv
                        exact flattenHOL_shape_u256 hsh_amt)
                      (fun x hx => by
                        simp [evalHOLExact, evalListHOLExact, toExact, hs1_a, panOpHOL, wordOpHOL, wordOp,
                          valueIsWord, valueWord] at hx
                        subst hx
                        have hx8 : (bw + 8#64).toNat = bw.toNat + 8 := by
                          apply BitVec.toNat_add_of_lt; change bw.toNat + 8 < 2 ^ 64; omega
                        exact ⟨by omega, Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))⟩)
                  have hws0 : WorldStepCodeSc [] ["heap_ptr"] sa
                      (evaluateHOLFiniteState s1
                        (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "amount")))).1
                      (evaluateHOLFiniteState s1
                        (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "amount")))).2 :=
                    worldEff_to_worldStepCodeSc (B := [])
                      (r := (evaluateHOLFiniteState s1
                        (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "amount")))).1)
                      hWsa (by decide) (by intro _ hp; cases hp) (by decide) heff2
                  exact worldStepCodeSc_mono_bufs (fun _ h => by cases h) (by simp) hws0
              have hm_code := (PanRunBounded.evaluateHOLFiniteState_metadata sa
                (.seq (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy") [.var .local (ofString "a")])
                  (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "amount"))))).1
              rcases hm : evaluateHOLFiniteState sa
                  (.seq (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy") [.var .local (ofString "a")])
                    (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "amount")))) with ⟨rm, sm⟩
              simp only [hm] at hm_step hm_code hnt0 hfr0 ⊢
              cases rm with
              | some crm => exact hm_step
              | none =>
                dsimp only at hnt0 hfr0 ⊢
                have hWsm : WorldOK sm := hm_step.worldOK_bufs hB.1 hWsa
                have htail := progWStepCode_seq hB hgw
                  (progWStepCode_call0 (by intro p hp; simp at hp; subst hp; simp [acctMutBufs])
                    (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp) wkCodeSc_modify_state_commit)
                  (progWStepCode_return _ _ _)
                  sm (hm_code.trans hsa_code) hWsm hnt0 hfr0
                exact worldStepCodeSc_trans hB hgw hm_step htail
            exact worldStepCodeSc_trans hB hgw hstep_ga (worldStepCodeSc_with_locals_clock hcont_step _ _)
          · simp [hsh_ga] at hfr0; exact absurd hfr0 not_flowingOrResumes_error

theorem wkCodeSc_increment_nonce :
    WorldKeepsCodeSc acctMutBufs ["heap_ptr", "journal_n", "scratch_ptr"]
      (ofString "increment_nonce") := by
  have hB := posBufList_acctMutBufs
  have hgw := safeStepGlobals_acctMut_code
  refine worldKeepsCodeSc_of_progWStepCode lookup_increment_nonce ?_
  simp only [sourceFunctionEntry, Guest.Software.guestFn_increment_nonce,
    FrontendCodecComputation.declToHOLStructural, FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural, FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, FrontendCodecComputation.shapeToHOLStructural,
    FrontendCodecComputation.shapeListToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStepCode_decCall hB hgw
    (by intro p hp; simp [wsAcctBufs] at hp; rcases hp with rfl | rfl | rfl <;> simp [acctMutBufs])
    (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp)
    wkCodeSc_get_account ?_
  exact progWStepCode_acctCopy_mut_tail hB hgw (by simp) _ _
    (fun {F} s s1 bw heff1 _ hs1_a hbw_lo hbw_hi _ _ =>
      R16Shards.worldEff_store_word heff1 _ _
        (fun v hv => by
          rcases hld : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
              (.load .one (.op .add [.var .local (ofString "a"), .const 0#64])) with _ | vl
          · simp [evalHOLExact, evalListHOLExact] at hv hld; rw [hld] at hv; simp at hv
          · simp [evalHOLExact, evalListHOLExact] at hv hld; rw [hld] at hv
            rcases vl with ⟨⟨wl⟩⟩ | _ | _ <;> simp [panOpHOL, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
            exact ⟨wl + 1#64, hv.symm⟩)
        (fun x hx _ => by
          simp [evalHOLExact, evalListHOLExact, toExact, hs1_a, panOpHOL, wordOpHOL, wordOp,
            valueIsWord, valueWord] at hx
          subst hx
          have hx0 : (bw + 0#64).toNat = bw.toNat := by simp
          exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))
    (progWStepCode_seq hB hgw
      (progWStepCode_call0 (by intro p hp; simp at hp; subst hp; simp [acctMutBufs])
        (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp) wkCodeSc_modify_state_commit)
      (progWStepCode_return _ _ _))

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
