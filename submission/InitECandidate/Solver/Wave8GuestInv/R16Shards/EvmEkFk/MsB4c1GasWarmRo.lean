import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.MsB4c1aHeadGas
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.WarmAccessHelpers

/-!
# Scratch Rung B4c1: Read-Only Callees, Head Gas Updates, and `warm_address` under `D0PreB`
-/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
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
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.EvmStepLemmas
open InitECandidate.Solver.Wave8GuestInv.EvmFrameSpecs
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
open InitECandidate.Solver.Wave8M19.Htab
open InitECandidate.Solver.Wave8GuestInv.HtabC00Ports
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge
open InitECandidate.Solver.Wave8Contracts
open InitECandidate.Solver.Wave8Contracts.M23
open InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue (noCatchableRaise evaluate_noCatchableRaise)

section MsB4c1GasWarmRo
open R10Shards.GbodyProcessMsg
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

/-! ## 1. Read-only `is_warm_address` and generic `D0PreB` read-only `decCall` wrapper -/
theorem funSpec_charge_state_gas_msgBounded :
    FunSpec EvmMsgReadyMsgBounded
      (fun s r post => Resumes r →
        EvmMsgReadyMsgBounded post ∧ EvmStepCC [] s post ∧
          post.globals = s.globals ∧
          memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112))
      (ofString "charge_state_gas") := by
  refine ⟨_, _, _, lookup_charge_state_gas_b, ?_⟩
  intro F s hcode hB ⟨vals, hl⟩ hnt hres
  have hInv : EvmInv s := evmInv_of_msgBounded hB
  have hlen1 : ∃ v0, vals = [v0] := by
    have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
      originalRuntimeCode.lookup (ofString "charge_state_gas") vals _ _ _ hl
    simp only [Flapjack.lookupCodeHOLExact, lookup_charge_state_gas_b] at hx
    rcases vals with _ | ⟨v0, _ | _⟩ <;> simp at hx
    exact ⟨v0, rfl⟩
  obtain ⟨v0, rfl⟩ := hlen1
  obtain ⟨_, _, amtw, rfl, hamt⟩ := one_word_arg_lookup lookup_charge_state_gas_b hl
  obtain ⟨hb_ev, evw, hevw, hevw_nat⟩ := ev_word_bounds hInv
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by norm_num
  have hev64 : evw + BitVec.ofNat 64 64 = BitVec.ofNat 64 (globN s "ev" + 64) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hevw_nat]
  have hev72 : evw + BitVec.ofNat 64 72 = BitVec.ofNat 64 (globN s "ev" + 72) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hevw_nat]
  have hev192 : evw + BitVec.ofNat 64 192 = BitVec.ofNat 64 (globN s "ev" + 192) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hevw_nat]
  have herr_abs : ∀ {post0 : PanSemStateFiniteExact 64 F},
      Resumes (some PanSemResultExact.error) →
      EvmMsgReadyMsgBounded post0 ∧ EvmStepCC [] s post0 ∧
        post0.globals = s.globals ∧
        memW post0 (globN s "ev" + 112) = memW s (globN s "ev" + 112) :=
    fun hr => absurd hr EvmFrameSpecs.not_resumes_error
  have hsh_w : ∀ w : BitVec 64, shapeEqHOL .one (shapeOfHOLExact (.val (.word w) : ValueHOL 64)) = true :=
    fun _ => by simp [shapeEqHOL, shapeOfHOLExact]
  have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
  have hbody : sourceFnBody Guest.Software.guestFn_charge_state_gas =
      .dec (ofString "sgl") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 72]))
        (.dec (ofString "gl") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 64]))
          (.seq
            (.ite (.cmp .notLower (.var .local (ofString "sgl")) (.var .local (ofString "amount")))
              (.seq
                (.store (.op .add [.var .global (ofString "ev"), .const 72])
                  (.op .sub [.var .local (ofString "sgl"), .var .local (ofString "amount")]))
                (.return (.const 0)))
              .skip)
            (.decCall (ofString "tot") .one (ofString "add_sat")
              [.var .local (ofString "sgl"), .var .local (ofString "gl")]
              (.seq
                (.ite (.cmp .notLower (.var .local (ofString "tot")) (.var .local (ofString "amount")))
                  (.dec (ofString "rem") .one
                    (.op .sub [.var .local (ofString "amount"), .var .local (ofString "sgl")])
                    (.seq
                      (.store (.op .add [.var .global (ofString "ev"), .const 72]) (.const 0))
                      (.seq
                        (.store (.op .add [.var .global (ofString "ev"), .const 64])
                          (.op .sub [.var .local (ofString "gl"), .var .local (ofString "rem")]))
                        (.seq
                          (.store (.op .add [.var .global (ofString "ev"), .const 192])
                            (.op .add
                              [.load .one (.op .add [.var .global (ofString "ev"), .const 192]),
                               .var .local (ofString "rem")]))
                          (.return (.const 0))))))
                  .skip)
                (.seq
                  (.raise (ofString "EvmErr") (.const 4))
                  (.return (.const 0))))))) := rfl
  revert hres
  rw [hbody, evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
  rcases hsgl : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .global (ofString "ev"), .const 72])) with _ | sglv
  · dsimp only; exact herr_abs
  · simp only [hsgl] at hnt ⊢
    have hsgl_w : ∃ sglw : BitVec 64, sglv = .val (.word sglw) ∧ sglw.toNat = memW s (globN s "ev" + 72) := by
      simp [evalHOLExact, evalListHOLExact, hevw, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at hsgl
      rcases hm : s.memory (evw + 72#64) with ⟨sglw⟩
      rw [hm] at hsgl
      exact ⟨sglw, hsgl.2.symm, by unfold memW; rw [← hev72, hm]⟩
    obtain ⟨sglw, rfl, _⟩ := hsgl_w
    rw [if_pos (hsh_w sglw)] at hnt ⊢; dsimp only at hnt ⊢
    set s1 := setVarHOLFinite (ofString "sgl") (.val (.word sglw)) s with hs1
    rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
    rcases hgl : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        (.load .one (.op .add [.var .global (ofString "ev"), .const 64])) with _ | glv
    · dsimp only; exact herr_abs
    · simp only [hgl] at hnt ⊢
      have hs1_evw : s1.globals.lookup (ofString "ev") = some (.val (.word evw)) := hevw
      have hgl_w : ∃ glw : BitVec 64, glv = .val (.word glw) ∧ glw.toNat = memW s (globN s "ev" + 64) := by
        simp [evalHOLExact, evalListHOLExact, hs1_evw, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at hgl
        rcases hm : s.memory (evw + 64#64) with ⟨glw⟩
        have hm1 : s1.memory (evw + 64#64) = .word glw := hm
        rw [hm1] at hgl
        exact ⟨glw, hgl.2.symm, by unfold memW; rw [← hev64, hm]⟩
      obtain ⟨glw, rfl, hglw_eq⟩ := hgl_w
      rw [if_pos (hsh_w glw)] at hnt ⊢; dsimp only at hnt ⊢
      set s2 := setVarHOLFinite (ofString "gl") (.val (.word glw)) s1 with hs2
      have hs2_sgl : s2.locals.lookup (ofString "sgl") = some (.val (.word sglw)) := by
        simp [hs2, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "gl" ≠ ofString "sgl" by decide]
      have hs2_gl : s2.locals.lookup (ofString "gl") = some (.val (.word glw)) := by
        simp [hs2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hs2_amt : s2.locals.lookup (ofString "amount") = some (.val (.word amtw)) := by
        simp [hs2, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hamt,
          show ofString "gl" ≠ ofString "amount" by decide,
          show ofString "sgl" ≠ ofString "amount" by decide]
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
      by_cases hge1 : ¬ (sglw < amtw)
      · have hcmp1 : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
            (.cmp .notLower (.var .local (ofString "sgl")) (.var .local (ofString "amount"))) =
            some (.val (.word 1)) := by
          simp [evalHOLExact, hs2_sgl, hs2_amt, Compiler.Encoders.Asm.wordCmpHOL, hge1]
        rw [hcmp1] at hnt ⊢; dsimp only at hnt ⊢
        rw [if_neg h10] at hnt ⊢
        rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
        rcases hst1 : evaluateHOLFiniteState s2
            (.store (.op .add [.var .global (ofString "ev"), .const 72])
              (.op .sub [.var .local (ofString "sgl"), .var .local (ofString "amount")])) with ⟨r1, s3⟩
        simp only [hst1] at hnt ⊢
        cases r1 with
        | some res1 =>
          have herr1 := store_some_eq_error_d0 hst1; subst herr1
          dsimp only; exact herr_abs
        | none =>
          dsimp only at hnt ⊢
          obtain ⟨w1, _, hs3_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s2) (post := s3)
            (gname := "ev") (gbase := globN s "ev") (off := 72) hevw hevw_nat (by omega)
            (fun v hv => by
              simp [evalHOLExact, evalListHOLExact, hs2_sgl, hs2_amt, valueIsWord, valueWord, wordOpHOL, wordOp] at hv
              exact ⟨_, hv.symm⟩) hst1
          rw [evaluateHOLFiniteState_return] at hnt ⊢; dsimp only [evalHOLExact] at hnt ⊢
          have hsz0 : sizeOfShapeWithContextHOL s3.structs
              (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
            simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
          rw [if_pos hsz0] at hnt ⊢; dsimp only at hnt ⊢
          intro _
          let post : PanSemStateFiniteExact 64 F := { (emptyLocalsHOLFinite s3) with
            locals := ((emptyLocalsHOLFinite s3).locals.resVarEq (ofString "gl", s1.locals.lookup (ofString "gl"))).resVarEq
              (ofString "sgl", s.locals.lookup (ofString "sgl")) }
          have hGp : GuestInv post := guestInv_congr (s := s)
            (by simp [post, emptyLocalsHOLFinite, hs3_eq, hs2, hs1, setVarHOLFinite])
            (by simp [post, emptyLocalsHOLFinite, hs3_eq, hs2, hs1, setVarHOLFinite])
            (by simp [post, emptyLocalsHOLFinite, hs3_eq, hs2, hs1, setVarHOLFinite])
            (by simp [post, emptyLocalsHOLFinite, hs3_eq, hs2, hs1, setVarHOLFinite]) hInv.1.1
          have hglob_p : post.globals = s.globals := by
            simp [post, emptyLocalsHOLFinite, hs3_eq, hs2, hs1, setVarHOLFinite]
          have hbe_p : post.be = s.be := by
            simp [post, emptyLocalsHOLFinite, hs3_eq, hs2, hs1, setVarHOLFinite]
          have hmem_out : ∀ x : BitVec 64,
              (∀ off' ∈ headGasUpdateOffs, x ≠ BitVec.ofNat 64 (globN s "ev" + off')) →
              post.memory x = s.memory x := by
            intro x hx
            change s3.memory x = s.memory x
            rw [hs3_eq]
            have hn72 : x ≠ BitVec.ofNat 64 (globN s "ev" + 72) := hx 72 (by decide)
            simp [R14Shards.OpHandlersA.updW, hn72, hs2, hs1, setVarHOLFinite]
          have hm64 : memW post (globN s "ev" + 64) = memW s (globN s "ev" + 64) := by
            change memW s3 (globN s "ev" + 64) = memW s (globN s "ev" + 64)
            rw [hs3_eq, R14Shards.OpHandlersA.memW_updW_ne s2 _ _ w1 (by omega) (by omega) (by omega)]
            rfl
          have hm192 : memW post (globN s "ev" + 192) = memW s (globN s "ev" + 192) := by
            change memW s3 (globN s "ev" + 192) = memW s (globN s "ev" + 192)
            rw [hs3_eq, R14Shards.OpHandlersA.memW_updW_ne s2 _ _ w1 (by omega) (by omega) (by omega)]
            rfl
          obtain ⟨hBp, hstepCC, h112⟩ := evmMsgReadyMsgBounded_of_head_gas_mem hB hGp hglob_p hbe_p hmem_out
            (by rw [hm64, hm192])
          exact ⟨hBp, hstepCC, hglob_p, h112⟩
      · have hsgl_lt : sglw.toNat < amtw.toNat := by
          rw [Classical.not_not, BitVec.lt_def] at hge1; exact hge1
        have hcmp1 : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
            (.cmp .notLower (.var .local (ofString "sgl")) (.var .local (ofString "amount"))) =
            some (.val (.word 0)) := by
          simp [evalHOLExact, hs2_sgl, hs2_amt, Compiler.Encoders.Asm.wordCmpHOL, hge1]
        rw [hcmp1] at hnt ⊢; dsimp only at hnt ⊢
        rw [if_pos rfl, evaluateHOLFiniteState_skip] at hnt ⊢; dsimp only at hnt ⊢
        rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
        have hargs_as : evalListHOLFinite s2 (h := fun a => Classical.propDecidable (s2.memaddrs a))
            [.var .local (ofString "sgl"), .var .local (ofString "gl")] =
            some [.val (.word sglw), .val (.word glw)] := by
          rw [evalListHOLFinite_eq_toExact]
          simp [evalListHOLExact, evalHOLExact, hs2_sgl, hs2_gl]
        rw [hargs_as] at hnt ⊢; dsimp only at hnt ⊢
        have hs2_code : s2.code = originalRuntimeCode := hcode
        rcases hl_as : lookupCodeHOLFinite s2.code.lookup (ofString "add_sat")
            [.val (.word sglw), .val (.word glw)] with _ | ⟨body_as, cal_as, ret_as⟩
        · dsimp only; exact herr_abs
        · dsimp only at hnt ⊢
          by_cases hclk0 : s2.clock = 0
          · simp [hl_as, hclk0] at hnt
          · simp only [hclk0, ↓reduceIte] at hnt ⊢
            have hl_as_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "add_sat")
                [.val (.word sglw), .val (.word glw)] = some (body_as, cal_as, ret_as) := by
              rwa [← hs2_code]
            obtain ⟨rfl, rfl, w_a, w_b, hvals_eq, hcal_a, hcal_b⟩ :=
              two_word_arg_lookup (by decide) lookup_add_sat hl_as_orig
            injection hvals_eq with hv1 hrest_v
            injection hv1 with hv1'; injection hv1' with hw_a; subst hw_a
            injection hrest_v with hv2 _
            injection hv2 with hv2'; injection hv2' with hw_b; subst hw_b
            have hsafe_as := evaluate_readOnlyProg opRoCallees opRoCallees_good
              (sourceFnBody Guest.Software.guestFn_add_sat) rfl
              (callEntryStateHOLFinite s2 cal_as) hs2_code
            rcases hrun_as : evaluateHOLFiniteState (callEntryStateHOLFinite s2 cal_as)
                (sourceFnBody Guest.Software.guestFn_add_sat) with ⟨res_as, st_as⟩
            simp only [hl_as, hclk0, ↓reduceIte, hrun_as] at hnt hsafe_as ⊢
            cases res_as with
            | none => dsimp only; exact herr_abs
            | some r0_as =>
              cases r0_as with
              | timeOut => simp at hnt
              | «break» | «continue» | error => dsimp only; exact herr_abs
              | finalFfi _ =>
                dsimp only
                intro hres; rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
              | exception eid_as ev_as =>
                dsimp only
                intro hres
                rcases hres with ⟨_, h⟩ | ⟨eid', ev', h, hne_st⟩
                · cases h
                · injection h with h'; injection h' with h1 _; subst h1
                  have hlf_as : R14Shards.OpHandlersA.LocFrame (callEntryStateHOLFinite s2 cal_as) st_as :=
                    hsafe_as.to_resumes (Or.inr ⟨_, ev_as, rfl, hne_st⟩)
                  set post : PanSemStateFiniteExact 64 F := { st_as.emptyLocalsHOLFinite with
                    locals := (st_as.emptyLocalsHOLFinite.locals.resVarEq (ofString "gl", s1.locals.lookup (ofString "gl"))).resVarEq
                      (ofString "sgl", s.locals.lookup (ofString "sgl")) }
                  have hp_eq : post = { s with locals := post.locals, clock := st_as.clock } := by
                    have h1 : post = { st_as with locals := post.locals, clock := st_as.clock } := rfl
                    have h2 : st_as = { callEntryStateHOLFinite s2 cal_as with locals := st_as.locals, clock := st_as.clock } := hlf_as
                    rw [h1, h2]; rfl
                  have hBp : EvmMsgReadyMsgBounded post := by
                    rw [hp_eq]; exact localsFree_evmMsgReadyMsgBounded s _ _ hB
                  have hstep : EvmStep [] s post :=
                    ⟨evmInv_of_msgBounded hBp, by rw [hp_eq]; exact Nat.le_refl _,
                     fun _ _ => by rw [hp_eq], by rw [hp_eq]; exact evmChain_with_locals s _ _⟩
                  have hcc : ChainCellsAgree s post := by
                    intro ec _; rw [hp_eq]; exact ⟨rfl, rfl, rfl, rfl⟩
                  refine ⟨hBp, ⟨hstep, hcc⟩, ?_, ?_⟩
                  · change post.globals = s.globals; rw [hp_eq]
                  · change memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112); rw [hp_eq]; rfl
              | returned v_as =>
                have hlf_as : R14Shards.OpHandlersA.LocFrame (callEntryStateHOLFinite s2 cal_as) st_as :=
                  hsafe_as.to_resumes (Or.inl ⟨v_as, rfl⟩)
                obtain ⟨totw, rfl, htot_le⟩ := add_sat_body_le_sum_d0 (callEntryStateHOLFinite s2 cal_as) sglw glw
                  hcal_a hcal_b v_as (by rw [hrun_as])
                have hsh_ok : (shapeEqHOL (shapeOfHOLExact (.val (.word totw) : ValueHOL 64)) .one &&
                    shapeEqHOL (shapeOfHOLExact (.val (.word totw) : ValueHOL 64)) .one) = true := by
                  simp [shapeOfHOLExact, shapeEqHOL]
                have hsh_ok' : (shapeEqHOL (shapeOfHOLExact (.val (.word totw) : ValueHOL 64)) .one &&
                    shapeEqHOL .one (shapeOfHOLExact (.val (.word totw) : ValueHOL 64))) = true := by
                  simp [shapeOfHOLExact, shapeEqHOL]
                dsimp only at hnt ⊢
                simp only [hsh_ok, hsh_ok', ↓reduceIte] at hnt ⊢
                set s3 := setVarHOLFinite (ofString "tot") (.val (.word totw)) { st_as with locals := s2.locals } with hs3
                have hs3_eq_s : s3 = { s with locals := s3.locals, clock := st_as.clock } := by
                  have h1 : s3 = { st_as with locals := s3.locals, clock := st_as.clock } := rfl
                  have h2 : st_as = { callEntryStateHOLFinite s2 cal_as with locals := st_as.locals, clock := st_as.clock } := hlf_as
                  rw [h1, h2]; rfl
                have hs3_mem : s3.memory = s.memory := by rw [hs3_eq_s]
                have hs3_glob : s3.globals = s.globals := by rw [hs3_eq_s]
                have hs3_code : s3.code = s.code := by rw [hs3_eq_s]
                have hs3_ma : s3.memaddrs = s.memaddrs := by rw [hs3_eq_s]
                have hs3_sh : s3.shMemaddrs = s.shMemaddrs := by rw [hs3_eq_s]
                have hs3_ba : s3.baseAddr = s.baseAddr := by rw [hs3_eq_s]
                have hs3_be : s3.be = s.be := by rw [hs3_eq_s]
                have hs3_tot : s3.locals.lookup (ofString "tot") = some (.val (.word totw)) := by
                  simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                have hs3_amt : s3.locals.lookup (ofString "amount") = some (.val (.word amtw)) := by
                  simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_amt,
                    show ofString "tot" ≠ ofString "amount" by decide]
                have hs3_sgl : s3.locals.lookup (ofString "sgl") = some (.val (.word sglw)) := by
                  simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_sgl,
                    show ofString "tot" ≠ ofString "sgl" by decide]
                have hs3_gl : s3.locals.lookup (ofString "gl") = some (.val (.word glw)) := by
                  simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_gl,
                    show ofString "tot" ≠ ofString "gl" by decide]
                have hs3_evw : s3.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
                  rw [hs3_glob]; exact hevw
                rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
                by_cases hge2 : ¬ (totw < amtw)
                · have hamt_le_tot : amtw.toNat ≤ totw.toNat := by rw [BitVec.lt_def] at hge2; omega
                  have hcmp2 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
                      (.cmp .notLower (.var .local (ofString "tot")) (.var .local (ofString "amount"))) =
                      some (.val (.word 1)) := by
                    simp [evalHOLExact, hs3_tot, hs3_amt, Compiler.Encoders.Asm.wordCmpHOL, hge2]
                  rw [hcmp2] at hnt ⊢; dsimp only at hnt ⊢
                  rw [if_neg h10] at hnt ⊢
                  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
                  have hsub_ev : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
                      (.op .sub [.var .local (ofString "amount"), .var .local (ofString "sgl")]) =
                      some (.val (.word (amtw - sglw))) := by
                    simp only [evalHOLExact, evalListHOLExact, hs3_amt, hs3_sgl, wordOpHOL, wordOp, valueIsWord, valueWord,
                      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte]
                  rw [hsub_ev] at hnt ⊢; dsimp only at hnt ⊢
                  rw [if_pos (hsh_w (amtw - sglw))] at hnt ⊢; dsimp only at hnt ⊢
                  set remw := amtw - sglw
                  have hrem_nat : remw.toNat = amtw.toNat - sglw.toNat :=
                    BitVec.toNat_sub_of_le (BitVec.le_def.2 (by omega))
                  have hrem_le_gl : remw.toNat ≤ glw.toNat := by omega
                  set s4 := setVarHOLFinite (ofString "rem") (.val (.word remw)) s3 with hs4
                  have hs4_gl : s4.locals.lookup (ofString "gl") = some (.val (.word glw)) := by
                    simp [hs4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_gl,
                      show ofString "rem" ≠ ofString "gl" by decide]
                  have hs4_rem : s4.locals.lookup (ofString "rem") = some (.val (.word remw)) := by
                    simp [hs4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
                  rcases hst_72 : evaluateHOLFiniteState s4
                      (.store (.op .add [.var .global (ofString "ev"), .const 72]) (.const 0)) with ⟨r_72, s5⟩
                  simp only [hst_72] at hnt ⊢
                  cases r_72 with
                  | some res_72 =>
                    have herr := store_some_eq_error_d0 hst_72; subst herr
                    dsimp only; exact herr_abs
                  | none =>
                    dsimp only at hnt ⊢
                    obtain ⟨w_72, _, hs5_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s4) (post := s5)
                      (gname := "ev") (gbase := globN s "ev") (off := 72) hs3_evw hevw_nat (by omega)
                      (fun v hv => by simp [evalHOLExact] at hv; exact ⟨0, hv.symm⟩) hst_72
                    rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
                    rcases hst_64 : evaluateHOLFiniteState s5
                        (.store (.op .add [.var .global (ofString "ev"), .const 64])
                          (.op .sub [.var .local (ofString "gl"), .var .local (ofString "rem")])) with ⟨r_64, s6⟩
                    simp only [hst_64] at hnt ⊢
                    cases r_64 with
                    | some res_64 =>
                      have herr := store_some_eq_error_d0 hst_64; subst herr
                      dsimp only; exact herr_abs
                    | none =>
                      dsimp only at hnt ⊢
                      obtain ⟨w_64, hw_64_ev, hs6_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s5) (post := s6)
                        (gname := "ev") (gbase := globN s "ev") (off := 64)
                        (by rw [hs5_eq]; exact hs3_evw) hevw_nat (by omega)
                        (fun v hv => by
                          have h5_gl : s5.locals.lookup (ofString "gl") = some (.val (.word glw)) := by
                            rw [hs5_eq]; exact hs4_gl
                          have h5_rem : s5.locals.lookup (ofString "rem") = some (.val (.word remw)) := by
                            rw [hs5_eq]; exact hs4_rem
                          simp [evalHOLExact, evalListHOLExact, h5_gl, h5_rem, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
                          exact ⟨_, hv.symm⟩) hst_64
                      have hw_64_val : w_64 = glw - remw := by
                        have h5_gl : s5.locals.lookup (ofString "gl") = some (.val (.word glw)) := by
                          rw [hs5_eq]; exact hs4_gl
                        have h5_rem : s5.locals.lookup (ofString "rem") = some (.val (.word remw)) := by
                          rw [hs5_eq]; exact hs4_rem
                        simp [evalHOLExact, evalListHOLExact, h5_gl, h5_rem, wordOpHOL, wordOp, valueIsWord, valueWord] at hw_64_ev
                        exact hw_64_ev.symm
                      subst hw_64_val
                      rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
                      rcases hst_192 : evaluateHOLFiniteState s6
                          (.store (.op .add [.var .global (ofString "ev"), .const 192])
                            (.op .add
                              [.load .one (.op .add [.var .global (ofString "ev"), .const 192]),
                               .var .local (ofString "rem")])) with ⟨r_192, s7⟩
                      simp only [hst_192] at hnt ⊢
                      cases r_192 with
                      | some res_192 =>
                        have herr := store_some_eq_error_d0 hst_192; subst herr
                        dsimp only; exact herr_abs
                      | none =>
                        dsimp only at hnt ⊢
                        have hs6_192_mem : s6.memory (evw + 192#64) = s.memory (evw + 192#64) := by
                          rw [hs6_eq, hs5_eq]
                          have hn64 : evw + 192#64 ≠ BitVec.ofNat 64 (globN s "ev" + 64) := by rw [hev192]; intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
                          have hn72 : evw + 192#64 ≠ BitVec.ofNat 64 (globN s "ev" + 72) := by rw [hev192]; intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
                          simp only [R14Shards.OpHandlersA.updW, hn64, hn72, ↓reduceIte]
                          change s3.memory (evw + 192#64) = s.memory (evw + 192#64)
                          exact congrFun hs3_mem _
                        obtain ⟨w_192, hw_192_ev, hs7_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s6) (post := s7)
                          (gname := "ev") (gbase := globN s "ev") (off := 192)
                          (by rw [hs6_eq, hs5_eq]; exact hs3_evw) hevw_nat (by omega)
                          (fun v hv => by
                            simp only [evalHOLExact, wordOpHOL] at hv; revert hv
                            rcases @evalListHOLExact 64 F _ s6.toExact (fun a => Classical.propDecidable (s6.memaddrs a)) _ with _ | vs
                            · simp
                            · dsimp only; split
                              · simp only [Option.map]
                                rcases wordOp .add (vs.map valueWord) with _ | w
                                · simp
                                · intro hv; injection hv with hv'; exact ⟨w, hv'.symm⟩
                              · simp) hst_192
                        have hw_192_le : w_192.toNat ≤ memW s (globN s "ev" + 192) + remw.toNat := by
                          have h6_rem : s6.locals.lookup (ofString "rem") = some (.val (.word remw)) := by
                            rw [hs6_eq, hs5_eq]; exact hs4_rem
                          have h6_evw : s6.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
                            rw [hs6_eq, hs5_eq]; exact hs3_evw
                          rcases hm192_s : s.memory (evw + 192#64) with ⟨spw⟩
                          have hm192_6 : s6.memory (evw + 192#64) = .word spw := hs6_192_mem.trans hm192_s
                          have hw_wf1 : isWfShapeExactHOL s6.structs ShapeHOL.one = true := by
                            simp [isWfShapeExactHOL]
                          have h192_c : (192 : BitVec 64) = 192#64 := rfl
                          have h0_c : (0 : BitVec 64) = 0#64 := rfl
                          by_cases hdom192 : s6.memaddrs (evw + 192#64)
                          · simp only [evalHOLExact, evalListHOLExact, h6_rem, h6_evw, h192_c, h0_c, hm192_6, hdom192,
                              memLoadHOLExact, hw_wf1, wordOpHOL, wordOp, valueIsWord, valueWord, List.map,
                              Option.map, List.all, Bool.and_self, List.foldr, BitVec.add_zero, ↓reduceIte] at hw_192_ev
                            injection hw_192_ev with hw1; injection hw1 with hw2; injection hw2 with hw_eq
                            subst hw_eq
                            have hspw_nat : spw.toNat = memW s (globN s "ev" + 192) := by
                              unfold memW; rw [← hev192, hm192_s]
                            rw [← hspw_nat, BitVec.toNat_add]
                            exact Nat.mod_le _ _
                          · simp only [evalHOLExact, evalListHOLExact, h6_rem, h6_evw, h192_c, h0_c, hm192_6, hdom192,
                              memLoadHOLExact, hw_wf1, wordOpHOL, wordOp, valueIsWord, valueWord, List.map,
                              Option.map, List.all, Bool.and_self, List.foldr, BitVec.add_zero, ↓reduceIte] at hw_192_ev
                            cases hw_192_ev
                        rw [evaluateHOLFiniteState_return] at hnt ⊢; dsimp only [evalHOLExact] at hnt ⊢
                        have hsz0 : sizeOfShapeWithContextHOL s7.structs
                            (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
                          simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
                        rw [if_pos hsz0] at hnt ⊢; dsimp only at hnt ⊢
                        intro _
                        let post : PanSemStateFiniteExact 64 F := { s7.emptyLocalsHOLFinite with
                          locals := (((s7.emptyLocalsHOLFinite.locals.resVarEq (ofString "rem", s3.locals.lookup (ofString "rem"))).resVarEq
                            (ofString "tot", s2.locals.lookup (ofString "tot"))).resVarEq
                            (ofString "gl", s1.locals.lookup (ofString "gl"))).resVarEq
                            (ofString "sgl", s.locals.lookup (ofString "sgl")) }
                        have hp_meta : post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ post.shMemaddrs = s.shMemaddrs ∧ post.baseAddr = s.baseAddr ∧ post.globals = s.globals ∧ post.be = s.be := by
                          have h7 : s7.code = s3.code ∧ s7.memaddrs = s3.memaddrs ∧ s7.shMemaddrs = s3.shMemaddrs ∧ s7.baseAddr = s3.baseAddr ∧ s7.globals = s3.globals ∧ s7.be = s3.be := by
                            rw [hs7_eq, hs6_eq, hs5_eq]; simp [hs4, setVarHOLFinite]
                          exact ⟨h7.1.trans hs3_code, h7.2.1.trans hs3_ma, h7.2.2.1.trans hs3_sh,
                            h7.2.2.2.1.trans hs3_ba, h7.2.2.2.2.1.trans hs3_glob, h7.2.2.2.2.2.trans hs3_be⟩
                        have hGp : GuestInv post := guestInv_congr hp_meta.1 hp_meta.2.1 hp_meta.2.2.1 hp_meta.2.2.2.1 hInv.1.1
                        have hmem_out : ∀ x : BitVec 64,
                            (∀ off' ∈ headGasUpdateOffs, x ≠ BitVec.ofNat 64 (globN s "ev" + off')) →
                            post.memory x = s.memory x := by
                          intro x hx
                          change s7.memory x = s.memory x
                          rw [hs7_eq, hs6_eq, hs5_eq]
                          have hn192 : x ≠ BitVec.ofNat 64 (globN s "ev" + 192) := hx 192 (by decide)
                          have hn64 : x ≠ BitVec.ofNat 64 (globN s "ev" + 64) := hx 64 (by decide)
                          have hn72 : x ≠ BitVec.ofNat 64 (globN s "ev" + 72) := hx 72 (by decide)
                          simp only [R14Shards.OpHandlersA.updW, hn192, hn64, hn72, ↓reduceIte]
                          change s3.memory x = s.memory x
                          exact congrFun hs3_mem x
                        have hm64_post : memW post (globN s "ev" + 64) = memW s (globN s "ev" + 64) - remw.toNat := by
                          change memW s7 (globN s "ev" + 64) = _
                          rw [hs7_eq, R14Shards.OpHandlersA.memW_updW_ne s6 _ _ w_192 (by omega) (by omega) (by omega),
                              hs6_eq, R14Shards.OpHandlersA.memW_updW_same s5 _ (glw - remw),
                              BitVec.toNat_sub_of_le (BitVec.le_def.2 hrem_le_gl), hglw_eq]
                        have hm192_post : memW post (globN s "ev" + 192) = w_192.toNat := by
                          change memW s7 (globN s "ev" + 192) = _
                          rw [hs7_eq, R14Shards.OpHandlersA.memW_updW_same s6 _ w_192]
                        obtain ⟨hBp, hstepCC, h112⟩ := evmMsgReadyMsgBounded_of_head_gas_mem hB hGp hp_meta.2.2.2.2.1 hp_meta.2.2.2.2.2 hmem_out
                          (by rw [hm64_post, hm192_post]; omega)
                        exact ⟨hBp, hstepCC, hp_meta.2.2.2.2.1, h112⟩
                · have hcmp2 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
                      (.cmp .notLower (.var .local (ofString "tot")) (.var .local (ofString "amount"))) =
                      some (.val (.word 0)) := by
                    simp [evalHOLExact, hs3_tot, hs3_amt, Compiler.Encoders.Asm.wordCmpHOL, hge2]
                  rw [hcmp2] at hnt ⊢; dsimp only at hnt ⊢
                  rw [if_pos rfl, evaluateHOLFiniteState_skip] at hnt ⊢; dsimp only at hnt ⊢
                  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_raise] at hnt ⊢
                  dsimp only [evalHOLExact] at hnt ⊢
                  cases hs3_esh : s3.eshapes.lookup (ofString "EvmErr") with
                  | none => dsimp only; exact herr_abs
                  | some sh =>
                    dsimp only
                    by_cases hcond : shapeOfHOLExact (.val (.word (4 : BitVec 64))) = sh ∧
                        sizeOfShapeWithContextHOL s3.structs (shapeOfHOLExact (.val (.word (4 : BitVec 64)))) ≤ 32
                    · rw [if_pos hcond]; dsimp only
                      intro _
                      set post : PanSemStateFiniteExact 64 F := { s3.emptyLocalsHOLFinite with
                        locals := ((s3.emptyLocalsHOLFinite.locals.resVarEq (ofString "tot", s2.locals.lookup (ofString "tot"))).resVarEq
                          (ofString "gl", s1.locals.lookup (ofString "gl"))).resVarEq
                          (ofString "sgl", s.locals.lookup (ofString "sgl")) }
                      have hp_eq : post = { s with locals := post.locals, clock := st_as.clock } := by
                        have h1 : post = { st_as with locals := post.locals, clock := st_as.clock } := rfl
                        have h2 : st_as = { callEntryStateHOLFinite s2 cal_as with locals := st_as.locals, clock := st_as.clock } := hlf_as
                        rw [h1, h2]; rfl
                      have hBp : EvmMsgReadyMsgBounded post := by
                        rw [hp_eq]; exact localsFree_evmMsgReadyMsgBounded s _ _ hB
                      have hstep : EvmStep [] s post :=
                        ⟨evmInv_of_msgBounded hBp, by rw [hp_eq]; exact Nat.le_refl _,
                         fun _ _ => by rw [hp_eq], by rw [hp_eq]; exact evmChain_with_locals s _ _⟩
                      have hcc : ChainCellsAgree s post := by
                        intro ec _; rw [hp_eq]; exact ⟨rfl, rfl, rfl, rfl⟩
                      refine ⟨hBp, ⟨hstep, hcc⟩, ?_, ?_⟩
                      · change post.globals = s.globals; rw [hp_eq]
                      · change memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112); rw [hp_eq]; rfl
                    · rw [if_neg hcond]; dsimp only; exact herr_abs

/-! ## 4. `funSpec_warm_address_msgBounded` -/

private theorem head_frame_addr_role_props_d0 {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hInv : EvmInvAt s S) :
    let t0 := memW s (globN s "ev" + 168)
    t0 ∈ S ∧
    (∀ (i : Nat) (_hi : i + 1 < (evmChain s).length), ¬ DelExclusive s S (evmChain s) i t0) ∧
    (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t0) ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
    globN s "bal_accounts" ≠ t0 ∧
    (∀ ad ∈ balRecords s, memW s ad ≠ t0) ∧
    (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) ∧
    (globN s "ws" ≠ 0 → memW s (globN s "ws" + 16) ≠ t0) ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 48) ≠ t0) ∧
    (globN s "ts" ≠ 0 → memW s (globN s "ts" + 48) ≠ t0) := by
  dsimp only
  set t0 := memW s (globN s "ev" + 168)
  obtain ⟨⟨hT, _, _, _⟩, hch_ne, _, _, hFW_all, _, _, _, _, _, _, hRoles, _⟩ := hInv
  have hch_cons : ∃ tail, evmChain s = (globN s "ev", globN s "cur_cont") :: tail := ⟨_, rfl⟩
  obtain ⟨chTail, hch⟩ := hch_cons
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by rw [hch]; exact List.mem_cons_self
  have ht0_S : t0 ∈ S := (hFW_all _ hhead).2.2.2.2.2.2.2.2.1
  have ht0_pos : 0 < t0 := by
    have := ((hT.2.1 t0 ht0_S).1.1 (t0, 88) (by simp [htabFootprint])).1.1
    have hsb : 0 < sourceBase := by decide
    dsimp at this; omega
  have hnot_world_role : ∀ rname : String, rname ≠ "frame.addr" → (t0, rname) ∉ worldRoleSlots s := by
    intro rname hr_ne hmem
    have hpw : (worldRoleSlots s ++ frameRoleSlots s (evmChain s)).Pairwise
        (fun a b => a.1 = b.1 → a.2 = b.2 ∧ a.2 ∈ sharedRoles) := hRoles.2.1
    have hcross := (List.pairwise_append.1 hpw).2.2 (t0, rname) hmem (t0, "frame.addr")
      (by
        unfold frameRoleSlots
        exact List.mem_flatMap.2 ⟨(globN s "ev", globN s "cur_cont"), hhead, by simp [t0]⟩)
      rfl
    exact hr_ne hcross.1
  refine ⟨ht0_S, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi hdel
    have h0_lt : 0 < (evmChain s).length := by omega
    have hch0 : (evmChain s)[0].1 = globN s "ev" := by simp [hch]
    have h168 := hdel.2 0 h0_lt 168 (by decide) (by rw [hch0])
    omega
  · intro hws heq
    apply hnot_world_role "ws+32" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    unfold recRoles; simp [hws, heq]
  · intro hbs heq
    apply hnot_world_role "bs+32" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
    unfold recRoles; simp [hbs, heq]
  · intro heq
    apply hnot_world_role "bal_accounts" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_right; simp [heq]
  · intro ad had heq
    apply hnot_world_role "bal.stor" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_right
    exact List.mem_flatMap.2 ⟨ad, had, by simp [heq]⟩
  · intro hts heq
    apply hnot_world_role "ts+32" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_right
    unfold recRoles; simp [hts, heq]
  · intro hws heq
    apply hnot_world_role "ws+16" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    unfold recRoles; simp [hws, heq]
  · intro hbs heq
    apply hnot_world_role "bs+48" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
    unfold recRoles; simp [hbs, heq]
  · intro hts heq
    apply hnot_world_role "ts+48" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_right
    unfold recRoles; simp [hts, heq]

private theorem three_one_word_call_args_wa_d0 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (fn : MlS) (e1 e2 e3 : ExpHOL 64)
    (body : ProgHOL 64) (retShape : ShapeHOL)
    (p1 p2 p3 : MlS)
    (hcode : s.code.lookup fn = some ([(p1, .one), (p2, .one), (p3, .one)], body, retShape))
    (hok : (evaluateHOLFiniteState s (.call (some (none, none)) fn [e1, e2, e3])).1 ≠ some .error) :
    ∃ w1 w2 w3 : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 = some (.val (.word w1)) ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 = some (.val (.word w2)) ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e3 = some (.val (.word w3)) := by
  rw [evaluateHOLFiniteState_call] at hok
  rcases hv1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | v1
  · simp [evalListHOLFinite, evalListHOLExact, hv1] at hok
  · rcases hv2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 with _ | v2
    · simp [evalListHOLFinite, evalListHOLExact, hv1, hv2] at hok
    · rcases hv3 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e3 with _ | v3
      · simp [evalListHOLFinite, evalListHOLExact, hv1, hv2, hv3] at hok
      · have hevl : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1, e2, e3] =
            some [v1, v2, v3] := by
          simp [evalListHOLFinite, evalListHOLExact, hv1, hv2, hv3]
        rw [hevl] at hok; dsimp only at hok
        rcases hl : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fn [v1, v2, v3] with _ | ⟨b, c, rs⟩
        · rw [hl] at hok; exact absurd rfl hok
        · have hraw : lookupCodeHOLExact s.code.lookup fn [v1, v2, v3] ≠ none := by
            intro hn
            unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
            split at hl
            · simp at hl
            · rename_i hsome; rw [hn] at hsome; simp at hsome
          simp only [lookupCodeHOLExact, hcode, List.length_cons, List.length_nil, ↓reduceIte,
            List.zip, List.zipWith, List.all, Bool.and_true, Bool.and_eq_true] at hraw
          have hshapes : shapeEqHOL .one (shapeOfHOLExact v1) = true ∧
              shapeEqHOL .one (shapeOfHOLExact v2) = true ∧
              shapeEqHOL .one (shapeOfHOLExact v3) = true := by
            by_contra hns; simp [hns] at hraw
          have hw : ∀ v : ValueHOL 64, shapeEqHOL .one (shapeOfHOLExact v) = true → ∃ w, v = .val (.word w) := by
            intro v hsv
            rcases v with ⟨⟨w⟩⟩ | _ | _
            · exact ⟨w, rfl⟩
            · simp [shapeOfHOLExact, shapeEqHOL] at hsv
            · simp [shapeOfHOLExact, shapeEqHOL] at hsv
          obtain ⟨w1, rfl⟩ := hw v1 hshapes.1
          obtain ⟨w2, rfl⟩ := hw v2 hshapes.2.1
          obtain ⟨w3, rfl⟩ := hw v3 hshapes.2.2
          exact ⟨w1, w2, w3, rfl, rfl, rfl⟩

private theorem typed_code_root_after_htab_exit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    (g : String) (sz k : Nat)
    (htr : (g, sz) ∈ typedRecords) (hk_in : k + 8 ≤ sz) (hk8 : k % 8 = 0)
    (hAs : ArenaReady s) (hW : WorldTyped s S)
    (ht : locN s "t" ∈ S) (hgnz : globN s g ≠ 0)
    (hx : HtabExit s post) :
    memW post (globN s g + k) = memW s (globN s g + k) := by
  have hi : (globN s g, sz) ∈ fixedObjects s := by
    have hm := R10Shards.GbodyProcessMsg.typedRecord_mem_fixedObjects s htr
    simpa [hgnz] using hm
  have hpos : sz ≠ 0 := by omega
  have hw := ((hW.2.2.1.1 _ hi).resolve_left hpos).2
  have hal : globN s g % 8 = 0 := hw.1
  apply fixed_word_after_htab_exit _ (globN s g, sz) hAs hW ht hi
  · unfold Inside; dsimp; omega
  · omega
  · exact hx

theorem funSpec_warm_address_msgBounded :
    FunSpec EvmMsgReadyMsgBounded
      (fun s r post => Resumes r →
        EvmMsgReadyMsgBounded post ∧ EvmStepCC ["heap_ptr"] s post ∧
          memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112))
      (ofString "warm_address") := by
  refine ⟨_, _, _, R16Shards.OpHandlersB.lookup_warm_address, ?_⟩
  intro F s hcode hB _ hnt hres
  have hnc := evaluate_noCatchableRaise R16Shards.OpHandlersB.warmAccessNcrCallees
    R16Shards.OpHandlersB.warmAccessNcrCallees_good
    (sourceFnBody Guest.Software.guestFn_warm_address) (by decide) s hcode
  have hret_ex : ∃ v_ret,
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_warm_address)).1 =
        some (.returned v_ret) := by
    rcases hres with ⟨v_ret, hv⟩ | ⟨eid, ev, hev, hne_tr⟩
    · exact ⟨v_ret, hv⟩
    · exact False.elim (hnc eid ev hne_tr hev)
  obtain ⟨v_ret, hret⟩ := hret_ex
  obtain ⟨hAs, hM, S, hInvAt, hm_s, hC⟩ := hB
  have hInv : EvmInv s := ⟨hAs, S, hInvAt⟩
  have hb_wa : sourceFnBody Guest.Software.guestFn_warm_address =
      .seq
        (.call (some (none, none)) (ofString "htab_set")
          [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 168)]),
           .var .local (ofString "addr"), .const (BitVec.ofNat 64 1)])
        (.return (.const (BitVec.ofNat 64 0))) := rfl
  rw [hb_wa] at hret ⊢
  rcases hrun_c : evaluateHOLFiniteState s
      (.seq
        (.call (some (none, none)) (ofString "htab_set")
          [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 168)]),
           .var .local (ofString "addr"), .const (BitVec.ofNat 64 1)])
        (.return (.const (BitVec.ofNat 64 0)))) with ⟨res_c, post_c⟩
  have hret' : res_c = some (.returned v_ret) := by
    have := hret; rw [hrun_c] at this; exact this
  subst hret'
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780] at hrun_c
  rcases hc_set : evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set")
        [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 168)]),
         .var .local (ofString "addr"), .const (BitVec.ofNat 64 1)]) with ⟨r_set, s2⟩
  rw [hc_set] at hrun_c
  cases r_set with
  | some rs =>
    dsimp only at hrun_c
    exfalso
    have hrs_ret : rs = .returned v_ret := Option.some.inj (Prod.mk.inj hrun_c).1
    rw [evaluateHOLFiniteState_call] at hc_set
    split at hc_set
    · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
    · split at hc_set
      · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
      · split at hc_set
        · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
        · split at hc_set
          · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
          · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
          · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
          · split at hc_set
            · simp at hc_set
            · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
          · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
          · rename_i other _ _ heq_other _ _
            have h1 := Option.some.inj (Prod.mk.inj hc_set).1
            rw [hrs_ret] at h1; subst h1; exact heq_other v_ret rfl
  | none =>
    dsimp only at hrun_c
    rw [evaluateHOLFiniteState_return] at hrun_c
    have hev0_s2 : @evalHOLExact 64 F _ s2.toExact
        (fun a => Classical.propDecidable (s2.memaddrs a)) (.const (BitVec.ofNat 64 0)) =
        some (.val (.word 0)) := rfl
    have hsz0_s2 : sizeOfShapeWithContextHOL s2.structs
        (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) ≤ 32 := by
      simp [shapeOfHOLExact]
    rw [hev0_s2] at hrun_c; dsimp only at hrun_c; rw [if_pos hsz0_s2] at hrun_c
    injection hrun_c with _ hpost_c
    obtain ⟨tw, kw, vw, htw_ev, hkw_ev, hvw_ev⟩ :=
      three_one_word_call_args_wa_d0 s (ofString "htab_set")
        (.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 168)]))
        (.var .local (ofString "addr")) (.const (BitVec.ofNat 64 1))
        _ _ (ofString "t") (ofString "key") (ofString "value")
        (by rw [hcode]; exact SoloHtabSet.lookup_htab_set)
        (by rw [hc_set]; simp)
    obtain ⟨hb_ev, evw, hevw_lk, hevw_nat⟩ := ev_word_bounds hInv
    have htw_nat : tw.toNat = memW s (globN s "ev" + 168) := by
      have had_eq : @evalHOLExact 64 F _ s.toExact
          (fun a => Classical.propDecidable (s.memaddrs a))
          (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 168)]) =
          some (.val (.word (BitVec.ofNat 64 (globN s "ev" + 168)))) := by
        simp only [evalHOLExact, evalListHOLExact, hevw_lk, wordOpHOL, wordOp, valueIsWord, valueWord,
          List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr, BitVec.add_zero]
        congr 3
        apply BitVec.eq_of_toNat_eq
        have hz0 : (0 : BitVec 64).toNat = 0 := rfl
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hevw_nat, hz0, Nat.add_zero,
          Nat.mod_eq_of_lt (show 168 < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (show globN s "ev" + 168 < 2 ^ 64 by omega)]
      unfold evalHOLExact at htw_ev
      rw [had_eq] at htw_ev; dsimp only at htw_ev
      unfold memLoadHOLExact at htw_ev
      split at htw_ev
      · split at htw_ev
        · injection htw_ev with htw_m
          unfold memW
          cases hm_cell : s.memory (BitVec.ofNat 64 (globN s "ev" + 168)) with
          | word cw =>
            change ValueHOL.val (s.memory (BitVec.ofNat 64 (globN s "ev" + 168))) = .val (.word tw) at htw_m
            rw [hm_cell] at htw_m
            injection htw_m with htw_m; injection htw_m with htw_m; subst htw_m; rfl
        · cases htw_ev
      · cases htw_ev
    rw [evaluateHOLFiniteState_call] at hc_set
    have hargs_set : evalListHOLFinite s
        (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 168)]),
         .var .local (ofString "addr"), .const (BitVec.ofNat 64 1)] =
        some [.val (.word tw), .val (.word kw), .val (.word vw)] := by
      simp [evalListHOLFinite, evalListHOLExact, htw_ev, hkw_ev, hvw_ev]
    have hlook_set := pan_three_word_lookup s.code.lookup (ofString "htab_set")
      (ofString "t") (ofString "key") (ofString "value")
      (sourceFnBody Guest.Software.guestFn_htab_set) tw kw vw
      (by decide) (by decide) (by decide)
      (by rw [hcode]; exact SoloHtabSet.lookup_htab_set)
    rw [hargs_set] at hc_set; dsimp only at hc_set
    rw [hlook_set] at hc_set; dsimp only at hc_set
    by_cases hclk_s : s.clock = 0
    · rw [if_pos hclk_s] at hc_set; simp at hc_set
    · rw [if_neg hclk_s] at hc_set
      let cmap_s : HolFiniteMapExact MlS (ValueHOL 64) :=
        ((HolFiniteMapExact.empty.update (ofString "t", ValueHOL.val (.word tw))).update
          (ofString "key", ValueHOL.val (.word kw))).update (ofString "value", ValueHOL.val (.word vw))
      let entry_s := callEntryStateHOLFinite s cmap_s
      rcases hb_set : evaluateHOLFiniteState entry_s (sourceFnBody Guest.Software.guestFn_htab_set) with
        ⟨r_bs, cpost_s⟩
      have hb_set' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap_s)
          (sourceFnBody Guest.Software.guestFn_htab_set) = (r_bs, cpost_s) := hb_set
      rw [hb_set'] at hc_set
      have hr_bs_ret : ∃ rv_bs, r_bs = some (.returned rv_bs) ∧ s2 = { cpost_s with locals := s.locals } := by
        cases r_bs with
        | none => simp at hc_set
        | some rbi =>
          cases rbi with
          | returned rv_bs =>
            dsimp only at hc_set
            split at hc_set
            · exact ⟨rv_bs, rfl, (Prod.mk.inj hc_set).2.symm⟩
            · simp at hc_set
          | _ => simp at hc_set
      obtain ⟨rv_bs, rfl, hs2_eq⟩ := hr_bs_ret
      obtain ⟨ht0_S, ht0_ndel, ht0_nws32, ht0_nbs32, ht0_nba, ht0_nad, ht0_nts32,
        ht0_nws16, ht0_nbs48, ht0_nts48⟩ := head_frame_addr_role_props_d0 hInvAt
      have hcal_t : entry_s.locals.lookup (ofString "t") = some (.val (.word tw)) := by
        have h1 : ofString "value" ≠ ofString "t" := by decide
        have h2 : ofString "key" ≠ ofString "t" := by decide
        simp [entry_s, cmap_s, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h1, h2, Ne.symm h1, Ne.symm h2]
      have hloc_ts : locN entry_s "t" = memW s (globN s "ev" + 168) := by
        simp [locN, hcal_t, htw_nat]
      have hAe : ArenaReady entry_s := localsFree_arenaReady s _ _ hAs
      have hWe : WorldTyped entry_s S := (worldTyped_with_locals s _ _ S).2 hInvAt.1
      have hInvAt_e : EvmInvAt entry_s S := (evmInvAt_with_locals s _ _ S).2 hInvAt
      have hArg_s : HtabArgWF entry_s := by
        refine ⟨hAe, ?_, ?_⟩
        · rw [hloc_ts]; exact (hWe.1.2.1 _ ht0_S).1
        · rw [hloc_ts]; intro i hi; exact ((hWe.1.2.1 _ ht0_S).2 i hi).1
      have hhl_entry : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "htab_set")
          [.val (.word tw), .val (.word kw), .val (.word vw)] =
          some (sourceFnBody Guest.Software.guestFn_htab_set, entry_s.locals, .one) := by
        rw [← hcode]; exact hlook_set
      obtain ⟨params_sp, body_sp, rs_sp, hlk_spec, hfn_spec⟩ := SoloHtabSet.htab_set_spec_proof
      have hbody_eq : ([(ofString "t", ShapeHOL.one), (ofString "key", ShapeHOL.one), (ofString "value", ShapeHOL.one)],
          sourceFnBody Guest.Software.guestFn_htab_set, ShapeHOL.one) = (params_sp, body_sp, rs_sp) :=
        Option.some.inj (SoloHtabSet.lookup_htab_set.symm.trans hlk_spec)
      rcases Prod.mk.inj hbody_eq with ⟨_, hbr⟩
      rcases Prod.mk.inj hbr with ⟨hb_eq, hrs_eq⟩
      subst hb_eq hrs_eq
      have hexit_s := hfn_spec entry_s hcode hArg_s ⟨_, hhl_entry⟩
        (by rw [hb_set]; simp) rv_bs (by rw [hb_set])
      have hbe_s : cpost_s.be = s.be := by
        have hbe0 := evaluate_be_eq entry_s (sourceFnBody Guest.Software.guestFn_htab_set)
        rw [hb_set] at hbe0; exact hbe0
      have hcpost_eq : (evaluateHOLFiniteState entry_s (sourceFnBody Guest.Software.guestFn_htab_set)).2 = cpost_s := by
        rw [hb_set]
      rw [hcpost_eq] at hexit_s
      have hexit_full : HtabExit entry_s cpost_s := hexit_s
      unfold HtabExit at hexit_s; dsimp only at hexit_s
      rw [hloc_ts] at hexit_s
      obtain ⟨hAp_s, hwf_s, hhdr0_s, _, hhp_s, hfp_s, hfr_s, hg_s⟩ := hexit_s
      obtain ⟨hInv_cs, hch_cs, _, hu_ec⟩ := evmInvAt_of_htab_step
        hAs hInvAt hAp_s hbe_s hwf_s hhdr0_s hhp_s hfp_s hfr_s
        (fun k hk => hg_s k (fun h => hk (by simp at h; simp [h])))
        (by
          have hjn : globN cpost_s "journal_n" = globN entry_s "journal_n" :=
            globN_eq_of_lookup_eq (hg_s (ofString "journal_n") (by decide)).symm
          have hjn_ent : globN entry_s "journal_n" = globN s "journal_n" := rfl
          omega)
        ht0_S ht0_ndel ht0_nws32 ht0_nbs32 ht0_nba ht0_nad (Or.inl ht0_nts32)
      have hgN : ∀ g : String, ofString g ≠ ofString "heap_ptr" → globN cpost_s g = globN s g := by
        intro g hgne
        have hlk := hg_s (ofString g) (by simp [hgne])
        unfold globN; rw [← hlk]; rfl
      have hec_words : ∀ ec ∈ evmChain s,
          (∀ off, off + 8 ≤ 280 → off % 8 = 0 → memW cpost_s (ec.1 + off) = memW s (ec.1 + off)) ∧
          (∀ off, off + 8 ≤ 104 → off % 8 = 0 → memW cpost_s (ec.2 + off) = memW s (ec.2 + off)) := by
        intro ec hec
        have hFW := hInvAt.2.2.2.2.1 ec hec
        obtain ⟨hb1, hb2, _, _⟩ := EvmStepLemmas.frameWF_bounds hAs.2 hFW
        have he1_8 : ec.1 % 8 = 0 := (hFW.1 (ec.1, 280) (by simp)).2.1
        have he2_8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
        obtain ⟨hu1, hu2⟩ := hu_ec ec hec
        refine ⟨fun off hoff hoff8 => ?_, fun off hoff hoff8 => ?_⟩
        · exact R16Shards.memW_eq_of_ivlUnhit hu1 (by omega) hb1 ⟨by omega, by omega⟩
        · exact R16Shards.memW_eq_of_ivlUnhit hu2 (by omega) hb2 ⟨by omega, by omega⟩
      have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
        have hcons : ∃ tl, evmChain s = (globN s "ev", globN s "cur_cont") :: tl := ⟨_, rfl⟩
        obtain ⟨tl, htl⟩ := hcons; rw [htl]; exact List.mem_cons_self
      have h112_cs : memW cpost_s (globN s "ev" + 112) = memW s (globN s "ev" + 112) :=
        (hec_words _ hhead_mem).1 112 (by omega) (by omega)
      have hm_cs : MsgOwned cpost_s S (memW cpost_s (globN cpost_s "ev" + 112)) := by
        have hhead_cs : (globN s "ev", globN s "cur_cont") ∈ evmChain cpost_s := by
          rw [hch_cs]; exact hhead_mem
        have hFW_cs := hInv_cs.2.2.2.2.1 _ hhead_cs
        simpa [hgN "ev" (by decide)] using hFW_cs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      have ht_ent : locN entry_s "t" ∈ S := by rw [hloc_ts]; exact ht0_S
      have hroot_eq : ∀ g k, (g, k) ∈ ([("ws", 16), ("bs", 48), ("ts", 48)] : List (String × Nat)) →
          globN s g ≠ 0 → memW cpost_s (globN s g + k) = memW s (globN s g + k) := by
        intro g k hgk hgnz
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk
        rcases hgk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact typed_code_root_after_htab_exit (s := entry_s) (post := cpost_s) "ws" 40 16
            (by decide) (by omega) (by omega) hAe hWe ht_ent hgnz hexit_full
        · exact typed_code_root_after_htab_exit (s := entry_s) (post := cpost_s) "bs" 80 48
            (by decide) (by omega) (by omega) hAe hWe ht_ent hgnz hexit_full
        · exact typed_code_root_after_htab_exit (s := entry_s) (post := cpost_s) "ts" 72 48
            (by decide) (by omega) (by omega) hAe hWe ht_ent hgnz hexit_full
      have hroot_ne_t0 : ∀ g k, (g, k) ∈ ([("ws", 16), ("bs", 48), ("ts", 48)] : List (String × Nat)) →
          globN s g ≠ 0 → memW s (globN s g + k) ≠ memW s (globN s "ev" + 168) := by
        intro g k hgk hgnz
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk
        rcases hgk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ht0_nws16 hgnz
        · exact ht0_nbs48 hgnz
        · exact ht0_nts48 hgnz
      have hroot_in_S : ∀ g k, (g, k) ∈ ([("ws", 16), ("bs", 48), ("ts", 48)] : List (String × Nat)) →
          globN s g ≠ 0 → memW s (globN s g + k) ≠ 0 → memW s (globN s g + k) ∈ S := by
        intro g k hgk hgnz hnz
        have hrin : RootIn S (memW s (globN s g + k)) := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk
          rcases hgk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hInvAt.1.1.2.2.2.1 16 (by decide) hgnz
          · exact hInvAt.1.1.2.2.2.2.1 48 (by decide) hgnz
          · exact hInvAt.1.1.2.2.2.2.2.1 48 (by decide) hgnz
        exact hrin.resolve_left hnz
      have hC_cs : CodeDbPayloadBoundedNz cpost_s S := by
        intro g k hgk hgnz_p hdb_nz_p
        have hg_eq : globN cpost_s g = globN s g := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk
          rcases hgk with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact hgN _ (by decide)
        rw [hg_eq] at hgnz_p hdb_nz_p ⊢
        rw [hroot_eq g k hgk hgnz_p] at hdb_nz_p ⊢
        have hdb_S := hroot_in_S g k hgk hgnz_p hdb_nz_p
        have hne_t0 := hroot_ne_t0 g k hgk hgnz_p
        have hne_ent : memW s (globN s g + k) ≠ locN entry_s "t" := by rw [hloc_ts]; exact hne_t0
        have hnba_ent : globN entry_s "bal_accounts" ≠ locN entry_s "t" := by rw [hloc_ts]; exact ht0_nba
        have hnad_ent : ∀ ad ∈ balRecords entry_s, memW entry_s ad ≠ locN entry_s "t" := by
          intro ad had; rw [hloc_ts]; exact ht0_nad ad had
        exact codeDbPayloadBounded_of_nonbal_htab_exit (s := entry_s) (post := cpost_s) (memW s (globN s g + k))
          ((codeDbPayloadBounded_with_locals_clock s S _ cmap_s (s.clock - 1)).2 (hC g k hgk hgnz_p hdb_nz_p))
          hAe hWe hdb_S ht_ent hne_ent hexit_full ⟨hnba_ent, hnad_ent⟩
      have hM_cs : MsgDisjCodeStrong cpost_s := by
        intro g k hgk hgnz_p hdb_nz_p p hp
        have hg_eq : globN cpost_s g = globN s g := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk
          rcases hgk with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact hgN _ (by decide)
        rw [hg_eq] at hgnz_p hdb_nz_p hp
        rw [hroot_eq g k hgk hgnz_p] at hdb_nz_p hp
        have hdb_S := hroot_in_S g k hgk hgnz_p hdb_nz_p
        have hne_t0 := hroot_ne_t0 g k hgk hgnz_p
        have htw_ent : HtabWF entry_s (locN entry_s "t") := by rw [hloc_ts]; exact (hWe.1.2.1 _ ht0_S).1
        have hdj_ent : ∀ i ∈ htabFootprint entry_s (memW s (globN s g + k)),
            ∀ j ∈ htabFootprint entry_s (locN entry_s "t"), Disj i j := by
          rw [hloc_ts]; exact hWe.1.2.2.1 _ hdb_S _ ht0_S hne_t0
        have hv_eq : htabValues cpost_s (memW s (globN s g + k)) =
            htabValues entry_s (memW s (globN s g + k)) :=
          htabValues_eq_of_htab_exit (s := entry_s) (post := cpost_s) (memW s (globN s g + k))
            (hWe.1.2.1 _ hdb_S).1 htw_ent
            (fun i hi => ((hWe.1.2.1 _ hdb_S).2 i hi).1) hAe hexit_full hdj_ent
        rw [hv_eq] at hp
        rw [hgN "ev" (by decide), h112_cs]
        exact hM g k hgk hgnz_p hdb_nz_p p hp
      have hB_cs : EvmMsgReadyMsgBounded cpost_s := ⟨hAp_s, hM_cs, S, hInv_cs, hm_cs, hC_cs⟩
      have hpost_eq : post_c = { cpost_s with locals := post_c.locals, clock := cpost_s.clock } := by
        rw [← hpost_c, hs2_eq]; rfl
      have hB_p : EvmMsgReadyMsgBounded post_c := by
        rw [hpost_eq]; exact localsFree_evmMsgReadyMsgBounded cpost_s _ _ hB_cs
      have hch_p : evmChain post_c = evmChain s := by
        rw [hpost_eq]; exact (evmChain_with_locals cpost_s _ _).trans hch_cs
      have hstep_p : EvmStep ["heap_ptr"] s post_c := by
        refine ⟨evmInv_of_msgBounded hB_p, ?_, ?_, hch_p⟩
        · rw [hpost_eq]; exact hhp_s
        · intro k hk; rw [hpost_eq]; exact hg_s k hk
      have hcc_p : ChainCellsAgree s post_c := by
        intro ec hec
        obtain ⟨he_w, hc_w⟩ := hec_words ec hec
        rw [hpost_eq]
        exact ⟨he_w 24 (by omega) (by omega), he_w 32 (by omega) (by omega),
          he_w 40 (by omega) (by omega), hc_w 56 (by omega) (by omega)⟩
      have h112_p : memW post_c (globN s "ev" + 112) = memW s (globN s "ev" + 112) := by
        rw [hpost_eq]; exact h112_cs
      exact ⟨hB_p, ⟨hstep_p, hcc_p⟩, h112_p⟩

/-! ## 5. `D0CallPostB` and `Hoare` call wrappers for `D0PreB` -/

/-- Strengthened `D0CallPost` for `D0PreB`: fall-through preserves `D0PreB ∧ L`, while a resuming
exception preserves `EvmMsgReadyMsgBounded ∧ StepFromCC`. -/
def D0CallPostB (gw : List String) (hp : Nat) (G : MlS → Option (ValueHOL 64))
    (ch : List Ivl) (cells : List (Nat × Nat × Nat × Nat))
    (L : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) :
    ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop :=
  fun r t => (r = none → D0PreB gw hp G ch cells t ∧ L t) ∧
    (Resumes r → EvmMsgReadyMsgBounded t ∧ StepFromCC gw hp G ch cells t)

/-- Generic handler-free destination-free call of a `FunSpec EvmMsgReadyMsgBounded` callee inside
a `D0PreB ∧ L` sequence, yielding `D0CallPostB` (so it chains directly with `Hoare.seq`). -/
theorem hoare_d0PreB_call0_step {gw gw_c : List String} {hp : Nat}
    {G : MlS → Option (ValueHOL 64)} {ch : List Ivl} {cells : List (Nat × Nat × Nat × Nat)}
    {L : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {fname : MlS}
    (hL : ∀ {F : Type} (s t : PanSemStateFiniteExact 64 F), t.locals = s.locals → L s → L t)
    (hsub : ∀ g ∈ gw_c, g ∈ gw)
    (hev : ofString "ev" ∉ gw_c.map ofString)
    (hf : FunSpec EvmMsgReadyMsgBounded
      (fun s r post => Resumes r →
        EvmMsgReadyMsgBounded post ∧ EvmStepCC gw_c s post ∧
          memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112)) fname)
    (arguments : List (ExpHOL 64)) :
    Hoare (fun s => D0PreB gw hp G ch cells s ∧ L s)
      (.call (some (none, none)) fname arguments)
      (D0CallPostB gw hp G ch cells L) := by
  refine ⟨fun {F} s hcode ⟨hD, hLs⟩ hnt => ?_⟩
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite s
      (h := fun address => Classical.propDecidable (s.memaddrs address)) arguments with
    _ | values
  · simp only [hargs]
    exact ⟨(fun h => by cases h), fun h => absurd h EvmFrameSpecs.not_resumes_error⟩
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · simp only [hl]
      exact ⟨(fun h => by cases h), fun h => absurd h EvmFrameSpecs.not_resumes_error⟩
    · simp only [hl] at hnt ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hBe : EvmMsgReadyMsgBounded (callEntryStateHOLFinite s callee) :=
          localsFree_evmMsgReadyMsgBounded s callee (s.clock - 1) hD.1.1
        have hSe : StepFromCC gw hp G ch cells (callEntryStateHOLFinite s callee) :=
          localsFree_stepFromCC gw hp G ch cells s callee (s.clock - 1) hD.1.2
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        simp only [hrun] at hnt ⊢
        have hQc (hsafe : res ≠ some .timeOut) (hres : Resumes res) :
            EvmMsgReadyMsgBounded post ∧ StepFromCC gw hp G ch cells post ∧
              post.globals.lookup (ofString "ev") = s.globals.lookup (ofString "ev") ∧
              memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112) := by
          have hsp := FunSpec.at_lookup hf s hcode values body' callee ret' hl hBe
            (by rw [hrun]; exact hsafe)
          rw [hrun] at hsp
          obtain ⟨hBp, hstep_c, h112_c⟩ := hsp hres
          have hSp := stepFromCC_of_evmStepCC hsub hSe hstep_c
          have hev_p : post.globals.lookup (ofString "ev") = s.globals.lookup (ofString "ev") :=
            (hstep_c.1.2.2.1 (ofString "ev") hev).symm
          exact ⟨hBp, hSp, hev_p, h112_c⟩
        cases res with
        | none =>
          exact ⟨(fun h => by cases h), fun h => absurd h EvmFrameSpecs.not_resumes_error⟩
        | some r =>
          cases r with
          | returned v =>
            dsimp only
            split
            · refine ⟨fun _ => ?_, fun h => absurd h (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h)⟩
              obtain ⟨hBp, hSp, hev_p, h112_p⟩ := hQc (by simp) (Or.inl ⟨v, rfl⟩)
              have hBt : EvmMsgReadyMsgBounded { post with locals := s.locals } :=
                localsFree_evmMsgReadyMsgBounded post s.locals post.clock hBp
              have hSt : StepFromCC gw hp G ch cells { post with locals := s.locals } :=
                localsFree_stepFromCC gw hp G ch cells post s.locals post.clock hSp
              exact ⟨d0PreB_of_stepFromCC gw hp G ch cells hD hBt hSt rfl hev_p h112_p,
                hL s { post with locals := s.locals } rfl hLs⟩
            · exact ⟨(fun h => by cases h), fun h => absurd h EvmFrameSpecs.not_resumes_error⟩
          | timeOut => simp at hnt
          | exception e v =>
            dsimp only
            refine ⟨(fun h => by cases h), fun hres => ?_⟩
            obtain ⟨hBp, hSp, _, _⟩ := hQc (by simp) hres
            exact ⟨localsFree_evmMsgReadyMsgBounded post _ post.clock hBp,
              localsFree_stepFromCC gw hp G ch cells post _ post.clock hSp⟩
          | error =>
            exact ⟨(fun h => by cases h), fun h => absurd h EvmFrameSpecs.not_resumes_error⟩
          | _ =>
            exact ⟨(fun h => by cases h),
              fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h⟩

/-- Sequence a `D0CallPostB` call before a `Fall` continuation. -/
theorem hoare_d0PreB_seq_call {gw : List String} {hp : Nat}
    {G : MlS → Option (ValueHOL 64)} {ch : List Ivl} {cells : List (Nat × Nat × Nat × Nat)}
    {L : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {c tail : ProgHOL 64}
    (hc : Hoare (fun s => D0PreB gw hp G ch cells s ∧ L s) c (D0CallPostB gw hp G ch cells L))
    (htail : Hoare (fun s => D0PreB gw hp G ch cells s ∧ L s) tail
      (Fall (fun s => EvmMsgReadyMsgBounded s ∧ StepFromCC gw hp G ch cells s))) :
    Hoare (fun s => D0PreB gw hp G ch cells s ∧ L s) (.seq c tail)
      (Fall (fun s => EvmMsgReadyMsgBounded s ∧ StepFromCC gw hp G ch cells s)) := by
  refine Hoare.seq (R := fun s => D0PreB gw hp G ch cells s ∧ L s) (Hoare.weaken hc ?_) htail
  intro F r t ⟨h1, h2⟩
  refine ⟨h1, fun hne hr => ?_⟩
  rcases hr with hr | hr
  · exact absurd hr hne
  · exact h2 hr

theorem hoare_d0PreB_call_charge_gas {gw : List String} {hp : Nat}
    {G : MlS → Option (ValueHOL 64)} {ch : List Ivl} {cells : List (Nat × Nat × Nat × Nat)}
    {L : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hL : ∀ {F : Type} (s t : PanSemStateFiniteExact 64 F), t.locals = s.locals → L s → L t)
    (args : List (ExpHOL 64)) :
    Hoare (fun s => D0PreB gw hp G ch cells s ∧ L s)
      (.call (some (none, none)) (ofString "charge_gas") args)
      (D0CallPostB gw hp G ch cells L) := by
  obtain ⟨ps, b, rs, hl, hsp⟩ := funSpec_charge_gas_msgBounded
  exact hoare_d0PreB_call0_step (gw_c := []) hL (fun _ h => nomatch h) (by decide)
    ⟨ps, b, rs, hl, fun s hc hB hex hnt hres => by
      obtain ⟨hBp, hsc, _, h112⟩ := hsp s hc hB hex hnt hres
      exact ⟨hBp, hsc, h112⟩⟩ args

theorem hoare_d0PreB_call_charge_state_gas {gw : List String} {hp : Nat}
    {G : MlS → Option (ValueHOL 64)} {ch : List Ivl} {cells : List (Nat × Nat × Nat × Nat)}
    {L : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hL : ∀ {F : Type} (s t : PanSemStateFiniteExact 64 F), t.locals = s.locals → L s → L t)
    (args : List (ExpHOL 64)) :
    Hoare (fun s => D0PreB gw hp G ch cells s ∧ L s)
      (.call (some (none, none)) (ofString "charge_state_gas") args)
      (D0CallPostB gw hp G ch cells L) := by
  obtain ⟨ps, b, rs, hl, hsp⟩ := funSpec_charge_state_gas_msgBounded
  exact hoare_d0PreB_call0_step (gw_c := []) hL (fun _ h => nomatch h) (by decide)
    ⟨ps, b, rs, hl, fun s hc hB hex hnt hres => by
      obtain ⟨hBp, hsc, _, h112⟩ := hsp s hc hB hex hnt hres
      exact ⟨hBp, hsc, h112⟩⟩ args

theorem hoare_d0PreB_call_warm_address {gw : List String} {hp : Nat}
    {G : MlS → Option (ValueHOL 64)} {ch : List Ivl} {cells : List (Nat × Nat × Nat × Nat)}
    {L : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hL : ∀ {F : Type} (s t : PanSemStateFiniteExact 64 F), t.locals = s.locals → L s → L t)
    (hhp : "heap_ptr" ∈ gw)
    (args : List (ExpHOL 64)) :
    Hoare (fun s => D0PreB gw hp G ch cells s ∧ L s)
      (.call (some (none, none)) (ofString "warm_address") args)
      (D0CallPostB gw hp G ch cells L) :=
  hoare_d0PreB_call0_step hL
    (fun g hg => by simp at hg; subst hg; exact hhp)
    (by decide)
    funSpec_warm_address_msgBounded args

end MsB4c1GasWarmRo

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
