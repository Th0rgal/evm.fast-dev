import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.Common
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.ReadOnly
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.StackPush
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.CalldataloadSpecs

/-! # OpHandlerSpec Group 04 (`OpHandlers-A`): environment & calldata opcodes -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8Contracts.M23

theorem op_address_spec : OpHandlerSpec (ofString "op_address") := by
  refine opHandlerSpec_of_run 531 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_address rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_address, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.seq_charge_gas_const (by decide)
      (HandlerRun.decCall_simple eps_address_to_u256
        (HandlerRun.seq_call_simple eps_stack_push
          (HandlerRun.seq_call_simple eps_pc_add
            (HandlerRun.ret _))))

theorem op_origin_spec : OpHandlerSpec (ofString "op_origin") := by
  refine opHandlerSpec_of_run 533 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_origin rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_origin, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.seq_charge_gas_const (by decide)
      (HandlerRun.dec_simple
        (HandlerRun.decCall_simple eps_address_to_u256
          (HandlerRun.seq_call_simple eps_stack_push
            (HandlerRun.seq_call_simple eps_pc_add
              (HandlerRun.ret _)))))

theorem op_caller_spec : OpHandlerSpec (ofString "op_caller") := by
  refine opHandlerSpec_of_run 534 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_caller rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_caller, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.seq_charge_gas_const (by decide)
      (HandlerRun.decCall_simple eps_address_to_u256
        (HandlerRun.seq_call_simple eps_stack_push
          (HandlerRun.seq_call_simple eps_pc_add
            (HandlerRun.ret _))))

theorem op_callvalue_spec : OpHandlerSpec (ofString "op_callvalue") := by
  refine opHandlerSpec_of_run 535 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_callvalue rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_callvalue, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.seq_charge_gas_const (by decide)
      (HandlerRun.seq_call_simple eps_stack_push
        (HandlerRun.seq_call_simple eps_pc_add
          (HandlerRun.ret _)))

theorem op_calldatasize_spec : OpHandlerSpec (ofString "op_calldatasize") := by
  refine opHandlerSpec_of_run 537 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_calldatasize rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_calldatasize, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.seq_charge_gas_const (by decide)
      (HandlerRun.seq_call_simple eps_stack_push_word
        (HandlerRun.seq_call_simple eps_pc_add
          (HandlerRun.ret _)))

/-! ## `extend_memory_cost1` return-value bounds -/

theorem lookup_ceil32 :
    originalRuntimeCode.lookup (ofString "ceil32") =
      some ([(ofString "v", .one)], sourceFnBody Guest.Software.guestFn_ceil32, .one) :=
  lookup_of_guestAst_getElem 442 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ceil32) rfl

theorem lookup_mul64x64 :
    originalRuntimeCode.lookup (ofString "mul64x64") =
      some ([(ofString "a", .one), (ofString "b", .one)],
        sourceFnBody Guest.Software.guestFn_mul64x64, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 59 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mul64x64) rfl

theorem lookup_memory_gas_cost :
    originalRuntimeCode.lookup (ofString "memory_gas_cost") =
      some ([(ofString "size", .one)], sourceFnBody Guest.Software.guestFn_memory_gas_cost, .one) :=
  lookup_of_guestAst_getElem 457 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memory_gas_cost) rfl

theorem lookup_extend_memory_cost1 :
    originalRuntimeCode.lookup (ofString "extend_memory_cost1") =
      some ([(ofString "start", .comb [.one, .one, .one, .one]),
             (ofString "size", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_extend_memory_cost1, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 458 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_extend_memory_cost1) rfl

theorem lookup_extend_memory :
    originalRuntimeCode.lookup (ofString "extend_memory") =
      some ([(ofString "expand_by", .one)],
        sourceFnBody Guest.Software.guestFn_extend_memory, .one) :=
  lookup_of_guestAst_getElem 460 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_extend_memory) rfl

private theorem add_sat_body_exact {F : Type} (s : PanSemStateFiniteExact 64 F) {aw bw : BitVec 64}
    (ha : s.locals.lookup (ofString "a") = some (.val (.word aw)))
    (hb : s.locals.lookup (ofString "b") = some (.val (.word bw)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_add_sat)).1 =
      some (.returned v)) :
    ∃ rw : BitVec 64, v = .val (.word rw) ∧
      rw.toNat = if aw.toNat + bw.toNat < 2 ^ 64 then aw.toNat + bw.toNat else 2 ^ 64 - 1 := by
  have hbody : sourceFnBody Guest.Software.guestFn_add_sat =
      .dec (ofString "s") .one (.op .add [.var .local (ofString "a"), .var .local (ofString "b")])
        (.seq
          (.ite (.cmp .lower (.var .local (ofString "s")) (.var .local (ofString "a")))
            (.return (.const 18446744073709551615#64))
            .skip)
          (.return (.var .local (ofString "s")))) := rfl
  rw [hbody, evaluateHOLFiniteState_dec_total] at hret; dsimp only at hret
  have hsum : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
      (.op .add [.var .local (ofString "a"), .var .local (ofString "b")]) =
      some (.val (.word (aw + bw))) := by
    simp [evalHOLExact, evalListHOLExact, ha, hb, wordOpHOL, wordOp, valueIsWord, valueWord]
  rw [hsum] at hret; dsimp only at hret
  have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word (aw + bw)))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh] at hret; dsimp only at hret
  set s1 := setVarHOLFinite (ofString "s") (.val (.word (aw + bw))) s
  have hs1_s : s1.locals.lookup (ofString "s") = some (.val (.word (aw + bw))) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_a : s1.locals.lookup (ofString "a") = some (.val (.word aw)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ha,
      show ofString "s" ≠ ofString "a" by decide]
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
  have hcmp : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
      (.cmp .lower (.var .local (ofString "s")) (.var .local (ofString "a"))) =
      some (.val (.word (if (aw + bw) < aw then 1 else 0))) := by
    simp [evalHOLExact, hs1_s, hs1_a, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp] at hret; dsimp only at hret
  have haw_lt := aw.isLt
  have hbw_lt := bw.isLt
  by_cases hlt : (aw + bw) < aw
  · have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    simp only [hlt, ↓reduceIte, h10] at hret
    rw [evaluateHOLFiniteState_return] at hret; dsimp only [evalHOLExact] at hret
    have hsz : sizeOfShapeWithContextHOL s1.structs
        (shapeOfHOLExact (.val (.word 18446744073709551615#64))) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [if_pos hsz] at hret; dsimp only at hret
    injection hret with h1; injection h1 with hv
    refine ⟨18446744073709551615#64, hv.symm, ?_⟩
    rw [BitVec.lt_def, BitVec.toNat_add] at hlt
    have hover : ¬ (aw.toNat + bw.toNat < 2 ^ 64) := by
      intro hok; rw [Nat.mod_eq_of_lt hok] at hlt; omega
    rw [if_neg hover]; decide
  · simp only [hlt, ↓reduceIte, evaluateHOLFiniteState_skip] at hret
    rw [evaluateHOLFiniteState_return] at hret
    have hev_s : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
        (.var .local (ofString "s")) = some (.val (.word (aw + bw))) := hs1_s
    rw [hev_s] at hret; dsimp only at hret
    split at hret
    · injection hret with h1; injection h1 with hv
      refine ⟨aw + bw, hv.symm, ?_⟩
      rw [BitVec.lt_def, BitVec.toNat_add] at hlt
      have hok : aw.toNat + bw.toNat < 2 ^ 64 := by
        by_contra hover
        have hmod : (aw.toNat + bw.toNat) % 2 ^ 64 = aw.toNat + bw.toNat - 2 ^ 64 := by omega
        omega
      rw [if_pos hok, BitVec.toNat_add, Nat.mod_eq_of_lt hok]
    · simp at hret

private theorem ceil32_body_exact {F : Type} (s : PanSemStateFiniteExact 64 F) {vw : BitVec 64}
    (hcode : s.code = originalRuntimeCode)
    (hv_lk : s.locals.lookup (ofString "v") = some (.val (.word vw)))
    (ret : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_ceil32)).1 =
      some (.returned ret)) :
    ∃ cw : BitVec 64, ret = .val (.word cw) ∧
      (vw.toNat ≤ 2 ^ 64 - 32 →
        cw.toNat = ((vw.toNat + 31) / 32) * 32 ∧ vw.toNat ≤ cw.toNat ∧
        cw.toNat ≤ 2 ^ 64 - 32 ∧ cw.toNat % 32 = 0 ∧ (vw.toNat % 32 = 0 → cw.toNat = vw.toNat)) ∧
      (2 ^ 64 - 31 ≤ vw.toNat → cw.toNat = 2 ^ 64 - 1) := by
  have hbody : sourceFnBody Guest.Software.guestFn_ceil32 =
      .dec (ofString "r") .one (.op .and [.var .local (ofString "v"), .const 31#64])
        (.seq
          (.ite (.cmp .equal (.var .local (ofString "r")) (.const 0#64))
            (.return (.var .local (ofString "v")))
            .skip)
          (.decCall (ofString "s") .one (ofString "add_sat")
            [.var .local (ofString "v"), .op .sub [.const 32#64, .var .local (ofString "r")]]
            (.return (.var .local (ofString "s"))))) := rfl
  rw [hbody, evaluateHOLFiniteState_dec_total] at hret; dsimp only at hret
  have hand : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
      (.op .and [.var .local (ofString "v"), .const 31#64]) =
      some (.val (.word (vw &&& 31#64))) := by
    simp [evalHOLExact, evalListHOLExact, hv_lk, wordOpHOL, wordOp, valueIsWord, valueWord]
  rw [hand] at hret; dsimp only at hret
  have hsh_r : shapeEqHOL .one (shapeOfHOLExact (.val (.word (vw &&& 31#64)))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh_r] at hret; dsimp only at hret
  set rw := vw &&& 31#64
  have hrw_nat : rw.toNat = vw.toNat % 32 := by
    change (vw &&& 31#64).toNat = vw.toNat % 32
    rw [BitVec.toNat_and, show (31#64 : BitVec 64).toNat = 2 ^ 5 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  set s1 := setVarHOLFinite (ofString "r") (.val (.word rw)) s
  have hs1_r : s1.locals.lookup (ofString "r") = some (.val (.word rw)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_v : s1.locals.lookup (ofString "v") = some (.val (.word vw)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hv_lk,
      show ofString "r" ≠ ofString "v" by decide]
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
  have hcmp : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
      (.cmp .equal (.var .local (ofString "r")) (.const 0#64)) =
      some (.val (.word (if rw = 0#64 then 1 else 0))) := by
    simp [evalHOLExact, hs1_r, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp] at hret; dsimp only at hret
  have hvw_lt := vw.isLt
  by_cases hr0 : rw = 0#64
  · have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    simp only [hr0, ↓reduceIte, h10] at hret
    rw [evaluateHOLFiniteState_return] at hret
    have hev_v : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
        (.var .local (ofString "v")) = some (.val (.word vw)) := hs1_v
    rw [hev_v] at hret; dsimp only at hret
    have hsz : sizeOfShapeWithContextHOL s1.structs
        (shapeOfHOLExact (.val (.word vw))) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [if_pos hsz] at hret; dsimp only at hret
    injection hret with h1; injection h1 with hv
    have hmod0 : vw.toNat % 32 = 0 := by rw [← hrw_nat, hr0]; rfl
    refine ⟨vw, hv.symm, ?_, ?_⟩
    · intro hle; exact ⟨by omega, le_rfl, hle, hmod0, fun _ => rfl⟩
    · intro hge; omega
  · simp only [hr0, ↓reduceIte, evaluateHOLFiniteState_skip] at hret
    have hmod_pos : 0 < vw.toNat % 32 := by
      rw [← hrw_nat]
      by_contra hz
      apply hr0
      apply BitVec.eq_of_toNat_eq
      change rw.toNat = 0; omega
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
    have hargs : evalListHOLFinite s1 (h := fun x => Classical.propDecidable (s1.memaddrs x))
        [.var .local (ofString "v"), .op .sub [.const 32#64, .var .local (ofString "r")]] =
        some [.val (.word vw), .val (.word (32#64 - rw))] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs1_v, hs1_r, wordOpHOL, wordOp, valueIsWord, valueWord]
    rw [hargs] at hret; dsimp only at hret
    have hlk := pan_two_word_lookup s1.code.lookup (ofString "add_sat") (ofString "a") (ofString "b")
      (sourceFnBody Guest.Software.guestFn_add_sat) vw (32#64 - rw) (by decide)
      (by change s.code.lookup _ = _; rw [hcode]; exact lookup_add_sat)
    rw [hlk] at hret; dsimp only at hret
    split at hret
    · simp at hret
    · let cal := (HolFiniteMapExact.empty.update (ofString "a", ValueHOL.val (.word vw))).update
        (ofString "b", ValueHOL.val (.word (32#64 - rw)))
      rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s1 cal)
          (sourceFnBody Guest.Software.guestFn_add_sat) with ⟨rb, pb⟩
      rw [hrun] at hret
      rcases rb with _ | rb
      · simp at hret
      · cases rb with
        | returned vb =>
          dsimp only at hret
          split at hret
          · dsimp only at hret
            have ha_lk : (callEntryStateHOLFinite s1 cal).locals.lookup (ofString "a") = some (.val (.word vw)) := by
              have hne : ofString "b" ≠ ofString "a" := by decide
              simp [cal, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne]
            have hb_lk : (callEntryStateHOLFinite s1 cal).locals.lookup (ofString "b") = some (.val (.word (32#64 - rw))) := by
              simp [cal, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            obtain ⟨sw, rfl, hsw_nat⟩ := add_sat_body_exact (callEntryStateHOLFinite s1 cal) ha_lk hb_lk vb
              (by rw [hrun])
            set cs := setVarHOLFinite (ofString "s") (.val (.word sw)) { pb with locals := s1.locals }
            rw [evaluateHOLFiniteState_return] at hret
            have hev_s : @evalHOLExact 64 F _ cs.toExact (fun x => Classical.propDecidable (cs.memaddrs x))
                (.var .local (ofString "s")) = some (.val (.word sw)) := by
              simp [evalHOLExact, cs, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            rw [hev_s] at hret; dsimp only at hret
            split at hret
            · injection hret with h1; injection h1 with hv
              have hsub_nat : (32#64 - rw).toNat = 32 - vw.toNat % 32 := by
                have hle_rw : rw.toNat ≤ 32 := by omega
                rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle_rw), hrw_nat]
                rfl
              rw [hsub_nat] at hsw_nat
              refine ⟨sw, hv.symm, ?_, ?_⟩
              · intro hle
                have hok : vw.toNat + (32 - vw.toNat % 32) < 2 ^ 64 := by omega
                rw [if_pos hok] at hsw_nat
                refine ⟨by omega, by omega, by omega, by omega, fun hm => by omega⟩
              · intro hge
                have hover : ¬ (vw.toNat + (32 - vw.toNat % 32) < 2 ^ 64) := by omega
                rw [if_neg hover] at hsw_nat
                exact hsw_nat
            · simp at hret
          · simp at hret
        | _ => simp at hret

private theorem eval_mul64x64_twoPow59Sub1 {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (ha : s.locals.lookup (ofString "a") = some (.val (.word (576460752303423487#64))))
    (hb : s.locals.lookup (ofString "b") = some (.val (.word (576460752303423487#64))))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_mul64x64)).1 =
      some (.returned v)) :
    v = .rStruct [.val (.word (17293822569102704641#64)), .val (.word (18014398509481983#64))] := by
  have hbody : sourceFnBody Guest.Software.guestFn_mul64x64 =
      .dec (ofString "a0") .one (.op .and [.var .local (ofString "a"), .const (4294967295#64)])
        (.dec (ofString "a1") .one (.shift .lsr (.var .local (ofString "a")) (.const (32#64)))
          (.dec (ofString "b0") .one (.op .and [.var .local (ofString "b"), .const (4294967295#64)])
            (.dec (ofString "b1") .one (.shift .lsr (.var .local (ofString "b")) (.const (32#64)))
              (.dec (ofString "p00") .one (.panop .mul [.var .local (ofString "a0"), .var .local (ofString "b0")])
                (.dec (ofString "p11") .one (.panop .mul [.var .local (ofString "a1"), .var .local (ofString "b1")])
                  (.dec (ofString "mid") (.comb [.one, .one]) (.rstruct [.const (0#64), .const (0#64)])
                    (.seq
                      (.primitive (ofString "mid") .addCarry
                        [.panop .mul [.var .local (ofString "a0"), .var .local (ofString "b1")],
                         .panop .mul [.var .local (ofString "a1"), .var .local (ofString "b0")],
                         .const (0#64)])
                      (.dec (ofString "lo") (.comb [.one, .one]) (.rstruct [.const (0#64), .const (0#64)])
                        (.seq
                          (.primitive (ofString "lo") .addCarry
                            [.var .local (ofString "p00"),
                             .shift .lsl (.rfield 0 (.var .local (ofString "mid"))) (.const (32#64)),
                             .const (0#64)])
                          (.dec (ofString "hi") .one
                            (.op .add
                              [.var .local (ofString "p11"),
                               .shift .lsr (.rfield 0 (.var .local (ofString "mid"))) (.const (32#64)),
                               .shift .lsl (.rfield 1 (.var .local (ofString "mid"))) (.const (32#64)),
                               .rfield 1 (.var .local (ofString "lo"))])
                            (.return (.rstruct [.rfield 0 (.var .local (ofString "lo")), .var .local (ofString "hi")])))))))))))) := rfl
  have hand59 : wordOpHOL .and [576460752303423487#64, 4294967295#64] = some 4294967295#64 := by decide
  have hlsr59 : wordShiftHOL .lsr 576460752303423487#64 32 = some 134217727#64 := by decide
  have hmul00 : (4294967295#64 : BitVec 64) * 4294967295#64 = 18446744065119617025#64 := by decide
  have hmul11 : (134217727#64 : BitVec 64) * 134217727#64 = 18014398241046529#64 := by decide
  have hmul01 : (4294967295#64 : BitVec 64) * 134217727#64 = 576460747874238465#64 := by decide
  have hmul10 : (134217727#64 : BitVec 64) * 4294967295#64 = 576460747874238465#64 := by decide
  have hpo_mid : panPrimopHOLExact PrimOp.addCarry
      ([.val (.word (576460747874238465#64)), .val (.word (576460747874238465#64)), .val (.word (0#64))] : List (ValueHOL 64)) =
      some (.rStruct [.val (.word (1152921495748476930#64)), .val (.word (0#64))]) := by
    simp [panPrimopHOLExact, wordAddCarryHOL]
  have hlsl_mid0 : wordShiftHOL .lsl (1152921495748476930#64) 32 = some 17293822577692639232#64 := by decide
  have hlsr_mid0 : wordShiftHOL .lsr (1152921495748476930#64) 32 = some 268435453#64 := by decide
  have hlsl0 : wordShiftHOL .lsl (0#64) 32 = some 0#64 := by decide
  have hpo_lo : panPrimopHOLExact PrimOp.addCarry
      ([.val (.word (18446744065119617025#64)), .val (.word (17293822577692639232#64)), .val (.word (0#64))] : List (ValueHOL 64)) =
      some (.rStruct [.val (.word (17293822569102704641#64)), .val (.word (1#64))]) := by
    simp [panPrimopHOLExact, wordAddCarryHOL]
  have hadd4 : wordOpHOL .add [18014398241046529#64, 268435453#64, 0#64, 1#64] = some 18014398509481983#64 := by decide
  have h32 : (32#64).toNat = 32 := rfl
  have hlk_eq {st : PanSemStateFiniteExact 64 F} (k : MlS) (u : ValueHOL 64) :
      (setVarHOLFinite k u st).locals.lookup k = some u := by
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hlk_ne {st : PanSemStateFiniteExact 64 F} (k1 k2 : MlS) (u : ValueHOL 64) (hne : k1 ≠ k2) :
      (setVarHOLFinite k1 u st).locals.lookup k2 = st.locals.lookup k2 := by
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
  have step_dec : ∀ {nm : MlS} {sh : ShapeHOL} {e : ExpHOL 64} {b : ProgHOL 64}
      {st : PanSemStateFiniteExact 64 F} {u : ValueHOL 64},
      @evalHOLExact 64 F _ st.toExact (fun x => Classical.propDecidable (st.memaddrs x)) e = some u →
      shapeEqHOL sh (shapeOfHOLExact u) = true →
      (evaluateHOLFiniteState st (.dec nm sh e b)).1 =
        (evaluateHOLFiniteState (setVarHOLFinite nm u st) b).1 := by
    intro nm sh e b st u hev hsh
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    rw [hev]; dsimp only; rw [if_pos hsh]
  have step_prim : ∀ {nm : MlS} {op : PrimOp} {args : List (ExpHOL 64)} {tl : ProgHOL 64}
      {st : PanSemStateFiniteExact 64 F} {vals : List (ValueHOL 64)} {u : ValueHOL 64},
      @evalListHOLExact 64 F _ st.toExact (fun x => Classical.propDecidable (st.memaddrs x)) args = some vals →
      panPrimopHOLExact op vals = some u →
      st.isValidValueHOLFinite .local nm u = true →
      (evaluateHOLFiniteState st (.seq (.primitive nm op args) tl)).1 =
        (evaluateHOLFiniteState (setVarHOLFinite nm u st) tl).1 := by
    intro nm op args tl st vals u hargs hpo hval
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_primitive, hargs]; dsimp only
    rw [hpo]; dsimp only; rw [if_pos hval]
  have hsh1 : ∀ w : BitVec 64, shapeEqHOL .one (shapeOfHOLExact (.val (.word w) : ValueHOL 64)) = true :=
    fun _ => by simp [shapeEqHOL, shapeOfHOLExact]
  have hsh2 : shapeEqHOL (.comb [.one, .one]) (shapeOfHOLExact (.rStruct [.val (.word (0#64)), .val (.word (0#64))] : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeEqHOL.shapeEqListHOL, shapeOfHOLExact]
  rw [hbody] at hret
  rw [step_dec (u := .val (.word 4294967295#64)) (by simp [evalHOLExact, evalListHOLExact, ha, valueIsWord, valueWord, hand59]) (hsh1 _)] at hret
  set s1 := setVarHOLFinite (ofString "a0") (.val (.word 4294967295#64)) s
  have hs1_a0 : s1.locals.lookup (ofString "a0") = some (.val (.word 4294967295#64)) := hlk_eq _ _
  have hs1_a : s1.locals.lookup (ofString "a") = some (.val (.word 576460752303423487#64)) := by
    rw [hlk_ne (ofString "a0") (ofString "a") _ (by decide)]; exact ha
  have hs1_b : s1.locals.lookup (ofString "b") = some (.val (.word 576460752303423487#64)) := by
    rw [hlk_ne (ofString "a0") (ofString "b") _ (by decide)]; exact hb
  rw [step_dec (u := .val (.word 134217727#64)) (by simp [evalHOLExact, hs1_a, h32, hlsr59]) (hsh1 _)] at hret
  set s2 := setVarHOLFinite (ofString "a1") (.val (.word 134217727#64)) s1
  have hs2_a1 : s2.locals.lookup (ofString "a1") = some (.val (.word 134217727#64)) := hlk_eq _ _
  have hs2_a0 : s2.locals.lookup (ofString "a0") = some (.val (.word 4294967295#64)) := by
    rw [hlk_ne (ofString "a1") (ofString "a0") _ (by decide)]; exact hs1_a0
  have hs2_b : s2.locals.lookup (ofString "b") = some (.val (.word 576460752303423487#64)) := by
    rw [hlk_ne (ofString "a1") (ofString "b") _ (by decide)]; exact hs1_b
  rw [step_dec (u := .val (.word 4294967295#64)) (by simp [evalHOLExact, evalListHOLExact, hs2_b, valueIsWord, valueWord, hand59]) (hsh1 _)] at hret
  set s3 := setVarHOLFinite (ofString "b0") (.val (.word 4294967295#64)) s2
  have hs3_b0 : s3.locals.lookup (ofString "b0") = some (.val (.word 4294967295#64)) := hlk_eq _ _
  have hs3_a1 : s3.locals.lookup (ofString "a1") = some (.val (.word 134217727#64)) := by
    rw [hlk_ne (ofString "b0") (ofString "a1") _ (by decide)]; exact hs2_a1
  have hs3_a0 : s3.locals.lookup (ofString "a0") = some (.val (.word 4294967295#64)) := by
    rw [hlk_ne (ofString "b0") (ofString "a0") _ (by decide)]; exact hs2_a0
  have hs3_b : s3.locals.lookup (ofString "b") = some (.val (.word 576460752303423487#64)) := by
    rw [hlk_ne (ofString "b0") (ofString "b") _ (by decide)]; exact hs2_b
  rw [step_dec (u := .val (.word 134217727#64)) (by simp [evalHOLExact, hs3_b, h32, hlsr59]) (hsh1 _)] at hret
  set s4 := setVarHOLFinite (ofString "b1") (.val (.word 134217727#64)) s3
  have hs4_b1 : s4.locals.lookup (ofString "b1") = some (.val (.word 134217727#64)) := hlk_eq _ _
  have hs4_b0 : s4.locals.lookup (ofString "b0") = some (.val (.word 4294967295#64)) := by
    rw [hlk_ne (ofString "b1") (ofString "b0") _ (by decide)]; exact hs3_b0
  have hs4_a1 : s4.locals.lookup (ofString "a1") = some (.val (.word 134217727#64)) := by
    rw [hlk_ne (ofString "b1") (ofString "a1") _ (by decide)]; exact hs3_a1
  have hs4_a0 : s4.locals.lookup (ofString "a0") = some (.val (.word 4294967295#64)) := by
    rw [hlk_ne (ofString "b1") (ofString "a0") _ (by decide)]; exact hs3_a0
  rw [step_dec (u := .val (.word 18446744065119617025#64)) (by simp [evalHOLExact, evalListHOLExact, hs4_a0, hs4_b0, valueIsWord, valueWord, panOpHOL, hmul00]) (hsh1 _)] at hret
  set s5 := setVarHOLFinite (ofString "p00") (.val (.word 18446744065119617025#64)) s4
  have hs5_p00 : s5.locals.lookup (ofString "p00") = some (.val (.word 18446744065119617025#64)) := hlk_eq _ _
  have hs5_b1 : s5.locals.lookup (ofString "b1") = some (.val (.word 134217727#64)) := by
    rw [hlk_ne (ofString "p00") (ofString "b1") _ (by decide)]; exact hs4_b1
  have hs5_b0 : s5.locals.lookup (ofString "b0") = some (.val (.word 4294967295#64)) := by
    rw [hlk_ne (ofString "p00") (ofString "b0") _ (by decide)]; exact hs4_b0
  have hs5_a1 : s5.locals.lookup (ofString "a1") = some (.val (.word 134217727#64)) := by
    rw [hlk_ne (ofString "p00") (ofString "a1") _ (by decide)]; exact hs4_a1
  have hs5_a0 : s5.locals.lookup (ofString "a0") = some (.val (.word 4294967295#64)) := by
    rw [hlk_ne (ofString "p00") (ofString "a0") _ (by decide)]; exact hs4_a0
  rw [step_dec (u := .val (.word 18014398241046529#64)) (by simp [evalHOLExact, evalListHOLExact, hs5_a1, hs5_b1, valueIsWord, valueWord, panOpHOL, hmul11]) (hsh1 _)] at hret
  set s6 := setVarHOLFinite (ofString "p11") (.val (.word 18014398241046529#64)) s5
  have hs6_p11 : s6.locals.lookup (ofString "p11") = some (.val (.word 18014398241046529#64)) := hlk_eq _ _
  have hs6_p00 : s6.locals.lookup (ofString "p00") = some (.val (.word 18446744065119617025#64)) := by
    rw [hlk_ne (ofString "p11") (ofString "p00") _ (by decide)]; exact hs5_p00
  have hs6_b1 : s6.locals.lookup (ofString "b1") = some (.val (.word 134217727#64)) := by
    rw [hlk_ne (ofString "p11") (ofString "b1") _ (by decide)]; exact hs5_b1
  have hs6_b0 : s6.locals.lookup (ofString "b0") = some (.val (.word 4294967295#64)) := by
    rw [hlk_ne (ofString "p11") (ofString "b0") _ (by decide)]; exact hs5_b0
  have hs6_a1 : s6.locals.lookup (ofString "a1") = some (.val (.word 134217727#64)) := by
    rw [hlk_ne (ofString "p11") (ofString "a1") _ (by decide)]; exact hs5_a1
  have hs6_a0 : s6.locals.lookup (ofString "a0") = some (.val (.word 4294967295#64)) := by
    rw [hlk_ne (ofString "p11") (ofString "a0") _ (by decide)]; exact hs5_a0
  rw [step_dec (u := .rStruct [.val (.word 0#64), .val (.word 0#64)]) (by simp [evalHOLExact, evalListHOLExact]) hsh2] at hret
  set s7 := setVarHOLFinite (ofString "mid") (.rStruct [.val (.word 0#64), .val (.word 0#64)]) s6
  have hs7_mid : s7.locals.lookup (ofString "mid") = some (.rStruct [.val (.word 0#64), .val (.word 0#64)]) := hlk_eq _ _
  have hs7_p11 : s7.locals.lookup (ofString "p11") = some (.val (.word 18014398241046529#64)) := by
    rw [hlk_ne (ofString "mid") (ofString "p11") _ (by decide)]; exact hs6_p11
  have hs7_p00 : s7.locals.lookup (ofString "p00") = some (.val (.word 18446744065119617025#64)) := by
    rw [hlk_ne (ofString "mid") (ofString "p00") _ (by decide)]; exact hs6_p00
  have hs7_b1 : s7.locals.lookup (ofString "b1") = some (.val (.word 134217727#64)) := by
    rw [hlk_ne (ofString "mid") (ofString "b1") _ (by decide)]; exact hs6_b1
  have hs7_b0 : s7.locals.lookup (ofString "b0") = some (.val (.word 4294967295#64)) := by
    rw [hlk_ne (ofString "mid") (ofString "b0") _ (by decide)]; exact hs6_b0
  have hs7_a1 : s7.locals.lookup (ofString "a1") = some (.val (.word 134217727#64)) := by
    rw [hlk_ne (ofString "mid") (ofString "a1") _ (by decide)]; exact hs6_a1
  have hs7_a0 : s7.locals.lookup (ofString "a0") = some (.val (.word 4294967295#64)) := by
    rw [hlk_ne (ofString "mid") (ofString "a0") _ (by decide)]; exact hs6_a0
  rw [step_prim
    (by simp [evalListHOLExact, evalHOLExact, hs7_a0, hs7_a1, hs7_b0, hs7_b1, valueIsWord, valueWord, panOpHOL, hmul01, hmul10])
    hpo_mid
    (by simp [isValidValueHOLFinite, lookupKvarHOLFinite, hs7_mid, shapeEqHOL, shapeEqHOL.shapeEqListHOL, shapeOfHOLExact])] at hret
  set s8 := setVarHOLFinite (ofString "mid") (.rStruct [.val (.word 1152921495748476930#64), .val (.word 0#64)]) s7
  have hs8_mid : s8.locals.lookup (ofString "mid") = some (.rStruct [.val (.word 1152921495748476930#64), .val (.word 0#64)]) := hlk_eq _ _
  have hs8_p11 : s8.locals.lookup (ofString "p11") = some (.val (.word 18014398241046529#64)) := by
    rw [hlk_ne (ofString "mid") (ofString "p11") _ (by decide)]; exact hs7_p11
  have hs8_p00 : s8.locals.lookup (ofString "p00") = some (.val (.word 18446744065119617025#64)) := by
    rw [hlk_ne (ofString "mid") (ofString "p00") _ (by decide)]; exact hs7_p00
  rw [step_dec (u := .rStruct [.val (.word 0#64), .val (.word 0#64)]) (by simp [evalHOLExact, evalListHOLExact]) hsh2] at hret
  set s9 := setVarHOLFinite (ofString "lo") (.rStruct [.val (.word 0#64), .val (.word 0#64)]) s8
  have hs9_lo : s9.locals.lookup (ofString "lo") = some (.rStruct [.val (.word 0#64), .val (.word 0#64)]) := hlk_eq _ _
  have hs9_mid : s9.locals.lookup (ofString "mid") = some (.rStruct [.val (.word 1152921495748476930#64), .val (.word 0#64)]) := by
    rw [hlk_ne (ofString "lo") (ofString "mid") _ (by decide)]; exact hs8_mid
  have hs9_p11 : s9.locals.lookup (ofString "p11") = some (.val (.word 18014398241046529#64)) := by
    rw [hlk_ne (ofString "lo") (ofString "p11") _ (by decide)]; exact hs8_p11
  have hs9_p00 : s9.locals.lookup (ofString "p00") = some (.val (.word 18446744065119617025#64)) := by
    rw [hlk_ne (ofString "lo") (ofString "p00") _ (by decide)]; exact hs8_p00
  rw [step_prim
    (by simp [evalListHOLExact, evalHOLExact, hs9_p00, hs9_mid, h32, hlsl_mid0])
    hpo_lo
    (by simp [isValidValueHOLFinite, lookupKvarHOLFinite, hs9_lo, shapeEqHOL, shapeEqHOL.shapeEqListHOL, shapeOfHOLExact])] at hret
  set s10 := setVarHOLFinite (ofString "lo") (.rStruct [.val (.word 17293822569102704641#64), .val (.word 1#64)]) s9
  have hs10_lo : s10.locals.lookup (ofString "lo") = some (.rStruct [.val (.word 17293822569102704641#64), .val (.word 1#64)]) := hlk_eq _ _
  have hs10_mid : s10.locals.lookup (ofString "mid") = some (.rStruct [.val (.word 1152921495748476930#64), .val (.word 0#64)]) := by
    rw [hlk_ne (ofString "lo") (ofString "mid") _ (by decide)]; exact hs9_mid
  have hs10_p11 : s10.locals.lookup (ofString "p11") = some (.val (.word 18014398241046529#64)) := by
    rw [hlk_ne (ofString "lo") (ofString "p11") _ (by decide)]; exact hs9_p11
  rw [step_dec (u := .val (.word 18014398509481983#64))
    (by simp [evalHOLExact, evalListHOLExact, hs10_p11, hs10_mid, hs10_lo, valueIsWord, valueWord, h32, hlsr_mid0, hlsl0, hadd4]) (hsh1 _)] at hret
  set s11 := setVarHOLFinite (ofString "hi") (.val (.word 18014398509481983#64)) s10
  have hs11_hi : s11.locals.lookup (ofString "hi") = some (.val (.word 18014398509481983#64)) := hlk_eq _ _
  have hs11_lo : s11.locals.lookup (ofString "lo") = some (.rStruct [.val (.word 17293822569102704641#64), .val (.word 1#64)]) := by
    rw [hlk_ne (ofString "hi") (ofString "lo") _ (by decide)]; exact hs10_lo
  rw [evaluateHOLFiniteState_return] at hret
  have hev_ret : @evalHOLExact 64 F _ s11.toExact (fun a => Classical.propDecidable (s11.memaddrs a))
      (.rstruct [.rfield 0 (.var .local (ofString "lo")), .var .local (ofString "hi")]) =
      some (.rStruct [.val (.word (17293822569102704641#64)), .val (.word 18014398509481983#64)]) := by
    simp [evalHOLExact, evalListHOLExact, hs11_lo, hs11_hi]
  rw [hev_ret] at hret; dsimp only at hret
  have hsz : sizeOfShapeWithContextHOL s11.structs
      (shapeOfHOLExact (.rStruct [.val (.word (17293822569102704641#64)), .val (.word 18014398509481983#64)] : ValueHOL 64)) ≤ 32 := by
    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
  rw [if_pos hsz] at hret; dsimp only at hret
  injection hret with h1; injection h1 with hv
  exact hv.symm

private theorem words_of_twoPow64Sub1 {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word 18446744073709551615#64)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_words_of)).1 =
      some (.returned v)) :
    v = .val (.word 576460752303423487#64) := by
  have hbody : sourceFnBody Guest.Software.guestFn_words_of =
      .decCall (ofString "c") .one (ofString "ceil32") [.var .local (ofString "n")]
        (.return (.shift .lsr (.var .local (ofString "c")) (.const 5#64))) := rfl
  rw [hbody, evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
  have hargs : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x))
      [.var .local (ofString "n")] = some [.val (.word 18446744073709551615#64)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hn]
  rw [hargs] at hret; dsimp only at hret
  have hlk := pan_one_word_lookup s.code.lookup (ofString "ceil32") (ofString "v")
    (sourceFnBody Guest.Software.guestFn_ceil32) 18446744073709551615#64
    (by rw [hcode]; exact lookup_ceil32)
  rw [hlk] at hret; dsimp only at hret
  split at hret
  · simp at hret
  · let cal := HolFiniteMapExact.empty.update (ofString "v", ValueHOL.val (.word 18446744073709551615#64))
    rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s cal)
        (sourceFnBody Guest.Software.guestFn_ceil32) with ⟨rb, pb⟩
    rw [hrun] at hret
    rcases rb with _ | rb
    · simp at hret
    · cases rb with
      | returned vb =>
        dsimp only at hret
        split at hret
        · dsimp only at hret
          have hv_lk : (callEntryStateHOLFinite s cal).locals.lookup (ofString "v") =
              some (.val (.word 18446744073709551615#64)) := by
            simp [cal, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          obtain ⟨cw, rfl, _, hhi⟩ := ceil32_body_exact (callEntryStateHOLFinite s cal) hcode hv_lk vb
            (by rw [hrun])
          have hcw_eq : cw = 18446744073709551615#64 := by
            apply BitVec.eq_of_toNat_eq
            have := hhi (by decide)
            simpa using this
          subst hcw_eq
          set cs := setVarHOLFinite (ofString "c") (.val (.word 18446744073709551615#64)) { pb with locals := s.locals }
          rw [evaluateHOLFiniteState_return] at hret
          have hcs_c : cs.locals.lookup (ofString "c") = some (.val (.word 18446744073709551615#64)) := by
            simp [cs, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have h5 : (5#64 : BitVec 64).toNat = 5 := rfl
          have hshf : wordShiftHOL .lsr 18446744073709551615#64 5 = some 576460752303423487#64 := by decide
          have hev : @evalHOLExact 64 F _ cs.toExact (fun a => Classical.propDecidable (cs.memaddrs a))
              (.shift .lsr (.var .local (ofString "c")) (.const 5#64)) =
              some (.val (.word 576460752303423487#64)) := by
            simp [evalHOLExact, hcs_c, h5, hshf]
          rw [hev] at hret; dsimp only at hret
          split at hret
          · injection hret with h1; injection h1 with hv; exact hv.symm
          · simp at hret
        · simp at hret
      | _ => simp at hret

private theorem memory_gas_cost_twoPow64Sub1 {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (hsz_lk : s.locals.lookup (ofString "size") = some (.val (.word 18446744073709551615#64)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memory_gas_cost)).1 =
      some (.returned v)) :
    v = .val (.word 18446744073709551615#64) := by
  have hbody : sourceFnBody Guest.Software.guestFn_memory_gas_cost =
      .decCall (ofString "w") .one (ofString "words_of") [.var .local (ofString "size")]
        (.decCall (ofString "sq") (.comb [.one, .one]) (ofString "mul64x64")
          [.var .local (ofString "w"), .var .local (ofString "w")]
          (.seq
            (.ite (.cmp .notEqual (.rfield 1 (.var .local (ofString "sq"))) (.const 0#64))
              (.return (.const 18446744073709551615#64))
              .skip)
            (.decCall (ofString "a") .one (ofString "add_sat")
              [.panop .mul [.var .local (ofString "w"), .const 3#64],
               .shift .lsr (.rfield 0 (.var .local (ofString "sq"))) (.const 9#64)]
              (.return (.var .local (ofString "a")))))) := rfl
  rw [hbody, evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
  have hargs1 : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x))
      [.var .local (ofString "size")] = some [.val (.word 18446744073709551615#64)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hsz_lk]
  rw [hargs1] at hret; dsimp only at hret
  have hlk1 := pan_one_word_lookup s.code.lookup (ofString "words_of") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_words_of) 18446744073709551615#64
    (by rw [hcode]; exact lookup_words_of)
  rw [hlk1] at hret; dsimp only at hret
  split at hret
  · simp at hret
  · let cal1 := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word 18446744073709551615#64))
    rcases hrun1 : evaluateHOLFiniteState (callEntryStateHOLFinite s cal1)
        (sourceFnBody Guest.Software.guestFn_words_of) with ⟨rb1, pb1⟩
    rw [hrun1] at hret
    have hpb1_code : pb1.code = originalRuntimeCode := by
      have hm := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s cal1)
        (sourceFnBody Guest.Software.guestFn_words_of)).1
      rw [hrun1] at hm; exact hm.trans hcode
    rcases rb1 with _ | rb1
    · simp at hret
    · cases rb1 with
      | returned vb1 =>
        dsimp only at hret
        split at hret
        · dsimp only at hret
          have hn1 : (callEntryStateHOLFinite s cal1).locals.lookup (ofString "n") =
              some (.val (.word 18446744073709551615#64)) := by
            simp [cal1, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hvb1 := words_of_twoPow64Sub1 (callEntryStateHOLFinite s cal1) hcode hn1 vb1 (by rw [hrun1])
          subst hvb1
          set s1 := setVarHOLFinite (ofString "w") (.val (.word 576460752303423487#64)) { pb1 with locals := s.locals }
          have hs1_w : s1.locals.lookup (ofString "w") = some (.val (.word 576460752303423487#64)) := by
            simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hs1_code : s1.code = originalRuntimeCode := hpb1_code
          rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
          have hargs2 : evalListHOLFinite s1 (h := fun x => Classical.propDecidable (s1.memaddrs x))
              [.var .local (ofString "w"), .var .local (ofString "w")] =
              some [.val (.word 576460752303423487#64), .val (.word 576460752303423487#64)] := by
            simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs1_w]
          rw [hargs2] at hret; dsimp only at hret
          have hlk2 : lookupCodeHOLFinite s1.code.lookup (ofString "mul64x64")
              [.val (.word 576460752303423487#64), .val (.word 576460752303423487#64)] =
              some (sourceFnBody Guest.Software.guestFn_mul64x64,
                (HolFiniteMapExact.empty.update (ofString "a", ValueHOL.val (.word 576460752303423487#64))).update
                  (ofString "b", ValueHOL.val (.word 576460752303423487#64)),
                .comb [.one, .one]) := by
            have hd : ofString "a" ≠ ofString "b" := by decide
            have raw : lookupCodeHOLExact s1.code.lookup (ofString "mul64x64")
                [.val (.word 576460752303423487#64), .val (.word 576460752303423487#64)] =
                some (sourceFnBody Guest.Software.guestFn_mul64x64,
                  (fun key => if key = ofString "b" then some (.val (.word 576460752303423487#64))
                    else if key = ofString "a" then some (.val (.word 576460752303423487#64)) else none),
                  .comb [.one, .one]) := by
              simp [lookupCodeHOLExact, hs1_code, lookup_mul64x64, shapeOfHOLExact, shapeEqHOL, hd]
            unfold PanSemStateFiniteExact.lookupCodeHOLFinite
            split
            · rename_i missing; rw [raw] at missing; cases missing
            · rename_i foundBody foundLocals foundShape found
              have equal := Option.some.inj (found.symm.trans raw)
              obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
              apply congrArg (fun locals => some (sourceFnBody Guest.Software.guestFn_mul64x64, locals, ShapeHOL.comb [.one, .one]))
              apply HolFiniteMapExact.ext
              funext key
              by_cases hb_k : key = ofString "b"
              · subst key; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]
              · have hb_k' : ofString "b" ≠ key := Ne.symm hb_k
                by_cases ha_k : key = ofString "a"
                · subst key; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, hd, Ne.symm hd]
                · have ha_k' : ofString "a" ≠ key := Ne.symm ha_k
                  simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, ha_k, hb_k, ha_k', hb_k']
          rw [hlk2] at hret; dsimp only at hret
          split at hret
          · simp at hret
          · let cal2 := (HolFiniteMapExact.empty.update (ofString "a", ValueHOL.val (.word 576460752303423487#64))).update
              (ofString "b", ValueHOL.val (.word 576460752303423487#64))
            rcases hrun2 : evaluateHOLFiniteState (callEntryStateHOLFinite s1 cal2)
                (sourceFnBody Guest.Software.guestFn_mul64x64) with ⟨rb2, pb2⟩
            rw [hrun2] at hret
            rcases rb2 with _ | rb2
            · simp at hret
            · cases rb2 with
              | returned vb2 =>
                dsimp only at hret
                split at hret
                · dsimp only at hret
                  have ha2 : (callEntryStateHOLFinite s1 cal2).locals.lookup (ofString "a") =
                      some (.val (.word 576460752303423487#64)) := by
                    have hne : ofString "b" ≠ ofString "a" := by decide
                    simp [cal2, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne]
                  have hb2 : (callEntryStateHOLFinite s1 cal2).locals.lookup (ofString "b") =
                      some (.val (.word 576460752303423487#64)) := by
                    simp [cal2, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  have hvb2 := eval_mul64x64_twoPow59Sub1 (callEntryStateHOLFinite s1 cal2) ha2 hb2 vb2 (by rw [hrun2])
                  subst hvb2
                  set s2 := setVarHOLFinite (ofString "sq")
                    (.rStruct [.val (.word 17293822569102704641#64), .val (.word 18014398509481983#64)]) { pb2 with locals := s1.locals }
                  have hs2_sq : s2.locals.lookup (ofString "sq") =
                      some (.rStruct [.val (.word 17293822569102704641#64), .val (.word 18014398509481983#64)]) := by
                    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
                  have hne0 : (18014398509481983#64 : BitVec 64) ≠ 0#64 := by decide
                  have h10 : ¬ ((1#64 : BitVec 64) = 0) := by decide
                  have hcmp : @evalHOLExact 64 F _ s2.toExact (fun x => Classical.propDecidable (s2.memaddrs x))
                      (.cmp .notEqual (.rfield 1 (.var .local (ofString "sq"))) (.const 0#64)) =
                      some (.val (.word 1#64)) := by
                    simp [evalHOLExact, hs2_sq, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne0]
                  rw [hcmp] at hret; dsimp only at hret
                  rw [if_neg h10] at hret
                  rw [evaluateHOLFiniteState_return] at hret; dsimp only [evalHOLExact] at hret
                  have hsz : sizeOfShapeWithContextHOL s2.structs
                      (shapeOfHOLExact (.val (.word 18446744073709551615#64))) ≤ 32 := by
                    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
                  rw [if_pos hsz] at hret; dsimp only at hret
                  injection hret with h1; injection h1 with hv; exact hv.symm
                · simp at hret
              | _ => simp at hret
        · simp at hret
      | _ => simp at hret

private theorem extend_memory_cost1_body_bounds {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_extend_memory_cost1)).1 =
      some (.returned v)) :
    ∃ cw ebw : BitVec 64,
      v = .rStruct [.val (.word cw), .val (.word ebw)] ∧
      (ebw = 0#64 ∨
        ∃ before after : Nat,
          after ≤ 2 ^ 64 - 32 ∧
          after % 32 = 0 ∧
          before < after ∧
          ebw.toNat = after - before ∧
          (memW s (globN s "ev" + 32) % 32 = 0 → before = memW s (globN s "ev" + 32))) := by
  have hbody : sourceFnBody Guest.Software.guestFn_extend_memory_cost1 =
      .decCall (ofString "z") .one (ofString "u256_is_zero") [.var .local (ofString "size")]
        (.seq
          (.ite (.cmp .notEqual (.var .local (ofString "z")) (.const 0#64))
            (.return (.rstruct [.const 0#64, .const 0#64]))
            .skip)
          (.decCall (ofString "s") .one (ofString "sat_word") [.var .local (ofString "start")]
            (.decCall (ofString "n") .one (ofString "sat_word") [.var .local (ofString "size")]
              (.decCall (ofString "endp") .one (ofString "add_sat") [.var .local (ofString "s"), .var .local (ofString "n")]
                (.seq
                  (.ite (.cmp .equal (.var .local (ofString "endp")) (.const 18446744073709551615#64))
                    (.return (.rstruct [.const 18446744073709551615#64, .const 0#64]))
                    .skip)
                  (.dec (ofString "cur") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 32#64]))
                    (.decCall (ofString "before") .one (ofString "ceil32") [.var .local (ofString "cur")]
                      (.decCall (ofString "after") .one (ofString "ceil32") [.var .local (ofString "endp")]
                        (.seq
                          (.ite (.cmp .notLower (.var .local (ofString "before")) (.var .local (ofString "after")))
                            (.return (.rstruct [.const 0#64, .const 0#64]))
                            .skip)
                          (.decCall (ofString "ca") .one (ofString "memory_gas_cost") [.var .local (ofString "after")]
                            (.decCall (ofString "cb") .one (ofString "memory_gas_cost") [.var .local (ofString "before")]
                              (.seq
                                (.ite (.cmp .equal (.var .local (ofString "ca")) (.const 18446744073709551615#64))
                                  (.return (.rstruct [.const 18446744073709551615#64, .const 0#64]))
                                  .skip)
                                (.return (.rstruct
                                  [.op .sub [.var .local (ofString "ca"), .var .local (ofString "cb")],
                                   .op .sub [.var .local (ofString "after"), .var .local (ofString "before")]])))))))))))))) := rfl
  have hret_rstruct : ∀ (st : PanSemStateFiniteExact 64 F) (w1 w2 : BitVec 64),
      evaluateHOLFiniteState st (.return (.rstruct [.const w1, .const w2])) =
        (some (.returned (.rStruct [.val (.word w1), .val (.word w2)])), st.emptyLocalsHOLFinite) := by
    intro st w1 w2
    rw [evaluateHOLFiniteState_return]
    have hev : @evalHOLExact 64 F _ st.toExact (fun x => Classical.propDecidable (st.memaddrs x))
        (.rstruct [.const w1, .const w2]) =
        some (.rStruct [.val (.word w1), .val (.word w2)]) := by
      simp [evalHOLExact, evalListHOLExact]
    rw [hev]; dsimp only
    have hsz : sizeOfShapeWithContextHOL st.structs
        (shapeOfHOLExact (.rStruct [.val (.word w1), .val (.word w2)] : ValueHOL 64)) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
    rw [if_pos hsz]
  have step_ro_call : ∀ {st : PanSemStateFiniteExact 64 F} {nm fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64},
      opRoCallees fname = true →
      st.code = originalRuntimeCode →
      LocFrame s st →
      (evaluateHOLFiniteState st (.decCall nm .one fname args cont)).1 = some (.returned v) →
      ∃ (w : BitVec 64) (st' : PanSemStateFiniteExact 64 F),
        st'.code = originalRuntimeCode ∧
        LocFrame s st' ∧
        st'.locals = st.locals.update (nm, .val (.word w)) ∧
        (∃ vals body callee rs,
          evalListHOLFinite st (h := fun x => Classical.propDecidable (st.memaddrs x)) args = some vals ∧
          lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, callee, rs) ∧
          (evaluateHOLFiniteState (callEntryStateHOLFinite st callee) body).1 = some (.returned (.val (.word w)))) ∧
        (evaluateHOLFiniteState st' cont).1 = some (.returned v) := by
    intro st nm fname args cont hfn hst_c hst_lf hr
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hr
    rcases hargs : evalListHOLFinite st (h := fun x => Classical.propDecidable (st.memaddrs x)) args with _ | vals
    · rw [hargs] at hr; simp at hr
    · rw [hargs] at hr; dsimp only at hr
      rcases hl : lookupCodeHOLFinite st.code.lookup fname vals with _ | ⟨body, callee, rs⟩
      · rw [hl] at hr; simp at hr
      · rw [hl] at hr; dsimp only at hr
        split at hr
        · simp at hr
        · have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, callee, rs) := by
            rwa [← hst_c]
          have hbody_ro := opRoCallees_good fname hfn vals body callee rs hl_orig
          have hsafe := evaluate_readOnlyProg opRoCallees opRoCallees_good body hbody_ro
            (callEntryStateHOLFinite st callee) hst_c
          rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite st callee) body with ⟨rb, pb⟩
          rw [hrun] at hr
          have hpb_c : pb.code = originalRuntimeCode := by
            have hm := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite st callee) body).1
            rw [hrun] at hm; exact hm.trans hst_c
          rcases rb with _ | rb
          · simp at hr
          · cases rb with
            | returned vb =>
              dsimp only at hr
              split at hr
              · rename_i hsh_vb
                dsimp only at hr
                have hsh_one : shapeEqHOL (shapeOfHOLExact vb) .one = true := by
                  simp [Bool.and_eq_true] at hsh_vb; exact hsh_vb.1
                rcases vb with ⟨⟨w⟩⟩ | _ | _
                · have hlf_ce : LocFrame (callEntryStateHOLFinite st callee) pb := by
                    have hres := hsafe.to_resumes (by rw [hrun]; exact Or.inl ⟨.val (.word w), rfl⟩)
                    simpa [hrun] using hres
                  have hlf_st : LocFrame st pb := by
                    unfold LocFrame at hlf_ce ⊢; rw [hlf_ce]; rfl
                  let st' := setVarHOLFinite nm (.val (.word w)) { pb with locals := st.locals }
                  have hlf_st' : LocFrame s st' :=
                    hst_lf.trans (hlf_st.with_locals_clock (st.locals.update (nm, .val (.word w))) pb.clock)
                  exact ⟨w, st', hpb_c, hlf_st', rfl,
                    ⟨vals, body, callee, rs, rfl, hl_orig, by rw [hrun]⟩, hr⟩
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh_one
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh_one
              · simp at hr
            | _ => simp at hr
  have h10 : ¬ ((1#64 : BitVec 64) = 0) := by decide
  have h00 : (0#64 : BitVec 64) = 0 := rfl
  rw [hbody] at hret
  obtain ⟨zw, s1, hs1_c, hs1_lf, hs1_loc, _, hr1⟩ :=
    step_ro_call (by decide) hcode (LocFrame.refl s) hret
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr1
  have hs1_z : s1.locals.lookup (ofString "z") = some (.val (.word zw)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hcmp_z : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
      (.cmp .notEqual (.var .local (ofString "z")) (.const 0#64)) =
      some (.val (.word (if zw ≠ 0#64 then (1#64 : BitVec 64) else 0#64))) := by
    simp [evalHOLExact, hs1_z, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp_z] at hr1; dsimp only at hr1
  by_cases hzw : zw ≠ 0#64
  · rw [if_pos hzw] at hr1; rw [if_neg h10] at hr1; rw [hret_rstruct s1 0#64 0#64] at hr1
    injection hr1 with h1; injection h1 with hv
    exact ⟨0#64, 0#64, hv.symm, Or.inl rfl⟩
  · rw [if_neg hzw] at hr1; rw [if_pos h00] at hr1; rw [evaluateHOLFiniteState_skip] at hr1; dsimp only at hr1
    obtain ⟨sw, s2, hs2_c, hs2_lf, hs2_loc, _, hr2⟩ :=
      step_ro_call (by decide) hs1_c hs1_lf hr1
    obtain ⟨nw, s3, hs3_c, hs3_lf, hs3_loc, _, hr3⟩ :=
      step_ro_call (by decide) hs2_c hs2_lf hr2
    obtain ⟨endpw, s4, hs4_c, hs4_lf, hs4_loc, _, hr4⟩ :=
      step_ro_call (by decide) hs3_c hs3_lf hr3
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr4
    have hs4_endp : s4.locals.lookup (ofString "endp") = some (.val (.word endpw)) := by
      rw [hs4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hcmp_endp : @evalHOLExact 64 F _ s4.toExact (fun x => Classical.propDecidable (s4.memaddrs x))
        (.cmp .equal (.var .local (ofString "endp")) (.const 18446744073709551615#64)) =
        some (.val (.word (if endpw = 18446744073709551615#64 then (1#64 : BitVec 64) else 0#64))) := by
      simp [evalHOLExact, hs4_endp, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [hcmp_endp] at hr4; dsimp only at hr4
    by_cases hendp : endpw = 18446744073709551615#64
    · rw [if_pos hendp] at hr4; rw [if_neg h10] at hr4; rw [hret_rstruct s4 18446744073709551615#64 0#64] at hr4
      injection hr4 with h1; injection h1 with hv
      exact ⟨18446744073709551615#64, 0#64, hv.symm, Or.inl rfl⟩
    · rw [if_neg hendp] at hr4; rw [if_pos h00] at hr4; rw [evaluateHOLFiniteState_skip] at hr4; dsimp only at hr4
      rw [evaluateHOLFiniteState_dec_total] at hr4; dsimp only at hr4
      rcases hld_cur : @evalHOLExact 64 F _ s4.toExact (fun x => Classical.propDecidable (s4.memaddrs x))
          (.load .one (.op .add [.var .global (ofString "ev"), .const 32#64])) with _ | curv
      · rw [hld_cur] at hr4; simp at hr4
      · obtain ⟨curw, rfl, hcurw_nat⟩ := evalAt_loadG_word s4 "ev" 32#64 curv hld_cur
        rw [hld_cur] at hr4; dsimp only at hr4
        have hsh_cur : shapeEqHOL .one (shapeOfHOLExact (.val (.word curw))) = true := by
          simp [shapeEqHOL, shapeOfHOLExact]
        rw [if_pos hsh_cur] at hr4; dsimp only at hr4
        have hs4_mem : s4.memory = s.memory := by unfold LocFrame at hs4_lf; conv_lhs => rw [hs4_lf]
        have hs4_glob : s4.globals = s.globals := by unfold LocFrame at hs4_lf; conv_lhs => rw [hs4_lf]
        have hcur_eq : curw.toNat = memW s (globN s "ev" + 32) := by
          have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
          rw [hcurw_nat, h32]
          simp [memW, globN, hs4_mem, hs4_glob]
        set s5 := setVarHOLFinite (ofString "cur") (.val (.word curw)) s4 with hs5_def
        have hs5_c : s5.code = originalRuntimeCode := hs4_c
        have hs5_lf : LocFrame s s5 := hs4_lf.with_locals_clock _ s4.clock
        have hs5_cur : s5.locals.lookup (ofString "cur") = some (.val (.word curw)) := by
          simp [hs5_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        obtain ⟨befw, s6, hs6_c, hs6_lf, hs6_loc, ⟨vals6, body6, cal6, rs6, hargs6, hl6, hrun6⟩, hr6⟩ :=
          step_ro_call (by decide) hs5_c hs5_lf hr4
        have hvals6 : vals6 = [.val (.word curw)] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs5_cur] at hargs6
          exact hargs6.symm
        subst hvals6
        obtain ⟨rfl, rfl, curw', hcur_inj, hcal6_v⟩ := one_word_arg_lookup lookup_ceil32 hl6
        injection hcur_inj with hcur_inj'; injection hcur_inj' with hcur_inj''; subst hcur_inj''
        have hbef_ex := ceil32_body_exact (callEntryStateHOLFinite s5 cal6) hs5_c hcal6_v
          (.val (.word befw)) hrun6
        obtain ⟨befw', hbef_inj, hbef_lo, hbef_hi⟩ := hbef_ex
        injection hbef_inj with hbef_inj'; injection hbef_inj' with hbef_inj''; subst hbef_inj''
        have hs6_endp : s6.locals.lookup (ofString "endp") = some (.val (.word endpw)) := by
          rw [hs6_loc]; simp [hs5_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs4_endp,
            show ofString "before" ≠ ofString "endp" by decide,
            show ofString "cur" ≠ ofString "endp" by decide]
        obtain ⟨aftw, s7, hs7_c, hs7_lf, hs7_loc, ⟨vals7, body7, cal7, rs7, hargs7, hl7, hrun7⟩, hr7⟩ :=
          step_ro_call (by decide) hs6_c hs6_lf hr6
        have hvals7 : vals7 = [.val (.word endpw)] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs6_endp] at hargs7
          exact hargs7.symm
        subst hvals7
        obtain ⟨rfl, rfl, endpw', hendp_inj, hcal7_v⟩ := one_word_arg_lookup lookup_ceil32 hl7
        injection hendp_inj with hendp_inj'; injection hendp_inj' with hendp_inj''; subst hendp_inj''
        obtain ⟨aftw', haft_inj, haft_lo, haft_hi⟩ := ceil32_body_exact (callEntryStateHOLFinite s6 cal7) hs6_c
          hcal7_v (.val (.word aftw)) hrun7
        injection haft_inj with haft_inj'; injection haft_inj' with haft_inj''; subst haft_inj''
        have hs7_bef : s7.locals.lookup (ofString "before") = some (.val (.word befw)) := by
          rw [hs7_loc, hs6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "after" ≠ ofString "before" by decide]
        have hs7_aft : s7.locals.lookup (ofString "after") = some (.val (.word aftw)) := by
          rw [hs7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr7
        have hcmp_ba : @evalHOLExact 64 F _ s7.toExact (fun x => Classical.propDecidable (s7.memaddrs x))
            (.cmp .notLower (.var .local (ofString "before")) (.var .local (ofString "after"))) =
            some (.val (.word (if ¬ (befw < aftw) then (1#64 : BitVec 64) else 0#64))) := by
          simp [evalHOLExact, hs7_bef, hs7_aft, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        rw [hcmp_ba] at hr7; dsimp only at hr7
        by_cases hba : ¬ (befw < aftw)
        · rw [if_pos hba] at hr7; rw [if_neg h10] at hr7; rw [hret_rstruct s7 0#64 0#64] at hr7
          injection hr7 with h1; injection h1 with hv
          exact ⟨0#64, 0#64, hv.symm, Or.inl rfl⟩
        · rw [if_neg hba] at hr7; rw [if_pos h00] at hr7; rw [evaluateHOLFiniteState_skip] at hr7; dsimp only at hr7
          have hba_lt : befw.toNat < aftw.toNat := BitVec.lt_def.1 (Classical.not_not.1 hba)
          obtain ⟨caw, s8, hs8_c, hs8_lf, hs8_loc, ⟨vals8, body8, cal8, rs8, hargs8, hl8, hrun8⟩, hr8⟩ :=
            step_ro_call (by decide) hs7_c hs7_lf hr7
          have hvals8 : vals8 = [.val (.word aftw)] := by
            simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs7_aft] at hargs8
            exact hargs8.symm
          subst hvals8
          obtain ⟨rfl, rfl, aftw_arg, haft_arg_inj, hcal8_sz⟩ := one_word_arg_lookup lookup_memory_gas_cost hl8
          injection haft_arg_inj with h1; injection h1 with h2; subst h2
          obtain ⟨cbw, s9, hs9_c, hs9_lf, hs9_loc, _, hr9⟩ :=
            step_ro_call (by decide) hs8_c hs8_lf hr8
          have hs9_ca : s9.locals.lookup (ofString "ca") = some (.val (.word caw)) := by
            rw [hs9_loc, hs8_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "cb" ≠ ofString "ca" by decide]
          have hs9_cb : s9.locals.lookup (ofString "cb") = some (.val (.word cbw)) := by
            rw [hs9_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
          have hs9_bef : s9.locals.lookup (ofString "before") = some (.val (.word befw)) := by
            rw [hs9_loc, hs8_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs7_bef,
              show ofString "cb" ≠ ofString "before" by decide,
              show ofString "ca" ≠ ofString "before" by decide]
          have hs9_aft : s9.locals.lookup (ofString "after") = some (.val (.word aftw)) := by
            rw [hs9_loc, hs8_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs7_aft,
              show ofString "cb" ≠ ofString "after" by decide,
              show ofString "ca" ≠ ofString "after" by decide]
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr9
          have hcmp_ca : @evalHOLExact 64 F _ s9.toExact (fun x => Classical.propDecidable (s9.memaddrs x))
              (.cmp .equal (.var .local (ofString "ca")) (.const 18446744073709551615#64)) =
              some (.val (.word (if caw = 18446744073709551615#64 then (1#64 : BitVec 64) else 0#64))) := by
            simp [evalHOLExact, hs9_ca, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
          rw [hcmp_ca] at hr9; dsimp only at hr9
          by_cases hca_max : caw = 18446744073709551615#64
          · rw [if_pos hca_max] at hr9; rw [if_neg h10] at hr9; rw [hret_rstruct s9 18446744073709551615#64 0#64] at hr9
            injection hr9 with h1; injection h1 with hv
            exact ⟨18446744073709551615#64, 0#64, hv.symm, Or.inl rfl⟩
          · rw [if_neg hca_max] at hr9; rw [if_pos h00] at hr9; rw [evaluateHOLFiniteState_skip] at hr9; dsimp only at hr9
            rw [evaluateHOLFiniteState_return] at hr9
            have hev_ret : @evalHOLExact 64 F _ s9.toExact (fun x => Classical.propDecidable (s9.memaddrs x))
                (.rstruct
                  [.op .sub [.var .local (ofString "ca"), .var .local (ofString "cb")],
                   .op .sub [.var .local (ofString "after"), .var .local (ofString "before")]]) =
                some (.rStruct [.val (.word (caw - cbw)), .val (.word (aftw - befw))]) := by
              simp [evalHOLExact, evalListHOLExact, hs9_ca, hs9_cb, hs9_aft, hs9_bef,
                wordOpHOL, wordOp, valueIsWord, valueWord]
            rw [hev_ret] at hr9; dsimp only at hr9
            have hsz : sizeOfShapeWithContextHOL s9.structs
                (shapeOfHOLExact (.rStruct [.val (.word (caw - cbw)), .val (.word (aftw - befw))] : ValueHOL 64)) ≤ 32 := by
              simp [shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
            rw [if_pos hsz] at hr9; dsimp only at hr9
            injection hr9 with h1; injection h1 with hv
            have hendp_le : endpw.toNat ≤ 2 ^ 64 - 32 := by
              by_contra hgt
              have haft_max_nat := haft_hi (by omega)
              have haft_max : aftw = 18446744073709551615#64 := by
                apply BitVec.eq_of_toNat_eq; simpa using haft_max_nat
              subst haft_max
              have hca_eq := memory_gas_cost_twoPow64Sub1 (callEntryStateHOLFinite s7 cal8) hs7_c hcal8_sz
                (.val (.word caw)) hrun8
              injection hca_eq with h1; injection h1 with h2
              exact hca_max h2
            have haft_eq := haft_lo hendp_le
            have haft_le : aftw.toNat ≤ 2 ^ 64 - 32 := by omega
            have haft_mod : aftw.toNat % 32 = 0 := by omega
            have hcur_le : curw.toNat ≤ 2 ^ 64 - 32 := by
              by_contra hgt
              have := hbef_hi (by omega)
              omega
            have hbef_eq := hbef_lo hcur_le
            have hsub_nat : (aftw - befw).toNat = aftw.toNat - befw.toNat :=
              BitVec.toNat_sub_of_le (BitVec.le_def.2 (Nat.le_of_lt hba_lt))
            refine ⟨caw - cbw, aftw - befw, hv.symm, Or.inr ⟨befw.toNat, aftw.toNat, haft_le, haft_mod, hba_lt, hsub_nat, ?_⟩⟩
            intro hcur_al
            rw [← hcur_eq] at hcur_al ⊢
            omega

/-- `extend_memory_cost1` is read-only and returns `[cw, ebw]` where either `ebw = 0` or
    `ebw = after - before` with `after ≤ 2^64 - 32`, `after % 32 = 0`, `before % 32 = 0`,
    and `before = mem_len` whenever `mem_len % 32 = 0`. -/
theorem eps_extend_memory_cost1_bounds :
    EvmPreservingSpec (fun _ => True)
      (fun s v post =>
        LocFrame s post ∧
        ∃ cw ebw : BitVec 64,
          v = .rStruct [.val (.word cw), .val (.word ebw)] ∧
          (ebw = 0#64 ∨
            ∃ before after : Nat,
              after ≤ 2 ^ 64 - 32 ∧
              after % 32 = 0 ∧
              before < after ∧
              ebw.toNat = after - before ∧
              (memW s (globN s "ev" + 32) % 32 = 0 → before = memW s (globN s "ev" + 32))))
      (ofString "extend_memory_cost1") := by
  obtain ⟨params, body, retShape, hlk, hro⟩ := eps_extend_memory_cost1
  have hlk_eq := lookup_extend_memory_cost1.symm.trans hlk
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_eq, rfl⟩
  subst hbody_eq
  refine ⟨_, _, _, lookup_extend_memory_cost1, ?_⟩
  intro F s hcode hInv hP hlookup hnt
  have hs := hro s hcode hInv hP hlookup hnt
  dsimp only at hs ⊢
  refine ⟨fun v hv => ?_, hs.2⟩
  obtain ⟨h1, h2, h3, hlf⟩ := hs.1 v hv
  exact ⟨h1, h2, h3, hlf, extend_memory_cost1_body_bounds s hcode v hv⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
