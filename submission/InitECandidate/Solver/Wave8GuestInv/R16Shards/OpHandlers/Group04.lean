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

private theorem eval_mul64x64_hi_nonzero {F : Type}
    (s : PanSemStateFiniteExact 64 F) {ww : BitVec 64}
    (hw_ge : 2 ^ 32 ≤ ww.toNat) (hw_lt : ww.toNat < 2 ^ 59)
    (ha : s.locals.lookup (ofString "a") = some (.val (.word ww)))
    (hb : s.locals.lookup (ofString "b") = some (.val (.word ww)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_mul64x64)).1 =
      some (.returned v)) :
    ∃ lo hi : BitVec 64, v = .rStruct [.val (.word lo), .val (.word hi)] ∧ hi ≠ 0#64 := by
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
  let a0 := ww &&& 4294967295#64
  let a1 := ww >>> (32 : Nat)
  let p00 := a0 * a0
  let p11 := a1 * a1
  let p01 := a0 * a1
  let mid := wordAddCarryHOL p01 p01 0#64
  let lo := wordAddCarryHOL p00 (mid.1 <<< (32 : Nat)) 0#64
  let hi := p11 + (mid.1 >>> (32 : Nat)) + (mid.2 <<< (32 : Nat)) + lo.2
  have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
  have hand_w : wordOpHOL .and [ww, 4294967295#64] = some a0 := rfl
  have hlsr_w : wordShiftHOL .lsr ww 32 = some a1 := by simp [wordShiftHOL, a1]
  have hpo_mid : panPrimopHOLExact PrimOp.addCarry
      ([.val (.word p01), .val (.word p01), .val (.word 0#64)] : List (ValueHOL 64)) =
      some (.rStruct [.val (.word mid.1), .val (.word mid.2)]) := by
    simp [panPrimopHOLExact, mid]
  have hlsl_mid0 : wordShiftHOL .lsl mid.1 32 = some (mid.1 <<< (32 : Nat)) := by simp [wordShiftHOL]
  have hlsr_mid0 : wordShiftHOL .lsr mid.1 32 = some (mid.1 >>> (32 : Nat)) := by simp [wordShiftHOL]
  have hlsl_mid1 : wordShiftHOL .lsl mid.2 32 = some (mid.2 <<< (32 : Nat)) := by simp [wordShiftHOL]
  have hpo_lo : panPrimopHOLExact PrimOp.addCarry
      ([.val (.word p00), .val (.word (mid.1 <<< (32 : Nat))), .val (.word 0#64)] : List (ValueHOL 64)) =
      some (.rStruct [.val (.word lo.1), .val (.word lo.2)]) := by
    simp [panPrimopHOLExact, lo]
  have hadd4 : wordOpHOL .add [p11, mid.1 >>> (32 : Nat), mid.2 <<< (32 : Nat), lo.2] = some hi := by
    simp [wordOpHOL, wordOp, hi, BitVec.add_assoc]
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
  rw [step_dec (u := .val (.word a0)) (by simp [evalHOLExact, evalListHOLExact, ha, valueIsWord, valueWord, hand_w]) (hsh1 _)] at hret
  set s1 := setVarHOLFinite (ofString "a0") (.val (.word a0)) s
  have hs1_a0 : s1.locals.lookup (ofString "a0") = some (.val (.word a0)) := hlk_eq _ _
  have hs1_a : s1.locals.lookup (ofString "a") = some (.val (.word ww)) := by
    rw [hlk_ne (ofString "a0") (ofString "a") _ (by decide)]; exact ha
  have hs1_b : s1.locals.lookup (ofString "b") = some (.val (.word ww)) := by
    rw [hlk_ne (ofString "a0") (ofString "b") _ (by decide)]; exact hb
  rw [step_dec (u := .val (.word a1)) (by simp [evalHOLExact, hs1_a, h32, hlsr_w]) (hsh1 _)] at hret
  set s2 := setVarHOLFinite (ofString "a1") (.val (.word a1)) s1
  have hs2_a1 : s2.locals.lookup (ofString "a1") = some (.val (.word a1)) := hlk_eq _ _
  have hs2_a0 : s2.locals.lookup (ofString "a0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "a1") (ofString "a0") _ (by decide)]; exact hs1_a0
  have hs2_b : s2.locals.lookup (ofString "b") = some (.val (.word ww)) := by
    rw [hlk_ne (ofString "a1") (ofString "b") _ (by decide)]; exact hs1_b
  rw [step_dec (u := .val (.word a0)) (by simp [evalHOLExact, evalListHOLExact, hs2_b, valueIsWord, valueWord, hand_w]) (hsh1 _)] at hret
  set s3 := setVarHOLFinite (ofString "b0") (.val (.word a0)) s2
  have hs3_b0 : s3.locals.lookup (ofString "b0") = some (.val (.word a0)) := hlk_eq _ _
  have hs3_a1 : s3.locals.lookup (ofString "a1") = some (.val (.word a1)) := by
    rw [hlk_ne (ofString "b0") (ofString "a1") _ (by decide)]; exact hs2_a1
  have hs3_a0 : s3.locals.lookup (ofString "a0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "b0") (ofString "a0") _ (by decide)]; exact hs2_a0
  have hs3_b : s3.locals.lookup (ofString "b") = some (.val (.word ww)) := by
    rw [hlk_ne (ofString "b0") (ofString "b") _ (by decide)]; exact hs2_b
  rw [step_dec (u := .val (.word a1)) (by simp [evalHOLExact, hs3_b, h32, hlsr_w]) (hsh1 _)] at hret
  set s4 := setVarHOLFinite (ofString "b1") (.val (.word a1)) s3
  have hs4_b1 : s4.locals.lookup (ofString "b1") = some (.val (.word a1)) := hlk_eq _ _
  have hs4_b0 : s4.locals.lookup (ofString "b0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "b1") (ofString "b0") _ (by decide)]; exact hs3_b0
  have hs4_a1 : s4.locals.lookup (ofString "a1") = some (.val (.word a1)) := by
    rw [hlk_ne (ofString "b1") (ofString "a1") _ (by decide)]; exact hs3_a1
  have hs4_a0 : s4.locals.lookup (ofString "a0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "b1") (ofString "a0") _ (by decide)]; exact hs3_a0
  rw [step_dec (u := .val (.word p00)) (by simp [evalHOLExact, evalListHOLExact, hs4_a0, hs4_b0, valueIsWord, valueWord, panOpHOL, p00]) (hsh1 _)] at hret
  set s5 := setVarHOLFinite (ofString "p00") (.val (.word p00)) s4
  have hs5_p00 : s5.locals.lookup (ofString "p00") = some (.val (.word p00)) := hlk_eq _ _
  have hs5_b1 : s5.locals.lookup (ofString "b1") = some (.val (.word a1)) := by
    rw [hlk_ne (ofString "p00") (ofString "b1") _ (by decide)]; exact hs4_b1
  have hs5_b0 : s5.locals.lookup (ofString "b0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "p00") (ofString "b0") _ (by decide)]; exact hs4_b0
  have hs5_a1 : s5.locals.lookup (ofString "a1") = some (.val (.word a1)) := by
    rw [hlk_ne (ofString "p00") (ofString "a1") _ (by decide)]; exact hs4_a1
  have hs5_a0 : s5.locals.lookup (ofString "a0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "p00") (ofString "a0") _ (by decide)]; exact hs4_a0
  rw [step_dec (u := .val (.word p11)) (by simp [evalHOLExact, evalListHOLExact, hs5_a1, hs5_b1, valueIsWord, valueWord, panOpHOL, p11]) (hsh1 _)] at hret
  set s6 := setVarHOLFinite (ofString "p11") (.val (.word p11)) s5
  have hs6_p11 : s6.locals.lookup (ofString "p11") = some (.val (.word p11)) := hlk_eq _ _
  have hs6_p00 : s6.locals.lookup (ofString "p00") = some (.val (.word p00)) := by
    rw [hlk_ne (ofString "p11") (ofString "p00") _ (by decide)]; exact hs5_p00
  have hs6_b1 : s6.locals.lookup (ofString "b1") = some (.val (.word a1)) := by
    rw [hlk_ne (ofString "p11") (ofString "b1") _ (by decide)]; exact hs5_b1
  have hs6_b0 : s6.locals.lookup (ofString "b0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "p11") (ofString "b0") _ (by decide)]; exact hs5_b0
  have hs6_a1 : s6.locals.lookup (ofString "a1") = some (.val (.word a1)) := by
    rw [hlk_ne (ofString "p11") (ofString "a1") _ (by decide)]; exact hs5_a1
  have hs6_a0 : s6.locals.lookup (ofString "a0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "p11") (ofString "a0") _ (by decide)]; exact hs5_a0
  rw [step_dec (u := .rStruct [.val (.word 0#64), .val (.word 0#64)]) (by simp [evalHOLExact, evalListHOLExact]) hsh2] at hret
  set s7 := setVarHOLFinite (ofString "mid") (.rStruct [.val (.word 0#64), .val (.word 0#64)]) s6
  have hs7_mid : s7.locals.lookup (ofString "mid") = some (.rStruct [.val (.word 0#64), .val (.word 0#64)]) := hlk_eq _ _
  have hs7_p11 : s7.locals.lookup (ofString "p11") = some (.val (.word p11)) := by
    rw [hlk_ne (ofString "mid") (ofString "p11") _ (by decide)]; exact hs6_p11
  have hs7_p00 : s7.locals.lookup (ofString "p00") = some (.val (.word p00)) := by
    rw [hlk_ne (ofString "mid") (ofString "p00") _ (by decide)]; exact hs6_p00
  have hs7_b1 : s7.locals.lookup (ofString "b1") = some (.val (.word a1)) := by
    rw [hlk_ne (ofString "mid") (ofString "b1") _ (by decide)]; exact hs6_b1
  have hs7_b0 : s7.locals.lookup (ofString "b0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "mid") (ofString "b0") _ (by decide)]; exact hs6_b0
  have hs7_a1 : s7.locals.lookup (ofString "a1") = some (.val (.word a1)) := by
    rw [hlk_ne (ofString "mid") (ofString "a1") _ (by decide)]; exact hs6_a1
  have hs7_a0 : s7.locals.lookup (ofString "a0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "mid") (ofString "a0") _ (by decide)]; exact hs6_a0
  have hp10 : a1 * a0 = p01 := BitVec.mul_comm a1 a0
  rw [step_prim
    (by simp [evalListHOLExact, evalHOLExact, hs7_a0, hs7_a1, hs7_b0, hs7_b1, valueIsWord, valueWord, panOpHOL, p01, hp10])
    hpo_mid
    (by simp [isValidValueHOLFinite, lookupKvarHOLFinite, hs7_mid, shapeEqHOL, shapeEqHOL.shapeEqListHOL, shapeOfHOLExact])] at hret
  set s8 := setVarHOLFinite (ofString "mid") (.rStruct [.val (.word mid.1), .val (.word mid.2)]) s7
  have hs8_mid : s8.locals.lookup (ofString "mid") = some (.rStruct [.val (.word mid.1), .val (.word mid.2)]) := hlk_eq _ _
  have hs8_p11 : s8.locals.lookup (ofString "p11") = some (.val (.word p11)) := by
    rw [hlk_ne (ofString "mid") (ofString "p11") _ (by decide)]; exact hs7_p11
  have hs8_p00 : s8.locals.lookup (ofString "p00") = some (.val (.word p00)) := by
    rw [hlk_ne (ofString "mid") (ofString "p00") _ (by decide)]; exact hs7_p00
  rw [step_dec (u := .rStruct [.val (.word 0#64), .val (.word 0#64)]) (by simp [evalHOLExact, evalListHOLExact]) hsh2] at hret
  set s9 := setVarHOLFinite (ofString "lo") (.rStruct [.val (.word 0#64), .val (.word 0#64)]) s8
  have hs9_lo : s9.locals.lookup (ofString "lo") = some (.rStruct [.val (.word 0#64), .val (.word 0#64)]) := hlk_eq _ _
  have hs9_mid : s9.locals.lookup (ofString "mid") = some (.rStruct [.val (.word mid.1), .val (.word mid.2)]) := by
    rw [hlk_ne (ofString "lo") (ofString "mid") _ (by decide)]; exact hs8_mid
  have hs9_p11 : s9.locals.lookup (ofString "p11") = some (.val (.word p11)) := by
    rw [hlk_ne (ofString "lo") (ofString "p11") _ (by decide)]; exact hs8_p11
  have hs9_p00 : s9.locals.lookup (ofString "p00") = some (.val (.word p00)) := by
    rw [hlk_ne (ofString "lo") (ofString "p00") _ (by decide)]; exact hs8_p00
  rw [step_prim
    (by simp [evalListHOLExact, evalHOLExact, hs9_p00, hs9_mid, h32, hlsl_mid0])
    hpo_lo
    (by simp [isValidValueHOLFinite, lookupKvarHOLFinite, hs9_lo, shapeEqHOL, shapeEqHOL.shapeEqListHOL, shapeOfHOLExact])] at hret
  set s10 := setVarHOLFinite (ofString "lo") (.rStruct [.val (.word lo.1), .val (.word lo.2)]) s9
  have hs10_lo : s10.locals.lookup (ofString "lo") = some (.rStruct [.val (.word lo.1), .val (.word lo.2)]) := hlk_eq _ _
  have hs10_mid : s10.locals.lookup (ofString "mid") = some (.rStruct [.val (.word mid.1), .val (.word mid.2)]) := by
    rw [hlk_ne (ofString "lo") (ofString "mid") _ (by decide)]; exact hs9_mid
  have hs10_p11 : s10.locals.lookup (ofString "p11") = some (.val (.word p11)) := by
    rw [hlk_ne (ofString "lo") (ofString "p11") _ (by decide)]; exact hs9_p11
  rw [step_dec (u := .val (.word hi))
    (by simp [evalHOLExact, evalListHOLExact, hs10_p11, hs10_mid, hs10_lo, valueIsWord, valueWord, h32, hlsr_mid0, hlsl_mid1, hadd4]) (hsh1 _)] at hret
  set s11 := setVarHOLFinite (ofString "hi") (.val (.word hi)) s10
  have hs11_hi : s11.locals.lookup (ofString "hi") = some (.val (.word hi)) := hlk_eq _ _
  have hs11_lo : s11.locals.lookup (ofString "lo") = some (.rStruct [.val (.word lo.1), .val (.word lo.2)]) := by
    rw [hlk_ne (ofString "hi") (ofString "lo") _ (by decide)]; exact hs10_lo
  rw [evaluateHOLFiniteState_return] at hret
  have hev_ret : @evalHOLExact 64 F _ s11.toExact (fun a => Classical.propDecidable (s11.memaddrs a))
      (.rstruct [.rfield 0 (.var .local (ofString "lo")), .var .local (ofString "hi")]) =
      some (.rStruct [.val (.word lo.1), .val (.word hi)]) := by
    simp [evalHOLExact, evalListHOLExact, hs11_lo, hs11_hi]
  rw [hev_ret] at hret; dsimp only at hret
  have hsz : sizeOfShapeWithContextHOL s11.structs
      (shapeOfHOLExact (.rStruct [.val (.word lo.1), .val (.word hi)] : ValueHOL 64)) ≤ 32 := by
    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
  rw [if_pos hsz] at hret; dsimp only at hret
  injection hret with h1; injection h1 with hv
  refine ⟨lo.1, hi, hv.symm, ?_⟩
  have ha1_nat : a1.toNat = ww.toNat / 2 ^ 32 := by
    dsimp only [a1]; rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have ha1_pos : 1 ≤ a1.toNat := by omega
  have ha1_lt : a1.toNat < 2 ^ 27 := by
    have : (2 ^ 59 : Nat) = 2 ^ 27 * 2 ^ 32 := by decide
    omega
  have hp11_lt : a1.toNat * a1.toNat < 2 ^ 54 := by
    have hmul : a1.toNat * a1.toNat < 2 ^ 27 * 2 ^ 27 := Nat.mul_lt_mul'' ha1_lt ha1_lt
    have : (2 ^ 27 : Nat) * 2 ^ 27 = 2 ^ 54 := by decide
    omega
  have hp11_nat : p11.toNat = a1.toNat * a1.toNat := by
    dsimp only [p11]; rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (by omega)]
  have hp11_pos : 1 ≤ p11.toNat := by
    rw [hp11_nat]; exact Nat.mul_le_mul ha1_pos ha1_pos
  have hmid0_lsr : (mid.1 >>> (32 : Nat)).toNat < 2 ^ 32 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := mid.1.isLt
    have : (2 ^ 64 : Nat) = 2 ^ 32 * 2 ^ 32 := by decide
    omega
  have hcarry_bit : ∀ x y z : BitVec 64, (wordAddCarryHOL x y z).2 = 0 ∨ (wordAddCarryHOL x y z).2 = 1 := by
    intro x y z; unfold wordAddCarryHOL; split_ifs <;> simp <;> omega
  have hmid2_le : mid.2.toNat ≤ 1 := by
    rcases hcarry_bit p01 p01 0#64 with h | h
    · dsimp only [mid]; rw [h]; decide
    · dsimp only [mid]; rw [h]; decide
  have hmid2_lsl : (mid.2 <<< (32 : Nat)).toNat ≤ 2 ^ 32 := by
    rw [BitVec.toNat_shiftLeft]
    have : mid.2.toNat <<< 32 = mid.2.toNat * 2 ^ 32 := Nat.shiftLeft_eq mid.2.toNat 32
    rw [this, Nat.mod_eq_of_lt (by omega)]
    omega
  have hlo2_le : lo.2.toNat ≤ 1 := by
    rcases hcarry_bit p00 (mid.1 <<< (32 : Nat)) 0#64 with h | h
    · dsimp only [lo]; rw [h]; decide
    · dsimp only [lo]; rw [h]; decide
  have hhi_pos : 0 < hi.toNat := by
    dsimp only [hi]
    have hsum1 : (p11 + (mid.1 >>> (32 : Nat))).toNat = p11.toNat + (mid.1 >>> (32 : Nat)).toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have hsum2 : (p11 + (mid.1 >>> (32 : Nat)) + (mid.2 <<< (32 : Nat))).toNat =
        p11.toNat + (mid.1 >>> (32 : Nat)).toNat + (mid.2 <<< (32 : Nat)).toNat := by
      rw [BitVec.toNat_add, hsum1, Nat.mod_eq_of_lt (by omega)]
    have hsum3 : (p11 + (mid.1 >>> (32 : Nat)) + (mid.2 <<< (32 : Nat)) + lo.2).toNat =
        p11.toNat + (mid.1 >>> (32 : Nat)).toNat + (mid.2 <<< (32 : Nat)).toNat + lo.2.toNat := by
      rw [BitVec.toNat_add, hsum2, Nat.mod_eq_of_lt (by omega)]
    omega
  intro hz; rw [hz] at hhi_pos; simp at hhi_pos

private theorem words_of_ge_of_ge {F : Type}
    (s : PanSemStateFiniteExact 64 F) {nw : BitVec 64}
    (hn_ge : 2 ^ 37 ≤ nw.toNat)
    (hcode : s.code = originalRuntimeCode)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_words_of)).1 =
      some (.returned v)) :
    ∃ ww : BitVec 64, v = .val (.word ww) ∧ 2 ^ 32 ≤ ww.toNat ∧ ww.toNat < 2 ^ 59 := by
  have hbody : sourceFnBody Guest.Software.guestFn_words_of =
      .decCall (ofString "c") .one (ofString "ceil32") [.var .local (ofString "n")]
        (.return (.shift .lsr (.var .local (ofString "c")) (.const 5#64))) := rfl
  rw [hbody, evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
  have hargs : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x))
      [.var .local (ofString "n")] = some [.val (.word nw)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hn]
  rw [hargs] at hret; dsimp only at hret
  have hlk := pan_one_word_lookup s.code.lookup (ofString "ceil32") (ofString "v")
    (sourceFnBody Guest.Software.guestFn_ceil32) nw
    (by rw [hcode]; exact lookup_ceil32)
  rw [hlk] at hret; dsimp only at hret
  split at hret
  · simp at hret
  · let cal := HolFiniteMapExact.empty.update (ofString "v", ValueHOL.val (.word nw))
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
              some (.val (.word nw)) := by
            simp [cal, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          obtain ⟨cw, rfl, hlo, hhi⟩ := ceil32_body_exact (callEntryStateHOLFinite s cal) hcode hv_lk vb
            (by rw [hrun])
          have hcw_ge : 2 ^ 37 ≤ cw.toNat := by
            by_cases hle : nw.toNat ≤ 2 ^ 64 - 32
            · have := (hlo hle).1; omega
            · have := hhi (by omega); omega
          set cs := setVarHOLFinite (ofString "c") (.val (.word cw)) { pb with locals := s.locals }
          rw [evaluateHOLFiniteState_return] at hret
          have hcs_c : cs.locals.lookup (ofString "c") = some (.val (.word cw)) := by
            simp [cs, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have h5 : (5#64 : BitVec 64).toNat = 5 := rfl
          have hshf : wordShiftHOL .lsr cw 5 = some (cw >>> (5 : Nat)) := by simp [wordShiftHOL]
          have hev : @evalHOLExact 64 F _ cs.toExact (fun a => Classical.propDecidable (cs.memaddrs a))
              (.shift .lsr (.var .local (ofString "c")) (.const 5#64)) =
              some (.val (.word (cw >>> (5 : Nat)))) := by
            simp [evalHOLExact, hcs_c, h5, hshf]
          rw [hev] at hret; dsimp only at hret
          split at hret
          · injection hret with h1; injection h1 with hv
            refine ⟨cw >>> (5 : Nat), hv.symm, ?_, ?_⟩
            · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
              have : (2 ^ 37 : Nat) = 2 ^ 32 * 2 ^ 5 := by decide
              omega
            · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
              have := cw.isLt
              have : (2 ^ 64 : Nat) = 2 ^ 59 * 2 ^ 5 := by decide
              omega
          · simp at hret
        · simp at hret
      | _ => simp at hret

private theorem memory_gas_cost_ge_twoPow37 {F : Type}
    (s : PanSemStateFiniteExact 64 F) {szw : BitVec 64}
    (hsz_ge : 2 ^ 37 ≤ szw.toNat)
    (hcode : s.code = originalRuntimeCode)
    (hsz_lk : s.locals.lookup (ofString "size") = some (.val (.word szw)))
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
      [.var .local (ofString "size")] = some [.val (.word szw)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hsz_lk]
  rw [hargs1] at hret; dsimp only at hret
  have hlk1 := pan_one_word_lookup s.code.lookup (ofString "words_of") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_words_of) szw
    (by rw [hcode]; exact lookup_words_of)
  rw [hlk1] at hret; dsimp only at hret
  split at hret
  · simp at hret
  · let cal1 := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word szw))
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
              some (.val (.word szw)) := by
            simp [cal1, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          obtain ⟨ww, rfl, hww_ge, hww_lt⟩ :=
            words_of_ge_of_ge (callEntryStateHOLFinite s cal1) hsz_ge hcode hn1 vb1 (by rw [hrun1])
          set s1 := setVarHOLFinite (ofString "w") (.val (.word ww)) { pb1 with locals := s.locals }
          have hs1_w : s1.locals.lookup (ofString "w") = some (.val (.word ww)) := by
            simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hs1_code : s1.code = originalRuntimeCode := hpb1_code
          rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
          have hargs2 : evalListHOLFinite s1 (h := fun x => Classical.propDecidable (s1.memaddrs x))
              [.var .local (ofString "w"), .var .local (ofString "w")] =
              some [.val (.word ww), .val (.word ww)] := by
            simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs1_w]
          rw [hargs2] at hret; dsimp only at hret
          have hlk2 : lookupCodeHOLFinite s1.code.lookup (ofString "mul64x64")
              [.val (.word ww), .val (.word ww)] =
              some (sourceFnBody Guest.Software.guestFn_mul64x64,
                (HolFiniteMapExact.empty.update (ofString "a", ValueHOL.val (.word ww))).update
                  (ofString "b", ValueHOL.val (.word ww)),
                .comb [.one, .one]) := by
            have hd : ofString "a" ≠ ofString "b" := by decide
            have raw : lookupCodeHOLExact s1.code.lookup (ofString "mul64x64")
                [.val (.word ww), .val (.word ww)] =
                some (sourceFnBody Guest.Software.guestFn_mul64x64,
                  (fun key => if key = ofString "b" then some (.val (.word ww))
                    else if key = ofString "a" then some (.val (.word ww)) else none),
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
          · let cal2 := (HolFiniteMapExact.empty.update (ofString "a", ValueHOL.val (.word ww))).update
              (ofString "b", ValueHOL.val (.word ww))
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
                      some (.val (.word ww)) := by
                    have hne : ofString "b" ≠ ofString "a" := by decide
                    simp [cal2, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne]
                  have hb2 : (callEntryStateHOLFinite s1 cal2).locals.lookup (ofString "b") =
                      some (.val (.word ww)) := by
                    simp [cal2, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  obtain ⟨low, hiw, rfl, hhi_ne0⟩ :=
                    eval_mul64x64_hi_nonzero (callEntryStateHOLFinite s1 cal2) hww_ge hww_lt ha2 hb2 vb2 (by rw [hrun2])
                  set s2 := setVarHOLFinite (ofString "sq")
                    (.rStruct [.val (.word low), .val (.word hiw)]) { pb2 with locals := s1.locals }
                  have hs2_sq : s2.locals.lookup (ofString "sq") =
                      some (.rStruct [.val (.word low), .val (.word hiw)]) := by
                    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
                  have h10 : ¬ ((1#64 : BitVec 64) = 0) := by decide
                  have hcmp : @evalHOLExact 64 F _ s2.toExact (fun x => Classical.propDecidable (s2.memaddrs x))
                      (.cmp .notEqual (.rfield 1 (.var .local (ofString "sq"))) (.const 0#64)) =
                      some (.val (.word 1#64)) := by
                    simp [evalHOLExact, hs2_sq, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hhi_ne0]
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
          after < 2 ^ 37 ∧
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
            have haft_lt37 : aftw.toNat < 2 ^ 37 := by
              by_contra hge
              have hca_eq := memory_gas_cost_ge_twoPow37 (callEntryStateHOLFinite s7 cal8)
                (Nat.le_of_not_lt hge) hs7_c hcal8_sz (.val (.word caw)) hrun8
              injection hca_eq with h1; injection h1 with h2
              exact hca_max h2
            have hendp_le : endpw.toNat ≤ 2 ^ 64 - 32 := by
              by_contra hgt
              have haft_max_nat := haft_hi (by omega)
              omega
            have haft_eq := haft_lo hendp_le
            have haft_mod : aftw.toNat % 32 = 0 := by omega
            have hcur_le : curw.toNat ≤ 2 ^ 64 - 32 := by
              by_contra hgt
              have := hbef_hi (by omega)
              omega
            have hbef_eq := hbef_lo hcur_le
            have hsub_nat : (aftw - befw).toNat = aftw.toNat - befw.toNat :=
              BitVec.toNat_sub_of_le (BitVec.le_def.2 (Nat.le_of_lt hba_lt))
            refine ⟨caw - cbw, aftw - befw, hv.symm, Or.inr ⟨befw.toNat, aftw.toNat, haft_lt37, haft_mod, hba_lt, hsub_nat, ?_⟩⟩
            intro hcur_al
            rw [← hcur_eq] at hcur_al ⊢
            omega

/-- `extend_memory_cost1` is read-only and returns `[cw, ebw]` where either `ebw = 0` or
    `ebw = after - before` with `after < 2^37`, `after % 32 = 0`, `before < after`,
    and `before = mem_len` whenever `mem_len % 32 = 0`. -/
theorem eps_extend_memory_cost1_bounds :
    EvmPreservingSpec (fun _ => True)
      (fun s v post =>
        LocFrame s post ∧
        ∃ cw ebw : BitVec 64,
          v = .rStruct [.val (.word cw), .val (.word ebw)] ∧
          (ebw = 0#64 ∨
            ∃ before after : Nat,
              after < 2 ^ 37 ∧
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

/-! ## `extend_memory` and `op_keccak` specs -/

/-- Head-frame EVM memory layout condition for `extend_memory`:
    `ev + 32` (`mem_len`) is 32-byte aligned, and the current memory buffer ends at `frame_mem_ptr`
    (`mem + mem_cap = frame_mem_ptr`). -/
def HeadMemAligned {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  memW s (globN s "ev" + 32) % 32 = 0 ∧
  (memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = globN s "frame_mem_ptr")

/-- Precondition for `extend_memory(expand_by)`: `expand_by` is a word bounded so that
    `mem_len + expand_by < 2^37` (so `nlen + 1024` does not wrap `BitVec 64`), `(mem_len + expand_by) % 8 = 0`,
    and either `expand_by = 0` or `mem + mem_cap = frame_mem_ptr`. -/
def ExtendMemoryPre {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ ebw : BitVec 64,
    s.locals.lookup (ofString "expand_by") = some (.val (.word ebw)) ∧
    (ebw = 0#64 ∨
      (memW s (globN s "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
       (memW s (globN s "ev" + 32) + ebw.toNat) % 8 = 0 ∧
       memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = globN s "frame_mem_ptr"))

theorem eps_extend_memory_aligned :
    EvmPreservingSpec ExtendMemoryPre
      (fun s _ post => ∀ g : String, ofString g ≠ ofString "frame_mem_ptr" → globN post g = globN s g)
      (ofString "extend_memory") := by
  refine ⟨_, _, _, lookup_extend_memory, ?_⟩
  intro F s hcode hInv ⟨ebw, heb_loc, heb_cond⟩ _ hnt
  have herr_triv : ∀ {P1 P2 : Prop},
      (∀ v, (some PanSemResultExact.error : Option (PanSemResultExact 64)) = some (.returned v) → P1) ∧
      (IsEvmErr (some PanSemResultExact.error) → P2) := by
    intro _ _; constructor
    · intro _ h; cases h
    · rintro ⟨_, h⟩; cases h
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by simp [evmChain, evmChainFrom]
  have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead_mem
  have hb_ev := (frameWF_bounds hInv.1.2 hFW0).1
  dsimp only at hb_ev
  have hev_pos : 0 < globN s "ev" := by
    obtain ⟨hin1, _⟩ := (hFW0.1 (globN s "ev", 280) (by simp)).1
    have h1 := hInv.1.2.2.2.1; have h2 := hInv.1.2.2.2.2.1
    rw [R11Shards.scratchStart_val] at h1; dsimp only at hin1; omega
  obtain ⟨evw, hevw, hevw_nat⟩ := global_word_of_pos s "ev" hev_pos
  obtain ⟨hp_w, fp_w, sp_g_w, hhp_lk, hhp_nat, hfp_lk, hfp_nat, hsp_g_lk, hsp_g_nat⟩ :=
    Wave8Contracts.M26.arenaOK_globals s hInv.1.2
  let growBranch : ProgHOL 64 :=
    .dec (ofString "ncap") .one (.panop .mul [.var .local (ofString "cap"), .const 2#64])
      (.seq
        (.ite (.cmp .lower (.var .local (ofString "ncap")) (.var .local (ofString "nlen")))
          (.assign .local (ofString "ncap") (.op .add [.var .local (ofString "nlen"), .const 1024#64]))
          .skip)
        (.seq
          (.call (some (none, none)) (ofString "frame_mem_alloc")
            [.op .sub [.var .local (ofString "ncap"), .var .local (ofString "cap")]])
          (.seq
            (.call (some (none, none)) (ofString "memzero")
              [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "cap")],
               .op .sub [.var .local (ofString "ncap"), .var .local (ofString "cap")]])
            (.store (.op .add [.var .global (ofString "ev"), .const 40#64]) (.var .local (ofString "ncap"))))))
  let tailProg : ProgHOL 64 :=
    .seq
      (.call (some (none, none)) (ofString "memzero")
        [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "len")],
         .var .local (ofString "expand_by")])
      (.seq
        (.store (.op .add [.var .global (ofString "ev"), .const 32#64]) (.var .local (ofString "nlen")))
        (.return (.const 0#64)))
  have hbody : sourceFnBody Guest.Software.guestFn_extend_memory =
      .seq
        (.ite (.cmp .equal (.var .local (ofString "expand_by")) (.const 0#64))
          (.return (.const 0#64))
          .skip)
        (.dec (ofString "len") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 32#64]))
          (.dec (ofString "cap") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 40#64]))
            (.dec (ofString "nlen") .one (.op .add [.var .local (ofString "len"), .var .local (ofString "expand_by")])
              (.seq
                (.ite (.cmp .lower (.var .local (ofString "cap")) (.var .local (ofString "nlen")))
                  growBranch
                  .skip)
                tailProg)))) := rfl
  dsimp only
  rw [hbody] at hnt ⊢
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
  have hcmp_eb0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.var .local (ofString "expand_by")) (.const 0#64)) =
      some (.val (.word (if ebw = 0#64 then 1 else 0))) := by
    simp [evalHOLExact, heb_loc, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp_eb0] at hnt ⊢; dsimp only at hnt ⊢
  have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
  by_cases heb0 : ebw = 0#64
  · simp only [heb0, ↓reduceIte, h10] at hnt ⊢
    rw [evaluateHOLFiniteState_return]
    have hc0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.const 0#64) =
        some (.val (.word 0#64)) := rfl
    rw [hc0]; dsimp only
    have hsz0 : sizeOfShapeWithContextHOL s.structs
        (shapeOfHOLExact (.val (.word 0#64))) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [if_pos hsz0]; dsimp only
    have hInv_el : EvmInv s.emptyLocalsHOLFinite := localsFree_evmInv s _ s.clock hInv
    have hc_el := evm_congr (s := s) (t := s.emptyLocalsHOLFinite) rfl rfl
    have hch_el : evmChain s.emptyLocalsHOLFinite = evmChain s := evmChain_congr rfl rfl
    exact ⟨fun _ _ => ⟨hInv_el, hch_el, le_of_eq hc_el.2.1, fun _ _ => rfl⟩,
           by rintro ⟨_, h⟩; cases h⟩
  · rcases heb_cond with rfl | ⟨hnlen_bound, hnlen_al8, hmem_end_fp⟩
    · exact absurd rfl heb0
    have heb_pos : 0 < ebw.toNat := by
      by_contra hz
      apply heb0
      apply BitVec.eq_of_toNat_eq
      have : (0#64 : BitVec 64).toNat = 0 := rfl
      omega
    simp only [heb0, ↓reduceIte, evaluateHOLFiniteState_skip] at hnt ⊢
    rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
    rcases hload_len : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one (.op .add [.var .global (ofString "ev"), .const 32#64])) with _ | vlen
    · exact herr_triv
    · simp only [hload_len] at hnt ⊢
      obtain ⟨lenw, rfl, hlenw_eq⟩ := evalAt_loadG_word s "ev" 32#64 vlen hload_len
      have h32_n : (32#64 : BitVec 64).toNat = 32 := rfl
      rw [h32_n] at hlenw_eq
      have hsh_len : shapeEqHOL .one (shapeOfHOLExact (.val (.word lenw))) = true := by
        simp [shapeEqHOL, shapeOfHOLExact]
      rw [if_pos hsh_len] at hnt ⊢; dsimp only at hnt ⊢
      set s1 := setVarHOLFinite (ofString "len") (.val (.word lenw)) s with hs1
      rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
      rcases hload_cap : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
          (.load .one (.op .add [.var .global (ofString "ev"), .const 40#64])) with _ | vcap
      · exact herr_triv
      · simp only [hload_cap] at hnt ⊢
        obtain ⟨capw, rfl, hcapw_eq⟩ := evalAt_loadG_word s1 "ev" 40#64 vcap hload_cap
        have h40_n : (40#64 : BitVec 64).toNat = 40 := rfl
        have hs1_gm : memW s1 (globN s1 "ev" + 40) = memW s (globN s "ev" + 40) := rfl
        rw [h40_n, hs1_gm] at hcapw_eq
        have hsh_cap : shapeEqHOL .one (shapeOfHOLExact (.val (.word capw))) = true := by
          simp [shapeEqHOL, shapeOfHOLExact]
        rw [if_pos hsh_cap] at hnt ⊢; dsimp only at hnt ⊢
        set s2 := setVarHOLFinite (ofString "cap") (.val (.word capw)) s1 with hs2
        have hs2_len : s2.locals.lookup (ofString "len") = some (.val (.word lenw)) := by
          simp [hs2, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "cap" ≠ ofString "len" by decide]
        have hs2_cap : s2.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
          simp [hs2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hs2_eb : s2.locals.lookup (ofString "expand_by") = some (.val (.word ebw)) := by
          simp [hs2, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, heb_loc,
            show ofString "cap" ≠ ofString "expand_by" by decide,
            show ofString "len" ≠ ofString "expand_by" by decide]
        rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
        have hnlen_ev : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
            (.op .add [.var .local (ofString "len"), .var .local (ofString "expand_by")]) =
            some (.val (.word (lenw + ebw))) := by
          simp [evalHOLExact, evalListHOLExact, hs2_len, hs2_eb, wordOpHOL, wordOp, valueIsWord, valueWord]
        rw [hnlen_ev] at hnt ⊢; dsimp only at hnt ⊢
        set nlenw := lenw + ebw
        have hnlenw_nat : nlenw.toNat = lenw.toNat + ebw.toNat := by
          rw [BitVec.toNat_add, hlenw_eq, Nat.mod_eq_of_lt (by omega)]
        have hsh_nlen : shapeEqHOL .one (shapeOfHOLExact (.val (.word nlenw))) = true := by
          simp [shapeEqHOL, shapeOfHOLExact]
        rw [if_pos hsh_nlen] at hnt ⊢; dsimp only at hnt ⊢
        set s3 := setVarHOLFinite (ofString "nlen") (.val (.word nlenw)) s2 with hs3
        have hs3_nlen : s3.locals.lookup (ofString "nlen") = some (.val (.word nlenw)) := by
          simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hs3_len : s3.locals.lookup (ofString "len") = some (.val (.word lenw)) := by
          simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_len,
            show ofString "nlen" ≠ ofString "len" by decide]
        have hs3_cap : s3.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
          simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_cap,
            show ofString "nlen" ≠ ofString "cap" by decide]
        have hs3_eb : s3.locals.lookup (ofString "expand_by") = some (.val (.word ebw)) := by
          simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_eb,
            show ofString "nlen" ≠ ofString "expand_by" by decide]
        -- Bounds on old memory buffer `(memW s (ev + 24), memW s (ev + 40))` from `FrameWF`:
        have hmem_in : Inside (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40)) scratchStart (globN s "frame_mem_ptr") :=
          hFW0.2.1
        have hmem_wok := hFW0.2.2.1
        have hmem24_8 : memW s (globN s "ev" + 24) % 8 = 0 := hmem_wok.1
        have hmem40_8 : memW s (globN s "ev" + 40) % 8 = 0 := hmem_wok.2.1
        have hfp_le_se : globN s "frame_mem_ptr" ≤ scratchEnd :=
          le_trans hInv.1.2.2.2.2.1 hInv.1.2.2.2.2.2.1
        have hse_val := R11Shards.scratchEnd_val
        have hss_val := R11Shards.scratchStart_val
        have hcap_lt : capw.toNat < 2 ^ 30 := by
          dsimp only [Inside] at hmem_in; omega
        have hlen_le_cap0 : lenw.toNat ≤ capw.toNat := by
          rw [hlenw_eq, hcapw_eq]; exact hFW0.2.2.2.2.2.2.1
        -- `run_tail` from any intermediate state `m` after the optional grow branch:
        have run_tail : ∀ (m : PanSemStateFiniteExact 64 F) (freshIvl : Ivl),
            ArenaReady m →
            globN s "frame_mem_ptr" ≤ globN m "frame_mem_ptr" →
            (∀ g : String, ofString g ≠ ofString "frame_mem_ptr" → m.globals.lookup (ofString g) = s.globals.lookup (ofString g)) →
            FrameMemByteEff s m [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))] →
            (freshIvl = (0, 0) ∨
              (freshIvl.1 % 8 = 0 ∧ freshIvl.2 % 8 = 0 ∧
                Inside freshIvl (globN s "frame_mem_ptr") (globN m "frame_mem_ptr"))) →
            (∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 32 → off ≠ 40 →
              memW m (globN s "ev" + off) = memW s (globN s "ev" + off)) →
            ((freshIvl.2 = 0 ∧ memW m (globN s "ev" + 40) = memW s (globN s "ev" + 40)) ∨
              (freshIvl.2 ≠ 0 ∧
                memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = freshIvl.1 ∧
                memW m (globN s "ev" + 40) = memW s (globN s "ev" + 40) + freshIvl.2)) →
            nlenw.toNat ≤ memW m (globN s "ev" + 40) →
            m.locals.lookup (ofString "len") = some (.val (.word lenw)) →
            m.locals.lookup (ofString "nlen") = some (.val (.word nlenw)) →
            m.locals.lookup (ofString "expand_by") = some (.val (.word ebw)) →
            (evaluateHOLFiniteState m tailProg).1 ≠ some .timeOut →
            let out := evaluateHOLFiniteState m tailProg
            let post := { out.2 with
              locals := ((out.2.locals.resVarEq (ofString "nlen", s2.locals.lookup (ofString "nlen"))).resVarEq
                (ofString "cap", s1.locals.lookup (ofString "cap"))).resVarEq
                (ofString "len", s.locals.lookup (ofString "len")) }
            (∀ v, out.1 = some (.returned v) →
              EvmInv post ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s ∧
              (∀ g : String, ofString g ≠ ofString "frame_mem_ptr" → globN post g = globN s g)) ∧
            (IsEvmErr out.1 →
              EvmInv post ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s) := by
          intro m freshIvl hAm hfm_m hm_glob_other heff_m hfresh_m he0_m hnew_m hnlen_le_mcap hm_len hm_nlen hm_eb hnt_t
          dsimp only [tailProg] at hnt_t ⊢
          have hm_ev : m.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
            rw [hm_glob_other "ev" (by decide)]; exact hevw
          have hm_code : m.code = originalRuntimeCode := heff_m.code.trans hcode
          have hm_ma : m.memaddrs = ordinaryDomain := hAm.1.memaddrs
          have hm_dom24 : m.memaddrs (evw + 24#64) := by
            rw [hm_ma, ← hInv.1.1.memaddrs]
            have hev24_eq : evw + 24#64 = BitVec.ofNat 64 (globN s "ev" + 24) := by
              apply BitVec.eq_of_toNat_eq
              have : (24#64 : BitVec 64).toNat = 24 := rfl
              rw [BitVec.toNat_add, hevw_nat, this, BitVec.toNat_ofNat]
            rw [hev24_eq]
            exact ((hFW0.1 (globN s "ev", 280) (by simp)).2.2.2 3 (by omega)).choose_spec.1
          rcases hm_m24 : m.memory (evw + 24#64) with ⟨memPtrW⟩
          have hmemPtrW_nat : memPtrW.toNat = memW s (globN s "ev" + 24) := by
            have hev24_eq : evw + 24#64 = BitVec.ofNat 64 (globN s "ev" + 24) := by
              apply BitVec.eq_of_toNat_eq
              have : (24#64 : BitVec 64).toNat = 24 := rfl
              rw [BitVec.toNat_add, hevw_nat, this, BitVec.toNat_ofNat]
            have hm24_eq := he0_m 24 (by omega) (by omega) (by omega) (by omega)
            have hm24_lhs : memW m (globN s "ev" + 24) = memPtrW.toNat := by
              unfold memW; rw [← hev24_eq, hm_m24]
            rw [← hm24_lhs, hm24_eq]
          let mzDstExp : ExpHOL 64 :=
            .op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "len")]
          have hev_mz_dst : @evalHOLExact 64 F _ m.toExact (fun a => Classical.propDecidable (m.memaddrs a)) mzDstExp =
              some (.val (.word (memPtrW + lenw))) := by
            simp [mzDstExp, evalHOLExact, evalListHOLExact, hm_ev, hm_len, wordOpHOL, wordOp,
              valueIsWord, valueWord, memLoadHOLExact, hm_dom24, hm_m24]
          have hev_mz_n : @evalHOLExact 64 F _ m.toExact (fun a => Classical.propDecidable (m.memaddrs a))
              (.var .local (ofString "expand_by")) = some (.val (.word ebw)) := hm_eb
          have hmcap_bound : memW s (globN s "ev" + 24) + memW m (globN s "ev" + 40) ≤ scratchEnd := by
            rcases hnew_m with ⟨_, h40_eq⟩ | ⟨hnz, hfr1, h40_eq⟩
            · rw [h40_eq]; dsimp only [Inside] at hmem_in; omega
            · rcases hfresh_m with rfl | ⟨_, _, _, hfin2⟩
              · exact absurd rfl hnz
              · have hm_fp_se : globN m "frame_mem_ptr" ≤ scratchEnd :=
                  le_trans hAm.2.2.2.2.1 hAm.2.2.2.2.2.1
                omega
          have hdst_nat : (memPtrW + lenw).toNat = memW s (globN s "ev" + 24) + lenw.toNat := by
            rw [BitVec.toNat_add, hmemPtrW_nat, Nat.mod_eq_of_lt (by omega)]
          let combinedMem : Ivl := (memW s (globN s "ev" + 24), memW m (globN s "ev" + 40))
          let mzTailCall : ProgHOL 64 := .call (some (none, none)) (ofString "memzero") [mzDstExp, .var .local (ofString "expand_by")]
          rw [evaluateHOLFiniteState_seq_line780] at hnt_t ⊢
          have hnt_mz : (evaluateHOLFiniteState m mzTailCall).1 ≠ some .timeOut := by
            intro hto
            rcases hmz_to : evaluateHOLFiniteState m
                (.call (some (none, none)) (ofString "memzero") [mzDstExp, .var .local (ofString "expand_by")]) with ⟨rmz_to, smz_to⟩
            have hto' : rmz_to = some .timeOut := by
              dsimp only [mzTailCall] at hto; rw [hmz_to] at hto; exact hto
            subst hto'
            have hmz_to_raw : evaluateHOLFiniteState m
                (.call (some (none, none)) (ofString "memzero")
                  [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "len")],
                   .var .local (ofString "expand_by")]) = (some .timeOut, smz_to) := hmz_to
            simp only [hmz_to_raw] at hnt_t
            exact hnt_t rfl
          have hmz := eval_call_memzero_bre m mzDstExp (.var .local (ofString "expand_by"))
            (memPtrW + lenw) ebw [combinedMem] hm_code hm_ma hev_mz_dst hev_mz_n
            (fun _ => ⟨combinedMem, by simp, by rw [hdst_nat]; dsimp only [combinedMem]; omega,
              by rw [hdst_nat]; dsimp only [combinedMem]; omega⟩) hnt_mz
          dsimp only at hmz
          rcases hmz_run : evaluateHOLFiniteState m mzTailCall with ⟨rmz, m1⟩
          rw [hmz_run] at hmz
          have hmz_run_raw : evaluateHOLFiniteState m
              (.call (some (none, none)) (ofString "memzero")
                [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "len")],
                 .var .local (ofString "expand_by")]) = (rmz, m1) := hmz_run
          simp only [hmz_run_raw] at hnt_t ⊢
          cases rmz with
          | some rmz0 =>
            dsimp only at hnt_t ⊢
            have hnr := hmz.2 (by simp)
            refine ⟨fun v hv => absurd (Or.inl ⟨v, hv⟩) hnr, ?_⟩
            rintro ⟨ev, hv⟩
            injection hv with hv'; subst hv'
            exact absurd (Or.inr ⟨ofString "EvmErr", ev, rfl, by decide⟩) hnr
          | none =>
            dsimp only at hnt_t ⊢
            obtain ⟨heff_mz_comb, hm1_loc⟩ := hmz.1 rfl
            -- Convert `ByteRegionEffect m m1 [combinedMem]` to `FrameMemByteEff m m1 [freshIvl, (e0, 280), oldMem]`!
            have heff_mz : FrameMemByteEff m m1
                [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))] := by
              refine ⟨heff_mz_comb.code, heff_mz_comb.memaddrs, heff_mz_comb.shMemaddrs,
                heff_mz_comb.baseAddr, heff_mz_comb.be, fun _ _ => by rw [heff_mz_comb.globals],
                heff_mz_comb.out_dom, ?_, ?_⟩
              · intro a ha
                apply heff_mz_comb.cell_frame a
                intro i hi hch
                simp at hi; subst hi
                obtain ⟨hc1, hc2⟩ := hch
                dsimp only [combinedMem] at hc1 hc2
                rcases hnew_m with ⟨_, h40_eq⟩ | ⟨hnz, hfr1, h40_eq⟩
                · rw [h40_eq] at hc2
                  exact ha (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40)) (by simp) ⟨hc1, hc2⟩
                · by_cases hsplit : a.toNat < memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40)
                  · exact ha (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40)) (by simp) ⟨hc1, hsplit⟩
                  · exact ha freshIvl (by simp) ⟨by omega, by omega⟩
              · intro b hb hno
                apply heff_mz_comb.byte_frame b hb
                intro i hi hin
                simp at hi; subst hi
                obtain ⟨hb1, hb2⟩ := hin
                dsimp only [combinedMem] at hb1 hb2
                rcases hnew_m with ⟨_, h40_eq⟩ | ⟨hnz, hfr1, h40_eq⟩
                · rw [h40_eq] at hb2
                  exact hno (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40)) (by simp) ⟨hb1, hb2⟩
                · by_cases hsplit : b < memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40)
                  · exact hno (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40)) (by simp) ⟨hb1, hsplit⟩
                  · exact hno freshIvl (by simp) ⟨by omega, by omega⟩
            have hm1_e0_eq : ∀ off, off + 8 ≤ 280 → off % 8 = 0 →
                memW m1 (globN s "ev" + off) = memW m (globN s "ev" + off) := by
              intro off hoff hoff8
              unfold memW
              rw [heff_mz_comb.cell_frame (BitVec.ofNat 64 (globN s "ev" + off))]
              intro x hx
              simp at hx; subst hx
              have htn : (BitVec.ofNat 64 (globN s "ev" + off)).toNat = globN s "ev" + off :=
                Nat.mod_eq_of_lt (by omega)
              rw [htn]
              have he0_8 : (globN s "ev") % 8 = 0 := (hFW0.1 (globN s "ev", 280) (by simp)).2.1
              have ha8 : (globN s "ev" + off) % 8 = 0 := by omega
              rcases hnew_m with ⟨_, h40_eq⟩ | ⟨hnz, hfr1, h40_eq⟩
              · dsimp only [combinedMem]; rw [h40_eq]
                have hpw_fo := hInv.2.choose_spec.2.2.2.2.2.2.2.1
                have hch_s : ∃ tl, evmChain s = (globN s "ev", globN s "cur_cont") :: tl := ⟨_, rfl⟩
                obtain ⟨tl_s, hch_s_eq⟩ := hch_s
                rw [hch_s_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw_fo
                have hd_mem : Disj (globN s "ev", 280) (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40)) := by
                  have hp0 := hpw_fo.1; unfold frameObjects at hp0
                  exact (List.pairwise_cons.1 hp0).1 _ (by simp)
                exact not_cellHits_of_disj_aligned (i := (globN s "ev", 280)) ha8 hmem24_8
                  (Nat.le_add_right _ off) (Nat.add_le_add_left hoff _) hd_mem
              · rcases hfresh_m with rfl | ⟨_, _, _, hfin2⟩
                · exact absurd rfl hnz
                · obtain ⟨he0_scr, _⟩ := (hFW0.1 (globN s "ev", 280) (by simp)).1
                  have hfp_le_scr : globN m "frame_mem_ptr" ≤ globN s "scratch_ptr" := by
                    have hle_m := hAm.2.2.2.2.1
                    have hsp_eq := R16Shards.OpHandlers.globN_eq_of_lookup_eq (hm_glob_other "scratch_ptr" (by decide))
                    omega
                  exact not_cellHits_of_disj_aligned (i := (globN s "ev", 280)) ha8 hmem24_8
                    (Nat.le_add_right _ off) (Nat.add_le_add_left hoff _)
                    (Or.inr (Or.inr (Or.inr (by dsimp only [combinedMem, Inside] at he0_scr hfin2 ⊢; omega))))
            rw [evaluateHOLFiniteState_seq_line780] at hnt_t ⊢
            rcases hst32 : evaluateHOLFiniteState m1
                (.store (.op .add [.var .global (ofString "ev"), .const 32#64]) (.var .local (ofString "nlen"))) with ⟨rst32, m2⟩
            simp only [hst32] at hnt_t ⊢
            cases rst32 with
            | some res32 =>
              have herr := store_some_eq_error' hst32; subst herr; dsimp only; exact herr_triv
            | none =>
              dsimp only at hnt_t ⊢
              have hm1_ev : m1.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
                rw [heff_mz_comb.globals]; exact hm_ev
              have hm1_nlen : m1.locals.lookup (ofString "nlen") = some (.val (.word nlenw)) := by
                rw [hm1_loc]; exact hm_nlen
              obtain ⟨w_nl', hw_nl_ev, hm2_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := m1) (post := m2)
                (gname := "ev") (gbase := globN s "ev") (off := 32) hm1_ev hevw_nat (by omega)
                (fun v hv => by
                  change m1.locals.lookup (ofString "nlen") = some v at hv
                  rw [hm1_nlen] at hv; injection hv with hv'; exact ⟨nlenw, hv'.symm⟩) hst32
              have hw_nl_val : nlenw = w_nl' := by
                change m1.locals.lookup (ofString "nlen") = some (.val (.word w_nl')) at hw_nl_ev
                rw [hm1_nlen] at hw_nl_ev
                injection hw_nl_ev with h1; injection h1 with h2; injection h2 with h3
              subst w_nl'
              have heff_st32 := (ByteRegionEffect.of_store_word (Rl := [(globN s "ev", 280)])
                (heff_mz_comb.memaddrs.trans hm_ma) hst32
                (fun v hv => by
                  change m1.locals.lookup (ofString "nlen") = some v at hv
                  rw [hm1_nlen] at hv; injection hv with hv'; exact ⟨nlenw, hv'.symm⟩)
                (fun addr hdst _ => by
                  simp [evalHOLExact, evalListHOLExact, hm1_ev, wordOpHOL, wordOp, valueIsWord, valueWord] at hdst
                  have h32_eq : (evw + 32#64).toNat = globN s "ev" + 32 := by
                    have : (32#64 : BitVec 64).toNat = 32 := rfl
                    rw [BitVec.toNat_add, hevw_nat, this, Nat.mod_eq_of_lt (by omega)]
                  exact ⟨(globN s "ev", 280), by simp, by rw [← hdst, h32_eq]; dsimp only; omega,
                    by rw [← hdst, h32_eq]; dsimp only; omega⟩)).1
              have heff_st32_fm : FrameMemByteEff m1 m2
                  [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))] :=
                (FrameMemByteEff.of_bre heff_st32).mono (fun x hx => by
                  simp at hx; subst hx; exact ⟨(globN s "ev", 280), by simp, le_refl _, le_refl _⟩)
              rw [evaluateHOLFiniteState_return]
              have hc0_m2 : @evalHOLExact 64 F _ m2.toExact (fun a => Classical.propDecidable (m2.memaddrs a)) (.const (0 : BitVec 64)) =
                  some (.val (.word 0)) := rfl
              have hc0_m2' : @evalHOLExact 64 F _ m2.toExact (fun a => Classical.propDecidable (m2.memaddrs a)) (.const 0#64) =
                  some (.val (.word 0#64)) := rfl
              simp only [hc0_m2, hc0_m2']
              have hsz0 : sizeOfShapeWithContextHOL m2.structs
                  (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
                simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
              have hsz0' : sizeOfShapeWithContextHOL m2.structs
                  (shapeOfHOLExact (.val (.word 0#64))) ≤ 32 := by
                simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
              simp only [hsz0, hsz0', ↓reduceIte]
              let post := { m2.emptyLocalsHOLFinite with
                locals := ((m2.emptyLocalsHOLFinite.locals.resVarEq (ofString "nlen", s2.locals.lookup (ofString "nlen"))).resVarEq
                  (ofString "cap", s1.locals.lookup (ofString "cap"))).resVarEq
                  (ofString "len", s.locals.lookup (ofString "len")) }
              have heff_total : FrameMemByteEff s post
                  [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))] :=
                ((heff_m.trans heff_mz).trans heff_st32_fm).with_locals_clock post.locals m2.clock
              have hm1_glob_m : m1.globals = m.globals := heff_mz_comb.globals
              have hm1_code_m : m1.code = m.code := heff_mz_comb.code
              have hm1_ma_m : m1.memaddrs = m.memaddrs := heff_mz_comb.memaddrs
              have hm1_sh_m : m1.shMemaddrs = m.shMemaddrs := heff_mz_comb.shMemaddrs
              have hm1_ba_m : m1.baseAddr = m.baseAddr := heff_mz_comb.baseAddr
              have hpost_glob_m : post.globals = m.globals := by
                simp [post, emptyLocalsHOLFinite, hm2_eq, hm1_glob_m]
              have hApost : ArenaReady post :=
                ⟨guestInv_congr (s := m) (by simp [post, emptyLocalsHOLFinite, hm2_eq, hm1_code_m])
                  (by simp [post, emptyLocalsHOLFinite, hm2_eq, hm1_ma_m])
                  (by simp [post, emptyLocalsHOLFinite, hm2_eq, hm1_sh_m])
                  (by simp [post, emptyLocalsHOLFinite, hm2_eq, hm1_ba_m]) hAm.1,
                 arenaOK_congr hpost_glob_m hAm.2⟩
              have hfm_post : globN s "frame_mem_ptr" ≤ globN post "frame_mem_ptr" := by
                unfold globN; rw [hpost_glob_m]; exact hfm_m
              have hfresh_post : freshIvl = (0, 0) ∨
                  (freshIvl.1 % 8 = 0 ∧ freshIvl.2 % 8 = 0 ∧
                    Inside freshIvl (globN s "frame_mem_ptr") (globN post "frame_mem_ptr")) := by
                unfold globN; rw [hpost_glob_m]; exact hfresh_m
              have hm2_memW_ne32 : ∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 32 →
                  memW post (globN s "ev" + off) = memW m (globN s "ev" + off) := by
                intro off hoff hoff8 hne32
                change memW m2 (globN s "ev" + off) = memW m (globN s "ev" + off)
                rw [hm2_eq, R14Shards.OpHandlersA.memW_updW_ne m1 (globN s "ev" + 32) (globN s "ev" + off) _ (by omega) (by omega) (by omega),
                    hm1_e0_eq off hoff hoff8]
              have hm2_memW_32 : memW post (globN s "ev" + 32) = nlenw.toNat := by
                change memW m2 (globN s "ev" + 32) = nlenw.toNat
                rw [hm2_eq, R14Shards.OpHandlersA.memW_updW_same m1 (globN s "ev" + 32) nlenw]
              have he0_post : ∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 32 → off ≠ 40 →
                  memW post (globN s "ev" + off) = memW s (globN s "ev" + off) := by
                intro off hoff hoff8 h32 h40
                rw [hm2_memW_ne32 off hoff hoff8 h32, he0_m off hoff hoff8 h32 h40]
              have hnew_post :
                  (freshIvl.2 = 0 ∧ memW post (globN s "ev" + 40) = memW s (globN s "ev" + 40)) ∨
                  (freshIvl.2 ≠ 0 ∧
                    memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = freshIvl.1 ∧
                    memW post (globN s "ev" + 40) = memW s (globN s "ev" + 40) + freshIvl.2) := by
                rw [hm2_memW_ne32 40 (by omega) (by omega) (by omega)]
                exact hnew_m
              have hlen_le_cap_post : memW post (globN s "ev" + 32) ≤ memW post (globN s "ev" + 40) := by
                rw [hm2_memW_32, hm2_memW_ne32 40 (by omega) (by omega) (by omega)]
                exact hnlen_le_mcap
              obtain ⟨hInv_p, hch_p, hR_p⟩ := evmInv_of_head_mem_extend hInv hApost hfm_post
                heff_total hfresh_post he0_post hnew_post hlen_le_cap_post
              constructor
              · intro _ _
                refine ⟨hInv_p, hch_p, le_of_eq hR_p, fun g hg => ?_⟩
                unfold globN; rw [hpost_glob_m, hm_glob_other g hg]
              · rintro ⟨_, h⟩; cases h
        -- Now evaluate `if cap < nlen then growBranch else skip` before `tailProg`:
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
        have hcmp_grow : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
            (.cmp .lower (.var .local (ofString "cap")) (.var .local (ofString "nlen"))) =
            some (.val (.word (if capw < nlenw then 1 else 0))) := by
          simp [evalHOLExact, hs3_cap, hs3_nlen, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        rw [hcmp_grow] at hnt ⊢; dsimp only at hnt ⊢
        by_cases hgrow : capw < nlenw
        · have hcap_lt_nlen : capw.toNat < nlenw.toNat := BitVec.lt_def.1 hgrow
          simp only [hgrow, ↓reduceIte, h10] at hnt ⊢
          dsimp only [growBranch] at hnt ⊢
          rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
          have hmul2 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
              (.panop .mul [.var .local (ofString "cap"), .const 2#64]) =
              some (.val (.word (capw * 2#64))) := by
            simp [evalHOLExact, evalListHOLExact, hs3_cap, panOpHOL, valueIsWord, valueWord]
          rw [hmul2] at hnt ⊢; dsimp only at hnt ⊢
          have hsh_ncap : shapeEqHOL .one (shapeOfHOLExact (.val (.word (capw * 2#64)))) = true := by
            simp [shapeEqHOL, shapeOfHOLExact]
          rw [if_pos hsh_ncap] at hnt ⊢; dsimp only at hnt ⊢
          set s4 := setVarHOLFinite (ofString "ncap") (.val (.word (capw * 2#64))) s3 with hs4
          have hncap0_nat : (capw * 2#64).toNat = 2 * capw.toNat := by
            have : (2#64 : BitVec 64).toNat = 2 := rfl
            rw [BitVec.toNat_mul, this, Nat.mod_eq_of_lt (by omega)]; omega
          have hite_ncap : ∃ (s5 : PanSemStateFiniteExact 64 F) (ncapw : BitVec 64),
              evaluateHOLFiniteState s4
                (.ite (.cmp .lower (.var .local (ofString "ncap")) (.var .local (ofString "nlen")))
                  (.assign .local (ofString "ncap") (.op .add [.var .local (ofString "nlen"), .const 1024#64]))
                  .skip) = (none, s5) ∧
              s5 = { s with locals := s5.locals, clock := s.clock } ∧
              s5.locals.lookup (ofString "ncap") = some (.val (.word ncapw)) ∧
              s5.locals.lookup (ofString "cap") = some (.val (.word capw)) ∧
              s5.locals.lookup (ofString "len") = some (.val (.word lenw)) ∧
              s5.locals.lookup (ofString "nlen") = some (.val (.word nlenw)) ∧
              s5.locals.lookup (ofString "expand_by") = some (.val (.word ebw)) ∧
              nlenw.toNat ≤ ncapw.toNat ∧ capw.toNat < ncapw.toNat ∧
              ncapw.toNat < 2 ^ 38 ∧ ncapw.toNat % 8 = 0 := by
            have hnlenw_al8 : nlenw.toNat % 8 = 0 := by
              rw [hnlenw_nat, hlenw_eq]; exact hnlen_al8
            have hcapw_al8 : capw.toNat % 8 = 0 := by
              rw [hcapw_eq]; exact hmem40_8
            have hs4_ncap : s4.locals.lookup (ofString "ncap") = some (.val (.word (capw * 2#64))) := by
              simp [hs4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have hs4_nlen : s4.locals.lookup (ofString "nlen") = some (.val (.word nlenw)) := by
              simp [hs4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_nlen,
                show ofString "ncap" ≠ ofString "nlen" by decide]
            rw [evaluateHOLFiniteState_ite]
            have hcmp_nc : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
                (.cmp .lower (.var .local (ofString "ncap")) (.var .local (ofString "nlen"))) =
                some (.val (.word (if capw * 2#64 < nlenw then 1 else 0))) := by
              simp [evalHOLExact, hs4_ncap, hs4_nlen, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
            rw [hcmp_nc]; dsimp only
            by_cases hlt_nl : capw * 2#64 < nlenw
            · simp only [hlt_nl, ↓reduceIte, h10, evaluateHOLFiniteState_assign]
              have hev_add1024 : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
                  (.op .add [.var .local (ofString "nlen"), .const 1024#64]) =
                  some (.val (.word (nlenw + 1024#64))) := by
                simp [evalHOLExact, evalListHOLExact, hs4_nlen, wordOpHOL, wordOp, valueIsWord, valueWord]
              have hval_nc : s4.isValidValueHOLFinite .local (ofString "ncap") (.val (.word (nlenw + 1024#64))) = true := by
                simp [isValidValueHOLFinite, lookupKvarHOLFinite, hs4_ncap, shapeOfHOLExact, shapeEqHOL]
              rw [hev_add1024]; dsimp only; rw [if_pos hval_nc]
              let s5 := setKvarHOLFinite .local (ofString "ncap") (.val (.word (nlenw + 1024#64))) s4
              have h1024_n : (1024#64 : BitVec 64).toNat = 1024 := rfl
              have hnl1024_nat : (nlenw + 1024#64).toNat = nlenw.toNat + 1024 := by
                rw [BitVec.toNat_add, h1024_n, Nat.mod_eq_of_lt (by omega)]
              refine ⟨s5, nlenw + 1024#64, rfl, by cases s; rfl, ?_, ?_, ?_, ?_, ?_, by omega, by omega, by omega, by omega⟩
              · simp [s5, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              · simp [s5, hs4, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_cap,
                  show ofString "ncap" ≠ ofString "cap" by decide]
              · simp [s5, hs4, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_len,
                  show ofString "ncap" ≠ ofString "len" by decide]
              · simp [s5, hs4, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_nlen,
                  show ofString "ncap" ≠ ofString "nlen" by decide]
              · simp [s5, hs4, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_eb,
                  show ofString "ncap" ≠ ofString "expand_by" by decide]
            · simp only [hlt_nl, ↓reduceIte, evaluateHOLFiniteState_skip]
              have hge_nl : nlenw.toNat ≤ (capw * 2#64).toNat := by
                rw [BitVec.lt_def] at hlt_nl; omega
              refine ⟨s4, capw * 2#64, rfl, by cases s; rfl, hs4_ncap, ?_, ?_, hs4_nlen, ?_, hge_nl, by omega, by omega, by omega⟩
              · simp [hs4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_cap,
                  show ofString "ncap" ≠ ofString "cap" by decide]
              · simp [hs4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_len,
                  show ofString "ncap" ≠ ofString "len" by decide]
              · simp [hs4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_eb,
                  show ofString "ncap" ≠ ofString "expand_by" by decide]
          obtain ⟨s5, ncapw, hs5_run, hs5_eq, hs5_ncap, hs5_cap, hs5_len, hs5_nlen, hs5_eb,
            hnlen_le_ncap, hcap_lt_ncap, hncap_lt, hncap_al8⟩ := hite_ncap
          rw [evaluateHOLFiniteState_seq_line780, hs5_run] at hnt ⊢; dsimp only at hnt ⊢
          set diffw := ncapw - capw
          have hdiff_nat : diffw.toNat = ncapw.toNat - capw.toNat :=
            BitVec.toNat_sub_of_le (BitVec.le_def.2 (Nat.le_of_lt hcap_lt_ncap))
          -- Evaluate `.call (some (none, none)) "frame_mem_alloc" [ncap - cap]` followed by `memzero` and `store`:
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt ⊢
          have hs5_code : s5.code = originalRuntimeCode := by rw [hs5_eq]; exact hcode
          have hargs_fma : evalListHOLFinite s5 (h := fun a => Classical.propDecidable (s5.memaddrs a))
              [.op .sub [.var .local (ofString "ncap"), .var .local (ofString "cap")]] =
              some [.val (.word diffw)] := by
            simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs5_ncap, hs5_cap,
              wordOpHOL, wordOp, valueIsWord, valueWord, diffw]
          have hlk_fma := pan_one_word_lookup s5.code.lookup (ofString "frame_mem_alloc") (ofString "n")
            (sourceFnBody Guest.Software.guestFn_frame_mem_alloc) diffw
            (by rw [hs5_code]; exact lookup_frame_mem_alloc)
          rw [hargs_fma] at hnt ⊢; dsimp only at hnt ⊢
          rw [hlk_fma] at hnt ⊢; dsimp only at hnt ⊢
          by_cases hs5_clk0 : s5.clock = 0
          · rw [if_pos hs5_clk0] at hnt; simp at hnt
          · rw [if_neg hs5_clk0] at hnt ⊢
            let fmaCallee := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word diffw))
            let fmaEntry := callEntryStateHOLFinite s5 fmaCallee
            have hfma_code : fmaEntry.code = originalRuntimeCode := hs5_code
            have hfma_no_evmErr := frame_mem_alloc_body_no_evmErr fmaEntry hfma_code
            rcases hfma_run : evaluateHOLFiniteState fmaEntry
                (sourceFnBody Guest.Software.guestFn_frame_mem_alloc) with ⟨rfma, fmaPost⟩
            rw [hfma_run] at hfma_no_evmErr
            have hfma_run_raw : evaluateHOLFiniteState
                (callEntryStateHOLFinite s5 (HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word diffw))))
                (sourceFnBody Guest.Software.guestFn_frame_mem_alloc) = (rfma, fmaPost) := hfma_run
            simp only [hfma_run_raw] at hnt ⊢
            cases rfma with
            | none => exact herr_triv
            | some rfma0 =>
              cases rfma0 with
              | timeOut => simp at hnt
              | exception eid ev =>
                dsimp only at hnt ⊢
                by_cases heid : eid = ofString "EvmErr"
                · subst heid; exact absurd ⟨ev, rfl⟩ hfma_no_evmErr
                · constructor
                  · intro _ h; cases h
                  · rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact (heid h1).elim
              | «break» => exact herr_triv
              | «continue» => exact herr_triv
              | finalFfi _ =>
                constructor
                · intro _ h; cases h
                · rintro ⟨_, h⟩; cases h
              | error => exact herr_triv
              | returned vfma =>
                have hfma_fp_lk : fmaEntry.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fp_w)) := by
                  change s5.globals.lookup _ = _; rw [hs5_eq]; exact hfp_lk
                have hfma_sp_lk : fmaEntry.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp_g_w)) := by
                  change s5.globals.lookup _ = _; rw [hs5_eq]; exact hsp_g_lk
                have hfma_n_lk : fmaEntry.locals.lookup (ofString "n") = some (.val (.word diffw)) := by
                  simp [fmaEntry, fmaCallee, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                obtain ⟨rfl, hcmp1_fma, hcmp2_fma, hfmaPost_eq_raw⟩ :=
                  frame_mem_alloc_body_run fmaEntry fp_w sp_g_w diffw
                    hfma_code hfma_fp_lk hfma_sp_lk hfma_n_lk vfma (by rw [hfma_run])
                have hfmaPost_eq : fmaPost = { fmaEntry with
                    globals := fmaEntry.globals.update (ofString "frame_mem_ptr",
                      .val (.word ((fp_w + (diffw + 7)) &&& ((0 : BitVec 64) - 8)))),
                    locals := fmaPost.locals,
                    clock := fmaPost.clock } := by
                  rw [hfma_run] at hfmaPost_eq_raw; exact hfmaPost_eq_raw
                dsimp only [fmaEntry] at hfmaPost_eq
                set qw : BitVec 64 := (fp_w + (diffw + 7)) &&& ((0 : BitVec 64) - 8)
                have hsh_p : shapeEqHOL (shapeOfHOLExact (.val (.word fp_w) : ValueHOL 64)) .one = true := by
                  simp [shapeEqHOL, shapeOfHOLExact]
                dsimp only at hnt ⊢
                simp only [hsh_p, ↓reduceIte] at hnt ⊢
                have hfp_le_sp_g : fp_w.toNat ≤ sp_g_w.toNat := by
                  have := hInv.1.2.2.2.2.1; omega
                have hsp_g_le_se : sp_g_w.toNat ≤ scratchEnd := by
                  have := hInv.1.2.2.2.2.2.1; omega
                have hfp_al8 : fp_w.toNat % 8 = 0 := by
                  have h8 : globN s "frame_mem_ptr" % 8 = 0 := hInv.1.2.2.2.2.2.2.2.1
                  rw [hfp_nat]; exact h8
                obtain ⟨hq_nat, hq_le_sp, hq_al8, hfp_le_q⟩ :=
                  frame_mem_alloc_arith fp_w sp_g_w diffw hfp_le_sp_g hsp_g_le_se hfp_al8 hcmp1_fma hcmp2_fma
                have hqw_nat : qw.toNat = fp_w.toNat + diffw.toNat := by
                  have hdiff_al8' : diffw.toNat % 8 = 0 := by
                    have hcapw_al8 : capw.toNat % 8 = 0 := by rw [hcapw_eq]; exact hmem40_8
                    omega
                  have halign_eq : (diffw.toNat + 7) / 8 * 8 = diffw.toNat := by omega
                  change qw.toNat = _ at hq_nat
                  omega
                have hqw_al8 : qw.toNat % 8 = 0 := hq_al8
                have hqw_le_sp : qw.toNat ≤ sp_g_w.toNat := hq_le_sp
                have hdiff_al8 : diffw.toNat % 8 = 0 := by
                  have hcapw_al8 : capw.toNat % 8 = 0 := by rw [hcapw_eq]; exact hmem40_8
                  omega
                have hdiff_pos : 0 < diffw.toNat := by omega
                set s6 : PanSemStateFiniteExact 64 F := { fmaPost with locals := s5.locals } with hs6_def
                have hs6_glob : s6.globals = s.globals.update (ofString "frame_mem_ptr", .val (.word qw)) := by
                  change fmaPost.globals = _
                  rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq]
                have hs6_code : s6.code = originalRuntimeCode := by
                  change fmaPost.code = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; exact hs5_code
                have hs6_ma : s6.memaddrs = ordinaryDomain := by
                  change fmaPost.memaddrs = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]
                  rw [hs5_eq]; exact hInv.1.1.memaddrs
                have hs6_mem : s6.memory = s.memory := by
                  change fmaPost.memory = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq]
                have hs6_ev : s6.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
                  rw [hs6_glob]
                  simp [HolFiniteMapExact.lookup_update, FUPDATE,
                    show ofString "frame_mem_ptr" ≠ ofString "ev" by decide, hevw]
                have hs6_dom24 : s6.memaddrs (evw + 24#64) := by
                  rw [hs6_ma, ← hInv.1.1.memaddrs]
                  have hev24_eq : evw + 24#64 = BitVec.ofNat 64 (globN s "ev" + 24) := by
                    apply BitVec.eq_of_toNat_eq
                    have : (24#64 : BitVec 64).toNat = 24 := rfl
                    rw [BitVec.toNat_add, hevw_nat, this, BitVec.toNat_ofNat]
                  rw [hev24_eq]
                  exact ((hFW0.1 (globN s "ev", 280) (by simp)).2.2.2 3 (by omega)).choose_spec.1
                rcases hs_m24 : s.memory (evw + 24#64) with ⟨memPtrW⟩
                have hs6_m24 : s6.memory (evw + 24#64) = .word memPtrW := by rw [hs6_mem, hs_m24]
                have hmemPtrW_nat : memPtrW.toNat = memW s (globN s "ev" + 24) := by
                  have hev24_eq : evw + 24#64 = BitVec.ofNat 64 (globN s "ev" + 24) := by
                    apply BitVec.eq_of_toNat_eq
                    have : (24#64 : BitVec 64).toNat = 24 := rfl
                    rw [BitVec.toNat_add, hevw_nat, this, BitVec.toNat_ofNat]
                  unfold memW; rw [← hev24_eq, hs_m24]
                let freshIvl : Ivl := (globN s "frame_mem_ptr", diffw.toNat)
                let mzGrowDst : ExpHOL 64 :=
                  .op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "cap")]
                let mzGrowN : ExpHOL 64 :=
                  .op .sub [.var .local (ofString "ncap"), .var .local (ofString "cap")]
                have hev_mzg_dst : @evalHOLExact 64 F _ s6.toExact (fun a => Classical.propDecidable (s6.memaddrs a)) mzGrowDst =
                    some (.val (.word (memPtrW + capw))) := by
                  have hs6_cap : s6.locals.lookup (ofString "cap") = some (.val (.word capw)) := hs5_cap
                  simp [mzGrowDst, evalHOLExact, evalListHOLExact, hs6_ev, hs6_cap, wordOpHOL, wordOp,
                    valueIsWord, valueWord, memLoadHOLExact, hs6_dom24, hs6_m24]
                have hev_mzg_n : @evalHOLExact 64 F _ s6.toExact (fun a => Classical.propDecidable (s6.memaddrs a)) mzGrowN =
                    some (.val (.word diffw)) := by
                  have hs6_ncap : s6.locals.lookup (ofString "ncap") = some (.val (.word ncapw)) := hs5_ncap
                  have hs6_cap : s6.locals.lookup (ofString "cap") = some (.val (.word capw)) := hs5_cap
                  simp [mzGrowN, evalHOLExact, evalListHOLExact, hs6_ncap, hs6_cap, wordOpHOL, wordOp,
                    valueIsWord, valueWord, diffw]
                have hmzg_dst_nat : (memPtrW + capw).toNat = globN s "frame_mem_ptr" := by
                  rw [BitVec.toNat_add, hmemPtrW_nat, hcapw_eq, hmem_end_fp, Nat.mod_eq_of_lt (by omega)]
                let mzGrowCall : ProgHOL 64 := .call (some (none, none)) (ofString "memzero") [mzGrowDst, mzGrowN]
                rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
                have hnt_mzg : (evaluateHOLFiniteState s6 mzGrowCall).1 ≠ some .timeOut := by
                  intro hto
                  rcases hmzg_to : evaluateHOLFiniteState s6
                      (.call (some (none, none)) (ofString "memzero") [mzGrowDst, mzGrowN]) with ⟨rmzg_to, smzg_to⟩
                  have hto' : rmzg_to = some .timeOut := by
                    dsimp only [mzGrowCall] at hto; rw [hmzg_to] at hto; exact hto
                  subst hto'
                  have hmzg_to_raw : evaluateHOLFiniteState s6
                      (.call (some (none, none)) (ofString "memzero")
                        [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "cap")],
                         .op .sub [.var .local (ofString "ncap"), .var .local (ofString "cap")]]) = (some .timeOut, smzg_to) := hmzg_to
                  simp only [hmzg_to_raw] at hnt
                  exact hnt rfl
                have hmzg := eval_call_memzero_bre s6 mzGrowDst mzGrowN
                  (memPtrW + capw) diffw [freshIvl] hs6_code hs6_ma hev_mzg_dst hev_mzg_n
                  (fun _ => ⟨freshIvl, by simp, by rw [hmzg_dst_nat]; dsimp only [freshIvl]; omega⟩) hnt_mzg
                dsimp only at hmzg
                rcases hmzg_run : evaluateHOLFiniteState s6 mzGrowCall with ⟨rmzg, s7⟩
                rw [hmzg_run] at hmzg
                have hmzg_run_raw : evaluateHOLFiniteState s6
                    (.call (some (none, none)) (ofString "memzero")
                      [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "cap")],
                       .op .sub [.var .local (ofString "ncap"), .var .local (ofString "cap")]]) = (rmzg, s7) := hmzg_run
                simp only [hmzg_run_raw] at hnt ⊢
                cases rmzg with
                | some rmzg0 =>
                  dsimp only at hnt ⊢
                  have hnr := hmzg.2 (by simp)
                  refine ⟨fun v hv => absurd (Or.inl ⟨v, hv⟩) hnr, ?_⟩
                  rintro ⟨ev, hv⟩
                  injection hv with hv'; subst hv'
                  exact absurd (Or.inr ⟨ofString "EvmErr", ev, rfl, by decide⟩) hnr
                | none =>
                  dsimp only at hnt ⊢
                  obtain ⟨heff_mzg, hs7_loc⟩ := hmzg.1 rfl
                  rcases hst40 : evaluateHOLFiniteState s7
                      (.store (.op .add [.var .global (ofString "ev"), .const 40#64]) (.var .local (ofString "ncap"))) with ⟨rst40, s8⟩
                  simp only [hst40] at hnt ⊢
                  cases rst40 with
                  | some res40 =>
                    have herr := store_some_eq_error' hst40; subst herr; dsimp only; exact herr_triv
                  | none =>
                    dsimp only at hnt ⊢
                    have hs7_ev : s7.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
                      rw [heff_mzg.globals]; exact hs6_ev
                    have hs7_ncap : s7.locals.lookup (ofString "ncap") = some (.val (.word ncapw)) := by
                      rw [hs7_loc]; exact hs5_ncap
                    obtain ⟨w_ncap', hw_ncap_ev, hs8_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s7) (post := s8)
                      (gname := "ev") (gbase := globN s "ev") (off := 40) hs7_ev hevw_nat (by omega)
                      (fun v hv => by
                        change s7.locals.lookup (ofString "ncap") = some v at hv
                        rw [hs7_ncap] at hv; injection hv with hv'; exact ⟨ncapw, hv'.symm⟩) hst40
                    have hw_ncap_val : ncapw = w_ncap' := by
                      change s7.locals.lookup (ofString "ncap") = some (.val (.word w_ncap')) at hw_ncap_ev
                      rw [hs7_ncap] at hw_ncap_ev
                      injection hw_ncap_ev with h1; injection h1 with h2; injection h2 with h3
                    subst w_ncap'
                    have heff_st40 := (ByteRegionEffect.of_store_word (Rl := [(globN s "ev", 280)])
                      (heff_mzg.memaddrs.trans hs6_ma) hst40
                      (fun v hv => by
                        change s7.locals.lookup (ofString "ncap") = some v at hv
                        rw [hs7_ncap] at hv; injection hv with hv'; exact ⟨ncapw, hv'.symm⟩)
                      (fun addr hdst _ => by
                        simp [evalHOLExact, evalListHOLExact, hs7_ev, wordOpHOL, wordOp, valueIsWord, valueWord] at hdst
                        have h40_eq : (evw + 40#64).toNat = globN s "ev" + 40 := by
                          have : (40#64 : BitVec 64).toNat = 40 := rfl
                          rw [BitVec.toNat_add, hevw_nat, this, Nat.mod_eq_of_lt (by omega)]
                        exact ⟨(globN s "ev", 280), by simp, by rw [← hdst, h40_eq]; dsimp only; omega,
                          by rw [← hdst, h40_eq]; dsimp only; omega⟩)).1
                    let m : PanSemStateFiniteExact 64 F :=
                      { s8 with locals := s8.locals.resVarEq (ofString "ncap", s3.locals.lookup (ofString "ncap")) }
                    change (let out := evaluateHOLFiniteState m tailProg
                      let post := { out.2 with
                        locals := ((out.2.locals.resVarEq (ofString "nlen", s2.locals.lookup (ofString "nlen"))).resVarEq
                          (ofString "cap", s1.locals.lookup (ofString "cap"))).resVarEq
                          (ofString "len", s.locals.lookup (ofString "len")) }
                      (∀ v, out.1 = some (.returned v) →
                        EvmInv post ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s ∧
                        (∀ g : String, ofString g ≠ ofString "frame_mem_ptr" → globN post g = globN s g)) ∧
                      (IsEvmErr out.1 →
                        EvmInv post ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s))
                    have hm_glob : m.globals = s.globals.update (ofString "frame_mem_ptr", .val (.word qw)) := by
                      dsimp only [m]; rw [hs8_eq]; dsimp only; rw [heff_mzg.globals, hs6_glob]
                    have hm_fp_glob : globN m "frame_mem_ptr" = qw.toNat := by
                      unfold globN; rw [hm_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
                    have hm_other_glob : ∀ g : String, ofString g ≠ ofString "frame_mem_ptr" →
                        m.globals.lookup (ofString g) = s.globals.lookup (ofString g) := by
                      intro g hg; rw [hm_glob]
                      simp [HolFiniteMapExact.lookup_update, FUPDATE, hg, Ne.symm hg]
                    have hm_G : GuestInv m := by
                      have hcode_m : m.code = s.code := by
                        dsimp only [m]; rw [hs8_eq]; dsimp only; rw [heff_mzg.code, hs6_code, hcode]
                      have hma_m : m.memaddrs = s.memaddrs := by
                        dsimp only [m]; rw [hs8_eq]; dsimp only; rw [heff_mzg.memaddrs, hs6_ma, hInv.1.1.memaddrs]
                      have hsh_m : m.shMemaddrs = s.shMemaddrs := by
                        dsimp only [m]; rw [hs8_eq]; dsimp only; rw [heff_mzg.shMemaddrs]
                        change fmaPost.shMemaddrs = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq]
                      have hba_m : m.baseAddr = s.baseAddr := by
                        dsimp only [m]; rw [hs8_eq]; dsimp only; rw [heff_mzg.baseAddr]
                        change fmaPost.baseAddr = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq]
                      exact guestInv_congr hcode_m hma_m hsh_m hba_m hInv.1.1
                    have hfm_m : globN s "frame_mem_ptr" ≤ globN m "frame_mem_ptr" := by
                      rw [hm_fp_glob, hqw_nat, hfp_nat]; omega
                    have hAm : ArenaReady m := by
                      refine ⟨hm_G, ?_⟩
                      unfold ArenaOK
                      have hhp_m : globN m "heap_ptr" = globN s "heap_ptr" :=
                        R16Shards.OpHandlers.globN_eq_of_lookup_eq (hm_other_glob "heap_ptr" (by decide))
                      have hsp_m : globN m "scratch_ptr" = globN s "scratch_ptr" :=
                        R16Shards.OpHandlers.globN_eq_of_lookup_eq (hm_other_glob "scratch_ptr" (by decide))
                      rw [hhp_m, hm_fp_glob, hsp_m]
                      have hA := hInv.1.2
                      have hss_le_fp : scratchStart ≤ globN s "frame_mem_ptr" := hA.2.2.1
                      exact ⟨hA.1, hA.2.1, by rw [hqw_nat, hfp_nat]; omega, by rw [← hsp_g_nat]; exact hqw_le_sp,
                        hA.2.2.2.2.1, hA.2.2.2.2.2.1, hqw_al8, hA.2.2.2.2.2.2.2.1,
                        globalsWord_update (ofString "frame_mem_ptr") qw hm_glob hA.2.2.2.2.2.2.2.2⟩
                    have heff_s_s6 : FrameMemByteEff s s6 [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))] :=
                      ⟨hs6_code.trans hcode.symm,
                       hs6_ma.trans hInv.1.1.memaddrs.symm,
                       by change fmaPost.shMemaddrs = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq],
                       by change fmaPost.baseAddr = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq],
                       by change fmaPost.be = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq],
                       fun g hg => by
                         change fmaPost.globals.lookup (ofString g) = _; rw [hfmaPost_eq]
                         dsimp only [callEntryStateHOLFinite]; rw [hs5_eq]
                         simp [HolFiniteMapExact.lookup_update, FUPDATE, hg, Ne.symm hg],
                       fun a _ => by rw [hs6_mem],
                       fun a _ => by rw [hs6_mem],
                       fun b _ _ => by
                         unfold memB; rw [hs6_mem]
                         have hbe6 : s6.be = s.be := by
                           change fmaPost.be = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq]
                         rw [hbe6]⟩
                    have heff_m : FrameMemByteEff s m
                        [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))] := by
                      have h1 := (FrameMemByteEff.of_bre heff_mzg).mono
                        (R2 := [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))])
                        (fun x hx => by simp at hx; subst hx; exact ⟨freshIvl, by simp, le_refl _, le_refl _⟩)
                      have h2 := (FrameMemByteEff.of_bre heff_st40).mono
                        (R2 := [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))])
                        (fun x hx => by simp at hx; subst hx; exact ⟨(globN s "ev", 280), by simp, le_refl _, le_refl _⟩)
                      exact ((heff_s_s6.trans h1).trans h2).with_locals_clock m.locals s8.clock
                    have hs7_e0_eq : ∀ off, off + 8 ≤ 280 → off % 8 = 0 →
                        memW s7 (globN s "ev" + off) = memW s (globN s "ev" + off) := by
                      intro off hoff hoff8
                      unfold memW
                      rw [heff_mzg.cell_frame (BitVec.ofNat 64 (globN s "ev" + off)), hs6_mem]
                      intro x hx; simp at hx; subst hx
                      have htn : (BitVec.ofNat 64 (globN s "ev" + off)).toNat = globN s "ev" + off :=
                        Nat.mod_eq_of_lt (by omega)
                      rw [htn]
                      have he0_8 : (globN s "ev") % 8 = 0 := (hFW0.1 (globN s "ev", 280) (by simp)).2.1
                      have ha8 : (globN s "ev" + off) % 8 = 0 := by omega
                      have hfp_s_8 : globN s "frame_mem_ptr" % 8 = 0 := hInv.1.2.2.2.2.2.2.2.1
                      obtain ⟨he0_scr, _⟩ := (hFW0.1 (globN s "ev", 280) (by simp)).1
                      exact not_cellHits_of_disj_aligned (i := (globN s "ev", 280)) ha8 hfp_s_8
                        (Nat.le_add_right _ off) (Nat.add_le_add_left hoff _)
                        (Or.inr (Or.inr (Or.inr (by dsimp only [freshIvl] at he0_scr ⊢; omega))))
                    have hm_e0_other : ∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 32 → off ≠ 40 →
                        memW m (globN s "ev" + off) = memW s (globN s "ev" + off) := by
                      intro off hoff hoff8 _ hne40
                      change memW s8 (globN s "ev" + off) = memW s (globN s "ev" + off)
                      rw [hs8_eq, R14Shards.OpHandlersA.memW_updW_ne s7 (globN s "ev" + 40) (globN s "ev" + off) _ (by omega) (by omega) (by omega),
                          hs7_e0_eq off hoff hoff8]
                    have hm_e0_40 : memW m (globN s "ev" + 40) = ncapw.toNat := by
                      change memW s8 (globN s "ev" + 40) = ncapw.toNat
                      rw [hs8_eq, R14Shards.OpHandlersA.memW_updW_same s7 (globN s "ev" + 40) ncapw]
                    have hfresh_m : freshIvl = (0, 0) ∨
                        (freshIvl.1 % 8 = 0 ∧ freshIvl.2 % 8 = 0 ∧
                          Inside freshIvl (globN s "frame_mem_ptr") (globN m "frame_mem_ptr")) := by
                      refine Or.inr ⟨hInv.1.2.2.2.2.2.2.2.1, hdiff_al8, ?_⟩
                      rw [hm_fp_glob, hqw_nat, hfp_nat]; dsimp only [freshIvl, Inside]; omega
                    have hnew_m :
                        (freshIvl.2 = 0 ∧ memW m (globN s "ev" + 40) = memW s (globN s "ev" + 40)) ∨
                        (freshIvl.2 ≠ 0 ∧
                          memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = freshIvl.1 ∧
                          memW m (globN s "ev" + 40) = memW s (globN s "ev" + 40) + freshIvl.2) := by
                      refine Or.inr ⟨by dsimp only [freshIvl]; omega, hmem_end_fp, ?_⟩
                      rw [hm_e0_40]; dsimp only [freshIvl]; omega
                    have hm_loc_s5 : ∀ k, k ≠ ofString "ncap" → m.locals.lookup k = s5.locals.lookup k := by
                      intro k hk
                      have hres_ne : ∀ (mp : HolFiniteMapExact MlS (ValueHOL 64)) (key q : MlS) (old : Option (ValueHOL 64)),
                          key ≠ q → (mp.resVarEq (key, old)).lookup q = mp.lookup q := by
                        intro mp key q old hne
                        unfold HolFiniteMapExact.resVarEq
                        cases old with
                        | none => simp [HolFiniteMapExact.eraseEq, FDOMSUB_HOL, hne.symm]
                        | some v => simp [HolFiniteMapExact.updateEq, FUPDATE_HOL, hne.symm]
                      have hs8_l : s8.locals = s5.locals := by rw [hs8_eq]; exact hs7_loc
                      dsimp only [m]
                      rw [hres_ne _ _ _ _ hk.symm, hs8_l]
                    have hnt_m : (evaluateHOLFiniteState m tailProg).1 ≠ some .timeOut := by
                      dsimp only [m]
                      exact hnt
                    exact run_tail m freshIvl hAm hfm_m hm_other_glob heff_m hfresh_m hm_e0_other hnew_m
                      (by rw [hm_e0_40]; exact hnlen_le_ncap)
                      (by rw [hm_loc_s5 (ofString "len") (by decide)]; exact hs5_len)
                      (by rw [hm_loc_s5 (ofString "nlen") (by decide)]; exact hs5_nlen)
                      (by rw [hm_loc_s5 (ofString "expand_by") (by decide)]; exact hs5_eb)
                      hnt_m
        · have hnlen_le_cap : nlenw.toNat ≤ capw.toNat := by
            rw [BitVec.lt_def] at hgrow; omega
          simp only [hgrow, ↓reduceIte, evaluateHOLFiniteState_skip] at hnt ⊢
          exact run_tail s3 (0, 0)
            ⟨guestInv_congr (s := s) rfl rfl rfl rfl hInv.1.1, hInv.1.2⟩
            (le_refl _)
            (fun _ _ => rfl)
            ((FrameMemByteEff.refl s _).with_locals_clock s3.locals s.clock)
            (Or.inl rfl)
            (fun _ _ _ _ _ => rfl)
            (Or.inl ⟨rfl, rfl⟩)
            (by change nlenw.toNat ≤ memW s (globN s "ev" + 40); rw [← hcapw_eq]; exact hnlen_le_cap)
            hs3_len hs3_nlen hs3_eb hnt

theorem lookup_op_keccak :
    originalRuntimeCode.lookup (ofString "op_keccak") =
      some ([], sourceFnBody Guest.Software.guestFn_op_keccak, .one) :=
  lookup_of_guestAst_getElem 501 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_op_keccak) rfl

private theorem headMemAligned_congr_head_only {F : Type}
    {s t : PanSemStateFiniteExact 64 F}
    (hg : t.globals = s.globals)
    (hmem : ∀ off : Nat, off ∈ ([24, 32, 40] : List Nat) →
      memW t (globN s "ev" + off) = memW s (globN s "ev" + off))
    (h : HeadMemAligned s) : HeadMemAligned t := by
  have hgev : globN t "ev" = globN s "ev" := globN_eq_of_lookup_eq (by rw [hg])
  have hgfp : globN t "frame_mem_ptr" = globN s "frame_mem_ptr" := globN_eq_of_lookup_eq (by rw [hg])
  refine ⟨?_, ?_⟩
  · rw [hgev, hmem 32 (by simp)]; exact h.1
  · rw [hgev, hgfp, hmem 24 (by simp), hmem 40 (by simp)]; exact h.2

private theorem eps_stack_pop_preserves_headMem :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post =>
        post.globals = s.globals ∧
        (HeadMemAligned s → HeadMemAligned post))
      (ofString "stack_pop") := by
  refine ⟨_, _, _, lookup_stack_pop_pub, ?_⟩
  intro F s hcode hInv _ hlookup hnt
  obtain ⟨params_sp, body_sp, ret_sp, hlk_sp, hspec_sp⟩ := eps_stack_pop
  have hlk_eq : some ([], sourceFnBody Guest.Software.guestFn_stack_pop, ShapeHOL.comb [.one, .one, .one, .one]) =
      some (params_sp, body_sp, ret_sp) := lookup_stack_pop_pub.symm.trans hlk_sp
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_sp, rfl⟩
  subst hbody_sp
  have hs := hspec_sp s hcode hInv trivial hlookup hnt
  dsimp only at hs ⊢
  refine ⟨fun v hv => ?_, hs.2⟩
  obtain ⟨hInv_p, hch_p, hR_p, hglob_p⟩ := hs.1 v hv
  refine ⟨hInv_p, hch_p, hR_p, hglob_p, ?_⟩
  intro hHM
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by simp [evmChain, evmChainFrom]
  have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead_mem
  have hb_ev := (frameWF_bounds hInv.1.2 hFW0).1
  dsimp only at hb_ev
  have hev_pos : 0 < globN s "ev" := by
    obtain ⟨hin, _⟩ := (hFW0.1 (globN s "ev", 280) (by simp)).1
    have h1 := hInv.1.2.2.2.1; have h2 := hInv.1.2.2.2.2.1
    rw [R11Shards.scratchStart_val] at h1; dsimp only at hin; omega
  obtain ⟨evw, hevw, hevw_nat⟩ := global_word_of_pos s "ev" hev_pos
  let retExp : ExpHOL 64 :=
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural
      (Exp.load (Shape.comb [Shape.one, Shape.one, Shape.one, Shape.one])
        (Exp.op BinOp.add [(Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.global "ev"), (Exp.const (BitVec.ofNat 64 8))])),
          (Exp.panOp PanOp.mul [(Exp.var VarKind.local "sp"), (Exp.const (BitVec.ofNat 64 32))])]))
  have hb : sourceFnBody Guest.Software.guestFn_stack_pop =
      .dec (ofString "sp") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 16]))
        (.seq
          (.ite (.cmp .equal (.var .local (ofString "sp")) (.const 0))
            (.raise (ofString "EvmErr") (.const 2))
            .skip)
          (.seq
            (.assign .local (ofString "sp") (.op .sub [.var .local (ofString "sp"), .const 1]))
            (.seq
              (.store (.op .add [.var .global (ofString "ev"), .const 16]) (.var .local (ofString "sp")))
              (.return retExp)))) := rfl
  have hmem_ne16 : ∀ x : BitVec 64, x ≠ BitVec.ofNat 64 (globN s "ev" + 16) →
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_stack_pop)).2.memory x = s.memory x := by
    revert hv
    rw [hb, evaluateHOLFiniteState_dec_total]; dsimp only
    split
    · simp
    · rename_i vsp _
      split
      · dsimp only
        set s1 := setVarHOLFinite (ofString "sp") vsp s
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
        split
        · split
          · simp only [evaluateHOLFiniteState_skip]
            rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
            split
            · simp
            · rename_i sp1 hsp1
              have hsp1_w : ∃ w : BitVec 64, sp1 = .val (.word w) := by
                simp only [evalHOLExact, wordOpHOL] at hsp1; revert hsp1
                rcases @evalListHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a)) _ with _ | vs
                · simp
                · dsimp only; split
                  · simp only [Option.map]
                    rcases wordOp .sub (vs.map valueWord) with _ | w
                    · simp
                    · intro h'; injection h' with h''; exact ⟨w, h''.symm⟩
                  · simp
              obtain ⟨spw, rfl⟩ := hsp1_w
              split
              · dsimp only
                set s2 := setKvarHOLFinite .local (ofString "sp") (.val (.word spw)) s1
                rw [evaluateHOLFiniteState_seq_line780]
                rcases hst : evaluateHOLFiniteState s2
                    (.store (.op .add [.var .global (ofString "ev"), .const 16]) (.var .local (ofString "sp"))) with ⟨r2, s3⟩
                cases r2 with
                | some res2 =>
                  have herr := store_some_eq_error' hst; subst herr; simp
                | none =>
                  dsimp only
                  obtain ⟨w2, _, hs3_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s2) (post := s3)
                    (gname := "ev") (gbase := globN s "ev") (off := 16) hevw hevw_nat (by omega)
                    (fun u hu => by
                      have hsp2 : s2.locals.lookup (ofString "sp") = some (.val (.word spw)) := by
                        simp [s2, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                      change s2.locals.lookup (ofString "sp") = some u at hu
                      rw [hsp2] at hu; injection hu with hu'; exact ⟨spw, hu'.symm⟩) hst
                  intro _ x hx
                  rw [evaluateHOLFiniteState_return]
                  split
                  · dsimp only; rw [hs3_eq]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hx]; rfl
                  · split
                    · dsimp only [emptyLocalsHOLFinite]; rw [hs3_eq]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hx]; rfl
                    · dsimp only; rw [hs3_eq]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hx]; rfl
              · simp
          · rcases hraise : evaluateHOLFiniteState s1 (.raise (ofString "EvmErr") (.const 2)) with ⟨rr, sr⟩
            have hr_nn : rr ≠ none ∧ sr.globals = s.globals ∧ sr.memory = s.memory := by
              rw [evaluateHOLFiniteState_raise] at hraise; dsimp only [evalHOLExact] at hraise
              split at hraise
              · split at hraise <;> (injection hraise with h1 h2; subst h1 h2; exact ⟨by simp, rfl, rfl⟩)
              · injection hraise with h1 h2; subst h1 h2; exact ⟨by simp, rfl, rfl⟩
            cases rr with
            | none => exact absurd rfl hr_nn.1
            | some r0 =>
              dsimp only
              intro hres
              cases r0 <;> simp at hres
              rename_i vr
              subst hres
              intro x _
              change sr.memory x = s.memory x
              rw [hr_nn.2.2]
        · simp
      · simp
  refine headMemAligned_congr_head_only hglob_p (fun off hoff => ?_) hHM
  have hne_bv : BitVec.ofNat 64 (globN s "ev" + off) ≠ BitVec.ofNat 64 (globN s "ev" + 16) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    intro heq
    have htn := congrArg BitVec.toNat heq
    rcases hoff with rfl | rfl | rfl <;>
      (rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at htn; omega)
  unfold memW; rw [hmem_ne16 _ hne_bv]

private theorem seq_charge_gas_preserves_headMem {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {amtExp : ExpHOL 64} {cont : ProgHOL 64}
    (hpos : ∀ t (w : BitVec 64),
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp =
        some (.val (.word w)) →
      EvmInv t → P t → 0 < w.toNat)
    (hstep : ∀ t cpost,
      EvmInv t → P t → EvmInv cpost → cpost.globals = t.globals →
      evmChain cpost = evmChain t →
      (∀ off : Nat, off ∈ ([24, 32, 40] : List Nat) →
        memW cpost (globN t "ev" + off) = memW t (globN t "ev" + off)) →
      Q { cpost with locals := t.locals })
    (hcont : HandlerRun s0 Q true cont) :
    HandlerRun s0 P charged (.seq (.call (some (none, none)) (ofString "charge_gas") [amtExp]) cont) := by
  intro t hc hInv hlen hR hP hnt
  have hR_le : OpDispatchSpec.evmR t ≤ OpDispatchSpec.evmR s0 := by
    cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at hR <;> omega
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) [amtExp] with _ | values
  · exact opDispatchPost_error s0 t
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup (ofString "charge_gas") values with _ | ⟨body', callee, ret'⟩
    · exact opDispatchPost_error s0 t
    · simp only [hl] at hnt ⊢
      by_cases hz : t.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hv_list : ∃ v0, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp = some v0 ∧ values = [v0] := by
          rw [evalListHOLFinite_eq_toExact] at hargs
          simp only [evalListHOLExact] at hargs
          rcases he : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp with _ | v0
          · simp [he] at hargs
          · simp only [he, Option.some.injEq] at hargs; exact ⟨v0, rfl, hargs.symm⟩
        obtain ⟨v0, hv0_ev, rfl⟩ := hv_list
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "charge_gas") [v0] =
            some (body', callee, ret') := by rwa [← hc]
        obtain ⟨rfl, rfl, amtw, rfl, hamt_cal⟩ := one_word_arg_lookup M21.lookup_charge_gas hl_orig
        have hamt_pos : 0 < amtw.toNat := hpos t amtw hv0_ev hInv hP
        have hInv_ce : EvmInv (callEntryStateHOLFinite t callee) := localsFree_evmInv t callee (t.clock - 1) hInv
        have hc_ce := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
          (callEntryStateHOLFinite t callee) (sourceFnBody Guest.Software.guestFn_charge_gas)).1
        have hcg := charge_gas_body_exact (callEntryStateHOLFinite t callee) hInv_ce hamt_cal
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee)
            (sourceFnBody Guest.Software.guestFn_charge_gas) with ⟨res, cpost⟩
        simp only [hrun] at hnt hmeta hcg ⊢
        let ce := callEntryStateHOLFinite t callee
        change cpost.code = t.code at hmeta
        cases res with
        | none => exact opDispatchPost_error s0 cpost
        | some r0 =>
          cases r0 with
          | timeOut => simp at hnt
          | returned v =>
            by_cases hsh_ok : shapeEqHOL (shapeOfHOLExact v) .one = true
            · simp only [hsh_ok, ↓reduceIte] at hnt ⊢
              obtain ⟨hInv_cp, hglob_cp, hch_cp, hR_cp⟩ := hcg.1 v rfl
              have hmem_head_cp : ∀ off : Nat, off ∈ ([24, 32, 40] : List Nat) →
                  memW cpost (globN t "ev" + off) = memW t (globN t "ev" + off) := by
                intro off hoff
                have hhead_mem : (globN t "ev", globN t "cur_cont") ∈ evmChain t := by simp [evmChain, evmChainFrom]
                have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead_mem
                have hb_ev := (frameWF_bounds hInv.1.2 hFW0).1
                dsimp only at hb_ev
                have hev_pos : 0 < globN t "ev" := by
                  obtain ⟨hin, _⟩ := (hFW0.1 (globN t "ev", 280) (by simp)).1
                  have h1 := hInv.1.2.2.2.1; have h2 := hInv.1.2.2.2.2.1
                  rw [R11Shards.scratchStart_val] at h1; dsimp only at hin; omega
                obtain ⟨evw, hevw, hevw_nat⟩ := global_word_of_pos t "ev" hev_pos
                have hevw_ce : ce.globals.lookup (ofString "ev") = some (.val (.word evw)) := hevw
                have hbody_cg : sourceFnBody Guest.Software.guestFn_charge_gas =
                    .dec (ofString "gl") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 64]))
                      (.seq
                        (.ite (.cmp .lower (.var .local (ofString "gl")) (.var .local (ofString "amount")))
                          (.raise (ofString "EvmErr") (.const 4))
                          .skip)
                        (.seq
                          (.store (.op .add [.var .global (ofString "ev"), .const 64])
                            (.op .sub [.var .local (ofString "gl"), .var .local (ofString "amount")]))
                          (.seq
                            (.store (.op .add [.var .global (ofString "ev"), .const 184])
                              (.op .add
                                [.load .one (.op .add [.var .global (ofString "ev"), .const 184]),
                                 .var .local (ofString "amount")]))
                            (.return (.const 0))))) := rfl
                have hmem_ne : ∀ x : BitVec 64,
                    x ≠ BitVec.ofNat 64 (globN t "ev" + 64) →
                    x ≠ BitVec.ofNat 64 (globN t "ev" + 184) →
                    cpost.memory x = t.memory x := by
                  have hrun' := hrun
                  rw [hbody_cg, evaluateHOLFiniteState_dec_total] at hrun'; dsimp only at hrun'
                  split at hrun'
                  · simp at hrun'
                  · rename_i glv _
                    split at hrun'
                    · set s1 := setVarHOLFinite (ofString "gl") glv ce
                      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hrun'
                      split at hrun'
                      · split at hrun'
                        · simp only [evaluateHOLFiniteState_skip] at hrun'
                          rw [evaluateHOLFiniteState_seq_line780] at hrun'
                          rcases hst1 : evaluateHOLFiniteState s1
                              (.store (.op .add [.var .global (ofString "ev"), .const 64])
                                (.op .sub [.var .local (ofString "gl"), .var .local (ofString "amount")])) with ⟨r1, s2⟩
                          rw [hst1] at hrun'
                          cases r1 with
                          | some res1 =>
                            have herr1 := store_some_eq_error' hst1; subst herr1; simp at hrun'
                          | none =>
                            dsimp only at hrun'
                            obtain ⟨w1, _, hs2_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s1) (post := s2)
                              (gname := "ev") (gbase := globN t "ev") (off := 64) hevw_ce hevw_nat (by omega)
                              (fun u hu => by
                                simp only [evalHOLExact, wordOpHOL] at hu; revert hu
                                rcases @evalListHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a)) _ with _ | vs
                                · simp
                                · dsimp only; split
                                  · simp only [Option.map]
                                    rcases wordOp .sub (vs.map valueWord) with _ | w
                                    · simp
                                    · intro h'; injection h' with h''; exact ⟨w, h''.symm⟩
                                  · simp) hst1
                            rw [evaluateHOLFiniteState_seq_line780] at hrun'
                            rcases hst2 : evaluateHOLFiniteState s2
                                (.store (.op .add [.var .global (ofString "ev"), .const 184])
                                  (.op .add
                                    [.load .one (.op .add [.var .global (ofString "ev"), .const 184]),
                                     .var .local (ofString "amount")])) with ⟨r2, s3⟩
                            rw [hst2] at hrun'
                            cases r2 with
                            | some res2 =>
                              have herr2 := store_some_eq_error' hst2; subst herr2; simp at hrun'
                            | none =>
                              dsimp only at hrun'
                              obtain ⟨w2, _, hs3_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s2) (post := s3)
                                (gname := "ev") (gbase := globN t "ev") (off := 184)
                                (by rw [hs2_eq]; exact hevw_ce) hevw_nat (by omega)
                                (fun u hu => by
                                  simp only [evalHOLExact, wordOpHOL] at hu; revert hu
                                  rcases @evalListHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a)) _ with _ | vs
                                  · simp
                                  · dsimp only; split
                                    · simp only [Option.map]
                                      rcases wordOp .add (vs.map valueWord) with _ | w
                                      · simp
                                      · intro h'; injection h' with h''; exact ⟨w, h''.symm⟩
                                    · simp) hst2
                              rw [evaluateHOLFiniteState_return] at hrun'; dsimp only [evalHOLExact] at hrun'
                              have hsz0 : sizeOfShapeWithContextHOL s3.structs
                                  (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
                                simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
                              rw [if_pos hsz0] at hrun'; dsimp only at hrun'
                              injection hrun' with _ hcpost_eq
                              subst hcpost_eq
                              intro x hx64 hx184
                              dsimp only [emptyLocalsHOLFinite]
                              rw [hs3_eq]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hx184]
                              rw [hs2_eq]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hx64]
                              rfl
                        · rcases hraise : evaluateHOLFiniteState s1 (.raise (ofString "EvmErr") (.const 4)) with ⟨rr, sr⟩
                          rw [hraise] at hrun'
                          have hr_nn : rr ≠ none := by
                            rw [evaluateHOLFiniteState_raise] at hraise; dsimp only [evalHOLExact] at hraise
                            split at hraise
                            · split at hraise <;> (injection hraise with h1 _; subst h1; simp)
                            · injection hraise with h1 _; subst h1; simp
                          cases rr with
                          | none => exact absurd rfl hr_nn
                          | some r0 =>
                            dsimp only at hrun'
                            have hr_not_ret : ∀ vr, r0 ≠ .returned vr := by
                              rw [evaluateHOLFiniteState_raise] at hraise; dsimp only [evalHOLExact] at hraise
                              split at hraise
                              · split at hraise <;> (injection hraise with h1 _; injection h1 with h1'; subst h1'; simp)
                              · injection hraise with h1 _; injection h1 with h1'; subst h1'; simp
                            cases r0 with
                            | returned vr => exact absurd rfl (hr_not_ret vr)
                            | _ => simp at hrun'
                      · simp at hrun'
                    · simp at hrun'
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
                have hne64 : BitVec.ofNat 64 (globN t "ev" + off) ≠ BitVec.ofNat 64 (globN t "ev" + 64) := by
                  intro heq; have htn := congrArg BitVec.toNat heq
                  rcases hoff with rfl | rfl | rfl <;>
                    (rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at htn; omega)
                have hne184 : BitVec.ofNat 64 (globN t "ev" + off) ≠ BitVec.ofNat 64 (globN t "ev" + 184) := by
                  intro heq; have htn := congrArg BitVec.toNat heq
                  rcases hoff with rfl | rfl | rfl <;>
                    (rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at htn; omega)
                unfold memW; rw [hmem_ne _ hne64 hne184]
              let resumed : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
              have hInv_res : EvmInv resumed := localsFree_evmInv cpost t.locals cpost.clock hInv_cp
              have hc_res := evm_congr (s := cpost) (t := resumed) rfl rfl
              have hlen_res : (evmChain resumed).length = (evmChain s0).length := by
                rw [hc_res.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              have hR_lt : OpDispatchSpec.evmR resumed < OpDispatchSpec.evmR s0 := by
                rw [hc_res.2.1]; rw [hc_ce.2.1] at hR_cp; omega
              have hR_lt_if : if true then OpDispatchSpec.evmR resumed < OpDispatchSpec.evmR s0 else OpDispatchSpec.evmR resumed ≤ OpDispatchSpec.evmR s0 := by
                simp only [↓reduceIte]; exact hR_lt
              exact hcont resumed (hmeta.trans hc) hInv_res hlen_res hR_lt_if
                (hstep t cpost hInv hP hInv_cp hglob_cp (hch_cp.trans (evmChain_congr rfl rfl)) hmem_head_cp)
                (by simpa [resumed] using hnt)
            · simp only [hsh_ok, Bool.false_eq_true, ↓reduceIte]
              exact opDispatchPost_error s0 cpost
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨hInv_cp, _, hch_cp, hR_cp⟩ := hcg.2 ⟨ev, rfl⟩
              have hInv_el : EvmInv cpost.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost _ cpost.clock hInv_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              refine ⟨?_, fun _ => ⟨hInv_el, ?_, ?_⟩⟩
              · rintro ⟨_, h⟩; cases h
              · rw [hc_el.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              · rw [hc_el.2.1, hR_cp, hc_ce.2.1]; exact hR_le
            · refine opDispatchPost_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => exact opDispatchPost_error s0 cpost
          | «continue» => exact opDispatchPost_error s0 cpost
          | finalFfi _ =>
            refine opDispatchPost_other (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => exact opDispatchPost_error s0 cpost.emptyLocalsHOLFinite

/-- Shared tail of `op_keccak` after `extend_memory(x.1)` at `charged = true`:
    `mark := heap_mark()`, `out := alloc(32)`, `s := sat_word(start)`,
    `keccak256(load(ev+24) + s, n, out)`, `v := u256_from_be(out, 32)`,
    `heap_release(mark)`, `stack_push(v)`, `pc_add(1)`, `return 0`. -/
private theorem op_keccak_post_extend_run {F : Type} (s0 : PanSemStateFiniteExact 64 F) :
    HandlerRun s0 (fun _ => True) true
      (.decCall (ofString "mark") .one (ofString "heap_mark") []
        (.decCall (ofString "out") .one (ofString "alloc") [.const 32#64]
          (.decCall (ofString "s") .one (ofString "sat_word") [.var .local (ofString "start")]
            (.seq
              (.call (some (none, none)) (ofString "keccak256")
                [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "s")],
                 .var .local (ofString "n"),
                 .var .local (ofString "out")])
              (.decCall (ofString "v") (.comb [.one, .one, .one, .one]) (ofString "u256_from_be")
                [.var .local (ofString "out"), .const 32#64]
                (.seq
                  (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")])
                  (.seq
                    (.call (some (none, none)) (ofString "stack_push") [.var .local (ofString "v")])
                    (.seq
                      (.call (some (none, none)) (ofString "pc_add") [.const 1#64])
                      (.return (.const 0#64)))))))))) := by
  intro t hc hInv hlen hR _ hnt
  simp only [↓reduceIte] at hR
  have hhp_mem : "heap_ptr" ∈ guestGlobalNames := by decide
  obtain ⟨markw, hmark_gw⟩ := hInv.1.2.2.2.2.2.2.2.2.2 "heap_ptr" hhp_mem
  have hmark_lk : t.globals.lookup (ofString "heap_ptr") = some (.val (.word markw)) := hmark_gw
  have hmark_nat : markw.toNat = globN t "heap_ptr" := by simp [globN, hmark_lk]
  have hmark_le : markw.toNat ≤ InitECandidate.Solver.HeapPotential.cMax.toNat := by
    have h1 := hInv.1.2.2.1; rw [hmark_nat]; exact h1
  have hmark_8 : markw.toNat % 8 = 0 := by
    rw [hmark_nat]; exact hInv.1.2.2.2.2.2.2.1
  -- Step 1: `decCall "mark" .one "heap_mark" []`
  have hargs_hm : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) [] = some [] := rfl
  have hlook_hm := pan_zero_arg_lookup t.code.lookup (ofString "heap_mark")
    (sourceFnBody Guest.Software.guestFn_heap_mark) .one (by rw [hc]; exact lookup_heap_mark)
  refine decCall_general_step s0 t (ofString "mark") (ofString "heap_mark") .one [] [] _ hargs_hm hnt ?_
  clear hnt
  intro body_hm cal_hm rs_hm hlk_hm _
  have hEq_hm := Option.some.inj (hlk_hm.symm.trans hlook_hm)
  obtain ⟨rfl, hEq_hm2⟩ := Prod.mk.inj hEq_hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq_hm2
  have hhm_body : evaluateHOLFiniteState (callEntryStateHOLFinite t HolFiniteMapExact.empty)
      (sourceFnBody Guest.Software.guestFn_heap_mark) =
      (some (.returned (.val (.word markw))),
       emptyLocalsHOLFinite (callEntryStateHOLFinite t HolFiniteMapExact.empty)) := by
    dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_heap_mark,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural]
    rw [evaluateHOLFiniteState_return]
    have hev_hp : @evalHOLExact 64 F _ (callEntryStateHOLFinite t HolFiniteMapExact.empty).toExact
        (fun a => Classical.propDecidable ((callEntryStateHOLFinite t HolFiniteMapExact.empty).memaddrs a))
        (.var .global (ofString "heap_ptr")) = some (.val (.word markw)) := hmark_lk
    rw [hev_hp]; dsimp only
    have hsz : sizeOfShapeWithContextHOL (callEntryStateHOLFinite t HolFiniteMapExact.empty).structs
        (shapeOfHOLExact (.val (.word markw) : ValueHOL 64)) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [if_pos hsz]
  have hne_hm : ¬ IsEvmErr (evaluateHOLFiniteState (callEntryStateHOLFinite t HolFiniteMapExact.empty)
      (sourceFnBody Guest.Software.guestFn_heap_mark)).1 := by
    rw [hhm_body]; rintro ⟨_, h⟩; cases h
  refine ⟨hne_hm, ?_⟩
  intro val_hm shm hrun_hm _ hnt
  have hEq_ret := Prod.mk.inj (hrun_hm.symm.trans hhm_body)
  have hval_hm : val_hm = .val (.word markw) := by injection hEq_ret.1 with h'; injection h'
  subst hval_hm
  rcases hEq_ret with ⟨_, rfl⟩
  set t1 := setVarHOLFinite (ofString "mark") (.val (.word markw))
    { emptyLocalsHOLFinite (callEntryStateHOLFinite t HolFiniteMapExact.empty) with locals := t.locals }
  -- Step 2: `decCall "out" .one "alloc" [.const 32#64]` on `t1`
  have hargs_al : evalListHOLFinite t1 (h := fun a => Classical.propDecidable (t1.memaddrs a)) [.const 32#64] =
      some [.val (.word 32#64)] := rfl
  have hlook_al := pan_one_word_lookup t1.code.lookup (ofString "alloc") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_alloc) 32#64 (by change t.code.lookup _ = _; rw [hc]; exact lookup_alloc)
  refine decCall_general_step s0 t1 (ofString "out") (ofString "alloc") .one
    [.const 32#64] [.val (.word 32#64)] _ hargs_al hnt ?_
  clear hnt
  intro body_al cal_al rs_al hlk_al _
  have hEq_al := Option.some.inj (hlk_al.symm.trans hlook_al)
  obtain ⟨rfl, hEq_al2⟩ := Prod.mk.inj hEq_al
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq_al2
  refine ⟨alloc_body_no_evmErr _ hc, ?_⟩
  intro val_al sal hrun_al _ hnt
  let cal_al := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word 32#64))
  let ent_al := callEntryStateHOLFinite t1 cal_al
  have hal_gen := Wave8GuestInv.M13.evaluate_alloc_body_general ent_al markw 32#64 hc hmark_le hmark_lk
    (by simp [ent_al, cal_al, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
  have hal_meta := PanRunBounded.evaluateHOLFiniteState_metadata ent_al (sourceFnBody Guest.Software.guestFn_alloc)
  have hal_ba := evaluate_baseAddr ent_al (sourceFnBody Guest.Software.guestFn_alloc)
  have hrun_al' : evaluateHOLFiniteState ent_al (sourceFnBody Guest.Software.guestFn_alloc) = (some (.returned val_al), sal) := hrun_al
  rw [hrun_al'] at hal_gen hal_meta hal_ba
  dsimp only at hal_gen hal_meta hal_ba
  obtain ⟨rfl, hsal_glob, hsal_mem, hq_ge, hq_le_cMax, _⟩ := hal_gen val_al rfl
  let q : BitVec 64 := (markw + (32#64 + 7)) &&& ((0 : BitVec 64) - 8)
  set t2 := setVarHOLFinite (ofString "out") (.val (.word markw)) { sal with locals := t1.locals }
  have ht2_code : t2.code = originalRuntimeCode := hal_meta.1.trans hc
  have ht2_ma : t2.memaddrs = ordinaryDomain := hal_meta.2.1.trans hInv.1.1.memaddrs
  have ht2_be : t2.be = t.be := hal_meta.2.2.1
  have ht2_sh : t2.shMemaddrs = t.shMemaddrs := hal_meta.2.2.2.1
  have ht2_ba : t2.baseAddr = t.baseAddr := hal_ba
  have ht2_glob : t2.globals = t.globals.update (ofString "heap_ptr", .val (.word q)) := hsal_glob
  have ht2_mem : t2.memory = t.memory := hsal_mem
  have ht2_G : GuestInv t2 := guestInv_congr (s := t)
    (ht2_code.trans hc.symm) (ht2_ma.trans hInv.1.1.memaddrs.symm) ht2_sh ht2_ba hInv.1.1
  have ht2_out : t2.locals.lookup (ofString "out") = some (.val (.word markw)) := by
    simp [t2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have ht2_mark : t2.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    have hne : ofString "out" ≠ ofString "mark" := by decide
    simp [t2, t1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne]
  -- Step 3: `decCall "s" .one "sat_word" [.var .local "start"]` on `t2`
  let tailAfterSat : ProgHOL 64 :=
    .seq
      (.call (some (none, none)) (ofString "keccak256")
        [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "s")],
         .var .local (ofString "n"),
         .var .local (ofString "out")])
      (.decCall (ofString "v") (.comb [.one, .one, .one, .one]) (ofString "u256_from_be")
        [.var .local (ofString "out"), .const 32#64]
        (.seq
          (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")])
          (.seq
            (.call (some (none, none)) (ofString "stack_push") [.var .local (ofString "v")])
            (.seq
              (.call (some (none, none)) (ofString "pc_add") [.const 1#64])
              (.return (.const 0#64))))))
  rcases hargs_sw : evalListHOLFinite t2 (h := fun a => Classical.propDecidable (t2.memaddrs a))
      [.var .local (ofString "start")] with _ | vals_sw
  · rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hargs_sw]
    exact opDispatchPost_error s0 _
  · refine decCall_general_step s0 t2 (ofString "s") (ofString "sat_word") .one
      [.var .local (ofString "start")] vals_sw tailAfterSat hargs_sw hnt ?_
    clear hnt
    intro body_sw cal_sw rs_sw hlk_sw _
    have hlk_sw_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "sat_word") vals_sw =
        some (body_sw, cal_sw, rs_sw) := by rwa [← ht2_code]
    have hro_sw : readOnlyProg opRoCallees body_sw = true :=
      installed_body_readOnly 440 (by rw [guestAst_len]; decide)
        Guest.Software.guestFn_sat_word rfl opRoCallees rfl hlk_sw_orig
    have hsw_safe := evaluate_readOnlyProg opRoCallees opRoCallees_good body_sw hro_sw
      (callEntryStateHOLFinite t2 cal_sw) ht2_code
    have hne_sw : ¬ IsEvmErr (evaluateHOLFiniteState (callEntryStateHOLFinite t2 cal_sw) body_sw).1 := by
      let satCallees : MlS → Bool := fun f => f == ofString "sat_word"
      have hsat_good : ∀ function, satCallees function = true → ∀ values body callee rs,
          PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
            some (body, callee, rs) →
          noRaiseProg satCallees body = true := by
        intro function hfn values body callee rs hfound
        obtain ⟨params, rs', hinst⟩ := lookupCode_installed hfound
        simp only [satCallees, beq_iff_eq] at hfn
        subst hfn
        have hlk_sw_fn := lookup_of_guestAst_getElem 440 (by rw [guestAst_len]; decide)
          (extractFn Guest.Software.guestFn_sat_word) rfl
        change originalRuntimeCode.lookup (ofString "sat_word") = _ at hlk_sw_fn
        rw [hlk_sw_fn] at hinst
        have hbeq := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
        rw [← hbeq]; decide
      exact evaluate_noRaiseProg satCallees hsat_good body_sw
        (hsat_good (ofString "sat_word") (by decide) vals_sw body_sw cal_sw rs_sw hlk_sw_orig)
        (callEntryStateHOLFinite t2 cal_sw) ht2_code
    refine ⟨hne_sw, ?_⟩
    intro v_sw ssw hrun_sw _ hnt
    rw [hrun_sw] at hsw_safe
    have hlf_sw : LocFrame (callEntryStateHOLFinite t2 cal_sw) ssw :=
      SafeOrTrapped.to_resumes hsw_safe (Or.inl ⟨v_sw, rfl⟩)
    set t2s := setVarHOLFinite (ofString "s") v_sw { ssw with locals := t2.locals }
    have ht2s_lf : LocFrame t2 t2s := by
      unfold LocFrame at hlf_sw ⊢
      simp only [t2s, setVarHOLFinite]; rw [hlf_sw]; cases t2; rfl
    have ht2s_code : t2s.code = originalRuntimeCode := by rw [ht2s_lf]; exact ht2_code
    have ht2s_ma : t2s.memaddrs = ordinaryDomain := by rw [ht2s_lf]; exact ht2_ma
    have ht2s_be : t2s.be = t.be := by rw [ht2s_lf]; exact ht2_be
    have ht2s_sh : t2s.shMemaddrs = t.shMemaddrs := by rw [ht2s_lf]; exact ht2_sh
    have ht2s_ba : t2s.baseAddr = t.baseAddr := by rw [ht2s_lf]; exact ht2_ba
    have ht2s_glob : t2s.globals = t.globals.update (ofString "heap_ptr", .val (.word q)) := by
      rw [ht2s_lf]; exact ht2_glob
    have ht2s_mem : t2s.memory = t.memory := by rw [ht2s_lf]; exact ht2_mem
    have ht2s_G : GuestInv t2s := guestInv_congr (s := t2)
      (by rw [ht2s_lf]) (by rw [ht2s_lf]) (by rw [ht2s_lf]) (by rw [ht2s_lf]) ht2_G
    have ht2s_out : t2s.locals.lookup (ofString "out") = some (.val (.word markw)) := by
      have hne : ofString "s" ≠ ofString "out" := by decide
      simp [t2s, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, ht2_out]
    have ht2s_mark : t2s.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
      have hne : ofString "s" ≠ ofString "mark" := by decide
      simp [t2s, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, ht2_mark]
    -- Step 4: `seq (call "keccak256" [pExp, nExp, outExp]) ...` on `t2s`
    let pExp : ExpHOL 64 := .op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "s")]
    let nExp : ExpHOL 64 := .var .local (ofString "n")
    let outExp : ExpHOL 64 := .var .local (ofString "out")
    refine seq_step s0 t2s _ _ hnt ?_
    clear hnt
    intro hnt_kc
    by_cases hargs_kc_ok :
        (∃ pw : BitVec 64, @evalHOLExact 64 F _ t2s.toExact (fun a => Classical.propDecidable (t2s.memaddrs a)) pExp = some (.val (.word pw))) ∧
        (∃ nw : BitVec 64, @evalHOLExact 64 F _ t2s.toExact (fun a => Classical.propDecidable (t2s.memaddrs a)) nExp = some (.val (.word nw)))
    · obtain ⟨⟨pw, hpw⟩, ⟨nw, hnw⟩⟩ := hargs_kc_ok
      have houtw : @evalHOLExact 64 F _ t2s.toExact (fun a => Classical.propDecidable (t2s.memaddrs a)) outExp =
          some (.val (.word markw)) := ht2s_out
      have hkc := eval_call_keccak256_bre t2s pExp nExp outExp pw nw markw ht2s_code ht2s_G hpw hnw houtw
      refine ⟨?_, fun hne => ?_⟩
      · intro hnone hnt
        obtain ⟨heff_kc, ht3_loc⟩ := hkc.2 hnt_kc hnone
        set t3 := (evaluateHOLFiniteState t2s (.call (some (none, none)) (ofString "keccak256") [pExp, nExp, outExp])).2
        have ht3_code : t3.code = originalRuntimeCode := heff_kc.code.trans ht2s_code
        have ht3_out : t3.locals.lookup (ofString "out") = some (.val (.word markw)) := by
          rw [ht3_loc]; exact ht2s_out
        have ht3_mark : t3.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
          rw [ht3_loc]; exact ht2s_mark
        -- Step 5: `decCall "v" (comb [1,1,1,1]) "u256_from_be" [out, 32]` on `t3`
        have hargs_ub : evalListHOLFinite t3 (h := fun a => Classical.propDecidable (t3.memaddrs a))
            [.var .local (ofString "out"), .const 32#64] =
            some [.val (.word markw), .val (.word 32#64)] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ht3_out]
        refine decCall_general_step s0 t3 (ofString "v") (ofString "u256_from_be") _
          [.var .local (ofString "out"), .const 32#64]
          [.val (.word markw), .val (.word 32#64)] _ hargs_ub hnt ?_
        clear hnt
        intro body_ub cal_ub rs_ub hlk_ub _
        have hlk_ub_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "u256_from_be")
            [.val (.word markw), .val (.word 32#64)] = some (body_ub, cal_ub, rs_ub) := by
          rwa [← ht3_code]
        have hro_ub : readOnlyProg opRoCallees body_ub = true :=
          installed_body_readOnly 86 (by rw [guestAst_len]; decide)
            Guest.Software.guestFn_u256_from_be rfl opRoCallees rfl hlk_ub_orig
        have hnr_ub : noRaiseProg u256FromBeCallees body_ub = true :=
          u256FromBeCallees_good (ofString "u256_from_be") (by decide)
            [.val (.word markw), .val (.word 32#64)] body_ub cal_ub rs_ub hlk_ub_orig
        have hub_no_evm : ¬ IsEvmErr (evaluateHOLFiniteState (callEntryStateHOLFinite t3 cal_ub) body_ub).1 :=
          evaluate_noRaiseProg u256FromBeCallees u256FromBeCallees_good body_ub hnr_ub
            (callEntryStateHOLFinite t3 cal_ub) ht3_code
        refine ⟨hub_no_evm, ?_⟩
        intro v_ub sub hrun_ub _ hnt
        have hub_safe := evaluate_readOnlyProg opRoCallees opRoCallees_good body_ub hro_ub
          (callEntryStateHOLFinite t3 cal_ub) ht3_code
        rw [hrun_ub] at hub_safe
        have hlf_ub : LocFrame (callEntryStateHOLFinite t3 cal_ub) sub :=
          SafeOrTrapped.to_resumes hub_safe (Or.inl ⟨v_ub, rfl⟩)
        set t4 := setVarHOLFinite (ofString "v") v_ub { sub with locals := t3.locals }
        have ht4_lf : LocFrame t3 t4 := by
          unfold LocFrame at hlf_ub ⊢
          simp only [t4, setVarHOLFinite]; rw [hlf_ub]; cases t3; rfl
        have ht4_code : t4.code = originalRuntimeCode := by rw [ht4_lf]; exact ht3_code
        have ht4_mark : t4.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
          have hne : ofString "v" ≠ ofString "mark" := by decide
          simp [t4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, ht3_mark]
        -- Step 6: `seq (call "heap_release" [mark]) ...` on `t4`
        refine seq_step s0 t4 _ _ hnt ?_
        clear hnt
        intro hnt_hr
        rw [evaluateHOLFiniteState_call] at hnt_hr ⊢
        have hargs_hr : evalListHOLFinite t4
            (h := fun a => Classical.propDecidable (t4.memaddrs a))
            [.var .local (ofString "mark")] = some [.val (.word markw)] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ht4_mark]
        have hlook_hr := pan_one_word_lookup t4.code.lookup (ofString "heap_release")
          (ofString "m") (sourceFnBody Guest.Software.guestFn_heap_release) markw
          (by rw [ht4_code]; exact lookup_heap_release)
        rw [hargs_hr] at hnt_hr ⊢; dsimp only at hnt_hr ⊢
        rw [hlook_hr] at hnt_hr ⊢; dsimp only at hnt_hr ⊢
        by_cases hclk_t4 : t4.clock = 0
        · simp [hclk_t4] at hnt_hr
        · simp only [hclk_t4, ↓reduceIte] at hnt_hr ⊢
          let cal_hr := HolFiniteMapExact.empty.update (ofString "m", ValueHOL.val (.word markw))
          let ent_hr := callEntryStateHOLFinite t4 cal_hr
          have hhr_body : evaluateHOLFiniteState ent_hr
              (sourceFnBody Guest.Software.guestFn_heap_release) =
              (some (.returned (.val (.word 0))),
               emptyLocalsHOLFinite (setKvarHOLFinite .global (ofString "heap_ptr") (.val (.word markw)) ent_hr)) := by
            dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_heap_release,
              InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
              InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
              InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
              InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural]
            rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
            have hm_loc : ent_hr.locals.lookup (ofString "m") = some (.val (.word markw)) := by
              simp [ent_hr, cal_hr, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have hlk_hp4 : ent_hr.globals.lookup (ofString "heap_ptr") = some (.val (.word q)) := by
              have hg4 : ent_hr.globals = t2s.globals := by
                change t4.globals = t2s.globals; rw [ht4_lf, heff_kc.globals]
              rw [hg4, ht2s_glob]
              simp [HolFiniteMapExact.lookup_update, FUPDATE]
            simp [evalHOLExact, hm_loc, isValidValueHOLFinite, isValidValueHOLExact,
              lookupKvarHOLFinite, lookupKvarHOLExact, hlk_hp4,
              shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite,
              evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
          rw [hhr_body]; dsimp only
          have hsh0_one : shapeEqHOL (shapeOfHOLExact (.val (.word (0 : BitVec 64)) : ValueHOL 64)) .one = true := by
            simp [shapeOfHOLExact, shapeEqHOL]
          rw [if_pos hsh0_one]; dsimp only
          refine ⟨?_, fun hne => absurd rfl hne⟩
          intro _ hnt
          set t5 : PanSemStateFiniteExact 64 F :=
            { emptyLocalsHOLFinite (setKvarHOLFinite .global (ofString "heap_ptr") (.val (.word markw)) ent_hr) with
              locals := t4.locals }
          have ht5_glob : t5.globals = t.globals := by
            have hg4 : ent_hr.globals = t2s.globals := by
              change t4.globals = t2s.globals; rw [ht4_lf, heff_kc.globals]
            change ent_hr.globals.update (ofString "heap_ptr", .val (.word markw)) = t.globals
            rw [hg4, ht2s_glob]
            exact globals_update_twice_restore t.globals (ofString "heap_ptr")
              (.val (.word markw)) (.val (.word q)) hmark_lk
          have ht5_code : t5.code = originalRuntimeCode := ht4_code
          have ht5_mem : t5.memory = t3.memory := by change t4.memory = t3.memory; rw [ht4_lf]
          have hub_eq : untypedGlobalBufIvls t2s = untypedGlobalBufIvls t := by
            have hgl_ne : ∀ (g : String), ofString "heap_ptr" ≠ ofString g → globN t2s g = globN t g := by
              intro g hne
              unfold globN; rw [ht2s_glob]
              simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne]
            unfold untypedGlobalBufIvls
            simp only [List.map]
            rw [hgl_ne "u256_ws" (by decide), hgl_ne "sk_buf" (by decide),
                hgl_ne "keccak_pad" (by decide), hgl_ne "keccak_st" (by decide),
                hgl_ne "mpt_nib_scratch" (by decide)]
          have heff_t_t5 : ByteRegionEffect t t5 ((markw.toNat, 32) :: untypedGlobalBufIvls t) := by
            rw [← hub_eq]
            refine ⟨ht5_code.trans hc.symm, ?_, ?_, ?_, ?_, ht5_glob, ?_, ?_, ?_⟩
            · change t4.memaddrs = t.memaddrs
              rw [ht4_lf, heff_kc.memaddrs, ht2s_ma, hInv.1.1.memaddrs]
            · change t4.shMemaddrs = t.shMemaddrs
              rw [ht4_lf, heff_kc.shMemaddrs, ht2s_sh]
            · change t4.baseAddr = t.baseAddr
              rw [ht4_lf, heff_kc.baseAddr, ht2s_ba]
            · change t4.be = t.be
              rw [ht4_lf, heff_kc.be, ht2s_be]
            · intro a hna
              rw [ht5_mem]
              have hna2 : ¬ t2s.memaddrs a := by
                rw [ht2s_ma, ← hInv.1.1.memaddrs]; exact hna
              rw [heff_kc.out_dom a hna2, ht2s_mem]
            · intro a ha
              rw [ht5_mem, heff_kc.cell_frame a ha, ht2s_mem]
            · intro b hb hno
              have hbe53 : t5.be = t3.be := by change t4.be = t3.be; rw [ht4_lf]
              have hmb5 : memB t5 b = memB t3 b := by unfold memB; rw [ht5_mem, hbe53]
              have hmb2 : memB t2s b = memB t b := by unfold memB; rw [ht2s_mem, ht2s_be]
              rw [hmb5, heff_kc.byte_frame b hb hno, hmb2]
          have hmark32_le : markw.toNat + 32 ≤ InitECandidate.Solver.HeapPotential.cMax.toNat := by
            have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
            omega
          obtain ⟨hInv_t5, hch_t5, hR_t5⟩ :=
            heapGap_and_untypedBufs_bre_to_evmStep hInv hmark_nat hmark32_le hmark_8 heff_t_t5
          have hlen_t5 : (evmChain t5).length = (evmChain s0).length := by
            rw [hch_t5]; exact hlen
          have hR_t5' : OpDispatchSpec.evmR t5 = OpDispatchSpec.evmR t := hR_t5
          have hR_lt_t5 : if true then OpDispatchSpec.evmR t5 < OpDispatchSpec.evmR s0 else OpDispatchSpec.evmR t5 ≤ OpDispatchSpec.evmR s0 := by
            simp only [↓reduceIte]; rw [hR_t5']; exact hR
          have htail : HandlerRun s0 (fun _ => True) true
              (.seq (.call (some (none, none)) (ofString "stack_push") [.var .local (ofString "v")])
                (.seq (.call (some (none, none)) (ofString "pc_add") [.const 1#64])
                  (.return (.const 0#64)))) :=
            HandlerRun.seq_call_simple eps_stack_push
              (HandlerRun.seq_call_simple eps_pc_add (HandlerRun.ret _))
          exact htail t5 ht5_code hInv_t5 hlen_t5 hR_lt_t5 trivial hnt
      · refine ⟨?_, hkc.1⟩
        intro v hv
        rw [evaluateHOLFiniteState_call] at hv
        rcases hargs_ev : evalListHOLFinite t2s (h := fun a => Classical.propDecidable (t2s.memaddrs a))
            [pExp, nExp, outExp] with _ | vs_kc
        · dsimp only [pExp, nExp, outExp] at hargs_ev; rw [hargs_ev] at hv; simp at hv
        · dsimp only [pExp, nExp, outExp] at hargs_ev; rw [hargs_ev] at hv; dsimp only at hv
          rcases hlk_ev : lookupCodeHOLFinite t2s.code.lookup (ofString "keccak256") vs_kc with _ | ⟨b_kc, c_kc, r_kc⟩
          · rw [hlk_ev] at hv; simp at hv
          · rw [hlk_ev] at hv; dsimp only at hv
            split at hv
            · simp at hv
            · rcases hrun_ev : evaluateHOLFiniteState (callEntryStateHOLFinite t2s c_kc) b_kc with ⟨res_kc, st_kc⟩
              rw [hrun_ev] at hv
              cases res_kc with
              | none => simp at hv
              | some rk0 =>
                cases rk0 with
                | returned vk =>
                  dsimp only at hv
                  split at hv <;> simp at hv
                | _ => simp at hv
    · rw [evaluateHOLFiniteState_call]
      rcases hargs_kc : evalListHOLFinite t2s
          (h := fun a => Classical.propDecidable (t2s.memaddrs a))
          [pExp, nExp, outExp] with _ | vals_kc
      · dsimp only
        refine ⟨(fun h => by cases h), fun _ => ⟨(fun _ h => by cases h), ?_⟩⟩
        rintro ⟨_, h⟩; cases h
      · dsimp only
        rcases hlk_kc : lookupCodeHOLFinite t2s.code.lookup (ofString "keccak256") vals_kc with
          _ | ⟨body_kc, cal_kc, rs_kc⟩
        · dsimp only
          refine ⟨(fun h => by cases h), fun _ => ⟨(fun _ h => by cases h), ?_⟩⟩
          rintro ⟨_, h⟩; cases h
        · exfalso
          apply hargs_kc_ok
          have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
            t2s.code.lookup (ofString "keccak256") vals_kc body_kc cal_kc rs_kc hlk_kc
          rw [ht2s_code] at hx
          simp only [Flapjack.lookupCodeHOLExact, lookup_keccak256] at hx
          split at hx
          · rename_i hcond
            have hlen3 : vals_kc.length = 3 := by simpa using hcond.2.1.symm
            rcases vals_kc with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩
            all_goals try (simp at hlen3)
            have hsh12 : shapeEqHOL .one (shapeOfHOLExact v1) = true ∧
                shapeEqHOL .one (shapeOfHOLExact v2) = true := by
              have hs := hcond.2.2
              simp only [List.map, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
                List.zip_cons_cons, List.zip_nil_right] at hs
              exact ⟨hs.1, hs.2.1⟩
            have hw_of_one : ∀ u : ValueHOL 64, shapeEqHOL .one (shapeOfHOLExact u) = true →
                ∃ w : BitVec 64, u = .val (.word w) := by
              intro u hu
              rcases u with ⟨⟨w⟩⟩ | _ | _
              · exact ⟨w, rfl⟩
              · simp [shapeOfHOLExact, shapeEqHOL] at hu
              · simp [shapeOfHOLExact, shapeEqHOL] at hu
            obtain ⟨pw, rfl⟩ := hw_of_one v1 hsh12.1
            obtain ⟨nw, rfl⟩ := hw_of_one v2 hsh12.2
            change @evalListHOLExact 64 F _ t2s.toExact (fun a => Classical.propDecidable (t2s.memaddrs a))
              [pExp, nExp, outExp] = some [.val (.word pw), .val (.word nw), v3] at hargs_kc
            have hb3 : @evalHOLExact 64 F _ t2s.toExact (fun a => Classical.propDecidable (t2s.memaddrs a))
                outExp = some (.val (.word markw)) := ht2s_out
            rcases hb1 : @evalHOLExact 64 F _ t2s.toExact (fun a => Classical.propDecidable (t2s.memaddrs a)) pExp with _ | u1
            · simp [evalListHOLExact, hb1] at hargs_kc
            · rcases hb2 : @evalHOLExact 64 F _ t2s.toExact (fun a => Classical.propDecidable (t2s.memaddrs a)) nExp with _ | u2
              · simp [evalListHOLExact, hb1, hb2] at hargs_kc
              · simp [evalListHOLExact, hb1, hb2, hb3] at hargs_kc
                obtain ⟨rfl, rfl, _⟩ := hargs_kc
                exact ⟨⟨pw, rfl⟩, ⟨nw, rfl⟩⟩
          · cases hx

private theorem eval_keccak_base_cost_pos {F : Type}
    (t : PanSemStateFiniteExact 64 F) {ww : BitVec 64}
    (hww : t.locals.lookup (ofString "w") = some (.val (.word ww)))
    (hlt : ww.toNat < 2 ^ 59)
    {v0 : ValueHOL 64}
    (hev : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.op .add
        [.const (BitVec.ofNat 64 30),
         .panop .mul [.const (BitVec.ofNat 64 6), .var .local (ofString "w")]]) = some v0) :
    ∃ aw : BitVec 64, v0 = .val (.word aw) ∧ 0 < aw.toNat := by
  have hadd : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.op .add
        [.const (BitVec.ofNat 64 30),
         .panop .mul [.const (BitVec.ofNat 64 6), .var .local (ofString "w")]]) =
      some (.val (.word (BitVec.ofNat 64 30 + BitVec.ofNat 64 6 * ww))) := by
    simp [evalHOLExact, evalListHOLExact, hww, wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord]
  rw [hadd] at hev
  injection hev with hv0
  refine ⟨BitVec.ofNat 64 30 + BitVec.ofNat 64 6 * ww, hv0.symm, ?_⟩
  have h6 : (BitVec.ofNat 64 6).toNat = 6 := rfl
  have h30 : (BitVec.ofNat 64 30).toNat = 30 := rfl
  have hmul_nat : (BitVec.ofNat 64 6 * ww).toNat = 6 * ww.toNat := by
    rw [BitVec.toNat_mul, h6, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_add, h30, hmul_nat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Conditional `OpHandlerSpec` for `op_keccak` given an `EvmPreservingSpec` for `extend_memory`
    under bounded `expand_by < 2 ^ 37`. -/
theorem op_keccak_spec_of_extend_memory
    {Qem : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h_extend_memory : EvmPreservingSpec
      (fun s => ∃ ebw : BitVec 64,
        s.locals.lookup (ofString "expand_by") = some (.val (.word ebw)) ∧
        ebw.toNat < 2 ^ 37)
      Qem
      (ofString "extend_memory")) :
    OpHandlerSpec (ofString "op_keccak") := by
  refine opHandlerSpec_of_run 501 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_keccak rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_keccak, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRun.decCall_simple eps_stack_pop ?_
  refine HandlerRun.decCall_simple eps_stack_pop ?_
  refine HandlerRun.decCall_simple eps_sat_word ?_
  refine HandlerRun.decCall
    (Q := fun t => ∃ ww : BitVec 64, t.locals.lookup (ofString "w") = some (.val (.word ww)) ∧ ww.toNat < 2 ^ 59)
    eps_words_of_lt
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ v _ _ _ _ _ _ _ hQc => by
      obtain ⟨_, ww, rfl, hlt⟩ := hQc
      exact ⟨ww, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], hlt⟩)
    ?_
  refine HandlerRun.decCall
    (Q := fun t =>
      (∃ ww : BitVec 64, t.locals.lookup (ofString "w") = some (.val (.word ww)) ∧ ww.toNat < 2 ^ 59) ∧
      ∃ cw ebw : BitVec 64,
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        ebw.toNat < 2 ^ 37)
    eps_extend_memory_cost1_bounds
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ v _ _ ⟨ww, hww, hlt⟩ _ _ _ _ hQc => by
      obtain ⟨_, cw, ebw, rfl, heb_bounds⟩ := hQc
      have hne_xw : ofString "x" ≠ ofString "w" := by decide
      refine ⟨⟨ww, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne_xw, Ne.symm hne_xw, hww], hlt⟩,
              cw, ebw, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], ?_⟩
      rcases heb_bounds with rfl | ⟨before, after, haft_lt, _, _, heb_sub, _⟩
      · decide
      · omega)
    ?_
  refine HandlerRun.decCall
    (Q := fun t =>
      (∃ costw : BitVec 64, t.locals.lookup (ofString "cost") = some (.val (.word costw)) ∧ 0 < costw.toNat) ∧
      ∃ cw ebw : BitVec 64,
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        ebw.toNat < 2 ^ 37)
    eps_add_sat_pos
    (fun t values b_as callee rs_as hc _ ⟨⟨ww, hww, hlt⟩, _⟩ hargs hl => by
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "add_sat") values =
          some (b_as, callee, rs_as) := by rwa [← hc]
      obtain ⟨_, _, w1, w2, rfl, hw1, _⟩ := two_word_arg_lookup (by decide) lookup_add_sat hl_orig
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact] at hargs
      rcases he1 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.op .add
            [.const (BitVec.ofNat 64 30),
             .panop .mul [.const (BitVec.ofNat 64 6), .var .local (ofString "w")]]) with _ | u1
      · simp [he1] at hargs
      · rcases he2 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
            (.rfield 0 (.var .local (ofString "x"))) with _ | u2
        · simp [he1, he2] at hargs
        · simp only [he1, he2, Option.some.injEq, List.cons.injEq] at hargs
          obtain ⟨rfl, _⟩ := hargs
          obtain ⟨aw, haw, hpos⟩ := eval_keccak_base_cost_pos t hww hlt he1
          injection haw with haw'; injection haw' with haw_eq; subst haw_eq
          exact ⟨w1, hw1, hpos⟩)
    (fun _ _ _ _ _ v _ _ ⟨_, cw, ebw, hx, heb_lt⟩ _ _ _ _ hQc => by
      obtain ⟨_, costw, rfl, hpos⟩ := hQc
      have hne_cx : ofString "cost" ≠ ofString "x" := by decide
      exact ⟨⟨costw, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], hpos⟩,
             cw, ebw, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne_cx, Ne.symm hne_cx, hx], heb_lt⟩)
    ?_
  refine HandlerRun.seq_charge_gas
    (Q := fun t =>
      ∃ cw ebw : BitVec 64,
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        ebw.toNat < 2 ^ 37)
    (fun t w hw _ ⟨⟨costw, hcost, hpos⟩, _⟩ => by
      change t.locals.lookup (ofString "cost") = some (.val (.word w)) at hw
      rw [hcost] at hw; injection hw with hw'; injection hw' with hw''; injection hw'' with hweq; subst hweq
      exact hpos)
    (fun _ _ _ ⟨_, hx⟩ _ _ _ => hx)
    ?_
  refine HandlerRun.seq_call
    (Q := fun _ => True)
    h_extend_memory
    (fun t values b_em callee rs_em hc _ ⟨cw, ebw, hx, heb_lt⟩ hargs hl => by
      have hx1 : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.rfield 1 (.var .local (ofString "x"))] = some [.val (.word ebw)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hx]
      rw [hx1] at hargs; injection hargs with hvs; subst hvs
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "extend_memory") [.val (.word ebw)] =
          some (b_em, callee, rs_em) := by rwa [← hc]
      obtain ⟨_, _, ebw', heq_eb, hcal_eb⟩ := one_word_arg_lookup lookup_extend_memory hl_orig
      injection heq_eb with heq1; injection heq1 with heq2; subst heq2
      exact ⟨ebw, hcal_eb, heb_lt⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
    (op_keccak_post_extend_run s0)

/-- Unconditional `FunSpec` for `op_keccak` under `EvmRun s ∧ HeadMemAligned s`,
    discharging `extend_memory` directly via `eps_extend_memory_aligned`. -/
theorem op_keccak_aligned_spec :
    FunSpec (fun s => EvmRun s ∧ HeadMemAligned s) OpDispatchPost (ofString "op_keccak") := by
  refine ⟨_, _, _, lookup_op_keccak, ?_⟩
  intro F s0 hcode ⟨hRun, hHM0⟩ _ hnt
  suffices hrun : HandlerRun s0 HeadMemAligned false (sourceFnBody Guest.Software.guestFn_op_keccak) from
    hrun s0 hcode hRun.1 rfl (le_refl _) hHM0 hnt
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_op_keccak,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRun.decCall
    (Q := HeadMemAligned)
    eps_stack_pop_preserves_headMem
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ callee _ v cpost _ hHM _ _ _ _ ⟨_, hHM_step⟩ => by
      have hHM_ce : HeadMemAligned (callEntryStateHOLFinite t callee) :=
        headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      have hHM_cp : HeadMemAligned cpost := hHM_step hHM_ce
      exact headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp)
    ?_
  refine HandlerRun.decCall
    (Q := HeadMemAligned)
    eps_stack_pop_preserves_headMem
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ callee _ v cpost _ hHM _ _ _ _ ⟨_, hHM_step⟩ => by
      have hHM_ce : HeadMemAligned (callEntryStateHOLFinite t callee) :=
        headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      have hHM_cp : HeadMemAligned cpost := hHM_step hHM_ce
      exact headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp)
    ?_
  refine HandlerRun.decCall
    (Q := HeadMemAligned)
    eps_sat_word
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ callee _ v cpost _ hHM _ _ _ _ hlf => by
      have hHM_ce : HeadMemAligned (callEntryStateHOLFinite t callee) :=
        headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      have hHM_cp : HeadMemAligned cpost :=
        headMemAligned_congr_head_only (by rw [hlf]) (fun off _ => by unfold memW; rw [hlf]) hHM_ce
      exact headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp)
    ?_
  refine HandlerRun.decCall
    (Q := fun t => HeadMemAligned t ∧
      ∃ ww : BitVec 64, t.locals.lookup (ofString "w") = some (.val (.word ww)) ∧ ww.toNat < 2 ^ 59)
    eps_words_of_lt
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ callee _ v cpost _ hHM _ _ _ _ hQc => by
      obtain ⟨hlf, ww, rfl, hlt⟩ := hQc
      have hHM_ce : HeadMemAligned (callEntryStateHOLFinite t callee) :=
        headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      have hHM_cp : HeadMemAligned cpost :=
        headMemAligned_congr_head_only (by rw [hlf]) (fun off _ => by unfold memW; rw [hlf]) hHM_ce
      exact ⟨headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp,
             ww, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], hlt⟩)
    ?_
  refine HandlerRun.decCall
    (Q := fun t =>
      HeadMemAligned t ∧
      (∃ ww : BitVec 64, t.locals.lookup (ofString "w") = some (.val (.word ww)) ∧ ww.toNat < 2 ^ 59) ∧
      ∃ cw ebw : BitVec 64,
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        (ebw = 0#64 ∨
          (memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
           (memW t (globN t "ev" + 32) + ebw.toNat) % 8 = 0 ∧
           memW t (globN t "ev" + 24) + memW t (globN t "ev" + 40) = globN t "frame_mem_ptr")))
    eps_extend_memory_cost1_bounds
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ callee _ v cpost _ ⟨hHM, ww, hww, hlt⟩ _ _ _ _ hQc => by
      obtain ⟨hlf, cw, ebw, rfl, heb_bounds⟩ := hQc
      let ce := callEntryStateHOLFinite t callee
      have hHM_ce : HeadMemAligned ce := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      have hHM_cp : HeadMemAligned cpost :=
        headMemAligned_congr_head_only (by rw [hlf]) (fun off _ => by unfold memW; rw [hlf]) hHM_ce
      let res := setVarHOLFinite (ofString "x") (.rStruct [.val (.word cw), .val (.word ebw)]) { cpost with locals := t.locals }
      have hHM_res : HeadMemAligned res := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp
      have hne_xw : ofString "x" ≠ ofString "w" := by decide
      have hmem32_eq : memW res (globN res "ev" + 32) = memW ce (globN ce "ev" + 32) := by
        have hg : globN res "ev" = globN ce "ev" := globN_eq_of_lookup_eq (by change cpost.globals.lookup _ = ce.globals.lookup _; rw [hlf])
        have hm : res.memory = ce.memory := by change cpost.memory = ce.memory; rw [hlf]
        rw [hg]; unfold memW; rw [hm]
      refine ⟨hHM_res,
              ⟨ww, by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne_xw, Ne.symm hne_xw, hww], hlt⟩,
              cw, ebw, by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], ?_⟩
      rcases heb_bounds with rfl | ⟨before, after, haft_lt, haft_mod, hbef_lt, heb_sub, hbef_eq⟩
      · exact Or.inl rfl
      · right
        have hbef : before = memW ce (globN ce "ev" + 32) := hbef_eq hHM_ce.1
        have hsum : memW res (globN res "ev" + 32) + ebw.toNat = after := by
          rw [hmem32_eq, ← hbef]; omega
        rw [hsum]
        exact ⟨haft_lt, by omega, hHM_res.2⟩)
    ?_
  refine HandlerRun.decCall
    (Q := fun t =>
      HeadMemAligned t ∧
      (∃ costw : BitVec 64, t.locals.lookup (ofString "cost") = some (.val (.word costw)) ∧ 0 < costw.toNat) ∧
      ∃ cw ebw : BitVec 64,
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        (ebw = 0#64 ∨
          (memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
           (memW t (globN t "ev" + 32) + ebw.toNat) % 8 = 0 ∧
           memW t (globN t "ev" + 24) + memW t (globN t "ev" + 40) = globN t "frame_mem_ptr")))
    eps_add_sat_pos
    (fun t values b_as callee rs_as hc _ ⟨_, ⟨ww, hww, hlt⟩, _⟩ hargs hl => by
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "add_sat") values =
          some (b_as, callee, rs_as) := by rwa [← hc]
      obtain ⟨_, _, w1, w2, rfl, hw1, _⟩ := two_word_arg_lookup (by decide) lookup_add_sat hl_orig
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact] at hargs
      rcases he1 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.op .add
            [.const (BitVec.ofNat 64 30),
             .panop .mul [.const (BitVec.ofNat 64 6), .var .local (ofString "w")]]) with _ | u1
      · simp [he1] at hargs
      · rcases he2 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
            (.rfield 0 (.var .local (ofString "x"))) with _ | u2
        · simp [he1, he2] at hargs
        · simp only [he1, he2, Option.some.injEq, List.cons.injEq] at hargs
          obtain ⟨rfl, _⟩ := hargs
          obtain ⟨aw, haw, hpos⟩ := eval_keccak_base_cost_pos t hww hlt he1
          injection haw with haw'; injection haw' with haw_eq; subst haw_eq
          exact ⟨w1, hw1, hpos⟩)
    (fun t _ _ callee _ v cpost _ ⟨hHM, _, cw, ebw, hx, heb_cond⟩ _ _ _ _ hQc => by
      obtain ⟨hlf, costw, rfl, hpos⟩ := hQc
      let ce := callEntryStateHOLFinite t callee
      have hHM_ce : HeadMemAligned ce := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      have hHM_cp : HeadMemAligned cpost :=
        headMemAligned_congr_head_only (by rw [hlf]) (fun off _ => by unfold memW; rw [hlf]) hHM_ce
      let res := setVarHOLFinite (ofString "cost") (.val (.word costw)) { cpost with locals := t.locals }
      have hHM_res : HeadMemAligned res := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp
      have hne_cx : ofString "cost" ≠ ofString "x" := by decide
      have hmem32_eq : memW res (globN res "ev" + 32) = memW t (globN t "ev" + 32) := by
        have hg : globN res "ev" = globN t "ev" := globN_eq_of_lookup_eq (by change cpost.globals.lookup _ = t.globals.lookup _; rw [hlf]; rfl)
        have hm : res.memory = t.memory := by change cpost.memory = t.memory; rw [hlf]; rfl
        rw [hg]; unfold memW; rw [hm]
      refine ⟨hHM_res,
              ⟨costw, by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], hpos⟩,
              cw, ebw, by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne_cx, Ne.symm hne_cx, hx], ?_⟩
      rcases heb_cond with rfl | ⟨hlt37, hmod8, _⟩
      · exact Or.inl rfl
      · right
        rw [hmem32_eq]
        exact ⟨hlt37, hmod8, hHM_res.2⟩)
    ?_
  refine seq_charge_gas_preserves_headMem
    (Q := fun t =>
      ∃ cw ebw : BitVec 64,
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        (ebw = 0#64 ∨
          (memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
           (memW t (globN t "ev" + 32) + ebw.toNat) % 8 = 0 ∧
           memW t (globN t "ev" + 24) + memW t (globN t "ev" + 40) = globN t "frame_mem_ptr")))
    (fun t w hw _ ⟨_, ⟨costw, hcost, hpos⟩, _⟩ => by
      change t.locals.lookup (ofString "cost") = some (.val (.word w)) at hw
      rw [hcost] at hw; injection hw with hw'; injection hw' with hw''; injection hw'' with hweq; subst hweq
      exact hpos)
    (fun t cpost _ ⟨hHM, _, cw, ebw, hx, heb_cond⟩ _ hglob_cp _ hmem_head_cp => by
      have hHM_cp : HeadMemAligned cpost := headMemAligned_congr_head_only hglob_cp hmem_head_cp hHM
      let res : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
      have hHM_res : HeadMemAligned res := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp
      have hmem32_eq : memW res (globN res "ev" + 32) = memW t (globN t "ev" + 32) := by
        have hg : globN res "ev" = globN t "ev" := globN_eq_of_lookup_eq (by change cpost.globals.lookup _ = t.globals.lookup _; rw [hglob_cp])
        rw [hg]; exact hmem_head_cp 32 (by simp)
      refine ⟨cw, ebw, hx, ?_⟩
      rcases heb_cond with rfl | ⟨hlt37, hmod8, _⟩
      · exact Or.inl rfl
      · right
        rw [hmem32_eq]
        exact ⟨hlt37, hmod8, hHM_res.2⟩)
    ?_
  refine HandlerRun.seq_call
    (Q := fun _ => True)
    eps_extend_memory_aligned
    (fun t values b_em callee rs_em hc _ ⟨cw, ebw, hx, heb_cond⟩ hargs hl => by
      have hx1 : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.rfield 1 (.var .local (ofString "x"))] = some [.val (.word ebw)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hx]
      rw [hx1] at hargs; injection hargs with hvs; subst hvs
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "extend_memory") [.val (.word ebw)] =
          some (b_em, callee, rs_em) := by rwa [← hc]
      obtain ⟨_, _, ebw', heq_eb, hcal_eb⟩ := one_word_arg_lookup lookup_extend_memory hl_orig
      injection heq_eb with heq1; injection heq1 with heq2; subst heq2
      exact ⟨ebw, hcal_eb, heb_cond⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
    (op_keccak_post_extend_run s0)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
