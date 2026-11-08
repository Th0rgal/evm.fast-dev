import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.Common
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.ReadOnly
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.StackPush
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.StackPushInv
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.CalldataloadSpecs

/-! # OpHandlerSpec Group 06b (`OpHandlers-A`): stack helpers and `op_push_bounded_spec` -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
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

/-! ## 1. Immediate and index helpers -/

theorem lookup_code_imm :
    originalRuntimeCode.lookup (ofString "code_imm") =
      some ([], sourceFnBody Guest.Software.guestFn_code_imm, .one) :=
  lookup_of_guestAst_getElem 518 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_code_imm) rfl

theorem lookup_decode_single :
    originalRuntimeCode.lookup (ofString "decode_single") =
      some ([(ofString "x", .one)], sourceFnBody Guest.Software.guestFn_decode_single, .one) :=
  lookup_of_guestAst_getElem 519 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_decode_single) rfl

theorem lookup_max :
    originalRuntimeCode.lookup (ofString "max") =
      some ([(ofString "a", .one), (ofString "b", .one)], sourceFnBody Guest.Software.guestFn_max, .one) :=
  lookup_of_guestAst_getElem 32 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_max) rfl

theorem lookup_stack_swap_positions :
    originalRuntimeCode.lookup (ofString "stack_swap_positions") =
      some ([(ofString "i", .one), (ofString "j", .one)],
        sourceFnBody Guest.Software.guestFn_stack_swap_positions, .one) :=
  lookup_of_guestAst_getElem 516 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_stack_swap_positions) rfl

theorem lookup_op_push :
    originalRuntimeCode.lookup (ofString "op_push") =
      some ([(ofString "nbytes", .one)], sourceFnBody Guest.Software.guestFn_op_push, .one) :=
  lookup_of_guestAst_getElem 514 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_op_push) rfl

theorem eps_code_imm :
    EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "code_imm") :=
  eps_of_readOnly 518 (by rw [guestAst_len]; decide) Guest.Software.guestFn_code_imm rfl
    opRoCallees opRoCallees_good rfl

theorem eps_decode_single :
    EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "decode_single") := by
  refine ⟨_, _, _, lookup_decode_single, ?_⟩
  intro F s hcode hInv _ hlookup hnt
  dsimp only
  have hno_ret_err {r0 : Option (PanSemResultExact 64)} {P1 P2 : Prop}
      (h1 : ∀ v, r0 ≠ some (.returned v)) (h2 : ¬ IsEvmErr r0) :
      (∀ v, r0 = some (.returned v) → P1) ∧ (IsEvmErr r0 → P2) :=
    ⟨fun v hv => (h1 v hv).elim, fun he => (h2 he).elim⟩
  have herr_triv {P1 P2 : Prop} :
      (∀ v, (some PanSemResultExact.error : Option (PanSemResultExact 64)) = some (.returned v) → P1) ∧
      (IsEvmErr (some PanSemResultExact.error) → P2) :=
    hno_ret_err (fun _ h => by cases h) (by rintro ⟨_, h⟩; cases h)
  have hbody : sourceFnBody Guest.Software.guestFn_decode_single =
      .seq (.ite (.cmp .notEqual (.const (0#64))
          (.op .or [.cmp .notLower (.const (90#64)) (.var .local (ofString "x")),
            .cmp .notLower (.var .local (ofString "x")) (.const (128#64))]))
        (.return (.op .and [.op .add [.var .local (ofString "x"), .const (145#64)], .const (255#64)]))
        .skip)
      (.seq (.raise (ofString "EvmErr") (.const (10#64))) (.return (.const (0#64)))) := rfl
  rw [hbody, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  split
  · rename_i w hw
    by_cases hw0 : w = 0
    · subst hw0
      simp only [↓reduceIte, evaluateHOLFiniteState_skip]
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_raise]
      dsimp only [evalHOLExact]
      cases hs_esh : s.eshapes.lookup (ofString "EvmErr") with
      | none => dsimp only; exact herr_triv
      | some sh =>
        dsimp only
        by_cases hcond : shapeOfHOLExact (.val (.word (10#64))) = sh ∧
            sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact (.val (.word (10#64)))) ≤ 32
        · rw [if_pos hcond]; dsimp only
          have hInv' : EvmInv (emptyLocalsHOLFinite s) :=
            localsFree_evmInv s _ s.clock hInv
          have hc := evm_congr (s := s) (t := emptyLocalsHOLFinite s) rfl rfl
          constructor
          · intro _ h; cases h
          · intro _
            exact ⟨hInv', evmChain_congr rfl rfl, le_of_eq hc.2.1⟩
        · rw [if_neg hcond]; dsimp only; exact herr_triv
    · simp only [hw0, ↓reduceIte]
      rw [evaluateHOLFiniteState_return]
      rcases hev_ret : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.op .and [.op .add [.var .local (ofString "x"), .const (145#64)], .const (255#64)]) with _ | rv
      · dsimp only; exact herr_triv
      · dsimp only
        by_cases hsz : sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact rv) ≤ 32
        · rw [if_pos hsz]; dsimp only
          have hInv' : EvmInv (emptyLocalsHOLFinite s) := localsFree_evmInv s _ s.clock hInv
          have hc := evm_congr (s := s) (t := emptyLocalsHOLFinite s) rfl rfl
          exact ⟨fun _ _ => ⟨hInv', evmChain_congr rfl rfl, le_of_eq hc.2.1, rfl⟩,
            by rintro ⟨_, h⟩; cases h⟩
        · rw [if_neg hsz]; dsimp only; exact herr_triv
  · dsimp only; exact herr_triv

theorem max_body_exact {F : Type} (s : PanSemStateFiniteExact 64 F) {aw bw : BitVec 64}
    (ha : s.locals.lookup (ofString "a") = some (.val (.word aw)))
    (hb : s.locals.lookup (ofString "b") = some (.val (.word bw)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_max)).1 =
      some (.returned v)) :
    ∃ rw : BitVec 64, v = .val (.word rw) ∧ rw.toNat = Nat.max aw.toNat bw.toNat := by
  have hbody : sourceFnBody Guest.Software.guestFn_max =
      .seq (.ite (.cmp .lower (.var .local (ofString "b")) (.var .local (ofString "a")))
        (.return (.var .local (ofString "a"))) .skip)
      (.return (.var .local (ofString "b"))) := rfl
  rw [hbody, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
  have hcmp : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
      (.cmp .lower (.var .local (ofString "b")) (.var .local (ofString "a"))) =
      some (.val (.word (if bw < aw then 1 else 0))) := by
    simp [evalHOLExact, ha, hb, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp] at hret; dsimp only at hret
  by_cases hlt : bw < aw
  · have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    simp only [hlt, ↓reduceIte, h10] at hret
    rw [evaluateHOLFiniteState_return] at hret
    have hev_a : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
        (.var .local (ofString "a")) = some (.val (.word aw)) := ha
    rw [hev_a] at hret; dsimp only at hret
    have hsz_a : sizeOfShapeWithContextHOL s.structs
        (shapeOfHOLExact (.val (.word aw))) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [if_pos hsz_a] at hret; dsimp only at hret
    injection hret with h1; injection h1 with hv
    refine ⟨aw, hv.symm, ?_⟩
    rw [BitVec.lt_def] at hlt
    exact (Nat.max_eq_left (Nat.le_of_lt hlt)).symm
  · simp only [hlt, ↓reduceIte, evaluateHOLFiniteState_skip] at hret
    rw [evaluateHOLFiniteState_return] at hret
    have hev_b : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
        (.var .local (ofString "b")) = some (.val (.word bw)) := hb
    rw [hev_b] at hret; dsimp only at hret
    have hsz_b : sizeOfShapeWithContextHOL s.structs
        (shapeOfHOLExact (.val (.word bw))) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [if_pos hsz_b] at hret; dsimp only at hret
    injection hret with h1; injection h1 with hv
    refine ⟨bw, hv.symm, ?_⟩
    rw [BitVec.lt_def] at hlt
    exact (Nat.max_eq_right (Nat.le_of_not_lt hlt)).symm

theorem eps_max :
    EvmPreservingSpec
      (fun s => ∃ aw bw : BitVec 64,
        s.locals.lookup (ofString "a") = some (.val (.word aw)) ∧
        s.locals.lookup (ofString "b") = some (.val (.word bw)))
      (fun s v post => LocFrame s post ∧
        ∀ aw bw : BitVec 64,
          s.locals.lookup (ofString "a") = some (.val (.word aw)) →
          s.locals.lookup (ofString "b") = some (.val (.word bw)) →
          ∃ rw : BitVec 64, v = .val (.word rw) ∧ rw.toNat = Nat.max aw.toNat bw.toNat)
      (ofString "max") := by
  obtain ⟨params, body, retShape, hlk, hro⟩ :=
    eps_of_readOnly 32 (by rw [guestAst_len]; decide) Guest.Software.guestFn_max rfl
      opRoCallees opRoCallees_good rfl
  have hlk_eq := lookup_max.symm.trans hlk
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_eq, rfl⟩
  subst hbody_eq
  refine ⟨_, _, _, lookup_max, ?_⟩
  intro F s hcode hInv _ hlookup hnt
  have hs := hro s hcode hInv trivial hlookup hnt
  dsimp only at hs ⊢
  refine ⟨fun v hv => ?_, hs.2⟩
  obtain ⟨h1, h2, h3, hlf⟩ := hs.1 v hv
  exact ⟨h1, h2, h3, hlf, fun aw bw ha hb => max_body_exact s ha hb v hv⟩

/-! ## 2. Stack slot swap (`eps_stack_swap_positions`) -/

private def loadWordExp (base : ExpHOL 64) (off : BitVec 64) : ExpHOL 64 :=
  .load .one (.op .add [base, .const off])

private def struct4 : ShapeHOL := .comb [.one, .one, .one, .one]

private theorem stack_slot_in {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    {stk sp item : BitVec 64}
    (_hA : ArenaOK s)
    (hFW : FrameWF s S (globN s "ev", globN s "cur_cont"))
    (hstk : stk.toNat = memW s (globN s "ev" + 8))
    (hsp : sp.toNat = memW s (globN s "ev" + 16))
    (hcap : memW s (globN s "ev" + 232) ≤ 1024)
    (hsp_le_cap : memW s (globN s "ev" + 16) ≤ memW s (globN s "ev" + 232))
    (hitem : item.toNat < sp.toNat) :
    let addr := stk + (sp - (1#64) - item) * (32#64)
    addr.toNat = stk.toNat + (sp.toNat - 1 - item.toNat) * 32 ∧
    stk.toNat ≤ addr.toNat ∧
    addr.toNat + 32 ≤ stk.toNat + 32 * memW s (globN s "ev" + 232) ∧
    addr.toNat + 32 ≤ 2 ^ 64 ∧
    addr.toNat % 8 = 0 := by
  intro addr
  have hstk_in := (hFW.1 (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232)) (by simp)).1
  have hse : scratchEnd ≤ 2 ^ 64 := by rw [R11Shards.scratchEnd_val]; decide
  have hstk_bnd : memW s (globN s "ev" + 8) + 32 * memW s (globN s "ev" + 232) ≤ 2 ^ 64 :=
    le_trans hstk_in.2 hse
  have hstk8 : stk.toNat % 8 = 0 := by
    rw [hstk]
    exact (hFW.1 (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232)) (by simp)).2.1
  have h1_lt : 1 ≤ sp.toNat := by omega
  have hsub1 : (sp - 1#64).toNat = sp.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le]
    · rfl
    · rw [BitVec.le_def]; change 1 ≤ sp.toNat; omega
  have hsub2 : (sp - 1#64 - item).toNat = sp.toNat - 1 - item.toNat := by
    rw [BitVec.toNat_sub_of_le]
    · rw [hsub1]
    · rw [BitVec.le_def, hsub1]; omega
  have hmul : ((sp - 1#64 - item) * 32#64).toNat = (sp.toNat - 1 - item.toNat) * 32 := by
    have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
    rw [BitVec.toNat_mul, hsub2, h32, Nat.mod_eq_of_lt (by omega)]
  have hadd : addr.toNat = stk.toNat + (sp.toNat - 1 - item.toNat) * 32 := by
    rw [BitVec.toNat_add, hmul, Nat.mod_eq_of_lt (by omega)]
  refine ⟨hadd, by omega, by omega, by omega, ?_⟩
  rw [hadd]
  omega

theorem eps_stack_swap_positions :
    EvmPreservingSpec
      (fun s =>
        ∃ i j : BitVec 64,
          s.locals.lookup (ofString "i") = some (.val (.word i)) ∧
          s.locals.lookup (ofString "j") = some (.val (.word j)) ∧
          i.toNat < memW s (globN s "ev" + 16) ∧
          j.toNat < memW s (globN s "ev" + 16))
      (fun s _ post => post.globals = s.globals)
      (ofString "stack_swap_positions") := by
  refine ⟨_, _, _, lookup_stack_swap_positions, ?_⟩
  intro F s hcode hInv hP _ hnt
  obtain ⟨iw, jw, hi_lk, hj_lk, hi_lt, hj_lt⟩ := hP
  have hno_ret_err {r0 : Option (PanSemResultExact 64)} {P1 P2 : Prop}
      (h1 : ∀ v, r0 ≠ some (.returned v)) (h2 : ¬ IsEvmErr r0) :
      (∀ v, r0 = some (.returned v) → P1) ∧ (IsEvmErr r0 → P2) :=
    ⟨fun v hv => (h1 v hv).elim, fun he => (h2 he).elim⟩
  have herr_triv {P1 P2 : Prop} :
      (∀ v, (some PanSemResultExact.error : Option (PanSemResultExact 64)) = some (.returned v) → P1) ∧
      (IsEvmErr (some PanSemResultExact.error) → P2) :=
    hno_ret_err (fun _ h => by cases h) (by rintro ⟨_, h⟩; cases h)
  have hbody : sourceFnBody Guest.Software.guestFn_stack_swap_positions =
      .dec (ofString "sp") .one (loadWordExp (.var .global (ofString "ev")) 16#64)
        (.dec (ofString "stk") .one (loadWordExp (.var .global (ofString "ev")) 8#64)
          (.dec (ofString "pa") .one
            (.op .add [.var .local (ofString "stk"),
              .panop .mul [.op .sub [.op .sub [.var .local (ofString "sp"), .const (1#64)],
                .var .local (ofString "i")], .const (32#64)]])
            (.dec (ofString "pb") .one
              (.op .add [.var .local (ofString "stk"),
                .panop .mul [.op .sub [.op .sub [.var .local (ofString "sp"), .const (1#64)],
                  .var .local (ofString "j")], .const (32#64)]])
              (.dec (ofString "a") struct4 (.load struct4 (.var .local (ofString "pa")))
                (.dec (ofString "b") struct4 (.load struct4 (.var .local (ofString "pb")))
                  (.seq (.store (.var .local (ofString "pa")) (.var .local (ofString "b")))
                    (.seq (.store (.var .local (ofString "pb")) (.var .local (ofString "a")))
                      (.return (.const (0#64)))))))))) := rfl
  dsimp only
  rw [hbody]
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    simp [evmChain, evmChainFrom]
  have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead_mem
  have hb_ev := (frameWF_bounds hInv.1.2 hFW0).1
  dsimp only at hb_ev
  have hsp_le_cap : memW s (globN s "ev" + 16) ≤ memW s (globN s "ev" + 232) := hFW0.2.2.2.2.1
  have hcap_ge1 : 1 ≤ memW s (globN s "ev" + 232) := hFW0.2.2.2.1
  have hcap_le1024 : memW s (globN s "ev" + 232) ≤ 1024 := hFW0.2.2.2.2.2.1
  -- Step 1: `dec "sp"`
  rw [evaluateHOLFiniteState_dec_total]; dsimp only
  rcases hload_sp : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (loadWordExp (.var .global (ofString "ev")) 16#64) with _ | vsp
  · simp only [hload_sp]; exact herr_triv
  · simp only [hload_sp]
    obtain ⟨spw, rfl, hspw_nat⟩ := evalAt_loadG_word s "ev" 16#64 vsp hload_sp
    have h16_n : (16#64 : BitVec 64).toNat = 16 := rfl
    rw [h16_n] at hspw_nat
    have hsh1_sp : shapeEqHOL .one (shapeOfHOLExact (.val (.word spw))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    rw [if_pos hsh1_sp]; dsimp only
    set s1 := setVarHOLFinite (ofString "sp") (.val (.word spw)) s with hs1
    -- Step 2: `dec "stk"`
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    rcases hload_stk : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        (loadWordExp (.var .global (ofString "ev")) 8#64) with _ | vstk
    · simp only [hload_stk]; exact herr_triv
    · simp only [hload_stk]
      obtain ⟨stkw, rfl, hstkw_nat⟩ := evalAt_loadG_word s1 "ev" 8#64 vstk hload_stk
      have h8_n : (8#64 : BitVec 64).toNat = 8 := rfl
      have hs1_gm8 : memW s1 (globN s1 "ev" + 8) = memW s (globN s "ev" + 8) := rfl
      rw [h8_n, hs1_gm8] at hstkw_nat
      have hsh1_stk : shapeEqHOL .one (shapeOfHOLExact (.val (.word stkw))) = true := by
        simp [shapeEqHOL, shapeOfHOLExact]
      rw [if_pos hsh1_stk]; dsimp only
      set s2 := setVarHOLFinite (ofString "stk") (.val (.word stkw)) s1 with hs2
      -- Step 3: `dec "pa"`
      rw [evaluateHOLFiniteState_dec_total]; dsimp only
      have hs2_sp : s2.locals.lookup (ofString "sp") = some (.val (.word spw)) := by
        simp [hs2, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "stk" ≠ ofString "sp" by decide]
      have hs2_stk : s2.locals.lookup (ofString "stk") = some (.val (.word stkw)) := by
        simp [hs2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hs2_i : s2.locals.lookup (ofString "i") = some (.val (.word iw)) := by
        simp [hs2, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hi_lk,
          show ofString "stk" ≠ ofString "i" by decide, show ofString "sp" ≠ ofString "i" by decide]
      let pa_w : BitVec 64 := stkw + (spw - 1#64 - iw) * 32#64
      have hpa_eval : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
          (.op .add [.var .local (ofString "stk"),
            .panop .mul [.op .sub [.op .sub [.var .local (ofString "sp"), .const (1#64)],
              .var .local (ofString "i")], .const (32#64)]]) =
          some (.val (.word pa_w)) := by
        simp [evalHOLExact, evalListHOLExact, hs2_stk, hs2_sp, hs2_i,
          wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord, pa_w]
      rw [hpa_eval]; dsimp only
      have hsh1_pa : shapeEqHOL .one (shapeOfHOLExact (.val (.word pa_w))) = true := by
        simp [shapeEqHOL, shapeOfHOLExact]
      rw [if_pos hsh1_pa]; dsimp only
      set s3 := setVarHOLFinite (ofString "pa") (.val (.word pa_w)) s2 with hs3
      -- Step 4: `dec "pb"`
      rw [evaluateHOLFiniteState_dec_total]; dsimp only
      have hs3_sp : s3.locals.lookup (ofString "sp") = some (.val (.word spw)) := by
        simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_sp,
          show ofString "pa" ≠ ofString "sp" by decide]
      have hs3_stk : s3.locals.lookup (ofString "stk") = some (.val (.word stkw)) := by
        simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_stk,
          show ofString "pa" ≠ ofString "stk" by decide]
      have hs3_j : s3.locals.lookup (ofString "j") = some (.val (.word jw)) := by
        simp [hs3, hs2, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hj_lk,
          show ofString "pa" ≠ ofString "j" by decide,
          show ofString "stk" ≠ ofString "j" by decide,
          show ofString "sp" ≠ ofString "j" by decide]
      let pb_w : BitVec 64 := stkw + (spw - 1#64 - jw) * 32#64
      have hpb_eval : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
          (.op .add [.var .local (ofString "stk"),
            .panop .mul [.op .sub [.op .sub [.var .local (ofString "sp"), .const (1#64)],
              .var .local (ofString "j")], .const (32#64)]]) =
          some (.val (.word pb_w)) := by
        simp [evalHOLExact, evalListHOLExact, hs3_stk, hs3_sp, hs3_j,
          wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord, pb_w]
      rw [hpb_eval]; dsimp only
      have hsh1_pb : shapeEqHOL .one (shapeOfHOLExact (.val (.word pb_w))) = true := by
        simp [shapeEqHOL, shapeOfHOLExact]
      rw [if_pos hsh1_pb]; dsimp only
      set s4 := setVarHOLFinite (ofString "pb") (.val (.word pb_w)) s3 with hs4
      -- Step 5: `dec "a"`
      rw [evaluateHOLFiniteState_dec_total]; dsimp only
      rcases hload_a : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
          (.load struct4 (.var .local (ofString "pa"))) with _ | va
      · simp only [hload_a]; exact herr_triv
      · simp only [hload_a]
        by_cases hsha : shapeEqHOL struct4 (shapeOfHOLExact va) = true
        · rw [if_pos hsha]; dsimp only
          have hva4 : ∃ w0 w1 w2 w3 : BitVec 64,
              va = .rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)] := by
            have hsh := hsha
            rw [shapeEqHOL_eq_true] at hsh
            rcases va with _ | fs | _
            · simp [struct4, shapeOfHOLExact] at hsh
            · simp only [struct4, shapeOfHOLExact, ShapeHOL.comb.injEq] at hsh
              rcases fs with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, _ | ⟨f3, _ | _⟩⟩⟩⟩
              · simp at hsh
              · simp at hsh
              · simp at hsh
              · simp at hsh
              · simp only [List.map, List.cons.injEq] at hsh
                obtain ⟨h0, h1, h2, h3, _⟩ := hsh
                rcases f0 with ⟨⟨w0⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h0
                rcases f1 with ⟨⟨w1⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h1
                rcases f2 with ⟨⟨w2⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h2
                rcases f3 with ⟨⟨w3⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h3
                exact ⟨w0, w1, w2, w3, rfl⟩
              · simp at hsh
            · simp [struct4, shapeOfHOLExact] at hsh
          obtain ⟨aw0, aw1, aw2, aw3, rfl⟩ := hva4
          set s5 := setVarHOLFinite (ofString "a")
            (.rStruct [.val (.word aw0), .val (.word aw1), .val (.word aw2), .val (.word aw3)]) s4 with hs5
          -- Step 6: `dec "b"`
          rw [evaluateHOLFiniteState_dec_total]; dsimp only
          rcases hload_b : @evalHOLExact 64 F _ s5.toExact (fun a => Classical.propDecidable (s5.memaddrs a))
              (.load struct4 (.var .local (ofString "pb"))) with _ | vb
          · simp only [hload_b]; exact herr_triv
          · simp only [hload_b]
            by_cases hshb : shapeEqHOL struct4 (shapeOfHOLExact vb) = true
            · rw [if_pos hshb]; dsimp only
              have hvb4 : ∃ w0 w1 w2 w3 : BitVec 64,
                  vb = .rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)] := by
                have hsh := hshb
                rw [shapeEqHOL_eq_true] at hsh
                rcases vb with _ | fs | _
                · simp [struct4, shapeOfHOLExact] at hsh
                · simp only [struct4, shapeOfHOLExact, ShapeHOL.comb.injEq] at hsh
                  rcases fs with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, _ | ⟨f3, _ | _⟩⟩⟩⟩
                  · simp at hsh
                  · simp at hsh
                  · simp at hsh
                  · simp at hsh
                  · simp only [List.map, List.cons.injEq] at hsh
                    obtain ⟨h0, h1, h2, h3, _⟩ := hsh
                    rcases f0 with ⟨⟨w0⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h0
                    rcases f1 with ⟨⟨w1⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h1
                    rcases f2 with ⟨⟨w2⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h2
                    rcases f3 with ⟨⟨w3⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h3
                    exact ⟨w0, w1, w2, w3, rfl⟩
                  · simp at hsh
                · simp [struct4, shapeOfHOLExact] at hsh
              obtain ⟨bw0, bw1, bw2, bw3, rfl⟩ := hvb4
              set s6 := setVarHOLFinite (ofString "b")
                (.rStruct [.val (.word bw0), .val (.word bw1), .val (.word bw2), .val (.word bw3)]) s5 with hs6
              -- Slot bounds for `pa_w` and `pb_w`
              have hslot_i := stack_slot_in (item := iw) hInv.1.2 hFW0 hstkw_nat hspw_nat hcap_le1024 hsp_le_cap
                (by rw [hspw_nat]; exact hi_lt)
              have hslot_j := stack_slot_in (item := jw) hInv.1.2 hFW0 hstkw_nat hspw_nat hcap_le1024 hsp_le_cap
                (by rw [hspw_nat]; exact hj_lt)
              have hs6_pa : s6.locals.lookup (ofString "pa") = some (.val (.word pa_w)) := by
                simp [hs6, hs5, hs4, hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "b" ≠ ofString "pa" by decide,
                  show ofString "a" ≠ ofString "pa" by decide,
                  show ofString "pb" ≠ ofString "pa" by decide]
              have hs6_pb : s6.locals.lookup (ofString "pb") = some (.val (.word pb_w)) := by
                simp [hs6, hs5, hs4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "b" ≠ ofString "pb" by decide,
                  show ofString "a" ≠ ofString "pb" by decide]
              have hs6_a : s6.locals.lookup (ofString "a") =
                  some (.rStruct [.val (.word aw0), .val (.word aw1), .val (.word aw2), .val (.word aw3)]) := by
                simp [hs6, hs5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "b" ≠ ofString "a" by decide]
              have hs6_b : s6.locals.lookup (ofString "b") =
                  some (.rStruct [.val (.word bw0), .val (.word bw1), .val (.word bw2), .val (.word bw3)]) := by
                simp [hs6, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              -- Step 7: `store pa b`
              rw [evaluateHOLFiniteState_seq_line780]
              rcases hst1 : evaluateHOLFiniteState s6
                  (.store (.var .local (ofString "pa")) (.var .local (ofString "b"))) with ⟨r1, m1⟩
              simp only [hst1]
              cases r1 with
              | some res1 =>
                have herr := store_some_eq_error' hst1; subst herr; dsimp only; exact herr_triv
              | none =>
                dsimp only
                let oldStk : Ivl := (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))
                have hd1 := ScratchByteEff.of_store_struct4 (s := s6) (Rl := [oldStk])
                  hInv.1.1.memaddrs hst1
                  (fun v hv => by
                    change s6.locals.lookup (ofString "b") = some v at hv
                    rw [hs6_b] at hv; injection hv with hv'
                    exact ⟨bw0, bw1, bw2, bw3, hv'.symm⟩)
                  (fun addr hdst => by
                    change s6.locals.lookup (ofString "pa") = some (.val (.word addr)) at hdst
                    rw [hs6_pa] at hdst; injection hdst with hd1'; injection hd1' with hd2'; injection hd2' with hd3'
                    subst hd3'
                    exact ⟨hslot_i.2.2.2.1, oldStk, List.mem_singleton.2 rfl,
                      by dsimp only [oldStk]; rw [← hstkw_nat]; exact hslot_i.2.1,
                      by dsimp only [oldStk]; rw [← hstkw_nat]; exact hslot_i.2.2.1⟩)
                obtain ⟨heff1, hm1_loc, hm1_glob⟩ := hd1
                -- Step 8: `store pb a`
                rw [evaluateHOLFiniteState_seq_line780]
                rcases hst2 : evaluateHOLFiniteState m1
                    (.store (.var .local (ofString "pb")) (.var .local (ofString "a"))) with ⟨r2, m2⟩
                simp only [hst2]
                cases r2 with
                | some res2 =>
                  have herr := store_some_eq_error' hst2; subst herr; dsimp only; exact herr_triv
                | none =>
                  dsimp only
                  have hd2 := ScratchByteEff.of_store_struct4 (Rl := [oldStk])
                    (heff1.memaddrs.trans hInv.1.1.memaddrs) hst2
                    (fun v hv => by
                      change m1.locals.lookup (ofString "a") = some v at hv
                      rw [hm1_loc, hs6_a] at hv; injection hv with hv'
                      exact ⟨aw0, aw1, aw2, aw3, hv'.symm⟩)
                    (fun addr hdst => by
                      change m1.locals.lookup (ofString "pb") = some (.val (.word addr)) at hdst
                      rw [hm1_loc, hs6_pb] at hdst; injection hdst with hd1'; injection hd1' with hd2'; injection hd2' with hd3'
                      subst hd3'
                      exact ⟨hslot_j.2.2.2.1, oldStk, List.mem_singleton.2 rfl,
                        by dsimp only [oldStk]; rw [← hstkw_nat]; exact hslot_j.2.1,
                        by dsimp only [oldStk]; rw [← hstkw_nat]; exact hslot_j.2.2.1⟩)
                  obtain ⟨heff2, hm2_loc, hm2_glob⟩ := hd2
                  -- Step 9: `return 0`
                  rw [evaluateHOLFiniteState_return]
                  have hc0_m2 : @evalHOLExact 64 F _ m2.toExact
                      (fun a => Classical.propDecidable (m2.memaddrs a)) (.const 0#64) =
                      some (.val (.word 0#64)) := rfl
                  simp only [hc0_m2]
                  have hsz0 : sizeOfShapeWithContextHOL m2.structs
                      (shapeOfHOLExact (.val (.word 0#64))) ≤ 32 := by
                    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
                  rw [if_pos hsz0]; dsimp only
                  let post := {
                    {
                      {
                        {
                          {
                            { m2.emptyLocalsHOLFinite with
                              locals := m2.emptyLocalsHOLFinite.locals.resVarEq
                                (ofString "b", s5.locals.lookup (ofString "b")) } with
                            locals := (m2.emptyLocalsHOLFinite.locals.resVarEq
                              (ofString "b", s5.locals.lookup (ofString "b"))).resVarEq
                              (ofString "a", s4.locals.lookup (ofString "a")) } with
                          locals := ((m2.emptyLocalsHOLFinite.locals.resVarEq
                            (ofString "b", s5.locals.lookup (ofString "b"))).resVarEq
                            (ofString "a", s4.locals.lookup (ofString "a"))).resVarEq
                            (ofString "pb", s3.locals.lookup (ofString "pb")) } with
                        locals := (((m2.emptyLocalsHOLFinite.locals.resVarEq
                          (ofString "b", s5.locals.lookup (ofString "b"))).resVarEq
                          (ofString "a", s4.locals.lookup (ofString "a"))).resVarEq
                          (ofString "pb", s3.locals.lookup (ofString "pb"))).resVarEq
                          (ofString "pa", s2.locals.lookup (ofString "pa")) } with
                      locals := ((((m2.emptyLocalsHOLFinite.locals.resVarEq
                        (ofString "b", s5.locals.lookup (ofString "b"))).resVarEq
                        (ofString "a", s4.locals.lookup (ofString "a"))).resVarEq
                        (ofString "pb", s3.locals.lookup (ofString "pb"))).resVarEq
                        (ofString "pa", s2.locals.lookup (ofString "pa"))).resVarEq
                        (ofString "stk", s1.locals.lookup (ofString "stk")) } with
                    locals := (((((m2.emptyLocalsHOLFinite.locals.resVarEq
                      (ofString "b", s5.locals.lookup (ofString "b"))).resVarEq
                      (ofString "a", s4.locals.lookup (ofString "a"))).resVarEq
                      (ofString "pb", s3.locals.lookup (ofString "pb"))).resVarEq
                      (ofString "pa", s2.locals.lookup (ofString "pa"))).resVarEq
                      (ofString "stk", s1.locals.lookup (ofString "stk"))).resVarEq
                      (ofString "sp", s.locals.lookup (ofString "sp")) }
                  have hpost_glob : post.globals = s.globals := by
                    change m2.globals = s.globals
                    rw [hm2_glob, hm1_glob]; rfl
                  have hs_s6 : ScratchByteEff s s6 [oldStk] :=
                    ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩
                  have heff_old : ScratchByteEff s post [oldStk] :=
                    ((hs_s6.trans heff1).trans heff2).with_locals_clock post.locals m2.clock
                  have heff_full : ScratchByteEff s post [(0, 0), (globN s "ev", 280), oldStk] :=
                    heff_old.mono (fun x hx => by
                      simp only [List.mem_singleton] at hx; subst hx
                      exact ⟨oldStk, by simp, le_refl _, le_refl _⟩)
                  have hApost : ArenaReady post :=
                    ⟨guestInv_congr (s := s) heff_full.code heff_full.memaddrs
                      heff_full.shMemaddrs heff_full.baseAddr hInv.1.1,
                     arenaOK_congr hpost_glob hInv.1.2⟩
                  have hsc_le : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by
                    unfold globN; rw [hpost_glob]
                  have he0_eq : ∀ off, off + 8 ≤ 280 → off % 8 = 0 →
                      memW post (globN s "ev" + off) = memW s (globN s "ev" + off) := by
                    intro off hoff hoff8
                    unfold memW
                    rw [heff_old.cell_frame (BitVec.ofNat 64 (globN s "ev" + off))]
                    intro x hx
                    simp only [List.mem_singleton] at hx; subst hx
                    have htn : (BitVec.ofNat 64 (globN s "ev" + off)).toNat = globN s "ev" + off :=
                      Nat.mod_eq_of_lt (by omega)
                    rw [htn]
                    have he0_8 : (globN s "ev") % 8 = 0 := (hFW0.1 (globN s "ev", 280) (by simp)).2.1
                    have ha8 : (globN s "ev" + off) % 8 = 0 := by omega
                    have hold_8 : (memW s (globN s "ev" + 8)) % 8 = 0 :=
                      (hFW0.1 oldStk (by simp [oldStk])).2.1
                    have hpw_fo := hInv.2.choose_spec.2.2.2.2.2.2.2.1
                    have hch_s : ∃ tl, evmChain s = (globN s "ev", globN s "cur_cont") :: tl := ⟨_, rfl⟩
                    obtain ⟨tl_s, hch_s_eq⟩ := hch_s
                    rw [hch_s_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw_fo
                    have hd_stk : Disj (globN s "ev", 280) oldStk := by
                      have hp0 := hpw_fo.1; unfold frameObjects at hp0
                      exact (List.pairwise_cons.1 hp0).1 _ (by simp [oldStk])
                    exact not_cellHits_of_disj_aligned (i := (globN s "ev", 280)) ha8 hold_8
                      (Nat.le_add_right _ off) (Nat.add_le_add_left hoff _) hd_stk
                  have hnew_stk :
                      ((0, 0).2 = 0 ∧ memW post (globN s "ev" + 8) = memW s (globN s "ev" + 8) ∧
                        memW post (globN s "ev" + 232) = memW s (globN s "ev" + 232)) ∨
                      ((0, 0).2 ≠ 0 ∧ (memW post (globN s "ev" + 8), 32 * memW post (globN s "ev" + 232)) = (0, 0)) :=
                    Or.inl ⟨rfl,
                      he0_eq 8 (by omega) (by omega),
                      he0_eq 232 (by omega) (by omega)⟩
                  have hcap_post :
                      1 ≤ memW post (globN s "ev" + 232) ∧
                      memW post (globN s "ev" + 16) ≤ memW post (globN s "ev" + 232) ∧
                      memW post (globN s "ev" + 232) ≤ 1024 := by
                    rw [he0_eq 16 (by omega) (by omega), he0_eq 232 (by omega) (by omega)]
                    exact ⟨hcap_ge1, hsp_le_cap, hcap_le1024⟩
                  obtain ⟨hInv_p, hch_p, hR_p⟩ := evmInv_of_head_stack_push hInv hApost hsc_le
                    heff_full (Or.inl rfl)
                    (fun off hoff hoff8 _ _ _ => he0_eq off hoff hoff8)
                    hnew_stk hcap_post
                  exact ⟨fun _ _ => ⟨hInv_p, hch_p, le_of_eq hR_p, hpost_glob⟩,
                    by rintro ⟨_, h⟩; cases h⟩
            · rw [if_neg hshb]; dsimp only; exact herr_triv
        · rw [if_neg hsha]; dsimp only; exact herr_triv

/-! ## 3. Bounded `op_push` (`nbytes ≤ 32`) -/

private theorem op_push_after_gas {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (nw : BitVec 64) (hn_le : nw.toNat ≤ 32) :
    HandlerRun s0
      (fun t => t.locals.lookup (ofString "nbytes") = some (.val (.word nw)))
      true
      (.decCall (ofString "mark") .one (ofString "heap_mark") []
        (.decCall (ofString "tmp") .one (ofString "alloc") [.const (32#64)]
          (.seq
            (.call (some (none, none)) (ofString "buffer_read")
              [.load .one (.op .add [.var .global (ofString "ev"), .const (48#64)]),
               .load .one (.op .add [.var .global (ofString "ev"), .const (56#64)]),
               .op .add [.load .one (.op .add [.var .global (ofString "ev"), .const (0#64)]), .const (1#64)],
               .var .local (ofString "nbytes"),
               .var .local (ofString "tmp")])
            (.decCall (ofString "v") (.comb [.one, .one, .one, .one]) (ofString "u256_from_be")
              [.var .local (ofString "tmp"), .var .local (ofString "nbytes")]
              (.seq
                (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")])
                (.seq
                  (.call (some (none, none)) (ofString "stack_push") [.var .local (ofString "v")])
                  (.seq
                    (.call (some (none, none)) (ofString "pc_add")
                      [.op .add [.const (1#64), .var .local (ofString "nbytes")]])
                    (.return (.const (0#64)))))))))) := by
  intro t hc hInv hlen hR ht_nb hnt
  simp only [↓reduceIte] at hR
  have hhp_mem : "heap_ptr" ∈ guestGlobalNames := by decide
  obtain ⟨markw, hmark_gw⟩ := hInv.1.2.2.2.2.2.2.2.2.2 "heap_ptr" hhp_mem
  have hmark_lk : t.globals.lookup (ofString "heap_ptr") = some (.val (.word markw)) := hmark_gw
  have hmark_nat : markw.toNat = globN t "heap_ptr" := by simp [globN, hmark_lk]
  have hmark_le : markw.toNat ≤ InitECandidate.Solver.HeapPotential.cMax.toNat := by
    rw [hmark_nat]; exact hInv.1.2.2.1
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
  -- Step 2: `decCall "tmp" .one "alloc" [.const 32]`
  have hargs_al : evalListHOLFinite t1 (h := fun a => Classical.propDecidable (t1.memaddrs a)) [.const (32#64)] =
      some [.val (.word (32#64))] := rfl
  have hlook_al := pan_one_word_lookup t1.code.lookup (ofString "alloc") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_alloc) (32#64) (by change t.code.lookup _ = _; rw [hc]; exact lookup_alloc)
  refine decCall_general_step s0 t1 (ofString "tmp") (ofString "alloc") .one
    [.const (32#64)] [.val (.word (32#64))] _ hargs_al hnt ?_
  clear hnt
  intro body_al cal_al rs_al hlk_al _
  have hEq_al := Option.some.inj (hlk_al.symm.trans hlook_al)
  obtain ⟨rfl, hEq_al2⟩ := Prod.mk.inj hEq_al
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq_al2
  refine ⟨alloc_body_no_evmErr _ hc, ?_⟩
  intro val_al sal hrun_al _ hnt
  let cal_al := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word (32#64)))
  let ent_al := callEntryStateHOLFinite t1 cal_al
  have hal_gen := M13.evaluate_alloc_body_general ent_al markw (32#64) hc hmark_le hmark_lk
    (by simp [ent_al, cal_al, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
  have hal_meta := PanRunBounded.evaluateHOLFiniteState_metadata ent_al (sourceFnBody Guest.Software.guestFn_alloc)
  have hal_ba := evaluate_baseAddr ent_al (sourceFnBody Guest.Software.guestFn_alloc)
  have hrun_al' : evaluateHOLFiniteState ent_al (sourceFnBody Guest.Software.guestFn_alloc) = (some (.returned val_al), sal) := hrun_al
  rw [hrun_al'] at hal_gen hal_meta hal_ba
  dsimp only at hal_gen hal_meta hal_ba
  obtain ⟨rfl, hsal_glob, hsal_mem, hbnd32, hq_le, _⟩ := hal_gen val_al rfl
  let q : BitVec 64 := (markw + ((32#64) + 7)) &&& ((0 : BitVec 64) - 8)
  set t2 := setVarHOLFinite (ofString "tmp") (.val (.word markw)) { sal with locals := t1.locals }
  have ht2_code : t2.code = originalRuntimeCode := hal_meta.1.trans hc
  have ht2_ma : t2.memaddrs = ordinaryDomain := hal_meta.2.1.trans hInv.1.1.memaddrs
  have ht2_be : t2.be = t.be := hal_meta.2.2.1
  have ht2_sh : t2.shMemaddrs = t.shMemaddrs := hal_meta.2.2.2.1
  have ht2_ba : t2.baseAddr = t.baseAddr := hal_ba
  have ht2_glob : t2.globals = t.globals.update (ofString "heap_ptr", .val (.word q)) := hsal_glob
  have ht2_mem : t2.memory = t.memory := hsal_mem
  have ht2_tmp : t2.locals.lookup (ofString "tmp") = some (.val (.word markw)) := by
    simp [t2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have ht2_mark : t2.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    have hne : ofString "tmp" ≠ ofString "mark" := by decide
    simp [t2, t1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne]
  have ht2_nb : t2.locals.lookup (ofString "nbytes") = some (.val (.word nw)) := by
    have hne1 : ofString "tmp" ≠ ofString "nbytes" := by decide
    have hne2 : ofString "mark" ≠ ofString "nbytes" := by decide
    simp [t2, t1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      hne1, Ne.symm hne1, hne2, Ne.symm hne2, ht_nb]
  -- Step 3: `seq (call "buffer_read" [bExp, blExp, sExp, nbytes, tmp]) ...`
  let bExp : ExpHOL 64 := .load .one (.op .add [.var .global (ofString "ev"), .const (48#64)])
  let blExp : ExpHOL 64 := .load .one (.op .add [.var .global (ofString "ev"), .const (56#64)])
  let sExp : ExpHOL 64 := .op .add [.load .one (.op .add [.var .global (ofString "ev"), .const (0#64)]), .const (1#64)]
  refine seq_step s0 t2 _ _ hnt ?_
  clear hnt
  intro hnt_br
  by_cases hargs_br_ok :
      (∃ bw : BitVec 64, @evalHOLExact 64 F _ t2.toExact (fun a => Classical.propDecidable (t2.memaddrs a)) bExp = some (.val (.word bw))) ∧
      (∃ blw : BitVec 64, @evalHOLExact 64 F _ t2.toExact (fun a => Classical.propDecidable (t2.memaddrs a)) blExp = some (.val (.word blw))) ∧
      (∃ sw : BitVec 64, @evalHOLExact 64 F _ t2.toExact (fun a => Classical.propDecidable (t2.memaddrs a)) sExp = some (.val (.word sw)))
  · obtain ⟨⟨bw, hbw⟩, ⟨blw, hblw⟩, ⟨sw, hsw⟩⟩ := hargs_br_ok
    have hbnd_mn : markw.toNat + nw.toNat < 2 ^ 64 := by
      have hcMax_val : InitECandidate.Solver.HeapPotential.cMax.toNat = 2952790016 := rfl
      omega
    have hbr := eval_call_buffer_read_bre t2 bExp blExp sExp (.var .local (ofString "nbytes")) (.var .local (ofString "tmp"))
      bw blw sw nw markw [(markw.toNat, 32)] ht2_code ht2_ma hbw hblw hsw ht2_nb ht2_tmp hbnd_mn
      (fun _ => ⟨(markw.toNat, 32), List.mem_singleton.2 rfl, le_refl _, by dsimp only; omega⟩)
      hnt_br
    refine ⟨?_, fun hne => hbr.2 hne⟩
    intro hnone hnt
    obtain ⟨heff_br, ht3_loc⟩ := hbr.1 hnone
    set t3 := (evaluateHOLFiniteState t2
      (.call (some (none, none)) (ofString "buffer_read")
        [bExp, blExp, sExp, .var .local (ofString "nbytes"), .var .local (ofString "tmp")])).2
    have ht3_code : t3.code = originalRuntimeCode := heff_br.code.trans ht2_code
    have ht3_tmp : t3.locals.lookup (ofString "tmp") = some (.val (.word markw)) := by
      rw [ht3_loc]; exact ht2_tmp
    have ht3_mark : t3.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
      rw [ht3_loc]; exact ht2_mark
    have ht3_nb : t3.locals.lookup (ofString "nbytes") = some (.val (.word nw)) := by
      rw [ht3_loc]; exact ht2_nb
    -- Step 4: `decCall "v" (comb [1,1,1,1]) "u256_from_be" [tmp, nbytes]`
    have hargs_ub : evalListHOLFinite t3 (h := fun a => Classical.propDecidable (t3.memaddrs a))
        [.var .local (ofString "tmp"), .var .local (ofString "nbytes")] =
        some [.val (.word markw), .val (.word nw)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ht3_tmp, ht3_nb]
    refine decCall_general_step s0 t3 (ofString "v") (ofString "u256_from_be") _
      [.var .local (ofString "tmp"), .var .local (ofString "nbytes")]
      [.val (.word markw), .val (.word nw)] _ hargs_ub hnt ?_
    clear hnt
    intro body_ub cal_ub rs_ub hlk_ub _
    have hlk_ub_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "u256_from_be")
        [.val (.word markw), .val (.word nw)] = some (body_ub, cal_ub, rs_ub) := by
      rwa [← ht3_code]
    have hro_ub : readOnlyProg opRoCallees body_ub = true :=
      installed_body_readOnly 86 (by rw [guestAst_len]; decide)
        Guest.Software.guestFn_u256_from_be rfl opRoCallees rfl hlk_ub_orig
    have hnr_ub : noRaiseProg u256FromBeCallees body_ub = true :=
      u256FromBeCallees_good (ofString "u256_from_be") (by decide)
        [.val (.word markw), .val (.word nw)] body_ub cal_ub rs_ub hlk_ub_orig
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
      simp only [t4, setVarHOLFinite]
      rw [hlf_ub]; cases t3; rfl
    have ht4_code : t4.code = originalRuntimeCode := by
      rw [ht4_lf]; exact ht3_code
    have ht4_mark : t4.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
      have hne : ofString "v" ≠ ofString "mark" := by decide
      simp [t4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, ht3_mark]
    -- Step 5: `call "heap_release" [mark]`
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
          have hg4 : ent_hr.globals = t2.globals := by
            change t4.globals = t2.globals
            rw [ht4_lf, heff_br.globals]
          rw [hg4, ht2_glob]
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
        have hg4 : ent_hr.globals = t2.globals := by
          change t4.globals = t2.globals
          rw [ht4_lf, heff_br.globals]
        change ent_hr.globals.update (ofString "heap_ptr", .val (.word markw)) = t.globals
        rw [hg4, ht2_glob]
        exact globals_update_twice_restore t.globals (ofString "heap_ptr")
          (.val (.word markw)) (.val (.word q)) hmark_lk
      have ht5_code : t5.code = originalRuntimeCode := ht4_code
      have ht4_mem : t4.memory = t3.memory := by rw [ht4_lf]
      have ht5_mem : t5.memory = t3.memory := ht4_mem
      have heff_t_t5 : ByteRegionEffect t t5 [(markw.toNat, 32)] := by
        refine ⟨ht5_code.trans hc.symm, ?_, ?_, ?_, ?_, ht5_glob, ?_, ?_, ?_⟩
        · change t4.memaddrs = t.memaddrs
          rw [ht4_lf, heff_br.memaddrs, ht2_ma, hInv.1.1.memaddrs]
        · change t4.shMemaddrs = t.shMemaddrs
          rw [ht4_lf, heff_br.shMemaddrs, ht2_sh]
        · change t4.baseAddr = t.baseAddr
          rw [ht4_lf, heff_br.baseAddr, ht2_ba]
        · change t4.be = t.be
          rw [ht4_lf, heff_br.be, ht2_be]
        · intro a hna
          rw [ht5_mem]
          have hna2 : ¬ t2.memaddrs a := by
            rw [ht2_ma, ← hInv.1.1.memaddrs]; exact hna
          rw [heff_br.out_dom a hna2, ht2_mem]
        · intro a ha
          rw [ht5_mem, heff_br.cell_frame a ha, ht2_mem]
        · intro b hb hno
          have hbe53 : t5.be = t3.be := by
            change t4.be = t3.be; rw [ht4_lf]
          have hmb5 : memB t5 b = memB t3 b := by
            unfold memB; rw [ht5_mem, hbe53]
          have hmb2 : memB t2 b = memB t b := by
            unfold memB; rw [ht2_mem, ht2_be]
          rw [hmb5, heff_br.byte_frame b hb hno, hmb2]
      have hmark32_le : markw.toNat + 32 ≤ InitECandidate.Solver.HeapPotential.cMax.toNat := by
        have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
        omega
      have heff_ext : ByteRegionEffect t t5 ((markw.toNat, 32) :: untypedGlobalBufIvls t) :=
        heff_t_t5.mono (fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx
          exact ⟨(markw.toNat, 32), List.mem_cons_self, le_refl _, le_refl _⟩)
      obtain ⟨hInv_t5, hch_t5, hR_t5⟩ :=
        heapGap_and_untypedBufs_bre_to_evmStep hInv hmark_nat hmark32_le hmark_8 heff_ext
      have hlen_t5 : (evmChain t5).length = (evmChain s0).length := by
        rw [hch_t5]; exact hlen
      have hR_lt_t5 : if true then evmR t5 < evmR s0 else evmR t5 ≤ evmR s0 := by
        simp only [↓reduceIte, hR_t5]; exact hR
      have htail : HandlerRun s0 (fun _ => True) true
          (.seq (.call (some (none, none)) (ofString "stack_push") [.var .local (ofString "v")])
            (.seq (.call (some (none, none)) (ofString "pc_add")
              [.op .add [.const (1#64), .var .local (ofString "nbytes")]])
              (.return (.const (0#64))))) :=
        HandlerRun.seq_call_simple eps_stack_push
          (HandlerRun.seq_call_simple eps_pc_add (HandlerRun.ret _))
      exact htail t5 ht5_code hInv_t5 hlen_t5 hR_lt_t5 trivial hnt
  · rw [evaluateHOLFiniteState_call]
    rcases hargs_br : evalListHOLFinite t2
        (h := fun a => Classical.propDecidable (t2.memaddrs a))
        [bExp, blExp, sExp, .var .local (ofString "nbytes"), .var .local (ofString "tmp")] with _ | vals_br
    · dsimp only
      refine ⟨(fun h => by cases h), fun _ => ⟨(fun _ h => by cases h), ?_⟩⟩
      rintro ⟨_, h⟩; cases h
    · dsimp only
      rcases hlk_br : lookupCodeHOLFinite t2.code.lookup (ofString "buffer_read") vals_br with
        _ | ⟨body_br, cal_br, rs_br⟩
      · dsimp only
        refine ⟨(fun h => by cases h), fun _ => ⟨(fun _ h => by cases h), ?_⟩⟩
        rintro ⟨_, h⟩; cases h
      · exfalso
        apply hargs_br_ok
        have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
          t2.code.lookup (ofString "buffer_read") vals_br body_br cal_br rs_br hlk_br
        rw [ht2_code] at hx
        simp only [Flapjack.lookupCodeHOLExact, lookup_buffer_read] at hx
        split at hx
        · rename_i hcond
          have hlen5 : vals_br.length = 5 := by
            have hl := hcond.2.1
            simpa using hl.symm
          rcases vals_br with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, _ | ⟨v5, _ | _⟩⟩⟩⟩⟩
          all_goals try (simp at hlen5)
          have hsh123 : shapeEqHOL .one (shapeOfHOLExact v1) = true ∧
              shapeEqHOL .one (shapeOfHOLExact v2) = true ∧
              shapeEqHOL .one (shapeOfHOLExact v3) = true := by
            have hs := hcond.2.2
            simp only [List.map, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
              List.zip_cons_cons, List.zip_nil_right] at hs
            exact ⟨hs.1, hs.2.1, hs.2.2.1⟩
          have hw_of_one : ∀ u : ValueHOL 64, shapeEqHOL .one (shapeOfHOLExact u) = true →
              ∃ w : BitVec 64, u = .val (.word w) := by
            intro u hu
            rcases u with ⟨⟨w⟩⟩ | _ | _
            · exact ⟨w, rfl⟩
            · simp [shapeOfHOLExact, shapeEqHOL] at hu
            · simp [shapeOfHOLExact, shapeEqHOL] at hu
          obtain ⟨bw, rfl⟩ := hw_of_one v1 hsh123.1
          obtain ⟨blw, rfl⟩ := hw_of_one v2 hsh123.2.1
          obtain ⟨sw, rfl⟩ := hw_of_one v3 hsh123.2.2
          change @evalListHOLExact 64 F _ t2.toExact (fun a => Classical.propDecidable (t2.memaddrs a))
            [bExp, blExp, sExp, .var .local (ofString "nbytes"), .var .local (ofString "tmp")] =
            some [.val (.word bw), .val (.word blw), .val (.word sw), v4, v5] at hargs_br
          have hb4 : @evalHOLExact 64 F _ t2.toExact (fun a => Classical.propDecidable (t2.memaddrs a))
              (.var .local (ofString "nbytes")) = some (.val (.word nw)) := by
            simp [evalHOLExact, ht2_nb]
          have hb5 : @evalHOLExact 64 F _ t2.toExact (fun a => Classical.propDecidable (t2.memaddrs a))
              (.var .local (ofString "tmp")) = some (.val (.word markw)) := by
            simp [evalHOLExact, ht2_tmp]
          rcases hb1 : @evalHOLExact 64 F _ t2.toExact (fun a => Classical.propDecidable (t2.memaddrs a)) bExp with _ | u1
          · simp [evalListHOLExact, hb1] at hargs_br
          · rcases hb2 : @evalHOLExact 64 F _ t2.toExact (fun a => Classical.propDecidable (t2.memaddrs a)) blExp with _ | u2
            · simp [evalListHOLExact, hb1, hb2] at hargs_br
            · rcases hb3 : @evalHOLExact 64 F _ t2.toExact (fun a => Classical.propDecidable (t2.memaddrs a)) sExp with _ | u3
              · simp [evalListHOLExact, hb1, hb2, hb3] at hargs_br
              · simp [evalListHOLExact, hb1, hb2, hb3, hb4, hb5] at hargs_br
                obtain ⟨rfl, rfl, rfl, _⟩ := hargs_br
                exact ⟨⟨bw, rfl⟩, ⟨blw, rfl⟩, ⟨sw, rfl⟩⟩
        · cases hx

theorem op_push_bounded_spec :
    FunSpec
      (fun s => EvmRun s ∧
        ∃ n : BitVec 64, s.locals.lookup (ofString "nbytes") = some (.val (.word n)) ∧ n.toNat ≤ 32)
      OpDispatchPost
      (ofString "op_push") := by
  refine ⟨_, _, _, lookup_op_push, ?_⟩
  intro F s0 hcode ⟨hRun, nw, hnb, hn_le⟩ _ hnt
  have hrun : HandlerRun s0
      (fun t => t.locals.lookup (ofString "nbytes") = some (.val (.word nw)))
      false
      (sourceFnBody Guest.Software.guestFn_op_push) := by
    dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_op_push,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
      Option.map, List.map]
    -- Rewrite `.seq (.ite c g2 g3) rest` on state `s0`
    intro t hc hInv hlen hR ht_nb hnt_body
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt_body ⊢
    have hcmp : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        (.cmp .equal (.var .local (ofString "nbytes")) (.const 0#64)) =
        some (.val (.word (if nw = 0#64 then 1 else 0))) := by
      simp [evalHOLExact, ht_nb, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hcmp] at hnt_body ⊢; dsimp only at hnt_body ⊢
    by_cases hnw0 : nw = 0#64
    · have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
      simp only [hnw0, ↓reduceIte, h10] at hnt_body ⊢
      rw [← evaluateHOLFiniteState_seq_line780] at hnt_body ⊢
      refine (HandlerRun.seq_charge_gas
        (P := fun u => u.locals.lookup (ofString "nbytes") = some (.val (.word 0#64)))
        (Q := fun u => u.locals.lookup (ofString "nbytes") = some (.val (.word 0#64)))
        (fun _ w hw _ _ => by
          simp only [evalHOLExact] at hw
          injection hw with h1; injection h1 with h2; injection h2 with h3; subst h3; decide)
        (fun _ _ _ hu_nb _ _ _ => hu_nb)
        (op_push_after_gas s0 0#64 (by decide))) t hc hInv hlen hR (by rwa [hnw0] at ht_nb) hnt_body
    · simp only [hnw0, ↓reduceIte] at hnt_body ⊢
      rw [← evaluateHOLFiniteState_seq_line780] at hnt_body ⊢
      refine (HandlerRun.seq_charge_gas
        (P := fun u => u.locals.lookup (ofString "nbytes") = some (.val (.word nw)))
        (Q := fun u => u.locals.lookup (ofString "nbytes") = some (.val (.word nw)))
        (fun _ w hw _ _ => by
          simp only [evalHOLExact] at hw
          injection hw with h1; injection h1 with h2; injection h2 with h3; subst h3; decide)
        (fun _ _ _ hu_nb _ _ _ => hu_nb)
        (op_push_after_gas s0 nw hn_le)) t hc hInv hlen hR ht_nb hnt_body
  exact hrun s0 hcode hRun.1 rfl (le_refl _) hnb hnt

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
