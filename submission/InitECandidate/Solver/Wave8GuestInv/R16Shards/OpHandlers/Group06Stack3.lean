import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.Common
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.ReadOnly
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.StackPush
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.Group06Stack2

/-! # OpHandlerSpec Group 06c (`OpHandlers-A`): 7 stack and immediate opcode specs -/

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
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8Contracts.M23

/-! ## 1. Direct handlers -/

theorem op_pop_spec : OpHandlerSpec (ofString "op_pop") := by
  refine opHandlerSpec_of_run 513 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_pop rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_pop, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.seq_charge_gas_const (by decide)
        (HandlerRun.seq_call_simple eps_pc_add
          (HandlerRun.ret _)))

theorem op_msize_spec : OpHandlerSpec (ofString "op_msize") := by
  refine opHandlerSpec_of_run 511 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_msize rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_msize, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  exact
    HandlerRun.seq_charge_gas_const (by decide)
      (HandlerRun.seq_call_simple eps_stack_push_word
        (HandlerRun.seq_call_simple eps_pc_add
          (HandlerRun.ret _)))

/-! ## 2. Bounded immediate and stack-guard helpers -/

theorem decode_single_body_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_single)).1 =
      some (.returned v)) :
    ∃ nw : BitVec 64, v = .val (.word nw) ∧ nw.toNat ≤ 255 := by
  have hbody : sourceFnBody Guest.Software.guestFn_decode_single =
      .seq (.ite (.cmp .notEqual (.const (0#64))
          (.op .or [.cmp .notLower (.const (90#64)) (.var .local (ofString "x")),
            .cmp .notLower (.var .local (ofString "x")) (.const (128#64))]))
        (.return (.op .and [.op .add [.var .local (ofString "x"), .const (145#64)], .const (255#64)]))
        .skip)
      (.seq (.raise (ofString "EvmErr") (.const (10#64))) (.return (.const (0#64)))) := rfl
  rw [hbody, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
  split at hret
  · rename_i w hw
    by_cases hw0 : w = 0
    · subst hw0
      simp only [↓reduceIte, evaluateHOLFiniteState_skip] at hret
      rw [evaluateHOLFiniteState_seq_line780] at hret
      rcases hr : evaluateHOLFiniteState s (.raise (ofString "EvmErr") (.const 10#64)) with ⟨rr, sr⟩
      cases rr with
      | none => exact absurd hr (fun h => raise_ne_none s _ _ (by rw [h]))
      | some r0 =>
        rw [hr] at hret; dsimp only at hret
        rw [evaluateHOLFiniteState_raise] at hr
        revert hr
        split
        · dsimp only
          split
          · intro hr; injection hr with h1 _; rw [← h1] at hret; cases hret
          · intro hr; injection hr with h1 _; rw [← h1] at hret; cases hret
        · intro hr; injection hr with h1 _; rw [← h1] at hret; cases hret
    · simp only [hw0, ↓reduceIte] at hret
      rw [evaluateHOLFiniteState_return] at hret
      rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.op .and [.op .add [.var .local (ofString "x"), .const (145#64)], .const (255#64)]) with _ | rv
      · simp [hev] at hret
      · rw [hev] at hret
        by_cases hsz : sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact rv) ≤ 32
        · simp only [if_pos hsz] at hret
          injection hret with h1; injection h1 with hv
          subst hv
          simp only [evalHOLExact, evalListHOLExact] at hev
          rcases hx : s.locals.lookup (ofString "x") with _ | xv
          · simp [hx] at hev
          · rcases xv with ⟨⟨xw⟩⟩ | _ | _
            · simp [hx, valueIsWord, valueWord, wordOpHOL, wordOp] at hev
              refine ⟨(xw + 145#64) &&& 255#64, hev.symm, ?_⟩
              rw [BitVec.toNat_and]
              have h255 : (255#64 : BitVec 64).toNat = 255 := rfl
              rw [h255]
              have hand_lt : (xw + 145#64).toNat &&& 255 < 256 :=
                Nat.and_lt_two_pow (n := 8) (x := (xw + 145#64).toNat) (by decide)
              omega
            · simp [hx, valueIsWord] at hev
            · simp [hx, valueIsWord] at hev
        · simp only [if_neg hsz] at hret; simp at hret
  · simp at hret

theorem eps_decode_single_bounded :
    EvmPreservingSpec (fun _ => True)
      (fun s v post => LocFrame s post ∧ ∃ nw : BitVec 64, v = .val (.word nw) ∧ nw.toNat ≤ 255)
      (ofString "decode_single") := by
  obtain ⟨params, body, retShape, hlk, hds⟩ := eps_decode_single
  have hlk_eq := lookup_decode_single.symm.trans hlk
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_eq, rfl⟩
  subst hbody_eq
  refine ⟨_, _, _, lookup_decode_single, ?_⟩
  intro F s hcode hInv hP hlookup hnt
  have hs := hds s hcode hInv hP hlookup hnt
  dsimp only at hs ⊢
  refine ⟨fun v hv => ?_, hs.2⟩
  obtain ⟨h1, h2, h3, hlf⟩ := hs.1 v hv
  exact ⟨h1, h2, h3, hlf, decode_single_body_bounded s v hv⟩

private theorem eval_loadByte_eq {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.loadByte e) =
    match @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with
    | some (.val (.word word)) =>
      Option.map (fun value => ValueHOL.val (.word (BitVec.ofNat 64 value.toNat)))
        (@panMemLoadByteHOL 64 _ s.memory s.memaddrs
          (fun a => Classical.propDecidable (s.memaddrs a)) s.be word)
    | _ => none := by
  simp only [evalHOLExact]
  have hmem : s.toExact.memaddrs = s.memaddrs := rfl
  rcases @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | ⟨⟨w⟩ | _⟩ | _ | _ <;> rfl

theorem code_imm_body_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_code_imm)).1 =
      some (.returned v)) :
    ∃ immw : BitVec 64, v = .val (.word immw) ∧ immw.toNat < 256 := by
  have hbody : sourceFnBody Guest.Software.guestFn_code_imm =
      .dec (ofString "pc") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 0#64]))
        (.seq
          (.ite (.cmp .lower (.op .add [.var .local (ofString "pc"), .const 1#64])
              (.load .one (.op .add [.var .global (ofString "ev"), .const 56#64])))
            (.return (.loadByte (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 48#64]),
              .var .local (ofString "pc"), .const 1#64])))
            .skip)
          (.return (.const 0#64))) := rfl
  rw [hbody, evaluateHOLFiniteState_dec_total] at hret
  dsimp only at hret
  split at hret
  · simp at hret
  · rename_i vpc _
    split at hret
    · dsimp only at hret
      set s1 := setVarHOLFinite (ofString "pc") vpc s
      change (evaluateHOLFiniteState s1
        (.seq
          (.ite (.cmp .lower (.op .add [.var .local (ofString "pc"), .const 1#64])
              (.load .one (.op .add [.var .global (ofString "ev"), .const 56#64])))
            (.return (.loadByte (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 48#64]),
              .var .local (ofString "pc"), .const 1#64])))
            .skip)
          (.return (.const 0#64)))).1 = some (.returned v) at hret
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
      split at hret
      · rename_i cw _
        by_cases hcw0 : cw = 0
        · subst hcw0
          simp only [↓reduceIte, evaluateHOLFiniteState_skip] at hret
          rw [evaluateHOLFiniteState_return] at hret
          dsimp only [evalHOLExact] at hret
          have hsz0 : sizeOfShapeWithContextHOL s1.structs
              (shapeOfHOLExact (.val (.word 0#64))) ≤ 32 := by
            simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
          rw [if_pos hsz0] at hret; dsimp only at hret
          injection hret with h1; injection h1 with hv
          exact ⟨0#64, hv.symm, by decide⟩
        · simp only [hcw0, ↓reduceIte] at hret
          rw [evaluateHOLFiniteState_return] at hret
          rcases hev : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
              (.loadByte (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 48#64]),
                .var .local (ofString "pc"), .const 1#64])) with _ | rv
          · simp [hev] at hret
          · rw [hev] at hret
            by_cases hsz : sizeOfShapeWithContextHOL s1.structs (shapeOfHOLExact rv) ≤ 32
            · simp only [if_pos hsz] at hret
              injection hret with h1; injection h1 with hv
              subst hv
              rw [eval_loadByte_eq] at hev
              rcases haddr : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
                  (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 48#64]),
                    .var .local (ofString "pc"), .const 1#64]) with _ | av
              · rw [haddr] at hev; cases hev
              · rw [haddr] at hev
                rcases av with ⟨⟨addr⟩⟩ | _ | _
                · dsimp only at hev
                  rcases hlb : @panMemLoadByteHOL 64 _ s1.memory s1.memaddrs
                      (fun a => Classical.propDecidable (s1.memaddrs a)) s1.be addr with _ | b
                  · rw [hlb] at hev; cases hev
                  · rw [hlb] at hev; dsimp only [Option.map] at hev
                    injection hev with hv'
                    refine ⟨BitVec.ofNat 64 b.toNat, hv'.symm, ?_⟩
                    have hb_lt : b.toNat < 256 := b.toBitVec.isLt
                    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                    exact hb_lt
                · cases hev
                · cases hev
            · simp only [if_neg hsz] at hret; simp at hret
      · simp at hret
    · simp at hret

theorem eps_code_imm_bounded :
    EvmPreservingSpec (fun _ => True)
      (fun s v post => LocFrame s post ∧ ∃ immw : BitVec 64, v = .val (.word immw) ∧ immw.toNat < 256)
      (ofString "code_imm") := by
  obtain ⟨params, body, retShape, hlk, hci⟩ := eps_code_imm
  have hlk_eq := lookup_code_imm.symm.trans hlk
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_eq, rfl⟩
  subst hbody_eq
  refine ⟨_, _, _, lookup_code_imm, ?_⟩
  intro F s hcode hInv hP hlookup hnt
  have hs := hci s hcode hInv hP hlookup hnt
  dsimp only at hs ⊢
  refine ⟨fun v hv => ?_, hs.2⟩
  obtain ⟨h1, h2, h3, hlf⟩ := hs.1 v hv
  exact ⟨h1, h2, h3, hlf, code_imm_body_bounded s v hv⟩

private theorem eval_cmp_eq {F : Type} (t : PanSemStateFiniteExact 64 F)
    (op : Cmp) (e1 e2 : ExpHOL 64) :
    @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) (.cmp op e1 e2) =
    match @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e1,
          @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e2 with
    | some (.val (.word lw)), some (.val (.word rw)) =>
      some (.val (.word (if Compiler.Encoders.Asm.wordCmpHOL op lw rw then 1#64 else 0#64)))
    | _, _ => none := by
  simp only [evalHOLExact]
  rcases @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e1 with _ | ⟨⟨w1⟩ | _⟩ | _ | _ <;>
  rcases @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e2 with _ | ⟨⟨w2⟩ | _⟩ | _ | _ <;>
  rfl

private theorem eval_notLower_var_loadG_eq_zero {F : Type}
    (t : PanSemStateFiniteExact 64 F) (nm : MlS) (g : String) (off : BitVec 64)
    (hw : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.cmp .notLower (.var .local nm)
        (.load .one (.op .add [.var .global (ofString g), .const off]))) =
      some (.val (.word 0#64))) :
    ∃ xw : BitVec 64, t.locals.lookup nm = some (.val (.word xw)) ∧
      xw.toNat < memW t (globN t g + off.toNat) := by
  rw [eval_cmp_eq] at hw
  have hvar : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.var .local nm) = t.locals.lookup nm := rfl
  rw [hvar] at hw
  rcases hr : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.load .one (.op .add [.var .global (ofString g), .const off])) with _ | rv
  · rw [hr] at hw
    rcases hl : t.locals.lookup nm with _ | lv
    · rw [hl] at hw; cases hw
    · rw [hl] at hw
      rcases lv with ⟨⟨_⟩ | _⟩ | _ | _ <;> cases hw
  · obtain ⟨spw, rfl, hsp_nat⟩ := evalAt_loadG_word t g off rv hr
    rw [hr] at hw
    rcases hl : t.locals.lookup nm with _ | lv
    · rw [hl] at hw; cases hw
    · rw [hl] at hw
      rcases lv with ⟨⟨xw⟩⟩ | _ | _
      · dsimp only at hw
        simp only [Compiler.Encoders.Asm.wordCmpHOL] at hw
        by_cases hle : spw ≤ xw
        · simp [hle] at hw
        · rw [BitVec.le_def] at hle
          exact ⟨xw, rfl, by omega⟩
      · cases hw
      · cases hw

private theorem eval_lower_loadG_add1_eq_zero {F : Type}
    (t : PanSemStateFiniteExact 64 F) (g : String) (off : BitVec 64) (nm : MlS)
    {xw : BitVec 64} (hx : t.locals.lookup nm = some (.val (.word xw))) (hx_le : xw.toNat ≤ 255)
    (hw : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.cmp .lower (.load .one (.op .add [.var .global (ofString g), .const off]))
        (.op .add [.var .local nm, .const 1#64])) =
      some (.val (.word 0#64))) :
    xw.toNat < memW t (globN t g + off.toNat) := by
  have hadd_ev : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.op .add [.var .local nm, .const 1#64]) = some (.val (.word (xw + 1#64))) := by
    simp [evalHOLExact, evalListHOLExact, hx, valueIsWord, valueWord, wordOpHOL, wordOp]
  rw [eval_cmp_eq, hadd_ev] at hw
  rcases hld : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.load .one (.op .add [.var .global (ofString g), .const off])) with _ | lv
  · rw [hld] at hw; cases hw
  · obtain ⟨spw, rfl, hsp_nat⟩ := evalAt_loadG_word t g off lv hld
    rw [hld] at hw; dsimp only at hw
    simp only [Compiler.Encoders.Asm.wordCmpHOL] at hw
    by_cases hlt : spw < xw + 1#64
    · simp [hlt] at hw
    · rw [BitVec.lt_def, BitVec.toNat_add] at hlt
      have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
      rw [h1, Nat.mod_eq_of_lt (by omega)] at hlt
      omega

private theorem seq_call_stack_swap {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {arg1 arg2 : ExpHOL 64} {cont : ProgHOL 64}
    (hargs_ok : ∀ t (w1 w2 : BitVec 64),
      EvmInv t → P t →
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) arg1 =
        some (.val (.word w1)) →
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) arg2 =
        some (.val (.word w2)) →
      w1.toNat < memW t (globN t "ev" + 16) ∧ w2.toNat < memW t (globN t "ev" + 16))
    (hcont : HandlerRun s0 (fun _ => True) charged cont) :
    HandlerRun s0 P charged
      (.seq (.call (some (none, none)) (ofString "stack_swap_positions") [arg1, arg2]) cont) := by
  refine HandlerRun.seq_call eps_stack_swap_positions ?_ (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) hcont
  intro t values body' callee ret' hc hInv hP hargs hl
  have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "stack_swap_positions") values =
      some (body', callee, ret') := by rwa [← hc]
  obtain ⟨_, _, w1, w2, rfl, hw1_cal, hw2_cal⟩ :=
    two_word_arg_lookup (by decide) lookup_stack_swap_positions hl_orig
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact] at hargs
  rcases he1 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) arg1 with _ | u1
  · simp [he1] at hargs
  · rcases he2 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) arg2 with _ | u2
    · simp [he1, he2] at hargs
    · simp only [he1, he2, Option.some.injEq, List.cons.injEq, and_true] at hargs
      rcases hargs with ⟨rfl, rfl⟩
      obtain ⟨h1_lt, h2_lt⟩ := hargs_ok t w1 w2 hInv hP he1 he2
      exact ⟨w1, w2, hw1_cal, hw2_cal, h1_lt, h2_lt⟩

/-! ## 3. Duplicate, swap, and exchange -/

theorem op_dup_spec : OpHandlerSpec (ofString "op_dup") := by
  refine opHandlerSpec_of_run 515 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_dup rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_dup, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  exact
    HandlerRun.seq_charge_gas_const (by decide)
      (HandlerRun.dec_simple
        (HandlerRun.seq_ite_raise_skip (fun _ _ _ _ => trivial)
          (HandlerRun.dec_simple
            (HandlerRun.seq_call_simple eps_stack_push
              (HandlerRun.seq_call_simple eps_pc_add
                (HandlerRun.ret _))))))

theorem op_swap_spec : OpHandlerSpec (ofString "op_swap") := by
  refine opHandlerSpec_of_run 517 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_swap rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_swap, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRun.seq_charge_gas_const (by decide) ?_
  refine HandlerRun.seq_ite_raise_skip
    (Q := fun t => ∃ itemw : BitVec 64,
      t.locals.lookup (ofString "item") = some (.val (.word itemw)) ∧
      itemw.toNat < memW t (globN t "ev" + 16))
    (fun t hw _ _ => by
      obtain ⟨itemw, hitem, hlt⟩ := eval_notLower_var_loadG_eq_zero t (ofString "item") "ev" 16#64 hw
      exact ⟨itemw, hitem, hlt⟩)
    ?_
  refine seq_call_stack_swap
    (fun t w1 w2 _ ⟨itemw, hitem, hlt⟩ he1 he2 => by
      simp only [evalHOLExact] at he1
      injection he1 with h1; injection h1 with h2; injection h2 with h3; subst h3
      change t.locals.lookup (ofString "item") = some (.val (.word w2)) at he2
      rw [hitem] at he2; injection he2 with h1; injection h1 with h2; injection h2 with h3; subst h3
      have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
      exact ⟨by omega, hlt⟩)
    (HandlerRun.seq_call_simple eps_pc_add (HandlerRun.ret _))

theorem op_dupn_spec : OpHandlerSpec (ofString "op_dupn") := by
  refine opHandlerSpec_of_run 520 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_dupn rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_dupn, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  exact
    HandlerRun.seq_charge_gas_const (by decide)
      (HandlerRun.decCall_simple eps_code_imm
        (HandlerRun.decCall_simple eps_decode_single
          (HandlerRun.seq_ite_raise_skip (fun _ _ _ _ => trivial)
            (HandlerRun.dec_simple
              (HandlerRun.dec_simple
                (HandlerRun.seq_call_simple eps_stack_push
                  (HandlerRun.seq_call_simple eps_pc_add
                    (HandlerRun.ret _))))))))

theorem op_swapn_spec : OpHandlerSpec (ofString "op_swapn") := by
  refine opHandlerSpec_of_run 521 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_swapn rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_swapn, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRun.seq_charge_gas_const (by decide) ?_
  refine HandlerRun.decCall (Q := fun _ => True) eps_code_imm
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) ?_
  refine HandlerRun.decCall
    (Q := fun t => ∃ nw : BitVec 64,
      t.locals.lookup (ofString "n") = some (.val (.word nw)) ∧ nw.toNat ≤ 255)
    eps_decode_single_bounded
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ _ _ v cpost _ _ _ _ _ _ ⟨_, nw, hv, hnw_le⟩ => by
      subst hv
      exact ⟨nw, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], hnw_le⟩)
    ?_
  refine HandlerRun.seq_ite_raise_skip
    (Q := fun t => ∃ nw : BitVec 64,
      t.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
      nw.toNat < memW t (globN t "ev" + 16))
    (fun t hw _ ⟨nw, hnw, hnw_le⟩ =>
      ⟨nw, hnw, eval_lower_loadG_add1_eq_zero t "ev" 16#64 (ofString "n") hnw hnw_le hw⟩)
    ?_
  refine seq_call_stack_swap
    (fun t w1 w2 _ ⟨nw, hnw, hlt⟩ he1 he2 => by
      simp only [evalHOLExact] at he1
      injection he1 with h1; injection h1 with h2; injection h2 with h3; subst h3
      change t.locals.lookup (ofString "n") = some (.val (.word w2)) at he2
      rw [hnw] at he2; injection he2 with h1; injection h1 with h2; injection h2 with h3; subst h3
      have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
      exact ⟨by omega, hlt⟩)
    (HandlerRun.seq_call_simple eps_pc_add (HandlerRun.ret _))

private theorem op_exchange_tail {F : Type} (s0 : PanSemStateFiniteExact 64 F) :
    HandlerRun s0
      (fun t => ∃ nw mw : BitVec 64,
        t.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
        t.locals.lookup (ofString "m") = some (.val (.word mw)) ∧
        nw.toNat ≤ 255 ∧ mw.toNat ≤ 255)
      true
      (.decCall (ofString "mx") .one (ofString "max")
        [.var .local (ofString "n"), .var .local (ofString "m")]
        (.seq
          (.ite (.cmp .lower
              (.load .one (.op .add [.var .global (ofString "ev"), .const 16#64]))
              (.op .add [.var .local (ofString "mx"), .const 1#64]))
            (.raise (ofString "EvmErr") (.const 2#64))
            .skip)
          (.seq
            (.call (some (none, none)) (ofString "stack_swap_positions")
              [.var .local (ofString "n"), .var .local (ofString "m")])
            (.seq
              (.call (some (none, none)) (ofString "pc_add") [.const 2#64])
              (.return (.const 0#64)))))) := by
  refine HandlerRun.decCall
    (Q := fun t => ∃ nw mw mxw : BitVec 64,
      t.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
      t.locals.lookup (ofString "m") = some (.val (.word mw)) ∧
      t.locals.lookup (ofString "mx") = some (.val (.word mxw)) ∧
      mxw.toNat = Nat.max nw.toNat mw.toNat ∧ mxw.toNat ≤ 255)
    eps_max
    (fun t values b_m callee rs_m hc _ ⟨nw, mw, hn, hm, _, _⟩ hargs hl => by
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "max") values =
          some (b_m, callee, rs_m) := by rwa [← hc]
      obtain ⟨_, _, w1, w2, _, hw1, hw2⟩ := two_word_arg_lookup (by decide) lookup_max hl_orig
      exact ⟨w1, w2, hw1, hw2⟩)
    (fun t values b_m callee rs_m v cpost _ ⟨nw, mw, hn, hm, hn_le, hm_le⟩ hargs hl_orig _ _ ⟨_, hmax⟩ => by
      have hev_args : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.var .local (ofString "n"), .var .local (ofString "m")] =
          some [.val (.word nw), .val (.word mw)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hn, hm]
      rw [hev_args] at hargs; injection hargs with hvs; subst hvs
      obtain ⟨_, _, w1, w2, hvs_eq, hw1, hw2⟩ := two_word_arg_lookup (by decide) lookup_max hl_orig
      simp only [List.cons.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq, and_true] at hvs_eq
      rcases hvs_eq with ⟨rfl, rfl⟩
      obtain ⟨mxw, rfl, hmx_nat⟩ := hmax nw mw hw1 hw2
      have hmx_le : mxw.toNat ≤ 255 := by
        rw [hmx_nat]; exact Nat.max_le.2 ⟨hn_le, hm_le⟩
      refine ⟨nw, mw, mxw, ?_, ?_, ?_, hmx_nat, hmx_le⟩
      · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
          show ofString "mx" ≠ ofString "n" by decide]
      · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm,
          show ofString "mx" ≠ ofString "m" by decide]
      · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    ?_
  refine HandlerRun.seq_ite_raise_skip
    (Q := fun t => ∃ nw mw : BitVec 64,
      t.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
      t.locals.lookup (ofString "m") = some (.val (.word mw)) ∧
      nw.toNat < memW t (globN t "ev" + 16) ∧
      mw.toNat < memW t (globN t "ev" + 16))
    (fun t hw _ ⟨nw, mw, mxw, hn, hm, hmx, hmx_nat, hmx_le⟩ => by
      have hlt := eval_lower_loadG_add1_eq_zero t "ev" 16#64 (ofString "mx") hmx hmx_le hw
      have h16 : (16#64 : BitVec 64).toNat = 16 := rfl
      rw [h16] at hlt
      have hn_le_mx : nw.toNat ≤ mxw.toNat := by rw [hmx_nat]; exact Nat.le_max_left _ _
      have hm_le_mx : mw.toNat ≤ mxw.toNat := by rw [hmx_nat]; exact Nat.le_max_right _ _
      exact ⟨nw, mw, hn, hm, by omega, by omega⟩)
    ?_
  refine seq_call_stack_swap
    (fun t w1 w2 _ ⟨nw, mw, hn, hm, hn_lt, hm_lt⟩ he1 he2 => by
      change t.locals.lookup (ofString "n") = some (.val (.word w1)) at he1
      change t.locals.lookup (ofString "m") = some (.val (.word w2)) at he2
      rw [hn] at he1; injection he1 with h1; injection h1 with h2; injection h2 with h3; subst h3
      rw [hm] at he2; injection he2 with h1; injection h1 with h2; injection h2 with h3; subst h3
      exact ⟨hn_lt, hm_lt⟩)
    (HandlerRun.seq_call_simple eps_pc_add (HandlerRun.ret _))

private theorem eval_seq_seq {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p1 p2 p3 : ProgHOL 64) :
    evaluateHOLFiniteState s (.seq (.seq p1 p2) p3) =
    evaluateHOLFiniteState s (.seq p1 (.seq p2 p3)) := by
  simp only [evaluateHOLFiniteState_seq_line780]
  rcases h1 : evaluateHOLFiniteState s p1 with ⟨r1, s1⟩
  cases r1 <;> rfl

theorem op_exchange_spec : OpHandlerSpec (ofString "op_exchange") := by
  refine opHandlerSpec_of_run 522 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_exchange rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_exchange, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRun.seq_charge_gas_const (by decide) ?_
  refine HandlerRun.decCall
    (Q := fun t => ∃ immw : BitVec 64,
      t.locals.lookup (ofString "imm") = some (.val (.word immw)) ∧ immw.toNat < 256)
    eps_code_imm_bounded
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ v _ _ _ _ _ _ _ ⟨_, immw, hv, himm_lt⟩ => by
      subst hv
      exact ⟨immw, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], himm_lt⟩)
    ?_
  refine HandlerRun.seq_ite_raise_skip
    (Q := fun t => ∃ immw : BitVec 64,
      t.locals.lookup (ofString "imm") = some (.val (.word immw)) ∧ immw.toNat < 256)
    (fun _ _ _ hP => hP)
    ?_
  refine HandlerRun.dec
    (Q := fun t => ∃ kw : BitVec 64,
      t.locals.lookup (ofString "k") = some (.val (.word kw)) ∧ kw.toNat < 256)
    (fun t v hv _ ⟨immw, himm, himm_lt⟩ => by
      have hev : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.op .xor [.var .local (ofString "imm"), .const 143#64]) =
          some (.val (.word (immw ^^^ 143#64))) := by
        simp [evalHOLExact, evalListHOLExact, himm, valueIsWord, valueWord, wordOpHOL, wordOp]
      rw [hev] at hv; injection hv with hv'; subst hv'
      refine ⟨immw ^^^ 143#64, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], ?_⟩
      rw [BitVec.toNat_xor]
      have h143 : (143#64 : BitVec 64).toNat = 143 := rfl
      rw [h143]
      exact Nat.xor_lt_two_pow (n := 8) himm_lt (by decide))
    ?_
  refine HandlerRun.dec
    (Q := fun t => ∃ kw qw : BitVec 64,
      t.locals.lookup (ofString "k") = some (.val (.word kw)) ∧
      t.locals.lookup (ofString "q") = some (.val (.word qw)) ∧
      kw.toNat < 256 ∧ qw.toNat < 16)
    (fun t v hv _ ⟨kw, hk, hk_lt⟩ => by
      have h4 : (4#64 : BitVec 64).toNat = 4 := rfl
      have hev : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.shift .lsr (.var .local (ofString "k")) (.const 4#64)) =
          some (.val (.word (kw >>> (4 : Nat)))) := by
        simp [evalHOLExact, hk, wordShiftHOL, h4]
      rw [hev] at hv; injection hv with hv'; subst hv'
      refine ⟨kw, kw >>> (4 : Nat),
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hk,
          show ofString "q" ≠ ofString "k" by decide],
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
        hk_lt, ?_⟩
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      have : (2 ^ 4 : Nat) = 16 := rfl
      omega)
    ?_
  refine HandlerRun.dec
    (Q := fun t => ∃ qw rw : BitVec 64,
      t.locals.lookup (ofString "q") = some (.val (.word qw)) ∧
      t.locals.lookup (ofString "r") = some (.val (.word rw)) ∧
      qw.toNat < 16 ∧ rw.toNat < 16)
    (fun t v hv _ ⟨kw, qw, hk, hq, _, hq_lt⟩ => by
      have hev : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.op .and [.var .local (ofString "k"), .const 15#64]) =
          some (.val (.word (kw &&& 15#64))) := by
        simp [evalHOLExact, evalListHOLExact, hk, valueIsWord, valueWord, wordOpHOL, wordOp]
      rw [hev] at hv; injection hv with hv'; subst hv'
      refine ⟨qw, kw &&& 15#64,
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hq,
          show ofString "r" ≠ ofString "q" by decide],
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
        hq_lt, ?_⟩
      rw [BitVec.toNat_and]
      have h15 : (15#64 : BitVec 64).toNat = 15 := rfl
      rw [h15]
      exact Nat.and_lt_two_pow (n := 4) (x := kw.toNat) (by decide))
    ?_
  refine HandlerRun.dec
    (Q := fun t => ∃ qw rw : BitVec 64,
      t.locals.lookup (ofString "q") = some (.val (.word qw)) ∧
      t.locals.lookup (ofString "r") = some (.val (.word rw)) ∧
      qw.toNat < 16 ∧ rw.toNat < 16)
    (fun t v hv _ ⟨qw, rw, hq, hr, hq_lt, hr_lt⟩ =>
      ⟨qw, rw,
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hq,
          show ofString "n" ≠ ofString "q" by decide],
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hr,
          show ofString "n" ≠ ofString "r" by decide],
        hq_lt, hr_lt⟩)
    ?_
  refine HandlerRun.dec
    (Q := fun t => ∃ qw rw : BitVec 64,
      t.locals.lookup (ofString "q") = some (.val (.word qw)) ∧
      t.locals.lookup (ofString "r") = some (.val (.word rw)) ∧
      qw.toNat < 16 ∧ rw.toNat < 16)
    (fun t v hv _ ⟨qw, rw, hq, hr, hq_lt, hr_lt⟩ =>
      ⟨qw, rw,
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hq,
          show ofString "m" ≠ ofString "q" by decide],
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hr,
          show ofString "m" ≠ ofString "r" by decide],
        hq_lt, hr_lt⟩)
    ?_
  intro t hc hInv hlen hR ⟨qw, rw, hq, hr, hq_lt, hr_lt⟩ hnt
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
  have hcmp : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.cmp .lower (.var .local (ofString "q")) (.var .local (ofString "r"))) =
      some (.val (.word (if qw < rw then 1#64 else 0#64))) := by
    simp [evalHOLExact, hq, hr, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp] at hnt ⊢; dsimp only at hnt ⊢
  by_cases hqr : qw < rw
  · have h10 : ¬ ((1#64 : BitVec 64) = 0) := by decide
    simp only [hqr, ↓reduceIte, h10] at hnt ⊢
    rw [← evaluateHOLFiniteState_seq_line780, eval_seq_seq] at hnt ⊢
    refine (HandlerRun.seq_assign_local
      (P := fun u => ∃ qw rw : BitVec 64,
        u.locals.lookup (ofString "q") = some (.val (.word qw)) ∧
        u.locals.lookup (ofString "r") = some (.val (.word rw)) ∧
        qw.toNat < 16 ∧ rw.toNat < 16)
      (Q := fun u => ∃ nw rw : BitVec 64,
        u.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
        u.locals.lookup (ofString "r") = some (.val (.word rw)) ∧
        nw.toNat ≤ 255 ∧ rw.toNat < 16)
      (fun u v hv _ ⟨qw, rw, hq, hr, hq_lt, hr_lt⟩ => by
        have hev : @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
            (.op .add [.var .local (ofString "q"), .const 1#64]) =
            some (.val (.word (qw + 1#64))) := by
          simp [evalHOLExact, evalListHOLExact, hq, valueIsWord, valueWord, wordOpHOL, wordOp]
        rw [hev] at hv; injection hv with hv'; subst hv'
        refine ⟨qw + 1#64, rw,
          by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
          by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hr,
            show ofString "n" ≠ ofString "r" by decide],
          ?_, hr_lt⟩
        rw [BitVec.toNat_add]
        have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
        rw [h1, Nat.mod_eq_of_lt (by omega)]; omega)
      (HandlerRun.seq_assign_local
        (Q := fun u => ∃ nw mw : BitVec 64,
          u.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
          u.locals.lookup (ofString "m") = some (.val (.word mw)) ∧
          nw.toNat ≤ 255 ∧ mw.toNat ≤ 255)
        (fun u v hv _ ⟨nw, rw, hn, hr, hn_le, hr_lt⟩ => by
          have hev : @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
              (.op .add [.var .local (ofString "r"), .const 1#64]) =
              some (.val (.word (rw + 1#64))) := by
            simp [evalHOLExact, evalListHOLExact, hr, valueIsWord, valueWord, wordOpHOL, wordOp]
          rw [hev] at hv; injection hv with hv'; subst hv'
          refine ⟨nw, rw + 1#64,
            by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
              show ofString "m" ≠ ofString "n" by decide],
            by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
            hn_le, ?_⟩
          rw [BitVec.toNat_add]
          have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
          rw [h1, Nat.mod_eq_of_lt (by omega)]; omega)
        (op_exchange_tail s0))) t hc hInv hlen hR ⟨qw, rw, hq, hr, hq_lt, hr_lt⟩ hnt
  · have h00 : (0#64 : BitVec 64) = 0 := rfl
    simp only [hqr, h00, ↓reduceIte] at hnt ⊢
    rw [← evaluateHOLFiniteState_seq_line780, eval_seq_seq] at hnt ⊢
    refine (HandlerRun.seq_assign_local
      (P := fun u => ∃ qw rw : BitVec 64,
        u.locals.lookup (ofString "q") = some (.val (.word qw)) ∧
        u.locals.lookup (ofString "r") = some (.val (.word rw)) ∧
        qw.toNat < 16 ∧ rw.toNat < 16)
      (Q := fun u => ∃ nw qw : BitVec 64,
        u.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
        u.locals.lookup (ofString "q") = some (.val (.word qw)) ∧
        nw.toNat ≤ 255 ∧ qw.toNat < 16)
      (fun u v hv _ ⟨qw, rw, hq, hr, hq_lt, hr_lt⟩ => by
        have hev : @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
            (.op .add [.var .local (ofString "r"), .const 1#64]) =
            some (.val (.word (rw + 1#64))) := by
          simp [evalHOLExact, evalListHOLExact, hr, valueIsWord, valueWord, wordOpHOL, wordOp]
        rw [hev] at hv; injection hv with hv'; subst hv'
        refine ⟨rw + 1#64, qw,
          by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
          by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hq,
            show ofString "n" ≠ ofString "q" by decide],
          ?_, hq_lt⟩
        rw [BitVec.toNat_add]
        have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
        rw [h1, Nat.mod_eq_of_lt (by omega)]; omega)
      (HandlerRun.seq_assign_local
        (Q := fun u => ∃ nw mw : BitVec 64,
          u.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
          u.locals.lookup (ofString "m") = some (.val (.word mw)) ∧
          nw.toNat ≤ 255 ∧ mw.toNat ≤ 255)
        (fun u v hv _ ⟨nw, qw, hn, hq, hn_le, hq_lt⟩ => by
          have hev : @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
              (.op .sub [.const 29#64, .var .local (ofString "q")]) =
              some (.val (.word (29#64 - qw))) := by
            simp [evalHOLExact, evalListHOLExact, hq, valueIsWord, valueWord, wordOpHOL, wordOp]
          rw [hev] at hv; injection hv with hv'; subst hv'
          refine ⟨nw, 29#64 - qw,
            by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
              show ofString "m" ≠ ofString "n" by decide],
            by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
            hn_le, ?_⟩
          have h29 : (29#64 : BitVec 64).toNat = 29 := rfl
          rw [BitVec.toNat_sub_of_le (BitVec.le_def.2 (by omega)), h29]
          omega)
        (op_exchange_tail s0))) t hc hInv hlen hR ⟨qw, rw, hq, hr, hq_lt, hr_lt⟩ hnt

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
