import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.Common
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.ReadOnly
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group06ControlFlow

/-! # State Gas & Combinator Helpers for `OpHandlersB`

Proves:
- `eps_min_le`, `eps_max`, `eps_check_gas`, `eps_memeq_ro`, `eps_htab_has_ro`,
  `eps_u256_eq_ro`, `eps_u256_is_zero_ro`, `eps_u256_from_be_ro`, `eps_acct_is_empty_ro`,
  `eps_is_warm_address_ro`
- `eps_charge_gas_any`, `eps_charge_state_gas`, `eps_credit_state_gas_refund`
- `HandlerRun.seq_assoc`, `HandlerRun.seq_decCall_call`, `HandlerRun.seq_ite_unit`,
  `HandlerRun.seq_call_assign_local`, `HandlerRun.seq_call_assign_local_simple`
-/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB

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

/-! ## 1. Pure read-only & gas/state-gas helper specs -/

theorem lookup_min_b :
    originalRuntimeCode.lookup (ofString "min") =
      some ([(ofString "a", .one), (ofString "b", .one)],
        sourceFnBody Guest.Software.guestFn_min, .one) :=
  lookup_of_guestAst_getElem 31 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_min) rfl

theorem lookup_max_b :
    originalRuntimeCode.lookup (ofString "max") =
      some ([(ofString "a", .one), (ofString "b", .one)],
        sourceFnBody Guest.Software.guestFn_max, .one) :=
  lookup_of_guestAst_getElem 32 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_max) rfl

theorem lookup_check_gas_b :
    originalRuntimeCode.lookup (ofString "check_gas") =
      some ([(ofString "amount", .one)],
        sourceFnBody Guest.Software.guestFn_check_gas, .one) :=
  lookup_of_guestAst_getElem 447 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_check_gas) rfl

theorem lookup_charge_state_gas_b :
    originalRuntimeCode.lookup (ofString "charge_state_gas") =
      some ([(ofString "amount", .one)],
        sourceFnBody Guest.Software.guestFn_charge_state_gas, .one) :=
  lookup_of_guestAst_getElem 449 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_charge_state_gas) rfl

theorem lookup_credit_state_gas_refund_b :
    originalRuntimeCode.lookup (ofString "credit_state_gas_refund") =
      some ([(ofString "amount", .one)],
        sourceFnBody Guest.Software.guestFn_credit_state_gas_refund, .one) :=
  lookup_of_guestAst_getElem 450 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_credit_state_gas_refund) rfl

theorem min_body_exact {F : Type} (s : PanSemStateFiniteExact 64 F) {aw bw : BitVec 64}
    (ha : s.locals.lookup (ofString "a") = some (.val (.word aw)))
    (hb : s.locals.lookup (ofString "b") = some (.val (.word bw)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_min)).1 =
      some (.returned v)) :
    ∃ rw : BitVec 64, v = .val (.word rw) ∧ rw.toNat ≤ aw.toNat ∧ rw.toNat ≤ bw.toNat := by
  have hbody : sourceFnBody Guest.Software.guestFn_min =
      .seq
        (.ite (.cmp .lower (.var .local (ofString "a")) (.var .local (ofString "b")))
          (.return (.var .local (ofString "a")))
          .skip)
        (.return (.var .local (ofString "b"))) := rfl
  rw [hbody, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
  have hcmp : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
      (.cmp .lower (.var .local (ofString "a")) (.var .local (ofString "b"))) =
      some (.val (.word (if aw < bw then 1 else 0))) := by
    simp [evalHOLExact, ha, hb, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp] at hret; dsimp only at hret
  by_cases hlt : aw < bw
  · have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    simp only [hlt, ↓reduceIte, h10] at hret
    rw [evaluateHOLFiniteState_return] at hret
    have heva : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
        (.var .local (ofString "a")) = some (.val (.word aw)) := ha
    rw [heva] at hret; dsimp only at hret
    have hsz : sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact (.val (.word aw) : ValueHOL 64)) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [if_pos hsz] at hret; dsimp only at hret
    injection hret with h1; injection h1 with hv
    refine ⟨aw, hv.symm, le_rfl, ?_⟩
    rw [BitVec.lt_def] at hlt; omega
  · simp only [hlt, ↓reduceIte, evaluateHOLFiniteState_skip] at hret
    rw [evaluateHOLFiniteState_return] at hret
    have hevb : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
        (.var .local (ofString "b")) = some (.val (.word bw)) := hb
    rw [hevb] at hret; dsimp only at hret
    have hsz : sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact (.val (.word bw) : ValueHOL 64)) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [if_pos hsz] at hret; dsimp only at hret
    injection hret with h1; injection h1 with hv
    refine ⟨bw, hv.symm, ?_, le_rfl⟩
    rw [BitVec.lt_def] at hlt; omega

theorem eps_min_le :
    EvmPreservingSpec (fun _ => True)
      (fun s v post => LocFrame s post ∧
        ∀ aw bw : BitVec 64,
          s.locals.lookup (ofString "a") = some (.val (.word aw)) →
          s.locals.lookup (ofString "b") = some (.val (.word bw)) →
          ∃ rw : BitVec 64, v = .val (.word rw) ∧ rw.toNat ≤ aw.toNat ∧ rw.toNat ≤ bw.toNat)
      (ofString "min") := by
  obtain ⟨params, body, retShape, hlk, hro⟩ :=
    eps_of_readOnly 31 (by rw [guestAst_len]; decide) Guest.Software.guestFn_min rfl
      opRoCallees opRoCallees_good rfl
  have hlk_eq := lookup_min_b.symm.trans hlk
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_eq, rfl⟩
  subst hbody_eq
  refine ⟨_, _, _, lookup_min_b, ?_⟩
  intro F s hcode hInv hP hlookup hnt
  have hs := hro s hcode hInv hP hlookup hnt
  dsimp only at hs ⊢
  refine ⟨fun v hv => ?_, hs.2⟩
  obtain ⟨h1, h2, h3, hlf⟩ := hs.1 v hv
  exact ⟨h1, h2, h3, hlf, fun aw bw ha hb => min_body_exact s ha hb v hv⟩

theorem eps_max :
    EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "max") :=
  eps_of_readOnly 32 (by rw [guestAst_len]; decide) Guest.Software.guestFn_max rfl
    opRoCallees opRoCallees_good rfl

theorem eps_check_gas :
    EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "check_gas") :=
  eps_of_readOnly 447 (by rw [guestAst_len]; decide) Guest.Software.guestFn_check_gas rfl
    opRoCallees opRoCallees_good rfl

theorem eps_memeq_ro :
    EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "memeq") :=
  eps_of_readOnly 18 (by rw [guestAst_len]; decide) Guest.Software.guestFn_memeq rfl
    opRoCallees opRoCallees_good rfl

theorem eps_htab_has_ro :
    EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "htab_has") :=
  eps_of_readOnly 133 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htab_has rfl
    opRoCallees opRoCallees_good rfl

theorem eps_u256_eq_ro :
    EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "u256_eq") :=
  eps_of_readOnly 45 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_eq rfl
    opRoCallees opRoCallees_good rfl

theorem eps_u256_is_zero_ro :
    EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "u256_is_zero") :=
  eps_of_readOnly 42 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_is_zero rfl
    opRoCallees opRoCallees_good rfl

theorem eps_u256_from_be_ro :
    EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "u256_from_be") :=
  eps_of_readOnly 86 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_from_be rfl
    opRoCallees opRoCallees_good rfl

theorem eps_acct_is_empty_ro :
    EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "acct_is_empty") :=
  eps_of_readOnly 384 (by rw [guestAst_len]; decide) Guest.Software.guestFn_acct_is_empty rfl
    opRoCallees opRoCallees_good rfl

theorem eps_is_warm_address_ro :
    EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "is_warm_address") :=
  eps_of_readOnly 471 (by rw [guestAst_len]; decide) Guest.Software.guestFn_is_warm_address rfl
    opRoCallees opRoCallees_good rfl

/-! ## 2. Non-strict `eps_charge_gas_any`, `eps_charge_state_gas`, and `eps_credit_state_gas_refund` -/

theorem eps_charge_gas_any :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => post.globals = s.globals)
      (ofString "charge_gas") := by
  refine ⟨_, _, _, M21.lookup_charge_gas, ?_⟩
  intro F s _ hInv _ ⟨vals, hl⟩ _
  have hlen1 : ∃ v0, vals = [v0] := by
    have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
      originalRuntimeCode.lookup (ofString "charge_gas") vals _ _ _ hl
    simp only [Flapjack.lookupCodeHOLExact, M21.lookup_charge_gas] at hx
    rcases vals with _ | ⟨v0, _ | _⟩ <;> simp at hx
    exact ⟨v0, rfl⟩
  obtain ⟨v0, rfl⟩ := hlen1
  obtain ⟨_, _, amtw, rfl, hamt⟩ := one_word_arg_lookup M21.lookup_charge_gas hl
  have hcg := charge_gas_body_exact s hInv hamt
  dsimp only at hcg ⊢
  refine ⟨fun v hv => ?_, fun herr => ?_⟩
  · obtain ⟨hI, hg, hch, hR⟩ := hcg.1 v hv
    exact ⟨hI, hch, by change _ + _ = _ at hR; omega, hg⟩
  · obtain ⟨hI, _, hch, hR⟩ := hcg.2 herr
    exact ⟨hI, hch, le_of_eq hR⟩

private theorem store_some_eq_error_sg {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {dst val : ExpHOL 64} {res : PanSemResultExact 64}
    (h : evaluateHOLFiniteState s (.store dst val) = (some res, post)) :
    res = .error := by
  rw [evaluateHOLFiniteState_store] at h
  revert h
  rcases @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst with _ | dv
  · intro h; injection h with h1; injection h1 with h2; exact h2.symm
  · rcases dv with ⟨⟨addr⟩⟩ | _ | _
    · rcases @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val with _ | v
      · intro h; injection h with h1; injection h1 with h2; exact h2.symm
      · dsimp only
        split
        · intro h; injection h with h1; cases h1
        · intro h; injection h with h1; injection h1 with h2; exact h2.symm
    · intro h; injection h with h1; injection h1 with h2; exact h2.symm
    · intro h; injection h with h1; injection h1 with h2; exact h2.symm

private theorem add_sat_body_le_sum {F : Type} (s : PanSemStateFiniteExact 64 F) (aw bw : BitVec 64)
    (ha : s.locals.lookup (ofString "a") = some (.val (.word aw)))
    (hb : s.locals.lookup (ofString "b") = some (.val (.word bw)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_add_sat)).1 =
      some (.returned v)) :
    ∃ rw : BitVec 64, v = .val (.word rw) ∧ rw.toNat ≤ aw.toNat + bw.toNat := by
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
    simp [evalHOLExact, hs1_s, hs1_a, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp] at hret; dsimp only at hret
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
    have haw := aw.isLt
    have hbw := bw.isLt
    have : (18446744073709551615#64 : BitVec 64).toNat = 18446744073709551615 := rfl
    omega
  · simp only [hlt, ↓reduceIte, evaluateHOLFiniteState_skip] at hret
    rw [evaluateHOLFiniteState_return] at hret
    have hev_s : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
        (.var .local (ofString "s")) = some (.val (.word (aw + bw))) := hs1_s
    rw [hev_s] at hret; dsimp only at hret
    split at hret
    · injection hret with h1; injection h1 with hv
      refine ⟨aw + bw, hv.symm, ?_⟩
      rw [BitVec.toNat_add]; exact Nat.mod_le _ _
    · simp at hret

theorem eps_charge_state_gas :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => post.globals = s.globals)
      (ofString "charge_state_gas") := by
  refine ⟨_, _, _, lookup_charge_state_gas_b, ?_⟩
  intro F s hcode hInv _ ⟨vals, hl⟩ hnt
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
  have hno_ret_err {r0 : Option (PanSemResultExact 64)} {P1 P2 : Prop}
      (h1 : ∀ v, r0 ≠ some (.returned v)) (h2 : ¬ IsEvmErr r0) :
      (∀ v, r0 = some (.returned v) → P1) ∧ (IsEvmErr r0 → P2) :=
    ⟨fun v hv => (h1 v hv).elim, fun he => (h2 he).elim⟩
  have herr_triv {P1 P2 : Prop} :
      (∀ v, (some PanSemResultExact.error : Option (PanSemResultExact 64)) = some (.returned v) → P1) ∧
      (IsEvmErr (some PanSemResultExact.error) → P2) :=
    hno_ret_err (fun _ h => by cases h) (by rintro ⟨_, h⟩; cases h)
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
  dsimp only
  rw [hbody, evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
  rcases hsgl : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .global (ofString "ev"), .const 72])) with _ | sglv
  · dsimp only; exact herr_triv
  · simp only [hsgl] at hnt ⊢
    have hsgl_w : ∃ sglw : BitVec 64, sglv = .val (.word sglw) ∧ sglw.toNat = memW s (globN s "ev" + 72) := by
      simp [evalHOLExact, evalListHOLExact, hevw, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at hsgl
      rcases hm : s.memory (evw + 72#64) with ⟨sglw⟩
      rw [hm] at hsgl
      exact ⟨sglw, hsgl.2.symm, by unfold memW; rw [← hev72, hm]⟩
    obtain ⟨sglw, rfl, hsglw_eq⟩ := hsgl_w
    rw [if_pos (hsh_w sglw)] at hnt ⊢; dsimp only at hnt ⊢
    set s1 := setVarHOLFinite (ofString "sgl") (.val (.word sglw)) s with hs1
    rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
    rcases hgl : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        (.load .one (.op .add [.var .global (ofString "ev"), .const 64])) with _ | glv
    · dsimp only; exact herr_triv
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
          have herr1 := store_some_eq_error_sg hst1; subst herr1
          dsimp only; exact herr_triv
        | none =>
          dsimp only at hnt ⊢
          obtain ⟨w1, _, hs3_eq⟩ := store_global_off_word (t := s2) (post := s3)
            (gname := "ev") (gbase := globN s "ev") (off := 72) hevw hevw_nat (by omega)
            (fun v hv => by
              simp [evalHOLExact, evalListHOLExact, hs2_sgl, hs2_amt, valueIsWord, valueWord, wordOpHOL, wordOp] at hv
              exact ⟨_, hv.symm⟩) hst1
          rw [evaluateHOLFiniteState_return] at hnt ⊢; dsimp only [evalHOLExact] at hnt ⊢
          have hsz0 : sizeOfShapeWithContextHOL s3.structs
              (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
            simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
          rw [if_pos hsz0] at hnt ⊢; dsimp only at hnt ⊢
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
              (∀ off' ∈ nonStructFrameOffs, x ≠ BitVec.ofNat 64 (globN s "ev" + off')) →
              post.memory x = s.memory x := by
            intro x hx
            change s3.memory x = s.memory x
            rw [hs3_eq]
            have hn72 : x ≠ BitVec.ofNat 64 (globN s "ev" + 72) := hx 72 (by simp [nonStructFrameOffs])
            simp [updW, hn72, hs2, hs1, setVarHOLFinite]
          obtain ⟨hInv_p, hch_p, hR_p⟩ := evmInv_of_head_nonstruct hInv hGp hglob_p hbe_p hmem_out
          exact ⟨fun _ _ => ⟨hInv_p, hch_p, le_of_eq hR_p, hglob_p⟩, by rintro ⟨_, h⟩; cases h⟩
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
        · dsimp only; exact herr_triv
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
            | none => dsimp only; exact herr_triv
            | some r0_as =>
              cases r0_as with
              | timeOut => simp at hnt
              | «break» | «continue» | error => dsimp only; exact herr_triv
              | finalFfi _ =>
                dsimp only
                exact hno_ret_err (fun _ h => by cases h) (by rintro ⟨_, h⟩; cases h)
              | exception eid_as ev_as =>
                dsimp only
                by_cases heid : eid_as = ofString "EvmErr"
                · subst heid
                  have hlf_as : LocFrame (callEntryStateHOLFinite s2 cal_as) st_as :=
                    hsafe_as.to_resumes (Or.inr ⟨_, ev_as, rfl, by decide⟩)
                  let post : PanSemStateFiniteExact 64 F := { st_as.emptyLocalsHOLFinite with
                    locals := (st_as.emptyLocalsHOLFinite.locals.resVarEq (ofString "gl", s1.locals.lookup (ofString "gl"))).resVarEq
                      (ofString "sgl", s.locals.lookup (ofString "sgl")) }
                  have hp_eq : post = { s with locals := post.locals, clock := st_as.clock } := by
                    have h1 : post = { st_as with locals := post.locals, clock := st_as.clock } := rfl
                    have h2 : st_as = { callEntryStateHOLFinite s2 cal_as with locals := st_as.locals, clock := st_as.clock } := hlf_as
                    rw [h1, h2]; rfl
                  have hInv_p : EvmInv post := by
                    rw [hp_eq]; exact localsFree_evmInv s _ _ hInv
                  have hc_p := evm_congr (s := s) (t := post) (by rw [hp_eq]) (by rw [hp_eq])
                  have hch_p := evmChain_congr (s := s) (t := post) (by rw [hp_eq]) (by rw [hp_eq])
                  exact And.intro (fun _ h => by cases h) (fun _ => ⟨hInv_p, hch_p, le_of_eq hc_p.2.1⟩)
                · exact hno_ret_err (fun _ h => by cases h)
                    (by rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1)
              | returned v_as =>
                have hlf_as : LocFrame (callEntryStateHOLFinite s2 cal_as) st_as :=
                  hsafe_as.to_resumes (Or.inl ⟨v_as, rfl⟩)
                obtain ⟨totw, rfl, htot_le⟩ := add_sat_body_le_sum (callEntryStateHOLFinite s2 cal_as) sglw glw
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
                    have herr := store_some_eq_error_sg hst_72; subst herr
                    dsimp only; exact herr_triv
                  | none =>
                    dsimp only at hnt ⊢
                    obtain ⟨w_72, _, hs5_eq⟩ := store_global_off_word (t := s4) (post := s5)
                      (gname := "ev") (gbase := globN s "ev") (off := 72) hs3_evw hevw_nat (by omega)
                      (fun v hv => by simp [evalHOLExact] at hv; exact ⟨0, hv.symm⟩) hst_72
                    rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
                    rcases hst_64 : evaluateHOLFiniteState s5
                        (.store (.op .add [.var .global (ofString "ev"), .const 64])
                          (.op .sub [.var .local (ofString "gl"), .var .local (ofString "rem")])) with ⟨r_64, s6⟩
                    simp only [hst_64] at hnt ⊢
                    cases r_64 with
                    | some res_64 =>
                      have herr := store_some_eq_error_sg hst_64; subst herr
                      dsimp only; exact herr_triv
                    | none =>
                      dsimp only at hnt ⊢
                      obtain ⟨w_64, hw_64_ev, hs6_eq⟩ := store_global_off_word (t := s5) (post := s6)
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
                        have herr := store_some_eq_error_sg hst_192; subst herr
                        dsimp only; exact herr_triv
                      | none =>
                        dsimp only at hnt ⊢
                        have hs6_192_mem : s6.memory (evw + 192#64) = s.memory (evw + 192#64) := by
                          rw [hs6_eq, hs5_eq]
                          have hn64 : evw + 192#64 ≠ BitVec.ofNat 64 (globN s "ev" + 64) := by rw [hev192]; intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
                          have hn72 : evw + 192#64 ≠ BitVec.ofNat 64 (globN s "ev" + 72) := by rw [hev192]; intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
                          simp only [updW, hn64, hn72, ↓reduceIte]
                          change s3.memory (evw + 192#64) = s.memory (evw + 192#64)
                          exact congrFun hs3_mem _
                        obtain ⟨w_192, hw_192_ev, hs7_eq⟩ := store_global_off_word (t := s6) (post := s7)
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
                            (∀ addr ∈ headAllowedOffsets (globN s "ev") (globN s "cur_cont"), x ≠ BitVec.ofNat 64 addr) →
                            post.memory x = s.memory x := by
                          intro x hx
                          change s7.memory x = s.memory x
                          rw [hs7_eq, hs6_eq, hs5_eq]
                          have hn192 : x ≠ BitVec.ofNat 64 (globN s "ev" + 192) := hx _ (by simp [headAllowedOffsets])
                          have hn64 : x ≠ BitVec.ofNat 64 (globN s "ev" + 64) := hx _ (by simp [headAllowedOffsets])
                          have hn72 : x ≠ BitVec.ofNat 64 (globN s "ev" + 72) := hx _ (by simp [headAllowedOffsets])
                          simp only [updW, hn192, hn64, hn72, ↓reduceIte]
                          change s3.memory x = s.memory x
                          exact congrFun hs3_mem x
                        have hm64_post : memW post (globN s "ev" + 64) = memW s (globN s "ev" + 64) - remw.toNat := by
                          change memW s7 (globN s "ev" + 64) = _
                          rw [hs7_eq, memW_updW_ne s6 _ _ w_192 (by omega) (by omega) (by omega),
                              hs6_eq, memW_updW_same s5 _ (glw - remw),
                              BitVec.toNat_sub_of_le (BitVec.le_def.2 hrem_le_gl), hglw_eq]
                        have hm192_post : memW post (globN s "ev" + 192) = w_192.toNat := by
                          change memW s7 (globN s "ev" + 192) = _
                          rw [hs7_eq, memW_updW_same s6 _ w_192]
                        obtain ⟨hInv_p, hch_p, hsum_le⟩ := evmInv_of_head_status_gas_update hInv hGp hp_meta.2.2.2.2.1 hp_meta.2.2.2.2.2 hmem_out
                          (by rw [hm64_post, hm192_post]; omega)
                        exact And.intro (fun _ _ => ⟨hInv_p, hch_p, hsum_le, hp_meta.2.2.2.2.1⟩) (by rintro ⟨_, h⟩; cases h)
                · have hcmp2 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
                      (.cmp .notLower (.var .local (ofString "tot")) (.var .local (ofString "amount"))) =
                      some (.val (.word 0)) := by
                    simp [evalHOLExact, hs3_tot, hs3_amt, Compiler.Encoders.Asm.wordCmpHOL, hge2]
                  rw [hcmp2] at hnt ⊢; dsimp only at hnt ⊢
                  rw [if_pos rfl, evaluateHOLFiniteState_skip] at hnt ⊢; dsimp only at hnt ⊢
                  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_raise] at hnt ⊢
                  dsimp only [evalHOLExact] at hnt ⊢
                  cases hs3_esh : s3.eshapes.lookup (ofString "EvmErr") with
                  | none => dsimp only; exact herr_triv
                  | some sh =>
                    dsimp only
                    by_cases hcond : shapeOfHOLExact (.val (.word (4 : BitVec 64))) = sh ∧
                        sizeOfShapeWithContextHOL s3.structs (shapeOfHOLExact (.val (.word (4 : BitVec 64)))) ≤ 32
                    · rw [if_pos hcond]; dsimp only
                      let post : PanSemStateFiniteExact 64 F := { s3.emptyLocalsHOLFinite with
                        locals := ((s3.emptyLocalsHOLFinite.locals.resVarEq (ofString "tot", s2.locals.lookup (ofString "tot"))).resVarEq
                          (ofString "gl", s1.locals.lookup (ofString "gl"))).resVarEq
                          (ofString "sgl", s.locals.lookup (ofString "sgl")) }
                      have hp_eq : post = { s with locals := post.locals, clock := st_as.clock } := by
                        have h1 : post = { st_as with locals := post.locals, clock := st_as.clock } := rfl
                        have h2 : st_as = { callEntryStateHOLFinite s2 cal_as with locals := st_as.locals, clock := st_as.clock } := hlf_as
                        rw [h1, h2]; rfl
                      have hInv_p : EvmInv post := by
                        rw [hp_eq]; exact localsFree_evmInv s _ _ hInv
                      have hc_p := evm_congr (s := s) (t := post) (by rw [hp_eq]) (by rw [hp_eq])
                      have hch_p := evmChain_congr (s := s) (t := post) (by rw [hp_eq]) (by rw [hp_eq])
                      exact And.intro (fun _ h => by cases h) (fun _ => ⟨hInv_p, hch_p, le_of_eq hc_p.2.1⟩)
                    · rw [if_neg hcond]; dsimp only; exact herr_triv

theorem eps_credit_state_gas_refund :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => post.globals = s.globals)
      (ofString "credit_state_gas_refund") := by
  refine ⟨_, _, _, lookup_credit_state_gas_refund_b, ?_⟩
  intro F s hcode hInv _ ⟨vals, hl⟩ hnt
  have hlen1 : ∃ v0, vals = [v0] := by
    have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
      originalRuntimeCode.lookup (ofString "credit_state_gas_refund") vals _ _ _ hl
    simp only [Flapjack.lookupCodeHOLExact, lookup_credit_state_gas_refund_b] at hx
    rcases vals with _ | ⟨v0, _ | _⟩ <;> simp at hx
    exact ⟨v0, rfl⟩
  obtain ⟨v0, rfl⟩ := hlen1
  obtain ⟨_, _, amtw, rfl, hamt⟩ := one_word_arg_lookup lookup_credit_state_gas_refund_b hl
  obtain ⟨hb_ev, evw, hevw, hevw_nat⟩ := ev_word_bounds hInv
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by norm_num
  have hev64 : evw + BitVec.ofNat 64 64 = BitVec.ofNat 64 (globN s "ev" + 64) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hevw_nat]
  have hev72 : evw + BitVec.ofNat 64 72 = BitVec.ofNat 64 (globN s "ev" + 72) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hevw_nat]
  have hev192 : evw + BitVec.ofNat 64 192 = BitVec.ofNat 64 (globN s "ev" + 192) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hevw_nat]
  have hno_ret_err {r0 : Option (PanSemResultExact 64)} {P1 P2 : Prop}
      (h1 : ∀ v, r0 ≠ some (.returned v)) (h2 : ¬ IsEvmErr r0) :
      (∀ v, r0 = some (.returned v) → P1) ∧ (IsEvmErr r0 → P2) :=
    ⟨fun v hv => (h1 v hv).elim, fun he => (h2 he).elim⟩
  have herr_triv {P1 P2 : Prop} :
      (∀ v, (some PanSemResultExact.error : Option (PanSemResultExact 64)) = some (.returned v) → P1) ∧
      (IsEvmErr (some PanSemResultExact.error) → P2) :=
    hno_ret_err (fun _ h => by cases h) (by rintro ⟨_, h⟩; cases h)
  have hsh_w : ∀ w : BitVec 64, shapeEqHOL .one (shapeOfHOLExact (.val (.word w) : ValueHOL 64)) = true :=
    fun _ => by simp [shapeEqHOL, shapeOfHOLExact]
  have hbody : sourceFnBody Guest.Software.guestFn_credit_state_gas_refund =
      .dec (ofString "spilled") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 192]))
        (.decCall (ofString "from_gl") .one (ofString "min")
          [.var .local (ofString "amount"), .var .local (ofString "spilled")]
          (.seq
            (.store (.op .add [.var .global (ofString "ev"), .const 64])
              (.op .add
                [.load .one (.op .add [.var .global (ofString "ev"), .const 64]),
                 .var .local (ofString "from_gl")]))
            (.seq
              (.store (.op .add [.var .global (ofString "ev"), .const 192])
                (.op .sub [.var .local (ofString "spilled"), .var .local (ofString "from_gl")]))
              (.seq
                (.store (.op .add [.var .global (ofString "ev"), .const 72])
                  (.op .add
                    [.load .one (.op .add [.var .global (ofString "ev"), .const 72]),
                     .op .sub [.var .local (ofString "amount"), .var .local (ofString "from_gl")]]))
                (.return (.const 0)))))) := rfl
  dsimp only
  rw [hbody, evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
  rcases hsp : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .global (ofString "ev"), .const 192])) with _ | spv
  · dsimp only; exact herr_triv
  · simp only [hsp] at hnt ⊢
    have hsp_w : ∃ spw : BitVec 64, spv = .val (.word spw) ∧ spw.toNat = memW s (globN s "ev" + 192) := by
      simp [evalHOLExact, evalListHOLExact, hevw, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at hsp
      rcases hm : s.memory (evw + 192#64) with ⟨spw⟩
      rw [hm] at hsp
      exact ⟨spw, hsp.2.symm, by unfold memW; rw [← hev192, hm]⟩
    obtain ⟨spw, rfl, hspw_eq⟩ := hsp_w
    rw [if_pos (hsh_w spw)] at hnt ⊢; dsimp only at hnt ⊢
    set s1 := setVarHOLFinite (ofString "spilled") (.val (.word spw)) s with hs1
    have hs1_sp : s1.locals.lookup (ofString "spilled") = some (.val (.word spw)) := by
      simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs1_amt : s1.locals.lookup (ofString "amount") = some (.val (.word amtw)) := by
      simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hamt,
        show ofString "spilled" ≠ ofString "amount" by decide]
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
    have hargs_min : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
        [.var .local (ofString "amount"), .var .local (ofString "spilled")] =
        some [.val (.word amtw), .val (.word spw)] := by
      rw [evalListHOLFinite_eq_toExact]
      simp [evalListHOLExact, evalHOLExact, hs1_amt, hs1_sp]
    rw [hargs_min] at hnt ⊢; dsimp only at hnt ⊢
    have hs1_code : s1.code = originalRuntimeCode := hcode
    rcases hl_min : lookupCodeHOLFinite s1.code.lookup (ofString "min")
        [.val (.word amtw), .val (.word spw)] with _ | ⟨body_min, cal_min, ret_min⟩
    · dsimp only; exact herr_triv
    · dsimp only at hnt ⊢
      by_cases hclk0 : s1.clock = 0
      · simp [hl_min, hclk0] at hnt
      · simp only [hclk0, ↓reduceIte] at hnt ⊢
        have hl_min_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "min")
            [.val (.word amtw), .val (.word spw)] = some (body_min, cal_min, ret_min) := by
          rwa [← hs1_code]
        obtain ⟨rfl, rfl, w_a, w_b, hvals_eq, hcal_a, hcal_b⟩ :=
          two_word_arg_lookup (by decide) lookup_min_b hl_min_orig
        injection hvals_eq with hv1 hrest_v
        injection hv1 with hv1'; injection hv1' with hw_a; subst hw_a
        injection hrest_v with hv2 _
        injection hv2 with hv2'; injection hv2' with hw_b; subst hw_b
        have hsafe_min := evaluate_readOnlyProg opRoCallees opRoCallees_good
          (sourceFnBody Guest.Software.guestFn_min) rfl
          (callEntryStateHOLFinite s1 cal_min) hs1_code
        rcases hrun_min : evaluateHOLFiniteState (callEntryStateHOLFinite s1 cal_min)
            (sourceFnBody Guest.Software.guestFn_min) with ⟨res_min, st_min⟩
        simp only [hl_min, hclk0, ↓reduceIte, hrun_min] at hnt hsafe_min ⊢
        cases res_min with
        | none => dsimp only; exact herr_triv
        | some r0_min =>
          cases r0_min with
          | timeOut => simp at hnt
          | «break» | «continue» | error => dsimp only; exact herr_triv
          | finalFfi _ =>
            dsimp only
            exact hno_ret_err (fun _ h => by cases h) (by rintro ⟨_, h⟩; cases h)
          | exception eid_m ev_m =>
            dsimp only
            by_cases heid : eid_m = ofString "EvmErr"
            · subst heid
              have hlf_min : LocFrame (callEntryStateHOLFinite s1 cal_min) st_min :=
                hsafe_min.to_resumes (Or.inr ⟨_, ev_m, rfl, by decide⟩)
              let post : PanSemStateFiniteExact 64 F := { st_min.emptyLocalsHOLFinite with
                locals := st_min.emptyLocalsHOLFinite.locals.resVarEq (ofString "spilled", s.locals.lookup (ofString "spilled")) }
              have hp_eq : post = { s with locals := post.locals, clock := st_min.clock } := by
                have h1 : post = { st_min with locals := post.locals, clock := st_min.clock } := rfl
                have h2 : st_min = { callEntryStateHOLFinite s1 cal_min with locals := st_min.locals, clock := st_min.clock } := hlf_min
                rw [h1, h2]; rfl
              have hInv_p : EvmInv post := by rw [hp_eq]; exact localsFree_evmInv s _ _ hInv
              have hc_p := evm_congr (s := s) (t := post) (by rw [hp_eq]) (by rw [hp_eq])
              have hch_p := evmChain_congr (s := s) (t := post) (by rw [hp_eq]) (by rw [hp_eq])
              exact And.intro (fun _ h => by cases h) (fun _ => ⟨hInv_p, hch_p, le_of_eq hc_p.2.1⟩)
            · exact hno_ret_err (fun _ h => by cases h)
                (by rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1)
          | returned v_min =>
            have hlf_min : LocFrame (callEntryStateHOLFinite s1 cal_min) st_min :=
              hsafe_min.to_resumes (Or.inl ⟨v_min, rfl⟩)
            obtain ⟨fgw, rfl, hfg_le_amt, hfg_le_sp⟩ := min_body_exact (callEntryStateHOLFinite s1 cal_min)
              hcal_a hcal_b v_min (by rw [hrun_min])
            have hsh_ok : (shapeEqHOL (shapeOfHOLExact (.val (.word fgw) : ValueHOL 64)) .one &&
                shapeEqHOL (shapeOfHOLExact (.val (.word fgw) : ValueHOL 64)) .one) = true := by
              simp [shapeOfHOLExact, shapeEqHOL]
            have hsh_ok' : (shapeEqHOL (shapeOfHOLExact (.val (.word fgw) : ValueHOL 64)) .one &&
                shapeEqHOL .one (shapeOfHOLExact (.val (.word fgw) : ValueHOL 64))) = true := by
              simp [shapeOfHOLExact, shapeEqHOL]
            dsimp only at hnt ⊢
            simp only [hsh_ok, hsh_ok', ↓reduceIte] at hnt ⊢
            set s2 := setVarHOLFinite (ofString "from_gl") (.val (.word fgw)) { st_min with locals := s1.locals } with hs2
            have hs2_eq_s : s2 = { s with locals := s2.locals, clock := st_min.clock } := by
              have h1 : s2 = { st_min with locals := s2.locals, clock := st_min.clock } := rfl
              have h2 : st_min = { callEntryStateHOLFinite s1 cal_min with locals := st_min.locals, clock := st_min.clock } := hlf_min
              rw [h1, h2]; rfl
            have hs2_mem : s2.memory = s.memory := by rw [hs2_eq_s]
            have hs2_glob : s2.globals = s.globals := by rw [hs2_eq_s]
            have hs2_code : s2.code = s.code := by rw [hs2_eq_s]
            have hs2_ma : s2.memaddrs = s.memaddrs := by rw [hs2_eq_s]
            have hs2_sh : s2.shMemaddrs = s.shMemaddrs := by rw [hs2_eq_s]
            have hs2_ba : s2.baseAddr = s.baseAddr := by rw [hs2_eq_s]
            have hs2_be : s2.be = s.be := by rw [hs2_eq_s]
            have hs2_evw : s2.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
              rw [hs2_glob]; exact hevw
            have hs2_fg : s2.locals.lookup (ofString "from_gl") = some (.val (.word fgw)) := by
              simp [hs2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have hs2_sp : s2.locals.lookup (ofString "spilled") = some (.val (.word spw)) := by
              simp [hs2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_sp,
                show ofString "from_gl" ≠ ofString "spilled" by decide]
            rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
            rcases hst_64 : evaluateHOLFiniteState s2
                (.store (.op .add [.var .global (ofString "ev"), .const 64])
                  (.op .add
                    [.load .one (.op .add [.var .global (ofString "ev"), .const 64]),
                     .var .local (ofString "from_gl")])) with ⟨r_64, s3⟩
            simp only [hst_64] at hnt ⊢
            cases r_64 with
            | some res_64 =>
              have herr := store_some_eq_error_sg hst_64; subst herr
              dsimp only; exact herr_triv
            | none =>
              dsimp only at hnt ⊢
              obtain ⟨w_64, hw_64_ev, hs3_eq⟩ := store_global_off_word (t := s2) (post := s3)
                (gname := "ev") (gbase := globN s "ev") (off := 64) hs2_evw hevw_nat (by omega)
                (fun v hv => by
                  simp only [evalHOLExact, wordOpHOL] at hv; revert hv
                  rcases @evalListHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a)) _ with _ | vs
                  · simp
                  · dsimp only; split
                    · simp only [Option.map]
                      rcases wordOp .add (vs.map valueWord) with _ | w
                      · simp
                      · intro hv; injection hv with hv'; exact ⟨w, hv'.symm⟩
                    · simp) hst_64
              have hw_64_le : w_64.toNat ≤ memW s (globN s "ev" + 64) + fgw.toNat := by
                rcases hm64_s : s.memory (evw + 64#64) with ⟨glw⟩
                have hm64_2 : s2.memory (evw + 64#64) = .word glw := (congrFun hs2_mem _).trans hm64_s
                have hw_wf1 : isWfShapeExactHOL s2.structs ShapeHOL.one = true := by
                  simp [isWfShapeExactHOL]
                have h64_c : (64 : BitVec 64) = 64#64 := rfl
                have h0_c : (0 : BitVec 64) = 0#64 := rfl
                by_cases hdom64 : s2.memaddrs (evw + 64#64)
                · simp only [evalHOLExact, evalListHOLExact, hs2_fg, hs2_evw, h64_c, h0_c, hm64_2, hdom64,
                    memLoadHOLExact, hw_wf1, wordOpHOL, wordOp, valueIsWord, valueWord, List.map,
                    Option.map, List.all, Bool.and_self, List.foldr, BitVec.add_zero, ↓reduceIte] at hw_64_ev
                  injection hw_64_ev with hw1; injection hw1 with hw2; injection hw2 with hw_eq
                  subst hw_eq
                  have hglw_nat : glw.toNat = memW s (globN s "ev" + 64) := by
                    unfold memW; rw [← hev64, hm64_s]
                  rw [← hglw_nat, BitVec.toNat_add]
                  exact Nat.mod_le _ _
                · simp only [evalHOLExact, evalListHOLExact, hs2_fg, hs2_evw, h64_c, h0_c, hm64_2, hdom64,
                    memLoadHOLExact, hw_wf1, wordOpHOL, wordOp, valueIsWord, valueWord, List.map,
                    Option.map, List.all, Bool.and_self, List.foldr, BitVec.add_zero, ↓reduceIte] at hw_64_ev
                  cases hw_64_ev
              rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
              rcases hst_192 : evaluateHOLFiniteState s3
                  (.store (.op .add [.var .global (ofString "ev"), .const 192])
                    (.op .sub [.var .local (ofString "spilled"), .var .local (ofString "from_gl")])) with ⟨r_192, s4⟩
              simp only [hst_192] at hnt ⊢
              cases r_192 with
              | some res_192 =>
                have herr := store_some_eq_error_sg hst_192; subst herr
                dsimp only; exact herr_triv
              | none =>
                dsimp only at hnt ⊢
                obtain ⟨w_192, hw_192_ev, hs4_eq⟩ := store_global_off_word (t := s3) (post := s4)
                  (gname := "ev") (gbase := globN s "ev") (off := 192)
                  (by rw [hs3_eq]; exact hs2_evw) hevw_nat (by omega)
                  (fun v hv => by
                    have h3_sp : s3.locals.lookup (ofString "spilled") = some (.val (.word spw)) := by rw [hs3_eq]; exact hs2_sp
                    have h3_fg : s3.locals.lookup (ofString "from_gl") = some (.val (.word fgw)) := by rw [hs3_eq]; exact hs2_fg
                    simp [evalHOLExact, evalListHOLExact, h3_sp, h3_fg, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
                    exact ⟨_, hv.symm⟩) hst_192
                have hw_192_val : w_192 = spw - fgw := by
                  have h3_sp : s3.locals.lookup (ofString "spilled") = some (.val (.word spw)) := by rw [hs3_eq]; exact hs2_sp
                  have h3_fg : s3.locals.lookup (ofString "from_gl") = some (.val (.word fgw)) := by rw [hs3_eq]; exact hs2_fg
                  simp [evalHOLExact, evalListHOLExact, h3_sp, h3_fg, wordOpHOL, wordOp, valueIsWord, valueWord] at hw_192_ev
                  exact hw_192_ev.symm
                subst hw_192_val
                rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
                rcases hst_72 : evaluateHOLFiniteState s4
                    (.store (.op .add [.var .global (ofString "ev"), .const 72])
                      (.op .add
                        [.load .one (.op .add [.var .global (ofString "ev"), .const 72]),
                         .op .sub [.var .local (ofString "amount"), .var .local (ofString "from_gl")]])) with ⟨r_72, s5⟩
                simp only [hst_72] at hnt ⊢
                cases r_72 with
                | some res_72 =>
                  have herr := store_some_eq_error_sg hst_72; subst herr
                  dsimp only; exact herr_triv
                | none =>
                  dsimp only at hnt ⊢
                  obtain ⟨w_72, _, hs5_eq⟩ := store_global_off_word (t := s4) (post := s5)
                    (gname := "ev") (gbase := globN s "ev") (off := 72)
                    (by rw [hs4_eq, hs3_eq]; exact hs2_evw) hevw_nat (by omega)
                    (fun v hv => by
                      simp only [evalHOLExact, wordOpHOL] at hv; revert hv
                      rcases @evalListHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a)) _ with _ | vs
                      · simp
                      · dsimp only; split
                        · simp only [Option.map]
                          rcases wordOp .add (vs.map valueWord) with _ | w
                          · simp
                          · intro hv; injection hv with hv'; exact ⟨w, hv'.symm⟩
                        · simp) hst_72
                  rw [evaluateHOLFiniteState_return] at hnt ⊢; dsimp only [evalHOLExact] at hnt ⊢
                  have hsz0 : sizeOfShapeWithContextHOL s5.structs
                      (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
                    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
                  rw [if_pos hsz0] at hnt ⊢; dsimp only at hnt ⊢
                  let post : PanSemStateFiniteExact 64 F := { s5.emptyLocalsHOLFinite with
                    locals := (s5.emptyLocalsHOLFinite.locals.resVarEq (ofString "from_gl", s1.locals.lookup (ofString "from_gl"))).resVarEq
                      (ofString "spilled", s.locals.lookup (ofString "spilled")) }
                  have hp_meta : post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ post.shMemaddrs = s.shMemaddrs ∧ post.baseAddr = s.baseAddr ∧ post.globals = s.globals ∧ post.be = s.be := by
                    have h5 : s5.code = s2.code ∧ s5.memaddrs = s2.memaddrs ∧ s5.shMemaddrs = s2.shMemaddrs ∧ s5.baseAddr = s2.baseAddr ∧ s5.globals = s2.globals ∧ s5.be = s2.be := by
                      rw [hs5_eq, hs4_eq, hs3_eq]; simp
                    exact ⟨h5.1.trans hs2_code, h5.2.1.trans hs2_ma, h5.2.2.1.trans hs2_sh,
                      h5.2.2.2.1.trans hs2_ba, h5.2.2.2.2.1.trans hs2_glob, h5.2.2.2.2.2.trans hs2_be⟩
                  have hGp : GuestInv post := guestInv_congr hp_meta.1 hp_meta.2.1 hp_meta.2.2.1 hp_meta.2.2.2.1 hInv.1.1
                  have hmem_out : ∀ x : BitVec 64,
                      (∀ addr ∈ headAllowedOffsets (globN s "ev") (globN s "cur_cont"), x ≠ BitVec.ofNat 64 addr) →
                      post.memory x = s.memory x := by
                    intro x hx
                    change s5.memory x = s.memory x
                    rw [hs5_eq, hs4_eq, hs3_eq]
                    have hn72 : x ≠ BitVec.ofNat 64 (globN s "ev" + 72) := hx _ (by simp [headAllowedOffsets])
                    have hn192 : x ≠ BitVec.ofNat 64 (globN s "ev" + 192) := hx _ (by simp [headAllowedOffsets])
                    have hn64 : x ≠ BitVec.ofNat 64 (globN s "ev" + 64) := hx _ (by simp [headAllowedOffsets])
                    simp only [updW, hn72, hn192, hn64, ↓reduceIte]
                    exact congrFun hs2_mem x
                  have hm64_post : memW post (globN s "ev" + 64) = w_64.toNat := by
                    change memW s5 (globN s "ev" + 64) = _
                    rw [hs5_eq, memW_updW_ne s4 _ _ w_72 (by omega) (by omega) (by omega),
                        hs4_eq, memW_updW_ne s3 _ _ (spw - fgw) (by omega) (by omega) (by omega),
                        hs3_eq, memW_updW_same s2 _ w_64]
                  have hm192_post : memW post (globN s "ev" + 192) = memW s (globN s "ev" + 192) - fgw.toNat := by
                    change memW s5 (globN s "ev" + 192) = _
                    rw [hs5_eq, memW_updW_ne s4 _ _ w_72 (by omega) (by omega) (by omega),
                        hs4_eq, memW_updW_same s3 _ (spw - fgw),
                        BitVec.toNat_sub_of_le (BitVec.le_def.2 hfg_le_sp), hspw_eq]
                  obtain ⟨hInv_p, hch_p, hsum_le⟩ := evmInv_of_head_status_gas_update hInv hGp hp_meta.2.2.2.2.1 hp_meta.2.2.2.2.2 hmem_out
                    (by rw [hm64_post, hm192_post]; have : fgw.toNat ≤ memW s (globN s "ev" + 192) := hspw_eq ▸ hfg_le_sp; omega)
                  exact And.intro (fun _ _ => ⟨hInv_p, hch_p, hsum_le, hp_meta.2.2.2.2.1⟩) (by rintro ⟨_, h⟩; cases h)

/-! ## 3. Additional `HandlerRun` combinators -/

private theorem rbound_step_sg {charged : Bool} {r1 r2 r0 : Nat}
    (h1 : r2 ≤ r1) (h2 : if charged then r1 < r0 else r1 ≤ r0) :
    if charged then r2 < r0 else r2 ≤ r0 := by
  cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at h2 ⊢ <;> omega

private theorem rbound_to_le_sg {charged : Bool} {r1 r0 : Nat}
    (h : if charged then r1 < r0 else r1 ≤ r0) : r1 ≤ r0 := by
  cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at h <;> omega

theorem _root_.InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.HandlerRun.seq_assoc
    {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {p1 p2 p3 : ProgHOL 64}
    (hrun : HandlerRun s0 P charged (.seq p1 (.seq p2 p3))) :
    HandlerRun s0 P charged (.seq (.seq p1 p2) p3) := by
  intro t hc hInv hlen hR hP hnt
  have hr := hrun t hc hInv hlen hR hP
  rw [evaluateHOLFiniteState_seq_line780] at hnt hr ⊢
  dsimp only at hnt hr ⊢
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  dsimp only at hnt ⊢
  rcases h1 : evaluateHOLFiniteState t p1 with ⟨r1, s1⟩
  simp only [h1] at hnt hr ⊢
  cases r1 with
  | none =>
    dsimp only at hnt hr ⊢
    rw [evaluateHOLFiniteState_seq_line780] at hr
    exact hr hnt
  | some _ =>
    dsimp only at hnt hr ⊢
    exact hr hnt

theorem _root_.InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.HandlerRun.seq_decCall_call
    {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop}
    {Pc1 Pc2 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc1 Qc2 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    {charged : Bool}
    {nm : MlS} {sh : ShapeHOL} {fn1 : MlS} {args1 : List (ExpHOL 64)}
    {fn2 : MlS} {args2 : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hf1 : EvmPreservingSpec Pc1 Qc1 fn1)
    (hf2 : EvmPreservingSpec Pc2 Qc2 fn2)
    (hentry1 : ∀ (t : PanSemStateFiniteExact 64 F) values body' callee ret',
      t.code = originalRuntimeCode → EvmInv t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args1 = some values →
      lookupCodeHOLFinite t.code.lookup fn1 values = some (body', callee, ret') →
      Pc1 (callEntryStateHOLFinite t callee))
    (hentry2 : ∀ (t1 : PanSemStateFiniteExact 64 F) values body' callee ret',
      t1.code = originalRuntimeCode → EvmInv t1 →
      evalListHOLFinite t1 (h := fun a => Classical.propDecidable (t1.memaddrs a)) args2 = some values →
      lookupCodeHOLFinite t1.code.lookup fn2 values = some (body', callee, ret') →
      Pc2 (callEntryStateHOLFinite t1 callee))
    (hstep : ∀ (t : PanSemStateFiniteExact 64 F) v1 (cpost1 cpost2 : PanSemStateFiniteExact 64 F),
      EvmInv t → P t → EvmInv cpost2 →
      Q { cpost2 with
          locals := (setVarHOLFinite nm v1 { cpost1 with locals := t.locals }).locals.resVarEq
            (nm, t.locals.lookup nm) })
    (hcont : HandlerRun s0 Q charged cont) :
    HandlerRun s0 P charged
      (.seq (.decCall nm sh fn1 args1 (.call (some (none, none)) fn2 args2)) cont) := by
  intro t hc hInv hlen hR hP hnt
  obtain ⟨params1, body1, ret1, hlook1, hspec1⟩ := hf1
  obtain ⟨params2, body2, ret2, hlook2, hspec2⟩ := hf2
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  rcases hargs1 : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args1 with _ | vals1
  · exact opDispatchPost_error s0 t
  · simp only [hargs1] at hnt ⊢
    rcases hl1 : lookupCodeHOLFinite t.code.lookup fn1 vals1 with _ | ⟨body1', cal1, ret1'⟩
    · exact opDispatchPost_error s0 t
    · simp only [hl1] at hnt ⊢
      by_cases hz1 : t.clock = 0
      · simp [hz1] at hnt
      · simp only [hz1, ↓reduceIte] at hnt ⊢
        have hb1_eq := lookupCodeHOLFinite_installed_body t.code.lookup fn1 params1 body1 body1'
          ret1 ret1' vals1 cal1 (by rw [hc]; exact hlook1) hl1
        subst body1'
        have hr1_eq : ret1' = ret1 := by
          have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
            t.code.lookup fn1 vals1 body1 cal1 ret1' hl1
          rw [hc] at hx; simp only [Flapjack.lookupCodeHOLExact, hlook1] at hx
          split at hx
          · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
          · cases hx
        subst ret1'
        have hInv_ce1 : EvmInv (callEntryStateHOLFinite t cal1) := localsFree_evmInv t cal1 (t.clock - 1) hInv
        have hPc1 := hentry1 t vals1 body1 cal1 ret1 hc hInv hP hargs1 hl1
        have hl1_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fn1 vals1 =
            some (body1, cal1, ret1) := by rwa [← hc]
        have hmeta1 := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite t cal1) body1).1
        rcases hrun1 : evaluateHOLFiniteState (callEntryStateHOLFinite t cal1) body1 with ⟨res1, cpost1⟩
        simp only [hrun1] at hnt hmeta1 ⊢
        change cpost1.code = t.code at hmeta1
        have hc_ce1 := evm_congr (s := t) (t := callEntryStateHOLFinite t cal1) rfl rfl
        have hQ1 (hsafe1 : res1 ≠ some .timeOut) :
            (∀ v, res1 = some (.returned v) →
              EvmInv cpost1 ∧ evmChain cpost1 = evmChain (callEntryStateHOLFinite t cal1) ∧
              evmR cpost1 ≤ evmR (callEntryStateHOLFinite t cal1) ∧
              Qc1 (callEntryStateHOLFinite t cal1) v cpost1) ∧
            (IsEvmErr res1 →
              EvmInv cpost1 ∧ evmChain cpost1 = evmChain (callEntryStateHOLFinite t cal1) ∧
              evmR cpost1 ≤ evmR (callEntryStateHOLFinite t cal1)) := by
          have hs := hspec1 (callEntryStateHOLFinite t cal1) hc hInv_ce1 hPc1 ⟨vals1, hl1_orig⟩
            (by rw [hrun1]; exact hsafe1)
          dsimp only at hs; rw [hrun1] at hs; exact hs
        cases res1 with
        | none => dsimp only; exact opDispatchPost_error s0 cpost1
        | some r10 =>
          cases r10 with
          | timeOut => simp at hnt
          | exception eid ev =>
            dsimp only at hnt ⊢
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨hInv_cp1, hch_cp1, hR_cp1⟩ := (hQ1 (by simp)).2 ⟨ev, rfl⟩
              have hInv_el : EvmInv cpost1.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost1 _ cpost1.clock hInv_cp1
              have hc_el := evm_congr (s := cpost1) (t := cpost1.emptyLocalsHOLFinite) rfl rfl
              refine ⟨?_, fun _ => ⟨hInv_el, ?_, ?_⟩⟩
              · rintro ⟨_, h⟩; cases h
              · rw [hc_el.2.2.1, hch_cp1, hc_ce1.2.2.1]; exact hlen
              · have := rbound_to_le_sg hR; rw [hc_el.2.1]; rw [hc_ce1.2.1] at hR_cp1; omega
            · refine opDispatchPost_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» | «continue» | error =>
            dsimp only
            exact opDispatchPost_error s0 _
          | finalFfi _ =>
            dsimp only
            refine opDispatchPost_other (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | returned v1 =>
            dsimp only at hnt ⊢
            by_cases hsh1 : (shapeEqHOL (shapeOfHOLExact v1) sh && shapeEqHOL (shapeOfHOLExact v1) ret1) = true
            · simp only [hsh1, ↓reduceIte] at hnt ⊢
              obtain ⟨hInv_cp1, hch_cp1, hR_cp1, _⟩ := (hQ1 (by simp)).1 v1 rfl
              let t1 := setVarHOLFinite nm v1 { cpost1 with locals := t.locals }
              have hc_t1 : t1.code = originalRuntimeCode := hmeta1.trans hc
              have hInv_t1 : EvmInv t1 := localsFree_evmInv cpost1 t1.locals cpost1.clock hInv_cp1
              have hc_res1 := evm_congr (s := cpost1) (t := t1) rfl rfl
              have ht1_def : setVarHOLFinite nm v1 { cpost1 with locals := t.locals } = t1 := rfl
              simp only [ht1_def] at hnt ⊢
              rw [evaluateHOLFiniteState_call] at hnt ⊢
              rcases hargs2 : evalListHOLFinite t1 (h := fun a => Classical.propDecidable (t1.memaddrs a)) args2 with _ | vals2
              · dsimp only; exact opDispatchPost_error s0 _
              · simp only [hargs2] at hnt ⊢
                rcases hl2 : lookupCodeHOLFinite t1.code.lookup fn2 vals2 with _ | ⟨body2', cal2, ret2'⟩
                · dsimp only; exact opDispatchPost_error s0 _
                · simp only [hl2] at hnt ⊢
                  by_cases hz2 : t1.clock = 0
                  · simp [hz2] at hnt
                  · simp only [hz2, ↓reduceIte] at hnt ⊢
                    have hb2_eq := lookupCodeHOLFinite_installed_body t1.code.lookup fn2 params2 body2 body2'
                      ret2 ret2' vals2 cal2 (by rw [hc_t1]; exact hlook2) hl2
                    subst body2'
                    have hr2_eq : ret2' = ret2 := by
                      have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
                        t1.code.lookup fn2 vals2 body2 cal2 ret2' hl2
                      rw [hc_t1] at hx; simp only [Flapjack.lookupCodeHOLExact, hlook2] at hx
                      split at hx
                      · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
                      · cases hx
                    subst ret2'
                    have hInv_ce2 : EvmInv (callEntryStateHOLFinite t1 cal2) :=
                      localsFree_evmInv t1 cal2 (t1.clock - 1) hInv_t1
                    have hPc2 := hentry2 t1 vals2 body2 cal2 ret2 hc_t1 hInv_t1 hargs2 hl2
                    have hl2_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fn2 vals2 =
                        some (body2, cal2, ret2) := by rwa [← hc_t1]
                    have hmeta2 := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite t1 cal2) body2).1
                    rcases hrun2 : evaluateHOLFiniteState (callEntryStateHOLFinite t1 cal2) body2 with ⟨res2, cpost2⟩
                    simp only [hrun2] at hnt hmeta2 ⊢
                    change cpost2.code = t1.code at hmeta2
                    have hc_ce2 := evm_congr (s := t1) (t := callEntryStateHOLFinite t1 cal2) rfl rfl
                    have hQ2 (hsafe2 : res2 ≠ some .timeOut) :
                        (∀ v, res2 = some (.returned v) →
                          EvmInv cpost2 ∧ evmChain cpost2 = evmChain (callEntryStateHOLFinite t1 cal2) ∧
                          evmR cpost2 ≤ evmR (callEntryStateHOLFinite t1 cal2) ∧
                          Qc2 (callEntryStateHOLFinite t1 cal2) v cpost2) ∧
                        (IsEvmErr res2 →
                          EvmInv cpost2 ∧ evmChain cpost2 = evmChain (callEntryStateHOLFinite t1 cal2) ∧
                          evmR cpost2 ≤ evmR (callEntryStateHOLFinite t1 cal2)) := by
                      have hs := hspec2 (callEntryStateHOLFinite t1 cal2) hc_t1 hInv_ce2 hPc2 ⟨vals2, hl2_orig⟩
                        (by rw [hrun2]; exact hsafe2)
                      dsimp only at hs; rw [hrun2] at hs; exact hs
                    cases res2 with
                    | none => dsimp only; exact opDispatchPost_error s0 _
                    | some r20 =>
                      cases r20 with
                      | timeOut => simp at hnt
                      | exception eid2 ev2 =>
                        dsimp only at hnt ⊢
                        by_cases heid2 : eid2 = ofString "EvmErr"
                        · subst heid2
                          obtain ⟨hInv_cp2, hch_cp2, hR_cp2⟩ := (hQ2 (by simp)).2 ⟨ev2, rfl⟩
                          let errSt := { cpost2.emptyLocalsHOLFinite with
                            locals := cpost2.emptyLocalsHOLFinite.locals.resVarEq (nm, t.locals.lookup nm) }
                          have hInv_err : EvmInv errSt := localsFree_evmInv cpost2 _ cpost2.clock hInv_cp2
                          have hc_err := evm_congr (s := cpost2) (t := errSt) rfl rfl
                          refine ⟨?_, fun _ => ⟨hInv_err, ?_, ?_⟩⟩
                          · rintro ⟨_, h⟩; cases h
                          · rw [hc_err.2.2.1, hch_cp2, hc_ce2.2.2.1, hc_res1.2.2.1, hch_cp1, hc_ce1.2.2.1]
                            exact hlen
                          · have := rbound_to_le_sg hR
                            rw [hc_err.2.1]; rw [hc_ce2.2.1] at hR_cp2
                            rw [hc_res1.2.1] at hR_cp2; rw [hc_ce1.2.1] at hR_cp1
                            omega
                        · refine opDispatchPost_other (fun _ h => by cases h) ?_
                          rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid2 h1
                      | «break» | «continue» | error =>
                        dsimp only; exact opDispatchPost_error s0 _
                      | finalFfi _ =>
                        dsimp only
                        refine opDispatchPost_other (fun _ h => by cases h) ?_
                        rintro ⟨_, h⟩; cases h
                      | returned v2 =>
                        dsimp only at hnt ⊢
                        by_cases hsh2 : shapeEqHOL (shapeOfHOLExact v2) ret2 = true
                        · simp only [hsh2, ↓reduceIte] at hnt ⊢
                          obtain ⟨hInv_cp2, hch_cp2, hR_cp2, _⟩ := (hQ2 (by simp)).1 v2 rfl
                          let resumed : PanSemStateFiniteExact 64 F :=
                            { cpost2 with locals := t1.locals.resVarEq (nm, t.locals.lookup nm) }
                          have hcode_res : resumed.code = originalRuntimeCode := hmeta2.trans hc_t1
                          have hInv_res : EvmInv resumed := localsFree_evmInv cpost2 resumed.locals cpost2.clock hInv_cp2
                          have hc_res2 := evm_congr (s := cpost2) (t := resumed) rfl rfl
                          have hlen_res : (evmChain resumed).length = (evmChain s0).length := by
                            rw [hc_res2.2.2.1, hch_cp2, hc_ce2.2.2.1, hc_res1.2.2.1, hch_cp1, hc_ce1.2.2.1]
                            exact hlen
                          have hR_le : evmR resumed ≤ evmR t := by
                            rw [hc_res2.2.1]; rw [hc_ce2.2.1] at hR_cp2
                            rw [hc_res1.2.1] at hR_cp2; rw [hc_ce1.2.1] at hR_cp1
                            omega
                          have hR_res : if charged then evmR resumed < evmR s0
                              else evmR resumed ≤ evmR s0 :=
                            rbound_step_sg hR_le hR
                          have hQ_res : Q resumed := hstep t v1 cpost1 cpost2 hInv hP hInv_cp2
                          exact hcont resumed hcode_res hInv_res hlen_res hR_res hQ_res (by simpa [resumed] using hnt)
                        · simp only [hsh2, Bool.false_eq_true, ↓reduceIte]
                          exact opDispatchPost_error s0 _
            · simp only [hsh1, Bool.false_eq_true, ↓reduceIte]
              exact opDispatchPost_error s0 _

theorem _root_.InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.HandlerRun.seq_ite_unit
    {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {cond : ExpHOL 64} {yes no cont : ProgHOL 64}
    (hyes : ∀ (t : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) cond = some (.val (.word w)) →
      w ≠ 0 →
      HandlerRun s0 P charged (.seq yes cont))
    (hno : ∀ (t : PanSemStateFiniteExact 64 F),
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) cond = some (.val (.word 0)) →
      HandlerRun s0 (fun s => P s) charged (.seq no cont)) :
    HandlerRun s0 P charged (.seq (.ite cond yes no) cont) := by
  intro t hc hInv hlen hR hP hnt
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
  revert hnt
  split
  · rename_i w hw
    by_cases hw0 : w = 0
    · subst hw0; simp only [↓reduceIte]
      rw [← evaluateHOLFiniteState_seq_line780]
      intro hnt; exact hno t hw t hc hInv hlen hR hP hnt
    · simp only [hw0, ↓reduceIte]
      rw [← evaluateHOLFiniteState_seq_line780]
      intro hnt; exact hyes t w hw hw0 t hc hInv hlen hR hP hnt
  · intro _; dsimp only; exact opDispatchPost_error s0 t

theorem _root_.InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.HandlerRun.seq_call_assign_local
    {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop}
    {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    {charged : Bool}
    {nm : MlS} {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hf : EvmPreservingSpec Pc Qc fname)
    (hentry : ∀ (t : PanSemStateFiniteExact 64 F) values body' callee ret',
      t.code = originalRuntimeCode → EvmInv t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite t.code.lookup fname values = some (body', callee, ret') →
      Pc (callEntryStateHOLFinite t callee))
    (hstep : ∀ (t : PanSemStateFiniteExact 64 F) values body callee retShape v (cpost : PanSemStateFiniteExact 64 F),
      EvmInv t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, callee, retShape) →
      EvmInv cpost → evmChain cpost = evmChain (callEntryStateHOLFinite t callee) →
      Qc (callEntryStateHOLFinite t callee) v cpost →
      Q (setVarHOLFinite nm v { cpost with locals := t.locals }))
    (hcont : HandlerRun s0 Q charged cont) :
    HandlerRun s0 P charged (.seq (.call (some (some (.local, nm), none)) fname args) cont) := by
  intro t hc hInv hlen hR hP hnt
  obtain ⟨params, body, retShape, hlook, hspec⟩ := hf
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args with _ | values
  · dsimp only; exact opDispatchPost_error s0 t
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · dsimp only; exact opDispatchPost_error s0 t
    · simp only [hl] at hnt ⊢
      by_cases hz : t.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hbody_eq : body' = body :=
          lookupCodeHOLFinite_installed_body t.code.lookup fname params body body'
            retShape ret' values callee (by rw [hc]; exact hlook) hl
        subst body'
        have hret_eq : ret' = retShape := by
          have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
            t.code.lookup fname values body callee ret' hl
          rw [hc] at hx; simp only [Flapjack.lookupCodeHOLExact, hlook] at hx
          split at hx
          · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
          · cases hx
        subst ret'
        have hInv_ce : EvmInv (callEntryStateHOLFinite t callee) := localsFree_evmInv t callee (t.clock - 1) hInv
        have hPc : Pc (callEntryStateHOLFinite t callee) := hentry t values body callee retShape hc hInv hP hargs hl
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
            some (body, callee, retShape) := by rwa [← hc]
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite t callee) body).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body with ⟨res, cpost⟩
        simp only [hrun] at hnt hmeta ⊢
        change cpost.code = t.code at hmeta
        have hc_ce := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
        have hQ (hsafe : res ≠ some .timeOut) :
            (∀ v, res = some (.returned v) →
              EvmInv cpost ∧ evmChain cpost = evmChain (callEntryStateHOLFinite t callee) ∧
              evmR cpost ≤ evmR (callEntryStateHOLFinite t callee) ∧
              Qc (callEntryStateHOLFinite t callee) v cpost) ∧
            (IsEvmErr res →
              EvmInv cpost ∧ evmChain cpost = evmChain (callEntryStateHOLFinite t callee) ∧
              evmR cpost ≤ evmR (callEntryStateHOLFinite t callee)) := by
          have hs := hspec (callEntryStateHOLFinite t callee) hc hInv_ce hPc ⟨values, hl_orig⟩
            (by rw [hrun]; exact hsafe)
          dsimp only at hs; rw [hrun] at hs
          exact hs
        cases res with
        | none => dsimp only; exact opDispatchPost_error s0 cpost
        | some r0 =>
          cases r0 with
          | timeOut => simp at hnt
          | returned v =>
            dsimp only at hnt ⊢
            by_cases hsh_ok : shapeEqHOL (shapeOfHOLExact v) retShape = true
            · simp only [hsh_ok, ↓reduceIte] at hnt ⊢
              by_cases hvld : isValidValueHOLExact t.toExact .local nm v = true
              · simp only [hvld, ↓reduceIte] at hnt ⊢
                dsimp only [setKvarHOLFinite] at hnt ⊢
                obtain ⟨hInv_cp, hch_cp, hR_cp, hQc_cp⟩ := (hQ (by simp)).1 v rfl
                let resumed := setVarHOLFinite nm v { cpost with locals := t.locals }
                have hcode_res : resumed.code = originalRuntimeCode := hmeta.trans hc
                have hInv_res : EvmInv resumed := localsFree_evmInv cpost resumed.locals cpost.clock hInv_cp
                have hc_res := evm_congr (s := cpost) (t := resumed) rfl rfl
                have hlen_res : (evmChain resumed).length = (evmChain s0).length := by
                  rw [hc_res.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
                have hR_res : if charged then evmR resumed < evmR s0
                    else evmR resumed ≤ evmR s0 :=
                  rbound_step_sg (by rw [hc_res.2.1]; rw [hc_ce.2.1] at hR_cp; exact hR_cp) hR
                have hQ_res : Q resumed := hstep t values body callee retShape v cpost hInv hP hargs hl_orig hInv_cp hch_cp hQc_cp
                exact hcont resumed hcode_res hInv_res hlen_res hR_res hQ_res (by simpa [resumed] using hnt)
              · simp only [hvld, Bool.false_eq_true, ↓reduceIte]
                exact opDispatchPost_error s0 cpost
            · simp only [hsh_ok, Bool.false_eq_true, ↓reduceIte]
              exact opDispatchPost_error s0 cpost
          | exception eid ev =>
            dsimp only at hnt ⊢
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨hInv_cp, hch_cp, hR_cp⟩ := (hQ (by simp)).2 ⟨ev, rfl⟩
              have hInv_el : EvmInv cpost.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost _ cpost.clock hInv_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              refine ⟨?_, fun _ => ⟨hInv_el, ?_, ?_⟩⟩
              · rintro ⟨_, h⟩; cases h
              · rw [hc_el.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              · have := rbound_to_le_sg hR; rw [hc_el.2.1]; rw [hc_ce.2.1] at hR_cp; omega
            · refine opDispatchPost_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => dsimp only; exact opDispatchPost_error s0 cpost
          | «continue» => dsimp only; exact opDispatchPost_error s0 cpost
          | finalFfi _ =>
            dsimp only
            refine opDispatchPost_other (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => dsimp only; exact opDispatchPost_error s0 cpost.emptyLocalsHOLFinite

theorem _root_.InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.HandlerRun.seq_call_assign_local_simple
    {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    {charged : Bool}
    {nm : MlS} {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hf : EvmPreservingSpec (fun _ => True) Qc fname)
    (hcont : HandlerRun s0 (fun _ => True) charged cont) :
    HandlerRun s0 (fun _ => True) charged (.seq (.call (some (some (.local, nm), none)) fname args) cont) :=
  HandlerRun.seq_call_assign_local hf
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
    hcont

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
