import InitECandidate.Solver.Wave8GuestInv.MemoryViews

/-! Value contract `rv_rlp_encode_bytes` for micro-shard `m27` (`wave8/contracts-m27`),
frozen revision 9 (`8a79d9f28`, tag `wave8-spec-frozen-r9`).

Imports only the light split module `InitECandidate.Solver.Wave8GuestInv.MemoryViews`.
Restates `FunSpec` and `RetLe` verbatim from `campaign/specs-proposed/GuestInv.lean` @ `8a79d9f28`
so they delta-reduce definitionally (`rfl`) to the spec statement in `Axioms.lean`.
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
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-- Outcome specification of a function body from its callee-entry state
(verbatim from `GuestInv.lean` @ `8a79d9f28`). -/
def FunSpec_rlp (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → P s →
      (∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
        some (body, s.locals, retShape)) →
      (evaluateHOLFiniteState s body).1 ≠ some .timeOut →
      Q s (evaluateHOLFiniteState s body).1 (evaluateHOLFiniteState s body).2

/-- Value contract (verbatim from `GuestInv.lean` @ `8a79d9f28`): a normal return is a word at most
`B` of the entry state. -/
def RetLe_rlp (B : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat) (fname : MlS) : Prop :=
  FunSpec_rlp GuestInv (fun s r _ => ∀ v, r = some (.returned v) →
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ B s) fname

private def WordBound_rlp (M : Nat) (v : ValueHOL 64) : Prop :=
  ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ M

private theorem lookup_rlp_be_len :
    originalRuntimeCode.lookup (ofString "rlp_be_len") =
      some ([(ofString "v", .one)], sourceFnBody Guest.Software.guestFn_rlp_be_len, .one) :=
  lookup_of_guestAst_getElem 118 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_be_len) rfl

private theorem lookup_rlp_write_header :
    originalRuntimeCode.lookup (ofString "rlp_write_header") =
      some ([(ofString "dst", .one), (ofString "base", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_write_header, .one) :=
  lookup_of_guestAst_getElem 120 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_write_header) rfl

theorem lookup_rlp_encode_bytes :
    originalRuntimeCode.lookup (ofString "rlp_encode_bytes") =
      some ((sourceFunctionEntry Guest.Software.guestFn_rlp_encode_bytes).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 122 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_encode_bytes) rfl

private theorem decCall_returned_inv_rlp {F : Type}
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

private theorem storeByte_not_returned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b : ExpHOL 64) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s (.storeByte a b)).1 ≠ some (.returned v) := by
  rcases (PanRunBounded.evaluate_storeByte_control_frame s a b).1 with h | h <;> rw [h] <;> simp

private theorem call_void_not_returned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fn : MlS) (args : List (ExpHOL 64)) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fn args)).1 ≠ some (.returned v) := by
  rw [evaluateHOLFiniteState_call]
  cases hargs : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x)) args with
  | none => simp
  | some vs =>
    dsimp only
    cases hlk : lookupCodeHOLFinite s.code.lookup fn vs with
    | none => simp
    | some inst =>
      obtain ⟨body, callee, retSh⟩ := inst
      dsimp only
      split
      · simp
      · rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, post⟩
        cases res with
        | none => simp
        | some r =>
          cases r with
          | returned rv =>
            dsimp only
            split <;> simp
          | _ => simp

private theorem rlp_be_len_while_normal {F : Type}
    (k : Nat) (st : PanSemStateFiniteExact 64 F) (v n : BitVec 64)
    (hv : st.locals.lookup (ofString "v") = some (.val (.word v)))
    (hn : st.locals.lookup (ofString "n") = some (.val (.word n)))
    (hbound : v.toNat < 2 ^ (8 * k)) :
    let wprog : ProgHOL 64 :=
      .while (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64))
        (.seq
          (.assign .local (ofString "v")
            (.shift .lsr (.var .local (ofString "v")) (.const 8#64)))
          (.assign .local (ofString "n")
            (.op .add [.var .local (ofString "n"), .const 1#64])))
    (evaluateHOLFiniteState st wprog).1 = none →
      ∃ (n' : BitVec 64) (d : Nat), d ≤ k ∧ n' = n + BitVec.ofNat 64 d ∧
        (evaluateHOLFiniteState st wprog).2.locals.lookup (ofString "n") =
          some (.val (.word n')) := by
  induction k generalizing st v n with
  | zero =>
    intro wprog _
    have hv0 : v = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      change v.toNat = 0
      omega
    subst hv0
    have hcond : @evalHOLExact 64 F _ st.toExact
        (fun a => Classical.propDecidable (st.memaddrs a))
        (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) =
        some (.val (.word 0#64)) := by
      simp [evalHOLExact, hv, Compiler.Encoders.Asm.wordCmpHOL]
    have hstep : evaluateHOLFiniteState st wprog = (none, st) := by
      have hcond' : evalHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
          (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) =
          some (.val (.word 0#64)) := by
        rw [evalHOLFinite_eq_toExact]; exact hcond
      dsimp only [wprog]
      rw [evaluateHOLFiniteState_while_total, hcond']
      simp
    rw [hstep]
    exact ⟨n, 0, le_refl _, by simp, hn⟩
  | succ m ih =>
    intro wprog hnorm
    by_cases hvz : v = 0#64
    · subst hvz
      have hcond : @evalHOLExact 64 F _ st.toExact
          (fun a => Classical.propDecidable (st.memaddrs a))
          (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) =
          some (.val (.word 0#64)) := by
        simp [evalHOLExact, hv, Compiler.Encoders.Asm.wordCmpHOL]
      have hstep : evaluateHOLFiniteState st wprog = (none, st) := by
        have hcond' : evalHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
            (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) =
            some (.val (.word 0#64)) := by
          rw [evalHOLFinite_eq_toExact]; exact hcond
        dsimp only [wprog]
        rw [evaluateHOLFiniteState_while_total, hcond']
        simp
      rw [hstep]
      exact ⟨n, 0, by omega, by simp, hn⟩
    · have hcond : @evalHOLExact 64 F _ st.toExact
          (fun a => Classical.propDecidable (st.memaddrs a))
          (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) =
          some (.val (.word 1#64)) := by
        simp [evalHOLExact, hv, Compiler.Encoders.Asm.wordCmpHOL, hvz]
      by_cases hclk0 : st.clock = 0
      · have hto : (evaluateHOLFiniteState st wprog).1 = some .timeOut := by
          dsimp only [wprog]
          have hcond' : evalHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
              (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) =
              some (.val (.word 1#64)) := by
            rw [evalHOLFinite_eq_toExact]; exact hcond
          rw [evaluateHOLFiniteState_while_total, hcond']
          simp [show (1#64 : BitVec 64) ≠ 0 by decide, hclk0]
        rw [hto] at hnorm
        cases hnorm
      · have hne_vn : ofString "n" ≠ ofString "v" := by decide
        have hne_nv : ofString "v" ≠ ofString "n" := by decide
        have h8 : (8#64 : BitVec 64).toNat = 8 := rfl
        have hnotge8 : ¬ (64 ≤ (8#64 : BitVec 64).toNat) := by rw [h8]; omega
        let st1 := setVarHOLFinite (ofString "v") (.val (.word (v >>> (8#64).toNat)))
          (decClockHOLFinite st)
        have hv1 : evaluateHOLFiniteState (decClockHOLFinite st)
            (.assign .local (ofString "v")
              (.shift .lsr (.var .local (ofString "v")) (.const 8#64))) =
            (none, st1) := by
          have hvd : (decClockHOLFinite st).locals.lookup (ofString "v") =
              some (.val (.word v)) := hv
          simp [st1, evaluateHOLFiniteState_assign, evalHOLExact, hvd, wordShiftHOL, hnotge8,
            lookupKvarHOLExact, PanSemStateFiniteExact.isValidValueHOLFinite, isValidValueHOLExact,
            setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
        have hn1_lk : st1.locals.lookup (ofString "n") = some (.val (.word n)) := by
          simp [st1, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            hne_nv, hn]
        let st2 := setVarHOLFinite (ofString "n") (.val (.word (n + 1#64))) st1
        have hn2 : evaluateHOLFiniteState st1
            (.assign .local (ofString "n")
              (.op .add [.var .local (ofString "n"), .const 1#64])) =
            (none, st2) := by
          simp [st2, evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hn1_lk,
            wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact,
            PanSemStateFiniteExact.isValidValueHOLFinite, isValidValueHOLExact,
            setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
        have hbodyStep : evaluateHOLFiniteState (decClockHOLFinite st)
            (.seq
              (.assign .local (ofString "v")
                (.shift .lsr (.var .local (ofString "v")) (.const 8#64)))
              (.assign .local (ofString "n")
                (.op .add [.var .local (ofString "n"), .const 1#64]))) =
            (none, st2) := by
          rw [evaluateHOLFiniteState_seq_line780, hv1]
          exact hn2
        have hwStep : evaluateHOLFiniteState st wprog = evaluateHOLFiniteState st2 wprog := by
          dsimp only [wprog]
          rw [evaluateHOLFiniteState_while_total]
          have hcond' : evalHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
              (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) =
              some (.val (.word 1#64)) := by
            rw [evalHOLFinite_eq_toExact]
            exact hcond
          rw [hcond']
          have h10 : (1#64 : BitVec 64) ≠ 0 := by decide
          have hfix : ((decClockHOLFinite st).fixClockHOLFinite
              ((none : Option (PanSemResultExact 64)), st2)) = (none, st2) := by
            simp [fixClockHOLFinite, st2, st1, setVarHOLFinite, decClockHOLFinite]
          simp only [hclk0, if_false, hbodyStep, hfix]
          exact if_pos h10
        have hv_st2 : st2.locals.lookup (ofString "v") =
            some (.val (.word (v >>> (8#64).toNat))) := by
          simp [st2, st1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne_vn]
        have hn_st2 : st2.locals.lookup (ofString "n") = some (.val (.word (n + 1#64))) := by
          simp [st2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hv_shr : (v >>> (8#64).toNat).toNat < 2 ^ (8 * m) := by
          rw [h8, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
          have hp : 2 ^ (8 * (m + 1)) = 2 ^ 8 * 2 ^ (8 * m) := by
            rw [show 8 * (m + 1) = 8 + 8 * m by omega, Nat.pow_add]
          rw [hp] at hbound
          omega
        rw [hwStep] at hnorm ⊢
        obtain ⟨n', d, hd, rfl, ihn⟩ :=
          ih st2 (v >>> (8#64).toNat) (n + 1#64) hv_st2 hn_st2 hv_shr hnorm
        refine ⟨n + 1#64 + BitVec.ofNat 64 d, d + 1, by omega, ?_, ihn⟩
        rw [BitVec.add_assoc]
        congr 1
        change BitVec.ofNat 64 1 + BitVec.ofNat 64 d = BitVec.ofNat 64 (d + 1)
        rw [← BitVec.ofNat_add, Nat.add_comm]

private theorem rlp_be_len_body_returns_le8 {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (retVal : ValueHOL 64)
    (hrun : evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_rlp_be_len) =
      (some (.returned retVal), post)) :
    WordBound_rlp 8 retVal := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_be_len,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    at hrun
  rw [evaluateHOLFiniteState_dec_total] at hrun
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true] at hrun
  have hrun1 := (Prod.mk.inj hrun).1
  clear hrun
  let s1 := setVarHOLFinite (ofString "n") (.val (.word 0#64)) state
  let wbody : ProgHOL 64 :=
    .seq
      (.assign .local (ofString "v")
        (.shift .lsr (.var .local (ofString "v")) (.const 8#64)))
      (.assign .local (ofString "n")
        (.op .add [.var .local (ofString "n"), .const 1#64]))
  let wprog : ProgHOL 64 :=
    .while (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) wbody
  have hassign_noret : ∀ {F' : Type} (t : PanSemStateFiniteExact 64 F') (nm : MlS) (e : ExpHOL 64)
      (rv : ValueHOL 64),
      (evaluateHOLFiniteState t (.assign .local nm e)).1 ≠ some (.returned rv) := by
    intro F' t nm e rv
    rw [evaluateHOLFiniteState_assign]
    split
    · simp
    · split <;> simp
  have hno_body_ret : ∀ {F' : Type} (t : PanSemStateFiniteExact 64 F') (rv : ValueHOL 64),
      (evaluateHOLFiniteState t wbody).1 ≠ some (.returned rv) := by
    intro F' t rv
    dsimp only [wbody]
    rw [evaluateHOLFiniteState_seq_line780]
    have ha1_no := hassign_noret t (ofString "v")
      (.shift .lsr (.var .local (ofString "v")) (.const 8#64)) rv
    rcases ha1 : evaluateHOLFiniteState t
        (.assign .local (ofString "v")
          (.shift .lsr (.var .local (ofString "v")) (.const 8#64))) with ⟨r1, m1⟩
    rw [ha1] at ha1_no
    cases r1 with
    | none => exact hassign_noret m1 _ _ rv
    | some _ => exact ha1_no
  have hno_while_ret : ∀ {F' : Type} (k : Nat) (t : PanSemStateFiniteExact 64 F') (rv : ValueHOL 64),
      t.clock ≤ k → (evaluateHOLFiniteState t wprog).1 ≠ some (.returned rv) := by
    intro F' k
    induction k with
    | zero =>
      intro t rv hclk hret
      have hc0 : t.clock = 0 := by omega
      dsimp only [wprog] at hret
      rw [evaluateHOLFiniteState_while_total] at hret
      split at hret
      · split at hret <;> simp [hc0] at hret
      · simp at hret
    | succ m ih =>
      intro t rv hclk hret
      dsimp only [wprog] at hret
      rw [evaluateHOLFiniteState_while_total] at hret
      split at hret
      · split at hret
        · split at hret
          · simp at hret
          · rename_i hnz
            dsimp only at hret
            rw [fixClockHOLFinite_evaluateState] at hret
            have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite t) wbody
            rcases hbr : evaluateHOLFiniteState (decClockHOLFinite t) wbody with ⟨r1, mid⟩
            rw [hbr] at hret hrem
            have hmclk : mid.clock ≤ m := by
              change mid.clock ≤ t.clock - 1 at hrem
              omega
            cases r1 with
            | none => exact ih mid rv hmclk hret
            | some r1' =>
              cases r1' with
              | «continue» => exact ih mid rv hmclk hret
              | «break» => simp at hret
              | returned rv' =>
                have hno := hno_body_ret (decClockHOLFinite t) rv'
                rw [hbr] at hno
                exact hno rfl
              | _ => simp at hret
        · simp at hret
      · simp at hret
  cases hv : s1.locals.lookup (ofString "v") with
  | none =>
    rw [evaluateHOLFiniteState_seq_line780] at hrun1
    have hcond : evalHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
        (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) = none := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, hv]
    have hstep : evaluateHOLFiniteState
        (setVarHOLFinite (ofString "n") (.val (.word 0#64)) state) wprog =
        (some .error, s1) := by
      change evaluateHOLFiniteState s1 wprog = _
      rw [evaluateHOLFiniteState_while_total, hcond]
    rw [hstep] at hrun1
    simp at hrun1
  | some val =>
    cases val with
    | rStruct _ =>
      rw [evaluateHOLFiniteState_seq_line780] at hrun1
      have hcond : evalHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
          (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) = none := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, hv]
      have hstep : evaluateHOLFiniteState
          (setVarHOLFinite (ofString "n") (.val (.word 0#64)) state) wprog =
          (some .error, s1) := by
        change evaluateHOLFiniteState s1 wprog = _
        rw [evaluateHOLFiniteState_while_total, hcond]
      rw [hstep] at hrun1
      simp at hrun1
    | nStruct _ _ =>
      rw [evaluateHOLFiniteState_seq_line780] at hrun1
      have hcond : evalHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
          (.cmp .notEqual (.var .local (ofString "v")) (.const 0#64)) = none := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, hv]
      have hstep : evaluateHOLFiniteState
          (setVarHOLFinite (ofString "n") (.val (.word 0#64)) state) wprog =
          (some .error, s1) := by
        change evaluateHOLFiniteState s1 wprog = _
        rw [evaluateHOLFiniteState_while_total, hcond]
      rw [hstep] at hrun1
      simp at hrun1
    | val wl =>
      cases wl with
      | word vw =>
        have hn1 : s1.locals.lookup (ofString "n") = some (.val (.word 0#64)) := by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        rw [evaluateHOLFiniteState_seq_line780] at hrun1
        cases hwRun : evaluateHOLFiniteState
            (setVarHOLFinite (ofString "n") (.val (.word 0#64)) state) wprog with
        | mk wRes wMid =>
          rw [hwRun] at hrun1
          cases wRes with
          | some wr =>
            cases wr with
            | returned rv =>
              have hno := hno_while_ret s1.clock s1 rv (le_refl _)
              have hwRun' : evaluateHOLFiniteState s1 wprog = (some (.returned rv), wMid) := hwRun
              rw [hwRun'] at hno
              exact False.elim (hno rfl)
            | _ => simp at hrun1
          | none =>
            dsimp only at hrun1
            have hwNorm : (evaluateHOLFiniteState s1 wprog).1 = none := by
              have hwRun' : evaluateHOLFiniteState s1 wprog = (none, wMid) := hwRun
              rw [hwRun']
            obtain ⟨_, d, hd, rfl, hn'⟩ :=
              rlp_be_len_while_normal 8 s1 vw 0#64 hv hn1 vw.isLt hwNorm
            have hwRun' : evaluateHOLFiniteState s1 wprog = (none, wMid) := hwRun
            rw [hwRun'] at hn'
            dsimp only at hn'
            have hret : evaluateHOLFiniteState wMid (.return (.var .local (ofString "n"))) =
                (some (.returned (.val (.word (0#64 + BitVec.ofNat 64 d)))),
                  wMid.emptyLocalsHOLFinite) := by
              simp [evaluateHOLFiniteState_return, evalHOLExact, lookupKvarHOLExact, hn',
                shapeOfHOLExact, sizeOfShapeWithContextHOL]
            rw [hret] at hrun1
            cases hrun1
            refine ⟨0#64 + BitVec.ofNat 64 d, rfl, ?_⟩
            simp only [BitVec.zero_add, BitVec.toNat_ofNat]
            omega

private theorem rlp_write_header_body_returns_le9 {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (retVal : ValueHOL 64)
    (hcode : state.code = originalRuntimeCode)
    (hrun : evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_rlp_write_header) =
      (some (.returned retVal), post)) :
    WordBound_rlp 9 retVal := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_write_header,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    at hrun
  let iteProg : ProgHOL 64 :=
    .ite (.cmp .notLower (.const 55#64) (.var .local (ofString "n")))
      (.seq
        (.storeByte (.var .local (ofString "dst"))
          (.op .add [.var .local (ofString "base"), .var .local (ofString "n")]))
        (.return (.const 1#64)))
      .skip
  rw [evaluateHOLFiniteState_seq_line780] at hrun
  cases hiteRun : evaluateHOLFiniteState state iteProg with
  | mk iRes iMid =>
    rw [hiteRun] at hrun
    cases iRes with
    | some ir =>
      dsimp only at hrun
      cases hrun
      simp only [iteProg, evaluateHOLFiniteState_ite] at hiteRun
      split at hiteRun
      · split at hiteRun
        · rw [evaluateHOLFiniteState_skip] at hiteRun
          simp at hiteRun
        · rw [evaluateHOLFiniteState_seq_line780] at hiteRun
          cases hst : evaluateHOLFiniteState state
              (.storeByte (.var .local (ofString "dst"))
                (.op .add [.var .local (ofString "base"), .var .local (ofString "n")])) with
          | mk sRes sMid =>
            rw [hst] at hiteRun
            cases sRes with
            | none =>
              dsimp only at hiteRun
              have hret1 : evaluateHOLFiniteState sMid (.return (.const 1#64)) =
                  (some (.returned (.val (.word 1#64))), sMid.emptyLocalsHOLFinite) := by
                simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact,
                  sizeOfShapeWithContextHOL]
              rw [hret1] at hiteRun
              cases hiteRun
              exact ⟨1#64, rfl, by decide⟩
            | some sr =>
              have hno := storeByte_not_returned state
                (.var .local (ofString "dst"))
                (.op .add [.var .local (ofString "base"), .var .local (ofString "n")])
                retVal
              rw [hst] at hno
              dsimp only at hiteRun hno
              cases hiteRun
              exact absurd rfl hno
      · simp at hiteRun
    | none =>
      dsimp only at hrun
      have hmeta0 := PanRunBounded.evaluateHOLFiniteState_metadata state iteProg
      rw [hiteRun] at hmeta0
      dsimp only at hmeta0
      have hiCode : iMid.code = originalRuntimeCode := hmeta0.1.trans hcode
      obtain ⟨vs, b, loc, rs, w, bPost, inner1, _, hlk, hbRun, hcont⟩ :=
        decCall_returned_inv_rlp hrun
      have hbEq := lookupCodeHOLFinite_installed_body iMid.code.lookup (ofString "rlp_be_len")
        _ _ b _ rs vs loc (by rw [hiCode]; exact lookup_rlp_be_len) hlk
      subst hbEq
      obtain ⟨llW, rfl, hllLe⟩ := rlp_be_len_body_returns_le8
        (callEntryStateHOLFinite iMid loc) bPost w hbRun
      let s1 := setVarHOLFinite (ofString "ll") (.val (.word llW))
        {bPost with locals := iMid.locals}
      have hll1 : s1.locals.lookup (ofString "ll") = some (.val (.word llW)) := by
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      let pfx : ProgHOL 64 :=
        .seq
          (.storeByte (.var .local (ofString "dst"))
            (.op .add [.var .local (ofString "base"), .const 55#64,
              .var .local (ofString "ll")]))
          (.call (some (none, none)) (ofString "rlp_put_be")
            [.op .add [.var .local (ofString "dst"), .const 1#64],
              .var .local (ofString "n"), .var .local (ofString "ll")])
      have hcont1 : (evaluateHOLFiniteState s1
          (.seq pfx (.return (.op .add [.const 1#64, .var .local (ofString "ll")])))).1 =
          some (.returned retVal) := by
        have heq : evaluateHOLFiniteState s1
            (.seq pfx (.return (.op .add [.const 1#64, .var .local (ofString "ll")]))) =
            evaluateHOLFiniteState
              (setVarHOLFinite (ofString "ll") (.val (.word llW)) {bPost with locals := iMid.locals})
              (.seq
                (.storeByte (.var .local (ofString "dst"))
                  (.op .add [.var .local (ofString "base"), .const 55#64,
                    .var .local (ofString "ll")]))
                (.seq
                  (.call (some (none, none)) (ofString "rlp_put_be")
                    [.op .add [.var .local (ofString "dst"), .const 1#64],
                      .var .local (ofString "n"), .var .local (ofString "ll")])
                  (.return (.op .add [.const 1#64, .var .local (ofString "ll")])))) := by
          change evaluateHOLFiniteState s1 (.seq pfx _) = _
          simp only [s1, pfx, evaluateHOLFiniteState_seq_line780]
          rcases evaluateHOLFiniteState
              (setVarHOLFinite (ofString "ll") (.val (.word llW)) {bPost with locals := iMid.locals})
              (.storeByte (.var .local (ofString "dst"))
                (.op .add [.var .local (ofString "base"), .const 55#64,
                  .var .local (ofString "ll")])) with ⟨_ | rA, mA⟩ <;> rfl
        rw [heq, hcont]
      have hframe := evaluate_avoidsLocal_flowing (ofString "ll") pfx (by decide) s1
      have hnoRet : (evaluateHOLFiniteState s1 pfx).1 ≠ some (.returned retVal) := by
        dsimp only [pfx]
        rw [evaluateHOLFiniteState_seq_line780]
        rcases hst : evaluateHOLFiniteState s1
            (.storeByte (.var .local (ofString "dst"))
              (.op .add [.var .local (ofString "base"), .const 55#64,
                .var .local (ofString "ll")])) with ⟨rA, mA⟩
        cases rA with
        | none => exact call_void_not_returned mA _ _ retVal
        | some rA' =>
          have hno := storeByte_not_returned s1
            (.var .local (ofString "dst"))
            (.op .add [.var .local (ofString "base"), .const 55#64, .var .local (ofString "ll")])
            retVal
          rw [hst] at hno
          exact hno
      rw [evaluateHOLFiniteState_seq_line780] at hcont1
      cases hpRun : evaluateHOLFiniteState s1 pfx with
      | mk pRes pMid =>
        rw [hpRun] at hcont1 hframe hnoRet
        dsimp only at hcont1 hframe hnoRet
        cases pRes with
        | some pr => exact absurd hcont1 hnoRet
        | none =>
          dsimp only at hcont1
          have hllMid : pMid.locals.lookup (ofString "ll") = some (.val (.word llW)) :=
            (hframe (Or.inl rfl)).trans hll1
          have hretEq : evaluateHOLFiniteState pMid
              (.return (.op .add [.const 1#64, .var .local (ofString "ll")])) =
              (some (.returned (.val (.word (1#64 + llW)))), pMid.emptyLocalsHOLFinite) := by
            simp [evaluateHOLFiniteState_return, evalHOLExact, evalListHOLExact, hllMid,
              wordOpHOL, wordOp, valueIsWord, valueWord, shapeOfHOLExact,
              sizeOfShapeWithContextHOL]
          rw [hretEq] at hcont1
          cases hcont1
          refine ⟨1#64 + llW, rfl, ?_⟩
          have h264 : 2 ^ 64 = 18446744073709551616 := rfl
          have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
          rw [BitVec.toNat_add_of_lt (by omega), h1]
          omega

/-- `rlp_encode_bytes` (AST line 4768): returns at most `n + 9` (header and payload; value
contract). -/
theorem rv_rlp_encode_bytes :
    RetLe_rlp (fun s => locN s "n" + 9) (ofString "rlp_encode_bytes") := by
  refine ⟨_, (sourceFunctionEntry Guest.Software.guestFn_rlp_encode_bytes).2.2.1, _,
    lookup_rlp_encode_bytes, ?_⟩
  intro F state hcode _ _ _ v hv
  rcases hpair : evaluateHOLFiniteState state
      (sourceFunctionEntry Guest.Software.guestFn_rlp_encode_bytes).2.2.1 with ⟨res, post⟩
  rw [hpair] at hv
  dsimp only at hv
  subst hv
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_rlp_encode_bytes,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    List.map] at hpair
  let iteProg : ProgHOL 64 :=
    .ite (.cmp .equal (.var .local (ofString "n")) (.const 1#64))
      (.dec (ofString "b") .one (.loadByte (.var .local (ofString "src")))
        (.ite (.cmp .lower (.var .local (ofString "b")) (.const 128#64))
          (.seq
            (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "b")))
            (.return (.const 1#64)))
          .skip))
      .skip
  rw [evaluateHOLFiniteState_seq_line780] at hpair
  cases hiteRun : evaluateHOLFiniteState state iteProg with
  | mk iRes iMid =>
    rw [hiteRun] at hpair
    cases iRes with
    | some ir =>
      dsimp only at hpair
      cases hpair
      simp only [iteProg, evaluateHOLFiniteState_ite] at hiteRun
      split at hiteRun
      · split at hiteRun
        · rw [evaluateHOLFiniteState_skip] at hiteRun
          simp at hiteRun
        · rw [evaluateHOLFiniteState_dec_total] at hiteRun
          dsimp only at hiteRun
          split at hiteRun
          · simp at hiteRun
          · split at hiteRun
            · rename_i bVal _ _
              let sb := setVarHOLFinite (ofString "b") bVal state
              rw [evaluateHOLFiniteState_ite] at hiteRun
              split at hiteRun
              · split at hiteRun
                · rw [evaluateHOLFiniteState_skip] at hiteRun
                  simp at hiteRun
                · rw [evaluateHOLFiniteState_seq_line780] at hiteRun
                  cases hst : evaluateHOLFiniteState sb
                      (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "b"))) with
                  | mk sRes sMid =>
                    rw [hst] at hiteRun
                    cases sRes with
                    | none =>
                      dsimp only at hiteRun
                      have hret1 : evaluateHOLFiniteState sMid (.return (.const 1#64)) =
                          (some (.returned (.val (.word 1#64))), sMid.emptyLocalsHOLFinite) := by
                        simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact,
                          sizeOfShapeWithContextHOL]
                      rw [hret1] at hiteRun
                      simp only [Prod.mk.injEq, Option.some.injEq,
                        PanSemResultExact.returned.injEq] at hiteRun
                      exact ⟨1#64, hiteRun.1.symm, by change 1 ≤ locN state "n" + 9; omega⟩
                    | some sr =>
                      have hno := storeByte_not_returned sb
                        (.var .local (ofString "dst")) (.var .local (ofString "b")) v
                      rw [hst] at hno
                      dsimp only at hiteRun hno
                      simp only [Prod.mk.injEq] at hiteRun
                      exact absurd hiteRun.1 hno
              · simp at hiteRun
            · simp at hiteRun
      · simp at hiteRun
    | none =>
      dsimp only at hpair
      have hmeta0 := PanRunBounded.evaluateHOLFiniteState_metadata state iteProg
      have hframe0 := evaluate_avoidsLocal_flowing (ofString "n") iteProg (by decide) state
      rw [hiteRun] at hmeta0 hframe0
      dsimp only at hmeta0 hframe0
      have hiCode : iMid.code = originalRuntimeCode := hmeta0.1.trans hcode
      have hiN : iMid.locals.lookup (ofString "n") = state.locals.lookup (ofString "n") :=
        hframe0 (Or.inl rfl)
      obtain ⟨vs, b, loc, rs, w, bPost, inner1, hargs, hlk, hbRun, hcont⟩ :=
        decCall_returned_inv_rlp hpair
      have hbEq := lookupCodeHOLFinite_installed_body iMid.code.lookup (ofString "rlp_write_header")
        _ _ b _ rs vs loc (by rw [hiCode]; exact lookup_rlp_write_header) hlk
      subst hbEq
      obtain ⟨hw, rfl, hhwLe⟩ := rlp_write_header_body_returns_le9
        (callEntryStateHOLFinite iMid loc) bPost w hiCode hbRun
      let s1 := setVarHOLFinite (ofString "h") (.val (.word hw))
        {bPost with locals := iMid.locals}
      have hh1 : s1.locals.lookup (ofString "h") = some (.val (.word hw)) := by
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hn1 : s1.locals.lookup (ofString "n") = state.locals.lookup (ofString "n") := by
        have hne : ofString "h" ≠ ofString "n" := by decide
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hiN]
      let mcCall : ProgHOL 64 :=
        .call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
            .var .local (ofString "src"), .var .local (ofString "n")]
      have hcont1 : (evaluateHOLFiniteState s1
          (.seq mcCall (.return (.op .add [.var .local (ofString "h"), .var .local (ofString "n")])))).1 =
          some (.returned v) := by
        have heq := (Prod.mk.inj hcont).1
        exact heq
      have hframe_h := evaluate_avoidsLocal_flowing (ofString "h") mcCall (by decide) s1
      have hframe_n := evaluate_avoidsLocal_flowing (ofString "n") mcCall (by decide) s1
      have hnoRet := call_void_not_returned s1 (ofString "memcpy")
        [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
          .var .local (ofString "src"), .var .local (ofString "n")] v
      rw [evaluateHOLFiniteState_seq_line780] at hcont1
      cases hmcRun : evaluateHOLFiniteState s1 mcCall with
      | mk mcRes mcMid =>
        rw [hmcRun] at hcont1 hframe_h hframe_n hnoRet
        dsimp only at hcont1 hframe_h hframe_n hnoRet
        cases mcRes with
        | some mr => exact absurd hcont1 hnoRet
        | none =>
          dsimp only at hcont1
          have hhMid : mcMid.locals.lookup (ofString "h") = some (.val (.word hw)) :=
            (hframe_h (Or.inl rfl)).trans hh1
          have hnMid : mcMid.locals.lookup (ofString "n") = state.locals.lookup (ofString "n") :=
            (hframe_n (Or.inl rfl)).trans hn1
          rw [evaluateHOLFiniteState_return] at hcont1
          rcases hn_st : state.locals.lookup (ofString "n") with _ | nv
          · simp [evalHOLExact, evalListHOLExact, lookupKvarHOLExact, hhMid, hnMid, hn_st] at hcont1
          · rcases nv with ⟨⟨nw⟩⟩ | _ | _
            · have hlocN : locN state "n" = nw.toNat := by simp [locN, hn_st]
              simp [evalHOLExact, evalListHOLExact, lookupKvarHOLExact, hhMid, hnMid, hn_st,
                wordOpHOL, wordOp, valueIsWord, valueWord, shapeOfHOLExact,
                sizeOfShapeWithContextHOL] at hcont1
              refine ⟨hw + nw, hcont1.symm, ?_⟩
              dsimp only
              rw [hlocN]
              have hle : (hw + nw).toNat ≤ hw.toNat + nw.toNat := by
                rw [BitVec.toNat_add]
                exact Nat.mod_le _ _
              omega
            · simp [evalHOLExact, evalListHOLExact, lookupKvarHOLExact, hhMid, hnMid, hn_st,
                valueIsWord] at hcont1
            · simp [evalHOLExact, evalListHOLExact, lookupKvarHOLExact, hhMid, hnMid, hn_st,
                valueIsWord] at hcont1

end InitECandidate.Solver.Wave8Contracts.M27
