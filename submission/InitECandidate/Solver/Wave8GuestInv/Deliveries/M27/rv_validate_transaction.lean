import InitECandidate.Solver.Wave8GuestInv.Defs

/-! Value contract `rv_validate_transaction` for micro-shard `m27` (`wave8/contracts-m27`),
frozen revision 9 (`8a79d9f28`, tag `wave8-spec-frozen-r9`).

Imports only the light split module `InitECandidate.Solver.Wave8GuestInv.Defs`.
Restates `FunSpec` and `RetIntrinsic` verbatim from `campaign/specs-proposed/GuestInv.lean` @
`8a79d9f28` so they delta-reduce definitionally (`rfl`) to the spec statement in `Axioms.lean`.
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

/-- Outcome specification of a function body from its callee-entry state
(verbatim from `GuestInv.lean` @ `8a79d9f28`). -/
def FunSpec_vt (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
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

/-- Value contract (verbatim from `GuestInv.lean` @ `8a79d9f28`): `validate_transaction` returns
its intrinsic cost triple with regular part at most `2^24` (`TxErr 63` otherwise, AST 12667). -/
def RetIntrinsic (fname : MlS) : Prop :=
  FunSpec_vt GuestInv (fun _ r _ => ∀ v, r = some (.returned v) →
    ∃ a b c : BitVec 64, v = .rStruct [.val (.word a), .val (.word b), .val (.word c)] ∧
      a.toNat ≤ 16777216) fname

theorem lookup_validate_transaction :
    originalRuntimeCode.lookup (ofString "validate_transaction") =
      some ((sourceFunctionEntry Guest.Software.guestFn_validate_transaction).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 346 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_validate_transaction) rfl

private theorem shapeEq_one_word {v : ValueHOL 64}
    (h : shapeEqHOL .one (shapeOfHOLExact v) = true) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  rw [shapeEqHOL_eq_true] at h
  rcases v with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
  · exact ⟨w, rfl⟩
  · simp [shapeOfHOLExact] at h
  · simp [shapeOfHOLExact] at h

private theorem shapeEq_three_words {v : ValueHOL 64}
    (h : shapeEqHOL (.comb [.one, .one, .one]) (shapeOfHOLExact v) = true) :
    ∃ a b c : BitVec 64, v = .rStruct [.val (.word a), .val (.word b), .val (.word c)] := by
  rw [shapeEqHOL_eq_true] at h
  rcases v with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
  · simp [shapeOfHOLExact] at h
  · simp only [shapeOfHOLExact, ShapeHOL.comb.injEq] at h
    rcases fs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩⟩
    · simp at h
    · simp at h
    · simp at h
    · simp only [List.map, List.cons.injEq] at h
      obtain ⟨h0, h1, h2, _⟩ := h
      obtain ⟨a, rfl⟩ := shapeEq_one_word (shapeEqHOL_eq_true _ _ |>.mpr h0)
      obtain ⟨b, rfl⟩ := shapeEq_one_word (shapeEqHOL_eq_true _ _ |>.mpr h1)
      obtain ⟨c, rfl⟩ := shapeEq_one_word (shapeEqHOL_eq_true _ _ |>.mpr h2)
      exact ⟨a, b, c, rfl⟩
    · simp at h
  · simp [shapeOfHOLExact] at h

private theorem raise_not_returned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (exn : MlS) (e : ExpHOL 64) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s (.raise exn e)).1 ≠ some (.returned v) := by
  rw [evaluateHOLFiniteState_raise]
  split
  · dsimp only; split_ifs <;> simp
  · simp

private theorem raise_ne_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (exn : MlS) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.raise exn e)).1 ≠ none := by
  rw [evaluateHOLFiniteState_raise]
  split
  · dsimp only; split_ifs <;> simp
  · simp

private theorem seq_ite_raise_returned {F : Type} {s : PanSemStateFiniteExact 64 F}
    {cond : ExpHOL 64} {exn : MlS} {e : ExpHOL 64} {rest : ProgHOL 64} {v : ValueHOL 64}
    (h : (evaluateHOLFiniteState s (.seq (.ite cond (.raise exn e) .skip) rest)).1 =
      some (.returned v)) :
    @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) cond =
      some (.val (.word 0)) ∧
    (evaluateHOLFiniteState s rest).1 = some (.returned v) := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at h
  revert h
  split
  · rename_i w hw
    split
    · rename_i hz
      subst hz
      rw [evaluateHOLFiniteState_skip]
      dsimp only
      intro hrest
      exact ⟨hw, hrest⟩
    · intro h
      have hne := raise_not_returned s exn e v
      have hnn := raise_ne_none s exn e
      rcases hr : evaluateHOLFiniteState s (.raise exn e) with ⟨res, post⟩
      rw [hr] at h hne hnn
      cases res with
      | none => exact absurd rfl hnn
      | some r => exact absurd h hne
  · simp

private theorem seq_ite_ite_raise_returned {F : Type} {s : PanSemStateFiniteExact 64 F}
    {c1 c2 : ExpHOL 64} {exn : MlS} {e : ExpHOL 64} {rest : ProgHOL 64} {v : ValueHOL 64}
    (h : (evaluateHOLFiniteState s
      (.seq (.ite c1 (.ite c2 (.raise exn e) .skip) .skip) rest)).1 = some (.returned v)) :
    (evaluateHOLFiniteState s rest).1 = some (.returned v) := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at h
  revert h
  split
  · split
    · rw [evaluateHOLFiniteState_skip]; exact id
    · rw [evaluateHOLFiniteState_ite]
      split
      · split
        · rw [evaluateHOLFiniteState_skip]; exact id
        · intro h
          have hne := raise_not_returned s exn e v
          have hnn := raise_ne_none s exn e
          rcases hr : evaluateHOLFiniteState s (.raise exn e) with ⟨res, post⟩
          rw [hr] at h hne hnn
          cases res with
          | none => exact absurd rfl hnn
          | some r => exact absurd h hne
      · simp
  · simp

private theorem dec_returned {F : Type} {s : PanSemStateFiniteExact 64 F}
    {name : MlS} {sh : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64} {v : ValueHOL 64}
    (h : (evaluateHOLFiniteState s (.dec name sh init body)).1 = some (.returned v)) :
    ∃ val : ValueHOL 64,
      shapeEqHOL sh (shapeOfHOLExact val) = true ∧
      (evaluateHOLFiniteState (setVarHOLFinite name val s) body).1 = some (.returned v) := by
  rw [evaluateHOLFiniteState_dec_total] at h
  dsimp only at h
  revert h
  split
  · simp
  · rename_i val _
    split
    · rename_i hsh
      intro hbody
      exact ⟨val, hsh, hbody⟩
    · simp

private theorem decCall_returned {F : Type} {s : PanSemStateFiniteExact 64 F}
    {name : MlS} {sh : ShapeHOL} {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    {v : ValueHOL 64}
    (h : (evaluateHOLFiniteState s (.decCall name sh fname args cont)).1 = some (.returned v)) :
    ∃ (val : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      shapeEqHOL sh (shapeOfHOLExact val) = true ∧
      (evaluateHOLFiniteState (setVarHOLFinite name val { post with locals := s.locals }) cont).1 =
        some (.returned v) := by
  rcases hargs : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x)) args with
    _ | values
  · rw [evaluateHOLFiniteState_decCall_args_none s name sh fname args cont hargs] at h
    simp at h
  · rw [evaluateHOLFiniteState_decCall_total, hargs] at h
    dsimp only at h
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body, callee, retSh⟩
    · simp [hl] at h
    · rw [hl] at h
      dsimp only at h
      revert h
      split
      · simp
      · rw [fixClockHOLFinite_evaluateState]
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, post⟩
        dsimp only
        cases res with
        | none => simp
        | some r =>
          cases r with
          | returned rv =>
            dsimp only
            split
            · rename_i hsh
              intro hcont
              rw [Bool.and_eq_true, shapeEqHOL_eq_true] at hsh
              exact ⟨rv, post, shapeEqHOL_eq_true _ _ |>.mpr hsh.1.symm, hcont⟩
            · simp
          | _ => simp

/-- `validate_transaction` (AST line 12639): returns an intrinsic cost with regular part at most
`2^24` (value contract, checks 12667). -/
theorem rv_validate_transaction :
    RetIntrinsic (ofString "validate_transaction") := by
  refine ⟨_, _, _, lookup_validate_transaction, ?_⟩
  intro F s _ _ _ _ v hv
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_validate_transaction,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    List.map] at hv
  obtain ⟨icVal, post1, hicSh, hv⟩ := decCall_returned hv
  obtain ⟨a, b, c, rfl⟩ := shapeEq_three_words hicSh
  obtain ⟨gasVal, _, hv⟩ := dec_returned hv
  obtain ⟨_, hv⟩ := seq_ite_raise_returned hv
  obtain ⟨_, hv⟩ := seq_ite_raise_returned hv
  obtain ⟨_, hv⟩ := seq_ite_raise_returned hv
  have hv := seq_ite_ite_raise_returned hv
  have hic_mid : (setVarHOLFinite (ofString "gas") gasVal
      (setVarHOLFinite (ofString "ic")
        (.rStruct [.val (.word a), .val (.word b), .val (.word c)])
        { post1 with locals := s.locals })).locals.lookup (ofString "ic") =
      some (.rStruct [.val (.word a), .val (.word b), .val (.word c)]) := by
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "gas" ≠ ofString "ic" by decide]
  obtain ⟨hcmp63, hv⟩ := seq_ite_raise_returned hv
  have ha_le : a.toNat ≤ 16777216 := by
    simp [evalHOLExact, lookupKvarHOLExact, hic_mid,
      Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def] at hcmp63
    omega
  obtain ⟨_, hv⟩ := seq_ite_raise_returned hv
  obtain ⟨nonceVal, _, hv⟩ := dec_returned hv
  obtain ⟨fitsVal, post2, _, hv⟩ := decCall_returned hv
  obtain ⟨_, hv⟩ := seq_ite_raise_returned hv
  obtain ⟨_, hv⟩ := seq_ite_raise_returned hv
  have hic_end : (setVarHOLFinite (ofString "fits") fitsVal
      { post2 with locals := (setVarHOLFinite (ofString "nonce") nonceVal
        (setVarHOLFinite (ofString "gas") gasVal
          (setVarHOLFinite (ofString "ic")
            (.rStruct [.val (.word a), .val (.word b), .val (.word c)])
            { post1 with locals := s.locals }))).locals }).locals.lookup
      (ofString "ic") =
      some (.rStruct [.val (.word a), .val (.word b), .val (.word c)]) := by
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "fits" ≠ ofString "ic" by decide,
      show ofString "nonce" ≠ ofString "ic" by decide,
      show ofString "gas" ≠ ofString "ic" by decide]
  rw [evaluateHOLFiniteState_return] at hv
  simp [evalHOLExact, lookupKvarHOLExact, hic_end, shapeOfHOLExact,
    sizeOfShapeWithContextHOL] at hv
  exact ⟨a, b, c, hv.symm, ha_le⟩

end InitECandidate.Solver.Wave8Contracts.M27
