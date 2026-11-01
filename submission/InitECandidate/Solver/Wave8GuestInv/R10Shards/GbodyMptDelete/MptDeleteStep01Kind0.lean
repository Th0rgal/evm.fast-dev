import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.MptCuts
import InitECandidate.Solver.GuestTrapOutcomes

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

private theorem lookup_fail :
    originalRuntimeCode.lookup (ofString "mpt_fail") =
      some ([(ofString "code", .one)],
        .seq (.raise (ofString "MptErr") (.var .local (ofString "code")))
          (.return (.const 0)), .one) := by
  exact originalRuntimeCode_lookup_of_guestAst_getElem 246 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mpt_fail) rfl

/-- The installed failure function raises or errors; it cannot resume the descent.
Even a zero-clock call consumes at most one tick. -/
private theorem fail_run {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "mpt_fail") [.const 2])
    s.clock ≤ out.2.clock + 1 ∧ out.2.clock ≤ s.clock ∧
      out.1 ≠ none ∧ out.1 ≠ some .continue := by
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 2] = some [.val (.word 2)] := by
    rw [evalListHOLFinite_eq_toExact]
    rfl
  dsimp only
  rw [evaluateHOLFiniteState_call, hargs]
  dsimp only
  rw [hc, InitECandidate.Solver.GuestTrapAndLookup.pan_one_word_lookup
    originalRuntimeCode.lookup (ofString "mpt_fail") (ofString "code") _ 2 lookup_fail]
  dsimp only
  split
  · simp [emptyLocalsHOLFinite]
  · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_raise]
    simp only [evalHOLExact, callEntryStateHOLFinite,
      HolFiniteMapExact.lookup_update, FUPDATE, beq_self_eq_true, if_true]
    cases he : s.eshapes.lookup (ofString "MptErr") with
    | none =>
      simp [emptyLocalsHOLFinite]
      omega
    | some shape =>
      by_cases hv : ShapeHOL.one = shape
      · subst shape
        simp [shapeOfHOLExact, emptyLocalsHOLFinite]
        omega
      · simp [shapeOfHOLExact, hv, emptyLocalsHOLFinite]
        omega

private def kind0NonNull (tail : ProgHOL 64) : ProgHOL 64 :=
  .dec (ofString "k") .one
    (.load .one (.op .add [.var .local (ofString "node"), .const 0]))
    (.seq
      (.ite (.cmp .equal (.var .local (ofString "k")) (.const 0))
        (.call (some (none, none)) (ofString "mpt_fail") [.const 2]) .skip)
      tail)

/-- A zero tag stops before the arbitrary remainder of the non-null branch. -/
private theorem nonNull_run {F : Type} (s : PanSemStateFiniteExact 64 F)
    (tail : ProgHOL 64) (node : BitVec 64)
    (hc : s.code = originalRuntimeCode)
    (hn : s.locals.lookup (ofString "node") = some (.val (.word node)))
    (hm : s.memory node = .word 0) :
    let out := evaluateHOLFiniteState s (kind0NonNull tail)
    s.clock ≤ out.2.clock + 1 ∧ out.2.clock ≤ s.clock ∧
      out.1 ≠ none ∧ out.1 ≠ some .continue := by
  classical
  have hl : evalAt s
      (.load .one (.op .add [.var .local (ofString "node"), .const 0])) =
      if s.memaddrs node then some (.val (.word 0)) else none := by
    simp [evalAt, evalHOLExact, evalListHOLExact, hn,
      valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact, hm]
  dsimp only
  rw [kind0NonNull, evaluateHOLFiniteState_dec_total]
  dsimp only [evalAt] at hl
  dsimp only
  rw [hl]
  by_cases hd : s.memaddrs node
  · simp only [hd, if_true, shapeOfHOLExact, shapeEqHOL]
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
    have ht : evalAt (setVarHOLFinite (ofString "k") (.val (.word 0)) s)
        (.cmp .equal (.var .local (ofString "k")) (.const 0)) = some (.val (.word 1)) := by
      simp [evalAt, evalHOLExact, setVarHOLFinite,
        HolFiniteMapExact.lookup_update, FUPDATE, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    dsimp only [evalAt] at ht
    rw [ht]
    simp only [show (1 : BitVec 64) ≠ 0 by decide, if_false]
    have hf := fail_run (setVarHOLFinite (ofString "k") (.val (.word 0)) s) hc
    rcases hr : evaluateHOLFiniteState (setVarHOLFinite (ofString "k") (.val (.word 0)) s)
        (.call (some (none, none)) (ofString "mpt_fail") [.const 2]) with ⟨r, t⟩
    rw [hr] at hf
    cases r with
    | none => exact (hf.2.2.1 rfl).elim
    | some r => exact hf
  · simp [hd]

private def kind0Tail : ProgHOL 64 :=
  match mptDeleteBody with
  | .seq _ (.ite _ _ (.dec _ _ _ (.seq _ tail))) => tail
  | _ => .skip

/-- Expose only the prefix needed by this shard, retaining the exact AST tail. -/
private theorem kind0_ast : mptDeleteBody =
    .seq (.assign .local (ofString "go") (.const 0))
      (.ite (.cmp .equal (.var .local (ofString "node")) (.const 0))
        (.assign .local (ofString "res") (.const 0)) (kind0NonNull kind0Tail)) := rfl

private theorem stack_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (ls : HolFiniteMapExact MlS (ValueHOL 64)) (Nd : List Nat) :
    ∀ fs p, MptStack { s with locals := ls } Nd p fs ↔ MptStack s Nd p fs
  | [], _ => Iff.rfl
  | _ :: fs, _ => by
    simp only [MptStack, stack_locals s ls Nd fs]
    rfl

private def nullResult {F : Type} (s : PanSemStateFiniteExact 64 F) :=
  setVarHOLFinite (ofString "res") (.val (.word 0))
    (setVarHOLFinite (ofString "go") (.val (.word 0)) s)

private theorem nullResult_head {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hs : MptDeleteHead s) : MptDeleteHead (nullResult s) ∧
      MptDeleteEffect s (nullResult s) := by
  have hg : locN (nullResult s) "go" = 0 := by
    simp [nullResult, locN_setVar_ne, locN_setVar_same,
      show ofString "go" ≠ ofString "res" by decide]
  have hr : locN (nullResult s) "res" = 0 := by
    simp [nullResult, locN_setVar_same]
  have ht : locN (nullResult s) "top" = locN s "top" := by
    simp [nullResult, locN_setVar_ne,
      show ofString "top" ≠ ofString "res" by decide,
      show ofString "top" ≠ ofString "go" by decide]
  refine ⟨⟨?_, ?_⟩, Or.inl hg⟩
  · exact (arenaReady_with_locals s _ s.clock).2 hs.1
  · obtain ⟨Nd, fs, hn, hstack, _, _⟩ := hs.2
    refine ⟨Nd, fs, hn, ?_, ?_, ?_⟩
    · rw [ht]
      exact (stack_locals s _ Nd fs _).2 hstack
    · exact Or.inl hr
    · simp only [hg, ne_eq, not_true_eq_false, false_implies]

/-- All continuing kind-0 runs have the null-node result. Malformed locals and
failed loads are covered by the evaluator error cases. -/
private theorem kind0_run {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hk : mptKind s = 0) :
    let out := evaluateHOLFiniteState s mptDeleteBody
    s.clock ≤ out.2.clock + 1 ∧ out.2.clock ≤ s.clock ∧
      ((out.1 = none ∨ out.1 = some .continue) → out.2 = nullResult s) := by
  classical
  dsimp only
  rw [kind0_ast, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
  simp only [evalHOLExact]
  by_cases hv : isValidValueHOLFinite s .local (ofString "go") (.val (.word 0)) = true
  · simp only [hv, if_true, setKvarHOLFinite]
    rw [evaluateHOLFiniteState_ite]
    have hnode : (setVarHOLFinite (ofString "go") (.val (.word (0 : BitVec 64))) s).locals.lookup
        (ofString "node") = s.locals.lookup (ofString "node") := by
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "go" ≠ ofString "node" by decide]
    simp only [evalHOLExact, hnode]
    cases hn : s.locals.lookup (ofString "node") with
    | none => simp [setVarHOLFinite]
    | some v =>
      cases v with
      | val v =>
        cases v with
        | word node =>
          by_cases hz : node = 0
          · subst node
            simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
              beq_self_eq_true, if_true, show (1 : BitVec 64) ≠ 0 by decide, if_false]
            rw [evaluateHOLFiniteState_assign]
            simp only [evalHOLExact]
            split <;> simp [setKvarHOLFinite, nullResult, setVarHOLFinite]
          · have hnz : node.toNat ≠ 0 := by
              intro hzero
              exact hz (BitVec.eq_of_toNat_eq hzero)
            have htag : memW s node.toNat = 0 := by
              simpa [mptKind, locN, hn, hnz] using hk
            have hm : s.memory node = .word 0 := by
              cases he : s.memory node with
              | word w =>
                have hw : w.toNat = 0 := by simpa [memW, he] using htag
                have hw0 : w = 0 := BitVec.eq_of_toNat_eq hw
                simp [hw0]
            simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
              beq_iff_eq, hz, if_false, if_true]
            have hs := nonNull_run (setVarHOLFinite (ofString "go") (.val (.word 0)) s)
              kind0Tail node hc (hnode.trans hn) hm
            exact ⟨hs.1, hs.2.1, fun hr => (hr.elim hs.2.2.1 hs.2.2.2).elim⟩
      | rStruct vs => simp [setVarHOLFinite]
      | nStruct n vs => simp [setVarHOLFinite]
  · simp only [hv]
    simp

/-- One iteration with node tag 0; shard 0 includes the null-root case.
Prove the bound and the continuing-state effect. No other kind shard is imported. -/
theorem mptDelete_kind0 (h : MptDeleteCallees) :
    MptStepAt MptDeleteActive MptDeleteHead MptDeleteEffect mptDeleteBody mptDeleteCost 0 := by
  -- The actual failure body suffices; this shard needs no callee contracts.
  clear h
  intro F s hc hs hk
  have hr := kind0_run s hc hk
  refine ⟨?_, ?_⟩
  · intro _
    refine ⟨Nat.le_trans hr.1 (Nat.add_le_add_left ?_ _), hr.2.1⟩
    exact Nat.le_trans (Nat.le_add_left 1 K.node_invalidate)
      (Nat.le_trans (Nat.le_add_left (K.node_invalidate + 1) _)
        (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_max_right _ _)))
  · intro hf
    rw [hr.2.2 hf]
    exact nullResult_head s hs.1


end InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
