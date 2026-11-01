import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.MptDeleteLeafSupport
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

private theorem leafStraight (p : ProgHOL 64) (hs : extStraightLine p = true) :
    TerminatingProgBoundedOn GuestInv p 0 :=
  fun s hc _ => TerminatingProgBounded.straight p hs s hc

private theorem leafDec {name : MlS} {shape : ShapeHOL} {e : ExpHOL 64}
    {p : ProgHOL 64} {b : Nat} (h : TerminatingProgBoundedOn GuestInv p b) :
    TerminatingProgBoundedOn GuestInv (.dec name shape e p) b :=
  TerminatingProgBoundedOn.dec_on localsFree_guestInv name shape e h

private theorem leafCall {name : MlS} {b : Nat} {dst : Option (VarKind × MlS)}
    {args : List (ExpHOL 64)} (h : TerminatingFunBoundedOn GuestInv name b) :
    TerminatingProgBoundedOn GuestInv (.call (some (dst, none)) name args) (b + 1) :=
  TerminatingProgBoundedOn.call_guestInv h dst args

private theorem leafDecCall {name fname : MlS} {shape : ShapeHOL} {args : List (ExpHOL 64)}
    {p : ProgHOL 64} {b c : Nat} (h : TerminatingFunBoundedOn GuestInv fname b)
    (hp : TerminatingProgBoundedOn GuestInv p c) :
    TerminatingProgBoundedOn GuestInv (.decCall name shape fname args p) (b + c + 1) :=
  TerminatingProgBoundedOn.decCall_guestInv h name shape args hp

syntax "delete_bound" : tactic
macro_rules
  | `(tactic| delete_bound) => `(tactic| (first
      | assumption
      | exact leafStraight _ rfl
      | apply TerminatingProgBoundedOn.seq_guestInv
      | apply TerminatingProgBoundedOn.ite_on
      | apply leafDec
      | apply leafCall
      | apply leafDecCall) <;> delete_bound)

private theorem deleteBody_bound (h : MptDeleteCallees) :
    TerminatingProgBoundedOn GuestInv mptDeleteBody mptDeleteCost := by
  have h1 := h.fb__collapse_branch
  have h2 := h.fb__delete_ext_finish
  have h3 := h.fb_common_prefix_length
  have h4 := h.fb_memeq
  have h5 := h.fb_mpt_fail
  have h6 := h.fb_node_invalidate
  have h7 := h.fb_scratch_alloc
  apply TerminatingProgBoundedOn.mono_bound
  · simp only [mptDeleteBody, mptDeleteTail, mptDeleteCode, mptDecBody, mptWhileBody,
      mptLeft, sourceFunctionEntry, Guest.Software.guestFn__mpt_delete_node_body,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
    delete_bound
  · simp only [mptDeleteCost, Nat.zero_add, Nat.add_zero, Nat.zero_max,
      Nat.max_zero, Nat.add_assoc]
    simp only [Nat.add_left_comm]
    exact Nat.le_refl _

private def DeleteEntry (node top : Nat) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => DeleteSaved node top s ∧ locN s "node" = node ∧ locN s "top" = top ∧ memW s node = 1

private def DeleteStarted (node top : Nat) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => DeleteEntry node top s ∧ locN s "go" = 0

private theorem deleteLeaf_walk (h : MptDeleteCallees) (node top : Nat) (hz : node ≠ 0) :
    DeleteTriple (DeleteEntry node top) mptDeleteBody (DeleteLeafOut node top) := by
  simp only [mptDeleteBody, mptDeleteTail, mptDeleteCode, mptDecBody, mptWhileBody,
    mptLeft, sourceFunctionEntry, Guest.Software.guestFn__mpt_delete_node_body,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  apply DeleteTriple.seq (R := DeleteStarted node top)
  · apply DeleteTriple.assign
    intro F t v hp hv
    cases evalAt_const t 0 v hv
    refine ⟨⟨deleteSaved_locals node top t _ t.clock hp.1, ?_, ?_, hp.2.2.2⟩, ?_⟩
    · rw [locN_setVar_ne t "node" _ _ (by decide)]; exact hp.2.1
    · rw [locN_setVar_ne t "top" _ _ (by decide)]; exact hp.2.2.1
    · rw [locN_setVar_same]; rfl
  · apply DeleteTriple.ite
    · apply DeleteTriple.of_false
      intro F t hp
      have he := deleteCond_eq_true hp.2
      exact hz (hp.1.1.2.1.symm.trans he)
    · apply DeleteTriple.dec (R := DeleteTagged node top) (names := ["top", "go", "res"])
        (by decide)
      · intro F t v hp hv
        obtain ⟨a, rfl, ha⟩ := deleteEval_loadL t "node" 0 v hv
        have hat : a.toNat = 1 := by
          change a.toNat = memW t (locN t "node" + 0) at ha
          rw [Nat.add_zero, hp.1.1.2.1] at ha
          exact ha.trans hp.1.1.2.2.2
        refine ⟨deleteSaved_locals node top t _ t.clock hp.1.1.1, ?_, ?_, ?_, ?_⟩
        · rw [locN_setVar_ne t "node" _ _ (by decide)]; exact hp.1.1.2.1
        · rw [locN_setVar_ne t "top" _ _ (by decide)]; exact hp.1.1.2.2.1
        · rw [locN_setVar_ne t "go" _ _ (by decide)]; exact hp.1.2
        · rw [locN_setVar_same]; exact hat
      · apply DeleteTriple.seq (R := DeleteTagged node top)
        · apply DeleteTriple.ite
          · apply DeleteTriple.of_false
            intro F t hp
            have he := deleteCond_eq_true hp.2
            have hk := hp.1.2.2.2.2
            simp only [BitVec.toNat_zero] at he
            omega
          · exact DeleteTriple.skip (fun _ hp => hp.1)
        · apply DeleteTriple.seq (deleteTagged_invalidate h node top)
          apply DeleteTriple.ite
          · apply DeleteTriple.seq (R := DeleteLeafOut node top)
            · apply DeleteTriple.assign
              intro F t v hp hv
              have ht := LocalsOnly.setVar (P := DeleteTagged node top)
                (deleteTagged_locals node top)
                (name := ofString "res") (by decide) v t hp.1
              exact ⟨ht.1, ht.2.2.1, ht.2.2.2.1,
                Or.inr ((deleteAssign_local t "res" "node" v hv).trans hp.1.2.1)⟩
            · apply DeleteTriple.ite
              · refine DeleteTriple.mono ?_ (fun _ hp => hp.1)
                apply DeleteTriple.decCall (R := DeleteLeafOut node top)
                  (names := ["top", "go", "res"])
                · exact ReadOnlyFn.resumeOn (deleteLeafOut_locals node top)
                    (fun _ hp => hp.1.1.1) h.ro_memeq _ (by decide) _
                · apply DeleteTriple.ite
                  · apply DeleteTriple.assign
                    intro F t v hp hv
                    cases evalAt_const t 0 v hv
                    refine ⟨deleteSaved_locals node top t _ t.clock hp.1.1, ?_, ?_, Or.inl ?_⟩
                    · rw [locN_setVar_ne t "top" _ _ (by decide)]; exact hp.1.2.1
                    · rw [locN_setVar_ne t "go" _ _ (by decide)]; exact hp.1.2.2.1
                    · rw [locN_setVar_same]; rfl
                  · exact DeleteTriple.skip (fun _ hp => hp.1)
                · exact deleteLeafOut_locals node top
                · decide
              · exact DeleteTriple.skip (fun _ hp => hp.1)
          · apply DeleteTriple.of_false
            intro F t hp
            exact deleteCond_eq_false hp.2 hp.1.2.2.2.2
      · exact deleteLeafOut_locals node top

private theorem deleteLeaf_post (h : MptDeleteCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode)
    (hp : MptDeleteActive s) (hk : mptKind s = 1) (hf : MptFlow s mptDeleteBody) :
    MptDeleteHead (evaluateHOLFiniteState s mptDeleteBody).2 ∧
      MptDeleteEffect s (evaluateHOLFiniteState s mptDeleteBody).2 := by
  have hz : locN s "node" ≠ 0 := by
    intro hz
    simp [mptKind, hz] at hk
  have htag : memW s (locN s "node") = 1 := by
    simpa only [mptKind, if_neg hz] using hk
  obtain ⟨Nd, fs, hn, hs, _, ha⟩ := hp.1.2
  have hm : locN s "node" ∈ Nd := ((ha hp.2).2.1).resolve_left hz
  have he : DeleteEntry (locN s "node") (locN s "top") s :=
    ⟨⟨hp.1.1, Nd, fs, hn, hs, hm⟩, rfl, rfl, htag⟩
  have hnt : (evaluateHOLFiniteState s mptDeleteBody).1 ≠ some .timeOut := by
    rcases hf with hf | hf <;> simp [hf]
  have hout := (deleteLeaf_walk h (locN s "node") (locN s "top") hz).run s hc he hnt
  have hdone : DeleteLeafOut (locN s "node") (locN s "top")
      (evaluateHOLFiniteState s mptDeleteBody).2 := by
    rcases hf with hf | hf
    · exact hout.2 hf
    · exact (hout.1 hf).elim
  obtain ⟨⟨ha', Nd', fs', hn', hs', hm'⟩, ht, hg, hr⟩ := hdone
  refine ⟨⟨ha', Nd', fs', hn', ?_, ?_, ?_⟩, Or.inl hg⟩
  · rw [ht]; exact hs'
  · rcases hr with hr | hr
    · exact Or.inl hr
    · exact Or.inr (hr ▸ hm')
  · intro hgo
    exact (hgo hg).elim

/-- One iteration with node tag 1; shard 0 includes the null-root case.
Prove the bound and the continuing-state effect. No other kind shard is imported. -/
theorem mptDelete_kind1 (h : MptDeleteCallees) :
    MptStepAt MptDeleteActive MptDeleteHead MptDeleteEffect mptDeleteBody mptDeleteCost 1 := by
  intro F s hc hp hk
  refine ⟨deleteBody_bound h s hc hp.1.1.1, ?_⟩
  intro hflow
  exact deleteLeaf_post h s hc hp hk hflow


end InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
