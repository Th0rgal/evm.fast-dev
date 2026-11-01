import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptInsertCountRank
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

/-- Counting only: consume already-proved one-iteration semantics. The proof must
charge cache warmups and bound finite zero-extension walks between strict level
increases; repeated warm cycles time out. The R10 key-length guard bounds the
level phases, and heap-relative parent slots give the stated 2^66 iteration budget. -/
theorem mptInsert_count
    (steps : MptSteps MptInsertActive MptInsertHead MptInsertEffect mptInsertBody mptInsertCost) :
    TerminatingProgBoundedOn MptInsertHead (.while mptGo mptInsertBody) mptInsertBudget := by
  have hdec {F : Type} (s : PanSemStateFiniteExact 64 F) (hs : MptInsertHead s) :
      MptInsertHead (decClockHOLFinite s) :=
    ⟨⟨guestInv_with_locals_clock s s.locals (s.clock - 1) hs.1.1, hs.1.2⟩, hs.2⟩
  let hloop : InitECandidate.Solver.Wave8Leaves.Rlp.PhasedLoop MptInsertHead MptInsertActive
      InsertCount.Frame InsertCount.phase InsertCount.key mptGo mptInsertBody mptInsertCost := {
    body_bound := fun s hc hs => (steps s hc hs).1
    entry := by
      intro F s w hc hs hw hn _
      exact ⟨hdec s hs, RunFramesRace.condTrue_local_ne0 ⟨w, hw, hn⟩⟩
    step := by
      intro F s w hc hs hw hn _
      dsimp only
      intro _ hflow
      have ha : MptInsertActive (decClockHOLFinite s) :=
        ⟨hdec s hs, RunFramesRace.condTrue_local_ne0 ⟨w, hw, hn⟩⟩
      obtain ⟨ht, he⟩ := (steps (decClockHOLFinite s) hc ha).2 hflow
      have hr : evaluateHOLFiniteState (decClockHOLFinite s) mptInsertBody =
          (none, (evaluateHOLFiniteState (decClockHOLFinite s) mptInsertBody).2) :=
        Prod.ext (InsertCount.body_flow_none _ hflow) rfl
      refine ⟨ht, ?_⟩
      rcases InsertCount.step_phase ha ht he hr with ⟨hp, hf⟩ | hp
      · exact Or.inl ⟨hp, ⟨hs, hf.head_t, hf.normal_s, hf.normal_t,
          hf.state, hf.level, hf.result, hf.other⟩⟩
      · exact Or.inr hp
    trans := InsertCount.frame_trans
    key := fun s t h _ _ hk => InsertCount.frame_key s t h hk }
  intro F s hc hs
  have hb := InitECandidate.Solver.Wave8Leaves.Rlp.TerminatingProgBoundedOn.while_phased
    (Φ := 2 ^ 36) hloop (fun t _ => InsertCount.phase_le t) s hc hs
  apply hb.weaken
  unfold mptInsertBudget
  apply Nat.mul_le_mul_right
  norm_num

/-- Only three constant declarations; tail is arbitrary. -/
theorem mptInsert_initialize {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn MptInsertHead tail b) :
    TerminatingProgBoundedOn MptInsertReady (mptInit "result" "slot" tail) b := by
  intro F s hc hs
  unfold mptInit TerminatingRunBounded
  simp only [evaluateHOLFiniteState_dec_total, evalHOLExact,
    shapeOfHOLExact, shapeEqHOL, if_true]
  let t := setVarHOLFinite (ofString "go") (.val (.word 1))
    (setVarHOLFinite (ofString "slot") (.val (.word 0))
      (setVarHOLFinite (ofString "result") (.val (.word 0)) s))
  have ha : ArenaReady t := RunFramesRace.localsFree_arenaReady s t.locals s.clock hs.1.1
  have hl (n : String) (h1 : ofString n ≠ ofString "go")
      (h2 : ofString n ≠ ofString "slot") (h3 : ofString n ≠ ofString "result") :
      locN t n = locN s n := by
    simp [t, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update,
      FUPDATE, Ne.symm h1, Ne.symm h2, Ne.symm h3]
  have ht : MptInsertHead t := by
    refine ⟨ha, fun _ => ?_⟩
    obtain ⟨⟨_, hlevel, Nd, hn, hr, hk, hlen⟩, hval⟩ := hs
    have hlevel' := hl "level" (by decide) (by decide) (by decide)
    have hklen := hl "klen" (by decide) (by decide) (by decide)
    have hnode := hl "node" (by decide) (by decide) (by decide)
    have hkey := hl "key" (by decide) (by decide) (by decide)
    have hvlen := hl "vlen" (by decide) (by decide) (by decide)
    refine ⟨by simpa only [hlevel', hklen] using hlevel, Nd, hn, ?_, ?_, Or.inl ?_, ?_, ?_⟩
    · simpa only [hnode] using hr
    · rw [hkey, hlevel', hklen]
      exact hk
    · change locN (setVarHOLFinite (ofString "go") (.val (.word 1)) _) "slot" = 0
      rw [locN_setVar_ne _ "slot" _ _ (by decide), locN_setVar_same]
      rfl
    · simpa only [hvlen] using hval
    · simpa only [hklen] using hlen
  exact htail t hc ht

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
