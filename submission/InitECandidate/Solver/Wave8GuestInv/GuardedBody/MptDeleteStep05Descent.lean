import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptCuts
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

private theorem deleteStack_clock {F : Type} (s : PanSemStateFiniteExact 64 F)
    (k : Nat) (Nd : List Nat) (fs : List Nat) (p : Nat) :
    MptStack { s with clock := k } Nd p fs ↔ MptStack s Nd p fs := by
  induction fs generalizing p with
  | nil => rfl
  | cons q qs ih =>
    simp only [MptStack, ih]
    rfl

private theorem deleteHead_decClock {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : MptDeleteHead s) : MptDeleteHead (decClockHOLFinite s) := by
  obtain ⟨ha, Nd, fs, hn, hs, hr, hk⟩ := h
  exact ⟨localsFree_arenaReady s s.locals (s.clock - 1) ha,
    Nd, fs, hn, (deleteStack_clock s (s.clock - 1) Nd fs _).2 hs, hr, hk⟩

/-- Normal exit retains the typed finite stack. The concrete body has no `break`,
so the step interface covers every iteration that can reach the continuation. -/
private theorem deleteLoop_head
    (steps : MptSteps MptDeleteActive MptDeleteHead MptDeleteEffect mptDeleteBody mptDeleteCost)
    {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hs : MptDeleteHead s)
    (hr : evaluateHOLFiniteState s (.while mptGo mptDeleteBody) = (none, post)) :
    MptDeleteHead post := by
  generalize hk : s.clock = k
  induction k using Nat.strongRecOn generalizing s with
  | ind k ih =>
    rw [evaluateHOLFiniteState_while_total] at hr
    split at hr
    · rename_i w hw
      split at hr
      · rename_i hwne
        split at hr
        · simp at hr
        · dsimp only at hr
          rw [fixClockHOLFinite_evaluateState] at hr
          have ha : LoopActive mptGo s := ⟨w, hw, hwne⟩
          have hg : locN (decClockHOLFinite s) "go" ≠ 0 :=
            RunFramesRace.condTrue_local_ne0 (loopActive_decClock ha)
          have hstep := (steps (decClockHOLFinite s) hc
            ⟨deleteHead_decClock s hs, hg⟩).2
          have hnb := GuestUniformClockBound.evaluate_noTopBreak mptDeleteBody rfl
            (decClockHOLFinite s)
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) mptDeleteBody
          have hmeta := (evaluateHOLFiniteState_metadata (decClockHOLFinite s) mptDeleteBody).1
          rcases hb : evaluateHOLFiniteState (decClockHOLFinite s) mptDeleteBody with ⟨r, mid⟩
          simp only [MptFlow, hb] at hstep hnb hr hrem hmeta
          have hlt : mid.clock < k := by
            change mid.clock ≤ s.clock - 1 at hrem
            omega
          have next (hf : r = none ∨ r = some .continue)
              (hloop : evaluateHOLFiniteState mid (.while mptGo mptDeleteBody) = (none, post)) :
              MptDeleteHead post :=
            ih mid.clock hlt mid (hmeta.trans hc) (hstep hf).1 hloop rfl
          cases r with
          | none => exact next (Or.inl rfl) hr
          | some r =>
            cases r with
            | «continue» => exact next (Or.inr rfl) hr
            | «break» => exact (hnb rfl).elim
            | _ => simp at hr
      · simp at hr
        obtain ⟨_, rfl⟩ := hr
        exact hs
    · simp at hr

/-- Count descent via strictly decreasing scratch_ptr on every continuing step.
The continuation receives a finite typed stack, even after a zero-extension cycle. -/
theorem mptDelete_descent
    (steps : MptSteps MptDeleteActive MptDeleteHead MptDeleteEffect mptDeleteBody mptDeleteCost)
    {tail : ProgHOL 64} {b : Nat} (htail : TerminatingProgBoundedOn MptUnwindHead tail b) :
    TerminatingProgBoundedOn MptDeleteHead (.seq (.while mptGo mptDeleteBody) tail)
      (mptDeleteBudget + b) := by
  let rank : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat :=
    fun s => if locN s "go" = 0 then 0 else globN s "scratch_ptr" + 1
  have hbody : TerminatingProgBoundedOn
      (fun s => MptDeleteHead s ∧ LoopActive mptGo s) mptDeleteBody mptDeleteCost :=
    fun s hc hs => (steps s hc ⟨hs.1, RunFramesRace.condTrue_local_ne0 hs.2⟩).1
  have hloop : TerminatingProgBoundedOn MptDeleteHead
      (.while mptGo mptDeleteBody) mptDeleteBudget := by
    apply TerminatingProgBoundedOn.while_rank_active (N := 2 ^ 130) rank
      deleteHead_decClock hbody
    · intro F s _ hs ha
      have hptr := hs.1.2.2.2.2.2.1
      change globN s "scratch_ptr" ≤ scratchEnd at hptr
      simp only [rank, if_neg (RunFramesRace.condTrue_local_ne0 ha)]
      norm_num [scratchEnd] at hptr ⊢
      omega
    · intro F s hc hs ha hf
      have hg : locN s "go" ≠ 0 := RunFramesRace.condTrue_local_ne0 ha
      obtain ⟨hp, he⟩ := (steps (decClockHOLFinite s) hc
        ⟨deleteHead_decClock s hs, hg⟩).2 hf
      refine ⟨hp, ?_⟩
      simp only [rank, if_neg hg]
      rcases he with hz | hdown
      · simp only [hz, if_pos]; omega
      · change globN (evaluateHOLFiniteState (decClockHOLFinite s) mptDeleteBody).2
          "scratch_ptr" + 40 ≤ globN s "scratch_ptr" at hdown
        split <;> omega
  intro F s hc hs hnt
  have hmeta := (evaluateHOLFiniteState_metadata s (.while mptGo mptDeleteBody)).1
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr : evaluateHOLFiniteState s (.while mptGo mptDeleteBody) with ⟨r, mid⟩
  simp only [hr] at hmeta hnt ⊢
  cases r with
  | none =>
    dsimp only at hnt ⊢
    obtain ⟨hspent, hkept⟩ := hloop s hc hs (by simp [hr])
    simp only [hr] at hspent hkept
    obtain ⟨ha, Nd, fs, hn, hstack, hres, _⟩ := deleteLoop_head steps s mid hc hs hr
    obtain ⟨ht, htk⟩ := htail mid (hmeta.trans hc) ⟨ha, Nd, fs, hn, hstack, hres⟩ hnt
    exact ⟨by omega, by omega⟩
  | some r =>
    dsimp only at hnt ⊢
    obtain ⟨hspent, hkept⟩ := hloop s hc hs (by simpa only [hr] using hnt)
    simp only [hr] at hspent hkept
    exact ⟨by omega, hkept⟩

private theorem delete_decConst {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (w : BitVec 64) {body : ProgHOL 64} {b : Nat}
    (h : TerminatingRunBounded (setVarHOLFinite name (.val (.word w)) s) body b) :
    TerminatingRunBounded s (.dec name .one (.const w) body) b := by
  intro hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true] at hnt ⊢
  exact h hnt

/-- Only three constant declarations; tail is arbitrary. -/
theorem mptDelete_initialize {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn MptDeleteHead tail b) :
    TerminatingProgBoundedOn MptReady (mptInit "top" "res" tail) b := by
  intro F s hc hs
  apply delete_decConst
  apply delete_decConst
  apply delete_decConst
  let s1 := setVarHOLFinite (ofString "top") (.val (.word 0)) s
  let s2 := setVarHOLFinite (ofString "res") (.val (.word 0)) s1
  let s3 := setVarHOLFinite (ofString "go") (.val (.word 1)) s2
  apply htail s3 hc
  have h1 : MptReady s1 := localsOnly_mptReady.setVar (by decide) _ s hs
  have h2 : MptReady s2 := localsOnly_mptReady.setVar (by decide) _ s1 h1
  have h3 : MptReady s3 := localsOnly_mptReady.setVar (by decide) _ s2 h2
  obtain ⟨ha, hl, Nd, hn, hr, hk⟩ := h3
  have htop : locN s3 "top" = 0 := by
    rw [RunFramesRace.locN_setVar_ne s2 "top" (ofString "go") _ (by decide),
      RunFramesRace.locN_setVar_ne s1 "top" (ofString "res") _ (by decide),
      RunFramesRace.locN_setVar_same]
    rfl
  have hres : locN s3 "res" = 0 := by
    rw [RunFramesRace.locN_setVar_ne s2 "res" (ofString "go") _ (by decide),
      RunFramesRace.locN_setVar_same]
    rfl
  exact ⟨ha, Nd, [], hn, htop, Or.inl hres, fun _ => ⟨hl, hr, hk⟩⟩


end InitECandidate.Solver.Wave8GuestInv.GuardedBody
