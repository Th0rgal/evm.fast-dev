import InitECandidate.Solver.PanTerminatingBounded

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
# `InitECandidate.Solver.PanTerminatingNoRepeat` — no-repeat (pigeonhole) bound for `while`

Step 0 contract item 4. A non-`.timeOut` run of `.while cond body` can never revisit a loop-head
state that agrees with an earlier loop head on everything but the clock: by clock irrelevance
(`Flapjack.panPropsEvaluateAddClockEq`, restated as `evaluate_clock_irrelevant`) both heads would
reach the same post-state with clocks differing by the ticks spent in between, which is at least
one. So if every loop head reachable by the body is determined (up to clock) by a key in `Fin N`,
the loop runs at most `N` iterations and consumes at most `N * (B + 1)` ticks.
-/

namespace InitECandidate.Solver.PanTerminatingNoRepeat

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded

/-- Clock irrelevance for non-`.timeOut` runs (contract item 4). This is Flapjack's exact port of
HOL `panProps$evaluate_add_clock_eq`, `Flapjack.panPropsEvaluateAddClockEq`; it is restated here
only to fix the name required by the contract. -/
theorem evaluate_clock_irrelevant {F : Type} (prog : ProgHOL 64)
    (state post : PanSemStateFiniteExact 64 F) (res : Option (PanSemResultExact 64)) (d : Nat)
    (hrun : evaluateHOLFiniteState state prog = (res, post)) (hnt : res ≠ some .timeOut) :
    evaluateHOLFiniteState { state with clock := state.clock + d } prog =
      (res, { post with clock := post.clock + d }) :=
  panPropsEvaluateAddClockEq prog state res post d ⟨hrun, hnt⟩

/-- A non-`.timeOut` run from `state` cannot have the same outcome as the run from a state that
differs only by having strictly more clock. -/
theorem evaluate_ne_of_clock_lt {F : Type} (prog : ProgHOL 64)
    (state upper : PanSemStateFiniteExact 64 F)
    (hupper : upper = { state with clock := upper.clock }) (hlt : state.clock < upper.clock)
    (hsame : evaluateHOLFiniteState upper prog = evaluateHOLFiniteState state prog)
    (hnt : (evaluateHOLFiniteState state prog).1 ≠ some .timeOut) : False := by
  rcases hrun : evaluateHOLFiniteState state prog with ⟨res, post⟩
  rw [hrun] at hsame hnt
  have hadd := evaluate_clock_irrelevant prog state post res (upper.clock - state.clock) hrun hnt
  have hshift : ({ state with clock := state.clock + (upper.clock - state.clock) } :
      PanSemStateFiniteExact 64 F) = upper := by
    have hsum : state.clock + (upper.clock - state.clock) = upper.clock := by omega
    rw [hsum]
    exact hupper.symm
  rw [hshift, hsame] at hadd
  have hclk := congrArg (fun out => out.2.clock) hadd
  dsimp only at hclk
  omega

/-- One continuing iteration of `.while` hands the rest of the run to the body's post-state. -/
theorem while_unfold_continue {F : Type} (condition : ExpHOL 64) (body : ProgHOL 64)
    (state : PanSemStateFiniteExact 64 F) (word : BitVec 64)
    (hcond : evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      condition = some (.val (.word word)))
    (hword : word ≠ 0) (hclock : state.clock ≠ 0)
    (hflow : (evaluateHOLFiniteState (decClockHOLFinite state) body).1 = none ∨
      (evaluateHOLFiniteState (decClockHOLFinite state) body).1 = some .continue) :
    evaluateHOLFiniteState state (.while condition body) =
      evaluateHOLFiniteState (evaluateHOLFiniteState (decClockHOLFinite state) body).2
        (.while condition body) := by
  rw [evaluateHOLFiniteState_while_fixClockRewrite]
  simp only [hcond, if_pos hword, if_neg hclock]
  rcases hb : evaluateHOLFiniteState (decClockHOLFinite state) body with ⟨r, post⟩
  rw [hb] at hflow
  rcases hflow with h | h <;> (dsimp only at h; subst h; rfl)

section NoRepeat

/-- A loop head is active when the `while` condition evaluates to a nonzero word, i.e. the loop
is about to run its body (or time out). -/
def LoopActive (condition : ExpHOL 64) {F : Type} (state : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ word : BitVec 64,
    evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      condition = some (.val (.word word)) ∧ word ≠ 0

variable (P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
  (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop)
  {N : Nat} (κ : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Fin N)
  (condition : ExpHOL 64) (body : ProgHOL 64) (B : Nat)

/-- Hypotheses of the no-repeat rule.
* `body` is bounded by `B` on `Q`, and `Q` holds on entry to every iteration from a `P` loop head;
* every continuing iteration (`none` / `continue`) from a `P` loop head `s` lands in a `P` loop
  head `t` with `R s t`, and `R` is transitive;
* `R`-related *active* loop heads with equal keys `κ` agree on every field except `clock`.
`R` is the frame of the loop: for a read-only loop whose only changing local is the word `x`,
`R s t` says that `t` agrees with `s` on every field except `clock` and the local `x`, and
`κ s` is the value of `x` as a `Fin (2 ^ 64)`. Only active heads need distinct keys, so the exit
head may hold anything in `x` (e.g. a label loaded from memory). -/
structure NoRepeatLoop : Prop where
  body_bound : TerminatingProgBoundedOn Q body B
  entry : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (word : BitVec 64),
    state.code = originalRuntimeCode → P state →
    evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      condition = some (.val (.word word)) →
    word ≠ 0 → state.clock ≠ 0 → Q (decClockHOLFinite state)
  step : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (word : BitVec 64),
    state.code = originalRuntimeCode → P state →
    evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      condition = some (.val (.word word)) →
    word ≠ 0 → state.clock ≠ 0 →
    let output := evaluateHOLFiniteState (decClockHOLFinite state) body
    output.1 ≠ some .timeOut → (output.1 = none ∨ output.1 = some .continue) →
      P output.2 ∧ R state output.2
  trans : ∀ {F : Type} (a b c : PanSemStateFiniteExact 64 F), R a b → R b c → R a c
  key : ∀ {F : Type} (a b : PanSemStateFiniteExact 64 F), R a b →
    LoopActive condition a → LoopActive condition b → κ a = κ b →
    b = { a with clock := b.clock }

variable {P Q R κ condition body B}

/-- Earlier active loop heads, one per visited key, each `R`-below `state`, with strictly more
clock and the same remaining `while` run as `state`. -/
def VisitedHeads (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop)
    (κ : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Fin N) (condition : ExpHOL 64)
    (body : ProgHOL 64) {F : Type} (state : PanSemStateFiniteExact 64 F)
    (visited : Finset (Fin N)) : Prop :=
  ∀ k ∈ visited, ∃ earlier : PanSemStateFiniteExact 64 F, κ earlier = k ∧ R earlier state ∧
    LoopActive condition earlier ∧ state.clock < earlier.clock ∧
    evaluateHOLFiniteState earlier (.while condition body) =
      evaluateHOLFiniteState state (.while condition body)

/-- No-repeat: an active loop head of a non-`.timeOut` run carries a fresh key. -/
theorem key_fresh (hloop : NoRepeatLoop P Q R κ condition body B)
    {F : Type} (state : PanSemStateFiniteExact 64 F) (visited : Finset (Fin N))
    (hact : LoopActive condition state) (hvis : VisitedHeads R κ condition body state visited)
    (hnt : (evaluateHOLFiniteState state (.while condition body)).1 ≠ some .timeOut) :
    κ state ∉ visited := by
  intro hmem
  obtain ⟨earlier, hk, hR, hactE, hlt, hsame⟩ := hvis _ hmem
  have heq := hloop.key earlier state hR hactE hact hk
  exact evaluate_ne_of_clock_lt _ state earlier (by rw [heq]) hlt hsame hnt

theorem card_insert_key_le {F : Type} (κ : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Fin N)
    (state : PanSemStateFiniteExact 64 F) (visited : Finset (Fin N)) (hfresh : κ state ∉ visited) :
    visited.card + 1 ≤ N := by
  have hle : (insert (κ state) visited).card ≤ N := by
    simpa using Finset.card_le_univ (insert (κ state) visited)
  rwa [Finset.card_insert_of_notMem hfresh] at hle

/-- Induction core: `n` bounds the number of keys not yet visited. -/
theorem while_noRepeat_aux (hloop : NoRepeatLoop P Q R κ condition body B) :
    ∀ (n : Nat) {F : Type} (state : PanSemStateFiniteExact 64 F) (visited : Finset (Fin N)),
      state.code = originalRuntimeCode → P state → N ≤ visited.card + n →
      VisitedHeads R κ condition body state visited →
      TerminatingRunBounded state (.while condition body) (n * (B + 1)) := by
  intro n
  induction n with
  | zero =>
    intro F state visited hcode hP hcard hvis hnt
    have hnt0 := hnt
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    split
    · rename_i word hword
      simp only [hword] at hnt
      by_cases hzero : word = 0
      · rw [if_neg (by simp [hzero])]; exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
      · have hfresh := key_fresh hloop state visited ⟨word, hword, hzero⟩ hvis hnt0
        have := card_insert_key_le κ state visited hfresh
        omega
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  | succ n ih =>
    intro F state visited hcode hP hcard hvis hnt
    have hone : B + 1 ≤ (n + 1) * (B + 1) := Nat.le_mul_of_pos_left _ (by omega)
    have hnt0 := hnt
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    split
    · rename_i word hword
      simp only [hword] at hnt
      by_cases hzero : word = 0
      · rw [if_neg (by simp [hzero])]; exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
      · rw [if_pos hzero] at hnt ⊢
        by_cases hclock : state.clock = 0
        · rw [if_pos hclock] at hnt; exact absurd rfl hnt
        · rw [if_neg hclock] at hnt ⊢
          have hact : LoopActive condition state := ⟨word, hword, hzero⟩
          have hfresh := key_fresh hloop state visited hact hvis hnt0
          have hQ := hloop.entry state word hcode hP hword hzero hclock
          have hb := hloop.body_bound (decClockHOLFinite state) hcode hQ
          have hstep := hloop.step state word hcode hP hword hzero hclock
          have hunfold := while_unfold_continue condition body state word hword hzero hclock
          have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
            (decClockHOLFinite state) body).1
          unfold TerminatingRunBounded at hb
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite state) body with ⟨result, post⟩
          simp only [hrun] at hnt hb hstep hunfold hmeta
          dsimp only at hb hstep hunfold hmeta hnt ⊢
          change post.code = state.code at hmeta
          have hcont (hflow : result = none ∨ result = some .continue) :
              state.clock ≤ (evaluateHOLFiniteState post (.while condition body)).2.clock +
                (n + 1) * (B + 1) ∧
              (evaluateHOLFiniteState post (.while condition body)).2.clock ≤ state.clock := by
            have hsafe : result ≠ some .timeOut := by
              rcases hflow with h | h <;> simp [h]
            obtain ⟨hspent, hkept⟩ := hb hsafe
            change state.clock - 1 ≤ post.clock + B at hspent
            change post.clock ≤ state.clock - 1 at hkept
            obtain ⟨hPpost, hRpost⟩ := hstep hsafe hflow
            have hsame := hunfold hflow
            have hntPost : (evaluateHOLFiniteState post (.while condition body)).1 ≠
                some .timeOut := by
              rw [← hsame]; exact hnt0
            obtain ⟨htail, htailKept⟩ := ih post (insert (κ state) visited)
              (hmeta.trans hcode) hPpost
              (by rw [Finset.card_insert_of_notMem hfresh]; omega)
              (by
                intro k hk
                rcases Finset.mem_insert.mp hk with rfl | hk
                · exact ⟨state, rfl, hRpost, hact, by omega, hsame⟩
                · obtain ⟨earlier, hke, hRe, hactE, hlt, hsameE⟩ := hvis k hk
                  exact ⟨earlier, hke, hloop.trans _ _ _ hRe hRpost, hactE, by omega,
                    hsameE.trans hsame⟩)
              hntPost
            have hmul : n * (B + 1) + (B + 1) = (n + 1) * (B + 1) := by
              rw [Nat.succ_mul]
            exact ⟨by omega, by omega⟩
          cases result with
          | none => exact hcont (Or.inl rfl)
          | some r =>
            cases r with
            | «continue» => exact hcont (Or.inr rfl)
            | timeOut => exact absurd rfl hnt
            | _ =>
              obtain ⟨hspent, hkept⟩ := hb (by simp)
              change state.clock - 1 ≤ post.clock + B at hspent
              change post.clock ≤ state.clock - 1 at hkept
              simp only
              exact ⟨by omega, by omega⟩
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

/-- No-repeat rule, sharp form: at most `N` iterations, each costing at most `B + 1`. -/
theorem TerminatingProgBoundedOn.while_noRepeat_sharp
    (hloop : NoRepeatLoop P Q R κ condition body B) :
    TerminatingProgBoundedOn P (.while condition body) (N * (B + 1)) :=
  fun state hcode hP =>
    while_noRepeat_aux hloop N state ∅ hcode hP (by simp) (by simp [VisitedHeads])

/-- Contract item 4: a `while` whose continuing iterations stay within an `R`-frame and whose
active loop heads are determined (up to clock) by a key in a set of size `N` is bounded by
`(N + 1) * (B + 1)`. -/
theorem TerminatingProgBoundedOn.while_noRepeat
    (hloop : NoRepeatLoop P Q R κ condition body B) :
    TerminatingProgBoundedOn P (.while condition body) ((N + 1) * (B + 1)) :=
  fun state hcode hP =>
    (TerminatingProgBoundedOn.while_noRepeat_sharp hloop state hcode hP).weaken
      (Nat.mul_le_mul_right _ (Nat.le_succ N))

end NoRepeat

end InitECandidate.Solver.PanTerminatingNoRepeat
