import InitECandidate.Solver.Wave8GuestInv.LeafStatements
import InitECandidate.Solver.PanTerminatingNoRepeat

/-! RLP family, part 8: phased no-repeat loop rule. A potential `φ ≤ Φ` never increases along
continuing iterations; iterations that keep `φ` stay inside an `R`-frame (no-repeat with keys in
`Fin N`), iterations that lower `φ` start a new phase. Bound `(N + Φ·N)·(B+1)`. The proof is step0's
`PanTerminatingNoRepeat.while_noRepeat_aux` with an outer strong induction on `φ`. -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.Rlp

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingNoRepeat

section Phased

variable (P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
  (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop)
  (φ : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat)
  {N : Nat} (κ : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Fin N)
  (condition : ExpHOL 64) (body : ProgHOL 64) (B : Nat)

structure PhasedLoop : Prop where
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
      P output.2 ∧ ((φ output.2 = φ state ∧ R state output.2) ∨ φ output.2 < φ state)
  trans : ∀ {F : Type} (a b c : PanSemStateFiniteExact 64 F), R a b → R b c → R a c
  key : ∀ {F : Type} (a b : PanSemStateFiniteExact 64 F), R a b →
    PanTerminatingNoRepeat.LoopActive condition a → PanTerminatingNoRepeat.LoopActive condition b → κ a = κ b →
    b = { a with clock := b.clock }

variable {P Q R φ κ condition body B}

theorem phased_key_fresh (hloop : PhasedLoop P Q R φ κ condition body B)
    {F : Type} (state : PanSemStateFiniteExact 64 F) (visited : Finset (Fin N))
    (hact : PanTerminatingNoRepeat.LoopActive condition state) (hvis : VisitedHeads R κ condition body state visited)
    (hnt : (evaluateHOLFiniteState state (.while condition body)).1 ≠ some .timeOut) :
    κ state ∉ visited := by
  intro hmem
  obtain ⟨earlier, hk, hR, hactE, hlt, hsame⟩ := hvis _ hmem
  have heq := hloop.key earlier state hR hactE hact hk
  exact InitECandidate.Solver.PanTerminatingNoRepeat.evaluate_ne_of_clock_lt _ state earlier (by rw [heq]) hlt hsame hnt

theorem while_phased_aux (hloop : PhasedLoop P Q R φ κ condition body B) :
    ∀ (m : Nat) (n : Nat) {F : Type} (state : PanSemStateFiniteExact 64 F) (visited : Finset (Fin N)),
      state.code = originalRuntimeCode → P state → φ state ≤ m → N ≤ visited.card + n →
      VisitedHeads R κ condition body state visited →
      TerminatingRunBounded state (.while condition body) ((n + m * N) * (B + 1)) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ihm =>
  intro n
  induction n with
  | zero =>
    intro F state visited hcode hP hφ hcard hvis hnt
    have hnt0 := hnt
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    split
    · rename_i word hword
      simp only [hword] at hnt
      by_cases hzero : word = 0
      · rw [if_neg (by simp [hzero])]; exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
      · have hfresh := phased_key_fresh hloop state visited ⟨word, hword, hzero⟩ hvis hnt0
        have := card_insert_key_le κ state visited hfresh
        omega
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  | succ n ih =>
    intro F state visited hcode hP hφ hcard hvis hnt
    have hone : B + 1 ≤ (n + 1 + m * N) * (B + 1) := Nat.le_mul_of_pos_left _ (by omega)
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
          have hact : PanTerminatingNoRepeat.LoopActive condition state := ⟨word, hword, hzero⟩
          have hfresh := phased_key_fresh hloop state visited hact hvis hnt0
          have hQ := hloop.entry state word hcode hP hword hzero hclock
          have hb := hloop.body_bound (decClockHOLFinite state) hcode hQ
          have hstep := hloop.step state word hcode hP hword hzero hclock
          have hunfold := InitECandidate.Solver.PanTerminatingNoRepeat.while_unfold_continue condition body state word hword hzero hclock
          have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
            (decClockHOLFinite state) body).1
          unfold TerminatingRunBounded at hb
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite state) body with ⟨result, post⟩
          simp only [hrun] at hnt hb hstep hunfold hmeta
          dsimp only at hb hstep hunfold hmeta hnt ⊢
          change post.code = state.code at hmeta
          have hcont (hflow : result = none ∨ result = some .continue) :
              state.clock ≤ (evaluateHOLFiniteState post (.while condition body)).2.clock +
                (n + 1 + m * N) * (B + 1) ∧
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
            rcases hRpost with ⟨hφeq, hRpost⟩ | hφlt
            · obtain ⟨htail, htailKept⟩ := ih post (insert (κ state) visited)
                (hmeta.trans hcode) hPpost (by omega)
                (by rw [Finset.card_insert_of_notMem hfresh]; omega)
                (by
                  intro k hk
                  rcases Finset.mem_insert.mp hk with rfl | hk
                  · exact ⟨state, rfl, hRpost, hact, by omega, hsame⟩
                  · obtain ⟨earlier, hke, hRe, hactE, hlt, hsameE⟩ := hvis k hk
                    exact ⟨earlier, hke, hloop.trans _ _ _ hRe hRpost, hactE, by omega,
                      hsameE.trans hsame⟩)
                hntPost
              have hmul : (n + m * N) * (B + 1) + (B + 1) = (n + 1 + m * N) * (B + 1) := by
                rw [show n + 1 + m * N = (n + m * N) + 1 by omega, Nat.succ_mul]
              exact ⟨by omega, by omega⟩
            · have hm' : φ post < m := by omega
              obtain ⟨htail, htailKept⟩ := ihm (φ post) hm' N post ∅ (hmeta.trans hcode) hPpost
                (Nat.le_refl _) (by simp) (by simp [VisitedHeads]) hntPost
              have hle : (N + φ post * N) * (B + 1) ≤ (n + m * N) * (B + 1) := by
                apply Nat.mul_le_mul_right
                have : (φ post + 1) * N ≤ m * N := Nat.mul_le_mul_right _ (by omega)
                rw [Nat.succ_mul] at this
                omega
              have hmul : (n + m * N) * (B + 1) + (B + 1) = (n + 1 + m * N) * (B + 1) := by
                rw [show n + 1 + m * N = (n + m * N) + 1 by omega, Nat.succ_mul]
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

/-- Phased no-repeat rule. -/
theorem TerminatingProgBoundedOn.while_phased {Φ : Nat}
    (hloop : PhasedLoop P Q R φ κ condition body B)
    (hφ : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → φ s ≤ Φ) :
    TerminatingProgBoundedOn P (.while condition body) ((Φ + 1) * N * (B + 1)) := by
  intro F state hcode hP
  have h := while_phased_aux hloop Φ N state ∅ hcode hP (hφ state hP) (by simp)
    (by simp [VisitedHeads])
  refine h.weaken (Nat.le_of_eq ?_)
  rw [Nat.succ_mul, Nat.add_comm]

end Phased

end InitECandidate.Solver.Wave8Leaves.Rlp
