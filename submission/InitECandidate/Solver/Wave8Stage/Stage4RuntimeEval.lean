import InitECandidate.Solver.Wave8Stage.Stage4RuntimeLeaves

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8Stage.RuntimeLabels
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemStateOps Flapjack.StackSemControl Flapjack.StackSemEvaluate
open Flapjack.StackSemMeasure
variable {width : Nat} [NeZero width]

/-- Exclude the chosen direct target and all ways of manufacturing its label.
Allocation and store-constants are excluded; installation is harmless when
its oracle supplies no code. -/
def ProgramSafe (bad : Nat) : HolProg width → Prop
  | .seq a b | .ite _ _ _ a b => ProgramSafe bad a ∧ ProgramSafe bad b
  | .loop b => ProgramSafe bad b
  | .jumpLower _ _ d | .rawCall d => d ≠ bad
  | .call ret dest handler =>
      (∀ n, dest = .inl n → n ≠ bad) ∧
      (match ret with
       | none => True
       | some (p, _, label, _) => ProgramSafe bad p ∧ label ≠ bad) ∧
      (match handler with
       | none => True
       | some (p, _, _) => ProgramSafe bad p)
  | .install .. => True
  | p => LeafAllowed bad p
termination_by p => sizeOf p

def CodeSafe {C F : Type} (bad : Nat) (s : StackSemStateFiniteExact width C F) : Prop :=
  ∀ n p, n ≠ bad → sptLookup n s.code = some p → ProgramSafe bad p

theorem mapSafe_erase {K : Type} [DecidableEq K] {bad : Nat}
    {m : HolFiniteMapExact K (WordLocW width)} (hm : MapSafe bad m) (k : K) :
    MapSafe bad (m.eraseEq k) := by
  intro q v hv
  simp only [HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL] at hv
  split at hv
  · cases hv
  · exact hm q v hv

theorem codeSafe_findCode {C F K : Type} {bad : Nat}
    {s : StackSemStateFiniteExact width C F} (hc : CodeSafe bad s)
    (regs : HolFiniteMapExact K (WordLocW width)) (hr : MapSafe bad regs)
    (dest : Nat ⊕ K) (hd : ∀ n, dest = .inl n → n ≠ bad)
    (p : HolProg width) (hl : findCode dest regs s.code = some p) : ProgramSafe bad p := by
  obtain ⟨n, hn, he⟩ := findCode_safe_target regs s.code dest p hr hd hl
  exact hc n p hn he

theorem codeSafe_evaluate {C F : Type} {bad : Nat}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (hc : CodeSafe bad s) (ho : ∀ i, (s.compileOracle i).2.1 = []) :
    CodeSafe bad (evaluate (p, s)).2 ∧
      ∀ i, ((evaluate (p, s)).2.compileOracle i).2.1 = [] := by
  obtain ⟨he, ho'⟩ := evaluate_code_empty_oracle p s _ _ rfl ho
  exact ⟨fun n q hn hq => hc n q hn (he ▸ hq), ho'⟩

theorem install_evaluate_safe {C F : Type} {bad : Nat}
    (a b c d e : Nat) (s : StackSemStateFiniteExact width C F)
    (h : StateSafe bad s) (ho : ∀ i, (s.compileOracle i).2.1 = []) :
    StateSafe bad (evaluate (.install a b c d e, s)).2 := by
  rw [evaluate_install]
  simp only [ho 0]
  repeat' split
  all_goals first | exact h | contradiction

private theorem evaluate_safe_measure {C F : Type} {bad : Nat} :
    ∀ (measure : Nat × Nat) (p : HolProg width) (s : StackSemStateFiniteExact width C F),
      stackSemMeasure p s = measure → ProgramSafe bad p → StateSafe bad s →
      CodeSafe bad s → (∀ i, (s.compileOracle i).2.1 = []) →
      StateSafe bad (evaluate (p, s)).2 := by
  intro measure
  induction measure using StackProps.EvaluateAddClock.lexNat_wf.induction with
  | _ measure ih =>
  intro p s hm hp hs hc ho
  subst hm
  cases p <;> (try simp only [ProgramSafe] at hp)
  case seq a b =>
    obtain ⟨ha, hb⟩ := hp
    have h1 := ih _ (seq_first_measure_lt a b s) a s rfl ha hs hc ho
    have hcode := codeSafe_evaluate a s hc ho
    rw [evaluate_seq]
    generalize he : evaluate (a, s) = out at h1 hcode ⊢
    obtain ⟨r, middle⟩ := out
    cases r with
    | some r => exact h1.withClock _
    | none =>
      exact ih _ (seq_second_measure_lt a b s (none, middle)) b _ rfl hb
        (h1.withClock _) hcode.1 hcode.2
  case ite cmp reg operand a b =>
    obtain ⟨ha, hb⟩ := hp
    have h1 := ih _ (if_first_measure_lt cmp reg operand a b s) a s rfl ha hs hc ho
    have h2 := ih _ (if_second_measure_lt cmp reg operand a b s) b s rfl hb hs hc ho
    rw [evaluate_ite]
    repeat' split
    all_goals first | exact h1 | exact h2 | exact hs
  case loop body =>
    have h1 := ih _ (loop_body_measure_lt body s) body s rfl hp hs hc ho
    have hcode := codeSafe_evaluate body s hc ho
    rw [evaluate_loop]
    generalize he : evaluate (body, s) = out at h1 hcode ⊢
    obtain ⟨r, middle⟩ := out
    dsimp only [fixClock]
    split
    · split
      · exact (h1.withClock _).emptyEnv_safe
      · exact ih _ (loop_reentry_measure_lt body s (r, middle) (by assumption))
          (.loop body) _ rfl (by rw [ProgramSafe]; exact hp) ((h1.withClock _).withClock _) hcode.1 hcode.2
    · exact h1.withClock _
  case jumpLower r1 r2 dest =>
    rw [evaluate_jumpLower]
    split
    · split
      · split
        · exact hs
        · rename_i body lookup
          have hb := hc dest body hp lookup
          split
          · exact hs.emptyEnv_safe
          · have h1 := ih _ (callee_measure_lt body (.jumpLower r1 r2 dest) s (by assumption))
              body _ rfl hb (hs.withClock _) hc ho
            generalize he : evaluate (body, decClock s) = out at h1 ⊢
            obtain ⟨res, middle⟩ := out
            dsimp only
            split <;> exact h1
      · exact hs
    · exact hs
  case rawCall dest =>
    rw [evaluate_rawCall]
    split
    · exact hs
    · rename_i prog lookup
      have hprog := hc dest prog hp lookup
      split
      · rename_i first body sequence
        have hb : ProgramSafe bad body := by
          cases prog <;> simp only [destSeq] at sequence
          all_goals try contradiction
          cases sequence
          rw [ProgramSafe] at hprog
          exact hprog.2
        split
        · exact hs.emptyEnv_safe
        · have h1 := ih _ (callee_measure_lt body (.rawCall dest) s (by assumption))
            body _ rfl hb (hs.withClock _) hc ho
          generalize he : evaluate (body, decClock s) = out at h1 ⊢
          obtain ⟨res, middle⟩ := out
          dsimp only
          split <;> exact h1
      · exact hs
  case call ret dest handler =>
    rw [ProgramSafe.eq_def] at hp
    obtain ⟨hd, hr, hh⟩ := hp
    rw [evaluate_call]
    cases ret with
    | none =>
      dsimp only
      split
      · exact hs
      · rename_i body lookup
        have hb := codeSafe_findCode hc s.regs hs.regs dest hd body lookup
        cases handler with
        | some handler => exact hs
        | none =>
          dsimp only
          split
          · exact hs.emptyEnv_safe
          · have h1 := ih _ (callee_measure_lt body (.call none dest none) s (by assumption))
              body _ rfl hb (hs.withClock _) hc ho
            generalize he : evaluate (body, decClock s) = out at h1 ⊢
            obtain ⟨res, middle⟩ := out
            dsimp only [fixClock]
            by_cases hbad : badFunReturn res = true
            all_goals simp only [hbad, ↓reduceIte]
            all_goals exact h1.withClock _
    | some ret =>
      obtain ⟨cont, link, l1, l2⟩ := ret
      dsimp only at hr ⊢
      split
      · exact hs
      · rename_i body lookup
        have hb := codeSafe_findCode hc _ (mapSafe_erase hs.regs link) dest hd body lookup
        split
        · exact hs.emptyEnv_safe
        · rename_i nonzero
          have hstart := (hs.setVar_safe link (.loc l1 l2) hr.2).withClock (s.clock - 1)
          have h1 := ih _ (callee_measure_lt body (.call (some (cont, link, l1, l2)) dest handler)
              (setVar link (.loc l1 l2) s) nonzero) body _ rfl hb hstart hc ho
          have hcode := codeSafe_evaluate body (decClock (setVar link (.loc l1 l2) s)) hc ho
          generalize he : evaluate (body, decClock (setVar link (.loc l1 l2) s)) = out at h1 hcode ⊢
          obtain ⟨res, middle⟩ := out
          have hcont : ∀ q, ProgramSafe bad q →
              StateSafe bad (evaluate (q,
                (fixClock (decClock (setVar link (.loc l1 l2) s)) (res, middle)).2)).2 := by
            intro q hq
            exact ih _ (call_continuation_measure_lt q _ s link l1 l2 (res, middle) nonzero)
              q _ rfl hq (h1.withClock _) hcode.1 hcode.2
          cases res with
          | none => exact h1.withClock _
          | some res =>
            cases res
            all_goals dsimp only [fixClock]
            all_goals try exact h1.withClock _
            case result x =>
              split
              · exact h1.withClock _
              · exact hcont cont hr.1
            case exception x =>
              cases handler with
              | none => exact h1.withClock _
              | some handler =>
                obtain ⟨h, hl1, hl2⟩ := handler
                dsimp only
                split
                · exact h1.withClock _
                · exact hcont h hh
  case install a b c d e => exact install_evaluate_safe a b c d e s hs ho
  all_goals exact leaf_evaluate_safe _ _ hp hs

/-- Runtime labels remain safe through arbitrary calls, loops and instruction
execution, provided the installed non-excluded code satisfies ProgramSafe. -/
theorem evaluate_safe {C F : Type} {bad : Nat}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (hp : ProgramSafe bad p) (hs : StateSafe bad s) (hc : CodeSafe bad s)
    (ho : ∀ i, (s.compileOracle i).2.1 = []) : StateSafe bad (evaluate (p, s)).2 :=
  evaluate_safe_measure (stackSemMeasure p s) p s rfl hp hs hc ho

#print axioms evaluate_safe
end InitECandidate.Solver.Wave8Stage.RuntimeLabels
