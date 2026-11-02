import InitECandidate.Solver.Wave8Stage.Stage4AllocFieldsLeaves

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8Stage.AllocFields
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemStateOps Flapjack.StackSemControl Flapjack.StackSemEvaluate
open InitECandidate.Solver.Wave8Stage.RuntimeLabels
open Flapjack.StackSemMeasure Flapjack.Compiler.Encoders.Asm
variable {width : Nat} [NeZero width]

private theorem evaluate_withAllocFields_measure {C F : Type} {bad : Nat} :
    ∀ (measure : Nat × Nat) (p : HolProg width) (s : StackSemStateFiniteExact width C F),
      stackSemMeasure p s = measure → ProgramSafe bad p → StateSafe bad s →
      CodeSafe bad s → (∀ i, (s.compileOracle i).2.1 = []) →
      ∀ cfg : StackSemStateFiniteExact width C F, (∀ i, (cfg.compileOracle i).2.1 = []) →
      evaluate (p, { s with useAlloc := cfg.useAlloc, gcFun := cfg.gcFun, compile := cfg.compile, compileOracle := cfg.compileOracle }) = replaceResult cfg (evaluate (p, s)) := by
  intro measure
  induction measure using StackProps.EvaluateAddClock.lexNat_wf.induction with
  | _ measure ih =>
  intro p s hm hp hs hc ho cfg ht
  subst hm
  cases p <;> (try simp only [ProgramSafe] at hp)
  case seq a b =>
    obtain ⟨ha, hb⟩ := hp
    have eq1 := ih _ (seq_first_measure_lt a b s) a s rfl ha hs hc ho cfg ht
    have h1 := evaluate_safe a s ha hs hc ho
    have hcode := codeSafe_evaluate a s hc ho
    rw [evaluate_seq, evaluate_seq, eq1]
    generalize he : evaluate (a, s) = out at h1 hcode ⊢
    obtain ⟨res, middle⟩ := out
    cases res with
    | some res => rfl
    | none =>
      exact ih _ (seq_second_measure_lt a b s (none, middle)) b _ rfl hb
        (h1.withClock _) hcode.1 hcode.2 cfg ht
  case ite cmp reg operand a b =>
    obtain ⟨ha, hb⟩ := hp
    have eq1 := ih _ (if_first_measure_lt cmp reg operand a b s) a s rfl ha hs hc ho cfg ht
    have eq2 := ih _ (if_second_measure_lt cmp reg operand a b s) b s rfl hb hs hc ho cfg ht
    simp only [evaluate_ite, getVar, StackSemStateOps.getVarImm]
    cases HolRegImm.toWordRegImm operand <;> simp only [StackSemStateOps.getVarImm, getVar]
    all_goals repeat' split
    all_goals first | exact eq1 | exact eq2 | rfl
  case loop body =>
    have eq1 := ih _ (loop_body_measure_lt body s) body s rfl hp hs hc ho cfg ht
    have h1 := evaluate_safe body s hp hs hc ho
    have hcode := codeSafe_evaluate body s hc ho
    rw [evaluate_loop, evaluate_loop, eq1]
    generalize he : evaluate (body, s) = out at h1 hcode ⊢
    obtain ⟨res, middle⟩ := out
    dsimp only [replaceResult, override, fixClock]
    split
    · split
      · rfl
      · exact ih _ (loop_reentry_measure_lt body s (res, middle) (by assumption))
          (.loop body) _ rfl (by rw [ProgramSafe]; exact hp)
          ((h1.withClock _).withClock _) hcode.1 hcode.2 cfg ht
    · rfl
  case jumpLower r1 r2 dest =>
    simp only [evaluate_jumpLower, getVar, findCode]
    split
    · split
      · split
        · rfl
        · rename_i body lookup
          have hb := hc dest body hp lookup
          split
          · rfl
          · have eq1 := ih _ (callee_measure_lt body (.jumpLower r1 r2 dest) s (by assumption))
              body _ rfl hb (hs.withClock _) hc ho cfg ht
            rw [show decClock ({ s with useAlloc := cfg.useAlloc, gcFun := cfg.gcFun, compile := cfg.compile, compileOracle := cfg.compileOracle }) = { decClock s with useAlloc := cfg.useAlloc, gcFun := cfg.gcFun, compile := cfg.compile, compileOracle := cfg.compileOracle } from rfl, eq1]
            generalize he : evaluate (body, decClock s) = out
            obtain ⟨res, middle⟩ := out
            dsimp only [replaceResult, override]
            by_cases hbad : badFunReturn res = true <;> simp only [hbad, ↓reduceIte] <;> rfl
      · rfl
    · rfl
  case rawCall dest =>
    simp only [evaluate_rawCall]
    split
    · rfl
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
        · rfl
        · have eq1 := ih _ (callee_measure_lt body (.rawCall dest) s (by assumption))
            body _ rfl hb (hs.withClock _) hc ho cfg ht
          rw [show decClock ({ s with useAlloc := cfg.useAlloc, gcFun := cfg.gcFun, compile := cfg.compile, compileOracle := cfg.compileOracle }) = { decClock s with useAlloc := cfg.useAlloc, gcFun := cfg.gcFun, compile := cfg.compile, compileOracle := cfg.compileOracle } from rfl, eq1]
          generalize he : evaluate (body, decClock s) = out
          obtain ⟨res, middle⟩ := out
          dsimp only [replaceResult, override]
          by_cases hbad : badFunReturn res = true <;> simp only [hbad, ↓reduceIte] <;> rfl
      · rfl
  case call ret dest handler =>
    rw [ProgramSafe.eq_def] at hp
    obtain ⟨hd, hr, hh⟩ := hp
    rw [evaluate_call, evaluate_call]
    cases ret with
    | none =>
      dsimp only
      split
      · rfl
      · rename_i body lookup
        have hb := codeSafe_findCode hc s.regs hs.regs dest hd body lookup
        cases handler with
        | some handler => rfl
        | none =>
          dsimp only
          split
          · rfl
          · have eq1 := ih _ (callee_measure_lt body (.call none dest none) s (by assumption))
              body _ rfl hb (hs.withClock _) hc ho cfg ht
            rw [show decClock ({ s with useAlloc := cfg.useAlloc, gcFun := cfg.gcFun, compile := cfg.compile, compileOracle := cfg.compileOracle }) = { decClock s with useAlloc := cfg.useAlloc, gcFun := cfg.gcFun, compile := cfg.compile, compileOracle := cfg.compileOracle } from rfl, eq1]
            generalize he : evaluate (body, decClock s) = out
            obtain ⟨res, middle⟩ := out
            dsimp only [replaceResult, override, fixClock]
            by_cases hbad : badFunReturn res = true <;> simp only [hbad, ↓reduceIte]
            all_goals rfl
    | some ret =>
      obtain ⟨cont, link, l1, l2⟩ := ret
      dsimp only at hr ⊢
      split
      · rfl
      · rename_i body lookup
        have hb := codeSafe_findCode hc _ (mapSafe_erase hs.regs link) dest hd body lookup
        split
        · rfl
        · rename_i nonzero
          let start := decClock (setVar link (.loc l1 l2) s)
          have hstart : StateSafe bad start :=
            (hs.setVar_safe link (.loc l1 l2) hr.2).withClock _
          have eq1 := ih _ (callee_measure_lt body (.call (some (cont, link, l1, l2)) dest handler)
              (setVar link (.loc l1 l2) s) nonzero) body start rfl hb hstart hc ho cfg ht
          have h1 := evaluate_safe body start hb hstart hc ho
          have hcode := codeSafe_evaluate body start hc ho
          rw [show decClock (setVar link (.loc l1 l2) ({ s with useAlloc := cfg.useAlloc, gcFun := cfg.gcFun, compile := cfg.compile, compileOracle := cfg.compileOracle })) =
            { start with useAlloc := cfg.useAlloc, gcFun := cfg.gcFun, compile := cfg.compile, compileOracle := cfg.compileOracle } from rfl, eq1]
          generalize he : evaluate (body, start) = out at h1 hcode ⊢
          obtain ⟨res, middle⟩ := out
          have hcont : ∀ q, ProgramSafe bad q →
              evaluate (q, { (fixClock start (res, middle)).2 with useAlloc := cfg.useAlloc, gcFun := cfg.gcFun, compile := cfg.compile, compileOracle := cfg.compileOracle }) =
                replaceResult cfg (evaluate (q, (fixClock start (res, middle)).2)) := by
            intro q hq
            exact ih _ (call_continuation_measure_lt q _ s link l1 l2 (res, middle) nonzero)
              q _ rfl hq (h1.withClock _) hcode.1 hcode.2 cfg ht
          cases res with
          | none => rfl
          | some res =>
            cases res
            all_goals dsimp only [replaceResult, override, fixClock]
            all_goals try rfl
            case result x =>
              split
              · rfl
              · exact hcont cont hr.1
            case exception x =>
              cases handler with
              | none => rfl
              | some handler =>
                obtain ⟨h, hl1, hl2⟩ := handler
                dsimp only
                split
                · rfl
                · exact hcont h hh
  case install a b c d e => exact install_evaluate_withAllocFields a b c d e s cfg ho ht
  all_goals exact leaf_evaluate_withAllocFields _ s cfg hp

/-- Allocation-free safe execution is independent of the allocation flag,
collector and compiler callback when both installation oracles supply no code.
The result and clock are exactly preserved. -/
theorem evaluate_withAllocFields {C F : Type} {bad : Nat}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (hp : ProgramSafe bad p) (hs : StateSafe bad s) (hc : CodeSafe bad s)
    (ho : ∀ i, (s.compileOracle i).2.1 = [])
    (cfg : StackSemStateFiniteExact width C F) (ht : ∀ i, (cfg.compileOracle i).2.1 = []) :
    evaluate (p, { s with useAlloc := cfg.useAlloc, gcFun := cfg.gcFun, compile := cfg.compile, compileOracle := cfg.compileOracle }) = replaceResult cfg (evaluate (p, s)) :=
  evaluate_withAllocFields_measure (stackSemMeasure p s) p s rfl hp hs hc ho cfg ht

end InitECandidate.Solver.Wave8Stage.AllocFields
