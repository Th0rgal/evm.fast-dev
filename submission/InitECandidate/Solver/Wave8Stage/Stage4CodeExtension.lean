import InitECandidate.Solver.Wave8Stage.Stage4CodeExtensionLeaves

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8Stage.RuntimeLabels
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemStateOps Flapjack.StackSemControl Flapjack.StackSemEvaluate
open Flapjack.StackSemMeasure Flapjack.Compiler.Encoders.Asm
variable {width : Nat} [NeZero width]

private theorem evaluate_extendCode_measure {C F : Type} {bad : Nat} :
    ∀ (measure : Nat × Nat) (p : HolProg width) (s : StackSemStateFiniteExact width C F),
      stackSemMeasure p s = measure → ProgramSafe bad p → StateSafe bad s →
      CodeSafe bad s → (∀ i, (s.compileOracle i).2.1 = []) →
      ∀ code, CodeExtension s.code code → (evaluate (p, s)).1 ≠ some .error →
      evaluate (p, { s with code := code }) = replaceResultCode code (evaluate (p, s)) := by
  intro measure
  induction measure using StackProps.EvaluateAddClock.lexNat_wf.induction with
  | _ measure ih =>
  intro p s hm hp hs hc ho code ext hne
  subst hm
  cases p <;> (try simp only [ProgramSafe] at hp)
  case seq a b =>
    obtain ⟨ha, hb⟩ := hp
    have hn1 : (evaluate (a, s)).1 ≠ some .error := by
      intro he
      have heq : evaluate (a, s) = (some .error, (evaluate (a, s)).2) := Prod.ext he rfl
      rw [evaluate_seq, heq] at hne
      exact hne rfl
    have eq1 := ih _ (seq_first_measure_lt a b s) a s rfl ha hs hc ho code ext hn1
    have h1 := evaluate_safe a s ha hs hc ho
    have hcode := codeSafe_evaluate a s hc ho
    have hex := ext.after_evaluate a ho
    rw [evaluate_seq] at hne
    rw [evaluate_seq, evaluate_seq, eq1]
    generalize he : evaluate (a, s) = out at h1 hcode hex hne ⊢
    obtain ⟨res, middle⟩ := out
    cases res with
    | some res => rfl
    | none =>
      exact ih _ (seq_second_measure_lt a b s (none, middle)) b _ rfl hb
        (h1.withClock _) hcode.1 hcode.2 code hex hne
  case ite cmp reg operand a b =>
    obtain ⟨ha, hb⟩ := hp
    have eq1 := ih _ (if_first_measure_lt cmp reg operand a b s) a s rfl ha hs hc ho code ext
    have eq2 := ih _ (if_second_measure_lt cmp reg operand a b s) b s rfl hb hs hc ho code ext
    simp only [evaluate_ite, getVar, StackSemStateOps.getVarImm] at hne ⊢
    cases hop : HolRegImm.toWordRegImm operand <;> simp only [hop, StackSemStateOps.getVarImm, getVar] at hne ⊢
    all_goals repeat' split
    all_goals try simp_all only
    all_goals first | exact eq1 hne | exact eq2 hne | rfl | contradiction
  case loop body =>
    have hn1 : (evaluate (body, s)).1 ≠ some .error := by
      intro he
      have heq : evaluate (body, s) = (some .error, (evaluate (body, s)).2) := Prod.ext he rfl
      rw [evaluate_loop, heq] at hne
      exact hne rfl
    have eq1 := ih _ (loop_body_measure_lt body s) body s rfl hp hs hc ho code ext hn1
    have h1 := evaluate_safe body s hp hs hc ho
    have hcode := codeSafe_evaluate body s hc ho
    have hex := ext.after_evaluate body ho
    rw [evaluate_loop] at hne
    rw [evaluate_loop, evaluate_loop, eq1]
    generalize he : evaluate (body, s) = out at h1 hcode hex hne ⊢
    obtain ⟨res, middle⟩ := out
    dsimp only [replaceResultCode, fixClock] at hne ⊢
    split at hne
    · rename_i hgo
      simp only [hgo, ↓reduceIte]
      split at hne
      · rename_i hz
        simp only [hz, ↓reduceIte]
        rfl
      · rename_i hnz
        simp only [hnz, ↓reduceIte]
        exact ih _ (loop_reentry_measure_lt body s (res, middle) hnz)
          (.loop body) _ rfl (by rw [ProgramSafe]; exact hp)
          ((h1.withClock _).withClock _) hcode.1 hcode.2 code hex hne
    · rename_i hstop
      simp only [hstop, ↓reduceIte]
      rfl
  case jumpLower r1 r2 dest =>
    simp only [evaluate_jumpLower, getVar, findCode] at hne ⊢
    split at hne
    · rename_i x y hx hy
      try dsimp only
      try simp only [hx, hy]
      split at hne
      · rename_i hlt
        simp only [hlt, ↓reduceIte]
        cases hl : sptLookup dest s.code with
        | none => simp [hl] at hne
        | some body =>
          have ht := ext dest body hl
          simp only [hl, ht]
          try simp only [hl] at hne
          have hb := hc dest body hp hl
          split at hne
          · rename_i hz
            simp only [hz, ↓reduceIte]
            simp only [replaceResultCode, emptyEnv, hz]
          · rename_i hnz
            simp only [hnz, ↓reduceIte]
            have hn1 : (evaluate (body, decClock s)).1 ≠ some .error := by
              intro he
              simp [he, badFunReturn] at hne
            have eq1 := ih _ (callee_measure_lt body (.jumpLower r1 r2 dest) s hnz)
              body _ rfl hb (hs.withClock _) hc ho code ext hn1
            rw [show decClock { s with code := code } = { decClock s with code := code } from rfl, eq1]
            generalize he : evaluate (body, decClock s) = out
            obtain ⟨res, middle⟩ := out
            dsimp only [replaceResultCode]
            by_cases hbad : badFunReturn res = true <;> simp only [hbad, ↓reduceIte] <;> rfl
      · rename_i hlt
        simp only [hlt, ↓reduceIte]
        rfl
    · exact False.elim (hne rfl)
  case rawCall dest =>
    rw [evaluate_rawCall] at hne
    rw [evaluate_rawCall, evaluate_rawCall]
    cases hl : sptLookup dest s.code with
    | none => simp [hl] at hne
    | some prog =>
      simp only [hl, ext dest prog hl]
      try simp only [hl] at hne
      have hprog := hc dest prog hp hl
      split at hne
      · rename_i first body hseq
        try rw [hseq]
        have hb : ProgramSafe bad body := by
          cases prog <;> simp only [destSeq] at hseq
          all_goals try contradiction
          cases hseq
          rw [ProgramSafe] at hprog
          exact hprog.2
        split at hne
        · rename_i hz
          simp only [hz, ↓reduceIte]
          simp only [replaceResultCode, emptyEnv, hz]
        · rename_i hnz
          simp only [hnz, ↓reduceIte]
          have hn1 : (evaluate (body, decClock s)).1 ≠ some .error := by
            intro he
            simp [he, badFunReturn] at hne
          have eq1 := ih _ (callee_measure_lt body (.rawCall dest) s hnz)
            body _ rfl hb (hs.withClock _) hc ho code ext hn1
          rw [show decClock { s with code := code } = { decClock s with code := code } from rfl, eq1]
          generalize he : evaluate (body, decClock s) = out
          obtain ⟨res, middle⟩ := out
          dsimp only [replaceResultCode]
          by_cases hbad : badFunReturn res = true <;> simp only [hbad, ↓reduceIte] <;> rfl
      · exact False.elim (hne rfl)
  case call ret dest handler =>
    rw [ProgramSafe.eq_def] at hp
    obtain ⟨hd, hr, hh⟩ := hp
    rw [evaluate_call] at hne
    rw [evaluate_call, evaluate_call]
    cases ret with
    | none =>
      dsimp only at hne ⊢
      cases hl : findCode dest s.regs s.code with
      | none => simp [hl] at hne
      | some body =>
        simp only [hl, ext.findCode s.regs dest body hl]
        try simp only [hl] at hne
        have hb := codeSafe_findCode hc s.regs hs.regs dest hd body hl
        cases handler with
        | some handler => exact False.elim (hne rfl)
        | none =>
          dsimp only at hne ⊢
          split at hne
          · rename_i hz
            simp only [hz, ↓reduceIte]
            simp only [replaceResultCode, emptyEnv, hz]
          · rename_i hnz
            simp only [hnz, ↓reduceIte]
            have hn1 : (evaluate (body, decClock s)).1 ≠ some .error := by
              intro he
              simp [fixClock, he, badFunReturn] at hne
            have eq1 := ih _ (callee_measure_lt body (.call none dest none) s hnz)
              body _ rfl hb (hs.withClock _) hc ho code ext hn1
            rw [show decClock { s with code := code } = { decClock s with code := code } from rfl, eq1]
            generalize he : evaluate (body, decClock s) = out
            obtain ⟨res, middle⟩ := out
            dsimp only [replaceResultCode, fixClock]
            by_cases hbad : badFunReturn res = true <;> simp only [hbad, ↓reduceIte] <;> rfl
    | some ret =>
      obtain ⟨cont, link, l1, l2⟩ := ret
      dsimp only at hr hne ⊢
      cases hl : findCode dest (s.regs.eraseEq link) s.code with
      | none => simp [hl] at hne
      | some body =>
        simp only [hl, ext.findCode _ dest body hl]
        try simp only [hl] at hne
        have hb := codeSafe_findCode hc _ (mapSafe_erase hs.regs link) dest hd body hl
        split at hne
        · rename_i hz
          simp only [hz, ↓reduceIte]
          simp only [replaceResultCode, emptyEnv, hz]
        · rename_i hnz
          simp only [hnz, ↓reduceIte]
          let start := decClock (setVar link (.loc l1 l2) s)
          have hstart : StateSafe bad start := (hs.setVar_safe link (.loc l1 l2) hr.2).withClock _
          have hn1 : (evaluate (body, start)).1 ≠ some .error := by
            intro he
            simp [fixClock, show (evaluate (body, decClock (setVar link (.loc l1 l2) s))).1 = some .error from he] at hne
          have eq1 := ih _ (callee_measure_lt body (.call (some (cont, link, l1, l2)) dest handler)
              (setVar link (.loc l1 l2) s) hnz) body start rfl hb hstart hc ho code ext hn1
          have h1 := evaluate_safe body start hb hstart hc ho
          have hcode := codeSafe_evaluate body start hc ho
          have hex := ext.after_evaluate body ho (s := start)
          rw [show decClock (setVar link (.loc l1 l2) { s with code := code }) =
            { start with code := code } from rfl, eq1]
          generalize he : evaluate (body, start) = out at h1 hcode hex hne ⊢
          have hne' := hne
          obtain ⟨res, middle⟩ := out
          have hcont : ∀ q, ProgramSafe bad q →
              (evaluate (q, (fixClock start (res, middle)).2)).1 ≠ some .error →
              evaluate (q, { (fixClock start (res, middle)).2 with code := code }) =
                replaceResultCode code (evaluate (q, (fixClock start (res, middle)).2)) := by
            intro q hq hn
            exact ih _ (call_continuation_measure_lt q _ s link l1 l2 (res, middle) hnz)
              q _ rfl hq (h1.withClock _) hcode.1 hcode.2 code hex hn
          cases res with
          | none => rfl
          | some res =>
            cases res
            all_goals dsimp only [replaceResultCode, fixClock] at hne' ⊢
            all_goals try rfl
            case result x =>
              split at hne'
              · exact False.elim (hne' rfl)
              · rename_i hl
                simp only [hl, ↓reduceIte]
                exact hcont cont hr.1 hne'
            case exception x =>
              cases handler with
              | none => rfl
              | some handler =>
                obtain ⟨h, hl1, hl2⟩ := handler
                dsimp only at hne' ⊢
                split at hne'
                · exact False.elim (hne' rfl)
                · rename_i hl
                  simp only [hl, ↓reduceIte]
                  exact hcont h hh hne'
  case install a b c d e => exact install_evaluate_withCode a b c d e s code ho
  all_goals exact leaf_evaluate_extendCode _ s code hp ext hne

/-- Adding sections cannot change a safe non-error run, provided existing
sections retain their bodies and the installation oracle supplies no code. -/
theorem evaluate_extendCode {C F : Type} {bad : Nat}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (hp : ProgramSafe bad p) (hs : StateSafe bad s) (hc : CodeSafe bad s)
    (ho : ∀ i, (s.compileOracle i).2.1 = [])
    (code : Spt (HolProg width)) (ext : CodeExtension s.code code)
    (hne : (evaluate (p, s)).1 ≠ some .error) :
    evaluate (p, { s with code := code }) = replaceResultCode code (evaluate (p, s)) :=
  evaluate_extendCode_measure (stackSemMeasure p s) p s rfl hp hs hc ho code ext hne

end InitECandidate.Solver.Wave8Stage.RuntimeLabels
