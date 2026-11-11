import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4F

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.EvmBase (stdKeep)
open InitECandidate.Solver.Wave8GuestInv.R13Shards
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
open InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs

/-! # Phase 4G: the generic while-loop runner

`p4Run_while` reduces `PtxRelRunStrong entry (.seq (.while cond body) rest) s`
to three obligations: the invariant at `s`, the exit obligation (`hexit`, when
`cond` evaluates to the word `0`) and the body obligation (`hbody`), which
receives the induction hypothesis as a parameter and is discharged by the
ordinary per-instruction engines with the loop program as the final tail.
The body must not raise a top-level `break`/`continue` (the phase-4 spine is
straight-line code, so both hold by computation). -/

/-- Generic while-loop runner for `PtxRelRunStrong`. -/
theorem p4Run_while {F : Type} {entry : PanSemStateFiniteExact 64 F}
    (cond : ExpHOL 64) (body rest : ProgHOL 64)
    (INV : PanSemStateFiniteExact 64 F → Prop)
    (hnb : InitECandidate.Solver.GuestUniformClockBound.noTopBreak body = true)
    (hnc : InitECandidate.Solver.PanRunBounded.noTopContinue body = true)
    (hexit : ∀ t, INV t → evalAt t cond = some (.val (.word 0#64)) →
      PtxRelRunStrong entry rest t)
    (hbody : ∀ t, INV t →
      (∀ mid, INV mid → mid.clock < t.clock →
        PtxRelRunStrong entry (.seq (.while cond body) rest) mid) →
      PtxRelRunStrong entry (.seq body (.seq (.while cond body) rest)) (decClockHOLFinite t))
    (s : PanSemStateFiniteExact 64 F) (hINV : INV s) :
    PtxRelRunStrong entry (.seq (.while cond body) rest) s := by
  intro hres
  suffices H : ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F),
      st.clock = k → INV st →
      PtxRelRunStrong entry (.seq (.while cond body) rest) st from
    H s.clock s rfl hINV hres
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st hk hINVst hres
    rcases hc : @evalHOLFinite 64 F _ st
        (fun address => Classical.propDecidable (st.memaddrs address)) cond with _ | cval
    · -- condition evaluation fails: the loop traps with `.error`
      have herr : evaluateHOLFiniteState st (.seq (.while cond body) rest) = (some .error, st) := by
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_while_fixClockRewrite, hc]
      rw [herr] at hres ⊢
      dsimp only at hres ⊢
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
    · cases cval with
      | val wv =>
        cases wv with
        | word w =>
          by_cases hw : w = 0
          · -- loop exit
            subst hw
            have hrun : evaluateHOLFiniteState st (.seq (.while cond body) rest) =
                evaluateHOLFiniteState st rest := by
              rw [evaluateHOLFiniteState_seq_line780,
                  evaluateHOLFiniteState_while_fixClockRewrite, hc]
              dsimp only
              rw [if_neg (by decide)]
            rw [hrun] at hres ⊢
            exact hexit st hINVst hc hres
          · -- loop iterates
            by_cases hclk : st.clock = 0
            · -- clock exhausted: `.timeOut`
              have hto : evaluateHOLFiniteState st (.seq (.while cond body) rest) =
                  (some .timeOut, emptyLocalsHOLFinite st) := by
                rw [evaluateHOLFiniteState_seq_line780,
                    evaluateHOLFiniteState_while_fixClockRewrite, hc]
                dsimp only
                rw [if_pos hw, if_pos hclk]
              rw [hto] at hres ⊢
              dsimp only at hres ⊢
              exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
            · -- run the body at the decremented clock
              rcases hbrun : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨rb, mid⟩
              have hnb' := InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak
                body hnb (decClockHOLFinite st)
              have hnc' := InitECandidate.Solver.PanRunBounded.evaluate_noTopContinue
                body hnc (decClockHOLFinite st)
              rw [hbrun] at hnb' hnc'
              have hcomp : evaluateHOLFiniteState st (.seq (.while cond body) rest) =
                  evaluateHOLFiniteState (decClockHOLFinite st)
                    (.seq body (.seq (.while cond body) rest)) := by
                rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_seq_line780,
                    evaluateHOLFiniteState_while_fixClockRewrite, hc]
                dsimp only
                rw [if_pos hw, if_neg hclk, hbrun]
                dsimp only
                cases rb with
                | none =>
                  rw [evaluateHOLFiniteState_seq_line780]
                | some r =>
                  cases r with
                  | «continue» => exact absurd rfl hnc'
                  | «break» => exact absurd rfl hnb'
                  | returned _ | exception _ | timeOut | error | finalFfi _ => rfl
              rw [hcomp] at hres ⊢
              have hclt : mid.clock < k := by
                have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
                rw [hbrun] at hrem
                change mid.clock ≤ st.clock - 1 at hrem
                omega
              exact hbody st hINVst
                (fun mid' hINVmid hlt => ih mid'.clock (by omega) mid' rfl hINVmid)
                hres
      | rStruct _ | nStruct _ _ =>
        -- the condition is not a word: the loop traps with `.error`
        have herr : evaluateHOLFiniteState st (.seq (.while cond body) rest)
            = (some .error, st) := by
          rw [evaluateHOLFiniteState_seq_line780,
              evaluateHOLFiniteState_while_fixClockRewrite, hc]
        rw [herr] at hres ⊢
        dsimp only at hres ⊢
        exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

/-- Generic seq bridge: run `P`, and if it finishes without a result, continue
with `T'` at the post state.  The `some r` case is delegated to `h` (the
`PtxRelRunStrong` for the bare `P`). -/
theorem p4Run_seq_bridge {F : Type} {entry : PanSemStateFiniteExact 64 F}
    (P T' : ProgHOL 64) (s : PanSemStateFiniteExact 64 F)
    (h : PtxRelRunStrong entry P s)
    (hmid : ∀ post, evaluateHOLFiniteState s P = (none, post) →
      PtxRelRunStrong entry T' post) :
    PtxRelRunStrong entry (.seq P T') s := by
  intro hres
  rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
  rcases hP : evaluateHOLFiniteState s P with ⟨r, post⟩
  cases r with
  | none =>
    rw [hP] at hres
    dsimp only at hres ⊢
    exact hmid post hP hres
  | some r =>
    rw [hP] at hres
    dsimp only at hres ⊢
    have hw := h (by rw [hP]; exact hres)
    rw [hP] at hw
    exact hw

/-- The loop-31 condition: `i < nl`. -/
def p4Loop31Cond : ExpHOL 64 :=
  .cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl"))

/-- The loop-31 body: push a slot onto the logs list, store the log entry
into it, then bump `i`. -/
def p4Loop31Body : ProgHOL 64 :=
  .decCall (ofString "slot") .one (ofString "lst_push")
    [(.load .one (.op .add [(.var .global (ofString "bo")), (.const 0x0000000000000028#64)])),
     (.const 0x0000000000000008#64)]
    (.seq (.store (.var .local (ofString "slot"))
            (.load .one (.op .add [(.var .local (ofString "lp")),
              (.panop .mul [(.var .local (ofString "i")), (.const 0x0000000000000008#64)])])))
          (.assign .local (ofString "i")
            (.op .add [(.var .local (ofString "i")), (.const 0x0000000000000001#64)])))

theorem p4Loop31Body_noTopBreak :
    InitECandidate.Solver.GuestUniformClockBound.noTopBreak p4Loop31Body = true := by
  unfold p4Loop31Body; decide

theorem p4Loop31Body_noTopContinue :
    InitECandidate.Solver.PanRunBounded.noTopContinue p4Loop31Body = true := by
  unfold p4Loop31Body; decide

/-- The loop-38 condition: `i < nl`. -/
def p4Loop38Cond : ExpHOL 64 :=
  .cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl"))

/-- The loop-38 body: copy one log entry into the stable list, bump `i`. -/
def p4Loop38Body : ProgHOL 64 :=
  .seq (.store (.op .add [(.var .local (ofString "stable_lp")),
              (.panop .mul [(.var .local (ofString "i")), (.const 0x0000000000000008#64)])])
          (.load .one (.op .add [(.var .local (ofString "lp")),
              (.panop .mul [(.var .local (ofString "i")), (.const 0x0000000000000008#64)])])))
       (.assign .local (ofString "i")
          (.op .add [(.var .local (ofString "i")), (.const 0x0000000000000001#64)]))

theorem p4Loop38Body_noTopBreak :
    InitECandidate.Solver.GuestUniformClockBound.noTopBreak p4Loop38Body = true := by
  unfold p4Loop38Body; decide

theorem p4Loop38Body_noTopContinue :
    InitECandidate.Solver.PanRunBounded.noTopContinue p4Loop38Body = true := by
  unfold p4Loop38Body; decide

/-- The loop-31 runner, specialized to the concrete body and condition. -/
theorem p4Run_while31 {F : Type} {entry : PanSemStateFiniteExact 64 F}
    {rest : ProgHOL 64} (INV : PanSemStateFiniteExact 64 F → Prop)
    (hexit : ∀ t, INV t → evalAt t p4Loop31Cond = some (.val (.word 0#64)) →
      PtxRelRunStrong entry rest t)
    (hbody : ∀ t, INV t →
      (∀ mid, INV mid → mid.clock < t.clock →
        PtxRelRunStrong entry (.seq (.while p4Loop31Cond p4Loop31Body) rest) mid) →
      PtxRelRunStrong entry (.seq p4Loop31Body
        (.seq (.while p4Loop31Cond p4Loop31Body) rest)) (decClockHOLFinite t))
    (s : PanSemStateFiniteExact 64 F) (hINV : INV s) :
    PtxRelRunStrong entry (.seq (.while p4Loop31Cond p4Loop31Body) rest) s :=
  p4Run_while p4Loop31Cond p4Loop31Body rest INV
    p4Loop31Body_noTopBreak p4Loop31Body_noTopContinue hexit hbody s hINV

/-- The loop-38 runner, specialized to the concrete body and condition. -/
theorem p4Run_while38 {F : Type} {entry : PanSemStateFiniteExact 64 F}
    {rest : ProgHOL 64} (INV : PanSemStateFiniteExact 64 F → Prop)
    (hexit : ∀ t, INV t → evalAt t p4Loop38Cond = some (.val (.word 0#64)) →
      PtxRelRunStrong entry rest t)
    (hbody : ∀ t, INV t →
      (∀ mid, INV mid → mid.clock < t.clock →
        PtxRelRunStrong entry (.seq (.while p4Loop38Cond p4Loop38Body) rest) mid) →
      PtxRelRunStrong entry (.seq p4Loop38Body
        (.seq (.while p4Loop38Cond p4Loop38Body) rest)) (decClockHOLFinite t))
    (s : PanSemStateFiniteExact 64 F) (hINV : INV s) :
    PtxRelRunStrong entry (.seq (.while p4Loop38Cond p4Loop38Body) rest) s :=
  p4Run_while p4Loop38Cond p4Loop38Body rest INV
    p4Loop38Body_noTopBreak p4Loop38Body_noTopContinue hexit hbody s hINV

/-- Seq associativity for `PtxRelRunStrong`: re-associate
`.seq (.seq A B) C` into `.seq A (.seq B C)` so the per-instruction engines
(which conclude over `.seq instr tail`) can be chained directly. -/
theorem p4Run_seq_assoc {F : Type} {entry : PanSemStateFiniteExact 64 F}
    (A B C : ProgHOL 64) (s : PanSemStateFiniteExact 64 F)
    (h : PtxRelRunStrong entry (.seq A (.seq B C)) s) :
    PtxRelRunStrong entry (.seq (.seq A B) C) s := by
  intro hres
  have hEq : evaluateHOLFiniteState s (.seq (.seq A B) C) =
      evaluateHOLFiniteState s (.seq A (.seq B C)) := by
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_seq_line780,
        evaluateHOLFiniteState_seq_line780]
    rcases hA : evaluateHOLFiniteState s A with ⟨r, s'⟩
    cases r with
    | none =>
      dsimp only
      rw [evaluateHOLFiniteState_seq_line780]
    | some r => rfl
  rw [hEq] at hres ⊢
  exact h hres

/-- The loop-38 store destination: `stable_lp + 8 * i`. -/
def p4L38Dst : ExpHOL 64 :=
  .op .add [(.var .local (ofString "stable_lp")),
    (.panop .mul [(.var .local (ofString "i")), (.const 0x0000000000000008#64)])]

/-- The loop-38 store source: the log entry at `lp + 8 * i`. -/
def p4L38Src : ExpHOL 64 :=
  .load .one (.op .add [(.var .local (ofString "lp")),
    (.panop .mul [(.var .local (ofString "i")), (.const 0x0000000000000008#64)])])

/-- The loop-38 increment expression: `i + 1`. -/
def p4L38I : ExpHOL 64 :=
  .op .add [(.var .local (ofString "i")), (.const 0x0000000000000001#64)]

/-- The loop-38 body obligation for `p4Run_while38`: compose the store and
assign engines directly (no bare terminals).  All semantic obligations are
isolated into `hfacts` (evaluation facts, the store effect and the invariant
transport). -/
theorem p4Run_loop38Body {F : Type} {entry : PanSemStateFiniteExact 64 F}
    {rest : ProgHOL 64} {t u : PanSemStateFiniteExact 64 F}
    (INV : PanSemStateFiniteExact 64 F → Prop)
    (hu : u = decClockHOLFinite t)
    (ih : ∀ mid, INV mid → mid.clock < t.clock →
      PtxRelRunStrong entry (.seq (.while p4Loop38Cond p4Loop38Body) rest) mid)
    (hexit : ∀ t', INV t' → evalAt t' p4Loop38Cond = some (.val (.word 0#64)) →
      PtxRelRunStrong entry rest t')
    (hfacts : ∃ (a v w : BitVec 64) (mem' : RiscV.Word 64 → HolWordLab 64),
      evalAt u p4L38Dst = some (.val (.word a)) ∧
      evalAt u p4L38Src = some (.val (.word v)) ∧
      @panMemStoresHOL 64 _ a (flattenHOL (.val (.word v))) u.memaddrs
        (fun address => Classical.propDecidable (u.memaddrs address)) u.memory = some mem' ∧
      evalAt {u with memory := mem'} p4L38I = some (.val (.word w)) ∧
      INV (setVarHOLFinite (ofString "i") (.val (.word w)) {u with memory := mem'}) ∧
      (evalAt (setVarHOLFinite (ofString "i") (.val (.word w)) {u with memory := mem'})
          p4Loop38Cond = some (.val (.word 0#64)) ∨ t.clock ≠ 0)) :
    PtxRelRunStrong entry (.seq p4Loop38Body
      (.seq (.while p4Loop38Cond p4Loop38Body) rest)) u := by
  intro hres
  obtain ⟨a, v, w, mem', hed, hes, hmem, hea, hINV2, hcond2⟩ := hfacts
  refine p4Run_seq_assoc _ _ _ _ ?_ hres
  intro hres1
  refine p4Run_store p4L38Dst p4L38Src _ ?_ hres1
  intro a' v' mem'' hed' hes' hmem'
  have hva : a' = a := by
    have h1 := hed'.symm.trans hed
    have h2 := (Option.some.inj h1 : (.val (.word a') : ValueHOL 64) = .val (.word a))
    injection h2 with h3
    injection h3 with h4
  subst hva
  have hvv : v' = .val (.word v) := Option.some.inj (hes'.symm.trans hes)
  subst hvv
  have hmem_eq : mem' = mem'' := (Option.some.inj (hmem'.symm.trans hmem)).symm
  subst hmem_eq
  refine p4Run_assign (ofString "i") p4L38I _ ?_
  intro v'' hv''
  have hvw : v'' = .val (.word w) := Option.some.inj (hv''.symm.trans hea)
  subst hvw
  rcases hcond2 with hcond | hclk
  · -- the condition is `0` at the post state: the loop exits immediately
    intro hres2
    have hrw : evaluateHOLFiniteState
        (setVarHOLFinite (ofString "i") (.val (.word w)) {u with memory := mem'})
        (.seq (.while p4Loop38Cond p4Loop38Body) rest) =
        evaluateHOLFiniteState
          (setVarHOLFinite (ofString "i") (.val (.word w)) {u with memory := mem'}) rest := by
      have hc : @evalHOLFinite 64 F _
          (setVarHOLFinite (ofString "i") (.val (.word w)) {u with memory := mem'})
          (fun address => Classical.propDecidable
            ((setVarHOLFinite (ofString "i") (.val (.word w)) {u with memory := mem'}).memaddrs
              address))
          p4Loop38Cond = some (.val (.word 0#64)) := hcond
      rw [evaluateHOLFiniteState_seq_line780,
          evaluateHOLFiniteState_while_fixClockRewrite, hc]
      dsimp only
      rw [if_neg (by decide)]
    rw [hrw] at hres2 ⊢
    exact hexit _ hINV2 hcond hres2
  · -- the clock is positive: apply the induction hypothesis
    have huclk : u.clock = t.clock - 1 := by simp [hu, decClockHOLFinite]
    have hs2clk : (setVarHOLFinite (ofString "i") (.val (.word w))
        {u with memory := mem'}).clock = u.clock := rfl
    exact ih _ hINV2 (by omega)

/-- The loop-31 body obligation for `p4Run_while31`: compose the (bare
`decCall`) body with the while-continuation via the seq bridge.  The whole
`lst_push` engine result is isolated into `hengine`; the invariant transport
and the exit/clock disjunction into `hmidFacts`. -/
theorem p4Run_loop31Body {F : Type} {entry : PanSemStateFiniteExact 64 F}
    {rest : ProgHOL 64} {t u : PanSemStateFiniteExact 64 F}
    (INV : PanSemStateFiniteExact 64 F → Prop)
    (hu : u = decClockHOLFinite t)
    (ih : ∀ mid, INV mid → mid.clock < t.clock →
      PtxRelRunStrong entry (.seq (.while p4Loop31Cond p4Loop31Body) rest) mid)
    (hexit : ∀ t', INV t' → evalAt t' p4Loop31Cond = some (.val (.word 0#64)) →
      PtxRelRunStrong entry rest t')
    (hengine : PtxRelRunStrong entry p4Loop31Body u)
    (hmidFacts : ∀ post, evaluateHOLFiniteState u p4Loop31Body = (none, post) →
      INV post ∧ (evalAt post p4Loop31Cond = some (.val (.word 0#64)) ∨ t.clock ≠ 0)) :
    PtxRelRunStrong entry (.seq p4Loop31Body
      (.seq (.while p4Loop31Cond p4Loop31Body) rest)) u := by
  intro hres
  refine p4Run_seq_bridge p4Loop31Body _ u hengine ?_ hres
  intro post heq
  obtain ⟨hINVp, hcond2⟩ := hmidFacts post heq
  rcases hcond2 with hcond | hclk
  · -- the condition is `0` at the post state: the loop exits immediately
    intro hres2
    have hrw : evaluateHOLFiniteState post
        (.seq (.while p4Loop31Cond p4Loop31Body) rest) =
        evaluateHOLFiniteState post rest := by
      have hc : @evalHOLFinite 64 F _ post
          (fun address => Classical.propDecidable (post.memaddrs address))
          p4Loop31Cond = some (.val (.word 0#64)) := hcond
      rw [evaluateHOLFiniteState_seq_line780,
          evaluateHOLFiniteState_while_fixClockRewrite, hc]
      dsimp only
      rw [if_neg (by decide)]
    rw [hrw] at hres2 ⊢
    exact hexit post hINVp hcond hres2
  · -- the clock is positive: apply the induction hypothesis
    have huclk : u.clock = t.clock - 1 := by simp [hu, decClockHOLFinite]
    have hcl2 : post.clock ≤ u.clock := by
      have hrem := evaluateHOLFiniteState_clock_le u p4Loop31Body
      rw [heq] at hrem
      exact hrem
    exact ih post hINVp (by omega)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
