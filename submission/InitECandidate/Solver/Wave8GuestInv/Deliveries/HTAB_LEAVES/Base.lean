import InitECandidate.Solver.Wave8GuestInv.LeafStatements
import InitECandidate.Solver.Wave8GuestInv.Deliveries.HTAB_LEAVES.OldBounds

/-! Shared infrastructure for the hash-table leaves (`wave8/leaves-htab-opus55`).

* `onOf`: an unconditional bound is a bound under any guard;
* `LocFrame` / `locOnly`: a loop-free program that only writes locals changes nothing but the
  locals and the clock;
* the no-repeat `while` rule (`while_noRepeat`), ported from `wave8/step0-opus55`
  (`PanTerminatingNoRepeat`, proved there), restated over the spec's `LoopActive`,
  `evaluate_ne_of_clock_lt` and `while_unfold_continue`;
* `while_oneWord`: a read-only loop whose only changing local is one word is bounded by
  `(2^64 + 1) * (B + 1)`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8GuestInv.Htab

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## Unconditional bounds -/

theorem onOf {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {p : ProgHOL 64} {K : Nat}
    (h : TerminatingProgBounded p K) : TerminatingProgBoundedOn P p K :=
  fun s hcode _ => h s hcode

theorem straightOn {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (p : ProgHOL 64)
    (hs : extStraightLine p = true) : TerminatingProgBoundedOn P p 0 :=
  onOf (TerminatingProgBounded.straight p hs)

theorem progOn {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {p : ProgHOL 64} {K : Nat}
    (h : ProgBounded p K) : TerminatingProgBoundedOn P p K :=
  onOf (terminatingProgBounded_of_progBounded h)

theorem funOn {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {f : MlS} {K K' : Nat}
    (h : FunBounded f K) (hle : K ≤ K') : TerminatingFunBoundedOn P f K' :=
  (TerminatingFunBoundedOn.of_unconditional (terminatingFunBounded_of_funBounded h)).weaken hle

theorem TerminatingProgBoundedOn.weakenK {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {p : ProgHOL 64} {K K' : Nat} (h : TerminatingProgBoundedOn P p K) (hle : K ≤ K') :
    TerminatingProgBoundedOn P p K' :=
  fun s hcode hP => (h s hcode hP).weaken hle

theorem onFun_of_guestAst {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (i : Nat) (hi : i < Guest.Software.guestAst.length)
    (d : Decl (BitVec 64)) (K : Nat)
    (hd : Guest.Software.guestAst[i] = .function (extractFn d))
    (hprog : TerminatingProgBoundedOn P
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body) K) :
    TerminatingFunBoundedOn P (ofString (extractFn d).name) K :=
  ⟨_, _, _, InitECandidate.Solver.GuestTrapAndLookup.lookup_of_guestAst_getElem i hi (extractFn d) hd,
    hprog⟩

theorem onFun_le {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (i : Nat) (hi : i < Guest.Software.guestAst.length)
    (d : Decl (BitVec 64)) (K : Nat)
    (hd : Guest.Software.guestAst[i] = .function (extractFn d)) {K' : Nat}
    (hprog : TerminatingProgBoundedOn P
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body) K')
    (hle : K' ≤ K) :
    TerminatingFunBoundedOn P (ofString (extractFn d).name) K :=
  (onFun_of_guestAst i hi d K' hd hprog).weaken hle

/-! ## Local frames of loop-free local-only programs -/

/-- `t` agrees with `s` on every field but the locals and the clock. -/
def LocFrame {F : Type} (s t : PanSemStateFiniteExact 64 F) : Prop :=
  t = { s with locals := t.locals, clock := t.clock }

theorem LocFrame.refl {F : Type} (s : PanSemStateFiniteExact 64 F) : LocFrame s s := by
  cases s; rfl

theorem LocFrame.trans {F : Type} {s t u : PanSemStateFiniteExact 64 F}
    (h1 : LocFrame s t) (h2 : LocFrame t u) : LocFrame s u := by
  unfold LocFrame at *
  rw [h2]; rw [h1]

/-- Loop-free programs whose only effects are on locals. -/
def locOnly : ProgHOL 64 → Bool
  | .dec _ _ _ body => locOnly body
  | .seq first second => locOnly first && locOnly second
  | .ite _ yes no => locOnly yes && locOnly no
  | .assign .local _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | _ => false

theorem locFrame_eval {F : Type} : ∀ (p : ProgHOL 64), locOnly p = true →
    ∀ (s : PanSemStateFiniteExact 64 F), LocFrame s (evaluateHOLFiniteState s p).2
  | .skip, _, s => by rw [evaluateHOLFiniteState_skip]; exact LocFrame.refl s
  | .break, _, s => by rw [evaluateHOLFiniteState_break]; exact LocFrame.refl s
  | .continue, _, s => by rw [evaluateHOLFiniteState_continue]; exact LocFrame.refl s
  | .annot _ _, _, s => by rw [evaluateHOLFiniteState_annot]; exact LocFrame.refl s
  | .raise _ _, _, s => by
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split
      · rfl
      · exact LocFrame.refl s
    · exact LocFrame.refl s
  | .return _, _, s => by
    rw [evaluateHOLFiniteState_return]
    split
    · exact LocFrame.refl s
    · split
      · rfl
      · exact LocFrame.refl s
  | .assign kind name e, h, s => by
    cases kind with
    | global => simp [locOnly] at h
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · exact LocFrame.refl s
      · split
        · rfl
        · exact LocFrame.refl s
  | .dec name sh init body, h, s => by
    have hb : locOnly body = true := by simpa [locOnly] using h
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · exact LocFrame.refl s
    · rename_i val _
      split
      · have ih := locFrame_eval body hb (setVarHOLFinite name val s)
        unfold LocFrame at ih ⊢
        dsimp only
        rw [ih]; rfl
      · exact LocFrame.refl s
  | .seq first second, h, s => by
    have h12 : locOnly first = true ∧ locOnly second = true := by
      simpa [locOnly, Bool.and_eq_true] using h
    rw [evaluateHOLFiniteState_seq_line780]
    have ih1 := locFrame_eval first h12.1 s
    rcases hr1 : evaluateHOLFiniteState s first with ⟨r1, mid⟩
    rw [hr1] at ih1
    dsimp only at ih1 ⊢
    cases r1 with
    | none => exact ih1.trans (locFrame_eval second h12.2 mid)
    | some _ => exact ih1
  | .ite cond yes no, h, s => by
    have h12 : locOnly yes = true ∧ locOnly no = true := by
      simpa [locOnly, Bool.and_eq_true] using h
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact locFrame_eval no h12.2 s
      · exact locFrame_eval yes h12.1 s
    · exact LocFrame.refl s
  | .while _ _, h, _ => by simp [locOnly] at h
  | .call _ _ _, h, _ => by simp [locOnly] at h
  | .decCall _ _ _ _ _, h, _ => by simp [locOnly] at h
  | .store _ _, h, _ => by simp [locOnly] at h
  | .storeByte _ _, h, _ => by simp [locOnly] at h
  | .store32 _ _, h, _ => by simp [locOnly] at h
  | .tick, h, _ => by simp [locOnly] at h
  | .primitive _ _ _, h, _ => by simp [locOnly] at h
  | .extCall _ _ _ _ _, h, _ => by simp [locOnly] at h
  | .shMemLoad _ _ _ _, h, _ => by simp [locOnly] at h
  | .shMemStore _ _ _, h, _ => by simp [locOnly] at h

open Lean Elab Tactic Meta in
/-- Close `TerminatingFunBoundedOn P (ofString "f") ?B` by the local hypothesis about the
syntactically same function name (comparing `MlS` literals by unification is very slow). -/
elab "callee_hyp" : tactic => withMainContext do
  let g ← instantiateMVars (← getMainTarget)
  unless g.isAppOfArity ``TerminatingFunBoundedOn 3 do throwError "callee_hyp: bad goal"
  let fn := g.getAppArgs[1]!
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t ← whnfR (← instantiateMVars d.type)
    if t.isAppOfArity ``TerminatingFunBoundedOn 3 && t.getAppArgs[1]! == fn then
      if ← isDefEq t g then
        (← getMainGoal).assign d.toExpr
        replaceMainGoal []
        return
  throwError "callee_hyp: no hypothesis for {fn}"

/-- Walk a body under `GuestInv`: straight-line subprograms cost `0`, `dec`/`seq`/`ite` are
decomposed, calls use a callee bound from the context. Loops are left as goals. -/
macro "htab_walk" : tactic => `(tactic| repeat (first
  | exact straightOn _ rfl
  | apply TerminatingProgBoundedOn.dec_on localsFree_guestInv
  | apply TerminatingProgBoundedOn.seq_guestInv
  | apply TerminatingProgBoundedOn.ite_on
  | (apply TerminatingProgBoundedOn.decCall_guestInv; case hf => callee_hyp)
  | (apply TerminatingProgBoundedOn.call_guestInv; case hf => callee_hyp)
  | (apply TerminatingProgBoundedOn.tailCall_guestInv; case hf => callee_hyp)))

/-- Close `bound ≤ K.«f»` after unfolding `K.«f»`: split every `max`, then `omega`. -/
macro "htab_bound" k:ident : tactic => `(tactic| (simp only [$k:ident, Nat.max_def]; (try split_ifs) <;> omega))

/-- Reduce the structural translation of a guest function body. -/
macro "htab_unfold" d:ident : tactic => `(tactic| dsimp only [extractFn, $d:ident,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map])

end InitECandidate.Solver.Wave8GuestInv.Htab
