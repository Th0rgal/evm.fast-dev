import InitECandidate.Solver.Wave8GuestInv.ContractParts.C09

/-! Counted signed `<s` loop and bundled `PBounded P` combinators for `compute_state_root`. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false

namespace InitECandidate.Solver.Wave8GuestInv.P3Csr

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

inductive IncrBody (c : MlS) : ProgHOL 64 → Prop
  | incr : IncrBody c (.assign .local c (.op .add [.var .local c, .const 1]))
  | seq (first : ProgHOL 64) {tail : ProgHOL 64}
      (avoid : avoidsLocal c first = true) (noCont : noTopContinue first = true)
      (rest : IncrBody c tail) : IncrBody c (.seq first tail)
  | dec (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64}
      (distinct : c ≠ name) (rest : IncrBody c body) : IncrBody c (.dec name shape init body)
  | decCall (name : MlS) (shape : ShapeHOL) (fn : MlS) (args : List (ExpHOL 64))
      {cont : ProgHOL 64} (distinct : c ≠ name) (rest : IncrBody c cont) :
      IncrBody c (.decCall name shape fn args cont)

theorem IncrBody.run {c : MlS} {body : ProgHOL 64} (hb : IncrBody c body) :
    ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      state.locals.lookup c = some (.val (.word w)) →
      (evaluateHOLFiniteState state body).1 ≠ some .continue ∧
      ((evaluateHOLFiniteState state body).1 = none →
        (evaluateHOLFiniteState state body).2.locals.lookup c = some (.val (.word (w + 1)))) := by
  induction hb with
  | incr =>
    intro F state w atC
    have run : evaluateHOLFiniteState state
        (.assign .local c (.op .add [.var .local c, .const 1])) =
        (none, setVarHOLFinite c (.val (.word (w + 1))) state) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, atC, wordOpHOL, wordOp,
        valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
        shapeOfHOLExact, shapeEqHOL]
    rw [run]
    refine ⟨by simp, fun _ => ?_⟩
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  | seq first avoid noCont rest ih =>
    intro F state w atC
    have frame := evaluate_avoidsLocal_flowing c first avoid state
    have noContinue := evaluate_noTopContinue first noCont state
    rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at frame noContinue
      dsimp only at frame noContinue
      cases result with
      | none =>
        dsimp only
        exact ih middle w (by rw [frame (Or.inl rfl)]; exact atC)
      | some _ => exact ⟨noContinue, fun h => by simp at h⟩
  | dec name shape init distinct rest ih =>
    intro F state w atC
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · exact ⟨by simp, by simp⟩
    · rename_i val _
      split
      · have atInner : (setVarHOLFinite name val state).locals.lookup c =
            some (.val (.word w)) := by
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm distinct, atC]
        obtain ⟨t1, t2⟩ := ih (setVarHOLFinite name val state) w atInner
        cases run : evaluateHOLFiniteState (setVarHOLFinite name val state) _ with
        | mk res post =>
          rw [run] at t1 t2
          dsimp only at t1 t2 ⊢
          refine ⟨t1, fun normal => ?_⟩
          rw [PanRunBounded.resVarEq_lookup, if_neg distinct]
          exact t2 normal
      · exact ⟨by simp, by simp⟩
  | @decCall name shape fn args cont distinct rest ih =>
    intro F state w atC
    have hcont : (evaluateHOLFiniteState state (.decCall name shape fn args cont)).1 ≠
        some .continue := by
      intro hc
      rcases hrun : evaluateHOLFiniteState state (.decCall name shape fn args cont) with ⟨r, post⟩
      rw [hrun] at hc; dsimp only at hc; subst hc
      obtain ⟨_, resumed, _, hloc, _, hcr, _⟩ := decCall_flowing (Or.inr (Or.inr rfl)) hrun
      have := (ih resumed w ((hloc c distinct).trans atC)).1
      rw [hcr] at this; exact this rfl
    refine ⟨hcont, fun hnone => ?_⟩
    rcases hrun : evaluateHOLFiniteState state (.decCall name shape fn args cont) with ⟨r, post⟩
    rw [hrun] at hnone; dsimp only at hnone; subst hnone
    obtain ⟨_, resumed, _, hloc, _, hcr, hpost⟩ := decCall_flowing (Or.inl rfl) hrun
    have := (ih resumed w ((hloc c distinct).trans atC)).2
    rw [hcr] at this
    rw [hpost, PanRunBounded.resVarEq_lookup, if_neg distinct]
    exact this rfl

private theorem signed_less_eq (left right : BitVec 64) :
    holAsmSignedLess left right = left.slt right := by
  have bl := left.isLt
  have br := right.isLt
  simp only [holAsmSignedLess, BitVec.slt_eq_decide, BitVec.toInt_eq_msb_cond,
    BitVec.msb_eq_decide]
  repeat (any_goals first | split)
  all_goals simp_all only [decide_eq_true_eq]
  all_goals apply Bool.eq_iff_iff.mpr
  all_goals simp_all [decide_eq_true_eq]
  all_goals omega

def signedUpRank (counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup counter with
  | some (.val (.word w)) => (9223372036854775807 - w.toInt).toNat
  | _ => 0

theorem signedUpRank_le (counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    signedUpRank counter s ≤ 2 ^ 64 := by
  unfold signedUpRank
  split
  · rename_i w _; have := BitVec.le_toInt w; omega
  · omega

theorem while_less_on {names : List String} {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : LocalsOnly names P) (counter : MlS) (bound : ExpHOL 64)
    {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn P body B)
    (hp : Hoare P body (fun r t => r = none → P t))
    (hinc : IncrBody counter body) :
    TerminatingProgBoundedOn P (.while (.cmp .less (.var .local counter) bound) body)
      ((2 ^ 64 + 1) * (B + 1)) := by
  refine TerminatingProgBoundedOn.while_rank (signedUpRank counter)
    (fun s hs => hP.decClock s hs) hbody
    (fun s _ _ _ => signedUpRank_le counter s) ?_
  intro F s hcode hs ⟨result, hcond, hnz⟩ hflow
  change evalAt s _ = _ at hcond
  obtain ⟨w, v, hw, _, hword⟩ := evalAt_cmp s .less _ _ result hcond
  simp only [evalAt, evalHOLExact] at hw
  have hwl : s.locals.lookup counter = some (.val (.word w)) := by simpa using hw
  obtain ⟨hnc_w, hinc_w⟩ := hinc.run (decClockHOLFinite s) w hwl
  have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none :=
    hflow.elim id (fun h => absurd h hnc_w)
  have hP_post : P (evaluateHOLFiniteState (decClockHOLFinite s) body).2 :=
    hp.run (decClockHOLFinite s) hcode (hP.decClock s hs) (by rw [hnone]; simp) hnone
  refine ⟨hP_post, ?_⟩
  have hcmp : wordCmpHOL .less w v = true := by
    by_contra h; simp [h] at hword; exact hnz hword
  have hlt : w.toInt < v.toInt := by
    simpa only [wordCmpHOL, signed_less_eq, BitVec.slt_iff_toInt_lt] using hcmp
  have hvmax := BitVec.toInt_le (x := v)
  have hwmin := BitVec.le_toInt w
  have hwmax := BitVec.toInt_le (x := w)
  have hone : (1 : BitVec 64).toInt = 1 := by decide
  have hnext : (w + 1).toInt = w.toInt + 1 := by
    rw [BitVec.toInt_add, hone]; apply Int.bmod_eq_of_le <;> omega
  simp only [signedUpRank, hinc_w hnone, hwl, hnext]
  omega

theorem hoare_while_less_preserve {names : List String}
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : LocalsOnly names P) (counter : MlS) (bound : ExpHOL 64) {body : ProgHOL 64}
    (hp : Hoare P body (fun r t => r = none → P t))
    (hinc : IncrBody counter body)
    (hnb : noTopBreak body = true) :
    Hoare P (.while (.cmp .less (.var .local counter) bound) body) (fun r t => r = none → P t) := by
  refine ⟨fun {F} s hcode hs _ hr => ?_⟩
  rcases hrun : evaluateHOLFiniteState s (.while (.cmp .less (.var .local counter) bound) body) with
    ⟨r, post⟩
  rw [hrun] at hr; dsimp only at hr; subst hr
  suffices ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F),
      st.clock = k → st.code = originalRuntimeCode → P st →
      evaluateHOLFiniteState st (.while (.cmp .less (.var .local counter) bound) body) =
        (none, post) → P post from
    this s.clock s rfl hcode hs hrun
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st hk st_code hPst hst_run
    rw [evaluateHOLFiniteState_while_total] at hst_run
    split at hst_run
    · rename_i res hcond
      split at hst_run
      · split at hst_run
        · simp at hst_run
        · dsimp only at hst_run
          rw [fixClockHOLFinite_evaluateState] at hst_run
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
          have hmeta := (evaluateHOLFiniteState_metadata (decClockHOLFinite st) body).1
          have hno_brk := evaluate_noTopBreak body hnb (decClockHOLFinite st)
          change evalAt st _ = _ at hcond
          obtain ⟨w, _, hw, _, _⟩ := evalAt_cmp st .less _ _ res hcond
          simp only [evalAt, evalHOLExact] at hw
          have hwl : (decClockHOLFinite st).locals.lookup counter = some (.val (.word w)) := by
            simpa [decClockHOLFinite] using hw
          obtain ⟨hnc_w, _⟩ := hinc.run (decClockHOLFinite st) w hwl
          rcases bRun : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨r1, mid⟩
          rw [bRun] at hst_run hrem hmeta hnc_w hno_brk
          have hclk_lt : mid.clock < k := by change mid.clock ≤ st.clock - 1 at hrem; omega
          cases r1 with
          | none =>
            have hPmid := hp.run (decClockHOLFinite st) st_code (hP.decClock st hPst)
              (by rw [bRun]; simp) (by rw [bRun])
            rw [bRun] at hPmid
            exact ih mid.clock hclk_lt mid rfl (hmeta.trans st_code) hPmid hst_run
          | some r1' =>
            cases r1' with
            | «continue» => exact absurd rfl hnc_w
            | «break» => exact absurd rfl hno_brk
            | _ => simp at hst_run
      · simp at hst_run; obtain ⟨_, rfl⟩ := hst_run; exact hPst
    · simp at hst_run

structure PBounded (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (prog : ProgHOL 64) (K : Nat) : Prop where
  bounded : TerminatingProgBoundedOn P prog K
  hoare : Hoare P prog (fun r t => r = none → P t)

theorem PBounded.skip {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} :
    PBounded P .skip 0 :=
  ⟨TerminatingProgBoundedOn.of_clock (fun s => clock_skip s), Hoare.skip (fun _ h _ => h)⟩

theorem PBounded.seq {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {first second : ProgHOL 64} {a b : Nat}
    (h1 : PBounded P first a) (h2 : PBounded P second b) :
    PBounded P (.seq first second) (a + b) :=
  ⟨TerminatingProgBoundedOn.seq_hoare h1.bounded h1.hoare h2.bounded,
   Hoare.seq ⟨fun s hc hP hnt => ⟨h1.hoare.run s hc hP hnt, fun hr h => absurd h hr⟩⟩ h2.hoare⟩

theorem PBounded.ite {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (cond : ExpHOL 64) {yes no : ProgHOL 64} {a b : Nat}
    (hy : PBounded P yes a) (hn : PBounded P no b) :
    PBounded P (.ite cond yes no) (max a b) :=
  ⟨TerminatingProgBoundedOn.ite_on hy.bounded hn.bounded,
   Hoare.ite (Hoare.mono hy.hoare (fun _ h => h.1))
     (Hoare.mono hn.hoare (fun _ h => h.1))
     (fun _ _ hr => absurd hr (by simp))⟩

theorem PBounded.assignLocal {names : List String}
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : LocalsOnly names P) (name : MlS) (hne : ∀ n ∈ names, ofString n ≠ name)
    (e : ExpHOL 64) :
    PBounded P (.assign .local name e) 0 :=
  ⟨TerminatingProgBoundedOn.of_clock (fun s => clock_assign s .local name e),
   Hoare.assign (fun s v hs _ _ => hP.setVar hne v s hs) (fun _ _ hr => absurd hr (by simp))⟩

theorem PBounded.dec {names : List String}
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : LocalsOnly names P) (name : MlS) (hne : ∀ n ∈ names, ofString n ≠ name)
    (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64} {K : Nat}
    (hb : PBounded P body K) :
    PBounded P (.dec name shape init body) K :=
  ⟨TerminatingProgBoundedOn.dec_onLocals hP name hne shape init hb.bounded,
   Hoare.dec (names := names) (P' := P) hne
     (fun s v hs _ => hP.setVar hne v s hs)
     hb.hoare
     (fun _ t locals hlk h hr => hP t locals t.clock hlk (h hr))
     (fun _ _ hr => absurd hr (by simp))⟩

theorem PBounded.whileLess {names : List String}
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : LocalsOnly names P) (counter : MlS) (bound : ExpHOL 64) {body : ProgHOL 64} {B : Nat}
    (hb : PBounded P body B) (hinc : IncrBody counter body) (hnb : noTopBreak body = true) :
    PBounded P (.while (.cmp .less (.var .local counter) bound) body) ((2 ^ 64 + 1) * (B + 1)) :=
  ⟨while_less_on hP counter bound hb.bounded hb.hoare hinc,
   hoare_while_less_preserve hP counter bound hb.hoare hinc hnb⟩

theorem PBounded.decCallTrans {names : List String}
    {P R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {fname : MlS} {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {B Bc : Nat}
    (hf : TerminatingFunBoundedOn Pc fname B)
    (hP : LocalsOnly names P)
    (name : MlS) (hne : ∀ n ∈ names, ofString n ≠ name)
    (shape : ShapeHOL) (args : List (ExpHOL 64)) {cont : ProgHOL 64}
    (hentry : CallEntryOn P Pc fname args)
    (hres : DecCallResumeOn P R name fname args)
    (hcont : TerminatingProgBoundedOn R cont Bc)
    (hhoare : Hoare R cont (fun r t => r = none → P t)) :
    PBounded P (.decCall name shape fname args cont) (B + Bc + 1) := by
  refine ⟨TerminatingProgBoundedOn.decCall_on hf name shape args hentry hres hcont, ?_⟩
  refine ⟨fun {F} s hc hs hnt => ?_⟩
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  rcases ha : evalListHOLFinite s
      (h := fun address => Classical.propDecidable (s.memaddrs address)) args with _ | vs
  · simp only [ha]; intro he; cases he
  · simp only [ha] at hnt ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨b, callee, ret⟩
    · simp only [hl]; intro he; cases he
    · simp only [hl] at hnt ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hm := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) b).1
        rcases hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) b with ⟨r, t⟩
        simp only [hr] at hnt hm ⊢
        change t.code = s.code at hm
        cases r with
        | none => intro he; cases he
        | some r =>
          cases r with
          | returned v =>
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) shape &&
                shapeEqHOL (shapeOfHOLExact v) ret) = true
            · simp only [hsh, ↓reduceIte] at hnt ⊢
              have hR := hres s vs b callee ret v t hc hs ha hl hr
              have h := hhoare.run (setVarHOLFinite name v { t with locals := s.locals })
                (hm.trans hc) hR hnt
              intro hn
              exact hP _ _ _ (fun n hn' => resVarEq_lookup_ne _ _ _ _ (hne n hn')) (h hn)
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte]; intro he; cases he
          | timeOut => simp at hnt
          | _ => intro he; cases he

end InitECandidate.Solver.Wave8GuestInv.P3Csr
