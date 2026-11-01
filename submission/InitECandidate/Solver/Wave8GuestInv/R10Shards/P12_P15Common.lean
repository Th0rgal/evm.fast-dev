import InitECandidate.Solver.Wave8GuestInv.Expressions

/-! Shared R11 structural combinators and memory/counter loop bounds for R10Shards (P13, P12, P15).
Imports `InitECandidate.Solver.Wave8GuestInv.Expressions` (never `LeafStatements.lean`), so zero
unproved `sorry` stubs exist in the dependency cone. -/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.P12_P15.Common

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

theorem nat_max_eq (a b : Nat) : Nat.max a b = max a b := rfl

theorem TerminatingProgBoundedOn.weaken' {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {prog : ProgHOL 64} {K K' : Nat} (h : TerminatingProgBoundedOn P prog K) (hle : K ≤ K') :
    TerminatingProgBoundedOn P prog K' :=
  fun s hc hP => (h s hc hP).weaken hle

theorem straightOn (prog : ProgHOL 64) (hs : extStraightLine prog = true) :
    TerminatingProgBoundedOn GuestInv prog 0 :=
  fun s hc _ => TerminatingProgBounded.straight prog hs s hc

theorem dec_guestInv (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64}
    {K : Nat} (hbody : TerminatingProgBoundedOn GuestInv body K) :
    TerminatingProgBoundedOn GuestInv (.dec name shape init body) K :=
  TerminatingProgBoundedOn.dec_on localsFree_guestInv name shape init hbody

theorem call_guestInv' {fname : MlS} {B : Nat} {destination : Option (VarKind × MlS)}
    {arguments : List (ExpHOL 64)} (hf : TerminatingFunBoundedOn GuestInv fname B) :
    TerminatingProgBoundedOn GuestInv (.call (some (destination, none)) fname arguments) (B + 1) :=
  TerminatingProgBoundedOn.call_guestInv hf destination arguments

theorem decCall_guestInv' {fname : MlS} {B Bc : Nat} {name : MlS} {shape : ShapeHOL}
    {arguments : List (ExpHOL 64)} {continuation : ProgHOL 64}
    (hf : TerminatingFunBoundedOn GuestInv fname B)
    (hcont : TerminatingProgBoundedOn GuestInv continuation Bc) :
    TerminatingProgBoundedOn GuestInv (.decCall name shape fname arguments continuation)
      (B + Bc + 1) :=
  TerminatingProgBoundedOn.decCall_guestInv hf name shape arguments hcont

theorem callHandle_guestInv' {fname : MlS} {B Bh : Nat} {destination : Option (VarKind × MlS)}
    {exn var : MlS} {handler : ProgHOL 64} {arguments : List (ExpHOL 64)}
    (hf : TerminatingFunBoundedOn GuestInv fname B)
    (hh : TerminatingProgBoundedOn GuestInv handler Bh) :
    TerminatingProgBoundedOn GuestInv
      (.call (some (destination, some (exn, var, handler))) fname arguments) (B + Bh + 1) :=
  TerminatingProgBoundedOn.callHandle_guestInv hf destination exn var hh arguments

theorem guestInv_decClock {F : Type} (s : PanSemStateFiniteExact 64 F) (hs : GuestInv s) :
    GuestInv (decClockHOLFinite s) :=
  guestInv_with_locals_clock s s.locals _ hs

/-! ### 1. Counted loops `while i < X { ... ; i = i + 1 }` -/

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
        have kept := frame (Or.inl rfl)
        exact ih middle w (by rw [kept]; exact atC)
      | some r =>
        dsimp only
        exact ⟨noContinue, fun h => by simp at h⟩
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
      rw [hrun] at hc
      dsimp only at hc
      subst hc
      obtain ⟨_, resumed, _, hloc, _, hcr, _⟩ :=
        decCall_flowing (Or.inr (Or.inr rfl)) hrun
      have atR : resumed.locals.lookup c = some (.val (.word w)) := (hloc c distinct).trans atC
      have := (ih resumed w atR).1
      rw [hcr] at this
      exact this rfl
    refine ⟨hcont, fun hnone => ?_⟩
    rcases hrun : evaluateHOLFiniteState state (.decCall name shape fn args cont) with ⟨r, post⟩
    rw [hrun] at hnone
    dsimp only at hnone
    subst hnone
    obtain ⟨_, resumed, _, hloc, _, hcr, hpost⟩ := decCall_flowing (Or.inl rfl) hrun
    have atR : resumed.locals.lookup c = some (.val (.word w)) := (hloc c distinct).trans atC
    have := (ih resumed w atR).2
    rw [hcr] at this
    rw [hpost, PanRunBounded.resVarEq_lookup, if_neg distinct]
    exact this rfl

def cmpRank (op : Cmp) (a : BitVec 64) : Nat :=
  match op with
  | .less => (a.toNat + 2 ^ 63) % 2 ^ 64
  | _ => a.toNat

theorem cmpRank_lt (op : Cmp) (hop : op = .less ∨ op = .lower) (a b : BitVec 64)
    (h : wordCmpHOL op a b = true) : cmpRank op a < cmpRank op b := by
  have ha := a.isLt
  have hb := b.isLt
  rcases hop with rfl | rfl
  · simp only [wordCmpHOL, holAsmSignedLess] at h
    simp only [cmpRank]
    split_ifs at h <;> simp_all <;> omega
  · simp only [wordCmpHOL, decide_eq_true_eq, BitVec.lt_def] at h
    simp only [cmpRank]
    omega

theorem cmpRank_succ (op : Cmp) (a b : BitVec 64) (h : cmpRank op a < cmpRank op b) :
    cmpRank op (a + 1) = cmpRank op a + 1 := by
  have ha := a.isLt
  have hb := b.isLt
  have hs : (a + 1).toNat = (a.toNat + 1) % 2 ^ 64 := by simp [BitVec.toNat_add]
  cases op <;> simp only [cmpRank] at h ⊢ <;> omega

theorem cmpRank_le (op : Cmp) (a : BitVec 64) : cmpRank op a < 2 ^ 64 := by
  have := a.isLt
  cases op <;> simp only [cmpRank] <;> omega

def counterGap (op : Cmp) (i X : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup i, s.locals.lookup X with
  | some (.val (.word a)), some (.val (.word b)) => cmpRank op b - cmpRank op a
  | _, _ => 0

theorem while_counter_guestInv (op : Cmp) (hop : op = .less ∨ op = .lower) (i X : MlS)
    {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B) (hinc : IncrBody i body)
    (hX : avoidsLocal X body = true) :
    TerminatingProgBoundedOn GuestInv (.while (.cmp op (.var .local i) (.var .local X)) body)
      ((2 ^ 64 + 1) * (B + 1)) := by
  refine @TerminatingProgBoundedOn.while_rank GuestInv
    (.cmp op (.var .local i) (.var .local X)) body B (2 ^ 64)
    (counterGap op i X)
    (fun s hs => guestInv_decClock s hs) hbody ?_ ?_
  · intro F s _ _ _
    simp only [counterGap]
    split
    · rename_i a b _ _
      have := cmpRank_le op b
      omega
    · omega
  · intro F s _ hs hact hflow
    refine ⟨guestInv_evaluate _ _ (guestInv_decClock s hs), ?_⟩
    obtain ⟨word, hw, hnz⟩ := hact
    change evalAt s _ = _ at hw
    obtain ⟨a, b, ha, hb, hword⟩ := evalAt_cmp s op _ _ word hw
    simp only [evalAt, evalHOLExact] at ha hb
    have hia : s.locals.lookup i = some (.val (.word a)) := by simpa using ha
    have hXb : s.locals.lookup X = some (.val (.word b)) := by simpa using hb
    have hcmp : wordCmpHOL op a b = true := by
      by_contra hc
      simp [hc] at hword
      exact hnz hword
    have hlt := cmpRank_lt op hop a b hcmp
    obtain ⟨hnc, hinc'⟩ := hinc.run (decClockHOLFinite s) a hia
    have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none := by
      rcases hflow with h | h
      · exact h
      · exact absurd h hnc
    have hi' := hinc' hnone
    have hX' := evaluate_avoidsLocal_flowing X body hX (decClockHOLFinite s) (Or.inl hnone)
    have hX'' : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup X =
        some (.val (.word b)) := hX'.trans hXb
    have hsucc := cmpRank_succ op a b hlt
    simp only [counterGap, hi', hX'', hia, hXb]
    omega

/-! ### 2. Constant-bounded counter loops (signed & unsigned, arbitrary step) -/

/-- General semantic counter effect `counter := counter + step` on continuing runs. -/
def CounterStep (counter : MlS) (step : BitVec 64) (body : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (w : BitVec 64),
    s.locals.lookup counter = some (.val (.word w)) →
    let out := evaluateHOLFiniteState s body
    (out.1 = none ∨ out.1 = some .continue) →
    out.2.locals.lookup counter = some (.val (.word (w + step)))

theorem CounterStep.assign (counter : MlS) (step : BitVec 64) :
    CounterStep counter step (.assign .local counter (.op .add [.var .local counter, .const step])) := by
  intro F s w hlocal
  have run : evaluateHOLFiniteState s
      (.assign .local counter (.op .add [.var .local counter, .const step])) =
      (none, setVarHOLFinite counter (.val (.word (w + step))) s) := by
    simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact,
      hlocal, wordOpHOL, wordOp, valueIsWord, valueWord,
      lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
      shapeOfHOLExact, shapeEqHOL]
  rw [run]
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

theorem CounterStep.sub_one (counter : MlS) :
    CounterStep counter (-1) (.assign .local counter (.op .sub [.var .local counter, .const 1])) := by
  intro F s w hlocal
  have run : evaluateHOLFiniteState s
      (.assign .local counter (.op .sub [.var .local counter, .const 1])) =
      (none, setVarHOLFinite counter (.val (.word (w - 1))) s) := by
    simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact,
      hlocal, wordOpHOL, wordOp, valueIsWord, valueWord,
      lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
      shapeOfHOLExact, shapeEqHOL]
  rw [run]
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, BitVec.sub_eq_add_neg]

theorem CounterStep.seq (counter : MlS) (step : BitVec 64) (first : ProgHOL 64)
    {rest : ProgHOL 64} (havoid : avoidsLocal counter first = true)
    (hnocont : noTopContinue first = true) (hrest : CounterStep counter step rest) :
    CounterStep counter step (.seq first rest) := by
  intro F s w hlocal
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780]
  cases hrun : evaluateHOLFiniteState s first with
  | mk r mid =>
    have hkeep := evaluate_avoidsLocal_flowing counter first havoid s
    have hnc := evaluate_noTopContinue first hnocont s
    rw [hrun] at hkeep hnc
    cases r with
    | none =>
      dsimp only at hkeep ⊢
      exact hrest mid w ((hkeep (Or.inl rfl)).trans hlocal)
    | some _ =>
      dsimp only at hnc ⊢
      intro hflow
      rcases hflow with h | h
      · cases h
      · exact False.elim (hnc h)

theorem CounterStep.suffix (counter : MlS) (step : BitVec 64) {first : ProgHOL 64}
    (last : ProgHOL 64) (hfirst : CounterStep counter step first)
    (havoid : avoidsLocal counter last = true) :
    CounterStep counter step (.seq first last) := by
  intro F s w hlocal
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780]
  cases hrun : evaluateHOLFiniteState s first with
  | mk r mid =>
    have h := hfirst s w hlocal
    dsimp only at h
    rw [hrun] at h
    cases r with
    | none =>
      dsimp only at h ⊢
      intro hflow
      have hkeep := evaluate_avoidsLocal_flowing counter last havoid mid
        (hflow.elim Or.inl (fun h => Or.inr (Or.inr h)))
      exact hkeep.trans (h (Or.inl rfl))
    | some _ =>
      dsimp only at h ⊢
      exact h

theorem CounterStep.dec (counter : MlS) (step : BitVec 64) (name : MlS)
    (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64}
    (hne : counter ≠ name) (hbody : CounterStep counter step body) :
    CounterStep counter step (.dec name shape init body) := by
  intro F s w hlocal
  dsimp only
  intro hflow
  cases hrun : evaluateHOLFiniteState s (.dec name shape init body) with
  | mk result post =>
    rw [hrun] at hflow
    dsimp only at hflow ⊢
    obtain ⟨value, inner, hinner, hrestore⟩ :=
      dec_flowing (hflow.elim Or.inl (fun h => Or.inr (Or.inr h))) hrun
    have hentry : (setVarHOLFinite name value s).locals.lookup counter = some (.val (.word w)) := by
      simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne] using hlocal
    have h := hbody (setVarHOLFinite name value s) w hentry
    dsimp only at h
    rw [hinner] at h
    dsimp only at h
    rw [hrestore, PanRunBounded.resVarEq_lookup]
    simpa [hne] using h hflow

theorem CounterStep.decCall (counter : MlS) (step : BitVec 64) (name : MlS)
    (shape : ShapeHOL) (fname : MlS) (args : List (ExpHOL 64)) {body : ProgHOL 64}
    (hne : counter ≠ name) (hbody : CounterStep counter step body) :
    CounterStep counter step (.decCall name shape fname args body) := by
  intro F s w hlocal
  dsimp only
  intro hflow
  cases hrun : evaluateHOLFiniteState s (.decCall name shape fname args body) with
  | mk result post =>
    rw [hrun] at hflow
    dsimp only at hflow ⊢
    obtain ⟨_, resumed, _, hpres, _, hinner, hrestore⟩ :=
      decCall_flowing (hflow.elim Or.inl (fun h => Or.inr (Or.inr h))) hrun
    have h := hbody resumed w ((hpres counter hne).trans hlocal)
    dsimp only at h
    rw [hinner] at h
    dsimp only at h
    rw [hrestore, PanRunBounded.resVarEq_lookup]
    simpa [hne] using h hflow

macro "counter_step" : tactic => `(tactic| repeat (first
  | exact CounterStep.assign _ _
  | exact CounterStep.sub_one _
  | apply CounterStep.dec _ _ _ _ _ (by decide)
  | apply CounterStep.decCall _ _ _ _ _ _ (by decide)
  | apply CounterStep.seq _ _ _ rfl rfl))

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

theorem while_up_signed_const_guestInv (counter : MlS) (step limit : BitVec 64)
    {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B)
    (hadd : CounterStep counter step body)
    (hstep : 0 < step.toInt)
    (hlim : limit.toInt + step.toInt ≤ 9223372036854775808) :
    TerminatingProgBoundedOn GuestInv
      (.while (.cmp .less (.var .local counter) (.const limit)) body)
      ((2 ^ 64 + 1) * (B + 1)) := by
  refine @TerminatingProgBoundedOn.while_rank GuestInv
    (.cmp .less (.var .local counter) (.const limit)) body B (2 ^ 64)
    (signedUpRank counter)
    (fun s hs => guestInv_decClock s hs) hbody ?_ ?_
  · intro F s _ _ _
    unfold signedUpRank
    split
    · rename_i w _
      have := BitVec.le_toInt w
      omega
    · omega
  · intro F s _ hs hact hflow
    refine ⟨guestInv_evaluate _ _ (guestInv_decClock s hs), ?_⟩
    obtain ⟨word, hw, hnz⟩ := hact
    change evalAt s _ = _ at hw
    obtain ⟨w, v, hl, hv, hword⟩ := evalAt_cmp s .less _ _ word hw
    have hv_eq : v = limit := by simpa [evalAt, evalHOLExact] using hv.symm
    subst v
    have hlw : s.locals.lookup counter = some (.val (.word w)) := by simpa [evalAt, evalHOLExact] using hl
    have hcmp : wordCmpHOL .less w limit = true := by
      by_cases hc : wordCmpHOL .less w limit = true
      · exact hc
      · simp [hc] at hword; exact absurd hword hnz
    have hlt : w.toInt < limit.toInt := by
      simpa only [wordCmpHOL, signed_less_eq, BitVec.slt_iff_toInt_lt] using hcmp
    have hwmin := BitVec.le_toInt w
    have hwmax := BitVec.toInt_le (x := w)
    have hnext : (w + step).toInt = w.toInt + step.toInt := by
      rw [BitVec.toInt_add]
      apply Int.bmod_eq_of_le <;> omega
    have heff := hadd (decClockHOLFinite s) w hlw hflow
    simp only [signedUpRank, heff, hlw, hnext]
    omega

def constUpRank (counter : MlS) (limit : BitVec 64) {F : Type}
    (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup counter with
  | some (.val (.word w)) => limit.toNat - w.toNat
  | _ => 0

theorem while_up_unsigned_const_guestInv (counter : MlS) (limit : BitVec 64)
    {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B)
    (hadd : CounterStep counter 1 body) :
    TerminatingProgBoundedOn GuestInv
      (.while (.cmp .lower (.var .local counter) (.const limit)) body)
      ((limit.toNat + 1) * (B + 1)) := by
  refine @TerminatingProgBoundedOn.while_rank GuestInv
    (.cmp .lower (.var .local counter) (.const limit)) body B limit.toNat
    (constUpRank counter limit)
    (fun s hs => guestInv_decClock s hs) hbody
    (fun _ _ _ _ => by unfold constUpRank; split <;> omega) ?_
  intro F s _ hs hact hflow
  refine ⟨guestInv_evaluate _ _ (guestInv_decClock s hs), ?_⟩
  obtain ⟨word, hw, hnz⟩ := hact
  change evalAt s _ = _ at hw
  obtain ⟨w, v, hl, hv, hword⟩ := evalAt_cmp s .lower _ _ word hw
  have hv_eq : v = limit := by simpa [evalAt, evalHOLExact] using hv.symm
  subst v
  have hlw : s.locals.lookup counter = some (.val (.word w)) := by simpa [evalAt, evalHOLExact] using hl
  have hcmp : wordCmpHOL .lower w limit = true := by
    by_cases hc : wordCmpHOL .lower w limit = true
    · exact hc
    · simp [hc] at hword; exact absurd hword hnz
  have hlt : w.toNat < limit.toNat := by
    simpa only [wordCmpHOL, decide_eq_true_eq, BitVec.lt_def] using hcmp
  have hvmax := limit.isLt
  have hone : (1 : BitVec 64).toNat = 1 := by decide
  have hnext : (w + 1).toNat = w.toNat + 1 := by
    rw [BitVec.toNat_add, hone]
    apply Nat.mod_eq_of_lt; omega
  have heff := hadd (decClockHOLFinite s) w hlw hflow
  simp only [constUpRank, heff, hlw, hnext]
  omega

def subRank (counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup counter with
  | some (.val (.word w)) => w.toNat
  | _ => 0

theorem while_down_unsigned_guestInv (counter : MlS) {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B)
    (hsub : CounterStep counter (-1) body) :
    TerminatingProgBoundedOn GuestInv
      (.while (.cmp .lower (.const 0) (.var .local counter)) body)
      ((2 ^ 64 + 1) * (B + 1)) := by
  refine @TerminatingProgBoundedOn.while_rank GuestInv
    (.cmp .lower (.const 0) (.var .local counter)) body B (2 ^ 64)
    (subRank counter)
    (fun s hs => guestInv_decClock s hs) hbody ?_ ?_
  · intro F s _ _ _
    unfold subRank
    split
    · rename_i w _
      exact Nat.le_of_lt w.isLt
    · omega
  · intro F s _ hs hact hflow
    refine ⟨guestInv_evaluate _ _ (guestInv_decClock s hs), ?_⟩
    obtain ⟨word, hw, hnz⟩ := hact
    change evalAt s _ = _ at hw
    obtain ⟨z, w, hz, hlw, hword⟩ := evalAt_cmp s .lower _ _ word hw
    have hz0 : z = 0#64 := by simpa [evalAt, evalHOLExact] using hz.symm
    subst z
    have hlookup : s.locals.lookup counter = some (.val (.word w)) := by simpa [evalAt, evalHOLExact] using hlw
    have hwpos : 0 < w.toNat := by
      by_contra hc
      have hw0 : w = 0#64 := BitVec.eq_of_toNat_eq (by simpa using Nat.eq_zero_of_not_pos hc)
      subst w
      simp [wordCmpHOL] at hword
      exact hnz hword
    have heff := hsub (decClockHOLFinite s) w hlookup hflow
    have hpost : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup counter =
        some (.val (.word (w - 1))) := by simpa only [BitVec.sub_eq_add_neg] using heff
    simp only [subRank, hpost, hlookup]
    rw [BitVec.toNat_sub]
    change (18446744073709551615 + w.toNat) % 18446744073709551616 < w.toNat
    have := w.isLt
    omega

/-! ### 3. Capped downward counters (`div64by32`, `udivmod`, `divmnu` Loop #3) -/

def locCapInv (name : String) (C : Nat) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ locN s name ≤ C

theorem while_down_first_capped_on (op : Cmp) (hop : op = .less ∨ op = .lower)
    (counter : String) {C B : Nat} {tail : ProgHOL 64}
    (htail : TerminatingProgBoundedOn GuestInv tail B)
    (havoid : avoidsLocal (ofString counter) tail = true) :
    TerminatingProgBoundedOn (locCapInv counter C)
      (.while (.cmp op (.const 0#64) (.var .local (ofString counter)))
        (.seq (.assign .local (ofString counter) (.op .sub [.var .local (ofString counter), .const 1#64])) tail))
      ((C + 1) * (B + 1)) := by
  have hb : TerminatingProgBoundedOn (locCapInv counter C)
      (.seq (.assign .local (ofString counter) (.op .sub [.var .local (ofString counter), .const 1#64])) tail) B := by
    intro F s hc hP
    simpa only [Nat.zero_add] using
      (TerminatingProgBoundedOn.seq_guestInv (straightOn _ rfl) htail s hc hP.1)
  refine @TerminatingProgBoundedOn.while_rank (locCapInv counter C)
    (.cmp op (.const 0#64) (.var .local (ofString counter))) _ B C
    (fun s => locN s counter)
    (fun s hP => ⟨guestInv_decClock s hP.1, hP.2⟩)
    hb
    (fun _ _ hP _ => hP.2)
    ?_
  intro F s _ hP hact hflow
  obtain ⟨word, hw, hnz⟩ := hact
  change evalAt s _ = _ at hw
  obtain ⟨z, w, hz, hlw, hword⟩ := evalAt_cmp s op _ _ word hw
  have hz0 : z = 0#64 := by simpa [evalAt, evalHOLExact] using hz.symm
  subst hz0
  have hlookup : s.locals.lookup (ofString counter) = some (.val (.word w)) := by
    simpa [evalAt, evalHOLExact] using hlw
  have hwpos : 0 < w.toNat := by
    by_contra hc
    have hw0 : w = 0#64 := BitVec.eq_of_toNat_eq (by simpa using Nat.eq_zero_of_not_pos hc)
    subst hw0
    rcases hop with rfl | rfl <;> simp [wordCmpHOL, holAsmSignedLess] at hword <;> exact hnz hword
  have hass : evaluateHOLFiniteState (decClockHOLFinite s)
      (.assign .local (ofString counter) (.op .sub [.var .local (ofString counter), .const 1#64])) =
      (none, setVarHOLFinite (ofString counter) (.val (.word (w - 1#64))) (decClockHOLFinite s)) := by
    simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, decClockHOLFinite, hlookup,
      wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact,
      setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
  rw [evaluateHOLFiniteState_seq_line780, hass] at hflow ⊢
  dsimp only at hflow ⊢
  have hkeep := evaluate_avoidsLocal_flowing (ofString counter) tail havoid
    (setVarHOLFinite (ofString counter) (.val (.word (w - 1#64))) (decClockHOLFinite s))
    (hflow.elim Or.inl (fun h => Or.inr (Or.inr h)))
  have hpost_lookup : (evaluateHOLFiniteState
      (setVarHOLFinite (ofString counter) (.val (.word (w - 1#64))) (decClockHOLFinite s)) tail).2.locals.lookup (ofString counter) =
      some (.val (.word (w - 1#64))) := by
    simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE] using hkeep
  have hsub : (w - 1#64).toNat = w.toNat - 1 := by
    rw [BitVec.toNat_sub]
    change (18446744073709551615 + w.toNat) % 18446744073709551616 = w.toNat - 1
    have := w.isLt
    omega
  have hloc_before : locN s counter = w.toNat := by simp [locN, hlookup]
  have hloc_after : locN (evaluateHOLFiniteState
      (setVarHOLFinite (ofString counter) (.val (.word (w - 1#64))) (decClockHOLFinite s)) tail).2 counter = w.toNat - 1 := by
    unfold locN
    rw [hpost_lookup]
    exact hsub
  refine ⟨⟨guestInv_evaluate _ _ (guestInv_setVar _ _ _ (guestInv_decClock s hP.1)), ?_⟩, ?_⟩
  · have := hP.2; omega
  · omega

theorem dec_const_cap_guestInv (counter : String) (c : BitVec 64) {body : ProgHOL 64} {B : Nat}
    (hb : TerminatingProgBoundedOn (locCapInv counter c.toNat) body B) :
    TerminatingProgBoundedOn GuestInv (.dec (ofString counter) .one (.const c) body) B := by
  intro F state hcode hg hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only [evalHOLExact] at hnt ⊢
  rw [if_pos (show shapeEqHOL ShapeHOL.one (shapeOfHOLExact (.val (.word c))) = true by simp [shapeOfHOLExact, shapeEqHOL])] at hnt ⊢
  dsimp only at hnt ⊢
  have hcap : locCapInv counter c.toNat (setVarHOLFinite (ofString counter) (.val (.word c)) state) := by
    refine ⟨guestInv_setVar _ _ state hg, ?_⟩
    simp [locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  simpa [setVarHOLFinite] using hb (setVarHOLFinite (ofString counter) (.val (.word c)) state) hcode hcap hnt

/-! ### 4. Ordinary-domain memory walks (`memcpy`, `memzero`, `keccak256`, `divmnu` Loop #1) -/

theorem ordinaryDomain_interval (a : BitVec 64) (h : ordinaryDomain a) :
    sourceBase ≤ a.toNat ∧ a.toNat + 8 ≤ heapEnd := by
  unfold ordinaryDomain at h
  rw [StackRemove.mem_addresses] at h
  obtain ⟨i, hi, rfl⟩ := h
  simp only [StackRemove.bytesInWord, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  norm_num [sourceBase, heapEnd, stackStart, ramEnd, ramStart, ramSize, stackSize, globalsWords] at hi ⊢
  omega

theorem byteAlign_toNat (a : BitVec 64) :
    (panByteAlignHOL a).toNat = a.toNat / 8 * 8 := by
  have ha := a.isLt
  change (a.toNat / 8 * 8) % 2 ^ 64 = a.toNat / 8 * 8
  omega

theorem ordinaryDomain_byte_interval (a : BitVec 64) (h : ordinaryDomain (panByteAlignHOL a)) :
    sourceBase ≤ a.toNat ∧ a.toNat < heapEnd := by
  have hi := ordinaryDomain_interval _ h
  rw [byteAlign_toNat] at hi
  norm_num [sourceBase] at hi ⊢
  omega

def domainRank (a : BitVec 64) : Nat :=
  if sourceBase ≤ a.toNat ∧ a.toNat < heapEnd then heapEnd - a.toNat else 0

theorem domainRank_bound (a : BitVec 64) : domainRank a ≤ domainBytes + 1 := by
  unfold domainRank domainBytes
  split_ifs <;> omega

theorem domainRank_add_lt (a : BitVec 64) (step : Nat)
    (ha : sourceBase ≤ a.toNat ∧ a.toNat < heapEnd)
    (hstep : 0 < step) (hsmall : step ≤ 256) :
    domainRank (a + BitVec.ofNat 64 step) < domainRank a := by
  have hend : heapEnd + 256 < 2 ^ 64 := by decide
  have hadd : (a + BitVec.ofNat 64 step).toNat = a.toNat + step := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  unfold domainRank
  rw [if_pos ha, hadd]
  split_ifs <;> omega

def WordExpression (e : ExpHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some v →
    ∃ w : BitVec 64, v = .val (.word w)

theorem WordExpression.const (w : BitVec 64) : WordExpression (.const w) := by
  intro F s v h; cases h; exact ⟨w, rfl⟩

theorem WordExpression.load (a : ExpHOL 64) : WordExpression (.load .one a) := by
  classical
  intro F s v h
  simp only [evalHOLExact, isWfShapeExactHOL, ↓reduceIte] at h
  split at h
  · rename_i address _
    simp only [memLoadHOLExact] at h
    split at h
    · cases hm : s.memory address with
      | word w => exact ⟨w, by simpa [hm] using h.symm⟩
    · cases h
  · cases h

theorem WordExpression.op (bop : BinOp) (es : List (ExpHOL 64)) : WordExpression (.op bop es) := by
  intro F s v h
  simp only [evalHOLExact] at h
  split at h
  · split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨w, _, hw⟩ := h
      exact ⟨w, hw.symm⟩
    · cases h
  · cases h

def DomainTouch (address : ExpHOL 64) (body : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), GuestInv s →
    ((evaluateHOLFiniteState s body).1 = none ∨ (evaluateHOLFiniteState s body).1 = some .continue) →
    ∃ a : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) address = some (.val (.word a)) ∧
      sourceBase ≤ a.toNat ∧ a.toNat < heapEnd

theorem DomainTouch.storeByte (address value : ExpHOL 64) :
    DomainTouch address (.storeByte address value) := by
  intro F s hguest hflow
  rw [evaluateHOLFiniteState_storeByte] at hflow
  split at hflow
  · rename_i addr haddr
    split at hflow
    · split at hflow
      · rename_i memory hmem
        refine ⟨addr, haddr, ordinaryDomain_byte_interval addr ?_⟩
        unfold panMemStoreByteWord8HOL at hmem
        cases hm : s.memory (panByteAlignHOL addr) with
        | word _ =>
          simp only [hm] at hmem
          split at hmem
          · rename_i hd
            rw [hguest.memaddrs] at hd
            exact hd
          · cases hmem
      · simp at hflow
    · simp at hflow
  · simp at hflow

theorem DomainTouch.store (address value : ExpHOL 64) (hw : WordExpression value) :
    DomainTouch address (.store address value) := by
  intro F s hguest hflow
  rw [evaluateHOLFiniteState_store] at hflow
  split at hflow
  · rename_i addr haddr
    split at hflow
    · rename_i v hv
      obtain ⟨_, rfl⟩ := hw s v hv
      simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hflow
      by_cases hd : s.memaddrs addr
      · rw [hguest.memaddrs] at hd
        have hi := ordinaryDomain_interval addr hd
        exact ⟨addr, haddr, hi.1, by omega⟩
      · simp [hd] at hflow
    · simp at hflow
  · simp at hflow

theorem DomainTouch.seq (address : ExpHOL 64) (first rest : ProgHOL 64)
    (ht : DomainTouch address first) : DomainTouch address (.seq first rest) := by
  intro F s hguest hflow
  apply ht s hguest
  rw [evaluateHOLFiniteState_seq_line780] at hflow
  cases hfirst : evaluateHOLFiniteState s first with
  | mk result _ =>
    rw [hfirst] at hflow
    cases result with
    | none => exact Or.inl rfl
    | some result => cases result <;> simp_all

private theorem add_locals_inv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (base counter : MlS) (address : BitVec 64)
    (h : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local base, .var .local counter]) = some (.val (.word address))) :
    ∃ b i : BitVec 64, s.locals.lookup base = some (.val (.word b)) ∧
      s.locals.lookup counter = some (.val (.word i)) ∧ address = b + i := by
  cases hb : s.locals.lookup base with
  | none => simp [evalHOLExact, evalListHOLExact, hb] at h
  | some bv =>
    cases bv with
    | rStruct _ => cases hi : s.locals.lookup counter <;> simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord] at h
    | nStruct _ _ => cases hi : s.locals.lookup counter <;> simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord] at h
    | val bw =>
      cases bw with
      | word b =>
        cases hi : s.locals.lookup counter with
        | none => simp [evalHOLExact, evalListHOLExact, hb, hi] at h
        | some iv =>
          cases iv with
          | rStruct _ => simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord] at h
          | nStruct _ _ => simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord] at h
          | val iw =>
            cases iw with
            | word i =>
              refine ⟨b, i, rfl, rfl, ?_⟩
              simpa [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord, valueWord, wordOpHOL, wordOp] using h.symm

def memoryWalkRank (base counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup base, s.locals.lookup counter with
  | some (.val (.word b)), some (.val (.word i)) => domainRank (b + i)
  | _, _ => 0

theorem memoryWalkRank_bound (base counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    memoryWalkRank base counter s ≤ domainBytes + 1 := by
  unfold memoryWalkRank
  split
  · exact domainRank_bound _
  · omega

theorem while_memory_walk_guestInv (base counter : MlS) (step : Nat) (condition : ExpHOL 64)
    {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B)
    (htouch : DomainTouch (.op .add [.var .local base, .var .local counter]) body)
    (hadd : CounterStep counter (BitVec.ofNat 64 step) body)
    (hbase : avoidsLocal base body = true)
    (hstep : 0 < step) (hsmall : step ≤ 256) :
    TerminatingProgBoundedOn GuestInv (.while condition body) ((domainBytes + 1 + 1) * (B + 1)) := by
  refine @TerminatingProgBoundedOn.while_rank GuestInv condition body B (domainBytes + 1)
    (memoryWalkRank base counter)
    (fun s hs => guestInv_decClock s hs) hbody
    (fun s _ _ _ => memoryWalkRank_bound base counter s) ?_
  intro F s _ hguest _ hflow
  have hguest' := guestInv_decClock s hguest
  obtain ⟨addr, haddr, hlow, hhigh⟩ := htouch (decClockHOLFinite s) hguest' hflow
  obtain ⟨b, i, hb, hi, rfl⟩ := add_locals_inv (decClockHOLFinite s) base counter addr haddr
  have hipost := hadd (decClockHOLFinite s) i hi hflow
  have hbpost := evaluate_avoidsLocal_flowing base body hbase (decClockHOLFinite s)
    (hflow.elim Or.inl (fun h => Or.inr (Or.inr h)))
  change s.locals.lookup base = some (.val (.word b)) at hb
  change s.locals.lookup counter = some (.val (.word i)) at hi
  have hbpost' := hbpost.trans hb
  refine ⟨guestInv_evaluate (decClockHOLFinite s) body hguest', ?_⟩
  simpa only [memoryWalkRank, hipost, hbpost', hb, hi, BitVec.add_assoc]
    using domainRank_add_lt (b + i) step ⟨hlow, hhigh⟩ hstep hsmall

/-! ### 5. Tactics `fb_auto`, `fb_unfold`, `fb_arith`, `fb_prove` -/

macro "incr_body" : tactic => `(tactic| repeat (first
  | exact IncrBody.incr
  | apply IncrBody.dec _ _ _ (by decide)
  | apply IncrBody.decCall _ _ _ _ (by decide)
  | apply IncrBody.seq _ rfl rfl))

open Lean Elab Tactic Meta in
elab "exact_fb_hyp" : tactic => withMainContext do
  let goalType ← instantiateMVars (← getMainTarget)
  let args := goalType.getAppArgs
  if args.size < 2 then throwError "not TerminatingFunBoundedOn"
  let fnameExpr := args[1]!
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    let hty ← instantiateMVars ldecl.type
    let hargs := hty.getAppArgs
    if hargs.size >= 2 && hargs[1]! == fnameExpr then
      let goal ← getMainGoal
      let rest ← goal.apply ldecl.toExpr
      if rest.isEmpty then
        replaceMainGoal []
        return
  throwError m!"no matching fb hypothesis for {fnameExpr}"

syntax "fb_auto" : tactic
macro_rules
  | `(tactic| fb_auto) => `(tactic| first
      | exact straightOn _ rfl
      | (apply TerminatingProgBoundedOn.seq_guestInv
         · fb_auto
         · fb_auto)
      | (apply TerminatingProgBoundedOn.ite_on
         · fb_auto
         · fb_auto)
      | (apply dec_guestInv; fb_auto)
      | (apply call_guestInv'; exact_fb_hyp)
      | (apply decCall_guestInv'
         · exact_fb_hyp
         · fb_auto)
      | (apply callHandle_guestInv'
         · exact_fb_hyp
         · fb_auto)
      | (apply TerminatingProgBoundedOn.tailCall_guestInv; exact_fb_hyp)
      | (apply while_counter_guestInv .less (Or.inl rfl)
         · fb_auto
         · incr_body
         · rfl)
      | (apply while_counter_guestInv .lower (Or.inr rfl)
         · fb_auto
         · incr_body
         · rfl))

syntax "fb_unfold " num ident : tactic
macro_rules
  | `(tactic| fb_unfold $idx $fn) => `(tactic|
      (refine ⟨_, _, _, lookup_of_guestAst_getElem $idx (by rw [guestAst_len]; decide)
          (extractFn $fn) rfl, ?_⟩
       dsimp only [extractFn, $fn:ident,
         InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]))

open Lean Elab Tactic Meta in
elab "generalize_K" : tactic => do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  let cs := t.foldConsts #[] fun c acc =>
    if c.getPrefix == `InitECandidate.Solver.Wave8GuestInv.K && !acc.contains c then acc.push c else acc
  let mut i := 0
  for c in cs do
    i := i + 1
    let x := mkIdent (Name.mkSimple s!"kg{i}")
    evalTactic (← `(tactic| generalize ($(mkIdent c) : Nat) = $x))

syntax "fb_arith " ident : tactic
macro_rules
  | `(tactic| fb_arith $k) => `(tactic|
      (have hD : domainBytes + 1 + 1 ≤ 2 ^ 64 + 1 := by rw [domainBytes_eq]; decide
       unfold $k:ident
       generalize_K
       generalize domainBytes = D at hD ⊢
       try simp only [nat_max_eq]
       omega))

syntax "fb_prove " num ident ident : tactic
macro_rules
  | `(tactic| fb_prove $idx $fn $k) => `(tactic|
      (fb_unfold $idx $fn
       apply TerminatingProgBoundedOn.weaken'
       · fb_auto
       · fb_arith $k))

end InitECandidate.Solver.Wave8GuestInv.P12_P15.Common
