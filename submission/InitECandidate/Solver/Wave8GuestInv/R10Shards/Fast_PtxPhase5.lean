import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxCuts
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase1Compose
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

namespace FastPhase5
open Phase1

/-! ## 1. Counted `while` under `GuestInv` and fallthrough Hoare rule for `while` -/

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
      obtain ⟨_, resumed, inner, hloc, _, hcr, _⟩ :=
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
    obtain ⟨_, resumed, inner, hloc, _, hcr, hpost⟩ := decCall_flowing (Or.inl rfl) hrun
    have atR : resumed.locals.lookup c = some (.val (.word w)) := (hloc c distinct).trans atC
    have := (ih resumed w atR).2
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
  · rename_i w _
    have := BitVec.le_toInt w
    omega
  · omega

theorem while_less_guestInv (counter : MlS) (bound : ExpHOL 64)
    {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B)
    (hinc : IncrBody counter body) :
    TerminatingProgBoundedOn GuestInv (.while (.cmp .less (.var .local counter) bound) body)
      ((2 ^ 64 + 1) * (B + 1)) := by
  refine TerminatingProgBoundedOn.while_rank (signedUpRank counter)
    (fun s hs => guestInv_congr (s := s) rfl rfl rfl rfl hs) hbody
    (fun s _ _ _ => signedUpRank_le counter s) ?_
  intro F s _ hs ⟨result, hcond, hnz⟩ hflow
  refine ⟨guestInv_evaluate _ _ (guestInv_congr (s := s) rfl rfl rfl rfl hs), ?_⟩
  change evalAt s _ = _ at hcond
  obtain ⟨w, v, hw, hv, hword⟩ := evalAt_cmp s .less _ _ result hcond
  simp only [evalAt, evalHOLExact] at hw
  have hwl : s.locals.lookup counter = some (.val (.word w)) := by simpa using hw
  have hcmp : wordCmpHOL .less w v = true := by
    by_contra h; simp [h] at hword; exact hnz hword
  have hlt : w.toInt < v.toInt := by
    simpa only [wordCmpHOL, signed_less_eq, BitVec.slt_iff_toInt_lt] using hcmp
  have hvmax := BitVec.toInt_le (x := v)
  have hwmin := BitVec.le_toInt w
  have hwmax := BitVec.toInt_le (x := w)
  have hone : (1 : BitVec 64).toInt = 1 := by decide
  have hnext : (w + 1).toInt = w.toInt + 1 := by
    rw [BitVec.toInt_add, hone]
    apply Int.bmod_eq_of_le <;> omega
  obtain ⟨hnc, hinc'⟩ := hinc.run (decClockHOLFinite s) w hwl
  have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none := by
    rcases hflow with h | h
    · exact h
    · exact False.elim (hnc h)
  have hi' := hinc' hnone
  simp only [signedUpRank, hi', hwl, hnext]
  omega

theorem Hoare.while_preserve {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {cond : ExpHOL 64} {body : ProgHOL 64}
    (hdec : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → P (decClockHOLFinite s))
    (hbody : Hoare (fun s => P s ∧ CondTrue cond s) body
      (fun r t => (r = none ∨ r = some .continue ∨ r = some .break) → P t)) :
    Hoare P (.while cond body) (fun r t => r = none → P t) := by
  refine ⟨fun {F} s hcode hP _ hr => ?_⟩
  rcases hrun : evaluateHOLFiniteState s (.while cond body) with ⟨r, post⟩
  rw [hrun] at hr
  dsimp only at hr
  subst hr
  suffices ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F),
      st.clock = k → st.code = originalRuntimeCode → P st →
      evaluateHOLFiniteState st (.while cond body) = (none, post) → P post from
    this s.clock s rfl hcode hP hrun
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st hk st_code hPst hst_run
    rw [evaluateHOLFiniteState_while_total] at hst_run
    split at hst_run
    · rename_i w hw
      split at hst_run
      · rename_i hwnz
        split at hst_run
        · simp at hst_run
        · dsimp only at hst_run
          rw [fixClockHOLFinite_evaluateState] at hst_run
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
          have hmeta := (evaluateHOLFiniteState_metadata (decClockHOLFinite st) body).1
          have hct : CondTrue cond (decClockHOLFinite st) := by
            obtain ⟨_, hw', hwnz'⟩ := loopActive_decClock (s := st) ⟨w, hw, hwnz⟩
            refine ⟨_, ?_, hwnz'⟩
            rw [← evalHOLFinite_eq_toExact]
            exact hw'
          rcases bRun : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨r1, mid⟩
          rw [bRun] at hst_run hrem hmeta
          have hclk_lt : mid.clock < k := by
            change mid.clock ≤ st.clock - 1 at hrem
            omega
          have hb_nt : (evaluateHOLFiniteState (decClockHOLFinite st) body).1 ≠ some .timeOut := by
            intro hto
            rw [bRun] at hto; dsimp only at hto; subst hto
            simp at hst_run
          have hb_post := hbody.run (decClockHOLFinite st) st_code ⟨hdec st hPst, hct⟩ hb_nt
          rw [bRun] at hb_post
          dsimp only at hb_post
          cases r1 with
          | none =>
            exact ih mid.clock hclk_lt mid rfl (hmeta.trans st_code)
              (hb_post (Or.inl rfl)) hst_run
          | some r1' =>
            cases r1' with
            | «continue» =>
              exact ih mid.clock hclk_lt mid rfl (hmeta.trans st_code)
                (hb_post (Or.inr (Or.inl rfl))) hst_run
            | «break» =>
              simp at hst_run
              obtain ⟨_, rfl⟩ := hst_run
              exact hb_post (Or.inr (Or.inr rfl))
            | _ => simp at hst_run
      · simp at hst_run
        obtain ⟨_, rfl⟩ := hst_run
        exact hPst
    · simp at hst_run

/-! ## 2. `WorldOK` Preservation Helpers for Phase 5 -/

theorem localsFree_worldOK : LocalsFree WorldOK := by
  intro F s locals k ⟨hA, S, hW⟩
  exact ⟨(arenaReady_with_locals s locals k).2 hA, S, (worldTyped_with_locals s locals k S).2 hW⟩

theorem localsOnly_worldOK : LocalsOnly [] WorldOK :=
  LocalsOnly.of_localsFree localsFree_worldOK

theorem worldOK_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F) (h : WorldOK s) :
    GuestInv s := h.1.1

theorem worldTypedWith_of_worldOK {F : Type} {s : PanSemStateFiniteExact 64 F} (h : WorldOK s) :
    ∃ S Nd, WorldTypedWith s S Nd := by
  obtain ⟨_, S, hT, hJ, hF, Nd, hTr⟩ := h
  exact ⟨S, Nd, hT, hJ, hF, hTr⟩

theorem Hoare.seq_fall {P R Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {first second : ProgHOL 64}
    (h1 : Hoare P first (fun r t => r = none → R t))
    (h2 : Hoare R second (fun r t => r = none → Q t)) :
    Hoare P (.seq first second) (fun r t => r = none → Q t) :=
  Hoare.seq ⟨fun s hc hP hnt => ⟨h1.run s hc hP hnt, fun hr h => False.elim (hr h)⟩⟩ h2

theorem Hoare.dec_fall {P P' Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {names : List String} {name : MlS} {shape : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (hname : ∀ n ∈ names, ofString n ≠ name)
    (hQ : LocalsOnly names Q)
    (hinit : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      evalAt s init = some v → P' (setVarHOLFinite name v s))
    (hbody : Hoare P' body (fun r t => r = none → Q t)) :
    Hoare P (.dec name shape init body) (fun r t => r = none → Q t) :=
  Hoare.dec hname hinit hbody
    (fun _ t locals hl h hr => hQ t locals t.clock hl (h hr))
    (fun _ _ hr => by cases hr)

theorem Hoare.ite_fall {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {cond : ExpHOL 64} {yes no : ProgHOL 64}
    (hyes : Hoare (fun s => P s ∧ CondTrue cond s) yes (fun r t => r = none → Q t))
    (hno : Hoare (fun s => P s ∧ CondFalse cond s) no (fun r t => r = none → Q t)) :
    Hoare P (.ite cond yes no) (fun r t => r = none → Q t) :=
  Hoare.ite hyes hno (fun _ _ hr => by cases hr)

theorem Hoare.assign_fall {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {kind : VarKind} {name : MlS} {source : ExpHOL 64}
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      evalAt s source = some v → Q (setKvarHOLFinite kind name v s)) :
    Hoare P (.assign kind name source) (fun r t => r = none → Q t) :=
  Hoare.assign (fun s v hP hv _ => h s v hP hv) (fun _ _ hr => by cases hr)

theorem resume_ro_worldOK {fname name : MlS}
    (hro : ReadOnlyFn fname) (args : List (ExpHOL 64)) :
    DecCallResumeOn WorldOK WorldOK name fname args := by
  intro F s vs body callee ret v post hc hP _ hl hrun
  have hspec := funSpec_at_lookup hro s hc vs body callee ret hl
    (guestInv_callEntry s callee hP.1.1) (by rw [hrun]; simp)
  rw [hrun] at hspec
  have heq : post = { callEntryStateHOLFinite s callee with locals := post.locals, clock := post.clock } :=
    hspec (Or.inl ⟨v, rfl⟩)
  have h2 : ({ post with locals := s.locals } : PanSemStateFiniteExact 64 F) =
      { s with locals := s.locals, clock := post.clock } := by rw [heq]; rfl
  rw [h2]
  exact LocalsOnly.setVar localsOnly_worldOK (by simp) v _ (localsFree_worldOK s s.locals post.clock hP)

theorem hoare_call_scratch_worldOK {fname : MlS}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    (hwk : WorldKeeps WorldOK R gw keep Q fname)
    {gs : List (String × Nat)} (hgs : ScratchSet gs)
    (hR : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), R s = gs.map (fun g => (globN s g.1, g.2)))
    (args : List (ExpHOL 64)) :
    Hoare WorldOK (.call (some (none, none)) fname args) (fun r t => r = none → WorldOK t) := by
  refine Hoare.call0 hwk ?_ ?_ (fun _ _ hn _ he => (hn he).elim)
  · intro F s vs body callee ret _ hP _ _
    exact worldOK_callEntry hP callee
  · intro F s callee post v _ hP hspec _
    have hstep := hspec (Or.inl ⟨v, rfl⟩)
    obtain ⟨S, Nd, hW⟩ := worldTypedWith_of_worldOK hP
    have hce_W : WorldTypedWith (callEntryStateHOLFinite s callee) S Nd :=
      (worldTypedWith_with_locals s callee (s.clock - 1) S Nd).2 hW
    have hce_A : ArenaOK (callEntryStateHOLFinite s callee) := hP.1.2
    have hrSafe : IvlsDisj (R (callEntryStateHOLFinite s callee))
        (worldTypedIvls (callEntryStateHOLFinite s callee) S Nd) := by
      intro i hi j hj
      rw [hR] at hi
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hi
      obtain ⟨hgb, hgt, hgn, hsmall⟩ := hgs g hg
      exact buffer_disj_typed hce_A hce_W hgb hgt hgn hsmall j hj
    obtain ⟨S', Nd', _, hW', _⟩ := hstep.2.2.2.2 S Nd hce_W hrSafe
    exact worldOK_of_parts
      ((arenaReady_with_locals post s.locals post.clock).2 hstep.1)
      ((worldTypedWith_with_locals post s.locals post.clock S' Nd').2 hW')

/-! ## 3. Phase 5: Deletion Loop + `incorporate_tx_into_block` + Scratch/Frame Release -/

def delLoopBody : ProgHOL 64 :=
  .decCall (ofString "s") (.comb [.one, .one, .one]) (ofString "htab_item")
    [.var .local (ofString "del"), .var .local (ofString "i")]
    (.seq
      (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s"))) (.const 0))
        (.call (some (none, none)) (ofString "clear_account_preserving_balance")
          [.rfield 1 (.var .local (ofString "s"))])
        .skip)
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))

theorem delLoopBody_bound (h : PtxCallees) :
    TerminatingProgBoundedOn GuestInv delLoopBody
      ((K.«htab_item» + 1) + Nat.max (K.«clear_account_preserving_balance» + 1) 0) := by
  unfold delLoopBody
  have hb : TerminatingProgBoundedOn GuestInv
      (.decCall (ofString "s") (.comb [.one, .one, .one]) (ofString "htab_item")
        [.var .local (ofString "del"), .var .local (ofString "i")]
        (.seq
          (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s"))) (.const 0))
            (.call (some (none, none)) (ofString "clear_account_preserving_balance")
              [.rfield 1 (.var .local (ofString "s"))])
            .skip)
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
      (K.«htab_item» +
        ((Nat.max (K.«clear_account_preserving_balance» + 1) 0 + 0) + 1)) :=
    TerminatingProgBoundedOn.decCall_guestInv h.fb_htab_item
      (ofString "s") (.comb [.one, .one, .one]) _
      (TerminatingProgBoundedOn.seq_guestInv
        (TerminatingProgBoundedOn.ite_on
          (TerminatingProgBoundedOn.call_guestInv h.fb_clear_account_preserving_balance none _)
          (bound_of_clock clock_skip))
        (bound_of_clock (fun s => clock_assign s .local (ofString "i")
          (.op .add [.var .local (ofString "i"), .const 1]))))
  intro F s hc hg
  simpa only [Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb s hc hg

theorem delLoopBody_incr : IncrBody (ofString "i") delLoopBody := by
  unfold delLoopBody
  refine IncrBody.decCall _ _ _ _ (by decide) ?_
  exact IncrBody.seq _ rfl rfl IncrBody.incr

def noBreakCont : ProgHOL 64 → Bool
  | .seq a b => noBreakCont a && noBreakCont b
  | .ite _ a b => noBreakCont a && noBreakCont b
  | .dec _ _ _ b => noBreakCont b
  | .decCall _ _ _ _ b => noBreakCont b
  | .skip | .assign _ _ _ | .store _ _ | .call (some (_, none)) _ _ => true
  | _ => false

theorem evaluate_noBreakCont :
    ∀ (p : ProgHOL 64), noBreakCont p = true → ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s p).1 ≠ some .continue ∧
      (evaluateHOLFiniteState s p).1 ≠ some .break
  | .seq a b, hp, _, s => by
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hp
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hr : evaluateHOLFiniteState s a with ⟨r1, mid⟩
    cases r1 with
    | none => exact evaluate_noBreakCont b hb mid
    | some _ =>
      have ⟨hnc, hnbr⟩ := evaluate_noBreakCont a ha s
      rw [hr] at hnc hnbr
      exact ⟨hnc, hnbr⟩
  | .ite _ a b, hp, _, s => by
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noBreakCont b hb s
      · exact evaluate_noBreakCont a ha s
    · simp
  | .dec _ _ _ b, hp, _, s => by
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · split
      · exact evaluate_noBreakCont b hp _
      · simp
  | .decCall nm sh fn args b, hp, _, s => by
    refine ⟨?_, ?_⟩
    · intro hc
      rcases hrun : evaluateHOLFiniteState s (.decCall nm sh fn args b) with ⟨r, post⟩
      rw [hrun] at hc; dsimp only at hc; subst hc
      obtain ⟨_, resumed, _, _, _, hcr, _⟩ := decCall_flowing (Or.inr (Or.inr rfl)) hrun
      have hnc := (evaluate_noBreakCont b hp resumed).1
      rw [hcr] at hnc; exact hnc rfl
    · intro hbr
      rcases hrun : evaluateHOLFiniteState s (.decCall nm sh fn args b) with ⟨r, post⟩
      rw [hrun] at hbr; dsimp only at hbr; subst hbr
      obtain ⟨_, resumed, _, _, _, hcr, _⟩ := decCall_flowing (Or.inr (Or.inl rfl)) hrun
      have hnbr := (evaluate_noBreakCont b hp resumed).2
      rw [hcr] at hnbr; exact hnbr rfl
  | .skip, _, _, s => by simp [evaluateHOLFiniteState_skip]
  | .assign _ _ _, _, _, s => by
    rw [evaluateHOLFiniteState_assign]; split
    · simp
    · split <;> simp
  | .store dst src, _, _, s => by
    rcases (evaluate_store_control_frame s dst src).1 with h | h <;> rw [h] <;> simp
  | .call (some (_, none)) _ _, _, _, s => by
    rw [evaluateHOLFiniteState_call]
    dsimp only
    refine ⟨?_, ?_⟩
    all_goals
      intro h
      repeat' first | split at h | simp at h | simp_all

theorem delLoopBody_hoare (h : PtxCallees) :
    Hoare WorldOK delLoopBody (fun r t => r = none → WorldOK t) := by
  unfold delLoopBody
  apply Hoare.decCall_fall (names := []) (by simp) localsOnly_worldOK
  · exact resume_ro_worldOK h.ro_htab_item _
  · apply Hoare.seq_fall (R := WorldOK)
    · apply Hoare.ite_fall
      · exact Hoare.mono
          (hoare_call_scratch_worldOK h.wk_clear_account_preserving_balance
            (gs := [("keccak_pad", 136), ("keccak_st", 200), ("mpt_nib_scratch", 64), ("sk_buf", 64)])
            (by unfold ScratchSet; decide) (fun _ => rfl) _)
          (fun _ hp => hp.1)
      · exact Hoare.skip (fun _ hp _ => hp.1)
    · exact Hoare.assign_fall fun s v hP _ =>
        LocalsOnly.setVar localsOnly_worldOK (by simp) v s hP

def delIteProg : ProgHOL 64 :=
  .ite (.cmp .notEqual (.var .local (ofString "del")) (.const 0))
    (.dec (ofString "dcap") .one
      (.load .one (.op .add [.var .local (ofString "del"), .const 24]))
      (.seq
        (.assign .local (ofString "i") (.const 0))
        (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "dcap")))
          delLoopBody)))
    .skip

theorem delIteProg_bound (h : PtxCallees) :
    TerminatingProgBoundedOn GuestInv delIteProg
      (Nat.max ((2 ^ 64 + 1) * ((K.«htab_item» + 1) +
        Nat.max (K.«clear_account_preserving_balance» + 1) 0 + 1)) 0) := by
  unfold delIteProg
  have hyes : TerminatingProgBoundedOn GuestInv
      (.dec (ofString "dcap") .one
        (.load .one (.op .add [.var .local (ofString "del"), .const 24]))
        (.seq
          (.assign .local (ofString "i") (.const 0))
          (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "dcap")))
            delLoopBody)))
      (0 + (2 ^ 64 + 1) * (((K.«htab_item» + 1) +
        Nat.max (K.«clear_account_preserving_balance» + 1) 0) + 1)) :=
    TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _
      (TerminatingProgBoundedOn.seq_guestInv
        (bound_of_clock (fun s => clock_assign s .local (ofString "i") (.const 0)))
        (while_less_guestInv (ofString "i") (.var .local (ofString "dcap"))
          (delLoopBody_bound h) delLoopBody_incr))
  have hb : TerminatingProgBoundedOn GuestInv delIteProg
      (Nat.max (0 + (2 ^ 64 + 1) * (((K.«htab_item» + 1) +
        Nat.max (K.«clear_account_preserving_balance» + 1) 0) + 1)) 0) :=
    TerminatingProgBoundedOn.ite_on hyes (bound_of_clock clock_skip)
  unfold delIteProg at *
  intro F s hc hg
  simpa only [Nat.zero_add] using hb s hc hg

theorem delIteProg_hoare (h : PtxCallees) :
    Hoare WorldOK delIteProg (fun r t => r = none → WorldOK t) := by
  unfold delIteProg
  apply Hoare.ite_fall
  · refine Hoare.mono ?_ (fun _ hp => hp.1)
    apply Hoare.dec_fall (names := []) (by simp) localsOnly_worldOK
    · exact fun s v hP _ => LocalsOnly.setVar localsOnly_worldOK (by simp) v s hP
    · apply Hoare.seq_fall (R := WorldOK)
      · exact Hoare.assign_fall fun s v hP _ =>
          LocalsOnly.setVar localsOnly_worldOK (by simp) v s hP
      · refine Hoare.while_preserve (fun s hP => localsFree_worldOK s s.locals (s.clock - 1) hP) ?_
        refine ⟨fun {F} s hc hP hnt hfl => ?_⟩
        have hb := (delLoopBody_hoare h).run s hc hP.1 hnt
        have ⟨hnc, hnbr⟩ := evaluate_noBreakCont delLoopBody rfl s
        rcases hfl with hnone | hcont | hbrk
        · exact hb hnone
        · exact False.elim (hnc hcont)
        · exact False.elim (hnbr hbrk)
  · exact Hoare.skip (fun _ hp _ => hp.1)

def phase5Tail : ProgHOL 64 :=
  .seq (.call (some (none, none)) (ofString "incorporate_tx_into_block") [])
    (.dec (ofString "tx_frame_mark") .one
      (.load .one (.op .add [.var .local (ofString "out"), .const 80]))
      (.seq
        (.ite (.cmp .notEqual (.var .local (ofString "tx_frame_mark")) (.const 0))
          (.seq
            (.call (some (none, none)) (ofString "scratch_release")
              [.var .local (ofString "tx_frame_mark")])
            (.call (some (none, none)) (ofString "frame_mem_release")
              [.load .one (.op .add [.var .local (ofString "out"), .const 88])]))
          .skip)
        (.return (.const 0))))

theorem phase5Tail_bound (h : PtxCallees) :
    TerminatingProgBoundedOn WorldOK phase5Tail
      ((K.«incorporate_tx_into_block» + 1) +
        Nat.max ((K.«scratch_release» + 1) + (K.«frame_mem_release» + 1)) 0) := by
  unfold phase5Tail
  have h1 : TerminatingProgBoundedOn WorldOK
      (.call (some (none, none)) (ofString "incorporate_tx_into_block") [])
      (K.«incorporate_tx_into_block» + 1) :=
    TerminatingProgBoundedOn.call_on h.gb_incorporate_tx_into_block none []
      (fun s _ _ callee _ _ hP _ _ => worldOK_callEntry hP callee)
  have h1_hoare : Hoare WorldOK
      (.call (some (none, none)) (ofString "incorporate_tx_into_block") [])
      (fun r t => r = none → GuestInv t) := by
    refine ⟨fun {F} s _ hP _ _ => ?_⟩
    exact guestInv_evaluate s _ (worldOK_guestInv s hP)
  have h2 : TerminatingProgBoundedOn GuestInv
      (.dec (ofString "tx_frame_mark") .one
        (.load .one (.op .add [.var .local (ofString "out"), .const 80]))
        (.seq
          (.ite (.cmp .notEqual (.var .local (ofString "tx_frame_mark")) (.const 0))
            (.seq
              (.call (some (none, none)) (ofString "scratch_release")
                [.var .local (ofString "tx_frame_mark")])
              (.call (some (none, none)) (ofString "frame_mem_release")
                [.load .one (.op .add [.var .local (ofString "out"), .const 88])]))
            .skip)
          (.return (.const 0))))
      (Nat.max ((K.«scratch_release» + 1) + (K.«frame_mem_release» + 1)) 0 + 0) :=
    TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _
      (TerminatingProgBoundedOn.seq_guestInv
        (TerminatingProgBoundedOn.ite_on
          (TerminatingProgBoundedOn.seq_guestInv
            (TerminatingProgBoundedOn.call_guestInv h.fb_scratch_release none _)
            (TerminatingProgBoundedOn.call_guestInv h.fb_frame_mem_release none _))
          (bound_of_clock clock_skip))
        (bound_of_clock (fun s => clockPreserving_return (.const 0) s)))
  have hb : TerminatingProgBoundedOn WorldOK phase5Tail
      ((K.«incorporate_tx_into_block» + 1) +
        (Nat.max ((K.«scratch_release» + 1) + (K.«frame_mem_release» + 1)) 0 + 0)) :=
    seq_bound h1 h1_hoare h2
  unfold phase5Tail at hb
  intro F s hc hp
  simpa only [Nat.add_zero] using hb s hc hp

theorem phase5_eq : ptxPhase5 =
    .dec (ofString "del") .one
      (.load .one (.op .add [.var .local (ofString "out"), .const 24]))
      (.seq delIteProg phase5Tail) := by
  unfold ptxPhase5 ptxCode delIteProg delLoopBody phase5Tail
  rfl

private theorem phase5_cost_algebra (a b c : Nat) :
    a + (b + c) = a + b + c := by omega

theorem phase5_worldOK (h : PtxCallees) :
    TerminatingProgBoundedOn WorldOK ptxPhase5 ptxCost5 := by
  rw [phase5_eq]
  have hb : TerminatingProgBoundedOn WorldOK
      (.dec (ofString "del") .one
        (.load .one (.op .add [.var .local (ofString "out"), .const 24]))
        (.seq delIteProg phase5Tail))
      (Nat.max ((2 ^ 64 + 1) * ((K.«htab_item» + 1) +
        Nat.max (K.«clear_account_preserving_balance» + 1) 0 + 1)) 0 +
      ((K.«incorporate_tx_into_block» + 1) +
        Nat.max ((K.«scratch_release» + 1) + (K.«frame_mem_release» + 1)) 0)) :=
    TerminatingProgBoundedOn.dec_on localsFree_worldOK _ _ _
      (seq_bound
        (bound_mono (delIteProg_bound h) worldOK_guestInv)
        (delIteProg_hoare h)
        (phase5Tail_bound h))
  have he : Nat.max ((2 ^ 64 + 1) * ((K.«htab_item» + 1) +
        Nat.max (K.«clear_account_preserving_balance» + 1) 0 + 1)) 0 +
      ((K.«incorporate_tx_into_block» + 1) +
        Nat.max ((K.«scratch_release» + 1) + (K.«frame_mem_release» + 1)) 0) = ptxCost5 :=
    phase5_cost_algebra _ _ _
  rw [← he]
  intro F s hc hP
  exact hb s hc hP

/-- Phase 5: native HOL spine depths 139–144. -/
theorem ptxPhase5_cut (h : PtxCallees) :
    TerminatingProgBoundedOn PtxReceiptsDone ptxPhase5 ptxCost5 :=
  fun s hc hp => phase5_worldOK h s hc hp.1.1

end FastPhase5

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10

namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.FastPtxPhase5
open Flapjack.Pancake.PanLang
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10

/-- Phase 5: native HOL spine depths 139–144 (exact signature expected by `PtxRouter.lean`). -/
theorem ptxPhase5_cut (h : PtxCallees) :
    TerminatingProgBoundedOn PtxReceiptsDone ptxPhase5 ptxCost5 :=
  FastPhase5.ptxPhase5_cut h

end InitECandidate.Solver.Wave8GuestInv.R10Shards.FastPtxPhase5
