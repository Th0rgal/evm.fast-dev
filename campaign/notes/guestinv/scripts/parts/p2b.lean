
/-- Guarded `seq` for `GuestInv`: no preservation hypothesis (`preservesOn_guestInv`). -/
theorem TerminatingProgBoundedOn.seq_guestInv {first second : ProgHOL 64} {a b : Nat}
    (h1 : TerminatingProgBoundedOn GuestInv first a)
    (h2 : TerminatingProgBoundedOn GuestInv second b) :
    TerminatingProgBoundedOn GuestInv (.seq first second) (a + b) :=
  TerminatingProgBoundedOn.seq_on h1 (preservesOn_guestInv first) h2

/-- A `while` loop head is active: its condition evaluates to a nonzero word (same definition as
`PanTerminatingNoRepeat.LoopActive` on `wave8/step0`). -/
def LoopActive (condition : ExpHOL 64) {F : Type} (state : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ word : BitVec 64,
    evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      condition = some (.val (.word word)) ∧ word ≠ 0

/-! ### `while` rules (round-2 item 3)

`evaluate_clock_irrelevant`, `evaluate_ne_of_clock_lt` and `while_unfold_continue` are copied
verbatim from `PanTerminatingNoRepeat` (`wave8/step0`), which this file cannot import (it is not
on this branch's cone). -/

/-- Clock irrelevance for non-`.timeOut` runs (Flapjack `panPropsEvaluateAddClockEq`). -/
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

/-- `t` is an exact repeat of the loop head `s`: every field but the clock agrees. -/
def SameHead {F : Type} (s t : PanSemStateFiniteExact 64 F) : Prop :=
  t = { s with clock := t.clock }

/-- The rest of the loop, run from `t`, times out (e.g. `modinv_bin`'s halving loop once `u = 0`:
the body is straight-line word arithmetic that always returns, and `u` stays `0`). -/
def WhileTimesOut (condition : ExpHOL 64) (body : ProgHOL 64) {F : Type}
    (t : PanSemStateFiniteExact 64 F) : Prop :=
  (evaluateHOLFiniteState t (.while condition body)).1 = some .timeOut

/-- The stationary alternatives of `while_rank_stationary`: an exact repeat of the loop head, or
a state from which the loop times out. -/
def Stationary (condition : ExpHOL 64) (body : ProgHOL 64) {F : Type}
    (s t : PanSemStateFiniteExact 64 F) : Prop :=
  SameHead s t ∨ WhileTimesOut condition body t

/-- Induction core of `while_rank_stationary`: `n` bounds `μ + 1` at the active loop head. The
body bound is needed only after an ACTIVE `P` loop head (revision 4, round-3 item 1). -/
theorem while_rank_stationary_aux
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {condition : ExpHOL 64}
    {body : ProgHOL 64} {B : Nat}
    (μ : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat)
    (hbody : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      P s → LoopActive condition s → TerminatingRunBounded (decClockHOLFinite s) body B)
    (hstep : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      P s → LoopActive condition s →
      ((evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .continue) →
      P (evaluateHOLFiniteState (decClockHOLFinite s) body).2 ∧
        (μ (evaluateHOLFiniteState (decClockHOLFinite s) body).2 < μ s ∨
          Stationary condition body s (evaluateHOLFiniteState (decClockHOLFinite s) body).2)) :
    ∀ (n : Nat) {F : Type} (state : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode → P state →
      (LoopActive condition state → μ state + 1 ≤ n) →
      TerminatingRunBounded state (.while condition body) (n * (B + 1)) := by
  intro n
  induction n with
  | zero =>
    intro F state hcode hP hle hnt
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    split
    · rename_i word hword
      by_cases hzero : word = 0
      · rw [if_neg (by simp [hzero])]; exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
      · have := hle ⟨word, hword, hzero⟩
        omega
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  | succ n ih =>
    intro F state hcode hP hle hnt
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
          have hμ := hle hact
          have hb := hbody state hcode hP hact
          have hstep' := hstep state hcode hP hact
          have hunfold := while_unfold_continue condition body state word hword hzero hclock
          have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
            (decClockHOLFinite state) body).1
          unfold TerminatingRunBounded at hb
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite state) body with ⟨result, post⟩
          simp only [hrun] at hnt hb hstep' hunfold hmeta
          dsimp only at hb hstep' hunfold hmeta hnt ⊢
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
            obtain ⟨hPpost, hdown⟩ := hstep' hflow
            have hsame := hunfold hflow
            have hntPost : (evaluateHOLFiniteState post (.while condition body)).1 ≠
                some .timeOut := by
              rw [← hsame]; exact hnt0
            rcases hdown with hlt | hrep
            · obtain ⟨htail, htailKept⟩ := ih post (hmeta.trans hcode) hPpost
                (fun _ => by omega) hntPost
              have hmul : n * (B + 1) + (B + 1) = (n + 1) * (B + 1) := by
                rw [Nat.succ_mul]
              exact ⟨by omega, by omega⟩
            · exfalso
              rcases hrep with hrep | hto
              · refine evaluate_ne_of_clock_lt (.while condition body) post state ?_
                  (by omega) hsame hntPost
                rw [hrep]
              · exact hntPost hto
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
              have hone : B + 1 ≤ (n + 1) * (B + 1) := Nat.le_mul_of_pos_left _ (by omega)
              exact ⟨by omega, by omega⟩
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

/-- Ranking rule with stationary iterations (round-2 item 3). Every continuing iteration from an
active `P` loop head `s` lands in a `P` state that either has a strictly smaller rank
`μ ≤ N`, or is stationary: an exact repeat of `s` (`SameHead`: all fields but the clock agree), or
a state from which the loop times out (`WhileTimesOut`). An exact repeat is a timeout (clock
irrelevance: the run from the repeat is the run from `s` with less clock), so neither needs a
decrease. This is `while_noRepeat` (`wave8/step0`) with the visited-key count replaced by `μ` and
the key collision replaced by `SameHead`. This covers `htab_truncate` (an `htab_del` that finds no matching key writes
nothing), both `fq12_inv` loops, `sort_elems` at width `0` and the `_mpt_insert_node` self-loop.
A loop that becomes stationary only after a warm-up iteration (writes that are idempotent from the
second iteration on) uses `μ = 2·r + [the next iteration is not an exact repeat]`. -/
theorem TerminatingProgBoundedOn.while_rank_stationary
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {condition : ExpHOL 64}
    {body : ProgHOL 64} {B N : Nat}
    (μ : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat)
    (hdec : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → P (decClockHOLFinite s))
    (hbody : TerminatingProgBoundedOn P body B)
    (hle : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      P s → LoopActive condition s → μ s ≤ N)
    (hstep : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      P s → LoopActive condition s →
      ((evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .continue) →
      P (evaluateHOLFiniteState (decClockHOLFinite s) body).2 ∧
        (μ (evaluateHOLFiniteState (decClockHOLFinite s) body).2 < μ s ∨
          Stationary condition body s (evaluateHOLFiniteState (decClockHOLFinite s) body).2)) :
    TerminatingProgBoundedOn P (.while condition body) ((N + 1) * (B + 1)) :=
  fun state hcode hP =>
    while_rank_stationary_aux μ (fun s hc hPs _ => hbody (decClockHOLFinite s) hc (hdec s hPs))
      hstep (N + 1) state hcode hP (fun hact => by have := hle state hcode hP hact; omega)

/-- Ranking rule for `while` (strict decrease on every continuing iteration): the special case of
`while_rank_stationary` without stationary iterations. It covers the loop classes of DESIGN.md §3:
* strict local counter `i < X`, `i := i + 1` (resp. `i ≠ 0`, `i := i - 1`): `μ = X - i` (resp.
  `μ = i`) read from the locals, `N = 2^64`, for ARBITRARY memory (errors inside the body
  terminate the run and are covered);
* fresh-address walk: `μ = heapEnd - address`, `N = W`;
* monotone measure (halving, degree, allocation potential, EVM potential): `N` = its range. -/
theorem TerminatingProgBoundedOn.while_rank
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {condition : ExpHOL 64}
    {body : ProgHOL 64} {B N : Nat}
    (μ : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat)
    (hdec : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → P (decClockHOLFinite s))
    (hbody : TerminatingProgBoundedOn P body B)
    (hle : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      P s → LoopActive condition s → μ s ≤ N)
    (hstep : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      P s → LoopActive condition s →
      ((evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .continue) →
      P (evaluateHOLFiniteState (decClockHOLFinite s) body).2 ∧
        μ (evaluateHOLFiniteState (decClockHOLFinite s) body).2 < μ s) :
    TerminatingProgBoundedOn P (.while condition body) ((N + 1) * (B + 1)) :=
  TerminatingProgBoundedOn.while_rank_stationary μ hdec hbody hle
    fun s hcode hP hact hflow =>
      let h := hstep s hcode hP hact hflow
      ⟨h.1, Or.inl h.2⟩

/-! ### `while` rules with the body needed only on active loop heads (round-3 item 1)

`gb_run_frames` uses `P = GuestInv ∧ (EvmInv ∨ go = 0)`: the last iteration restores `ev` and
`cur_cont` and sets `go := 0`, so `P` must admit exit states that are not `EvmInv`, and from those
the body's guarded callees (`op_dispatch`, `finish_child`, …) have no bound leaf. The body is only
ever run after an active head, so the rules below ask for its bound under
`P s ∧ LoopActive condition s` (for `run_frames`: `go ≠ 0`, hence `EvmInv`). Same proof as
`while_rank_stationary`; the condition is read without the clock, so it survives `decClock`. -/

/-- The loop condition does not read the clock: an active head stays active after `decClock`. -/
theorem loopActive_decClock {condition : ExpHOL 64} {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : LoopActive condition s) : LoopActive condition (decClockHOLFinite s) := by
  obtain ⟨w, hw, hne⟩ := h
  refine ⟨w, ?_, hne⟩
  rw [← hw]
  exact @evalHOLFinite_upd_clock_eq 64 F _ s
    (fun address => Classical.propDecidable (s.memaddrs address)) (s.clock - 1) condition

/-- `while_rank_stationary` with the body bound required only on active `P` heads. -/
theorem TerminatingProgBoundedOn.while_rank_stationary_active
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {condition : ExpHOL 64}
    {body : ProgHOL 64} {B N : Nat}
    (μ : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat)
    (hdec : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → P (decClockHOLFinite s))
    (hbody : TerminatingProgBoundedOn (fun s => P s ∧ LoopActive condition s) body B)
    (hle : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      P s → LoopActive condition s → μ s ≤ N)
    (hstep : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      P s → LoopActive condition s →
      ((evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .continue) →
      P (evaluateHOLFiniteState (decClockHOLFinite s) body).2 ∧
        (μ (evaluateHOLFiniteState (decClockHOLFinite s) body).2 < μ s ∨
          Stationary condition body s (evaluateHOLFiniteState (decClockHOLFinite s) body).2)) :
    TerminatingProgBoundedOn P (.while condition body) ((N + 1) * (B + 1)) :=
  fun state hcode hP =>
    while_rank_stationary_aux μ
      (fun s hc hPs hact => hbody (decClockHOLFinite s) hc ⟨hdec s hPs, loopActive_decClock hact⟩)
      hstep (N + 1) state hcode hP (fun hact => by have := hle state hcode hP hact; omega)

/-- `while_rank` with the body bound required only on active `P` heads (`gb_run_frames`). -/
theorem TerminatingProgBoundedOn.while_rank_active
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {condition : ExpHOL 64}
    {body : ProgHOL 64} {B N : Nat}
    (μ : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat)
    (hdec : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → P (decClockHOLFinite s))
    (hbody : TerminatingProgBoundedOn (fun s => P s ∧ LoopActive condition s) body B)
    (hle : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      P s → LoopActive condition s → μ s ≤ N)
    (hstep : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      P s → LoopActive condition s →
      ((evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .continue) →
      P (evaluateHOLFiniteState (decClockHOLFinite s) body).2 ∧
        μ (evaluateHOLFiniteState (decClockHOLFinite s) body).2 < μ s) :
    TerminatingProgBoundedOn P (.while condition body) ((N + 1) * (B + 1)) :=
  TerminatingProgBoundedOn.while_rank_stationary_active μ hdec hbody hle
    fun s hcode hP hact hflow =>
      let h := hstep s hcode hP hact hflow
      ⟨h.1, Or.inl h.2⟩

/-! ### Guards that read locals (round-2 item 3) -/

/-- `P` reads the locals only through the names in `names`, and ignores the clock. Every guard of
the guarded tier has this form: `GuestInv`, `ArenaReady`, `WorldOK`, `EvmInv`, `FinishReady`
(`names = []`), `HtabArgWF` (`["t"]`), `UnionArgWF` (`["dst"]`), `MptReady` (`["node"]`),
`MptObjReady` (`["m"]`), `RollbackReady` (`["child"]`). -/
def LocalsOnly (names : List String) (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) :
    Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (locals : HolFiniteMapExact MlS (ValueHOL 64))
    (k : Nat), (∀ n ∈ names, locals.lookup (ofString n) = s.locals.lookup (ofString n)) →
    P s → P { s with locals := locals, clock := k }

theorem LocalsOnly.of_localsFree {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (h : LocalsFree P) : LocalsOnly [] P :=
  fun s locals k _ hP => h s locals k hP

theorem localsOnly_guestInv : LocalsOnly [] GuestInv :=
  LocalsOnly.of_localsFree localsFree_guestInv

/-- The clock step of a loop head keeps such a guard (`hdec` of `while_rank`). -/
theorem LocalsOnly.decClock {names : List String}
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (h : LocalsOnly names P)
    {F : Type} (s : PanSemStateFiniteExact 64 F) (hP : P s) : P (decClockHOLFinite s) :=
  h s s.locals (s.clock - 1) (fun _ _ => rfl) hP

/-- Declaring a local that the guard does not read keeps the guard. -/
theorem LocalsOnly.setVar {names : List String}
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (h : LocalsOnly names P)
    {name : MlS} (hname : ∀ n ∈ names, ofString n ≠ name) (v : ValueHOL 64)
    {F : Type} (s : PanSemStateFiniteExact 64 F) (hP : P s) : P (setVarHOLFinite name v s) := by
  have := h s (s.locals.update (name, v)) s.clock (fun n hn => by
    have hne := hname n hn
    simp only [HolFiniteMapExact.update, FUPDATE]
    split
    · rename_i heq; exact absurd (by simpa using heq) hne.symm
    · rfl) hP
  simpa [setVarHOLFinite] using this

/-- `dec` for a guard that reads locals (round-2 item 3): the declared name must not be one the
guard reads. Every `dec` inside the guarded leaves declares a fresh name (`pos`, `leaf`, `k`, …)
distinct from the guard's parameter (`t`, `dst`, `node`, `m`, `child`). -/
theorem TerminatingProgBoundedOn.dec_onLocals
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {names : List String}
    (hP : LocalsOnly names P) (name : MlS) (hname : ∀ n ∈ names, ofString n ≠ name)
    (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64} {K : Nat}
    (hbody : TerminatingProgBoundedOn P body K) :
    TerminatingProgBoundedOn P (.dec name shape init body) K := by
  intro F state hcode hPs
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  revert hnt
  split <;> intro hnt
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · revert hnt
    split <;> intro hnt
    · rename_i val _ _
      have hb := hbody (setVarHOLFinite name val state) hcode (hP.setVar hname val state hPs) hnt
      simpa [setVarHOLFinite] using hb
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

/-- The condition of an `ite` evaluates to a nonzero word (resp. to the word `0`). -/
def CondTrue (cond : ExpHOL 64) {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ w : BitVec 64, @evalHOLExact 64 F _ s.toExact
    (fun address => Classical.propDecidable (s.memaddrs address)) cond = some (.val (.word w)) ∧
    w ≠ 0

def CondFalse (cond : ExpHOL 64) {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  @evalHOLExact 64 F _ s.toExact
    (fun address => Classical.propDecidable (s.memaddrs address)) cond = some (.val (.word 0))

/-- `ite` whose branches may use the outcome of the test (a guarded call under a test such as
`kind ≠ 0` before `finish_child`). -/
theorem TerminatingProgBoundedOn.ite_cond_on
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {cond : ExpHOL 64}
    {yes no : ProgHOL 64} {a b : Nat}
    (hyes : TerminatingProgBoundedOn (fun s => P s ∧ CondTrue cond s) yes a)
    (hno : TerminatingProgBoundedOn (fun s => P s ∧ CondFalse cond s) no b) :
    TerminatingProgBoundedOn P (.ite cond yes no) (max a b) := by
  intro F state hcode hP
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_ite] at hnt ⊢
  revert hnt
  split <;> intro hnt
  · rename_i w hw
    revert hnt
    split <;> intro hnt
    · rename_i hz
      subst hz
      exact TerminatingRunBounded.weaken (hno state hcode ⟨hP, hw⟩) (Nat.le_max_right a b) hnt
    · rename_i hz
      exact TerminatingRunBounded.weaken (hyes state hcode ⟨hP, w, hw, hz⟩) (Nat.le_max_left a b)
        hnt
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

/-- What a `decCall`'s continuation may assume: from a `P` caller state whose callee returned
`value` normally, the resumed state (`name := value`, caller locals, callee memory and globals)
satisfies `Q`. Discharged by the callee's contract (`FunSpec`/`FunEnsures`, §7) and, for a guard
reading locals, `LocalsOnly`. -/
def DecCallResumeOn (P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) (name : MlS)
    (fname : MlS) (arguments : List (ExpHOL 64)) : Prop :=
  ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (value : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
    state.code = originalRuntimeCode → P state →
    evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      arguments = some values →
    lookupCodeHOLFinite state.code.lookup fname values = some (body, callee, returnShape) →
    evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
      (some (.returned value), post) →
    Q (setVarHOLFinite name value { post with locals := state.locals })

/-- Guarded `decCall`: callee guard `Pc` from `CallEntryOn`, continuation guard `Q` from
`DecCallResumeOn`. `decCall_guestInv` is the instance `P = Pc = Q = GuestInv`. -/
theorem TerminatingProgBoundedOn.decCall_on
    {P Pc Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {fname : MlS} {B Bc : Nat}
    (hf : TerminatingFunBoundedOn Pc fname B)
    (name : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) {continuation : ProgHOL 64}
    (hentry : CallEntryOn P Pc fname arguments)
    (hres : DecCallResumeOn P Q name fname arguments)
    (hcont : TerminatingProgBoundedOn Q continuation Bc) :
    TerminatingProgBoundedOn P (.decCall name shape fname arguments continuation)
      (B + Bc + 1) := by
  obtain ⟨params, body, ret, hlook, hbody⟩ := hf
  intro F state hcode hP hnt
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  rcases hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
    _ | values
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite state.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    · simp only [hl] at hnt ⊢
      obtain ⟨hbb, hrunBound⟩ := callee_body_bound hlook hbody hentry state hcode hP values body'
        callee ret' hargs hl
      subst hbb
      by_cases hz : state.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee)
          body').1
        have hresQ := hres state values body' callee ret'
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body' with
          ⟨res, post⟩
        simp only [hrun] at hnt hmeta ⊢
        change post.code = state.code at hmeta
        have bodyClock (hsafe : res ≠ some .timeOut) :
            state.clock - 1 ≤ post.clock + B ∧ post.clock ≤ state.clock - 1 := by
          have hb := hrunBound (by rw [hrun]; exact hsafe)
          rw [hrun] at hb
          exact hb
        cases res with
        | none =>
          obtain ⟨hs, hk⟩ := bodyClock (by simp)
          exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
        | some r =>
          cases r with
          | returned value =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact value) shape &&
                shapeEqHOL (shapeOfHOLExact value) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt ⊢
              set resumed := setVarHOLFinite name value { post with locals := state.locals } with hres'
              have hresCode : resumed.code = originalRuntimeCode := hmeta.trans hcode
              have hresInv : Q resumed := hresQ value post hcode hP hargs hl hrun
              have hcb := hcont resumed hresCode hresInv hnt
              obtain ⟨hsc, hkc⟩ := hcb
              change post.clock ≤ (evaluateHOLFiniteState resumed continuation).2.clock + Bc
                at hsc
              change (evaluateHOLFiniteState resumed continuation).2.clock ≤ post.clock at hkc
              exact ⟨by omega, by omega⟩
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte]
              exact ⟨by omega, by omega⟩
          | timeOut => simp at hnt
          | «break» =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
          | «continue» =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
          | _ =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega⟩
