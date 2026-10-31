
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

/-- Ranking rule for `while` (proposed combinator; the proof is the induction of
`PanTerminatingNoRepeat.while_noRepeat_aux` with `μ` in place of the visited-key count).
It covers the four loop classes of DESIGN.md §3:
* strict local counter `i < X`, `i := i + 1` (resp. `i ≠ 0`, `i := i - 1`): `μ = X - i` (resp.
  `μ = i`) read from the locals, `N = 2^64`, for ARBITRARY memory (errors inside the body
  terminate the run and are covered);
* fresh-address walk: `μ = heapEnd - address`, `N = W`;
* monotone measure (halving, degree, allocation potential, EVM potential): `N` = its range;
* a stationary iteration is a repeated loop head, i.e. a timeout, so it never needs a decrease
  (`while_noRepeat` on `wave8/step0` is the read-only special case). -/
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
    TerminatingProgBoundedOn P (.while condition body) ((N + 1) * (B + 1)) := by
  sorry
