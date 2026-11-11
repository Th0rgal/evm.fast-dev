import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.GbodyRunAttempt

/-! Wave 8 R32 Slot 8 (RunAttemptHtrR32), obligation B core.

`run_attempt`'s strong entry guard `InputReadyStrong` requires every host-input cell
(`runAttemptCells`) to be a nonempty heap interval. At the decode boundary the empty
transaction / witness / access-list case materializes as `(0, 0)` cells — exactly what
`ssz_split_var_list` returns for an empty list — and `(0, 0)` is never `Inside` the heap
window because `sourceBase > 0`. This module weakens the guard to `InputReadyR32`:
every cell is either the null pair `(0, 0)` or an ordinary `Inside` interval, keeping
alignment, `WordsOK`, world disjointness, the `nvh`/`nwd` bounds and `PayloadAt`/
`RequestsAt`.

On states whose cells are all `Inside` (every nonempty decode output), the R32 guard
is equivalent to the strong one (`inputAtStrong_of_r32`), so the strong bound applies
verbatim. The residual `(0, 0)` states are carved out by `RunAttemptR32EmptyCase`,
which `gbody_run_attempt_r32_of` takes as an explicit premise: closing it requires a
full spine replay of `run_attempt`'s scan and is left to the sibling R32 missions. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptR32

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk

/-! ### Interval arithmetic helpers -/

/-- Sub-intervals: shrinking the size keeps `Inside`. -/
theorem inside_of_le {lo hi a b b' : Nat} (hle : b' ≤ b) (h : Inside (a, b) lo hi) :
    Inside (a, b') lo hi := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨h1, by omega⟩

/-- Sub-intervals: shrinking the size keeps `WordsOK` (new size separately aligned). -/
theorem wordsOK_of_le {F : Type} {s : PanSemStateFiniteExact 64 F} {a b b' : Nat}
    (hb' : b' % 8 = 0) (hle : b' ≤ b) (h : WordsOK s (a, b)) : WordsOK s (a, b') := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, hb', fun k hk => h3 k (by omega)⟩

/-- Shrinking the left endpoint's reach keeps left-side disjointness. -/
theorem disj_left_of_le {i j : Ivl} {n : Nat} (hle : n ≤ i.2) (h : Disj i j) :
    Disj (i.1, n) j := by
  rcases h with h | h | h | h
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr h))

/-- Membership in `inputCells` as a four-way disjunction. -/
theorem inputCells_mem_cases {F : Type} {s : PanSemStateFiniteExact 64 F} {si : Nat}
    {i : Ivl} (hi : i ∈ inputCells s si) :
    i = (si, 40) ∨ i = (memW s si, 136) ∨ i = (memW s (si + 32), 80) ∨
      i = (memW s (memW s si + 32), 16 * memW s (memW s si + 40)) := by
  simp only [inputCells] at hi
  rcases List.mem_cons.mp hi with rfl | hi
  · exact Or.inl rfl
  rcases List.mem_cons.mp hi with rfl | hi
  · exact Or.inr (Or.inl rfl)
  rcases List.mem_cons.mp hi with rfl | hi
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases List.mem_cons.mp hi with rfl | hi
  · exact Or.inr (Or.inr (Or.inr rfl))
  exact absurd hi (List.not_mem_nil)

/-! ### The R32 input guard -/

/-- `InputAtStrongWith` with the per-cell `Inside` requirement weakened to "null pair or
`Inside`". Everything else (alignment, `WordsOK`, world disjointness, `nvh`/`nwd`
numeric bounds, `PayloadAt`, `RequestsAt`) is unchanged. -/
def InputAtR32With {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S Nd : List Nat) (si : Nat) : Prop :=
  ArenaReady s ∧ WorldTypedWith s S Nd ∧
    (∀ i ∈ runAttemptCells s si,
      i.1 % 8 = 0 ∧ ((i.1 = 0 ∧ i.2 = 0) ∨
        Inside i sourceBase (globN s "heap_ptr")) ∧ WordsOK s i) ∧
    IvlsDisj (runAttemptCells s si) (worldOwned s S Nd) ∧
    memW s (si + 16) < 2 ^ 32 ∧
    memW s (memW s si + 56) < 2 ^ 32 ∧
    PayloadAt s (memW s si) ∧ RequestsAt s (memW s (si + 32))

def InputAtR32 {F : Type} (s : PanSemStateFiniteExact 64 F) (si : Nat) : Prop :=
  ∃ S Nd, InputAtR32With s S Nd si

def InputReadyR32 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => InputAtR32 s (locN s "si")

/-! ### Strong implies R32 -/

theorem inputAtR32With_of_strongWith {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si : Nat} (h : InputAtStrongWith s S Nd si) :
    InputAtR32With s S Nd si := by
  obtain ⟨⟨hAr, hWT, -, -, -, hPay, hReq⟩, hcells, hdisj, hnvh, hnwd⟩ := h
  exact ⟨hAr, hWT,
    fun i hi => ⟨(hcells i hi).1, Or.inr (hcells i hi).2.1, (hcells i hi).2.2⟩,
    hdisj, hnvh, hnwd, hPay, hReq⟩

theorem inputAtR32_of_strongWith {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si : Nat} (h : InputAtStrongWith s S Nd si) : InputAtR32 s si :=
  ⟨S, Nd, inputAtR32With_of_strongWith h⟩

theorem inputAtR32_of_strong {F : Type} {s : PanSemStateFiniteExact 64 F} {si : Nat}
    (h : InputAtStrong s si) : InputAtR32 s si := by
  obtain ⟨hIn, hnvh, hnwd, S, Nd, hWT, hcells, hdisj⟩ := h
  obtain ⟨hAr, S', Nd', -, -, -, -, hPay, hReq⟩ := hIn
  exact ⟨S, Nd, hAr, hWT,
    fun i hi => ⟨(hcells i hi).1, Or.inr (hcells i hi).2.1, (hcells i hi).2.2⟩,
    hdisj, hnvh, hnwd, hPay, hReq⟩

theorem inputReadyR32_of_strong {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : InputReadyStrong s) : InputReadyR32 s :=
  inputAtR32_of_strong h

/-! ### R32 with all cells `Inside` implies strong -/

theorem inputAtStrong_of_r32 {F : Type} {s : PanSemStateFiniteExact 64 F} {si : Nat}
    (h : InputAtR32 s si)
    (hin : ∀ i ∈ runAttemptCells s si, Inside i sourceBase (globN s "heap_ptr")) :
    InputAtStrong s si := by
  obtain ⟨S, Nd, hAr, hWT, hcells, hdisj, hnvh, hnwd, hPay, hReq⟩ := h
  -- The transaction count bound: `PayloadAt` gives `ntx < 2^32 < 2^63`.
  have hntx : memW s (memW s si + 40) < 2 ^ 63 := Nat.lt_trans hPay.2.2.1 (by decide)
  -- The 96-byte run-attempt header cell covers the 40-byte `inputCells` header cell.
  have hsi96 := hcells (si, 96) (by simp [runAttemptCells])
  have hsi96In : Inside (si, 96) sourceBase (globN s "heap_ptr") :=
    hin (si, 96) (by simp [runAttemptCells])
  have h4cells : ∀ i ∈ inputCells s si,
      Inside i sourceBase (globN s "heap_ptr") ∧ WordsOK s i := by
    intro i hi
    rcases inputCells_mem_cases hi with rfl | rfl | rfl | rfl
    · exact ⟨inside_of_le (by decide) hsi96In, wordsOK_of_le (by decide) (by decide) hsi96.2.2⟩
    · exact ⟨hin _ (by simp [runAttemptCells]), (hcells _ (by simp [runAttemptCells])).2.2⟩
    · exact ⟨hin _ (by simp [runAttemptCells]), (hcells _ (by simp [runAttemptCells])).2.2⟩
    · exact ⟨hin _ (by simp [runAttemptCells]), (hcells _ (by simp [runAttemptCells])).2.2⟩
  have hdisj4 : IvlsDisj (inputCells s si) (worldOwned s S Nd) := by
    intro i hi j hj
    rcases inputCells_mem_cases hi with rfl | rfl | rfl | rfl
    · exact disj_left_of_le (by decide : (40 : Nat) ≤ 96)
        (hdisj (si, 96) (by simp [runAttemptCells]) j hj)
    · exact hdisj _ (by simp [runAttemptCells]) j hj
    · exact hdisj _ (by simp [runAttemptCells]) j hj
    · exact hdisj _ (by simp [runAttemptCells]) j hj
  exact ⟨⟨hAr, S, Nd, hWT, h4cells, hdisj4, hntx, hPay, hReq⟩, hnvh, hnwd, S, Nd, hWT,
    fun i hi => ⟨(hcells i hi).1, hin i hi, (hcells i hi).2.2⟩, hdisj⟩

theorem inputReadyStrong_of_r32 {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : InputReadyR32 s)
    (hin : ∀ i ∈ runAttemptCells s (locN s "si"), Inside i sourceBase (globN s "heap_ptr")) :
    InputReadyStrong s :=
  inputAtStrong_of_r32 h hin

/-! ### Case split -/

/-- An R32 state either has every cell `Inside` (the strong guard holds) or some cell is
the null pair `(0, 0)` (the decode-empty case). -/
theorem inputAtR32_cases {F : Type} {s : PanSemStateFiniteExact 64 F} {si : Nat}
    (h : InputAtR32 s si) :
    (∀ i ∈ runAttemptCells s si, Inside i sourceBase (globN s "heap_ptr")) ∨
      (∃ i ∈ runAttemptCells s si, i.1 = 0 ∧ i.2 = 0) := by
  obtain ⟨S, Nd, -, -, hcells, -, -, -, -, -⟩ := h
  by_cases hall : ∀ i ∈ runAttemptCells s si, Inside i sourceBase (globN s "heap_ptr")
  · exact Or.inl hall
  · push_neg at hall
    obtain ⟨i, hi, hni⟩ := hall
    refine Or.inr ⟨i, hi, ?_⟩
    rcases (hcells i hi).2.1 with h | h
    · exact h
    · exact absurd h hni

/-! ### Guarded bound plumbing -/

/-- The residual decode-empty case: some run-attempt cell is the null pair `(0, 0)`. -/
def RunAttemptR32EmptyCase : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => InputReadyR32 s ∧ ∃ i ∈ runAttemptCells s (locN s "si"), i.1 = 0 ∧ i.2 = 0

/-- On nonempty decode output (all cells `Inside`), the strong bound is the R32 bound. -/
theorem gbody_run_attempt_r32_nonempty
    (hstrong : TerminatingFunBoundedOn InputReadyStrong (ofString "run_attempt")
      K.«run_attempt») :
    TerminatingFunBoundedOn
      (fun s => InputReadyR32 s ∧
        ∀ i ∈ runAttemptCells s (locN s "si"), Inside i sourceBase (globN s "heap_ptr"))
      (ofString "run_attempt") K.«run_attempt» :=
  hstrong.mono (fun _ hs => inputReadyStrong_of_r32 hs.1 hs.2)

/-- Main R32 `run_attempt` bound: the strong bound plus the decode-empty-case bound
(both taken as premises) give the bound on the weakened guard. The empty case is the
only R32-specific obligation left open; every other state satisfies the strong guard
and is covered by the existing `run_attempt` proof. -/
theorem gbody_run_attempt_r32_of
    (hstrong : TerminatingFunBoundedOn InputReadyStrong (ofString "run_attempt")
      K.«run_attempt»)
    (hempty : TerminatingFunBoundedOn RunAttemptR32EmptyCase (ofString "run_attempt")
      K.«run_attempt») :
    TerminatingFunBoundedOn InputReadyR32 (ofString "run_attempt") K.«run_attempt» := by
  obtain ⟨p, b, rs, hlk, hrun⟩ := hstrong
  obtain ⟨p2, b2, rs2, hlk2, hrun2⟩ := hempty
  rw [hlk] at hlk2
  obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj hlk2
  refine ⟨p, b, rs, hlk, fun state hcode hp => ?_⟩
  rcases inputAtR32_cases hp with hall | hzero
  · exact hrun state hcode (inputReadyStrong_of_r32 hp hall)
  · exact hrun2 state hcode ⟨hp, hzero⟩

end InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptR32
