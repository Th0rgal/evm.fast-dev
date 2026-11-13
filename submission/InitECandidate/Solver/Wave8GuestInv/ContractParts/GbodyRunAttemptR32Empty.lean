import InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptR32
import InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptR32VhNull
import InitECandidate.Solver.Wave8GuestInv.ContractParts.R32CanonicalBridges
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.GbodySysTxExecBlock

/-! Wave 8 R32 Slot 8 (RunAttemptHtrR32), obligation C: the decode-empty case.

`GbodyRunAttemptR32.gbody_run_attempt_r32_of` and
`R32CanonicalBridges.hraR32` take the decode-empty case
(`RunAttemptR32EmptyCase` / `RunAttemptR32CanonEmptyCase`: some run-attempt
cell is the null pair `(0, 0)`) as an explicit premise. This module delivers it
as a **parameterized spine**: the empty case is decomposed into the four
null-list sub-cases (a run-attempt cell can only be null if it is one of the
four indirect list cells — the tx, witness, access-list and vh-list cells,
since the three header cells have nonzero fixed sizes), and the spine
`hempty_of` assembles the full empty-case bound from one terminating-bounded
sub-case premise each.

Each sub-case premise is a documented open leaf for the sibling R32 missions:

* `TxNullCase` (tx list null, `ntx = 0 ∧ txs = 0`): `run_attempt`'s scan
  replays at the R32 guard and tails into the `execute_block` entry with an
  empty transaction list. The strong execute-block entry
  (`GbodySysTxExecBlock.ExecBlock.EntryAt`) fails there — its `inputRegions`
  demand the tx cell `Inside`, but `(0, 0)` is never `Inside` since
  `sourceBase > 0` — so the weakened entry `EntryAtR32` below (cells either
  null or `Inside`) and the payload-header replay at that guard are the
  residual obligations (`PayloadHeaderR32TxNullBound`,
  `ExecBlockR32Bound`).
* `WitNullCase` / `AccNullCase` (witness / access-list null): the scan replays
  with the corresponding loop at zero iterations; the execute-block entry
  still applies via the strong `BlockReadyExecStrong` on the remaining cells.
* `VhNullCase` (vh list null): the scan raises early at the empty
  validation-header list. This sub-case is **closed** below
  (`vhNullCase_run_attempt`, from
  `GbodyRunAttemptR32VhNull.run_attempt_vhLenZero`); `hraR32_of` no longer
  takes it as a premise.

Everything else in this module is proved: the null-cell decomposition, the
spine assembly `hempty_of`, the canonical-form corollary `hemptyCanon_of`
(exactly the `hempty` premise of `R32CanonicalBridges.hraR32`), the
end-to-end `hraR32_of`, and the bridge `entryAt_of_entryAtR32` showing the
weakened entry recovers the strong one on null-free inputs. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptR32Empty

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
open InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptR32
open InitECandidate.Solver.Wave8GuestInv.ContractParts.R32CanonicalBridges

/-! ### The four null-list sub-cases -/

/-- Tx-list null: the tx cell `(memW s (pl + 32), 16 * memW s (pl + 40))` of
`runAttemptCells` is the null pair (`txs = 0 ∧ ntx = 0`, with `pl = memW s si`). -/
def TxNullCase {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  InputReadyR32 s ∧
  memW s (memW s (locN s "si") + 32) = 0 ∧ memW s (memW s (locN s "si") + 40) = 0

/-- Witness-list null: the witness cell `(memW s (si + 40), 16 * memW s (si + 48))`
is the null pair. -/
def WitNullCase {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  InputReadyR32 s ∧
  memW s (locN s "si" + 40) = 0 ∧ memW s (locN s "si" + 48) = 0

/-- Access-list null: the access cell `(memW s (si + 56), 16 * memW s (si + 64))`
is the null pair. -/
def AccNullCase {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  InputReadyR32 s ∧
  memW s (locN s "si" + 56) = 0 ∧ memW s (locN s "si" + 64) = 0

/-- Vh-list null: the validation-header cell `(memW s (si + 72), 16 * memW s (si + 80))`
is the null pair. -/
def VhNullCase {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  InputReadyR32 s ∧
  memW s (locN s "si" + 72) = 0 ∧ memW s (locN s "si" + 80) = 0

/-- A null run-attempt cell must be one of the four indirect list cells: the
three header cells have the nonzero fixed sizes `96`, `136` and `80`, so they
can never satisfy `i.2 = 0`. -/
theorem runAttemptNullCell_cases {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hred : InputReadyR32 s) {i : Ivl}
    (hi : i ∈ runAttemptCells s (locN s "si")) (h0 : i.1 = 0 ∧ i.2 = 0) :
    TxNullCase s ∨ WitNullCase s ∨ AccNullCase s ∨ VhNullCase s := by
  simp only [runAttemptCells, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd (show (96 : Nat) = 0 from h0.2) (by decide)
  · exact absurd (show (136 : Nat) = 0 from h0.2) (by decide)
  · exact absurd (show (80 : Nat) = 0 from h0.2) (by decide)
  · refine Or.inl ⟨hred, h0.1, ?_⟩
    have h16 : 16 * memW s (memW s (locN s "si") + 40) = 0 := h0.2
    omega
  · refine Or.inr (Or.inl ⟨hred, h0.1, ?_⟩)
    have h16 : 16 * memW s (locN s "si" + 48) = 0 := h0.2
    omega
  · refine Or.inr (Or.inr (Or.inl ⟨hred, h0.1, ?_⟩))
    have h16 : 16 * memW s (locN s "si" + 64) = 0 := h0.2
    omega
  · refine Or.inr (Or.inr (Or.inr ⟨hred, h0.1, ?_⟩))
    have h16 : 16 * memW s (locN s "si" + 80) = 0 := h0.2
    omega

/-! ### The spine: `hempty_of` -/

/-- Parameterized empty-case spine: the four sub-case terminating bounds give
the full decode-empty-case bound (`GbodyRunAttemptR32.RunAttemptR32EmptyCase`,
the `hempty` premise of `GbodyRunAttemptR32.gbody_run_attempt_r32_of`). -/
theorem hempty_of
    (hTx : TerminatingFunBoundedOn TxNullCase (ofString "run_attempt") K.«run_attempt»)
    (hWit : TerminatingFunBoundedOn WitNullCase (ofString "run_attempt") K.«run_attempt»)
    (hAcc : TerminatingFunBoundedOn AccNullCase (ofString "run_attempt") K.«run_attempt»)
    (hVh : TerminatingFunBoundedOn VhNullCase (ofString "run_attempt") K.«run_attempt») :
    TerminatingFunBoundedOn RunAttemptR32EmptyCase (ofString "run_attempt")
      K.«run_attempt» := by
  obtain ⟨p1, b1, rs1, hlk1, hrun1⟩ := hTx
  obtain ⟨p2, b2, rs2, hlk2, hrun2⟩ := hWit
  obtain ⟨p3, b3, rs3, hlk3, hrun3⟩ := hAcc
  obtain ⟨p4, b4, rs4, hlk4, hrun4⟩ := hVh
  rw [hlk1] at hlk2 hlk3 hlk4
  obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj hlk2
  obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj hlk3
  obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj hlk4
  refine ⟨p1, b1, rs1, hlk1, fun state hcode hp => ?_⟩
  obtain ⟨hred, i, hi, h0⟩ := hp
  rcases runAttemptNullCell_cases hred hi h0 with h | h | h | h
  · exact hrun1 state hcode h
  · exact hrun2 state hcode h
  · exact hrun3 state hcode h
  · exact hrun4 state hcode h

/-- Canonical-form corollary: the four sub-case bounds give exactly the
`hempty` premise of `R32CanonicalBridges.hraR32` (and of
`R32CanonicalBridges.run_attempt_r32_canon`). -/
theorem hemptyCanon_of
    (hTx : TerminatingFunBoundedOn TxNullCase (ofString "run_attempt") K.«run_attempt»)
    (hWit : TerminatingFunBoundedOn WitNullCase (ofString "run_attempt") K.«run_attempt»)
    (hAcc : TerminatingFunBoundedOn AccNullCase (ofString "run_attempt") K.«run_attempt»)
    (hVh : TerminatingFunBoundedOn VhNullCase (ofString "run_attempt") K.«run_attempt») :
    TerminatingFunBoundedOn RunAttemptR32CanonEmptyCase (ofString "run_attempt")
      K.«run_attempt» :=
  (hempty_of hTx hWit hAcc hVh).mono (fun s hs =>
    ⟨(inputReadyR32CanonBounded_iff _).mp hs.1, hs.2⟩)

/-- The vh-list-null sub-case, closed: with an empty witness header list
`run_attempt` throws `BlockErr 3` right after `validate_headers(_, 0)`
(`GbodyRunAttemptR32VhNull.run_attempt_vhLenZero`). -/
theorem vhNullCase_run_attempt :
    TerminatingFunBoundedOn VhNullCase (ofString "run_attempt") K.«run_attempt» :=
  GbodyRunAttemptR32VhNull.run_attempt_vhLenZero.mono (fun _ hs => ⟨hs.1, hs.2.2⟩)

/-- End-to-end: the `hraR32` premise of `MainEntryR32.mainEntryR32` from the
strong bound plus the three open empty-case sub-bounds (the vh-list-null
sub-case is `vhNullCase_run_attempt`). -/
theorem hraR32_of
    (hstrong : TerminatingFunBoundedOn InputReadyStrong (ofString "run_attempt")
      K.«run_attempt»)
    (hTx : TerminatingFunBoundedOn TxNullCase (ofString "run_attempt") K.«run_attempt»)
    (hWit : TerminatingFunBoundedOn WitNullCase (ofString "run_attempt") K.«run_attempt»)
    (hAcc : TerminatingFunBoundedOn AccNullCase (ofString "run_attempt") K.«run_attempt») :
    TerminatingFunBoundedOn MainEntryR32.InputReadyR32 (ofString "run_attempt")
      K.«run_attempt» :=
  hraR32 hstrong (hemptyCanon_of hTx hWit hAcc vhNullCase_run_attempt)

/-! ### The R32 execute-block entry (tx-null route) -/

/-- Weakened `EntryAt` for the tx-null route: identical to
`GbodySysTxExecBlock.ExecBlock.EntryAt` except that an input region may be
the null pair `(0, 0)` (the empty-list encoding, never `Inside` the heap
window since `sourceBase > 0`) instead of an `Inside` interval. -/
def EntryAtR32 {F : Type} (s : PanSemStateFiniteExact 64 F) (si hdr : Nat) : Prop :=
  globN s "journal_cap" ≠ 0 ∧
  ∃ S Nd, WorldTypedWith s S Nd ∧
    (∀ c ∈ ExecBlock.inputRegions s si hdr,
      c.1 % 8 = 0 ∧ ((c.1 = 0 ∧ c.2 = 0) ∨ Inside c sourceBase (globN s "heap_ptr")) ∧
      WordsOK s c) ∧
    IvlsDisj (ExecBlock.inputRegions s si hdr) (worldOwned s S Nd) ∧
    (∀ i, i < memW s (memW s si + 40) →
      let p := memW s (memW s (memW s si + 32) + 16 * i)
      let n := memW s (memW s (memW s si + 32) + 16 * i + 8)
      p + n ≤ globN s "heap_ptr") ∧
    memW s (memW s si + 56) < 2 ^ 32 ∧
    (∀ i, i < memW s (memW s si + 56) →
      memW s (globN s "wd_rlp_slices" + 16 * i + 8) < 2 ^ 40) ∧
    (globN s "block_hashes_n" ≠ 0 →
      Inside (globN s "block_hashes", 32 * globN s "block_hashes_n")
        sourceBase (globN s "heap_ptr") ∧
      WordsOK s (globN s "block_hashes", 32 * globN s "block_hashes_n") ∧
      IvlsDisj [(globN s "block_hashes", 32 * globN s "block_hashes_n")]
        (worldOwned s S Nd))

/-- Bridge: on null-free inputs the weakened entry recovers the strong one. -/
theorem entryAt_of_entryAtR32 {F : Type} {s : PanSemStateFiniteExact 64 F} {si hdr : Nat}
    (h : EntryAtR32 s si hdr)
    (hnn : ∀ c ∈ ExecBlock.inputRegions s si hdr, ¬(c.1 = 0 ∧ c.2 = 0)) :
    ExecBlock.EntryAt s si hdr := by
  obtain ⟨hjc, S, Nd, hWT, hcells, hdisj, htx, hnwd, hwd, hbh⟩ := h
  refine ⟨hjc, S, Nd, hWT, ?_, hdisj, htx, hnwd, hwd, hbh⟩
  intro c hc
  obtain ⟨hal, hor, hwok⟩ := hcells c hc
  exact ⟨hal, hor.resolve_left (hnn c hc), hwok⟩

/-- The R32 execute-block entry: `GbodySysTxExecBlock.BlockReadyExecStrong`
with the strong `EntryAt` relaxed to `EntryAtR32`. -/
def BlockReadyExecR32 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => BlockReadyStrong s ∧
    (∀ name ∈ (["si", "hdr"] : List String),
      ∃ w : BitVec 64, s.locals.lookup (ofString name) = some (.val (.word w))) ∧
    EntryAtR32 s (locN s "si") (locN s "hdr")

/-- Bridge: on null-free inputs the R32 execute-block entry recovers the
strong one. -/
theorem blockReadyExecStrong_of_r32 {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : BlockReadyExecR32 s)
    (hnn : ∀ c ∈ ExecBlock.inputRegions s (locN s "si") (locN s "hdr"),
      ¬(c.1 = 0 ∧ c.2 = 0)) :
    BlockReadyExecStrong s :=
  ⟨h.1, h.2.1, entryAt_of_entryAtR32 h.2.2 hnn⟩

/-- The residual `execute_block` bound at the R32 entry (open leaf,
sibling-mission scale): replaying `GbodySysTxExecBlock`'s execute-block walk
at `EntryAtR32` — the tx list is empty there, so the per-transaction loop
runs zero iterations and only the block-level spine remains. -/
abbrev ExecBlockR32Bound : Prop :=
  TerminatingFunBoundedOn BlockReadyExecR32 (ofString "execute_block")
    K.«execute_block»

/-- The weakened payload-header spec for the tx-null route (open leaf,
sibling-mission scale): the `run_attempt` scan — including the
`payload_header` walk, whose proven form
(`GbodyPayloadHeaderExport.«gbody_payload_header»`) demands the strong
all-`Inside` entry that fails on the null `(0, 0)` tx cell — replayed at the
R32 guard. Shape: the `hTx` premise of `hempty_of`. -/
abbrev PayloadHeaderR32TxNullBound : Prop :=
  TerminatingFunBoundedOn TxNullCase (ofString "run_attempt") K.«run_attempt»

end InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptR32Empty
