import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4Q2

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

/-! # Phase 4Q3: the g8 tail setup (instructions 34-36)

This file continues `WkPtxPhase4Q2`.  After the `lst_new` allocation, the
program stores the count into the fresh header (`stable_logs + 8 := nl`,
instruction 34), loads the fresh backing pointer into `stable_lp`
(`stable_logs + 0`, instruction 35), resets `i := 0` (instruction 36), and
enters the copy loop (loop 38).  The three setup steps are pure
forward-evaluation work: the count store writes the single header cell
`lw + 8` (the only memory effect, and the data-base cell `lw` is untouched
because `lw ≠ lw + 8`), and the two local bindings only extend the locals.
The continuation receives the fully explicit post-setup state. -/

/-- Forward evaluation of the `stable_logs + 0` load (instruction 35):
the address is the header's data-base cell, an in-domain word. -/
theorem p4Q8_eval_load_stable0 {F : Type}
    {s : PanSemStateFiniteExact 64 F} {lw v : BitVec 64}
    (hsl : s.locals.lookup (ofString "stable_logs") = some (.val (.word lw)))
    (hdom : s.memaddrs lw)
    (hcell : s.memory lw = .word v) :
    evalAt s (.load .one (.op .add [.var .local (ofString "stable_logs"),
        (.const 0x0000000000000000#64)])) =
      some (.val (.word v)) := by
  have hz : lw + ((0x0000000000000000#64 : BitVec 64) + (0 : BitVec 64)) = lw := by
    simp
  simp only [evalAt, evalHOLExact, evalListHOLExact, toExact, hsl, valueIsWord, valueWord,
    wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
    memLoadHOLExact, isWfShapeExactHOL, hz, hdom, hcell]

/-- Instructions 34-36: the count store, the `stable_lp` load and the `i`
reset.  The memory effect is exactly one header-cell write
(`lw + 8 := nl_w`); the locals gain `stable_lp` (the data-base word `w_lp`
of the fresh header) and `i := 0`. -/
theorem p4Q8_tailSetup {F : Type}
    {entry mid : PanSemStateFiniteExact 64 F} {lw nl_w w_lp : BitVec 64}
    (tail : ProgHOL 64)
    (hnl : mid.locals.lookup (ofString "nl") = some (.val (.word nl_w)))
    (hsl : mid.locals.lookup (ofString "stable_logs") = some (.val (.word lw)))
    (hhdr : WordsOK mid (lw.toNat, 24))
    (hlw64 : lw.toNat + 24 ≤ 2 ^ 64)
    (hw0 : mid.memory lw = .word w_lp)
    (htail : PtxRelRunStrong entry tail
      (setVarHOLFinite (ofString "i") (.val (.word 0x0000000000000000#64))
        (setVarHOLFinite (ofString "stable_lp") (.val (.word w_lp))
          {mid with memory :=
            (pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w)}))) :
    PtxRelRunStrong entry
      (.seq (.store (.op .add [.var .local (ofString "stable_logs"),
          (.const 0x0000000000000008#64)])
          (.var .local (ofString "nl")))
        (.dec (ofString "stable_lp") .one
          (.load .one (.op .add [.var .local (ofString "stable_logs"),
            (.const 0x0000000000000000#64)]))
          (.seq (.assign .local (ofString "i") (.const 0x0000000000000000#64))
            tail))) mid := by
  -- geometry of the fresh header
  have hlt : lw.toNat < 2 ^ 64 := by omega
  have hdom8 : mid.memaddrs (BitVec.ofNat 64 (lw.toNat + 8)) := by
    obtain ⟨u, hd8, _⟩ := hhdr.2.2 1 (by norm_num)
    have hz8 : BitVec.ofNat 64 (lw.toNat + 8 * 1) = BitVec.ofNat 64 (lw.toNat + 8) := by
      simp only [Nat.mul_one]
    rwa [hz8] at hd8
  have hdom_lw : mid.memaddrs lw := by
    obtain ⟨u, hd0, _⟩ := hhdr.2.2 0 (by norm_num)
    have hz0 : BitVec.ofNat 64 (lw.toNat + 8 * 0) = lw := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt hlt]
    rwa [hz0] at hd0
  -- the count store's address differs from the data-base cell
  have hne : lw ≠ BitVec.ofNat 64 (lw.toNat + 8) := by
    intro heq
    have h2 : (BitVec.ofNat 64 (lw.toNat + 8)).toNat = lw.toNat :=
      congrArg BitVec.toNat heq.symm
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h2
    omega
  -- instruction 34: `store (stable_logs + 8) := nl`
  refine p4Run_store (.op .add [.var .local (ofString "stable_logs"),
      (.const 0x0000000000000008#64)]) (.var .local (ofString "nl")) _ ?_
  intro a v mem' hdst hsrc hmem
  have haddr : evalAt mid (.op .add [.var .local (ofString "stable_logs"),
      (.const 0x0000000000000008#64)]) =
      some (.val (.word (BitVec.ofNat 64 (lw.toNat + 8)))) :=
    p4Q8_eval_var_add_const hsl (by omega)
  rw [haddr] at hdst
  have ha : a = BitVec.ofNat 64 (lw.toNat + 8) := by
    injection hdst with h1
    injection h1 with h2
    injection h2 with h3
    exact h3.symm
  have hv : v = .val (.word nl_w) := by
    simp only [evalAt, evalHOLExact, toExact, hnl] at hsrc
    exact (Option.some.inj hsrc).symm
  subst ha
  subst hv
  have hmem' : mem' = pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w := by
    have heq := p4Q8_store_word_eq (s := mid)
      (x := BitVec.ofNat 64 (lw.toNat + 8)) (w := nl_w) hdom8
    rw [hmem] at heq
    exact Option.some.inj heq
  subst hmem'
  -- instruction 35: load the data base into `stable_lp`
  refine p4Run_dec (ofString "stable_lp") .one
    (.load .one (.op .add [.var .local (ofString "stable_logs"),
      (.const 0x0000000000000000#64)])) _ ?_
  intro v2 hev2 hsh2
  have hload : evalAt {mid with memory :=
      (pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w)}
      (.load .one (.op .add [.var .local (ofString "stable_logs"),
        (.const 0x0000000000000000#64)])) = some (.val (.word w_lp)) :=
    p4Q8_eval_load_stable0 hsl hdom_lw
      (by show pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w lw = .word w_lp
          simp only [pmcUpdW, hne]
          exact hw0)
  rw [hload] at hev2
  have hv2 : v2 = .val (.word w_lp) := (Option.some.inj hev2).symm
  subst hv2
  -- instruction 36: reset `i`
  refine p4Run_assign (ofString "i") (.const 0x0000000000000000#64) _ ?_
  intro v3 hev3
  have hc3 : evalAt (setVarHOLFinite (ofString "stable_lp") (.val (.word w_lp))
      {mid with memory := (pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w)})
      (ExpHOL.const 0x0000000000000000#64) =
      some (.val (.word 0x0000000000000000#64)) := rfl
  rw [hc3] at hev3
  have hv3 : v3 = .val (.word 0x0000000000000000#64) := (Option.some.inj hev3).symm
  subst hv3
  exact htail

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
