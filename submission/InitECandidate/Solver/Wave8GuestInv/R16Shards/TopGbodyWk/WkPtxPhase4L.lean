import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4K

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

/-! # Phase 4L: the loop-31 assembly

The guard-threading while-runner (`p4Run_while_guard`): unlike `p4Run_while`
(Phase 4G), the body obligation receives the loop-guard fact (the condition
evaluated to a nonzero word), which the loop-31 body needs for the source
cell (the log entry at `lp + 8*i` is in the list only for `i < nl`) and for
the invariant's index bound.  The full loop-31 invariant
(`P4Loop31Full`) adds to `P4Loop31` the `TxEnv`, the nonvacuousness of the
`out+16` log list, and the identification of the `lp`/`nl` locals with that
list's data pointer and length. -/

/-- Generic guard-threading while-loop runner for `PtxRelRunStrong`: the
body obligation additionally receives the guard fact that the condition
evaluated to a nonzero word. -/
theorem p4Run_while_guard {F : Type} {entry : PanSemStateFiniteExact 64 F}
    (cond : ExpHOL 64) (body rest : ProgHOL 64)
    (INV : PanSemStateFiniteExact 64 F → Prop)
    (hnb : InitECandidate.Solver.GuestUniformClockBound.noTopBreak body = true)
    (hnc : InitECandidate.Solver.PanRunBounded.noTopContinue body = true)
    (hexit : ∀ t, INV t → evalAt t cond = some (.val (.word 0#64)) →
      PtxRelRunStrong entry rest t)
    (hbody : ∀ t, INV t →
      (∃ w : BitVec 64, evalAt t cond = some (.val (.word w)) ∧ w ≠ 0#64) →
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
            · -- run the body at the decremented clock, with the guard fact
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
              exact hbody st hINVst ⟨w, hc, hw⟩
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

/-- The loop-31 guard conversion: if the condition `i < nl` evaluates to a
nonzero word at a state satisfying the invariant's index bound and length
bound, then `i < nl` (as naturals).  The comparison is signed, but `i ≤ nl`
and `nl < 2^28` keep both words nonnegative, where signed and unsigned
order coincide. -/
theorem p4Loop31_guard_lt {F : Type} {u : PanSemStateFiniteExact 64 F}
    {i_w nl_w : BitVec 64}
    (hi : u.locals.lookup (ofString "i") = some (.val (.word i_w)))
    (hnl : u.locals.lookup (ofString "nl") = some (.val (.word nl_w)))
    (hile : i_w.toNat ≤ nl_w.toNat) (hnl28 : nl_w.toNat < 2 ^ 28)
    (w : BitVec 64) (hw : w ≠ 0#64)
    (hc : evalAt u p4Loop31Cond = some (.val (.word w))) :
    i_w.toNat < nl_w.toNat := by
  obtain ⟨a, b, ha, hb, hwif⟩ := evalAt_cmp u .less
    (.var .local (ofString "i")) (.var .local (ofString "nl")) w hc
  have ha' : evalAt u (.var .local (ofString "i")) = some (.val (.word i_w)) := by
    simp [evalAt, evalHOLExact, hi]
  have hb' : evalAt u (.var .local (ofString "nl")) = some (.val (.word nl_w)) := by
    simp [evalAt, evalHOLExact, hnl]
  have hp1 : some ((.val (.word a) : ValueHOL 64)) = some (.val (.word i_w)) := ha.symm.trans ha'
  have hp2 : some ((.val (.word b) : ValueHOL 64)) = some (.val (.word nl_w)) := hb.symm.trans hb'
  simp only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hp1 hp2
  rw [hp1, hp2] at hwif
  have h2 : (2 ^ 28 : Nat) < 2 ^ 63 := by decide
  by_cases hcmp : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .less i_w nl_w = true
  · unfold Flapjack.Compiler.Encoders.Asm.wordCmpHOL at hcmp
    simp only at hcmp
    simp only [Flapjack.Compiler.Encoders.Asm.holAsmSignedLess] at hcmp
    split at hcmp
    · split at hcmp
      · simpa using hcmp
      · omega
    · omega
  · exfalso
    rw [if_neg hcmp] at hwif
    exact hw hwif

/-- The full loop-31 invariant: the Phase-4H invariant plus the `TxEnv`, the
nonvacuousness of the `out+16` log list, and the identification of the `lp`
and `nl` locals with that list's data pointer and length. -/
structure P4Loop31Full {F : Type}
    (entry s s_pmc : PanSemStateFiniteExact 64 F) (w_out : BitVec 64) : Prop where
  base : P4Loop31 entry s s_pmc w_out
  txenv : TxEnv s
  logs_nz : memW s (w_out.toNat + 16) ≠ 0
  lp_nl : ∃ lp_w nl_w : BitVec 64,
    s.locals.lookup (ofString "lp") = some (.val (.word lp_w)) ∧
    s.locals.lookup (ofString "nl") = some (.val (.word nl_w)) ∧
    lp_w.toNat = memW s (memW s (w_out.toNat + 16)) ∧
    nl_w.toNat = memW s (memW s (w_out.toNat + 16) + 8)

/-! ## The out-list cell preservation

The `out+16` log-list header and its data-pointer/length cells survive both
the `lst_push` callee (they are allocated and disjoint from the pushed list
header, so they miss the callee's write set) and the single-cell slot store
(the stored slot lies in the bo+40 backing array, disjoint from both the out
object and the out-list header). -/

/-- Every memory word is below `2^64`. -/
theorem p4Loop31_memW_lt {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) :
    memW s a < 2 ^ 64 := by
  unfold memW
  split
  exact BitVec.isLt _

/-- A word cell inside a container that is disjoint from the stored cell is
not the stored address. -/
theorem p4Loop31_cellMiss {k : Nat} {x : BitVec 64} {c : Ivl}
    (hd : Disj c (x.toNat, 8)) (hkin : c.1 ≤ k ∧ k + 8 ≤ c.1 + c.2)
    (hk64 : k < 2 ^ 64) : BitVec.ofNat 64 k ≠ x := by
  intro heq
  have htonat := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at htonat
  rcases hd with h0 | h0 | h1 | h1 <;> omega

/-- The loop-31 out-list header cells survive the `lst_push` callee: the out
object and the out-list header are allocated and disjoint from every owned
object (in particular from the pushed list header `(w_l, 24)`), so all three
cells miss the callee's write set. -/
theorem p4Loop31_outListPres {F : Type}
    {u post : PanSemStateFiniteExact 64 F} {w_out w_l : BitVec 64}
    {S Nd : List Nat} (hAR : ArenaReady u) (hE : TxEnv u) (hWT : WorldTypedWith u S Nd)
    (hout_disj : ∀ o ∈ worldOwned u S Nd, Disj (w_out.toNat, 96) o)
    (hout_inside : Inside (w_out.toNat, 96) sourceBase (globN u "heap_ptr"))
    (hLok : LogsListOK u (memW u (w_out.toNat + 16)))
    (hPmc : PmcLogsLiveOwned u S Nd (memW u (w_out.toNat + 16)))
    (hL_nz : memW u (w_out.toNat + 16) ≠ 0)
    (hl40 : w_l.toNat = memW u (globN u "bo" + 40))
    (hmem : ∀ a : BitVec 64, ¬ CellHits a.toNat (w_l.toNat, 24) →
      ¬ CellHits a.toNat (InitECandidate.Solver.Wave8Contracts.M08.heapFree u) →
      post.memory a = u.memory a) :
    memW post (w_out.toNat + 16) = memW u (w_out.toNat + 16) ∧
    memW post (memW u (w_out.toNat + 16)) = memW u (memW u (w_out.toNat + 16)) ∧
    memW post (memW u (w_out.toNat + 16) + 8) = memW u (memW u (w_out.toNat + 16) + 8) := by
  obtain ⟨hc40, hc72, hbo_eq⟩ := blockOutObjects_eq_list hE hWT.1
  have hbo_len : (blockOutObjects u).length = 7 := by rw [hbo_eq]; rfl
  have hget3 : (blockOutObjects u)[3] = (w_l.toNat, 24) := by
    rw [hl40]; simp [hbo_eq]
  have he3_mem : (w_l.toNat, 24) ∈ blockOutObjects u :=
    hget3 ▸ List.getElem_mem (by rw [hbo_len]; decide)
  have he3_fix : (w_l.toNat, 24) ∈ fixedObjects u := by
    unfold fixedObjects
    apply List.mem_append_left
    apply List.mem_append_right
    exact he3_mem
  have he3_own : (w_l.toNat, 24) ∈ worldOwned u S Nd := by
    unfold worldOwned
    apply List.mem_append_left
    apply List.mem_append_right
    exact he3_fix
  have hL_alloc : Allocated u (memW u (w_out.toNat + 16), 24) := by
    rcases hLok with h0 | hLok'
    · exact absurd h0 hL_nz
    · exact hLok'.2.1
  have hIvls : IvlsDisj [(memW u (w_out.toNat + 16), 24),
      (memW u (memW u (w_out.toNat + 16)), 8 * memW u (memW u (w_out.toNat + 16) + 8))]
      (worldOwned u S Nd) := (hPmc hL_nz).2.1
  have hL_disj_wl : Disj (memW u (w_out.toNat + 16), 24) (w_l.toNat, 24) :=
    hIvls _ (by simp) _ he3_own
  have hout_disj_wl : Disj (w_out.toNat, 96) (w_l.toNat, 24) := hout_disj _ he3_own
  have hout_alloc : Allocated u (w_out.toNat, 96) := Or.inl hout_inside
  have hout_hi := (ivl_allocated_bound hAR.2 hout_alloc).2
  have hkin_out : w_out.toNat ≤ w_out.toNat + 16 ∧
      w_out.toNat + 16 + 8 ≤ w_out.toNat + 96 := ⟨Nat.le_add_right _ 16, by omega⟩
  have hkin_L : memW u (w_out.toNat + 16) ≤ memW u (w_out.toNat + 16) ∧
      memW u (w_out.toNat + 16) + 8 ≤ memW u (w_out.toNat + 16) + 24 :=
    ⟨Nat.le_refl _, by omega⟩
  have hkin_L8 : memW u (w_out.toNat + 16) ≤ memW u (w_out.toNat + 16) + 8 ∧
      memW u (w_out.toNat + 16) + 8 + 8 ≤ memW u (w_out.toNat + 16) + 24 :=
    ⟨Nat.le_add_right _ 8, by omega⟩
  have hL_hi := (ivl_allocated_bound hAR.2 hL_alloc).2
  have hL_lt : memW u (w_out.toNat + 16) < 2 ^ 64 := p4Loop31_memW_lt u _
  have hL8_lt : memW u (w_out.toNat + 16) + 8 < 2 ^ 64 := by omega
  have hout16_lt : w_out.toNat + 16 < 2 ^ 64 := by omega
  refine ⟨?_, ?_, ?_⟩
  · exact p4Loop31_memW_of_miss hmem hout16_lt
      (p4Loop31_noHit hkin_out (by simp) hout_disj_wl)
      (p4Loop31_noFreeHit hAR.2 hout_alloc hkin_out)
  · exact p4Loop31_memW_of_miss hmem hL_lt
      (p4Loop31_noHit hkin_L (by simp) hL_disj_wl)
      (p4Loop31_noFreeHit hAR.2 hL_alloc hkin_L)
  · exact p4Loop31_memW_of_miss hmem hL8_lt
      (p4Loop31_noHit hkin_L8 (by simp) hL_disj_wl)
      (p4Loop31_noFreeHit hAR.2 hL_alloc hkin_L8)

/-- The out-list header cells miss the single-cell slot store: the stored
slot `w` lies inside the bo+40 backing array, which is owned at the stored
state and disjoint from both the out object and the out-list header. -/
theorem p4Loop31_outListStoreMiss {F : Type}
    {s : PanSemStateFiniteExact 64 F} {w w_out : BitVec 64}
    {S Nd : List Nat} (hA : ArenaOK s) (hE : TxEnv s) (hWT : WorldTypedWith s S Nd)
    (hout_disj : ∀ o ∈ worldOwned s S Nd, Disj (w_out.toNat, 96) o)
    (hout_inside : Inside (w_out.toNat, 96) sourceBase (globN s "heap_ptr"))
    (hPmc : PmcLogsLiveOwned s S Nd (memW s (w_out.toNat + 16)))
    (hLok : LogsListOK s (memW s (w_out.toNat + 16)))
    (hL_nz : memW s (w_out.toNat + 16) ≠ 0)
    (hdata_nz : memW s (memW s (globN s "bo" + 40)) ≠ 0)
    (hin : Inside (w.toNat, 8) (memW s (memW s (globN s "bo" + 40)))
      (memW s (memW s (globN s "bo" + 40)) + 8 *
        memW s (memW s (globN s "bo" + 40) + 16))) :
    BitVec.ofNat 64 (w_out.toNat + 16) ≠ w ∧
    BitVec.ofNat 64 (memW s (w_out.toNat + 16)) ≠ w ∧
    BitVec.ofNat 64 (memW s (w_out.toNat + 16) + 8) ≠ w := by
  have harr_mem : (memW s (memW s (globN s "bo" + 40)),
      8 * memW s (memW s (globN s "bo" + 40) + 16)) ∈ blockOutObjects s :=
    (p4Loop31_arrFacts hE hWT.1 rfl hdata_nz).1
  have harr_fix : (memW s (memW s (globN s "bo" + 40)),
      8 * memW s (memW s (globN s "bo" + 40) + 16)) ∈ fixedObjects s := by
    unfold fixedObjects
    apply List.mem_append_left
    apply List.mem_append_right
    exact harr_mem
  have harr_own : (memW s (memW s (globN s "bo" + 40)),
      8 * memW s (memW s (globN s "bo" + 40) + 16)) ∈ worldOwned s S Nd := by
    unfold worldOwned
    apply List.mem_append_left
    apply List.mem_append_right
    exact harr_fix
  have hL_disj_arr : Disj (memW s (w_out.toNat + 16), 24)
      (memW s (memW s (globN s "bo" + 40)),
        8 * memW s (memW s (globN s "bo" + 40) + 16)) :=
    (hPmc hL_nz).2.1 _ (by simp) _ harr_own
  have hout_disj_arr : Disj (w_out.toNat, 96)
      (memW s (memW s (globN s "bo" + 40)),
        8 * memW s (memW s (globN s "bo" + 40) + 16)) :=
    hout_disj _ harr_own
  have hd_out : Disj (w_out.toNat, 96) (w.toNat, 8) :=
    disj_of_inside_right hin hout_disj_arr
  have hd_L : Disj (memW s (w_out.toNat + 16), 24) (w.toNat, 8) :=
    disj_of_inside_right hin hL_disj_arr
  have hout_alloc : Allocated s (w_out.toNat, 96) := Or.inl hout_inside
  have hout_hi := (ivl_allocated_bound hA hout_alloc).2
  have hL_alloc : Allocated s (memW s (w_out.toNat + 16), 24) := by
    rcases hLok with h0 | hLok'
    · exact absurd h0 hL_nz
    · exact hLok'.2.1
  have hL_hi := (ivl_allocated_bound hA hL_alloc).2
  have hout16_lt : w_out.toNat + 16 < 2 ^ 64 := by omega
  have hL_lt : memW s (w_out.toNat + 16) < 2 ^ 64 := p4Loop31_memW_lt s _
  have hL8_lt : memW s (w_out.toNat + 16) + 8 < 2 ^ 64 := by omega
  have hkin_out : w_out.toNat ≤ w_out.toNat + 16 ∧
      w_out.toNat + 16 + 8 ≤ w_out.toNat + 96 := ⟨Nat.le_add_right _ 16, by omega⟩
  have hkin_L : memW s (w_out.toNat + 16) ≤ memW s (w_out.toNat + 16) ∧
      memW s (w_out.toNat + 16) + 8 ≤ memW s (w_out.toNat + 16) + 24 :=
    ⟨Nat.le_refl _, by omega⟩
  have hkin_L8 : memW s (w_out.toNat + 16) ≤ memW s (w_out.toNat + 16) + 8 ∧
      memW s (w_out.toNat + 16) + 8 + 8 ≤ memW s (w_out.toNat + 16) + 24 :=
    ⟨Nat.le_add_right _ 8, by omega⟩
  exact ⟨p4Loop31_cellMiss hd_out hkin_out hout16_lt,
    p4Loop31_cellMiss hd_L hkin_L hL_lt,
    p4Loop31_cellMiss hd_L hkin_L8 hL8_lt⟩

/-! ## The run side: the loop-31 body at a full-invariant state -/

/-- The loop-31 body run: at a state satisfying the full loop-31 invariant
(with the loop guard `i < nl` holding), the body instruction satisfies
`PtxRelRunStrong`: the entry-anchored base is transported through the
callee, the slot-setVar and the single-cell slot store via
`p4Loop31_baseStored`, and the terminal WorldStep is the bare `i`-assign.
The source cell (the log entry at `lp + 8*i`) is read from the out-list via
`LogsListOK`, surviving the callee by the out-list data array's
disjointness from the callee's write set. -/
theorem p4Loop31_bodyRun {F : Type}
    {entry u s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (hINV : P4Loop31Full entry u s_pmc w_out)
    (hi_lt : locN u "i" < locN u "nl")
    (hcode : u.code = originalRuntimeCode) :
    PtxRelRunStrong entry p4Loop31Body u := by
  obtain ⟨hbase31, htxenv, hlogs_nz, hlpnl⟩ := hINV
  obtain ⟨hdata, hi_word, hnl_word, hlp_word, hile, hnl28, hlenb31⟩ := hbase31
  obtain ⟨i_w, hi⟩ := hi_word
  obtain ⟨lp_w, nl_w, hlp, hnl, hlpw, hnlw⟩ := hlpnl
  have hARu : ArenaReady u := hdata.base.world.1
  obtain ⟨⟨_, hbo_nz_e, hbo24_nz_e, hbo32_nz_e, hidx_lt_e⟩, _, hbo40_nz_e, hbo72_nz_e,
    S_e, Nd_e, hWT_e, _⟩ := hdata.base.ready_entry
  have hD_e : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e Nd_e) := by
    rw [ptxRegions_eq_bufRegions]
    exact validBufList_disj validBufList_ptxBufs hWT_e
  obtain ⟨logs, hll, hl_ok, hl_dj, hty⟩ := hdata.logs_facts
  obtain ⟨S_pmc, Nd_pmc, S_cur, Nd_cur, hty1, hty2, hWT_s, hty4, hty5, hty6, hty7, hty8, hty9⟩ :=
    hty S_e Nd_e hWT_e hD_e
  have hw_l_nat : (BitVec.ofNat 64 (memW u (globN u "bo" + 40))).toNat =
      memW u (globN u "bo" + 40) := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (p4Loop31_memW_lt u _)
  have harg := p4Loop31_harg hARu hWT_s htxenv hw_l_nat
  have hlist_nz : memW u (BitVec.ofNat 64 (memW u (globN u "bo" + 40))).toNat ≠ 0 := by
    rw [hw_l_nat]; exact hdata.base.log_backing
  have hidx : locN u "index" = locN entry "index" := by
    have hlu := hdata.idx_local
    simp only [locN, hlu]
  refine p4Run_loop31Engine hdata.base hcode _ (Or.inl hw_l_nat) hlist_nz harg ?_
  intro w post_c hmem hpush hstep0 hcode_post
  obtain ⟨-, hin, -, hslot, -⟩ := hpush
  obtain ⟨hsp, hfmp, hbo_eq, hhp, hARpost⟩ := p4Loop31_calleeGlobals hstep0
  have hstep := p4Loop31_calleeStepAtU hstep0
  have hjcap_eq : globN post_c "journal_cap" = globN u "journal_cap" :=
    globN_eq_of_lookup (hstep.2.2.1 (ofString "journal_cap")
      (by decide : ofString "journal_cap" ∉ ["heap_ptr"].map ofString))
  obtain ⟨hbo_pres, ⟨hl72_head, hl72_len⟩, hslice_pres⟩ :=
    p4Loop31_calleeCellsUnhit hARu htxenv hWT_s hidx hw_l_nat hmem
  have hmad : post_c.memaddrs = u.memaddrs := by
    rw [hARpost.1.memaddrs, hARu.1.memaddrs]
  -- the slot state and its transports
  set s₀ : PanSemStateFiniteExact 64 F :=
    setVarHOLFinite (ofString "slot") (.val (.word w)) {post_c with locals := u.locals} with hs₀
  have hARs₀ : ArenaReady s₀ := by
    rw [hs₀]
    exact localsFree_arenaReady post_c
      (u.locals.update (ofString "slot", (.val (.word w) : ValueHOL 64))) post_c.clock hARpost
  have hEslot : TxEnv s₀ := by
    rw [hs₀]
    exact p4Loop31_txEnvSlot htxenv hbo_eq hjcap_eq hbo_pres
  rw [hw_l_nat] at hin
  have hin₀ : Inside (w.toNat, 8) (memW s₀ (memW s₀ (globN s₀ "bo" + 40)))
      (memW s₀ (memW s₀ (globN s₀ "bo" + 40))
        + 8 * memW s₀ (memW s₀ (globN s₀ "bo" + 40) + 16)) := by
    have hl₀ : memW s₀ (globN s₀ "bo" + 40) = memW u (globN u "bo" + 40) := by
      show memW post_c (globN post_c "bo" + 40) = memW u (globN u "bo" + 40)
      rw [hbo_eq, hbo_pres 40 (by decide)]
    rw [hl₀]
    exact hin
  have hientry : locN entry "index" < memW s₀ (globN s₀ "bo" + 80) := by
    have h80 : memW s₀ (globN s₀ "bo" + 80) = memW u (globN u "bo" + 80) := by
      show memW post_c (globN post_c "bo" + 80) = memW u (globN u "bo" + 80)
      rw [hbo_eq, hbo_pres 80 (by decide)]
    rw [h80]
    have hidx_lt := htxenv.idx_lt
    have hidx' := hidx
    omega
  -- the out-list data array: allocated, disjoint from the pushed header
  have hL_alloc : Allocated u (memW u (memW u (w_out.toNat + 16)),
      8 * memW u (memW u (w_out.toNat + 16) + 8)) := (hty8 hlogs_nz).1
  have harr_hi : memW u (memW u (w_out.toNat + 16)) +
      8 * memW u (memW u (w_out.toNat + 16) + 8) ≤ 2 ^ 64 :=
    (ivl_allocated_bound hARu.2 hL_alloc).2
  have hi_lt' : i_w.toNat < nl_w.toNat := by
    have h1 : locN u "i" = i_w.toNat := by simp [locN, hi]
    have h2 : locN u "nl" = nl_w.toNat := by simp [locN, hnl]
    rw [h1, h2] at hi_lt
    exact hi_lt
  have hdata_disj : Disj (memW u (memW u (w_out.toNat + 16)),
      8 * memW u (memW u (w_out.toNat + 16) + 8)) (memW u (globN u "bo" + 40), 24) := by
    obtain ⟨hc40, hc72, hbo_eq'⟩ := blockOutObjects_eq_list htxenv hWT_s.1
    have hbo_len : (blockOutObjects u).length = 7 := by rw [hbo_eq']; rfl
    have hget3 : (blockOutObjects u)[3] = (memW u (globN u "bo" + 40), 24) := by
      simp [hbo_eq']
    have he3_mem : (memW u (globN u "bo" + 40), 24) ∈ blockOutObjects u :=
      hget3 ▸ List.getElem_mem (by rw [hbo_len]; decide)
    have he3_fix : (memW u (globN u "bo" + 40), 24) ∈ fixedObjects u := by
      unfold fixedObjects
      apply List.mem_append_left
      apply List.mem_append_right
      exact he3_mem
    have he3_own : (memW u (globN u "bo" + 40), 24) ∈ worldOwned u S_cur Nd_cur := by
      unfold worldOwned
      apply List.mem_append_left
      apply List.mem_append_right
      exact he3_fix
    exact (hty8 hlogs_nz).2.1 _ (by simp) _ he3_own
  -- the source cell: the out-list's i-th entry word, surviving the callee
  have hLok : LogsListOK u (memW u (w_out.toNat + 16)) := hdata.logs_ok
  obtain ⟨v_src, hdom_src_u, hcell_src_u⟩ :
      WordAt u (memW u (memW u (w_out.toNat + 16)) + 8 * i_w.toNat) := by
    rcases hLok with h0 | hLok'
    · exact absurd h0 hlogs_nz
    · exact (hLok'.2.2.2.2 i_w.toNat (by rw [← hnlw]; exact hi_lt')).1
  have hk64_src : lp_w.toNat + 8 * i_w.toNat < 2 ^ 64 := by
    have hlp := hlpw
    have hlenL := hnlw
    omega
  have hmul8 : (i_w * 0x0000000000000008#64 : BitVec 64).toNat = i_w.toNat * 8 := by
    have h8 : (0x0000000000000008#64 : BitVec 64).toNat = 8 := rfl
    rw [BitVec.toNat_mul, h8, Nat.mod_eq_of_lt (by omega)]
  have haddr : (lp_w + i_w * 0x0000000000000008#64 : BitVec 64).toNat =
      lp_w.toNat + 8 * i_w.toNat := by
    rw [BitVec.toNat_add, hmul8, Nat.mod_eq_of_lt (by omega)]
    omega
  have hround : (BitVec.ofNat 64 (lp_w.toNat + 8 * i_w.toNat)) =
      lp_w + i_w * 0x0000000000000008#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, haddr]
    exact Nat.mod_eq_of_lt hk64_src
  have hkin_src : memW u (memW u (w_out.toNat + 16)) ≤ lp_w.toNat + 8 * i_w.toNat ∧
      lp_w.toNat + 8 * i_w.toNat + 8 ≤
        memW u (memW u (w_out.toNat + 16)) +
          8 * memW u (memW u (w_out.toNat + 16) + 8) := by
    have hlp := hlpw
    have hlenL := hnlw
    omega
  have hmiss_src : ¬ CellHits (lp_w + i_w * 0x0000000000000008#64).toNat
      (memW u (globN u "bo" + 40), 24) ∧
      ¬ CellHits (lp_w + i_w * 0x0000000000000008#64).toNat
        (InitECandidate.Solver.Wave8Contracts.M08.heapFree u) := by
    constructor
    · rw [haddr]
      exact p4Loop31_noHit hkin_src (by simp) hdata_disj
    · rw [haddr]
      exact p4Loop31_noFreeHit hARu.2 hL_alloc hkin_src
  -- the hWSA bundle
  refine p4Run_loop31_hC (fun a v mem' v' hdst hsrc hmem' hev' => ?_)
  have haw : w = a := by
    have hslotval := p4Loop31_slotEval (u := u) (post := post_c) (w := w)
    have hchain := hslotval.symm.trans hdst
    simp only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hchain
    exact hchain
  subst haw
  have hmiss1 : ¬ CellHits (lp_w + i_w * 0x0000000000000008#64).toNat
      ((BitVec.ofNat 64 (memW u (globN u "bo" + 40))).toNat, 24) := by
    rw [hw_l_nat]
    exact hmiss_src.1
  have hcell_src : post_c.memory (lp_w + i_w * 0x0000000000000008#64) = .word v_src := by
    rw [hmem (lp_w + i_w * 0x0000000000000008#64) hmiss1 hmiss_src.2]
    rw [← hround, hlpw]
    exact hcell_src_u
  have hdom_src : post_c.memaddrs (lp_w + i_w * 0x0000000000000008#64) := by
    rw [hmad, ← hround, hlpw]
    exact hdom_src_u
  have hvform : v = .val (.word v_src) := by
    have hsrc' := p4Loop31_srcEval (u := u) (post := post_c) (w := w) (lp_w := lp_w)
      (i_w := i_w) (v_src := v_src) hlp hi hdom_src hcell_src
    have hchain := hsrc'.symm.trans hsrc
    simp only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hchain
    exact hchain.symm
  subst hvform
  have hflat : flattenHOL (.val (.word v_src) : ValueHOL 64) = [HolWordLab.word v_src] := by
    simp [flattenHOL]
  rw [hflat] at hmem'
  obtain ⟨hdom, hmemform⟩ := p4Loop31_storeWordEff hmem'
  have hmem'pw : ∀ x, x ≠ w → mem' x = s₀.memory x := by
    intro x hx
    rw [hmemform]
    simp [hx]
    rfl
  -- the arena/typing/miss facts for the store
  have hw_ge : sourceBase ≤ w.toNat := p4Loop31_storeWArg hARs₀ hdom
  have hdata_nz₀ : memW s₀ (memW s₀ (globN s₀ "bo" + 40)) ≠ 0 := by
    show memW post_c (memW post_c (globN post_c "bo" + 40)) ≠ 0
    rw [hbo_eq, hbo_pres 40 (by decide)]
    have hsl : w.toNat = memW post_c (memW u (globN u "bo" + 40)) +
        8 * memW u (memW u (globN u "bo" + 40) + 8) := by
      have h := hslot
      rw [hw_l_nat] at h
      exact h
    have hwg := hw_ge
    have hlenb := hlenb31
    have hil := hile
    omega
  have hlenb_direct : 8 * memW u ((BitVec.ofNat 64 (memW u (globN u "bo" + 40))).toNat + 8)
      < sourceBase := by
    rw [hw_l_nat]
    have hlenb := hlenb31
    have hil := hile
    omega
  have hcells := p4Loop31_hcells hdata.base hbo_eq hw_l_nat hslot hw_ge hlenb_direct
    hbo_pres hl72_head hl72_len hslice_pres
  have hb1 := p4Loop31_baseTransport hdata.base hstep0 hsp hfmp hcells
  have hb0 : PtxRelBase true entry s₀ := by
    rw [hs₀]
    exact ptxRelBase_with_locals hb1
      (u.locals.update (ofString "slot", (.val (.word w) : ValueHOL 64))) post_c.clock
  obtain ⟨S', Nd', hsub', hWT', hOG', hFO', -⟩ :=
    hstep.2.2.2.2 S_cur Nd_cur hWT_s (by intro i hi; simp [bufRegions] at hi)
  have hWTs₀ : WorldTypedWith s₀ S' Nd' := by
    rw [hs₀]
    exact (worldTypedWith_with_locals post_c
      (u.locals.update (ofString "slot", (.val (.word w) : ValueHOL 64))) post_c.clock
      S' Nd').2 hWT'
  obtain ⟨hmiss_bo, hmiss_mid, hmiss_slices⟩ :=
    p4Loop31_storeMisses hARs₀ hEslot hWTs₀ rfl hdata_nz₀ hientry hin₀
  obtain ⟨hmiss_l72p, hmiss_l72len, hmiss_l40⟩ := hmiss_mid
  have hcells2 := p4Loop31_hcellsStore hb0 hmem'pw hmiss_bo hmiss_l72p hmiss_l72len hmiss_l40
    hmiss_slices
  have hARs : ArenaReady {s₀ with memory := mem'} := p4Loop31_arenaStored hARs₀
  have hty₀ := p4Loop31_hty hARs₀ hEslot rfl hdata_nz₀ hin₀ hdom hmem'pw
  have hrecStd := p4Loop31_hrecStd hARs₀ hEslot hWTs₀ rfl hdata_nz₀ hin₀ hmem'pw
  have hbase' := p4Loop31_baseStored hdata.base hstep0 hsp hfmp hcells hARs hmem'pw
    (fun S Nd hWT hD => hty₀ S Nd hWT) hrecStd hcells2
  exact p4Loop31_terminalWorldStep (B := ([] : BufList)) hbase'
    (by intro p hp; cases hp) (by intro p hp; cases hp) hARs v'

/-! ## The post-invariant (L1): reconstructing the full invariant at the
body's post-state -/

/-- The pushed slot `w` cannot coincide with the pushed list's length cell
`L+8`: the bo+40 header `(L,24)` and the bo+40 backing array are distinct
`blockOutObjects` members (pairwise disjoint), and `w` lies inside the
backing array. -/
theorem p4Loop31_pushLenCellMiss {F : Type}
    {s : PanSemStateFiniteExact 64 F} {w : BitVec 64} {S Nd : List Nat}
    (hAR : ArenaReady s) (hE : TxEnv s) (hWT : WorldTypedWith s S Nd)
    (hdata_nz : memW s (memW s (globN s "bo" + 40)) ≠ 0)
    (hin : Inside (w.toNat, 8) (memW s (memW s (globN s "bo" + 40)))
      (memW s (memW s (globN s "bo" + 40))
        + 8 * memW s (memW s (globN s "bo" + 40) + 16))) :
    BitVec.ofNat 64 (memW s (globN s "bo" + 40) + 8) ≠ w := by
  obtain ⟨_, hpw, _, _, _⟩ := fixedObjects_disj_parts hWT.2.2.1
  obtain ⟨hc40, _, hbo_eq⟩ := blockOutObjects_eq_list hE hWT.1
  have hbo_len : (blockOutObjects s).length = 7 := by rw [hbo_eq]; rfl
  have hcap : 1 ≤ memW s (memW s (globN s "bo" + 40) + 16) := by
    rcases hin with ⟨h1, h2⟩
    omega
  have hlen_nz : 8 * memW s (memW s (globN s "bo" + 40) + 16) ≠ 0 := by omega
  have hget3 : (blockOutObjects s)[3] = (memW s (globN s "bo" + 40), 24) := by
    simp [hbo_eq]
  have hget4 : (blockOutObjects s)[4] =
      (memW s (memW s (globN s "bo" + 40)),
        8 * memW s (memW s (globN s "bo" + 40) + 16)) := by
    simp [hbo_eq, hE.bo_nz, hdata_nz, hlen_nz]
  have hd := List.pairwise_iff_getElem.1 hpw 3 4 (by omega) (by omega) (by omega)
  rw [hget3, hget4] at hd
  have hd' : Disj (memW s (globN s "bo" + 40), 24) (w.toNat, 8) :=
    disj_of_inside_right hin hd
  have hmem3 : (memW s (globN s "bo" + 40), 24) ∈ blockOutObjects s := by
    simp [blockOutObjects, hE.bo_nz, hE.bo40]
  have hfix3 : (memW s (globN s "bo" + 40), 24) ∈ fixedObjects s := by
    unfold fixedObjects
    apply List.mem_append_left
    apply List.mem_append_right
    exact hmem3
  have hk64 : memW s (globN s "bo" + 40) + 8 < 2 ^ 64 := by
    rcases hWT.2.2.1.1 _ hfix3 with h0 | ⟨hal3, _⟩
    · simp at h0
    · have hhi3 := (ivl_allocated_bound hAR.2 hal3).2
      omega
  exact p4Loop31_cellMiss hd' ⟨Nat.le_add_right _ 8, by omega⟩ hk64

/-- The loop-31 post-invariant (L1): if the body instruction evaluates to
`(none, post)` at a full-invariant state `u` (with the loop guard holding),
then the full invariant holds at `post`, the code is preserved and the
caller's clock was positive.  The proof decomposes the evaluation through
the decCall/store/assign equations, replays the `lst_push` callee spec for
the memory effects, and transports `P4Data` through the callee step, the
`slot`-setVar, the single-cell store and the `i`-setVar. -/
theorem p4Loop31_postInvariant {F : Type}
    {entry u s_pmc post : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (hINV : P4Loop31Full entry u s_pmc w_out)
    (hi_lt : locN u "i" < locN u "nl")
    (hcode : u.code = originalRuntimeCode)
    (heq : evaluateHOLFiniteState u p4Loop31Body = (none, post)) :
    P4Loop31Full entry post s_pmc w_out ∧
    post.code = originalRuntimeCode ∧ u.clock ≠ 0 := by
  obtain ⟨hbase31, htxenv, hlogs_nz, hlpnl⟩ := hINV
  obtain ⟨hdata, hi_word, hnl_word, hlp_word, hile, hnl28, hlenb31⟩ := hbase31
  obtain ⟨i_w, hi⟩ := hi_word
  obtain ⟨lp_w, nl_w, hlp, hnl, hlpw, hnlw⟩ := hlpnl
  have hARu : ArenaReady u := hdata.base.world.1
  obtain ⟨⟨_, hbo_nz_e, hbo24_nz_e, hbo32_nz_e, hidx_lt_e⟩, _, hbo40_nz_e, hbo72_nz_e,
    S_e, Nd_e, hWT_e, _⟩ := hdata.base.ready_entry
  have hD_e : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e Nd_e) := by
    rw [ptxRegions_eq_bufRegions]
    exact validBufList_disj validBufList_ptxBufs hWT_e
  obtain ⟨logs, hll, hl_ok, hl_dj, hty⟩ := hdata.logs_facts
  obtain ⟨S_pmc, Nd_pmc, S_cur, Nd_cur, hty1, hty2, hWT_s, hty4, hty5, hty6, hty7, hty8, hty9⟩ :=
    hty S_e Nd_e hWT_e hD_e
  have hw_l_nat : (BitVec.ofNat 64 (memW u (globN u "bo" + 40))).toNat =
      memW u (globN u "bo" + 40) := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (p4Loop31_memW_lt u _)
  have harg := p4Loop31_harg hARu hWT_s htxenv hw_l_nat
  have hlist_nz : memW u (BitVec.ofNat 64 (memW u (globN u "bo" + 40))).toNat ≠ 0 := by
    rw [hw_l_nat]; exact hdata.base.log_backing
  have hidx : locN u "index" = locN entry "index" := by
    have hlu := hdata.idx_local
    simp only [locN, hlu]
  -- decompose the decCall evaluation (4F pattern, reversed)
  have hdec : evaluateHOLFiniteState u
      (.decCall (ofString "slot") .one (ofString "lst_push") p4Loop31Args p4Loop31C)
      = (none, post) := heq
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hdec
  rw [harg] at hdec
  dsimp only at hdec
  have hlk := pan_two_word_lookup u.code.lookup (ofString "lst_push")
    (ofString "l") (ofString "esz") (sourceFnBody Guest.Software.guestFn_lst_push)
    (BitVec.ofNat 64 (memW u (globN u "bo" + 40))) 8 (by decide)
    (by rw [hcode]; exact R13Shards.lookup_lst_push)
  rw [hlk] at hdec
  dsimp only at hdec
  by_cases hcz : u.clock = 0
  · simp only [hcz, ↓reduceIte] at hdec
    exact absurd hdec (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · simp only [hcz, ↓reduceIte] at hdec
    set cmap := ((HolFiniteMapExact.empty.update
        (ofString "l", (.val (.word (BitVec.ofNat 64 (memW u (globN u "bo" + 40))))
          : ValueHOL 64))).update
        (ofString "esz", (.val (.word 8) : ValueHOL 64))) with hcmap_def
    have hW_ent : WorldOK (callEntryStateHOLFinite u cmap) :=
      PtxP1.worldOK_callEntry hdata.base.world cmap
    have hent_l : (callEntryStateHOLFinite u cmap).locals.lookup (ofString "l") =
        some (.val (.word (BitVec.ofNat 64 (memW u (globN u "bo" + 40))))) := by
      simp [callEntryStateHOLFinite, hcmap_def, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "l" ≠ ofString "esz" by decide,
        show ofString "esz" ≠ ofString "l" by decide]
    have hent_esz : (callEntryStateHOLFinite u cmap).locals.lookup (ofString "esz") =
        some (.val (.word 8)) := by
      simp [callEntryStateHOLFinite, hcmap_def, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "esz" ≠ ofString "l" by decide]
    have hentl : locN (callEntryStateHOLFinite u cmap) "l" =
        (BitVec.ofNat 64 (memW u (globN u "bo" + 40))).toNat := by
      simp [locN, hent_l]
    have hentesz : locN (callEntryStateHOLFinite u cmap) "esz" = 8 := by
      simp [locN, hent_esz]
    have hbo_nz : globN u "bo" ≠ 0 := by
      have hge : globN u "bo" = globN entry "bo" :=
        globN_eq_of_lookup (hdata.base.globals _ (by decide))
      rw [hge]; exact hbo_nz_e
    have hPre_ent : BoListArgStrong (callEntryStateHOLFinite u cmap) :=
      ⟨hW_ent, ⟨hW_ent, hbo_nz, by rw [hentl]; exact Or.inl hw_l_nat, hentesz⟩, by
        rw [hentl]; exact hlist_nz⟩
    have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
      (callEntryStateHOLFinite u cmap) (sourceFnBody Guest.Software.guestFn_lst_push)).1
    rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite u cmap)
        (sourceFnBody Guest.Software.guestFn_lst_push) with ⟨rb, post_c⟩
    have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite u cmap)
        (sourceFnBody Guest.Software.guestFn_lst_push) = (rb, post_c) := hb
    rw [hb] at hmeta
    simp only [hb] at hdec
    cases rb with
    | none => exact absurd hdec (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
    | some cr =>
      cases cr with
      | timeOut | error | «break» | «continue» | finalFfi _ =>
        exact absurd hdec (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
      | exception eid ev =>
        dsimp only at hdec
        exact absurd hdec (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
      | returned v =>
        dsimp only at hdec
        have hspec := wk_lst_push_strong.at_lookup u hcode
          [.val (.word (BitVec.ofNat 64 (memW u (globN u "bo" + 40)))), .val (.word 8)]
          (sourceFnBody Guest.Software.guestFn_lst_push) cmap .one hlk hPre_ent
          (by rw [hb']; simp)
        rw [hb'] at hspec
        have hstep0 := hspec (Or.inl ⟨v, rfl⟩)
        obtain ⟨S_ec, hWT_ec_ex⟩ := hW_ent.2
        obtain ⟨Nd_ec, hWT_ec⟩ :=
          (worldTyped_iff_with (callEntryStateHOLFinite u cmap) S_ec).1 hWT_ec_ex
        obtain ⟨S', Nd', hsub, hWT', hOG, hFO, hQ⟩ :=
          hstep0.2.2.2.2 S_ec Nd_ec hWT_ec (by intro i hi; cases hi)
        obtain ⟨w, hvw, hal, hin, hlen, hslot, hprefix⟩ := hQ.2 v rfl
        rw [hvw] at hstep0 hdec
        have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word w) : ValueHOL 64)) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word w) : ValueHOL 64)) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        simp only [hsh, ↓reduceIte] at hdec
        rw [hentl] at hin hlen hslot
        -- the callee's memory effects at the caller
        have hmem : ∀ a : BitVec 64,
            ¬ CellHits a.toNat ((BitVec.ofNat 64 (memW u (globN u "bo" + 40))).toNat, 24) →
            ¬ CellHits a.toNat (InitECandidate.Solver.Wave8Contracts.M08.heapFree u) →
            post_c.memory a = u.memory a := by
          intro a h1 h2
          refine hQ.1 a (by rw [hentl]; exact h1) h2
        -- callee facts (as in L2)
        obtain ⟨hsp, hfmp, hbo_eq, hhp, hARpost⟩ := p4Loop31_calleeGlobals hstep0
        have hstep := p4Loop31_calleeStepAtU hstep0
        have hjcap_eq : globN post_c "journal_cap" = globN u "journal_cap" :=
          globN_eq_of_lookup (hstep.2.2.1 (ofString "journal_cap")
            (by decide : ofString "journal_cap" ∉ ["heap_ptr"].map ofString))
        obtain ⟨hbo_pres, ⟨hl72_head, hl72_len⟩, hslice_pres⟩ :=
          p4Loop31_calleeCellsUnhit hARu htxenv hWT_s hidx hw_l_nat hmem
        -- the slot state (as in L2)
        set s₀ : PanSemStateFiniteExact 64 F :=
          setVarHOLFinite (ofString "slot") (.val (.word w)) {post_c with locals := u.locals}
          with hs₀
        have hARs₀ : ArenaReady s₀ := by
          rw [hs₀]
          exact localsFree_arenaReady post_c
            (u.locals.update (ofString "slot", (.val (.word w) : ValueHOL 64))) post_c.clock
            hARpost
        have hEslot : TxEnv s₀ := by
          rw [hs₀]
          exact p4Loop31_txEnvSlot htxenv hbo_eq hjcap_eq hbo_pres
        rw [hw_l_nat] at hin
        have hin₀ : Inside (w.toNat, 8) (memW s₀ (memW s₀ (globN s₀ "bo" + 40)))
            (memW s₀ (memW s₀ (globN s₀ "bo" + 40))
              + 8 * memW s₀ (memW s₀ (globN s₀ "bo" + 40) + 16)) := by
          have hl₀ : memW s₀ (globN s₀ "bo" + 40) = memW u (globN u "bo" + 40) := by
            show memW post_c (globN post_c "bo" + 40) = memW u (globN u "bo" + 40)
            rw [hbo_eq, hbo_pres 40 (by decide)]
          rw [hl₀]
          exact hin
        have hientry : locN entry "index" < memW s₀ (globN s₀ "bo" + 80) := by
          have h80 : memW s₀ (globN s₀ "bo" + 80) = memW u (globN u "bo" + 80) := by
            show memW post_c (globN post_c "bo" + 80) = memW u (globN u "bo" + 80)
            rw [hbo_eq, hbo_pres 80 (by decide)]
          rw [h80]
          have hidx_lt := htxenv.idx_lt
          have hidx' := hidx
          omega
        -- the out-list data array (as in L2)
        have hL_alloc : Allocated u (memW u (memW u (w_out.toNat + 16)),
            8 * memW u (memW u (w_out.toNat + 16) + 8)) := (hty8 hlogs_nz).1
        have harr_hi : memW u (memW u (w_out.toNat + 16)) +
            8 * memW u (memW u (w_out.toNat + 16) + 8) ≤ 2 ^ 64 :=
          (ivl_allocated_bound hARu.2 hL_alloc).2
        have hi_lt' : i_w.toNat < nl_w.toNat := by
          have h1 : locN u "i" = i_w.toNat := by simp [locN, hi]
          have h2 : locN u "nl" = nl_w.toNat := by simp [locN, hnl]
          rw [h1, h2] at hi_lt
          exact hi_lt
        have hdata_disj : Disj (memW u (memW u (w_out.toNat + 16)),
            8 * memW u (memW u (w_out.toNat + 16) + 8))
            (memW u (globN u "bo" + 40), 24) := by
          obtain ⟨hc40, hc72, hbo_eq'⟩ := blockOutObjects_eq_list htxenv hWT_s.1
          have hbo_len : (blockOutObjects u).length = 7 := by rw [hbo_eq']; rfl
          have hget3 : (blockOutObjects u)[3] = (memW u (globN u "bo" + 40), 24) := by
            simp [hbo_eq']
          have he3_mem : (memW u (globN u "bo" + 40), 24) ∈ blockOutObjects u :=
            hget3 ▸ List.getElem_mem (by rw [hbo_len]; decide)
          have he3_fix : (memW u (globN u "bo" + 40), 24) ∈ fixedObjects u := by
            unfold fixedObjects
            apply List.mem_append_left
            apply List.mem_append_right
            exact he3_mem
          have he3_own : (memW u (globN u "bo" + 40), 24) ∈ worldOwned u S_cur Nd_cur := by
            unfold worldOwned
            apply List.mem_append_left
            apply List.mem_append_right
            exact he3_fix
          exact (hty8 hlogs_nz).2.1 _ (by simp) _ he3_own
        -- the source cell (as in L2)
        have hLok : LogsListOK u (memW u (w_out.toNat + 16)) := hdata.logs_ok
        obtain ⟨v_src, hdom_src_u, hcell_src_u⟩ :
            WordAt u (memW u (memW u (w_out.toNat + 16)) + 8 * i_w.toNat) := by
          rcases hLok with h0 | hLok'
          · exact absurd h0 hlogs_nz
          · exact (hLok'.2.2.2.2 i_w.toNat (by rw [← hnlw]; exact hi_lt')).1
        have hk64_src : lp_w.toNat + 8 * i_w.toNat < 2 ^ 64 := by
          have hlp := hlpw
          have hlenL := hnlw
          omega
        have hmul8 : (i_w * 0x0000000000000008#64 : BitVec 64).toNat = i_w.toNat * 8 := by
          have h8 : (0x0000000000000008#64 : BitVec 64).toNat = 8 := rfl
          rw [BitVec.toNat_mul, h8, Nat.mod_eq_of_lt (by omega)]
        have haddr : (lp_w + i_w * 0x0000000000000008#64 : BitVec 64).toNat =
            lp_w.toNat + 8 * i_w.toNat := by
          rw [BitVec.toNat_add, hmul8, Nat.mod_eq_of_lt (by omega)]
          omega
        have hround : (BitVec.ofNat 64 (lp_w.toNat + 8 * i_w.toNat)) =
            lp_w + i_w * 0x0000000000000008#64 := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ofNat, haddr]
          exact Nat.mod_eq_of_lt hk64_src
        have hkin_src : memW u (memW u (w_out.toNat + 16)) ≤ lp_w.toNat + 8 * i_w.toNat ∧
            lp_w.toNat + 8 * i_w.toNat + 8 ≤
              memW u (memW u (w_out.toNat + 16)) +
                8 * memW u (memW u (w_out.toNat + 16) + 8) := by
          have hlp := hlpw
          have hlenL := hnlw
          omega
        have hmiss_src : ¬ CellHits (lp_w + i_w * 0x0000000000000008#64).toNat
            (memW u (globN u "bo" + 40), 24) ∧
            ¬ CellHits (lp_w + i_w * 0x0000000000000008#64).toNat
              (InitECandidate.Solver.Wave8Contracts.M08.heapFree u) := by
          constructor
          · rw [haddr]
            exact p4Loop31_noHit hkin_src (by simp) hdata_disj
          · rw [haddr]
            exact p4Loop31_noFreeHit hARu.2 hL_alloc hkin_src
        have hmiss1 : ¬ CellHits (lp_w + i_w * 0x0000000000000008#64).toNat
            ((BitVec.ofNat 64 (memW u (globN u "bo" + 40))).toNat, 24) := by
          rw [hw_l_nat]
          exact hmiss_src.1
        have hcell_src : post_c.memory (lp_w + i_w * 0x0000000000000008#64)
            = .word v_src := by
          rw [hmem (lp_w + i_w * 0x0000000000000008#64) hmiss1 hmiss_src.2]
          rw [← hround, hlpw]
          exact hcell_src_u
        have hdom_src : post_c.memaddrs (lp_w + i_w * 0x0000000000000008#64) := by
          have hmeta' := (PanRunBounded.evaluateHOLFiniteState_metadata
            (callEntryStateHOLFinite u cmap) (sourceFnBody Guest.Software.guestFn_lst_push)).2.1
          rw [hb] at hmeta'
          rw [hmeta']
          rw [← hround, hlpw]
          exact hdom_src_u
        -- decompose the continuation: store slot src; assign i
        unfold p4Loop31C at hdec
        rw [evaluateHOLFiniteState_seq_line780] at hdec
        rcases hst : evaluateHOLFiniteState s₀
            (.store (.var .local (ofString "slot")) p4Loop31Src) with ⟨r1, mid1⟩
        simp only [hst] at hdec
        cases r1 with
        | some r1' =>
          dsimp only at hdec
          exact absurd hdec (by simp)
        | none =>
          dsimp only at hdec
          rw [evaluateHOLFiniteState_store] at hst
          cases hdst : @evalHOLExact 64 F _ s₀.toExact
              (fun address => Classical.propDecidable (s₀.memaddrs address))
              (.var .local (ofString "slot")) with
          | none =>
            simp only [hdst] at hst
            exact absurd hst (by simp)
          | some dv =>
            cases dv with
            | rStruct _ | nStruct _ _ =>
              simp only [hdst] at hst
              exact absurd hst (by simp)
            | val dv' =>
              cases dv' with
              | word a =>
                cases hsrc : @evalHOLExact 64 F _ s₀.toExact
                    (fun address => Classical.propDecidable (s₀.memaddrs address)) p4Loop31Src
                  with
                | none =>
                  simp only [hdst, hsrc] at hst
                  exact absurd hst (by simp)
                | some v0 =>
                  cases hmem' : @panMemStoresHOL 64 _ a (flattenHOL v0) s₀.memaddrs
                      (fun address => Classical.propDecidable (s₀.memaddrs address)) s₀.memory
                    with
                  | none =>
                    simp only [hdst, hsrc, hmem'] at hst
                    exact absurd hst (by simp)
                  | some mem' =>
                    simp only [hdst, hsrc, hmem'] at hst
                    injection hst with _ hmid
                    subst hmid
                    rw [evaluateHOLFiniteState_assign] at hdec
                    cases hev : @evalHOLExact 64 F _
                        ({s₀ with memory := mem'} : PanSemStateFiniteExact 64 F).toExact
                        (fun address => Classical.propDecidable
                          (({s₀ with memory := mem'} : PanSemStateFiniteExact 64 F).memaddrs
                            address)) p4Loop31I with
                    | none =>
                      simp only [hev] at hdec
                      exact absurd hdec (by simp)
                    | some v' =>
                      by_cases hvalid : isValidValueHOLFinite
                          ({s₀ with memory := mem'} : PanSemStateFiniteExact 64 F) .local
                          (ofString "i") v' = true
                      · simp only [hev, hvalid, ↓reduceIte] at hdec
                        injection hdec with _ hpost
                        -- identify the stored and assigned values (as in L2)
                        have haw : w = a := by
                          have hslotval := p4Loop31_slotEval (u := u) (post := post_c) (w := w)
                          have hchain :=
                            hslotval.symm.trans (show evalAt s₀ (.var .local (ofString "slot"))
                              = some (.val (.word a)) from hdst)
                          simp only [Option.some.injEq, ValueHOL.val.injEq,
                            HolWordLab.word.injEq] at hchain
                          exact hchain
                        subst haw
                        have hvform0 : v0 = .val (.word v_src) := by
                          have hsrc' := p4Loop31_srcEval (u := u) (post := post_c) (w := w)
                            (lp_w := lp_w) (i_w := i_w) (v_src := v_src) hlp hi hdom_src
                            hcell_src
                          have hchain := hsrc'.symm.trans
                            (show evalAt s₀ p4Loop31Src = some v0 from hsrc)
                          simp only [Option.some.injEq, ValueHOL.val.injEq,
                            HolWordLab.word.injEq] at hchain
                          exact hchain.symm
                        subst hvform0
                        have hv'form : v' = .val (.word (i_w + 0x0000000000000001#64)) := by
                          have hiv := p4Loop31_iEval (u := u) (post := post_c) (w := w)
                            (i_w := i_w) (mem' := mem') hi
                          have hchain := hiv.symm.trans
                            (show evalAt ({s₀ with memory := mem'} :
                              PanSemStateFiniteExact 64 F) p4Loop31I = some v' from hev)
                          simp only [Option.some.injEq, ValueHOL.val.injEq,
                            HolWordLab.word.injEq] at hchain
                          exact hchain.symm
                        subst hv'form
                        have hpost' : post =
                            { setVarHOLFinite (ofString "i")
                                (.val (.word (i_w + 0x0000000000000001#64)))
                                {s₀ with memory := mem'} with
                              locals := HolFiniteMapExact.resVarEq
                                (setVarHOLFinite (ofString "i")
                                  (.val (.word (i_w + 0x0000000000000001#64)))
                                  {s₀ with memory := mem'}).locals
                                (ofString "slot", u.locals.lookup (ofString "slot")) } :=
                          hpost.symm
                        rw [hpost']
                        set post₂ : PanSemStateFiniteExact 64 F :=
                            { setVarHOLFinite (ofString "i")
                                (.val (.word (i_w + 0x0000000000000001#64)))
                                {s₀ with memory := mem'} with
                              locals := HolFiniteMapExact.resVarEq
                                (setVarHOLFinite (ofString "i")
                                  (.val (.word (i_w + 0x0000000000000001#64)))
                                  {s₀ with memory := mem'}).locals
                                (ofString "slot", u.locals.lookup (ofString "slot")) }
                          with hpost₂
                        -- lookup pass-through helpers at the restored post state
                        have hs0lu : ∀ name : String, ofString name ≠ ofString "slot" →
                            s₀.locals.lookup (ofString name) = u.locals.lookup (ofString name) := by
                          intro name hn
                          rw [hs₀]
                          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                            Ne.symm hn]
                        have hpostlu : ∀ name : String, ofString name ≠ ofString "slot" →
                            ofString name ≠ ofString "i" →
                            post₂.locals.lookup (ofString name)
                              = u.locals.lookup (ofString name) := by
                          intro name hnslot hni
                          rw [hpost₂]
                          rcases hus : u.locals.lookup (ofString "slot") with _ | w_slot <;>
                            simp [hus, FDOMSUB_HOL, FUPDATE_HOL, setVarHOLFinite,
                              HolFiniteMapExact.update, FUPDATE, hs₀, hnslot, hni,
                              Ne.symm hnslot, Ne.symm hni]
                        have hli : post₂.locals.lookup (ofString "i")
                            = some (.val (.word (i_w + 0x0000000000000001#64))) := by
                          rw [hpost₂]
                          rcases hus : u.locals.lookup (ofString "slot") with _ | w_slot <;>
                            simp [hus, FDOMSUB_HOL, FUPDATE_HOL, setVarHOLFinite,
                              HolFiniteMapExact.update, FUPDATE,
                              show ofString "i" ≠ ofString "slot" by decide]
                        -- the store effect (as in L2)
                        have hflat : flattenHOL (.val (.word v_src) : ValueHOL 64)
                            = [HolWordLab.word v_src] := by
                          simp [flattenHOL]
                        rw [hflat] at hmem'
                        obtain ⟨hdom, hmemform⟩ := p4Loop31_storeWordEff hmem'
                        have hmem'pw : ∀ x, x ≠ w → mem' x = s₀.memory x := by
                          intro x hx
                          rw [hmemform]
                          simp [hx]
                        have hw_ge : sourceBase ≤ w.toNat := p4Loop31_storeWArg hARs₀ hdom
                        have hdata_nz₀ : memW s₀ (memW s₀ (globN s₀ "bo" + 40)) ≠ 0 := by
                          show memW post_c (memW post_c (globN post_c "bo" + 40)) ≠ 0
                          rw [hbo_eq, hbo_pres 40 (by decide)]
                          have hsl : w.toNat = memW post_c (memW u (globN u "bo" + 40)) +
                              8 * memW u (memW u (globN u "bo" + 40) + 8) := by
                            have h := hslot
                            rw [hw_l_nat] at h
                            exact h
                          have hwg := hw_ge
                          have hlenb := hlenb31
                          have hil := hile
                          omega
                        have hlenb_direct : 8 * memW u
                            ((BitVec.ofNat 64 (memW u (globN u "bo" + 40))).toNat + 8)
                            < sourceBase := by
                          rw [hw_l_nat]
                          have hlenb := hlenb31
                          have hil := hile
                          omega
                        have hcells := p4Loop31_hcells hdata.base hbo_eq hw_l_nat hslot hw_ge
                          hlenb_direct hbo_pres hl72_head hl72_len hslice_pres
                        have hb1 := p4Loop31_baseTransport hdata.base hstep0 hsp hfmp hcells
                        have hb0 : PtxRelBase true entry s₀ := by
                          rw [hs₀]
                          exact ptxRelBase_with_locals hb1
                            (u.locals.update (ofString "slot", (.val (.word w) : ValueHOL 64)))
                            post_c.clock
                        obtain ⟨S'', Nd'', hsub'', hWT'', hOG'', hFO'', -⟩ :=
                          hstep.2.2.2.2 S_cur Nd_cur hWT_s
                            (by intro i hi; simp [bufRegions] at hi)
                        have hWTs₀ : WorldTypedWith s₀ S'' Nd'' := by
                          rw [hs₀]
                          exact (worldTypedWith_with_locals post_c
                            (u.locals.update (ofString "slot", (.val (.word w) : ValueHOL 64)))
                            post_c.clock S'' Nd'').2 hWT''
                        obtain ⟨hmiss_bo, hmiss_mid, hmiss_slices⟩ :=
                          p4Loop31_storeMisses hARs₀ hEslot hWTs₀ rfl hdata_nz₀ hientry hin₀
                        obtain ⟨hmiss_l72p, hmiss_l72len, hmiss_l40⟩ := hmiss_mid
                        have hcells2 := p4Loop31_hcellsStore hb0 hmem'pw hmiss_bo hmiss_l72p
                          hmiss_l72len hmiss_l40 hmiss_slices
                        have hARs : ArenaReady {s₀ with memory := mem'} :=
                          p4Loop31_arenaStored hARs₀
                        have hty₀ := p4Loop31_hty hARs₀ hEslot rfl hdata_nz₀ hin₀ hdom hmem'pw
                        have hrecStd := p4Loop31_hrecStd hARs₀ hEslot hWTs₀ rfl hdata_nz₀ hin₀
                          hmem'pw
                        -- P4Data transports: callee step, slot-setVar, store, i-setVar
                        have hD1 : P4Data entry
                            {post_c with locals := u.locals, clock := post_c.clock} s_pmc w_out :=
                          p4Data_step_of_worldStep_cells hdata
                            (by intro p hp; cases hp) (by intro p hp; cases hp)
                            (by intro g hg
                                simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
                                subst hg; decide)
                            (by decide) (by decide) ptxKeepSub_stdKeep hstep hsp hcells
                        have hD0 : P4Data entry s₀ s_pmc w_out :=
                          p4Data_setVar (by decide) (by decide) (by decide) (by decide)
                            (by decide) hD1
                        -- the out-list preservation chains
                        have houtpres := p4Loop31_outListPres hARu htxenv hWT_s hty7
                          hdata.out_inside hdata.logs_ok hty8 hlogs_nz hw_l_nat hmem
                        obtain ⟨logs₀, hll₀, hl_ok₀, hl_dj₀, hty₀f⟩ := hD0.logs_facts
                        obtain ⟨S_pmc0, Nd_pmc0, S_cur0, Nd_cur0, hty1₀, hty2₀, hWT_s₀f,
                          hty4₀, hty5₀, hty6₀, hty7₀, hty8₀, hty9₀⟩ :=
                          hty₀f S_e Nd_e hWT_e hD_e
                        have hlogs_nz₀ : memW s₀ (w_out.toNat + 16) ≠ 0 := by
                          show memW post_c (w_out.toNat + 16) ≠ 0
                          rw [houtpres.1]
                          exact hlogs_nz
                        have hmisses_out := p4Loop31_outListStoreMiss hARs₀.2 hEslot
                          hWT_s₀f hty7₀ hD0.out_inside hty8₀ hD0.logs_ok hlogs_nz₀ hdata_nz₀ hin₀
                        have hstep2 : WorldStep (bufRegions ([] : BufList)) [] stdKeep NoExtra
                            s₀ none {s₀ with memory := mem'} :=
                          worldStep_congr_R rfl
                            (p4Loop31_storeWorldStep hARs hmem'pw
                              (fun S Nd hWT _ => hty₀ S Nd hWT) hrecStd)
                        have hD2 : P4Data entry
                            ({ {s₀ with memory := mem'} with
                              locals := s₀.locals,
                              clock := {s₀ with memory := mem'}.clock }) s_pmc w_out :=
                          p4Data_step_of_worldStep_cells hD0
                            (by intro p hp; cases hp) (by intro p hp; cases hp)
                            (by intro g hg; cases hg) (by simp) (by simp) ptxKeepSub_stdKeep
                            hstep2 (le_of_eq rfl) hcells2
                        have hDpost : P4Data entry post₂ s_pmc w_out := by
                          have hD2' := p4Data_with_locals post₂.locals post₂.clock
                            (by rw [hpostlu "out" (by decide) (by decide)]
                                exact hdata.out_local)
                            (by show post₂.locals.lookup (ofString "tx")
                                  = s₀.locals.lookup (ofString "tx")
                                rw [hpostlu "tx" (by decide) (by decide),
                                  hs0lu "tx" (by decide)])
                            (by show post₂.locals.lookup (ofString "index")
                                  = s₀.locals.lookup (ofString "index")
                                rw [hpostlu "index" (by decide) (by decide),
                                  hs0lu "index" (by decide)])
                            (by show post₂.locals.lookup (ofString "logs")
                                  = s₀.locals.lookup (ofString "logs")
                                rw [hpostlu "logs" (by decide) (by decide),
                                  hs0lu "logs" (by decide)])
                            (by
                                refine ⟨?_, ?_, ?_⟩
                                · intro name hn
                                  rcases hdata.shapes.1 name hn with ⟨w', hw'⟩
                                  refine ⟨w', ?_⟩
                                  show post₂.locals.lookup (ofString name)
                                    = some (.val (.word w'))
                                  rw [hpostlu name (by
                                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
                                      rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide)
                                    (by
                                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
                                      rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide)]
                                  exact hw'
                                · show ∃ v, post₂.locals.lookup (ofString "price") = some v ∧
                                      shapeOfHOLExact v = .comb [.one, .one, .one, .one]
                                  rw [hpostlu "price" (by decide) (by decide)]
                                  exact hdata.shapes.2.1
                                · show ∃ v, post₂.locals.lookup (ofString "intrinsic") = some v ∧
                                      shapeOfHOLExact v = .comb [.one, .one, .one]
                                  rw [hpostlu "intrinsic" (by decide) (by decide)]
                                  exact hdata.shapes.2.2)
                            hD2
                          rw [hpost₂] at hD2' ⊢
                          exact hD2'
                        -- the full invariant at post₂
                        have hLs₀ : memW s₀ (globN s₀ "bo" + 40)
                            = memW u (globN u "bo" + 40) := by
                          rw [hs₀]
                          show memW post_c (globN post_c "bo" + 40)
                            = memW u (globN u "bo" + 40)
                          rw [hbo_eq, hbo_pres 40 (by decide)]
                        have hLcell : memW post₂ (globN post₂ "bo" + 40)
                            = memW u (globN u "bo" + 40) := by
                          rw [hpost₂]
                          show memW {s₀ with memory := mem'} (globN s₀ "bo" + 40)
                            = memW u (globN u "bo" + 40)
                          rw [p4Loop31_memW_of_storeMiss hmem'pw (hmiss_bo 40 (by decide))]
                          rw [hLs₀]
                        have hLs₀out : memW s₀ (w_out.toNat + 16)
                            = memW u (w_out.toNat + 16) := by
                          rw [hs₀]
                          exact houtpres.1
                        have hLs₀L : memW s₀ (memW u (w_out.toNat + 16))
                            = memW u (memW u (w_out.toNat + 16)) := by
                          rw [hs₀]
                          exact houtpres.2.1
                        have hLs₀L8 : memW s₀ (memW u (w_out.toNat + 16) + 8)
                            = memW u (memW u (w_out.toNat + 16) + 8) := by
                          rw [hs₀]
                          exact houtpres.2.2
                        have hmissL_u := hmisses_out.2.1
                        rw [hLs₀out] at hmissL_u
                        have hmissL8_u := hmisses_out.2.2
                        rw [hLs₀out] at hmissL8_u
                        have hout16 : memW post₂ (w_out.toNat + 16)
                            = memW u (w_out.toNat + 16) := by
                          rw [hpost₂]
                          show memW {s₀ with memory := mem'} (w_out.toNat + 16)
                            = memW u (w_out.toNat + 16)
                          rw [p4Loop31_memW_of_storeMiss hmem'pw hmisses_out.1]
                          rw [hLs₀out]
                        have houtL : memW post₂ (memW u (w_out.toNat + 16))
                            = memW u (memW u (w_out.toNat + 16)) := by
                          rw [hpost₂]
                          show memW {s₀ with memory := mem'} (memW u (w_out.toNat + 16))
                            = memW u (memW u (w_out.toNat + 16))
                          rw [p4Loop31_memW_of_storeMiss hmem'pw hmissL_u]
                          rw [hLs₀L]
                        have houtL8 : memW post₂ (memW u (w_out.toNat + 16) + 8)
                            = memW u (memW u (w_out.toNat + 16) + 8) := by
                          rw [hpost₂]
                          show memW {s₀ with memory := mem'} (memW u (w_out.toNat + 16) + 8)
                            = memW u (memW u (w_out.toNat + 16) + 8)
                          rw [p4Loop31_memW_of_storeMiss hmem'pw hmissL8_u]
                          rw [hLs₀L8]
                        have hmissL8 := p4Loop31_pushLenCellMiss hARs₀ hEslot hWTs₀ hdata_nz₀ hin₀
                        rw [hLs₀] at hmissL8
                        have hL8 : memW post₂ (memW u (globN u "bo" + 40) + 8)
                            = memW u (memW u (globN u "bo" + 40) + 8) + 1 := by
                          rw [hpost₂]
                          show memW {s₀ with memory := mem'} (memW u (globN u "bo" + 40) + 8)
                            = memW u (memW u (globN u "bo" + 40) + 8) + 1
                          rw [p4Loop31_memW_of_storeMiss hmem'pw hmissL8]
                          rw [hs₀]
                          show memW post_c (memW u (globN u "bo" + 40) + 8)
                            = memW u (memW u (globN u "bo" + 40) + 8) + 1
                          have hlen' := hlen
                          rw [hw_l_nat] at hlen'
                          exact hlen'
                        have hun : locN u "nl" = nl_w.toNat := by simp [locN, hnl]
                        have hnl28w : nl_w.toNat < 2 ^ 28 := by
                          rw [← hun]
                          exact hnl28
                        have h3 : (i_w + 0x0000000000000001#64).toNat = i_w.toNat + 1 := by
                          have h1n : (0x0000000000000001#64 : BitVec 64).toNat = 1 := rfl
                          have hlt : i_w.toNat + 1 < 2 ^ 64 := by omega
                          rw [BitVec.toNat_add, h1n, Nat.mod_eq_of_lt hlt]
                        -- the full invariant at post₂
                        refine ⟨⟨⟨hDpost, ⟨i_w + 0x0000000000000001#64, ?_⟩,
                          ⟨nl_w, ?_⟩, ⟨lp_w, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_,
                          ⟨lp_w, nl_w, ?_, ?_, ?_, ?_⟩⟩, ?_, hcz⟩
                        · exact hli
                        · rw [hpostlu "nl" (by decide) (by decide)]
                          exact hnl
                        · rw [hpostlu "lp" (by decide) (by decide)]
                          exact hlp
                        · -- i_le
                          have h1 : locN post₂ "i" = (i_w + 0x0000000000000001#64).toNat := by
                            simp only [locN, hli]
                          have h2 : locN post₂ "nl" = nl_w.toNat := by
                            simp only [locN, hpostlu "nl" (by decide) (by decide), hnl]
                          rw [h1, h2, h3]
                          omega
                        · -- nl_lt
                          simp only [locN, hpostlu "nl" (by decide) (by decide), hnl]
                          exact hnl28w
                        · -- len_bound
                          have hnlpost : locN post₂ "nl" = nl_w.toNat := by
                            simp only [locN, hpostlu "nl" (by decide) (by decide), hnl]
                          have hipost : locN post₂ "i" = i_w.toNat + 1 := by
                            have h1 : locN post₂ "i" = (i_w + 0x0000000000000001#64).toNat := by
                              simp only [locN, hli]
                            rw [h1, h3]
                          have hui : locN u "i" = i_w.toNat := by simp [locN, hi]
                          rw [hLcell, hL8, hnlpost, hipost]
                          have hlenb := hlenb31
                          have hil := hi_lt'
                          omega
                        · -- txenv
                          have hgs : globN s₀ "bo" = globN u "bo" := by
                            show globN post_c "bo" = globN u "bo"
                            rw [hbo_eq]
                          have hmiss_bo_u : ∀ off ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
                              BitVec.ofNat 64 (globN u "bo" + off) ≠ w := by
                            intro off hoff
                            have h := hmiss_bo off hoff
                            rw [hgs] at h
                            exact h
                          have htxLIT : TxEnv (setVarHOLFinite (ofString "i")
                              (.val (.word (i_w + 0x0000000000000001#64)))
                              {s₀ with memory := mem'}) := by
                            rw [hs₀]
                            exact p4Loop31_txEnvPost htxenv hbo_eq hjcap_eq hmem'pw hbo_pres
                              hmiss_bo_u
                          obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := htxLIT
                          refine ⟨hb1, hb2, hb3, hb4, hb5, ?_, hb7⟩
                          have hlu_idx : (setVarHOLFinite (ofString "i")
                              (.val (.word (i_w + 0x0000000000000001#64)))
                              {s₀ with memory := mem'}).locals.lookup (ofString "index")
                              = u.locals.lookup (ofString "index") := by
                            rw [hs₀]
                            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                              show ofString "i" ≠ ofString "index" by decide,
                              show ofString "slot" ≠ ofString "index" by decide,
                              show ofString "index" ≠ ofString "i" by decide,
                              show ofString "index" ≠ ofString "slot" by decide]
                          have hlocidx : locN (setVarHOLFinite (ofString "i")
                              (.val (.word (i_w + 0x0000000000000001#64)))
                              {s₀ with memory := mem'}) "index"
                              = locN post₂ "index" := by
                            simp only [locN, hlu_idx, hpostlu "index" (by decide) (by decide)]
                          rw [← hlocidx]
                          exact hb6
                        · -- logs_nz
                          rw [hpost₂]
                          show memW {s₀ with memory := mem'} (w_out.toNat + 16) ≠ 0
                          rw [p4Loop31_memW_of_storeMiss hmem'pw hmisses_out.1]
                          rw [hLs₀out]
                          exact hlogs_nz
                        · -- lp lookup
                          rw [hpostlu "lp" (by decide) (by decide)]
                          exact hlp
                        · -- nl lookup
                          rw [hpostlu "nl" (by decide) (by decide)]
                          exact hnl
                        · -- lpw
                          rw [hout16, houtL]
                          exact hlpw
                        · -- nlw
                          rw [hout16, houtL8]
                          exact hnlw
                        · -- code
                          rw [hpost₂, hs₀]
                          show post_c.code = originalRuntimeCode
                          rw [hmeta]
                          exact hcode
                      · simp only [hev, hvalid, Bool.false_eq_true, ↓reduceIte] at hdec
                        exact absurd hdec (by simp)

/-- `TxEnv` reads only globals, memory and locals, so it survives the
clock decrement definitionally field by field. -/
theorem TxEnv_decClockHOLFinite {F : Type} {t : PanSemStateFiniteExact 64 F}
    (h : TxEnv t) : TxEnv (decClockHOLFinite t) :=
  ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7⟩

/-- The full loop-31 invariant survives the clock decrement: every field
reads only locals, globals and memory, so `decClockHOLFinite` (a locals-
preserving clock update) transports it by `p4Data_with_locals` and
definitional field equalities. -/
theorem p4Loop31Full_decClock {F : Type}
    {entry t s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (hINV : P4Loop31Full entry t s_pmc w_out) :
    P4Loop31Full entry (decClockHOLFinite t) s_pmc w_out := by
  obtain ⟨hbase31, htxenv, hlogs_nz, hlpnl⟩ := hINV
  obtain ⟨hdata, hi_word, hnl_word, hlp_word, hile, hnl28, hlenb31⟩ := hbase31
  have hD : P4Data entry (decClockHOLFinite t) s_pmc w_out :=
    p4Data_with_locals t.locals (t.clock - 1) hdata.out_local rfl rfl rfl hdata.shapes hdata
  exact ⟨⟨hD, hi_word, hnl_word, hlp_word, hile, hnl28, hlenb31⟩,
    TxEnv_decClockHOLFinite htxenv, hlogs_nz, hlpnl⟩

/-- Theorem A: the loop-31 body obligation for `p4Run_while_guard`.  At a
full-invariant state `t` with the guard holding and the code intact, the
body-plus-while-continuation runs from the decremented-clock state. -/
theorem p4Loop31_bodyWhile {F : Type}
    {entry t s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    {rest : ProgHOL 64}
    (hINV : P4Loop31Full entry t s_pmc w_out)
    (hcode : t.code = originalRuntimeCode)
    (hguard : ∃ w : BitVec 64, evalAt t p4Loop31Cond = some (.val (.word w)) ∧ w ≠ 0#64)
    (ih : ∀ mid, P4Loop31Full entry mid s_pmc w_out → mid.code = originalRuntimeCode →
      mid.clock < t.clock →
      PtxRelRunStrong entry (.seq (.while p4Loop31Cond p4Loop31Body) rest) mid)
    (hexit : ∀ t', P4Loop31Full entry t' s_pmc w_out →
      evalAt t' p4Loop31Cond = some (.val (.word 0#64)) →
      PtxRelRunStrong entry rest t') :
    PtxRelRunStrong entry (.seq p4Loop31Body
      (.seq (.while p4Loop31Cond p4Loop31Body) rest)) (decClockHOLFinite t) := by
  obtain ⟨hbase31, htxenv, hlogs_nz, hlpnl⟩ := hINV
  obtain ⟨hdata, hi_word, hnl_word, hlp_word, hile, hnl28, hlenb31⟩ := hbase31
  obtain ⟨i_w, hi⟩ := hi_word
  obtain ⟨nl_w, hnl⟩ := hnl_word
  obtain ⟨wg, hwg, hwne⟩ := hguard
  have hINV' : P4Loop31Full entry t s_pmc w_out :=
    ⟨⟨hdata, ⟨i_w, hi⟩, ⟨nl_w, hnl⟩, hlp_word, hile, hnl28, hlenb31⟩,
      htxenv, hlogs_nz, hlpnl⟩
  have hi_lt : locN t "i" < locN t "nl" := by
    have h1 : locN t "i" = i_w.toNat := by simp [locN, hi]
    have h2 : locN t "nl" = nl_w.toNat := by simp [locN, hnl]
    have hile' : i_w.toNat ≤ nl_w.toNat := by
      simp only [locN, hi, hnl] at hile
      exact hile
    have hnl28' : nl_w.toNat < 2 ^ 28 := by
      simp only [locN, hnl] at hnl28
      exact hnl28
    rw [h1, h2]
    exact p4Loop31_guard_lt hi hnl hile' hnl28' wg hwne hwg
  refine p4Run_loop31Body
    (fun s => P4Loop31Full entry s s_pmc w_out ∧ s.code = originalRuntimeCode) rfl
    (fun mid hm hlt => ih mid hm.1 hm.2 hlt)
    (fun t' ht' hcond => hexit t' ht'.1 hcond)
    (p4Loop31_bodyRun (p4Loop31Full_decClock hINV') hi_lt hcode) ?_
  intro post heq
  obtain ⟨hINVp, hcodep, hcz⟩ := p4Loop31_postInvariant (p4Loop31Full_decClock hINV')
    hi_lt hcode heq
  refine ⟨⟨hINVp, hcodep⟩, Or.inr ?_⟩
  have huclk : (decClockHOLFinite t).clock = t.clock - 1 := rfl
  omega

/-- Theorem B: the full loop-31 runner.  From a full-invariant state with
the code intact, the while-loop (with its continuation `rest`) satisfies
`PtxRelRunStrong`. -/
theorem p4Run_loop31 {F : Type}
    {entry t s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    {rest : ProgHOL 64}
    (hINV : P4Loop31Full entry t s_pmc w_out)
    (hcode : t.code = originalRuntimeCode)
    (hexit : ∀ t', P4Loop31Full entry t' s_pmc w_out →
      evalAt t' p4Loop31Cond = some (.val (.word 0#64)) →
      PtxRelRunStrong entry rest t') :
    PtxRelRunStrong entry (.seq (.while p4Loop31Cond p4Loop31Body) rest) t :=
  p4Run_while_guard p4Loop31Cond p4Loop31Body rest
    (fun s => P4Loop31Full entry s s_pmc w_out ∧ s.code = originalRuntimeCode)
    p4Loop31Body_noTopBreak p4Loop31Body_noTopContinue
    (fun t' ht' hcond => hexit t' ht'.1 hcond)
    (fun t' ht' hguard ih' =>
      p4Loop31_bodyWhile ht'.1 ht'.2 hguard
        (fun mid hm hcm hlt => ih' mid ⟨hm, hcm⟩ hlt) hexit)
    t ⟨hINV, hcode⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
