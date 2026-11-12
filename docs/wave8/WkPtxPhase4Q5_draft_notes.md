I have all the patterns now. Time to write WkPtxPhase4Q5.lean. This is a large file — let me write it carefully, following the patterns from Q4's p4Q8Loop_store_mem.

Plan recap:

```lean
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4Q4

[options + opens + namespace from Q4]

theorem p4Q8_loopEntry {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (h : P4Data entry s s_pmc w_out)
    (hc : s.code = originalRuntimeCode)
    (tail : ProgHOL 64)
    (nl_w lp_w : BitVec 64)
    (hnl : s.locals.lookup (ofString "nl") = some (.val (.word nl_w)))
    (hlp : s.locals.lookup (ofString "lp") = some (.val (.word lp_w)))
    (hd_nz : memW s (w_out.toNat + 16) ≠ 0)
    (hnl_eq : nl_w.toNat = memW s (memW s (w_out.toNat + 16) + 8))
    (hlp_eq : lp_w.toNat = memW s (memW s (w_out.toNat + 16)))
    (hLL : LogsListOK s (memW s (w_out.toNat + 16)))
    (hDF : LogsDisjFixed s (memW s (w_out.toNat + 16)))
    (hnl28 : nl_w.toNat < 2 ^ 28)
    (htail : ∀ (lw capw w_lp : BitVec 64) (t' : PanSemStateFiniteExact 64 F) (i_w : BitVec 64),
      P4Q8Loop entry s_pmc w_out lw capw nl_w w_lp lp_w i_w t' →
      evalAt t' p4Loop38Cond = some (.val (.word 0#64)) →
      PtxRelRunStrong entry tail t') :
    PtxRelRunStrong entry
      (.dec (ofString "stable_log_cap") .one (.var .local (ofString "nl"))
        (.seq (.ite (.cmp .equal (.var .local (ofString "stable_log_cap")) (.const 0x0#64))
            (.assign .local (ofString "stable_log_cap") (.const 0x1#64)) .skip)
          (.decCall (ofString "stable_logs") .one (ofString "lst_new")
            [(.const 0x8#64), (.var .local (ofString "stable_log_cap"))]
            (.seq (.store (.op .add [.var .local (ofString "stable_logs"), (.const 0x8#64)])
                (.var .local (ofString "nl")))
              (.dec (ofString "stable_lp") .one
                (.load .one (.op .add [.var .local (ofString "stable_logs"), (.const 0x0#64)]))
                (.seq (.assign .local (ofString "i") (.const 0x0#64))
                  (.seq (.while p4Loop38Cond p4Loop38Body) tail)))))) s := by
```

Wait — I must match stableLogs_alloc's conclusion EXACTLY (well, up to defeq — but for refine to apply, the elaborated terms must unify — since I copy the text verbatim from stableLogs_alloc's conclusion with rest := REST1, it's fine — I need to copy the literals exactly: 0x0000000000000000#64 etc. (full 16-hex-digit literals). I'll copy from the dump verbatim.

Proof body:

```lean
  refine p4Q8_stableLogs_alloc h hc _ nl_w lp_w hnl hlp hnl28.le ?_
  intro capw lw mid hcap1 hnlcap hmul hlw_eq hlw_al hlw_nz hm0 hm8 hm16 hgl_mid hhp_sb
    hARmid hsp_mid hfmp_mid hlst_mid hobjs_mid hdisj_mid hobjs_props hFO_mid hk_mid hlocm
    hlocap hlocl hwout hchain0 hDmid hcmid
```

Then the body sections:

SECTION 0 — basic numeric facts:
```lean
  have hArenaOK_s : ArenaOK s := h.base.world.1.2
  have hhp_lim_s : globN s "heap_ptr" ≤ heapLimit := hArenaOK_s.2.1
  have hEnd64 : heapEnd < 2 ^ 64 := by decide
  have hLimEnd : heapLimit ≤ heapEnd := by decide
  have hSE64 : scratchEnd < 2 ^ 64 := by decide
  have hlt64 : lw.toNat < 2 ^ 64 := by omega
  have hlwv : lw = BitVec.ofNat 64 lw.toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt hlt64]
```
Hmm — after `rw [BitVec.toNat_ofNat]`: goal `lw.toNat = lw.toNat % 2 ^ 64` — `rw [Nat.mod_eq_of_lt hlt64]` rewrites `lw.toNat % 2^64` → lw.toNat ✓ goal closes rfl automatically after rw (rw tries rfl) ✓.

```lean
  -- the data word of the fresh header
  have hmem_lw : ∃ w : BitVec 64,
      mid.memory (BitVec.ofNat 64 lw.toNat) = .word w ∧ w.toNat = lw.toNat + 24 := by
    have h0 : memW mid lw.toNat = lw.toNat + 24 := hm0
    unfold memW at h0
    rw [hlwv] at h0
```
Hmm wait — h0 after unfold: `(match mid.memory (BitVec.ofNat 64 lw.toNat) with | .word w => w.toNat) = lw.toNat + 24`. rw [hlwv] at h0 — replaces `lw` with `BitVec.ofNat 64 lw.toNat` — but `lw` also occurs in `lw.toNat` on the RHS! rw would rewrite `lw` EVERYWHERE including inside `lw.toNat` → `(BitVec.ofNat 64 lw.toNat).toNat` — NO WAIT: rw [hlwv] rewrites occurrences of the PATTERN `lw` — in `lw.toNat`, the subterm `lw` occurs → becomes `(BitVec.ofNat 64 lw.toNat).toNat`?? That's a mess — rw replaces ALL occurrences of `lw`. Hmm — but `BitVec.ofNat 64 lw.toNat` itself contains `lw` — rw is one-pass simultaneous: all `lw` occurrences in h0 replaced by `BitVec.ofNat 64 lw.toNat` — including the one inside the RHS `lw.toNat` → RHS becomes `(BitVec.ofNat 64 lw.toNat).toNat`. And LHS discriminant becomes `mid.memory (BitVec.ofNat 64 (BitVec.ofNat 64 lw.toNat).toNat)`?? NO wait — LHS after unfold is `mid.memory (BitVec.ofNat 64 lw.toNat)` — the `lw` inside `lw.toNat` → replaced: `BitVec.ofNat 64 (BitVec.ofNat 64 lw.toNat).toNat` — DISASTER. rw [hlwv] at h0 is WRONG.

Better: work with the discriminant directly. Don't rw; instead do cases on `mid.memory (BitVec.ofNat 64 lw.toNat)`:

```lean
  have hmem_lw : ∃ w : BitVec 64,
      mid.memory (BitVec.ofNat 64 lw.toNat) = .word w ∧ w.toNat = lw.toNat + 24 := by
    have h0 : memW mid lw.toNat = lw.toNat + 24 := hm0
    unfold memW at h0
    cases hc2 : mid.memory (BitVec.ofNat 64 lw.toNat) with
    | word w =>
      rw [hc2] at h0
      dsimp only at h0
      exact ⟨w, hc2, h0⟩
```
Hmm — `rw [hc2] at h0` — hc2 : mid.memory (BitVec.ofNat 64 lw.toNat) = .word w — rw at h0 replaces the discriminant ✓ — h0 : (match .word w with | .word w => w.toNat) = lw.toNat + 24 — hmm, wait — actually after `cases hc2 : X with | word w =>` — in the goal (which is the ∃-statement) — hmm, cases on X — the GOAL doesn't mention X... the goal is `∃ w, mid.memory (BitVec.ofNat 64 lw.toNat) = .word w ∧ ...` — it DOES mention X ✓ — cases rewrites goal occurrences to `.word w` ✓. h0 (hypothesis) not rewritten — rw [hc2] at h0 ✓. Then `dsimp only at h0` — reduces the match — h0 : w.toNat = lw.toNat + 24 ✓. exact ⟨w, hc2, h0⟩ ✓.

Wait — but does `cases hc2 : e with | word w` work when HolWordLab 64 has ONE constructor? Yes — cases with one branch ✓. Hmm — actually is the constructor really named `word`? From p4Q8_stableLogs_alloc's own proof: `cases hw : w with | word b =>` ✓ (in the dump above). ✓.

```lean
  obtain ⟨w_lp, hw0, hwlp_nat⟩ := hmem_lw
  have hw0' : mid.memory lw = .word w_lp := by rw [hlwv]; exact hw0
```
Goal: mid.memory lw = .word w_lp — rw [hlwv] replaces `lw` → `BitVec.ofNat 64 lw.toNat` — again the RHS has no `lw` — but the LHS `mid.memory lw` — the `lw` there → replaced ✓; are there other `lw`s in the goal? `hw0`'s statement isn't in the goal. Goal: `mid.memory lw = HolWordLab.word w_lp` — only one `lw` ✓ → `mid.memory (BitVec.ofNat 64 lw.toNat) = .word w_lp` = hw0 ✓.

```lean
  -- geometry constants
  have hArenaOKmid : ArenaOK mid := hARmid.2
  have hhpm : globN mid "heap_ptr" ≤ heapLimit := hArenaOKmid.2.1
  have hheap_lim : lw.toNat + 24 ≤ heapLimit := by omega
```
omega context: hgl_mid : globN mid "heap_ptr" = lw.toNat + 24 + 8 * capw.toNat, hhpm ✓ → omega ✓.

SECTION 1 — the source list at s (geo + allocated):
```lean
  -- the source list at s: header, array, entries
  obtain ⟨hhdw_s, hhd_alloc_s, hhd8c_s, hhd16c_s, hent_s⟩ :=
    (by rcases hLL with h0 | ⟨hw, ha, hc8, hc16, he⟩
        · exact absurd h0 hd_nz
        · exact ⟨hw, ha, hc8, hc16, he⟩ :
      ∃ hw : WordsOK s (memW s (w_out.toNat + 16), 24) ...
```
Hmm — that's awkward. Cleaner:
```lean
  have hLL' : WordsOK s (memW s (w_out.toNat + 16), 24) ∧
      Allocated s (memW s (w_out.toNat + 16), 24) ∧
      memW s (memW s (w_out.toNat + 16) + 8) < 2 ^ 28 ∧
      memW s (memW s (w_out.toNat + 16) + 8) ≤ memW s (memW s (w_out.toNat + 16) + 16) ∧
      ∀ i, i < memW s (memW s (w_out.toNat + 16) + 8) →
        WordAt s (memW s (memW s (w_out.toNat + 16)) + 8 * i) ∧
        LogEntryOK s (memW s (memW s (memW s (w_out.toNat + 16)) + 8 * i)) := by
    rcases hLL with h0 | ⟨hw, ha, hc8, hc16, he⟩
    · exact absurd h0 hd_nz
    · exact ⟨hw, ha, hc8, hc16, he⟩
  obtain ⟨hhdw_s, hhd_alloc_s, hhd8c_s, hhd16c_s, hent_s⟩ := hLL'
```
Hmm — the rcases with h0 : memW s (w_out+16) = 0 — the term is not an fvar — plain rcases on Or is fine (h0 as eq hypothesis) ✓ `absurd h0 hd_nz` ✓.

Note: hLL : LogsListOK s (memW s (w_out.toNat + 16)) — the rcases second branch gives the conjunction with `logs := memW s (w_out.toNat + 16)` substituted ✓.

```lean
  -- the source array is allocated at s
  obtain ⟨ha_arr_s, -⟩ := hDF ... 
```
hDF : LogsDisjFixed s (memW s (w_out.toNat + 16)) — def: logs = 0 ∨ (Allocated s (memW s logs, 8 * memW s (logs + 8)) ∧ IvlsDisj [...] (fixedObjects s)) — hmm — what exactly is the IvlsDisj's first arg? From C03.lean:259: `LogsDisjFixed s logs := logs = 0 ∨ (Allocated s (memW s logs, 8*memW s (logs+8)) ∧ IvlsDisj [...] (fixedObjects s))` — the [...] I don't remember exactly — doesn't matter (ignored with `-`). Let me double-check by reading C03.lean:255-265.

```lean
  have ha_arr_s : Allocated s (lp_w.toNat, 8 * nl_w.toNat) := by
    rcases hDF with h0 | ⟨ha, -⟩
    · exact absurd h0 hd_nz
    · rw [← hlp_eq, ← hnl_eq]; exact ha
```
Goal: Allocated s (lp_w.toNat, 8*nl_w.toNat); rw [← hlp_eq] — hlp_eq : lp_w.toNat = memW s (memW s (w_out+16)) — ← rewrites `memW s (memW s (w_out.toNat + 16))` → lp_w.toNat — in the goal, is there such an occurrence? The goal is about (lp_w.toNat, 8*nl_w.toNat) — no occurrence of the memW-term — rw [← hlp_eq] would FAIL (no occurrence). I need the opposite: in `ha : Allocated s (memW s (memW s (w_out+16)), 8 * memW s (memW s (w_out+16) + 8))` — rw [hlp_eq] at ha?? hlp_eq's LHS is lp_w.toNat — rewriting lp_w.toNat → memW-term — in ha there's no lp_w. Hmm — rw [hlp_eq] at ha replaces `lp_w.toNat` occurrences — none. FAIL.

Correct approach: rw [← hlp_eq] and [← hnl_eq] in the GOAL — the goal is Allocated s (lp_w.toNat, 8 * nl_w.toNat) — rw [← hlp_eq] rewrites occurrences of hlp_eq's RHS (`memW s (memW s (w_out.toNat + 16))`) — none in goal. FAIL.

Hmm. So instead: state the goal in memW-form and then rewrite... or use ▸. Simplest: 
```lean
  have ha_arr_s : Allocated s (lp_w.toNat, 8 * nl_w.toNat) := by
    rcases hDF with h0 | ⟨ha, -⟩
    · exact absurd h0 hd_nz
    · have h1 : lp_w.toNat = memW s (memW s (w_out.toNat + 16)) := hlp_eq
      have h2 : nl_w.toNat = memW s (memW s (w_out.toNat + 16) + 8) := hnl_eq
      rw [h1, h2]  -- hmm — rewrites LHS→RHS in goal: lp_w.toNat → memW-term — goal becomes Allocated s (memW-term, 8 * memW-term2) = ha ✓
      exact ha
```
rw [h1] in goal `Allocated s (lp_w.toNat, 8 * nl_w.toNat)` — replaces lp_w.toNat → memW s (memW s (w_out+16)) ✓; rw [h2] replaces nl_w.toNat → memW s (hd+8) — but CAREFUL: after rw [h1], the goal contains `memW s (memW s (w_out.toNat + 16))` — h2's LHS is nl_w.toNat — distinct ✓. Then goal = ha ✓ exact ha.

Hmm wait — but actually there's a subtlety: `rw [h1]` — h1 : lp_w.toNat = memW s (memW s (w_out.toNat + 16)) — rewrites ALL occurrences of `lp_w.toNat` — the goal has it once ✓.

```lean
  -- geo facts (state-independent)
  have geo_hdr_s : p4Q8OldGeo lw.toNat (memW s (w_out.toNat + 16), 24) :=
    p4Q8OldGeo_of_alloc hArenaOK_s hlw_eq.symm hhd_alloc_s
  have geo_arr_s : p4Q8OldGeo lw.toNat (lp_w.toNat, 8 * nl_w.toNat) :=
    p4Q8OldGeo_of_alloc hArenaOK_s hlw_eq.symm ha_arr_s
  have hent_geo_s : ∀ i, i < nl_w.toNat →
      p4Q8OldGeo lw.toNat (memW s (lp_w.toNat + 8 * i), 40) := by
    intro i hi
    obtain ⟨-, hin40, -⟩ := hent_s i (by rw [hnl_eq]; exact hi)
    exact Or.inl ⟨hin40.1, by rw [hlw_eq]; exact hin40.2⟩
```
Hmm — hent_s i hi' : WordAt s (memW s (memW s (w_out+16)) + 8*i) ∧ LogEntryOK s (memW s (memW s (memW s (w_out+16)) + 8*i)) — the index condition: i < memW s (memW s (w_out+16) + 8) — provide via rw [hnl_eq]: goal `i < memW s (memW s (w_out.toNat + 16) + 8)` — rw [hnl_eq] rewrites nl_w.toNat → the memW term — WRONG direction — the goal doesn't contain nl_w.toNat. FAIL. Correct: `by rw [← hnl_eq]; exact hi` — goal i < memW-term — rw [← hnl_eq] rewrites the memW-term → nl_w.toNat ✓ — goal i < nl_w.toNat ✓ exact hi.

And the WordAt/entry values in hent_s are stated with `memW s (memW s (memW s (w_out+16)) + 8*i)` — hmm — hmm the entry VALUE differs from `memW s (lp_w.toNat + 8*i)` — they're equal by hlp_eq-rewriting. For hent_geo_s I want geo about `memW s (lp_w.toNat + 8*i)`. Since memW s (memW s (memW s (w_out+16)) + 8*i) — rewrite inner: = memW s (lp_w.toNat + 8*i). So:
```lean
  have hent_geo_s : ∀ i, i < nl_w.toNat →
      p4Q8OldGeo lw.toNat (memW s (lp_w.toNat + 8 * i), 40) := by
    intro i hi
    have hi' : i < memW s (memW s (w_out.toNat + 16) + 8) := by rw [← hnl_eq]; exact hi
    obtain ⟨-, hin40, -⟩ := hent_s i hi'
    refine Or.inl ⟨hin40.1, ?_⟩
    rw [← hlp_eq] at hin40  -- hmm — hin40.2 : log + 40 ≤ globN s hp where log = memW s (memW s (memW s (w_out+16)) + 8*i)...
```
Hmm — LogEntryOK's hin40 : Inside (log, 40) sourceBase (globN s "heap_ptr") — where log = memW s (memW s (memW s (w_out+16)) + 8*i)?? NO — wait. LogEntryOK s (memW s (memW s logs + 8*i)) — the LogEntryOK is ABOUT the value `memW s (memW s logs + 8*i)`. So obtain ⟨-, hin40, -⟩ — the second component of LogEntryOK — LogEntryOK s log := WordsOK s (log,40) ∧ Inside (log,40) sourceBase (globN s hp) ∧ ... — so from hent_s i hi' : WordAt ∧ LogEntryOK — obtain ⟨-, hle⟩ := hent_s — hle : LogEntryOK s (memW s (memW s (memW s (w_out+16)) + 8*i)) — then hle.2.1 : Inside (that log, 40) sourceBase (globN s hp). I want geo for `memW s (lp_w.toNat + 8*i)` — hmm — these are DIFFERENT TERMS: `memW s (memW s (memW s (w_out+16)) + 8*i)` vs `memW s (lp_w.toNat + 8*i)` — equal after rw [hlp_eq] (rewriting lp_w.toNat → memW s (memW s (w_out+16))). 

Let me restructure: first normalize hent_s into lp-form:
```lean
  have hent_s' : ∀ i, i < nl_w.toNat →
      WordAt s (lp_w.toNat + 8 * i) ∧ LogEntryOK s (memW s (lp_w.toNat + 8 * i)) := by
    intro i hi
    have hi' : i < memW s (memW s (w_out.toNat + 16) + 8) := by rw [← hnl_eq]; exact hi
    obtain ⟨hw, hle⟩ := hent_s i hi'
    rw [hlp_eq] at hw hle
    exact ⟨hw, hle⟩
```
Hmm — hw : WordAt s (memW s (memW s (w_out+16)) + 8*i) — rw [hlp_eq] at hw — hlp_eq : lp_w.toNat = memW s (memW s (w_out+16)) — rewrites lp_w.toNat → memW-term — hw has NO lp_w.toNat. FAIL again!! I need ←: rw [← hlp_eq] at hw — rewrites `memW s (memW s (w_out.toNat + 16))` → lp_w.toNat ✓ — hw becomes WordAt s (lp_w.toNat + 8*i) ✓. Similarly hle : LogEntryOK s (memW s (memW s (memW s (w_out+16)) + 8*i)) — rw [← hlp_eq] at hle — the inner `memW s (memW s (w_out+16))` → lp_w.toNat ✓ — hle : LogEntryOK s (memW s (lp_w.toNat + 8*i)) ✓.

OK so direction: `rw [← hlp_eq]` (RHS→LHS). Since hlp_eq : lp_w.toNat = memW s (...), ← direction rewrites memW s (...) → lp_w.toNat ✓.

Similarly for hnl_eq: `rw [← hnl_eq]` rewrites `memW s (memW s (w_out+16) + 8)` → nl_w.toNat.

Let me redo ha_arr_s with correct directions:
```lean
  have ha_arr_s : Allocated s (lp_w.toNat, 8 * nl_w.toNat) := by
    rcases hDF with h0 | ⟨ha, -⟩
    · exact absurd h0 hd_nz
    · rw [hlp_eq, hnl_eq]
      exact ha
```
Goal Allocated s (lp_w.toNat, 8*nl_w.toNat) — rw [hlp_eq] rewrites lp_w.toNat → memW s (memW s (w_out+16)) ✓ (forward direction this time — goal CONTAINS lp_w.toNat). Then rw [hnl_eq] rewrites nl_w.toNat → memW s (hd+8) ✓. Goal = ha's type ✓. 

And geo facts:
```lean
  have geo_hdr_s : p4Q8OldGeo lw.toNat (memW s (w_out.toNat + 16), 24) :=
    p4Q8OldGeo_of_alloc hArenaOK_s hlw_eq.symm hhd_alloc_s
  have geo_arr_s : p4Q8OldGeo lw.toNat (lp_w.toNat, 8 * nl_w.toNat) :=
    p4Q8OldGeo_of_alloc hArenaOK_s hlw_eq.symm ha_arr_s
```
✓ (p4Q8OldGeo_of_alloc (hAs : ArenaOK t) (hlw : globN t "heap_ptr" = lw) (ha : Allocated t i) — hlw_eq.symm : globN s "heap_ptr" = lw.toNat ✓).

```lean
  have hent_s' : ∀ i, i < nl_w.toNat →
      WordAt s (lp_w.toNat + 8 * i) ∧ LogEntryOK s (memW s (lp_w.toNat + 8 * i)) := ...
  have hent_geo_s : ∀ i, i < nl_w.toNat →
      p4Q8OldGeo lw.toNat (memW s (lp_w.toNat + 8 * i), 40) := by
    intro i hi
    obtain ⟨-, hle⟩ := hent_s' i hi
    exact Or.inl ⟨hle.2.1.1, by rw [hlw_eq]; exact hle.2.1.2⟩
```
Hmm — hle : LogEntryOK s (log) = WordsOK s (log,40) ∧ Inside (log,40) sourceBase (globN s hp) ∧ ... — hle.2.1 : Inside (log,40) sourceBase (globN s "heap_ptr") — Inside is a def to And — hle.2.1.1 : sourceBase ≤ log ✓; hle.2.1.2 : log + 40 ≤ globN s hp. Goal second component: `memW s (lp_w.toNat + 8*i) + 40 ≤ lw.toNat` — after rw [hlw_eq] — hmm — rw [hlw_eq] rewrites lw.toNat → globN s hp ✓ — goal becomes log + 40 ≤ globN s hp ✓ exact hle.2.1.2.
Hmm — but the geo's first disjunct: Inside (log,40) sourceBase lw.toNat — providing Or.inl ⟨h1, h2⟩ — the expected type after Or.inl: Inside (memW s (lp_w.toNat + 8*i), 40) sourceBase lw.toNat — a def — providing ⟨hle.2.1.1, ...⟩ — anonymous constructor against Inside — Inside unfolds to And — anonymous ⟨_, _⟩ works against a def-to-And? The expected type must whnf to a structure for anonymous constructor — Lean whnfs the expected type ✓ (anonymous constructor elaboration unfolds reducible... hmm — Inside is a regular def — anonymous constructor does whnf with default transparency? I believe ⟨...⟩ uses whnf which unfolds defs ✓ — Q4's code did `refine Or.inl ⟨h.1, ?_⟩` — wait — in Q2: `refine Or.inl ⟨h.1, ?_⟩` for Inside ✓ (p4Q8OldGeo_of_alloc's proof). And `⟨Nat.le_trans ..., by omega⟩` for Inside in Q4 ✓. OK ✓.

SECTION 2 — the frame s→mid (memW transports):
```lean
  -- the frame s → mid: cells of allocated regions survive the lst_new allocation
  have hscr_ge : scratchStart ≤ globN s "scratch_ptr" :=
    Nat.le_trans hArenaOK_s.2.2.1 hArenaOK_s.2.2.2.1
```
ArenaOK s .2.2.1 : scratchStart ≤ globN s frame_mem_ptr; .2.2.2.1 : globN s frame_mem_ptr ≤ globN s scratch_ptr ✓ — so hArenaOK_s.2.2.1 trans .2.2.2.1... wait order: ArenaOK := sourceBase≤hp ∧ hp≤heapLimit ∧ scratchStart≤fmp ∧ fmp≤sp ∧ sp≤scratchEnd ∧ ... — .1: sourceBase ≤ hp; .2.1: hp ≤ heapLimit; .2.2.1: scratchStart ≤ fmp; .2.2.2.1: fmp ≤ sp; .2.2.2.2.1: sp ≤ scratchEnd. So scratchStart ≤ sp := Nat.le_trans hArenaOK_s.2.2.1 hArenaOK_s.2.2.2.1 ✓.

```lean
  have hlim_scr : heapLimit = scratchStart := rfl
  have hmemW_frame : ∀ (i : Ivl), Allocated s i → ∀ k : Nat, i.1 ≤ k → k + 8 ≤ i.1 + i.2 →
      memW mid k = memW s k := by
    intro i halloc k hk1 hk2
    have hk64 : k < 2 ^ 64 := by
      rcases halloc with hgt | hgt
      · unfold Inside at hgt; obtain ⟨_, h2⟩ := hgt; omega
      · unfold Inside at hgt; obtain ⟨_, h2⟩ := hgt; omega
    have hk' : (BitVec.ofNat 64 k).toNat = k := by
      rw [BitVec.toNat_ofNat]; omega
    unfold memW
    dsimp only
    rw [hFO_mid (BitVec.ofNat 64 k) ?_ ?_]
    · rw [hk']
    · -- keep miss: ¬CellHits k (globN s "scratch_ptr", 0)
      intro hcc
      simp only [CellHits] at hcc
      obtain ⟨hc1, hc2⟩ := hcc
      dsimp only at hc1 hc2
      rcases halloc with hgt | hgt
      · unfold Inside at hgt; obtain ⟨g1, g2⟩ := hgt; omega
      · unfold Inside at hgt; obtain ⟨g1, g2⟩ := hgt; omega
    · -- fresh miss: ¬CellHits k (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr")
      intro hcc
      simp only [CellHits] at hcc
      obtain ⟨hc1, hc2⟩ := hcc
      dsimp only at hc1 hc2
      rcases halloc with hgt | hgt
      · unfold Inside at hgt; obtain ⟨g1, g2⟩ := hgt; omega
      · unfold Inside at hgt; obtain ⟨g1, g2⟩ := hgt; omega
```

Hmm — let me carefully verify the omega obligations:

hk64 (heap case): g2 : k + 8 ≤ i.1 + i.2 ≤ globN s "heap_ptr" — wait Inside i sourceBase (globN s hp): g2 : i.1 + i.2 ≤ globN s hp — hmm — Inside (i) (lo) (hi) := lo ≤ i.1 ∧ i.1 + i.2 ≤ hi. Heap case: Inside i sourceBase (globN s "heap_ptr") — g1 : sourceBase ≤ i.1, g2 : i.1 + i.2 ≤ globN s hp. With hk1 : i.1 ≤ k, hk2 : k+8 ≤ i.1+i.2: k+8 ≤ globN s hp = lw.toNat (hlw_eq) ≤ heapLimit (hhp_lim_s) ≤ heapEnd (hLimEnd) < 2^64 (hEnd64) ✓ omega (context: hk2, g2, hlw_eq, hhp_lim_s, hLimEnd, hEnd64 — all present ✓).
(scratch case): g2 : i.1 + i.2 ≤ scratchEnd — k+8 ≤ i.1+i.2 ≤ scratchEnd < 2^64 (hSE64) ✓.

keep-miss (heap): hc1 : (globN s "scratch_ptr", 0).1 < k + 8 — after dsimp: globN s "scratch_ptr" < k+8; hc2 : k < (scr,0).1 + (scr,0).2 = scr + 0. Need False. Heap: k+8 ≤ lw.toNat = globN s hp ≤ heapLimit = scratchStart ≤ scr (hscr_ge) — so k+8 ≤ scr → ¬(scr < k+8) ✓ contradiction with hc1. omega needs: hk2, g2 (i.1+i.2 ≤ globN s hp), hlw_eq, hhp_lim_s, hlim_scr (heapLimit = scratchStart), hscr_ge, hc1, hc2 ✓ all in context.
(scratch): g1 : globN s "scratch_ptr" ≤ i.1 ≤ k (hk1) → k ≥ scr → ¬(k < scr) contradiction with hc2 (k < scr + 0) ✓ omega.

fresh-miss: fresh = (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr"). hc1 : (fresh).1 < k+8 → globN s hp < k+8; hc2 : k < fresh.1 + fresh.2 = globN s hp + (globN mid hp - globN s hp). 
(heap): k+8 ≤ i.1+i.2 ≤ globN s hp → ¬(globN s hp < k+8) contradiction hc1 ✓ omega.
(scratch): k ≥ scr ≥ scratchStart = heapLimit ≥ globN s hp (hhp_lim_s)... and hc2 : k < globN s hp + (globN mid hp - globN s hp). Also globN mid hp ≤ heapLimit (hhpm — from ArenaOK mid ✓ in context). And globN s hp ≤ globN mid hp (hhp_sb — in context ✓ — it's a premise). So globN s hp + (globN mid hp - globN s hp) = globN mid hp ≤ heapLimit = scratchStart ≤ scr ≤ i.1 ≤ k → k < ... ≤ k contradiction ✓ omega (with hhp_sb, hhpm, hlim_scr, hscr_ge, g1, hk1, hc2 ✓).

Hmm — Nat.sub: omega handles ✓.

The `rw [hFO_mid (BitVec.ofNat 64 k) ?_ ?_]` — rw with a term containing metavariables — messy. Better:
```lean
    have hkeep : ∀ i ∈ [(globN s "scratch_ptr", 0 : Ivl)], ¬ CellHits (BitVec.ofNat 64 k).toNat i := by
      intro i hi
      rcases List.mem_singleton.1 hi with rfl
      intro hcc
      simp only [CellHits] at hcc
      obtain ⟨hc1, hc2⟩ := hcc
      dsimp only at hc1 hc2
      rcases halloc with hgt | hgt
      · unfold Inside at hgt; obtain ⟨g1, g2⟩ := hgt; omega
      · unfold Inside at hgt; obtain ⟨g1, g2⟩ := hgt; omega
    have hfresh : ¬ CellHits (BitVec.ofNat 64 k).toNat
        (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") := by
      intro hcc
      simp only [CellHits] at hcc
      obtain ⟨hc1, hc2⟩ := hcc
      dsimp only at hc1 hc2
      rcases halloc with hgt | hgt
      · unfold Inside at hgt; obtain ⟨g1, g2⟩ := hgt; omega
      · unfold Inside at hgt; obtain ⟨g1, g2⟩ := hgt; omega
    have hframe := hFO_mid (BitVec.ofNat 64 k) hkeep hfresh
    -- hframe : mid.memory (BitVec.ofNat 64 k) = s.memory (BitVec.ofNat 64 k)
    unfold memW
    dsimp only
    rw [hframe]
    rw [hk']
```
Hmm — the goal after `unfold memW; dsimp only`: `(match mid.memory (BitVec.ofNat 64 k) with | .word w => w.toNat) = (match s.memory (BitVec.ofNat 64 k) with | .word w => w.toNat)`. rw [hframe] — rewrites `mid.memory (BitVec.ofNat 64 k)` → `s.memory (BitVec.ofNat 64 k)` ✓ — goal becomes both sides identical → rfl closed by rw ✓. Then the `rw [hk']` line is dead — remove it. Actually after rw [hframe] the goal is rfl — rw closes it automatically. 

Hmm — wait: does `dsimp only` after unfold memW work — the goal `memW mid k = memW s k` — unfold memW gives match-expressions ✓ (from p4Q8MemW_store_of_geo's pattern: `unfold memW; dsimp only; rw [hcell ...]` ✓ exactly this pattern).

Hmm — but hold on: the goal is `memW mid k = memW s k` — `unfold memW` — unfolds BOTH occurrences ✓. Then rw [hframe] ✓.

Wait — actually — will `rw [hframe]` work when the match discriminant `mid.memory (BitVec.ofNat 64 k)` appears under a matcher? The matcher application `Matcher (mid.memory (BitVec.ofNat 64 k))` — rewriting inside works ✓ (rw under binders ok — no binders here, matcher applied directly).

Hmm — one concern: after `unfold memW`, is the discriminant exactly `mid.memory (BitVec.ofNat 64 k)`? memW def (MemoryViews:28): `memW s a := match s.memory (BitVec.ofNat 64 a) with | .word w => w.toNat` — wait, from my summary: `memW s a := match s.memory (BitVec.ofNat 64 a) with | .word w => w.toNat`. Hmm — but actually the real def might be `fun s a => match s.memory ... `. p4Q8MemW_store_of_geo's proof does `unfold memW; dsimp only; rw [hcell (BitVec.ofNat 64 k) ...]` where hcell : ∀ a, ¬CellHits a.toNat (base,sz) → mem' a = t.memory a — instantiated at a := BitVec.ofNat 64 k — gives `mem' (BitVec.ofNat 64 k) = t.memory (BitVec.ofNat 64 k)` — and rw rewrites the discriminant `mem' (BitVec.ofNat 64 k)` → `t.memory (BitVec.ofNat 64 k)` ✓ — EXACTLY my situation with hframe ✓. 

Now — the value transports:
```lean
  -- cells of the out-record and source list survive s → mid
  have hout_alloc : Allocated s (w_out.toNat, 96) := Or.inl h.out_inside
```
Hmm — h.out_inside : Inside (w_out.toNat, 96) sourceBase (globN s "heap_ptr") — h is P4Data entry s s_pmc w_out — h.out_inside at s ✓. Allocated s i := Inside i sourceBase (globN s hp) ∨ ... ✓ Or.inl h.out_inside ✓.

```lean
  have h16_mid : memW mid (w_out.toNat + 16) = memW s (w_out.toNat + 16) :=
    hmemW_frame (w_out.toNat, 96) hout_alloc (w_out.toNat + 16) (by omega) (by omega)
```
hk1 : (w_out,96).1 ≤ w_out+16 ✓ omega (after dsimp — hmm — `(w_out.toNat, 96).1` — omega sees pair projections? (w_out.toNat, 96).1 reduces definitionally — omega's preprocessing does dsimp/whnf on pair projections? The lesson says omega can't see structure projections — for PAIRS, omega handles .1/.2 of literal pairs? Hmm — risky. Q4's code: `hmemW_geo lp_w.toNat (8 * nl_w.toNat) h.geo_out_arr _ (by omega) (by omega)` — with hkin : i.1 ≤ k ∧ k+8 ≤ i.1+i.2 where i := (lp, 8nl) — in Q4's hmemW_geo (local have), the k arguments were `(by omega)`. Hmm — but those are Ivl-pair projections — in Q4 the same pattern worked with `by omega`?? Looking at Q4's code: `have hmemW_geo : ∀ a b : Nat, p4Q8OldGeo lw.toNat (a, b) → ∀ k : Nat, a ≤ k → k + 8 ≤ a + b → memW ... = memW u k := by intro a b hgeo k hk1 hk2; exact p4Q8MemW_store_of_geo hcell hgeo ⟨hk1, hk2⟩ hbase_le hheap_lim (by have := hgeo64 a b hgeo; omega)` — AH — Q4 re-stated the helper with SCALAR a b (not Ivl), so the k bounds are scalar hypotheses. The call sites: `hmemW_geo _ _ h.geo_out_hdr _ (by omega) (by omega)` — hmm the `_ _ _` are a b inferred from hgeo, and k inferred from... the conclusion — with goal memW post k' = memW u k' — k' := memW u (w_out+16) or similar. And the `by omega` proofs of `a ≤ k` / `k + 8 ≤ a + b` — with a b k as scalars — omega works if the needed inequalities follow from context (e.g., k = w_out+16, a = w_out — wait these involve w_out.toNat + 16 vs a = (memW u (w_out+16))... 

Hmm — for MY calls I need a ≤ k etc. — e.g. h16_mid: k := w_out.toNat + 16, i := (w_out.toNat, 96): need (w_out.toNat, 96).1 ≤ w_out.toNat + 16 — hmm — omega and pair projections of EXPLICIT pairs: I think omega DOES normalize `(a, b).1` to a (it dsimps simple projections — omega's preprocessing includes `simp only [Nat...]`? Not sure). To be safe, state my frame helper with scalar bounds like Q4:

```lean
  have hmemW_frame : ∀ (a b : Nat), Allocated s (a, b) → ∀ k : Nat, a ≤ k → k + 8 ≤ a + b →
      memW mid k = memW s k := by ...
```
Then calls: hmemW_frame w_out.toNat 96 hout_alloc (w_out.toNat + 16) (by omega) (by omega) — omega goals: w_out.toNat ≤ w_out.toNat + 16 ✓ trivial; w_out.toNat + 16 + 8 ≤ w_out.toNat + 96 ✓ trivial ✓.

And for the source header cells: 
```lean
  have h16_mid : memW mid (w_out.toNat + 16) = memW s (w_out.toNat + 16) :=
    hmemW_frame _ _ hout_alloc _ (by omega) (by omega)
```
hmm — with `_ _` for a b — inferred from hout_alloc : Allocated s (w_out.toNat, 96) ✓ a := w_out.toNat, b := 96 ✓; k := w_out.toNat + 16 — inferred from the CONCLUSION type (goal: memW mid (w_out+16) = memW s (w_out+16)) — unifies k ✓. (by omega): w_out.toNat ≤ w_out.toNat + 16 ✓. 

```lean
  have hhd_alloc_mid : Allocated s (memW s (w_out.toNat + 16), 24) := hhd_alloc_s
  have hhd0_mid : memW mid (memW mid (w_out.toNat + 16)) = memW s (memW s (w_out.toNat + 16)) :=
    hmemW_frame _ _ hhd_alloc_s _ (by omega) (by omega)
  have hhd8_mid : memW mid (memW mid (w_out.toNat + 16) + 8) = memW s (memW s (w_out.toNat + 16) + 8) :=
    hmemW_frame _ _ hhd_alloc_s _ (by omega) (by omega)
  have harr_cell_mid : ∀ j, j < nl_w.toNat →
      memW mid (lp_w.toNat + 8 * j) = memW s (lp_w.toNat + 8 * j) := by
    intro j hj
    exact hmemW_frame _ _ ha_arr_s _ (by omega) (by omega)
```
The omegas: header: k := memW s (w_out+16) hmm — wait hhd0_mid's k := memW mid (w_out+16)?? The conclusion: memW mid (memW mid (w_out+16)) = memW s (memW s (w_out+16)) — hmm — the helper concludes memW mid k = memW s k — for the LHS to match, k must be `memW mid (w_out.toNat + 16)` — but the RHS `memW s (memW s (w_out+16))` requires k = memW s (w_out+16) — DIFFERENT! Hmm — the unification would pick k from LHS: memW mid (memW mid (...)) — but then RHS is memW s (memW mid (...)) ≠ memW s (memW s (...)).

Right — I need TWO steps: first h16_mid : memW mid (w_out+16) = memW s (w_out+16), then:
```lean
  have hhd0_mid : memW mid (memW mid (w_out.toNat + 16)) = memW s (memW s (w_out.toNat + 16)) := by
    rw [h16_mid]
    exact hmemW_frame _ _ hhd_alloc_s _ (by omega) (by omega)
```
After rw [h16_mid]: goal `memW mid (memW s (w_out+16)) = memW s (memW s (w_out+16))` — now the helper with k := memW s (w_out+16) ✓ — bounds: memW s (w_out+16) ≤ memW s (w_out+16) — hmm `by omega` — the goal is `memW s (w_out.toNat + 16) ≤ memW s (w_out.toNat + 16)`? omega treats `memW s (w_out.toNat+16)` as an atom — a ≤ a ✓ omega closes (reflexivity) ✓. And k+8 ≤ a+b: memW s (w_out+16) + 8 ≤ memW s (w_out+16) + 24 ✓ omega ✓.

Similarly hhd8_mid:
```lean
  have hhd8_mid : memW mid (memW mid (w_out.toNat + 16) + 8) = memW s (memW s (w_out.toNat + 16) + 8) := by
    have hstep1 : memW mid (memW mid (w_out.toNat + 16) + 8) = memW mid (memW s (w_out.toNat + 16) + 8) := by
      rw [h16_mid]
    rw [hstep1]
    exact hmemW_frame _ _ hhd_alloc_s _ (by omega) (by omega)
```
✓.

harr_cell_mid:
```lean
  have harr_cell_mid : ∀ j, j < nl_w.toNat →
      memW mid (lp_w.toNat + 8 * j) = memW s (lp_w.toNat + 8 * j) := by
    intro j hj
    exact hmemW_frame lp_w.toNat (8 * nl_w.toNat) ha_arr_s (lp_w.toNat + 8 * j) (by omega) (by omega)
```
omega: lp_w.toNat ≤ lp_w.toNat + 8*j ✓; lp_w.toNat + 8*j + 8 ≤ lp_w.toNat + 8*nl_w.toNat — needs 8j + 8 ≤ 8*nl — j < nl ✓ omega (j and nl_w.toNat atoms with hj : j < nl_w.toNat) ✓.

Then mid-level value facts:
```lean
  have hlp_mid : memW mid (memW mid (w_out.toNat + 16)) = lp_w.toNat := by
    rw [hhd0_mid]; exact hlp_eq.symm
  have hnl8_mid : memW mid (memW mid (w_out.toNat + 16) + 8) = nl_w.toNat := by
    rw [hhd8_mid]; exact hnl_eq
  have hnz_mid : memW mid (w_out.toNat + 16) ≠ 0 := by rw [h16_mid]; exact hd_nz
  have hhdw_mid : WordsOK mid (memW mid (w_out.toNat + 16), 24) := by
    rw [h16_mid]  -- hmm — goal WordsOK mid (memW mid (w_out+16), 24) — rw h16_mid rewrites inner ✓
    exact hhdw_s
```
Hmm — rw [h16_mid] rewrites `memW mid (w_out.toNat + 16)` → `memW s (w_out.toNat + 16)` in the goal ✓ — goal WordsOK mid (memW s (w_out+16), 24) — but hhdw_s : WordsOK s (memW s (w_out+16), 24) — DIFFERENT STATE (mid vs s) — NOT the same! WordsOK is state-dependent (memaddrs + memory). FAIL — I don't get WordsOK mid from WordsOK s via memW-equality. Hmm.

But wait — do I need hhdw_mid? What for? p4Q8LogsListOK_store's conclusion rebuilds WordsOK from the OLD state's WordsOK (hw.1, hw.2.1 passed through, hw.2.2 cell-wise transported) — it takes h : LogsListOK t logs at t := mid — hDmid.logs_ok gives that ✓ — I DON'T need WordsOK s at all for the count-store transport. hLL's WordsOK/entries at s are needed ONLY for the value equalities (which I have via hmemW_frame) and geo (state-independent). ✓ Drop hhdw_mid. Wait — hmm, geo_hdr_mid:

```lean
  have geo_hdr_mid : p4Q8OldGeo lw.toNat (memW mid (w_out.toNat + 16), 24) := by
    rw [h16_mid]; exact geo_hdr_s
```
✓.

SECTION 3 — count-store machinery (mid → post):

```lean
  -- the count store: one header-cell write (lw + 8 := nl_w)
  have hhdr_words : WordsOK mid (lw.toNat, 24) :=
    (hobjs_props (lw.toNat, 24) (by rw [hobjs_mid]; simp)).2.1
  have hdom8 : mid.memaddrs (BitVec.ofNat 64 (lw.toNat + 8)) := by
    obtain ⟨u, hd8, _⟩ := hhdr_words.2.2 1 (by norm_num)
    have hz8 : BitVec.ofNat 64 (lw.toNat + 8 * 1) = BitVec.ofNat 64 (lw.toNat + 8) := by
      simp only [Nat.mul_one]
    rwa [hz8] at hd8
  have hst_cnt : @panMemStoresHOL 64 _ (BitVec.ofNat 64 (lw.toNat + 8))
      (flattenHOL (.val (.word nl_w) : ValueHOL 64)) mid.memaddrs
      (fun a => Classical.propDecidable (mid.memaddrs a)) mid.memory
      = some (pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w) :=
    p4Q8_store_word_eq hdom8
  have hflen : (flattenHOL (.val (.word nl_w) : ValueHOL 64)).length = 1 := by simp [flattenHOL]
  have hx8 : BitVec.ofNat 64 (lw.toNat + 8) = lw + BitVec.ofNat 64 8 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    norm_num
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
```
Hmm — let me trace: goal after apply: `(BitVec.ofNat 64 (lw.toNat + 8)).toNat = (lw + BitVec.ofNat 64 8).toNat`.
rw [BitVec.toNat_add] — rewrites the RHS's `(lw + BitVec.ofNat 64 8).toNat` → `(lw.toNat + (BitVec.ofNat 64 8).toNat) % 2^64` ✓ (does LHS have an add? `(BitVec.ofNat 64 (lw.toNat + 8)).toNat` — the + inside is Nat.add of Nats — BitVec.toNat_add is about BitVec.add — pattern `(a + b : BitVec).toNat` — LHS is ofNat applied — no match ✓).
rw [BitVec.toNat_ofNat] — rewrites BOTH `(BitVec.ofNat 64 (lw.toNat+8)).toNat` → `(lw.toNat+8) % 2^64` AND `(BitVec.ofNat 64 8).toNat` → `8 % 2^64` ✓ (rw rewrites all occurrences of the pattern instance? rw [BitVec.toNat_ofNat] with implicit args — first match determines instantiation (n:=64, x:=lw.toNat+8) — then rewrites only THAT instance. The `8` instance remains. Hmm — rw rewrites all occurrences of the pattern AFTER instantiation — the second `(ofNat 64 8).toNat` is a different instance — not rewritten. So then rw [BitVec.toNat_ofNat] again for the 8 — but I can't write the same rw twice cleanly... Actually since I need `8 % 2^64` reduced: `norm_num` handles. Let me simplify:

```lean
  have hx8 : BitVec.ofNat 64 (lw.toNat + 8) = lw + BitVec.ofNat 64 8 := by
    apply BitVec.eq_of_toNat_eq
    have h8t : (BitVec.ofNat 64 8).toNat = 8 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h8t,
      Nat.mod_eq_of_lt (show lw.toNat + 8 < 2 ^ 64 by omega)]
```
Hmm — after simp only [BitVec.toNat_add, BitVec.toNat_ofNat]: LHS = (lw.toNat + 8) % 2^64 — RHS = (lw.toNat + (BitVec.ofNat 64 8).toNat) % 2^64. Hmm — the second toNat_ofNat instance (8) — simp only [BitVec.toNat_ofNat] rewrites ALL instances (simp rewrites repeatedly, all instances) ✓ → RHS = (lw.toNat + 8 % 2^64) % 2^64. Then with h8t : (ofNat 64 8).toNat = 8 — hmm — after toNat_ofNat already rewrote it, h8t is useless. Order: simp only [BitVec.toNat_add] first → RHS (lw.toNat + (ofNat 64 8).toNat) % 2^64. Then simp only [BitVec.toNat_ofNat] → both: LHS (lw.toNat + 8) % 2^64, RHS (lw.toNat + 8 % 2^64) % 2^64. Then `Nat.mod_eq_of_lt (8 < 2^64)` rewrites 8 % 2^64 → 8 (simp lemma form Nat.mod_eq_of_lt needs the hypothesis as simp — provide `(Nat.mod_eq_of_lt (by norm_num : (8:Nat) < 2^64))` as a simp rewrite: 8 % 2^64 = 8 ✓). Then both sides (lw.toNat + 8) % 2^64 — then mod_eq_of_lt for lw.toNat + 8: rewrites → lw.toNat + 8 = lw.toNat + 8 — simp closes rfl ✓.

So:
```lean
  have hx8 : BitVec.ofNat 64 (lw.toNat + 8) = lw + BitVec.ofNat 64 8 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by norm_num : (8 : Nat) < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : lw.toNat + 8 < 2 ^ 64)]
```
Hmm — the last mod_eq_of_lt rewrite: pattern `?a % 2^64` with a < 2^64 — after the 8-reduction, both sides are `(lw.toNat + 8) % 2^64` — simp only with Nat.mod_eq_of_lt h where h : lw.toNat + 8 < 2^64 — the rewrite instance is specific ✓. Order of simp lemma application is unpredictable but should terminate with both sides lw.toNat + 8 ✓. Risk: `(by omega : lw.toNat + 8 < 2^64)` — omega with hlt64 ✓.

Alternatively crib Q2's hdst_eq pattern exactly:
```lean
  have hx8 : BitVec.ofNat 64 (lw.toNat + 8) = lw + BitVec.ofNat 64 8 := by
    apply BitVec.eq_of_toNat_eq
    have hz8 : ((8 : BitVec 64)).toNat = 8 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hz8,
      Nat.mod_eq_of_lt (show lw.toNat + 8 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show (8 : Nat) < 2 ^ 64 by norm_num)]
```
Hmm — hz8 : ((8 : BitVec 64)).toNat = 8 := rfl — but the RHS term is `BitVec.ofNat 64 8` not `8` — elaboration: `(8 : BitVec 64)` elaborates to `BitVec.ofNat 64 8` ✓ same term ✓. But is ((8:BitVec 64)).toNat = 8 rfl? toNat of ofNat = 8 % 2^64 — kernel: 8 % 18446744073709551616 — Nat % on GMP literals — kernel has fast Nat ops? `rfl` on 8 % 2^64 — the kernel evaluates via `Nat.mod` binary rec... hmm — Lean 4's kernel has special support for Nat literals with GMP — `decide (8 % 2^64 = 8)` — kernel Nat.mod with binary literals is supported (kernel byte-level acceleration) ✓ `rfl` should work (Nat.mod is implemented with well-founded recursion but has `@[csimp]`... hmm). Q2's proof used `have hz0 : ((0 : BitVec 64)).toNat = 0 := rfl` ✓ — so `rfl` works for 0; for 8 also ✓ (both reduce via decide inside rfl — GMP-accelerated). Fine.

Actually simpler — I'll use exactly the hdst_eq pattern from Q2's p4Q8_eval_var_add_const:

```lean
  have hdst8 : lw + (BitVec.ofNat 64 8 + (0 : BitVec 64)) = BitVec.ofNat 64 (lw.toNat + 8) := by
    apply BitVec.eq_of_toNat_eq
    have hz0 : ((0 : BitVec 64)).toNat = 0 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hz0, Nat.add_zero,
      Nat.mod_eq_of_lt (by norm_num : (8 : Nat) < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : lw.toNat + 8 < 2 ^ 64)]
  have hx8 : BitVec.ofNat 64 (lw.toNat + 8) = lw + BitVec.ofNat 64 8 := by
    rw [hdst8, BitVec.add_zero]
```
Hmm — `BitVec.ofNat 64 8 + (0 : BitVec 64)` — hx8's RHS is `lw + BitVec.ofNat 64 8` (no +0). I could just state hdst8 : BitVec.ofNat 64 (lw.toNat + 8) = lw + BitVec.ofNat 64 8 directly with the simp-only proof:
```lean
  have hx8 : BitVec.ofNat 64 (lw.toNat + 8) = lw + BitVec.ofNat 64 8 := by
    apply BitVec.eq_of_toNat_eq
    have h8v : ((8 : BitVec 64)).toNat = 8 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h8v,
      Nat.mod_eq_of_lt (by omega : lw.toNat + 8 < 2 ^ 64),
      Nat.mod_eq_of_lt (by norm_num : (8 : Nat) < 2 ^ 64)]
```
Trace: goal `(ofNat 64 (lw.toNat+8)).toNat = (lw + ofNat 64 8).toNat`. simp only [BitVec.toNat_add] → LHS unchanged, RHS → (lw.toNat + (ofNat 64 8).toNat) % 2^64. simp only [BitVec.toNat_ofNat] → LHS → (lw.toNat + 8) % 2^64; the inner (ofNat 64 8).toNat → 8 % 2^64 ✓ RHS → (lw.toNat + 8 % 2^64) % 2^64. h8v — pattern ((8:BitVec 64)).toNat — already rewritten — no-op. Nat.mod_eq_of_lt (8 < 2^64): rewrites 8 % 2^64 → 8 ✓ RHS → (lw.toNat + 8) % 2^64. Nat.mod_eq_of_lt (lw+8 < 2^64): rewrites (lw.toNat + 8) % 2^64 → lw.toNat + 8 — BOTH sides ✓ → goal lw.toNat + 8 = lw.toNat + 8 — simp only closes rfl ✓. 

Hmm — wait: simp only [BitVec.toNat_add] — its statement: (a + b).toNat = (a.toNat + b.toNat) % 2^n — for width 64. Fine.

Also — potential issue: `BitVec.toNat_ofNat` name — is it `BitVec.toNat_ofNat`? In recent Batteries: `theorem BitVec.toNat_ofNat {n : Nat} (x : Nat) : (BitVec.ofNat n x).toNat = x % 2^n` ✓ (used in Q3/Q4 code above ✓).

```lean
  have hbase8 : lw.toNat % 8 = 0 := hlw_al
  have hsz8 : (24 : Nat) % 8 = 0 := by decide
  have hoff8 : (8 : Nat) % 8 = 0 := by decide
  have hsz0 : (0 : Nat) < 24 := by decide
  have hin_blk : Inside (lw.toNat, 24) sourceBase (globN mid "heap_ptr") :=
    ⟨hArenaOKmid.1, by rw [hgl_mid]; omega⟩
```
Hmm — Inside (lw,24) sourceBase (globN mid hp) — components: sourceBase ≤ (lw,24).1 = lw.toNat ✓ hArenaOKmid.1 (ArenaOK mid .1 : sourceBase ≤ globN mid hp — wait NO — ArenaOK's first conjunct is sourceBase ≤ globN s "heap_ptr" — NOT sourceBase ≤ lw! Hmm!! I need sourceBase ≤ lw.toNat. From ArenaOK mid: sourceBase ≤ globN mid hp = lw+24+8cap ≥ lw — that gives sourceBase ≤ lw+24+8cap, and I need sourceBase ≤ lw — NOT directly!

Hmm. Where does sourceBase ≤ lw come from? ArenaOK s: sourceBase ≤ globN s hp = lw ✓!! hArenaOK_s.1 : sourceBase ≤ globN s "heap_ptr" — with hlw_eq : lw.toNat = globN s "heap_ptr" — so sourceBase ≤ lw.toNat ✓. So:
```lean
  have hlw_ge : sourceBase ≤ lw.toNat := by rw [hlw_eq]; exact hArenaOK_s.1
```
hmm — goal sourceBase ≤ lw.toNat — rw [hlw_eq] rewrites lw.toNat → globN s hp ✓ goal sourceBase ≤ globN s "heap_ptr" = hArenaOK_s.1 ✓.

And hin_blk := ⟨hlw_ge, by rw [hgl_mid]; omega⟩ — second: (lw,24).1 + (lw,24).2 ≤ globN mid hp — after rw [hgl_mid] the goal becomes lw.toNat + 24 ≤ lw.toNat + 24 + 8*capw.toNat — omega ✓. Hmm — the goal `(lw.toNat, 24).1 + (lw.toNat, 24).2 ≤ globN mid "heap_ptr"` — rw [hgl_mid] rewrites globN mid hp → the sum ✓. But the pair projections — omega needs them reduced — the goal after rw is `(lw.toNat, 24).1 + (lw.toNat, 24).2 ≤ lw.toNat + 24 + 8 * capw.toNat` — hmm — `(lw.toNat, 24).1` — does omega reduce pair projections of explicit pairs? I believe omega's pre-processing handles structure eta/projections of constructors — actually omega does `dsimp only` with some lemmas... In Q4: `have hin_blk : Inside (lw.toNat + 24, 8 * capw.toNat) sourceBase (globN u "heap_ptr") := by unfold Inside; dsimp only; rw [h.heap_fr]; omega` — they did `unfold Inside; dsimp only` FIRST to reduce the projections, then rw, then omega ✓. I'll do the same:
```lean
  have hin_blk : Inside (lw.toNat, 24) sourceBase (globN mid "heap_ptr") := by
    refine ⟨hlw_ge, ?_⟩
    dsimp only
    rw [hgl_mid]
    omega
```
Hmm — goal after refine: `(lw.toNat, 24).1 + (lw.toNat, 24).2 ≤ globN mid "heap_ptr"` — dsimp only reduces projections → `lw.toNat + 24 ≤ globN mid "heap_ptr"` ✓ — rw [hgl_mid] → `lw.toNat + 24 ≤ lw.toNat + 24 + 8 * capw.toNat` ✓ omega ✓.

Wait — also the anonymous ⟨hlw_ge, ?_⟩ against Inside — expected type Inside — whnf → And ✓ anonymous constructor works ✓ (Q2 does `refine Or.inl ⟨h.1, ?_⟩` where the target is Inside ✓).

Now the WorldStep and effects:
```lean
  have hstep_cnt : WorldStep (fun _ => [(lw.toNat, 24)]) [] stdKeep NoExtra mid none
      {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w} :=
    worldStep_store_in_block hDmid.base.world rfl hbase8 hsz8 hoff8 hin_blk hx8
      (by rw [hflen]; omega) hst_cnt
```
worldStep_store_in_block's premises: (hW) (hbase_lu : w_base.toNat = base) (hbase8) (_hsz8) (_hoff8) (hin_blk) (hx_eq : x = w_base + BitVec.ofNat 64 off) (hoff_fit : off + 8 * (flattenHOL v).length ≤ sz) (hst). With w_base := lw, base := lw.toNat: hbase_lu : lw.toNat = lw.toNat := rfl ✓. hx_eq : x = lw + BitVec.ofNat 64 8 — with x := BitVec.ofNat 64 (lw.toNat+8) — hx8 : BitVec.ofNat 64 (lw.toNat+8) = lw + BitVec.ofNat 64 8 ✓. hoff_fit : 8 + 8 * (flattenHOL (.val (.word nl_w))).length ≤ 24 — by rw [hflen]; omega — goal 8 + 8 * 1 ≤ 24 — after rw [hflen]: `8 + 8 * 1 ≤ 24` — omega ✓.

Hmm — the hst premise of worldStep_store_in_block: `@panMemStoresHOL 64 _ x (flattenHOL v) s.memaddrs (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem'` — with v := (.val (.word nl_w) : ValueHOL 64) ✓ hst_cnt matches ✓ (v implicit — inferred from hst's flattenHOL v — my hst_cnt has flattenHOL (.val (.word nl_w) : ValueHOL 64) ✓ same).

Implicit inference: x, w_base, base, sz, off, v, mem' — from hst_cnt and the explicit args... hW : WorldOK mid (t := mid from hW). hbase_lu : lw.toNat = lw.toNat — base := lw.toNat, w_base := lw. hin_blk : Inside (base, sz) sourceBase (globN mid "heap_ptr") — with base := lw.toNat, sz := 24 ✓ (I state hin_blk at (lw.toNat, 24) ✓). hx_eq : x = w_base + ofNat off — off := 8 — from hx8 ✓ x := ofNat (lw+8) ✓. ✓.

```lean
  have hAR_post : ArenaReady {mid with memory :=
      pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w} := hstep_cnt.1
  have hcode_post : {mid with memory :=
      pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}.code = originalRuntimeCode :=
    hcmid
  obtain ⟨hcell_cnt, hEff_cnt⟩ := p4Q8_store_effect
    (t := mid) (base := lw.toNat) (sz := 24) (off := 8) (w_base := lw)
    (x := BitVec.ofNat 64 (lw.toNat + 8)) (v := (.val (.word nl_w) : ValueHOL 64))
    (mem' := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w)
    hDmid.base.world hAR_post hcode_post rfl hbase8 hsz0 hsz8 hin_blk hx8
    (by rw [hflen]; omega) hst_cnt
```
p4Q8_store_effect's premises: (hW : WorldOK t) (hAR : ArenaReady {t with memory := mem'}) (hcode : {t with memory := mem'}.code = originalRuntimeCode) (hbase_lu : w_base.toNat = base) (hbase8 : base % 8 = 0) (hsz0 : 0 < sz) (hsz8 : sz % 8 = 0) (hin_blk) (hx_eq) (hoff_fit) (hst). ✓ — hcode_post via hcmid defeq — will `have hcode_post : ... := hcmid` typecheck? {mid with memory := ...}.code — projection of structure-update reduces to mid.code ✓ defeq — `:= hcmid` — elaborator checks defeq ✓.

Hmm — wait, actually — simpler: pass hcmid directly as the hcode argument (defeq-checked at application) ✓. But the `have hcode_post` version is also fine. I'll pass hcmid directly to reduce clutter. Actually — for p4Q8_store_effect, Q4 passed `hcode_u'` which they made via `have ... := h.code`. Both fine.

Chain store:
```lean
  -- the chain and base across the count store
  have hhp_ent_lw : globN entry "heap_ptr" ≤ lw.toNat := by
    rw [hlw_eq]
    exact h.base.heap_entry
  have hhp_s_mid : globN s "heap_ptr" ≤ globN mid "heap_ptr" := by
    rw [← hlw_eq, hgl_mid]
    omega
  have hchain_mid : p4Q8Chain entry s_pmc w_out lw capw mid := p4Q8Chain_of_bundle hchain0
```
Hmm — p4Q8Chain_of_bundle hbundle — the bundle must match hchain0's type EXACTLY (defeq ok). hchain0's shape (from stableLogs_alloc's htail premise): the ∃-bundle — p4Q8Chain_of_bundle's hbundle: `∀ S0 Nd0 : List Nat, WorldTypedWith entry S0 Nd0 → IvlsDisj (ptxRegions entry) (worldTypedIvls entry S0 Nd0) → ∃ S_pmc' Nd_pmc' S_new Nd_new : List Nat, WorldTypedWith s_pmc S_pmc' Nd_pmc' ∧ (∀ t' ∈ S0, t' ∈ S_new) ∧ WorldTypedWith mid S_new Nd_new ∧ OwnedGrows s_pmc mid ... ∧ OwnedGrows entry mid ... ∧ FrameOutside entry mid ... ∧ (∀ o ∈ worldOwned mid S_new Nd_new, Disj (w_out.toNat, 96) o) ∧ IvlsDisj [...] (worldOwned mid S_new Nd_new) ∧ PmcLogsLiveOwned mid S_new Nd_new (memW mid (w_out.toNat + 16)) ∧ PmcLogsLiveOwned mid S_new Nd_new lw.toNat` — versus hchain0 — let me compare from the dump: ✓ identical (I compared earlier — the last conjunct: hchain0 has `PmcLogsLiveOwned mid S_new Nd_new lw.toNat` ✓ matches).

Wait — actually p4Q8Chain_of_bundle is designed EXACTLY for this ✓ (used for the count store per its docstring "shared by the count store and the copy loop").

```lean
  have hR_fresh : Inside (lw.toNat, 24) (globN entry "heap_ptr") (globN mid "heap_ptr") :=
    ⟨hhp_ent_lw, by rw [hgl_mid]; omega⟩
```
Components: globN entry hp ≤ (lw,24).1 ✓; (lw,24).1 + .2 ≤ globN mid hp — rw [hgl_mid] → lw+24 ≤ lw+24+8cap omega ✓.

```lean
  have hRh : Disj (memW mid (w_out.toNat + 16), 24) (lw.toNat, 24) :=
    p4Q8OldGeo_disj geo_hdr_mid (le_refl _) hheap_lim
```
Hmm — p4Q8OldGeo_disj's signature: (hgeo : p4Q8OldGeo lw i) (hbase : lw ≤ base) (hin : base + sz ≤ heapLimit) : Disj i (base, sz) — hbase : lw.toNat ≤ lw.toNat — `le_refl _` — hmm — for Nat, `le_refl` — `Nat.le_refl _` ✓ or `(by omega)`. I'll use `(le_refl _)`.

```lean
  have hRa : memW mid (w_out.toNat + 16) ≠ 0 →
      Disj (memW mid (memW mid (w_out.toNat + 16)),
        8 * memW mid (memW mid (w_out.toNat + 16) + 8)) (lw.toNat, 24) := by
    intro _
    rw [hlp_mid, hnl8_mid]
    exact p4Q8OldGeo_disj geo_arr_s (le_refl _) hheap_lim
  have hRe : memW mid (w_out.toNat + 16) ≠ 0 → ∀ i, i < memW mid (memW mid (w_out.toNat + 16) + 8) →
      Disj (memW mid (memW mid (memW mid (w_out.toNat + 16)) + 8 * i), 40) (lw.toNat, 24) := by
    intro _ i hi
    rw [hnl8_mid] at hi
    rw [hlp_mid]
    exact p4Q8OldGeo_disj (hent_geo_s i hi) (le_refl _) hheap_lim
```
Hmm — hRe: goal after intro: Disj (memW mid (memW mid (memW mid (w_out+16)) + 8*i), 40) (lw,24) — rw [hlp_mid] rewrites `memW mid (memW mid (w_out.toNat + 16))` → lp_w.toNat — the term `memW mid (memW mid (memW mid (w_out+16)) + 8*i)` — hmm — the pattern `memW mid (memW mid (w_out+16))` — is it a subterm? The term is memW mid (X + 8*i) where X = memW mid (memW mid (w_out+16)) — YES X matches ✓ → becomes memW mid (lp_w.toNat + 8*i) ✓ — then p4Q8OldGeo_disj (hent_geo_s i hi) — hent_geo_s i hi : p4Q8OldGeo lw.toNat (memW s (lp_w.toNat + 8*i), 40) — BUT the goal after rw is about memW MID (lp+8i) — MISMATCH (mid vs s)!! p4Q8OldGeo is state-independent but the VALUES differ: memW mid (lp+8i) vs memW s (lp+8i) — equal via harr_cell_mid but not syntactically!

Fix: rw [hlp_mid, harr_cell_mid i hi] — harr_cell_mid i hi : memW mid (lp_w.toNat + 8*i) = memW s (lp_w.toNat + 8*i) — rewrites → memW s (lp+8i) ✓ then exact p4Q8OldGeo_disj (hent_geo_s i hi) ✓. But careful — after `rw [hlp_mid]`, the term is `memW mid (lp_w.toNat + 8 * i)` — harr_cell_mid i hi's LHS pattern `memW mid (lp_w.toNat + 8 * j)` with j := i ✓ matches ✓.

So hRe: `rw [hlp_mid, harr_cell_mid i hi]` — hmm wait — rw with multiple lemmas: rw [a, b] applies a then b ✓.

Similarly hRa: after rw [hlp_mid, hnl8_mid]: Disj (lp_w.toNat, 8 * nl_w.toNat) (lw.toNat, 24) — geo_arr_s : p4Q8OldGeo lw.toNat (lp_w.toNat, 8*nl_w.toNat) ✓ — p4Q8OldGeo_disj geo_arr_s — wait — p4Q8OldGeo_disj : Disj i (base, sz) — from geo of i — here i := (lp_w.toNat, 8*nl_w.toNat) ✓ ✓.

```lean
  have hw_out_blk : Disj (w_out.toNat, 96) (lw.toNat, 24) := by
    refine Or.inr (Or.inr (Or.inl ?_))
    dsimp only
    omega
```
Third disjunct: i.1 + i.2 ≤ j.1 — (w_out,96).1 + (w_out,96).2 ≤ (lw,24).1 — after Or.inl with goal w_out.toNat + 96 ≤ lw.toNat — dsimp only (reduce projections) then omega (hwout in context ✓). Hmm — Q4's version: `refine Or.inr (Or.inr (Or.inl ?_)); dsimp only; omega` — hmm — wait Q4's hw_out_blk for block (lw+24, 8cap): used `dsimp only; omega` with houtbelow in context ✓. Mine: hwout : w_out.toNat + 96 ≤ lw.toNat ✓ omega. Hmm — actually after `refine Or.inr (Or.inr (Or.inl ?_))` the goal is `(w_out.toNat, 96).1 + (w_out.toNat, 96).2 ≤ (lw.toNat, 24).1` — dsimp only reduces pair projections ✓ → w_out.toNat + 96 ≤ lw.toNat — omega ✓.

```lean
  have hchain_post : p4Q8Chain entry s_pmc w_out lw capw
      {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w} :=
    p4Q8Chain_store hchain_mid hDmid.base.world (Nat.le_trans hDmid.heap_pmc hhp_s_mid)
      (Nat.le_trans hDmid.base.heap_entry hhp_s_mid) hDmid.base.frame_entry
      hDmid.base.scratch_entry h.base.arena_entry hR_fresh rfl hbase8 hsz8 hoff8 hin_blk
      hx8 (by rw [hflen]; omega) hst_cnt (Or.inl rfl) hDmid.out_words.1 hDmid.out_words
      hDmid.out_inside hw_out_blk hDmid.logs_ok hRh hRa hRe
```
Wait — p4Q8Chain_store's premise order: (h) (hW) (hhp_pmc) (hhp_ent) (hfp_ent) (hsp_ent) (hAR_ent) (hR_fresh) (hbase_lu) (hbase8) (hsz8) (hoff8) (hin_blk) (hx_eq) (hoff_fit) (hst) (hblk) (hw_out8) (hout_words) (hout_inside) (hw_out_blk) (hlogs_list) (hRh) (hRa) (hRe) ✓ matches.

- hbase_lu : w_base.toNat = base → lw.toNat = lw.toNat := rfl ✓.
- hw_out8 : w_out.toNat % 8 = 0 := hDmid.out_words.1 ✓ (WordsOK's first conjunct).

```lean
  have hbo_unhit : PtxBlockOutUnhit mid {mid with memory :=
      pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w} :=
    p4Q8_blockOutUnhit_store hchain_mid hDmid.base.ready_entry (Or.inl rfl) hARmid hEff_cnt
  have hcells_post : PtxBoCells true entry mid {mid with memory :=
      pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w} :=
    p4Q8_boCells_store hDmid.base hchain_mid (Or.inl rfl) hsz0 hstep_cnt hbo_unhit
  have hbase_post : PtxRelBase true entry {mid with memory :=
      pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w} :=
    p4Q8Base_store hDmid.base hchain_mid hchain_post (Or.inl rfl) hsz0 hstep_cnt hcells_post
```
✓ (p4Q8_boCells_store's premise order: (hbase) (hchain) (hblk) (hsz0) (hstep) (hbo_unhit) ✓; p4Q8Base_store: (hbase) (hchain_t) (hchain) (hblk) (hsz0) (hstep) (hcells) ✓; p4Q8_blockOutUnhit_store: (hchain) (hready) (hblk) (hAR : ArenaReady t) (hEff) ✓ — hARmid : ArenaReady mid ✓).

SECTION 4 — apply tailSetup:
```lean
  have hnl_mid : mid.locals.lookup (ofString "nl") = some (.val (.word nl_w)) := by
    rw [hlocl (ofString "nl") (by decide) (by decide)]
    exact hnl
  refine p4Q8_tailSetup tail hnl_mid hlocm hhdr_words (by omega) hw0' ?_
```
hlw64 : lw.toNat + 24 ≤ 2^64 — by omega (hlt64 ✓).

After this the goal: PtxRelRunStrong entry tail (setVarHOLFinite (ofString "i") (.val (.word 0x0#64)) (setVarHOLFinite (ofString "stable_lp") (.val (.word w_lp)) {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w})).

SECTION 5 — the loop invariant at t0.

```lean
  set post : PanSemStateFiniteExact 64 F :=
    {mid with memory := (pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w)} with hpost
```
Hmm — `set X := e with h` gives h : X = e. Fine. After set, the goal becomes PtxRelRunStrong entry tail (setVar ... (setVar ... post)).

Hmm — actually is `set` going to abstract inside hypotheses too? `set` abstracts occurrences everywhere (goal and all hypotheses) by default? In Lean 4 Mathlib, `set x := e with h` introduces a local definition and replaces occurrences of e in the GOAL only (I believe it's goal-only by default... actually Mathlib's `set` replaces in all hypotheses and the goal by default? The doc: "set a := e with h introduces a : T := e and replaces e by a in the goal and all hypotheses" — hmm, I think Mathlib set replaces in goal AND hypotheses. There's `set!`... The `set` tactic: "like `let` but replaces occurrences". Default: replaces in goal and hypotheses? Mathlib's set has `(~.replace_all)`... I recall set replaces everywhere (goal + hyps). That's fine for me (post appears only in the goal anyway).

Then:
```lean
  refine p4Q8_loop38 (rest := tail) ⟨?base, ?chain, ...⟩ ?_
```
Hmm — the 35-field anonymous constructor with ?-placeholders is awkward. Better: build the invariant as a have first, then refine:

```lean
  have hINV : P4Q8Loop entry s_pmc w_out lw capw nl_w w_lp lp_w
      0x0000000000000000#64
      (setVarHOLFinite (ofString "i") (.val (.word 0x0000000000000000#64))
        (setVarHOLFinite (ofString "stable_lp") (.val (.word w_lp)) post)) := by
    ...
  refine p4Q8_loop38 (rest := tail) hINV ?_
  intro t' i_w hinv hcond
  exact htail lw capw w_lp t' i_w hinv hcond
```

Hmm — wait — the goal after tailSetup is PtxRelRunStrong entry tail (setVar ... post-term) — with `set post`, the goal shows `setVarHOLFinite (ofString "i") ... (setVarHOLFinite (ofString "stable_lp") ... post)`. And p4Q8_loop38's hINV : P4Q8Loop entry s_pmc w_out lw capw nl_w w_lp lp_w 0x0#64 t — t := that state ✓.

But hold on — `refine p4Q8_loop38 (rest := tail) hINV ?_` — p4Q8_loop38's conclusion: PtxRelRunStrong entry (.seq (.while p4Loop38Cond p4Loop38Body) rest) t — the GOAL is PtxRelRunStrong entry tail (state) — MISMATCH! The goal IS just `tail` — not `.seq (.while ...) tail`!!

RIGHT — because REST2 (what I passed to tailSetup) = `(.seq (.while p4Loop38Cond p4Loop38Body) tail)`. Hmm wait — let me redo: tailSetup's `tail` parameter is REST2 := (.seq (.while p4Loop38Cond p4Loop38Body) tail). Then tailSetup's htail premise: PtxRelRunStrong entry REST2 t0. So after `refine p4Q8_tailSetup REST2 hnl_mid hlocm hhdr_words (by omega) hw0' ?_` — the goal is PtxRelRunStrong entry REST2 t0-full-term — where REST2 = .seq (.while p4Loop38Cond p4Loop38Body) tail ✓. THEN p4Q8_loop38 with rest := tail: conclusion PtxRelRunStrong entry (.seq (.while p4Loop38Cond p4Loop38Body) tail) t — matches goal ✓✓.

So I pass REST2 to tailSetup. ✓.

Now the invariant construction — full assembly:

```lean
    -- locals of t0
    have hlu_i : (setVarHOLFinite (ofString "i") (.val (.word 0x0000000000000000#64))
        (setVarHOLFinite (ofString "stable_lp") (.val (.word w_lp)) post)).locals.lookup
        (ofString "i") = some (.val (.word 0x0000000000000000#64)) := by
      simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
```
Hmm — HolFiniteMapExact.update — wait, Q3 used `simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]` for hs1lu and `simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]` in Q4. The locals.update — setVarHOLFinite's def: `{state with locals := state.locals.update (name, value)}` — hmm — from my summary: `setVarHOLFinite name value state = {state with locals := state.locals.update (name, value)}` — the update on HolFiniteMapExact — is `.update` a field/function? The simp lemmas: FUPDATE etc. Since Q3/Q4 patterns worked, I'll crib: for the self-lookup use `simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]`; for others `simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hy, Ne.symm hy]`.

Hmm — for the double update (i over stable_lp):
- lookup "i" (the outer update's name): after unfolding both setVars: `(((post.locals.update (sl, v_lp)).update (i, v0)).lookup (ofString "i")` — the last update wins → v0 ✓ — simp should chain both FUPDATEs ✓.
- lookup "stable_lp": the outer update (i ≠ stable_lp) keeps, inner update wins ✓ — simp with disequalities: ofString "i" ≠ ofString "stable_lp" — simp can decide `ofString "stable_lp" = ofString "i"` is False (string literals) — decide ✓ automatic.
- lookup name (name ≠ i, ≠ stable_lp): both updates keep ✓ — needs the name disequalities provided.

So:
```lean
    have hlu_i : ... lookup (ofString "i") = some (.val (.word 0x0#64)) := by
      simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
    have hlu_slp : ... lookup (ofString "stable_lp") = some (.val (.word w_lp)) := by
      simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
    have hlu_others : ∀ (name : String), ofString name ≠ ofString "i" →
        ofString name ≠ ofString "stable_lp" →
        (setVarHOLFinite (ofString "i") (.val (.word 0x0#64))
          (setVarHOLFinite (ofString "stable_lp") (.val (.word w_lp)) post)).locals.lookup
          (ofString name) = post.locals.lookup (ofString name) := by
      intro name h1 h2
      simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, h1, h2]
      -- potential leftover: ofString name = ofString "stable_lp" or = "i" — handle:
      intro hcon
      ...
```
Hmm — the leftover shape is uncertain. Q4's single-update version:
```lean
    intro name hne
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
    intro hcon
    exact absurd hcon.symm hne
```
So after simp there was ONE leftover goal `ofString name = ofString "i"` (introduced by FUPDATE's ite — simp leaves `if ofString name = ofString "i" then ... else ...` and can't reduce — hmm no — with hne in the simp set, the `if` reduces → but then why `intro hcon`? Because simp [hne] — hne : ofString name ≠ ofString "i" — as a simp lemma this rewrites `ofString name = ofString "i"` → False → if_neg... hmm — the leftover was probably `¬(ofString name = ofString "i")` — wait the `intro hcon; exact absurd hcon.symm hne` — hcon : ofString "i" = ofString name — absurd against hne : ofString name ≠ ofString "i" — hcon.symm : ofString name = ofString "i" — absurd hcon.symm hne ✓. So the leftover goal was `ofString "i" = ofString name` — probably from `ite` condition not discharged.

For my double version, the leftover might be a disjunction or two separate goals. I'll write it defensively:
```lean
      intro hcon
      rcases hcon with hc | hc
      · exact absurd hc.symm h2
      · exact absurd hc.symm h1
```
Hmm — but if the leftover is a single eq I break. Alternative — avoid the leftover problem: do the rewrite in two single steps, each following Q4's exact pattern:

Step A (outer update, name ≠ "i"):
```lean
    have hluA : ∀ y : MlS, y ≠ ofString "i" →
        (setVarHOLFinite (ofString "i") (.val (.word 0x0#64))
          (setVarHOLFinite (ofString "stable_lp") (.val (.word w_lp)) post)).locals.lookup y =
        (setVarHOLFinite (ofString "stable_lp") (.val (.word w_lp)) post).locals.lookup y := by
      intro y hy
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hy]
      intro hcon
      exact absurd hcon.symm hy
```
Hmm wait — Q4's pattern used `simp [..., hne]` where hne : ofString name ≠ ofString "i" and goal about `lookup (ofString name)`. Here I quantify y : MlS with hy : y ≠ ofString "i" — the simp set [hy] — hy's LHS `y ≠ ofString "i"` — as simp lemma — Ne is a Prop — simp uses it via... hmm — Q4 used `simp [..., hne]` where hne : ofString name ≠ ofString "i"` ✓ same shape ✓. And leftover `intro hcon; exact absurd hcon.symm hne` — hcon : ofString "i" = ofString name — hmm — or `ofString "i" = y`? Since I quantified y : MlS (general), the leftover would be `ofString "i" = y` — `hcon.symm : y = ofString "i"` — absurd hcon.symm hy ✓ (hy : y ≠ ofString "i") ✓.

Step B (inner update, y = "stable_lp" or y ≠ "stable_lp"):
```lean
    have hluB_slp : (setVarHOLFinite (ofString "stable_lp") (.val (.word w_lp)) post).locals.lookup
        (ofString "stable_lp") = some (.val (.word w_lp)) := by
      simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
    have hluB_other : ∀ y : MlS, y ≠ ofString "stable_lp" →
        (setVarHOLFinite (ofString "stable_lp") (.val (.word w_lp)) post).locals.lookup y =
        post.locals.lookup y := by
      intro y hy
      simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hy]
      intro hcon
      exact absurd hcon.symm hy
```
Hmm — wait — for hluB_other the simp set — Q3's hs1fr used `simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hy, Ne.symm hy]` — with BOTH hy and Ne.symm hy. The leftover handling differs. Ugh — the exact simp behavior is hard to predict without running. I'll write my best guess and iterate on errors — that's the workflow anyway.

Then:
- hlu_i : lookup "i" — direct self-update of outer:
```lean
    have hlu_i : (setVarHOLFinite (ofString "i") (.val (.word 0x0#64)) (setVar... post)).locals.lookup
        (ofString "i") = some (.val (.word 0x0#64)) := by
      simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
```
- hlu_slp : lookup "stable_lp" = some (.val (.word w_lp)) := hluA (ofString "stable_lp") (by decide) |>.trans (hluB_slp) — hmm — hluA applied at y := ofString "stable_lp" with hy : ofString "stable_lp" ≠ ofString "i" (by decide ✓ string literals) — gives lookup at outer = lookup at inner; then .trans hluB_slp ✓. In term mode: `(hluA (ofString "stable_lp") (by decide)).trans hluB_slp`.
- hlu_other name (hne_i, hne_slp) : lookup name = post.locals.lookup name := (hluA (ofString name) hne_i').trans (hluB_other (ofString name) hne_slp') — where hne_i' : ofString name ≠ ofString "i" ✓ directly; hne_slp' : ofString name ≠ ofString "stable_lp" ✓.

Then the fields:
```lean
    refine ⟨hbase_t0, hchain_t0, hbase_t0.world, hcmid_defeq?, hlw_al, hlw_ge, hhp_ent_lw, hcap1, hnlcap, hnl28, hwlp_nat, hlim64, hheap_fr, hDmid.heap_pmc, ...⟩
```
- code field: t0.code = originalRuntimeCode — hcmid : mid.code = originalRuntimeCode — t0.code ≡ mid.code — `exact hcmid` in the anonymous constructor — defeq-checked ✓. Hmm — actually inside `refine ⟨...⟩` each field's expected type is known — providing hcmid for `t0.code = originalRuntimeCode` — t0 = setVar ... post — t0.code reduces: setVarHOLFinite n v s = {s with locals := ...} — .code of that = s.code — reduces through both ✓ defeq ✓.
- heap_fr : globN t0 "heap_ptr" = lw.toNat + 24 + 8*capw.toNat — globN t0 — globN s n := match s.globals.lookup ... — t0.globals ≡ mid.globals ✓ hgl_mid defeq ✓ — provide hgl_mid ✓.
- heap_pmc : globN s_pmc "heap_ptr" ≤ globN t0 "heap_ptr" — hDmid.heap_pmc : globN s_pmc hp ≤ globN mid hp — defeq ✓.
- out_words : pmc_wordsOK_updW mid (BitVec.ofNat 64 (lw.toNat + 8)) nl_w (w_out.toNat, 96) hDmid.out_words : WordsOK {mid with memory := pmcUpdW ...} (w_out, 96) — target WordsOK t0 (w_out, 96) — defeq ✓.
- out_inside : hDmid.out_inside — globN t0 ≡ globN mid ✓ defeq ✓.
- out_below : hwout ✓.
- marks : the transported version.
- src_nz / src_logs / src_lp_eq / src_len / geo_out_hdr / geo_out_arr / src_ent as designed.
- hdr_words : pmc_wordsOK_updW mid (BitVec.ofNat 64 (lw.toNat + 8)) nl_w (lw.toNat, 24) hhdr_words ✓.
- arr_words : pmc_wordsOK_updW mid ... (lw.toNat + 24, 8 * capw.toNat) — source: WordsOK mid (lw.toNat + 24, 8*capw.toNat) — from hobjs_props second element: (hobjs_props (lw.toNat + 24, 8 * capw.toNat) (by rw [hobjs_mid]; simp)).2.1 ✓.
- i_le : (0x0#64).toNat ≤ nl_w.toNat — by simp? BitVec.toNat of 0 literal = 0 — `by simp` or `by decide`? — hmm — (BitVec.ofNat 64 0).toNat = 0 % 2^64 = 0 — `Nat.zero_le _` after toNat-zero — Q4's pattern for such: in p4Q8Loop_store's i_le field: `by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]; have hile := hmem.i_le; omega` — for 0: `by simp` — Let me write `by decide`? toNat of 0#64 — decide on `0 % 2^64 ≤ nl_w.toNat` — nl_w.toNat is a VARIABLE — decide FAILS. omega? — goal (0x0#64).toNat ≤ nl_w.toNat — omega with BitVec literal — omega handles BitVec.toNat? "omega has BitVec.toNat < 2^64 built in" — hmm — for literal 0#64 — omega normalizes BitVec.toNat of literals? Risky. Write: `Nat.zero_le _`? — goal is `(0x0000000000000000#64 : BitVec 64).toNat ≤ nl_w.toNat` — provide `Nat.zero_le nl_w.toNat` — defeq? (0#64).toNat — is it defeq to 0? BitVec.ofNat 64 0 — mk ofFin 0 — toNat = 0 % 2^64 — `0 % n` reduces to 0 by rfl? Nat.mod 0 n — Nat.mod is defined by recursion on n... `Nat.mod_eq_of_lt` — hmm — (0 % 2^64) — kernel: Nat.mod 0 m = 0 — `rfl` ✓ (0 % m reduces: Nat.mod n m recurses on n — 0 case → 0 ✓). So (0#64).toNat ≡ 0 definitionally ✓ — `Nat.zero_le _` typechecks by defeq ✓. Or `by simp`. I'll use `Nat.zero_le _`.
- copied : ∀ j, j < (0x0#64).toNat → ... — `fun j hj => absurd hj (by decide)`? — j < 0 is False — hmm — `fun j hj => by simp at hj` — hj : j < (0#64).toNat — simp at hj — reduces to j < 0 → False — then goal anything — exact absurd — `by simp at hj` — after simp hj : False ✓ closes any goal? `simp at hj` turns hj into False and closes the goal ✓ (simp derives False and closes). Write `fun j hj => by simp at hj` — hmm — if simp doesn't reduce (0#64).toNat... `by have : (0x0000000000000000#64 : BitVec 64).toNat = 0 := rfl; omega` — safe: `fun j hj => by simp only [show ((0x0000000000000000#64 : BitVec 64)).toNat = 0 from rfl] at hj; omega`? hmm — omega on j < 0 → False ✓. Or simplest: `fun j hj => absurd hj (Nat.not_lt_zero j)` — hj : j < (0#64).toNat — Nat.not_lt_zero j : ¬ j < 0 — need (0#64).toNat ≡ 0 defeq — absurd hj (Nat.not_lt_zero j) — absurd (h : a) (h' : ¬a) — needs the types defeq — ¬(j < (0#64).toNat) vs ¬(j < 0) — defeq ✓. I'll use `fun j hj => absurd hj (Nat.not_lt_zero j)` — hmm — Nat.not_lt_zero : ∀ (n : Nat), ¬n < 0 ✓.

For src_nz etc., the t0-memW equalities:
```lean
    -- count-store transports to t0's memory (= post's memory)
    have hgeo64 : ∀ a b : Nat, p4Q8OldGeo lw.toNat (a, b) → a + b < 2 ^ 64 := by
      intro a b hgeo
      rcases hgeo with hg | hg
      · unfold Inside at hg; obtain ⟨hg1, hg2⟩ := hg; omega
      · unfold Inside at hg; obtain ⟨hg1, hg2⟩ := hg; omega
    have hmemW_geo : ∀ a b : Nat, p4Q8OldGeo lw.toNat (a, b) → ∀ k : Nat, a ≤ k → k + 8 ≤ a + b →
        memW post k = memW mid k := by
      intro a b hgeo k hk1 hk2
      exact p4Q8MemW_store_of_geo hcell_cnt hgeo ⟨hk1, hk2⟩ (le_refl _) hheap_lim
        (by have := hgeo64 a b hgeo; omega)
```
Hmm — p4Q8MemW_store_of_geo's conclusion: memW {t with memory := mem'} k = memW t k — with t := mid, mem' := pmcUpdW ... — the conclusion term is `memW {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w} k = memW mid k` — my target: `memW post k = memW mid k` — post is the `set`-definition — defeq ✓ `exact` works. Hmm — wait — but I stated the helper with `memW post k` — since `set` introduced post := that term, `post` in the goal displays — writing haves with `post` — fine, defeq everywhere.

Hmm — careful: `hbase : lw ≤ base` — in p4Q8MemW_store_of_geo (hgeo : p4Q8OldGeo lw i) (hkin) (hbase : lw ≤ base) (hin : base + sz ≤ heapLimit) — base/sz implicit — inferred from... hkin's i? No — i is from hgeo; base sz from hbase/hin — with `le_refl _` : lw ≤ ?base — unifies ?base := lw ✓ then hin : lw + ?sz ≤ heapLimit — from hheap_lim : lw.toNat + 24 ≤ heapLimit — unifies ?sz := 24?? — that would force the block to be (lw, 24) — which IS my case ✓ — but wait — p4Q8MemW_store_of_geo is generic over base sz — unification: `le_refl _` has type lw ≤ ?base — elaborated as Nat.le.refl : ?base ≤ ?base — unifies lw := ?base ✓ base := lw.toNat. hin := hheap_lim : lw.toNat + 24 ≤ heapLimit — ?sz := 24 ✓. So the no-hit check is against block (lw.toNat, 24) ✓ correct for the count store ✓.

Then:
```lean
    have h16_t0 : memW post (w_out.toNat + 16) = memW mid (w_out.toNat + 16) :=
      hmemW_geo _ _ geo_out  _ (by omega) (by omega)
```
where geo_out : p4Q8OldGeo lw.toNat (w_out.toNat, 96) := Or.inl ⟨hlw_ge, hwout⟩ — hmm — first disjunct: Inside (w_out, 96) sourceBase lw.toNat — ⟨sourceBase ≤ w_out, w_out + 96 ≤ lw.toNat⟩ — hlw_ge? no — h.out_inside.1 : sourceBase ≤ w_out.toNat (at s — Inside (w_out,96) sourceBase (globN s hp) — .1 : sourceBase ≤ w_out.toNat ✓ same value). Use ⟨h.out_inside.1, hwout⟩ ✓.
For h16_t0: a := w_out.toNat, b := 96, k := w_out.toNat + 16 — bounds: w_out.toNat ≤ w_out+16 ✓ omega; w_out+16+8 ≤ w_out+96 ✓ omega ✓.

Hmm wait — `hmemW_geo _ _ geo_out _ (by omega) (by omega)` — the k is inferred from the conclusion — conclusion memW post k = memW mid k vs target memW post (w_out+16) = memW mid (w_out+16) — k := w_out.toNat + 16 ✓.

```lean
    have hgeo_out : p4Q8OldGeo lw.toNat (w_out.toNat, 96) := Or.inl ⟨h.out_inside.1, hwout⟩
    have h16_t0 : memW post (w_out.toNat + 16) = memW mid (w_out.toNat + 16) :=
      hmemW_geo _ _ hgeo_out _ (by omega) (by omega)
    have hhd0_t0 : memW post (memW post (w_out.toNat + 16)) =
        memW mid (memW mid (w_out.toNat + 16)) := by
      rw [h16_t0]
      exact hmemW_geo _ _ geo_hdr_mid _ (by omega) (by omega)
    have hhd8_t0 : memW post (memW post (w_out.toNat + 16) + 8) =
        memW mid (memW mid (w_out.toNat + 16) + 8) := by
      have h1 : memW post (memW post (w_out.toNat + 16) + 8) =
          memW mid (memW post (w_out.toNat + 16) + 8) := by
        rw [h16_t0]
      rw [h1]
      exact hmemW_geo _ _ geo_hdr_mid _ (by omega) (by omega)
```
Hmm — hhd8_t0: after rw [h16_t0] the goal has memW mid (w_out+16) inside — wait — goal: memW post (memW post (w_out+16) + 8) = memW mid (memW mid (w_out+16) + 8). rw [h16_t0] rewrites `memW post (w_out.toNat + 16)` → `memW mid (w_out.toNat + 16)` — occurrences: LHS inner ✓ — also RHS? RHS has `memW mid (w_out+16)` — no `memW post` ✓. → goal: memW post (memW mid (w_out+16) + 8) = memW mid (memW mid (w_out+16) + 8) — hmm — that's exactly h1's statement ✓ so `rw [h16_t0]; exact hmemW_geo _ _ geo_hdr_mid _ (by omega) (by omega)` — wait after rw [h16_t0] the goal IS the h1 shape — and hmemW_geo with k := memW mid (w_out+16) + 8, geo (hd, 24): bounds hd ≤ hd+8 omega ✓, hd+8+8 ≤ hd+24 ✓ omega ✓. So:
```lean
    have hhd8_t0 : memW post (memW post (w_out.toNat + 16) + 8) =
        memW mid (memW mid (w_out.toNat + 16) + 8) := by
      rw [h16_t0]
      exact hmemW_geo _ _ geo_hdr_mid _ (by omega) (by omega)
```
Wait — hmm, no: after `rw [h16_t0]`, goal: `memW post (memW mid (w_out.toNat + 16) + 8) = memW mid (memW mid (w_out.toNat + 16) + 8)` — LHS is memW POST (…) — RHS memW mid (…) — and hmemW_geo gives memW post k = memW mid k with k := memW mid (w_out+16)+8 ✓ matches both sides ✓. 

Similarly hhd0_t0 — after `rw [h16_t0]`: goal `memW post (memW mid (w_out+16)) = memW mid (memW mid (w_out+16))` ✓ — hmemW_geo with k := memW mid (w_out+16), geo_hdr_mid, bounds: hd ≤ hd ✓ (le_refl — by omega — the goal for the bound is `memW mid (w_out.toNat + 16) ≤ memW mid (w_out.toNat + 16)` — omega reflexivity ✓); hd+8 ≤ hd+24 ✓ omega ✓.

Then the invariant's src fields — note they're stated at t0 — t0's memW ≡ post's memW ✓ (defeq — setVar only changes locals — but the FIELD types mention the full t0 term — providing `by rw [h16_t0]; ...` — hmm — the field goal is `memW t0 (w_out.toNat + 16) ≠ 0` — rw [h16_t0] — the pattern `memW post (w_out.toNat + 16)` — the goal has `memW t0 (…)` — post vs t0 — NOT syntactically equal!! rw FAILS (pattern not found).

CRITICAL: the field goals are at t0 (setVar-wrapped state). My haves are at post. Since defeq, I can't rw but I CAN `exact` — I need the field values as TERMS of the t0-types. E.g. src_nz : `memW t0 (w_out+16) ≠ 0` — provide `by rw [...]`? — no rw possible. Provide: `fun hnz => ...`? Ne is a function — h16_t0 : memW post … = memW mid … — the term `hnz : memW t0 (w_out+16) = 0` — defeq-transports? To use h16_t0 on hnz I need hnz : memW post … — `h16_t0 ▸ hnz`? ▸ with defeq mismatch — messy.

CLEANER SOLUTION: make hINV's STATE be spelled with post (as I did — hINV : P4Q8Loop … (setVar … (setVar … post))) — the fields' types mention that exact term — which contains post inside. So field goals like `memW (setVar … post) (w_out+16) ≠ 0` — the STATE is the setVar-term, NOT post. rw [h16_t0] — pattern `memW post (w_out+16)` — goal has `memW (setVarHOLFinite … post) (w_out+16)` — no syntactic match. FAIL.

Hmm!! How did Q4 handle this? In Q4's p4Q8Loop_store final assembly — the state was `setVarHOLFinite (ofString "i") … {u with memory := pmcUpdW …}` — and field goals like `by rw [hlu_others "out" …]; exact hmem.out_local` — for locals. For MEMORY fields — Q4's fields: `pmc_wordsOK_updW u … h.out_words` (defeq exact ✓) and `by rw [hout16]; exact h.src_nz` — WAIT — Q4 DID use rw for memory fields! `by rw [hout16]; exact h.src_nz` where hout16 : memW {u with memory := …} (w_out+16) = memW u (w_out+16) — and the field goal was `memW (setVarHOLFinite … {u with memory := …}) (w_out+16) ≠ 0` — hmm — how did rw [hout16] match?? The goal's memW is applied to `(setVarHOLFinite (ofString "i") (.val (.word …)) {u with memory := pmcUpdW …})` — NOT to `{u with memory := pmcUpdW …}`. rw [hout16] — pattern `memW {u with memory := …} (w_out+16)` — no match... UNLESS rw uses keyed matching up to reducible defeq — rw's matching is up to reducible transparency + instances — setVarHOLFinite is a def — reducible? By default defs are NOT reducible → no match → rw should have failed in Q4!!

Hmm wait — let me re-read Q4's final assembly: `by rw [hout16]; exact h.src_nz` — and hout16 was stated as: `have hout16 : memW {u with memory := (pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v)} (w_out.toNat + 16) = memW u (w_out.toNat + 16) := hmemW_below _ (by omega)` — hmm — and the field: src_nz : memW t (w_out.toNat+16) ≠ 0 where t := setVarHOLFinite … {u with memory := pmcUpdW …}. So Q4's rw [hout16] on goal `memW (setVarHOLFinite …) (w_out+16) ≠ 0`...

OH WAIT — I see — `≠` goals: `a ≠ b` unfolds to `a = b → False` — rw [hout16] on the goal `memW T (w_out+16) ≠ 0` — rw rewrites inside the Prop — the pattern `memW {u with memory := …} (w_out+16)` vs goal's `memW (setVarHOLFinite …) (w_out+16)` — these differ. UNLESS — hmm — did it actually work? Q4 compiled LEAN_OK — so YES it worked. How?

Possibility: rw's keyed matching DOES unfold setVarHOLFinite — because `setVarHOLFinite nm v s = {s with locals := ...}` — the goal's `memW (setVarHOLFinite …) x` — keyed matching at head `memW` — then unifies arguments up to reducible... `setVarHOLFinite` — if it's marked @[reducible] or is an abbrev — CHECK: StateExactFiniteMap.lean:316 — `def setVarHOLFinite` — hmm — or abbrev? Let me check. If it's a plain def, rw wouldn't unfold...

Hmm — alternative explanation: in the Q4 field, the state T in the goal might have been REDUCED by the anonymous-constructor elaboration — no...

Wait — actually — I misread Q4. Let me re-look at Q4's final assembly: the fields `by rw [hout16]; exact h.src_nz` — hout16 : `memW {u with memory := (pmcUpdW u.memory (w_lp + i_w * 8#64) v)} (w_out.toNat + 16) = memW u (w_out.toNat + 16)` — hmm — and the goal for src_nz — the P4Q8Loop field at state `setVarHOLFinite (ofString "i") (.val (.word (ofNat 64 (i_w.toNat+1)))) {u with memory := pmcUpdW u.memory (w_lp + i_w * 8#64) v}` — so the goal is `memW (setVarHOLFinite … {u with memory := …}) (w_out+16) ≠ 0`. And rw [hout16] succeeded?? 

Unless — the `refine ⟨…⟩` for the structure — when providing `by rw [hout16]; exact h.src_nz` for the field — the field's expected type has the setVar-term — rw [hout16] — pattern `memW {u with memory := pmcUpdW …} (w_out.toNat + 16)` — the goal contains `memW (setVarHOLFinite (ofString "i") (.val …) {u with memory := pmcUpdW u.memory (w_lp + i_w * 8#64) v}) (w_out.toNat + 16)` — hmm — for the pattern to match, rw needs `setVarHOLFinite … X` ≡ `X` — reducibly...

OR — maybe rw DID fail and they used a different route... but the code compiled. Let me actually TEST this hypothesis in a tiny file. Actually — the simplest explanation: `rw` uses `kabstract` which does matching up to REDUCIBLE transparency... BUT `setVarHOLFinite` — if it's an `abbrev` (abbrev is reducible) — check StateExactFiniteMap.lean:316. My summary says "setVarHOLFinite def exact form (StateExactFiniteMap.lean:316)". Let me check whether it's def or abbrev — and also whether memW's argument position forces unfolding... Actually — hmm — ANOTHER possibility: `memW s a` — the STATE argument — the goal's term is `memW (setVarHOLFinite …) (w_out+16)` — hmm.

Actually — WAIT. I bet the explanation is different: `rw` in Lean 4 Mathlib — `rw [h]` where h : a = b — uses `Eq.mpr`-style with motive built by `kabstract` — kabstract matches up to reducible DEFEQ — key: the HEAD of the pattern `memW …` — occurrences found by matching the whole term `memW {u with …} (w_out+16)` against subterms of the goal — subterm `memW (setVarHOLFinite …) (w_out+16)` — unifier: setVarHOLFinite … ≟ {u with memory := …} — with reducible transparency, if setVarHOLFinite is not reducible → FAIL.

So either setVarHOLFinite IS reducible (abbrev), or Q4's hout16 was stated differently. Let me just look at the file again — I read: `have hout16 : memW {u with memory := (pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v)} (w_out.toNat + 16) = memW u (w_out.toNat + 16) := hmemW_below _ (by omega)` — hmm wait — actually NO — looking at the Q4 source I fetched: hout16 was defined at line ~473: `have hout16 : memW {u with memory := (pmcUpdW ...)} (w_out.toNat + 16) = memW u (w_out.toNat + 16) := hmemW_below _ (by omega)` — hmm — wait that's in p4Q8Loop_store_mem (the memory-half lemma) whose conclusion state is `{u with memory := pmcUpdW …}` WITHOUT setVar! The setVar-wrapping happens in p4Q8Loop_store (the second lemma) — and THERE the fields were `by rw [hlu_others "out" …]; exact hmem.out_local` (LOCALS — where hlu_others was stated at the setVar-state ✓ syntactic match) — and MEMORY fields: `hmem.out_words, hmem.out_inside, hmem.out_below, hmem.marks, hmem.src_nz, hmem.src_logs, hmem.src_lp_eq, hmem.src_len, hmem.geo_out_hdr, hmem.geo_out_arr, hmem.src_ent, hmem.hdr_words, hmem.arr_words` — PASSED THROUGH DIRECTLY (hmem = the memory-half invariant at {u with memory := …}) — NOT rw'd! Because p4Q8Loop_store's field types are at the setVar-state — and they provided hmem's fields (at the memory-state) DIRECTLY — DEFEQ ✓!! 

E.g. `hmem.marks` : memW {u with memory := …} … — provided for field `marks` at setVar-state — defeq ✓ exact-in-constructor accepts ✓. And `by rw [hout16]; exact h.src_nz` — that was in p4Q8Loop_store_mem's OWN final assembly (state {u with memory := …} — NO setVar) ✓ consistent.

SO THE PATTERN IS: state memory-field facts at POST (no setVar), and provide them directly as constructor fields (defeq to t0-fields) ✓✓. The src_nz field: `memW t0 (w_out+16) ≠ 0` — provide a term of `memW post (w_out+16) ≠ 0` — need to BUILD that term — e.g. `fun hnz => hd_nz (by rw [← h16_t0] at hnz?? ...)` hmm — building Ne-terms: h16_t0 : memW post k = memW mid k, h16_mid : memW mid k = memW s k — so memW post k = memW s k := h16_t0.trans h16_mid — call it h16_ps : memW post (w_out+16) = memW s (w_out+16). Then the field src_nz := `by rw [h16_ps]; exact hd_nz`?? — rw on the goal `memW t0 (w_out+16) ≠ 0` — pattern `memW post (w_out+16)` — t0 ≠ post syntactically — FAIL again!

Hmm!! But Q4 PASSED hmem.marks etc. as direct defeq terms. For src_nz — hmem.src_nz was a FIELD of hmem (the invariant at memory-state) — i.e., the src_nz term was already of type `memW {u with memory := …} (w_out+16) ≠ 0` and provided directly ✓ defeq to the setVar-state version ✓.

For ME: I need terms of type `memW t0 (w_out+16) ≠ 0` (or defeq). I can BUILD such a term at post-type: `h16_ne : memW post (w_out+16) ≠ 0 := by intro hz; apply hd_nz; rw [← h16_ps]; exact hz`? — hmm — goal after intro hz: False — `apply hd_nz` — hd_nz : memW s (w_out+16) ≠ 0 — apply → goal `memW s (w_out+16) = 0` — rw [← h16_ps] — h16_ps : memW post … = memW s … — ← rewrites memW s … → memW post … ✓ — goal memW post (w_out+16) = 0 = hz ✓. So:
```lean
    have h16_ne : memW post (w_out.toNat + 16) ≠ 0 := by
      intro hz
      apply hd_nz
      rw [← h16_t0.trans h16_mid]  -- hmm — combine
      exact hz
```
Simpler: have h16_ps : memW post (w_out.toNat+16) = memW s (w_out.toNat+16) := h16_t0.trans h16_mid — then:
```lean
    have h16_ne : memW post (w_out.toNat + 16) ≠ 0 := by
      intro hz
      exact hd_nz (h16_ps ▸ hz)  -- ▸ risky
```
Use: `by rw [h16_ps] at hz; exact hd_nz hz` — hz : memW post (…) = 0 — rw [h16_ps] at hz ✓ (hz IS at post — syntactic ✓) → hz : memW s (…) = 0 → hd_nz hz : False ✓. ✓ THIS works — the have is stated AT POST, so rw applies fine.

So the approach: build ALL memory-dependent facts at POST-level (as haves with post in their types — rw works), then drop them into the constructor as defeq-terms. ✓ THIS IS THE Q4 PATTERN (hmem.marks etc. passed directly).

So:
```lean
    -- post-level source facts
    have h16_ne : memW post (w_out.toNat + 16) ≠ 0 := by
      intro hz
      rw [h16_ps] at hz
      exact hd_nz hz
    have hsrc_logs : LogsListOK post (memW post (w_out.toNat + 16)) := by
      rw [h16_t0]  -- hmm — goal at post ✓ pattern memW post (w_out+16) ✓ → LogsListOK post (memW mid (w_out+16))
      exact p4Q8LogsListOK_store hcell_cnt hnz_mid hDmid.logs_ok geo_hdr_mid harr_mid hent_mid
        (le_refl _) hheap_lim hh64 harr64 hent64
    have hlp_eq_post : lp_w.toNat = memW post (memW post (w_out.toNat + 16)) := by
      rw [hhd0_t0, hlp_mid]
```
Hmm — hlp_eq_post: goal lp_w.toNat = memW post (memW post (w_out+16)) — rw [hhd0_t0] rewrites `memW post (memW post (w_out.toNat + 16))` → `memW mid (memW mid (w_out.toNat + 16))` ✓ (LHS of hhd0_t0 matches the goal's subterm ✓) — then rw [hlp_mid] → `lp_w.toNat = lp_w.toNat`? — hlp_mid : memW mid (memW mid (w_out+16)) = lp_w.toNat — rewrites goal RHS → lp_w.toNat ✓ — goal lp_w.toNat = lp_w.toNat — rw closes rfl ✓.
```lean
    have hlen_post : memW post (memW post (w_out.toNat + 16) + 8) = nl_w.toNat := by
      rw [hhd8_t0, hnl8_mid]
    have hgeo_hdr_post : p4Q8OldGeo lw.toNat (memW post (w_out.toNat + 16), 24) := by
      rw [h16_t0]; exact geo_hdr_mid
```
✓.
```lean
    have hent_post : ∀ j, j < nl_w.toNat →
        WordAt post (lp_w.toNat + 8 * j) ∧
        LogEntryOK post (memW post (lp_w.toNat + 8 * j)) ∧
        p4Q8OldGeo lw.toNat (memW post (lp_w.toNat + 8 * j), 40) := by
      intro j hj
      have hvalj : memW post (lp_w.toNat + 8 * j) = memW mid (lp_w.toNat + 8 * j) :=
        hmemW_geo _ _ geo_arr_s _ (by omega) (by omega)
      obtain ⟨hw1, hw2⟩ := he_mid' j hj
      refine ⟨p4Q8WordAt_store_of_geo hcell_cnt hw1 geo_arr_s ⟨by omega, by omega⟩
          (le_refl _) hheap_lim (by have := hgeo64 _ _ geo_arr_s; omega), ?_, ?_⟩
      · rw [hvalj]
        exact p4Q8LogEntryOK_store hcell_cnt hw2 (by rw [harr_cell_mid j hj]; exact hent_geo_s j hj)
          (le_refl _) hheap_lim (by have := hgeo64 _ _ (hent_geo_s j hj); omega)
      · rw [hvalj, harr_cell_mid j hj]
        exact hent_geo_s j hj
```
Hmm — p4Q8WordAt_store_of_geo's premises: (hcell) (h : WordAt t k) (hgeo : p4Q8OldGeo lw i) (hkin : i.1 ≤ k ∧ k+8 ≤ i.1+i.2) (hbase : lw ≤ base) (hin : base + sz ≤ heapLimit) (hk64 : k < 2^64) — wait the signature: (hcell) (h) (hgeo) (hkin) (hbase) (hin) (hk64) : WordAt {t with memory := mem'} k — from Q2's dump: `theorem p4Q8WordAt_store_of_geo ... (hcell) (h : WordAt t k) (hgeo : p4Q8OldGeo lw i) (hkin : i.1 ≤ k ∧ k+8 ≤ i.1+i.2) (hbase : lw ≤ base) (hin : base + sz ≤ heapLimit) (hk64 : k < 2 ^ 64) : WordAt {t with memory := mem'} k` ✓.
Here: t := mid, k := lp_w.toNat + 8*j, i := (lp_w.toNat, 8*nl_w.toNat) (from geo_arr_s), base := lw.toNat (le_refl), sz := 24 (hheap_lim), hkin ⟨by omega, by omega⟩ — bounds: lp ≤ lp+8j ✓; lp+8j+8 ≤ lp+8nl (j<nl ✓ omega). hk64 : lp+8j < 2^64 — from geo_arr_s's geo (hgeo64 _ _ geo_arr_s : lp_w.toNat + 8*nl_w.toNat < 2^64 — hmm — that gives the ARRAY end — but k = lp+8j with 8j+8 ≤ 8nl → k+8 ≤ array end < 2^64 ✓ — so `by have := hgeo64 _ _ geo_arr_s; omega` — the goal lp_w.toNat + 8*j < 2^64 — omega with h : lp+8nl < 2^64 and hj : j < nl ✓ omega.

Hmm wait — hgeo64 as I stated it: `∀ a b, p4Q8OldGeo lw.toNat (a, b) → a + b < 2 ^ 64` — hgeo64 _ _ geo_arr_s : lp_w.toNat + 8*nl_w.toNat < 2^64 ✓.

Hmm — actually wait — p4Q8LogEntryOK_store's hk64 : log + 40 ≤ 2^64 — `by have := hgeo64 _ _ (hent_geo_s j hj); omega` — hgeo64 _ _ (hent_geo_s j hj) : memW s (lp+8j) + 40 < 2^64 ✓ — but the goal is about memW mid (lp+8j) + 40 — MISMATCH — the goal: `memW mid (lp_w.toNat + 8 * j) + 40 ≤ 2 ^ 64` — hmm — I have `memW s (lp+8j) + 40 < 2^64` — different atoms (memW mid vs memW s) — omega can't connect! Fix: rw first — the goal is inside p4Q8LogEntryOK_store's application — I'm passing `(by ... : memW mid (lp+8j) + 40 ≤ 2^64)` — to relate memW mid (lp+8j) to memW s — harr_cell_mid j hj : memW mid (lp+8j) = memW s (lp+8j) — so: `by rw [harr_cell_mid j hj]; exact (hgeo64 _ _ (hent_geo_s j hj)).le` — hmm — goal after rw: memW s (lp+8j) + 40 ≤ 2^64 — hgeo64 gives < — `.le` ✓. 

So hk64 := by rw [harr_cell_mid j hj]; exact (hgeo64 _ _ (hent_geo_s j hj)).le.

And hgeo for LogEntryOK: (by rw [harr_cell_mid j hj]; exact hent_geo_s j hj) : p4Q8OldGeo lw.toNat (memW mid (lp_w.toNat + 8*j), 40) — the `by` block's expected type is the geo of the mid-value ✓ — after rw the goal is geo of (memW s (lp+8j), 40) = hent_geo_s j hj ✓.

Wait — but hold on — p4Q8LogEntryOK_store (hcell) (h : LogEntryOK t log) — with log := memW mid (lp+8j) — hw2 : LogEntryOK mid (memW mid (lp_w.toNat + 8*j)) ✓ from he_mid' ✓.

And for src_ent's first component — hmm — the invariant's src_ent is: WordAt t (lp_w.toNat + 8*j) ∧ LogEntryOK t (memW t (lp_w.toNat + 8*j)) ∧ geo — at t0 — my hent_post gives it at post ✓ defeq ✓.

Now hsrc_logs's premises — harr_mid, hent_mid, hh64, harr64, hent64 — all stated at mid:
```lean
    have harr_mid : p4Q8OldGeo lw.toNat
        (memW mid (memW mid (w_out.toNat + 16)),
          8 * memW mid (memW mid (w_out.toNat + 16) + 8)) := by
      rw [hlp_mid, hnl8_mid]
      exact geo_arr_s
```
Hmm — rw [hlp_mid]: goal `p4Q8OldGeo lw.toNat (memW mid (memW mid (w_out+16)), 8 * memW mid (memW mid (w_out+16) + 8))` — the pattern `memW mid (memW mid (w_out.toNat + 16))` occurs: (1) as the first component; (2) inside `memW mid (memW mid (w_out+16) + 8)` — the inner part — BOTH get rewritten by rw [hlp_mid]! → `p4Q8OldGeo lw.toNat (lp_w.toNat, 8 * memW mid (lp_w.toNat + 8))` — hmm — the second: `memW mid (memW mid (w_out+16) + 8)` → `memW mid (lp_w.toNat + 8)` — but hnl8_mid's LHS is `memW mid (memW mid (w_out.toNat + 16) + 8)` — NO LONGER PRESENT (already rewritten)! FAIL for rw [hnl8_mid].

Fix: rewrite hnl8_mid FIRST: rw [hnl8_mid] — pattern `memW mid (memW mid (w_out.toNat + 16) + 8)` — occurs once ✓ → goal `p4Q8OldGeo lw.toNat (memW mid (memW mid (w_out+16)), 8 * nl_w.toNat)` — then rw [hlp_mid] → `p4Q8OldGeo lw.toNat (lp_w.toNat, 8 * nl_w.toNat)` ✓ = geo_arr_s ✓. So: `rw [hnl8_mid, hlp_mid]; exact geo_arr_s` ✓.

Similarly hent_mid:
```lean
    have hent_mid : ∀ i, i < memW mid (memW mid (w_out.toNat + 16) + 8) →
        p4Q8OldGeo lw.toNat (memW mid (memW mid (memW mid (w_out.toNat + 16)) + 8 * i), 40) := by
      intro i hi
      rw [hnl8_mid] at hi
      rw [hlp_mid]
      rw [harr_cell_mid i hi]
      exact hent_geo_s i hi
```
Trace: goal `p4Q8OldGeo lw.toNat (memW mid (memW mid (memW mid (w_out+16)) + 8 * i), 40)` — rw [hlp_mid] — pattern `memW mid (memW mid (w_out+16))` — occurs: the inner part of `mem