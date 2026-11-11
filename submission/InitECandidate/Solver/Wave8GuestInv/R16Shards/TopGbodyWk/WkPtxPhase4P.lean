import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4N

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

/-! # Phase 4P: instructions 25-30 (the out-logs copy loop)

`dec nl := logs[8]` (the log count), `dec lp := logs[0]` (the log data pointer),
`assign i := 0`, then the loop-31 while-loop pushing every log entry onto the
`bo+0x28` block-logs list.  The continuation receives the `nl`/`lp` locals
together with the out-list identification: either the live pinning of both
locals to the out-list's data pointer and length (with the list facts), or the
degenerate `nl = 0` (the loop never ran, the copy is empty). -/

/-- `setVarHOLFinite` leaves the code component untouched. -/
theorem p4P_setVar_code {F : Type} (nm : MlS) (v : ValueHOL 64)
    (s : PanSemStateFiniteExact 64 F) :
    (setVarHOLFinite nm v s).code = s.code := rfl

/-- An address below `sourceBase` is not in the guest domain. -/
theorem p4P_notDom {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hg : GuestInv s) {a : Nat} (halt : a < sourceBase) :
    ¬ s.memaddrs (BitVec.ofNat 64 a) := by
  intro hm
  rw [hg.memaddrs] at hm
  have hiff := (ordinaryDomain_iff _).mp hm
  have hto : (BitVec.ofNat 64 a).toNat = a := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (lt_trans halt (by decide : sourceBase < 2 ^ 64))
  rw [hto] at hiff
  omega

/-- The logs-list load at byte offset `k`: from the `logs` local word, the
in-domain word cell and the no-wraparound bound, the load evaluates forward. -/
theorem p4P_logsLoad {F : Type}
    {s : PanSemStateFiniteExact 64 F} {wl k : BitVec 64}
    (hlogs : s.locals.lookup (ofString "logs") = some (.val (.word wl)))
    (hwrap : wl.toNat + k.toNat < 2 ^ 64)
    (hwa : WordAt s (wl.toNat + k.toNat)) :
    ∃ w : BitVec 64,
      evalAt s (.load .one (.op .add [(.var .local (ofString "logs")), (.const k)])) =
        some (.val (.word w)) ∧
      w.toNat = memW s (wl.toNat + k.toNat) := by
  obtain ⟨w', hdom', hcell'⟩ := hwa
  have hmemW : memW s (wl.toNat + k.toNat) = w'.toNat := by
    simp only [memW, hcell']
  have hoffc : BitVec.ofNat 64 (wl.toNat + k.toNat) = wl + k := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    have hadd : (wl + k).toNat = wl.toNat + k.toNat := by
      rw [BitVec.toNat_add]
      exact Nat.mod_eq_of_lt hwrap
    rw [hadd]
    exact Nat.mod_eq_of_lt hwrap
  rw [hoffc] at hdom' hcell'
  have hz : k + 0 = k := BitVec.add_zero _
  refine ⟨w', ?_, hmemW.symm⟩
  simp only [evalAt, evalHOLExact, evalListHOLExact, toExact, hlogs, valueIsWord,
    valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, ↓reduceIte,
    List.foldr, Bool.and_self, memLoadHOLExact, isWfShapeExactHOL, hz,
    hdom', hcell']

/-- Looking up a different local is unaffected by a `setVarHOLFinite`. -/
theorem p4P_lookupUpdate {F : Type}
    {s : PanSemStateFiniteExact 64 F} {nm : MlS} {v : ValueHOL 64} {n : String}
    (hne : ofString n ≠ nm) :
    (setVarHOLFinite nm v s).locals.lookup (ofString n) = s.locals.lookup (ofString n) := by
  simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, Ne.symm hne]

/-- Looking up the assigned local after a `setVarHOLFinite` yields the value. -/
theorem p4P_lookupUpdateSelf {F : Type}
    {s : PanSemStateFiniteExact 64 F} {nm : MlS} {v : ValueHOL 64} :
    (setVarHOLFinite nm v s).locals.lookup nm = v := by
  simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

/-- The g7 segment runner: instructions 25-30 of phase 4. -/
theorem p4Run_g7 {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (h : P4Data entry s s_pmc w_out)
    (hc : s.code = originalRuntimeCode)
    (rest : ProgHOL 64)
    (wl succw : BitVec 64)
    (hlogs : s.locals.lookup (ofString "logs") = some (.val (.word wl)))
    (hsucc : s.locals.lookup (ofString "succeeded") = some (.val (.word succw)))
    (hLL : LogsListOK s wl.toNat)
    (hDF : LogsDisjFixed s wl.toNat)
    (hdisj : wl.toNat = memW s (w_out.toNat + 16) ∨
      (memW s wl.toNat = wl.toNat + 24 ∧
        memW s (wl.toNat + 8) = 0 ∧
        WordAt s wl.toNat ∧ WordAt s (wl.toNat + 8) ∧
        wl.toNat + 32 ≤ globN s "heap_ptr"))
    (htail : ∀ (s' : PanSemStateFiniteExact 64 F) (nl_w lp_w : BitVec 64),
      P4Data entry s' s_pmc w_out →
      s'.code = originalRuntimeCode →
      s'.locals.lookup (ofString "nl") = some (.val (.word nl_w)) →
      s'.locals.lookup (ofString "lp") = some (.val (.word lp_w)) →
      ((nl_w.toNat = memW s' (memW s' (w_out.toNat + 16) + 8) ∧
          lp_w.toNat = memW s' (memW s' (w_out.toNat + 16)) ∧
          LogsListOK s' (memW s' (w_out.toNat + 16)) ∧
          LogsDisjFixed s' (memW s' (w_out.toNat + 16)) ∧
          memW s' (w_out.toNat + 16) ≠ 0 ∧
          nl_w.toNat < 2 ^ 28) ∨
        nl_w.toNat = 0) →
      PtxRelRunStrong entry rest s') :
    PtxRelRunStrong entry
      (.dec (ofString "nl") .one
        (.load .one (.op .add [(.var .local (ofString "logs")),
          (.const 0x0000000000000008#64)]))
        (.dec (ofString "lp") .one
          (.load .one (.op .add [(.var .local (ofString "logs")),
            (.const 0x0000000000000000#64)]))
          (.seq (.assign .local (ofString "i") (.const 0x0000000000000000#64))
            (.seq (.while (.cmp .less (.var .local (ofString "i"))
                (.var .local (ofString "nl")))
                (.decCall (ofString "slot") .one (ofString "lst_push")
                  [(.load .one (.op .add [(.var .global (ofString "bo")),
                    (.const 0x0000000000000028#64)])),
                  (.const 0x0000000000000008#64)]
                  (.seq (.store (.var .local (ofString "slot"))
                      (.load .one (.op .add [(.var .local (ofString "lp")),
                        (.panop .mul [(.var .local (ofString "i")),
                          (.const 0x0000000000000008#64)])])))
                    (.assign .local (ofString "i")
                      (.op .add [(.var .local (ofString "i")),
                        (.const 0x0000000000000001#64)])))))
              rest)))) s := by
  have hAs : ArenaOK s := h.base.world.1.2
  have hgS : GuestInv s := h.base.world.1.1
  have hdom0 : ¬ s.memaddrs (BitVec.ofNat 64 0) := p4P_notDom hgS (by decide)
  rcases hLL with h0 | hlive
  · -- wl = 0: the load at `logs + 8` is at address 8, outside the domain
    rcases hdisj with hL0 | hFr0
    · refine p4Run_dec (ofString "nl") .one _ _ ?_
      intro v hev hsh
      exfalso
      have hw0 : wl = 0x0000000000000000#64 := by
        apply BitVec.eq_of_toNat_eq
        rw [h0]
        decide
      rw [hw0] at hlogs
      have hdom8 : ¬ s.memaddrs (0x0000000000000008#64) := p4P_notDom hgS (by decide)
      have hz8 : (0x0000000000000008#64 : BitVec 64) + 0 = 0x0000000000000008#64 :=
        BitVec.add_zero _
      simp only [evalAt, evalHOLExact, evalListHOLExact, toExact, hlogs, valueIsWord,
        valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, ↓reduceIte,
        List.foldr, Bool.and_self, BitVec.zero_add, memLoadHOLExact,
        isWfShapeExactHOL, hz8, hdom8] at hev
      simp at hev
    · exfalso
      obtain ⟨w, hdm, hcell⟩ := hFr0.2.2.1
      simp only [h0] at hdm
      exact hdom0 hdm
  · -- wl ≠ 0 with the full list facts: split on the out-list identification
    rcases hdisj with hL | hFr
    · -- LIVE: `logs` is the out-list; run the copy loop
      have hw0 : WordAt s (wl.toNat + 0) := hlive.1.2.2 0 (by norm_num)
      have hw8 : WordAt s (wl.toNat + 8) := hlive.1.2.2 1 (by norm_num)
      have hwrap8 : wl.toNat + (0x0000000000000008#64 : BitVec 64).toNat < 2 ^ 64 := by
        have hd8 : (0x0000000000000008#64 : BitVec 64).toNat = 8 := by decide
        rw [hd8]
        have h24 := (ivl_allocated_bound hAs hlive.2.1).2
        omega
      have hwl_nz : wl.toNat ≠ 0 := by
        intro hz
        obtain ⟨w, hdm, hcell⟩ := hw0
        simp only [hz, Nat.add_zero] at hdm
        exact hdom0 hdm
      obtain ⟨nl_w, hev_nl, hnlw⟩ :=
        p4P_logsLoad (k := 0x0000000000000008#64) hlogs hwrap8 hw8
      refine p4Run_dec (ofString "nl") .one _ _ ?_
      intro v hev hsh
      rw [hev_nl] at hev
      have hv : v = .val (.word nl_w) := (Option.some.inj hev).symm
      subst hv
      set s₁ : PanSemStateFiniteExact 64 F :=
        setVarHOLFinite (ofString "nl") (.val (.word nl_w)) s with hs₁
      have hD₁ : P4Data entry s₁ s_pmc w_out :=
        p4Data_setVar (by decide) (by decide) (by decide) (by decide)
          (by intro nm hnm
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hnm
              rcases hnm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
          h
      have hlogs₁ : s₁.locals.lookup (ofString "logs") = some (.val (.word wl)) := by
        rw [hs₁]
        exact (p4P_lookupUpdate
          (show (ofString "logs" : MlS) ≠ ofString "nl" by decide)).trans hlogs
      have hwrap0 : wl.toNat + (0x0000000000000000#64 : BitVec 64).toNat < 2 ^ 64 := by
        have hd0 : (0x0000000000000000#64 : BitVec 64).toNat = 0 := by decide
        rw [hd0]
        have := wl.isLt; omega
      obtain ⟨lp_w, hev_lp, hlpw⟩ :=
        p4P_logsLoad (k := 0x0000000000000000#64) hlogs₁ hwrap0 hw0
      refine p4Run_dec (ofString "lp") .one _ _ ?_
      intro v2 hev2 hsh2
      rw [hev_lp] at hev2
      have hv2 : v2 = .val (.word lp_w) := (Option.some.inj hev2).symm
      subst hv2
      set s₂ : PanSemStateFiniteExact 64 F :=
        setVarHOLFinite (ofString "lp") (.val (.word lp_w)) s₁ with hs₂
      have hD₂ : P4Data entry s₂ s_pmc w_out :=
        p4Data_setVar (by decide) (by decide) (by decide) (by decide)
          (by intro nm hnm
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hnm
              rcases hnm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
          hD₁
      refine p4Run_assign (ofString "i") _ _ ?_
      intro v3 hev3
      have hev0 : evalAt s₂ (.const 0x0000000000000000#64) =
          some (.val (.word 0x0000000000000000#64)) := rfl
      rw [hev0] at hev3
      have hv3 : v3 = .val (.word 0x0000000000000000#64) := (Option.some.inj hev3).symm
      subst hv3
      set s₃ : PanSemStateFiniteExact 64 F :=
        setVarHOLFinite (ofString "i")
          (.val (.word 0x0000000000000000#64)) s₂ with hs₃
      have hD₃ : P4Data entry s₃ s_pmc w_out :=
        p4Data_setVar (by decide) (by decide) (by decide) (by decide)
          (by intro nm hnm
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hnm
              rcases hnm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
          hD₂
      have hi₃ : s₃.locals.lookup (ofString "i") =
          some (.val (.word 0x0000000000000000#64)) := by
        rw [hs₃]
        exact p4P_lookupUpdateSelf
      have hnl₃ : s₃.locals.lookup (ofString "nl") = some (.val (.word nl_w)) := by
        rw [hs₃, hs₂]
        exact ((p4P_lookupUpdate
          (show (ofString "nl" : MlS) ≠ ofString "i" by decide)).trans
          ((p4P_lookupUpdate
            (show (ofString "nl" : MlS) ≠ ofString "lp" by decide)).trans
            p4P_lookupUpdateSelf))
      have hlp₃ : s₃.locals.lookup (ofString "lp") = some (.val (.word lp_w)) := by
        rw [hs₃, hs₂]
        exact ((p4P_lookupUpdate
          (show (ofString "lp" : MlS) ≠ ofString "i" by decide)).trans
          p4P_lookupUpdateSelf)
      have hcode₃ : s₃.code = originalRuntimeCode := hc
      have hloci : locN s₃ "i" = 0 := by
        simp [locN, hi₃]
      have hlocn : locN s₃ "nl" = nl_w.toNat := by
        simp only [locN, hnl₃]
      have hile : locN s₃ "i" ≤ locN s₃ "nl" := by
        rw [hloci, hlocn]; omega
      have hnl28 : locN s₃ "nl" < 2 ^ 28 := by
        rw [hlocn, hnlw]; exact hlive.2.2.1
      have hlp_pin : lp_w.toNat = memW s₃ (memW s₃ (w_out.toNat + 16)) := by
        show lp_w.toNat = memW s (memW s (w_out.toNat + 16))
        rw [← hL]; exact hlpw
      have hnl_pin : nl_w.toNat = memW s₃ (memW s₃ (w_out.toNat + 16) + 8) := by
        show nl_w.toNat = memW s (memW s (w_out.toNat + 16) + 8)
        rw [← hL]; exact hnlw
      have hlogs_nz : memW s₃ (w_out.toNat + 16) ≠ 0 := by
        show memW s (w_out.toNat + 16) ≠ 0
        rw [← hL]; exact hwl_nz
      -- the length bound: the bo+40 list length plus the remaining entries
      -- cannot reach `sourceBase` (both backing arrays are allocated)
      have hE : TxEnv s := txEnv_of_p4Data h
      obtain ⟨⟨_, hbo_nz_e, hbo24_nz_e, hbo32_nz_e, hidx_lt_e⟩, _, hbo40_nz_e, hbo72_nz_e,
        S_e, Nd_e, hWT_e, _⟩ := h.base.ready_entry
      have hD_e : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e Nd_e) := by
        rw [ptxRegions_eq_bufRegions]
        exact validBufList_disj validBufList_ptxBufs hWT_e
      obtain ⟨logs₀, hll₀, hl_ok₀, hl_dj₀, hty₀⟩ := h.logs_facts
      obtain ⟨S_pmc, Nd_pmc, S_cur, Nd_cur, hty1, hty2, hWT_s, hty4, hty5, hty6, hty7,
        hty8, hty9⟩ := hty₀ S_e Nd_e hWT_e hD_e
      obtain ⟨hnd, htabA, htabB, hws, hbs, hts, hgr, hbs32, hts32, hbal, hboL, hroles⟩ :=
        hWT_s.1
      have hLstOK : LstOK s (memW s (globN s "bo" + 40)) :=
        hboL hE.bo_nz 40 (by decide) hE.bo40
      obtain ⟨hLcap1, hLlencap⟩ := hLstOK
      have harr := p4Loop31_arrFacts (l := memW s (globN s "bo" + 40)) hE hWT_s.1 rfl
        h.base.log_backing
      have hmem_fix : (memW s (memW s (globN s "bo" + 40)),
          8 * memW s (memW s (globN s "bo" + 40) + 16)) ∈ fixedObjects s := by
        unfold fixedObjects
        apply List.mem_append_left
        apply List.mem_append_right
        exact harr.1
      have hFT : FixedTyped s := hWT_s.2.2.1
      have hAlArr : Allocated s (memW s (memW s (globN s "bo" + 40)),
          8 * memW s (memW s (globN s "bo" + 40) + 16)) := by
        rcases hFT.1 _ hmem_fix with hz0 | ⟨h1, hwords0⟩
        · exfalso
          have h8 : 8 * memW s (memW s (globN s "bo" + 40) + 16) = 0 := hz0
          have := hLcap1
          omega
        · exact h1
      have hAlDat : Allocated s (memW s wl.toNat, 8 * nl_w.toNat) := by
        rcases hDF with hzDF | ⟨h1DF, h2DF⟩
        · exact absurd hzDF hwl_nz
        · rw [hnlw]
          exact h1DF
      have hsb : sourceBase = 2701131776 := by decide
      have hhl : heapLimit = 2952790016 := by decide
      have hss : scratchStart = 2952790016 := by decide
      have hse : scratchEnd = 2965299200 := by decide
      have ha1 := hAs.1
      have ha2 := hAs.2.1
      have ha3 := hAs.2.2.1
      have ha4 := hAs.2.2.2.1
      have ha5 := hAs.2.2.2.2.1
      have hlenb : 8 * (memW s₃ (memW s₃ (globN s₃ "bo" + 40) + 8) +
          (locN s₃ "nl" - locN s₃ "i")) < sourceBase := by
        show 8 * (memW s (memW s (globN s "bo" + 40) + 8) +
          (locN s₃ "nl" - locN s₃ "i")) < sourceBase
        rw [hloci, hlocn]
        rcases hAlArr with hA1 | hA1 <;> rcases hAlDat with hA2 | hA2 <;>
          obtain ⟨hA1a, hA1b⟩ := hA1 <;> obtain ⟨hA2a, hA2b⟩ := hA2 <;> omega
      refine p4Run_loop31
        (⟨⟨hD₃, ⟨0x0000000000000000#64, hi₃⟩, ⟨nl_w, hnl₃⟩, ⟨lp_w, hlp₃⟩,
            hile, hnl28, hlenb⟩, txEnv_of_p4Data hD₃, hlogs_nz,
          ⟨lp_w, nl_w, hlp₃, hnl₃, hlp_pin, hnl_pin⟩⟩) hcode₃ ?_
      intro t' hfull hcond
      obtain ⟨⟨hD', hi_w', hnl_w', hlp_w', hile', hnl28', hlenb'⟩, htxenv', hlogs_nz',
        ⟨lp_w', nl_w', hlp', hnl', hlp_pin', hnl_pin'⟩⟩ := hfull
      have hqlocn : locN t' "nl" = nl_w'.toNat := by simp only [locN, hnl']
      refine htail t' nl_w' lp_w' hD' ?_ hnl' hlp'
        (Or.inl ⟨hnl_pin', hlp_pin', hD'.logs_ok, ?_, hlogs_nz', ?_⟩)
      · exact hD'.base.world.1.1.code
      · obtain ⟨⟨_, hbo_nz_e', hbo24_nz_e', hbo32_nz_e', hidx_lt_e'⟩, _, hbo40_nz_e',
          hbo72_nz_e', S_e', Nd_e', hWT_e', _⟩ := hD'.base.ready_entry
        have hD_e' : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e' Nd_e') := by
          rw [ptxRegions_eq_bufRegions]
          exact validBufList_disj validBufList_ptxBufs hWT_e'
        obtain ⟨logs'', hll'', hl_ok'', hl_dj'', hty''⟩ := hD'.logs_facts
        obtain ⟨S_pmc'', Nd_pmc'', S_cur'', Nd_cur'', -, -, -, -, -, -, -, hty8'', -⟩ :=
          hty'' S_e' Nd_e' hWT_e' hD_e'
        exact pmcLogsLiveOwned_disjFixed hty8''
      · omega
    · -- FRESH list: `nl` is the stored zero length; the loop is vacuous
      have hwrap8' : wl.toNat + (0x0000000000000008#64 : BitVec 64).toNat < 2 ^ 64 := by
        have hd8 : (0x0000000000000008#64 : BitVec 64).toNat = 8 := by decide
        rw [hd8]
        have h5 := hFr.2.2.2.2
        have h2 := hAs.2.1
        have hhl : heapLimit < 2 ^ 64 := by decide
        omega
      obtain ⟨nl_w, hev_nl, hnlw⟩ :=
        p4P_logsLoad (k := 0x0000000000000008#64) hlogs hwrap8' hFr.2.2.2.1
      have hn0 : nl_w.toNat = 0 := by rw [hnlw]; exact hFr.2.1
      refine p4Run_dec (ofString "nl") .one _ _ ?_
      intro v hev hsh
      rw [hev_nl] at hev
      have hv : v = .val (.word nl_w) := (Option.some.inj hev).symm
      subst hv
      set s₁ : PanSemStateFiniteExact 64 F :=
        setVarHOLFinite (ofString "nl") (.val (.word nl_w)) s with hs₁
      have hD₁ : P4Data entry s₁ s_pmc w_out :=
        p4Data_setVar (by decide) (by decide) (by decide) (by decide)
          (by intro nm hnm
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hnm
              rcases hnm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
          h
      have hlogs₁ : s₁.locals.lookup (ofString "logs") = some (.val (.word wl)) := by
        rw [hs₁]
        exact (p4P_lookupUpdate
          (show (ofString "logs" : MlS) ≠ ofString "nl" by decide)).trans hlogs
      have hwrap0' : wl.toNat + (0x0000000000000000#64 : BitVec 64).toNat < 2 ^ 64 := by
        have hd0 : (0x0000000000000000#64 : BitVec 64).toNat = 0 := by decide
        rw [hd0]
        have := wl.isLt; omega
      obtain ⟨lp_w, hev_lp, hlpw⟩ :=
        p4P_logsLoad (k := 0x0000000000000000#64) hlogs₁ hwrap0' hFr.2.2.1
      refine p4Run_dec (ofString "lp") .one _ _ ?_
      intro v2 hev2 hsh2
      rw [hev_lp] at hev2
      have hv2 : v2 = .val (.word lp_w) := (Option.some.inj hev2).symm
      subst hv2
      set s₂ : PanSemStateFiniteExact 64 F :=
        setVarHOLFinite (ofString "lp") (.val (.word lp_w)) s₁ with hs₂
      have hD₂ : P4Data entry s₂ s_pmc w_out :=
        p4Data_setVar (by decide) (by decide) (by decide) (by decide)
          (by intro nm hnm
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hnm
              rcases hnm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
          hD₁
      refine p4Run_assign (ofString "i") _ _ ?_
      intro v3 hev3
      have hev0 : evalAt s₂ (.const 0x0000000000000000#64) =
          some (.val (.word 0x0000000000000000#64)) := rfl
      rw [hev0] at hev3
      have hv3 : v3 = .val (.word 0x0000000000000000#64) := (Option.some.inj hev3).symm
      subst hv3
      set s₃ : PanSemStateFiniteExact 64 F :=
        setVarHOLFinite (ofString "i")
          (.val (.word 0x0000000000000000#64)) s₂ with hs₃
      have hD₃ : P4Data entry s₃ s_pmc w_out :=
        p4Data_setVar (by decide) (by decide) (by decide) (by decide)
          (by intro nm hnm
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hnm
              rcases hnm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
          hD₂
      have hi₃ : s₃.locals.lookup (ofString "i") =
          some (.val (.word 0x0000000000000000#64)) := by
        rw [hs₃]
        exact p4P_lookupUpdateSelf
      have hnl₃ : s₃.locals.lookup (ofString "nl") = some (.val (.word nl_w)) := by
        rw [hs₃, hs₂]
        exact ((p4P_lookupUpdate
          (show (ofString "nl" : MlS) ≠ ofString "i" by decide)).trans
          ((p4P_lookupUpdate
            (show (ofString "nl" : MlS) ≠ ofString "lp" by decide)).trans
            p4P_lookupUpdateSelf))
      have hlp₃ : s₃.locals.lookup (ofString "lp") = some (.val (.word lp_w)) := by
        rw [hs₃, hs₂]
        exact ((p4P_lookupUpdate
          (show (ofString "lp" : MlS) ≠ ofString "i" by decide)).trans
          p4P_lookupUpdateSelf)
      have hcode₃ : s₃.code = originalRuntimeCode := hc
      have hw0' : nl_w = 0x0000000000000000#64 := by
        apply BitVec.eq_of_toNat_eq
        rw [hn0]
        decide
      subst hw0'
      refine p4Run_while_guard p4Loop31Cond p4Loop31Body rest (fun t => t = s₃)
        p4Loop31Body_noTopBreak p4Loop31Body_noTopContinue ?_ ?_ s₃ rfl
      · intro t ht hcond
        subst ht
        exact htail s₃ _ _ hD₃ hcode₃ hnl₃ hlp₃ (Or.inr hn0)
      · intro t ht ⟨w, hw1, hw2⟩ ih
        subst ht
        exfalso
        have hlt := p4Loop31_guard_lt hi₃ hnl₃ (by decide) (by decide) w hw2 hw1
        omega

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
