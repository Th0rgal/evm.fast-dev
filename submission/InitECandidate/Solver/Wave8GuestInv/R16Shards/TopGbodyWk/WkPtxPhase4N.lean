import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4L
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4M

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

/-! # Phase 4N: instructions 20-23 (the logs block and the succeeded flag)

`dec logs := out[0x10]` (the output record's logs-list pointer), the
null-logs `lst_new` fallback (a fresh empty list), `dec succeeded := 1` and
the `out[0x20]`-conditioned reset to `0`.  The continuation receives the
final `logs` word together with its list facts (either the kept out-list
identification or the fresh-list layout) and the `succeeded` word. -/

/-- `setVarHOLFinite` leaves the code component untouched. -/
theorem p4N_setVar_code {F : Type} (nm : MlS) (v : ValueHOL 64)
    (s : PanSemStateFiniteExact 64 F) :
    (setVarHOLFinite nm v s).code = s.code := rfl

/-- The out-block load at byte offset `c` evaluates to the memory word. -/
theorem p4N_outLoad {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (h : P4Data entry s s_pmc w_out) (c : BitVec 64)
    (hcmod : c.toNat % 8 = 0) (hclt : c.toNat < 96) :
    ∃ wl : BitVec 64,
      evalAt s (.load .one (.op .add [(.var .local (ofString "out")), (.const c)])) =
        some (.val (.word wl)) ∧
      wl.toNat = memW s (w_out.toNat + c.toNat) := by
  have hAs : ArenaOK s := h.base.world.1.2
  have hout_hi : w_out.toNat + 96 ≤ 2 ^ 64 :=
    (R13Shards.ivl_allocated_bound hAs (Or.inl h.out_inside)).2
  have hw : WordAt s (w_out.toNat + 8 * (c.toNat / 8)) :=
    h.out_words.2.2 (c.toNat / 8) (by omega)
  have hoffeq : w_out.toNat + 8 * (c.toNat / 8) = w_out.toNat + c.toNat := by omega
  rw [hoffeq] at hw
  obtain ⟨w', hdom', hcell'⟩ := hw
  have hmemW : memW s (w_out.toNat + c.toNat) = w'.toNat := by
    simp only [memW, hcell']
  have hsumlt : w_out.toNat + c.toNat < 2 ^ 64 := by omega
  have hoffc : BitVec.ofNat 64 (w_out.toNat + c.toNat) = w_out + c := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    have hadd : (w_out + c).toNat = w_out.toNat + c.toNat := by
      rw [BitVec.toNat_add]
      exact Nat.mod_eq_of_lt hsumlt
    rw [hadd]
    exact Nat.mod_eq_of_lt hsumlt
  rw [hoffc] at hdom' hcell'
  have hz : c + 0 = c := BitVec.add_zero _
  refine ⟨w', ?_, hmemW.symm⟩
  simp only [evalAt, evalHOLExact, evalListHOLExact, toExact, h.out_local, valueIsWord,
    valueWord, wordOpHOL, wordOp, panOpHOL, List.all, List.map, Option.map, ↓reduceIte,
    List.foldr, Bool.and_self, memLoadHOLExact, isWfShapeExactHOL, hz,
    hdom', hcell']

/-- Rebinding the local `logs` to a word preserves `P4Data`; the
`logs_facts` witness degrades to the trivial `0` (the out-list facts stay
available through `logs_ok` and the typing field). -/
theorem p4Data_setLogs {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out wl : BitVec 64}
    (h : P4Data entry s s_pmc w_out) :
    P4Data entry (setVarHOLFinite (ofString "logs") (.val (.word wl)) s) s_pmc w_out := by
  have hlu : ∀ name : String, ofString name ≠ ofString "logs" →
      (setVarHOLFinite (ofString "logs") (.val (.word wl)) s).locals.lookup
        (ofString name) = s.locals.lookup (ofString name) := by
    intro name hne
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, Ne.symm hne]
  refine ⟨ptxRelBase_with_locals h.base
      (s.locals.update (ofString "logs", (.val (.word wl) : ValueHOL 64))) s.clock,
    h.arena_pmc, h.heap_pmc, ?_, h.out_words, h.out_inside, h.marks,
    (R13Shards.logsListOK_with_locals s _ s.clock (memW s (w_out.toNat + 16))).2 h.logs_ok,
    ptxPhase4LocalShapes_setVar ?_ h.shapes, ?_, ?_,
    ⟨0, Or.inr rfl, Or.inl rfl, Or.inl rfl, ?_⟩⟩
  · rw [hlu "out" (by decide)]
    exact h.out_local
  · intro nm hnm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hnm
    rcases hnm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [hlu "tx" (by decide)]
    exact h.tx_local
  · rw [hlu "index" (by decide)]
    exact h.idx_local
  · intro S0 Nd0 hW hD
    obtain ⟨logs0, hll0, hl_ok0, hl_dj0, hty0⟩ := h.logs_facts
    obtain ⟨S_pmc, Nd_pmc, S_cur, Nd_cur, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
      hty0 S0 Nd0 hW hD
    exact ⟨S_pmc, Nd_pmc, S_cur, Nd_cur, h1, h2,
      (R13Shards.worldTypedWith_with_locals s _ s.clock S_cur Nd_cur).2 h3,
      h4, h5, h6, h7, h8, pmcLogsLiveOwned_zero _ _ _⟩

/-- Instructions 20-23. -/
theorem p4Run_g5 {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (h : P4Data entry s s_pmc w_out)
    (hc : s.code = originalRuntimeCode)
    (rest : ProgHOL 64)
    (htail : ∀ (s' : PanSemStateFiniteExact 64 F) (wl succw : BitVec 64),
      P4Data entry s' s_pmc w_out →
      s'.code = originalRuntimeCode →
      s'.locals.lookup (ofString "logs") = some (.val (.word wl)) →
      s'.locals.lookup (ofString "succeeded") = some (.val (.word succw)) →
      LogsListOK s' wl.toNat →
      LogsDisjFixed s' wl.toNat →
      (wl.toNat = memW s' (w_out.toNat + 16) ∨
        (memW s' (wl.toNat) = wl.toNat + 24 ∧
          memW s' (wl.toNat + 8) = 0 ∧
          WordAt s' (wl.toNat) ∧ WordAt s' (wl.toNat + 8) ∧
          wl.toNat + 32 ≤ globN s' "heap_ptr")) →
      PtxRelRunStrong entry rest s') :
    PtxRelRunStrong entry
      (.dec (ofString "logs") .one
        (.load .one (.op .add [(.var .local (ofString "out")),
          (.const 0x0000000000000010#64)]))
        (.seq (.ite (.cmp .equal (.var .local (ofString "logs"))
            (.const 0x0000000000000000#64))
            (.call (some (some (.local, (ofString "logs")), none)) (ofString "lst_new")
              [(.const 0x0000000000000008#64), (.const 0x0000000000000001#64)])
            .skip)
          (.dec (ofString "succeeded") .one (.const 0x0000000000000001#64)
            (.seq (.ite (.cmp .notEqual
                (.load .one (.op .add [(.var .local (ofString "out")),
                  (.const 0x0000000000000020#64)]))
                (.const 0x0000000000000000#64))
              (.assign .local (ofString "succeeded") (.const 0x0000000000000000#64))
              .skip)
            rest)))) s := by
  -- the succeeded-block continuation, factored over both ite-21 branches
  have hsucc : ∀ (s₂ : PanSemStateFiniteExact 64 F) (w₂ : BitVec 64),
      P4Data entry s₂ s_pmc w_out →
      s₂.code = originalRuntimeCode →
      s₂.locals.lookup (ofString "logs") = some (.val (.word w₂)) →
      LogsListOK s₂ w₂.toNat →
      LogsDisjFixed s₂ w₂.toNat →
      (w₂.toNat = memW s₂ (w_out.toNat + 16) ∨
        (memW s₂ (w₂.toNat) = w₂.toNat + 24 ∧
          memW s₂ (w₂.toNat + 8) = 0 ∧
          WordAt s₂ (w₂.toNat) ∧ WordAt s₂ (w₂.toNat + 8) ∧
          w₂.toNat + 32 ≤ globN s₂ "heap_ptr")) →
      PtxRelRunStrong entry
        (.dec (ofString "succeeded") .one (.const 0x0000000000000001#64)
          (.seq (.ite (.cmp .notEqual
              (.load .one (.op .add [(.var .local (ofString "out")),
                (.const 0x0000000000000020#64)]))
              (.const 0x0000000000000000#64))
            (.assign .local (ofString "succeeded") (.const 0x0000000000000000#64))
            .skip)
            rest)) s₂ := by
    intro s₂ w₂ hD₂ hc₂ hl₂ hLL₂ hDF₂ hdisj₂
    have hne_ls : (ofString "succeeded" : MlS) ≠ ofString "logs" := by decide
    refine p4Run_dec (ofString "succeeded") .one _ _ ?_
    intro v22 hev22 hsh22
    obtain ⟨succw1, hv22⟩ : ∃ succw1 : BitVec 64, v22 = .val (.word succw1) := by
      simp only [evalAt, evalHOLExact, Option.some.injEq] at hev22
      exact ⟨_, hev22.symm⟩
    refine p4Run_ite _ _ .skip _ ?_ ?_
    · refine p4Run_assign (ofString "succeeded") _ _ ?_
      intro v23 hev23
      obtain ⟨succw, hv23⟩ : ∃ succw : BitVec 64, v23 = .val (.word succw) := by
        simp only [evalAt, evalHOLExact, Option.some.injEq] at hev23
        exact ⟨_, hev23.symm⟩
      have hD₃ : P4Data entry
          (setVarHOLFinite (ofString "succeeded") v23
            (setVarHOLFinite (ofString "succeeded") v22 s₂)) s_pmc w_out :=
        p4Data_setVar (by decide) (by decide) (by decide) (by decide)
          (by intro nm hnm
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hnm
              rcases hnm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
          (p4Data_setVar (by decide) (by decide) (by decide) (by decide)
            (by intro nm hnm
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hnm
                rcases hnm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
            hD₂)
      refine htail
        (setVarHOLFinite (ofString "succeeded") v23
          (setVarHOLFinite (ofString "succeeded") v22 s₂)) w₂ succw hD₃
        ?_ ?_ ?_ ?_ ?_ ?_
      · rw [p4N_setVar_code, p4N_setVar_code]
        exact hc₂
      · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne_ls, hl₂]
      · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hv23]
      · exact hLL₂
      · exact hDF₂
      · exact hdisj₂
    · refine p4RelRunStrong_skip ?_
      have hD₃ : P4Data entry
          (setVarHOLFinite (ofString "succeeded") v22 s₂) s_pmc w_out :=
        p4Data_setVar (by decide) (by decide) (by decide) (by decide)
          (by intro nm hnm
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hnm
              rcases hnm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
          hD₂
      refine htail (setVarHOLFinite (ofString "succeeded") v22 s₂) w₂ succw1 hD₃
        ?_ ?_ ?_ ?_ ?_ ?_
      · rw [p4N_setVar_code]
        exact hc₂
      · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne_ls, hl₂]
      · rw [hv22]
        simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
      · exact hLL₂
      · exact hDF₂
      · exact hdisj₂
  -- instruction 20: the logs dec
  refine p4Run_dec (ofString "logs") .one _ _ ?_
  intro v20 hev20 hsh20
  obtain ⟨wl0, heval, hwl0⟩ :=
    p4N_outLoad h 0x0000000000000010#64 (by decide) (by decide)
  rw [heval] at hev20
  simp only [Option.some.injEq] at hev20
  subst hev20
  have h10 : (0x0000000000000010#64).toNat = 16 := by decide
  rw [h10] at hwl0
  have hD1 : P4Data entry
      (setVarHOLFinite (ofString "logs") (.val (.word wl0)) s) s_pmc w_out :=
    p4Data_setLogs h
  have hcode1 : (setVarHOLFinite (ofString "logs") (.val (.word wl0)) s).code =
      originalRuntimeCode := by
    rw [p4N_setVar_code]
    exact hc
  have hloc1 : (setVarHOLFinite (ofString "logs") (.val (.word wl0)) s).locals.lookup
      (ofString "logs") = some (.val (.word wl0)) := by
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  -- the kept-branch logs facts (out-list identification)
  have hAs : ArenaOK s := h.base.world.1.2
  obtain ⟨⟨_, hbo_nz_e, hbo24_nz_e, hbo32_nz_e, hidx_lt_e⟩, _, hbo40_nz_e, hbo72_nz_e,
    S_e, Nd_e, hWT_e, _⟩ := h.base.ready_entry
  have hD_e : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e Nd_e) := by
    rw [ptxRegions_eq_bufRegions]
    exact validBufList_disj validBufList_ptxBufs hWT_e
  obtain ⟨logs0, hll0, hl_ok0, hl_dj0, hty0⟩ := hD1.logs_facts
  obtain ⟨S_pmc, Nd_pmc, S_cur, Nd_cur, hty01, hty02, hWT_s, hty04, hty05, hty06, hty07,
    h8, h9⟩ := hty0 S_e Nd_e hWT_e hD_e
  have hLLkept : LogsListOK
      (setVarHOLFinite (ofString "logs") (.val (.word wl0)) s) wl0.toNat := by
    rw [hwl0]
    exact hD1.logs_ok
  have hDFkept : LogsDisjFixed
      (setVarHOLFinite (ofString "logs") (.val (.word wl0)) s) wl0.toNat := by
    rw [hwl0]
    exact pmcLogsLiveOwned_disjFixed h8
  -- instruction 21: the null-logs ite
  refine p4Run_ite _ _ .skip _ ?_ ?_
  · refine p4Run_call_local_lst_new hD1 hcode1 _ ?_
    intro lw mid hlw_eq hlw_al hlw_nz hm0 hm8 hm16 hhp_sb hhp_lt hARmid hsp_mid hfmp_mid
      hlst_mid hobjs_mid hDisj_mid hAlloc_mid hFO_mid hgl_mid hlocm hlocl_mid hLLf hDFf
      hDmid hcmid
    have hmem24 : (lw.toNat, 24) ∈ lstObjects mid lw.toNat 8 := by
      rw [hobjs_mid]; simp
    have hmem32 : (lw.toNat + 24, 8) ∈ lstObjects mid lw.toNat 8 := by
      rw [hobjs_mid]; simp
    have hWentry : ∀ k, k < 24 / 8 → WordAt mid (lw.toNat + 8 * k) :=
      (hAlloc_mid _ hmem24).2.1.2.2
    have hbound : lw.toNat + 32 ≤ globN mid "heap_ptr" := by
      have h9 := (hAlloc_mid _ hmem32).2.2.2
      omega
    exact hsucc mid lw hDmid hcmid hlocm hLLf hDFf
      (Or.inr ⟨hm0, hm8, hWentry 0 (by omega), hWentry 1 (by omega), hbound⟩)
  · refine p4RelRunStrong_skip ?_
    exact hsucc _ wl0 hD1 hcode1 hloc1 hLLkept hDFkept (Or.inl hwl0)
