import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4J
import InitECandidate.Solver.Wave8GuestInv.R10Ports.ReadOnly

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

/-! # Phase 4M: the head of the phase-4 spine (instructions 0-19)

Gas accounting over the read-only callee chain (`udiv_small5`, `min`, `max`,
`fee_mul`, `u256_sub`), the two `create_ether` coin transfers, the state-gas
clamp and the four block-output counter updates `bo[0] += tx_regular_gas`,
`bo[8] += tx_state_gas_nat`, `bo[48] += tx_blob_gas_used`,
`bo[16] += tx_gas_used`. -/

/-! ## Fresh-name transport -/

/-- Every local bound by the phase-4 head lies outside the set of names the
`P4Data` invariant tracks, so `p4Data_setVar` applies verbatim. -/
theorem p4Head_freshFacts {nm : MlS}
    (hnm : nm ∈ ([ofString "used_before_refund", ofString "ubr5", ofString "refund",
      ofString "used_after_refund", ofString "tx_gas_used", ofString "tx_gas_left",
      ofString "gra", ofString "priority_fee", ofString "tf", ofString "tx_state_gas",
      ofString "tx_state_gas_nat", ofString "tx_regular_gas"] : List MlS)) :
    ofString "out" ≠ nm ∧ ofString "tx" ≠ nm ∧ ofString "index" ≠ nm ∧
      ofString "logs" ≠ nm ∧
      (∀ name ∈ (["tx", "index", "sender", "gas", "tx_blob_gas_used",
        "price", "intrinsic"] : List String), ofString name ≠ nm) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hnm
  rcases hnm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    refine ⟨by decide, by decide, by decide, by decide, ?_⟩
    intro name hname
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hname
    rcases hname with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## World facts for the bo-counter stores -/

/-- The typing facts the bo-counter stores need: a typed world at the state,
the `TxEnv`, the arena and the bound on the bo record. -/
theorem p4Head_boFacts {F : Type}
    {entry u s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (hD : P4Data entry u s_pmc w_out) :
    ∃ S Nd : List Nat, WorldTypedWith u S Nd ∧ TxEnv u ∧ ArenaReady u ∧
      globN u "bo" + 88 ≤ 2 ^ 64 := by
  have hAR : ArenaReady u := hD.base.world.1
  have hE : TxEnv u := txEnv_of_p4Data hD
  obtain ⟨⟨_, hbo_nz_e, hbo24_nz_e, hbo32_nz_e, hidx_lt_e⟩, hjcap_e, hbo40_nz_e, hbo72_nz_e,
    S_e, Nd_e, hWT_e, _⟩ := hD.base.ready_entry
  have hD_e : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e Nd_e) := by
    rw [ptxRegions_eq_bufRegions]
    exact validBufList_disj validBufList_ptxBufs hWT_e
  obtain ⟨S_c, N_c, _, hWT_u, _, _⟩ := hD.base.typing S_e Nd_e hWT_e hD_e
  obtain ⟨halloc, _⟩ := bo_words hWT_u.2.2.1 hE.bo_nz
  exact ⟨S_c, N_c, hWT_u, hE, hAR, (ivl_allocated_bound hAR.2 halloc).2⟩

/-- The store destination `bo + c` (for a constant `c` inside the 88-byte bo
record) evaluates to a word pinned to `globN u "bo" + c.toNat`. -/
theorem p4Head_dstEval {F : Type} {u : PanSemStateFiniteExact 64 F}
    (hE : TxEnv u) (hbo264 : globN u "bo" + 88 ≤ 2 ^ 64) {c a : BitVec 64}
    (hclt : c.toNat < 88)
    (hev : evalAt u (.op .add [.var .global (ofString "bo"), .const c])
      = some (.val (.word a))) :
    a.toNat = globN u "bo" + c.toNat := by
  obtain ⟨bw, hgl, hbwn⟩ := p4Loop31_boWord hE.bo_nz (by omega)
  have hcomp : evalAt u (.op .add [.var .global (ofString "bo"), .const c]) =
      some (.val (.word (bw + c))) := by
    have hz : c + 0 = c := BitVec.add_zero _
    simp only [evalAt, evalHOLExact, evalListHOLExact, toExact, hgl, valueIsWord, valueWord,
      wordOpHOL, wordOp, List.all, List.map, Option.map, ↓reduceIte, List.foldr,
      Bool.and_self, hz]
  have hval : (.val (.word (bw + c)) : ValueHOL 64) = .val (.word a) :=
    Option.some.inj (hcomp.symm.trans hev)
  injection hval with h1
  injection h1 with h2
  subst h2
  have hadd : (bw + c).toNat = bw.toNat + c.toNat := by
    rw [BitVec.toNat_add]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hadd, hbwn]

/-- The store source `bo[c] + wl` (the bo-cell load at byte offset `c.toNat`
plus a word-valued local) evaluates to a word value. -/
theorem p4Head_srcEval {F : Type} {u : PanSemStateFiniteExact 64 F}
    (hAR : ArenaReady u) (hE : TxEnv u) {S Nd : List Nat} (hWT : WorldTypedWith u S Nd)
    (c : BitVec 64) (hcmod : c.toNat % 8 = 0) (hclt : c.toNat < 88)
    {nm : MlS} {wl : BitVec 64}
    (hlu : u.locals.lookup nm = some (.val (.word wl))) :
    ∃ w : BitVec 64,
      evalAt u (.op .add
        [(.load .one (.op .add [.var .global (ofString "bo"), .const c])),
          (.var .local nm)]) = some (.val (.word w)) := by
  obtain ⟨halloc, hwords⟩ := bo_words hWT.2.2.1 hE.bo_nz
  have hbo264 : globN u "bo" + 88 ≤ 2 ^ 64 := (ivl_allocated_bound hAR.2 halloc).2
  obtain ⟨bw, hgl, hbwn⟩ := p4Loop31_boWord hE.bo_nz (by omega)
  have hoffc : BitVec.ofNat 64 (globN u "bo" + c.toNat) = bw + c := by
    apply BitVec.eq_of_toNat_eq
    have hsumlt : globN u "bo" + c.toNat < 2 ^ 64 := by omega
    rw [BitVec.toNat_ofNat]
    have hadd : (bw + c).toNat = bw.toNat + c.toNat := by
      rw [BitVec.toNat_add]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hadd, hbwn]
    exact Nat.mod_eq_of_lt hsumlt
  have hoffeq : globN u "bo" + 8 * (c.toNat / 8) = globN u "bo" + c.toNat := by omega
  have hw : WordAt u (globN u "bo" + 8 * (c.toNat / 8)) :=
    hwords.2.2 (c.toNat / 8) (by omega)
  rw [hoffeq] at hw
  obtain ⟨w', hdom', hcell'⟩ := hw
  rw [hoffc] at hdom' hcell'
  have hz : c + 0 = c := BitVec.add_zero _
  have hz2 : wl + 0 = wl := BitVec.add_zero _
  refine ⟨w' + wl, ?_⟩
  simp only [evalAt, evalHOLExact, evalListHOLExact, toExact, hgl, hlu, valueIsWord,
    valueWord, wordOpHOL, wordOp, panOpHOL, List.all, List.map, Option.map, ↓reduceIte,
    List.foldr, Bool.and_self, memLoadHOLExact, isWfShapeExactHOL, hz, hdom', hcell', hz2]

/-! ## The four counter stores (instructions 14-19) -/

/-- Instructions 14-19: the block-output counter updates and the trailing
skip.  The word locals `tx_state_gas_nat` and `tx_gas_used` are supplied as
existential diaries because the `ite` at instruction 13 fixes
`tx_state_gas_nat` to either the `tx_state_gas` word or `0`. -/
theorem p4Head_storeRun {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (h : P4Data entry s s_pmc w_out)
    (hc : s.code = originalRuntimeCode)
    (hnsn : ∃ wn : BitVec 64,
      s.locals.lookup (ofString "tx_state_gas_nat") = some (.val (.word wn)))
    (hngu : ∃ wg : BitVec 64,
      s.locals.lookup (ofString "tx_gas_used") = some (.val (.word wg)))
    (rest : ProgHOL 64)
    (htail : ∀ s' : PanSemStateFiniteExact 64 F,
      P4Data entry s' s_pmc w_out → s'.code = originalRuntimeCode →
      PtxRelRunStrong entry rest s') :
    PtxRelRunStrong entry
      (.decCall (ofString "tx_regular_gas") .one (ofString "max")
        [(.op .sub [(.var .local (ofString "used_before_refund")),
          (.var .local (ofString "tx_state_gas_nat"))]),
        (.rfield 2 (.var .local (ofString "intrinsic")))]
        (.seq (.store (.op .add [(.var .global (ofString "bo")),
            (.const 0x0000000000000000#64)])
          (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")),
            (.const 0x0000000000000000#64)])),
            (.var .local (ofString "tx_regular_gas"))]))
        (.seq (.store (.op .add [(.var .global (ofString "bo")),
            (.const 0x0000000000000008#64)])
          (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")),
            (.const 0x0000000000000008#64)])),
            (.var .local (ofString "tx_state_gas_nat"))]))
        (.seq (.store (.op .add [(.var .global (ofString "bo")),
            (.const 0x0000000000000030#64)])
          (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")),
            (.const 0x0000000000000030#64)])),
            (.var .local (ofString "tx_blob_gas_used"))]))
        (.seq (.store (.op .add [(.var .global (ofString "bo")),
            (.const 0x0000000000000010#64)])
          (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")),
            (.const 0x0000000000000010#64)])),
            (.var .local (ofString "tx_gas_used"))]))
        (.seq .skip rest)))))) s := by
  obtain ⟨hnout', hntx', hnidx', hnlogs', hshn'⟩ :=
    p4Head_freshFacts (nm := ofString "tx_regular_gas") (by decide)
  refine p4Run_decCall_ro h hc Wave8Contracts.M15.«ro_max»
    (ofString "tx_regular_gas") .one
    [(.op .sub [(.var .local (ofString "used_before_refund")),
      (.var .local (ofString "tx_state_gas_nat"))]),
    (.rfield 2 (.var .local (ofString "intrinsic")))] _
    (Ne.symm hnout') (Ne.symm hntx') (Ne.symm hnidx') (Ne.symm hnlogs') hshn' ?_
  intro vs body callee ret v post hargs hlook hrun hsh hD14 hpost_code
  obtain ⟨w14, hw14⟩ : ∃ w14 : BitVec 64, v = .val (.word w14) := by
    cases v with
    | val wl => cases wl with
      | word w14 => exact ⟨w14, rfl⟩
    | rStruct _ => simp [shapeOfHOLExact] at hsh
    | nStruct _ _ => simp [shapeOfHOLExact] at hsh
  set s15 : PanSemStateFiniteExact 64 F :=
    setVarHOLFinite (ofString "tx_regular_gas") v { post with locals := s.locals } with hs15
  have hlu14 : s15.locals.lookup (ofString "tx_regular_gas") = some (.val (.word w14)) := by
    simp [hs15, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hw14]
  have hframe15 : ∀ nm : MlS, nm ≠ ofString "tx_regular_gas" →
      s15.locals.lookup nm = s.locals.lookup nm := by
    intro nm hnm
    simp [hs15, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hnm, Ne.symm hnm]
  obtain ⟨wn, hwn⟩ := hnsn
  have hnsn15 : s15.locals.lookup (ofString "tx_state_gas_nat") = some (.val (.word wn)) :=
    (hframe15 (ofString "tx_state_gas_nat") (by decide)).trans hwn
  obtain ⟨wg, hwg15⟩ := hngu
  have hngu15 : s15.locals.lookup (ofString "tx_gas_used") = some (.val (.word wg)) :=
    (hframe15 (ofString "tx_gas_used") (by decide)).trans hwg15
  have hblob15 : ∃ wb : BitVec 64,
      s15.locals.lookup (ofString "tx_blob_gas_used") = some (.val (.word wb)) :=
    hD14.shapes.1 "tx_blob_gas_used" (by simp)
  -- instruction 15: bo[0] += tx_regular_gas
  refine p4Run_store _ _ _ ?_
  intro a15 v15 mem15 hed15 hes15 hmem15
  obtain ⟨S15, Nd15, hWT15, hE15, hAR15, hbo264_15⟩ := p4Head_boFacts hD14
  obtain ⟨w15, hw15⟩ : ∃ w15 : BitVec 64, v15 = .val (.word w15) := by
    obtain ⟨w, hw⟩ := p4Head_srcEval hAR15 hE15 hWT15
      (0x0000000000000000#64 : BitVec 64) (by decide) (by decide) hlu14
    exact ⟨w, (Option.some.inj (hw.symm.trans hes15)).symm⟩
  have hflat15 : flattenHOL v15 = [HolWordLab.word w15] := by rw [hw15]; simp [flattenHOL]
  rw [hflat15] at hmem15
  obtain ⟨hdom15, hval15, hmem15'⟩ := panMemStoresHOL_word_spec hmem15
  have hc0 : (0x0000000000000000#64 : BitVec 64).toNat = 0 := rfl
  have hx_eq15 : a15.toNat = globN s15 "bo" + 0 := by
    have h0 := p4Head_dstEval hE15 hbo264_15 (by decide) hed15
    rwa [hc0] at h0
  have hD16 : P4Data entry ({s15 with memory := mem15} : PanSemStateFiniteExact 64 F)
      s_pmc w_out := p4Data_of_bo_word_store hD14 (off := 0) (by decide) hdom15 hx_eq15 hmem15'
  -- instruction 16: bo[8] += tx_state_gas_nat
  refine p4Run_store _ _ _ ?_
  intro a16 v16 mem16 hed16 hes16 hmem16
  obtain ⟨S16, Nd16, hWT16, hE16, hAR16, hbo264_16⟩ := p4Head_boFacts hD16
  obtain ⟨w16, hw16⟩ : ∃ w16 : BitVec 64, v16 = .val (.word w16) := by
    have hlu16 : ({s15 with memory := mem15} : PanSemStateFiniteExact 64 F).locals.lookup
        (ofString "tx_state_gas_nat") = some (.val (.word wn)) := hnsn15
    obtain ⟨w, hw⟩ := p4Head_srcEval hAR16 hE16 hWT16
      (0x0000000000000008#64 : BitVec 64) (by decide) (by decide) hlu16
    exact ⟨w, (Option.some.inj (hw.symm.trans hes16)).symm⟩
  have hflat16 : flattenHOL v16 = [HolWordLab.word w16] := by rw [hw16]; simp [flattenHOL]
  rw [hflat16] at hmem16
  obtain ⟨hdom16, hval16, hmem16'⟩ := panMemStoresHOL_word_spec hmem16
  have hc8 : (0x0000000000000008#64 : BitVec 64).toNat = 8 := rfl
  have hx_eq16 : a16.toNat = globN ({s15 with memory := mem15} : PanSemStateFiniteExact 64 F)
      "bo" + 8 := by
    have h0 := p4Head_dstEval hE16 hbo264_16 (by decide) hed16
    rwa [hc8] at h0
  have hD17 : P4Data entry
      ({{s15 with memory := mem15} with memory := mem16} : PanSemStateFiniteExact 64 F)
      s_pmc w_out := p4Data_of_bo_word_store hD16 (off := 8) (by decide) hdom16 hx_eq16 hmem16'
  -- instruction 17: bo[48] += tx_blob_gas_used
  refine p4Run_store _ _ _ ?_
  intro a17 v17 mem17 hed17 hes17 hmem17
  obtain ⟨S17, Nd17, hWT17, hE17, hAR17, hbo264_17⟩ := p4Head_boFacts hD17
  obtain ⟨w17, hw17⟩ : ∃ w17 : BitVec 64, v17 = .val (.word w17) := by
    obtain ⟨wb, hwb⟩ := hblob15
    have hlu17 : ({{s15 with memory := mem15} with memory := mem16} :
        PanSemStateFiniteExact 64 F).locals.lookup
        (ofString "tx_blob_gas_used") = some (.val (.word wb)) := hwb
    obtain ⟨w, hw⟩ := p4Head_srcEval hAR17 hE17 hWT17
      (0x0000000000000030#64 : BitVec 64) (by decide) (by decide) hlu17
    exact ⟨w, (Option.some.inj (hw.symm.trans hes17)).symm⟩
  have hflat17 : flattenHOL v17 = [HolWordLab.word w17] := by rw [hw17]; simp [flattenHOL]
  rw [hflat17] at hmem17
  obtain ⟨hdom17, hval17, hmem17'⟩ := panMemStoresHOL_word_spec hmem17
  have hc48 : (0x0000000000000030#64 : BitVec 64).toNat = 48 := rfl
  have hx_eq17 : a17.toNat = globN
      ({{s15 with memory := mem15} with memory := mem16} : PanSemStateFiniteExact 64 F)
      "bo" + 48 := by
    have h0 := p4Head_dstEval hE17 hbo264_17 (by decide) hed17
    rwa [hc48] at h0
  have hD18 : P4Data entry
      ({{{s15 with memory := mem15} with memory := mem16} with memory := mem17} :
        PanSemStateFiniteExact 64 F) s_pmc w_out :=
    p4Data_of_bo_word_store hD17 (off := 48) (by decide) hdom17 hx_eq17 hmem17'
  -- instruction 18: bo[16] += tx_gas_used
  refine p4Run_store _ _ _ ?_
  intro a18 v18 mem18 hed18 hes18 hmem18
  obtain ⟨S18, Nd18, hWT18, hE18, hAR18, hbo264_18⟩ := p4Head_boFacts hD18
  obtain ⟨w18, hw18⟩ : ∃ w18 : BitVec 64, v18 = .val (.word w18) := by
    have hlu18 : ({{{s15 with memory := mem15} with memory := mem16} with memory := mem17} :
        PanSemStateFiniteExact 64 F).locals.lookup
        (ofString "tx_gas_used") = some (.val (.word wg)) := hngu15
    obtain ⟨w, hw⟩ := p4Head_srcEval hAR18 hE18 hWT18
      (0x0000000000000010#64 : BitVec 64) (by decide) (by decide) hlu18
    exact ⟨w, (Option.some.inj (hw.symm.trans hes18)).symm⟩
  have hflat18 : flattenHOL v18 = [HolWordLab.word w18] := by rw [hw18]; simp [flattenHOL]
  rw [hflat18] at hmem18
  obtain ⟨hdom18, hval18, hmem18'⟩ := panMemStoresHOL_word_spec hmem18
  have hc16 : (0x0000000000000010#64 : BitVec 64).toNat = 16 := rfl
  have hx_eq18 : a18.toNat = globN
      ({{{s15 with memory := mem15} with memory := mem16} with memory := mem17} :
        PanSemStateFiniteExact 64 F) "bo" + 16 := by
    have h0 := p4Head_dstEval hE18 hbo264_18 (by decide) hed18
    rwa [hc16] at h0
  have hD19 : P4Data entry
      ({{{{s15 with memory := mem15} with memory := mem16} with memory := mem17} with
        memory := mem18} : PanSemStateFiniteExact 64 F) s_pmc w_out :=
    p4Data_of_bo_word_store hD18 (off := 16) (by decide) hdom18 hx_eq18 hmem18'
  refine p4RelRunStrong_skip ?_
  exact htail _ hD19 hpost_code

/-! ## The state-gas clamp `ite` (instruction 13) -/

/-- Instructions 13-19: the `tx_state_gas_nat` clamp (`< 0` keeps the
clamped value, otherwise `0`) followed by the counter stores. -/
theorem p4Head_afterIte {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (h : P4Data entry s s_pmc w_out)
    (hc : s.code = originalRuntimeCode)
    (hnsn : ∃ wn : BitVec 64,
      s.locals.lookup (ofString "tx_state_gas_nat") = some (.val (.word wn)))
    (hngu : ∃ wg : BitVec 64,
      s.locals.lookup (ofString "tx_gas_used") = some (.val (.word wg)))
    (rest : ProgHOL 64)
    (htail : ∀ s' : PanSemStateFiniteExact 64 F,
      P4Data entry s' s_pmc w_out → s'.code = originalRuntimeCode →
      PtxRelRunStrong entry rest s') :
    PtxRelRunStrong entry
      (.seq (.ite (.cmp .less (.var .local (ofString "tx_state_gas"))
          (.const 0x0000000000000000#64))
        (.assign .local (ofString "tx_state_gas_nat") (.const 0x0000000000000000#64)) .skip)
        (.decCall (ofString "tx_regular_gas") .one (ofString "max")
          [(.op .sub [(.var .local (ofString "used_before_refund")),
            (.var .local (ofString "tx_state_gas_nat"))]),
          (.rfield 2 (.var .local (ofString "intrinsic")))]
          (.seq (.store (.op .add [(.var .global (ofString "bo")),
              (.const 0x0000000000000000#64)])
            (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")),
              (.const 0x0000000000000000#64)])),
              (.var .local (ofString "tx_regular_gas"))]))
          (.seq (.store (.op .add [(.var .global (ofString "bo")),
              (.const 0x0000000000000008#64)])
            (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")),
              (.const 0x0000000000000008#64)])),
              (.var .local (ofString "tx_state_gas_nat"))]))
          (.seq (.store (.op .add [(.var .global (ofString "bo")),
              (.const 0x0000000000000030#64)])
            (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")),
              (.const 0x0000000000000030#64)])),
              (.var .local (ofString "tx_blob_gas_used"))]))
          (.seq (.store (.op .add [(.var .global (ofString "bo")),
              (.const 0x0000000000000010#64)])
            (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")),
              (.const 0x0000000000000010#64)])),
              (.var .local (ofString "tx_gas_used"))]))
          (.seq .skip rest))))))) s := by
  refine p4Run_ite _ _ _ _ ?_ ?_
  · refine p4Run_assign (ofString "tx_state_gas_nat")
      (.const 0x0000000000000000#64) _ ?_
    intro v13 hev13
    have hc013 : evalAt s (ExpHOL.const 0x0000000000000000#64) =
        some (.val (.word 0x0000000000000000#64)) := rfl
    have hv13 : v13 = .val (.word 0x0000000000000000#64) :=
      Option.some.inj (hev13.symm.trans hc013)
    obtain ⟨hnout, hntx, hnidx, hnlogs, hshn⟩ :=
      p4Head_freshFacts (nm := ofString "tx_state_gas_nat") (by decide)
    have hD13 : P4Data entry
        (setVarHOLFinite (ofString "tx_state_gas_nat") v13 s) s_pmc w_out :=
      p4Data_setVar (Ne.symm hnout) (Ne.symm hntx) (Ne.symm hnidx) (Ne.symm hnlogs) hshn h
    have hnsn13 : ∃ wn : BitVec 64,
        (setVarHOLFinite (ofString "tx_state_gas_nat") v13 s).locals.lookup
          (ofString "tx_state_gas_nat") = some (.val (.word wn)) := by
      refine ⟨0x0000000000000000#64, ?_⟩
      simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hv13]
    have hngu13 : ∃ wg : BitVec 64,
        (setVarHOLFinite (ofString "tx_state_gas_nat") v13 s).locals.lookup
          (ofString "tx_gas_used") = some (.val (.word wg)) := by
      obtain ⟨wg, hwg⟩ := hngu
      refine ⟨wg, ?_⟩
      have hne : ofString "tx_gas_used" ≠ ofString "tx_state_gas_nat" := by decide
      simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, Ne.symm hne, hwg]
    exact p4Head_storeRun hD13 hc hnsn13 hngu13 rest htail
  · refine p4RelRunStrong_skip ?_
    exact p4Head_storeRun h hc hnsn hngu rest htail

/-! ## The state-gas `dec`s (instructions 11-12) -/

/-- Instructions 11-19. -/
theorem p4Head_afterDecs {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (h : P4Data entry s s_pmc w_out)
    (hc : s.code = originalRuntimeCode)
    (hngu : ∃ wg : BitVec 64,
      s.locals.lookup (ofString "tx_gas_used") = some (.val (.word wg)))
    (rest : ProgHOL 64)
    (htail : ∀ s' : PanSemStateFiniteExact 64 F,
      P4Data entry s' s_pmc w_out → s'.code = originalRuntimeCode →
      PtxRelRunStrong entry rest s') :
    PtxRelRunStrong entry
      (.dec (ofString "tx_state_gas") .one
        (.op .add [(.rfield 1 (.var .local (ofString "intrinsic"))),
          (.load .one (.op .add [(.var .local (ofString "out")),
            (.const 0x0000000000000048#64)]))])
        (.dec (ofString "tx_state_gas_nat") .one (.var .local (ofString "tx_state_gas"))
          (.seq (.ite (.cmp .less (.var .local (ofString "tx_state_gas"))
              (.const 0x0000000000000000#64))
            (.assign .local (ofString "tx_state_gas_nat") (.const 0x0000000000000000#64)) .skip)
            (.decCall (ofString "tx_regular_gas") .one (ofString "max")
              [(.op .sub [(.var .local (ofString "used_before_refund")),
                (.var .local (ofString "tx_state_gas_nat"))]),
              (.rfield 2 (.var .local (ofString "intrinsic")))]
              (.seq (.store (.op .add [(.var .global (ofString "bo")),
                  (.const 0x0000000000000000#64)])
                (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")),
                  (.const 0x0000000000000000#64)])),
                  (.var .local (ofString "tx_regular_gas"))]))
              (.seq (.store (.op .add [(.var .global (ofString "bo")),
                  (.const 0x0000000000000008#64)])
                (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")),
                  (.const 0x0000000000000008#64)])),
                  (.var .local (ofString "tx_state_gas_nat"))]))
              (.seq (.store (.op .add [(.var .global (ofString "bo")),
                  (.const 0x0000000000000030#64)])
                (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")),
                  (.const 0x0000000000000030#64)])),
                  (.var .local (ofString "tx_blob_gas_used"))]))
              (.seq (.store (.op .add [(.var .global (ofString "bo")),
                  (.const 0x0000000000000010#64)])
                (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")),
                  (.const 0x0000000000000010#64)])),
                  (.var .local (ofString "tx_gas_used"))]))
              (.seq .skip rest))))))))) s := by
  refine p4Run_dec (ofString "tx_state_gas") .one _ _ ?_
  intro v11 hev11 hsh11
  obtain ⟨hnout11, hntx11, hnidx11, hnlogs11, hshn11⟩ :=
    p4Head_freshFacts (nm := ofString "tx_state_gas") (by decide)
  have hD11 : P4Data entry
      (setVarHOLFinite (ofString "tx_state_gas") v11 s) s_pmc w_out :=
    p4Data_setVar (Ne.symm hnout11) (Ne.symm hntx11) (Ne.symm hnidx11)
      (Ne.symm hnlogs11) hshn11 h
  refine p4Run_dec (ofString "tx_state_gas_nat") .one _ _ ?_
  intro v12 hev12 hsh12
  obtain ⟨w12, hw12⟩ : ∃ w12 : BitVec 64, v12 = .val (.word w12) := by
    cases v12 with
    | val wl => cases wl with
      | word w12 => exact ⟨w12, rfl⟩
    | rStruct _ => simp [shapeOfHOLExact] at hsh12
    | nStruct _ _ => simp [shapeOfHOLExact] at hsh12
  obtain ⟨hnout12, hntx12, hnidx12, hnlogs12, hshn12⟩ :=
    p4Head_freshFacts (nm := ofString "tx_state_gas_nat") (by decide)
  have hD12 : P4Data entry
      (setVarHOLFinite (ofString "tx_state_gas_nat") v12
        (setVarHOLFinite (ofString "tx_state_gas") v11 s)) s_pmc w_out :=
    p4Data_setVar (Ne.symm hnout12) (Ne.symm hntx12) (Ne.symm hnidx12)
      (Ne.symm hnlogs12) hshn12 hD11
  have hnsn12 : ∃ wn : BitVec 64,
      (setVarHOLFinite (ofString "tx_state_gas_nat") v12
        (setVarHOLFinite (ofString "tx_state_gas") v11 s)).locals.lookup
        (ofString "tx_state_gas_nat") = some (.val (.word wn)) := by
    refine ⟨w12, ?_⟩
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hw12]
  have hngu12 : ∃ wg : BitVec 64,
      (setVarHOLFinite (ofString "tx_state_gas_nat") v12
        (setVarHOLFinite (ofString "tx_state_gas") v11 s)).locals.lookup
        (ofString "tx_gas_used") = some (.val (.word wg)) := by
    obtain ⟨wg, hwg⟩ := hngu
    refine ⟨wg, ?_⟩
    have hne1 : ofString "tx_gas_used" ≠ ofString "tx_state_gas_nat" := by decide
    have hne2 : ofString "tx_gas_used" ≠ ofString "tx_state_gas" := by decide
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne1, Ne.symm hne1,
      hne2, Ne.symm hne2, hwg]
  exact p4Head_afterIte hD12 hc hnsn12 hngu12 rest htail

/-! ## The two `create_ether` transfers (instructions 9-10) -/

/-- Instructions 9-19. -/
theorem p4Head_afterCreates {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (h : P4Data entry s s_pmc w_out)
    (hc : s.code = originalRuntimeCode)
    (hngu : ∃ wg : BitVec 64,
      s.locals.lookup (ofString "tx_gas_used") = some (.val (.word wg)))
    (rest : ProgHOL 64)
    (htail : ∀ s' : PanSemStateFiniteExact 64 F,
      P4Data entry s' s_pmc w_out → s'.code = originalRuntimeCode →
      PtxRelRunStrong entry rest s') :
    PtxRelRunStrong entry
      (.seq (.call (some (none, none)) (ofString "create_ether")
          [(.var .local (ofString "sender")),
            (.rstruct [(.rfield 1 (.var .local (ofString "gra"))),
              (.rfield 2 (.var .local (ofString "gra"))),
              (.rfield 3 (.var .local (ofString "gra"))),
              (.rfield 4 (.var .local (ofString "gra")))])])
        (.seq (.call (some (none, none)) (ofString "create_ether")
            [(.load .one (.op .add [(.var .global (ofString "be")),
              (.const 0x0000000000000020#64)])),
            (.rstruct [(.rfield 1 (.var .local (ofString "tf"))),
              (.rfield 2 (.var .local (ofString "tf"))),
              (.rfield 3 (.var .local (ofString "tf"))),
              (.rfield 4 (.var .local (ofString "tf")))])])
          (.dec (ofString "tx_state_gas") .one
            (.op .add [(.rfield 1 (.var .local (ofString "intrinsic"))),
              (.load .one (.op .add [(.var .local (ofString "out")),
                (.const 0x0000000000000048#64)]))])
            (.dec (ofString "tx_state_gas_nat") .one (.var .local (ofString "tx_state_gas"))
              (.seq (.ite (.cmp .less (.var .local (ofString "tx_state_gas"))
                  (.const 0x0000000000000000#64))
                (.assign .local (ofString "tx_state_gas_nat")
                  (.const 0x0000000000000000#64)) .skip)
                (.decCall (ofString "tx_regular_gas") .one (ofString "max")
                  [(.op .sub [(.var .local (ofString "used_before_refund")),
                    (.var .local (ofString "tx_state_gas_nat"))]),
                  (.rfield 2 (.var .local (ofString "intrinsic")))]
                  (.seq (.store (.op .add [(.var .global (ofString "bo")),
                      (.const 0x0000000000000000#64)])
                    (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")),
                      (.const 0x0000000000000000#64)])),
                      (.var .local (ofString "tx_regular_gas"))]))
                  (.seq (.store (.op .add [(.var .global (ofString "bo")),
                      (.const 0x0000000000000008#64)])
                    (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")),
                      (.const 0x0000000000000008#64)])),
                      (.var .local (ofString "tx_state_gas_nat"))]))
                  (.seq (.store (.op .add [(.var .global (ofString "bo")),
                      (.const 0x0000000000000030#64)])
                    (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")),
                      (.const 0x0000000000000030#64)])),
                      (.var .local (ofString "tx_blob_gas_used"))]))
                  (.seq (.store (.op .add [(.var .global (ofString "bo")),
                      (.const 0x0000000000000010#64)])
                    (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")),
                      (.const 0x0000000000000010#64)])),
                      (.var .local (ofString "tx_gas_used"))]))
                  (.seq .skip rest))))))))))) s := by
  refine p4Run_call0_create_ether h hc _ _ ?_
  intro vs body callee ret v post1 hargs hlook hrun hstep hD9 hpost9
  have hngu9 : ∃ wg : BitVec 64,
      ({post1 with locals := s.locals} : PanSemStateFiniteExact 64 F).locals.lookup
        (ofString "tx_gas_used") = some (.val (.word wg)) := by
    obtain ⟨wg, hwg⟩ := hngu
    exact ⟨wg, hwg⟩
  refine p4Run_call0_create_ether hD9 hpost9 _ _ ?_
  intro vs body callee ret v post2 hargs hlook hrun hstep hD10 hpost10
  have hngu10 : ∃ wg : BitVec 64,
      ({post2 with locals := ({post1 with locals := s.locals} :
        PanSemStateFiniteExact 64 F).locals} : PanSemStateFiniteExact 64 F).locals.lookup
        (ofString "tx_gas_used") = some (.val (.word wg)) := hngu9
  exact p4Head_afterDecs hD10 hpost10 hngu10 rest htail

/-! ## The full head (instructions 0-19) -/

/-- The head of the phase-4 spine: instructions 0-19, ending in `rest`
(instructions 20 onward). -/
theorem p4Run_head {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (h : P4Data entry s s_pmc w_out)
    (hc : s.code = originalRuntimeCode)
    (rest : ProgHOL 64)
    (htail : ∀ s' : PanSemStateFiniteExact 64 F,
      P4Data entry s' s_pmc w_out → s'.code = originalRuntimeCode →
      PtxRelRunStrong entry rest s') :
    PtxRelRunStrong entry
      (.dec (ofString "used_before_refund") .one
        (.op .sub [(.op .sub [(.var .local (ofString "gas")),
          (.load .one (.op .add [(.var .local (ofString "out")),
            (.const 0x0000000000000000#64)]))]),
        (.load .one (.op .add [(.var .local (ofString "out")),
          (.const 0x0000000000000038#64)]))])
        (.decCall (ofString "ubr5") .one (ofString "udiv_small5")
          [(.var .local (ofString "used_before_refund"))]
          (.decCall (ofString "refund") .one (ofString "min")
            [(.var .local (ofString "ubr5")),
            (.load .one (.op .add [(.var .local (ofString "out")),
              (.const 0x0000000000000008#64)]))]
            (.dec (ofString "used_after_refund") .one
              (.op .sub [(.var .local (ofString "used_before_refund")),
                (.var .local (ofString "refund"))])
              (.decCall (ofString "tx_gas_used") .one (ofString "max")
                [(.var .local (ofString "used_after_refund")),
                (.rfield 2 (.var .local (ofString "intrinsic")))]
                (.dec (ofString "tx_gas_left") .one
                  (.op .sub [(.var .local (ofString "gas")),
                    (.var .local (ofString "tx_gas_used"))])
                  (.decCall (ofString "gra") (.comb [.one, .one, .one, .one, .one])
                    (ofString "fee_mul")
                    [(.var .local (ofString "tx_gas_left")),
                    (.var .local (ofString "price"))]
                    (.decCall (ofString "priority_fee") (.comb [.one, .one, .one, .one])
                      (ofString "u256_sub")
                      [(.var .local (ofString "price")),
                      (.load (.comb [.one, .one, .one, .one])
                        (.op .add [(.var .global (ofString "be")),
                          (.const 0x0000000000000030#64)]))]
                      (.decCall (ofString "tf") (.comb [.one, .one, .one, .one, .one])
                        (ofString "fee_mul")
                        [(.var .local (ofString "tx_gas_used")),
                        (.var .local (ofString "priority_fee"))]
      (.seq (.call (some (none, none)) (ofString "create_ether")
          [(.var .local (ofString "sender")),
            (.rstruct [(.rfield 1 (.var .local (ofString "gra"))),
              (.rfield 2 (.var .local (ofString "gra"))),
              (.rfield 3 (.var .local (ofString "gra"))),
              (.rfield 4 (.var .local (ofString "gra")))])])
        (.seq (.call (some (none, none)) (ofString "create_ether")
            [(.load .one (.op .add [(.var .global (ofString "be")),
              (.const 0x0000000000000020#64)])),
            (.rstruct [(.rfield 1 (.var .local (ofString "tf"))),
              (.rfield 2 (.var .local (ofString "tf"))),
              (.rfield 3 (.var .local (ofString "tf"))),
              (.rfield 4 (.var .local (ofString "tf")))])])
          (.dec (ofString "tx_state_gas") .one
            (.op .add [(.rfield 1 (.var .local (ofString "intrinsic"))),
              (.load .one (.op .add [(.var .local (ofString "out")),
                (.const 0x0000000000000048#64)]))])
            (.dec (ofString "tx_state_gas_nat") .one (.var .local (ofString "tx_state_gas"))
              (.seq (.ite (.cmp .less (.var .local (ofString "tx_state_gas"))
                  (.const 0x0000000000000000#64))
                (.assign .local (ofString "tx_state_gas_nat")
                  (.const 0x0000000000000000#64)) .skip)
                (.decCall (ofString "tx_regular_gas") .one (ofString "max")
                  [(.op .sub [(.var .local (ofString "used_before_refund")),
                    (.var .local (ofString "tx_state_gas_nat"))]),
                  (.rfield 2 (.var .local (ofString "intrinsic")))]
                  (.seq (.store (.op .add [(.var .global (ofString "bo")),
                      (.const 0x0000000000000000#64)])
                    (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")),
                      (.const 0x0000000000000000#64)])),
                      (.var .local (ofString "tx_regular_gas"))]))
                  (.seq (.store (.op .add [(.var .global (ofString "bo")),
                      (.const 0x0000000000000008#64)])
                    (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")),
                      (.const 0x0000000000000008#64)])),
                      (.var .local (ofString "tx_state_gas_nat"))]))
                  (.seq (.store (.op .add [(.var .global (ofString "bo")),
                      (.const 0x0000000000000030#64)])
                    (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")),
                      (.const 0x0000000000000030#64)])),
                      (.var .local (ofString "tx_blob_gas_used"))]))
                  (.seq (.store (.op .add [(.var .global (ofString "bo")),
                      (.const 0x0000000000000010#64)])
                    (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")),
                      (.const 0x0000000000000010#64)])),
                      (.var .local (ofString "tx_gas_used"))]))
                  (.seq .skip rest)))))))))))))))))))) s := by
  -- instruction 0: dec used_before_refund
  refine p4Run_dec (ofString "used_before_refund") .one _ _ ?_
  intro v0 hev0 hsh0
  obtain ⟨hnout0, hntx0, hnidx0, hnlogs0, hshn0⟩ :=
    p4Head_freshFacts (nm := ofString "used_before_refund") (by decide)
  have hD1 : P4Data entry
      (setVarHOLFinite (ofString "used_before_refund") v0 s) s_pmc w_out :=
    p4Data_setVar (Ne.symm hnout0) (Ne.symm hntx0) (Ne.symm hnidx0)
      (Ne.symm hnlogs0) hshn0 h
  set s1 : PanSemStateFiniteExact 64 F :=
    setVarHOLFinite (ofString "used_before_refund") v0 s with hs1
  -- instruction 1: decCall ubr5 := udiv_small5(used_before_refund)
  obtain ⟨hnout1, hntx1, hnidx1, hnlogs1, hshn1⟩ :=
    p4Head_freshFacts (nm := ofString "ubr5") (by decide)
  refine p4Run_decCall_ro hD1 hc Wave8Contracts.M18.«ro_udiv_small5»
    (ofString "ubr5") .one _ _ (Ne.symm hnout1) (Ne.symm hntx1) (Ne.symm hnidx1)
    (Ne.symm hnlogs1) hshn1 ?_
  intro vs body callee ret v1 post1 hargs1 hlook1 hrun1 hsh1 hD2 hpost1
  set s2 : PanSemStateFiniteExact 64 F :=
    setVarHOLFinite (ofString "ubr5") v1 { post1 with locals := s1.locals } with hs2
  -- instruction 2: decCall refund := min(ubr5, out[8])
  obtain ⟨hnout2, hntx2, hnidx2, hnlogs2, hshn2⟩ :=
    p4Head_freshFacts (nm := ofString "refund") (by decide)
  refine p4Run_decCall_ro hD2 hpost1 Wave8Contracts.M15.«ro_min»
    (ofString "refund") .one _ _ (Ne.symm hnout2) (Ne.symm hntx2) (Ne.symm hnidx2)
    (Ne.symm hnlogs2) hshn2 ?_
  intro vs body callee ret v2 post2 hargs2 hlook2 hrun2 hsh2 hD3 hpost2
  set s3 : PanSemStateFiniteExact 64 F :=
    setVarHOLFinite (ofString "refund") v2 { post2 with locals := s2.locals } with hs3
  -- instruction 3: dec used_after_refund := used_before_refund - refund
  refine p4Run_dec (ofString "used_after_refund") .one _ _ ?_
  intro v3 hev3 hsh3
  obtain ⟨hnout3, hntx3, hnidx3, hnlogs3, hshn3⟩ :=
    p4Head_freshFacts (nm := ofString "used_after_refund") (by decide)
  have hD4 : P4Data entry
      (setVarHOLFinite (ofString "used_after_refund") v3 s3) s_pmc w_out :=
    p4Data_setVar (Ne.symm hnout3) (Ne.symm hntx3) (Ne.symm hnidx3)
      (Ne.symm hnlogs3) hshn3 hD3
  set s4 : PanSemStateFiniteExact 64 F :=
    setVarHOLFinite (ofString "used_after_refund") v3 s3 with hs4
  -- instruction 4: decCall tx_gas_used := max(used_after_refund, intrinsic[2])
  obtain ⟨hnout4, hntx4, hnidx4, hnlogs4, hshn4⟩ :=
    p4Head_freshFacts (nm := ofString "tx_gas_used") (by decide)
  refine p4Run_decCall_ro hD4 hpost2
    Wave8Contracts.M15.«ro_max» (ofString "tx_gas_used") .one _ _
    (Ne.symm hnout4) (Ne.symm hntx4) (Ne.symm hnidx4) (Ne.symm hnlogs4) hshn4 ?_
  intro vs body callee ret v4 post4 hargs4 hlook4 hrun4 hsh4 hD5 hpost4
  obtain ⟨w4, hw4⟩ : ∃ w4 : BitVec 64, v4 = .val (.word w4) := by
    cases v4 with
    | val wl => cases wl with
      | word w4 => exact ⟨w4, rfl⟩
    | rStruct _ => simp [shapeOfHOLExact] at hsh4
    | nStruct _ _ => simp [shapeOfHOLExact] at hsh4
  set s5 : PanSemStateFiniteExact 64 F :=
    setVarHOLFinite (ofString "tx_gas_used") v4 { post4 with locals := s4.locals } with hs5
  -- instruction 5: dec tx_gas_left := gas - tx_gas_used
  refine p4Run_dec (ofString "tx_gas_left") .one _ _ ?_
  intro v5 hev5 hsh5
  obtain ⟨hnout5, hntx5, hnidx5, hnlogs5, hshn5⟩ :=
    p4Head_freshFacts (nm := ofString "tx_gas_left") (by decide)
  have hD6 : P4Data entry
      (setVarHOLFinite (ofString "tx_gas_left") v5 s5) s_pmc w_out :=
    p4Data_setVar (Ne.symm hnout5) (Ne.symm hntx5) (Ne.symm hnidx5)
      (Ne.symm hnlogs5) hshn5 hD5
  set s6 : PanSemStateFiniteExact 64 F :=
    setVarHOLFinite (ofString "tx_gas_left") v5 s5 with hs6
  -- instruction 6: decCall gra := fee_mul(tx_gas_left, price)
  obtain ⟨hnout6, hntx6, hnidx6, hnlogs6, hshn6⟩ :=
    p4Head_freshFacts (nm := ofString "gra") (by decide)
  refine p4Run_decCall_ro hD6 hpost4
    InitECandidate.Solver.Wave8GuestInv.R10Ports.ro_fee_mul
    (ofString "gra") (.comb [.one, .one, .one, .one, .one]) _ _
    (Ne.symm hnout6) (Ne.symm hntx6) (Ne.symm hnidx6) (Ne.symm hnlogs6) hshn6 ?_
  intro vs body callee ret v6 post6 hargs6 hlook6 hrun6 hsh6 hD7 hpost6
  set s7 : PanSemStateFiniteExact 64 F :=
    setVarHOLFinite (ofString "gra") v6 { post6 with locals := s6.locals } with hs7
  -- instruction 7: decCall priority_fee := u256_sub(price, be[0x30])
  obtain ⟨hnout7, hntx7, hnidx7, hnlogs7, hshn7⟩ :=
    p4Head_freshFacts (nm := ofString "priority_fee") (by decide)
  refine p4Run_decCall_ro hD7 hpost6 Wave8Contracts.M18.«ro_u256_sub»
    (ofString "priority_fee") (.comb [.one, .one, .one, .one]) _ _
    (Ne.symm hnout7) (Ne.symm hntx7) (Ne.symm hnidx7) (Ne.symm hnlogs7) hshn7 ?_
  intro vs body callee ret v7 post7 hargs7 hlook7 hrun7 hsh7 hD8 hpost7
  set s8 : PanSemStateFiniteExact 64 F :=
    setVarHOLFinite (ofString "priority_fee") v7 { post7 with locals := s7.locals } with hs8
  -- instruction 8: decCall tf := fee_mul(tx_gas_used, priority_fee)
  obtain ⟨hnout8, hntx8, hnidx8, hnlogs8, hshn8⟩ :=
    p4Head_freshFacts (nm := ofString "tf") (by decide)
  refine p4Run_decCall_ro hD8 hpost7
    InitECandidate.Solver.Wave8GuestInv.R10Ports.ro_fee_mul
    (ofString "tf") (.comb [.one, .one, .one, .one, .one]) _ _
    (Ne.symm hnout8) (Ne.symm hntx8) (Ne.symm hnidx8) (Ne.symm hnlogs8) hshn8 ?_
  intro vs body callee ret v8 post8 hargs8 hlook8 hrun8 hsh8 hD9' hpost8
  set s9 : PanSemStateFiniteExact 64 F :=
    setVarHOLFinite (ofString "tf") v8 { post8 with locals := s8.locals } with hs9
  -- instruction 9: call create_ether(sender, gra×4)
  refine p4Run_call0_create_ether hD9' hpost8 _ _ ?_
  intro vs body callee ret v post9 hargs hlook hrun hstep hD9 hpost9
  -- instruction 10: call create_ether(be[0x20], tf×4)
  refine p4Run_call0_create_ether hD9 hpost9 _ _ ?_
  intro vs body callee ret v post10 hargs hlook hrun hstep hD10 hpost10
  have hne_tgl : ofString "tx_gas_used" ≠ ofString "tx_gas_left" := by decide
  have hne_gra : ofString "tx_gas_used" ≠ ofString "gra" := by decide
  have hne_pf : ofString "tx_gas_used" ≠ ofString "priority_fee" := by decide
  have hne_tf : ofString "tx_gas_used" ≠ ofString "tf" := by decide
  have hgu10 : ∃ wg : BitVec 64,
      ({post10 with locals := ({post9 with locals := s9.locals} :
        PanSemStateFiniteExact 64 F).locals} : PanSemStateFiniteExact 64 F).locals.lookup
        (ofString "tx_gas_used") = some (.val (.word wg)) := by
    refine ⟨w4, ?_⟩
    simp [hs9, hs8, hs7, hs6, hs5, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      hne_tf, Ne.symm hne_tf, hne_pf, Ne.symm hne_pf, hne_gra, Ne.symm hne_gra,
      hne_tgl, Ne.symm hne_tgl, hw4]
  exact p4Head_afterDecs hD10 hpost10 hgu10 rest htail
