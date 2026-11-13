import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4C

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

/-! # Phase 4D: the `encode_receipt` engine (instruction 25)

`encode_receipt` is the one phase-4 callee that writes outside the fresh heap
gap: it fills the two global keccak scratch buffers. Its relational spec
`«wk_encode_receipt»` carries `R` = the two keccak buffer regions, which are
members of `ptxBufs`, so the step is transported with
`p4Data_step_of_worldStepScBo`. The `PtxBlockOutUnhit` half of the
`WorldStepScBo` comes from `encode_receipt_main`'s `HeapByteEff` output via
`ptxBlockOutUnhit_of_heapByteEff` (the keccak buffers are separated from the
block-output objects by `PtxP34.blockOut_disj_global_buffer`). -/

/-- The keccak buffers written by `encode_receipt` form a valid buffer list. -/
theorem validBufList_keccak :
    ValidBufList [("keccak_pad", 136), ("keccak_st", 200)] := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨136, by decide, by decide, le_rfl⟩
  · exact ⟨200, by decide, by decide, le_rfl⟩

/-- Both keccak buffers are phase-transaction buffers with non-`ptxGlobals`
names. -/
theorem keccak_bufs_sub :
    ∀ p ∈ [("keccak_pad", 136), ("keccak_st", 200)], p ∈ ptxBufs ∧ p.1 ∉ ptxGlobals := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨by simp [ptxBufs], by decide⟩
  · exact ⟨by simp [ptxBufs], by decide⟩

/-- Four-word-parameter lookup helper with arbitrary return shape (needed for
`encode_receipt`, whose result shape is `.comb [.one, .one]`); four-word
analogue of `GuestTrapAndLookup.pan_three_word_lookup`. -/
private theorem pan_four_word_lookup_comb {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name first second third fourth : MlS) (body : ProgHOL width)
    (w1 w2 w3 w4 : BitVec width) {rs : ShapeHOL}
    (d12 : first ≠ second) (d13 : first ≠ third) (d14 : first ≠ fourth)
    (d23 : second ≠ third) (d24 : second ≠ fourth) (d34 : third ≠ fourth)
    (lookup : code name =
      some ([(first, .one), (second, .one), (third, .one), (fourth, .one)], body, rs)) :
    PanSemStateFiniteExact.lookupCodeHOLFinite code name
        [.val (.word w1), .val (.word w2), .val (.word w3), .val (.word w4)] =
      some (body, (((HolFiniteMapExact.empty.update (first, .val (.word w1))).update
        (second, .val (.word w2))).update (third, .val (.word w3))).update
        (fourth, .val (.word w4)), rs) := by
  have raw : lookupCodeHOLExact code name
        [.val (.word w1), .val (.word w2), .val (.word w3), .val (.word w4)] =
      some (body, (fun key => if key = fourth then some (.val (.word w4)) else
        if key = third then some (.val (.word w3)) else
        if key = second then some (.val (.word w2)) else
        if key = first then some (.val (.word w1)) else none), rs) := by
    simp [lookupCodeHOLExact, lookup, shapeOfHOLExact, shapeEqHOL,
      d12, d13, d14, d23, d24, d34]
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i missing
    rw [raw] at missing
    cases missing
  · rename_i foundBody foundLocals foundShape found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun locals => some (foundBody, locals, foundShape))
    apply HolFiniteMapExact.ext
    funext key
    by_cases h4 : key = fourth
    · subst key
      simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]
    · have hb4 := Ne.symm h4
      by_cases h3 : key = third
      · subst key
        simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY,
          d34, Ne.symm d34]
      · have hb3 := Ne.symm h3
        by_cases h2 : key = second
        · subst key
          simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY,
            d23, Ne.symm d23, d24, Ne.symm d24]
        · have hb2 := Ne.symm h2
          by_cases h1 : key = first
          · subst key
            simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY,
              d12, Ne.symm d12, d13, Ne.symm d13, d14, Ne.symm d14]
          · have hb1 := Ne.symm h1
            simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY,
              h1, h2, h3, h4, hb1, hb2, hb3, hb4]

/-- The inst-25 engine: `decCall "rc" encode_receipt(...)`.  The callee
returns a two-word struct into the local `rc`; the continuation receives the
decomposed words `a`, `b` together with the new state. -/
theorem p4Run_decCall_encode_receipt {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (h : P4Data entry s s_pmc w_out)
    (hc : s.code = originalRuntimeCode)
    (args : List (ExpHOL 64)) (txw succw cgasw logsw : BitVec 64) (tail : ProgHOL 64)
    (harg : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args =
      some [.val (.word txw), .val (.word succw), .val (.word cgasw), .val (.word logsw)])
    (hLL : LogsListOK s logsw.toNat) (hDF : LogsDisjFixed s logsw.toNat)
    (htail : ∀ (a b : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      a.toNat < 2 ^ 61 → b.toNat < 2 ^ 61 →
      b.toNat < 2 ^ 40 →
      mid.locals.lookup (ofString "rc") = some (.rStruct [.val (.word a), .val (.word b)]) →
      (∀ y, y ≠ ofString "rc" → mid.locals.lookup y = s.locals.lookup y) →
      HeapByteEff s mid (receiptKeccakIvls s) ["heap_ptr"] →
      LogsListOK mid logsw.toNat →
      P4Data entry mid s_pmc w_out →
      mid.code = originalRuntimeCode →
      PtxRelRunStrong entry tail mid) :
    PtxRelRunStrong entry
      (.decCall (ofString "rc") (.comb [.one, .one]) (ofString "encode_receipt") args tail) s := by
  intro hres
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hres ⊢
  rw [harg] at hres ⊢
  dsimp only at hres ⊢
  have hlk := pan_four_word_lookup_comb s.code.lookup (ofString "encode_receipt")
    (ofString "tx_type") (ofString "succeeded") (ofString "cumulative_gas") (ofString "logs")
    (sourceFnBody Guest.Software.guestFn_encode_receipt) txw succw cgasw logsw
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hc]; exact WkBlockTxEnc.lookup_encode_receipt)
  rw [hlk] at hres ⊢
  dsimp only at hres ⊢
  by_cases hcz : s.clock = 0
  · simp only [hcz, ↓reduceIte] at hres
    exact absurd hres (by rintro (⟨_, hh⟩ | ⟨_, _, hh, _⟩) <;> simp at hh)
  · simp only [hcz, ↓reduceIte] at hres ⊢
    set cmap := (((HolFiniteMapExact.empty.update
        (ofString "tx_type", ValueHOL.val (.word txw))).update
        (ofString "succeeded", ValueHOL.val (.word succw))).update
        (ofString "cumulative_gas", ValueHOL.val (.word cgasw))).update
        (ofString "logs", ValueHOL.val (.word logsw)) with hcmap_def
    have hAR_ent : ArenaReady (callEntryStateHOLFinite s cmap) :=
      (arenaReady_with_locals s cmap (s.clock - 1)).2 h.base.world.1
    have hent_logs : (callEntryStateHOLFinite s cmap).locals.lookup (ofString "logs") =
        some (.val (.word logsw)) := by
      simp [callEntryStateHOLFinite, hcmap_def, HolFiniteMapExact.lookup_update, FUPDATE]
    have hW_ent : WorldOK (callEntryStateHOLFinite s cmap) :=
      PtxP1.worldOK_callEntry h.base.world cmap
    have hLL_ent : LogsListOK (callEntryStateHOLFinite s cmap)
        (locN (callEntryStateHOLFinite s cmap) "logs") := by
      simp only [locN, hent_logs]
      exact hLL
    have hDF_ent : LogsDisjFixed (callEntryStateHOLFinite s cmap)
        (locN (callEntryStateHOLFinite s cmap) "logs") := by
      simp only [locN, hent_logs]
      exact hDF
    have hcode' : (callEntryStateHOLFinite s cmap).code = originalRuntimeCode := hc
    have hparams : ∃ values,
        PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
          (ofString "encode_receipt") values =
        some (sourceFnBody Guest.Software.guestFn_encode_receipt,
          (callEntryStateHOLFinite s cmap).locals, .comb [.one, .one]) := by
      refine ⟨[.val (.word txw), .val (.word succw), .val (.word cgasw), .val (.word logsw)], ?_⟩
      rw [← hc]
      exact hlk
    have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
      (callEntryStateHOLFinite s cmap) (sourceFnBody Guest.Software.guestFn_encode_receipt)).1
    rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_encode_receipt) with ⟨rb, sb⟩
    have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_encode_receipt) = (rb, sb) := hb
    rw [hb] at hmeta
    simp only [hb] at hres ⊢
    cases rb with
    | none => exact absurd hres (by rintro (⟨_, hh⟩ | ⟨_, _, hh, _⟩) <;> simp at hh)
    | some cr =>
      cases cr with
      | timeOut | error | «break» | «continue» | finalFfi _ =>
        exact absurd hres (by rintro (⟨_, hh⟩ | ⟨_, _, hh, _⟩) <;> simp at hh)
      | exception eid ev =>
        dsimp only at hres ⊢
        have hspec := PtxP1.funSpec_at_lookup (R16Shards.WkBlockTxEnc.«wk_encode_receipt») s hc
          [.val (.word txw), .val (.word succw), .val (.word cgasw), .val (.word logsw)]
          (sourceFnBody Guest.Software.guestFn_encode_receipt)
          cmap (.comb [.one, .one]) hlk ⟨hW_ent, hLL_ent, hDF_ent⟩ (by rw [hb']; simp)
        rw [hb'] at hspec
        have hstep_bo : WorldStep (bufRegions [("keccak_pad", 136), ("keccak_st", 200)])
            ["heap_ptr"] stdKeep RetReceiptBounded (callEntryStateHOLFinite s cmap)
            (some (.exception eid ev)) sb := by
          refine worldStep_congr_R ?_ (hspec hres)
          rfl
        have hstep_s : WorldStep (bufRegions [("keccak_pad", 136), ("keccak_st", 200)])
            ["heap_ptr"] stdKeep NoExtra s (some (.exception eid ev)) sb := by
          refine worldStep_congr_R ?_
            (R13Shards.worldStep_with_locals hstep_bo s.locals s.clock)
          rfl
        have hex := ptxRelBase_exception_worldStep h.base validBufList_keccak keccak_bufs_sub
          (fun g hg => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
            subst hg
            decide)
          ptxKeepSub_stdKeep hstep_s
        exact ptxWorldStep_strong_with_locals_right' .empty sb.clock hex
      | returned v =>
        dsimp only at hres ⊢
        have hres_raw : Resumes (evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
            (sourceFnBody Guest.Software.guestFn_encode_receipt)).1 := by
          rw [hb']; exact Or.inl ⟨v, rfl⟩
        have hmain := encode_receipt_main (callEntryStateHOLFinite s cmap)
          hcode' hW_ent hLL_ent hDF_ent hparams (by rw [hb']; simp) hres_raw
        have hrun_snd : (evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
            (sourceFnBody Guest.Software.guestFn_encode_receipt)).2 = sb := congrArg Prod.snd hb'
        rw [hrun_snd] at hmain
        obtain ⟨a, b, rfl, hins, ha61, hb61, hmemlen, hlogs_sb⟩ :=
          hmain.2 v (congrArg Prod.fst hb')
        by_cases hsh : (shapeEqHOL (shapeOfHOLExact
              (.rStruct [.val (.word a), .val (.word b)] : ValueHOL 64))
              (.comb [.one, .one]) &&
            shapeEqHOL (shapeOfHOLExact
              (.rStruct [.val (.word a), .val (.word b)] : ValueHOL 64))
              (.comb [.one, .one])) = true
        · simp only [hsh, ↓reduceIte] at hres ⊢
          have hspec := PtxP1.funSpec_at_lookup (R16Shards.WkBlockTxEnc.«wk_encode_receipt») s hc
            [.val (.word txw), .val (.word succw), .val (.word cgasw), .val (.word logsw)]
            (sourceFnBody Guest.Software.guestFn_encode_receipt)
            cmap (.comb [.one, .one]) hlk ⟨hW_ent, hLL_ent, hDF_ent⟩ (by rw [hb']; simp)
          rw [hb'] at hspec
          have hstep_bo : WorldStep (bufRegions [("keccak_pad", 136), ("keccak_st", 200)])
              ["heap_ptr"] stdKeep RetReceiptBounded (callEntryStateHOLFinite s cmap)
              (some (.returned (.rStruct [.val (.word a), .val (.word b)]))) sb := by
            refine worldStep_congr_R ?_ (hspec (Or.inl ⟨
              (.rStruct [.val (.word a), .val (.word b)] : ValueHOL 64), rfl⟩))
            rfl
          have hstep_s : WorldStep (bufRegions [("keccak_pad", 136), ("keccak_st", 200)])
              ["heap_ptr"] stdKeep NoExtra s
              (some (.returned (.rStruct [.val (.word a), .val (.word b)]))) sb := by
            refine worldStep_congr_R ?_
              (R13Shards.worldStep_with_locals hstep_bo s.locals s.clock)
            rfl
          have hsp : globN sb "scratch_ptr" ≤ globN s "scratch_ptr" :=
            Nat.le_of_eq (globN_eq_of_lookup (hstep_s.2.2.1 _ (by decide)))
          obtain ⟨⟨_, hbo_nz_e, hbo24_nz_e, hbo32_nz_e, hidx_lt_e⟩, _, hbo40_nz_e, hbo72_nz_e,
            S_e, Nd_e, hWT_e, _⟩ := h.base.ready_entry
          have hD_e : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e Nd_e) := by
            rw [ptxRegions_eq_bufRegions]
            exact validBufList_disj validBufList_ptxBufs hWT_e
          obtain ⟨logs, hll, hl_ok, hl_dj, hty⟩ := h.logs_facts
          obtain ⟨S_pmc, Nd_pmc, S_cur, Nd_cur, hty1, hty2, hWT_s, hty4, hty5, hty6, hty7, hty8,
            hty9⟩ := hty S_e Nd_e hWT_e hD_e
          have hWT_ent : WorldTypedWith (callEntryStateHOLFinite s cmap) S_cur Nd_cur :=
            (R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals s cmap (s.clock - 1)
              S_cur Nd_cur).2 hWT_s
          have hR_disj : ∀ j ∈ receiptKeccakIvls (callEntryStateHOLFinite s cmap),
              ∀ i ∈ blockOutObjects (callEntryStateHOLFinite s cmap), Disj i j := by
            intro j hj i hi
            simp only [receiptKeccakIvls, List.mem_cons, List.not_mem_nil, or_false] at hj
            rcases hj with rfl | rfl
            · exact PtxP34.blockOut_disj_global_buffer hWT_ent.2.2.1 hi
                (g := ("keccak_pad", 136)) (by decide)
            · exact PtxP34.blockOut_disj_global_buffer hWT_ent.2.2.1 hi
                (g := ("keccak_st", 200)) (by decide)
          have hbo_ent : PtxBlockOutUnhit (callEntryStateHOLFinite s cmap) sb :=
            ptxBlockOutUnhit_of_heapByteEff hW_ent hmain.1 hR_disj
          have hbo : PtxBlockOutUnhit s sb := hbo_ent
          have hscbo : WorldStepScBo (bufRegions [("keccak_pad", 136), ("keccak_st", 200)])
              ["heap_ptr"] stdKeep NoExtra s
              (some (.returned (.rStruct [.val (.word a), .val (.word b)]))) sb :=
            ⟨⟨hstep_s, hsp⟩, fun _ => hbo⟩
          have hdata_sb : P4Data entry { sb with locals := s.locals, clock := sb.clock }
              s_pmc w_out :=
            p4Data_step_of_worldStepScBo h validBufList_keccak keccak_bufs_sub
              (fun g hg => by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
                subst hg
                decide)
              (by decide) (by decide) ptxKeepSub_stdKeep (by decide)
              (Or.inr (by simp [stdKeep])) hscbo
              (Or.inr (Or.inr (Or.inr ⟨
                (.rStruct [.val (.word a), .val (.word b)] : ValueHOL 64), rfl⟩)))
          have hshn : ∀ nm ∈ (["tx", "index", "sender", "gas", "tx_blob_gas_used",
              "price", "intrinsic"] : List String), ofString nm ≠ ofString "rc" := by
            intro nm hnm
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hnm
            rcases hnm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
          have hdata_mid : P4Data entry
              (setVarHOLFinite (ofString "rc")
                (.rStruct [.val (.word a), .val (.word b)]) { sb with locals := s.locals })
              s_pmc w_out :=
            p4Data_setVar (by decide) (by decide) (by decide) (by decide) hshn hdata_sb
          have hloc_name : (setVarHOLFinite (ofString "rc")
              (.rStruct [.val (.word a), .val (.word b)])
              { sb with locals := s.locals }).locals.lookup (ofString "rc") =
              some (.rStruct [.val (.word a), .val (.word b)]) := by
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hloc_rest : ∀ y, y ≠ ofString "rc" → (setVarHOLFinite (ofString "rc")
              (.rStruct [.val (.word a), .val (.word b)])
              { sb with locals := s.locals }).locals.lookup y = s.locals.lookup y := by
            intro y hy
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hy, Ne.symm hy]
          have hAR_s : ArenaReady s := h.base.world.1
          have heff_ent : HeapByteEff s (callEntryStateHOLFinite s cmap)
              (receiptKeccakIvls s) ["heap_ptr"] :=
            ((HeapByteEff.refl hAR_s (receiptKeccakIvls s) []).locals_clock
              (callEntryStateHOLFinite s cmap).locals
              (callEntryStateHOLFinite s cmap).clock).mono
              (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩) (fun _ h => by cases h)
          have heff_sb : HeapByteEff s sb (receiptKeccakIvls s) ["heap_ptr"] :=
            heff_ent.trans hmain.1
          have heff_mid : HeapByteEff s
              (setVarHOLFinite (ofString "rc")
                (.rStruct [.val (.word a), .val (.word b)]) { sb with locals := s.locals })
              (receiptKeccakIvls s) ["heap_ptr"] :=
            heff_sb.locals_clock
              (setVarHOLFinite (ofString "rc")
                (.rStruct [.val (.word a), .val (.word b)]) { sb with locals := s.locals }).locals
              (setVarHOLFinite (ofString "rc")
                (.rStruct [.val (.word a), .val (.word b)]) { sb with locals := s.locals }).clock
          have hLL_sb : LogsListOK sb logsw.toNat := by
            simp only [locN, hent_logs] at hlogs_sb
            exact hlogs_sb
          have hLL_mid : LogsListOK
              (setVarHOLFinite (ofString "rc")
                (.rStruct [.val (.word a), .val (.word b)]) { sb with locals := s.locals })
              logsw.toNat := hLL_sb
          have hb40 : b.toNat < 2 ^ 40 := by
            have hlim : globN sb "heap_ptr" ≤ heapLimit := hstep_s.1.2.2.1
            have hlv : heapLimit = 2952790016 := heapLimit_val
            have hin2 : a.toNat + b.toNat ≤ globN sb "heap_ptr" := hins.2
            omega
          have hmid := htail a b
            (setVarHOLFinite (ofString "rc")
              (.rStruct [.val (.word a), .val (.word b)]) { sb with locals := s.locals })
            ha61 hb61 hb40 hloc_name hloc_rest heff_mid hLL_mid hdata_mid (hmeta.trans hc) hres
          exact ptxWorldStep_strong_with_locals_right'
            (HolFiniteMapExact.resVarEq
              (evaluateHOLFiniteState (setVarHOLFinite (ofString "rc")
                (.rStruct [.val (.word a), .val (.word b)])
                { sb with locals := s.locals }) tail).2.locals
              (ofString "rc", s.locals.lookup (ofString "rc")))
            (evaluateHOLFiniteState (setVarHOLFinite (ofString "rc")
              (.rStruct [.val (.word a), .val (.word b)])
              { sb with locals := s.locals }) tail).2.clock hmid
        · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hres
          exact absurd hres (by rintro (⟨_, hh⟩ | ⟨_, _, hh, _⟩) <;> simp at hh)
