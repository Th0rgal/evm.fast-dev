import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group10CallsHelpers2

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards (evmInvAt_of_htab_step evaluate_be_eq)
open InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue (noCatchableRaise evaluate_noCatchableRaise)
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8Contracts.M23

/-! ## Milestone 4 (call family): `op_staticcall` / `op_callcode` / `op_call` -/

/-- A single head-frame word store preserves `GuestInv` (only memory *values* change). -/
theorem guestInv_updW_g10 {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hAs : GuestInv s) (a : BitVec 64) (w : BitVec 64) :
    GuestInv { s with memory := R14Shards.OpHandlersA.updW s.memory a w } :=
  ⟨hAs.1, hAs.2, hAs.3, hAs.4⟩

/-- Preservation of `EvmInv`, `HeadMemChainWF`, `evmChain` and the `evmR` bound
under a single word store at head offset `k = 184` (stipend un-charge) or `k = 72`
(reservoir clear). -/
theorem evOff_store_evmStep_g10 {F : Type}
    {Q : PanSemStateFiniteExact 64 F → Prop}
    (t : PanSemStateFiniteExact 64 F) (w : BitVec 64) (k : Nat)
    (hk : k = 184 ∨ k = 72)
    (hInv : EvmInv t) (hWF : Group10.HeadMemChainWF t) :
    EvmInv { t with memory := R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (globN t "ev" + k)) w } ∧
    Group10.HeadMemChainWF { t with memory := R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (globN t "ev" + k)) w } ∧
    evmChain { t with memory := R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (globN t "ev" + k)) w } = evmChain t ∧
    evmR { t with memory := R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (globN t "ev" + k)) w } ≤ evmR t := by
  have hk280 : k < 280 ∧ k ≠ 24 ∧ k ≠ 32 ∧ k ≠ 40 ∧ k ≠ 64 ∧ k ≠ 192 := by rcases hk <;> omega
  obtain ⟨hAR, S, hWT, hrest⟩ := hInv
  dsimp only at hrest
  obtain ⟨hch_ne, hch_len, hlast, hFWF, hFRoom, hRetW, hPair, hDisj, hTries, hMarks, hRoles, hGasSum⟩ := hrest
  set e0 := globN t "ev"
  set c0 := globN t "cur_cont"
  have hec0_mem : (e0, c0) ∈ evmChain t := by simp [evmChain, evmChainFrom, e0, c0]
  have hF0 := hFWF (e0, c0) hec0_mem
  have he0_blk := hF0.1 (e0, 280) (by simp)
  have he0_lt : e0 + 280 < 2 ^ 64 := by
    have := he0_blk.1.2; rw [R11Shards.scratchEnd_val] at this; omega
  have hmem_eq : ∀ a : BitVec 64, a ≠ BitVec.ofNat 64 (e0 + k) →
      (R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (e0 + k)) w) a = t.memory a := by
    intro a ha
    simp [R14Shards.OpHandlersA.updW, ha]
  have hmem_out : ∀ x : BitVec 64,
      (∀ addr ∈ R11Shards.headAllowedOffsets e0 c0, x ≠ BitVec.ofNat 64 addr) →
      (R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (e0 + k)) w) x = t.memory x := by
    intro x hx
    by_cases hxa : x = BitVec.ofNat 64 (e0 + k)
    · subst hxa
      exfalso
      have hmem184 : (e0 + 184) ∈ R11Shards.headAllowedOffsets e0 c0 := by
        simp only [R11Shards.headAllowedOffsets, List.mem_cons]
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl trivial)))))))
      have hmem72 : (e0 + 72) ∈ R11Shards.headAllowedOffsets e0 c0 := by
        simp only [R11Shards.headAllowedOffsets, List.mem_cons]
        exact Or.inr (Or.inl trivial)
      rcases hk with rfl | rfl
      · exact hx (e0 + 184) hmem184 rfl
      · exact hx (e0 + 72) hmem72 rfl
    · exact hmem_eq x hxa
  have h64 : R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (e0 + k)) w
      (BitVec.ofNat 64 (e0 + 64)) = t.memory (BitVec.ofNat 64 (e0 + 64)) := by
    simp [R14Shards.OpHandlersA.updW]
    intro hc
    have hnat := congrArg BitVec.toNat hc
    simp only [BitVec.toNat_ofNat, Nat.reducePow] at hnat
    omega
  have h192 : R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (e0 + k)) w
      (BitVec.ofNat 64 (e0 + 192)) = t.memory (BitVec.ofNat 64 (e0 + 192)) := by
    simp [R14Shards.OpHandlersA.updW]
    intro hc
    have hnat := congrArg BitVec.toNat hc
    simp only [BitVec.toNat_ofNat, Nat.reducePow] at hnat
    omega
  have hgas_le : memW { t with memory := R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (e0 + k)) w }
      (e0 + 64) + memW { t with memory := R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (e0 + k)) w }
      (e0 + 192) ≤ memW t (e0 + 64) + memW t (e0 + 192) := by
    have : memW { t with memory := R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (e0 + k)) w }
        (e0 + 64) + memW { t with memory := R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (e0 + k)) w }
        (e0 + 192) = memW t (e0 + 64) + memW t (e0 + 192) := by
      simp only [memW, h64, h192]
    omega
  have hmain := R11Shards.evmInv_of_head_status_gas_update (s := t)
    (post := { t with memory := R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (e0 + k)) w })
    ⟨hAR, S, hWT, hch_ne, hch_len, hlast, hFWF, hFRoom, hRetW, hPair, hDisj, hTries, hMarks,
      hRoles, hGasSum⟩
    (guestInv_updW_g10 hAR.1 (BitVec.ofNat 64 (e0 + k)) w) rfl rfl hmem_out hgas_le
  have hAn : BitVec.toNat (BitVec.ofNat 64 (e0 + k)) = e0 + k := by
    simp only [BitVec.toNat_ofNat]
    omega
  refine ⟨hmain.1, ?_, hmain.2.1, ?_⟩
  · exact headMemChainWF_store_headSafe ⟨hAR, S, hWT, hch_ne, hch_len, hlast, hFWF, hFRoom,
      hRetW, hPair, hDisj, hTries, hMarks, hRoles, hGasSum⟩ hWF
      (Or.inl ⟨k, by rw [hAn], by omega, by omega, by omega, by omega⟩) rfl hmain.2.1 hmem_eq
  · exact hmain.2.2

/-! ### `op_staticcall` walk -/

/-- The `x`-facts (from `extend_memory_cost2`) needed for the later `extend_memory`
call: the expansion bound for the head frame's memory-size word `ev+32`. -/
def scXQ {F : Type} (t : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ cw ebw : BitVec 64,
    t.locals.lookup (ofString "x") =
      some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
    (ebw = 0#64 ∨ (memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
      (memW t (globN t "ev" + 32) + ebw.toNat) % 32 = 0))

/-- `scXQ` transport: same `x` local, same `ev+32` word, same globals. -/
theorem scXQ_congr_g10 {F : Type} {t u : PanSemStateFiniteExact 64 F}
    (hx : u.locals.lookup (ofString "x") = t.locals.lookup (ofString "x"))
    (hm : memW u (globN u "ev" + 32) = memW t (globN t "ev" + 32))
    (hg : u.globals = t.globals) (h : scXQ t) : scXQ u := by
  obtain ⟨cw, ebw, hxl, hbd⟩ := h
  refine ⟨cw, ebw, by rw [hx]; exact hxl, ?_⟩
  have hgev : globN u "ev" = globN t "ev" := by
    unfold globN
    rw [hg]
  rw [hgev] at hm ⊢
  simpa [hm] using hbd

theorem op_staticcall_prefix1_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {charged : Bool} {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 scXQ charged cont) :
    HandlerRunA s0 (fun _ => True) charged
      (.decCall (ofString "gasv") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
        (.decCall (ofString "tov") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
          (.decCall (ofString "to") .one (ofString "to_address_masked") [.var .local (ofString "tov")]
            (.decCall (ofString "in_start") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
              (.decCall (ofString "in_size") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
                (.decCall (ofString "out_start") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
                  (.decCall (ofString "out_size") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
                    (.dec (ofString "msg") .one
                      (.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 112)]))
                      (.decCall (ofString "x") (.comb [.one, .one]) (ofString "extend_memory_cost2")
                        [.var .local (ofString "in_start"), .var .local (ofString "in_size"),
                          .var .local (ofString "out_start"), .var .local (ofString "out_size")]
                        cont))))))))) := by
  refine HandlerRunA.decCall_simple epsA_stack_pop_le_g10 ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop_le_g10 ?_
  refine HandlerRunA.decCall_simple epsA_to_address_masked ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop_le_g10 ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop_le_g10 ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop_le_g10 ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop_le_g10 ?_
  refine HandlerRunA.dec_simple ?_
  refine HandlerRunA.decCall (hf := epsA_extend_memory_cost2) ?_ ?_ hcont
  · intros; trivial
  · intro t values body callee retShape v cpost _ _ _ _ _ _ _ _ hQc
    obtain ⟨hlf, cw, ebw, hv, hbd⟩ := hQc
    refine ⟨cw, ebw, ?_, ?_⟩
    · dsimp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      first
        | rw [if_pos rfl, hv]
        | simp [hv]
    · rw [hlf]
      exact hbd

/-! ### `calculate_delegation_cost` preserves the head frame's bookkeeping -/

/-- The `calculate_delegation_cost` callee's only memory write is the 20-byte `memcpy`
into the freshly allocated heap buffer, which lies strictly below the scratch region
housing the frame structs.  Consequently the head frame's memory bookkeeping words
(`ev+24/32/40`) and the `frame_mem_ptr` global are preserved. -/
def CdcPinsG10 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (rp : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F) : Prop :=
  ∀ v, rp.1 = some (.returned v) →
    globN rp.2 "ev" = globN s0 "ev" ∧
    memW rp.2 (globN s0 "ev" + 32) = memW s0 (globN s0 "ev" + 32) ∧
    globN rp.2 "frame_mem_ptr" = globN s0 "frame_mem_ptr"

theorem one_word_value_of_shape_g10 {v : ValueHOL 64}
    (hsh : shapeEqHOL (shapeOfHOLExact v) .one = true) :
    ∃ a : BitVec 64, v = .val (.word a) := by
  rcases v with ⟨⟨a⟩⟩ | _ | _ <;> try simp [shapeOfHOLExact, shapeEqHOL] at hsh
  exact ⟨a, rfl⟩

theorem globN_congr_g10 {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : t.globals = s.globals) (n : String) : globN t n = globN s n := by
  unfold globN; rw [h]

theorem memW_congr_g10 {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : t.memory = s.memory) (n : Nat) : memW t n = memW s n := by unfold memW; rw [h]

theorem lookup_ext_code_of_g10 :
    originalRuntimeCode.lookup (ofString "ext_code_of") =
      some ([(ofString "addr", .one)],
        sourceFnBody Guest.Software.guestFn_ext_code_of,
        .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 543 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ext_code_of) rfl

/-- A successful `ext_code_of` lookup forces its single argument to be a word. -/
theorem ext_code_of_arg_word_g10 {body' : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret' : ShapeHOL} {v0 : ValueHOL 64}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "ext_code_of") [v0] =
      some (body', callee, ret')) :
    ∃ w0 : BitVec 64, v0 = .val (.word w0) := by
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
    originalRuntimeCode.lookup (ofString "ext_code_of") [v0] body' callee ret' hl
  simp only [Flapjack.lookupCodeHOLExact, lookup_ext_code_of_g10] at hx
  split at hx
  · rename_i hcond
    have hsh0 : shapeEqHOL ShapeHOL.one (shapeOfHOLExact v0) = true := by
      simpa using hcond.2.2
    rcases v0 with ⟨⟨w0⟩⟩ | _ | _
    · exact ⟨w0, rfl⟩
    · exact absurd hsh0 (by simp [shapeOfHOLExact, shapeEqHOL])
    · exact absurd hsh0 (by simp [shapeOfHOLExact, shapeEqHOL])
  · cases hx

theorem comb2_value_of_shape_g10 {v : ValueHOL 64}
    (hsh : shapeEqHOL (shapeOfHOLExact v) (.comb [.one, .one]) = true) :
    ∃ a b : BitVec 64, v = .rStruct [.val (.word a), .val (.word b)] := by
  rcases v with _ | vs | _
  · simp [shapeOfHOLExact, shapeEqHOL] at hsh
  · rcases vs with _ | ⟨v0, _ | ⟨v1, _ | _⟩⟩
    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh
    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh
    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh
      rcases hsh with ⟨h0, h1⟩
      rcases v0 with ⟨⟨a⟩⟩ | _ | _ <;> try simp [shapeOfHOLExact, shapeEqHOL] at h0
      rcases v1 with ⟨⟨b⟩⟩ | _ | _ <;> try simp [shapeOfHOLExact, shapeEqHOL] at h1
      exact ⟨a, b, rfl⟩
    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh
  · simp [shapeOfHOLExact, shapeEqHOL] at hsh

theorem cdc_pins_return_any_g10 {F : Type} {t : PanSemStateFiniteExact 64 F}
    {e : ExpHOL 64} {v : ValueHOL 64}
    (hev : @evalHOLExact 64 F _ t.toExact (fun x => Classical.propDecidable (t.memaddrs x)) e =
      some v) :
    CdcPinsG10 t (evaluateHOLFiniteState t (.return e)) := by
  rw [evaluateHOLFiniteState_return, hev]
  split
  · simp only [CdcPinsG10]
    intro w hw
    cases hw
  · split
    · simp only [CdcPinsG10]
      intro w hw
      injection hw with hw'; injection hw' with hw''
      subst hw''
      refine ⟨?_, ?_, ?_⟩ <;> simp [globN, emptyLocalsHOLFinite, memW]
    · simp only [CdcPinsG10]
      intro w hw
      cases hw

theorem cdc_pins_transfer_g10 {F : Type} {s0 t : PanSemStateFiniteExact 64 F}
    (rp : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F)
    (hgev : globN t "ev" = globN s0 "ev")
    (hgefp : globN t "frame_mem_ptr" = globN s0 "frame_mem_ptr")
    (hm32 : memW t (globN s0 "ev" + 32) = memW s0 (globN s0 "ev" + 32))
    (h : CdcPinsG10 t rp) : CdcPinsG10 s0 rp := by
  unfold CdcPinsG10 at h ⊢
  intro v hv
  obtain ⟨he1, hm32', hfp⟩ := h v hv
  refine ⟨by rw [he1, hgev], ?_, by rw [hfp, hgefp]⟩
  rw [← hgev] at hm32 ⊢
  rw [hm32', hm32]

theorem cdc_pins_return_known_g10 {F : Type} {t : PanSemStateFiniteExact 64 F}
    {e : ExpHOL 64} {v : ValueHOL 64} {post : PanSemStateFiniteExact 64 F}
    (hev : @evalHOLExact 64 F _ t.toExact (fun x => Classical.propDecidable (t.memaddrs x)) e =
      some v)
    (hr : evaluateHOLFiniteState t (.return e) = (some (.returned v), post)) :
    CdcPinsG10 t (some (.returned v), post) := by
  have hfold := cdc_pins_return_any_g10 (t := t) (e := e) (v := v) hev
  rw [hr] at hfold
  exact hfold

theorem cdc_pins_seq_known_g10 {F : Type} {s0 t : PanSemStateFiniteExact 64 F}
    {a b : ProgHOL 64} {r1 : Option (PanSemResultExact 64)} {st1 : PanSemStateFiniteExact 64 F}
    (hra : evaluateHOLFiniteState t a = (r1, st1))
    (hret : r1 ≠ none → CdcPinsG10 s0 (r1, st1))
    (hnone : r1 = none → CdcPinsG10 s0 (evaluateHOLFiniteState st1 b)) :
    CdcPinsG10 s0 (evaluateHOLFiniteState t (.seq a b)) := by
  rw [evaluateHOLFiniteState_seq_line780, hra]
  dsimp only
  cases r1 with
  | none => exact hnone rfl
  | some res => exact hret (by simp)

theorem cdc_pins_decCall_g10 {F : Type}
    {s0 t : PanSemStateFiniteExact 64 F}
    {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    {nm : MlS} {sh : ShapeHOL} {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hc : t.code = originalRuntimeCode) (hi : EvmInv t) (hw : Group10.HeadMemChainWF t)
    (hf : EvmPreservingSpecA Pc Qc fname)
    (hPc : ∀ values callee,
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      Pc (callEntryStateHOLFinite t callee))
    (hcont : ∀ values callee body_c ret_c v cpost,
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body_c, callee, ret_c) →
      cpost.code = originalRuntimeCode →
      shapeEqHOL (shapeOfHOLExact v) sh = true →
      EvmInv cpost → Group10.HeadMemChainWF cpost →
      evmChain cpost = evmChain (callEntryStateHOLFinite t callee) →
      Qc (callEntryStateHOLFinite t callee) v cpost →
      evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body_c =
        (some (.returned v), cpost) →
      (evaluateHOLFiniteState (setVarHOLFinite nm v { cpost with locals := t.locals }) cont).1 ≠
        some .timeOut →
      CdcPinsG10 s0
        (evaluateHOLFiniteState (setVarHOLFinite nm v { cpost with locals := t.locals }) cont))
    (hnt : (evaluateHOLFiniteState t (.decCall nm sh fname args cont)).1 ≠ some .timeOut) :
    CdcPinsG10 s0
      (evaluateHOLFiniteState t (.decCall nm sh fname args cont)) := by
  obtain ⟨params, body, retShape, hlook, hspec⟩ := hf
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args with _ | values
  · simp only [CdcPinsG10]; intro v hv; cases hv
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · simp only [CdcPinsG10]; intro v hv; cases hv
    · simp only [hl] at hnt ⊢
      by_cases hz : t.clock = 0
      · rw [if_pos hz] at hnt; exact absurd rfl hnt
      · rw [if_neg hz] at hnt ⊢
        have hbody_eq : body' = body :=
          lookupCodeHOLFinite_installed_body t.code.lookup fname params body body'
            retShape ret' values callee (by rw [hc]; exact hlook) hl
        subst body'
        have hret_eq : ret' = retShape := by
          have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
            t.code.lookup fname values body callee ret' hl
          rw [hc] at hx; simp only [Flapjack.lookupCodeHOLExact, hlook] at hx
          split at hx
          · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
          · cases hx
        subst ret'
        have hi_ce : EvmInv (callEntryStateHOLFinite t callee) := localsFree_evmInv t callee (t.clock - 1) hi
        have hw_ce : Group10.HeadMemChainWF (callEntryStateHOLFinite t callee) :=
          Group10.headMemChainWF_locals t callee (t.clock - 1) hw
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
            some (body, callee, retShape) := by rwa [← hc]
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite t callee) body).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body with ⟨res, cpost⟩
        simp only [hrun] at hnt hmeta ⊢
        change cpost.code = t.code at hmeta
        have hc_cp : cpost.code = originalRuntimeCode := hmeta.trans hc
        have hQ (hsafe : res ≠ some .timeOut) :=
          hspec (callEntryStateHOLFinite t callee) hc hi_ce hw_ce (hPc values callee hargs)
            ⟨values, hl_orig⟩ (by rw [hrun]; exact hsafe)
        cases res with
        | none => simp only [CdcPinsG10]; intro v hv; cases hv
        | some r0 =>
          cases r0 with
          | timeOut => simp at hnt
          | «break» | «continue» | error | finalFfi _ | exception _ _ =>
            simp only [CdcPinsG10]; intro v hv; cases hv
          | returned v =>
            dsimp only at hnt ⊢
            split
            · rename_i hsh_ok
              rw [if_pos hsh_ok] at hnt
              have hsh_v : shapeEqHOL (shapeOfHOLExact v) sh = true :=
                (Bool.and_eq_true _ _).mp hsh_ok |>.1
              have hq := hQ (by simp); dsimp only at hq; rw [hrun] at hq
              obtain ⟨⟨hi_cp, hw_cp⟩, hch_cp, _, hQc_cp⟩ := hq.1 v rfl
              exact hcont values callee body retShape v cpost hargs hl_orig hc_cp hsh_v
                hi_cp hw_cp hch_cp hQc_cp hrun hnt
            · simp only [CdcPinsG10]; intro v hv; cases hv

theorem cdc_pins_g10 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hW : WorldAccountSpecsA) (hc : s.code = originalRuntimeCode) (hi : EvmInv s)
    (hw : Group10.HeadMemChainWF s)
    (r : Option (PanSemResultExact 64)) (post : PanSemStateFiniteExact 64 F)
    (hr : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_calculate_delegation_cost) =
      (r, post))
    (hnt : r ≠ some .timeOut) :
    CdcPinsG10 s (r, post) := by
  have hbody : sourceFnBody Guest.Software.guestFn_calculate_delegation_cost =
      .decCall (ofString "code") (.comb [.one, .one]) (ofString "ext_code_of") [.var .local (ofString "addr")]
        (.decCall (ofString "v") .one (ofString "is_valid_delegation")
          [.rfield 0 (.var .local (ofString "code")), .rfield 1 (.var .local (ofString "code"))]
          (.seq
            (.ite (.cmp .equal (.var .local (ofString "v")) (.const 0#64))
              (.return (.rstruct [.const 0#64, .var .local (ofString "addr"), .const 0#64]))
              .skip)
            (.decCall (ofString "da") .one (ofString "alloc") [.const 24#64]
              (.seq
                (.call (some (none, none)) (ofString "memcpy")
                  [.var .local (ofString "da"),
                   .op .add [.rfield 0 (.var .local (ofString "code")), .const 3#64],
                   .const 20#64])
                (.decCall (ofString "warm") .one (ofString "is_warm_address") [.var .local (ofString "da")]
                  (.seq
                    (.ite (.cmp .notEqual (.var .local (ofString "warm")) (.const 0#64))
                      (.return (.rstruct [.const 1#64, .var .local (ofString "da"), .const 100#64]))
                      .skip)
                    (.return (.rstruct [.const 1#64, .var .local (ofString "da"), .const 3000#64])))))))) := rfl
  rw [← hr, hbody]
  have hEvmInv : EvmInv s := hi
  have hnt0 : (evaluateHOLFiniteState s
      (.decCall (ofString "code") (.comb [.one, .one]) (ofString "ext_code_of") [.var .local (ofString "addr")]
        (.decCall (ofString "v") .one (ofString "is_valid_delegation")
          [.rfield 0 (.var .local (ofString "code")), .rfield 1 (.var .local (ofString "code"))]
          (.seq
            (.ite (.cmp .equal (.var .local (ofString "v")) (.const 0#64))
              (.return (.rstruct [.const 0#64, .var .local (ofString "addr"), .const 0#64]))
              .skip)
            (.decCall (ofString "da") .one (ofString "alloc") [.const 24#64]
              (.seq
                (.call (some (none, none)) (ofString "memcpy")
                  [.var .local (ofString "da"),
                   .op .add [.rfield 0 (.var .local (ofString "code")), .const 3#64],
                   .const 20#64])
                (.decCall (ofString "warm") .one (ofString "is_warm_address") [.var .local (ofString "da")]
                  (.seq
                    (.ite (.cmp .notEqual (.var .local (ofString "warm")) (.const 0#64))
                      (.return (.rstruct [.const 1#64, .var .local (ofString "da"), .const 100#64]))
                      .skip)
                    (.return (.rstruct [.const 1#64, .var .local (ofString "da"), .const 3000#64])))))))))).1 ≠
      some .timeOut := by rw [← hbody, hr]; exact hnt
  obtain ⟨haS, _, _, _, _, _, hfw_all, _⟩ := id hEvmInv
  obtain ⟨_, _, _, hss_fp, hfp_sp, _, _, _⟩ := haS.2
  have hev_in : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by simp [evmChain, evmChainFrom]
  have hfw_ev := hfw_all _ hev_in
  have hsc_le_ev : globN s "scratch_ptr" ≤ globN s "ev" :=
    (hfw_ev.1 (globN s "ev", 280) (by simp)).1.1
  have hcMax : InitECandidate.Solver.HeapPotential.cMax.toNat = scratchStart := rfl
  refine cdc_pins_decCall_g10 hc hEvmInv hw hW.epsA_ext_code_of
    (fun _ _ _ => trivial) ?_ hnt0
  intro values1 callee1 body_c1 ret_c1 v1 cp1 hargs1 hl1 hc_cp1 hsh1 hi_cp1 hw_cp1 hch_cp1 hQc1 hrun1 hnt1
  obtain ⟨c0, c1, rfl⟩ := comb2_value_of_shape_g10 hsh1
  have hgev1 : globN cp1 "ev" = globN s "ev" := by
    unfold globN; rw [← hQc1.1 (ofString "ev") (by decide)]; rfl
  have hfp1 : globN cp1 "frame_mem_ptr" = globN s "frame_mem_ptr" := by
    unfold globN; rw [← hQc1.1 (ofString "frame_mem_ptr") (by decide)]; rfl
  have hm32_1 : memW cp1 (globN s "ev" + 32) = memW s (globN s "ev" + 32) := hQc1.2.2
  let s1 := setVarHOLFinite (ofString "code")
    (.rStruct [.val (.word c0), .val (.word c1)]) { cp1 with locals := s.locals }
  have hi1 : EvmInv s1 := localsFree_evmInv cp1 s1.locals s1.clock hi_cp1
  have hw1 : Group10.HeadMemChainWF s1 := Group10.headMemChainWF_locals cp1 s1.locals s1.clock hw_cp1
  have hs1_code : s1.locals.lookup (ofString "code") =
      some (.rStruct [.val (.word c0), .val (.word c1)]) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  refine cdc_pins_decCall_g10 hc_cp1 hi1 hw1 epsA_is_valid_delegation
    (fun _ _ _ => trivial) ?_ hnt1
  intro values2 callee2 body_c2 ret_c2 v2 cp2 hargs2 hl2 hc_cp2 hsh2 hi_cp2 hw_cp2 hch_cp2 hQc2 hrun2 hnt2
  have hm2 : cp2.memory = cp1.memory := by rw [hQc2]; rfl
  have hg2 : cp2.globals = cp1.globals := by rw [hQc2]; rfl
  obtain ⟨w2, hv2w⟩ := one_word_value_of_shape_g10 hsh2
  let s2 := setVarHOLFinite (ofString "v") v2 { cp2 with locals := s1.locals }
  have hs2_v : s2.locals.lookup (ofString "v") = some (.val (.word w2)) := by
    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hv2w]
  have haddr_v2 : s2.locals.lookup (ofString "addr") = s.locals.lookup (ofString "addr") := by
    simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "v" ≠ ofString "addr" by decide, show ofString "code" ≠ ofString "addr" by decide]
  have hs2_code : s2.locals.lookup (ofString "code") =
      some (.rStruct [.val (.word c0), .val (.word c1)]) := by
    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "v" ≠ ofString "code" by decide, hs1_code]
  obtain ⟨vw1, hla1⟩ : ∃ vw : ValueHOL 64, s.locals.lookup (ofString "addr") = some vw := by
    generalize hlook : s.locals.lookup (ofString "addr") = x
    cases x with
    | none => simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hlook] at hargs1
    | some vw => exact ⟨vw, rfl⟩
  have hvals1 : values1 = [vw1] := by
    simp only [hla1, evalListHOLFinite, evalListHOLExact, evalHOLExact] at hargs1
    exact (Option.some.inj hargs1).symm
  rw [hvals1] at hl1
  obtain ⟨aw1, hvw1⟩ := ext_code_of_arg_word_g10 hl1
  have hla1w : s.locals.lookup (ofString "addr") = some (.val (.word aw1)) := by
    rw [hla1, hvw1]
  have hcond_v : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
      (.cmp .equal (.var .local (ofString "v")) (.const 0#64)) =
      some (.val (.word (if Compiler.Encoders.Asm.wordCmpHOL .equal w2 0#64 then 1 else 0))) := by
    simp [evalHOLExact, evalListHOLExact, hs2_v, Compiler.Encoders.Asm.wordCmpHOL]
  have hev_ret : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
      (.rstruct [.const 0#64, .var .local (ofString "addr"), .const 0#64]) =
      some (.rStruct [.val (.word 0#64), .val (.word aw1), .val (.word 0#64)]) := by
    simp [evalHOLExact, evalListHOLExact, haddr_v2, hla1w]
  by_cases hv20 : w2 = 0#64
  · -- v = 0 → not delegated → return [0, addr, 0]
    have hbeqT : (Compiler.Encoders.Asm.wordCmpHOL .equal w2 0#64) = true := by
      rw [Compiler.Encoders.Asm.wordCmpHOL, hv20]; decide
    have hsz : sizeOfShapeWithContextHOL s2.structs
        (shapeOfHOLExact
          (.rStruct [.val (.word 0#64), .val (.word aw1), .val (.word 0#64)] : ValueHOL 64)) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
    have hra : evaluateHOLFiniteState s2
        (.ite (.cmp .equal (.var .local (ofString "v")) (.const 0#64))
          (.return (.rstruct [.const 0#64, .var .local (ofString "addr"), .const 0#64])) .skip) =
      (some (.returned (.rStruct [.val (.word 0#64), .val (.word aw1), .val (.word 0#64)])),
        emptyLocalsHOLFinite s2) := by
      rw [evaluateHOLFiniteState_ite, hcond_v]
      generalize hwc : ((if Compiler.Encoders.Asm.wordCmpHOL .equal w2 0#64 then 1 else 0) : BitVec 64) = wc
      have hwne : ¬(wc = 0) := by
        rw [← hwc, hbeqT, if_pos (show ((true : Bool) = true) by rfl)]; decide
      dsimp only
      rw [if_neg hwne]
      rw [evaluateHOLFiniteState_return, hev_ret]
      dsimp only
      rw [if_pos hsz]
    have hr_ret : evaluateHOLFiniteState s2
        (.return (.rstruct [.const 0#64, .var .local (ofString "addr"), .const 0#64])) =
      (some (.returned (.rStruct [.val (.word 0#64), .val (.word aw1), .val (.word 0#64)])),
        emptyLocalsHOLFinite s2) := by
      rw [evaluateHOLFiniteState_return, hev_ret]
      dsimp only
      rw [if_pos hsz]
    have hs2g : s2.globals = cp2.globals := rfl
    have hs2m : s2.memory = cp2.memory := rfl
    refine cdc_pins_seq_known_g10 hra ?_ (fun hne => by simp at hne)
    intro _
    exact cdc_pins_transfer_g10 _
      ((globN_congr_g10 hs2g "ev").trans ((globN_congr_g10 hg2 "ev").trans hgev1))
      ((globN_congr_g10 hs2g "frame_mem_ptr").trans
        ((globN_congr_g10 hg2 "frame_mem_ptr").trans hfp1))
      ((memW_congr_g10 (hs2m.trans hm2) (globN s "ev" + 32)).trans hm32_1)
      (cdc_pins_return_known_g10 hev_ret hr_ret)
  · -- v ≠ 0 → delegated → skip → the alloc decCall tail
    have hbeqF : (Compiler.Encoders.Asm.wordCmpHOL .equal w2 0#64) = false := by
      rw [Compiler.Encoders.Asm.wordCmpHOL]
      cases hb : (w2 == 0#64) with
      | true => rw [beq_iff_eq] at hb; exact absurd hb hv20
      | false => rfl
    have hra : evaluateHOLFiniteState s2
        (.ite (.cmp .equal (.var .local (ofString "v")) (.const 0#64))
          (.return (.rstruct [.const 0#64, .var .local (ofString "addr"), .const 0#64])) .skip) =
      (none, s2) := by
      rw [evaluateHOLFiniteState_ite, hcond_v, hbeqF,
        if_neg (show ¬ ((false : Bool) = true) by decide)]
      dsimp only
      first
        | rw [if_pos (show ((0#64 : BitVec 64) = 0) by decide), evaluateHOLFiniteState_skip]
        | simp only [↓reduceIte, evaluateHOLFiniteState_skip]
    refine cdc_pins_seq_known_g10 hra (fun hne => by simp at hne) ?_
    intro _
    rw [evaluateHOLFiniteState_seq_line780, hra] at hnt2
    dsimp only at hnt2
    have hc2 : s2.code = originalRuntimeCode := hc_cp2
    have hi2 : EvmInv s2 := localsFree_evmInv cp2 s2.locals s2.clock hi_cp2
    have hw2 : Group10.HeadMemChainWF s2 := Group10.headMemChainWF_locals cp2 s2.locals s2.clock hw_cp2
    have hs2g : s2.globals = cp2.globals := rfl
    have hs2m : s2.memory = cp2.memory := rfl
    refine cdc_pins_decCall_g10 hc2 hi2 hw2 epsA_alloc_avoids_g10
      (fun _ _ _ => trivial)
      (fun values3 callee3 body_c3 ret_c3 v3 cp3 hargs3 hl3 hc_cp3 hsh3 hi_cp3 hw_cp3 hch_cp3 hQc3 hrun3 hnt3 => ?_) hnt2
    obtain ⟨hm3, hR3, p0, rfl, hp0n, hal3, hb3, hhi3, hav3⟩ := hQc3
    have hvals3 : values3 = [.val (.word 24#64)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact] at hargs3
      exact hargs3.symm
    subst values3
    obtain ⟨hb_al, _, n3, hv3n, hn3⟩ :=
      R14Shards.OpHandlersA.one_word_arg_lookup GuestTrapAndLookup.lookup_alloc hl3
    injection hv3n with hv3n'; injection hv3n' with hv3n''; subst n3
    have hloc_n3 : locN (callEntryStateHOLFinite s2 callee3) "n" = 24 := by
      simp [locN, callEntryStateHOLFinite, hn3]
    rw [hloc_n3] at hb3 hav3
    let s3 := setVarHOLFinite (ofString "da") (.val (.word p0)) { cp3 with locals := s2.locals }
    have hc3 : s3.code = originalRuntimeCode := hc_cp3
    have hi3 : EvmInv s3 := localsFree_evmInv cp3 s3.locals s3.clock hi_cp3
    have hw3 : Group10.HeadMemChainWF s3 := Group10.headMemChainWF_locals cp3 s3.locals s3.clock hw_cp3
    have hs3_da : s3.locals.lookup (ofString "da") = some (.val (.word p0)) := by
      simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs3_code : s3.locals.lookup (ofString "code") =
        some (.rStruct [.val (.word c0), .val (.word c1)]) := by
      simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "da" ≠ ofString "code" by decide, hs2_code]
    have hi_ce3 : EvmInv (callEntryStateHOLFinite s2 callee3) :=
      localsFree_evmInv s2 callee3 (s2.clock - 1) hi2
    obtain ⟨p0e, hp0e⟩ := hi_ce3.1.2.2.2.2.2.2.2.2.2 "heap_ptr" (by decide)
    change (callEntryStateHOLFinite s2 callee3).globals.lookup (ofString "heap_ptr") =
      some (.val (.word p0e)) at hp0e
    have hpgn : globN (callEntryStateHOLFinite s2 callee3) "heap_ptr" = p0e.toNat := by
      simp [globN, hp0e]
    rw [hpgn] at hp0n
    have hple3 : p0e.toNat ≤ InitECandidate.Solver.HeapPotential.cMax.toNat := by omega
    have hc3e : (callEntryStateHOLFinite s2 callee3).code = originalRuntimeCode := hc2
    have hn3' : (callEntryStateHOLFinite s2 callee3).locals.lookup (ofString "n") =
        some (.val (.word 24#64)) := by
      simp [callEntryStateHOLFinite, hn3]
    rw [hb_al] at hrun3
    obtain ⟨_, _, hglob3⟩ := alloc_return_frame_g10 (callEntryStateHOLFinite s2 callee3) p0e 24#64
      hc3e hple3 hp0e hn3' (.val (.word p0)) cp3 hrun3
    have hs3g : s3.globals = cp3.globals := rfl
    have hge3 : globN cp3 "ev" = globN s2 "ev" := by
      simp [globN, hglob3, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "heap_ptr" ≠ ofString "ev" by decide]
    have hgefp3 : globN cp3 "frame_mem_ptr" = globN s2 "frame_mem_ptr" := by
      simp [globN, hglob3, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
    have hav3' : Wave8Contracts.M23.EvmAvoids (fun _ => [(p0.toNat, 24)]) s3 :=
      evmAvoids_const_lc_g10 [(p0.toNat, 24)] cp3 s3.locals s3.clock hav3
    rw [evaluateHOLFiniteState_seq_line780] at hnt3 ⊢
    let mcall : ProgHOL 64 := .call (some (none, none)) (ofString "memcpy")
      [.var .local (ofString "da"),
       .op .add [.rfield 0 (.var .local (ofString "code")), .const 3#64],
       .const 20#64]
    have hsrc_eval : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
        (.op .add [.rfield 0 (.var .local (ofString "code")), .const 3#64]) =
        some (.val (.word (c0 + 3#64))) := by
      simp only [evalHOLExact, evalListHOLExact, hs3_code, wordOpHOL, wordOp, valueIsWord, valueWord,
        List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
      have hz : (3#64 : BitVec 64) + 0 = 3#64 := BitVec.add_zero _
      exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word (c0 + w)))) hz
    rcases hr4 : evaluateHOLFiniteState s3 mcall with ⟨res4, s4⟩
    have hr4' : evaluateHOLFiniteState s3
        (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "da"),
           .op .add [.rfield 0 (.var .local (ofString "code")), .const 3#64],
           .const 20#64]) = (res4, s4) := hr4
    rw [hr4'] at hnt3
    have hnt_mc : (evaluateHOLFiniteState s3 mcall).1 ≠ some .timeOut := by
      rw [hr4]; intro hto; dsimp only at hto; subst hto; simp at hnt3
    have hmc_bre := Wave8GuestInv.M11.eval_call_memcpy_bre s3
      (.var .local (ofString "da"))
      (.op .add [.rfield 0 (.var .local (ofString "code")), .const 3#64])
      (.const 20#64)
      p0 (c0 + 3#64) 20#64 [(p0.toNat, 24)]
      hc3 hi3.1.1.memaddrs
      (by simp [evalHOLExact, hs3_da])
      hsrc_eval
      (by simp [evalHOLExact])
      (fun _ => ⟨(p0.toNat, 24), List.mem_singleton.mpr rfl, le_rfl,
        by have h20 : (20#64 : BitVec 64).toNat = 20 := by decide
           dsimp only; omega⟩)
      hnt_mc
    rw [hr4'] at hmc_bre
    cases res4 with
    | some r4 =>
      dsimp only at hnt3 ⊢
      have hnot_res := hmc_bre.2 (by simp)
      cases r4 with
      | timeOut => simp only [CdcPinsG10]; intro v hv; simp at hv
      | returned vr => exact absurd (Or.inl ⟨vr, rfl⟩) hnot_res
      | exception eid4 ev4 =>
        by_cases heid4 : eid4 = ofString "EvmErr"
        · subst heid4
          exact absurd (Or.inr ⟨ofString "EvmErr", ev4, rfl, by decide⟩) hnot_res
        · simp only [CdcPinsG10]; intro v hv; simp at hv
      | «break» | «continue» | error | finalFfi _ =>
        simp only [CdcPinsG10]; intro v hv; simp at hv
    | none =>
      dsimp only at hnt3 ⊢
      obtain ⟨heff_m11, hloc4⟩ := hmc_bre.1 rfl
      have heff4 : Wave8Contracts.M23.ByteRegionEffect s3 s4 [(p0.toNat, 24)] :=
        OpHandlers.bre_of_m11 heff_m11
      have hevm_step4 := Wave8Contracts.M23.ByteRegionEffect.to_evmStep_avoids hav3' heff4
      have hi4 : EvmInv s4 := hevm_step4.1
      have hch4_s3 : evmChain s4 = evmChain s3 := hevm_step4.2.2.2
      have hc4 : s4.code = originalRuntimeCode := heff4.code.trans hc3
      have hp_lim_hl : p0.toNat + 24 ≤ heapLimit := by
        have hhl : InitECandidate.Solver.HeapPotential.cMax.toNat = heapLimit := rfl
        have hsub : p0.toNat + 24 ≤ InitECandidate.Solver.HeapPotential.cMax.toNat := by omega
        omega
      have hw4 : Group10.HeadMemChainWF s4 := by
        apply headMemChainWF_of_byteRegionEffect hi3 hw3 hch4_s3 heff4
        · intro i hi_mem; simp only [List.mem_singleton] at hi_mem; subst i; exact hal3
        · intro ec hec i hi_mem
          simp only [List.mem_singleton] at hi_mem; subst i
          obtain ⟨ha3, _, _, _, _, _, hfw3, _⟩ := hi3
          have hframe3 := ha3.2.2.2.1
          have hscratch3 := ha3.2.2.2.2.1
          have hlim : heapLimit = scratchStart := rfl
          have hfw_ec := hfw3 ec hec
          have he_lo : globN s3 "scratch_ptr" ≤ ec.1 := (hfw_ec.1 (ec.1, 280) (by simp)).1.1
          have hc_lo : globN s3 "scratch_ptr" ≤ ec.2 := (hfw_ec.1 (ec.2, 104) (by simp)).1.1
          exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (by dsimp [Disj] at *; omega)))),
                 Or.inr (Or.inr (Or.inr (Or.inr (by dsimp [Disj] at *; omega))))⟩
      have hs4_da : s4.locals.lookup (ofString "da") = some (.val (.word p0)) := by
        rw [hloc4]; exact hs3_da
      have hev3_eq : globN s3 "ev" = globN s "ev" :=
        (globN_congr_g10 hs3g "ev").trans (hge3.trans ((globN_congr_g10 hs2g "ev").trans
          ((globN_congr_g10 hg2 "ev").trans hgev1)))
      have hch3h : ∃ tl, evmChain s3 = (globN s3 "ev", globN s3 "cur_cont") :: tl := ⟨_, rfl⟩
      have hfw280 : globN s3 "ev" + 280 ≤ scratchEnd := by
        have hcopy := hi3
        rcases hcopy with ⟨_, S3, _, _, _, _, hfw3s, _⟩
        have him := hfw3s (globN s3 "ev", globN s3 "cur_cont")
          (by rcases hch3h with ⟨tl, htlt⟩; rw [htlt]; simp)
        exact ((him.1 (globN s3 "ev", 280) (by simp)).1).2
      have hlt_ev : globN s3 "ev" + 32 < 4294967296 * 4294967296 := by
        have hse : scratchEnd = 2965299200 := rfl
        omega
      have hdisj3 : ∀ i ∈ [(p0.toNat, 24)],
          ¬ CellHits ((BitVec.ofNat 64 (globN s3 "ev" + 32)).toNat) i := by
        intro i hi
        simp only [List.mem_singleton] at hi
        subst i
        have htn : (BitVec.ofNat 64 (globN s3 "ev" + 32)).toNat = globN s3 "ev" + 32 :=
          Nat.mod_eq_of_lt hlt_ev
        rw [htn, hev3_eq]
        dsimp only [CellHits]
        omega
      have hmw4 : memW s4 (globN s "ev" + 32) = memW s3 (globN s "ev" + 32) := by
        rw [← hev3_eq]
        unfold memW
        rw [heff4.cell_frame (BitVec.ofNat 64 (globN s3 "ev" + 32)) hdisj3]
      refine cdc_pins_decCall_g10 hc4 hi4 hw4 epsA_is_warm_address
        (fun _ _ _ => trivial)
        (fun values5 callee5 body_c5 ret_c5 v5 cp5 hargs5 hl5 hc_cp5 hsh5 hi_cp5 hw_cp5 hch_cp5 hQc5 hrun5 hnt5 => ?_) hnt3
      obtain ⟨warmw, rfl⟩ := one_word_value_of_shape_g10 hsh5
      let s5 := setVarHOLFinite (ofString "warm") (.val (.word warmw)) { cp5 with locals := s4.locals }
      have hi5 : EvmInv s5 := localsFree_evmInv cp5 s5.locals s5.clock hi_cp5
      have hw5 : Group10.HeadMemChainWF s5 := Group10.headMemChainWF_locals cp5 s5.locals s5.clock hw_cp5
      have hm_cp5 : cp5.memory = s4.memory := by
        unfold R14Shards.OpHandlersA.LocFrame at hQc5; rw [hQc5]; rfl
      have hg_cp5 : cp5.globals = s4.globals := by
        unfold R14Shards.OpHandlersA.LocFrame at hQc5; rw [hQc5]; rfl
      have hs5_warm : s5.locals.lookup (ofString "warm") = some (.val (.word warmw)) := by
        simp [s5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hs5_da : s5.locals.lookup (ofString "da") = some (.val (.word p0)) := by
        simp [s5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "warm" ≠ ofString "da" by decide, hs4_da]
      have hs4g : s4.globals = s3.globals := heff4.globals
      have hs5g : s5.globals = cp5.globals := rfl
      have hs3m : s3.memory = cp3.memory := rfl
      have hs5m : s5.memory = cp5.memory := rfl
      have hm3' : cp3.memory = s2.memory := hm3
      have hgev5 : globN s5 "ev" = globN s "ev" :=
        (globN_congr_g10 hs5g "ev").trans ((globN_congr_g10 hg_cp5 "ev").trans
          ((globN_congr_g10 hs4g "ev").trans ((globN_congr_g10 hs3g "ev").trans
            (hge3.trans ((globN_congr_g10 hs2g "ev").trans
              ((globN_congr_g10 hg2 "ev").trans hgev1))))))
      have hgefp5 : globN s5 "frame_mem_ptr" = globN s "frame_mem_ptr" :=
        (globN_congr_g10 hs5g "frame_mem_ptr").trans ((globN_congr_g10 hg_cp5 "frame_mem_ptr").trans
          ((globN_congr_g10 hs4g "frame_mem_ptr").trans ((globN_congr_g10 hs3g "frame_mem_ptr").trans
            (hgefp3.trans ((globN_congr_g10 hs2g "frame_mem_ptr").trans
              ((globN_congr_g10 hg2 "frame_mem_ptr").trans hfp1))))))
      have hm325 : memW s5 (globN s "ev" + 32) = memW s (globN s "ev" + 32) :=
        (memW_congr_g10 hs5m (globN s "ev" + 32)).trans
          ((memW_congr_g10 hm_cp5 (globN s "ev" + 32)).trans
            (hmw4.trans
              ((memW_congr_g10 hs3m (globN s "ev" + 32)).trans
                ((memW_congr_g10 hm3' (globN s "ev" + 32)).trans
                  ((memW_congr_g10 hs2m (globN s "ev" + 32)).trans
                    ((memW_congr_g10 hm2 (globN s "ev" + 32)).trans hm32_1))))))
      have hev3000 : @evalHOLExact 64 F _ s5.toExact (fun x => Classical.propDecidable (s5.memaddrs x))
          (.rstruct [.const 1#64, .var .local (ofString "da"), .const 3000#64]) =
          some (.rStruct [.val (.word 1#64), .val (.word p0), .val (.word 3000#64)]) := by
        simp [evalHOLExact, evalListHOLExact, hs5_da]
      have hev100 : @evalHOLExact 64 F _ s5.toExact (fun x => Classical.propDecidable (s5.memaddrs x))
          (.rstruct [.const 1#64, .var .local (ofString "da"), .const 100#64]) =
          some (.rStruct [.val (.word 1#64), .val (.word p0), .val (.word 100#64)]) := by
        simp [evalHOLExact, evalListHOLExact, hs5_da]
      have hsz5 : sizeOfShapeWithContextHOL s5.structs
          (shapeOfHOLExact (.rStruct [.val (.word 1#64), .val (.word p0), .val (.word 3000#64)] : ValueHOL 64)) ≤ 32 := by
        simp [shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
      have hsz5' : sizeOfShapeWithContextHOL s5.structs
          (shapeOfHOLExact (.rStruct [.val (.word 1#64), .val (.word p0), .val (.word 100#64)] : ValueHOL 64)) ≤ 32 := by
        simp [shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
      have hr_ret3000 : evaluateHOLFiniteState s5
          (.return (.rstruct [.const 1#64, .var .local (ofString "da"), .const 3000#64])) =
        (some (.returned (.rStruct [.val (.word 1#64), .val (.word p0), .val (.word 3000#64)])),
          emptyLocalsHOLFinite s5) := by
        rw [evaluateHOLFiniteState_return, hev3000]; dsimp only; rw [if_pos hsz5]
      have hr_ret100 : evaluateHOLFiniteState s5
          (.return (.rstruct [.const 1#64, .var .local (ofString "da"), .const 100#64])) =
        (some (.returned (.rStruct [.val (.word 1#64), .val (.word p0), .val (.word 100#64)])),
          emptyLocalsHOLFinite s5) := by
        rw [evaluateHOLFiniteState_return, hev100]; dsimp only; rw [if_pos hsz5']
      change (evaluateHOLFiniteState s5 _).1 ≠ some .timeOut at hnt5
      change CdcPinsG10 s (evaluateHOLFiniteState s5 _)
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt5 ⊢
      have hcond_w : @evalHOLExact 64 F _ s5.toExact (fun a => Classical.propDecidable (s5.memaddrs a))
          (.cmp .notEqual (.var .local (ofString "warm")) (.const 0#64)) =
          some (.val (.word (if warmw = 0#64 then 0#64 else 1#64))) := by
        by_cases hww0 : warmw = 0#64 <;>
          simp [evalHOLExact, evalListHOLExact, hs5_warm, Compiler.Encoders.Asm.wordCmpHOL, hww0]
      rw [hcond_w] at hnt5 ⊢; dsimp only at hnt5 ⊢
      by_cases hww0 : warmw = 0#64
      · subst hww0
        simp only [↓reduceIte, show (0#64 : BitVec 64) = 0 by decide] at hnt5 ⊢
        rw [evaluateHOLFiniteState_skip] at hnt5 ⊢
        dsimp only at hnt5 ⊢
        rw [hr_ret3000] at hnt5 ⊢
        exact cdc_pins_transfer_g10 _ hgev5 hgefp5 hm325
          (cdc_pins_return_known_g10 hev3000 hr_ret3000)
      · simp only [if_neg hww0, ↓reduceIte, show ¬ ((1#64 : BitVec 64) = 0) by decide] at hnt5 ⊢
        rw [hr_ret100] at hnt5 ⊢
        dsimp only at hnt5 ⊢
        exact cdc_pins_transfer_g10 _ hgev5 hgefp5 hm325
          (cdc_pins_return_known_g10 hev100 hr_ret100)

/-! ### Transports for `scXQ` through the remaining steps -/

/-- `scXQ` survives a `setVar` step for any key other than `"x"`. -/
theorem scXQ_setvar_g10 {F : Type} {t : PanSemStateFiniteExact 64 F}
    {nm : MlS} {v : ValueHOL 64} (hne : nm ≠ ofString "x")
    (h : scXQ t) : scXQ (setVarHOLFinite nm v t) := by
  refine scXQ_congr_g10 ?_ ?_ ?_ h
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
  · rfl
  · rfl

/-- `scXQ` reassembles on the record update `{cpost with locals := t.locals}` from the
`ev+32` word pin. -/
theorem scXQ_of_pins_g10 {F : Type} {t cpost : PanSemStateFiniteExact 64 F}
    (hp : scXQ t)
    (hm32 : memW cpost (globN cpost "ev" + 32) = memW t (globN t "ev" + 32)) :
    scXQ { cpost with locals := t.locals } := by
  obtain ⟨cw, ebw, hxl, hbd⟩ := hp
  have hmemu : memW { cpost with locals := t.locals }
      (globN { cpost with locals := t.locals } "ev" + 32) = memW cpost (globN cpost "ev" + 32) := rfl
  refine ⟨cw, ebw, hxl, ?_⟩
  rcases hbd with rfl | ⟨h1, h2⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨by rw [hmemu, hm32]; exact h1, by rw [hmemu, hm32]; exact h2⟩

/-- The `access_cost` local holds a word equal to one of the two delegation costs. -/
def AcQ_g10 {F : Type} (t : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ acw : BitVec 64, t.locals.lookup (ofString "access_cost") = some (.val (.word acw)) ∧
    (acw = 100#64 ∨ acw = 3000#64)

/-- The `need` local holds a word of value at least 100. -/
def NdQ_g10 {F : Type} (t : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ nw : BitVec 64, t.locals.lookup (ofString "need") = some (.val (.word nw)) ∧ 100 ≤ nw.toNat

/-! ### `calculate_delegation_cost` full spec (pins + shape) -/

/-- The full spec for `calculate_delegation_cost`: the head frame's bookkeeping pins
(`ev`, `ev+32`, `frame_mem_ptr`), unchanged `evmR`, and the delegation-cost triple
shape. -/
theorem epsA_cdc_full_g10 (hW : WorldAccountSpecsA) :
    EvmPreservingSpecA (fun _ => True)
      (fun s v post =>
        CdcPinsG10 s (some (.returned v), post) ∧
        evmR post = evmR s ∧
        ∃ d0 d1 d2 : BitVec 64,
          v = .rStruct [.val (.word d0), .val (.word d1), .val (.word d2)] ∧
          (d0 = 0#64 → d2 = 0#64) ∧
          (d0 ≠ 0#64 → 0 < d2.toNat))
      (ofString "calculate_delegation_cost") := by
  obtain ⟨params0, body0, ret0, hlk0, hspec0⟩ := epsA_calculate_delegation_cost_g10 hW
  have hbody_eq : sourceFnBody Guest.Software.guestFn_calculate_delegation_cost = body0 := by
    have hx : originalRuntimeCode.lookup (ofString "calculate_delegation_cost")
        = some (params0, body0, ret0) := hlk0
    rw [lookup_calculate_delegation_cost_g10] at hx
    rcases Prod.mk.inj (Option.some.inj hx) with ⟨_, h23⟩
    rcases Prod.mk.inj h23 with ⟨h2, _⟩
    exact h2
  subst hbody_eq
  refine ⟨_, _, _, hlk0, ?_⟩
  intro F s hc hi hw _ hlook hnt
  obtain ⟨vals, hl⟩ := hlook
  have hr := hspec0 s hc hi hw trivial ⟨vals, hl⟩ hnt
  dsimp only at hr ⊢
  refine ⟨fun v hv => ⟨(hr.1 v hv).1, (hr.1 v hv).2.1, (hr.1 v hv).2.2.1,
    ⟨?pins, (hr.1 v hv).2.2.2⟩⟩, fun herr => hr.2 herr⟩
  have hpins := cdc_pins_g10 s hW hc hi hw
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_calculate_delegation_cost)).1
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_calculate_delegation_cost)).2
    rfl hnt
  simp only [CdcPinsG10] at hpins ⊢
  intro v' hv'
  cases hv'
  exact hpins v hv

theorem rboundA_to_le_g10 {charged : Bool} {r1 r0 : Nat}
    (h : if charged then r1 < r0 else r1 ≤ r0) : r1 ≤ r0 := by
  cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at h <;> omega

/-! ### The charged switch through the `charge_gas` call with the `ev+32` pin -/

/-- `HandlerRunA.seq_charge_gas` with the head frame's memory-size word `ev+32` threaded
through the callee step: the amount is a positive word, and the callee step receives
the `ev+32` pin and the chain pin of the post-charge state. -/
theorem HandlerRunA.seq_charge_gas_keep32_g10 {F : Type}
    {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {amtExp : ExpHOL 64} {cont : ProgHOL 64}
    (hpos : ∀ t (w : BitVec 64),
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp =
        some (.val (.word w)) → EvmInv t → Group10.HeadMemChainWF t → P t → 0 < w.toNat)
    (hstep : ∀ t cpost,
      EvmInv t → Group10.HeadMemChainWF t → P t →
      EvmInv cpost → Group10.HeadMemChainWF cpost →
      cpost.globals = t.globals →
      memW cpost (globN cpost "ev" + 32) = memW t (globN t "ev" + 32) →
      evmChain cpost = evmChain t →
      Q { cpost with locals := t.locals })
    (hcont : HandlerRunA s0 Q true cont) :
    HandlerRunA s0 P charged
      (.seq (.call (some (none, none)) (ofString "charge_gas") [amtExp]) cont) := by
  intro t hc hi hw hlen hR hp hn
  have hR_le := rboundA_to_le_g10 hR
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hn ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) [amtExp] with _ | values
  · exact opDispatchPostA_error s0 t
  · simp only [hargs] at hn ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup (ofString "charge_gas") values with _ | ⟨body', callee, ret'⟩
    · exact opDispatchPostA_error s0 t
    · simp only [hl] at hn ⊢
      by_cases hz : t.clock = 0
      · simp [hz] at hn
      · simp only [hz, ↓reduceIte] at hn ⊢
        have hv_list : ∃ v0, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp = some v0 ∧ values = [v0] := by
          rw [evalListHOLFinite_eq_toExact] at hargs
          simp only [evalListHOLExact] at hargs
          rcases he : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp with _ | v0
          · simp [he] at hargs
          · simp only [he, Option.some.injEq] at hargs; exact ⟨v0, rfl, hargs.symm⟩
        obtain ⟨v0, hv0_ev, rfl⟩ := hv_list
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "charge_gas") [v0] =
            some (body', callee, ret') := by rwa [← hc]
        obtain ⟨rfl, rfl, amtw, rfl, hamt_cal⟩ :=
          R14Shards.OpHandlersA.one_word_arg_lookup M21.lookup_charge_gas hl_orig
        have hamt_pos : 0 < amtw.toNat := hpos t amtw hv0_ev hi hw hp
        have hi_ce : EvmInv (callEntryStateHOLFinite t callee) := localsFree_evmInv t callee (t.clock - 1) hi
        have hw_ce : Group10.HeadMemChainWF (callEntryStateHOLFinite t callee) :=
          Group10.headMemChainWF_locals t callee (t.clock - 1) hw
        have hch_ce : evmChain (callEntryStateHOLFinite t callee) = evmChain t :=
          OpDispatchSpec.evmChain_congr rfl rfl
        have hR_ce : OpDispatchSpec.evmR (callEntryStateHOLFinite t callee)
            = OpDispatchSpec.evmR t := by
          unfold OpDispatchSpec.evmR
          rw [hch_ce, OpDispatchSpec.memW_congr
            (show (callEntryStateHOLFinite t callee).memory = t.memory from rfl)]
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
          (callEntryStateHOLFinite t callee) (sourceFnBody Guest.Software.guestFn_charge_gas)).1
        have hcg := charge_gas_body_exactA (callEntryStateHOLFinite t callee) hi_ce hw_ce hamt_cal
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee)
            (sourceFnBody Guest.Software.guestFn_charge_gas) with ⟨res, cpost⟩
        simp only [hrun] at hn hmeta hcg ⊢
        change cpost.code = t.code at hmeta
        cases res with
        | none => exact opDispatchPostA_error s0 cpost
        | some r0' =>
          cases r0' with
          | timeOut => simp at hn
          | returned v =>
            by_cases hsh_ok : shapeEqHOL (shapeOfHOLExact v) .one = true
            · simp only [hsh_ok, ↓reduceIte] at hn ⊢
              obtain ⟨⟨hi_cp, hw_cp⟩, hglob_cp, hch_cp, hR_cp⟩ := hcg.1 v rfl
              -- the ev+32 pin, from the keep32 spec applied at the call entry
              obtain ⟨p0, b0, r0, hl0, hspec0⟩ := epsA_charge_gas_exact_keep32_g10
              have hb_eq : sourceFnBody Guest.Software.guestFn_charge_gas = b0 :=
                lookupCodeHOLFinite_installed_body t.code.lookup
                  (ofString "charge_gas") p0 b0 (sourceFnBody Guest.Software.guestFn_charge_gas) r0
                  ShapeHOL.one [.val (.word amtw)] callee (by rwa [hc]) hl
              have hrs_eq : ShapeHOL.one = r0 := by
                have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
                  originalRuntimeCode.lookup (ofString "charge_gas") [.val (.word amtw)]
                  (sourceFnBody Guest.Software.guestFn_charge_gas) callee ShapeHOL.one hl_orig
                simp only [Flapjack.lookupCodeHOLExact, hl0] at hx
                split at hx
                · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
                · cases hx
              have hlook_ce : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "charge_gas")
                  [.val (.word amtw)] = some (b0, callee, r0) := by
                rw [← hb_eq, ← hrs_eq]
                exact hl_orig
              have hnt_ce : (evaluateHOLFiniteState (callEntryStateHOLFinite t callee) b0).1
                  ≠ some .timeOut := by
                rw [← hb_eq, hrun]
                simp
              have hspec_ret := hspec0 (callEntryStateHOLFinite t callee) hc hi_ce hw_ce trivial
                ⟨[.val (.word amtw)], hlook_ce⟩ hnt_ce
              dsimp only at hspec_ret
              obtain ⟨_, _, _, _, hmem32_cp⟩ :=
                (hspec_ret.1 v (by rw [← hb_eq, hrun])).2.2.2
              let resumed : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
              have hi_res : EvmInv resumed := localsFree_evmInv cpost t.locals cpost.clock hi_cp
              have hw_res : Group10.HeadMemChainWF resumed :=
                Group10.headMemChainWF_locals cpost t.locals cpost.clock hw_cp
              have hch_res : evmChain resumed = evmChain cpost := OpDispatchSpec.evmChain_congr rfl rfl
              have hlen_res : (evmChain resumed).length = (evmChain s0).length := by
                rw [hch_res, hch_cp, hch_ce]; exact hlen
              have hR_lt : OpDispatchSpec.evmR resumed < OpDispatchSpec.evmR s0 := by
                have hR_res : OpDispatchSpec.evmR resumed = OpDispatchSpec.evmR cpost := by
                  unfold OpDispatchSpec.evmR
                  rw [hch_res, OpDispatchSpec.memW_congr
                    (show resumed.memory = cpost.memory from rfl)]
                rw [hR_res]
                rw [hR_ce] at hR_cp
                omega
              have hmem32_t : memW cpost (globN cpost "ev" + 32) = memW t (globN t "ev" + 32) := by
                have hgev : globN cpost "ev" = globN t "ev" := globN_congr_g10 hglob_cp "ev"
                rw [hgev]
                rw [← hb_eq, hrun] at hmem32_cp
                exact hmem32_cp
              exact hcont resumed (hmeta.trans hc) hi_res hw_res hlen_res (by simp [hR_lt])
                (hstep t cpost hi hw hp hi_cp hw_cp hglob_cp hmem32_t
                  (hch_cp.trans (OpDispatchSpec.evmChain_congr rfl rfl)))
                (by simpa [resumed] using hn)
            · simp only [hsh_ok, Bool.false_eq_true, ↓reduceIte]
              exact opDispatchPostA_error s0 cpost
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨⟨hi_cp, hw_cp⟩, _, hch_cp, hR_cp⟩ := hcg.2 ⟨ev, rfl⟩
              have hi_el : EvmInv cpost.emptyLocalsHOLFinite := localsFree_evmInv cpost _ cpost.clock hi_cp
              have hw_el : Group10.HeadMemChainWF cpost.emptyLocalsHOLFinite :=
                Group10.headMemChainWF_locals cpost _ cpost.clock hw_cp
              have hch_el : evmChain cpost.emptyLocalsHOLFinite = evmChain cpost :=
                OpDispatchSpec.evmChain_congr rfl rfl
              have hR_el : OpDispatchSpec.evmR cpost.emptyLocalsHOLFinite
                  = OpDispatchSpec.evmR cpost := by
                unfold OpDispatchSpec.evmR
                rw [hch_el, OpDispatchSpec.memW_congr
                  (show cpost.emptyLocalsHOLFinite.memory = cpost.memory from rfl)]
              refine ⟨?_, fun _ => ⟨⟨hi_el, hw_el⟩, ?_, ?_⟩⟩
              · rintro ⟨_, h⟩; cases h
              · rw [hch_el, hch_cp, hch_ce]; exact hlen
              · rw [hR_el, hR_cp, hR_ce]; exact hR_le
            · refine opDispatchPostA_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => exact opDispatchPostA_error s0 cpost
          | «continue» => exact opDispatchPostA_error s0 cpost
          | finalFfi _ =>
            refine opDispatchPostA_other (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => exact opDispatchPostA_error s0 cpost.emptyLocalsHOLFinite

/-! ### `op_staticcall` rest walk (nodes 18-47) -/

/-- A successful `.op` evaluation always returns a word. -/
theorem eval_op_word_g10 {F : Type} {t : PanSemStateFiniteExact 64 F}
    (op : BinOp) (args : List (ExpHOL 64)) (v : ValueHOL 64)
    (hv : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.op op args) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  simp only [evalHOLExact] at hv
  split at hv
  · rename_i values _
    split at hv
    · rename_i _
      cases hwo : wordOpHOL op (List.map valueWord values) with
      | none => rw [hwo] at hv; simp at hv
      | some w =>
        rw [hwo] at hv
        simp only [Option.map_some] at hv
        exact ⟨w, (Option.some.inj hv).symm⟩
    · exact absurd hv (by simp)
  · exact absurd hv (by simp)

/-- A successful `.const` evaluation returns that constant word. -/
theorem eval_const_word_g10 {F : Type} {t : PanSemStateFiniteExact 64 F}
    (c : BitVec 64) (v : ValueHOL 64)
    (hv : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.const c) = some v) :
    v = .val (.word c) := by
  simp only [evalHOLExact] at hv
  exact (Option.some.inj hv).symm

/-- Sequencing is associative at the evaluation level. -/
theorem eval_seq_seq_g10 {F : Type} (t : PanSemStateFiniteExact 64 F)
    (a b c : ProgHOL 64) :
    evaluateHOLFiniteState t (.seq (.seq a b) c) =
      evaluateHOLFiniteState t (.seq a (.seq b c)) := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_seq_line780]
  rw [evaluateHOLFiniteState_seq_line780 (state := t) (first := a) (second := .seq b c)]
  rcases hst : evaluateHOLFiniteState t a with ⟨r0, t0⟩
  simp only [hst]
  cases r0 with
  | none =>
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780 (state := t0) (first := b) (second := c)]
  | some _ => rfl

/-- The `ChildContinuationA` predicate only depends on the evaluation, so the
left-nested `seq` of the `op_staticcall` delegation branch can be reassociated. -/
theorem ccA_seq_seq_assoc_g10 {F : Type} {P : PanSemStateFiniteExact 64 F → Prop}
    {a b c : ProgHOL 64} :
    @ChildContinuationA F P (.seq (.seq a b) c) = @ChildContinuationA F P (.seq a (.seq b c)) := by
  apply propext
  constructor
  · intro h
    unfold ChildContinuationA at h ⊢
    intro t hc hi hw hp hnt
    rw [← eval_seq_seq_g10 t a b c] at hnt ⊢
    exact h t hc hi hw hp hnt
  · intro h
    unfold ChildContinuationA at h ⊢
    intro t hc hi hw hp hnt
    rw [eval_seq_seq_g10 t a b c] at hnt ⊢
    exact h t hc hi hw hp hnt

/-- `LocFrame` pins the memory and the globals of the callee's post state. -/
theorem locFrame_pins_g10 {F : Type} {s cpost : PanSemStateFiniteExact 64 F}
    (h : LocFrame s cpost) : cpost.memory = s.memory ∧ cpost.globals = s.globals := by
  unfold LocFrame at h
  rw [h]
  exact ⟨rfl, rfl⟩

/-- `LocFrame` preserves the head frame's memory-size word `ev+32`. -/
theorem locFrame_mem32_g10 {F : Type} {s cpost : PanSemStateFiniteExact 64 F}
    (h : LocFrame s cpost) : memW cpost (globN cpost "ev" + 32) = memW s (globN s "ev" + 32) := by
  obtain ⟨hmem, hglob⟩ := locFrame_pins_g10 h
  have hgev : globN cpost "ev" = globN s "ev" := globN_congr_g10 hglob "ev"
  unfold memW
  rw [hgev, hmem]

/-- `globN` agrees on matching globals lookups. -/
theorem globN_of_lookup_eq_g10 {F : Type} {s u : PanSemStateFiniteExact 64 F} (n : String)
    (h : u.globals.lookup (ofString n) = s.globals.lookup (ofString n)) :
    globN u n = globN s n := by
  unfold globN
  rw [h]

/-- `scXQ` transport through a read-only callee: the post state is a `LocFrame`
over the call entry, and the continuation restores the caller's locals. -/
theorem scXQ_of_locFrame_call_g10 {F : Type} {t : PanSemStateFiniteExact 64 F}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {cpost : PanSemStateFiniteExact 64 F}
    (hp : scXQ t) (h : LocFrame (callEntryStateHOLFinite t callee) cpost) :
    scXQ { cpost with locals := t.locals } := by
  refine scXQ_of_pins_g10 hp ?_
  exact locFrame_mem32_g10 h

/-- The `x`-shape facts once the memory expansion has been executed: only the
`rStruct` shape of the `x` local survives, the size-word condition having been
consumed by the `extend_memory` entry obligation. -/
def XShQ_g10 {F : Type} (t : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ cw ebw : BitVec 64,
    t.locals.lookup (ofString "x") =
      some (.rStruct [.val (.word cw), .val (.word ebw)])

theorem scXQ_to_XShQ_g10 {F : Type} {t : PanSemStateFiniteExact 64 F}
    (h : scXQ t) : XShQ_g10 t := by
  obtain ⟨cw, ebw, hxl, _⟩ := h
  exact ⟨cw, ebw, hxl⟩

theorem xShQ_setvar_g10 {F : Type} {t : PanSemStateFiniteExact 64 F}
    {nm : MlS} {v : ValueHOL 64} (hne : nm ≠ ofString "x")
    (h : XShQ_g10 t) : XShQ_g10 (setVarHOLFinite nm v t) := by
  obtain ⟨cw, ebw, hxl⟩ := h
  refine ⟨cw, ebw, ?_⟩
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
  exact hxl

theorem globN_lt_g10 {F : Type} (s : PanSemStateFiniteExact 64 F) (n : String) :
    globN s n < 2 ^ 64 := by
  rcases hv : s.globals.lookup (ofString n) with _ | ⟨v⟩
  · simp only [globN, hv]
    omega
  · rcases v with ⟨⟨w⟩⟩ | _ | _
    · simp only [globN, hv]
      exact BitVec.isLt w
    · simp only [globN, hv]
      omega
    · simp only [globN, hv]
      omega

theorem scXQ_of_updW_g10 {F : Type} {t : PanSemStateFiniteExact 64 F}
    (off : Nat) (hoff : off ∈ nonStructFrameOffs) (hoff32 : off ≠ 32) (hi : EvmInv t) (w : BitVec 64)
    (h : scXQ t) :
    scXQ { t with memory := R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (globN t "ev" + off)) w } := by
  have hoff_lt : off + 8 ≤ 280 := by
    simp only [nonStructFrameOffs, List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  obtain ⟨hev280, -⟩ := ev_word_bounds hi
  obtain ⟨cw, ebw, hxl, hbd⟩ := h
  have hm32 : memW { t with memory := R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (globN t "ev" + off)) w } (globN t "ev" + 32) = memW t (globN t "ev" + 32) :=
    R14Shards.OpHandlersA.memW_updW_ne t (globN t "ev" + off) (globN t "ev" + 32) w
      (by omega) (by omega) (by omega)
  refine ⟨cw, ebw, hxl, ?_⟩
  rcases hbd with hz | hb
  · exact Or.inl hz
  · have hgev : globN { t with memory := R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (globN t "ev" + off)) w } "ev" = globN t "ev" := rfl
    rw [hgev, hm32]
    exact Or.inr hb

theorem xShQ_of_updW_g10 {F : Type} {t : PanSemStateFiniteExact 64 F}
    (off : Nat) (w : BitVec 64) (h : XShQ_g10 t) :
    XShQ_g10 { t with memory := R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (globN t "ev" + off)) w } := by
  obtain ⟨cw, ebw, hxl⟩ := h
  exact ⟨cw, ebw, hxl⟩

theorem lookup_add_sat_g10 :
    originalRuntimeCode.lookup (ofString "add_sat") =
      some ([(ofString "a", .one), (ofString "b", .one)],
        sourceFnBody Guest.Software.guestFn_add_sat, .one) :=
  lookup_of_guestAst_getElem 441 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_add_sat) rfl

/-- The `add_sat` callee's argument locals are the (word-shaped) call values. -/
theorem add_sat_args_lookup_g10 {body' : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret' : ShapeHOL}
    {v0 v1 : ValueHOL 64}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "add_sat") [v0, v1] =
      some (body', callee, ret')) :
    ∃ w0 w1 : BitVec 64, v0 = .val (.word w0) ∧ v1 = .val (.word w1) ∧
      callee.lookup (ofString "a") = some (.val (.word w0)) ∧
      callee.lookup (ofString "b") = some (.val (.word w1)) := by
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
    originalRuntimeCode.lookup (ofString "add_sat") [v0, v1] body' callee ret' hl
  simp only [Flapjack.lookupCodeHOLExact, lookup_add_sat_g10] at hx
  split at hx
  · rename_i hcond
    have heq := Option.some.inj hx
    rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨hloc, rfl⟩
    have hall := hcond.2.2
    have hsh_pair : shapeEqHOL ShapeHOL.one (shapeOfHOLExact v0) = true ∧
        shapeEqHOL ShapeHOL.one (shapeOfHOLExact v1) = true := by
      simpa using hall
    obtain ⟨hsh0, hsh1⟩ := hsh_pair
    rcases v0 with ⟨⟨w0⟩⟩ | v0' | v0'
    · rcases v1 with ⟨⟨w1⟩⟩ | v1' | v1'
      · refine ⟨w0, w1, rfl, rfl, ?_, ?_⟩
        · have hfn := congrFun hloc.symm (ofString "a")
          simpa [FUPDATE_LIST, FUPDATE,
            show (ofString "a") ≠ (ofString "b") by decide] using hfn
        · have hfn := congrFun hloc.symm (ofString "b")
          simpa [FUPDATE_LIST, FUPDATE,
            show (ofString "a") ≠ (ofString "b") by decide] using hfn
      · exact absurd hsh1 (by simp [shapeOfHOLExact, shapeEqHOL])
      · exact absurd hsh1 (by simp [shapeOfHOLExact, shapeEqHOL])
    · exact absurd hsh0 (by simp [shapeOfHOLExact, shapeEqHOL])
    · exact absurd hsh0 (by simp [shapeOfHOLExact, shapeEqHOL])
  · cases hx

/-- A `store` step that returns `some` always returns the `.error` result. -/
theorem store_some_eq_error_g10 {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {dst val : ExpHOL 64} {res : PanSemResultExact 64}
    (h : evaluateHOLFiniteState s (.store dst val) = (some res, post)) :
    res = .error := by
  rw [evaluateHOLFiniteState_store] at h
  revert h
  rcases @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst with _ | dv
  · intro h; injection h with h1; injection h1 with h2; exact h2.symm
  · rcases dv with ⟨⟨addr⟩⟩ | _ | _
    · rcases @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val with _ | v
      · intro h; injection h with h1; injection h1 with h2; exact h2.symm
      · dsimp only
        split
        · intro h; injection h with h1; cases h1
        · intro h; injection h with h1; injection h1 with h2; exact h2.symm
    · intro h; injection h with h1; injection h1 with h2; exact h2.symm
    · intro h; injection h with h1; injection h1 with h2; exact h2.symm

/-- A ccA store step at a non-struct `ev`-offset: the frame's memory-size word and
the `x`-local survive the single word write. -/
theorem ccA_seq_store_ev_g10 {F : Type} {P Q : PanSemStateFiniteExact 64 F → Prop}
    (off : Nat) (hoff : off ∈ nonStructFrameOffs) {valExp : ExpHOL 64} {cont : ProgHOL 64}
    (hval : ∀ (t : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      P t →
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) valExp =
        some v →
      ∃ w : BitVec 64, v = .val (.word w))
    (hstep : ∀ (t : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) valExp =
        some (.val (.word w)) →
      EvmInv t → Group10.HeadMemChainWF t → P t →
      Q { t with memory := R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (globN t "ev" + off)) w })
    (hcont : ChildContinuationA Q cont) :
    ChildContinuationA P
      (.seq (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)])
        valExp) cont) := by
  intro t hc hi hw hp hnt
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hst : evaluateHOLFiniteState t
      (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]) valExp) with
    ⟨r1, t1⟩
  simp only [hst] at hnt ⊢
  cases r1 with
  | some res1 =>
    have herr : res1 = PanSemResultExact.error := store_some_eq_error_g10 hst
    subst herr
    exact ⟨fun hv => absurd hv (by rintro ⟨_, h⟩; cases h),
      fun he => absurd he (by rintro ⟨_, h⟩; cases h)⟩
  | none =>
    dsimp only at hnt ⊢
    obtain ⟨hb_ev, evw, hevw, hevw_nat⟩ := ev_word_bounds hi
    have hoff_lt : off + 8 ≤ 280 := by
      simp only [nonStructFrameOffs, List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    have hoff_safe : off ≠ 24 ∧ off ≠ 32 ∧ off ≠ 40 := by
      simp only [nonStructFrameOffs, List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    obtain ⟨w, hw_ev, ht1_eq⟩ := R14Shards.OpHandlersA.store_global_off_word
      (t := t) (post := t1) (gname := "ev") (gbase := globN t "ev") (off := off)
      hevw hevw_nat (by omega) (fun v hv => hval t v hp hv) hst
    have hGt1 : GuestInv t1 := guestInv_congr (s := t)
      (by simp [ht1_eq]) (by simp [ht1_eq]) (by simp [ht1_eq]) (by simp [ht1_eq]) hi.1.1
    have hmem_out : ∀ x : BitVec 64,
        (∀ off' ∈ nonStructFrameOffs, x ≠ BitVec.ofNat 64 (globN t "ev" + off')) →
        t1.memory x = t.memory x := by
      intro x hx
      rw [ht1_eq]
      dsimp only [R14Shards.OpHandlersA.updW]
      rw [if_neg (hx off hoff)]
    obtain ⟨hInv1, hch1, hR1_eq⟩ := evmInv_of_head_nonstruct hi hGt1
      (by simp [ht1_eq]) (by simp [ht1_eq]) hmem_out
    have hWF1 : Group10.HeadMemChainWF t1 := by
      apply headMemChainWF_store_headSafe hi hw
        (x := BitVec.ofNat 64 (globN t "ev" + off))
      · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        exact Or.inl ⟨off, rfl, by omega, hoff_safe.1, hoff_safe.2.1, hoff_safe.2.2⟩
      · simp [ht1_eq]
      · exact hch1
      · intro a ha
        simp [ht1_eq, R14Shards.OpHandlersA.updW, ha]
    have hQ1 : Q t1 := by
      rw [ht1_eq]
      exact hstep t w hw_ev hi hw hp
    have hpost := hcont t1 (by rw [ht1_eq]; exact hc) hInv1 hWF1 hQ1 hnt
    rw [hch1, hR1_eq] at hpost
    exact hpost

/-! ### The `op_staticcall` delegation tail (nodes 27-47) as a child continuation -/

/-- The `op_staticcall` tail after the delegation branch (nodes 27-47). -/
abbrev extCodeProg_g10 : ProgHOL 64 :=
  .decCall (ofString "code") (.comb [.one, .one]) (ofString "ext_code_of")
    [.var .local (ofString "code_address")]
    (.decCall (ofString "gw") .one (ofString "sat_word") [.var .local (ofString "gasv")]
      (.decCall (ofString "mcg") (.comb [.one, .one]) (ofString "calculate_message_call_gas")
        [.rstruct [.const (BitVec.ofNat 64 0), .const (BitVec.ofNat 64 0),
            .const (BitVec.ofNat 64 0), .const (BitVec.ofNat 64 0)],
          .var .local (ofString "gw"),
          .load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 64)]),
          .const (BitVec.ofNat 64 0), .const (BitVec.ofNat 64 0)]
        (.seq (.call (some (none, none)) (ofString "charge_gas")
            [.rfield 0 (.var .local (ofString "mcg"))])
          (.seq (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 184)])
              (.op .sub [.load .one
                  (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 184)]),
                .rfield 1 (.var .local (ofString "mcg"))]))
            (.seq (.call (some (none, none)) (ofString "extend_memory")
                [.rfield 1 (.var .local (ofString "x"))])
              (.dec (ofString "reservoir") .one
                (.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 72)]))
                (.seq (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 72)])
                    (.const (BitVec.ofNat 64 0)))
                  (.decCall (ofString "is") .one (ofString "sat_word")
                    [.var .local (ofString "in_start")]
                    (.decCall (ofString "isz") .one (ofString "sat_word")
                      [.var .local (ofString "in_size")]
                      (.decCall (ofString "os") .one (ofString "sat_word")
                        [.var .local (ofString "out_start")]
                        (.decCall (ofString "osz") .one (ofString "sat_word")
                          [.var .local (ofString "out_size")]
                          (.decCall (ofString "started") .one (ofString "generic_call")
                            [.rfield 1 (.var .local (ofString "mcg")),
                              .var .local (ofString "reservoir"),
                              .rstruct [.const (BitVec.ofNat 64 0), .const (BitVec.ofNat 64 0),
                                .const (BitVec.ofNat 64 0), .const (BitVec.ofNat 64 0)],
                              .load .one (.op .add [.var .local (ofString "msg"),
                                  .const (BitVec.ofNat 64 32)]),
                              .var .local (ofString "to"),
                              .var .local (ofString "code_address"),
                              .const (BitVec.ofNat 64 1), .const (BitVec.ofNat 64 1),
                              .var .local (ofString "is"), .var .local (ofString "isz"),
                              .var .local (ofString "os"), .var .local (ofString "osz"),
                              .rfield 0 (.var .local (ofString "code")),
                              .rfield 1 (.var .local (ofString "code")),
                              .rfield 0 (.var .local (ofString "dl")),
                              .const (BitVec.ofNat 64 0)]
                            (.seq (.ite (.cmp .equal (.var .local (ofString "started"))
                                (.const (BitVec.ofNat 64 0)))
                              (.call (some (none, none)) (ofString "pc_add")
                                [.const (BitVec.ofNat 64 1)])
                              .skip)
                              (.return (.const (BitVec.ofNat 64 0))))))))))))))))

theorem extCodeChain_ccA_g10 {F : Type} (hW : WorldAccountSpecsA)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) :
    @ChildContinuationA F scXQ extCodeProg_g10 := by
  apply ccA_decCall_g10 (Q := scXQ) hW.epsA_ext_code_of
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    obtain ⟨hgk, _, hm32⟩ := hQc
    refine scXQ_of_pins_g10 hp ?_
    rw [globN_of_lookup_eq_g10 "ev" (hgk (ofString "ev") (by decide)).symm]
    exact hm32
  apply ccA_decCall_g10 (Q := scXQ) epsA_sat_word
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    exact scXQ_setvar_g10 (by decide) (scXQ_of_locFrame_call_g10 hp hQc)
  apply ccA_decCall_g10 (Q := scXQ) epsA_calculate_message_call_gas
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    exact scXQ_setvar_g10 (by decide) (scXQ_of_locFrame_call_g10 hp hQc)
  apply ccA_seq_call_g10 (Q := scXQ) epsA_charge_gas_keep32
    (hentry := fun t values body callee rs _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ hQc
    obtain ⟨hglob, hm32⟩ := hQc
    refine scXQ_of_pins_g10 hp ?_
    rw [globN_congr_g10 hglob "ev"]
    exact hm32
  apply ccA_seq_store_ev_g10 (Q := scXQ) 184 (by decide)
    (hval := fun t v _ hv => eval_op_word_g10 _ _ v hv)
    (hstep := fun t w _ hi _ hp => scXQ_of_updW_g10 184 (by decide) (by decide) hi w hp)
  apply ccA_seq_call_g10 (Q := XShQ_g10) epsA_extend_memory
    (hentry := fun t values body callee rs hc hi hw hp ha hl =>
      memoryExpansionLocal_callee_pre_g10 t hc hw hp ha hl)
    (hstep := fun t values body callee rs v cpost _ _ hp _ _ _ hQc => by
      obtain ⟨cw, ebw, hxl, _⟩ := hp
      exact ⟨cw, ebw, hxl⟩)
  apply ccA_dec_g10 (Q := XShQ_g10)
    (hinit := fun t v _ _ hp => xShQ_setvar_g10 (by decide) hp)
  apply ccA_seq_store_ev_g10 (Q := XShQ_g10) 72 (by decide)
    (hval := fun t v _ hv => ⟨(BitVec.ofNat 64 0), eval_const_word_g10 _ v hv⟩)
    (hstep := fun t w _ _ _ hp => xShQ_of_updW_g10 72 w hp)
  apply ccA_decCall_g10 (Q := XShQ_g10) epsA_sat_word
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    exact xShQ_setvar_g10 (by decide) hp
  apply ccA_decCall_g10 (Q := XShQ_g10) epsA_sat_word
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    exact xShQ_setvar_g10 (by decide) hp
  apply ccA_decCall_g10 (Q := XShQ_g10) epsA_sat_word
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    exact xShQ_setvar_g10 (by decide) hp
  apply ccA_decCall_g10 (Q := XShQ_g10) epsA_sat_word
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    exact xShQ_setvar_g10 (by decide) hp
  apply ccA_decCall_g10 (Q := XShQ_g10) hgc
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    exact xShQ_setvar_g10 (by decide) hp
  apply ccA_seq_ite_g10
  · intro t w _ _
    exact ccA_seq_call_g10 (Q := fun _ => True) epsA_pc_add
      (hentry := fun t values body callee rs _ _ _ _ _ _ => trivial)
      (hstep := fun t values body callee rs v cpost _ _ _ _ _ _ hQc => trivial)
      (ccA_ret_g10 (.const (BitVec.ofNat 64 0)))
  · intro t _
    exact ccA_seq_skip_g10 (ccA_ret_g10 (.const (BitVec.ofNat 64 0)))

/-! ### The `op_staticcall` delegation chain (nodes 20-47) -/

theorem dlChain_ccA_g10 {F : Type} (hW : WorldAccountSpecsA)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) :
    @ChildContinuationA F scXQ
      (.decCall (ofString "dl") (.comb [.one, .one, .one])
        (ofString "calculate_delegation_cost") [.var .local (ofString "to")]
        (.dec (ofString "code_address") .one (.rfield 1 (.var .local (ofString "dl")))
          (.seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "dl")))
              (.const (BitVec.ofNat 64 0)))
            (.seq (.call (some (none, none)) (ofString "charge_gas")
                [.rfield 2 (.var .local (ofString "dl"))])
              (.call (some (none, none)) (ofString "warm_address")
                [.var .local (ofString "code_address")]))
            .skip)
            extCodeProg_g10))) := by
  apply ccA_decCall_g10 (Q := scXQ) (epsA_cdc_full_g10 hW)
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    obtain ⟨hpins, _, _⟩ := hQc
    obtain ⟨hev, hm32, _⟩ := hpins v rfl
    refine scXQ_setvar_g10 (by decide) (scXQ_of_pins_g10 hp ?_)
    rw [hev]
    exact hm32
  apply ccA_dec_g10 (Q := scXQ)
    (hinit := fun t v _ _ hp => scXQ_setvar_g10 (by decide) hp)
  apply ccA_seq_ite_g10
  · intro t w _ _
    rw [ccA_seq_seq_assoc_g10]
    apply ccA_seq_call_g10 (Q := scXQ) epsA_charge_gas_keep32
      (hentry := fun t values body callee rs _ _ _ _ _ _ => trivial)
    · intro t values body callee rs v cpost _ _ hp _ _ _ hQc
      obtain ⟨hglob, hm32⟩ := hQc
      refine scXQ_of_pins_g10 hp ?_
      rw [globN_congr_g10 hglob "ev"]
      exact hm32
    · apply ccA_seq_call_g10 (Q := scXQ) Group10.epsA_warm_address_keep32_g10
        (hentry := fun t values body callee rs _ _ _ _ _ _ => trivial)
      · intro t values body callee rs v cpost _ _ hp _ _ _ hQc
        obtain ⟨hgk, _, hm32⟩ := hQc
        refine scXQ_of_pins_g10 hp ?_
        rw [globN_of_lookup_eq_g10 "ev" (hgk (ofString "ev") (by decide)).symm]
        exact hm32
      · exact extCodeChain_ccA_g10 hW hgc
  · intro t _
    exact ccA_seq_skip_g10 (extCodeChain_ccA_g10 hW hgc)

/-! ### The `op_staticcall` rest (nodes 18-47) -/

theorem staticcallRest_ccA_g10 {F : Type} (hW : WorldAccountSpecsA)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) :
    @ChildContinuationA F scXQ
      (.seq (.ite (.cmp .equal (.var .local (ofString "warm")) (.const (BitVec.ofNat 64 0)))
          (.call (some (none, none)) (ofString "warm_address") [.var .local (ofString "to")])
          .skip)
        (.decCall (ofString "dl") (.comb [.one, .one, .one])
          (ofString "calculate_delegation_cost") [.var .local (ofString "to")]
          (.dec (ofString "code_address") .one (.rfield 1 (.var .local (ofString "dl")))
            (.seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "dl")))
                (.const (BitVec.ofNat 64 0)))
              (.seq (.call (some (none, none)) (ofString "charge_gas")
                  [.rfield 2 (.var .local (ofString "dl"))])
                (.call (some (none, none)) (ofString "warm_address")
                  [.var .local (ofString "code_address")]))
              .skip)
              extCodeProg_g10)))) := by
  apply ccA_seq_ite_g10
  · intro t w _ _
    exact ccA_seq_call_g10 (Q := scXQ) Group10.epsA_warm_address_keep32_g10
      (hentry := fun t values body callee rs _ _ _ _ _ _ => trivial)
      (hstep := fun t values body callee rs v cpost _ _ hp _ _ _ hQc => by
        obtain ⟨hgk, _, hm32⟩ := hQc
        refine scXQ_of_pins_g10 hp ?_
        rw [globN_of_lookup_eq_g10 "ev" (hgk (ofString "ev") (by decide)).symm]
        exact hm32)
      (dlChain_ccA_g10 hW hgc)
  · intro t _
    exact ccA_seq_skip_g10 (dlChain_ccA_g10 hW hgc)

/-! ### The `op_staticcall` need chain (nodes 14-16) -/

theorem op_staticcall_needChain_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {charged : Bool} {cont : ProgHOL 64} (hW : WorldAccountSpecsA)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call"))
    (hcont : HandlerRunA s0 scXQ true cont) :
    HandlerRunA s0 (fun s => scXQ s ∧ AcQ_g10 s) charged
      (.decCall (ofString "need") .one (ofString "add_sat")
        [.var .local (ofString "access_cost"), .rfield 0 (.var .local (ofString "x"))]
        (.seq (.call (some (none, none)) (ofString "charge_gas") [.var .local (ofString "need")])
          cont)) := by
  apply HandlerRunA.decCall (Q := fun s => scXQ s ∧ NdQ_g10 s) epsA_add_sat_ge_g10
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost hi hw hp hargs hlk hi2 hw2 hch hQc
    obtain ⟨hlf, aw, rw, hla, hvw, hle⟩ := hQc
    obtain ⟨acw, hl_ac, hac⟩ := hp.2
    obtain ⟨v0, v1, hv0_ev, hv1_ev, hvals⟩ : ∃ v0 v1,
        @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.var .local (ofString "access_cost")) = some v0 ∧
        @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.rfield 0 (.var .local (ofString "x"))) = some v1 ∧
        values = [v0, v1] := by
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact] at hargs
      rcases he0 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.var .local (ofString "access_cost")) with _ | v0
      · simp [he0] at hargs
      rcases he1 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.rfield 0 (.var .local (ofString "x"))) with _ | v1
      · simp [he0, he1] at hargs
      simp only [he0, he1, Option.some.injEq] at hargs
      exact ⟨v0, v1, rfl, rfl, hargs.symm⟩
    subst hvals
    obtain ⟨w0, w1, hv0w, hv1w, hla0, _⟩ := add_sat_args_lookup_g10 hlk
    have hv0_acw : t.locals.lookup (ofString "access_cost") = some (.val (.word w0)) := by
      rw [← hv0w]; exact hv0_ev
    have hw0_acw : w0 = acw := by
      have h := hl_ac.symm.trans hv0_acw
      injection h with h1
      injection h1 with h2
      injection h2 with h3
      exact h3.symm
    have hla' : callee.lookup (ofString "a") = some (.val (.word aw)) := hla
    have haw : aw = w0 := by
      have h := hla'.symm.trans hla0
      injection h with h1
      injection h1 with h2
      injection h2 with h3
    have hle_nat : aw.toNat ≤ rw.toNat := hle
    rw [haw, hw0_acw] at hle_nat
    have h100 : 100 ≤ acw.toNat := by rcases hac with rfl | rfl <;> simp
    refine ⟨scXQ_setvar_g10 (by decide) (scXQ_of_locFrame_call_g10 hp.1 hlf), rw, ?_, ?_⟩
    · dsimp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      first | rw [if_pos rfl, hvw] | simp [hvw]
    · omega
  apply HandlerRunA.seq_charge_gas_keep32_g10 (Q := scXQ)
    (hpos := fun t w hv _ _ hp => by
      obtain ⟨nw, hlk_n, hbound⟩ := hp.2
      have hev : t.locals.lookup (ofString "need") = some (.val (.word w)) := hv
      rw [hlk_n] at hev
      injection hev with h1
      injection h1 with h2
      injection h2 with h3
      subst h3
      omega)
    (hstep := fun t cpost _ _ hp _ _ _ hm32 _ => scXQ_of_pins_g10 hp.1 hm32)
    (hcont := hcont)

/-! ### The `op_staticcall` compiled prefix (nodes 10-16) -/

theorem op_staticcall_prefix2_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {charged : Bool} {cont : ProgHOL 64} (hW : WorldAccountSpecsA)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call"))
    (hcont : HandlerRunA s0 scXQ true cont) :
    HandlerRunA s0 scXQ charged
      (.decCall (ofString "warm") .one (ofString "is_warm_address") [.var .local (ofString "to")]
        (.dec (ofString "access_cost") .one (.const (BitVec.ofNat 64 100))
          (.seq (.ite (.cmp .equal (.var .local (ofString "warm")) (.const (BitVec.ofNat 64 0)))
              (.assign .local (ofString "access_cost") (.const (BitVec.ofNat 64 3000))) .skip)
            (.decCall (ofString "need") .one (ofString "add_sat")
              [.var .local (ofString "access_cost"), .rfield 0 (.var .local (ofString "x"))]
              (.seq (.call (some (none, none)) (ofString "charge_gas")
                [.var .local (ofString "need")]) cont))))) := by
  apply HandlerRunA.decCall (Q := scXQ) epsA_is_warm_address
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    exact scXQ_setvar_g10 (by decide) (scXQ_of_locFrame_call_g10 hp hQc)
  apply HandlerRunA.dec (Q := fun s => scXQ s ∧ AcQ_g10 s)
    (hinit := fun t v hv _ hp => by
      have hvw : v = .val (.word (BitVec.ofNat 64 100)) := eval_const_word_g10 _ v hv
      subst hvw
      refine ⟨scXQ_setvar_g10 (by decide) hp, (BitVec.ofNat 64 100), ?_, Or.inl rfl⟩
      dsimp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      first | rw [if_pos rfl] | simp)
  apply HandlerRunA.seq_ite_unit
  · intro t w _ _
    apply HandlerRunA.seq_assign_local (Q := fun s => scXQ s ∧ AcQ_g10 s)
      (hasgn := fun t v hv _ hp => by
        have hvw : v = .val (.word (BitVec.ofNat 64 3000)) := eval_const_word_g10 _ v hv
        subst hvw
        refine ⟨scXQ_setvar_g10 (by decide) hp.1, (BitVec.ofNat 64 3000), ?_, Or.inr rfl⟩
        dsimp only [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        first | rw [if_pos rfl] | simp)
    exact op_staticcall_needChain_g10 hW hgc hcont
  · intro t _
    exact HandlerRunA.seq_skip (op_staticcall_needChain_g10 hW hgc hcont)

/-! ### `op_staticcall` assembly -/

theorem op_staticcall_run_full_g10 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (hW : WorldAccountSpecsA)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) :
    HandlerRunA s0 (fun _ => True) false (sourceFnBody Guest.Software.guestFn_op_staticcall) :=
  op_staticcall_prefix1_g10
    (op_staticcall_prefix2_g10 hW hgc
      (handlerRunA_of_childContinuation_g10 s0 _ _ (staticcallRest_ccA_g10 hW hgc)))

theorem op_staticcall_specA_g10 (hW : WorldAccountSpecsA)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) :
    OpHandlerSpecA (ofString "op_staticcall") := by
  refine opHandlerSpecA_of_run 606 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_op_staticcall rfl ?_
  intro F s0 hInv0 hWF0 hnd0
  exact op_staticcall_run_full_g10 s0 hW hgc
