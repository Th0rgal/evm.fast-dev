import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group10CallsCreatesTail3

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

theorem evmInv_gas_top_g10t4 {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : EvmInv s) : evmR s + 1 < 2 ^ 64 := by
  obtain ⟨_, _, _, hrest⟩ := h
  dsimp only at hrest
  exact hrest.2.2.2.2.2.2.2.2.2.2.2

/-- A local slot other than the assigned one is untouched by `setVarHOLFinite`. -/
theorem setVar_lookup_ne_g10t4 {F : Type} (t : PanSemStateFiniteExact 64 F)
    (nm nm' : MlS) (v : ValueHOL 64) (hne : nm ≠ nm') :
    (setVarHOLFinite nm v t).locals.lookup nm' = t.locals.lookup nm' := by
  simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [if_neg (by simp [hne])]

/-- A local slot other than the assigned one is untouched by a call-return resume
that also restores the caller's locals. -/
theorem setVarRes_lookup_ne_g10t4 {F : Type} (t cpost : PanSemStateFiniteExact 64 F)
    (nm nm' : MlS) (v : ValueHOL 64) (hne : nm ≠ nm') :
    (setVarHOLFinite nm v { cpost with locals := t.locals }).locals.lookup nm' =
      t.locals.lookup nm' := by
  simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [if_neg (by simp [hne])]

/-- Transport `CcPQ` to a state whose pinned locals, `ev` global, `ev+32` word and
`evmR` agree with the old one. -/
theorem CcPQ_lu_g10t4 {F : Type} {s0 t r : PanSemStateFiniteExact 64 F}
    (hlu : ∀ nm' ∈ (["value", "vz", "transfer_cost", "access_cost", "x", "dl"] : List String),
      r.locals.lookup (ofString nm') = t.locals.lookup (ofString nm'))
    (heR : evmR r ≤ evmR t) (hgm : globN r "ev" = globN t "ev")
    (hxm : memW r (globN t "ev" + 32) = memW t (globN t "ev" + 32))
    (h : CcPQ_g10 s0 t) : CcPQ_g10 s0 r := by
  obtain ⟨q0, q1, q2, q3, vz, tcw, acw, cw, ebw, Sl,
    hvalue, hvz, htc, hac, hacw, hx, hxebw, hvzcase, hcredit, hInvS⟩ := h
  refine ⟨q0, q1, q2, q3, vz, tcw, acw, cw, ebw, Sl,
    (hlu "value" (by decide)).trans hvalue, (hlu "vz" (by decide)).trans hvz,
    (hlu "transfer_cost" (by decide)).trans htc,
    (hlu "access_cost" (by decide)).trans hac, hacw,
    (hlu "x" (by decide)).trans hx, ?_, hvzcase, ?_, hInvS⟩
  · rcases hxebw with hz | hb
    · exact Or.inl hz
    · rw [hgm]
      exact Or.inr ⟨by rw [hxm]; exact hb.1, by rw [hxm]; exact hb.2⟩
  · omega

/-- Transport `CcDLQ` to a state whose pinned locals (including `dl`), `ev`
global, `ev+32` word and `evmR` agree with the old one. -/
theorem CcDLQ_lu_g10t4 {F : Type} {s0 t r : PanSemStateFiniteExact 64 F}
    (hlu : ∀ nm' ∈ (["value", "vz", "transfer_cost", "access_cost", "x", "dl"] : List String),
      r.locals.lookup (ofString nm') = t.locals.lookup (ofString nm'))
    (heR : evmR r ≤ evmR t) (hgm : globN r "ev" = globN t "ev")
    (hxm : memW r (globN t "ev" + 32) = memW t (globN t "ev" + 32))
    (h : CcDLQ_g10 s0 t) : CcDLQ_g10 s0 r := by
  obtain ⟨hpq, d0, d1, d2, hdl, hc1, hc2⟩ := h
  exact ⟨CcPQ_lu_g10t4 hlu heR hgm hxm hpq,
    d0, d1, d2, (hlu "dl" (by decide)).trans hdl, hc1, hc2⟩

/-- Transport `CcR2Q` over a plain `dec` local assignment outside `mcg`. -/
theorem CcR2Q_setVar_g10t4 {F : Type} {s0 t : PanSemStateFiniteExact 64 F}
    {nm : MlS} {v : ValueHOL 64} (hne : nm ≠ ofString "mcg")
    (h : CcR2Q_g10 s0 t) : CcR2Q_g10 s0 (setVarHOLFinite nm v t) := by
  obtain ⟨w0, w1, hmcg, hcredit, hInvS⟩ := h
  have hc : evmR (setVarHOLFinite nm v t) = evmR t :=
    (evm_congr (s := t) (t := setVarHOLFinite nm v t) rfl rfl).2.1
  refine ⟨w0, w1, ?_, ?_, hInvS⟩
  · rw [setVar_lookup_ne_g10t4 t nm (ofString "mcg") v hne]
    exact hmcg
  · rw [hc]
    exact hcredit

/-- Transport `CcR2Q` over a call-return resume assigning a local outside `mcg`. -/
theorem CcR2Q_setVarRes_g10t4 {F : Type} {s0 t cpost : PanSemStateFiniteExact 64 F}
    {nm : MlS} {v : ValueHOL 64} (hne : nm ≠ ofString "mcg")
    (heR : evmR cpost ≤ evmR t) (h : CcR2Q_g10 s0 t) :
    CcR2Q_g10 s0 (setVarHOLFinite nm v { cpost with locals := t.locals }) := by
  obtain ⟨w0, w1, hmcg, hcredit, hInvS⟩ := h
  have hc : evmR (setVarHOLFinite nm v { cpost with locals := t.locals }) = evmR cpost :=
    (evm_congr (s := cpost)
      (t := setVarHOLFinite nm v { cpost with locals := t.locals }) rfl rfl).2.1
  refine ⟨w0, w1, ?_, ?_, hInvS⟩
  · rw [setVarRes_lookup_ne_g10t4 t cpost nm (ofString "mcg") v hne]
    exact hmcg
  · omega

/-! ### Stage C, chunk 4 batch B2a: helper lemmas for the `op_callcode` tail walk -/

/-- The first word of the `mcg` record, read as a standalone expression. -/
theorem eval_rfield0_mcg_word_g10t4 {F : Type} {t : PanSemStateFiniteExact 64 F}
    {w0 w1 amtw : BitVec 64}
    (hmcg : t.locals.lookup (ofString "mcg") =
      some (.rStruct [.val (.word w0), .val (.word w1)]))
    (hv : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.rfield 0 (.var .local (ofString "mcg"))) = some (.val (.word amtw))) :
    amtw = w0 := by
  simp [evalHOLExact, hmcg] at hv
  exact hv.symm

/-- The third word of the `dl` record, read as a standalone expression. -/
theorem eval_rfield2_dl_word_g10t4 {F : Type} {t : PanSemStateFiniteExact 64 F}
    {d0 d1 d2 amtw : BitVec 64}
    (hdl : t.locals.lookup (ofString "dl") =
      some (.rStruct [.val (.word d0), .val (.word d1), .val (.word d2)]))
    (hv : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.rfield 2 (.var .local (ofString "dl"))) = some (.val (.word amtw))) :
    amtw = d2 := by
  simp [evalHOLExact, hdl] at hv
  exact hv.symm

/-- Strict head-frame bound on the `ev` global. -/
theorem ev280_lt_g10t4 {F : Type} {t : PanSemStateFiniteExact 64 F} (hInv : EvmInv t) :
    globN t "ev" + 280 < 2 ^ 64 := by
  obtain ⟨hAR, S, hWT, hrest⟩ := hInv
  dsimp only at hrest
  obtain ⟨hch_ne, hch_len, hlast, hFWF, hFRoom, hRetW, hPair, hDisj, hTries, hMarks, hRoles, hGasSum⟩ := hrest
  have hhead : (globN t "ev", globN t "cur_cont") ∈ evmChain t := by
    simp [evmChain, evmChainFrom]
  have hF0 := hFWF _ hhead
  have hbb := (hF0.1 (globN t "ev", 280) (by simp)).1.2
  rw [R11Shards.scratchEnd_val] at hbb
  omega

/-- An off-store at `ev+k` (k = 184 or 72) preserves the head stack-size word at
`ev+32`. -/
theorem memW_updW_ev32_g10t4 {F : Type} {t : PanSemStateFiniteExact 64 F}
    {k : Nat} (hlt : globN t "ev" + 280 < 2 ^ 64) (w : BitVec 64) (hk : k = 184 ∨ k = 72)
    (hk32 : k ≠ 32) :
    memW ({ t with memory := R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (globN t "ev" + k)) w })
        (globN t "ev" + 32) = memW t (globN t "ev" + 32) := by
  have hbvne : BitVec.ofNat 64 (globN t "ev" + k) ≠ BitVec.ofNat 64 (globN t "ev" + 32) := by
    intro h
    have hc := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at hc
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc
    omega
  simp [memW, R14Shards.OpHandlersA.updW, Ne.symm hbvne]

/-- The call entry state has the same `evmR` as the caller. -/
theorem evmR_entry_eq_g10t4 {F : Type} {t : PanSemStateFiniteExact 64 F}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} :
    evmR (callEntryStateHOLFinite t callee) = evmR t :=
  (evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl).2.1

/-- A five-argument call list decomposes into its component evaluations. -/
theorem evalList5_decomp_g10t4 {F : Type} {t : PanSemStateFiniteExact 64 F}
    {e0 e1 e2 e3 e4 : ExpHOL 64} {values : List (ValueHOL 64)}
    (hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
      [e0, e1, e2, e3, e4] = some values) :
    ∃ v0 v1 v2 v3 v4 : ValueHOL 64,
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e0 = some v0 ∧
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e1 = some v1 ∧
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e2 = some v2 ∧
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e3 = some v3 ∧
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e4 = some v4 ∧
      values = [v0, v1, v2, v3, v4] := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact] at hargs
  rcases he0 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e0 with _ | v0
  · simp [he0] at hargs
  rcases he1 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e1 with _ | v1
  · simp [he0, he1] at hargs
  rcases he2 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e2 with _ | v2
  · simp [he0, he1, he2] at hargs
  rcases he3 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e3 with _ | v3
  · simp [he0, he1, he2, he3] at hargs
  rcases he4 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e4 with _ | v4
  · simp [he0, he1, he2, he3, he4] at hargs
  simp only [he0, he1, he2, he3, he4, Option.some.injEq] at hargs
  exact ⟨v0, v1, v2, v3, v4, rfl, rfl, rfl, rfl, rfl, hargs.symm⟩

/-- Six pinned locals are untouched by a `dec` that assigns outside them. -/
theorem lu6_setVar_ne_g10t4 {F : Type} (t : PanSemStateFiniteExact 64 F)
    (nm : MlS) (v : ValueHOL 64)
    (hne : nm ≠ ofString "value" ∧ nm ≠ ofString "vz" ∧ nm ≠ ofString "transfer_cost" ∧
      nm ≠ ofString "access_cost" ∧ nm ≠ ofString "x" ∧ nm ≠ ofString "dl") :
    ∀ nm' ∈ (["value", "vz", "transfer_cost", "access_cost", "x", "dl"] : List String),
      (setVarHOLFinite nm v t).locals.lookup (ofString nm') = t.locals.lookup (ofString nm') := by
  intro nm' hmem
  simp only [List.mem_cons, List.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | hbad
  · exact setVar_lookup_ne_g10t4 t nm (ofString "value") v hne.1
  · exact setVar_lookup_ne_g10t4 t nm (ofString "vz") v hne.2.1
  · exact setVar_lookup_ne_g10t4 t nm (ofString "transfer_cost") v hne.2.2.1
  · exact setVar_lookup_ne_g10t4 t nm (ofString "access_cost") v hne.2.2.2.1
  · exact setVar_lookup_ne_g10t4 t nm (ofString "x") v hne.2.2.2.2.1
  · exact setVar_lookup_ne_g10t4 t nm (ofString "dl") v hne.2.2.2.2.2
  · cases hbad

/-- Six pinned locals are untouched by a call-return resume assigning outside them. -/
theorem lu6_setVarRes_ne_g10t4 {F : Type} (t cpost : PanSemStateFiniteExact 64 F)
    (nm : MlS) (v : ValueHOL 64)
    (hne : nm ≠ ofString "value" ∧ nm ≠ ofString "vz" ∧ nm ≠ ofString "transfer_cost" ∧
      nm ≠ ofString "access_cost" ∧ nm ≠ ofString "x" ∧ nm ≠ ofString "dl") :
    ∀ nm' ∈ (["value", "vz", "transfer_cost", "access_cost", "x", "dl"] : List String),
      (setVarHOLFinite nm v { cpost with locals := t.locals }).locals.lookup (ofString nm')
        = t.locals.lookup (ofString nm') := by
  intro nm' hmem
  simp only [List.mem_cons, List.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | hbad
  · exact setVarRes_lookup_ne_g10t4 t cpost nm (ofString "value") v hne.1
  · exact setVarRes_lookup_ne_g10t4 t cpost nm (ofString "vz") v hne.2.1
  · exact setVarRes_lookup_ne_g10t4 t cpost nm (ofString "transfer_cost") v hne.2.2.1
  · exact setVarRes_lookup_ne_g10t4 t cpost nm (ofString "access_cost") v hne.2.2.2.1
  · exact setVarRes_lookup_ne_g10t4 t cpost nm (ofString "x") v hne.2.2.2.2.1
  · exact setVarRes_lookup_ne_g10t4 t cpost nm (ofString "dl") v hne.2.2.2.2.2
  · cases hbad

/-- Transport `CcPQ` over a state whose pinned locals (five names), `ev` global,
`ev+32` word and `evmR` agree with the old one. -/
theorem CcPQ_lu5_g10t4 {F : Type} {s0 t r : PanSemStateFiniteExact 64 F}
    (hlu : ∀ nm' ∈ (["value", "vz", "transfer_cost", "access_cost", "x"] : List String),
      r.locals.lookup (ofString nm') = t.locals.lookup (ofString nm'))
    (heR : evmR r ≤ evmR t) (hgm : globN r "ev" = globN t "ev")
    (hxm : memW r (globN t "ev" + 32) = memW t (globN t "ev" + 32))
    (h : CcPQ_g10 s0 t) : CcPQ_g10 s0 r := by
  obtain ⟨q0, q1, q2, q3, vz, tcw, acw, cw, ebw, Sl,
    hvalue, hvz, htc, hac, hacw, hx, hxebw, hvzcase, hcredit, hInvS⟩ := h
  refine ⟨q0, q1, q2, q3, vz, tcw, acw, cw, ebw, Sl,
    (hlu "value" (by decide)).trans hvalue, (hlu "vz" (by decide)).trans hvz,
    (hlu "transfer_cost" (by decide)).trans htc,
    (hlu "access_cost" (by decide)).trans hac, hacw,
    (hlu "x" (by decide)).trans hx, ?_, hvzcase, ?_, hInvS⟩
  · rcases hxebw with hz | hb
    · exact Or.inl hz
    · rw [hgm]
      exact Or.inr ⟨by rw [hxm]; exact hb.1, by rw [hxm]; exact hb.2⟩
  · omega

/-- Transport `CcR2Q` over a plain call-return resume with `evmR cpost ≤ evmR t`. -/
theorem CcR2Q_res_g10t4 {F : Type} {s0 t cpost : PanSemStateFiniteExact 64 F}
    (heR : evmR cpost ≤ evmR t) (h : CcR2Q_g10 s0 t) :
    CcR2Q_g10 s0 { cpost with locals := t.locals } := by
  obtain ⟨w0, w1, hmcg, hcredit, hInvS⟩ := h
  have h1 : evmR { cpost with locals := t.locals } = evmR cpost :=
    (evm_congr (s := cpost) (t := { cpost with locals := t.locals }) rfl rfl).2.1
  exact ⟨w0, w1, hmcg, by rw [h1]; omega, hInvS⟩

/-! ### Batch B2b: the `op_callcode` tail walk (chunk 5)

The tail after the prefix's `charge_gas [need]`: the warm-ite, the delegation-cost
chain, the message-call-gas charge with the spill/restore ledger, and the
insufficient-funds branch, down to the terminal `started`-test continuation. -/

/-- Five pinned locals are untouched by a call-return resume assigning outside them. -/
theorem lu5_setVarRes_ne_g10t4 {F : Type} (t cpost : PanSemStateFiniteExact 64 F)
    (nm : MlS) (v : ValueHOL 64)
    (hne : nm ≠ ofString "value" ∧ nm ≠ ofString "vz" ∧ nm ≠ ofString "transfer_cost" ∧
      nm ≠ ofString "access_cost" ∧ nm ≠ ofString "x") :
    ∀ nm' ∈ (["value", "vz", "transfer_cost", "access_cost", "x"] : List String),
      (setVarHOLFinite nm v { cpost with locals := t.locals }).locals.lookup (ofString nm')
        = t.locals.lookup (ofString nm') := by
  intro nm' hmem
  simp only [List.mem_cons, List.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | hbad
  · exact setVarRes_lookup_ne_g10t4 t cpost nm (ofString "value") v hne.1
  · exact setVarRes_lookup_ne_g10t4 t cpost nm (ofString "vz") v hne.2.1
  · exact setVarRes_lookup_ne_g10t4 t cpost nm (ofString "transfer_cost") v hne.2.2.1
  · exact setVarRes_lookup_ne_g10t4 t cpost nm (ofString "access_cost") v hne.2.2.2.1
  · exact setVarRes_lookup_ne_g10t4 t cpost nm (ofString "x") v hne.2.2.2.2
  · cases hbad

/-- Transport `CcDLQ` over a plain `dec` local assignment outside the six pinned names. -/
theorem CcDLQ_setVar_g10t4 {F : Type} {s0 t : PanSemStateFiniteExact 64 F}
    {nm : MlS} {v : ValueHOL 64}
    (hne : nm ≠ ofString "value" ∧ nm ≠ ofString "vz" ∧ nm ≠ ofString "transfer_cost" ∧
      nm ≠ ofString "access_cost" ∧ nm ≠ ofString "x" ∧ nm ≠ ofString "dl")
    (h : CcDLQ_g10 s0 t) : CcDLQ_g10 s0 (setVarHOLFinite nm v t) := by
  have hc : evmR (setVarHOLFinite nm v t) = evmR t :=
    (evm_congr (s := t) (t := setVarHOLFinite nm v t) rfl rfl).2.1
  exact CcDLQ_lu_g10t4 (lu6_setVar_ne_g10t4 t nm v hne) (by rw [hc]) rfl rfl h

/-! ## Continuation no-read (compositional machinery)

The `op_call` tail needs `seq_decCall_swap_g10` for the `alive` binding whose
continuation is the whole remaining message-call tail. Rather than proving
`ContNoread_g10` for that large continuation in one go, we build it
compositionally: per-shape evaluation congruences for expressions that never
read the local slot, and per-constructor lemmas that transport the no-read
property through every statement form occurring in the tail. The conclusion
has three parts (result equality, same-but-locals posts, and pointwise locals
agreement off the slot) so the lemmas chain through sequences and calls. -/

/-! ### Pointwise finite-map helpers -/

/-- Writing a local slot sets its own lookup. -/
theorem lookup_setVar_self_g10t4 {F : Type} (t : PanSemStateFiniteExact 64 F)
    (nm : MlS) (v : ValueHOL 64) :
    (setVarHOLFinite nm v t).locals.lookup nm = some v := by
  simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [if_pos (by simp)]

/-- Restoring a caller slot writes exactly the caller's old value. -/
theorem resVarEq_lookup_self_g10t4 {α β : Type} [DecidableEq α]
    (L : HolFiniteMapExact α β) (n : α) (p : Option β) :
    (HolFiniteMapExact.resVarEq L (n, p)).lookup n = p := by
  cases p with
  | none =>
      simp only [HolFiniteMapExact.resVarEq, HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL]
      rw [if_pos (by simp)]
  | some v =>
      simp only [HolFiniteMapExact.resVarEq, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
      rw [if_pos (by simp)]

/-- Restoring a caller slot leaves every other lookup untouched. -/
theorem resVarEq_lookup_ne_g10t4 {α β : Type} [DecidableEq α]
    (L : HolFiniteMapExact α β) (n : α) (p : Option β) {k : α} (hk : k ≠ n) :
    (HolFiniteMapExact.resVarEq L (n, p)).lookup k = L.lookup k := by
  cases p with
  | none =>
      simp only [HolFiniteMapExact.resVarEq, HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL]
      rw [if_neg hk]
  | some v =>
      simp only [HolFiniteMapExact.resVarEq, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
      rw [if_neg hk]

/-! ### Expression congruences (one local slot never read) -/

/-- Pointwise evaluation agreement between two states that agree off `locals`. -/
abbrev EvalEqN_g10t4 {F : Type} (s1 s2 : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) : Prop :=
  @evalHOLExact 64 F _ s1.toExact (fun address => Classical.propDecidable (s1.memaddrs address)) e =
    @evalHOLExact 64 F _ s2.toExact (fun address => Classical.propDecidable (s2.memaddrs address)) e

/-- Pointwise list-evaluation agreement in the exact evaluator. -/
abbrev ListEqX_g10t4 {F : Type} (s1 s2 : PanSemStateFiniteExact 64 F)
    (args : List (ExpHOL 64)) : Prop :=
  @evalListHOLExact 64 F _ s1.toExact
      (fun address => Classical.propDecidable (s1.memaddrs address)) args =
    @evalListHOLExact 64 F _ s2.toExact
      (fun address => Classical.propDecidable (s2.memaddrs address)) args

/-- The exact list agreement read as a finite-evaluator equation. -/
theorem listEqX_finite_g10t4 {F : Type} {s1 s2 : PanSemStateFiniteExact 64 F}
    {args : List (ExpHOL 64)} (h : ListEqX_g10t4 s1 s2 args) :
    evalListHOLFinite s1 (h := fun address => Classical.propDecidable (s1.memaddrs address)) args =
      evalListHOLFinite s2 (h := fun address => Classical.propDecidable (s2.memaddrs address)) args :=
  h

theorem evalN_const_g10t4 {F : Type} {s1 s2 : PanSemStateFiniteExact 64 F} (c : BitVec 64) :
    EvalEqN_g10t4 s1 s2 (.const c) := rfl

theorem evalN_var_local_g10t4 {F : Type} {s1 s2 : PanSemStateFiniteExact 64 F} {nm k : MlS}
    (hk : k ≠ nm)
    (hloc : ∀ j, j ≠ nm → s1.locals.lookup j = s2.locals.lookup j) :
    EvalEqN_g10t4 s1 s2 (.var .local k) := hloc k hk

theorem evalN_var_global_g10t4 {F : Type} {s1 s2 : PanSemStateFiniteExact 64 F}
    (hsame : SameButLocalsClock_g10 s1 s2) (name : MlS) :
    EvalEqN_g10t4 s1 s2 (.var .global name) :=
  congrArg (fun m : HolFiniteMapExact MlS (ValueHOL 64) => m.lookup name) hsame.1

theorem evalN_rfield_g10t4 {F : Type} {s1 s2 : PanSemStateFiniteExact 64 F} {i : Nat}
    {x : ExpHOL 64} (hx : EvalEqN_g10t4 s1 s2 x) : EvalEqN_g10t4 s1 s2 (.rfield i x) := by
  simp only [EvalEqN_g10t4, evalHOLExact, evalListHOLExact, evalListFieldsHOLExact]
  rw [hx]

theorem evalN_rstruct_g10t4 {F : Type} {s1 s2 : PanSemStateFiniteExact 64 F}
    {fs : List (ExpHOL 64)} (hl : ListEqX_g10t4 s1 s2 fs) :
    EvalEqN_g10t4 s1 s2 (.rstruct fs) := by
  simp only [EvalEqN_g10t4, evalHOLExact, evalListHOLExact, evalListFieldsHOLExact]
  rw [hl]

theorem evalN_load_g10t4 {F : Type} {s1 s2 : PanSemStateFiniteExact 64 F}
    (hsame : SameButLocalsClock_g10 s1 s2) {sh : ShapeHOL} {x : ExpHOL 64}
    (hx : EvalEqN_g10t4 s1 s2 x) : EvalEqN_g10t4 s1 s2 (.load sh x) := by
  obtain ⟨_, hst, _, _, hmem, hma, _, _, _, _, _, _⟩ := id hsame
  simp only [EvalEqN_g10t4, evalHOLExact, evalListHOLExact, evalListFieldsHOLExact]
  rw [hx, hst, hma, hmem]

theorem evalN_op_g10t4 {F : Type} {s1 s2 : PanSemStateFiniteExact 64 F} {o : Flapjack.BinOp}
    {args : List (ExpHOL 64)} (hl : ListEqX_g10t4 s1 s2 args) :
    EvalEqN_g10t4 s1 s2 (.op o args) := by
  simp only [EvalEqN_g10t4, evalHOLExact, evalListHOLExact, evalListFieldsHOLExact]
  rw [hl]

theorem evalN_panop_g10t4 {F : Type} {s1 s2 : PanSemStateFiniteExact 64 F}
    {o : Flapjack.PanOp} {args : List (ExpHOL 64)} (hl : ListEqX_g10t4 s1 s2 args) :
    EvalEqN_g10t4 s1 s2 (.panop o args) := by
  simp only [EvalEqN_g10t4, evalHOLExact, evalListHOLExact, evalListFieldsHOLExact]
  rw [hl]

theorem evalN_cmp_g10t4 {F : Type} {s1 s2 : PanSemStateFiniteExact 64 F} {o : Flapjack.Cmp}
    {a b : ExpHOL 64} (ha : EvalEqN_g10t4 s1 s2 a) (hb : EvalEqN_g10t4 s1 s2 b) :
    EvalEqN_g10t4 s1 s2 (.cmp o a b) := by
  simp only [EvalEqN_g10t4, evalHOLExact, evalListHOLExact, evalListFieldsHOLExact]
  rw [ha, hb]

theorem evalN_shift_g10t4 {F : Type} {s1 s2 : PanSemStateFiniteExact 64 F}
    {o : Flapjack.Shift} {a b : ExpHOL 64} (ha : EvalEqN_g10t4 s1 s2 a)
    (hb : EvalEqN_g10t4 s1 s2 b) : EvalEqN_g10t4 s1 s2 (.shift o a b) := by
  simp only [EvalEqN_g10t4, evalHOLExact, evalListHOLExact, evalListFieldsHOLExact]
  rw [ha, hb]

theorem evalListX_nil_g10t4 {F : Type} {s1 s2 : PanSemStateFiniteExact 64 F} :
    ListEqX_g10t4 s1 s2 [] := rfl

theorem evalListX_cons_g10t4 {F : Type} {s1 s2 : PanSemStateFiniteExact 64 F} {e : ExpHOL 64}
    {rest : List (ExpHOL 64)} (h1 : EvalEqN_g10t4 s1 s2 e) (h2 : ListEqX_g10t4 s1 s2 rest) :
    ListEqX_g10t4 s1 s2 (e :: rest) := by
  simp only [ListEqX_g10t4, EvalEqN_g10t4, evalHOLExact, evalListHOLExact, evalListFieldsHOLExact]
  rw [h1, h2]

/-! ### Congruence schemas over all same-but-locals pairs -/

/-- The evaluation congruence for one expression, over every pair of states
that agree off the local slot. -/
def EvalCongP_g10t4 {F : Type} (nm : MlS) (e : ExpHOL 64) : Prop :=
  ∀ (s1 s2 : PanSemStateFiniteExact 64 F),
    SameButLocalsClock_g10 s1 s2 →
    (∀ k, k ≠ nm → s1.locals.lookup k = s2.locals.lookup k) →
    EvalEqN_g10t4 s1 s2 e

/-- The list-evaluation congruence in the finite-evaluator form used by the
`decCall` and `call` equations. -/
def ListCongP_g10t4 {F : Type} (nm : MlS) (args : List (ExpHOL 64)) : Prop :=
  ∀ (s1 s2 : PanSemStateFiniteExact 64 F),
    SameButLocalsClock_g10 s1 s2 →
    (∀ k, k ≠ nm → s1.locals.lookup k = s2.locals.lookup k) →
    evalListHOLFinite s1 (h := fun address => Classical.propDecidable (s1.memaddrs address)) args =
      evalListHOLFinite s2 (h := fun address => Classical.propDecidable (s2.memaddrs address)) args

theorem evalCongP_const_g10t4 {F : Type} {nm : MlS} (c : BitVec 64) :
    EvalCongP_g10t4 (F := F) nm (.const c) := fun _ _ _ _ => rfl

theorem evalCongP_var_local_g10t4 {F : Type} {nm k : MlS} (hk : k ≠ nm) :
    EvalCongP_g10t4 (F := F) nm (.var .local k) := fun _ _ _ hloc => hloc k hk

theorem evalCongP_var_global_g10t4 {F : Type} {nm name : MlS} :
    EvalCongP_g10t4 (F := F) nm (.var .global name) :=
  fun _ _ hsame _ => evalN_var_global_g10t4 hsame name

theorem evalCongP_rfield_g10t4 {F : Type} {nm : MlS} {i : Nat} {x : ExpHOL 64}
    (hx : EvalCongP_g10t4 (F := F) nm x) : EvalCongP_g10t4 (F := F) nm (.rfield i x) :=
  fun s1 s2 hsame hloc => evalN_rfield_g10t4 (hx s1 s2 hsame hloc)

theorem evalCongP_rstruct_g10t4 {F : Type} {nm : MlS} {fs : List (ExpHOL 64)}
    (hl : ListCongP_g10t4 (F := F) nm fs) : EvalCongP_g10t4 (F := F) nm (.rstruct fs) :=
  fun s1 s2 hsame hloc => evalN_rstruct_g10t4 (hl s1 s2 hsame hloc)

theorem evalCongP_load_g10t4 {F : Type} {nm : MlS} {sh : ShapeHOL} {x : ExpHOL 64}
    (hx : EvalCongP_g10t4 (F := F) nm x) : EvalCongP_g10t4 (F := F) nm (.load sh x) :=
  fun s1 s2 hsame hloc => evalN_load_g10t4 hsame (hx s1 s2 hsame hloc)

theorem evalCongP_op_g10t4 {F : Type} {nm : MlS} {o : Flapjack.BinOp} {args : List (ExpHOL 64)}
    (hl : ListCongP_g10t4 (F := F) nm args) : EvalCongP_g10t4 (F := F) nm (.op o args) :=
  fun s1 s2 hsame hloc => evalN_op_g10t4 (hl s1 s2 hsame hloc)

theorem evalCongP_panop_g10t4 {F : Type} {nm : MlS} {o : Flapjack.PanOp}
    {args : List (ExpHOL 64)} (hl : ListCongP_g10t4 (F := F) nm args) :
    EvalCongP_g10t4 (F := F) nm (.panop o args) :=
  fun s1 s2 hsame hloc => evalN_panop_g10t4 (hl s1 s2 hsame hloc)

theorem evalCongP_cmp_g10t4 {F : Type} {nm : MlS} {o : Flapjack.Cmp} {a b : ExpHOL 64}
    (ha : EvalCongP_g10t4 (F := F) nm a) (hb : EvalCongP_g10t4 (F := F) nm b) :
    EvalCongP_g10t4 (F := F) nm (.cmp o a b) :=
  fun s1 s2 hsame hloc => evalN_cmp_g10t4 (ha s1 s2 hsame hloc) (hb s1 s2 hsame hloc)

theorem evalCongP_shift_g10t4 {F : Type} {nm : MlS} {o : Flapjack.Shift} {a b : ExpHOL 64}
    (ha : EvalCongP_g10t4 (F := F) nm a) (hb : EvalCongP_g10t4 (F := F) nm b) :
    EvalCongP_g10t4 (F := F) nm (.shift o a b) :=
  fun s1 s2 hsame hloc => evalN_shift_g10t4 (ha s1 s2 hsame hloc) (hb s1 s2 hsame hloc)

theorem listCongP_nil_g10t4 {F : Type} {nm : MlS} : ListCongP_g10t4 (F := F) nm [] :=
  fun _ _ _ _ => rfl

theorem listCongP_cons_g10t4 {F : Type} {nm : MlS} {e : ExpHOL 64} {rest : List (ExpHOL 64)}
    (h1 : EvalCongP_g10t4 (F := F) nm e) (h2 : ListCongP_g10t4 (F := F) nm rest) :
    ListCongP_g10t4 (F := F) nm (e :: rest) :=
  fun s1 s2 hsame hloc => evalListX_cons_g10t4 (h1 s1 s2 hsame hloc) (h2 s1 s2 hsame hloc)

/-! ### The three-part continuation no-read property -/

/-- Like `ContNoread_g10`, but additionally tracking pointwise locals agreement
off the slot, so the property chains through sequences and calls. -/
def ContNoreadP_g10 {F : Type} (nm : MlS) (cont : ProgHOL 64) : Prop :=
  ∀ (s1 s2 : PanSemStateFiniteExact 64 F),
    SameButLocalsClock_g10 s1 s2 →
    (∀ k, k ≠ nm → s1.locals.lookup k = s2.locals.lookup k) →
    (evaluateHOLFiniteState s1 cont).1 = (evaluateHOLFiniteState s2 cont).1 ∧
    SameButLocalsClock_g10 (evaluateHOLFiniteState s1 cont).2
      (evaluateHOLFiniteState s2 cont).2 ∧
    (∀ k, k ≠ nm → (evaluateHOLFiniteState s1 cont).2.locals.lookup k =
      (evaluateHOLFiniteState s2 cont).2.locals.lookup k)

/-- The three-part property implies the plain two-part one. -/
theorem contNoreadP_to_g10 {F : Type} {nm : MlS} {cont : ProgHOL 64}
    (h : ContNoreadP_g10 (F := F) nm cont) : ContNoread_g10 (F := F) nm cont := by
  intro s1 s2 hsame hloc
  exact ⟨(h s1 s2 hsame hloc).1, (h s1 s2 hsame hloc).2.1⟩

theorem cnp_skip_g10t4 {F : Type} {nm : MlS} : ContNoreadP_g10 (F := F) nm .skip := by
  intro s1 s2 hsame hloc
  simp only [evaluateHOLFiniteState_skip]
  exact ⟨trivial, hsame, hloc⟩

theorem cnp_return_g10t4 {F : Type} {nm : MlS} {e : ExpHOL 64}
    (hv : EvalCongP_g10t4 (F := F) nm e) : ContNoreadP_g10 (F := F) nm (.return e) := by
  intro s1 s2 hsame hloc
  obtain ⟨_, hst, _, _, _, _, _, _, _, _, _, _⟩ := id hsame
  rw [evaluateHOLFiniteState_return s1 e, evaluateHOLFiniteState_return s2 e]
  rw [← hv s1 s2 hsame hloc]
  rcases he : @evalHOLExact 64 F _ s1.toExact
      (fun a => Classical.propDecidable (s1.memaddrs a)) e with _ | v
  · simp only [he]
    exact ⟨trivial, hsame, hloc⟩
  · simp only [he]
    rw [hst]
    by_cases hsz : Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL s2.structs
        (shapeOfHOLExact v) ≤ 32
    · simp only [if_pos hsz]
      exact ⟨trivial, sameButLocalsClock_update_g10 hsame _ _, fun _ _ => rfl⟩
    · simp only [if_neg hsz]
      exact ⟨trivial, hsame, hloc⟩

theorem cnp_assign_local_g10t4 {F : Type} {nm : MlS} {name : MlS} {src : ExpHOL 64}
    (hne : name ≠ nm) (hv : EvalCongP_g10t4 (F := F) nm src) :
    ContNoreadP_g10 (F := F) nm (.assign .local name src) := by
  intro s1 s2 hsame hloc
  rw [evaluateHOLFiniteState_assign s1 .local name src,
    evaluateHOLFiniteState_assign s2 .local name src]
  rw [← hv s1 s2 hsame hloc]
  rcases he : @evalHOLExact 64 F _ s1.toExact
      (fun a => Classical.propDecidable (s1.memaddrs a)) src with _ | v
  · simp only [he]
    exact ⟨trivial, hsame, hloc⟩
  · simp only [he]
    have hval : isValidValueHOLFinite s1 .local name v =
        isValidValueHOLFinite s2 .local name v := by
      simp only [isValidValueHOLFinite, lookupKvarHOLFinite]
      rw [hloc name hne]
    rw [hval]
    by_cases hvalid : isValidValueHOLFinite s2 .local name v = true
    · simp only [if_pos hvalid]
      refine ⟨trivial, sameButLocalsClock_update_g10 hsame
        (s1.locals.update (name, v)) (s2.locals.update (name, v)), ?_⟩
      intro k hk
      by_cases hke : k = name
      · rw [hke]
        simp only [setKvarHOLFinite]
        rw [lookup_setVar_self_g10t4, lookup_setVar_self_g10t4]
      · simp only [setKvarHOLFinite]
        rw [setVar_lookup_ne_g10t4 s1 name k v (Ne.symm hke),
          setVar_lookup_ne_g10t4 s2 name k v (Ne.symm hke)]
        exact hloc k hk
    · simp only [if_neg hvalid]
      exact ⟨trivial, hsame, hloc⟩

theorem cnp_store_g10t4 {F : Type} {nm : MlS} {dst src : ExpHOL 64}
    (ha : EvalCongP_g10t4 (F := F) nm dst) (hv : EvalCongP_g10t4 (F := F) nm src) :
    ContNoreadP_g10 (F := F) nm (.store dst src) := by
  intro s1 s2 hsame hloc
  obtain ⟨hg, hst, hcd, hesh, hmem, hma, hsma, hck, hbe, hffi, hba, hta⟩ := id hsame
  rw [evaluateHOLFiniteState_store s1 dst src, evaluateHOLFiniteState_store s2 dst src]
  rw [← ha s1 s2 hsame hloc]
  rcases hda : @evalHOLExact 64 F _ s1.toExact
      (fun a => Classical.propDecidable (s1.memaddrs a)) dst with _ | dv
  · simp only [hda]
    exact ⟨trivial, hsame, hloc⟩
  · cases dv with
    | val payload =>
        cases payload with
        | word a =>
            rw [← hv s1 s2 hsame hloc]
            rcases hsa : @evalHOLExact 64 F _ s1.toExact
                (fun a => Classical.propDecidable (s1.memaddrs a)) src with _ | v
            · simp only [hsa]
              exact ⟨trivial, hsame, hloc⟩
            · simp only [hsa]
              rw [hma, hmem]
              rcases hps : @panMemStoresHOL 64 _ a (flattenHOL v) s2.memaddrs
                  (fun address => Classical.propDecidable (s2.memaddrs address)) s2.memory with _ | mem'
              · simp only [hps]
                exact ⟨trivial, hsame, hloc⟩
              · simp only [hps]
                exact ⟨trivial, ⟨hg, hst, hcd, hesh, rfl, rfl, hsma, hck, hbe, hffi, hba, hta⟩,
                  hloc⟩
    | rStruct _ => exact ⟨rfl, hsame, hloc⟩
    | nStruct _ _ => exact ⟨rfl, hsame, hloc⟩

theorem cnp_ite_g10t4 {F : Type} {nm : MlS} {condE : ExpHOL 64} {thn els : ProgHOL 64}
    (hc : EvalCongP_g10t4 (F := F) nm condE) (h1 : ContNoreadP_g10 (F := F) nm thn)
    (h2 : ContNoreadP_g10 (F := F) nm els) : ContNoreadP_g10 (F := F) nm (.ite condE thn els) := by
  intro s1 s2 hsame hloc
  rw [evaluateHOLFiniteState_ite s1 condE thn els,
    evaluateHOLFiniteState_ite s2 condE thn els]
  rw [← hc s1 s2 hsame hloc]
  rcases hcd : @evalHOLExact 64 F _ s1.toExact
      (fun a => Classical.propDecidable (s1.memaddrs a)) condE with _ | cv
  · simp only [hcd]
    exact ⟨trivial, hsame, hloc⟩
  · cases cv with
    | val payload =>
        cases payload with
        | word w =>
            simp only []
            by_cases hw : w = 0
            · simp only [if_pos hw]
              exact h2 s1 s2 hsame hloc
            · simp only [if_neg hw]
              exact h1 s1 s2 hsame hloc
    | rStruct _ => exact ⟨rfl, hsame, hloc⟩
    | nStruct _ _ => exact ⟨rfl, hsame, hloc⟩

theorem cnp_seq_g10t4 {F : Type} {nm : MlS} {p1 p2 : ProgHOL 64}
    (h1 : ContNoreadP_g10 (F := F) nm p1) (h2 : ContNoreadP_g10 (F := F) nm p2) :
    ContNoreadP_g10 (F := F) nm (.seq p1 p2) := by
  intro s1 s2 hsame hloc
  obtain ⟨r1, sbl1, hl1⟩ := h1 s1 s2 hsame hloc
  rw [evaluateHOLFiniteState_seq_line780 s1 p1 p2, evaluateHOLFiniteState_seq_line780 s2 p1 p2]
  simp only []
  rw [← r1]
  rcases hr : (evaluateHOLFiniteState s1 p1).1 with _ | r
  · simp only [hr]
    exact h2 (evaluateHOLFiniteState s1 p1).2 (evaluateHOLFiniteState s2 p1).2 sbl1 hl1
  · simp only [hr]
    exact ⟨hr.symm.trans r1, sbl1, hl1⟩

theorem cnp_dec_g10t4 {F : Type} {nm : MlS} {name : MlS} {sh : ShapeHOL} {init : ExpHOL 64}
    {body : ProgHOL 64} (hi : EvalCongP_g10t4 (F := F) nm init)
    (hb : ContNoreadP_g10 (F := F) nm body) :
    ContNoreadP_g10 (F := F) nm (.dec name sh init body) := by
  intro s1 s2 hsame hloc
  rw [evaluateHOLFiniteState_eq_evaluate_def s1 (.dec name sh init body),
    evaluateHOLFiniteState_eq_evaluate_def s2 (.dec name sh init body)]
  simp only []
  rw [← hi s1 s2 hsame hloc]
  rcases he : @evalHOLExact 64 F _ s1.toExact
      (fun a => Classical.propDecidable (s1.memaddrs a)) init with _ | v
  · simp only [he]
    exact ⟨trivial, hsame, hloc⟩
  · simp only [he]
    by_cases hsh : shapeEqHOL sh (shapeOfHOLExact v) = true
    · simp only [hsh, ↓reduceIte]
      have hlocb : ∀ k, k ≠ nm →
          (setVarHOLFinite name v s1).locals.lookup k =
            (setVarHOLFinite name v s2).locals.lookup k := by
        intro k hk
        by_cases hke : k = name
        · rw [hke, lookup_setVar_self_g10t4, lookup_setVar_self_g10t4]
        · rw [setVar_lookup_ne_g10t4 s1 name k v (Ne.symm hke),
            setVar_lookup_ne_g10t4 s2 name k v (Ne.symm hke)]
          exact hloc k hk
      obtain ⟨rb, sblb, hlb⟩ := hb (setVarHOLFinite name v s1) (setVarHOLFinite name v s2)
        (sameButLocalsClock_update_g10 hsame (s1.locals.update (name, v))
          (s2.locals.update (name, v))) hlocb
      rcases hb1 : evaluateHOLFiniteState (setVarHOLFinite name v s1) body with ⟨r1', s1'⟩
      rcases hb2 : evaluateHOLFiniteState (setVarHOLFinite name v s2) body with ⟨r2', s2'⟩
      simp only [hb1, hb2] at hlb sblb rb ⊢
      refine ⟨rb, sameButLocalsClock_update_g10 sblb _ _, ?_⟩
      intro k hk
      by_cases hke : k = name
      · rw [hke, resVarEq_lookup_self_g10t4, resVarEq_lookup_self_g10t4]
        exact hloc name (by intro h; exact hk (by rw [hke]; exact h))
      · rw [resVarEq_lookup_ne_g10t4 _ _ _ hke, resVarEq_lookup_ne_g10t4 _ _ _ hke]
        exact hlb k hk
    · simp only [hsh, ↓reduceIte]
      exact ⟨rfl, hsame, hloc⟩

theorem cnp_decCall_g10t4 {F : Type} {nm : MlS} {name : MlS} {sh : ShapeHOL} {fname : MlS}
    {args : List (ExpHOL 64)} {cont : ProgHOL 64} (hla : ListCongP_g10t4 (F := F) nm args)
    (hc : ContNoreadP_g10 (F := F) nm cont) :
    ContNoreadP_g10 (F := F) nm (.decCall name sh fname args cont) := by
  intro s1 s2 hsame hloc
  obtain ⟨_, _, hcd, _, _, _, _, hck, _, _, _, _⟩ := id hsame
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite s1 name sh fname args cont,
    evaluateHOLFiniteState_decCall_fixClockRewrite s2 name sh fname args cont]
  simp only []
  rw [← hla s1 s2 hsame hloc]
  rcases he1 : evalListHOLFinite s1
      (h := fun address => Classical.propDecidable (s1.memaddrs address)) args with _ | values
  · simp only [he1]
    exact ⟨trivial, hsame, hloc⟩
  · simp only [he1]
    rw [hcd]
    rcases hl : lookupCodeHOLFinite s2.code.lookup fname values with _ | ⟨body, callee, rs⟩
    · simp only [hl]
      exact ⟨trivial, hsame, hloc⟩
    · simp only [hl]
      rw [hck]
      by_cases hz : s2.clock = 0
      · simp only [hz, ↓reduceIte]
        exact ⟨trivial, sameButLocalsClock_update_g10 hsame _ _, fun _ _ => rfl⟩
      · simp only [hz, ↓reduceIte]
        rw [callEntry_eq_of_sameButLocals_g10 hsame]
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s2 callee) body
          with ⟨rB, sB⟩
        simp only [hb]
        cases rB with
        | none => exact ⟨rfl, SameButLocalsClock_g10_refl _, fun _ _ => rfl⟩
        | some r => cases r with
          | «break» => exact ⟨rfl, SameButLocalsClock_g10_refl _, fun _ _ => rfl⟩
          | «continue» => exact ⟨rfl, SameButLocalsClock_g10_refl _, fun _ _ => rfl⟩
          | returned v =>
              by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) sh &&
                  shapeEqHOL (shapeOfHOLExact v) rs) = true
              · simp only [hsh, ↓reduceIte]
                have hlocC : ∀ k, k ≠ nm →
                    (setVarHOLFinite name v {sB with locals := s1.locals}).locals.lookup k =
                      (setVarHOLFinite name v {sB with locals := s2.locals}).locals.lookup k := by
                  intro k hk
                  by_cases hke : k = name
                  · rw [hke, lookup_setVar_self_g10t4, lookup_setVar_self_g10t4]
                  · rw [setVarRes_lookup_ne_g10t4 s1 sB name k v (Ne.symm hke),
                      setVarRes_lookup_ne_g10t4 s2 sB name k v (Ne.symm hke)]
                    exact hloc k hk
                obtain ⟨rC, sblC, hlC⟩ := hc
                  (setVarHOLFinite name v {sB with locals := s1.locals})
                  (setVarHOLFinite name v {sB with locals := s2.locals})
                  (sameButLocalsClock_update_g10 (SameButLocalsClock_g10_refl sB)
                    (s1.locals.update (name, v)) (s2.locals.update (name, v))) hlocC
                rcases hc1 : evaluateHOLFiniteState
                    (setVarHOLFinite name v {sB with locals := s1.locals}) cont with ⟨rC1, u1⟩
                rcases hc2 : evaluateHOLFiniteState
                    (setVarHOLFinite name v {sB with locals := s2.locals}) cont with ⟨rC2, u2⟩
                simp only [hc1, hc2] at hlC sblC rC ⊢
                refine ⟨rC, sameButLocalsClock_update_g10 sblC _ _, ?_⟩
                intro k hk
                by_cases hke : k = name
                · rw [hke, resVarEq_lookup_self_g10t4, resVarEq_lookup_self_g10t4]
                  exact hloc name (by intro h; exact hk (by rw [hke]; exact h))
                · rw [resVarEq_lookup_ne_g10t4 _ _ _ hke, resVarEq_lookup_ne_g10t4 _ _ _ hke]
                  exact hlC k hk
              · simp only [hsh, ↓reduceIte]
                exact ⟨rfl, SameButLocalsClock_g10_refl _, fun _ _ => rfl⟩
          | exception id v => exact ⟨rfl, SameButLocalsClock_g10_refl _, fun _ _ => rfl⟩
          | error => exact ⟨rfl, SameButLocalsClock_g10_refl _, fun _ _ => rfl⟩
          | timeOut => exact ⟨rfl, SameButLocalsClock_g10_refl _, fun _ _ => rfl⟩
          | finalFfi fv => exact ⟨rfl, SameButLocalsClock_g10_refl _, fun _ _ => rfl⟩

theorem cnp_call_g10t4 {F : Type} {nm : MlS} {fname : MlS} {args : List (ExpHOL 64)}
    (hla : ListCongP_g10t4 (F := F) nm args) :
    ContNoreadP_g10 (F := F) nm (.call (some (none, none)) fname args) := by
  intro s1 s2 hsame hloc
  obtain ⟨_, _, hcd, _, _, _, _, hck, _, _, _, _⟩ := id hsame
  rw [evaluateHOLFiniteState_call s1 (some (none, none)) fname args,
    evaluateHOLFiniteState_call s2 (some (none, none)) fname args]
  simp only []
  rw [← hla s1 s2 hsame hloc]
  rcases he1 : evalListHOLFinite s1
      (h := fun address => Classical.propDecidable (s1.memaddrs address)) args with _ | values
  · simp only [he1]
    exact ⟨trivial, hsame, hloc⟩
  · simp only [he1]
    rw [hcd]
    rcases hl : lookupCodeHOLFinite s2.code.lookup fname values with _ | ⟨body, callee, rs⟩
    · simp only [hl]
      exact ⟨trivial, hsame, hloc⟩
    · simp only [hl]
      rw [hck]
      by_cases hz : s2.clock = 0
      · simp only [hz, ↓reduceIte]
        exact ⟨trivial, sameButLocalsClock_update_g10 hsame _ _, fun _ _ => rfl⟩
      · simp only [hz, ↓reduceIte]
        rw [callEntry_eq_of_sameButLocals_g10 hsame]
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s2 callee) body
          with ⟨rB, stB⟩
        cases rB with
        | none => exact ⟨rfl, SameButLocalsClock_g10_refl _, fun _ _ => rfl⟩
        | some r => cases r with
          | «break» => exact ⟨rfl, SameButLocalsClock_g10_refl _, fun _ _ => rfl⟩
          | «continue» => exact ⟨rfl, SameButLocalsClock_g10_refl _, fun _ _ => rfl⟩
          | returned v =>
              by_cases hsh : shapeEqHOL (shapeOfHOLExact v) rs = true
              · simp only [hsh, ↓reduceIte]
                exact ⟨trivial, sameButLocalsClock_update_g10 (SameButLocalsClock_g10_refl stB)
                  s1.locals s2.locals, fun k hk => hloc k hk⟩
              · simp only [hsh, ↓reduceIte]
                exact ⟨rfl, SameButLocalsClock_g10_refl _, fun _ _ => rfl⟩
          | exception id v => exact ⟨rfl, SameButLocalsClock_g10_refl _, fun _ _ => rfl⟩
          | error => exact ⟨rfl, SameButLocalsClock_g10_refl _, fun _ _ => rfl⟩
          | timeOut => exact ⟨rfl, SameButLocalsClock_g10_refl _, fun _ _ => rfl⟩
          | finalFfi fv => exact ⟨rfl, SameButLocalsClock_g10_refl _, fun _ _ => rfl⟩

theorem cnp_call_assign_local_g10t4 {F : Type} {nm : MlS} {name fname : MlS}
    {args : List (ExpHOL 64)} (hne : name ≠ nm) (hla : ListCongP_g10t4 (F := F) nm args) :
    ContNoreadP_g10 (F := F) nm (.call (some (some (.local, name), none)) fname args) := by
  intro s1 s2 hsame hloc
  obtain ⟨_, _, hcd, _, _, _, _, hck, _, _, _, _⟩ := id hsame
  rw [evaluateHOLFiniteState_call s1 (some (some (.local, name), none)) fname args,
    evaluateHOLFiniteState_call s2 (some (some (.local, name), none)) fname args]
  simp only []
  rw [← hla s1 s2 hsame hloc]
  rcases he1 : evalListHOLFinite s1
      (h := fun address => Classical.propDecidable (s1.memaddrs address)) args with _ | values
  · simp only [he1]
    exact ⟨trivial, hsame, hloc⟩
  · simp only [he1]
    rw [hcd]
    rcases hl : lookupCodeHOLFinite s2.code.lookup fname values with _ | ⟨body, callee, rs⟩
    · simp only [hl]
      exact ⟨trivial, hsame, hloc⟩
    · simp only [hl]
      rw [hck]
      by_cases hz : s2.clock = 0
      · simp only [hz, ↓reduceIte]
        exact ⟨trivial, sameButLocalsClock_update_g10 hsame _ _, fun _ _ => rfl⟩
      · simp only [hz, ↓reduceIte]
        rw [callEntry_eq_of_sameButLocals_g10 hsame]
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s2 callee) body
          with ⟨rB, stB⟩
        cases rB with
        | none => exact ⟨rfl, SameButLocalsClock_g10_refl _, fun _ _ => rfl⟩
        | some r => cases r with
          | «break» => exact ⟨rfl, SameButLocalsClock_g10_refl _, fun _ _ => rfl⟩
          | «continue» => exact ⟨rfl, SameButLocalsClock_g10_refl _, fun _ _ => rfl⟩
          | returned v =>
              by_cases hsh : shapeEqHOL (shapeOfHOLExact v) rs = true
              · simp only [hsh, ↓reduceIte]
                have hval : isValidValueHOLExact s1.toExact .local name v =
                    isValidValueHOLExact s2.toExact .local name v := by
                  simp only [isValidValueHOLExact, lookupKvarHOLExact]
                  rw [hloc name hne]
                rw [hval]
                by_cases hvalid : isValidValueHOLExact s2.toExact .local name v = true
                · simp only [if_pos hvalid]
                  refine ⟨trivial, sameButLocalsClock_update_g10 (SameButLocalsClock_g10_refl stB)
                    (s1.locals.update (name, v)) (s2.locals.update (name, v)), ?_⟩
                  intro k hk
                  by_cases hke : k = name
                  · rw [hke]
                    simp only [setKvarHOLFinite]
                    rw [lookup_setVar_self_g10t4, lookup_setVar_self_g10t4]
                  · simp only [setKvarHOLFinite]
                    rw [setVarRes_lookup_ne_g10t4 s1 stB name k v (Ne.symm hke),
                      setVarRes_lookup_ne_g10t4 s2 stB name k v (Ne.symm hke)]
                    exact hloc k hk
                · simp only [if_neg hvalid]
                  exact ⟨trivial, SameButLocalsClock_g10_refl _, fun _ _ => trivial⟩
              · simp only [hsh, ↓reduceIte]
                exact ⟨rfl, SameButLocalsClock_g10_refl _, fun _ _ => rfl⟩
          | exception id v => exact ⟨rfl, SameButLocalsClock_g10_refl _, fun _ _ => rfl⟩
          | error => exact ⟨rfl, SameButLocalsClock_g10_refl _, fun _ _ => rfl⟩
          | timeOut => exact ⟨rfl, SameButLocalsClock_g10_refl _, fun _ _ => rfl⟩
          | finalFfi fv => exact ⟨rfl, SameButLocalsClock_g10_refl _, fun _ _ => rfl⟩
