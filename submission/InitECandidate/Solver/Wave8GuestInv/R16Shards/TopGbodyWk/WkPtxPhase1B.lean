import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase1A

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

open private wk_alloc_local rt_alloc_local ro_u256_fits_word ro_u256_lt
  ro_u256_add_carry ro_is_valid_delegation
  wsEnv_of_worldOK_local heapByteEff_of_m23_bre_local wk_calculate_blob_gas_price_local
  lookup_calculate_blob_gas_price_local lookup_taylor_exponential_local
  taylor_exponential_wsSafe_local lookup_check_transaction checkTxBufs
  validBufList_checkTxBufs safeStepGlobals_checkTx ptxWorldStep_strong_with_locals_right
  acctMut_sub_ptx acctMut_globals_sub ptxKeep_not_acctMut_global
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkBlockTxProcess

/-! # Phase 1 Relational Stepping Combinators & Ownership Survival (`WkPtxPhase1B`) -/

/-! ## 1. `PtxAfterPhase1` & `SenderTxOwned` -/

def SenderTxOwned {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ S Nd, WorldTypedWith s S Nd ∧ TxAccessListAt s S Nd (locN s "tx") ∧
    IvlsDisj [(locN s "sender", 24)] (worldOwned s S Nd)

def PtxAfterPhase1 {F : Type} (entry s : PanSemStateFiniteExact 64 F) : Prop :=
  PtxRelBase true entry s ∧
  R13Shards.PtxValidatedStrong s ∧
  globN s "bn_expw" = globN entry "bn_expw" ∧
  globN s "bn_gamma" = globN entry "bn_gamma" ∧
  s.locals.lookup (ofString "tx") = entry.locals.lookup (ofString "tx") ∧
  s.locals.lookup (ofString "index") = entry.locals.lookup (ofString "index") ∧
  SenderTxOwned s

theorem senderTxOwned_with_locals {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (ck : Nat)
    (htx : L.lookup (ofString "tx") = s.locals.lookup (ofString "tx"))
    (hsnd : L.lookup (ofString "sender") = s.locals.lookup (ofString "sender"))
    (h : SenderTxOwned s) :
    SenderTxOwned { s with locals := L, clock := ck } := by
  obtain ⟨S, Nd, hW, hT, hD⟩ := h
  have htxN : locN { s with locals := L, clock := ck } "tx" = locN s "tx" := by
    simp only [locN, htx]
  have hsndN : locN { s with locals := L, clock := ck } "sender" = locN s "sender" := by
    simp only [locN, hsnd]
  refine ⟨S, Nd, (R13Shards.worldTypedWith_with_locals s L ck S Nd).mpr hW, ?_, ?_⟩
  · rw [htxN]
    exact PtxP1.txAccessListAt_with_locals s L ck hT
  · rw [hsndN]
    exact hD

theorem senderTxOwned_setVar {F : Type}
    {s : PanSemStateFiniteExact 64 F} {nm : MlS} {v : ValueHOL 64}
    (hntx : nm ≠ ofString "tx") (hnsnd : nm ≠ ofString "sender")
    (h : SenderTxOwned s) :
    SenderTxOwned (setVarHOLFinite nm v s) := by
  refine senderTxOwned_with_locals s (s.locals.update (nm, v)) s.clock ?_ ?_ h
  · simp [HolFiniteMapExact.update, FUPDATE, hntx]
  · simp [HolFiniteMapExact.update, FUPDATE, hnsnd]

def SenderAllocatedOwned {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  PtxP1.SenderAllocated s ∧
  ∃ S Nd, WorldTypedWith s S Nd ∧ TxAccessListOK s S Nd ∧
    IvlsDisj [(locN s "sender", 24)] (worldOwned s S Nd) ∧
    Disj (locN s "tx", 384) (locN s "sender", 24) ∧
    (0 < memW s (locN s "tx" + 216) →
      Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) (locN s "sender", 24))

theorem senderTxOwned_of_senderAllocatedOwned {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : SenderAllocatedOwned s) :
    SenderTxOwned s := by
  obtain ⟨_, S, Nd, hW, hT, hOw, _, _⟩ := h
  exact ⟨S, Nd, hW, hT, hOw⟩

theorem senderTxOwned_after_recover {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)}
    (hP : SenderAllocatedOwned s)
    (hs : WorldStep
      (fun _ => [(locN s "sender", 20), bufferRegion s ("keccak_pad", 136),
        bufferRegion s ("keccak_st", 200), bufferRegion s ("u256_ws", 640)])
      ["heap_ptr"] stdKeep NoExtra s r post) :
    SenderTxOwned { post with locals := s.locals } := by
  obtain ⟨⟨hR, hSnd, _⟩, S, Nd, hW, hT, hOw, hTx, hRecs⟩ := hP
  have hTyped : ∀ j ∈ worldTypedIvls s S Nd, Disj (locN s "sender", 24) j :=
    fun j hj => hOw _ (by simp) j (R13Shards.worldTypedIvls_sub_worldOwned hj)
  have hA := hR.1.1.1
  have hin20 : Inside (locN s "sender", 20) (locN s "sender") (locN s "sender" + 24) := ⟨le_rfl, by omega⟩
  let Rs : List Ivl := [(locN s "sender", 20), bufferRegion s ("keccak_pad", 136),
    bufferRegion s ("keccak_st", 200), bufferRegion s ("u256_ws", 640)]
  have hRT : IvlsDisj Rs (worldTypedIvls s S Nd) := by
    intro i hi j hj
    simp only [Rs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact R13Shards.disj_of_inside_left hin20 (hTyped j hj)
    · exact bufferRegion_disj_le hW ("keccak_pad", 136) (by decide) (by decide) 136 le_rfl j hj
    · exact bufferRegion_disj_le hW ("keccak_st", 200) (by decide) (by decide) 200 le_rfl j hj
    · exact bufferRegion_disj_le hW ("u256_ws", 640) (by decide) (by decide) 640 le_rfl j hj
  have hR0 : ∀ i ∈ Rs, i.2 = 0 → i.1 % 8 = 0 := by
    intro i hi hz
    simp only [Rs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · simp at hz
    · dsimp [bufferRegion] at hz ⊢; split at hz <;> [omega; simp_all]
    · dsimp [bufferRegion] at hz ⊢; split at hz <;> [omega; simp_all]
    · dsimp [bufferRegion] at hz ⊢; split at hz <;> [omega; simp_all]
  obtain ⟨S', Nd', _, hW', hog, hfr, _⟩ := hs.2.2.2.2 S Nd hW hRT
  have hT' : TxAccessListOK { post with locals := s.locals } S' Nd' := by
    refine PtxP1.txAccessListOK_survives_step hA hs.1.1 hs.2.1 hW hR0 hog hfr hT ?_ ?_ rfl
    · intro i hi
      simp only [Rs, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact R13Shards.disj_of_inside_right hin20 hTx
      · exact PtxP1.heap_ivl_disj_bufferRegion_le (fun j hj => hT.2.1 _ (by simp) j hj) ("keccak_pad", 136) (by decide) 136 le_rfl
      · exact PtxP1.heap_ivl_disj_bufferRegion_le (fun j hj => hT.2.1 _ (by simp) j hj) ("keccak_st", 200) (by decide) 200 le_rfl
      · exact PtxP1.heap_ivl_disj_bufferRegion_le (fun j hj => hT.2.1 _ (by simp) j hj) ("u256_ws", 640) (by decide) 640 le_rfl
    · intro hn i hi
      simp only [Rs, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact R13Shards.disj_of_inside_right hin20 (hRecs hn)
      · exact PtxP1.heap_ivl_disj_bufferRegion_le (fun j hj => (hT.2.2 hn).2 _ (by simp) j hj) ("keccak_pad", 136) (by decide) 136 le_rfl
      · exact PtxP1.heap_ivl_disj_bufferRegion_le (fun j hj => (hT.2.2 hn).2 _ (by simp) j hj) ("keccak_st", 200) (by decide) 200 le_rfl
      · exact PtxP1.heap_ivl_disj_bufferRegion_le (fun j hj => (hT.2.2 hn).2 _ (by simp) j hj) ("u256_ws", 640) (by decide) 640 le_rfl
  have hsnd_ow' : IvlsDisj [(locN s "sender", 24)] (worldOwned post S' Nd') := by
    intro i hi o ho
    simp only [List.mem_singleton] at hi; subst hi
    rcases hog o ho with rfl | ⟨j, hj, hin_o⟩ | hin_fresh
    · simp [Disj]
    · exact R13Shards.disj_of_inside_right hin_o (hOw _ (by simp) j hj)
    · exact Or.inr (Or.inr (Or.inl (by
        have := hSnd.1.2; unfold Inside at hin_fresh; omega)))
  exact ⟨S', Nd', (R13Shards.worldTypedWith_with_locals post s.locals post.clock S' Nd').mpr hW', hT', hsnd_ow'⟩

theorem senderTxOwned_scratchStep {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {B : BufList}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (hB : ValidBufList B)
    (hAs : ArenaReady s)
    (hsnd_in : Inside (locN s "sender", 24) sourceBase (globN s "heap_ptr"))
    (hOwn : SenderTxOwned s)
    (hstep : WorldStep (bufRegions B) gw keep Q s r post) :
    SenderTxOwned { post with locals := s.locals } := by
  obtain ⟨S, Nd, hW, hT, hD⟩ := hOwn
  have hBD : IvlsDisj (bufRegions B s) (worldTypedIvls s S Nd) := validBufList_disj hB hW
  obtain ⟨S', Nd', _, hW', hog, hfr, _⟩ := hstep.2.2.2.2 S Nd hW hBD
  have hR0 : ∀ i ∈ bufRegions B s, i.2 = 0 → i.1 % 8 = 0 :=
    ptx_bufRegions_zero_aligned hB hW.2.2.1
  have htx_B : ∀ r ∈ bufRegions B s, Disj (locN s "tx", 384) r :=
    ptx_disj_bufRegions_of_disj_worldOwned hB (fun j hj => hT.2.1 _ (by simp) j hj)
  have hrecs_B : 0 < memW s (locN s "tx" + 216) →
      ∀ r ∈ bufRegions B s, Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) r :=
    fun hn => ptx_disj_bufRegions_of_disj_worldOwned hB (fun j hj => (hT.2.2 hn).2 _ (by simp) j hj)
  have hT' : TxAccessListOK { post with locals := s.locals } S' Nd' :=
    PtxP1.txAccessListOK_survives_step hAs hstep.1.1 hstep.2.1 hW hR0 hog hfr hT htx_B hrecs_B rfl
  have hsnd_B : ∀ r ∈ bufRegions B s, Disj (locN s "sender", 24) r :=
    ptx_disj_bufRegions_of_disj_worldOwned hB (fun j hj => hD _ (by simp) j hj)
  have hD' : IvlsDisj [(locN s "sender", 24)] (worldOwned post S' Nd') := by
    intro i hi o ho
    simp only [List.mem_singleton] at hi; subst hi
    rcases hog o ho with rfl | ⟨j, hj, hin_o⟩ | hin_fresh
    · simp [Disj]
    · exact R13Shards.disj_of_inside_right hin_o (hD _ (by simp) j hj)
    · exact Or.inr (Or.inr (Or.inl (by have := hsnd_in.2; unfold Inside at hin_fresh; omega)))
  exact ⟨S', Nd', (R13Shards.worldTypedWith_with_locals post s.locals post.clock S' Nd').mpr hW', hT', hD'⟩

/-! ## 2. Relational Step Combinators for `PtxRelRunStrong` -/

theorem ptxRelRunStrong_skip {F : Type}
    {entry s : PanSemStateFiniteExact 64 F} {tail : ProgHOL 64}
    (htail : PtxRelRunStrong entry tail s) :
    PtxRelRunStrong entry (.seq .skip tail) s := by
  intro hres
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_skip] at hres ⊢
  exact htail hres

theorem ptxRelRunStrong_dec {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    (name : MlS) (sh : ShapeHOL) (e : ExpHOL 64) (tail : ProgHOL 64)
    (htail : ∀ v : ValueHOL 64,
      evalAt s e = some v → shapeOfHOLExact v = sh →
      PtxRelRunStrong entry tail (setVarHOLFinite name v s)) :
    PtxRelRunStrong entry (.dec name sh e tail) s := by
  intro hres
  rw [evaluateHOLFiniteState_dec_total] at hres ⊢
  dsimp only at hres ⊢
  rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | v
  · simp [hev] at hres; exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · simp only [hev] at hres ⊢
    by_cases hsh : shapeEqHOL sh (shapeOfHOLExact v) = true
    · simp only [hsh, ↓reduceIte] at hres ⊢
      have hsh_eq : shapeOfHOLExact v = sh :=
        (shapeEqHOL_eq_true sh (shapeOfHOLExact v)).1 hsh |>.symm
      have hev_at : evalAt s e = some v := hev
      have hmid := htail v hev_at hsh_eq hres
      exact ptxWorldStep_strong_with_locals_right
        (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState (setVarHOLFinite name v s) tail).2.locals
          (name, s.locals.lookup name))
        (evaluateHOLFiniteState (setVarHOLFinite name v s) tail).2.clock hmid
    · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hres
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

theorem ptxRelRunStrong_decCall_ro {F : Type}
    {entry s : PanSemStateFiniteExact 64 F} {txDone : Bool}
    (hbase : PtxRelBase txDone entry s)
    (hc : s.code = originalRuntimeCode)
    (name : MlS) (sh : ShapeHOL) (fname : MlS) (args : List (ExpHOL 64)) (tail : ProgHOL 64)
    (hro : ReadOnlyFn fname)
    (htail : ∀ (vs : List (ValueHOL 64)) (body : ProgHOL 64)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
      (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vs →
      lookupCodeHOLFinite s.code.lookup fname vs = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      shapeOfHOLExact v = sh →
      post = { callEntryStateHOLFinite s callee with locals := post.locals, clock := post.clock } →
      PtxRelRunStrong entry tail (setVarHOLFinite name v { post with locals := s.locals })) :
    PtxRelRunStrong entry (.decCall name sh fname args tail) s := by
  intro hres
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hres ⊢
  rcases ha : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [evalListHOLFinite, ha] at hres
    exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · simp only [evalListHOLFinite, ha] at hres ⊢
    have ha_fin : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vs := by
      simpa [evalListHOLFinite] using ha
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body, callee, ret⟩
    · simp only [hl] at hres
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
    · simp only [hl] at hres ⊢
      by_cases hcz : s.clock = 0
      · simp only [hcz, ↓reduceIte] at hres
        exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
      · simp only [hcz, ↓reduceIte] at hres ⊢
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rb, post⟩
        have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (rb, post) := hb
        simp only [hb] at hres ⊢
        cases rb with
        | none => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | some cr =>
          cases cr with
          | timeOut | error | «break» | «continue» | finalFfi _ =>
            exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | exception eid ev =>
            dsimp only at hres ⊢
            have hspec := FunSpec.at_lookup hro s hc vs body callee ret hl
              (guestInv_callEntry s callee hbase.world.1.1) (by rw [hb']; simp)
            have hro_eq : post = { callEntryStateHOLFinite s callee with locals := post.locals, clock := post.clock } := by
              have h1 := hspec (by rw [hb']; exact hres)
              simpa [hb'] using h1
            have hpost_s : post.emptyLocalsHOLFinite = { s with locals := .empty, clock := post.clock } := by
              rw [hro_eq]; rfl
            rw [hpost_s]
            have hid_step : WorldStep (bufRegions []) [] stdKeep NoExtra s (some (.exception eid ev)) s := by
              refine ⟨hbase.world.1, le_rfl, fun _ _ => rfl, fun _ _ _ _ _ _ => rfl, ?_⟩
              intro S0 Nd0 hWT0 _
              exact ⟨S0, Nd0, fun _ ht => ht, hWT0,
                fun o ho => Or.inr (Or.inl ⟨o, ho, le_rfl, le_rfl⟩),
                fun _ _ _ => rfl, trivial⟩
            have hex := ptxRelBase_exception_worldStep hbase
              (by intro p hp; cases hp) (by intro p hp; cases hp) (by intro g hg; cases hg)
              ptxKeepSub_stdKeep hid_step
            exact ptxWorldStep_strong_with_locals_right .empty post.clock hex
          | returned v =>
            dsimp only at hres ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) sh && shapeEqHOL (shapeOfHOLExact v) ret) = true
            · simp only [hsh, ↓reduceIte] at hres ⊢
              have hsh1 : shapeEqHOL (shapeOfHOLExact v) sh = true := ((Bool.and_eq_true _ _).mp hsh).1
              have hsh_eq : shapeOfHOLExact v = sh := (shapeEqHOL_eq_true _ _).1 hsh1
              have hspec := FunSpec.at_lookup hro s hc vs body callee ret hl
                (guestInv_callEntry s callee hbase.world.1.1) (by rw [hb']; simp)
              have hro_eq : post = { callEntryStateHOLFinite s callee with locals := post.locals, clock := post.clock } := by
                have h1 := hspec (by rw [hb']; exact Or.inl ⟨v, rfl⟩)
                simpa [hb'] using h1
              have hmid := htail vs body callee ret v post ha_fin hl hb' hsh_eq hro_eq hres
              exact ptxWorldStep_strong_with_locals_right
                (HolFiniteMapExact.resVarEq
                  (evaluateHOLFiniteState (setVarHOLFinite name v { post with locals := s.locals }) tail).2.locals
                  (name, s.locals.lookup name))
                (evaluateHOLFiniteState (setVarHOLFinite name v { post with locals := s.locals }) tail).2.clock hmid
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hres
              exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

theorem ptxRelRunStrong_callLocal_ro {F : Type}
    {entry s : PanSemStateFiniteExact 64 F} {txDone : Bool}
    (hbase : PtxRelBase txDone entry s)
    (hc : s.code = originalRuntimeCode)
    (name : MlS) (fname : MlS) (args : List (ExpHOL 64)) (tail : ProgHOL 64)
    (hro : ReadOnlyFn fname)
    (htail : ∀ (vs : List (ValueHOL 64)) (body : ProgHOL 64)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
      (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vs →
      lookupCodeHOLFinite s.code.lookup fname vs = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      shapeOfHOLExact v = ret →
      post = { callEntryStateHOLFinite s callee with locals := post.locals, clock := post.clock } →
      PtxRelRunStrong entry tail (setKvarHOLFinite .local name v { post with locals := s.locals })) :
    PtxRelRunStrong entry (.seq (.call (some (some (.local, name), none)) fname args) tail) s := by
  intro hres
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hres ⊢
  rcases ha : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [evalListHOLFinite, ha] at hres
    exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · simp only [evalListHOLFinite, ha] at hres ⊢
    have ha_fin : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vs := by
      simpa [evalListHOLFinite] using ha
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body, callee, ret⟩
    · simp only [hl] at hres
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
    · simp only [hl] at hres ⊢
      by_cases hcz : s.clock = 0
      · simp only [hcz, ↓reduceIte] at hres
        exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
      · simp only [hcz, ↓reduceIte] at hres ⊢
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rb, post⟩
        have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (rb, post) := hb
        simp only [hb] at hres ⊢
        cases rb with
        | none => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | some cr =>
          cases cr with
          | timeOut | error | «break» | «continue» | finalFfi _ =>
            exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | exception eid ev =>
            dsimp only at hres ⊢
            have hspec := FunSpec.at_lookup hro s hc vs body callee ret hl
              (guestInv_callEntry s callee hbase.world.1.1) (by rw [hb']; simp)
            have hro_eq : post = { callEntryStateHOLFinite s callee with locals := post.locals, clock := post.clock } := by
              have h1 := hspec (by rw [hb']; exact hres)
              simpa [hb'] using h1
            have hpost_s : post.emptyLocalsHOLFinite = { s with locals := .empty, clock := post.clock } := by
              rw [hro_eq]; rfl
            rw [hpost_s]
            have hid_step : WorldStep (bufRegions []) [] stdKeep NoExtra s (some (.exception eid ev)) s := by
              refine ⟨hbase.world.1, le_rfl, fun _ _ => rfl, fun _ _ _ _ _ _ => rfl, ?_⟩
              intro S0 Nd0 hWT0 _
              exact ⟨S0, Nd0, fun _ ht => ht, hWT0,
                fun o ho => Or.inr (Or.inl ⟨o, ho, le_rfl, le_rfl⟩),
                fun _ _ _ => rfl, trivial⟩
            have hex := ptxRelBase_exception_worldStep hbase
              (by intro p hp; cases hp) (by intro p hp; cases hp) (by intro g hg; cases hg)
              ptxKeepSub_stdKeep hid_step
            exact ptxWorldStep_strong_with_locals_right .empty post.clock hex
          | returned v =>
            dsimp only at hres ⊢
            by_cases hsh : shapeEqHOL (shapeOfHOLExact v) ret = true
            · simp only [hsh, ↓reduceIte] at hres ⊢
              by_cases hval : isValidValueHOLExact s.toExact .local name v = true
              · simp only [hval, ↓reduceIte] at hres ⊢
                have hsh_eq : shapeOfHOLExact v = ret := (shapeEqHOL_eq_true _ _).1 hsh
                have hspec := FunSpec.at_lookup hro s hc vs body callee ret hl
                  (guestInv_callEntry s callee hbase.world.1.1) (by rw [hb']; simp)
                have hro_eq : post = { callEntryStateHOLFinite s callee with locals := post.locals, clock := post.clock } := by
                  have h1 := hspec (by rw [hb']; exact Or.inl ⟨v, rfl⟩)
                  simpa [hb'] using h1
                exact htail vs body callee ret v post ha_fin hl hb' hsh_eq hro_eq hres
              · simp only [hval, Bool.false_eq_true, ↓reduceIte] at hres
                exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hres
              exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

theorem ptxRelRunStrong_decCall_scBo {F : Type}
    {entry s : PanSemStateFiniteExact 64 F} {txDone : Bool}
    {B : BufList} {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    (hbase : PtxRelBase txDone entry s)
    (hc : s.code = originalRuntimeCode)
    (hB : ValidBufList B)
    (hBsub : ∀ p ∈ B, p ∈ ptxBufs ∧ p.1 ∉ ptxGlobals)
    (hgw : ∀ g ∈ gw, g ∈ ptxGlobals)
    (hfmp_gw : ofString "frame_mem_ptr" ∉ gw.map ofString)
    (hbo_gw : ofString "bo" ∉ gw.map ofString)
    (hkeep : PtxKeepSub keep)
    (hbo_keep : ("bo", [24, 32, 40, 56, 64, 72, 80]) ∈ keep ∨
      ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) ∈ keep)
    (name : MlS) (sh : ShapeHOL) (fname : MlS) (args : List (ExpHOL 64)) (tail : ProgHOL 64)
    (hwk : WorldKeepsScBo WorldOK (bufRegions B) gw keep Q fname)
    (htail : ∀ (vs : List (ValueHOL 64)) (body : ProgHOL 64)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
      (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vs →
      lookupCodeHOLFinite s.code.lookup fname vs = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      shapeOfHOLExact v = sh →
      WorldStep (bufRegions B) gw keep Q (callEntryStateHOLFinite s callee) (some (.returned v)) post →
      PtxRelBase txDone entry (setVarHOLFinite name v { post with locals := s.locals }) →
      (post.code = originalRuntimeCode) →
      PtxRelRunStrong entry tail (setVarHOLFinite name v { post with locals := s.locals })) :
    PtxRelRunStrong entry (.decCall name sh fname args tail) s := by
  intro hres
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hres ⊢
  rcases ha : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [evalListHOLFinite, ha] at hres
    exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · simp only [evalListHOLFinite, ha] at hres ⊢
    have ha_fin : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vs := by
      simpa [evalListHOLFinite] using ha
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body, callee, ret⟩
    · simp only [hl] at hres
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
    · simp only [hl] at hres ⊢
      by_cases hcz : s.clock = 0
      · simp only [hcz, ↓reduceIte] at hres
        exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
      · simp only [hcz, ↓reduceIte] at hres ⊢
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).1
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rb, post⟩
        have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (rb, post) := hb
        rw [hb] at hmeta
        simp only [hb] at hres ⊢
        cases rb with
        | none => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | some cr =>
          cases cr with
          | timeOut | error | «break» | «continue» | finalFfi _ =>
            exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | exception eid ev =>
            dsimp only at hres ⊢
            have hspec := hwk.at_lookup s hc vs body callee ret hl
              (localsFree_worldOK s callee (s.clock - 1) hbase.world) (by rw [hb']; simp)
            rw [hb'] at hspec
            have hstep_cal := (hspec hres).1.1
            have hstep_s : WorldStep (bufRegions B) gw keep NoExtra s (some (.exception eid ev)) post :=
              R13Shards.worldStep_with_locals hstep_cal s.locals s.clock
            have hex := ptxRelBase_exception_worldStep hbase hB hBsub hgw hkeep hstep_s
            exact ptxWorldStep_strong_with_locals_right .empty post.clock hex
          | returned v =>
            dsimp only at hres ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) sh && shapeEqHOL (shapeOfHOLExact v) ret) = true
            · simp only [hsh, ↓reduceIte] at hres ⊢
              have hsh1 : shapeEqHOL (shapeOfHOLExact v) sh = true := ((Bool.and_eq_true _ _).mp hsh).1
              have hsh_eq : shapeOfHOLExact v = sh := (shapeEqHOL_eq_true _ _).1 hsh1
              have hspec := hwk.at_lookup s hc vs body callee ret hl
                (localsFree_worldOK s callee (s.clock - 1) hbase.world) (by rw [hb']; simp)
              rw [hb'] at hspec
              have hscbo := hspec (Or.inl ⟨v, rfl⟩)
              have hstep_s : WorldStep (bufRegions B) gw keep NoExtra s (some (.returned v)) post :=
                R13Shards.worldStep_with_locals hscbo.1.1 s.locals s.clock
              have hfmp_eq : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" :=
                globN_eq_of_lookup (hstep_s.2.2.1 _ hfmp_gw)
              have hbase_post : PtxRelBase txDone entry post :=
                ptxRelBase_step_of_blockOutUnhit hbase hB hBsub hgw hkeep hbo_gw hbo_keep
                  hstep_s hscbo.1.2 (by omega) (hscbo.2 (Or.inr (Or.inr (Or.inr ⟨v, rfl⟩))))
              have hbase_res : PtxRelBase txDone entry (setVarHOLFinite name v { post with locals := s.locals }) :=
                ptxRelBase_with_locals hbase_post (s.locals.update (name, v)) post.clock
              have hmid := htail vs body callee ret v post ha_fin hl hb' hsh_eq hscbo.1.1 hbase_res
                (hmeta.trans hc) hres
              exact ptxWorldStep_strong_with_locals_right
                (HolFiniteMapExact.resVarEq
                  (evaluateHOLFiniteState (setVarHOLFinite name v { post with locals := s.locals }) tail).2.locals
                  (name, s.locals.lookup name))
                (evaluateHOLFiniteState (setVarHOLFinite name v { post with locals := s.locals }) tail).2.clock hmid
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hres
              exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

theorem ptxRelRunStrong_call0_scBo {F : Type}
    {entry s : PanSemStateFiniteExact 64 F} {txDone : Bool}
    {B : BufList} {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    (hbase : PtxRelBase txDone entry s)
    (hc : s.code = originalRuntimeCode)
    (hB : ValidBufList B)
    (hBsub : ∀ p ∈ B, p ∈ ptxBufs ∧ p.1 ∉ ptxGlobals)
    (hgw : ∀ g ∈ gw, g ∈ ptxGlobals)
    (hfmp_gw : ofString "frame_mem_ptr" ∉ gw.map ofString)
    (hbo_gw : ofString "bo" ∉ gw.map ofString)
    (hkeep : PtxKeepSub keep)
    (hbo_keep : ("bo", [24, 32, 40, 56, 64, 72, 80]) ∈ keep ∨
      ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) ∈ keep)
    (fname : MlS) (args : List (ExpHOL 64)) (tail : ProgHOL 64)
    (hwk : WorldKeepsScBo WorldOK (bufRegions B) gw keep Q fname)
    (htail : ∀ (vs : List (ValueHOL 64)) (body : ProgHOL 64)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
      (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vs →
      lookupCodeHOLFinite s.code.lookup fname vs = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      WorldStep (bufRegions B) gw keep Q (callEntryStateHOLFinite s callee) (some (.returned v)) post →
      PtxBlockOutUnhit s { post with locals := s.locals } →
      PtxRelBase txDone entry { post with locals := s.locals } →
      (post.code = originalRuntimeCode) →
      PtxRelRunStrong entry tail { post with locals := s.locals }) :
    PtxRelRunStrong entry (.seq (.call (some (none, none)) fname args) tail) s := by
  intro hres
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hres ⊢
  rcases ha : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [evalListHOLFinite, ha] at hres
    exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · simp only [evalListHOLFinite, ha] at hres ⊢
    have ha_fin : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vs := by
      simpa [evalListHOLFinite] using ha
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body, callee, ret⟩
    · simp only [hl] at hres
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
    · simp only [hl] at hres ⊢
      by_cases hcz : s.clock = 0
      · simp only [hcz, ↓reduceIte] at hres
        exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
      · simp only [hcz, ↓reduceIte] at hres ⊢
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).1
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rb, post⟩
        have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (rb, post) := hb
        rw [hb] at hmeta
        simp only [hb] at hres ⊢
        cases rb with
        | none => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | some cr =>
          cases cr with
          | timeOut | error | «break» | «continue» | finalFfi _ =>
            exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | exception eid ev =>
            dsimp only at hres ⊢
            have hspec := hwk.at_lookup s hc vs body callee ret hl
              (localsFree_worldOK s callee (s.clock - 1) hbase.world) (by rw [hb']; simp)
            rw [hb'] at hspec
            have hstep_s : WorldStep (bufRegions B) gw keep NoExtra s (some (.exception eid ev)) post :=
              R13Shards.worldStep_with_locals (hspec hres).1.1 s.locals s.clock
            have hex := ptxRelBase_exception_worldStep hbase hB hBsub hgw hkeep hstep_s
            exact ptxWorldStep_strong_with_locals_right .empty post.clock hex
          | returned v =>
            dsimp only at hres ⊢
            by_cases hsh : shapeEqHOL (shapeOfHOLExact v) ret = true
            · simp only [hsh, ↓reduceIte] at hres ⊢
              have hspec := hwk.at_lookup s hc vs body callee ret hl
                (localsFree_worldOK s callee (s.clock - 1) hbase.world) (by rw [hb']; simp)
              rw [hb'] at hspec
              have hscbo := hspec (Or.inl ⟨v, rfl⟩)
              have hstep_s : WorldStep (bufRegions B) gw keep NoExtra s (some (.returned v)) post :=
                R13Shards.worldStep_with_locals hscbo.1.1 s.locals s.clock
              have hfmp_eq : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" :=
                globN_eq_of_lookup (hstep_s.2.2.1 _ hfmp_gw)
              have hbo_u : PtxBlockOutUnhit s post :=
                hscbo.2 (Or.inr (Or.inr (Or.inr ⟨v, rfl⟩)))
              have hbase_post : PtxRelBase txDone entry post :=
                ptxRelBase_step_of_blockOutUnhit hbase hB hBsub hgw hkeep hbo_gw hbo_keep
                  hstep_s hscbo.1.2 (by omega) hbo_u
              have hbase_res : PtxRelBase txDone entry { post with locals := s.locals } :=
                ptxRelBase_with_locals hbase_post s.locals post.clock
              exact htail vs body callee ret v post ha_fin hl hb' hscbo.1.1 hbo_u hbase_res
                (hmeta.trans hc) hres
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hres
              exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
