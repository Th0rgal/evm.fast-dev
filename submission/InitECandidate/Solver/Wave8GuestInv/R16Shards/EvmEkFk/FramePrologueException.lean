import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemAlignedBridge
import InitECandidate.Solver.Wave8GuestInv.R13Shards.Common

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! The prologue interface is separate from the finish-child interface. In
particular, its aligned contracts use `HeadMemBridge.HeadMemChainWF`. -/
namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFkPrologue

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R13
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge

abbrev FrameStartAvoids {F : Type} (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
   (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352),
   (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384),
   (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
   (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
   (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
   (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96),
   (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40),
   (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128),
   (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128),
   (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
   (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64),
   (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52),
   (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)]

private theorem bufferRegion_disj_frameObjects_le {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S : List Nat} (hInv : EvmInvAt s S)
    (gn : String × Nat) (hg : gn ∈ globalBuffers)
    (n : Nat) (hle : n ≤ gn.2) :
    ∀ j ∈ ((evmChain s).map (frameObjects s)).flatten, Disj (bufferRegion s (gn.1, n)) j := by
  obtain ⟨_, _, _, _, _, _, _, _, hFO_disj, _⟩ := hInv
  intro j hj
  rw [List.mem_flatten] at hj
  obtain ⟨fo, hfo_map, hj_fo⟩ := hj
  obtain ⟨ec, hec, rfl⟩ := List.mem_map.1 hfo_map
  have hfix : bufferRegion s gn ∈ fixedObjects s := by
    unfold fixedObjects
    apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
    exact List.mem_map.2 ⟨gn, hg, rfl⟩
  have hd : Disj (bufferRegion s gn) j :=
    ((hFO_disj ec hec j hj_fo).2 _ hfix).flip
  by_cases hz : globN s gn.1 = 0
  · exact Or.inl (by simp [bufferRegion, hz])
  · simp only [bufferRegion, hz, ↓reduceIte] at hd ⊢
    rcases hd with h | h | h | h
    · exact Or.inl (by dsimp only at h ⊢; omega)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (by dsimp only at h ⊢; omega)))
    · exact Or.inr (Or.inr (Or.inr h))

theorem evmAvoids_frameStart_of_evmInv {F : Type} (s : PanSemStateFiniteExact 64 F) (h : EvmInv s) :
    EvmAvoids FrameStartAvoids s := by
  obtain ⟨hA, S, hInv⟩ := (evmInv_iff_at s).1 h
  have hW := hInv.1
  obtain ⟨Nd, hTr, _⟩ := hInv.2.2.2.2.2.2.2.2.2.1
  have hWT : WorldTypedWith s S Nd := ⟨hW.1, hW.2.1, hW.2.2.1, hTr⟩
  refine ⟨hA, S, hInv, Nd, hTr, ?_⟩
  intro i hi j hj
  have hi_part : ∃ gn ∈ globalBuffers, gn.1 ∉ typedRecords.map Prod.fst ∧
      ∃ n, n ≤ gn.2 ∧ i = bufferRegion s (gn.1, n) := by
    change i ∈ [bufferRegion s ("b2_v", 128), bufferRegion s ("bn_expw", 352),
      bufferRegion s ("bn_gamma", 384), bufferRegion s ("keccak_pad", 136),
      bufferRegion s ("keccak_st", 200), bufferRegion s ("mpt_nib_scratch", 64),
      bufferRegion s ("pre_hdr_buf", 96), bufferRegion s ("rmd_h", 40),
      bufferRegion s ("rmd_pad", 128), bufferRegion s ("rmd_x", 128),
      bufferRegion s ("sha_pad", 128), bufferRegion s ("sha_st", 64),
      bufferRegion s ("sk_buf", 52), bufferRegion s ("u256_ws", 640)] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨("b2_v", 128), by decide, by decide, 128, le_rfl, rfl⟩
    · exact ⟨("bn_expw", 352), by decide, by decide, 352, le_rfl, rfl⟩
    · exact ⟨("bn_gamma", 384), by decide, by decide, 384, le_rfl, rfl⟩
    · exact ⟨("keccak_pad", 136), by decide, by decide, 136, le_rfl, rfl⟩
    · exact ⟨("keccak_st", 200), by decide, by decide, 200, le_rfl, rfl⟩
    · exact ⟨("mpt_nib_scratch", 64), by decide, by decide, 64, le_rfl, rfl⟩
    · exact ⟨("pre_hdr_buf", 96), by decide, by decide, 96, le_rfl, rfl⟩
    · exact ⟨("rmd_h", 40), by decide, by decide, 40, le_rfl, rfl⟩
    · exact ⟨("rmd_pad", 128), by decide, by decide, 128, le_rfl, rfl⟩
    · exact ⟨("rmd_x", 128), by decide, by decide, 128, le_rfl, rfl⟩
    · exact ⟨("sha_pad", 128), by decide, by decide, 128, le_rfl, rfl⟩
    · exact ⟨("sha_st", 64), by decide, by decide, 64, le_rfl, rfl⟩
    · exact ⟨("sk_buf", 64), by decide, by decide, 52, by decide, rfl⟩
    · exact ⟨("u256_ws", 640), by decide, by decide, 640, le_rfl, rfl⟩
  obtain ⟨gn, hg, hu, n, hle, rfl⟩ := hi_part
  rcases List.mem_append.1 hj with hj_w | hj_f
  · exact bufferRegion_disj_le hWT gn hg hu n hle j hj_w
  · exact bufferRegion_disj_frameObjects_le hInv gn hg n hle j hj_f

theorem localsFree_evmAvoids_frameStart : LocalsFree (EvmAvoids FrameStartAvoids) := by
  intro F s locals k h
  obtain ⟨hA, S, hInv, Nd, hTr, hD⟩ := h
  have hA' : ArenaReady { s with locals := locals, clock := k } := localsFree_arenaReady s locals k hA
  have htr_eq : TriesTypedWith { s with locals := locals, clock := k } S Nd ↔ TriesTypedWith s S Nd :=
    Iff.rfl
  have hinvAt_eq : EvmInvAt { s with locals := locals, clock := k } S ↔ EvmInvAt s S := by
    simp only [EvmInvAt, FrameWF, MsgOwned, worldTyped_with_locals, evmChain_with_locals]
    exact Iff.rfl
  refine ⟨hA', S, hinvAt_eq.2 hInv, Nd, htr_eq.2 hTr, ?_⟩
  change IvlsDisj (FrameStartAvoids { s with locals := locals, clock := k })
    (worldTypedIvls { s with locals := locals, clock := k } S Nd ++
      (List.map (frameObjects { s with locals := locals, clock := k })
        (evmChain { s with locals := locals, clock := k })).flatten)
  rw [evmChain_with_locals s locals k]
  exact hD

theorem ro_u256_is_zero : ReadOnlyFn (ofString "u256_is_zero") := by
  refine readOnlyFn_of_guestAst 42 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_is_zero rfl ?_
  dsimp only [Guest.Software.guestFn_u256_is_zero, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  exact ReadOnlyProg.seq
    (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
    (ReadOnlyProg.ret _)

theorem ro_memeq : ReadOnlyFn (ofString "memeq") := by
  refine readOnlyFn_of_guestAst 18 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_memeq rfl ?_
  dsimp only [Guest.Software.guestFn_memeq, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  exact ReadOnlyProg.dec _ _ _
    (ReadOnlyProg.seq
      (ReadOnlyProg.ite _
        (ReadOnlyProg.seq
          (ReadOnlyProg.ite _
            (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
              (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                  (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                    (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                      (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                        (ReadOnlyProg.ret _)))))))
            ReadOnlyProg.skip)
          (ReadOnlyProg.seq
            (ReadOnlyProg.ite _
              (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                  (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                    (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                      (ReadOnlyProg.ret _)))))
              ReadOnlyProg.skip)
            (ReadOnlyProg.seq
              (ReadOnlyProg.ite _
                (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                  (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                    (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                      (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                        (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                          (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                            (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                              (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                                (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                                  (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                                    (ReadOnlyProg.ret _)))))))))))
                ReadOnlyProg.skip)
              (ReadOnlyProg.seq
                (ReadOnlyProg.while_loop _
                  (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                    (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                      (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                        (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                          (ReadOnlyProg.assign_local _ _))))))
                (ReadOnlyProg.while_loop _
                  (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                    (ReadOnlyProg.assign_local _ _)))))))
        ReadOnlyProg.skip)
      (ReadOnlyProg.seq
        (ReadOnlyProg.while_loop _
          (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
            (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
              (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                  (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                    (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                      (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                        (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                          (ReadOnlyProg.assign_local _ _))))))))))
        (ReadOnlyProg.seq
          (ReadOnlyProg.while_loop _
            (ReadOnlyProg.seq (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
              (ReadOnlyProg.assign_local _ _)))
          (ReadOnlyProg.ret _))))

theorem ro_is_zero_bytes : ReadOnlyFn (ofString "is_zero_bytes") := by
  refine readOnlyFn_of_guestAst 19 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_is_zero_bytes rfl ?_
  dsimp only [Guest.Software.guestFn_is_zero_bytes, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  exact ReadOnlyProg.dec _ _ _
    (ReadOnlyProg.seq
      (ReadOnlyProg.while_loop _
        (ReadOnlyProg.seq
          (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
          (ReadOnlyProg.assign_local _ _)))
      (ReadOnlyProg.ret _))

theorem ro_precompile_index : ReadOnlyFn (ofString "precompile_index") := by
  refine readOnlyFn_of_guestAst 822 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_precompile_index rfl ?_
  dsimp only [Guest.Software.guestFn_precompile_index, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  exact ReadOnlyProg.decCall ro_is_zero_bytes _ _ _
    (ReadOnlyProg.seq
      (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
      (ReadOnlyProg.dec _ _ _
        (ReadOnlyProg.dec _ _ _
          (ReadOnlyProg.seq
            (ReadOnlyProg.ite _
              (ReadOnlyProg.seq
                (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                (ReadOnlyProg.ret _))
              ReadOnlyProg.skip)
            (ReadOnlyProg.seq
              (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
              (ReadOnlyProg.seq
                (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                (ReadOnlyProg.ret _)))))))

theorem precompile_index_chainCellsKept :
    ChainCellsKept GuestInv (ofString "precompile_index") := by
  obtain ⟨ps, body, rt, hl, hrun⟩ := ro_precompile_index
  refine ⟨ps, body, rt, hl, fun s hc hP hex hnt hr ec hec => ?_⟩
  have hpost := hrun s hc hP hex hnt hr
  rw [hpost]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem precompile_index_headMemChainWF :
    KeepsOn (fun s => GuestInv s ∧ HeadMemChainWF s) HeadMemChainWF
      (ofString "precompile_index") := by
  obtain ⟨ps, body, rt, hl, hrun⟩ := ro_precompile_index
  refine ⟨ps, body, rt, hl, fun s hc hP hex hnt hr => ?_⟩
  rw [hrun s hc hP.1 hex hnt hr]
  exact headMemChainWF_locals s _ _ hP.2

theorem ek_precompile_index : EvmKeeps EvmInv [] (ofString "precompile_index") := by
  obtain ⟨ps, body, rt, hl, hrun⟩ := ro_precompile_index
  refine ⟨ps, body, rt, hl, fun s hc hP hex hnt hr => ?_⟩
  have hpost := hrun s hc hP.1.1 hex hnt hr
  rw [hpost]
  refine ⟨localsFree_evmInv s _ _ hP, le_rfl, ?_, ?_⟩
  · intro k hk
    rfl
  · exact evmChain_with_locals s _ _

theorem frame_exception_headMemChainWF : FrameExceptionSpecA :=
  frame_exception_spec_aligned

section FrameExceptionPreservation

open InitECandidate.Solver.GuestGlobalKeep (lookupCode_installed)
open InitECandidate.Solver.Wave8GuestInv.R11Shards (ResumesR11 not_resumes_err
  store_res_not_resumes updW store_global_off_word memW_updW_same memW_updW_ne evm_head_globals
  refill_body_eq frame_halt_body_eq frame_exception_body_eq one_word_param_of_lookup
  lookup_refill_frame_state_gas lookup_frame_halt lookup_frame_exception headAllowedOffsets
  evmInv_of_head_status_gas_update)
open InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue (noCatchableRaise
  evaluate_noCatchableRaise)

def frameExceptionCallees (f : MlS) : Bool :=
  f == ofString "refill_frame_state_gas" || f == ofString "frame_halt" ||
  f == ofString "frame_exception"

theorem frameExceptionCallees_good :
    ∀ f, frameExceptionCallees f = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup f values =
        some (body, callee, rs) →
      noCatchableRaise frameExceptionCallees body = true := by
  intro f hf values body callee rs hfound
  obtain ⟨params, rs', hinst⟩ := lookupCode_installed hfound
  simp only [frameExceptionCallees, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with (rfl | rfl) | rfl
  · rw [lookup_refill_frame_state_gas] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [lookup_frame_halt] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [lookup_frame_exception] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl

theorem frame_exception_resumes_returned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) {values body callee rs}
    (hl : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "frame_exception") values = some (body, callee, rs))
    (hres : Resumes (evaluateHOLFiniteState s body).1) :
    ∃ v, (evaluateHOLFiniteState s body).1 = some (.returned v) := by
  rcases hres with h | ⟨e, v, he, hne⟩
  · exact h
  · exact absurd he (evaluate_noCatchableRaise frameExceptionCallees frameExceptionCallees_good
      body (frameExceptionCallees_good _ (by decide) values body callee rs hl) s hcode e v hne)

private theorem chain_cells_of_headAllowed {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hE : EvmInv s)
    (hmem_out : ∀ x : BitVec 64,
      (∀ addr ∈ headAllowedOffsets (globN s "ev") (globN s "cur_cont"),
        x ≠ BitVec.ofNat 64 addr) →
      post.memory x = s.memory x) :
    ∀ ec ∈ evmChain s,
      memW post (ec.1 + 24) = memW s (ec.1 + 24) ∧
      memW post (ec.1 + 32) = memW s (ec.1 + 32) ∧
      memW post (ec.1 + 40) = memW s (ec.1 + 40) ∧
      memW post (ec.2 + 56) = memW s (ec.2 + 56) := by
  obtain ⟨_, S, _, hrest⟩ := hE
  dsimp only at hrest
  obtain ⟨_, _, _, hFWF, _, _, hPair, _⟩ := hrest
  obtain ⟨tl, hcs⟩ : ∃ tl, evmChain s = (globN s "ev", globN s "cur_cont") :: tl :=
    ⟨_, evmChain_cons s⟩
  have hSE : scratchEnd = 2965299200 := rfl
  have hhead := hFWF _ (head_mem_evmChain s)
  have he_in := (hhead.1 (globN s "ev", 280) (by simp)).1.2
  have hc_in := (hhead.1 (globN s "cur_cont", 104) (by simp)).1.2
  dsimp only at he_in hc_in
  rw [hcs, List.map_cons, List.flatten_cons, List.pairwise_append] at hPair
  obtain ⟨hP0, _, hcross⟩ := hPair
  have hdec : Disj (globN s "ev", 280) (globN s "cur_cont", 104) := by
    unfold frameObjects at hP0
    exact (List.pairwise_cons.mp (List.pairwise_append.mp hP0).1).1 _ (by simp)
  have hsafe : ∀ a : Nat, a < 2 ^ 64 →
      (∀ addr ∈ headAllowedOffsets (globN s "ev") (globN s "cur_cont"), a ≠ addr) →
      memW post a = memW s a := by
    intro a hlt hne
    unfold memW
    rw [hmem_out (BitVec.ofNat 64 a)]
    intro addr haddr heq
    have hal : addr < 2 ^ 64 := by
      simp only [headAllowedOffsets, List.mem_cons, List.not_mem_nil, or_false] at haddr
      rw [hSE] at he_in hc_in
      rcases haddr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    have := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hal] at this
    exact hne addr haddr this
  intro ec hec
  rw [hcs] at hec
  rcases List.mem_cons.mp hec with rfl | htl
  · unfold Disj at hdec; dsimp only at hdec
    rw [hSE] at he_in hc_in
    refine ⟨?_, ?_, ?_, ?_⟩ <;> apply hsafe <;> (try dsimp only) <;> (try omega) <;>
      (intro addr haddr
       simp only [headAllowedOffsets, List.mem_cons, List.not_mem_nil, or_false] at haddr
       rcases haddr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  · have hFec := hFWF ec (by rw [hcs]; exact List.mem_cons_of_mem _ htl)
    have hr_in := (hFec.1 (ec.1, 280) (by simp)).1.2
    have hk_in := (hFec.1 (ec.2, 104) (by simp)).1.2
    dsimp only at hr_in hk_in
    have hmemb : ∀ o ∈ [(ec.1, 280), (ec.2, 104)],
        o ∈ ((tl.map (frameObjects s)).flatten) := by
      intro o ho
      exact List.mem_flatten.2 ⟨frameObjects s ec, List.mem_map_of_mem htl,
        by unfold frameObjects; simp only [List.mem_cons, List.mem_append] at ho ⊢; tauto⟩
    have hA : (globN s "ev", 280) ∈ frameObjects s (globN s "ev", globN s "cur_cont") := by
      unfold frameObjects; simp
    have hB : (globN s "cur_cont", 104) ∈ frameObjects s (globN s "ev", globN s "cur_cont") := by
      unfold frameObjects; simp
    have d1 := hcross _ hA _ (hmemb (ec.1, 280) (by simp))
    have d2 := hcross _ hB _ (hmemb (ec.1, 280) (by simp))
    have d3 := hcross _ hA _ (hmemb (ec.2, 104) (by simp))
    have d4 := hcross _ hB _ (hmemb (ec.2, 104) (by simp))
    unfold Disj at d1 d2 d3 d4; dsimp only at d1 d2 d3 d4
    rw [hSE] at he_in hc_in hr_in hk_in
    refine ⟨?_, ?_, ?_, ?_⟩ <;> apply hsafe <;> (try omega) <;>
      (intro addr haddr
       simp only [headAllowedOffsets, List.mem_cons, List.not_mem_nil, or_false] at haddr
       rcases haddr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)

private theorem refill_exec_mem_out {F : Type} {s : PanSemStateFiniteExact 64 F} (hInv : EvmInv s)
    (hres : ResumesR11 (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_refill_frame_state_gas)).1) :
    ∀ x : BitVec 64,
      (∀ addr ∈ headAllowedOffsets (globN s "ev") (globN s "cur_cont"),
        x ≠ BitVec.ofNat 64 addr) →
      (evaluateHOLFiniteState s
        (sourceFnBody Guest.Software.guestFn_refill_frame_state_gas)).2.memory x = s.memory x := by
  obtain ⟨he_lt, _, ⟨evw, hevw_lk, hevw_nat⟩, _, _⟩ := evm_head_globals hInv
  rw [refill_body_eq, evaluateHOLFiniteState_dec_total] at hres ⊢
  dsimp only at hres ⊢
  revert hres
  rcases @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .global (ofString "ev"), .const 112])) with _ | msgVal
  · dsimp only; intro hres; exact absurd hres not_resumes_err
  · dsimp only
    by_cases hsh_msg : shapeEqHOL .one (shapeOfHOLExact msgVal) = true
    · rw [if_pos hsh_msg]; dsimp only; intro hres
      let s0 := setVarHOLFinite (ofString "msg") msgVal s
      let body0 : ProgHOL 64 :=
        .seq
          (.store (.op .add [.var .global (ofString "ev"), .const 64])
            (.op .add
              [.load .one (.op .add [.var .global (ofString "ev"), .const 64]),
               .load .one (.op .add [.var .global (ofString "ev"), .const 192])]))
          (.seq
            (.store (.op .add [.var .global (ofString "ev"), .const 72])
              (.load .one (.op .add [.var .local (ofString "msg"), .const 48])))
            (.seq
              (.store (.op .add [.var .global (ofString "ev"), .const 192]) (.const 0))
              (.return (.const 0))))
      change ResumesR11 (evaluateHOLFiniteState s0 body0).1 at hres
      change ∀ x : BitVec 64, _ →
        ({ (evaluateHOLFiniteState s0 body0).2 with
          locals := (evaluateHOLFiniteState s0 body0).2.locals.resVarEq
            (ofString "msg", s.locals.lookup (ofString "msg")) }).memory x = s.memory x
      dsimp only [body0] at hres ⊢
      rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
      cases h1 : evaluateHOLFiniteState s0
          (.store (.op .add [.var .global (ofString "ev"), .const 64])
            (.op .add
              [.load .one (.op .add [.var .global (ofString "ev"), .const 64]),
               .load .one (.op .add [.var .global (ofString "ev"), .const 192])])) with
      | mk r1 s1 =>
        rw [h1] at hres; dsimp only at hres ⊢
        rcases r1 with _ | res1
        · obtain ⟨w1, _, hs1_eq⟩ := store_global_off_word (t := s0) (post := s1)
            (gname := "ev") (gbase := globN s "ev") (off := 64) hevw_lk hevw_nat (by omega)
            (fun v hv => by
              simp only [evalHOLExact, wordOpHOL] at hv; revert hv
              rcases @evalListHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a)) _ with _ | vs
              · simp
              · dsimp only; split
                · simp only [Option.map]
                  rcases wordOp .add (vs.map valueWord) with _ | w
                  · simp
                  · intro hv; injection hv with hv'; exact ⟨w, hv'.symm⟩
                · simp) h1
          rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
          cases h2 : evaluateHOLFiniteState s1
              (.store (.op .add [.var .global (ofString "ev"), .const 72])
                (.load .one (.op .add [.var .local (ofString "msg"), .const 48]))) with
          | mk r2 s2 =>
            rw [h2] at hres; dsimp only at hres ⊢
            rcases r2 with _ | res2
            · obtain ⟨w2, _, hs2_eq⟩ := store_global_off_word (t := s1) (post := s2)
                (gname := "ev") (gbase := globN s "ev") (off := 72)
                (by rw [hs1_eq]; exact hevw_lk) hevw_nat (by omega)
                (fun v hv => by
                  have hml_word : ∀ (addr : BitVec 64) dom (dec : DecidablePred dom),
                      @memLoadHOLExact 64 _ .one addr dom dec s1.memory s1.structs = some v →
                      ∃ w : BitVec 64, v = .val (.word w) := by
                    intro addr dom dec hml
                    unfold memLoadHOLExact at hml
                    by_cases hd : dom addr
                    · rw [if_pos hd] at hml; injection hml with hv'
                      cases hm : s1.memory addr with
                      | word w => rw [hm] at hv'; exact ⟨w, hv'.symm⟩
                    · rw [if_neg hd] at hml; cases hml
                  unfold evalHOLExact at hv; revert hv
                  split
                  · split
                    · rename_i addr _; exact hml_word addr _ _
                    · simp
                  · simp) h2
              rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
              cases h3 : evaluateHOLFiniteState s2
                  (.store (.op .add [.var .global (ofString "ev"), .const 192]) (.const 0)) with
              | mk r3 s3 =>
                rw [h3] at hres; dsimp only at hres ⊢
                rcases r3 with _ | res3
                · obtain ⟨w3, _, hs3_eq⟩ := store_global_off_word (t := s2) (post := s3)
                    (gname := "ev") (gbase := globN s "ev") (off := 192)
                    (by rw [hs2_eq, hs1_eq]; exact hevw_lk) hevw_nat (by omega)
                    (fun v hv => by injection hv with hv'; exact ⟨0, hv'.symm⟩) h3
                  rw [evaluateHOLFiniteState_return] at hres ⊢
                  dsimp only [evalHOLExact] at hres ⊢
                  have hle32 : sizeOfShapeWithContextHOL s3.structs
                      (shapeOfHOLExact (ValueHOL.val (HolWordLab.word (0 : BitVec 64)))) ≤ 32 := by
                    simp [shapeOfHOLExact]
                  rw [if_pos hle32]; dsimp only
                  intro x hx
                  change s3.memory x = s.memory x
                  rw [hs3_eq, hs2_eq, hs1_eq]
                  have hn192 : x ≠ BitVec.ofNat 64 (globN s "ev" + 192) := hx _ (by simp [headAllowedOffsets])
                  have hn72 : x ≠ BitVec.ofNat 64 (globN s "ev" + 72) := hx _ (by simp [headAllowedOffsets])
                  have hn64 : x ≠ BitVec.ofNat 64 (globN s "ev" + 64) := hx _ (by simp [headAllowedOffsets])
                  simp [updW, hn192, hn72, hn64, s0, setVarHOLFinite]
                · exact absurd hres (store_res_not_resumes h3)
            · exact absurd hres (store_res_not_resumes h2)
        · exact absurd hres (store_res_not_resumes h1)
    · rw [if_neg hsh_msg]; dsimp only; intro hres; exact absurd hres not_resumes_err

private theorem frame_halt_exec_mem_out {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s) {w_err : BitVec 64}
    (hw_err : s.locals.lookup (ofString "err") = some (.val (.word w_err)))
    (hres : ResumesR11 (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_frame_halt)).1) :
    ∀ x : BitVec 64,
      (∀ addr ∈ headAllowedOffsets (globN s "ev") (globN s "cur_cont"),
        x ≠ BitVec.ofNat 64 addr) →
      (evaluateHOLFiniteState s
        (sourceFnBody Guest.Software.guestFn_frame_halt)).2.memory x = s.memory x := by
  obtain ⟨he_lt, _, ⟨evw, hevw_lk, hevw_nat⟩, _, _⟩ := evm_head_globals hInv
  rw [frame_halt_body_eq, evaluateHOLFiniteState_seq_line780] at hres ⊢
  cases h1 : evaluateHOLFiniteState s
      (.store (.op .add [.var .global (ofString "ev"), .const 184])
        (.op .add
          [.load .one (.op .add [.var .global (ofString "ev"), .const 184]),
           .load .one (.op .add [.var .global (ofString "ev"), .const 64])])) with
  | mk r1 s1 =>
    rw [h1] at hres; dsimp only at hres ⊢
    rcases r1 with _ | res1
    · obtain ⟨w1, _, hs1_eq⟩ := store_global_off_word (t := s) (post := s1)
        (gname := "ev") (gbase := globN s "ev") (off := 184) hevw_lk hevw_nat (by omega)
        (fun v hv => by
          simp only [evalHOLExact, wordOpHOL] at hv; revert hv
          rcases @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) _ with _ | vs
          · simp
          · dsimp only; split
            · simp only [Option.map]
              rcases wordOp .add (vs.map valueWord) with _ | w
              · simp
              · intro hv; injection hv with hv'; exact ⟨w, hv'.symm⟩
            · simp) h1
      rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
      cases h2 : evaluateHOLFiniteState s1
          (.store (.op .add [.var .global (ofString "ev"), .const 64]) (.const 0)) with
      | mk r2 s2 =>
        rw [h2] at hres; dsimp only at hres ⊢
        rcases r2 with _ | res2
        · obtain ⟨w2, _, hs2_eq⟩ := store_global_off_word (t := s1) (post := s2)
            (gname := "ev") (gbase := globN s "ev") (off := 64)
            (by rw [hs1_eq]; exact hevw_lk) hevw_nat (by omega)
            (fun v hv => by injection hv with hv'; exact ⟨0, hv'.symm⟩) h2
          rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
          cases h3 : evaluateHOLFiniteState s2
              (.store (.op .add [.var .global (ofString "ev"), .const 160])
                (.var .local (ofString "err"))) with
          | mk r3 s3 =>
            rw [h3] at hres; dsimp only at hres ⊢
            rcases r3 with _ | res3
            · obtain ⟨w3, _, hs3_eq⟩ := store_global_off_word (t := s2) (post := s3)
                (gname := "ev") (gbase := globN s "ev") (off := 160)
                (by rw [hs2_eq, hs1_eq]; exact hevw_lk) hevw_nat (by omega)
                (fun v hv => by
                  change s2.locals.lookup (ofString "err") = some v at hv
                  rw [hs2_eq, hs1_eq] at hv; dsimp only at hv; rw [hw_err] at hv
                  injection hv with hv'; exact ⟨w_err, hv'.symm⟩) h3
              rw [evaluateHOLFiniteState_return] at hres ⊢
              dsimp only [evalHOLExact] at hres ⊢
              have hle32 : sizeOfShapeWithContextHOL s3.structs
                  (shapeOfHOLExact (ValueHOL.val (HolWordLab.word (0 : BitVec 64)))) ≤ 32 := by
                simp [shapeOfHOLExact]
              rw [if_pos hle32]; dsimp only
              intro x hx
              change s3.memory x = s.memory x
              rw [hs3_eq, hs2_eq, hs1_eq]
              have hn160 : x ≠ BitVec.ofNat 64 (globN s "ev" + 160) := hx _ (by simp [headAllowedOffsets])
              have hn64 : x ≠ BitVec.ofNat 64 (globN s "ev" + 64) := hx _ (by simp [headAllowedOffsets])
              have hn184 : x ≠ BitVec.ofNat 64 (globN s "ev" + 184) := hx _ (by simp [headAllowedOffsets])
              simp [updW, hn160, hn64, hn184]
            · exact absurd hres (store_res_not_resumes h3)
        · exact absurd hres (store_res_not_resumes h2)
    · exact absurd hres (store_res_not_resumes h1)

private theorem call0_returned_inv_fe {F : Type} {s post_call : PanSemStateFiniteExact 64 F}
    {fname : MlS} {args : List (ExpHOL 64)}
    (hcall : evaluateHOLFiniteState s (.call (some (none, none)) fname args) = (none, post_call)) :
    ∃ values body callee ret v cpost,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values ∧
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), cpost) ∧
      post_call = { cpost with locals := s.locals } := by
  rw [evaluateHOLFiniteState_call] at hcall
  revert hcall
  rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · simp
  · dsimp only
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body, callee, ret⟩
    · simp
    · dsimp only
      by_cases hz : s.clock = 0
      · simp [hz]
      · simp only [hz, ↓reduceIte]
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, cpost⟩
        rcases res with _ | r
        · simp
        · cases r with
          | returned v =>
            dsimp only; split
            · intro h; injection h with _ hp
              exact ⟨values, body, callee, ret, v, cpost, rfl, hl, hrun, hp.symm⟩
            · simp
          | _ => simp

private theorem seq_returned_inv_fe {F : Type} {s : PanSemStateFiniteExact 64 F} {p1 p2 : ProgHOL 64}
    {v : ValueHOL 64}
    (h : (evaluateHOLFiniteState s (.seq p1 p2)).1 = some (.returned v))
    (hn1 : ∀ u, (evaluateHOLFiniteState s p1).1 ≠ some (.returned u)) :
    ∃ m, evaluateHOLFiniteState s p1 = (none, m) ∧
      evaluateHOLFiniteState m p2 = evaluateHOLFiniteState s (.seq p1 p2) := by
  have hseq := evaluateHOLFiniteState_seq_line780 s p1 p2
  rcases hr1 : evaluateHOLFiniteState s p1 with ⟨r1, m⟩
  rw [hr1] at hseq
  cases r1 with
  | none => exact ⟨m, rfl, hseq.symm⟩
  | some r =>
    rw [hseq] at h; dsimp only at h
    injection h with hr; subst hr
    exact absurd hr1 (fun h' => hn1 v (by rw [h']))

private theorem call0_ne_returned_fe {F : Type} (s : PanSemStateFiniteExact 64 F) (fn : MlS)
    (args : List (ExpHOL 64)) (u : ValueHOL 64) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fn args)).1 ≠ some (.returned u) := by
  rw [evaluateHOLFiniteState_call]
  rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | _
  · simp
  · dsimp only
    rcases lookupCodeHOLFinite s.code.lookup fn _ with _ | ⟨_, _, _⟩
    · simp
    · dsimp only; split
      · simp
      · rcases evaluateHOLFiniteState _ _ with ⟨res, _⟩
        rcases res with _ | r
        · simp
        · cases r with
          | returned _ => dsimp only; split <;> simp
          | _ => simp

private theorem store_ne_returned_fe {F : Type} (s : PanSemStateFiniteExact 64 F) (d e : ExpHOL 64)
    (u : ValueHOL 64) :
    (evaluateHOLFiniteState s (.store d e)).1 ≠ some (.returned u) := by
  rw [evaluateHOLFiniteState_store]
  split
  · split
    · split <;> simp
    · simp
  · simp

private theorem ite_ne_returned_fe {F : Type} {s : PanSemStateFiniteExact 64 F}
    {c : ExpHOL 64} {y n : ProgHOL 64}
    (hy : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F) (u : ValueHOL 64),
      (evaluateHOLFiniteState t y).1 ≠ some (.returned u))
    (hn : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F) (u : ValueHOL 64),
      (evaluateHOLFiniteState t n).1 ≠ some (.returned u))
    (u : ValueHOL 64) :
    (evaluateHOLFiniteState s (.ite c y n)).1 ≠ some (.returned u) := by
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact hn s u
    · exact hy s u
  · simp

private theorem seq_ne_returned_fe {p1 p2 : ProgHOL 64}
    (h1 : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F) (u : ValueHOL 64),
      (evaluateHOLFiniteState t p1).1 ≠ some (.returned u))
    (h2 : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F) (u : ValueHOL 64),
      (evaluateHOLFiniteState t p2).1 ≠ some (.returned u))
    {F : Type} (s : PanSemStateFiniteExact 64 F) (u : ValueHOL 64) :
    (evaluateHOLFiniteState s (.seq p1 p2)).1 ≠ some (.returned u) := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases h : evaluateHOLFiniteState s p1 with ⟨r1, m⟩
  cases r1 with
  | none => exact h2 m u
  | some r =>
    dsimp only; intro hr
    exact h1 s u (by rw [h]; exact hr)

theorem frame_exception_exec_full {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hInv : EvmInv s)
    (w_emp w_err : BitVec 64) (hw_emp : GlobalWord s "evm_empty" w_emp)
    (hw_err : s.locals.lookup (ofString "err") = some (.val (.word w_err)))
    (v : ValueHOL 64)
    (hv : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_exception)).1 =
      some (.returned v)) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_exception)).2
    EvmStep [] s post ∧ EvmDone post ∧ Wave8GuestInv.evmR post ≤ Wave8GuestInv.evmR s ∧
      (∀ x : BitVec 64,
        (∀ addr ∈ headAllowedOffsets (globN s "ev") (globN s "cur_cont"),
          x ≠ BitVec.ofNat 64 addr) →
        post.memory x = s.memory x) ∧
      (∀ ec ∈ evmChain s,
        memW post (ec.1 + 24) = memW s (ec.1 + 24) ∧
        memW post (ec.1 + 32) = memW s (ec.1 + 32) ∧
        memW post (ec.1 + 40) = memW s (ec.1 + 40) ∧
        memW post (ec.2 + 56) = memW s (ec.2 + 56)) ∧
      (HeadMemChainWF s → HeadMemChainWF post) := by
  dsimp only
  obtain ⟨hInv_full, hDone_full, _, hR_full, hW_full⟩ :=
    frame_exception_exec_A s hcode hInv w_emp w_err hw_emp hw_err v hv
  rw [frame_exception_body_eq] at hv hInv_full hDone_full hR_full hW_full ⊢
  obtain ⟨m1, hs1_call, hrest1⟩ := seq_returned_inv_fe hv (call0_ne_returned_fe s _ _)
  have hpost_eq1 := congrArg Prod.snd hrest1.symm
  rw [← hrest1] at hv
  rw [hpost_eq1] at hInv_full hDone_full hR_full hW_full ⊢
  clear hrest1 hpost_eq1
  obtain ⟨vals1, body1, cal1, ret1, rv1, cpost1, _, hl1, hrun1, hm1_eq⟩ := call0_returned_inv_fe hs1_call
  have hcode_lk1 : s.code.lookup (ofString "refill_frame_state_gas") =
      some ([], sourceFnBody Guest.Software.guestFn_refill_frame_state_gas, .one) := by
    rw [hcode]; exact lookup_refill_frame_state_gas
  have hbody1 : body1 = sourceFnBody Guest.Software.guestFn_refill_frame_state_gas :=
    lookupCodeHOLFinite_installed_body s.code.lookup _ _ _ _ _ _ _ _ hcode_lk1 hl1
  subst hbody1
  have hInv_ce1 : EvmInv (callEntryStateHOLFinite s cal1) :=
    localsFree_evmInv s cal1 (s.clock - 1) hInv
  have hres1 : ResumesR11 (evaluateHOLFiniteState (callEntryStateHOLFinite s cal1)
      (sourceFnBody Guest.Software.guestFn_refill_frame_state_gas)).1 := by
    rw [hrun1]; exact Or.inl ⟨rv1, rfl⟩
  obtain ⟨hInv_cp1, hglob_cp1, hch_cp1, _, _⟩ := refill_exec_step_A hInv_ce1 hres1
  have hmem_cp1 := refill_exec_mem_out hInv_ce1 hres1
  have hcpost1_eq : (evaluateHOLFiniteState (callEntryStateHOLFinite s cal1)
      (sourceFnBody Guest.Software.guestFn_refill_frame_state_gas)).2 = cpost1 := by
    rw [hrun1]
  rw [hcpost1_eq] at hInv_cp1 hglob_cp1 hch_cp1 hmem_cp1
  subst hm1_eq
  let s1 := ({ cpost1 with locals := s.locals } : PanSemStateFiniteExact 64 F)
  have hInv1 : EvmInv s1 := localsFree_evmInv cpost1 s.locals cpost1.clock hInv_cp1
  have hglob1 : s1.globals = s.globals := hglob_cp1
  have hch1 : evmChain s1 = evmChain s := by
    exact (evmChain_with_locals cpost1 s.locals cpost1.clock).trans
      (hch_cp1.trans (evmChain_with_locals s cal1 (s.clock - 1)))
  have hmem1 : ∀ x : BitVec 64,
      (∀ addr ∈ headAllowedOffsets (globN s "ev") (globN s "cur_cont"), x ≠ BitVec.ofNat 64 addr) →
      s1.memory x = s.memory x := fun x hx => hmem_cp1 x hx
  have hcode1 : s1.code = originalRuntimeCode := by
    have hm := (PanRunBounded.evaluateHOLFiniteState_metadata s
      (.call (some (none, none)) (ofString "refill_frame_state_gas") [])).1
    rw [hs1_call] at hm; exact hm.trans hcode
  have hite_noret : ∀ u, (evaluateHOLFiniteState s1
      (.ite (.cmp .notEqual (.var .local (ofString "err")) (.const 1))
        (.seq (.call (some (none, none)) (ofString "frame_halt") [.var .local (ofString "err")])
          (.seq (.store (.op .add [.var .global (ofString "ev"), .const 120]) (.var .global (ofString "evm_empty")))
            (.store (.op .add [.var .global (ofString "ev"), .const 128]) (.const 0))))
        (.store (.op .add [.var .global (ofString "ev"), .const 160]) (.var .local (ofString "err"))))).1 ≠ some (.returned u) :=
    ite_ne_returned_fe
      (seq_ne_returned_fe (fun t u => call0_ne_returned_fe t _ _ u)
        (seq_ne_returned_fe (fun t u => store_ne_returned_fe t _ _ u) (fun t u => store_ne_returned_fe t _ _ u)))
      (fun t u => store_ne_returned_fe t _ _ u)
  obtain ⟨s2, hs2_ite, hrest2⟩ := seq_returned_inv_fe hv hite_noret
  have hpost_eq2 := congrArg Prod.snd hrest2.symm
  rw [← hrest2] at hv
  rw [hpost_eq2] at hInv_full hDone_full hR_full hW_full ⊢
  clear hrest2 hpost_eq2
  have hs2_props : EvmInv s2 ∧ s2.globals = s1.globals ∧ evmChain s2 = evmChain s1 ∧
      (∀ x : BitVec 64,
        (∀ addr ∈ headAllowedOffsets (globN s "ev") (globN s "cur_cont"), x ≠ BitVec.ofNat 64 addr) →
        s2.memory x = s1.memory x) := by
    obtain ⟨he_lt1, _, ⟨evw1, hevw1_lk, hevw1_nat⟩, _, _⟩ := evm_head_globals hInv1
    have herr_s1 : s1.locals.lookup (ofString "err") = some (.val (.word w_err)) := hw_err
    have hev_s1 : globN s1 "ev" = globN s "ev" := by simp [globN, hglob1]
    have hcc_s1 : globN s1 "cur_cont" = globN s "cur_cont" := by simp [globN, hglob1]
    rw [evaluateHOLFiniteState_ite] at hs2_ite
    have hcmp : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        (.cmp .notEqual (.var .local (ofString "err")) (.const 1)) =
        some (.val (.word (if w_err ≠ 1 then 1 else 0))) := by
      simp [evalHOLExact, herr_s1, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hcmp] at hs2_ite; dsimp only at hs2_ite
    by_cases hw1 : w_err = 1
    · subst hw1; simp only [ne_eq, not_true_eq_false, ↓reduceIte] at hs2_ite
      obtain ⟨w160, _, rfl⟩ := store_global_off_word (t := s1) (post := s2)
        (gname := "ev") (gbase := globN s1 "ev") (off := 160) hevw1_lk hevw1_nat (by omega)
        (fun v0 hv0 => by
          change s1.locals.lookup (ofString "err") = some v0 at hv0
          rw [herr_s1] at hv0; injection hv0 with hv'; exact ⟨1, hv'.symm⟩) hs2_ite
      let post2 := { s1 with memory := updW s1.memory (BitVec.ofNat 64 (globN s1 "ev" + 160)) w160 }
      have hGp2 : GuestInv post2 := guestInv_congr (s := s1) rfl rfl rfl rfl hInv1.1.1
      have hmem2 : ∀ x : BitVec 64,
          (∀ addr ∈ headAllowedOffsets (globN s1 "ev") (globN s1 "cur_cont"), x ≠ BitVec.ofNat 64 addr) →
          post2.memory x = s1.memory x := by
        intro x hx
        have hn160 : x ≠ BitVec.ofNat 64 (globN s1 "ev" + 160) := hx _ (by simp [headAllowedOffsets])
        simp [post2, updW, hn160]
      have hgas2 : memW post2 (globN s1 "ev" + 64) + memW post2 (globN s1 "ev" + 192) ≤
          memW s1 (globN s1 "ev" + 64) + memW s1 (globN s1 "ev" + 192) := by
        rw [memW_updW_ne s1 _ _ w160 (by omega) (by omega) (by omega),
            memW_updW_ne s1 _ _ w160 (by omega) (by omega) (by omega)]
      obtain ⟨hEp2, hch2, _⟩ := evmInv_of_head_status_gas_update hInv1 hGp2 rfl rfl hmem2 hgas2
      refine ⟨hEp2, rfl, hch2, fun x hx => hmem2 x ?_⟩
      rw [hev_s1, hcc_s1]; exact hx
    · have h10 : ((1 : BitVec 64) = 0) = False := by decide
      simp only [ne_eq, hw1, not_false_eq_true, ↓reduceIte, h10] at hs2_ite
      rw [evaluateHOLFiniteState_seq_line780] at hs2_ite
      rcases hfh : evaluateHOLFiniteState s1
          (.call (some (none, none)) (ofString "frame_halt") [.var .local (ofString "err")]) with ⟨rfh, mfh⟩
      rw [hfh] at hs2_ite
      rcases rfh with _ | r_bad
      · dsimp only at hs2_ite
        obtain ⟨vals_fh, body_fh, cal_fh, ret_fh, rv_fh, cpost_fh, _, hl_fh, hrun_fh, hmfh_eq⟩ :=
          call0_returned_inv_fe hfh
        subst hmfh_eq
        have hcode1_fh : s1.code.lookup (ofString "frame_halt") =
            some ([(ofString "err", .one)], sourceFnBody Guest.Software.guestFn_frame_halt, .one) := by
          rw [hcode1]; exact lookup_frame_halt
        have hbody_fh : body_fh = sourceFnBody Guest.Software.guestFn_frame_halt :=
          lookupCodeHOLFinite_installed_body s1.code.lookup _ _ _ _ _ _ _ _ hcode1_fh hl_fh
        subst hbody_fh
        obtain ⟨w_ce_err, hw_ce_err⟩ := one_word_param_of_lookup lookup_frame_halt
          ⟨vals_fh, by
            have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
              s1.code.lookup (ofString "frame_halt") vals_fh (sourceFnBody Guest.Software.guestFn_frame_halt)
              cal_fh ret_fh hl_fh
            simp only [Flapjack.lookupCodeHOLExact, hcode1_fh] at hx
            split at hx
            · have hret_fh : ret_fh = .one := (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
              subst hret_fh
              rwa [hcode1] at hl_fh
            · cases hx⟩
        have hInv_ce_fh : EvmInv (callEntryStateHOLFinite s1 cal_fh) :=
          localsFree_evmInv s1 cal_fh (s1.clock - 1) hInv1
        have hres_fh : ResumesR11 (evaluateHOLFiniteState (callEntryStateHOLFinite s1 cal_fh)
            (sourceFnBody Guest.Software.guestFn_frame_halt)).1 := by
          rw [hrun_fh]; exact Or.inl ⟨rv_fh, rfl⟩
        obtain ⟨hInv_cp_fh, hglob_cp_fh, hch_cp_fh, _, _⟩ :=
          frame_halt_exec_step_A hInv_ce_fh hw_ce_err hres_fh
        have hmem_cp_fh := frame_halt_exec_mem_out hInv_ce_fh hw_ce_err hres_fh
        have hcpost_fh_eq : (evaluateHOLFiniteState (callEntryStateHOLFinite s1 cal_fh)
            (sourceFnBody Guest.Software.guestFn_frame_halt)).2 = cpost_fh := by
          rw [hrun_fh]
        rw [hcpost_fh_eq] at hInv_cp_fh hglob_cp_fh hch_cp_fh hmem_cp_fh
        let sfh := ({ cpost_fh with locals := s1.locals } : PanSemStateFiniteExact 64 F)
        have hInv_fh : EvmInv sfh := localsFree_evmInv cpost_fh s1.locals cpost_fh.clock hInv_cp_fh
        have hglob_fh : sfh.globals = s1.globals := hglob_cp_fh
        have hch_fh : evmChain sfh = evmChain s1 := by
          exact (evmChain_with_locals cpost_fh s1.locals cpost_fh.clock).trans
            (hch_cp_fh.trans (evmChain_with_locals s1 cal_fh (s1.clock - 1)))
        rw [evaluateHOLFiniteState_seq_line780] at hs2_ite
        rcases hst120 : evaluateHOLFiniteState sfh
            (.store (.op .add [.var .global (ofString "ev"), .const 120])
              (.var .global (ofString "evm_empty"))) with ⟨r120, s120⟩
        rw [hst120] at hs2_ite
        rcases r120 with _ | _
        · dsimp only at hs2_ite
          have hev_sfh : globN sfh "ev" = globN s1 "ev" := by simp [globN, hglob_fh]
          have hcc_sfh : globN sfh "cur_cont" = globN s1 "cur_cont" := by simp [globN, hglob_fh]
          have hemp_sfh : sfh.globals.lookup (ofString "evm_empty") = some (.val (.word w_emp)) := by
            rw [hglob_fh, hglob1]; exact hw_emp
          obtain ⟨w120, _, hs120_eq⟩ := store_global_off_word (t := sfh) (post := s120)
            (gname := "ev") (gbase := globN s1 "ev") (off := 120)
            (by rw [hglob_fh]; exact hevw1_lk) hevw1_nat (by omega)
            (fun v0 hv0 => by
              change sfh.globals.lookup (ofString "evm_empty") = some v0 at hv0
              rw [hemp_sfh] at hv0; injection hv0 with hv'; exact ⟨w_emp, hv'.symm⟩) hst120
          obtain ⟨w128, _, hs2_eq⟩ := store_global_off_word (t := s120) (post := s2)
            (gname := "ev") (gbase := globN s1 "ev") (off := 128)
            (by rw [hs120_eq, hglob_fh]; exact hevw1_lk) hevw1_nat (by omega)
            (fun v0 hv0 => by
              simp [evalHOLExact] at hv0; exact ⟨0, hv0.symm⟩) hs2_ite
          have hGp_s2 : GuestInv s2 := by
            rw [hs2_eq, hs120_eq]
            exact guestInv_congr (s := sfh) rfl rfl rfl rfl hInv_fh.1.1
          have hglob_s2 : s2.globals = sfh.globals := by rw [hs2_eq, hs120_eq]
          have hbe_s2 : s2.be = sfh.be := by rw [hs2_eq, hs120_eq]
          have hmem_s2_fh : ∀ x : BitVec 64,
              (∀ addr ∈ headAllowedOffsets (globN sfh "ev") (globN sfh "cur_cont"), x ≠ BitVec.ofNat 64 addr) →
              s2.memory x = sfh.memory x := by
            intro x hx
            rw [hs2_eq, hs120_eq]
            have hn120 : x ≠ BitVec.ofNat 64 (globN s1 "ev" + 120) := by
              rw [← hev_sfh]; exact hx _ (by simp [headAllowedOffsets])
            have hn128 : x ≠ BitVec.ofNat 64 (globN s1 "ev" + 128) := by
              rw [← hev_sfh]; exact hx _ (by simp [headAllowedOffsets])
            simp [updW, hn120, hn128]
          have hgas_s2 : memW s2 (globN sfh "ev" + 64) + memW s2 (globN sfh "ev" + 192) ≤
              memW sfh (globN sfh "ev" + 64) + memW sfh (globN sfh "ev" + 192) := by
            rw [hev_sfh, hs2_eq,
                memW_updW_ne s120 _ _ w128 (by omega) (by omega) (by omega),
                memW_updW_ne s120 _ _ w128 (by omega) (by omega) (by omega),
                hs120_eq,
                memW_updW_ne sfh _ _ w120 (by omega) (by omega) (by omega),
                memW_updW_ne sfh _ _ w120 (by omega) (by omega) (by omega)]
          obtain ⟨hEp_s2, hch_s2, _⟩ :=
            evmInv_of_head_status_gas_update hInv_fh hGp_s2 hglob_s2 hbe_s2 hmem_s2_fh hgas_s2
          refine ⟨hEp_s2, hglob_s2.trans hglob_fh, hch_s2.trans hch_fh, ?_⟩
          intro x hx
          have hx_s1 : ∀ addr ∈ headAllowedOffsets (globN s1 "ev") (globN s1 "cur_cont"),
              x ≠ BitVec.ofNat 64 addr := by
            rw [hev_s1, hcc_s1]; exact hx
          have hx_sfh : ∀ addr ∈ headAllowedOffsets (globN sfh "ev") (globN sfh "cur_cont"),
              x ≠ BitVec.ofNat 64 addr := by
            rw [hev_sfh, hcc_sfh]; exact hx_s1
          exact (hmem_s2_fh x hx_sfh).trans (hmem_cp_fh x hx_s1)
        · cases hs2_ite
      · cases hs2_ite
  obtain ⟨hInv2, hglob2, hch2, hmem2⟩ := hs2_props
  obtain ⟨s3, hs3_st, hrest3⟩ := seq_returned_inv_fe hv (store_ne_returned_fe s2 _ _)
  have hpost_eq3 := congrArg Prod.snd hrest3.symm
  rw [← hrest3] at hv
  rw [hpost_eq3] at hInv_full hDone_full hR_full hW_full ⊢
  clear hrest3 hpost_eq3
  obtain ⟨_, _, _, ⟨ccw2, hccw2_lk, hccw2_nat⟩, _⟩ := evm_head_globals hInv2
  obtain ⟨w32, _, hs3_eq⟩ := store_global_off_word (t := s2) (post := s3)
    (gname := "cur_cont") (gbase := globN s2 "cur_cont") (off := 32) hccw2_lk hccw2_nat (by omega)
    (fun v0 hv0 => by simp [evalHOLExact] at hv0; exact ⟨1, hv0.symm⟩) hs3_st
  rw [evaluateHOLFiniteState_return] at hv hInv_full hDone_full hR_full hW_full ⊢
  have hc0 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
      (.const 0) = some (.val (.word 0)) := rfl
  rw [hc0] at hv hInv_full hDone_full hR_full hW_full ⊢
  dsimp only at hv hInv_full hDone_full hR_full hW_full ⊢
  have hle32 : sizeOfShapeWithContextHOL s3.structs
      (shapeOfHOLExact (ValueHOL.val (HolWordLab.word (0 : BitVec 64)))) ≤ 32 := by
    simp [shapeOfHOLExact]
  rw [if_pos hle32] at hInv_full hDone_full hR_full hW_full ⊢
  dsimp only at hInv_full hDone_full hR_full hW_full ⊢
  let post := emptyLocalsHOLFinite s3
  have hglob_post : post.globals = s.globals := by
    have hg3 : post.globals = s2.globals := by simp [post, emptyLocalsHOLFinite, hs3_eq]
    exact hg3.trans (hglob2.trans hglob1)
  have hGp_post : GuestInv post := by
    simp only [post, emptyLocalsHOLFinite, hs3_eq]
    exact guestInv_congr (s := s2) rfl rfl rfl rfl hInv2.1.1
  have hbe_post : post.be = s2.be := by simp [post, emptyLocalsHOLFinite, hs3_eq]
  have hev_s2 : globN s2 "ev" = globN s "ev" := by simp [globN, hglob2, hglob1]
  have hcc_s2 : globN s2 "cur_cont" = globN s "cur_cont" := by simp [globN, hglob2, hglob1]
  have hmem_post2 : ∀ x : BitVec 64,
      (∀ addr ∈ headAllowedOffsets (globN s2 "ev") (globN s2 "cur_cont"), x ≠ BitVec.ofNat 64 addr) →
      post.memory x = s2.memory x := by
    intro x hx
    change s3.memory x = s2.memory x
    rw [hs3_eq]
    have hn32 : x ≠ BitVec.ofNat 64 (globN s2 "cur_cont" + 32) := hx _ (by simp [headAllowedOffsets])
    simp [updW, hn32]
  have hgas_post : memW post (globN s2 "ev" + 64) + memW post (globN s2 "ev" + 192) ≤
      memW s2 (globN s2 "ev" + 64) + memW s2 (globN s2 "ev" + 192) := by
    have hdisj_ec2 : Disj (globN s2 "ev", 280) (globN s2 "cur_cont", 104) := by
      obtain ⟨_, _, _, _, _, _, _, _, _, hP2, _⟩ := hInv2
      have hfl := List.pairwise_flatten.mp hP2
      have hmem0 : (globN s2 "ev", globN s2 "cur_cont") ∈ evmChain s2 := by simp [evmChain, evmChainFrom]
      have hp0 := hfl.1 _ (List.mem_map_of_mem hmem0)
      exact (List.pairwise_cons.mp (List.pairwise_append.mp hp0).1).1 _ (by simp)
    have hne64 : globN s2 "ev" + 64 ≠ globN s2 "cur_cont" + 32 := by
      unfold Disj at hdisj_ec2; dsimp only at hdisj_ec2
      rcases hdisj_ec2 with h | h | h | h <;> omega
    have hne192 : globN s2 "ev" + 192 ≠ globN s2 "cur_cont" + 32 := by
      unfold Disj at hdisj_ec2; dsimp only at hdisj_ec2
      rcases hdisj_ec2 with h | h | h | h <;> omega
    change memW s3 (globN s2 "ev" + 64) + memW s3 (globN s2 "ev" + 192) ≤ _
    rw [hs3_eq,
        memW_updW_ne s2 _ _ w32 (by omega) (by omega) hne64,
        memW_updW_ne s2 _ _ w32 (by omega) (by omega) hne192]
  obtain ⟨_, hch_post, _⟩ :=
    evmInv_of_head_status_gas_update hInv2 hGp_post (by simp [post, emptyLocalsHOLFinite, hs3_eq])
      hbe_post hmem_post2 hgas_post
  have hmem_all : ∀ x : BitVec 64,
      (∀ addr ∈ headAllowedOffsets (globN s "ev") (globN s "cur_cont"), x ≠ BitVec.ofNat 64 addr) →
      post.memory x = s.memory x := by
    intro x hx
    have hx2 : ∀ addr ∈ headAllowedOffsets (globN s2 "ev") (globN s2 "cur_cont"),
        x ≠ BitVec.ofNat 64 addr := by
      rw [hev_s2, hcc_s2]; exact hx
    exact (hmem_post2 x hx2).trans ((hmem2 x hx).trans (hmem1 x hx))
  have hstep_all : EvmStep [] s post := by
    refine ⟨hInv_full, ?_, ?_, hch_post.trans (hch2.trans hch1)⟩
    · simp [globN, hglob_post]
    · intro k _
      rw [hglob_post]
  exact ⟨hstep_all, hDone_full, hR_full, hmem_all,
    chain_cells_of_headAllowed hInv hmem_all, hW_full⟩

theorem ek_frame_exception : EvmKeeps EvmInv [] (ofString "frame_exception") := by
  refine ⟨[(ofString "err", .one)], sourceFnBody Guest.Software.guestFn_frame_exception, .one,
    lookup_frame_exception, ?_⟩
  intro F s hcode hInv hex _ hres
  obtain ⟨v, hv⟩ := frame_exception_resumes_returned s hcode (Classical.choose_spec hex) hres
  obtain ⟨w_err, hw_err⟩ := one_word_param_of_lookup lookup_frame_exception hex
  obtain ⟨w_emp, hw_emp⟩ := hInv.1.2.2.2.2.2.2.2.2.2 "evm_empty" (by decide)
  exact (frame_exception_exec_full s hcode hInv w_emp w_err hw_emp hw_err v hv).1

theorem frame_exception_chainCellsKept :
    ChainCellsKept EvmInv (ofString "frame_exception") := by
  refine ⟨[(ofString "err", .one)], sourceFnBody Guest.Software.guestFn_frame_exception, .one,
    lookup_frame_exception, ?_⟩
  intro F s hcode hInv hex _ hres
  obtain ⟨v, hv⟩ := frame_exception_resumes_returned s hcode (Classical.choose_spec hex) hres
  obtain ⟨w_err, hw_err⟩ := one_word_param_of_lookup lookup_frame_exception hex
  obtain ⟨w_emp, hw_emp⟩ := hInv.1.2.2.2.2.2.2.2.2.2 "evm_empty" (by decide)
  exact (frame_exception_exec_full s hcode hInv w_emp w_err hw_emp hw_err v hv).2.2.2.2.1

theorem frame_exception_keepsOn_headMemChainWF :
    KeepsOn (fun s => EvmInv s ∧ HeadMemChainWF s) HeadMemChainWF
      (ofString "frame_exception") := by
  refine ⟨[(ofString "err", .one)], sourceFnBody Guest.Software.guestFn_frame_exception, .one,
    lookup_frame_exception, ?_⟩
  intro F s hcode ⟨hInv, hW⟩ hex _ hres
  obtain ⟨v, hv⟩ := frame_exception_resumes_returned s hcode (Classical.choose_spec hex) hres
  obtain ⟨w_err, hw_err⟩ := one_word_param_of_lookup lookup_frame_exception hex
  obtain ⟨w_emp, hw_emp⟩ := hInv.1.2.2.2.2.2.2.2.2.2 "evm_empty" (by decide)
  exact (frame_exception_exec_full s hcode hInv w_emp w_err hw_emp hw_err v hv).2.2.2.2.2 hW

theorem frame_exception_aligned :
    FunSpec (fun s => EvmInv s ∧ HeadMemChainWF s)
      (fun s r post => Resumes r → EvmStep [] s post ∧ HeadMemChainWF post)
      (ofString "frame_exception") :=
  evmKeeps_aligned ek_frame_exception frame_exception_chainCellsKept (by decide) (by decide)

end FrameExceptionPreservation

section FramePrologueStartPreservation

open InitECandidate.Solver.Wave8GuestInv.R11Shards (updW store_global_off_word memW_updW_ne
  evm_head_globals headAllowedOffsets evmInv_of_head_status_gas_update)

abbrev frameStartGw : List String :=
  ["bn_expw", "bn_gamma", "heap_ptr", "journal_n", "scratch_ptr"]

structure FramePrologueCalleeSpecs : Prop where
  ek_move_ether :
    EvmKeeps (EvmAvoids FrameStartAvoids) frameStartGw (ofString "move_ether")
  cc_move_ether :
    ChainCellsKept (EvmAvoids FrameStartAvoids) (ofString "move_ether")
  ek_emit_transfer_log :
    EvmKeeps (EvmAvoids FrameStartAvoids) frameStartGw (ofString "emit_transfer_log")
  cc_emit_transfer_log :
    ChainCellsKept (EvmAvoids FrameStartAvoids) (ofString "emit_transfer_log")
  ek_run_precompile :
    EvmKeeps (EvmAvoids FrameStartAvoids) frameStartGw (ofString "run_precompile")
  cc_run_precompile :
    ChainCellsKept (EvmAvoids FrameStartAvoids) (ofString "run_precompile")

def ChainCellsAgree {F : Type} (s post : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ ec ∈ evmChain s,
    memW post (ec.1 + 24) = memW s (ec.1 + 24) ∧
    memW post (ec.1 + 32) = memW s (ec.1 + 32) ∧
    memW post (ec.1 + 40) = memW s (ec.1 + 40) ∧
    memW post (ec.2 + 56) = memW s (ec.2 + 56)

def EvmStepCC (gw : List String) {F : Type} (s post : PanSemStateFiniteExact 64 F) : Prop :=
  EvmStep gw s post ∧ ChainCellsAgree s post

private theorem chainCellsAgree_refl {F : Type} (s : PanSemStateFiniteExact 64 F) :
    ChainCellsAgree s s :=
  fun _ _ => ⟨rfl, rfl, rfl, rfl⟩

private theorem chainCellsAgree_trans {F : Type} {s mid post : PanSemStateFiniteExact 64 F}
    (h1 : ChainCellsAgree s mid) (hch : evmChain mid = evmChain s)
    (h2 : ChainCellsAgree mid post) :
    ChainCellsAgree s post := by
  intro ec hec
  obtain ⟨a1, b1, c1, d1⟩ := h1 ec hec
  obtain ⟨a2, b2, c2, d2⟩ := h2 ec (hch.symm ▸ hec)
  exact ⟨a2.trans a1, b2.trans b1, c2.trans c1, d2.trans d1⟩

private theorem evmStep_refl {gw : List String} {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s) : EvmStep gw s s :=
  ⟨hInv, le_rfl, fun _ _ => rfl, rfl⟩

private theorem evmStepCC_refl {gw : List String} {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s) : EvmStepCC gw s s :=
  ⟨evmStep_refl hInv, chainCellsAgree_refl s⟩

private theorem evmStep_trans {gw : List String} {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F}
    (h1 : EvmStep gw s mid) (h2 : EvmStep gw mid post) :
    EvmStep gw s post :=
  ⟨h2.1, le_trans h1.2.1 h2.2.1, fun k hk => (h1.2.2.1 k hk).trans (h2.2.2.1 k hk),
    h2.2.2.2.trans h1.2.2.2⟩

private theorem evmStepCC_trans {gw : List String} {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F}
    (h1 : EvmStepCC gw s mid) (h2 : EvmStepCC gw mid post) :
    EvmStepCC gw s post :=
  ⟨evmStep_trans h1.1 h2.1, chainCellsAgree_trans h1.2 h1.1.2.2.2 h2.2⟩

private theorem evmStep_mono_gw {gw1 gw2 : List String} {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hsub : ∀ k : MlS, k ∉ gw2.map ofString → k ∉ gw1.map ofString)
    (h : EvmStep gw1 s post) : EvmStep gw2 s post :=
  ⟨h.1, h.2.1, fun k hk => h.2.2.1 k (hsub k hk), h.2.2.2⟩

private theorem evmStepCC_mono_gw {gw1 gw2 : List String} {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hsub : ∀ k : MlS, k ∉ gw2.map ofString → k ∉ gw1.map ofString)
    (h : EvmStepCC gw1 s post) : EvmStepCC gw2 s post :=
  ⟨evmStep_mono_gw hsub h.1, h.2⟩

private theorem evmStepCC_with_locals_right {gw : List String} {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat)
    (h : EvmStepCC gw s post) :
    EvmStepCC gw s { post with locals := locals, clock := clock } := by
  refine ⟨⟨localsFree_evmInv post locals clock h.1.1, h.1.2.1, h.1.2.2.1,
    (evmChain_with_locals post locals clock).trans h.1.2.2.2⟩, ?_⟩
  exact h.2

private theorem evmStepCC_with_locals_left {gw : List String} {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat)
    (h : EvmStepCC gw { s with locals := locals, clock := clock } post) :
    EvmStepCC gw s post := by
  refine ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.trans (evmChain_with_locals s locals clock)⟩, ?_⟩
  intro ec hec
  exact h.2 ec ((evmChain_with_locals s locals clock).symm ▸ hec)

private theorem evmStepCC_of_state_eq_lc {gw : List String} {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s)
    (heq : post = { s with locals := post.locals, clock := post.clock }) :
    EvmStepCC gw s post := by
  rw [heq]
  exact evmStepCC_with_locals_right post.locals post.clock (evmStepCC_refl hInv)

private theorem evmInv_of_evmAvoids {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {F : Type} {s : PanSemStateFiniteExact 64 F} (h : EvmAvoids R s) : EvmInv s := by
  obtain ⟨hA, S, hI, _⟩ := h
  exact (evmInv_iff_at s).2 ⟨hA, S, hI⟩

def EvmProgStep (gw : List String) (prog : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    s.code = originalRuntimeCode → EvmInv s →
    (evaluateHOLFiniteState s prog).1 ≠ some .timeOut →
    FlowsOrResumes (evaluateHOLFiniteState s prog).1 →
    EvmStepCC gw s (evaluateHOLFiniteState s prog).2

private theorem flowsOrResumes_none : FlowsOrResumes (none : Option (PanSemResultExact 64)) :=
  Or.inl rfl

private theorem not_flowsOrResumes_error :
    ¬ FlowsOrResumes (some (.error : PanSemResultExact 64)) := by
  rintro (h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩) <;> cases h

private theorem EvmProgStep.of_readOnly {gw : List String} {prog : ProgHOL 64}
    (hro : ReadOnlyProg prog) : EvmProgStep gw prog := by
  intro F s hcode hInv hnt hfr
  exact evmStepCC_of_state_eq_lc hInv (hro s hcode hInv.1.1 hnt hfr)

private theorem EvmProgStep.skip {gw : List String} : EvmProgStep gw .skip :=
  EvmProgStep.of_readOnly ReadOnlyProg.skip

private theorem EvmProgStep.ret {gw : List String} (e : ExpHOL 64) : EvmProgStep gw (.return e) :=
  EvmProgStep.of_readOnly (ReadOnlyProg.ret e)

private theorem EvmProgStep.dec {gw : List String} (name : MlS) (shape : ShapeHOL)
    (init : ExpHOL 64) {body : ProgHOL 64} (hbody : EvmProgStep gw body) :
    EvmProgStep gw (.dec name shape init body) := by
  intro F s hcode hInv hnt hfr
  rw [evaluateHOLFiniteState_dec_total] at hnt hfr ⊢
  dsimp only at hnt hfr ⊢
  revert hnt hfr
  split <;> intro hnt hfr
  · exact absurd hfr not_flowsOrResumes_error
  · rename_i v hv
    by_cases hsh : shapeEqHOL shape (shapeOfHOLExact v) = true
    · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
      have hset : setVarHOLFinite name v s =
          { s with locals := (setVarHOLFinite name v s).locals, clock := s.clock } := by
        cases s; rfl
      have hInv' : EvmInv (setVarHOLFinite name v s) := by
        rw [hset]; exact localsFree_evmInv s _ _ hInv
      have hb := hbody (setVarHOLFinite name v s) hcode hInv' hnt hfr
      rw [hset] at hb
      have hb' := evmStepCC_with_locals_left _ _ hb
      exact evmStepCC_with_locals_right _ (evaluateHOLFiniteState (setVarHOLFinite name v s) body).2.clock hb'
    · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hfr
      exact absurd hfr not_flowsOrResumes_error

private theorem EvmProgStep.seq {gw : List String} {first second : ProgHOL 64}
    (h1 : EvmProgStep gw first) (h2 : EvmProgStep gw second) :
    EvmProgStep gw (.seq first second) := by
  intro F s hcode hInv hnt hfr
  have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata s first).1
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases hr1 : evaluateHOLFiniteState s first with ⟨r1, mid⟩
  simp only [hr1] at hmeta hnt hfr ⊢
  change mid.code = s.code at hmeta
  cases r1 with
  | none =>
    have hs1 := h1 s hcode hInv (by rw [hr1]; simp) (by rw [hr1]; exact flowsOrResumes_none)
    rw [hr1] at hs1
    dsimp only at hs1 hnt hfr ⊢
    exact evmStepCC_trans hs1 (h2 mid (hmeta.trans hcode) hs1.1.1 hnt hfr)
  | some r =>
    have hs1 := h1 s hcode hInv (by rw [hr1]; exact hnt) (by rw [hr1]; exact hfr)
    rw [hr1] at hs1
    exact hs1

private theorem EvmProgStep.ite {gw : List String} (cond : ExpHOL 64) {yes no : ProgHOL 64}
    (hyes : EvmProgStep gw yes) (hno : EvmProgStep gw no) :
    EvmProgStep gw (.ite cond yes no) := by
  intro F s hcode hInv hnt hfr
  rw [evaluateHOLFiniteState_ite] at hnt hfr ⊢
  revert hnt hfr
  split <;> intro hnt hfr
  · split at hnt
    · rename_i hz; simp only [hz, ↓reduceIte] at hfr ⊢; exact hno s hcode hInv hnt hfr
    · rename_i hz; simp only [hz, ↓reduceIte] at hfr ⊢; exact hyes s hcode hInv hnt hfr
  · exact absurd hfr not_flowsOrResumes_error

private theorem EvmProgStep.decCall_ro {gw : List String} {fname : MlS}
    (hf : ReadOnlyFn fname) (name : MlS) (shape : ShapeHOL) (args : List (ExpHOL 64))
    {cont : ProgHOL 64} (hcont : EvmProgStep gw cont) :
    EvmProgStep gw (.decCall name shape fname args cont) := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  intro F s hcode hInv hnt hfr
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · simp only [hargs] at hfr; exact absurd hfr not_flowsOrResumes_error
  · simp only [hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · simp only [hl] at hfr; exact absurd hfr not_flowsOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hfr ⊢
        have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
          ret ret' values callee (by rw [hcode]; exact hlook) hl
        subst hsame
        have hret_eq := lookupCodeHOLFinite_installed_return s fname params body' body'
          ret ret' values callee (by rw [hcode]; exact hlook) hl
        subst hret_eq
        have hentryEq : callEntryStateHOLFinite s callee =
            { s with locals := callee, clock := (callEntryStateHOLFinite s callee).clock } := by
          cases s; rfl
        have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup fname vs =
            some (body', (callEntryStateHOLFinite s callee).locals, ret') :=
          ⟨values, by simpa only [hcode, callEntryStateHOLFinite] using hl⟩
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        simp only [hrun] at hnt hfr ⊢
        cases res with
        | none => exact absurd hfr not_flowsOrResumes_error
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hnt hfr ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) shape &&
                shapeEqHOL (shapeOfHOLExact v) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
              have hro := hspec (callEntryStateHOLFinite s callee) hcode
                (guestInv_callEntry s callee hInv.1.1) hex
                (by rw [hrun]; simp) (by rw [hrun]; exact Or.inl ⟨v, rfl⟩)
              rw [hrun] at hro; dsimp only at hro
              have hpost : post = { s with locals := post.locals, clock := post.clock } :=
                state_trans_locals_clock hentryEq hro
              let cstate := setVarHOLFinite name v { post with locals := s.locals }
              have hcstateEq : cstate = { s with locals := cstate.locals, clock := cstate.clock } := by
                have h2 : cstate = { post with locals := cstate.locals, clock := post.clock } := by
                  cases post; rfl
                exact state_trans_locals_clock hpost h2
              have hcode_c : cstate.code = originalRuntimeCode := by
                rw [hcstateEq]; exact hcode
              have hInv_c : EvmInv cstate := by
                rw [hcstateEq]; exact localsFree_evmInv s _ _ hInv
              have hc : EvmStepCC gw cstate (evaluateHOLFiniteState cstate cont).2 :=
                hcont cstate hcode_c hInv_c hnt hfr
              have hc0 : EvmStepCC gw s (evaluateHOLFiniteState cstate cont).2 := by
                conv at hc => arg 2; rw [hcstateEq]
                exact evmStepCC_with_locals_left _ _ hc
              exact evmStepCC_with_locals_right _ (evaluateHOLFiniteState cstate cont).2.clock hc0
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hfr
              exact absurd hfr not_flowsOrResumes_error
          | exception e v =>
            dsimp only at hfr ⊢
            have hres : Resumes (some (.exception e v)) := by
              rcases hfr with h | h | h | hr <;> [simp at h; simp at h; simp at h; exact hr]
            have hro := hspec (callEntryStateHOLFinite s callee) hcode
              (guestInv_callEntry s callee hInv.1.1) hex
              (by rw [hrun]; simp) (by rw [hrun]; exact hres)
            rw [hrun] at hro; dsimp only at hro
            have hpost : post = { s with locals := post.locals, clock := post.clock } :=
              state_trans_locals_clock hentryEq hro
            have hemp : emptyLocalsHOLFinite post =
                { post with
                  locals := (emptyLocalsHOLFinite post).locals,
                  clock := (emptyLocalsHOLFinite post).clock } := by
              cases post; rfl
            exact evmStepCC_of_state_eq_lc hInv (state_trans_locals_clock hpost hemp)
          | timeOut => simp at hnt
          | _ => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h

private theorem EvmProgStep.call0 {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {gw : List String} {fname : MlS}
    (hEntry : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) callee k,
      EvmInv s → P { s with locals := callee, clock := k })
    (hk : EvmKeeps P gw fname) (hc : ChainCellsKept P fname)
    (args : List (ExpHOL 64)) :
    EvmProgStep gw (.call (some (none, none)) fname args) := by
  intro F s hcode hInv hnt hfr
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · simp only [hargs] at hfr; exact absurd hfr not_flowsOrResumes_error
  · simp only [hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · simp only [hl] at hfr; exact absurd hfr not_flowsOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hfr ⊢
        have hentryEq : callEntryStateHOLFinite s callee =
            { s with locals := callee, clock := (callEntryStateHOLFinite s callee).clock } := by
          cases s; rfl
        have hPc : P (callEntryStateHOLFinite s callee) := by
          rw [hentryEq]; exact hEntry s callee _ hInv
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        simp only [hrun] at hnt hfr ⊢
        have hAtPost (hsafe : res ≠ some .timeOut) (hres : Resumes res) :
            EvmStepCC gw s post := by
          have hst := FunSpec.at_lookup hk s hcode values body' callee ret' hl hPc
            (by rw [hrun]; exact hsafe)
          have hcc := FunSpec.at_lookup hc s hcode values body' callee ret' hl hPc
            (by rw [hrun]; exact hsafe)
          rw [hrun] at hst hcc
          have hboth : EvmStepCC gw (callEntryStateHOLFinite s callee) post :=
            ⟨hst hres, hcc hres⟩
          rw [hentryEq] at hboth
          exact evmStepCC_with_locals_left _ _ hboth
        cases res with
        | none => exact absurd hfr not_flowsOrResumes_error
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hfr ⊢
            by_cases hsh : shapeEqHOL (shapeOfHOLExact v) ret' = true
            · simp only [hsh, ↓reduceIte] at hfr ⊢
              exact evmStepCC_with_locals_right s.locals post.clock
                (hAtPost (by simp) (Or.inl ⟨v, rfl⟩))
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hfr
              exact absurd hfr not_flowsOrResumes_error
          | exception e v =>
            dsimp only at hfr ⊢
            have hres : Resumes (some (.exception e v)) := by
              rcases hfr with h | h | h | hr <;> [simp at h; simp at h; simp at h; exact hr]
            have hemp : emptyLocalsHOLFinite post =
                { post with locals := (emptyLocalsHOLFinite post).locals, clock := post.clock } := by
              cases post; rfl
            rw [hemp]
            exact evmStepCC_with_locals_right _ post.clock (hAtPost (by simp) hres)
          | timeOut => simp at hnt
          | _ => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h

private theorem EvmProgStep.call_handle_dest {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {gw : List String} {fname dest exn var : MlS} {handler : ProgHOL 64}
    (hexn : exn ≠ ofString "TrapErr")
    (hEntry : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) callee k,
      EvmInv s → P { s with locals := callee, clock := k })
    (hk : EvmKeeps P gw fname) (hc : ChainCellsKept P fname)
    (hh : EvmProgStep gw handler)
    (args : List (ExpHOL 64)) :
    EvmProgStep gw (.call (some (some (.local, dest), some (exn, var, handler))) fname args) := by
  intro F s hcode hInv hnt hfr
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · simp only [hargs] at hfr; exact absurd hfr not_flowsOrResumes_error
  · simp only [hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · simp only [hl] at hfr; exact absurd hfr not_flowsOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hfr ⊢
        have hentryEq : callEntryStateHOLFinite s callee =
            { s with locals := callee, clock := (callEntryStateHOLFinite s callee).clock } := by
          cases s; rfl
        have hPc : P (callEntryStateHOLFinite s callee) := by
          rw [hentryEq]; exact hEntry s callee _ hInv
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
          (callEntryStateHOLFinite s callee) body').1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        simp only [hrun] at hnt hfr hmeta ⊢
        change post.code = s.code at hmeta
        have hAtPost (hsafe : res ≠ some .timeOut) (hres : Resumes res) :
            EvmStepCC gw s post := by
          have hst := FunSpec.at_lookup hk s hcode values body' callee ret' hl hPc
            (by rw [hrun]; exact hsafe)
          have hcc := FunSpec.at_lookup hc s hcode values body' callee ret' hl hPc
            (by rw [hrun]; exact hsafe)
          rw [hrun] at hst hcc
          have hboth : EvmStepCC gw (callEntryStateHOLFinite s callee) post :=
            ⟨hst hres, hcc hres⟩
          rw [hentryEq] at hboth
          exact evmStepCC_with_locals_left _ _ hboth
        cases res with
        | none => exact absurd hfr not_flowsOrResumes_error
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hfr ⊢
            by_cases hsh : shapeEqHOL (shapeOfHOLExact v) ret' = true
            · simp only [hsh, ↓reduceIte] at hfr ⊢
              by_cases hv : isValidValueHOLExact s.toExact .local dest v = true
              · simp only [hv, ↓reduceIte] at hfr ⊢
                have hbase := hAtPost (by simp) (Or.inl ⟨v, rfl⟩)
                have hsetEq : setKvarHOLFinite .local dest v { post with locals := s.locals } =
                    { post with
                      locals := (setKvarHOLFinite .local dest v { post with locals := s.locals }).locals,
                      clock := post.clock } := by
                  cases post; rfl
                rw [hsetEq]
                exact evmStepCC_with_locals_right _ post.clock hbase
              · simp only [hv, Bool.false_eq_true, ↓reduceIte] at hfr
                exact absurd hfr not_flowsOrResumes_error
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hfr
              exact absurd hfr not_flowsOrResumes_error
          | exception eid v =>
            dsimp only at hnt hfr ⊢
            by_cases hid : eid = exn
            · subst hid
              simp only [↓reduceIte] at hnt hfr ⊢
              rcases hsh : s.eshapes.lookup eid with _ | shape
              · simp only [hsh] at hfr; exact absurd hfr not_flowsOrResumes_error
              · simp only [hsh] at hnt hfr ⊢
                by_cases hv : (shapeEqHOL (shapeOfHOLExact v) shape &&
                    isValidValueHOLExact s.toExact .local var v) = true
                · simp only [hv, ↓reduceIte] at hnt hfr ⊢
                  have hbase := hAtPost (by simp) (Or.inr ⟨eid, v, rfl, hexn⟩)
                  let hstate := setVarHOLFinite var v { post with locals := s.locals }
                  have hhstateEq : hstate =
                      { post with locals := hstate.locals, clock := post.clock } := by
                    cases post; rfl
                  have hbase' : EvmStepCC gw s hstate := by
                    rw [hhstateEq]
                    exact evmStepCC_with_locals_right _ post.clock hbase
                  have hcode_h : hstate.code = originalRuntimeCode := by
                    rw [hhstateEq]; exact hmeta.trans hcode
                  exact evmStepCC_trans hbase' (hh hstate hcode_h hbase'.1.1 hnt hfr)
                · simp only [hv, Bool.false_eq_true, ↓reduceIte] at hfr
                  exact absurd hfr not_flowsOrResumes_error
            · simp only [hid, ↓reduceIte] at hfr ⊢
              have hres : Resumes (some (.exception eid v)) := by
                rcases hfr with h | h | h | hr <;> [simp at h; simp at h; simp at h; exact hr]
              have hemp : emptyLocalsHOLFinite post =
                  { post with locals := (emptyLocalsHOLFinite post).locals, clock := post.clock } := by
                cases post; rfl
              rw [hemp]
              exact evmStepCC_with_locals_right _ post.clock (hAtPost (by simp) hres)
          | timeOut => simp at hnt
          | _ => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h

private theorem store_res_not_flowsOrResumes {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {dst val : ExpHOL 64} {res : PanSemResultExact 64}
    (h : evaluateHOLFiniteState s (.store dst val) = (some res, post)) :
    ¬ FlowsOrResumes (some res) := by
  have herr : res = .error := by
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
  subst herr
  exact not_flowsOrResumes_error

private theorem EvmProgStep.store_cur_cont_32_const {gw : List String} (c : BitVec 64) :
    EvmProgStep gw
      (.store (.op .add [.var .global (ofString "cur_cont"), .const (BitVec.ofNat 64 32)])
        (.const c)) := by
  intro F s _ hInv _ hfr
  rcases hrun : evaluateHOLFiniteState s
      (.store (.op .add [.var .global (ofString "cur_cont"), .const (BitVec.ofNat 64 32)])
        (.const c)) with ⟨r, post⟩
  simp only [hrun] at hfr ⊢
  cases r with
  | some res => exact absurd hfr (store_res_not_flowsOrResumes hrun)
  | none =>
    obtain ⟨_, hc_lt, _, ⟨ccw, hccw_lk, hccw_nat⟩, _⟩ := evm_head_globals hInv
    obtain ⟨w, _, hpost_eq⟩ := store_global_off_word (t := s) (post := post)
      (gname := "cur_cont") (gbase := globN s "cur_cont") (off := 32) hccw_lk hccw_nat (by omega)
      (fun v0 hv0 => by simp [evalHOLExact] at hv0; exact ⟨c, hv0.symm⟩) hrun
    have hGp : GuestInv post := by
      rw [hpost_eq]; exact guestInv_congr (s := s) rfl rfl rfl rfl hInv.1.1
    have hglob : post.globals = s.globals := by rw [hpost_eq]
    have hbe : post.be = s.be := by rw [hpost_eq]
    have hmem_out : ∀ x : BitVec 64,
        (∀ addr ∈ headAllowedOffsets (globN s "ev") (globN s "cur_cont"), x ≠ BitVec.ofNat 64 addr) →
        post.memory x = s.memory x := by
      intro x hx
      rw [hpost_eq]
      have hn32 : x ≠ BitVec.ofNat 64 (globN s "cur_cont" + 32) :=
        hx _ (by simp [headAllowedOffsets])
      simp [updW, hn32]
    have hdisj_ec : Disj (globN s "ev", 280) (globN s "cur_cont", 104) := by
      obtain ⟨_, _, _, _, _, _, _, _, _, hPs, _⟩ := hInv
      have hfl := List.pairwise_flatten.mp hPs
      have hmem0 : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
        simp [evmChain, evmChainFrom]
      have hp0 := hfl.1 _ (List.mem_map_of_mem hmem0)
      exact (List.pairwise_cons.mp (List.pairwise_append.mp hp0).1).1 _ (by simp)
    have hne64 : globN s "ev" + 64 ≠ globN s "cur_cont" + 32 := by
      unfold Disj at hdisj_ec; dsimp only at hdisj_ec
      rcases hdisj_ec with h | h | h | h <;> omega
    have hne192 : globN s "ev" + 192 ≠ globN s "cur_cont" + 32 := by
      unfold Disj at hdisj_ec; dsimp only at hdisj_ec
      rcases hdisj_ec with h | h | h | h <;> omega
    obtain ⟨he_lt, _, _, _, _⟩ := evm_head_globals hInv
    have hgas_le : memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) ≤
        memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192) := by
      rw [hpost_eq,
          memW_updW_ne s _ _ w (by omega) (by omega) hne64,
          memW_updW_ne s _ _ w (by omega) (by omega) hne192]
    obtain ⟨hEp, hch_eq, _⟩ :=
      evmInv_of_head_status_gas_update hInv hGp hglob hbe hmem_out hgas_le
    refine ⟨⟨hEp, ?_, fun k _ => by rw [hglob], hch_eq⟩,
      chain_cells_of_headAllowed hInv hmem_out⟩
    simp [globN, hglob]

private theorem entry_frameStartAvoids {F : Type} (s : PanSemStateFiniteExact 64 F)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (h : EvmInv s) :
    EvmAvoids FrameStartAvoids { s with locals := callee, clock := k } :=
  localsFree_evmAvoids_frameStart s callee k (evmAvoids_frameStart_of_evmInv s h)

private theorem entry_evmInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (h : EvmInv s) :
    EvmInv { s with locals := callee, clock := k } :=
  localsFree_evmInv s callee k h

theorem lookup_frame_prologue :
    originalRuntimeCode.lookup (ofString "frame_prologue") =
      some ([], sourceFnBody Guest.Software.guestFn_frame_prologue, .one) :=
  lookup_of_guestAst_getElem 580 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_frame_prologue) rfl

theorem lookup_frame_start :
    originalRuntimeCode.lookup (ofString "frame_start") =
      some ([], sourceFnBody Guest.Software.guestFn_frame_start, .one) :=
  lookup_of_guestAst_getElem 581 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_frame_start) rfl

private theorem frame_prologue_body_step (hcallees : FramePrologueCalleeSpecs) :
    EvmProgStep frameStartGw (sourceFnBody Guest.Software.guestFn_frame_prologue) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_frame_prologue,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  exact EvmProgStep.seq
    EvmProgStep.skip
    (EvmProgStep.dec _ _ _
      (EvmProgStep.seq
        (EvmProgStep.ite _
          (EvmProgStep.dec _ _ _
            (EvmProgStep.decCall_ro ro_u256_is_zero _ _ _
              (EvmProgStep.ite _
                (EvmProgStep.seq
                  (EvmProgStep.call0 entry_frameStartAvoids
                    hcallees.ek_move_ether hcallees.cc_move_ether _)
                  (EvmProgStep.decCall_ro ro_memeq _ _ _
                    (EvmProgStep.ite _
                      (EvmProgStep.call0 entry_frameStartAvoids
                        hcallees.ek_emit_transfer_log hcallees.cc_emit_transfer_log _)
                      EvmProgStep.skip)))
                EvmProgStep.skip)))
          EvmProgStep.skip)
        (EvmProgStep.dec _ _ _
          (EvmProgStep.seq
            (EvmProgStep.ite _
              (EvmProgStep.decCall_ro ro_precompile_index _ _ _
                (EvmProgStep.ite _
                  (EvmProgStep.seq
                    (EvmProgStep.ite _
                      (EvmProgStep.call0 entry_frameStartAvoids
                        hcallees.ek_run_precompile hcallees.cc_run_precompile _)
                      EvmProgStep.skip)
                    (EvmProgStep.ret _))
                  EvmProgStep.skip))
              EvmProgStep.skip)
            (EvmProgStep.seq
              EvmProgStep.skip
              (EvmProgStep.ret _))))))

theorem ek_frame_prologue_of_callees (hcallees : FramePrologueCalleeSpecs) :
    EvmKeeps (EvmAvoids FrameStartAvoids) frameStartGw (ofString "frame_prologue") := by
  refine ⟨[], sourceFnBody Guest.Software.guestFn_frame_prologue, .one,
    lookup_frame_prologue, ?_⟩
  intro F s hcode hP _ hnt hres
  exact (frame_prologue_body_step hcallees s hcode (evmInv_of_evmAvoids hP) hnt
    (Or.inr (Or.inr (Or.inr hres)))).1

theorem frame_prologue_chainCellsKept_of_callees (hcallees : FramePrologueCalleeSpecs) :
    ChainCellsKept (EvmAvoids FrameStartAvoids) (ofString "frame_prologue") := by
  refine ⟨[], sourceFnBody Guest.Software.guestFn_frame_prologue, .one,
    lookup_frame_prologue, ?_⟩
  intro F s hcode hP _ hnt hres
  exact (frame_prologue_body_step hcallees s hcode (evmInv_of_evmAvoids hP) hnt
    (Or.inr (Or.inr (Or.inr hres)))).2

theorem ek_frame_prologue_evmInv_of_callees (hcallees : FramePrologueCalleeSpecs) :
    EvmKeeps EvmInv frameStartGw (ofString "frame_prologue") := by
  refine ⟨[], sourceFnBody Guest.Software.guestFn_frame_prologue, .one,
    lookup_frame_prologue, ?_⟩
  intro F s hcode hInv _ hnt hres
  exact (frame_prologue_body_step hcallees s hcode hInv hnt
    (Or.inr (Or.inr (Or.inr hres)))).1

theorem frame_prologue_chainCellsKept_evmInv_of_callees (hcallees : FramePrologueCalleeSpecs) :
    ChainCellsKept EvmInv (ofString "frame_prologue") := by
  refine ⟨[], sourceFnBody Guest.Software.guestFn_frame_prologue, .one,
    lookup_frame_prologue, ?_⟩
  intro F s hcode hInv _ hnt hres
  exact (frame_prologue_body_step hcallees s hcode hInv hnt
    (Or.inr (Or.inr (Or.inr hres)))).2

private theorem ek_frame_exception_frameStartGw :
    EvmKeeps EvmInv frameStartGw (ofString "frame_exception") := by
  obtain ⟨ps, b, rt, hl, hrun⟩ := ek_frame_exception
  exact ⟨ps, b, rt, hl, fun s hcode hInv hex hnt hres =>
    evmStep_mono_gw (by intro k _; simp) (hrun s hcode hInv hex hnt hres)⟩

private theorem frame_start_body_step
    (hk_fp : EvmKeeps (EvmAvoids FrameStartAvoids) frameStartGw (ofString "frame_prologue"))
    (hc_fp : ChainCellsKept (EvmAvoids FrameStartAvoids) (ofString "frame_prologue")) :
    EvmProgStep frameStartGw (sourceFnBody Guest.Software.guestFn_frame_start) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_frame_start,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, Option.map]
  exact EvmProgStep.dec _ _ _
    (EvmProgStep.dec _ _ _
      (EvmProgStep.seq
        (EvmProgStep.call_handle_dest (by decide) entry_frameStartAvoids hk_fp hc_fp
          (EvmProgStep.call0 entry_evmInv ek_frame_exception_frameStartGw
            frame_exception_chainCellsKept _) _)
        (EvmProgStep.seq
          (EvmProgStep.ite _
            (EvmProgStep.store_cur_cont_32_const _)
            EvmProgStep.skip)
          (EvmProgStep.ret _))))

theorem ek_frame_start_of_frame_prologue
    (hk_fp : EvmKeeps (EvmAvoids FrameStartAvoids) frameStartGw (ofString "frame_prologue"))
    (hc_fp : ChainCellsKept (EvmAvoids FrameStartAvoids) (ofString "frame_prologue")) :
    EvmKeeps (EvmAvoids FrameStartAvoids) frameStartGw (ofString "frame_start") := by
  refine ⟨[], sourceFnBody Guest.Software.guestFn_frame_start, .one,
    lookup_frame_start, ?_⟩
  intro F s hcode hP _ hnt hres
  exact (frame_start_body_step hk_fp hc_fp s hcode (evmInv_of_evmAvoids hP) hnt
    (Or.inr (Or.inr (Or.inr hres)))).1

theorem frame_start_chainCellsKept_of_frame_prologue
    (hk_fp : EvmKeeps (EvmAvoids FrameStartAvoids) frameStartGw (ofString "frame_prologue"))
    (hc_fp : ChainCellsKept (EvmAvoids FrameStartAvoids) (ofString "frame_prologue")) :
    ChainCellsKept (EvmAvoids FrameStartAvoids) (ofString "frame_start") := by
  refine ⟨[], sourceFnBody Guest.Software.guestFn_frame_start, .one,
    lookup_frame_start, ?_⟩
  intro F s hcode hP _ hnt hres
  exact (frame_start_body_step hk_fp hc_fp s hcode (evmInv_of_evmAvoids hP) hnt
    (Or.inr (Or.inr (Or.inr hres)))).2

theorem frame_start_aligned_of_frame_prologue
    (hk_fp : EvmKeeps (EvmAvoids FrameStartAvoids) frameStartGw (ofString "frame_prologue"))
    (hc_fp : ChainCellsKept (EvmAvoids FrameStartAvoids) (ofString "frame_prologue")) :
    FunSpec (fun s => EvmAvoids FrameStartAvoids s ∧ HeadMemChainWF s)
      (fun s r post => Resumes r →
        EvmStep frameStartGw s post ∧ HeadMemChainWF post)
      (ofString "frame_start") :=
  evmKeeps_aligned (ek_frame_start_of_frame_prologue hk_fp hc_fp)
    (frame_start_chainCellsKept_of_frame_prologue hk_fp hc_fp)
    ev_not_mem_frameStart_gw fmp_not_mem_frameStart_gw

theorem ek_frame_start_of_callees (hcallees : FramePrologueCalleeSpecs) :
    EvmKeeps (EvmAvoids FrameStartAvoids) frameStartGw (ofString "frame_start") :=
  ek_frame_start_of_frame_prologue (ek_frame_prologue_of_callees hcallees)
    (frame_prologue_chainCellsKept_of_callees hcallees)

theorem frame_start_chainCellsKept_of_callees (hcallees : FramePrologueCalleeSpecs) :
    ChainCellsKept (EvmAvoids FrameStartAvoids) (ofString "frame_start") :=
  frame_start_chainCellsKept_of_frame_prologue (ek_frame_prologue_of_callees hcallees)
    (frame_prologue_chainCellsKept_of_callees hcallees)

theorem frame_start_keepsOn_headMemChainWF_of_callees (hcallees : FramePrologueCalleeSpecs) :
    KeepsOn (fun s => EvmAvoids FrameStartAvoids s ∧ HeadMemChainWF s) HeadMemChainWF
      (ofString "frame_start") := by
  obtain ⟨ps, b, rt, hl, hrun⟩ :=
    evmKeeps_aligned (ek_frame_start_of_callees hcallees)
      (frame_start_chainCellsKept_of_callees hcallees)
      ev_not_mem_frameStart_gw fmp_not_mem_frameStart_gw
  exact ⟨ps, b, rt, hl, fun s hcode hP hex hnt hr => (hrun s hcode hP hex hnt hr).2⟩

theorem frame_start_aligned_of_callees (hcallees : FramePrologueCalleeSpecs) :
    FunSpec (fun s => EvmAvoids FrameStartAvoids s ∧ HeadMemChainWF s)
      (fun s r post => Resumes r →
        EvmStep frameStartGw s post ∧ HeadMemChainWF post)
      (ofString "frame_start") :=
  evmKeeps_aligned (ek_frame_start_of_callees hcallees)
    (frame_start_chainCellsKept_of_callees hcallees)
    ev_not_mem_frameStart_gw fmp_not_mem_frameStart_gw

theorem ek_frame_start_evmInv_of_callees (hcallees : FramePrologueCalleeSpecs) :
    EvmKeeps EvmInv frameStartGw (ofString "frame_start") := by
  refine ⟨[], sourceFnBody Guest.Software.guestFn_frame_start, .one,
    lookup_frame_start, ?_⟩
  intro F s hcode hInv _ hnt hres
  exact (frame_start_body_step (ek_frame_prologue_of_callees hcallees)
    (frame_prologue_chainCellsKept_of_callees hcallees) s hcode hInv hnt
    (Or.inr (Or.inr (Or.inr hres)))).1

theorem frame_start_chainCellsKept_evmInv_of_callees (hcallees : FramePrologueCalleeSpecs) :
    ChainCellsKept EvmInv (ofString "frame_start") := by
  refine ⟨[], sourceFnBody Guest.Software.guestFn_frame_start, .one,
    lookup_frame_start, ?_⟩
  intro F s hcode hInv _ hnt hres
  exact (frame_start_body_step (ek_frame_prologue_of_callees hcallees)
    (frame_prologue_chainCellsKept_of_callees hcallees) s hcode hInv hnt
    (Or.inr (Or.inr (Or.inr hres)))).2

theorem frame_start_aligned_evmInv_of_callees (hcallees : FramePrologueCalleeSpecs) :
    FunSpec (fun s => EvmInv s ∧ HeadMemChainWF s)
      (fun s r post => Resumes r →
        EvmStep frameStartGw s post ∧ HeadMemChainWF post)
      (ofString "frame_start") :=
  evmKeeps_aligned (ek_frame_start_evmInv_of_callees hcallees)
    (frame_start_chainCellsKept_evmInv_of_callees hcallees)
    ev_not_mem_frameStart_gw fmp_not_mem_frameStart_gw

theorem frame_prologue_aligned_evmInv_of_callees (hcallees : FramePrologueCalleeSpecs) :
    FunSpec (fun s => EvmInv s ∧ HeadMemChainWF s)
      (fun s r post => Resumes r →
        EvmStep frameStartGw s post ∧ HeadMemChainWF post)
      (ofString "frame_prologue") :=
  evmKeeps_aligned (ek_frame_prologue_evmInv_of_callees hcallees)
    (frame_prologue_chainCellsKept_evmInv_of_callees hcallees)
    ev_not_mem_frameStart_gw fmp_not_mem_frameStart_gw

theorem frame_prologue_keepsOn_headMemChainWF_of_callees (hcallees : FramePrologueCalleeSpecs) :
    KeepsOn (fun s => EvmAvoids FrameStartAvoids s ∧ HeadMemChainWF s) HeadMemChainWF
      (ofString "frame_prologue") := by
  obtain ⟨ps, b, rt, hl, hrun⟩ :=
    evmKeeps_aligned (ek_frame_prologue_of_callees hcallees)
      (frame_prologue_chainCellsKept_of_callees hcallees)
      ev_not_mem_frameStart_gw fmp_not_mem_frameStart_gw
  exact ⟨ps, b, rt, hl, fun s hcode hP hex hnt hr => (hrun s hcode hP hex hnt hr).2⟩

theorem frame_prologue_aligned_of_callees (hcallees : FramePrologueCalleeSpecs) :
    FunSpec (fun s => EvmAvoids FrameStartAvoids s ∧ HeadMemChainWF s)
      (fun s r post => Resumes r →
        EvmStep frameStartGw s post ∧ HeadMemChainWF post)
      (ofString "frame_prologue") :=
  evmKeeps_aligned (ek_frame_prologue_of_callees hcallees)
    (frame_prologue_chainCellsKept_of_callees hcallees)
    ev_not_mem_frameStart_gw fmp_not_mem_frameStart_gw

end FramePrologueStartPreservation

theorem frame_prologue_aligned
    (hk : EvmKeeps (EvmAvoids FrameStartAvoids)
      ["bn_expw", "bn_gamma", "heap_ptr", "journal_n", "scratch_ptr"] (ofString "frame_prologue"))
    (hc : ChainCellsKept (EvmAvoids FrameStartAvoids) (ofString "frame_prologue")) :
    FunSpec (fun s => EvmAvoids FrameStartAvoids s ∧ HeadMemChainWF s)
      (fun s r post => Resumes r →
        EvmStep ["bn_expw", "bn_gamma", "heap_ptr", "journal_n", "scratch_ptr"] s post ∧
          HeadMemChainWF post) (ofString "frame_prologue") :=
  evmKeeps_aligned hk hc ev_not_mem_frameStart_gw fmp_not_mem_frameStart_gw

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFkPrologue
