import InitECandidate.Solver.Wave8GuestInv.ContractParts.C19
import InitECandidate.Solver.GuestTrapOutcomes

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

namespace R13PayloadStateInit

theorem lookup_state_init :
    originalRuntimeCode.lookup (ofString "state_init") =
      some ((sourceFunctionEntry Guest.Software.guestFn_state_init).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 354 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_state_init) rfl

theorem lookup_payload_header :
    originalRuntimeCode.lookup (ofString "payload_header") =
      some ((sourceFunctionEntry Guest.Software.guestFn_payload_header).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 864 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_payload_header) rfl

theorem lookup_alloc_fn :
    originalRuntimeCode.lookup (ofString "alloc") =
      some ((sourceFunctionEntry Guest.Software.guestFn_alloc).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_alloc) rfl

theorem lookup_memzero_fn :
    originalRuntimeCode.lookup (ofString "memzero") =
      some ((sourceFunctionEntry Guest.Software.guestFn_memzero).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 17 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memzero) rfl

theorem lookup_keccak256_fn :
    originalRuntimeCode.lookup (ofString "keccak256") =
      some ((sourceFunctionEntry Guest.Software.guestFn_keccak256).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 103 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_keccak256) rfl

theorem lookup_build_mpt_indexed_fn :
    originalRuntimeCode.lookup (ofString "build_mpt_indexed") =
      some ((sourceFunctionEntry Guest.Software.guestFn_build_mpt_indexed).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 292 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_build_mpt_indexed) rfl

theorem lookup_encode_withdrawal_rlp_fn :
    originalRuntimeCode.lookup (ofString "encode_withdrawal_rlp") =
      some ((sourceFunctionEntry Guest.Software.guestFn_encode_withdrawal_rlp).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 838 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_encode_withdrawal_rlp) rfl

theorem lookup_block_rlp_length_fn :
    originalRuntimeCode.lookup (ofString "block_rlp_length") =
      some ((sourceFunctionEntry Guest.Software.guestFn_block_rlp_length).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 862 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_block_rlp_length) rfl

theorem arenaReady_setGlobal_ne {F : Type} {s : PanSemStateFiniteExact 64 F}
    {gname : MlS} {w : BitVec 64}
    (hne1 : gname ≠ ofString "heap_ptr")
    (hne2 : gname ≠ ofString "frame_mem_ptr")
    (hne3 : gname ≠ ofString "scratch_ptr")
    (hA : ArenaReady s) :
    ArenaReady (setGlobalHOLFinite gname (.val (.word w)) s) := by
  refine ⟨guestInv_congr (s := s) rfl rfl rfl rfl hA.1, ?_⟩
  have h1 : globN (setGlobalHOLFinite gname (.val (.word w)) s) "heap_ptr" = globN s "heap_ptr" := by
    simp [globN, setGlobalHOLFinite, HolFiniteMapExact.update, FUPDATE, hne1]
  have h2 : globN (setGlobalHOLFinite gname (.val (.word w)) s) "frame_mem_ptr" = globN s "frame_mem_ptr" := by
    simp [globN, setGlobalHOLFinite, HolFiniteMapExact.update, FUPDATE, hne2]
  have h3 : globN (setGlobalHOLFinite gname (.val (.word w)) s) "scratch_ptr" = globN s "scratch_ptr" := by
    simp [globN, setGlobalHOLFinite, HolFiniteMapExact.update, FUPDATE, hne3]
  obtain ⟨ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, hgw⟩ := hA.2
  unfold ArenaOK
  rw [h1, h2, h3]
  exact ⟨ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, globalsWord_update gname w rfl hgw⟩

theorem arenaReady_store (dst src : ExpHOL 64) :
    Hoare ArenaReady (.store dst src) (fun r t => r = none → ArenaReady t) := by
  refine ⟨fun {F} s _ hA _ hr => ?_⟩
  rw [evaluateHOLFiniteState_store] at hr ⊢
  revert hr
  split
  · split
    · split
      · intro _; exact ⟨guestInv_congr (s := s) rfl rfl rfl rfl hA.1, hA.2⟩
      · simp
    · simp
  · simp

theorem hoare_call_global_alloc_arenaReady
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc"))
    (gname : MlS) (args : List (ExpHOL 64))
    (hne1 : gname ≠ ofString "heap_ptr")
    (hne2 : gname ≠ ofString "frame_mem_ptr")
    (hne3 : gname ≠ ofString "scratch_ptr") :
    Hoare ArenaReady
      (.call (some (some (.global, gname), none)) (ofString "alloc") args)
      (fun r t => r = none → ArenaReady t) := by
  refine ⟨fun {F} state hcode hA _ hr => ?_⟩
  rcases hcall : evaluateHOLFiniteState state
      (.call (some (some (.global, gname), none)) (ofString "alloc") args) with ⟨cres, cpost⟩
  have hr' : cres = none := by rw [hcall] at hr; exact hr
  subst hr'
  show ArenaReady cpost
  rw [evaluateHOLFiniteState_call] at hcall
  rcases hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) args with _ | values
  · rw [hargs] at hcall; simp at hcall
  · rw [hargs] at hcall; dsimp only at hcall
    rcases hl : lookupCodeHOLFinite state.code.lookup (ofString "alloc") values with _ | ⟨body, callee, ret⟩
    · rw [hl] at hcall; simp at hcall
    · rw [hl] at hcall; dsimp only at hcall
      by_cases hz : state.clock = 0
      · rw [if_pos hz] at hcall; simp at hcall
      · rw [if_neg hz] at hcall
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with ⟨bres, post⟩
        rw [hrun] at hcall
        cases bres with
        | none => simp at hcall
        | some br =>
          cases br with
          | returned v =>
            dsimp only at hcall
            by_cases hsh : shapeEqHOL (shapeOfHOLExact v) ret = true
            · rw [if_pos hsh] at hcall
              by_cases hv : isValidValueHOLExact state.toExact .global gname v = true
              · rw [if_pos hv] at hcall
                obtain ⟨_, hpost_eq⟩ := Prod.mk.inj hcall
                rw [← hpost_eq]
                have hrt := FunSpec.at_lookup rtal state hcode values body callee ret hl
                  (localsFree_arenaReady state callee (state.clock - 1) hA)
                  (by rw [hrun]; simp)
                rw [hrun] at hrt
                dsimp only at hrt
                obtain ⟨_, rfl, hAp, _, _⟩ := hrt v rfl
                exact localsFree_arenaReady _ state.locals post.clock
                  (arenaReady_setGlobal_ne hne1 hne2 hne3 hAp)
              · rw [if_neg hv] at hcall; simp at hcall
            · rw [if_neg hsh] at hcall; simp at hcall
          | _ => simp at hcall

end R13PayloadStateInit

namespace R13Shards

theorem gbody_state_init : GBody.«state_init» := by
  intro hal hdw hhn _wal rtal
  refine TerminatingFunBoundedOn.mono ?_ (fun _ hW => hW.1)
  refine ⟨_, _, _, R13PayloadStateInit.lookup_state_init, ?_⟩
  simp only [InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.seq_hoare
      (TerminatingProgBoundedOn.call_on hal _ _
        (callEntryOn_of_imp localsFree_guestInv arenaReady_guestInv _ _))
      (R13PayloadStateInit.hoare_call_global_alloc_arenaReady rtal (ofString "ws") _
        (by decide) (by decide) (by decide))
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
        (R13PayloadStateInit.arenaReady_store _ _)
        (TerminatingProgBoundedOn.seq_hoare
          (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
          (R13PayloadStateInit.arenaReady_store _ _)
          (TerminatingProgBoundedOn.seq_hoare
            (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
            (R13PayloadStateInit.arenaReady_store _ _)
            (TerminatingProgBoundedOn.decCall_on hdw _ _ _
              (callEntryOn_of_localsFree localsFree_arenaReady _ _)
              (decCallResumeOn_guestInv arenaReady_guestInv _ _ _)
              (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                (TerminatingProgBoundedOn.decCall_guestInv hhn _ _ _
                  (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                    (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hal _ _)
                      (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                        (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hhn _ _)
                          (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                            (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hhn _ _)
                              (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hhn _ _)
                                  (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                    (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hhn _ _)
                                      (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                        (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hhn _ _)
                                          (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                            (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hhn _ _)
                                              (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                                (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                                  (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                                    (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hhn _ _)
                                                      (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                                        (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hal _ _)
                                                          (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
                                                            (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hal _ _)
                                                              (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
                                                                (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
                                                                  (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _))))))))))))))))))))))))))))))))) ?_
  unfold K.«state_init»; omega

end R13Shards

end InitECandidate.Solver.Wave8GuestInv
