import InitECandidate.Solver.Wave8GuestInv.R16Shards.GbodyC17ToC21Common
import InitECandidate.Solver.Wave8GuestInv.ContractParts.C19

/-! Zero-sorry proof of `gbody_state_init` (`ContractParts/C19.lean`). -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16Shards.GbodyC17ToC21Common

theorem lookup_state_init_fn :
    originalRuntimeCode.lookup (ofString "state_init") =
      some ((sourceFunctionEntry Guest.Software.guestFn_state_init).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 354 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_state_init) rfl

theorem globN_setGlobal_ne_si {F : Type} (s : PanSemStateFiniteExact 64 F)
    (g : MlS) (v : ValueHOL 64) (n : String) (hne : ofString n ≠ g) :
    globN (setGlobalHOLFinite g v s) n = globN s n := by
  have hl : (s.globals.update (g, v)).lookup (ofString n) = s.globals.lookup (ofString n) := by
    simp [HolFiniteMapExact.update, FUPDATE, Ne.symm hne]
  simp only [globN, setGlobalHOLFinite, hl]

theorem arenaReady_setGlobal_word_ne_si {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : ArenaReady s) (g : MlS) (w : BitVec 64)
    (h1 : ofString "heap_ptr" ≠ g) (h2 : ofString "frame_mem_ptr" ≠ g)
    (h3 : ofString "scratch_ptr" ≠ g) :
    ArenaReady (setGlobalHOLFinite g (.val (.word w)) s) := by
  refine ⟨guestInv_congr (s := s) rfl rfl rfl rfl h.1, ?_⟩
  have hgw : GlobalsWord (setGlobalHOLFinite g (.val (.word w)) s) :=
    globalsWord_update g w rfl h.2.2.2.2.2.2.2.2.2
  unfold ArenaOK
  rw [globN_setGlobal_ne_si s g (.val (.word w)) "heap_ptr" h1,
      globN_setGlobal_ne_si s g (.val (.word w)) "frame_mem_ptr" h2,
      globN_setGlobal_ne_si s g (.val (.word w)) "scratch_ptr" h3]
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, hgw⟩

theorem Hoare.callDest_fall_si {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop}
    {kind : VarKind} {dest fname : MlS} {arguments : List (ExpHOL 64)}
    (hf : FunSpec Pc Qc fname) (hentry : CallEntryOn P Pc fname arguments)
    (hret : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (post : PanSemStateFiniteExact 64 F)
      (v : ValueHOL 64), s.code = originalRuntimeCode → P s →
      Qc (callEntryStateHOLFinite s callee) (some (.returned v)) post →
      Q (setKvarHOLFinite kind dest v { post with locals := s.locals })) :
    Hoare P (.call (some (some (kind, dest), none)) fname arguments)
      (fun r t => r = none → Q t) := by
  refine ⟨fun {F} s hcode hP hnt => ?_⟩
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite s
      (h := fun address => Classical.propDecidable (s.memaddrs address)) arguments with
    _ | values
  · simp
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · simp
    · simp only [hl] at hnt ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hPc := hentry s values body' callee ret' hcode hP hargs hl
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with
          ⟨res, post⟩
        simp only [hrun] at hnt ⊢
        cases res with
        | none => simp
        | some r =>
          cases r with
          | returned v =>
            have hQc : Qc (callEntryStateHOLFinite s callee) (some (.returned v)) post := by
              have := FunSpec.at_lookup hf s hcode values body' callee ret' hl hPc (by rw [hrun]; simp)
              rw [hrun] at this; exact this
            dsimp only
            split
            · split
              · intro _
                exact hret s callee post v hcode hP hQc
              · simp
            · simp
          | _ => simp

theorem hoare_store_arenaReady_si (dst src : ExpHOL 64) :
    Hoare ArenaReady (.store dst src) (fun r t => r = none → ArenaReady t) :=
  Hoare.store_fall fun s _ _ _ hA _ _ _ => ⟨guestInv_congr (s := s) rfl rfl rfl rfl hA.1, hA.2⟩

theorem «gbody_state_init» : GBody.«state_init» := by
  intro hal hdwtm hhn _wal rtal
  refine ⟨_, _, _, lookup_state_init_fn, ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_state_init,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  have hws_alloc : Hoare WorldOK
      (.call (some (some (.global, ofString "ws"), none)) (ofString "alloc") [.const 40#64])
      (fun r t => r = none → ArenaReady t) :=
    Hoare.callDest_fall_si rtal
      (callEntryOn_of_imp localsFree_arenaReady (fun _ h => h.1) _ _)
      (fun s _ post v _ _ hrt => by
        obtain ⟨w, rfl, hAp, _⟩ := hrt v rfl
        exact arenaReady_setGlobal_word_ne_si
          (localsFree_arenaReady post s.locals post.clock hAp)
          (ofString "ws") w (by decide) (by decide) (by decide))
  apply TerminatingProgBoundedOn.mono_bound
  · exact TerminatingProgBoundedOn.seq_hoare_trans
      (TerminatingProgBoundedOn.call_on hal _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
      hws_alloc
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _)) (hoare_store_arenaReady_si _ _)
        (TerminatingProgBoundedOn.seq_hoare
          (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _)) (hoare_store_arenaReady_si _ _)
          (TerminatingProgBoundedOn.seq_hoare
            (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _)) (hoare_store_arenaReady_si _ _)
            (TerminatingProgBoundedOn.decCall_on hdwtm _ _ _
              (callEntryOn_of_localsFree localsFree_arenaReady _ _)
              (decCallResumeOn_guestInv arenaReady_guestInv _ _ _)
              (TerminatingProgBoundedOn.seq_guestInv
                (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                (TerminatingProgBoundedOn.decCall_guestInv hhn _ _ _
                  (TerminatingProgBoundedOn.seq_guestInv
                    (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                    (TerminatingProgBoundedOn.seq_guestInv
                      (TerminatingProgBoundedOn.call_guestInv hal _ _)
                      (TerminatingProgBoundedOn.seq_guestInv
                        (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                        (TerminatingProgBoundedOn.seq_guestInv
                          (TerminatingProgBoundedOn.call_guestInv hhn _ _)
                          (TerminatingProgBoundedOn.seq_guestInv
                            (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                            (TerminatingProgBoundedOn.seq_guestInv
                              (TerminatingProgBoundedOn.call_guestInv hhn _ _)
                              (TerminatingProgBoundedOn.seq_guestInv
                                (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                (TerminatingProgBoundedOn.seq_guestInv
                                  (TerminatingProgBoundedOn.call_guestInv hhn _ _)
                                  (TerminatingProgBoundedOn.seq_guestInv
                                    (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                    (TerminatingProgBoundedOn.seq_guestInv
                                      (TerminatingProgBoundedOn.call_guestInv hhn _ _)
                                      (TerminatingProgBoundedOn.seq_guestInv
                                        (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                        (TerminatingProgBoundedOn.seq_guestInv
                                          (TerminatingProgBoundedOn.call_guestInv hhn _ _)
                                          (TerminatingProgBoundedOn.seq_guestInv
                                            (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                            (TerminatingProgBoundedOn.seq_guestInv
                                              (TerminatingProgBoundedOn.call_guestInv hhn _ _)
                                              (TerminatingProgBoundedOn.seq_guestInv
                                                (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                                (TerminatingProgBoundedOn.seq_guestInv
                                                  (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                                  (TerminatingProgBoundedOn.seq_guestInv
                                                    (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                                    (TerminatingProgBoundedOn.seq_guestInv
                                                      (TerminatingProgBoundedOn.call_guestInv hhn _ _)
                                                      (TerminatingProgBoundedOn.seq_guestInv
                                                        (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                                        (TerminatingProgBoundedOn.seq_guestInv
                                                          (TerminatingProgBoundedOn.call_guestInv hal _ _)
                                                          (TerminatingProgBoundedOn.seq_guestInv
                                                            (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
                                                            (TerminatingProgBoundedOn.seq_guestInv
                                                              (TerminatingProgBoundedOn.call_guestInv hal _ _)
                                                              (TerminatingProgBoundedOn.seq_guestInv
                                                                (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
                                                                (TerminatingProgBoundedOn.seq_guestInv
                                                                  (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
                                                                  (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _))))))))))))))))))))))))))))))))
  · unfold K.«state_init»; omega

end InitECandidate.Solver.Wave8GuestInv.R16Shards
