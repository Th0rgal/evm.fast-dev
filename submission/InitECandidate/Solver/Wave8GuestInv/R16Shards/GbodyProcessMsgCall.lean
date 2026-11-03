import InitECandidate.Solver.Wave8GuestInv.R16Shards.GbodyC17ToC21Common
import InitECandidate.Solver.Wave8GuestInv.ContractParts.C17

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000
set_option exponentiation.threshold 2000

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

/-! ## 5. Proof 1: `gbody_process_message_call` -/

def MsgReadyWithOut : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_out : BitVec 64, ∃ S Nd : List Nat,
    MsgReadyAt s S Nd ∧
    s.locals.lookup (ofString "out") = some (.val (.word w_out)) ∧
    Disj (w_out.toNat, 96) (locN s "msg", 176) ∧
    IvlsDisj [(w_out.toNat, 96)] (worldTypedIvls s S Nd)

theorem msgReadyWithOut_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : MsgReadyWithOut s) : GuestInv s := by
  obtain ⟨_, _, _, hM, _⟩ := h
  exact hM.1.1

theorem resumeOn_alloc96_msgReady
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc")) :
    DecCallResumeOn MsgReady MsgReadyWithOut (ofString "out") (ofString "alloc") [.const 96#64] := by
  intro F state values body callee ret value post hcode hM hargs hl hrun
  obtain ⟨S, Nd, hMA⟩ := msgReadyAt_of_msgReady hM
  have hpc := callee_param_one_exp state (ofString "alloc") (ofString "n") .one _ _
    (by rw [hcode]; exact lookup_alloc_fn) (.const 96#64) (.val (.word 96#64)) values body callee ret rfl hargs hl
  have hn_loc : locN (callEntryStateHOLFinite state callee) "n" = 96 := by
    simp [locN, callEntryStateHOLFinite, hpc.2]
  have hstep := FunSpec.at_lookup wal state hcode values body callee ret hl
    (localsFree_worldOK state callee (state.clock - 1) (msgReady_worldOK state hM))
    (by rw [hrun]; simp)
  rw [hrun] at hstep
  dsimp only at hstep
  have hws := hstep (Or.inl ⟨value, rfl⟩)
  have hrt := FunSpec.at_lookup rtal state hcode values body callee ret hl
    (localsFree_arenaReady state callee (state.clock - 1) hM.1)
    (by rw [hrun]; simp)
  rw [hrun] at hrt
  dsimp only at hrt
  obtain ⟨w_out, rfl, _, _, hfb⟩ := hrt value rfl
  rw [hn_loc] at hfb
  have hws_caller : WorldStep (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (fun _ r' post' S' Nd' => ∀ v', r' = some (.returned v') → ∃ w : BitVec 64,
        v' = .val (.word w) ∧ IvlsDisj [(w.toNat, 96)] (worldOwned post' S' Nd'))
      state (some (.returned (.val (.word w_out)))) post := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hws
    refine ⟨h1, h2, h3, h4, fun S_x Nd_x hW_x _ => ?_⟩
    obtain ⟨S_x', Nd_x', hsub_x, hW_x', hog_x, hfr_x, hQ_x⟩ :=
      h5 S_x Nd_x ((worldTypedWith_with_locals _ _ _ _ _).2 hW_x) (fun x hx => by simp at hx)
    refine ⟨S_x', Nd_x', hsub_x, hW_x', hog_x, hfr_x, fun v' hv' => ?_⟩
    obtain ⟨w, hw_eq, hav⟩ := hQ_x v' hv'
    dsimp only at hav
    rw [hn_loc] at hav
    exact ⟨w, hw_eq, hav⟩
  obtain ⟨S0', Nd_post, hMA_post, hQ0, hfp_eq⟩ :=
    WorldStep.preserves_msgReadyAt hMA hws_caller (fun j hj => by simp at hj) (fun x hx => by simp at hx)
  obtain ⟨w_out', hw_eq, hav0⟩ := hQ0 (.val (.word w_out)) rfl
  injection hw_eq with hw_eq'
  injection hw_eq' with hw_eq''
  subst hw_eq''
  set resumed := setVarHOLFinite (ofString "out") (.val (.word w_out)) { post with locals := state.locals }
  have hout_ne_msg : ofString "out" ≠ ofString "msg" := by decide
  have hMA_res : MsgReadyAt resumed (S0' ++ [memW state (locN state "msg" + 152), memW state (locN state "msg" + 160)]) Nd_post :=
    msgReadyAt_with_locals (s := { post with locals := state.locals })
      (by simp [HolFiniteMapExact.update, FUPDATE, hout_ne_msg]) hMA_post
  have hm_loc_eq : locN resumed "msg" = locN state "msg" := by
    rw [locN_setVar_ne _ "msg" (ofString "out") _ (by decide)]
    rfl
  have hm_in_s : Inside (locN state "msg", 176) sourceBase (globN state "heap_ptr") :=
    hMA.2.2.2.2.2.2.2.2.2.2.1
  have hout_disj_m : Disj (w_out.toNat, 96) (locN state "msg", 176) :=
    Or.inr (Or.inr (Or.inr (Nat.le_trans hm_in_s.2 hfb.2.1.1)))
  refine ⟨w_out, S0' ++ [memW state (locN state "msg" + 152), memW state (locN state "msg" + 160)], Nd_post,
    hMA_res, ?_, ?_, ?_⟩
  · simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · rw [hm_loc_eq]; exact hout_disj_m
  · intro x hx j hj
    simp only [List.mem_singleton] at hx; subst hx
    have hj_ow : j ∈ worldOwned post (S0' ++ [memW state (locN state "msg" + 152), memW state (locN state "msg" + 160)]) Nd_post :=
      worldTypedIvls_sub_worldOwned _ _ _ j hj
    unfold worldOwned at hj_ow
    rcases List.mem_append.1 hj_ow with h1 | hnd
    · rcases List.mem_append.1 h1 with htab | hfix
      · rw [List.flatMap_append] at htab
        rcases List.mem_append.1 htab with htab0 | htab_loc
        · apply hav0 (w_out.toNat, 96) (by simp) j
          unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl htab0)))
        · obtain ⟨u, hu_loc, hj_fp⟩ := List.mem_flatMap.1 htab_loc
          rw [hfp_eq u hu_loc] at hj_fp
          have hu_S : u ∈ S := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_loc
            rcases hu_loc with rfl | rfl
            · exact hMA.2.2.1
            · exact hMA.2.2.2.1
          have hal_j : Allocated state j := ((hMA.2.1.1.2.1 u hu_S).2 j hj_fp).1
          have hsep : heapLimit ≤ scratchStart := by decide
          obtain ⟨_, h1_s, h2_s, h3_s, _⟩ := hMA.1.2
          obtain ⟨_, hp1, _⟩ := hws.1.2
          have hfb_in : Inside (w_out.toNat, 96) (globN state "heap_ptr") (globN post "heap_ptr") := hfb.2.1
          rcases hal_j with ⟨_, hhi_j⟩ | ⟨hlo_j, _⟩
          · exact Or.inr (Or.inr (Or.inr (Nat.le_trans hhi_j hfb_in.1)))
          · exact Or.inr (Or.inr (Or.inl (by unfold Inside at hfb_in; omega)))
      · apply hav0 (w_out.toNat, 96) (by simp) j
        unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))
    · apply hav0 (w_out.toNat, 96) (by simp) j
      unfold worldOwned; exact List.mem_append.2 (Or.inr hnd)

theorem hoare_memzero96_msgReady
    (wmz : WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")]) []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "memzero")) :
    Hoare MsgReadyWithOut
      (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "out"), .const 96#64])
      (fun r t => r = none → MsgReady t) := by
  refine ⟨fun {F} state hcode hMW _ hr => ?_⟩
  rcases hcall : evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "out"), .const 96#64]) with ⟨cres, cpost⟩
  have hr' : cres = none := by rw [hcall] at hr; exact hr
  subst hr'
  show MsgReady cpost
  obtain ⟨w_out, S, Nd, hMA, hout_lu, hout_dm, hout_dti⟩ := hMW
  rw [evaluateHOLFiniteState_call] at hcall
  have hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "out"), .const 96#64] = some [.val (.word w_out), .val (.word 96#64)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact, evalHOLExact, hout_lu]
  rw [hargs] at hcall
  dsimp only at hcall
  rcases hl : lookupCodeHOLFinite state.code.lookup (ofString "memzero")
      [.val (.word w_out), .val (.word 96#64)] with _ | ⟨body, callee, ret⟩
  · rw [hl] at hcall; simp at hcall
  · rw [hl] at hcall
    dsimp only at hcall
    by_cases hz : state.clock = 0
    · rw [if_pos hz] at hcall; simp at hcall
    · rw [if_neg hz] at hcall
      have hp2 := callee_param_two state (ofString "memzero") (ofString "dst") (ofString "n") .one .one _ _
        (by rw [hcode]; exact lookup_memzero_fn)
        (.var .local (ofString "out")) (.const 96#64) (.val (.word w_out)) (.val (.word 96#64))
        [.val (.word w_out), .val (.word 96#64)] body callee ret
        (by simp [evalAt, evalHOLExact, hout_lu]) rfl hargs hl
      have hdst : locN (callEntryStateHOLFinite state callee) "dst" = w_out.toNat := by
        simp [locN, callEntryStateHOLFinite, hp2.2.1]
      have hn : locN (callEntryStateHOLFinite state callee) "n" = 96 := by
        simp [locN, callEntryStateHOLFinite, hp2.2.2]
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
            obtain ⟨_, rfl⟩ := Prod.mk.inj hcall
            have hstep := FunSpec.at_lookup wmz state hcode _ body callee ret hl
              (localsFree_worldOK state callee (state.clock - 1) (msgReady_worldOK state (msgReadyAt_msgReady hMA)))
              (by rw [hrun]; simp)
            rw [hrun] at hstep
            dsimp only at hstep
            have hws := hstep (Or.inl ⟨v, rfl⟩)
            have hws_caller : WorldStep (fun _ => [(w_out.toNat, 96)]) []
                [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
                 ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
                NoExtra state (some (.returned v)) post := by
              obtain ⟨h1, h2, h3, h4, h5⟩ := hws
              refine ⟨h1, h2, h3, ?_, fun S_x Nd_x hW_x hD_x => ?_⟩
              · intro r_k hr_k hgnz k hk hnc
                apply h4 r_k hr_k hgnz k hk
                dsimp only
                rw [hdst, hn]; exact hnc
              · have h5' := h5 S_x Nd_x ((worldTypedWith_with_locals _ _ _ _ _).2 hW_x)
                  (by dsimp only; rw [hdst, hn]; exact hD_x)
                dsimp only at h5'
                rw [hdst, hn] at h5'
                exact h5'
            obtain ⟨_, _, hMA_post, _, _⟩ :=
              WorldStep.preserves_msgReadyAt hMA hws_caller
                (fun j hj => by simp at hj; subst hj; omega)
                (fun x hx j hj => by
                  simp only [List.mem_singleton] at hx; subst hx
                  rcases List.mem_cons.1 hj with rfl | hj_ti
                  · exact hout_dm
                  · exact hout_dti (w_out.toNat, 96) (by simp) j hj_ti)
            exact msgReadyAt_msgReady hMA_post
          · rw [if_neg hsh] at hcall; simp at hcall
        | _ => simp at hcall

theorem resumeOn_account_deployable_msgReady
    (wad : WorldKeeps WorldOK
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "account_deployable"))
    (args : List (ExpHOL 64)) :
    DecCallResumeOn MsgReady MsgReady (ofString "dep") (ofString "account_deployable") args := by
  intro F state values body callee ret value post hcode hM _ hl hrun
  obtain ⟨S, Nd, hMA⟩ := msgReadyAt_of_msgReady hM
  have hstep := FunSpec.at_lookup wad state hcode values body callee ret hl
    (localsFree_worldOK state callee (state.clock - 1) (msgReady_worldOK state hM))
    (by rw [hrun]; simp)
  rw [hrun] at hstep
  dsimp only at hstep
  have hws := hstep (Or.inl ⟨value, rfl⟩)
  have hws_caller : WorldStep
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra state (some (.returned value)) post := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hws
    refine ⟨h1, h2, h3, h4, fun S_x Nd_x hW_x hD_x => ?_⟩
    exact h5 S_x Nd_x ((worldTypedWith_with_locals _ _ _ _ _).2 hW_x) hD_x
  have hbuf_mem : ∀ gn ∈ ([("keccak_pad", 136), ("keccak_st", 200), ("mpt_nib_scratch", 64)] : List (String × Nat)),
      gn ∈ globalBuffers ∧ gn.1 ∉ typedRecords.map Prod.fst := by decide
  obtain ⟨_, _, hMA_post, _, _⟩ :=
    WorldStep.preserves_msgReadyAt hMA hws_caller
      (fun j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl
        · intro hz
          by_cases hk0 : globN state "keccak_pad" = 0
          · dsimp only; rw [hk0]
          · exfalso; have hz' : (if globN state "keccak_pad" = 0 then 0 else 136) = 0 := hz
            rw [if_neg hk0] at hz'; cases hz'
        · intro hz
          by_cases hk0 : globN state "keccak_st" = 0
          · dsimp only; rw [hk0]
          · exfalso; have hz' : (if globN state "keccak_st" = 0 then 0 else 200) = 0 := hz
            rw [if_neg hk0] at hz'; cases hz'
        · intro hz
          by_cases hk0 : globN state "mpt_nib_scratch" = 0
          · dsimp only; rw [hk0]
          · exfalso; have hz' : (if globN state "mpt_nib_scratch" = 0 then 0 else 64) = 0 := hz
            rw [if_neg hk0] at hz'; cases hz')
      (fun x hx j hj => by
        change x ∈ [bufferRegion state ("keccak_pad", 136), bufferRegion state ("keccak_st", 200),
          bufferRegion state ("mpt_nib_scratch", 64)] at hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        have hgn : ∃ gn ∈ ([("keccak_pad", 136), ("keccak_st", 200), ("mpt_nib_scratch", 64)] : List (String × Nat)),
            x = bufferRegion state gn := by
          rcases hx with rfl | rfl | rfl
          · exact ⟨("keccak_pad", 136), by simp, rfl⟩
          · exact ⟨("keccak_st", 200), by simp, rfl⟩
          · exact ⟨("mpt_nib_scratch", 64), by simp, rfl⟩
        obtain ⟨gn, hgn_in, rfl⟩ := hgn
        obtain ⟨hg, hu⟩ := hbuf_mem gn hgn_in
        rcases List.mem_cons.1 hj with rfl | hj_ti
        · have hx_ow : bufferRegion state gn ∈ worldOwned state S Nd := by
            unfold worldOwned fixedObjects
            apply List.mem_append.2; left; apply List.mem_append.2; right
            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
            exact List.mem_map.2 ⟨gn, hg, rfl⟩
          exact (hMA.2.2.2.2.2.2.2.2.2.2.2.1 _ hx_ow).flip
        · exact bufferRegion_disj hMA.2.1 gn hg hu j hj_ti)
  exact localsOnly_msgReady.setVar (by simp; decide) value _ (msgReadyAt_msgReady hMA_post)

theorem seq_ends_return_ne_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    {p : ProgHOL 64} {e : ExpHOL 64} :
    (evaluateHOLFiniteState s (.seq p (.return e))).1 ≠ none := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases evaluateHOLFiniteState s p with ⟨r, mid⟩
  cases r with
  | none => exact return_ne_none mid e
  | some _ => simp

theorem seq4_return_ne_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p1 p2 p3 p4 : ProgHOL 64) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.seq p1 (.seq p2 (.seq p3 (.seq p4 (.return e)))))).1 ≠ none := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases evaluateHOLFiniteState s p1 with ⟨r1, s1⟩
  cases r1 with
  | some _ => simp
  | none =>
    dsimp only; rw [evaluateHOLFiniteState_seq_line780]
    rcases evaluateHOLFiniteState s1 p2 with ⟨r2, s2⟩
    cases r2 with
    | some _ => simp
    | none =>
      dsimp only; rw [evaluateHOLFiniteState_seq_line780]
      rcases evaluateHOLFiniteState s2 p3 with ⟨r3, s3⟩
      cases r3 with
      | some _ => simp
      | none => exact seq_ends_return_ne_none s3

theorem prove_gbody_process_message_call
    (had : TerminatingFunBoundedOn GuestInv (ofString "account_deployable") K.«account_deployable»)
    (hal : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (hfsg : TerminatingFunBoundedOn GuestInv (ofString "frame_state_gas_used") K.«frame_state_gas_used»)
    (hmz : TerminatingFunBoundedOn GuestInv (ofString "memzero") K.«memzero»)
    (hpcm : TerminatingFunBoundedOn MsgReady (ofString "process_create_message") K.«process_create_message»)
    (hpm : TerminatingFunBoundedOn MsgReady (ofString "process_message") K.«process_message»)
    (wad : WorldKeeps WorldOK
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "account_deployable"))
    (wal : WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc"))
    (wmz : WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")])
      []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "memzero"))
    (_zvmz : ZeroFills (ofString "memzero")) :
    TerminatingFunBoundedOn MsgReady (ofString "process_message_call") K.«process_message_call» := by
  refine ⟨_, _, _, GbodyC17ToC21Common.lookup_process_message_call, ?_⟩
  simp only [InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  have hskip : Hoare MsgReady .skip (fun r t => r = none → MsgReady t) :=
    Hoare.skip fun _ h _ => h
  have hdep_guard : ∀ (cond : ExpHOL 64) (p1 p2 p3 p4 : ProgHOL 64) (e : ExpHOL 64),
      Hoare MsgReady (.ite cond (.seq p1 (.seq p2 (.seq p3 (.seq p4 (.return e))))) .skip)
        (fun r t => r = none → MsgReady t) := fun cond p1 p2 p3 p4 e =>
    Hoare.ite ⟨fun s _ _ _ h => absurd h (seq4_return_ne_none s p1 p2 p3 p4 e)⟩
      (Hoare.skip fun _ h _ => h.1) (fun _ _ h => absurd h (by simp))
  have hm_guest : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), MsgReady s → GuestInv s :=
    fun _ h => h.1.1
  have hentry_pcm : CallEntryOn MsgReady MsgReady (ofString "process_create_message")
      [.var .local (ofString "msg")] :=
    callEntryOn_msgReady_same GbodyC17ToC21Common.lookup_process_create_message rfl
  have hentry_pm : CallEntryOn MsgReady MsgReady (ofString "process_message")
      [.var .local (ofString "msg")] :=
    callEntryOn_msgReady_same GbodyC17ToC21Common.lookup_process_message rfl
  intro F state hcode hP
  exact TerminatingRunBounded.weaken
    ((TerminatingProgBoundedOn.seq_hoare
      (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)) hskip
      (TerminatingProgBoundedOn.decCall_on hal _ _ _
        (callEntryOn_of_imp localsFree_guestInv hm_guest _ _)
        (resumeOn_alloc96_msgReady wal rtal)
        (TerminatingProgBoundedOn.seq_hoare_trans
          (TerminatingProgBoundedOn.call_on hmz _ _
            (callEntryOn_of_imp localsFree_guestInv msgReadyWithOut_guestInv _ _))
          (hoare_memzero96_msgReady wmz)
          (TerminatingProgBoundedOn.dec_onLocals localsOnly_msgReady (ofString "frame") (by simp; decide) _ _
            (TerminatingProgBoundedOn.seq_guestInv_after
              (TerminatingProgBoundedOn.ite_on
                (TerminatingProgBoundedOn.decCall_on had _ _ _
                  (callEntryOn_of_imp localsFree_guestInv hm_guest _ _)
                  (resumeOn_account_deployable_msgReady wad _)
                  (TerminatingProgBoundedOn.seq_hoare
                    (TerminatingProgBoundedOn.ite_on
                      (TerminatingProgBoundedOn.of_clock
                        (seq_clock (fun s => clock_store s _ _)
                          (seq_clock (fun s => clock_store s _ _)
                            (seq_clock (fun s => clock_store s _ _)
                              (seq_clock (fun s => clock_store s _ _)
                                (fun s => clock_return s _))))))
                      (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
                    (hdep_guard _ _ _ _ _ _)
                    (TerminatingProgBoundedOn.call_on hpcm _ _ hentry_pcm)))
                (TerminatingProgBoundedOn.call_on hpm _ _ hentry_pm))
              hm_guest
              (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                  (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                    (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                      (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                        (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                          (TerminatingProgBoundedOn.decCall_guestInv hfsg _ _ _
                            (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                              (TerminatingProgBoundedOn.seq_guestInv
                                (TerminatingProgBoundedOn.ite_on
                                  (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                    (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                      (TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _
                                        (TerminatingProgBoundedOn.seq_guestInv
                                          (TerminatingProgBoundedOn.ite_on
                                            (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
                                            (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
                                          (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))))))
                                  (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
                                (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                  (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                    (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))))))))))))))))) state hcode hP)
    (by
      unfold K.«process_message_call»
      simp only [show ∀ a b : Nat, Nat.max a b = max a b from fun _ _ => rfl]
      omega)


theorem «gbody_process_message_call» : GBody.«process_message_call» :=
  prove_gbody_process_message_call

end InitECandidate.Solver.Wave8GuestInv.R16Shards
