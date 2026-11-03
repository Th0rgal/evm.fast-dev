import InitECandidate.Solver.Wave8GuestInv.Deliveries.M26.Common

/-! Return-typing contract `rt_scratch_alloc` for micro-shard `m26` (`wave8/contracts-m26`),
checked against frozen revision 9 (`8a79d9f28`, tag `wave8-spec-frozen-r9`).

`scratch_alloc` (AST line 154, index 13): returns a fresh aligned scratch block of `n` bytes and
lowers `scratch_ptr` to it.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8Contracts.M26

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

private theorem eval_scratch_alloc_nonword_n {F : Type}
    (s : PanSemStateFiniteExact 64 F) (p : BitVec 64)
    (hp : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word p)))
    (hn_not_word : ∀ nw : BitVec 64, s.locals.lookup (ofString "n") ≠ some (.val (.word nw)))
    (v : ValueHOL 64) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_scratch_alloc)).1 ≠
      some (.returned v) := by
  have hbody_eq : sourceFnBody Guest.Software.guestFn_scratch_alloc =
      .dec (ofString "p") .one (.var .global (ofString "scratch_ptr"))
        (.seq
          (.ite (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 7])
            .skip)
          (.dec (ofString "q") .one
            (.op .and [.op .sub [.var .local (ofString "p"), .var .local (ofString "n")],
              .op .sub [.const 0, .const 8]])
            (.seq
              (.ite (.cmp .lower (.var .local (ofString "q")) (.var .global (ofString "frame_mem_ptr")))
                (.call (some (none, none)) (ofString "trap_with") [.const 7])
                .skip)
              (.seq
                (.assign .global (ofString "scratch_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "q"))))))) := rfl
  rw [hbody_eq, evaluateHOLFiniteState_dec_total]
  have hp_eval : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .global (ofString "scratch_ptr")) = some (.val (.word p)) := hp
  dsimp only
  rw [hp_eval]
  have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only
  rw [if_pos hsh_p]
  dsimp only
  let pState := setVarHOLFinite (ofString "p") (.val (.word p)) s
  have hp_loc : pState.locals.lookup (ofString "p") = some (.val (.word p)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hn_loc : pState.locals.lookup (ofString "n") = s.locals.lookup (ofString "n") := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "p" ≠ ofString "n" by decide]
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  have hcond_none : @evalHOLExact 64 F _ pState.toExact
      (fun a => Classical.propDecidable (pState.memaddrs a))
      (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
        (.var .local (ofString "n"))) = none := by
    rcases hn : s.locals.lookup (ofString "n") with _ | vn
    · simp [evalHOLExact, evalListHOLExact, hp_loc, hn_loc, hn]
    · rcases vn with ⟨⟨nw⟩⟩ | _ | _
      · exact absurd hn (hn_not_word nw)
      · rcases hf : pState.globals.lookup (ofString "frame_mem_ptr") with _ | vf <;>
          (try cases vf) <;>
          simp [evalHOLExact, evalListHOLExact, hp_loc, hn_loc, hn, hf, valueIsWord]
      · rcases hf : pState.globals.lookup (ofString "frame_mem_ptr") with _ | vf <;>
          (try cases vf) <;>
          simp [evalHOLExact, evalListHOLExact, hp_loc, hn_loc, hn, hf, valueIsWord]
  rw [hcond_none]
  simp

/-- `scratch_alloc` (AST line 154): returns a fresh aligned scratch block of `n` bytes and lowers
`scratch_ptr` to it. -/
theorem rt_scratch_alloc :
    Returns ArenaReady (fun s post p => FreshScratch s post p (locN s "n") ∧
      globN post "scratch_ptr" = p)
    (ofString "scratch_alloc") := by
  refine ⟨_, _, _, lookup_scratch_alloc, ?_⟩
  intro F s hcode hAR _ _hnt v hret
  obtain ⟨hG, hA⟩ := hAR
  obtain ⟨hp, fp, sp, hhp, hhp_eq, hfp, hfp_eq, hsp, hsp_eq⟩ := arenaOK_globals s hA
  rcases hn : s.locals.lookup (ofString "n") with _ | vn
  · exfalso
    refine eval_scratch_alloc_nonword_n s sp hsp ?_ v hret
    intro nw h; rw [hn] at h; cases h
  · rcases vn with ⟨⟨n⟩⟩ | _ | _
    · obtain ⟨rfl, hcmp1, hcmp2, hpost⟩ := scratch_alloc_body_run s sp fp n hcode hsp hfp hn v hret
      set q : BitVec 64 := (sp - n) &&& ((0 : BitVec 64) - 8)
      set post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_scratch_alloc)).2
      have hpost_g : post.globals = s.globals.update (ofString "scratch_ptr", .val (.word q)) := by
        rw [hpost]
      refine ⟨q, rfl, ?_⟩
      have hloc_n : locN s "n" = n.toNat := by simp [locN, hn]
      have hpost_hp : globN post "heap_ptr" = globN s "heap_ptr" := by
        unfold globN
        rw [hpost_g]
        simp [HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "scratch_ptr" ≠ ofString "heap_ptr" by decide]
      have hpost_fp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by
        unfold globN
        rw [hpost_g]
        simp [HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "scratch_ptr" ≠ ofString "frame_mem_ptr" by decide]
      have hpost_sp : globN post "scratch_ptr" = q.toNat := by
        unfold globN
        rw [hpost_g]
        simp [HolFiniteMapExact.lookup_update, FUPDATE]
      have hG_post : GuestInv post := guestInv_evaluate s _ hG
      have hsp_lt : sp.toNat < 2 ^ 64 := sp.isLt
      have hfp_lt : fp.toNat < 2 ^ 64 := fp.isLt
      have hsub_pf : (sp - fp).toNat = sp.toNat - fp.toNat := by
        rw [BitVec.toNat_sub]; have := hA.2.2.2.1; omega
      have hn_le_gap : n.toNat ≤ sp.toNat - fp.toNat := by omega
      have hn_le_sp : n.toNat ≤ sp.toNat := by omega
      have hsub_pn : (sp - n).toNat = sp.toNat - n.toNat := by
        rw [BitVec.toNat_sub]; omega
      have hq_nat : q.toNat = (sp.toNat - n.toNat) / 8 * 8 := by
        have h := and_neg8_toNat (sp - n)
        rw [hsub_pn] at h
        exact h
      have hsp_al : sp.toNat % 8 = 0 := by rw [hhp_eq, hfp_eq, hsp_eq] at *; exact hA.2.2.2.2.2.2.2.1
      have hq_al : q.toNat % 8 = 0 := by omega
      have hq_ge_fp : fp.toNat ≤ q.toNat := Nat.le_of_not_lt hcmp2
      have hq_le_sp : q.toNat ≤ sp.toNat := by omega
      have hq_round : q.toNat + (n.toNat + 7) / 8 * 8 = sp.toNat := by omega
      have hA_post : ArenaOK post := by
        unfold ArenaOK
        rw [hpost_hp, hpost_fp, hpost_sp]
        refine ⟨hA.1, hA.2.1, hA.2.2.1, ?_, ?_, hA.2.2.2.2.2.1, hA.2.2.2.2.2.2.1, hq_al,
          globalsWord_update (ofString "scratch_ptr") q hpost_g hA.2.2.2.2.2.2.2.2⟩
        · rw [← hfp_eq]; exact hq_ge_fp
        · have hsp_le_se := hA.2.2.2.2.1
          rw [← hsp_eq] at hsp_le_se
          exact Nat.le_trans hq_le_sp hsp_le_se
      have hAG : AllocatorGrows s post := by
        refine ⟨by rw [hpost_hp], ?_⟩
        rw [hpost_sp, ← hsp_eq]
        exact hq_le_sp
      have hsb_le_ss : sourceBase ≤ scratchStart := by decide
      have hse_le_he : scratchEnd ≤ heapEnd := by decide
      have hWOK : WordsOK post (q.toNat, (locN s "n" + 7) / 8 * 8) := by
        rw [hloc_n]
        apply wordsOK_of_guestInv post hG_post q.toNat ((n.toNat + 7) / 8 * 8) hq_al (by omega)
        · have := hA.2.2.1
          omega
        · have := hA.2.2.2.2.1
          omega
      refine ⟨⟨hG_post, hA_post⟩, hAG, ⟨?_, hpost_sp⟩⟩
      refine ⟨hq_al, ?_, ?_, hWOK⟩
      · rw [← hfp_eq]; exact hq_ge_fp
      · rw [hloc_n, hpost_sp, ← hsp_eq]
        exact ⟨le_rfl, le_of_eq hq_round⟩
    · exfalso
      refine eval_scratch_alloc_nonword_n s sp hsp ?_ v hret
      intro nw h; rw [hn] at h; cases h
    · exfalso
      refine eval_scratch_alloc_nonword_n s sp hsp ?_ v hret
      intro nw h; rw [hn] at h; cases h

end InitECandidate.Solver.Wave8Contracts.M26
