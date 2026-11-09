import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group09LogReturnRevert
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemAlignedBridge

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8Contracts.M23
open Group09ChainWF

/-! ## 1. `extend_memory` unified body effect & `OpDispatchPostBoth` step -/

theorem extend_memory_body_frameMemEff_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) {ebw : BitVec 64}
    (hcode : s.code = originalRuntimeCode)
    (hInv : EvmInv s)
    (heb_loc : s.locals.lookup (ofString "expand_by") = some (.val (.word ebw)))
    (heb_cond : ebw = 0#64 ∨
      (memW s (globN s "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
       (memW s (globN s "ev" + 32) + ebw.toNat) % 32 = 0 ∧
       memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = globN s "frame_mem_ptr"))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_extend_memory)).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_extend_memory)
    (∀ v, out.1 = some (.returned v) →
      v = .val (.word 0#64) ∧
      ∃ freshIvl : Ivl,
        ArenaReady out.2 ∧
        globN s "frame_mem_ptr" ≤ globN out.2 "frame_mem_ptr" ∧
        FrameMemByteEff s out.2
          [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))] ∧
        (freshIvl = (0, 0) ∨
          (freshIvl.1 % 8 = 0 ∧ freshIvl.2 % 8 = 0 ∧
            Inside freshIvl (globN s "frame_mem_ptr") (globN out.2 "frame_mem_ptr"))) ∧
        (∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 32 → off ≠ 40 →
          memW out.2 (globN s "ev" + off) = memW s (globN s "ev" + off)) ∧
        ((freshIvl.2 = 0 ∧ memW out.2 (globN s "ev" + 40) = memW s (globN s "ev" + 40) ∧
            globN out.2 "frame_mem_ptr" = globN s "frame_mem_ptr") ∨
          (freshIvl.2 ≠ 0 ∧
            memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = freshIvl.1 ∧
            memW out.2 (globN s "ev" + 40) = memW s (globN s "ev" + 40) + freshIvl.2 ∧
            globN out.2 "frame_mem_ptr" = freshIvl.1 + freshIvl.2)) ∧
        memW out.2 (globN s "ev" + 32) ≤ memW out.2 (globN s "ev" + 40) ∧
        memW out.2 (globN s "ev" + 32) = memW s (globN s "ev" + 32) + ebw.toNat) ∧
    ¬ IsEvmErr out.1 := by
  have herr_triv : ∀ {P1 : ValueHOL 64 → Prop},
      (∀ v, (some PanSemResultExact.error : Option (PanSemResultExact 64)) = some (.returned v) → P1 v) ∧
      ¬ IsEvmErr (some PanSemResultExact.error) := by
    intro _; constructor
    · intro _ h; cases h
    · rintro ⟨_, h⟩; cases h
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := head_mem_evmChain_g09 s
  have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead_mem
  have hb_ev := (frameWF_bounds hInv.1.2 hFW0).1
  dsimp only at hb_ev
  have hev_pos : 0 < globN s "ev" := by
    obtain ⟨hin1, _⟩ := (hFW0.1 (globN s "ev", 280) (by simp)).1
    have h1 := hInv.1.2.2.2.1; have h2 := hInv.1.2.2.2.2.1
    rw [R11Shards.scratchStart_val] at h1; dsimp only at hin1; omega
  obtain ⟨evw, hevw, hevw_nat⟩ := global_word_of_pos s "ev" hev_pos
  obtain ⟨hp_w, fp_w, sp_g_w, hhp_lk, hhp_nat, hfp_lk, hfp_nat, hsp_g_lk, hsp_g_nat⟩ :=
    Wave8Contracts.M26.arenaOK_globals s hInv.1.2
  let growBranch : ProgHOL 64 :=
    .dec (ofString "ncap") .one (.panop .mul [.var .local (ofString "cap"), .const 2#64])
      (.seq
        (.ite (.cmp .lower (.var .local (ofString "ncap")) (.var .local (ofString "nlen")))
          (.assign .local (ofString "ncap") (.op .add [.var .local (ofString "nlen"), .const 1024#64]))
          .skip)
        (.seq
          (.call (some (none, none)) (ofString "frame_mem_alloc")
            [.op .sub [.var .local (ofString "ncap"), .var .local (ofString "cap")]])
          (.seq
            (.call (some (none, none)) (ofString "memzero")
              [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "cap")],
               .op .sub [.var .local (ofString "ncap"), .var .local (ofString "cap")]])
            (.store (.op .add [.var .global (ofString "ev"), .const 40#64]) (.var .local (ofString "ncap"))))))
  let tailProg : ProgHOL 64 :=
    .seq
      (.call (some (none, none)) (ofString "memzero")
        [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "len")],
         .var .local (ofString "expand_by")])
      (.seq
        (.store (.op .add [.var .global (ofString "ev"), .const 32#64]) (.var .local (ofString "nlen")))
        (.return (.const 0#64)))
  have hbody : sourceFnBody Guest.Software.guestFn_extend_memory =
      .seq
        (.ite (.cmp .equal (.var .local (ofString "expand_by")) (.const 0#64))
          (.return (.const 0#64))
          .skip)
        (.dec (ofString "len") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 32#64]))
          (.dec (ofString "cap") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 40#64]))
            (.dec (ofString "nlen") .one (.op .add [.var .local (ofString "len"), .var .local (ofString "expand_by")])
              (.seq
                (.ite (.cmp .lower (.var .local (ofString "cap")) (.var .local (ofString "nlen")))
                  growBranch
                  .skip)
                tailProg)))) := rfl
  dsimp only
  rw [hbody] at hnt ⊢
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
  have hcmp_eb0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.var .local (ofString "expand_by")) (.const 0#64)) =
      some (.val (.word (if ebw = 0#64 then 1 else 0))) := by
    simp [evalHOLExact, heb_loc, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp_eb0] at hnt ⊢; dsimp only at hnt ⊢
  have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
  by_cases heb0 : ebw = 0#64
  · simp only [heb0, ↓reduceIte, h10] at hnt ⊢
    rw [evaluateHOLFiniteState_return]
    have hc0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.const 0#64) =
        some (.val (.word 0#64)) := rfl
    rw [hc0]; dsimp only
    have hsz0 : sizeOfShapeWithContextHOL s.structs
        (shapeOfHOLExact (.val (.word 0#64))) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [if_pos hsz0]; dsimp only
    refine ⟨fun v hv => ?_, fun ⟨_, h⟩ => by cases h⟩
    injection hv with hv'; injection hv' with hv''
    subst hv''; subst heb0
    refine ⟨rfl, (0, 0), ⟨guestInv_congr (s := s) rfl rfl rfl rfl hInv.1.1, hInv.1.2⟩, le_refl _,
      (FrameMemByteEff.refl s _).with_locals_clock _ s.clock, Or.inl rfl,
      fun _ _ _ _ _ => rfl, Or.inl ⟨rfl, rfl, rfl⟩, hFW0.2.2.2.2.2.2.1, rfl⟩
  · rcases heb_cond with rfl | ⟨hnlen_bound, hnlen_al32, hmem_end_fp⟩
    · exact absurd rfl heb0
    have hnlen_al8 : (memW s (globN s "ev" + 32) + ebw.toNat) % 8 = 0 := by omega
    simp only [heb0, ↓reduceIte, evaluateHOLFiniteState_skip] at hnt ⊢
    rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
    rcases hload_len : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one (.op .add [.var .global (ofString "ev"), .const 32#64])) with _ | vlen
    · exact herr_triv
    · simp only [hload_len] at hnt ⊢
      obtain ⟨lenw, rfl, hlenw_eq⟩ := evalAt_loadG_word s "ev" 32#64 vlen hload_len
      have h32_n : (32#64 : BitVec 64).toNat = 32 := rfl
      rw [h32_n] at hlenw_eq
      have hsh_len : shapeEqHOL .one (shapeOfHOLExact (.val (.word lenw))) = true := by
        simp [shapeEqHOL, shapeOfHOLExact]
      rw [if_pos hsh_len] at hnt ⊢; dsimp only at hnt ⊢
      set s1 := setVarHOLFinite (ofString "len") (.val (.word lenw)) s with hs1
      rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
      rcases hload_cap : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
          (.load .one (.op .add [.var .global (ofString "ev"), .const 40#64])) with _ | vcap
      · exact herr_triv
      · simp only [hload_cap] at hnt ⊢
        obtain ⟨capw, rfl, hcapw_eq⟩ := evalAt_loadG_word s1 "ev" 40#64 vcap hload_cap
        have h40_n : (40#64 : BitVec 64).toNat = 40 := rfl
        have hs1_gm : memW s1 (globN s1 "ev" + 40) = memW s (globN s "ev" + 40) := rfl
        rw [h40_n, hs1_gm] at hcapw_eq
        have hsh_cap : shapeEqHOL .one (shapeOfHOLExact (.val (.word capw))) = true := by
          simp [shapeEqHOL, shapeOfHOLExact]
        rw [if_pos hsh_cap] at hnt ⊢; dsimp only at hnt ⊢
        set s2 := setVarHOLFinite (ofString "cap") (.val (.word capw)) s1 with hs2
        have hs2_len : s2.locals.lookup (ofString "len") = some (.val (.word lenw)) := by
          simp [hs2, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "cap" ≠ ofString "len" by decide]
        have hs2_cap : s2.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
          simp [hs2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hs2_eb : s2.locals.lookup (ofString "expand_by") = some (.val (.word ebw)) := by
          simp [hs2, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, heb_loc,
            show ofString "cap" ≠ ofString "expand_by" by decide,
            show ofString "len" ≠ ofString "expand_by" by decide]
        rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
        have hnlen_ev : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
            (.op .add [.var .local (ofString "len"), .var .local (ofString "expand_by")]) =
            some (.val (.word (lenw + ebw))) := by
          simp [evalHOLExact, evalListHOLExact, hs2_len, hs2_eb, wordOpHOL, wordOp, valueIsWord, valueWord]
        rw [hnlen_ev] at hnt ⊢; dsimp only at hnt ⊢
        set nlenw := lenw + ebw
        have hnlenw_nat : nlenw.toNat = lenw.toNat + ebw.toNat := by
          rw [BitVec.toNat_add, hlenw_eq, Nat.mod_eq_of_lt (by omega)]
        have hsh_nlen : shapeEqHOL .one (shapeOfHOLExact (.val (.word nlenw))) = true := by
          simp [shapeEqHOL, shapeOfHOLExact]
        rw [if_pos hsh_nlen] at hnt ⊢; dsimp only at hnt ⊢
        set s3 := setVarHOLFinite (ofString "nlen") (.val (.word nlenw)) s2 with hs3
        have hs3_nlen : s3.locals.lookup (ofString "nlen") = some (.val (.word nlenw)) := by
          simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hs3_len : s3.locals.lookup (ofString "len") = some (.val (.word lenw)) := by
          simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_len,
            show ofString "nlen" ≠ ofString "len" by decide]
        have hs3_cap : s3.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
          simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_cap,
            show ofString "nlen" ≠ ofString "cap" by decide]
        have hs3_eb : s3.locals.lookup (ofString "expand_by") = some (.val (.word ebw)) := by
          simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_eb,
            show ofString "nlen" ≠ ofString "expand_by" by decide]
        have hmem_in : Inside (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40)) scratchStart (globN s "frame_mem_ptr") :=
          hFW0.2.1
        have hmem_wok := hFW0.2.2.1
        have hmem24_8 : memW s (globN s "ev" + 24) % 8 = 0 := hmem_wok.1
        have hmem40_8 : memW s (globN s "ev" + 40) % 8 = 0 := hmem_wok.2.1
        have hfp_le_se : globN s "frame_mem_ptr" ≤ scratchEnd :=
          le_trans hInv.1.2.2.2.2.1 hInv.1.2.2.2.2.2.1
        have hse_val := R11Shards.scratchEnd_val
        have hss_val := R11Shards.scratchStart_val
        have hcap_lt : capw.toNat < 2 ^ 30 := by
          dsimp only [Inside] at hmem_in; omega
        have run_tail : ∀ (m : PanSemStateFiniteExact 64 F) (freshIvl : Ivl),
            ArenaReady m →
            globN s "frame_mem_ptr" ≤ globN m "frame_mem_ptr" →
            (∀ g : String, ofString g ≠ ofString "frame_mem_ptr" → m.globals.lookup (ofString g) = s.globals.lookup (ofString g)) →
            FrameMemByteEff s m [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))] →
            (freshIvl = (0, 0) ∨
              (freshIvl.1 % 8 = 0 ∧ freshIvl.2 % 8 = 0 ∧
                Inside freshIvl (globN s "frame_mem_ptr") (globN m "frame_mem_ptr"))) →
            (∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 32 → off ≠ 40 →
              memW m (globN s "ev" + off) = memW s (globN s "ev" + off)) →
            ((freshIvl.2 = 0 ∧ memW m (globN s "ev" + 40) = memW s (globN s "ev" + 40) ∧
                globN m "frame_mem_ptr" = globN s "frame_mem_ptr") ∨
              (freshIvl.2 ≠ 0 ∧
                memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = freshIvl.1 ∧
                memW m (globN s "ev" + 40) = memW s (globN s "ev" + 40) + freshIvl.2 ∧
                globN m "frame_mem_ptr" = freshIvl.1 + freshIvl.2)) →
            nlenw.toNat ≤ memW m (globN s "ev" + 40) →
            m.locals.lookup (ofString "len") = some (.val (.word lenw)) →
            m.locals.lookup (ofString "nlen") = some (.val (.word nlenw)) →
            m.locals.lookup (ofString "expand_by") = some (.val (.word ebw)) →
            (evaluateHOLFiniteState m tailProg).1 ≠ some .timeOut →
            let out := evaluateHOLFiniteState m tailProg
            let post := { out.2 with
              locals := ((out.2.locals.resVarEq (ofString "nlen", s2.locals.lookup (ofString "nlen"))).resVarEq
                (ofString "cap", s1.locals.lookup (ofString "cap"))).resVarEq
                (ofString "len", s.locals.lookup (ofString "len")) }
            (∀ v, out.1 = some (.returned v) →
              v = .val (.word 0#64) ∧
              ∃ fi : Ivl,
                ArenaReady post ∧
                globN s "frame_mem_ptr" ≤ globN post "frame_mem_ptr" ∧
                FrameMemByteEff s post
                  [fi, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))] ∧
                (fi = (0, 0) ∨
                  (fi.1 % 8 = 0 ∧ fi.2 % 8 = 0 ∧
                    Inside fi (globN s "frame_mem_ptr") (globN post "frame_mem_ptr"))) ∧
                (∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 32 → off ≠ 40 →
                  memW post (globN s "ev" + off) = memW s (globN s "ev" + off)) ∧
                ((fi.2 = 0 ∧ memW post (globN s "ev" + 40) = memW s (globN s "ev" + 40) ∧
                    globN post "frame_mem_ptr" = globN s "frame_mem_ptr") ∨
                  (fi.2 ≠ 0 ∧
                    memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = fi.1 ∧
                    memW post (globN s "ev" + 40) = memW s (globN s "ev" + 40) + fi.2 ∧
                    globN post "frame_mem_ptr" = fi.1 + fi.2)) ∧
                memW post (globN s "ev" + 32) ≤ memW post (globN s "ev" + 40) ∧
                memW post (globN s "ev" + 32) = memW s (globN s "ev" + 32) + ebw.toNat) ∧
            ¬ IsEvmErr out.1 := by
          intro m freshIvl hAm hfm_m hm_glob_other heff_m hfresh_m he0_m hnew_m hnlen_le_mcap hm_len hm_nlen hm_eb hnt_t
          dsimp only [tailProg] at hnt_t ⊢
          have hm_ev : m.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
            rw [hm_glob_other "ev" (by decide)]; exact hevw
          have hm_code : m.code = originalRuntimeCode := heff_m.code.trans hcode
          have hm_ma : m.memaddrs = ordinaryDomain := hAm.1.memaddrs
          have hev24_eq : evw + 24#64 = BitVec.ofNat 64 (globN s "ev" + 24) :=
            BitVec.eq_of_toNat_eq (by
              rw [BitVec.toNat_add, hevw_nat, show (24#64 : BitVec 64).toNat = 24 from rfl, BitVec.toNat_ofNat])
          have hm_dom24 : m.memaddrs (evw + 24#64) := by
            rw [hm_ma, ← hInv.1.1.memaddrs, hev24_eq]
            exact ((hFW0.1 (globN s "ev", 280) (by simp)).2.2.2 3 (by omega)).choose_spec.1
          rcases hm_m24 : m.memory (evw + 24#64) with ⟨memPtrW⟩
          have hmemPtrW_nat : memPtrW.toNat = memW s (globN s "ev" + 24) := by
            have hm24_eq := he0_m 24 (by omega) (by omega) (by omega) (by omega)
            have hm24_lhs : memW m (globN s "ev" + 24) = memPtrW.toNat := by
              unfold memW; rw [← hev24_eq, hm_m24]
            rw [← hm24_lhs, hm24_eq]
          let mzDstExp : ExpHOL 64 :=
            .op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "len")]
          have hev_mz_dst : @evalHOLExact 64 F _ m.toExact (fun a => Classical.propDecidable (m.memaddrs a)) mzDstExp =
              some (.val (.word (memPtrW + lenw))) := by
            simp [mzDstExp, evalHOLExact, evalListHOLExact, hm_ev, hm_len, wordOpHOL, wordOp,
              valueIsWord, valueWord, memLoadHOLExact, hm_dom24, hm_m24]
          have hev_mz_n : @evalHOLExact 64 F _ m.toExact (fun a => Classical.propDecidable (m.memaddrs a))
              (.var .local (ofString "expand_by")) = some (.val (.word ebw)) := hm_eb
          have hmcap_bound : memW s (globN s "ev" + 24) + memW m (globN s "ev" + 40) ≤ scratchEnd := by
            rcases hnew_m with ⟨_, h40_eq, _⟩ | ⟨hnz, hfr1, h40_eq, _⟩
            · rw [h40_eq]; dsimp only [Inside] at hmem_in; omega
            · rcases hfresh_m with rfl | ⟨_, _, _, hfin2⟩
              · exact absurd rfl hnz
              · have hm_fp_se : globN m "frame_mem_ptr" ≤ scratchEnd :=
                  le_trans hAm.2.2.2.2.1 hAm.2.2.2.2.2.1
                omega
          have hdst_nat : (memPtrW + lenw).toNat = memW s (globN s "ev" + 24) + lenw.toNat := by
            rw [BitVec.toNat_add, hmemPtrW_nat, Nat.mod_eq_of_lt (by omega)]
          let combinedMem : Ivl := (memW s (globN s "ev" + 24), memW m (globN s "ev" + 40))
          rw [evaluateHOLFiniteState_seq_line780] at hnt_t ⊢
          have hnt_mz : (evaluateHOLFiniteState m (.call (some (none, none)) (ofString "memzero") [mzDstExp, .var .local (ofString "expand_by")])).1 ≠ some .timeOut := by
            intro hto; rcases hmz_to : evaluateHOLFiniteState m (.call (some (none, none)) (ofString "memzero") [mzDstExp, .var .local (ofString "expand_by")]) with ⟨rmz_to, smz_to⟩
            rw [hmz_to] at hto; dsimp only at hto; subst hto; dsimp only [mzDstExp] at hmz_to; simp only [hmz_to] at hnt_t; exact hnt_t rfl
          have hmz := eval_call_memzero_bre m mzDstExp (.var .local (ofString "expand_by"))
            (memPtrW + lenw) ebw [combinedMem] hm_code hm_ma hev_mz_dst hev_mz_n
            (fun _ => ⟨combinedMem, by simp, by rw [hdst_nat]; dsimp only [combinedMem]; omega,
              by rw [hdst_nat]; dsimp only [combinedMem]; omega⟩) hnt_mz
          dsimp only at hmz
          rcases hmz_run : evaluateHOLFiniteState m (.call (some (none, none)) (ofString "memzero") [mzDstExp, .var .local (ofString "expand_by")]) with ⟨rmz, m1⟩
          rw [hmz_run] at hmz; dsimp only [mzDstExp] at hmz_run; simp only [hmz_run] at hnt_t ⊢
          cases rmz with
          | some rmz0 =>
            dsimp only at hnt_t ⊢
            have hnr := hmz.2 (by simp)
            refine ⟨fun v hv => absurd (Or.inl ⟨v, hv⟩) hnr, ?_⟩
            rintro ⟨ev, hv⟩
            injection hv with hv'; subst hv'
            exact hnr (Or.inr ⟨ofString "EvmErr", ev, rfl, by decide⟩)
          | none =>
            dsimp only at hnt_t ⊢
            obtain ⟨heff_mz_comb, hm1_loc⟩ := hmz.1 rfl
            have heff_mz : FrameMemByteEff m m1
                [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))] := by
              refine ⟨heff_mz_comb.code, heff_mz_comb.memaddrs, heff_mz_comb.shMemaddrs,
                heff_mz_comb.baseAddr, heff_mz_comb.be, fun _ _ => by rw [heff_mz_comb.globals],
                heff_mz_comb.out_dom, ?_, ?_⟩
              · intro a ha
                apply heff_mz_comb.cell_frame a
                intro i hi hch
                simp at hi; subst hi
                obtain ⟨hc1, hc2⟩ := hch
                dsimp only [combinedMem] at hc1 hc2
                rcases hnew_m with ⟨_, h40_eq, _⟩ | ⟨hnz, hfr1, h40_eq, _⟩
                · rw [h40_eq] at hc2
                  exact ha (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40)) (by simp) ⟨hc1, hc2⟩
                · by_cases hsplit : a.toNat < memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40)
                  · exact ha (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40)) (by simp) ⟨hc1, hsplit⟩
                  · exact ha freshIvl (by simp) ⟨by omega, by omega⟩
              · intro b hb hno
                apply heff_mz_comb.byte_frame b hb
                intro i hi hin
                simp at hi; subst hi
                obtain ⟨hb1, hb2⟩ := hin
                dsimp only [combinedMem] at hb1 hb2
                rcases hnew_m with ⟨_, h40_eq, _⟩ | ⟨hnz, hfr1, h40_eq, _⟩
                · rw [h40_eq] at hb2
                  exact hno (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40)) (by simp) ⟨hb1, hb2⟩
                · by_cases hsplit : b < memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40)
                  · exact hno (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40)) (by simp) ⟨hb1, hsplit⟩
                  · exact hno freshIvl (by simp) ⟨by omega, by omega⟩
            have hm1_e0_eq : ∀ off, off + 8 ≤ 280 → off % 8 = 0 →
                memW m1 (globN s "ev" + off) = memW m (globN s "ev" + off) := by
              intro off hoff hoff8
              unfold memW
              rw [heff_mz_comb.cell_frame (BitVec.ofNat 64 (globN s "ev" + off))]
              intro x hx
              simp at hx; subst hx
              have htn : (BitVec.ofNat 64 (globN s "ev" + off)).toNat = globN s "ev" + off :=
                Nat.mod_eq_of_lt (by omega)
              rw [htn]
              have he0_8 : (globN s "ev") % 8 = 0 := (hFW0.1 (globN s "ev", 280) (by simp)).2.1
              have ha8 : (globN s "ev" + off) % 8 = 0 := by omega
              rcases hnew_m with ⟨_, h40_eq, _⟩ | ⟨hnz, hfr1, h40_eq, _⟩
              · dsimp only [combinedMem]; rw [h40_eq]
                have hpw_fo := hInv.2.choose_spec.2.2.2.2.2.2.2.1
                obtain ⟨tl_s, hch_s_eq⟩ := (⟨_, evmChain_cons_g09 s⟩ : ∃ tl, evmChain s = (globN s "ev", globN s "cur_cont") :: tl)
                rw [hch_s_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw_fo
                have hd_mem : Disj (globN s "ev", 280) (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40)) := by
                  have hp0 := hpw_fo.1; unfold frameObjects at hp0
                  exact (List.pairwise_cons.1 hp0).1 _ (by simp)
                exact not_cellHits_of_disj_aligned (i := (globN s "ev", 280)) ha8 hmem24_8
                  (Nat.le_add_right _ off) (Nat.add_le_add_left hoff _) hd_mem
              · rcases hfresh_m with rfl | ⟨_, _, _, hfin2⟩
                · exact absurd rfl hnz
                · obtain ⟨he0_scr, _⟩ := (hFW0.1 (globN s "ev", 280) (by simp)).1
                  have hfp_le_scr : globN m "frame_mem_ptr" ≤ globN s "scratch_ptr" := by
                    have hle_m := hAm.2.2.2.2.1
                    have hsp_eq := R16Shards.OpHandlers.globN_eq_of_lookup_eq (hm_glob_other "scratch_ptr" (by decide))
                    omega
                  exact not_cellHits_of_disj_aligned (i := (globN s "ev", 280)) ha8 hmem24_8
                    (Nat.le_add_right _ off) (Nat.add_le_add_left hoff _)
                    (Or.inr (Or.inr (Or.inr (by dsimp only [combinedMem, Inside] at he0_scr hfin2 ⊢; omega))))
            rw [evaluateHOLFiniteState_seq_line780] at hnt_t ⊢
            rcases hst32 : evaluateHOLFiniteState m1
                (.store (.op .add [.var .global (ofString "ev"), .const 32#64]) (.var .local (ofString "nlen"))) with ⟨rst32, m2⟩
            simp only [hst32] at hnt_t ⊢
            cases rst32 with
            | some res32 =>
              have herr := store_some_eq_error' hst32; subst herr; dsimp only; exact herr_triv
            | none =>
              dsimp only at hnt_t ⊢
              have hm1_ev : m1.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
                rw [heff_mz_comb.globals]; exact hm_ev
              have hm1_nlen : m1.locals.lookup (ofString "nlen") = some (.val (.word nlenw)) := by
                rw [hm1_loc]; exact hm_nlen
              obtain ⟨w_nl', hw_nl_ev, hm2_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := m1) (post := m2)
                (gname := "ev") (gbase := globN s "ev") (off := 32) hm1_ev hevw_nat (by omega)
                (fun v hv => by
                  change m1.locals.lookup (ofString "nlen") = some v at hv
                  rw [hm1_nlen] at hv; injection hv with hv'; exact ⟨nlenw, hv'.symm⟩) hst32
              have hw_nl_val : nlenw = w_nl' := by
                change m1.locals.lookup (ofString "nlen") = some (.val (.word w_nl')) at hw_nl_ev
                rw [hm1_nlen] at hw_nl_ev
                injection hw_nl_ev with h1; injection h1 with h2; injection h2 with h3
              subst w_nl'
              have heff_st32 := (ByteRegionEffect.of_store_word (Rl := [(globN s "ev", 280)])
                (heff_mz_comb.memaddrs.trans hm_ma) hst32
                (fun v hv => by
                  change m1.locals.lookup (ofString "nlen") = some v at hv
                  rw [hm1_nlen] at hv; injection hv with hv'; exact ⟨nlenw, hv'.symm⟩)
                (fun addr hdst _ => by
                  simp [evalHOLExact, evalListHOLExact, hm1_ev, wordOpHOL, wordOp, valueIsWord, valueWord] at hdst
                  have h32_eq : (evw + 32#64).toNat = globN s "ev" + 32 := by
                    have : (32#64 : BitVec 64).toNat = 32 := rfl
                    rw [BitVec.toNat_add, hevw_nat, this, Nat.mod_eq_of_lt (by omega)]
                  exact ⟨(globN s "ev", 280), by simp, by rw [← hdst, h32_eq]; dsimp only; omega,
                    by rw [← hdst, h32_eq]; dsimp only; omega⟩)).1
              have heff_st32_fm : FrameMemByteEff m1 m2
                  [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))] :=
                (FrameMemByteEff.of_bre heff_st32).mono (fun x hx => by
                  simp at hx; subst hx; exact ⟨(globN s "ev", 280), by simp, le_refl _, le_refl _⟩)
              rw [evaluateHOLFiniteState_return]
              simp only [show @evalHOLExact 64 F _ m2.toExact (fun a => Classical.propDecidable (m2.memaddrs a)) (.const 0#64) = some (.val (.word 0#64)) from rfl,
                show sizeOfShapeWithContextHOL m2.structs (shapeOfHOLExact (.val (.word 0#64))) ≤ 32 by simp [shapeOfHOLExact, sizeOfShapeWithContextHOL],
                ↓reduceIte]
              let post := { m2.emptyLocalsHOLFinite with
                locals := ((m2.emptyLocalsHOLFinite.locals.resVarEq (ofString "nlen", s2.locals.lookup (ofString "nlen"))).resVarEq
                  (ofString "cap", s1.locals.lookup (ofString "cap"))).resVarEq
                  (ofString "len", s.locals.lookup (ofString "len")) }
              have heff_total : FrameMemByteEff s post
                  [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))] :=
                ((heff_m.trans heff_mz).trans heff_st32_fm).with_locals_clock post.locals m2.clock
              have hpost_glob_m : post.globals = m.globals := by
                dsimp only [post, emptyLocalsHOLFinite]; rw [hm2_eq]; exact heff_mz_comb.globals
              have hpost_code_m : post.code = m.code := by
                dsimp only [post, emptyLocalsHOLFinite]; rw [hm2_eq]; exact heff_mz_comb.code
              have hpost_ma_m : post.memaddrs = m.memaddrs := by
                dsimp only [post, emptyLocalsHOLFinite]; rw [hm2_eq]; exact heff_mz_comb.memaddrs
              have hpost_sma_m : post.shMemaddrs = m.shMemaddrs := by
                dsimp only [post, emptyLocalsHOLFinite]; rw [hm2_eq]; exact heff_mz_comb.shMemaddrs
              have hpost_ba_m : post.baseAddr = m.baseAddr := by
                dsimp only [post, emptyLocalsHOLFinite]; rw [hm2_eq]; exact heff_mz_comb.baseAddr
              have hApost : ArenaReady post :=
                ⟨guestInv_congr (s := m) hpost_code_m hpost_ma_m hpost_sma_m hpost_ba_m hAm.1,
                 arenaOK_congr hpost_glob_m hAm.2⟩
              have hfm_post : globN s "frame_mem_ptr" ≤ globN post "frame_mem_ptr" := by
                unfold globN; rw [hpost_glob_m]; exact hfm_m
              have hfresh_post : freshIvl = (0, 0) ∨
                  (freshIvl.1 % 8 = 0 ∧ freshIvl.2 % 8 = 0 ∧
                    Inside freshIvl (globN s "frame_mem_ptr") (globN post "frame_mem_ptr")) := by
                unfold globN; rw [hpost_glob_m]; exact hfresh_m
              have hm2_memW_ne32 : ∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 32 →
                  memW post (globN s "ev" + off) = memW m (globN s "ev" + off) := by
                intro off hoff hoff8 hne32
                change memW m2 (globN s "ev" + off) = memW m (globN s "ev" + off)
                rw [hm2_eq, R14Shards.OpHandlersA.memW_updW_ne m1 (globN s "ev" + 32) (globN s "ev" + off) _ (by omega) (by omega) (by omega),
                    hm1_e0_eq off hoff hoff8]
              have hm2_memW_32 : memW post (globN s "ev" + 32) = nlenw.toNat := by
                change memW m2 (globN s "ev" + 32) = nlenw.toNat
                rw [hm2_eq, R14Shards.OpHandlersA.memW_updW_same m1 (globN s "ev" + 32) nlenw]
              have he0_post : ∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 32 → off ≠ 40 →
                  memW post (globN s "ev" + off) = memW s (globN s "ev" + off) := by
                intro off hoff hoff8 h32 h40
                rw [hm2_memW_ne32 off hoff hoff8 h32, he0_m off hoff hoff8 h32 h40]
              have hnew_post :
                  (freshIvl.2 = 0 ∧ memW post (globN s "ev" + 40) = memW s (globN s "ev" + 40) ∧
                    globN post "frame_mem_ptr" = globN s "frame_mem_ptr") ∨
                  (freshIvl.2 ≠ 0 ∧
                    memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = freshIvl.1 ∧
                    memW post (globN s "ev" + 40) = memW s (globN s "ev" + 40) + freshIvl.2 ∧
                    globN post "frame_mem_ptr" = freshIvl.1 + freshIvl.2) := by
                rw [hm2_memW_ne32 40 (by omega) (by omega) (by omega)]
                unfold globN; rw [hpost_glob_m]; exact hnew_m
              have hlen_le_cap_post : memW post (globN s "ev" + 32) ≤ memW post (globN s "ev" + 40) := by
                rw [hm2_memW_32, hm2_memW_ne32 40 (by omega) (by omega) (by omega)]; exact hnlen_le_mcap
              refine ⟨fun v hv => ?_, fun ⟨_, h⟩ => by cases h⟩
              injection hv with hv'; injection hv' with hv''
              exact ⟨hv''.symm, freshIvl, hApost, hfm_post, heff_total, hfresh_post, he0_post, hnew_post,
                hlen_le_cap_post, by rw [hm2_memW_32, hnlenw_nat, hlenw_eq]⟩
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
        have hcmp_grow : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
            (.cmp .lower (.var .local (ofString "cap")) (.var .local (ofString "nlen"))) =
            some (.val (.word (if capw < nlenw then 1 else 0))) := by
          simp [evalHOLExact, hs3_cap, hs3_nlen, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        rw [hcmp_grow] at hnt ⊢; dsimp only at hnt ⊢
        by_cases hgrow : capw < nlenw
        · have hcap_lt_nlen : capw.toNat < nlenw.toNat := BitVec.lt_def.1 hgrow
          simp only [hgrow, ↓reduceIte, h10] at hnt ⊢
          dsimp only [growBranch] at hnt ⊢
          rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
          have hmul2 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
              (.panop .mul [.var .local (ofString "cap"), .const 2#64]) =
              some (.val (.word (capw * 2#64))) := by
            simp [evalHOLExact, evalListHOLExact, hs3_cap, panOpHOL, valueIsWord, valueWord]
          rw [hmul2] at hnt ⊢; dsimp only at hnt ⊢
          have hsh_ncap : shapeEqHOL .one (shapeOfHOLExact (.val (.word (capw * 2#64)))) = true := by
            simp [shapeEqHOL, shapeOfHOLExact]
          rw [if_pos hsh_ncap] at hnt ⊢; dsimp only at hnt ⊢
          set s4 := setVarHOLFinite (ofString "ncap") (.val (.word (capw * 2#64))) s3 with hs4
          have hncap0_nat : (capw * 2#64).toNat = 2 * capw.toNat := by
            have : (2#64 : BitVec 64).toNat = 2 := rfl
            rw [BitVec.toNat_mul, this, Nat.mod_eq_of_lt (by omega)]; omega
          have hite_ncap : ∃ (s5 : PanSemStateFiniteExact 64 F) (ncapw : BitVec 64),
              evaluateHOLFiniteState s4
                (.ite (.cmp .lower (.var .local (ofString "ncap")) (.var .local (ofString "nlen")))
                  (.assign .local (ofString "ncap") (.op .add [.var .local (ofString "nlen"), .const 1024#64]))
                  .skip) = (none, s5) ∧
              s5 = { s with locals := s5.locals, clock := s.clock } ∧
              s5.locals.lookup (ofString "ncap") = some (.val (.word ncapw)) ∧
              s5.locals.lookup (ofString "cap") = some (.val (.word capw)) ∧
              s5.locals.lookup (ofString "len") = some (.val (.word lenw)) ∧
              s5.locals.lookup (ofString "nlen") = some (.val (.word nlenw)) ∧
              s5.locals.lookup (ofString "expand_by") = some (.val (.word ebw)) ∧
              nlenw.toNat ≤ ncapw.toNat ∧ capw.toNat < ncapw.toNat ∧
              ncapw.toNat < 2 ^ 38 ∧ ncapw.toNat % 8 = 0 := by
            have hnlenw_al8 : nlenw.toNat % 8 = 0 := by
              rw [hnlenw_nat, hlenw_eq]; exact hnlen_al8
            have hcapw_al8 : capw.toNat % 8 = 0 := by
              rw [hcapw_eq]; exact hmem40_8
            have hs4_ncap : s4.locals.lookup (ofString "ncap") = some (.val (.word (capw * 2#64))) := by
              simp [hs4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have hs4_nlen : s4.locals.lookup (ofString "nlen") = some (.val (.word nlenw)) := by
              simp [hs4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_nlen,
                show ofString "ncap" ≠ ofString "nlen" by decide]
            rw [evaluateHOLFiniteState_ite]
            have hcmp_nc : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
                (.cmp .lower (.var .local (ofString "ncap")) (.var .local (ofString "nlen"))) =
                some (.val (.word (if capw * 2#64 < nlenw then 1 else 0))) := by
              simp [evalHOLExact, hs4_ncap, hs4_nlen, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
            rw [hcmp_nc]; dsimp only
            by_cases hlt_nl : capw * 2#64 < nlenw
            · simp only [hlt_nl, ↓reduceIte, h10, evaluateHOLFiniteState_assign]
              have hev_add1024 : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
                  (.op .add [.var .local (ofString "nlen"), .const 1024#64]) =
                  some (.val (.word (nlenw + 1024#64))) := by
                simp [evalHOLExact, evalListHOLExact, hs4_nlen, wordOpHOL, wordOp, valueIsWord, valueWord]
              have hval_nc : s4.isValidValueHOLFinite .local (ofString "ncap") (.val (.word (nlenw + 1024#64))) = true := by
                simp [isValidValueHOLFinite, lookupKvarHOLFinite, hs4_ncap, shapeOfHOLExact, shapeEqHOL]
              rw [hev_add1024]; dsimp only; rw [if_pos hval_nc]
              let s5 := setKvarHOLFinite .local (ofString "ncap") (.val (.word (nlenw + 1024#64))) s4
              have hnl1024_nat : (nlenw + 1024#64).toNat = nlenw.toNat + 1024 := by
                rw [BitVec.toNat_add, show (1024#64 : BitVec 64).toNat = 1024 from rfl, Nat.mod_eq_of_lt (by omega)]
              refine ⟨s5, nlenw + 1024#64, rfl, by cases s; rfl,
                by simp [s5, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
                by simp [s5, hs4, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_cap, (by decide : ofString "ncap" ≠ ofString "cap")],
                by simp [s5, hs4, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_len, (by decide : ofString "ncap" ≠ ofString "len")],
                by simp [s5, hs4, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_nlen, (by decide : ofString "ncap" ≠ ofString "nlen")],
                by simp [s5, hs4, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_eb, (by decide : ofString "ncap" ≠ ofString "expand_by")],
                by omega, by omega, by omega, by omega⟩
            · simp only [hlt_nl, ↓reduceIte, evaluateHOLFiniteState_skip]
              have hge_nl : nlenw.toNat ≤ (capw * 2#64).toNat := by rw [BitVec.lt_def] at hlt_nl; omega
              exact ⟨s4, capw * 2#64, rfl, by cases s; rfl, hs4_ncap,
                by simp [hs4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_cap, (by decide : ofString "ncap" ≠ ofString "cap")],
                by simp [hs4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_len, (by decide : ofString "ncap" ≠ ofString "len")],
                hs4_nlen,
                by simp [hs4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_eb, (by decide : ofString "ncap" ≠ ofString "expand_by")],
                hge_nl, by omega, by omega, by omega⟩
          obtain ⟨s5, ncapw, hs5_run, hs5_eq, hs5_ncap, hs5_cap, hs5_len, hs5_nlen, hs5_eb,
            hnlen_le_ncap, hcap_lt_ncap, hncap_lt, hncap_al8⟩ := hite_ncap
          rw [evaluateHOLFiniteState_seq_line780, hs5_run] at hnt ⊢; dsimp only at hnt ⊢
          set diffw := ncapw - capw
          have hdiff_nat : diffw.toNat = ncapw.toNat - capw.toNat :=
            BitVec.toNat_sub_of_le (BitVec.le_def.2 (Nat.le_of_lt hcap_lt_ncap))
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt ⊢
          have hs5_code : s5.code = originalRuntimeCode := by rw [hs5_eq]; exact hcode
          have hargs_fma : evalListHOLFinite s5 (h := fun a => Classical.propDecidable (s5.memaddrs a))
              [.op .sub [.var .local (ofString "ncap"), .var .local (ofString "cap")]] =
              some [.val (.word diffw)] := by
            simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs5_ncap, hs5_cap,
              wordOpHOL, wordOp, valueIsWord, valueWord, diffw]
          have hlk_fma := pan_one_word_lookup s5.code.lookup (ofString "frame_mem_alloc") (ofString "n")
            (sourceFnBody Guest.Software.guestFn_frame_mem_alloc) diffw
            (by rw [hs5_code]; exact lookup_frame_mem_alloc)
          rw [hargs_fma] at hnt ⊢; dsimp only at hnt ⊢
          rw [hlk_fma] at hnt ⊢; dsimp only at hnt ⊢
          by_cases hs5_clk0 : s5.clock = 0
          · rw [if_pos hs5_clk0] at hnt; simp at hnt
          · rw [if_neg hs5_clk0] at hnt ⊢
            let fmaCallee := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word diffw))
            let fmaEntry := callEntryStateHOLFinite s5 fmaCallee
            have hfma_code : fmaEntry.code = originalRuntimeCode := hs5_code
            have hfma_no_evmErr := frame_mem_alloc_body_no_evmErr fmaEntry hfma_code
            rcases hfma_run : evaluateHOLFiniteState fmaEntry
                (sourceFnBody Guest.Software.guestFn_frame_mem_alloc) with ⟨rfma, fmaPost⟩
            rw [hfma_run] at hfma_no_evmErr
            dsimp only [fmaEntry, fmaCallee] at hfma_run; simp only [hfma_run] at hnt ⊢
            cases rfma with
            | none => exact herr_triv
            | some rfma0 =>
              cases rfma0 with
              | timeOut => simp at hnt
              | exception eid ev =>
                dsimp only at hnt ⊢
                by_cases heid : eid = ofString "EvmErr"
                · subst heid; exact absurd ⟨ev, rfl⟩ hfma_no_evmErr
                · constructor
                  · intro _ h; cases h
                  · rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
              | «break» | «continue» | error => exact herr_triv
              | finalFfi _ =>
                constructor
                · intro _ h; cases h
                · rintro ⟨_, h⟩; cases h
              | returned vfma =>
                have hfma_fp_lk : fmaEntry.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fp_w)) := by
                  change s5.globals.lookup _ = _; rw [hs5_eq]; exact hfp_lk
                have hfma_sp_lk : fmaEntry.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp_g_w)) := by
                  change s5.globals.lookup _ = _; rw [hs5_eq]; exact hsp_g_lk
                have hfma_n_lk : fmaEntry.locals.lookup (ofString "n") = some (.val (.word diffw)) := by
                  simp [fmaEntry, fmaCallee, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                obtain ⟨rfl, hcmp1_fma, hcmp2_fma, hfmaPost_eq_raw⟩ :=
                  frame_mem_alloc_body_run fmaEntry fp_w sp_g_w diffw
                    hfma_code hfma_fp_lk hfma_sp_lk hfma_n_lk vfma (by rw [hfma_run])
                have hfmaPost_eq : fmaPost = { fmaEntry with
                    globals := fmaEntry.globals.update (ofString "frame_mem_ptr",
                      .val (.word ((fp_w + (diffw + 7)) &&& ((0 : BitVec 64) - 8)))),
                    locals := fmaPost.locals,
                    clock := fmaPost.clock } := by
                  rw [hfma_run] at hfmaPost_eq_raw; exact hfmaPost_eq_raw
                dsimp only [fmaEntry] at hfmaPost_eq
                set qw : BitVec 64 := (fp_w + (diffw + 7)) &&& ((0 : BitVec 64) - 8)
                have hsh_p : shapeEqHOL (shapeOfHOLExact (.val (.word fp_w) : ValueHOL 64)) .one = true := by
                  simp [shapeEqHOL, shapeOfHOLExact]
                dsimp only at hnt ⊢
                simp only [hsh_p, ↓reduceIte] at hnt ⊢
                have hfp_le_sp_g : fp_w.toNat ≤ sp_g_w.toNat := by
                  have := hInv.1.2.2.2.2.1; omega
                have hsp_g_le_se : sp_g_w.toNat ≤ scratchEnd := by
                  have := hInv.1.2.2.2.2.2.1; omega
                have hfp_al8 : fp_w.toNat % 8 = 0 := by
                  have h8 : globN s "frame_mem_ptr" % 8 = 0 := hInv.1.2.2.2.2.2.2.2.1
                  rw [hfp_nat]; exact h8
                obtain ⟨hq_nat, hq_le_sp, hq_al8, hfp_le_q⟩ :=
                  frame_mem_alloc_arith fp_w sp_g_w diffw hfp_le_sp_g hsp_g_le_se hfp_al8 hcmp1_fma hcmp2_fma
                have hdiff_al8 : diffw.toNat % 8 = 0 := by
                  have hcapw_al8 : capw.toNat % 8 = 0 := by rw [hcapw_eq]; exact hmem40_8
                  omega
                have hqw_nat : qw.toNat = fp_w.toNat + diffw.toNat := by
                  have halign_eq : (diffw.toNat + 7) / 8 * 8 = diffw.toNat := by omega
                  change qw.toNat = _ at hq_nat; omega
                have hqw_al8 : qw.toNat % 8 = 0 := hq_al8
                have hqw_le_sp : qw.toNat ≤ sp_g_w.toNat := hq_le_sp
                set s6 : PanSemStateFiniteExact 64 F := { fmaPost with locals := s5.locals } with hs6_def
                have hs6_glob : s6.globals = s.globals.update (ofString "frame_mem_ptr", .val (.word qw)) := by
                  change fmaPost.globals = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq]
                have hs6_code : s6.code = originalRuntimeCode := by
                  change fmaPost.code = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; exact hs5_code
                have hs6_ma : s6.memaddrs = ordinaryDomain := by
                  change fmaPost.memaddrs = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]
                  rw [hs5_eq]; exact hInv.1.1.memaddrs
                have hs6_mem : s6.memory = s.memory := by
                  change fmaPost.memory = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq]
                have hs6_ev : s6.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
                  rw [hs6_glob]
                  simp [HolFiniteMapExact.lookup_update, FUPDATE,
                    show ofString "frame_mem_ptr" ≠ ofString "ev" by decide, hevw]
                have hev24_eq : evw + 24#64 = BitVec.ofNat 64 (globN s "ev" + 24) :=
                  BitVec.eq_of_toNat_eq (by
                    rw [BitVec.toNat_add, hevw_nat, show (24#64 : BitVec 64).toNat = 24 from rfl, BitVec.toNat_ofNat])
                have hs6_dom24 : s6.memaddrs (evw + 24#64) := by
                  rw [hs6_ma, ← hInv.1.1.memaddrs, hev24_eq]
                  exact ((hFW0.1 (globN s "ev", 280) (by simp)).2.2.2 3 (by omega)).choose_spec.1
                rcases hs_m24 : s.memory (evw + 24#64) with ⟨memPtrW⟩
                have hs6_m24 : s6.memory (evw + 24#64) = .word memPtrW := by rw [hs6_mem, hs_m24]
                have hmemPtrW_nat : memPtrW.toNat = memW s (globN s "ev" + 24) := by
                  unfold memW; rw [← hev24_eq, hs_m24]
                let freshIvl : Ivl := (globN s "frame_mem_ptr", diffw.toNat)
                let mzGrowDst : ExpHOL 64 :=
                  .op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "cap")]
                let mzGrowN : ExpHOL 64 :=
                  .op .sub [.var .local (ofString "ncap"), .var .local (ofString "cap")]
                have hev_mzg_dst : @evalHOLExact 64 F _ s6.toExact (fun a => Classical.propDecidable (s6.memaddrs a)) mzGrowDst =
                    some (.val (.word (memPtrW + capw))) := by
                  have hs6_cap : s6.locals.lookup (ofString "cap") = some (.val (.word capw)) := hs5_cap
                  simp [mzGrowDst, evalHOLExact, evalListHOLExact, hs6_ev, hs6_cap, wordOpHOL, wordOp,
                    valueIsWord, valueWord, memLoadHOLExact, hs6_dom24, hs6_m24]
                have hev_mzg_n : @evalHOLExact 64 F _ s6.toExact (fun a => Classical.propDecidable (s6.memaddrs a)) mzGrowN =
                    some (.val (.word diffw)) := by
                  have hs6_ncap : s6.locals.lookup (ofString "ncap") = some (.val (.word ncapw)) := hs5_ncap
                  have hs6_cap : s6.locals.lookup (ofString "cap") = some (.val (.word capw)) := hs5_cap
                  simp [mzGrowN, evalHOLExact, evalListHOLExact, hs6_ncap, hs6_cap, wordOpHOL, wordOp,
                    valueIsWord, valueWord, diffw]
                have hmzg_dst_nat : (memPtrW + capw).toNat = globN s "frame_mem_ptr" := by
                  rw [BitVec.toNat_add, hmemPtrW_nat, hcapw_eq, hmem_end_fp, Nat.mod_eq_of_lt (by omega)]
                rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
                have hnt_mzg : (evaluateHOLFiniteState s6 (.call (some (none, none)) (ofString "memzero") [mzGrowDst, mzGrowN])).1 ≠ some .timeOut := by
                  intro hto; rcases hmzg_to : evaluateHOLFiniteState s6 (.call (some (none, none)) (ofString "memzero") [mzGrowDst, mzGrowN]) with ⟨rmzg_to, smzg_to⟩
                  rw [hmzg_to] at hto; dsimp only at hto; subst hto; dsimp only [mzGrowDst, mzGrowN] at hmzg_to; simp only [hmzg_to] at hnt; exact hnt rfl
                have hmzg := eval_call_memzero_bre s6 mzGrowDst mzGrowN
                  (memPtrW + capw) diffw [freshIvl] hs6_code hs6_ma hev_mzg_dst hev_mzg_n
                  (fun _ => ⟨freshIvl, by simp, by rw [hmzg_dst_nat]; dsimp only [freshIvl]; omega⟩) hnt_mzg
                dsimp only at hmzg
                rcases hmzg_run : evaluateHOLFiniteState s6 (.call (some (none, none)) (ofString "memzero") [mzGrowDst, mzGrowN]) with ⟨rmzg, s7⟩
                rw [hmzg_run] at hmzg; dsimp only [mzGrowDst, mzGrowN] at hmzg_run; simp only [hmzg_run] at hnt ⊢
                cases rmzg with
                | some rmzg0 =>
                  dsimp only at hnt ⊢
                  have hnr := hmzg.2 (by simp)
                  refine ⟨fun v hv => absurd (Or.inl ⟨v, hv⟩) hnr, ?_⟩
                  rintro ⟨ev, hv⟩
                  injection hv with hv'; subst hv'
                  exact hnr (Or.inr ⟨ofString "EvmErr", ev, rfl, by decide⟩)
                | none =>
                  dsimp only at hnt ⊢
                  obtain ⟨heff_mzg, hs7_loc⟩ := hmzg.1 rfl
                  rcases hst40 : evaluateHOLFiniteState s7
                      (.store (.op .add [.var .global (ofString "ev"), .const 40#64]) (.var .local (ofString "ncap"))) with ⟨rst40, s8⟩
                  simp only [hst40] at hnt ⊢
                  cases rst40 with
                  | some res40 =>
                    have herr := store_some_eq_error' hst40; subst herr; dsimp only; exact herr_triv
                  | none =>
                    dsimp only at hnt ⊢
                    have hs7_ev : s7.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
                      rw [heff_mzg.globals]; exact hs6_ev
                    have hs7_ncap : s7.locals.lookup (ofString "ncap") = some (.val (.word ncapw)) := by
                      rw [hs7_loc]; exact hs5_ncap
                    obtain ⟨w_ncap', hw_ncap_ev, hs8_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s7) (post := s8)
                      (gname := "ev") (gbase := globN s "ev") (off := 40) hs7_ev hevw_nat (by omega)
                      (fun v hv => by
                        change s7.locals.lookup (ofString "ncap") = some v at hv
                        rw [hs7_ncap] at hv; injection hv with hv'; exact ⟨ncapw, hv'.symm⟩) hst40
                    have hw_ncap_val : ncapw = w_ncap' := by
                      change s7.locals.lookup (ofString "ncap") = some (.val (.word w_ncap')) at hw_ncap_ev
                      rw [hs7_ncap] at hw_ncap_ev
                      injection hw_ncap_ev with h1; injection h1 with h2; injection h2 with h3
                    subst w_ncap'
                    have heff_st40 := (ByteRegionEffect.of_store_word (Rl := [(globN s "ev", 280)])
                      (heff_mzg.memaddrs.trans hs6_ma) hst40
                      (fun v hv => by
                        change s7.locals.lookup (ofString "ncap") = some v at hv
                        rw [hs7_ncap] at hv; injection hv with hv'; exact ⟨ncapw, hv'.symm⟩)
                      (fun addr hdst _ => by
                        simp [evalHOLExact, evalListHOLExact, hs7_ev, wordOpHOL, wordOp, valueIsWord, valueWord] at hdst
                        have h40_eq : (evw + 40#64).toNat = globN s "ev" + 40 := by
                          have : (40#64 : BitVec 64).toNat = 40 := rfl
                          rw [BitVec.toNat_add, hevw_nat, this, Nat.mod_eq_of_lt (by omega)]
                        exact ⟨(globN s "ev", 280), by simp, by rw [← hdst, h40_eq]; dsimp only; omega,
                          by rw [← hdst, h40_eq]; dsimp only; omega⟩)).1
                    let m : PanSemStateFiniteExact 64 F :=
                      { s8 with locals := s8.locals.resVarEq (ofString "ncap", s3.locals.lookup (ofString "ncap")) }
                    have hm_glob : m.globals = s.globals.update (ofString "frame_mem_ptr", .val (.word qw)) := by
                      dsimp only [m]; rw [hs8_eq]; dsimp only; rw [heff_mzg.globals, hs6_glob]
                    have hm_fp_glob : globN m "frame_mem_ptr" = qw.toNat := by
                      unfold globN; rw [hm_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
                    have hm_other_glob : ∀ g : String, ofString g ≠ ofString "frame_mem_ptr" →
                        m.globals.lookup (ofString g) = s.globals.lookup (ofString g) := by
                      intro g hg; rw [hm_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hg, Ne.symm hg]
                    have hm_G : GuestInv m := guestInv_congr
                      (by dsimp only [m]; rw [hs8_eq]; dsimp only; rw [heff_mzg.code, hs6_code, hcode])
                      (by dsimp only [m]; rw [hs8_eq]; dsimp only; rw [heff_mzg.memaddrs, hs6_ma, hInv.1.1.memaddrs])
                      (by dsimp only [m]; rw [hs8_eq]; dsimp only; rw [heff_mzg.shMemaddrs]; change fmaPost.shMemaddrs = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq])
                      (by dsimp only [m]; rw [hs8_eq]; dsimp only; rw [heff_mzg.baseAddr]; change fmaPost.baseAddr = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq])
                      hInv.1.1
                    have hfm_m : globN s "frame_mem_ptr" ≤ globN m "frame_mem_ptr" := by
                      rw [hm_fp_glob, hqw_nat, hfp_nat]; omega
                    have hAm : ArenaReady m := by
                      refine ⟨hm_G, ?_⟩
                      unfold ArenaOK
                      have hhp_m : globN m "heap_ptr" = globN s "heap_ptr" :=
                        R16Shards.OpHandlers.globN_eq_of_lookup_eq (hm_other_glob "heap_ptr" (by decide))
                      have hsp_m : globN m "scratch_ptr" = globN s "scratch_ptr" :=
                        R16Shards.OpHandlers.globN_eq_of_lookup_eq (hm_other_glob "scratch_ptr" (by decide))
                      rw [hhp_m, hm_fp_glob, hsp_m]
                      have hA := hInv.1.2
                      have hss_le_fp : scratchStart ≤ globN s "frame_mem_ptr" := hA.2.2.1
                      exact ⟨hA.1, hA.2.1, by rw [hqw_nat, hfp_nat]; omega, by rw [← hsp_g_nat]; exact hqw_le_sp,
                        hA.2.2.2.2.1, hA.2.2.2.2.2.1, hqw_al8, hA.2.2.2.2.2.2.2.1,
                        globalsWord_update (ofString "frame_mem_ptr") qw hm_glob hA.2.2.2.2.2.2.2.2⟩
                    have heff_s_s6 : FrameMemByteEff s s6 [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))] :=
                      ⟨hs6_code.trans hcode.symm,
                       hs6_ma.trans hInv.1.1.memaddrs.symm,
                       by change fmaPost.shMemaddrs = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq],
                       by change fmaPost.baseAddr = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq],
                       by change fmaPost.be = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq],
                       fun g hg => by
                         change fmaPost.globals.lookup (ofString g) = _; rw [hfmaPost_eq]
                         dsimp only [callEntryStateHOLFinite]; rw [hs5_eq]
                         simp [HolFiniteMapExact.lookup_update, FUPDATE, hg, Ne.symm hg],
                       fun a _ => by rw [hs6_mem],
                       fun a _ => by rw [hs6_mem],
                       fun b _ _ => by
                         unfold memB; rw [hs6_mem]
                         have hbe6 : s6.be = s.be := by
                           change fmaPost.be = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq]
                         rw [hbe6]⟩
                    have heff_m : FrameMemByteEff s m
                        [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))] := by
                      have h1 := (FrameMemByteEff.of_bre heff_mzg).mono
                        (R2 := [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))])
                        (fun x hx => by simp at hx; subst hx; exact ⟨freshIvl, by simp, le_refl _, le_refl _⟩)
                      have h2 := (FrameMemByteEff.of_bre heff_st40).mono
                        (R2 := [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))])
                        (fun x hx => by simp at hx; subst hx; exact ⟨(globN s "ev", 280), by simp, le_refl _, le_refl _⟩)
                      exact ((heff_s_s6.trans h1).trans h2).with_locals_clock m.locals s8.clock
                    have hs7_e0_eq : ∀ off, off + 8 ≤ 280 → off % 8 = 0 →
                        memW s7 (globN s "ev" + off) = memW s (globN s "ev" + off) := by
                      intro off hoff hoff8
                      unfold memW
                      rw [heff_mzg.cell_frame (BitVec.ofNat 64 (globN s "ev" + off)), hs6_mem]
                      intro x hx; simp at hx; subst hx
                      have htn : (BitVec.ofNat 64 (globN s "ev" + off)).toNat = globN s "ev" + off :=
                        Nat.mod_eq_of_lt (by omega)
                      rw [htn]
                      have he0_8 : (globN s "ev") % 8 = 0 := (hFW0.1 (globN s "ev", 280) (by simp)).2.1
                      have ha8 : (globN s "ev" + off) % 8 = 0 := by omega
                      have hfp_s_8 : globN s "frame_mem_ptr" % 8 = 0 := hInv.1.2.2.2.2.2.2.2.1
                      obtain ⟨he0_scr, _⟩ := (hFW0.1 (globN s "ev", 280) (by simp)).1
                      exact not_cellHits_of_disj_aligned (i := (globN s "ev", 280)) ha8 hfp_s_8
                        (Nat.le_add_right _ off) (Nat.add_le_add_left hoff _)
                        (Or.inr (Or.inr (Or.inr (by dsimp only [freshIvl] at he0_scr ⊢; omega))))
                    have hm_e0_other : ∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 32 → off ≠ 40 →
                        memW m (globN s "ev" + off) = memW s (globN s "ev" + off) := by
                      intro off hoff hoff8 _ hne40
                      change memW s8 (globN s "ev" + off) = memW s (globN s "ev" + off)
                      rw [hs8_eq, R14Shards.OpHandlersA.memW_updW_ne s7 (globN s "ev" + 40) (globN s "ev" + off) _ (by omega) (by omega) (by omega),
                          hs7_e0_eq off hoff hoff8]
                    have hm_e0_40 : memW m (globN s "ev" + 40) = ncapw.toNat := by
                      change memW s8 (globN s "ev" + 40) = ncapw.toNat
                      rw [hs8_eq, R14Shards.OpHandlersA.memW_updW_same s7 (globN s "ev" + 40) ncapw]
                    have hfresh_m : freshIvl = (0, 0) ∨
                        (freshIvl.1 % 8 = 0 ∧ freshIvl.2 % 8 = 0 ∧
                          Inside freshIvl (globN s "frame_mem_ptr") (globN m "frame_mem_ptr")) := by
                      refine Or.inr ⟨hInv.1.2.2.2.2.2.2.2.1, hdiff_al8, ?_⟩
                      rw [hm_fp_glob, hqw_nat, hfp_nat]; dsimp only [freshIvl, Inside]; omega
                    have hnew_m :
                        (freshIvl.2 = 0 ∧ memW m (globN s "ev" + 40) = memW s (globN s "ev" + 40) ∧
                          globN m "frame_mem_ptr" = globN s "frame_mem_ptr") ∨
                        (freshIvl.2 ≠ 0 ∧
                          memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = freshIvl.1 ∧
                          memW m (globN s "ev" + 40) = memW s (globN s "ev" + 40) + freshIvl.2 ∧
                          globN m "frame_mem_ptr" = freshIvl.1 + freshIvl.2) := by
                      refine Or.inr ⟨by dsimp only [freshIvl]; omega, hmem_end_fp, ?_, ?_⟩
                      · rw [hm_e0_40]; dsimp only [freshIvl]; omega
                      · rw [hm_fp_glob, hqw_nat, hfp_nat]
                    have hm_loc_s5 : ∀ k, k ≠ ofString "ncap" → m.locals.lookup k = s5.locals.lookup k := by
                      intro k hk
                      have hres_ne : ∀ (mp : HolFiniteMapExact MlS (ValueHOL 64)) (key q : MlS) (old : Option (ValueHOL 64)),
                          key ≠ q → (mp.resVarEq (key, old)).lookup q = mp.lookup q := by
                        intro mp key q old hne
                        unfold HolFiniteMapExact.resVarEq
                        cases old with
                        | none => simp [HolFiniteMapExact.eraseEq, FDOMSUB_HOL, hne.symm]
                        | some v => simp [HolFiniteMapExact.updateEq, FUPDATE_HOL, hne.symm]
                      have hs8_l : s8.locals = s5.locals := by rw [hs8_eq]; exact hs7_loc
                      dsimp only [m]
                      rw [hres_ne _ _ _ _ hk.symm, hs8_l]
                    have hnt_m : (evaluateHOLFiniteState m tailProg).1 ≠ some .timeOut := by
                      dsimp only [m]; exact hnt
                    exact run_tail m freshIvl hAm hfm_m hm_other_glob heff_m hfresh_m hm_e0_other hnew_m
                      (by rw [hm_e0_40]; exact hnlen_le_ncap)
                      (by rw [hm_loc_s5 (ofString "len") (by decide)]; exact hs5_len)
                      (by rw [hm_loc_s5 (ofString "nlen") (by decide)]; exact hs5_nlen)
                      (by rw [hm_loc_s5 (ofString "expand_by") (by decide)]; exact hs5_eb)
                      hnt_m
        · have hnlen_le_cap : nlenw.toNat ≤ capw.toNat := by
            rw [BitVec.lt_def] at hgrow; omega
          simp only [hgrow, ↓reduceIte, evaluateHOLFiniteState_skip] at hnt ⊢
          exact run_tail s3 (0, 0)
            ⟨guestInv_congr (s := s) rfl rfl rfl rfl hInv.1.1, hInv.1.2⟩
            (le_refl _)
            (fun _ _ => rfl)
            ((FrameMemByteEff.refl s _).with_locals_clock s3.locals s.clock)
            (Or.inl rfl)
            (fun _ _ _ _ _ => rfl)
            (Or.inl ⟨rfl, rfl, rfl⟩)
            (by change nlenw.toNat ≤ memW s (globN s "ev" + 40); rw [← hcapw_eq]; exact hnlen_le_cap)
            hs3_len hs3_nlen hs3_eb hnt

/-! ## 2. Unified `OpDispatchPostBoth` post-`charge_gas` continuation for `op_log` -/

theorem headMemChainWF_of_heap_bre_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {b sz : Nat}
    (hInv : EvmInv s) (hWF : HeadMemChainWF s)
    (heff : ByteRegionEffect s post [(b, sz)])
    (hch : evmChain post = evmChain s)
    (hb8 : b % 8 = 0) (hhi : b + sz ≤ heapLimit) :
    HeadMemChainWF post := by
  refine headMemChainWF_of_disj_bre hInv hWF hch
    (congrFun (globN_congr heff.globals) "ev")
    (congrFun (globN_congr heff.globals) "frame_mem_ptr")
    (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact hb8)
    heff.cell_frame ?_
  intro ec hec x hx
  simp only [List.mem_singleton] at hx; subst hx
  obtain ⟨hAs, _, _, _, _, _, hFW_all, _⟩ := hInv
  have hFW := hFW_all ec hec
  obtain ⟨he_lo, _⟩ := (hFW.1 (ec.1, 280) (by simp)).1
  obtain ⟨hc_lo, _⟩ := (hFW.1 (ec.2, 104) (by simp)).1
  have hsc1 := hAs.2.2.2.1; have hsc2 := hAs.2.2.2.2.1
  have hlim_le : heapLimit ≤ scratchStart := by
    rw [R11Shards.heapLimit_val, R11Shards.scratchStart_val]
  exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (by dsimp only at he_lo ⊢; omega)))),
         Or.inr (Or.inr (Or.inr (Or.inr (by dsimp only at hc_lo ⊢; omega))))⟩

theorem memcpy_heap_both_g09 {F : Type}
    {W : Prop} {s0 s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (dstExp srcExp nExp : ExpHOL 64) (dst src n : BitVec 64) (b sz : Nat) (cont : ProgHOL 64)
    (hc : s.code = originalRuntimeCode) (hw : EvmInvWith s S Nd) (hWF : W → HeadMemChainWF s)
    (hl : (evmChain s).length = (evmChain s0).length) (hr : evmR s < evmR s0)
    (hd : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp = some (.val (.word dst)))
    (hs : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) srcExp = some (.val (.word src)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp = some (.val (.word n)))
    (hb8 : b % 8 = 0) (hhi : b + sz ≤ heapLimit)
    (hsub : 0 < n.toNat → b ≤ dst.toNat ∧ dst.toNat + n.toNat ≤ b + sz)
    (hdj : IvlsDisj [(b, sz)] (worldTypedIvls s S Nd ++ ((evmChain s).map (frameObjects s)).flatten))
    (hcont : ∀ last : PanSemStateFiniteExact 64 F,
      last.code = originalRuntimeCode → EvmInvWith last S Nd → (W → HeadMemChainWF last) →
      (evmChain last).length = (evmChain s0).length → evmR last < evmR s0 →
      ByteRegionEffect s last [(b, sz)] → last.locals = s.locals →
      worldTypedIvls last S Nd = worldTypedIvls s S Nd →
      (evmChain last).map (frameObjects last) = (evmChain s).map (frameObjects s) →
      evmChain last = evmChain s → (HeadMemAligned s → HeadMemAligned last) →
      (evaluateHOLFiniteState last cont).1 ≠ some .timeOut →
      OpDispatchPostBoth W s0 (evaluateHOLFiniteState last cont).1 (evaluateHOLFiniteState last cont).2)
    (hnt : (evaluateHOLFiniteState s (.seq (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp]) cont)).1 ≠ some .timeOut) :
    OpDispatchPostBoth W s0
      (evaluateHOLFiniteState s (.seq (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp]) cont)).1
      (evaluateHOLFiniteState s (.seq (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp]) cont)).2 := by
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  let call := ProgHOL.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp]
  have hnc : (evaluateHOLFiniteState s call).1 ≠ some .timeOut := by
    intro h; rcases hh : evaluateHOLFiniteState s call with ⟨r, post⟩
    rw [hh] at h hnt; dsimp only at h; subst r; exact hnt rfl
  have he := Wave8GuestInv.M11.eval_call_memcpy_bre s dstExp srcExp nExp dst src n [(b, sz)]
    hc hw.1.1.memaddrs hd hs hn (fun hp => ⟨(b, sz), by simp, hsub hp⟩) hnc
  rcases heval : evaluateHOLFiniteState s call with ⟨r, last⟩
  change evaluateHOLFiniteState s (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp]) = (r, last) at heval
  simp only [heval] at hnt he ⊢
  cases r with
  | none =>
    obtain ⟨heff, hlocals⟩ := he.1 rfl
    have heff' := m11_bre_to_m23 heff
    obtain ⟨hwi, hworld, hframes, _, hchain, hR, hHM⟩ := evmInvWith_of_bre hw hdj heff'
    exact hcont last (heff'.code.trans hc) hwi
      (fun hw0 => headMemChainWF_of_heap_bre_g09 (evmInvWith_to_evmInv hw) (hWF hw0) heff' hchain hb8 hhi)
      (by rw [hchain]; exact hl) (by rw [hR]; exact hr) heff' hlocals hworld hframes hchain hHM hnt
  | some _ =>
    refine opDispatchPostBoth_other (fun v hv => he.2 (by simp) (Or.inl ⟨v, hv⟩)) ?_
    rintro ⟨v, hv⟩; exact he.2 (by simp) (Or.inr ⟨ofString "EvmErr", v, hv, by decide⟩)

theorem op_log_while_both_full_g09 {F : Type}
    {W : Prop} {s0 : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {nt topics qw : BitVec 64} {cont : ProgHOL 64} :
    ∀ (rem : Nat) (s : PanSemStateFiniteExact 64 F) (iv : BitVec 64),
      iv.toNat + rem = nt.toNat → nt.toNat ≤ 4 → s.code = originalRuntimeCode →
      EvmInvWith s S Nd → (W → HeadMemChainWF s) →
      (evmChain s).length = (evmChain s0).length → evmR s < evmR s0 →
      topics.toNat + (32 * nt.toNat + 8) ≤ qw.toNat → qw.toNat ≤ heapLimit →
      topics.toNat % 8 = 0 → sourceBase ≤ topics.toNat →
      IvlsDisj [(topics.toNat, qw.toNat - topics.toNat)]
        (worldTypedIvls s S Nd ++ ((evmChain s).map (frameObjects s)).flatten) →
      s.locals.lookup (ofString "i") = some (.val (.word iv)) →
      s.locals.lookup (ofString "ntopics") = some (.val (.word nt)) →
      s.locals.lookup (ofString "topics") = some (.val (.word topics)) →
      (∀ (s_end : PanSemStateFiniteExact 64 F),
        s_end.code = originalRuntimeCode → EvmInvWith s_end S Nd → (W → HeadMemChainWF s_end) →
        worldTypedIvls s_end S Nd = worldTypedIvls s S Nd →
        (evmChain s_end).map (frameObjects s_end) = (evmChain s).map (frameObjects s) →
        evmChain s_end = evmChain s → evmR s_end < evmR s0 →
        (∀ g : String, globN s_end g = globN s g) →
        (∀ ec ∈ evmChain s, memW s_end (ec.1 + 112) = memW s (ec.1 + 112)) →
        memW s_end (globN s "ev" + 32) = memW s (globN s "ev" + 32) →
        (HeadMemAligned s → HeadMemAligned s_end) →
        (∀ nm : MlS, nm ≠ ofString "i" → nm ≠ ofString "t" → s_end.locals.lookup nm = s.locals.lookup nm) →
        (evaluateHOLFiniteState s_end cont).1 ≠ some .timeOut →
        OpDispatchPostBoth W s0 (evaluateHOLFiniteState s_end cont).1 (evaluateHOLFiniteState s_end cont).2) →
      (evaluateHOLFiniteState s (.seq opLogWhileProg cont)).1 ≠ some .timeOut →
      OpDispatchPostBoth W s0
        (evaluateHOLFiniteState s (.seq opLogWhileProg cont)).1
        (evaluateHOLFiniteState s (.seq opLogWhileProg cont)).2 := by
  intro rem; induction rem with
  | zero =>
    intro s iv hiv _ hcode hInvW hWF _ hR _ _ _ _ _ hi_lu hnt_lu _ hcont hnt_seq
    have hiv_eq : iv = nt := BitVec.eq_of_toNat_eq (by omega); subst hiv_eq
    have hslt_ff : Compiler.Encoders.Asm.holAsmSignedLess iv iv = false := by
      rw [holAsmSignedLess_eq_slt_g09]; simp [BitVec.slt]
    rw [evaluateHOLFiniteState_seq_line780] at hnt_seq ⊢
    rcases hw : evaluateHOLFiniteState s opLogWhileProg with ⟨rw0, sw0⟩
    have hw' := hw; unfold opLogWhileProg at hw'; rw [evaluateHOLFiniteState_while_fixClockRewrite] at hw'
    have hcmp0 : PanSemStateFiniteExact.evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "ntopics"))) = some (.val (.word 0)) := by
      simp [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact, hi_lu, hnt_lu,
        Compiler.Encoders.Asm.wordCmpHOL, hslt_ff]
    rw [hcmp0] at hw'; simp only [ne_eq, not_true_eq_false, ↓reduceIte] at hw'
    injection hw' with hrw hsw; subst hrw hsw; rw [hw] at hnt_seq; dsimp only at hnt_seq ⊢
    exact hcont s hcode hInvW hWF rfl rfl rfl hR (fun _ => rfl) (fun _ _ => rfl) rfl id (fun _ _ _ => rfl) hnt_seq
  | succ rem ih =>
    intro s iv hiv hnt4 hcode hInvW hWF hlen hR htop_le hq_lim htop_mod8 htop_lo hdj hi_lu hnt_lu htop_lu hcont hnt_seq
    have hiv_lt : iv.toNat < nt.toNat := by omega
    have hslt_tt : Compiler.Encoders.Asm.holAsmSignedLess iv nt = true := by
      rw [holAsmSignedLess_eq_slt_g09, BitVec.slt_eq_decide, BitVec.toInt_eq_msb_cond,
        BitVec.toInt_eq_msb_cond, BitVec.msb_eq_decide, BitVec.msb_eq_decide]
      have h263 : (2 ^ 63 : Nat) = 9223372036854775808 := by norm_num
      rw [decide_eq_false (show ¬ 2 ^ 63 ≤ iv.toNat by omega),
          decide_eq_false (show ¬ 2 ^ 63 ≤ nt.toNat by omega)]
      simp [decide_eq_true_eq]; omega
    rw [evaluateHOLFiniteState_seq_line780] at hnt_seq ⊢
    rcases hw : evaluateHOLFiniteState s opLogWhileProg with ⟨rw0, sw0⟩
    have hw' := hw
    conv_lhs at hw' => unfold opLogWhileProg; rw [evaluateHOLFiniteState_while_fixClockRewrite]
    have hcmp1 : PanSemStateFiniteExact.evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "ntopics"))) = some (.val (.word 1)) := by
      simp [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact, hi_lu, hnt_lu,
        Compiler.Encoders.Asm.wordCmpHOL, hslt_tt]
    rw [hcmp1] at hw'
    simp only [ne_eq, (by decide : (1 : BitVec 64) ≠ 0), not_false_eq_true, ↓reduceIte] at hw'
    by_cases hclk0 : s.clock = 0
    · simp only [hclk0, ↓reduceIte] at hw'
      injection hw' with hrw hsw; subst hrw hsw; rw [hw] at hnt_seq; simp at hnt_seq
    · simp only [hclk0, ↓reduceIte] at hw'
      have hbody_step := op_log_while_body_step_g09 hiv_lt hnt4 hcode hInvW htop_le hq_lim htop_mod8 hdj hi_lu htop_lu
      have hbody_wf : W → (let out := evaluateHOLFiniteState (decClockHOLFinite s) opLogWhileBody;
          (out.1 = none ∨ IsEvmErr out.1) → HeadMemChainWF out.2) :=
        fun hw_s => op_log_while_body_hmwf_g09 hiv_lt hnt4 hcode hInvW (hWF hw_s) htop_le hq_lim htop_mod8 hdj hi_lu htop_lu
      dsimp only at hbody_step hbody_wf
      rcases hbody : evaluateHOLFiniteState (decClockHOLFinite s) opLogWhileBody with ⟨rb, sb⟩
      change evaluateHOLFiniteState (decClockHOLFinite s) opLogWhileBody = (rb, sb) at hbody
      rw [hbody] at hw' hbody_step hbody_wf; dsimp only at hw' hbody_step hbody_wf
      cases rb with
      | none =>
        obtain ⟨hsb_code, hsb_InvW, hsb_wti, hsb_fo, hsb_ch, hsb_R, _, hsb_HM, hsb_i, hsb_loc⟩ := hbody_step.1 rfl
        have hsb_glob_msg : (∀ g : String, globN sb g = globN s g) ∧
            (∀ ec ∈ evmChain s, memW sb (ec.1 + 112) = memW s (ec.1 + 112)) ∧
            memW sb (globN s "ev" + 32) = memW s (globN s "ev" + 32) := by
          have hbody' := hbody; unfold opLogWhileBody at hbody'
          dsimp only [InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
            InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
            InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
            InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
            List.map, Option.map] at hbody'
          rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hbody'
          have hlk_sp : lookupCodeHOLFinite (decClockHOLFinite s).code.lookup (ofString "stack_pop") [] =
              some (sourceFnBody Guest.Software.guestFn_stack_pop, HolFiniteMapExact.empty, ShapeHOL.comb [.one, .one, .one, .one]) := by
            have raw : lookupCodeHOLExact (decClockHOLFinite s).code.lookup (ofString "stack_pop") [] =
                some (sourceFnBody Guest.Software.guestFn_stack_pop, (fun _ => none), ShapeHOL.comb [.one, .one, .one, .one]) := by
              simp [lookupCodeHOLExact, decClockHOLFinite, hcode, lookup_stack_pop_pub]
            unfold PanSemStateFiniteExact.lookupCodeHOLFinite; split
            · rename_i m; rw [raw] at m; cases m
            · rename_i fb fl fs fd
              obtain ⟨rfl, r2⟩ := Prod.mk.inj (Option.some.inj (fd.symm.trans raw))
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj r2
              exact congrArg (fun lc => some (sourceFnBody Guest.Software.guestFn_stack_pop, lc, _))
                (HolFiniteMapExact.ext (funext fun _ => rfl))
          simp only [show evalListHOLFinite (decClockHOLFinite s) (h := fun a => Classical.propDecidable ((decClockHOLFinite s).memaddrs a)) [] = some [] from rfl,
            hlk_sp] at hbody'
          split at hbody'
          · cases hbody'
          · rcases hsp_r : evaluateHOLFiniteState (callEntryStateHOLFinite (decClockHOLFinite s) HolFiniteMapExact.empty)
              (sourceFnBody Guest.Software.guestFn_stack_pop) with ⟨rsp, ssp⟩
            simp only [hsp_r] at hbody'
            cases rsp with
            | none => cases hbody'
            | some rsp0 =>
              cases rsp0 with
              | timeOut | error | «break» | «continue» | finalFfi _ | exception _ _ => cases hbody'
              | returned tv =>
                dsimp only at hbody'; split at hbody'
                · rename_i hsh_tv
                  have hent_eq : callEntryStateHOLFinite (decClockHOLFinite s) HolFiniteMapExact.empty =
                      { s with locals := HolFiniteMapExact.empty, clock := (decClockHOLFinite s).clock - 1 } := by cases s; rfl
                  have hsp_r' := hsp_r; rw [hent_eq] at hsp_r'
                  have hsp_st := stack_pop_body_evmInvWith
                    (evmInvWith_localsFree (s := s) HolFiniteMapExact.empty ((decClockHOLFinite s).clock - 1) hInvW)
                    (by rw [hsp_r']; exact Or.inl ⟨tv, rfl⟩)
                  rw [hsp_r'] at hsp_st; dsimp only at hsp_st
                  obtain ⟨hssp_IW, _, _, hssp_gl, hssp_ma, _, _, _, hssp_mem⟩ := hsp_st
                  let s1 : PanSemStateFiniteExact 64 F := setVarHOLFinite (ofString "t") tv { ssp with locals := (decClockHOLFinite s).locals }
                  let out_i : BitVec 64 := topics + BitVec.ofNat 64 (32 * iv.toNat)
                  have hout_i_nat : out_i.toNat = topics.toNat + 32 * iv.toNat := by
                    have := R11Shards.heapLimit_val; dsimp only [out_i]
                    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                  rw [evaluateHOLFiniteState_seq_line780] at hbody'
                  rcases hu_c : evaluateHOLFiniteState s1 (.call (some (none, none)) (ofString "u256_to_be32")
                      [.var .local (ofString "t"), .op .add [.var .local (ofString "topics"), .panop .mul [.var .local (ofString "i"), .const 32#64]]]) with ⟨ru, su⟩
                  have hu_c' := hu_c
                  have hmul_ev : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
                      (.panop .mul [.var .local (ofString "i"), .const 32#64]) = some (.val (.word (BitVec.ofNat 64 (32 * iv.toNat)))) := by
                    have hmul_eq : iv * 32#64 = BitVec.ofNat 64 (32 * iv.toNat) := BitVec.eq_of_toNat_eq (by
                      rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mul_comm])
                    have hs1_i : s1.locals.lookup (ofString "i") = some (.val (.word iv)) := by
                      simp [s1, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                        (by decide : ofString "t" ≠ ofString "i"), hi_lu]
                    simp [evalHOLExact, evalListHOLExact, hs1_i, valueIsWord, valueWord, panOpHOL, hmul_eq]
                  have hs1_top : s1.locals.lookup (ofString "topics") = some (.val (.word topics)) := by
                    simp [s1, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                      (by decide : ofString "t" ≠ ofString "topics"), htop_lu]
                  have hargs_u : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
                      [.var .local (ofString "t"), .op .add [.var .local (ofString "topics"), .panop .mul [.var .local (ofString "i"), .const 32#64]]] =
                      some [tv, .val (.word out_i)] := by
                    unfold evalListHOLFinite
                    rw [evalListHOLExact, evalListHOLExact]
                    have ht_e : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a)) (.var .local (ofString "t")) = some tv := by
                      simp [evalHOLExact, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                    have ho_e : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
                        (.op .add [.var .local (ofString "topics"), .panop .mul [.var .local (ofString "i"), .const 32#64]]) = some (.val (.word out_i)) := by
                      rw [evalHOLExact, evalListHOLExact, evalListHOLExact, evalListHOLExact]
                      have ht_top : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a)) (.var .local (ofString "topics")) = some (.val (.word topics)) := by
                        simp [evalHOLExact, hs1_top]
                      rw [ht_top, hmul_ev]; simp [valueIsWord, valueWord, wordOpHOL, wordOp, out_i]
                    rw [ht_e, ho_e]; rfl
                  have hs1_code : s1.code = originalRuntimeCode :=
                    (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite (decClockHOLFinite s) HolFiniteMapExact.empty)
                      (sourceFnBody Guest.Software.guestFn_stack_pop)).1.trans hcode |> fun h => by
                        rw [hsp_r] at h; exact h
                  have htv_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact tv) = true := by
                    simp only [Bool.and_eq_true] at hsh_tv
                    exact (shapeEqHOL_eq_true _ _).mpr ((shapeEqHOL_eq_true _ _).mp hsh_tv.1).symm
                  have hlk_u : lookupCodeHOLFinite s1.code.lookup (ofString "u256_to_be32") [tv, .val (.word out_i)] =
                      some (sourceFnBody Guest.Software.guestFn_u256_to_be32,
                        (HolFiniteMapExact.empty.update (ofString "a", tv)).update (ofString "out", .val (.word out_i)), .one) := by
                    have raw : lookupCodeHOLExact s1.code.lookup (ofString "u256_to_be32") [tv, .val (.word out_i)] =
                        some (sourceFnBody Guest.Software.guestFn_u256_to_be32,
                          (fun k => if k = ofString "out" then some (.val (.word out_i)) else if k = ofString "a" then some tv else none), .one) := by
                      simp [lookupCodeHOLExact, hs1_code, lookup_u256_to_be32_b, htv_sh, shapeOfHOLExact, shapeEqHOL, FUPDATE,
                        (by decide : ofString "a" ≠ ofString "out")]
                    unfold PanSemStateFiniteExact.lookupCodeHOLFinite; split
                    · rename_i m; rw [raw] at m; cases m
                    · rename_i fb fl fs fd
                      obtain ⟨rfl, r2⟩ := Prod.mk.inj (Option.some.inj (fd.symm.trans raw))
                      obtain ⟨rfl, rfl⟩ := Prod.mk.inj r2
                      apply congrArg (fun lc => some (sourceFnBody Guest.Software.guestFn_u256_to_be32, lc, ShapeHOL.one))
                      apply HolFiniteMapExact.ext; funext key
                      by_cases ho_k : key = ofString "out"
                      · subst key; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty]
                      · by_cases ha_k : key = ofString "a"
                        · subst key; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, ho_k, Ne.symm ho_k]
                        · simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, ho_k, Ne.symm ho_k, ha_k, Ne.symm ha_k]
                  rw [evaluateHOLFiniteState_call, hargs_u] at hu_c'; dsimp only at hu_c'
                  rw [hlk_u] at hu_c'; dsimp only at hu_c'
                  change evaluateHOLFiniteState s1 _ = _ at hu_c
                  rw [hu_c] at hbody'
                  split at hu_c'
                  · injection hu_c' with hru _; subst hru; cases hbody'
                  · let cal_u := (HolFiniteMapExact.empty.update (ofString "a", tv)).update (ofString "out", .val (.word out_i))
                    let ent_u := callEntryStateHOLFinite s1 cal_u
                    have hu_eff := u256_to_be32_aligned_body_g09 ent_u out_i hs1_code
                      (hssp_ma.trans hInvW.1.1.memaddrs)
                      (by simp [ent_u, cal_u, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
                      (by omega) (by have := R11Shards.heapLimit_val; have := R11Shards.heapEnd_val; omega)
                    rcases hu_b : evaluateHOLFiniteState ent_u (sourceFnBody Guest.Software.guestFn_u256_to_be32) with ⟨rub, sub⟩
                    change evaluateHOLFiniteState ent_u _ = _ at hu_b
                    rw [hu_b] at hu_c' hu_eff; dsimp only at hu_eff
                    cases rub with
                    | none => dsimp only at hu_c'; injection hu_c' with hru _; subst hru; cases hbody'
                    | some rub0 =>
                      cases rub0 with
                      | timeOut | error | «break» | «continue» | finalFfi _ | exception _ _ =>
                        dsimp only at hu_c'; injection hu_c' with hru _; subst hru; cases hbody'
                      | returned _ =>
                        dsimp only at hu_c'; split at hu_c'
                        · injection hu_c' with hru hsu; subst hru hsu; dsimp only at hbody'
                          rw [evaluateHOLFiniteState_assign] at hbody'
                          split at hbody'
                          · cases hbody'
                          · split at hbody'
                            · injection hbody' with _ hsb_eq
                              have hsub_gl : sub.globals = s.globals := hu_eff.1.globals.trans hssp_gl
                              have hsb_gl : sb.globals = s.globals := by rw [← hsb_eq]; exact hsub_gl
                              have hsb_mem : sb.memory = sub.memory := by rw [← hsb_eq]; rfl
                              refine ⟨fun g => congrFun (globN_congr hsb_gl) g, fun ec hec => ?_, ?_⟩
                              · have hFW := hInvW.2.1.2.2.2.2.1 ec hec
                                obtain ⟨hb_e, _, _, _⟩ := frameWF_bounds hInvW.1.2 hFW
                                obtain ⟨he_lo, _⟩ := (hFW.1 (ec.1, 280) (by simp)).1
                                have h112_lt : ec.1 + 112 < 2 ^ 64 := by omega
                                have hne_sp : BitVec.ofNat 64 (ec.1 + 112) ≠ BitVec.ofNat 64 (globN s "ev" + 16) := by
                                  intro heq
                                  have hn := congrArg BitVec.toNat heq
                                  have hhead_in : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by simp [evmChain, evmChainFrom]
                                  have hb_ev0 := (frameWF_bounds hInvW.1.2 (hInvW.2.1.2.2.2.2.1 _ hhead_in)).1
                                  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                                      Nat.mod_eq_of_lt h112_lt, Nat.mod_eq_of_lt (by dsimp only at hb_ev0; omega)] at hn
                                  obtain ⟨tl, hch_tl⟩ : ∃ tl, evmChain s = (globN s "ev", globN s "cur_cont") :: tl := ⟨_, rfl⟩
                                  rw [hch_tl, List.mem_cons] at hec
                                  rcases hec with rfl | htl
                                  · omega
                                  · have hpw := hInvW.2.1.2.2.2.2.2.2.2.1
                                    rw [hch_tl, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
                                    have hd := hpw.2.2 (globN s "ev", 280) (by simp [frameObjects]) (ec.1, 280)
                                      (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ec, htl, rfl⟩, by simp [frameObjects]⟩)
                                    rcases hd with h | h | h | h <;> dsimp only at h <;> omega
                                have hno_hit : ∀ x ∈ ([(out_i.toNat, 32)] : List Ivl), ¬ CellHits (BitVec.ofNat 64 (ec.1 + 112)).toNat x := by
                                  intro x hx; simp only [List.mem_singleton] at hx; subst hx
                                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h112_lt]
                                  have hsc1 := hInvW.1.2.2.2.1; have hsc2 := hInvW.1.2.2.2.2.1
                                  have hlim_le : heapLimit ≤ scratchStart := by rw [R11Shards.heapLimit_val, R11Shards.scratchStart_val]
                                  unfold CellHits; dsimp only at he_lo ⊢; omega
                                unfold memW; rw [hsb_mem, hu_eff.1.cell_frame _ hno_hit]
                                change (match ssp.memory (BitVec.ofNat 64 (ec.1 + 112)) with | .word w => w.toNat) = _
                                rw [hssp_mem _ hne_sp]
                              · have hhead_in : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by simp [evmChain, evmChainFrom]
                                have hFW0 := hInvW.2.1.2.2.2.2.1 _ hhead_in
                                obtain ⟨hb_ev0, _, _, _⟩ := frameWF_bounds hInvW.1.2 hFW0
                                obtain ⟨hev_lo, _⟩ := (hFW0.1 (globN s "ev", 280) (by simp)).1
                                have h32_lt : globN s "ev" + 32 < 2 ^ 64 := by dsimp only at hb_ev0; omega
                                have hne_sp32 : BitVec.ofNat 64 (globN s "ev" + 32) ≠ BitVec.ofNat 64 (globN s "ev" + 16) := by
                                  intro heq; have hn := congrArg BitVec.toNat heq
                                  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h32_lt,
                                      Nat.mod_eq_of_lt (by dsimp only at hb_ev0; omega)] at hn; omega
                                have hno_hit32 : ∀ x ∈ ([(out_i.toNat, 32)] : List Ivl), ¬ CellHits (BitVec.ofNat 64 (globN s "ev" + 32)).toNat x := by
                                  intro x hx; simp only [List.mem_singleton] at hx; subst hx
                                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h32_lt]
                                  have hsc1 := hInvW.1.2.2.2.1; have hsc2 := hInvW.1.2.2.2.2.1
                                  have hlim_le : heapLimit ≤ scratchStart := by rw [R11Shards.heapLimit_val, R11Shards.scratchStart_val]
                                  unfold CellHits; dsimp only at hev_lo ⊢; omega
                                unfold memW; rw [hsb_mem, hu_eff.1.cell_frame _ hno_hit32]
                                change (match ssp.memory (BitVec.ofNat 64 (globN s "ev" + 32)) with | .word w => w.toNat) = _
                                rw [hssp_mem _ hne_sp32]
                            · cases hbody'
                        · injection hu_c' with hru _; subst hru; cases hbody'
                · cases hbody'
        have hsb_WF : W → HeadMemChainWF sb := fun hw_s => hbody_wf hw_s (Or.inl rfl)
        have hdj_sb : IvlsDisj [(topics.toNat, qw.toNat - topics.toNat)]
            (worldTypedIvls sb S Nd ++ ((evmChain sb).map (frameObjects sb)).flatten) := by
          rwa [hsb_wti, hsb_fo]
        have hiv1_nat : (iv + 1).toNat = iv.toNat + 1 := by
          rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
        change evaluateHOLFiniteState sb opLogWhileProg = (rw0, sw0) at hw'
        have hnt_sb : (evaluateHOLFiniteState sb (.seq opLogWhileProg cont)).1 ≠ some .timeOut := by
          rw [evaluateHOLFiniteState_seq_line780, hw']; dsimp only at hnt_seq ⊢; rw [hw] at hnt_seq; exact hnt_seq
        have hih := ih sb (iv + 1) (by omega) hnt4 hsb_code hsb_InvW hsb_WF
          (by rw [hsb_ch]; exact hlen)
          (by change evmR sb < evmR s0; rw [hsb_R]; exact hR)
          htop_le hq_lim htop_mod8 htop_lo hdj_sb hsb_i
          (by rw [hsb_loc _ (by decide) (by decide)]; exact hnt_lu)
          (by rw [hsb_loc _ (by decide) (by decide)]; exact htop_lu)
          (fun s_end hc_e hInv_e hWF_e hwti_e hfo_e hch_e hR_e hgl_e hmsg_e hm32_e hHM_e hloc_e hnt_e =>
            hcont s_end hc_e hInv_e hWF_e (hwti_e.trans hsb_wti) (hfo_e.trans hsb_fo) (hch_e.trans hsb_ch) hR_e
              (fun g => (hgl_e g).trans (hsb_glob_msg.1 g))
              (fun ec hec => (hmsg_e ec (by rwa [hsb_ch])).trans (hsb_glob_msg.2.1 ec hec))
              (by rw [← hsb_glob_msg.1 "ev", hm32_e, hsb_glob_msg.1 "ev", hsb_glob_msg.2.2])
              (fun hHM_s => hHM_e (hsb_HM hHM_s))
              (fun nm h1 h2 => (hloc_e nm h1 h2).trans (hsb_loc nm h1 h2)) hnt_e)
          hnt_sb
        rw [evaluateHOLFiniteState_seq_line780, hw'] at hih; dsimp only at hih ⊢; exact hih
      | some rb0 =>
        cases rb0 with
        | timeOut =>
          injection hw' with hrw hsw; subst hrw hsw; rw [hw] at hnt_seq; exact absurd rfl hnt_seq
        | error =>
          injection hw' with hrw hsw; subst hrw hsw; exact opDispatchPostBoth_error W s0 sb
        | «break» => exact absurd rfl hbody_step.2.2.1
        | «continue» => exact absurd rfl hbody_step.2.2.2.1
        | returned rv => exact absurd rfl (hbody_step.2.2.2.2 rv)
        | finalFfi _ =>
          injection hw' with hrw hsw; subst hrw hsw
          exact opDispatchPostBoth_other (fun _ h => by cases h) (by rintro ⟨_, h⟩; cases h)
        | exception eid ev =>
          injection hw' with hrw hsw; subst hrw hsw; dsimp only
          by_cases heid : eid = ofString "EvmErr"
          · subst heid
            obtain ⟨hsb_InvW, hsb_ch, hsb_R⟩ := hbody_step.2.1 ev rfl
            have hsb_Inv : EvmInv sb := evmInvWith_to_evmInv hsb_InvW
            have hch_len : (evmChain sb).length = (evmChain s0).length := by rw [hsb_ch]; exact hlen
            have hsb_R' : R11Shards.OpDispatchSpec.evmR sb = R11Shards.OpDispatchSpec.evmR s := hsb_R
            have hR_le : R11Shards.OpDispatchSpec.evmR sb ≤ R11Shards.OpDispatchSpec.evmR s0 := by
              rw [hsb_R']; exact Nat.le_of_lt hR
            refine And.intro (And.intro (fun ⟨_, h⟩ => by cases h) (fun _ => ⟨hsb_Inv, hch_len, hR_le⟩)) (fun hw_s => ?_)
            exact And.intro (fun ⟨_, h⟩ => by cases h) (fun _ => ⟨⟨hsb_Inv, hbody_wf hw_s (Or.inr ⟨ev, rfl⟩)⟩, hch_len, hR_le⟩)
          · refine opDispatchPostBoth_other (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact absurd h1 heid

def opLogPostChargeProg : ProgHOL 64 :=
  InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
    (Prog.decCall "topics" Shape.one "alloc"
      [Exp.op BinOp.add [Exp.panOp PanOp.mul [Exp.var VarKind.local "ntopics", Exp.const 0x20#64], Exp.const 0x8#64]]
      (Prog.dec "i" Shape.one (Exp.const 0x0#64)
        (Prog.seq
          (Prog.while (Exp.cmp Cmp.less (Exp.var VarKind.local "i") (Exp.var VarKind.local "ntopics"))
            (Prog.decCall "t" (Shape.comb [Shape.one, Shape.one, Shape.one, Shape.one]) "stack_pop" []
              (Prog.seq
                (Prog.call (some (none, none)) "u256_to_be32"
                  [Exp.var VarKind.local "t",
                   Exp.op BinOp.add [Exp.var VarKind.local "topics", Exp.panOp PanOp.mul [Exp.var VarKind.local "i", Exp.const 0x20#64]]])
                (Prog.assign VarKind.local "i" (Exp.op BinOp.add [Exp.var VarKind.local "i", Exp.const 0x1#64])))))
          (Prog.seq
            (Prog.call (some (none, none)) "extend_memory" [Exp.rField 1 (Exp.var VarKind.local "x")])
            (Prog.seq
              (Prog.call (some (none, none)) "require_not_static" [])
              (Prog.decCall "log" Shape.one "alloc" [Exp.const 0x28#64]
                (Prog.decCall "log_address" Shape.one "alloc" [Exp.const 0x18#64]
                  (Prog.seq
                    (Prog.call (some (none, none)) "memcpy"
                      [Exp.var VarKind.local "log_address",
                       Exp.load Shape.one (Exp.op BinOp.add [Exp.load Shape.one (Exp.op BinOp.add [Exp.var VarKind.global "ev", Exp.const 0x70#64]), Exp.const 0x20#64]),
                       Exp.const 0x14#64])
                    (Prog.seq
                      (Prog.store (Exp.op BinOp.add [Exp.var VarKind.local "log", Exp.const 0x0#64]) (Exp.var VarKind.local "log_address"))
                      (Prog.seq
                        (Prog.store (Exp.op BinOp.add [Exp.var VarKind.local "log", Exp.const 0x8#64]) (Exp.var VarKind.local "topics"))
                        (Prog.seq
                          (Prog.store (Exp.op BinOp.add [Exp.var VarKind.local "log", Exp.const 0x10#64]) (Exp.var VarKind.local "ntopics"))
                          (Prog.decCall "data" Shape.one "alloc" [Exp.op BinOp.add [Exp.var VarKind.local "n", Exp.const 0x8#64]]
                            (Prog.decCall "s" Shape.one "sat_word" [Exp.var VarKind.local "start"]
                              (Prog.seq
                                (Prog.call (some (none, none)) "memcpy"
                                  [Exp.var VarKind.local "data",
                                   Exp.op BinOp.add [Exp.load Shape.one (Exp.op BinOp.add [Exp.var VarKind.global "ev", Exp.const 0x18#64]), Exp.var VarKind.local "s"],
                                   Exp.var VarKind.local "n"])
                                (Prog.seq
                                  (Prog.store (Exp.op BinOp.add [Exp.var VarKind.local "log", Exp.const 0x18#64]) (Exp.var VarKind.local "data"))
                                  (Prog.seq
                                    (Prog.store (Exp.op BinOp.add [Exp.var VarKind.local "log", Exp.const 0x20#64]) (Exp.var VarKind.local "n"))
                                    (Prog.seq
                                      (Prog.call (some (none, none)) "log_append" [Exp.var VarKind.global "ev", Exp.var VarKind.local "log"])
                                      (Prog.seq
                                        (Prog.call (some (none, none)) "pc_add" [Exp.const 0x1#64])
                                        (Prog.return (Exp.const 0x0#64))))))))))))))))))))

theorem worldOwned_subset_of_wti_eq_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hwti : worldTypedIvls post S Nd = worldTypedIvls s S Nd)
    (hg : ∀ g : String, ofString g ≠ ofString "heap_ptr" → ofString g ≠ ofString "frame_mem_ptr" →
      globN post g = globN s g) :
    ∀ i ∈ worldOwned post S Nd, i ∈ worldOwned s S Nd := by
  have hwti_sub : ∀ j ∈ worldTypedIvls s S Nd, j ∈ worldOwned s S Nd := by
    intro j hj
    unfold worldTypedIvls at hj; unfold worldOwned fixedObjects
    simp only [List.mem_append] at hj ⊢
    rcases hj with ((((h1 | h2) | h3) | h4) | h5) | h6
    · exact Or.inl (Or.inl h1)
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
      have hfix := typedRec_in_fixedObjects s hr
      unfold fixedObjects at hfix; simp only [List.mem_append] at hfix
      exact Or.inl (Or.inr hfix)
    · exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr h3))))
    · exact Or.inl (Or.inr (Or.inl (Or.inr h4)))
    · exact Or.inl (Or.inr (Or.inr h5))
    · exact Or.inr h6
  intro i hi
  unfold worldOwned fixedObjects at hi
  simp only [List.mem_append] at hi
  rcases hi with (hfp | (((hgb | hj) | hbo) | hbal)) | hnd
  · exact hwti_sub i (hwti ▸ by unfold worldTypedIvls; simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hfp)))))
  · obtain ⟨gn, hgn, rfl⟩ := List.mem_map.1 hgb
    have hne1 : ofString gn.1 ≠ ofString "heap_ptr" := by clear * - hgn; revert gn hgn; decide
    have hne2 : ofString gn.1 ≠ ofString "frame_mem_ptr" := by clear * - hgn; revert gn hgn; decide
    rw [hg gn.1 hne1 hne2]
    unfold worldOwned fixedObjects; simp only [List.mem_append]
    exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (List.mem_map.2 ⟨gn, hgn, rfl⟩)))))
  · exact hwti_sub i (hwti ▸ by unfold worldTypedIvls; simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inr hj))))
  · exact hwti_sub i (hwti ▸ by unfold worldTypedIvls; simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inr hbo)))
  · exact hwti_sub i (hwti ▸ by unfold worldTypedIvls; simp only [List.mem_append]; exact Or.inl (Or.inr hbal))
  · exact hwti_sub i (hwti ▸ by unfold worldTypedIvls; simp only [List.mem_append]; exact Or.inr hnd)

private theorem lookup_sat_word_g09 :
    originalRuntimeCode.lookup (ofString "sat_word") =
      some ([(ofString "v", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_sat_word, .one) :=
  lookup_of_guestAst_getElem 440 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_sat_word) rfl

theorem op_log_post_charge_both_g09 {F : Type}
    {W : Prop} {s0 s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {nt nw cw ebw sa sb sc sd : BitVec 64}
    (hc0 : s.code = originalRuntimeCode) (hInvW0 : EvmInvWith s S Nd)
    (hHM0 : HeadMemAligned s) (hWF0 : W → HeadMemChainWF s)
    (hlen0 : (evmChain s).length = (evmChain s0).length) (hR0 : evmR s < evmR s0)
    (hnt4 : nt.toNat ≤ 4) (hn_lt : nw.toNat < 2 ^ 61)
    (hnt_lk : s.locals.lookup (ofString "ntopics") = some (.val (.word nt)))
    (hn_lk : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hstart_lk : s.locals.lookup (ofString "start") =
      some (.rStruct [.val (.word sa), .val (.word sb), .val (.word sc), .val (.word sd)]))
    (hx_lk : s.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]))
    (heb_cond : ebw = 0#64 ∨ (ebw.toNat % 32 = 0 ∧ memW s (globN s "ev" + 32) + ebw.toNat < 2 ^ 37))
    (hnt_prog : (evaluateHOLFiniteState s opLogPostChargeProg).1 ≠ some .timeOut) :
    OpDispatchPostBoth W s0
      (evaluateHOLFiniteState s opLogPostChargeProg).1
      (evaluateHOLFiniteState s opLogPostChargeProg).2 := by
  unfold opLogPostChargeProg at hnt_prog ⊢
  dsimp only [InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    List.map, Option.map] at hnt_prog ⊢
  change (evaluateHOLFiniteState s (.decCall (ofString "topics") .one (ofString "alloc")
    [.op .add [.panop .mul [.var .local (ofString "ntopics"), .const 32#64], .const 8#64]]
    (.dec (ofString "i") .one (.const 0#64) (.seq opLogWhileProg _)))).1 ≠ some .timeOut at hnt_prog
  change OpDispatchPostBoth W s0
    (evaluateHOLFiniteState s (.decCall (ofString "topics") .one (ofString "alloc")
      [.op .add [.panop .mul [.var .local (ofString "ntopics"), .const 32#64], .const 8#64]]
      (.dec (ofString "i") .one (.const 0#64) (.seq opLogWhileProg _)))).1
    (evaluateHOLFiniteState s (.decCall (ofString "topics") .one (ofString "alloc")
      [.op .add [.panop .mul [.var .local (ofString "ntopics"), .const 32#64], .const 8#64]]
      (.dec (ofString "i") .one (.const 0#64) (.seq opLogWhileProg _)))).2
  have hsz_top : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.panop .mul [.var .local (ofString "ntopics"), .const 32#64], .const 8#64]) =
      some (.val (.word (nt * 32#64 + 8#64))) := by
    simp [evalHOLExact, evalListHOLExact, hnt_lk, valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp]
  have htop_nat : (nt * 32#64 + 8#64).toNat = 32 * nt.toNat + 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_mul]
    change ((nt.toNat * 32) % 2 ^ 64 + 8) % 2 ^ 64 = _
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  apply decCall_alloc_both_g09 hc0 hInvW0 hWF0 hsz_top hnt_prog
  intro topics qw1 s1 hc1 hInvW1 hWF1 hwti1 hfo1 hch1 hR1 hHM1_imp hg1 hm1 _ hl1 hp0_eq hq1_eq hfit1 hlim1 htop8 _ htop_lo _ hdj1 hnt1
  rw [evaluateHOLFiniteState_dec_total] at hnt1 ⊢
  simp only [evalHOLFinite, evalHOLExact, shapeOfHOLExact, shapeEqHOL, Bool.true_and, Bool.and_true, ↓reduceIte] at hnt1 ⊢
  let si := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s1
  have hInvW_si : EvmInvWith si S Nd := evmInvWith_localsFree (s := s1) si.locals s1.clock hInvW1
  have hWF_si : W → HeadMemChainWF si := fun hw => headMemChainWF_locals s1 si.locals s1.clock (hWF1 hw)
  have hdj_si : IvlsDisj [(topics.toNat, qw1.toNat - topics.toNat)]
      (worldTypedIvls si S Nd ++ ((evmChain si).map (frameObjects si)).flatten) := by
    rw [worldTypedIvls_congr_mg_g09 (s := s1) (t := si) rfl rfl,
      map_frameObjects_congr_mg_g09 (s := s1) (t := si) rfl rfl]; exact hdj1
  have hfit1' : topics.toNat + (32 * nt.toNat + 8) ≤ qw1.toNat := by rwa [htop_nat] at hfit1
  have hnt_si : si.locals.lookup (ofString "ntopics") = some (.val (.word nt)) := by
    simpa [si, setVarHOLFinite, hl1, HolFiniteMapExact.lookup_update, FUPDATE,
      (by decide : ofString "i" ≠ ofString "ntopics"), (by decide : ofString "topics" ≠ ofString "ntopics")] using hnt_lk
  have htop_si : si.locals.lookup (ofString "topics") = some (.val (.word topics)) := by
    simp [si, setVarHOLFinite, hl1, HolFiniteMapExact.lookup_update, FUPDATE,
      (by decide : ofString "i" ≠ ofString "topics")]
  refine opDispatchPostBoth_congr_lc (post := (evaluateHOLFiniteState si (.seq opLogWhileProg _)).2) rfl ?_
  apply op_log_while_both_full_g09 nt.toNat si 0#64 (by simp) hnt4 hc1 hInvW_si hWF_si
    (by have hch : evmChain si = evmChain s :=
          (evmChain_congr (s := s1) (t := si) rfl rfl).trans hch1
        rw [hch]; exact hlen0)
    (by have hR_chain : evmR si = evmR s :=
          ((evm_congr (s := s1) (t := si) rfl rfl).2.1).trans hR1
        rw [hR_chain]; exact hR0)
    hfit1' hlim1 htop8 htop_lo hdj_si
    (by simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) hnt_si htop_si ?_ hnt1
  intro s2 hc2 hInvW2 hWF2 hwti2 hfo2 hch2 hR2 hglob2 hmsg2 hm32_2 hHM2_imp hlk2 hnt2
  have hHM2 : HeadMemAligned s2 := hHM2_imp (hHM1_imp hHM0)
  have hq2_eq : globN s2 "heap_ptr" = qw1.toNat := (hglob2 "heap_ptr").trans hq1_eq
  have hdj2 : IvlsDisj [(topics.toNat, qw1.toNat - topics.toNat)]
      (worldTypedIvls s2 S Nd ++ ((evmChain s2).map (frameObjects s2)).flatten) := by
    rwa [hwti2, hfo2]
  have hx2 : s2.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) := by
    rw [hlk2 _ (by decide) (by decide)]; simpa [si, setVarHOLFinite, hl1, HolFiniteMapExact.lookup_update, FUPDATE,
      (by decide : ofString "i" ≠ ofString "x"), (by decide : ofString "topics" ≠ ofString "x")] using hx_lk
  have hm32_s2 : memW s2 (globN s2 "ev" + 32) = memW s (globN s "ev" + 32) := by
    have hev_si : globN si "ev" = globN s "ev" := by
      change globN s1 "ev" = globN s "ev"; simp [globN, hg1, HolFiniteMapExact.lookup_update, FUPDATE, (by decide : ofString "heap_ptr" ≠ ofString "ev")]
    rw [hglob2 "ev", hm32_2, hev_si]; simp [si, setVarHOLFinite, memW, hm1]
  have heb_s2 : ebw = 0#64 ∨
      (memW s2 (globN s2 "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
       (memW s2 (globN s2 "ev" + 32) + ebw.toNat) % 32 = 0 ∧
       memW s2 (globN s2 "ev" + 24) + memW s2 (globN s2 "ev" + 40) = globN s2 "frame_mem_ptr") := by
    rcases heb_cond with rfl | ⟨heb32, h37⟩
    · exact Or.inl rfl
    · right
      have hlen32 := hHM2.1
      rw [hm32_s2] at hlen32 ⊢
      exact ⟨h37, by omega, hHM2.2⟩
  -- Step 12: call `extend_memory(x.1)`
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt2 ⊢
  have hargs_em : evalListHOLFinite s2 (h := fun a => Classical.propDecidable (s2.memaddrs a))
      [.rfield 1 (.var .local (ofString "x"))] = some [.val (.word ebw)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, evalHOLExact, hx2]
  have hlk_em := pan_one_word_lookup s2.code.lookup (ofString "extend_memory") (ofString "expand_by")
    (sourceFnBody Guest.Software.guestFn_extend_memory) ebw
    (by rw [hc2]; exact lookup_extend_memory)
  rw [hargs_em] at hnt2 ⊢; dsimp only at hnt2 ⊢; rw [hlk_em] at hnt2 ⊢; dsimp only at hnt2 ⊢
  by_cases hclk2 : s2.clock = 0
  · simp [hclk2] at hnt2
  · simp only [hclk2, ↓reduceIte] at hnt2 ⊢
    let cal_em := HolFiniteMapExact.empty.update (ofString "expand_by", ValueHOL.val (.word ebw))
    let ent_em := callEntryStateHOLFinite s2 cal_em
    have hnt_em : (evaluateHOLFiniteState ent_em (sourceFnBody Guest.Software.guestFn_extend_memory)).1 ≠ some .timeOut := by
      rintro hto
      change (evaluateHOLFiniteState (callEntryStateHOLFinite s2 cal_em)
        (sourceFnBody Guest.Software.guestFn_extend_memory)).1 = some .timeOut at hto
      rcases hb_eq : evaluateHOLFiniteState (callEntryStateHOLFinite s2 cal_em)
        (sourceFnBody Guest.Software.guestFn_extend_memory) with ⟨r0, stm0⟩
      rw [hb_eq] at hto hnt2; dsimp only at hto; subst hto; exact hnt2 rfl
    have hem_eff := extend_memory_body_frameMemEff_g09 ent_em hc2
      (localsFree_evmInv s2 cal_em (s2.clock - 1) (evmInvWith_to_evmInv hInvW2))
      (by simp [ent_em, cal_em, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) heb_s2 hnt_em
    have hmeta_em := (PanRunBounded.evaluateHOLFiniteState_metadata ent_em (sourceFnBody Guest.Software.guestFn_extend_memory)).1
    rcases hrun_em : evaluateHOLFiniteState ent_em (sourceFnBody Guest.Software.guestFn_extend_memory) with ⟨rem, sem⟩
    simp only [ent_em, cal_em, hrun_em] at hnt2 hem_eff hmeta_em ⊢
    cases rem with
    | none => exact opDispatchPostBoth_error W s0 sem
    | some rem0 =>
      cases rem0 with
      | timeOut => rw [hrun_em] at hnt_em; exact absurd rfl hnt_em
      | error => exact opDispatchPostBoth_error W s0 sem.emptyLocalsHOLFinite
      | «break» | «continue» => exact opDispatchPostBoth_error W s0 sem
      | finalFfi _ => exact opDispatchPostBoth_other (fun _ h => by cases h) (by rintro ⟨_, h⟩; cases h)
      | exception eid ev =>
        by_cases heid : eid = ofString "EvmErr"
        · subst heid; exact absurd ⟨ev, rfl⟩ hem_eff.2
        · refine opDispatchPostBoth_other (fun _ h => by cases h) ?_
          rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact absurd h1 heid
      | returned vem =>
        obtain ⟨rfl, freshIvl, hA_sem, hfm_le, heff_em, hfresh_em, he0_other, hnew_mem, hlen_le_cap, hlen_new⟩ := hem_eff.1 vem rfl
        have hsh0 : shapeEqHOL (shapeOfHOLExact (ValueHOL.val (.word 0#64))) .one = true := by simp [shapeOfHOLExact, shapeEqHOL]
        simp only [hsh0, ↓reduceIte] at hnt2 ⊢
        have hInvW_ent : EvmInvWith ent_em S Nd := evmInvWith_localsFree s2.locals (s2.clock - 1) hInvW2 |> fun _ =>
          evmInvWith_localsFree (s := s2) cal_em (s2.clock - 1) hInvW2
        have hnew_mem_std :
            (freshIvl.2 = 0 ∧ memW sem (globN ent_em "ev" + 40) = memW ent_em (globN ent_em "ev" + 40)) ∨
            (freshIvl.2 ≠ 0 ∧ memW ent_em (globN ent_em "ev" + 24) + memW ent_em (globN ent_em "ev" + 40) = freshIvl.1 ∧
              memW sem (globN ent_em "ev" + 40) = memW ent_em (globN ent_em "ev" + 40) + freshIvl.2) := by
          rcases hnew_mem with ⟨h1, h2, _⟩ | ⟨h1, h2, h3, _⟩
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr ⟨h1, h2, h3⟩
        obtain ⟨hInvW_sem, hwti_sem, hch_sem, hR_sem, hobj_sem⟩ :=
          evmInvWith_of_head_mem_extend_g09 hInvW_ent hA_sem hfm_le heff_em hfresh_em he0_other hnew_mem_std hlen_le_cap
        have hlen_al32 : memW sem (globN ent_em "ev" + 32) % 32 = 0 := by
          have hlen_ent : memW ent_em (globN ent_em "ev" + 32) = memW s2 (globN s2 "ev" + 32) := rfl
          rw [hlen_new, hlen_ent]
          rcases heb_s2 with rfl | ⟨_, hmod, _⟩
          · simpa using hHM2.1
          · exact hmod
        have hWF_sem : W → HeadMemChainWF sem := fun hw0 =>
          headMemChainWF_of_head_mem_extend (localsFree_evmInv s2 cal_em (s2.clock - 1) (evmInvWith_to_evmInv hInvW2))
            (headMemChainWF_locals s2 cal_em (s2.clock - 1) (hWF2 hw0))
            hA_sem heff_em hfresh_em he0_other hnew_mem hch_sem hlen_al32
        have hHM_sem : HeadMemAligned sem := by
          have hev_sem : globN sem "ev" = globN ent_em "ev" :=
            R16Shards.OpHandlers.globN_eq_of_lookup_eq (heff_em.glob_other "ev" (by decide))
          refine ⟨by rw [hev_sem]; exact hlen_al32, ?_⟩
          rw [hev_sem, he0_other 24 (by omega) (by omega) (by omega) (by omega)]
          rcases hnew_mem with ⟨_, hcap0, hfmp0⟩ | ⟨_, hcontig, hcap1, hfmp1⟩
          · rw [hcap0, hfmp0]; exact hHM2.2
          · rw [hcap1, hfmp1]; omega
        let s3 : PanSemStateFiniteExact 64 F := { sem with locals := s2.locals }
        have hs3_code : s3.code = originalRuntimeCode := hmeta_em.trans hc2
        have hInvW3 : EvmInvWith s3 S Nd := evmInvWith_localsFree (s := sem) s2.locals sem.clock hInvW_sem
        have hWF3 : W → HeadMemChainWF s3 := fun hw0 => headMemChainWF_locals sem s2.locals sem.clock (hWF_sem hw0)
        have hHM3 : HeadMemAligned s3 := headMemAligned_congr_head rfl (fun _ _ => rfl) hHM_sem
        have hdj_top3 : IvlsDisj [(topics.toNat, qw1.toNat - topics.toNat)]
            (worldTypedIvls s3 S Nd ++ ((evmChain s3).map (frameObjects s3)).flatten) := by
          rw [worldTypedIvls_congr_mg_g09 (s := sem) (t := s3) rfl rfl,
              map_frameObjects_congr_mg_g09 (s := sem) (t := s3) rfl rfl]
          refine heap_buffer_disj_after_head_mem_extend_g09 hInvW_sem (by dsimp only; omega) hwti_sem hch_sem hobj_sem ?_
          rw [worldTypedIvls_congr_mg_g09 (s := s2) (t := ent_em) rfl rfl,
              map_frameObjects_congr_mg_g09 (s := s2) (t := ent_em) rfl rfl]
          exact hdj2
        have hq3_eq : globN s3 "heap_ptr" = qw1.toNat :=
          (R16Shards.OpHandlers.globN_eq_of_lookup_eq (heff_em.glob_other "heap_ptr" (by decide))).trans hq2_eq
        have hch3 : evmChain s3 = evmChain s := by
          rw [evmChain_congr (s := sem) (t := s3) rfl rfl, hch_sem,
              evmChain_congr (s := s2) (t := ent_em) rfl rfl, hch2,
              evmChain_congr (s := s1) (t := si) rfl rfl, hch1]
        have hR3 : evmR s3 < evmR s0 := by
          have hR3_eq : evmR s3 = evmR s2 :=
            ((evm_congr (s := sem) (t := s3) rfl rfl).2.1.trans hR_sem).trans
              (evm_congr (s := s2) (t := ent_em) rfl rfl).2.1
          rw [hR3_eq]; exact hR2
        have hwti3 : worldTypedIvls s3 S Nd = worldTypedIvls s S Nd := by
          rw [worldTypedIvls_congr_mg_g09 (s := sem) (t := s3) rfl rfl, hwti_sem,
              worldTypedIvls_congr_mg_g09 (s := s2) (t := ent_em) rfl rfl, hwti2,
              worldTypedIvls_congr_mg_g09 (s := s1) (t := si) rfl rfl, hwti1]
        have hg3 : ∀ g : String, ofString g ≠ ofString "heap_ptr" → ofString g ≠ ofString "frame_mem_ptr" →
            globN s3 g = globN s g := by
          intro g hhp hfmp
          have h1 : globN s3 g = globN s2 g :=
            R16Shards.OpHandlers.globN_eq_of_lookup_eq (heff_em.glob_other g hfmp)
          have h2 : globN si g = globN s g := by
            change globN s1 g = globN s g
            simp [globN, hg1, HolFiniteMapExact.lookup_update, FUPDATE, hhp, Ne.symm hhp]
          exact h1.trans ((hglob2 g).trans h2)
        have hmsg3 : ∀ ec ∈ evmChain s, memW s3 (ec.1 + 112) = memW s (ec.1 + 112) := by
          intro ec hec
          have hec2 : ec ∈ evmChain ent_em := by
            rw [evmChain_congr (s := s2) (t := ent_em) rfl rfl, hch2,
                evmChain_congr (s := s1) (t := si) rfl rfl, hch1]; exact hec
          have hmsg_sem : memW sem (ec.1 + 112) = memW ent_em (ec.1 + 112) := by
            obtain ⟨chTail, hch_ent⟩ : ∃ tl, evmChain ent_em = (globN ent_em "ev", globN ent_em "cur_cont") :: tl := ⟨_, rfl⟩
            rw [hch_ent, List.mem_cons] at hec2
            rcases hec2 with rfl | htail
            · exact he0_other 112 (by omega) (by omega) (by omega) (by omega)
            · have hec_in : ec ∈ evmChain ent_em := by rw [hch_ent]; exact List.mem_cons_of_mem _ htail
              have hFW_ec := hInvW_ent.2.1.2.2.2.2.1 ec hec_in
              obtain ⟨hb_ec, _, _, _⟩ := frameWF_bounds hInvW_ent.1.2 hFW_ec
              have hec8 : ec.1 % 8 = 0 := (hFW_ec.1 (ec.1, 280) (by simp)).2.1
              have h112_lt : ec.1 + 112 < 2 ^ 64 := by omega
              unfold memW; rw [heff_em.cell_frame (BitVec.ofNat 64 (ec.1 + 112))]
              intro x hx; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h112_lt]
              have hhead_in : (globN ent_em "ev", globN ent_em "cur_cont") ∈ evmChain ent_em := by
                rw [hch_ent]; exact List.mem_cons_self
              have hFW0_ent := hInvW_ent.2.1.2.2.2.2.1 _ hhead_in
              have hpw_ent := hInvW_ent.2.1.2.2.2.2.2.2.2.1
              rw [hch_ent, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw_ent
              have hmem_ec_fl : (ec.1, 280) ∈ (chTail.map (frameObjects ent_em)).flatten :=
                List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ec, htail, rfl⟩, by simp [frameObjects]⟩
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
              have hx8_dj : x.1 % 8 = 0 ∧ Disj (ec.1, 280) x := by
                simp only [ent_em, cal_em] at hFW_ec hFW0_ent hpw_ent hmem_ec_fl
                rcases hx with rfl | rfl | rfl
                · rcases hfresh_em with rfl | ⟨hf8, _, hfin1, hfin2⟩
                  · exact ⟨rfl, Or.inr (Or.inl rfl)⟩
                  · obtain ⟨hin1, _⟩ := (hFW_ec.1 (ec.1, 280) (by simp)).1
                    have hle_m := hA_sem.2.2.2.2.1
                    have hsp_eq := R16Shards.OpHandlers.globN_eq_of_lookup_eq (heff_em.glob_other "scratch_ptr" (by decide))
                    have hsp_eq' : globN sem "scratch_ptr" = globN ent_em "scratch_ptr" := hsp_eq
                    have hin1a' : globN ent_em "scratch_ptr" ≤ ec.1 := hin1
                    exact ⟨hf8, Or.inr (Or.inr (Or.inr (by dsimp only at ⊢; omega)))⟩
                · exact ⟨(hFW0_ent.1 _ (by simp)).2.1,
                    R11Shards.Disj.symm (hpw_ent.2.2 _ (by simp [frameObjects]) _ hmem_ec_fl)⟩
                · exact ⟨hFW0_ent.2.2.1.1,
                    R11Shards.Disj.symm (hpw_ent.2.2 _ (by simp [frameObjects]) _ hmem_ec_fl)⟩
              exact not_cellHits_of_disj_aligned (i := (ec.1, 280)) (by omega) hx8_dj.1
                (Nat.le_add_right ec.1 112) (by dsimp only; omega) hx8_dj.2
          have hec_si : ec ∈ evmChain si := by rw [evmChain_congr (s := s1) (t := si) rfl rfl, hch1]; exact hec
          have hmsg_si : memW si (ec.1 + 112) = memW s (ec.1 + 112) := by simp [si, setVarHOLFinite, memW, hm1]
          exact hmsg_sem.trans ((hmsg2 ec hec_si).trans hmsg_si)
        have hfo3 : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s3 ec,
            o ∈ ((evmChain s).map (frameObjects s)).flatten ∨
            o = (memW sem (globN ent_em "ev" + 24), memW sem (globN ent_em "ev" + 40)) := by
          intro ec hec o ho
          have hec_ent : ec ∈ evmChain ent_em := by
            rw [evmChain_congr (s := s2) (t := ent_em) rfl rfl, hch2,
                evmChain_congr (s := s1) (t := si) rfl rfl, hch1]; exact hec
          have ho_sem : o ∈ frameObjects sem ec := by
            have hfe : frameObjects s3 ec = frameObjects sem ec := rfl
            rw [hfe] at ho
            exact ho
          rcases hobj_sem ec hec_ent o ho_sem with ho_ent | ⟨_, rfl⟩
          · left
            have hmem_fl : o ∈ ((evmChain ent_em).map (frameObjects ent_em)).flatten :=
              List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ec, hec_ent, rfl⟩, ho_ent⟩
            rw [map_frameObjects_congr_mg_g09 (s := s2) (t := ent_em) rfl rfl, hfo2,
                map_frameObjects_congr_mg_g09 (s := s1) (t := si) rfl rfl, hfo1] at hmem_fl
            exact hmem_fl
          · exact Or.inr rfl
        have hmem_em_ge : scratchStart ≤ memW sem (globN ent_em "ev" + 24) ∨ memW sem (globN ent_em "ev" + 40) = 0 := by
          have hhead_sem : (globN sem "ev", globN sem "cur_cont") ∈ evmChain sem := by simp [evmChain, evmChainFrom]
          have hFW_sem0 := hInvW_sem.2.1.2.2.2.2.1 _ hhead_sem
          have hev_sem : globN sem "ev" = globN ent_em "ev" :=
            R16Shards.OpHandlers.globN_eq_of_lookup_eq (heff_em.glob_other "ev" (by decide))
          rw [← hev_sem]
          exact Or.inl hFW_sem0.2.1.1
        -- Step 13: call `require_not_static()`
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt2 ⊢
        have hargs_rns : evalListHOLFinite s3 (h := fun a => Classical.propDecidable (s3.memaddrs a)) [] = some [] := rfl
        have hlk_rns : PanSemStateFiniteExact.lookupCodeHOLFinite s3.code.lookup (ofString "require_not_static") [] =
            some (sourceFnBody Guest.Software.guestFn_require_not_static, HolFiniteMapExact.empty, .one) := by
          have raw : lookupCodeHOLExact s3.code.lookup (ofString "require_not_static") [] =
              some (sourceFnBody Guest.Software.guestFn_require_not_static, FEMPTY, .one) := by
            simp [lookupCodeHOLExact, hs3_code, lookup_require_not_static]
            rfl
          unfold PanSemStateFiniteExact.lookupCodeHOLFinite; split
          · rename_i m; rw [raw] at m; cases m
          · rename_i fb fl fs fd
            obtain ⟨rfl, r2⟩ := Prod.mk.inj (Option.some.inj (fd.symm.trans raw))
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj r2
            apply congrArg (fun lc => some (sourceFnBody Guest.Software.guestFn_require_not_static, lc, ShapeHOL.one))
            apply HolFiniteMapExact.ext; funext _; rfl
        rw [hargs_rns] at hnt2 ⊢; dsimp only at hnt2 ⊢; rw [hlk_rns] at hnt2 ⊢; dsimp only at hnt2 ⊢
        by_cases hclk3 : s3.clock = 0
        · simp [show sem.clock = 0 from hclk3] at hnt2
        · simp only [show ¬(sem.clock = 0) from hclk3, ↓reduceIte] at hnt2 ⊢
          let ent_rns := callEntryStateHOLFinite s3 HolFiniteMapExact.empty
          obtain ⟨p_rns, b_rns, r_rns, hlk_rns_sp, hsp_rns⟩ := eps_require_not_static
          obtain ⟨p_rnsA, b_rnsA, r_rnsA, hlk_rns_spA, hsp_rnsA⟩ := Group09ChainWF.epsA_require_not_static
          have hb_rns : sourceFnBody Guest.Software.guestFn_require_not_static = b_rns :=
            lookupCodeHOLFinite_installed_body s3.code.lookup _ _ _ _ _ _ [] HolFiniteMapExact.empty
              (by rw [hs3_code]; exact hlk_rns_sp) hlk_rns
          have hb_rnsA : b_rns = b_rnsA := by
            have heq := hlk_rns_sp.symm.trans hlk_rns_spA
            exact (Prod.mk.inj (Prod.mk.inj (Option.some.inj heq)).2).1
          have hlk_rns_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "require_not_static") [] =
              some (b_rns, HolFiniteMapExact.empty, .one) := by rwa [← hb_rns, ← hs3_code]
          have hrns_shape : r_rns = ShapeHOL.one := by
            have heq := hlk_rns_sp.symm.trans lookup_require_not_static
            exact (Prod.mk.inj (Prod.mk.inj (Option.some.inj heq)).2).2
          have hrns_shapeA : r_rns = r_rnsA := by
            exact (Prod.mk.inj (Prod.mk.inj (Option.some.inj (hlk_rns_sp.symm.trans hlk_rns_spA))).2).2
          rcases hrun_rns : evaluateHOLFiniteState ent_rns
              (sourceFnBody Guest.Software.guestFn_require_not_static) with ⟨rrns, srns⟩
          have hrun_rns' : evaluateHOLFiniteState (callEntryStateHOLFinite { locals := s2.locals, globals := sem.globals, structs := sem.structs, code := sem.code, eshapes := sem.eshapes, memory := sem.memory, memaddrs := sem.memaddrs, shMemaddrs := sem.shMemaddrs, clock := sem.clock, be := sem.be, ffi := sem.ffi, baseAddr := sem.baseAddr, topAddr := sem.topAddr } HolFiniteMapExact.empty) (sourceFnBody Guest.Software.guestFn_require_not_static) = (rrns, srns) := hrun_rns
          simp only [hrun_rns'] at hnt2 ⊢
          have hrns_out (hsf : rrns ≠ some .timeOut) :=
            hsp_rns ent_rns hs3_code (localsFree_evmInv s3 HolFiniteMapExact.empty (s3.clock - 1) (evmInvWith_to_evmInv hInvW3))
              trivial ⟨[], by rw [hrns_shape, show ent_rns.locals = HolFiniteMapExact.empty from rfl]; exact hlk_rns_orig⟩ (by rw [← hb_rns, hrun_rns]; exact hsf)
          cases rrns with
          | none => exact opDispatchPostBoth_error W s0 srns
          | some rrns0 =>
            cases rrns0 with
            | timeOut => simp at hnt2
            | error => exact opDispatchPostBoth_error W s0 srns.emptyLocalsHOLFinite
            | «break» | «continue» => exact opDispatchPostBoth_error W s0 srns
            | finalFfi _ => exact opDispatchPostBoth_other (fun _ h => by cases h) (by rintro ⟨_, h⟩; cases h)
            | exception eid ev =>
              by_cases heid : eid = ofString "EvmErr"
              · subst heid
                have herr1 := (hrns_out (by simp)).2
                rw [← hb_rns, hrun_rns] at herr1; dsimp only at herr1
                obtain ⟨hInv_el, hch_el0, hR_el0⟩ := herr1 ⟨ev, rfl⟩
                have hch_el : (evmChain srns.emptyLocalsHOLFinite).length = (evmChain s0).length := by
                  have hB1 : evmChain srns.emptyLocalsHOLFinite = evmChain srns := evmChain_congr rfl rfl
                  have hB2 : evmChain ent_rns = evmChain s3 := StateRestoreEpilogue.evmChain_lc s3 _ _
                  rw [hB1, hch_el0, hB2, hch3]; exact hlen0
                have hR_el1 : evmR srns.emptyLocalsHOLFinite ≤ evmR ent_rns := by
                  rw [show evmR srns.emptyLocalsHOLFinite = evmR srns from StateRestoreEpilogue.evmR_lc srns _ _]
                  exact hR_el0
                have hR_el2 : evmR ent_rns < evmR s0 := by
                  rw [show evmR ent_rns = evmR s3 from StateRestoreEpilogue.evmR_lc s3 _ _]
                  exact hR3
                have hR_el : evmR srns.emptyLocalsHOLFinite ≤ evmR s0 :=
                  Nat.le_trans hR_el1 (Nat.le_of_lt hR_el2)
                have hInv_el_b : EvmInv srns.emptyLocalsHOLFinite :=
                  localsFree_evmInv srns srns.emptyLocalsHOLFinite.locals srns.clock hInv_el
                refine ⟨⟨(by rintro ⟨_, h⟩; cases h), fun _ => ⟨hInv_el_b, hch_el, hR_el⟩⟩, fun hw0 => ?_⟩
                have herrA := (hsp_rnsA ent_rns hs3_code
                  (localsFree_evmInv s3 HolFiniteMapExact.empty (s3.clock - 1) (evmInvWith_to_evmInv hInvW3))
                  (headMemChainWF_locals s3 HolFiniteMapExact.empty (s3.clock - 1) (hWF3 hw0))
                  trivial ⟨[], by rw [← hb_rnsA, ← hrns_shapeA, hrns_shape, show ent_rns.locals = HolFiniteMapExact.empty from rfl]; exact hlk_rns_orig⟩ (by rw [← hb_rnsA, ← hb_rns, hrun_rns]; simp)).2
                rw [← hb_rnsA, ← hb_rns, hrun_rns] at herrA; dsimp only at herrA
                obtain ⟨hInvWF_el, _, _⟩ := herrA ⟨ev, rfl⟩
                have hWF_el_b : HeadMemChainWF srns.emptyLocalsHOLFinite :=
                  headMemChainWF_locals srns srns.emptyLocalsHOLFinite.locals srns.clock hInvWF_el.2
                dsimp only at ⊢
                exact ⟨(by rintro ⟨_, h⟩; cases h),
                  fun _ => ⟨⟨hInv_el_b, hWF_el_b⟩, ⟨hch_el, hR_el⟩⟩⟩
              · refine opDispatchPostBoth_other (fun _ h => by cases h) ?_
                rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact absurd h1 heid
            | returned vrns =>
              have hrns_ret := (hrns_out (by simp)).1 vrns (by rw [← hb_rns, hrun_rns])
              rw [← hb_rns, hrun_rns] at hrns_ret; dsimp only at hrns_ret
              have hlf_rns : LocFrame ent_rns srns := hrns_ret.2.2.2
              let s4 : PanSemStateFiniteExact 64 F := { srns with locals := s3.locals }
              have hs4_eq : s4 = { s3 with clock := srns.clock } := by
                dsimp only [s4]; rw [hlf_rns]; dsimp only; rfl
              by_cases hsh_rns : shapeEqHOL (shapeOfHOLExact vrns) ShapeHOL.one = true
              case neg => simp only [if_neg hsh_rns, ↓reduceIte]; exact opDispatchPostBoth_error W s0 srns
              simp only [hsh_rns, ↓reduceIte] at hnt2 ⊢
              refine opDispatchPostBoth_congr_lc
                (post := (evaluateHOLFiniteState s4 (ProgHOL.decCall (ofString "log") ShapeHOL.one (ofString "alloc")
                  [ExpHOL.const 40#64] _)).2) rfl ?_
              have hlit4 : PanSemStateFiniteExact.mk s2.locals srns.globals srns.structs srns.code srns.eshapes
                  srns.memory srns.memaddrs srns.shMemaddrs srns.clock srns.be srns.ffi srns.baseAddr
                  srns.topAddr = s4 := rfl
              rw [hlit4] at ⊢
              have hs4_code : s4.code = originalRuntimeCode := by rw [hs4_eq]; exact hs3_code
              have hInvW4 : EvmInvWith s4 S Nd := by rw [hs4_eq]; exact evmInvWith_localsFree s3.locals srns.clock hInvW3
              have hWF4 : W → HeadMemChainWF s4 := fun hw0 => by rw [hs4_eq]; exact headMemChainWF_locals s3 s3.locals srns.clock (hWF3 hw0)
              have hHM4 : HeadMemAligned s4 := by rw [hs4_eq]; exact hHM3
              -- Step 14: `decCall "log" .one "alloc" [.const 0x28#64]`
              have hsz40 : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a)) (.const 0x28#64) =
                  some (.val (.word 0x28#64)) := rfl
              apply decCall_alloc_both_g09 hs4_code hInvW4 hWF4 hsz40 hnt2
              intro log qw2 s5 hc5 hInvW5 hWF5 hwti5 hfo5 hch5 hR5 hHM5_imp hg5 hm5 _ hl5 hp4_eq hq5_eq hfit5 hlim5 hlog8 _ hlog_lo hwok_log hdj_log5 hnt5
              have hp4_q1 : log.toNat = qw1.toNat := by
                have : globN s4 "heap_ptr" = qw1.toNat := by rw [hs4_eq]; exact hq3_eq
                omega
              have hfit5' : log.toNat + 40 ≤ qw2.toNat := hfit5
              -- Step 15: `decCall "log_address" .one "alloc" [.const 0x18#64]`
              have hsz24 : @evalHOLExact 64 F _ s5.toExact (fun a => Classical.propDecidable (s5.memaddrs a)) (.const 0x18#64) =
                  some (.val (.word 0x18#64)) := rfl
              apply decCall_alloc_both_g09 hc5 hInvW5 hWF5 hsz24 hnt5
              intro log_addr qw3 s6 hc6 hInvW6 hWF6 hwti6 hfo6 hch6 hR6 hHM6_imp hg6 hm6 _ hl6 hp5_eq hq6_eq hfit6 hlim6 haddr8 _ haddr_lo _ hdj_addr6 hnt6
              have hp5_q2 : log_addr.toNat = qw2.toNat := by omega
              have hfit6' : log_addr.toNat + 24 ≤ qw3.toNat := hfit6
              -- Step 16: `memcpy(log_address, load(load(ev + 0x70) + 0x20), 0x14)`
              obtain ⟨src_addr, hsrc_addr⟩ := eval_ev_msg_addr_g09 s6 hInvW6.1 hInvW6.2.1
              have hd_addr6 : @evalHOLExact 64 F _ s6.toExact (fun a => Classical.propDecidable (s6.memaddrs a))
                  (.var .local (ofString "log_address")) = some (.val (.word log_addr)) := by
                simp [evalHOLExact, hl6, HolFiniteMapExact.lookup_update, FUPDATE]
              apply memcpy_heap_both_g09 (s0 := s0)
                (ExpHOL.var VarKind.local (ofString "log_address"))
                (ExpHOL.load ShapeHOL.one
                  (ExpHOL.op BinOp.add
                    [ExpHOL.load ShapeHOL.one
                        (ExpHOL.op BinOp.add [ExpHOL.var VarKind.global (ofString "ev"), ExpHOL.const 112#64]),
                      ExpHOL.const 32#64]))
                (ExpHOL.const 20#64)
                log_addr src_addr 0x14#64 log_addr.toNat (qw3.toNat - log_addr.toNat) _
                hc6 hInvW6 hWF6
                (by rw [hch6, hch5, show evmChain s4 = evmChain s3 by rw [hs4_eq]; exact StateRestoreEpilogue.evmChain_lc s3 s3.locals srns.clock, hch3]; exact hlen0)
                (by show OpDispatchSpec.evmR s6 < OpDispatchSpec.evmR s0
                    rw [hR6, hR5,
                      show OpDispatchSpec.evmR s4 = OpDispatchSpec.evmR s3 by rw [hs4_eq]; exact StateRestoreEpilogue.evmR_lc s3 s3.locals srns.clock]
                    exact hR3)
                hd_addr6 hsrc_addr rfl haddr8 (by omega)
                (fun _ => ⟨le_refl _, by change log_addr.toNat + 20 ≤ _; omega⟩) hdj_addr6 ?_ hnt6
              intro s7 hc7 hInvW7 hWF7 hlen7 hR7 heff7 hl7 hwti7 hfo7 hch7 hHM7_imp hnt7
              -- Step 17: header stores `log+0 := log_address; log+8 := topics; log+16 := ntopics`
              rw [← evaluate_seq_assoc_g09, ← evaluate_seq_assoc_g09] at hnt7 ⊢
              have hl7_log : s7.locals.lookup (ofString "log") = some (.val (.word log)) := by
                rw [hl7, hl6]; simp [HolFiniteMapExact.lookup_update, FUPDATE, (by decide : ofString "log_address" ≠ ofString "log"), hl5]
              have hl7_addr : s7.locals.lookup (ofString "log_address") = some (.val (.word log_addr)) := by
                rw [hl7, hl6]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
              have hl7_top : s7.locals.lookup (ofString "topics") = some (.val (.word topics)) := by
                rw [hl7, hl6]; simp only [HolFiniteMapExact.lookup_update, FUPDATE, (by decide : ofString "log_address" ≠ ofString "topics"), ↓reduceIte]
                rw [hl5]; simp only [HolFiniteMapExact.lookup_update, FUPDATE, (by decide : ofString "log" ≠ ofString "topics"), ↓reduceIte]
                change s3.locals.lookup _ = _; change s2.locals.lookup _ = _
                rw [hlk2 _ (by decide) (by decide)]; exact htop_si
              have hl7_nt : s7.locals.lookup (ofString "ntopics") = some (.val (.word nt)) := by
                rw [hl7, hl6]; simp only [HolFiniteMapExact.lookup_update, FUPDATE, (by decide : ofString "log_address" ≠ ofString "ntopics"), ↓reduceIte]
                rw [hl5]; simp only [HolFiniteMapExact.lookup_update, FUPDATE, (by decide : ofString "log" ≠ ofString "ntopics"), ↓reduceIte]
                change s3.locals.lookup _ = _; change s2.locals.lookup _ = _
                rw [hlk2 _ (by decide) (by decide)]; exact hnt_si
              have hwok_log7 : WordsOK s7 (log.toNat, 40) := by
                have hw5 : WordsOK s5 (log.toNat, 40) :=
                  ⟨hwok_log.1, by have := hwok_log.2.1; omega, fun k hk => hwok_log.2.2 k (by dsimp only at hk ⊢; omega)⟩
                exact (wordsOK_congr_of_dom_g09 (heff7.memaddrs.trans (by rw [hInvW6.1.1.memaddrs, hInvW5.1.1.memaddrs]))).2 hw5
              have hoff_log : ∀ k : Nat, k < 40 → log + BitVec.ofNat 64 k = BitVec.ofNat 64 (log.toNat + k) := fun k hk =>
                BitVec.eq_of_toNat_eq (by
                  have := R11Shards.heapLimit_val
                  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)])
              have hd7_0 : s7.memaddrs log := by
                have h := (hwok_log7.2.2 0 (by omega)).choose_spec.1
                have heq : BitVec.ofNat 64 (log.toNat + 8 * 0) = log :=
                  BitVec.eq_of_toNat_eq (by have := R11Shards.heapLimit_val; rw [BitVec.toNat_ofNat, Nat.add_zero, Nat.mod_eq_of_lt (by omega)])
                rwa [heq] at h
              have hd7_8 : s7.memaddrs (log + 8#64) := by
                rw [hoff_log 8 (by omega)]; exact (hwok_log7.2.2 1 (by omega)).choose_spec.1
              have hd7_16 : s7.memaddrs (log + 16#64) := by
                rw [hoff_log 16 (by omega)]; exact (hwok_log7.2.2 2 (by omega)).choose_spec.1
              have hdj_log7 : IvlsDisj [(log.toNat, 40)] (worldTypedIvls s7 S Nd ++ ((evmChain s7).map (frameObjects s7)).flatten) := by
                rw [hwti7, hfo7, hwti6, hfo6]
                intro o ho j hj; simp only [List.mem_singleton] at ho; subst ho
                have hd := hdj_log5 (log.toNat, qw2.toNat - log.toNat) (by simp) j hj
                rcases hd with h0 | h0 | h0 | h0
                · simp only [Disj] at h0 ⊢; omega
                · exact Or.inr (Or.inl h0)
                · simp only [Disj] at h0 ⊢; omega
                · simp only [Disj] at h0 ⊢; omega
              have hst7 : s7.evaluateHOLFiniteState
                  (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "log"), ExpHOL.const 0#64]) (ExpHOL.var VarKind.local (ofString "log_address")))
                    (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "log"), ExpHOL.const 8#64]) (ExpHOL.var VarKind.local (ofString "topics")))
                      (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "log"), ExpHOL.const 16#64]) (ExpHOL.var VarKind.local (ofString "ntopics"))))) =
                (none, {s7 with memory := fun a => if a = log + 16#64 then .word nt else
                  if a = log + 8#64 then .word topics else if a = log then .word log_addr else s7.memory a}) :=
                op_log_header_stores_exact_g09 s7 log log_addr topics nt hl7_log hl7_addr hl7_top hl7_nt hd7_0 hd7_8 hd7_16
              rw [evaluateHOLFiniteState_seq_line780, evaluate_seq_assoc_g09] at hnt7 ⊢
              rw [hst7] at hnt7 ⊢
              dsimp only at hnt7 ⊢
              let s8 : PanSemStateFiniteExact 64 F :=
                { s7 with memory := fun a => if a = log + 16#64 then .word nt else
                    if a = log + 8#64 then .word topics else if a = log then .word log_addr else s7.memory a }
              have hc8 : s8.code = originalRuntimeCode := hc7
              have hb_log64 : log.toNat + 40 ≤ 2 ^ 64 := by have := R11Shards.heapLimit_val; omega
              have heff8 : ByteRegionEffect s7 s8 [(log.toNat, 40)] :=
                op_log_header_stores_effect_g09 s7 log log_addr topics nt hInvW7.1.1.memaddrs hb_log64 hd7_0 hd7_8 hd7_16
              obtain ⟨hInvW8, hwti8, hfo8, _, hch8, hR8, hHM8_imp⟩ := evmInvWith_of_bre hInvW7 hdj_log7 heff8
              have hWF8 : W → HeadMemChainWF s8 := fun hw0 =>
                headMemChainWF_of_heap_bre_g09 (evmInvWith_to_evmInv hInvW7) (hWF7 hw0) heff8 hch8 hlog8 (by omega)
              have hs8_0 : memW s8 log.toNat = log_addr.toNat := by
                have h0_eq : BitVec.ofNat 64 log.toNat = log := (BitVec.ofNat_toNat 64 log).trans (BitVec.setWidth_eq log)
                have hne16 : log ≠ log + 16#64 := by
                  intro he; have := congrArg BitVec.toNat he; rw [hoff_log 16 (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this; omega
                have hne8 : log ≠ log + 8#64 := by
                  intro he; have := congrArg BitVec.toNat he; rw [hoff_log 8 (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this; omega
                unfold memW; rw [h0_eq]; simp [s8, hne16, hne8]
              have hs8_8 : memW s8 (log.toNat + 8) = topics.toNat := by
                have hne16 : log + 8#64 ≠ log + 16#64 := by
                  intro he; have := congrArg BitVec.toNat he
                  rw [hoff_log 8 (by omega), hoff_log 16 (by omega), BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; omega
                unfold memW; rw [← hoff_log 8 (by omega)]; simp [s8, hne16]
              have hs8_16 : memW s8 (log.toNat + 16) = nt.toNat := by
                unfold memW; rw [← hoff_log 16 (by omega)]; simp [s8]
              -- Step 18: `decCall "data" .one "alloc" [n + 8#64]`
              have hl8_n : s8.locals.lookup (ofString "n") = some (.val (.word nw)) := by
                change s7.locals.lookup _ = _; rw [hl7, hl6]
                simp only [HolFiniteMapExact.lookup_update, FUPDATE, (by decide : ofString "log_address" ≠ ofString "n"), ↓reduceIte]
                rw [hl5]; simp only [HolFiniteMapExact.lookup_update, FUPDATE, (by decide : ofString "log" ≠ ofString "n"), ↓reduceIte]
                change s2.locals.lookup _ = _; rw [hlk2 _ (by decide) (by decide)]
                simpa [si, setVarHOLFinite, hl1, HolFiniteMapExact.lookup_update, FUPDATE,
                  (by decide : ofString "i" ≠ ofString "n"), (by decide : ofString "topics" ≠ ofString "n")] using hn_lk
              have hsz_data : @evalHOLExact 64 F _ s8.toExact (fun a => Classical.propDecidable (s8.memaddrs a))
                  (.op .add [.var .local (ofString "n"), .const 0x8#64]) = some (.val (.word (nw + 8#64))) := by
                simp [evalHOLExact, evalListHOLExact, hl8_n, wordOpHOL, wordOp, valueIsWord, valueWord]
              have hnw8_nat : (nw + 8#64).toNat = nw.toNat + 8 := by
                rw [BitVec.toNat_add, show (8#64 : BitVec 64).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
              apply decCall_alloc_both_g09 hc8 hInvW8 hWF8 hsz_data hnt7
              intro data qw4 s9 hc9 hInvW9 hWF9 hwti9 hfo9 hch9 hR9 hHM9_imp hg9 hm9 _ hl9 hp8_eq hq9_eq hfit9 hlim9 hdata8 _ hdata_lo _ hdj_data9 hnt9
              have hp8_q3 : data.toNat = qw3.toNat := by
                have : globN s8 "heap_ptr" = qw3.toNat := by
                  change globN s7 "heap_ptr" = qw3.toNat
                  rw [R16Shards.OpHandlers.globN_eq_of_lookup_eq (congrFun (congrArg HolFiniteMapExact.lookup heff7.globals) _)]; exact hq6_eq
                omega
              have hfit9' : data.toNat + (nw.toNat + 8) ≤ qw4.toNat := by rwa [hnw8_nat] at hfit9
              -- Step 19: `decCall "s" .one "sat_word" [start]`
              have hl9_start : s9.locals.lookup (ofString "start") =
                  some (.rStruct [.val (.word sa), .val (.word sb), .val (.word sc), .val (.word sd)]) := by
                rw [hl9]; simp only [HolFiniteMapExact.lookup_update, FUPDATE, (by decide : ofString "data" ≠ ofString "start"), ↓reduceIte]
                change s7.locals.lookup _ = _; rw [hl7, hl6]
                simp only [HolFiniteMapExact.lookup_update, FUPDATE, (by decide : ofString "log_address" ≠ ofString "start"), ↓reduceIte]
                rw [hl5]; simp only [HolFiniteMapExact.lookup_update, FUPDATE, (by decide : ofString "log" ≠ ofString "start"), ↓reduceIte]
                change s2.locals.lookup _ = _; rw [hlk2 _ (by decide) (by decide)]
                simpa [si, setVarHOLFinite, hl1, HolFiniteMapExact.lookup_update, FUPDATE,
                  (by decide : ofString "i" ≠ ofString "start"), (by decide : ofString "topics" ≠ ofString "start")] using hstart_lk
              rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt9 ⊢
              have hargs_sw : evalListHOLFinite s9 (h := fun a => Classical.propDecidable (s9.memaddrs a))
                  [.var .local (ofString "start")] =
                  some [.rStruct [.val (.word sa), .val (.word sb), .val (.word sc), .val (.word sd)]] := by
                rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, evalHOLExact, hl9_start]
              rw [hargs_sw] at hnt9 ⊢; dsimp only at hnt9 ⊢
              obtain ⟨params_sw, body_sw, ret_sw, hlk_sw_spec, hspec_sw⟩ := eps_sat_word_exact_g09
              rcases hlk_sw : lookupCodeHOLFinite s9.code.lookup (ofString "sat_word")
                  [.rStruct [.val (.word sa), .val (.word sb), .val (.word sc), .val (.word sd)]] with _ | ⟨bsw, calsw, rsw⟩
              · exact opDispatchPostBoth_error W s0 s9
              · simp only [hlk_sw] at hnt9 ⊢
                by_cases hclk9 : s9.clock = 0
                · simp [hclk9] at hnt9
                · simp only [hclk9, ↓reduceIte] at hnt9 ⊢
                  have hlk_sw_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "sat_word")
                      [.rStruct [.val (.word sa), .val (.word sb), .val (.word sc), .val (.word sd)]] = some (bsw, calsw, rsw) := by
                    rwa [← hc9]
                  obtain ⟨hbsw1, rfl, hcal_v⟩ := one_u256_arg_lookup_g09 lookup_sat_word_g09 hlk_sw_orig
                  have hbsw2 : bsw = body_sw :=
                    lookupCodeHOLFinite_installed_body s9.code.lookup _ _ _ _ _ _ [.rStruct _] calsw (by rw [hc9]; exact hlk_sw_spec) hlk_sw
                  subst hbsw2
                  have hret_one : ret_sw = ShapeHOL.one := by
                    have h2 := hlk_sw_spec.symm.trans lookup_sat_word_g09
                    injection h2 with h2p
                    rcases Prod.mk.inj h2p with ⟨_, h2r⟩
                    rcases Prod.mk.inj h2r with ⟨_, hret_one⟩
                    exact hret_one
                  rw [hret_one] at hspec_sw
                  let ent_sw := callEntryStateHOLFinite s9 calsw
                  have hmeta_sw := (PanRunBounded.evaluateHOLFiniteState_metadata ent_sw bsw).1
                  rcases hrun_sw : evaluateHOLFiniteState ent_sw bsw with ⟨r_sw, s_sw⟩
                  simp only [ent_sw, hrun_sw] at hnt9 hmeta_sw ⊢
                  have hsw_out (hsafe_sw : r_sw ≠ some .timeOut) :=
                    hspec_sw ent_sw hc9 (localsFree_evmInv s9 calsw (s9.clock - 1) (evmInvWith_to_evmInv hInvW9))
                      ⟨sa, sb, sc, sd, hcal_v⟩ ⟨[_], hlk_sw_orig⟩ (by rw [hrun_sw]; exact hsafe_sw)
                  cases r_sw with
                  | none => exact opDispatchPostBoth_error W s0 s_sw
                  | some r_sw0 =>
                    cases r_sw0 with
                    | timeOut => simp at hnt9
                    | error => exact opDispatchPostBoth_error W s0 s_sw.emptyLocalsHOLFinite
                    | «break» | «continue» => exact opDispatchPostBoth_error W s0 s_sw
                    | finalFfi _ => exact opDispatchPostBoth_other (fun _ h => by cases h) (by rintro ⟨_, h⟩; cases h)
                    | exception eid ev =>
                      by_cases heid : eid = ofString "EvmErr"
                      · subst heid
                        have herr_sw := (hsw_out (by simp)).2
                        rw [hrun_sw] at herr_sw; dsimp only at herr_sw
                        obtain ⟨hInv_sw, hch_sw0, hR_sw0⟩ := herr_sw ⟨ev, rfl⟩
                        have hch_sw : (evmChain s_sw.emptyLocalsHOLFinite).length = (evmChain s0).length := by
                          rw [emptyLocalsHOLFinite, StateRestoreEpilogue.evmChain_lc]
                          have h3 : evmChain ent_sw = evmChain s9 :=
                            StateRestoreEpilogue.evmChain_lc s9 calsw (s9.clock - 1)
                          rw [hch_sw0, h3, hch9, hch8]; exact hlen7
                        have hR_sw : evmR s_sw.emptyLocalsHOLFinite ≤ evmR s0 := by
                          have h1 : evmR s_sw.emptyLocalsHOLFinite = evmR s_sw :=
                            StateRestoreEpilogue.evmR_lc s_sw (emptyLocalsHOLFinite s_sw).locals
                              (emptyLocalsHOLFinite s_sw).clock
                          rw [h1]
                          have hR_ent : evmR ent_sw ≤ evmR s0 := by
                            have h2 : evmR ent_sw = evmR s9 :=
                              StateRestoreEpilogue.evmR_lc s9 calsw (s9.clock - 1)
                            rw [h2]
                            have h9' : evmR s9 < evmR s0 := by
                              have hR8b : evmR s8 = evmR s7 := hR8
                              have hR9b : evmR s9 = evmR s8 := hR9
                              rw [hR9b, hR8b]
                              exact hR7
                            exact Nat.le_of_lt h9'
                          exact Nat.le_trans hR_sw0 hR_ent
                        refine And.intro (And.intro (fun ⟨_, h⟩ => by cases h) (fun _ => ⟨localsFree_evmInv s_sw (emptyLocalsHOLFinite s_sw).locals s_sw.clock hInv_sw, hch_sw, hR_sw⟩)) (fun hw0 => ?_)
                        obtain ⟨_, body_swA, ret_swA, hlk_sw_specA, hspec_swA⟩ := Group09ChainWF.epsA_sat_word_exact_g09
                        have hb_swA : bsw = body_swA :=
                          (Prod.mk.inj (Prod.mk.inj (Option.some.inj (hlk_sw_spec.symm.trans hlk_sw_specA))).2).1
                        have hret_oneA : ret_swA = ShapeHOL.one := by
                          have h2 := hlk_sw_specA.symm.trans lookup_sat_word_g09
                          injection h2 with h2p
                          rcases Prod.mk.inj h2p with ⟨_, h2r⟩
                          rcases Prod.mk.inj h2r with ⟨_, hret_oneA⟩
                          exact hret_oneA
                        rw [hret_oneA] at hspec_swA
                        have herr_swA := (hspec_swA ent_sw hc9
                          (localsFree_evmInv s9 calsw (s9.clock - 1) (evmInvWith_to_evmInv hInvW9))
                          (headMemChainWF_locals s9 calsw (s9.clock - 1) (hWF9 hw0))
                          ⟨sa, sb, sc, sd, hcal_v⟩ ⟨[_], by rwa [← hb_swA]⟩ (by rw [← hb_swA, hrun_sw]; simp)).2
                        rw [← hb_swA, hrun_sw] at herr_swA; dsimp only at herr_swA
                        obtain ⟨hInvWF_sw, _, _⟩ := herr_swA ⟨ev, rfl⟩
                        have hInv_sw_b : EvmInv s_sw.emptyLocalsHOLFinite :=
                          localsFree_evmInv s_sw s_sw.emptyLocalsHOLFinite.locals s_sw.clock hInvWF_sw.1
                        have hWF_sw_b : HeadMemChainWF s_sw.emptyLocalsHOLFinite :=
                          headMemChainWF_locals s_sw s_sw.emptyLocalsHOLFinite.locals s_sw.clock hInvWF_sw.2
                        dsimp only at ⊢
                        exact And.intro (fun ⟨_, h⟩ => by cases h)
                          (fun _ => ⟨⟨hInv_sw_b, hWF_sw_b⟩, ⟨hch_sw, hR_sw⟩⟩)
                      · refine opDispatchPostBoth_other (fun _ h => by cases h) ?_
                        rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact absurd h1 heid
                    | returned v_sw =>
                      have hsw_ret := (hsw_out (by simp)).1 v_sw (by rw [hrun_sw])
                      rw [hrun_sw] at hsw_ret; dsimp only at hsw_ret
                      obtain ⟨_, _, _, hlf_sw, hv_sw_eq⟩ := hsw_ret
                      let sw_word := satWordG09 (.rStruct [.val (.word sa), .val (.word sb), .val (.word sc), .val (.word sd)])
                      have hv_sw : v_sw = .val (.word sw_word) := hv_sw_eq _ hcal_v
                      subst hv_sw
                      have hsh_sw : (shapeEqHOL (shapeOfHOLExact (.val (.word sw_word) : ValueHOL 64)) .one &&
                          shapeEqHOL (shapeOfHOLExact (.val (.word sw_word) : ValueHOL 64)) .one) = true := by
                        simp [shapeOfHOLExact, shapeEqHOL]
                      simp only [hsh_sw, ↓reduceIte] at hnt9 ⊢
                      let s10 : PanSemStateFiniteExact 64 F := setVarHOLFinite (ofString "s") (.val (.word sw_word)) { s_sw with locals := s9.locals }
                      have hs10_eq : s10 = { s9 with locals := s10.locals, clock := s_sw.clock } := by
                        dsimp only [s10, setVarHOLFinite]; rw [hlf_sw]; cases s9; rfl
                      have hc10 : s10.code = originalRuntimeCode := by rw [hs10_eq]; exact hc9
                      have hInvW10 : EvmInvWith s10 S Nd := by rw [hs10_eq]; exact evmInvWith_localsFree s10.locals s_sw.clock hInvW9
                      have hWF10 : W → HeadMemChainWF s10 := fun hw0 => by rw [hs10_eq]; exact headMemChainWF_locals s9 s10.locals s_sw.clock (hWF9 hw0)
                      have hR10 : OpDispatchSpec.evmR s10 = OpDispatchSpec.evmR s9 := by
                        rw [hs10_eq]; exact StateRestoreEpilogue.evmR_lc s9 s10.locals s_sw.clock
                      refine opDispatchPostBoth_congr_lc (post := (evaluateHOLFiniteState s10 _).2) rfl ?_
                      -- Step 20: `memcpy(data, load(ev + 0x18) + s, n)`
                      have hl10_s : s10.locals.lookup (ofString "s") = some (.val (.word sw_word)) := by
                        simp [s10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                      have hl10_data : s10.locals.lookup (ofString "data") = some (.val (.word data)) := by
                        simp [s10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                          (by decide : ofString "s" ≠ ofString "data"), hl9]
                      have hl10_n : s10.locals.lookup (ofString "n") = some (.val (.word nw)) := by
                        simp [s10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                          (by decide : ofString "s" ≠ ofString "n"), hl9, (by decide : ofString "data" ≠ ofString "n"), hl8_n]
                      obtain ⟨memw10, hsrc_data⟩ := eval_ev_mem_plus_s_g09 s10 hInvW10.1 hInvW10.2.1 hl10_s
                      have hd_data10 : @evalHOLExact 64 F _ s10.toExact (fun a => Classical.propDecidable (s10.memaddrs a))
                          (.var .local (ofString "data")) = some (.val (.word data)) := by simp [evalHOLExact, hl10_data]
                      have hn_data10 : @evalHOLExact 64 F _ s10.toExact (fun a => Classical.propDecidable (s10.memaddrs a))
                          (.var .local (ofString "n")) = some (.val (.word nw)) := by simp [evalHOLExact, hl10_n]
                      have hdj_data10 : IvlsDisj [(data.toNat, qw4.toNat - data.toNat)]
                          (worldTypedIvls s10 S Nd ++ ((evmChain s10).map (frameObjects s10)).flatten) := by
                        rw [worldTypedIvls_congr_mg_g09 (s := s9) (t := s10) (by rw [hs10_eq]) (by rw [hs10_eq]),
                            map_frameObjects_congr_mg_g09 (s := s9) (t := s10) (by rw [hs10_eq]) (by rw [hs10_eq])]; exact hdj_data9
                      apply memcpy_heap_both_g09 (s0 := s0)
                        (ExpHOL.var VarKind.local (ofString "data"))
                        (ExpHOL.op BinOp.add
                          [ExpHOL.load ShapeHOL.one
                              (ExpHOL.op BinOp.add [ExpHOL.var VarKind.global (ofString "ev"),
                                ExpHOL.const 24#64]),
                            ExpHOL.var VarKind.local (ofString "s")])
                        (ExpHOL.var VarKind.local (ofString "n"))
                        data (memw10 + sw_word) nw data.toNat (qw4.toNat - data.toNat) _
                        hc10 hInvW10 hWF10
                        (by rw [show evmChain s10 = evmChain s9 by rw [hs10_eq]; exact StateRestoreEpilogue.evmChain_lc s9 s10.locals s_sw.clock, hch9, hch8]; exact hlen7)
                        (by show OpDispatchSpec.evmR s10 < OpDispatchSpec.evmR s0
                            have h1 : OpDispatchSpec.evmR s10 = OpDispatchSpec.evmR s9 := hR10
                            have h2 : OpDispatchSpec.evmR s9 = OpDispatchSpec.evmR s8 := hR9
                            have h3 : OpDispatchSpec.evmR s8 = OpDispatchSpec.evmR s7 := hR8
                            rw [h1, h2, h3]
                            exact hR7)
                        hd_data10 hsrc_data hn_data10 hdata8 (by omega)
                        (fun _ => ⟨le_refl _, by omega⟩) hdj_data10 ?_ hnt9
                      intro s11 hc11 hInvW11 hWF11 hlen11 hR11 heff11 hl11 hwti11 hfo11 hch11 hHM11_imp hnt11
                      -- Step 21: `log+24 := data; log+32 := n`
                      rw [← evaluate_seq_assoc_g09] at hnt11 ⊢
                      have hl11_log : s11.locals.lookup (ofString "log") = some (.val (.word log)) := by
                        rw [hl11]; simp only [s10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, (by decide : ofString "s" ≠ ofString "log"), ↓reduceIte]
                        rw [hl9]; simp only [HolFiniteMapExact.lookup_update, FUPDATE, (by decide : ofString "data" ≠ ofString "log"), ↓reduceIte]
                        exact hl7_log
                      have hl11_data : s11.locals.lookup (ofString "data") = some (.val (.word data)) := by rw [hl11]; exact hl10_data
                      have hl11_n : s11.locals.lookup (ofString "n") = some (.val (.word nw)) := by rw [hl11]; exact hl10_n
                      have hwok_log11 : WordsOK s11 (log.toNat, 40) :=
                        (wordsOK_congr_of_dom_g09 (hInvW11.1.1.memaddrs.trans hInvW7.1.1.memaddrs.symm)).2 hwok_log7
                      have hd11_24 : s11.memaddrs (log + 24#64) := by
                        rw [hoff_log 24 (by omega)]; exact (hwok_log11.2.2 3 (by omega)).choose_spec.1
                      have hd11_32 : s11.memaddrs (log + 32#64) := by
                        rw [hoff_log 32 (by omega)]; exact (hwok_log11.2.2 4 (by omega)).choose_spec.1
                      have hdj_log11 : IvlsDisj [(log.toNat, 40)] (worldTypedIvls s11 S Nd ++ ((evmChain s11).map (frameObjects s11)).flatten) := by
                        rw [hwti11, hfo11,
                            worldTypedIvls_congr_mg_g09 (s := s9) (t := s10) (by rw [hs10_eq]) (by rw [hs10_eq]),
                            map_frameObjects_congr_mg_g09 (s := s9) (t := s10) (by rw [hs10_eq]) (by rw [hs10_eq]),
                            hwti9, hfo9, hwti8, hfo8]
                        exact hdj_log7
                      have hst11_data : s11.evaluateHOLFiniteState
                          (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "log"), ExpHOL.const 24#64]) (ExpHOL.var VarKind.local (ofString "data")))
                            (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "log"), ExpHOL.const 32#64]) (ExpHOL.var VarKind.local (ofString "n")))) =
                        (none, {s11 with memory := fun a => if a = log + 32#64 then .word nw else
                          if a = log + 24#64 then .word data else s11.memory a}) :=
                        op_log_data_stores_exact_g09 s11 log data nw hl11_log hl11_data hl11_n hd11_24 hd11_32
                      rw [evaluateHOLFiniteState_seq_line780] at hnt11 ⊢
                      rw [hst11_data] at hnt11 ⊢
                      dsimp only at hnt11 ⊢
                      let last : PanSemStateFiniteExact 64 F :=
                        { s11 with memory := fun a => if a = log + 32#64 then .word nw else
                            if a = log + 24#64 then .word data else s11.memory a }
                      have heff_last : ByteRegionEffect s11 last [(log.toNat, 40)] :=
                        op_log_data_stores_effect_g09 s11 log data nw hInvW11.1.1.memaddrs hb_log64 hd11_24 hd11_32
                      obtain ⟨hInvW_last, hwti_last, hfo_last, _, hch_last, hR_last, hHM_last_imp⟩ := evmInvWith_of_bre hInvW11 hdj_log11 heff_last
                      have hWF_last : W → HeadMemChainWF last := fun hw0 =>
                        headMemChainWF_of_heap_bre_g09 (evmInvWith_to_evmInv hInvW11) (hWF11 hw0) heff_last hch_last hlog8 (by omega)
                      have hHM_last : HeadMemAligned last :=
                        hHM_last_imp (hHM11_imp (by rw [hs10_eq]; exact hHM9_imp (hHM8_imp (hHM7_imp (hHM6_imp (hHM5_imp hHM4))))))
                      have hmem_s11_log : ∀ k : Nat, k + 8 ≤ 40 → k % 8 = 0 → memW s11 (log.toNat + k) = memW s8 (log.toNat + k) := by
                        intro k hk hk8
                        have hlt_k : log.toNat + k < 2 ^ 64 := by omega
                        unfold memW; rw [heff11.cell_frame (BitVec.ofNat 64 (log.toNat + k))]
                        · change (match s10.memory _ with | .word w => w.toNat) = _
                          have hm10_8 : s10.memory = s8.memory := by rw [hs10_eq, hm9]
                          rw [hm10_8]
                        · intro x hx; simp only [List.mem_singleton] at hx; subst hx
                          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt_k]
                          unfold CellHits; dsimp only; omega
                      have hnw_lt32 : nw.toNat < 2 ^ 32 :=
                        heap_alloc_size_lt_twoPow32 hdata_lo (by omega) hlim9
                      have hhp_s11 : globN s11 "heap_ptr" = qw4.toNat := by
                        rw [R16Shards.OpHandlers.globN_eq_of_lookup_eq (congrFun (congrArg HolFiniteMapExact.lookup heff11.globals) _)]
                        rw [show globN s10 "heap_ptr" = globN s9 "heap_ptr" by rw [hs10_eq]; rfl]; exact hq9_eq
                      have hlog_ok : LogEntryOK last log.toNat :=
                        op_log_data_stores_valid_g09 s11 log log_addr topics data nt nw hb_log64 hwok_log11
                          hlog_lo (by omega) haddr_lo (by omega) htop_lo (by omega) hdata_lo (by omega) hnt4 hnw_lt32
                          (by simpa using (hmem_s11_log 0 (by omega) (by omega)).trans hs8_0)
                          ((hmem_s11_log 8 (by omega) (by omega)).trans hs8_8)
                          ((hmem_s11_log 16 (by omega) (by omega)).trans hs8_16)
                      have hlast_fields :
                          memW last log.toNat = log_addr.toNat ∧ memW last (log.toNat + 8) = topics.toNat ∧
                          memW last (log.toNat + 16) = nt.toNat ∧ memW last (log.toNat + 24) = data.toNat ∧
                          memW last (log.toNat + 32) = nw.toNat := by
                        have hne_off : ∀ a b : Nat, a < 40 → b < 40 → a ≠ b → BitVec.ofNat 64 (log.toNat + a) ≠ log + BitVec.ofNat 64 b := by
                          intro a b ha hb' hab he; have ht := congrArg BitVec.toNat he
                          rw [hoff_log b hb', BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at ht; omega
                        refine ⟨?_, ?_, ?_, ?_, ?_⟩
                        · have h32 := hne_off 0 32 (by omega) (by omega) (by omega)
                          have h24 := hne_off 0 24 (by omega) (by omega) (by omega)
                          simp only [Nat.add_zero] at h32 h24
                          simpa only [last, memW, Nat.add_zero, if_neg h32, if_neg h24] using (hmem_s11_log 0 (by omega) (by omega)).trans hs8_0
                        · simpa only [last, memW, if_neg (hne_off 8 32 (by omega) (by omega) (by omega)),
                            if_neg (hne_off 8 24 (by omega) (by omega) (by omega))] using (hmem_s11_log 8 (by omega) (by omega)).trans hs8_8
                        · simpa only [last, memW, if_neg (hne_off 16 32 (by omega) (by omega) (by omega)),
                            if_neg (hne_off 16 24 (by omega) (by omega) (by omega))] using (hmem_s11_log 16 (by omega) (by omega)).trans hs8_16
                        · have hne24_32 : log + 24#64 ≠ log + 32#64 := by
                            intro he; have := congrArg BitVec.toNat he
                            rw [hoff_log 24 (by omega), hoff_log 32 (by omega), BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                                Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; omega
                          unfold memW; rw [← hoff_log 24 (by omega)]; simp [last, hne24_32]
                        · unfold memW; rw [← hoff_log 32 (by omega)]; simp [last]
                      -- Step 22: ownership package against `s` + `op_log_tail_log_append_pc_ret_g09`
                      obtain ⟨hpw_own, hfo_s_own, hmsg_s_own, hwo_s_own⟩ :=
                        op_log_detached_ownership_package_g09 hInvW0.1 hInvW0.2.1
                          hlast_fields.1 hlast_fields.2.1 hlast_fields.2.2.1 hlast_fields.2.2.2.1 hlast_fields.2.2.2.2
                          (by omega) (by omega) (by omega)
                          (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                              rcases hx with rfl | rfl | rfl | rfl <;> (dsimp only; omega))
                      have ho_hi : ∀ o ∈ logOwnedIvls last log.toNat, o.1 + o.2 ≤ heapLimit := by
                        intro o ho
                        have ho' := (List.mem_filter.1 ho).1
                        simp only [logRecordIvls, hlast_fields.1, hlast_fields.2.1, hlast_fields.2.2.1,
                          hlast_fields.2.2.2.1, hlast_fields.2.2.2.2, List.mem_cons, List.not_mem_nil, or_false] at ho'
                        rcases ho' with rfl | rfl | rfl | rfl <;> (dsimp only; omega)
                      have hch_last_s : evmChain last = evmChain s := by
                        rw [hch_last, hch11, show evmChain s10 = evmChain s9 by rw [hs10_eq]; exact StateRestoreEpilogue.evmChain_lc s9 s10.locals s_sw.clock, hch9, hch8, hch7, hch6, hch5,
                            show evmChain s4 = evmChain s3 by rw [hs4_eq]; exact StateRestoreEpilogue.evmChain_lc s3 s3.locals srns.clock, hch3]
                      have hfo_last_s3 : (evmChain last).map (frameObjects last) = (evmChain s3).map (frameObjects s3) := by
                        rw [hfo_last, hfo11,
                            map_frameObjects_congr_mg_g09 (s := s9) (t := s10) (by rw [hs10_eq]) (by rw [hs10_eq]),
                            hfo9, hfo8, hfo7, hfo6, hfo5,
                            map_frameObjects_congr_mg_g09 (s := s3) (t := s4) (by rw [hs4_eq]) (by rw [hs4_eq])]
                      have hnewOld_last : IvlsDisj ((evmChain last).map (frameObjects last)).flatten (logOwnedIvls last log.toNat) := by
                        rw [hfo_last_s3]
                        intro o ho j hj
                        obtain ⟨l, hl_mem, ho_l⟩ := List.mem_flatten.1 ho
                        obtain ⟨ec, hec3, rfl⟩ := List.mem_map.1 hl_mem
                        rw [hch3] at hec3
                        rcases hfo3 ec hec3 o ho_l with ho_s | rfl
                        · exact hfo_s_own o ho_s j hj
                        · rcases hmem_em_ge with hge | hz
                          · have := ho_hi j hj; have := R11Shards.heapLimit_val; have := R11Shards.scratchStart_val
                            exact Or.inr (Or.inr (Or.inr (by dsimp only; omega)))
                          · exact Or.inl hz
                      have hmsg_last : ∀ ec ∈ evmChain last, ∀ o ∈ logOwnedIvls last log.toNat,
                          Disj (memW last (ec.1 + 112), 176) o := by
                        intro ec hec o ho
                        rw [hch_last_s] at hec
                        have hFW_s := hInvW0.2.1.2.2.2.2.1 ec hec
                        obtain ⟨hb_e, _, _, _⟩ := frameWF_bounds hInvW0.1.2 hFW_s
                        obtain ⟨he_lo, _⟩ := (hFW_s.1 (ec.1, 280) (by simp)).1
                        have h112_lt : ec.1 + 112 < 2 ^ 64 := by omega
                        have hlim_le : heapLimit ≤ scratchStart := by rw [R11Shards.heapLimit_val, R11Shards.scratchStart_val]
                        have hno_heap : ∀ {b sz : Nat}, b + sz ≤ heapLimit →
                            ∀ x ∈ ([(b, sz)] : List Ivl), ¬ CellHits (BitVec.ofNat 64 (ec.1 + 112)).toNat x := by
                          intro b sz hbs x hx; simp only [List.mem_singleton] at hx; subst hx
                          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h112_lt]
                          have hsc1 := hInvW0.1.2.2.2.1; have hsc2 := hInvW0.1.2.2.2.2.1
                          unfold CellHits; dsimp only at he_lo ⊢; omega
                        have hm_eq : memW last (ec.1 + 112) = memW s3 (ec.1 + 112) := by
                          unfold memW
                          rw [heff_last.cell_frame _ (hno_heap (by omega)),
                              heff11.cell_frame _ (hno_heap (by omega)),
                              show s10.memory = s9.memory by rw [hs10_eq], hm9,
                              heff8.cell_frame _ (hno_heap (by omega)),
                              heff7.cell_frame _ (hno_heap (by omega)),
                              hm6, hm5, show s4.memory = s3.memory by rw [hs4_eq]]
                        rw [hm_eq, hmsg3 ec hec]
                        exact hmsg_s_own ec hec o ho
                      have hwti_last_s : worldTypedIvls last S Nd = worldTypedIvls s S Nd := by
                        rw [hwti_last, hwti11,
                            worldTypedIvls_congr_mg_g09 (s := s9) (t := s10) (by rw [hs10_eq]) (by rw [hs10_eq]),
                            hwti9, hwti8, hwti7, hwti6, hwti5,
                            worldTypedIvls_congr_mg_g09 (s := s3) (t := s4) (by rw [hs4_eq]) (by rw [hs4_eq]), hwti3]
                      have hg_last_s : ∀ g : String, ofString g ≠ ofString "heap_ptr" → ofString g ≠ ofString "frame_mem_ptr" →
                          globN last g = globN s g := by
                        intro g hhp hfmp
                        have hg_l3 : last.globals.lookup (ofString g) = s3.globals.lookup (ofString g) := by
                          change s11.globals.lookup _ = _
                          rw [heff11.globals, show s10.globals = s9.globals by rw [hs10_eq], hg9]
                          simp [HolFiniteMapExact.lookup_update, FUPDATE, hhp, Ne.symm hhp]
                          change s7.globals.lookup _ = _
                          rw [heff7.globals, hg6]
                          simp [HolFiniteMapExact.lookup_update, FUPDATE, hhp, Ne.symm hhp]
                          rw [hg5]
                          simp [HolFiniteMapExact.lookup_update, FUPDATE, hhp, Ne.symm hhp]
                          rw [hs4_eq]
                        exact (R16Shards.OpHandlers.globN_eq_of_lookup_eq hg_l3).trans (hg3 g hhp hfmp)
                      have hwo_last : IvlsDisj (logOwnedIvls last log.toNat) (worldOwned last S Nd) :=
                        fun o ho i hi => hwo_s_own Nd ⟨hInvW0.2.1.1.1, hInvW0.2.1.1.2.1, hInvW0.2.1.1.2.2.1, hInvW0.2.2.1⟩
                          o ho i (worldOwned_subset_of_wti_eq_g09 hwti_last_s hg_last_s i hi)
                      have hcl_last : last.code = originalRuntimeCode := hc11
                      have htail_res := op_log_tail_log_append_pc_ret_g09 (s0 := s0) hcl_last hInvW_last
                        (by rw [hch_last]; exact hlen11)
                        (by have h1 : OpDispatchSpec.evmR last = OpDispatchSpec.evmR s11 := hR_last
                            rw [h1]
                            exact hR11)
                        hHM_last hl11_log hlog_ok hpw_own hnewOld_last hmsg_last hwo_last hnt11
                      exact ⟨htail_res.1, fun hw0 => htail_res.2 (hWF_last hw0)⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
