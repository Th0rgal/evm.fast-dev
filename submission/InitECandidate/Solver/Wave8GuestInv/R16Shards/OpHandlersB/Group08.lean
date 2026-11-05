import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.Common
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.ReadOnly
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.StackPush
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.ExtendMemoryHelpers
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.StateGasHelpers
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.WarmAccessHelpers

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8Contracts.M23

section ExistingGroup08

local macro "evmR" : term => `(OpDispatchSpec.evmR)

theorem lookup_charge_with_memory :
    originalRuntimeCode.lookup (ofString "charge_with_memory") =
      some ([(ofString "base", .one),
             (ofString "start", .comb [.one, .one, .one, .one]),
             (ofString "size", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_charge_with_memory, .one) :=
  lookup_of_guestAst_getElem 461 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_charge_with_memory) rfl

theorem lookup_op_mload :
    originalRuntimeCode.lookup (ofString "op_mload") =
      some ([], sourceFnBody Guest.Software.guestFn_op_mload, .one) :=
  lookup_of_guestAst_getElem 510 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_op_mload) rfl

private theorem store_some_eq_error_g08 {F : Type} {s post : PanSemStateFiniteExact 64 F}
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

private theorem headMemAligned_congr_head_only {F : Type}
    {s t : PanSemStateFiniteExact 64 F}
    (hg : t.globals = s.globals)
    (hmem : ∀ off : Nat, off ∈ ([24, 32, 40] : List Nat) →
      memW t (globN s "ev" + off) = memW s (globN s "ev" + off))
    (h : HeadMemAligned s) : HeadMemAligned t := by
  have hgev : globN t "ev" = globN s "ev" := globN_eq_of_lookup_eq (by rw [hg])
  have hgfp : globN t "frame_mem_ptr" = globN s "frame_mem_ptr" := globN_eq_of_lookup_eq (by rw [hg])
  refine ⟨?_, ?_⟩
  · rw [hgev, hmem 32 (by simp)]; exact h.1
  · rw [hgev, hgfp, hmem 24 (by simp), hmem 40 (by simp)]; exact h.2

private theorem eps_stack_pop_preserves_headMem :
    EvmPreservingSpec (fun _ => True)
      (fun s v post =>
        post.globals = s.globals ∧
        shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact v) = true ∧
        (HeadMemAligned s → HeadMemAligned post))
      (ofString "stack_pop") := by
  refine ⟨_, _, _, lookup_stack_pop_pub, ?_⟩
  intro F s hcode hInv _ hlookup hnt
  obtain ⟨params_sp, body_sp, ret_sp, hlk_sp, hspec_sp⟩ := eps_stack_pop
  have hlk_eq : some ([], sourceFnBody Guest.Software.guestFn_stack_pop, ShapeHOL.comb [.one, .one, .one, .one]) =
      some (params_sp, body_sp, ret_sp) := lookup_stack_pop_pub.symm.trans hlk_sp
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_sp, rfl⟩
  subst hbody_sp
  have hs := hspec_sp s hcode hInv trivial hlookup hnt
  dsimp only at hs ⊢
  refine ⟨fun v hv => ?_, hs.2⟩
  obtain ⟨hInv_p, hch_p, hR_p, hglob_p⟩ := hs.1 v hv
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by simp [evmChain, evmChainFrom]
  have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead_mem
  have hb_ev := (frameWF_bounds hInv.1.2 hFW0).1
  dsimp only at hb_ev
  have hev_pos : 0 < globN s "ev" := by
    obtain ⟨hin, _⟩ := (hFW0.1 (globN s "ev", 280) (by simp)).1
    have h1 := hInv.1.2.2.2.1; have h2 := hInv.1.2.2.2.2.1
    rw [R11Shards.scratchStart_val] at h1; dsimp only at hin; omega
  obtain ⟨evw, hevw, hevw_nat⟩ := global_word_of_pos s "ev" hev_pos
  let retExp : ExpHOL 64 :=
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural
      (Exp.load (Shape.comb [Shape.one, Shape.one, Shape.one, Shape.one])
        (Exp.op BinOp.add [(Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.global "ev"), (Exp.const (BitVec.ofNat 64 8))])),
          (Exp.panOp PanOp.mul [(Exp.var VarKind.local "sp"), (Exp.const (BitVec.ofNat 64 32))])]))
  have hb : sourceFnBody Guest.Software.guestFn_stack_pop =
      .dec (ofString "sp") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 16]))
        (.seq
          (.ite (.cmp .equal (.var .local (ofString "sp")) (.const 0))
            (.raise (ofString "EvmErr") (.const 2))
            .skip)
          (.seq
            (.assign .local (ofString "sp") (.op .sub [.var .local (ofString "sp"), .const 1]))
            (.seq
              (.store (.op .add [.var .global (ofString "ev"), .const 16]) (.var .local (ofString "sp")))
              (.return retExp)))) := rfl
  have hret_load_shape : ∀ (st : PanSemStateFiniteExact 64 F) (vr : ValueHOL 64),
      (evaluateHOLFiniteState st (.return retExp)).1 = some (.returned vr) →
      shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact vr) = true := by
    intro st vr hret
    rw [evaluateHOLFiniteState_return] at hret
    dsimp only [retExp,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
      List.map] at hret
    rcases hev_r : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
        (.load (.comb [.one, .one, .one, .one])
          (.op .add
            [.load .one (.op .add [.var .global (ofString "ev"), .const 8#64]),
             .panop .mul [.var .local (ofString "sp"), .const 32#64]])) with _ | vr0
    · rw [hev_r] at hret; simp at hret
    · rw [hev_r] at hret; dsimp only at hret
      split at hret
      · injection hret with h1; injection h1 with hvr; subst hvr
        rw [evalHOLExact.eq_def] at hev_r
        dsimp only at hev_r
        split_ifs at hev_r
        rcases ha : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
            (.op .add
              [.load .one (.op .add [.var .global (ofString "ev"), .const 8#64]),
               .panop .mul [.var .local (ofString "sp"), .const 32#64]]) with _ | va
        · rw [ha] at hev_r; simp at hev_r
        · rw [ha] at hev_r
          cases va with
          | rStruct _ => simp at hev_r
          | nStruct _ => simp at hev_r
          | val wl =>
            cases wl with
            | word a =>
              dsimp only at hev_r
              have hone : ∀ {b : BitVec 64} {v1 : ValueHOL 64},
                  @memLoadHOLExact 64 _ .one b st.memaddrs (fun x => Classical.propDecidable (st.memaddrs x))
                    st.memory st.structs = some v1 → shapeEqHOL .one (shapeOfHOLExact v1) = true := by
                intro b v1 h1
                unfold memLoadHOLExact at h1
                split_ifs at h1
                simp only [Option.some.injEq] at h1
                subst h1
                simp [shapeOfHOLExact, shapeEqHOL]
              unfold memLoadHOLExact at hev_r
              rcases hm0 : @memLoadsHOLExact 64 _ [.one, .one, .one, .one] a st.memaddrs
                  (fun x => Classical.propDecidable (st.memaddrs x)) st.memory st.structs with _ | vs0
              · rw [hm0] at hev_r; simp at hev_r
              · rw [hm0] at hev_r
                simp only [Option.some.injEq] at hev_r
                subst hev_r
                unfold memLoadsHOLExact at hm0
                rcases hl1 : @memLoadHOLExact 64 _ .one a st.memaddrs
                    (fun x => Classical.propDecidable (st.memaddrs x)) st.memory st.structs with _ | v1
                · rw [hl1] at hm0; simp at hm0
                · rw [hl1] at hm0
                  rcases hm1 : @memLoadsHOLExact 64 _ [.one, .one, .one] _ st.memaddrs
                      (fun x => Classical.propDecidable (st.memaddrs x)) st.memory st.structs with _ | vs1
                  · rw [hm1] at hm0; simp at hm0
                  · rw [hm1] at hm0
                    simp only [Option.some.injEq] at hm0
                    subst hm0
                    unfold memLoadsHOLExact at hm1
                    rcases hl2 : @memLoadHOLExact 64 _ .one _ st.memaddrs
                        (fun x => Classical.propDecidable (st.memaddrs x)) st.memory st.structs with _ | v2
                    · rw [hl2] at hm1; simp at hm1
                    · rw [hl2] at hm1
                      rcases hm2 : @memLoadsHOLExact 64 _ [.one, .one] _ st.memaddrs
                          (fun x => Classical.propDecidable (st.memaddrs x)) st.memory st.structs with _ | vs2
                      · rw [hm2] at hm1; simp at hm1
                      · rw [hm2] at hm1
                        simp only [Option.some.injEq] at hm1
                        subst hm1
                        unfold memLoadsHOLExact at hm2
                        rcases hl3 : @memLoadHOLExact 64 _ .one _ st.memaddrs
                            (fun x => Classical.propDecidable (st.memaddrs x)) st.memory st.structs with _ | v3
                        · rw [hl3] at hm2; simp at hm2
                        · rw [hl3] at hm2
                          rcases hm3 : @memLoadsHOLExact 64 _ [.one] _ st.memaddrs
                              (fun x => Classical.propDecidable (st.memaddrs x)) st.memory st.structs with _ | vs3
                          · rw [hm3] at hm2; simp at hm2
                          · rw [hm3] at hm2
                            simp only [Option.some.injEq] at hm2
                            subst hm2
                            unfold memLoadsHOLExact at hm3
                            rcases hl4 : @memLoadHOLExact 64 _ .one _ st.memaddrs
                                (fun x => Classical.propDecidable (st.memaddrs x)) st.memory st.structs with _ | v4
                            · rw [hl4] at hm3; simp at hm3
                            · rw [hl4] at hm3
                              rcases hm4 : @memLoadsHOLExact 64 _ [] _ st.memaddrs
                                  (fun x => Classical.propDecidable (st.memaddrs x)) st.memory st.structs with _ | vs4
                              · rw [hm4] at hm3; simp at hm3
                              · rw [hm4] at hm3
                                simp only [Option.some.injEq] at hm3
                                subst hm3
                                unfold memLoadsHOLExact at hm4
                                simp only [Option.some.injEq] at hm4
                                subst hm4
                                simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL,
                                  hone hl1, hone hl2, hone hl3, hone hl4]
      · simp at hret
  have hmem_ne16 :
      shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact v) = true ∧
      ∀ x : BitVec 64, x ≠ BitVec.ofNat 64 (globN s "ev" + 16) →
        (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_stack_pop)).2.memory x = s.memory x := by
    revert hv
    rw [hb, evaluateHOLFiniteState_dec_total]; dsimp only
    split
    · simp
    · rename_i vsp _
      split
      · dsimp only
        set s1 := setVarHOLFinite (ofString "sp") vsp s
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
        split
        · split
          · simp only [evaluateHOLFiniteState_skip]
            rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
            split
            · simp
            · rename_i sp1 hsp1
              have hsp1_w : ∃ w : BitVec 64, sp1 = .val (.word w) := by
                simp only [evalHOLExact, wordOpHOL] at hsp1; revert hsp1
                rcases @evalListHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a)) _ with _ | vs
                · simp
                · dsimp only; split
                  · simp only [Option.map]
                    rcases wordOp .sub (vs.map valueWord) with _ | w
                    · simp
                    · intro h'; injection h' with h''; exact ⟨w, h''.symm⟩
                  · simp
              obtain ⟨spw, rfl⟩ := hsp1_w
              split
              · dsimp only
                set s2 := setKvarHOLFinite .local (ofString "sp") (.val (.word spw)) s1
                rw [evaluateHOLFiniteState_seq_line780]
                rcases hst : evaluateHOLFiniteState s2
                    (.store (.op .add [.var .global (ofString "ev"), .const 16]) (.var .local (ofString "sp"))) with ⟨r2, s3⟩
                cases r2 with
                | some res2 =>
                  have herr := store_some_eq_error_g08 hst; subst herr; simp
                | none =>
                  dsimp only
                  obtain ⟨w2, _, hs3_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s2) (post := s3)
                    (gname := "ev") (gbase := globN s "ev") (off := 16) hevw hevw_nat (by omega)
                    (fun u hu => by
                      have hsp2 : s2.locals.lookup (ofString "sp") = some (.val (.word spw)) := by
                        simp [s2, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                      change s2.locals.lookup (ofString "sp") = some u at hu
                      rw [hsp2] at hu; injection hu with hu'; exact ⟨spw, hu'.symm⟩) hst
                  intro hret_s3
                  refine ⟨hret_load_shape s3 v hret_s3, fun x hx => ?_⟩
                  rw [evaluateHOLFiniteState_return]
                  split
                  · dsimp only; rw [hs3_eq]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hx]; rfl
                  · split
                    · dsimp only [emptyLocalsHOLFinite]; rw [hs3_eq]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hx]; rfl
                    · dsimp only; rw [hs3_eq]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hx]; rfl
              · simp
          · rcases hraise : evaluateHOLFiniteState s1 (.raise (ofString "EvmErr") (.const 2)) with ⟨rr, sr⟩
            have hr_nn : rr ≠ none ∧ ∀ vr, rr ≠ some (.returned vr) := by
              rw [evaluateHOLFiniteState_raise] at hraise; dsimp only [evalHOLExact] at hraise
              split at hraise
              · split at hraise <;> (injection hraise with h1 _; subst h1; exact ⟨by simp, by simp⟩)
              · injection hraise with h1 _; subst h1; exact ⟨by simp, by simp⟩
            cases rr with
            | none => exact absurd rfl hr_nn.1
            | some r0 =>
              dsimp only
              intro hres
              injection hres with hr0
              subst hr0
              exact absurd rfl (hr_nn.2 v)
        · simp
      · simp
  refine ⟨hInv_p, hch_p, hR_p, hglob_p, hmem_ne16.1, ?_⟩
  intro hHM
  refine headMemAligned_congr_head_only hglob_p (fun off hoff => ?_) hHM
  have hne_bv : BitVec.ofNat 64 (globN s "ev" + off) ≠ BitVec.ofNat 64 (globN s "ev" + 16) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    intro heq
    have htn := congrArg BitVec.toNat heq
    rcases hoff with rfl | rfl | rfl <;>
      (rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at htn; omega)
  unfold memW; rw [hmem_ne16.2 _ hne_bv]

private def CalleeBodyRun {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (P : PanSemStateFiniteExact 64 F → Prop) (charged : Bool)
    (prog : ProgHOL 64) : Prop :=
  ∀ (t : PanSemStateFiniteExact 64 F),
    t.code = originalRuntimeCode →
    EvmInv t →
    (evmChain t).length = (evmChain s0).length →
    (if charged then evmR t < evmR s0 else evmR t ≤ evmR s0) →
    P t →
    (evaluateHOLFiniteState t prog).1 ≠ some .timeOut →
    let out := evaluateHOLFiniteState t prog
    ((∃ v, out.1 = some (.returned v)) →
      EvmInv out.2 ∧ (evmChain out.2).length = (evmChain s0).length ∧ evmR out.2 < evmR s0) ∧
    (IsEvmErr out.1 →
      EvmInv out.2 ∧ (evmChain out.2).length = (evmChain s0).length ∧ evmR out.2 ≤ evmR s0) ∧
    (∀ r0, out.1 = some r0 →
      (∀ v, r0 ≠ .returned v) → ¬ IsEvmErr out.1 →
      ∀ v', out.1 ≠ some (.returned v'))

private theorem calleeBodyRun_congr_lc {F : Type}
    {s0 post post' : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)}
    (hp_lc : post' = { post with locals := post'.locals, clock := post'.clock })
    (h : ((∃ v, r = some (.returned v)) →
           EvmInv post ∧ (evmChain post).length = (evmChain s0).length ∧ evmR post < evmR s0) ∧
         (IsEvmErr r →
           EvmInv post ∧ (evmChain post).length = (evmChain s0).length ∧ evmR post ≤ evmR s0)) :
    ((∃ v, r = some (.returned v)) →
      EvmInv post' ∧ (evmChain post').length = (evmChain s0).length ∧ evmR post' < evmR s0) ∧
    (IsEvmErr r →
      EvmInv post' ∧ (evmChain post').length = (evmChain s0).length ∧ evmR post' ≤ evmR s0) := by
  have hp_m : post'.memory = post.memory := by rw [hp_lc]
  have hp_g : post'.globals = post.globals := by rw [hp_lc]
  have hp := evm_congr hp_m hp_g
  have hinv : EvmInv post → EvmInv post' := fun h0 => by
    rw [hp_lc]; exact localsFree_evmInv post post'.locals post'.clock h0
  refine ⟨fun hret => ?_, fun herr => ?_⟩
  · obtain ⟨hi, hlen, hlt⟩ := h.1 hret
    exact ⟨hinv hi, by rw [hp.2.2.1]; exact hlen, by rw [hp.2.1]; exact hlt⟩
  · obtain ⟨hi, hlen, hR⟩ := h.2 herr
    exact ⟨hinv hi, by rw [hp.2.2.1]; exact hlen, by rw [hp.2.1]; exact hR⟩

private theorem calleeBodyRun_error {F : Type} (s0 t : PanSemStateFiniteExact 64 F) :
    (((∃ v, (some PanSemResultExact.error : Option (PanSemResultExact 64)) = some (.returned v)) →
      EvmInv t ∧ (evmChain t).length = (evmChain s0).length ∧ evmR t < evmR s0) ∧
     (IsEvmErr (some PanSemResultExact.error) →
      EvmInv t ∧ (evmChain t).length = (evmChain s0).length ∧ evmR t ≤ evmR s0) ∧
     (∀ r0, (some PanSemResultExact.error : Option (PanSemResultExact 64)) = some r0 →
      (∀ v, r0 ≠ .returned v) → ¬ IsEvmErr (some PanSemResultExact.error) →
      ∀ v', (some PanSemResultExact.error : Option (PanSemResultExact 64)) ≠ some (.returned v'))) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, h⟩; cases h
  · rintro ⟨_, h⟩; cases h
  · intro _ _ _ _ _ h; cases h

private theorem calleeBodyRun_other {F : Type} {s0 t : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)}
    (hnret : ∀ v, r ≠ some (.returned v)) (hnerr : ¬ IsEvmErr r) :
    (((∃ v, r = some (.returned v)) →
      EvmInv t ∧ (evmChain t).length = (evmChain s0).length ∧ evmR t < evmR s0) ∧
     (IsEvmErr r →
      EvmInv t ∧ (evmChain t).length = (evmChain s0).length ∧ evmR t ≤ evmR s0) ∧
     (∀ r0, r = some r0 → (∀ v, r0 ≠ .returned v) → ¬ IsEvmErr r → ∀ v', r ≠ some (.returned v'))) :=
  ⟨fun ⟨v, hv⟩ => (hnret v hv).elim, fun he => (hnerr he).elim, fun _ _ _ _ v' => hnret v'⟩

private theorem CalleeBodyRun.ret {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} (e : ExpHOL 64) :
    CalleeBodyRun s0 P true (.return e) := by
  intro t _ hInv hlen hR _ _
  simp only [↓reduceIte] at hR
  dsimp only
  rw [evaluateHOLFiniteState_return]
  split
  · exact calleeBodyRun_error s0 t
  · split
    · have hInv' : EvmInv (emptyLocalsHOLFinite t) :=
        localsFree_evmInv t (emptyLocalsHOLFinite t).locals t.clock hInv
      have hc := evm_congr (s := t) (t := emptyLocalsHOLFinite t) rfl rfl
      refine ⟨fun _ => ⟨hInv', by rw [hc.2.2.1]; exact hlen, by rw [hc.2.1]; exact hR⟩, ?_, ?_⟩
      · rintro ⟨_, h⟩; cases h
      · intro r0 hr hnr _ _
        injection hr with hr'
        subst hr'
        exact (hnr _ rfl).elim
    · exact calleeBodyRun_error s0 t

private theorem CalleeBodyRun.decCall {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop}
    {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    {charged : Bool}
    {nm : MlS} {sh : ShapeHOL} {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hf : EvmPreservingSpec Pc Qc fname)
    (hentry : ∀ t values body' callee ret',
      t.code = originalRuntimeCode → EvmInv t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite t.code.lookup fname values = some (body', callee, ret') →
      Pc (callEntryStateHOLFinite t callee))
    (hstep : ∀ t values body callee retShape v cpost,
      EvmInv t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, callee, retShape) →
      EvmInv cpost → evmChain cpost = evmChain (callEntryStateHOLFinite t callee) →
      Qc (callEntryStateHOLFinite t callee) v cpost →
      Q (setVarHOLFinite nm v { cpost with locals := t.locals }))
    (hcont : CalleeBodyRun s0 Q charged cont) :
    CalleeBodyRun s0 P charged (.decCall nm sh fname args cont) := by
  intro t hc hInv hlen hR hP hnt
  obtain ⟨params, body, retShape, hlook, hspec⟩ := hf
  dsimp only
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args with _ | values
  · exact calleeBodyRun_error s0 t
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact calleeBodyRun_error s0 t
    · simp only [hl] at hnt ⊢
      by_cases hz : t.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
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
        have hInv_ce : EvmInv (callEntryStateHOLFinite t callee) := localsFree_evmInv t callee (t.clock - 1) hInv
        have hPc : Pc (callEntryStateHOLFinite t callee) := hentry t values body callee retShape hc hInv hP hargs hl
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
            some (body, callee, retShape) := by rwa [← hc]
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite t callee) body).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body with ⟨res, cpost⟩
        simp only [hrun] at hnt hmeta ⊢
        change cpost.code = t.code at hmeta
        have hc_ce := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
        have hQ (hsafe : res ≠ some .timeOut) :
            (∀ v, res = some (.returned v) →
              EvmInv cpost ∧ evmChain cpost = evmChain (callEntryStateHOLFinite t callee) ∧
              evmR cpost ≤ evmR (callEntryStateHOLFinite t callee) ∧
              Qc (callEntryStateHOLFinite t callee) v cpost) ∧
            (IsEvmErr res →
              EvmInv cpost ∧ evmChain cpost = evmChain (callEntryStateHOLFinite t callee) ∧
              evmR cpost ≤ evmR (callEntryStateHOLFinite t callee)) := by
          have hs := hspec (callEntryStateHOLFinite t callee) hc hInv_ce hPc ⟨values, hl_orig⟩
            (by rw [hrun]; exact hsafe)
          dsimp only at hs; rw [hrun] at hs; exact hs
        cases res with
        | none => exact calleeBodyRun_error s0 cpost
        | some r0 =>
          cases r0 with
          | timeOut => simp at hnt
          | returned v =>
            dsimp only at hnt ⊢
            split
            · rename_i hsh_ok
              rw [if_pos hsh_ok] at hnt
              obtain ⟨hInv_cp, hch_cp, hR_cp, hQc_cp⟩ := (hQ (by simp)).1 v rfl
              let resumed := setVarHOLFinite nm v { cpost with locals := t.locals }
              have hcode_res : resumed.code = originalRuntimeCode := hmeta.trans hc
              have hInv_res : EvmInv resumed := localsFree_evmInv cpost resumed.locals cpost.clock hInv_cp
              have hc_res := evm_congr (s := cpost) (t := resumed) rfl rfl
              have hlen_res : (evmChain resumed).length = (evmChain s0).length := by
                rw [hc_res.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              have hR_res : if charged then evmR resumed < evmR s0 else evmR resumed ≤ evmR s0 := by
                cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at hR ⊢ <;>
                  (rw [hc_res.2.1]; rw [hc_ce.2.1] at hR_cp; omega)
              have hQ_res : Q resumed := hstep t values body callee retShape v cpost hInv hP hargs hl_orig hInv_cp hch_cp hQc_cp
              have hb := hcont resumed hcode_res hInv_res hlen_res hR_res hQ_res (by simpa [resumed] using hnt)
              dsimp only at hb
              refine ⟨?_, ?_, fun r1 hr1 hnr1 hnerr1 v' => hb.2.2 r1 hr1 hnr1 hnerr1 v'⟩
              · exact (calleeBodyRun_congr_lc rfl ⟨hb.1, hb.2.1⟩).1
              · exact (calleeBodyRun_congr_lc rfl ⟨hb.1, hb.2.1⟩).2
            · exact calleeBodyRun_error s0 cpost
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨hInv_cp, hch_cp, hR_cp⟩ := (hQ (by simp)).2 ⟨ev, rfl⟩
              have hInv_el : EvmInv cpost.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost _ cpost.clock hInv_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              have hR_le : evmR t ≤ evmR s0 := by
                cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at hR <;> omega
              refine ⟨?_, fun _ => ⟨hInv_el, ?_, ?_⟩, ?_⟩
              · rintro ⟨_, h⟩; cases h
              · rw [hc_el.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              · rw [hc_el.2.1]; rw [hc_ce.2.1] at hR_cp; omega
              · intro _ _ _ _ _ h; cases h
            · refine calleeBodyRun_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => exact calleeBodyRun_error s0 cpost
          | «continue» => exact calleeBodyRun_error s0 cpost
          | finalFfi f =>
            refine calleeBodyRun_other (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => exact calleeBodyRun_error s0 cpost.emptyLocalsHOLFinite

private theorem CalleeBodyRun.seq_call {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop}
    {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    {charged : Bool}
    {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hf : EvmPreservingSpec Pc Qc fname)
    (hentry : ∀ t values body' callee ret',
      t.code = originalRuntimeCode → EvmInv t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite t.code.lookup fname values = some (body', callee, ret') →
      Pc (callEntryStateHOLFinite t callee))
    (hstep : ∀ t values body callee retShape v cpost,
      EvmInv t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, callee, retShape) →
      EvmInv cpost → evmChain cpost = evmChain (callEntryStateHOLFinite t callee) →
      Qc (callEntryStateHOLFinite t callee) v cpost →
      Q { cpost with locals := t.locals })
    (hcont : CalleeBodyRun s0 Q charged cont) :
    CalleeBodyRun s0 P charged (.seq (.call (some (none, none)) fname args) cont) := by
  intro t hc hInv hlen hR hP hnt
  obtain ⟨params, body, retShape, hlook, hspec⟩ := hf
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args with _ | values
  · exact calleeBodyRun_error s0 t
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact calleeBodyRun_error s0 t
    · simp only [hl] at hnt ⊢
      by_cases hz : t.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
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
        have hInv_ce : EvmInv (callEntryStateHOLFinite t callee) := localsFree_evmInv t callee (t.clock - 1) hInv
        have hPc : Pc (callEntryStateHOLFinite t callee) := hentry t values body callee retShape hc hInv hP hargs hl
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
            some (body, callee, retShape) := by rwa [← hc]
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite t callee) body).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body with ⟨res, cpost⟩
        simp only [hrun] at hnt hmeta ⊢
        change cpost.code = t.code at hmeta
        have hc_ce := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
        have hQ (hsafe : res ≠ some .timeOut) :
            (∀ v, res = some (.returned v) →
              EvmInv cpost ∧ evmChain cpost = evmChain (callEntryStateHOLFinite t callee) ∧
              evmR cpost ≤ evmR (callEntryStateHOLFinite t callee) ∧
              Qc (callEntryStateHOLFinite t callee) v cpost) ∧
            (IsEvmErr res →
              EvmInv cpost ∧ evmChain cpost = evmChain (callEntryStateHOLFinite t callee) ∧
              evmR cpost ≤ evmR (callEntryStateHOLFinite t callee)) := by
          have hs := hspec (callEntryStateHOLFinite t callee) hc hInv_ce hPc ⟨values, hl_orig⟩
            (by rw [hrun]; exact hsafe)
          dsimp only at hs; rw [hrun] at hs; exact hs
        cases res with
        | none => exact calleeBodyRun_error s0 cpost
        | some r0 =>
          cases r0 with
          | timeOut => simp at hnt
          | returned v =>
            by_cases hsh_ok : shapeEqHOL (shapeOfHOLExact v) retShape = true
            · simp only [hsh_ok, ↓reduceIte] at hnt ⊢
              obtain ⟨hInv_cp, hch_cp, hR_cp, hQc_cp⟩ := (hQ (by simp)).1 v rfl
              let resumed : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
              have hcode_res : resumed.code = originalRuntimeCode := hmeta.trans hc
              have hInv_res : EvmInv resumed := localsFree_evmInv cpost t.locals cpost.clock hInv_cp
              have hc_res := evm_congr (s := cpost) (t := resumed) rfl rfl
              have hlen_res : (evmChain resumed).length = (evmChain s0).length := by
                rw [hc_res.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              have hR_res : if charged then evmR resumed < evmR s0 else evmR resumed ≤ evmR s0 := by
                cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at hR ⊢ <;>
                  (rw [hc_res.2.1]; rw [hc_ce.2.1] at hR_cp; omega)
              have hQ_res : Q resumed := hstep t values body callee retShape v cpost hInv hP hargs hl_orig hInv_cp hch_cp hQc_cp
              exact hcont resumed hcode_res hInv_res hlen_res hR_res hQ_res (by simpa [resumed] using hnt)
            · simp only [hsh_ok, Bool.false_eq_true, ↓reduceIte]
              exact calleeBodyRun_error s0 cpost
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨hInv_cp, hch_cp, hR_cp⟩ := (hQ (by simp)).2 ⟨ev, rfl⟩
              have hInv_el : EvmInv cpost.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost _ cpost.clock hInv_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              have hR_le : evmR t ≤ evmR s0 := by
                cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at hR <;> omega
              refine ⟨?_, fun _ => ⟨hInv_el, ?_, ?_⟩, ?_⟩
              · rintro ⟨_, h⟩; cases h
              · rw [hc_el.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              · rw [hc_el.2.1]; rw [hc_ce.2.1] at hR_cp; omega
              · intro _ _ _ _ _ h; cases h
            · refine calleeBodyRun_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => exact calleeBodyRun_error s0 cpost
          | «continue» => exact calleeBodyRun_error s0 cpost
          | finalFfi f =>
            refine calleeBodyRun_other (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => exact calleeBodyRun_error s0 cpost.emptyLocalsHOLFinite

private theorem CalleeBodyRun.seq_charge_gas_preserves_headMem {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {amtExp : ExpHOL 64} {cont : ProgHOL 64}
    (hpos : ∀ t (w : BitVec 64),
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp =
        some (.val (.word w)) →
      EvmInv t → P t → 0 < w.toNat)
    (hstep : ∀ t cpost,
      EvmInv t → P t → EvmInv cpost → cpost.globals = t.globals →
      evmChain cpost = evmChain t →
      (∀ off : Nat, off ∈ ([24, 32, 40] : List Nat) →
        memW cpost (globN t "ev" + off) = memW t (globN t "ev" + off)) →
      Q { cpost with locals := t.locals })
    (hcont : CalleeBodyRun s0 Q true cont) :
    CalleeBodyRun s0 P charged (.seq (.call (some (none, none)) (ofString "charge_gas") [amtExp]) cont) := by
  intro t hc hInv hlen hR hP hnt
  have hR_le : evmR t ≤ evmR s0 := by
    cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at hR <;> omega
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) [amtExp] with _ | values
  · exact calleeBodyRun_error s0 t
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup (ofString "charge_gas") values with _ | ⟨body', callee, ret'⟩
    · exact calleeBodyRun_error s0 t
    · simp only [hl] at hnt ⊢
      by_cases hz : t.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hv_list : ∃ v0, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp = some v0 ∧ values = [v0] := by
          rw [evalListHOLFinite_eq_toExact] at hargs
          simp only [evalListHOLExact] at hargs
          rcases he : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp with _ | v0
          · simp [he] at hargs
          · simp only [he, Option.some.injEq] at hargs; exact ⟨v0, rfl, hargs.symm⟩
        obtain ⟨v0, hv0_ev, rfl⟩ := hv_list
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "charge_gas") [v0] =
            some (body', callee, ret') := by rwa [← hc]
        obtain ⟨rfl, rfl, amtw, rfl, hamt_cal⟩ := one_word_arg_lookup M21.lookup_charge_gas hl_orig
        have hamt_pos : 0 < amtw.toNat := hpos t amtw hv0_ev hInv hP
        have hInv_ce : EvmInv (callEntryStateHOLFinite t callee) := localsFree_evmInv t callee (t.clock - 1) hInv
        have hc_ce := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
          (callEntryStateHOLFinite t callee) (sourceFnBody Guest.Software.guestFn_charge_gas)).1
        have hcg := charge_gas_body_exact (callEntryStateHOLFinite t callee) hInv_ce hamt_cal
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee)
            (sourceFnBody Guest.Software.guestFn_charge_gas) with ⟨res, cpost⟩
        simp only [hrun] at hnt hmeta hcg ⊢
        let ce := callEntryStateHOLFinite t callee
        change cpost.code = t.code at hmeta
        cases res with
        | none => exact calleeBodyRun_error s0 cpost
        | some r0 =>
          cases r0 with
          | timeOut => simp at hnt
          | returned v =>
            by_cases hsh_ok : shapeEqHOL (shapeOfHOLExact v) .one = true
            · simp only [hsh_ok, ↓reduceIte] at hnt ⊢
              obtain ⟨hInv_cp, hglob_cp, hch_cp, hR_cp⟩ := hcg.1 v rfl
              have hmem_head_cp : ∀ off : Nat, off ∈ ([24, 32, 40] : List Nat) →
                  memW cpost (globN t "ev" + off) = memW t (globN t "ev" + off) := by
                intro off hoff
                have hhead_mem : (globN t "ev", globN t "cur_cont") ∈ evmChain t := by simp [evmChain, evmChainFrom]
                have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead_mem
                have hb_ev := (frameWF_bounds hInv.1.2 hFW0).1
                dsimp only at hb_ev
                have hev_pos : 0 < globN t "ev" := by
                  obtain ⟨hin, _⟩ := (hFW0.1 (globN t "ev", 280) (by simp)).1
                  have h1 := hInv.1.2.2.2.1; have h2 := hInv.1.2.2.2.2.1
                  rw [R11Shards.scratchStart_val] at h1; dsimp only at hin; omega
                obtain ⟨evw, hevw, hevw_nat⟩ := global_word_of_pos t "ev" hev_pos
                have hevw_ce : ce.globals.lookup (ofString "ev") = some (.val (.word evw)) := hevw
                have hbody_cg : sourceFnBody Guest.Software.guestFn_charge_gas =
                    .dec (ofString "gl") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 64]))
                      (.seq
                        (.ite (.cmp .lower (.var .local (ofString "gl")) (.var .local (ofString "amount")))
                          (.raise (ofString "EvmErr") (.const 4))
                          .skip)
                        (.seq
                          (.store (.op .add [.var .global (ofString "ev"), .const 64])
                            (.op .sub [.var .local (ofString "gl"), .var .local (ofString "amount")]))
                          (.seq
                            (.store (.op .add [.var .global (ofString "ev"), .const 184])
                              (.op .add
                                [.load .one (.op .add [.var .global (ofString "ev"), .const 184]),
                                 .var .local (ofString "amount")]))
                            (.return (.const 0))))) := rfl
                have hmem_ne : ∀ x : BitVec 64,
                    x ≠ BitVec.ofNat 64 (globN t "ev" + 64) →
                    x ≠ BitVec.ofNat 64 (globN t "ev" + 184) →
                    cpost.memory x = t.memory x := by
                  have hrun' := hrun
                  rw [hbody_cg, evaluateHOLFiniteState_dec_total] at hrun'; dsimp only at hrun'
                  split at hrun'
                  · simp at hrun'
                  · rename_i glv _
                    split at hrun'
                    · set s1 := setVarHOLFinite (ofString "gl") glv ce
                      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hrun'
                      split at hrun'
                      · split at hrun'
                        · simp only [evaluateHOLFiniteState_skip] at hrun'
                          rw [evaluateHOLFiniteState_seq_line780] at hrun'
                          rcases hst1 : evaluateHOLFiniteState s1
                              (.store (.op .add [.var .global (ofString "ev"), .const 64])
                                (.op .sub [.var .local (ofString "gl"), .var .local (ofString "amount")])) with ⟨r1, s2⟩
                          rw [hst1] at hrun'
                          cases r1 with
                          | some res1 =>
                            have herr1 := store_some_eq_error_g08 hst1; subst herr1; simp at hrun'
                          | none =>
                            dsimp only at hrun'
                            obtain ⟨w1, _, hs2_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s1) (post := s2)
                              (gname := "ev") (gbase := globN t "ev") (off := 64) hevw_ce hevw_nat (by omega)
                              (fun u hu => by
                                simp only [evalHOLExact, wordOpHOL] at hu; revert hu
                                rcases @evalListHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a)) _ with _ | vs
                                · simp
                                · dsimp only; split
                                  · simp only [Option.map]
                                    rcases wordOp .sub (vs.map valueWord) with _ | w
                                    · simp
                                    · intro h'; injection h' with h''; exact ⟨w, h''.symm⟩
                                  · simp) hst1
                            rw [evaluateHOLFiniteState_seq_line780] at hrun'
                            rcases hst2 : evaluateHOLFiniteState s2
                                (.store (.op .add [.var .global (ofString "ev"), .const 184])
                                  (.op .add
                                    [.load .one (.op .add [.var .global (ofString "ev"), .const 184]),
                                     .var .local (ofString "amount")])) with ⟨r2, s3⟩
                            rw [hst2] at hrun'
                            cases r2 with
                            | some res2 =>
                              have herr2 := store_some_eq_error_g08 hst2; subst herr2; simp at hrun'
                            | none =>
                              dsimp only at hrun'
                              obtain ⟨w2, _, hs3_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s2) (post := s3)
                                (gname := "ev") (gbase := globN t "ev") (off := 184)
                                (by rw [hs2_eq]; exact hevw_ce) hevw_nat (by omega)
                                (fun u hu => by
                                  simp only [evalHOLExact, wordOpHOL] at hu; revert hu
                                  rcases @evalListHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a)) _ with _ | vs
                                  · simp
                                  · dsimp only; split
                                    · simp only [Option.map]
                                      rcases wordOp .add (vs.map valueWord) with _ | w
                                      · simp
                                      · intro h'; injection h' with h''; exact ⟨w, h''.symm⟩
                                    · simp) hst2
                              rw [evaluateHOLFiniteState_return] at hrun'; dsimp only [evalHOLExact] at hrun'
                              have hsz0 : sizeOfShapeWithContextHOL s3.structs
                                  (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
                                simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
                              rw [if_pos hsz0] at hrun'; dsimp only at hrun'
                              injection hrun' with _ hcpost_eq
                              subst hcpost_eq
                              intro x hx64 hx184
                              dsimp only [emptyLocalsHOLFinite]
                              rw [hs3_eq]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hx184]
                              rw [hs2_eq]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hx64]
                              rfl
                        · rcases hraise : evaluateHOLFiniteState s1 (.raise (ofString "EvmErr") (.const 4)) with ⟨rr, sr⟩
                          rw [hraise] at hrun'
                          have hr_nn : rr ≠ none := by
                            rw [evaluateHOLFiniteState_raise] at hraise; dsimp only [evalHOLExact] at hraise
                            split at hraise
                            · split at hraise <;> (injection hraise with h1 _; subst h1; simp)
                            · injection hraise with h1 _; subst h1; simp
                          cases rr with
                          | none => exact absurd rfl hr_nn
                          | some r0 =>
                            dsimp only at hrun'
                            have hr_not_ret : ∀ vr, r0 ≠ .returned vr := by
                              rw [evaluateHOLFiniteState_raise] at hraise; dsimp only [evalHOLExact] at hraise
                              split at hraise
                              · split at hraise <;> (injection hraise with h1 _; injection h1 with h1'; subst h1'; simp)
                              · injection hraise with h1 _; injection h1 with h1'; subst h1'; simp
                            cases r0 with
                            | returned vr => exact absurd rfl (hr_not_ret vr)
                            | _ => simp at hrun'
                      · simp at hrun'
                    · simp at hrun'
                have hne64 : BitVec.ofNat 64 (globN t "ev" + off) ≠ BitVec.ofNat 64 (globN t "ev" + 64) := by
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
                  intro heq; have htn := congrArg BitVec.toNat heq
                  rcases hoff with rfl | rfl | rfl <;>
                    (rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at htn; omega)
                have hne184 : BitVec.ofNat 64 (globN t "ev" + off) ≠ BitVec.ofNat 64 (globN t "ev" + 184) := by
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
                  intro heq; have htn := congrArg BitVec.toNat heq
                  rcases hoff with rfl | rfl | rfl <;>
                    (rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at htn; omega)
                unfold memW; rw [hmem_ne _ hne64 hne184]
              let resumed : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
              have hInv_res : EvmInv resumed := localsFree_evmInv cpost t.locals cpost.clock hInv_cp
              have hc_res := evm_congr (s := cpost) (t := resumed) rfl rfl
              have hlen_res : (evmChain resumed).length = (evmChain s0).length := by
                rw [hc_res.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              have hR_lt : evmR resumed < evmR s0 := by
                rw [hc_res.2.1]; rw [hc_ce.2.1] at hR_cp; omega
              exact hcont resumed (hmeta.trans hc) hInv_res hlen_res (by simp [hR_lt])
                (hstep t cpost hInv hP hInv_cp hglob_cp (hch_cp.trans (evmChain_congr rfl rfl)) hmem_head_cp)
                (by simpa [resumed] using hnt)
            · simp only [hsh_ok, Bool.false_eq_true, ↓reduceIte]
              exact calleeBodyRun_error s0 cpost
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨hInv_cp, _, hch_cp, hR_cp⟩ := hcg.2 ⟨ev, rfl⟩
              have hInv_el : EvmInv cpost.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost _ cpost.clock hInv_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              refine ⟨?_, fun _ => ⟨hInv_el, ?_, ?_⟩, ?_⟩
              · rintro ⟨_, h⟩; cases h
              · rw [hc_el.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              · rw [hc_el.2.1, hR_cp, hc_ce.2.1]; exact hR_le
              · intro _ _ _ _ _ h; cases h
            · refine calleeBodyRun_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => exact calleeBodyRun_error s0 cpost
          | «continue» => exact calleeBodyRun_error s0 cpost
          | finalFfi f =>
            refine calleeBodyRun_other (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => exact calleeBodyRun_error s0 cpost.emptyLocalsHOLFinite

private theorem seq_call_strict {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop}
    {Pc : PanSemStateFiniteExact 64 F → Prop}
    {charged : Bool}
    {fname : MlS} {params : List (MlS × ShapeHOL)} {body : ProgHOL 64}
    {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hlook : originalRuntimeCode.lookup fname = some (params, body, .one))
    (hentry : ∀ t values callee,
      t.code = originalRuntimeCode → EvmInv t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, callee, .one) →
      Pc (callEntryStateHOLFinite t callee))
    (hbody : CalleeBodyRun s0 Pc charged body)
    (hcont : HandlerRun s0 (fun _ => True) true cont) :
    HandlerRun s0 P charged (.seq (.call (some (none, none)) fname args) cont) := by
  intro t hc hInv hlen hR hP hnt
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args with _ | values
  · exact opDispatchPost_error s0 t
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact opDispatchPost_error s0 t
    · simp only [hl] at hnt ⊢
      by_cases hz : t.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hbody_eq : body' = body :=
          lookupCodeHOLFinite_installed_body t.code.lookup fname params body body'
            .one ret' values callee (by rw [hc]; exact hlook) hl
        subst body'
        have hret_eq : ret' = .one := by
          have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
            t.code.lookup fname values body callee ret' hl
          rw [hc] at hx; simp only [Flapjack.lookupCodeHOLExact, hlook] at hx
          split at hx
          · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
          · cases hx
        subst ret'
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
            some (body, callee, .one) := by rwa [← hc]
        have hInv_ce : EvmInv (callEntryStateHOLFinite t callee) := localsFree_evmInv t callee (t.clock - 1) hInv
        have hc_ce := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
        have hPc : Pc (callEntryStateHOLFinite t callee) := hentry t values callee hc hInv hP hargs hl_orig
        have hlen_ce : (evmChain (callEntryStateHOLFinite t callee)).length = (evmChain s0).length := hc_ce.2.2.1.trans hlen
        have hR_ce : if charged then evmR (callEntryStateHOLFinite t callee) < evmR s0 else evmR (callEntryStateHOLFinite t callee) ≤ evmR s0 := by
          rw [hc_ce.2.1]; exact hR
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite t callee) body).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body with ⟨res, cpost⟩
        simp only [hrun] at hnt hmeta ⊢
        change cpost.code = t.code at hmeta
        have hB (hsafe : res ≠ some .timeOut) :
            ((∃ v, res = some (.returned v)) →
              EvmInv cpost ∧ (evmChain cpost).length = (evmChain s0).length ∧ evmR cpost < evmR s0) ∧
            (IsEvmErr res →
              EvmInv cpost ∧ (evmChain cpost).length = (evmChain s0).length ∧ evmR cpost ≤ evmR s0) := by
          have hs := hbody (callEntryStateHOLFinite t callee) hc hInv_ce hlen_ce hR_ce hPc (by rw [hrun]; exact hsafe)
          dsimp only at hs; rw [hrun] at hs; exact ⟨hs.1, hs.2.1⟩
        cases res with
        | none => exact opDispatchPost_error s0 cpost
        | some r0 =>
          cases r0 with
          | timeOut => simp at hnt
          | returned v =>
            by_cases hsh_ok : shapeEqHOL (shapeOfHOLExact v) .one = true
            · simp only [hsh_ok, ↓reduceIte] at hnt ⊢
              obtain ⟨hInv_cp, hlen_cp, hR_cp⟩ := (hB (by simp)).1 ⟨v, rfl⟩
              let resumed : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
              have hInv_res : EvmInv resumed := localsFree_evmInv cpost t.locals cpost.clock hInv_cp
              have hc_res := evm_congr (s := cpost) (t := resumed) rfl rfl
              exact hcont resumed (hmeta.trans hc) hInv_res
                (by rw [hc_res.2.2.1]; exact hlen_cp)
                (by simp only [↓reduceIte, hc_res.2.1]; exact hR_cp)
                trivial
                (by simpa [resumed] using hnt)
            · simp only [hsh_ok, Bool.false_eq_true, ↓reduceIte]
              exact opDispatchPost_error s0 cpost
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨hInv_cp, hlen_cp, hR_cp⟩ := (hB (by simp)).2 ⟨ev, rfl⟩
              have hInv_el : EvmInv cpost.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost _ cpost.clock hInv_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              refine ⟨?_, fun _ => ⟨hInv_el, ?_, ?_⟩⟩
              · rintro ⟨_, h⟩; cases h
              · rw [hc_el.2.2.1]; exact hlen_cp
              · rw [hc_el.2.1]; exact hR_cp
            · refine opDispatchPost_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => exact opDispatchPost_error s0 cpost
          | «continue» => exact opDispatchPost_error s0 cpost
          | finalFfi f =>
              refine opDispatchPost_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; cases h
          | error => exact opDispatchPost_error s0 cpost.emptyLocalsHOLFinite

private theorem charge_with_memory_arg0_lookup {vals : List (ValueHOL 64)} {body' : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret' : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "charge_with_memory") vals =
      some (body', callee, ret')) :
    ∃ (basew : BitVec 64) (v2 v3 : ValueHOL 64),
      vals = [.val (.word basew), v2, v3] ∧
      callee.lookup (ofString "base") = some (.val (.word basew)) := by
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
    originalRuntimeCode.lookup (ofString "charge_with_memory") vals body' callee ret' hl
  simp only [Flapjack.lookupCodeHOLExact, lookup_charge_with_memory] at hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩
  · simp at hx
  · simp at hx
  · simp at hx
  · split at hx
    · rename_i hcond
      have heq := Option.some.inj hx
      rcases Prod.mk.inj heq with ⟨_, hrest⟩
      rcases Prod.mk.inj hrest with ⟨hloc, _⟩
      have hsh1 : shapeEqHOL .one (shapeOfHOLExact v1) = true := by
        have hs := hcond.2.2
        simp only [List.map, List.all_cons, Bool.and_eq_true, List.zip_cons_cons] at hs
        exact hs.1
      rcases v1 with ⟨⟨w1⟩⟩ | _ | _
      · refine ⟨w1, v2, v3, rfl, ?_⟩
        have hfn := congrFun hloc.symm (ofString "base")
        have hne_bs : ofString "base" ≠ ofString "start" := by decide
        have hne_bz : ofString "base" ≠ ofString "size" := by decide
        simpa [FUPDATE_LIST, FUPDATE, hne_bs, Ne.symm hne_bs, hne_bz, Ne.symm hne_bz] using hfn
      · simp [shapeOfHOLExact, shapeEqHOL] at hsh1
      · simp [shapeOfHOLExact, shapeEqHOL] at hsh1
    · cases hx
  · simp at hx

private theorem charge_with_memory_body_run_of_extend_memory {F : Type}
    (s0 : PanSemStateFiniteExact 64 F)
    {Qem : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h_extend_memory : EvmPreservingSpec
      (fun s => ∃ ebw : BitVec 64,
        s.locals.lookup (ofString "expand_by") = some (.val (.word ebw)) ∧
        ebw.toNat < 2 ^ 37)
      Qem
      (ofString "extend_memory")) :
    CalleeBodyRun s0
      (fun t => ∃ bw : BitVec 64, t.locals.lookup (ofString "base") = some (.val (.word bw)) ∧ 0 < bw.toNat)
      false
      (sourceFnBody Guest.Software.guestFn_charge_with_memory) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_charge_with_memory,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine CalleeBodyRun.decCall
    (Q := fun t =>
      (∃ bw : BitVec 64, t.locals.lookup (ofString "base") = some (.val (.word bw)) ∧ 0 < bw.toNat) ∧
      ∃ cw ebw : BitVec 64,
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        ebw.toNat < 2 ^ 37)
    eps_extend_memory_cost1_bounds
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ v _ _ ⟨bw, hbw, hpos⟩ _ _ _ _ hQc => by
      obtain ⟨_, cw, ebw, rfl, heb_bounds⟩ := hQc
      have hne_xb : ofString "x" ≠ ofString "base" := by decide
      refine ⟨⟨bw, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne_xb, Ne.symm hne_xb, hbw], hpos⟩,
              cw, ebw, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], ?_⟩
      rcases heb_bounds with rfl | ⟨before, after, haft_lt, _, _, heb_sub, _⟩
      · decide
      · omega)
    ?_
  refine CalleeBodyRun.decCall
    (Q := fun t =>
      (∃ totw : BitVec 64, t.locals.lookup (ofString "total") = some (.val (.word totw)) ∧ 0 < totw.toNat) ∧
      ∃ cw ebw : BitVec 64,
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        ebw.toNat < 2 ^ 37)
    eps_add_sat_pos
    (fun t values b_as callee rs_as hc _ ⟨⟨bw, hbw, hpos⟩, _⟩ hargs hl => by
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "add_sat") values =
          some (b_as, callee, rs_as) := by rwa [← hc]
      obtain ⟨_, _, w1, w2, rfl, hw1, _⟩ := two_word_arg_lookup (by decide) lookup_add_sat hl_orig
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact] at hargs
      have hb_ev : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.var .local (ofString "base")) = some (.val (.word bw)) := hbw
      rcases he2 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.rfield 0 (.var .local (ofString "x"))) with _ | u2
      · simp [hb_ev, he2] at hargs
      · simp only [hb_ev, he2, Option.some.injEq, List.cons.injEq] at hargs
        obtain ⟨hbw_eq, _⟩ := hargs
        injection hbw_eq with hbw1; injection hbw1 with hbw2; subst hbw2
        exact ⟨bw, hw1, hpos⟩)
    (fun _ _ _ _ _ v _ _ ⟨_, cw, ebw, hx, heb_lt⟩ _ _ _ _ hQc => by
      obtain ⟨_, totw, rfl, hpos⟩ := hQc
      have hne_tx : ofString "total" ≠ ofString "x" := by decide
      exact ⟨⟨totw, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], hpos⟩,
             cw, ebw, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne_tx, Ne.symm hne_tx, hx], heb_lt⟩)
    ?_
  refine CalleeBodyRun.seq_charge_gas_preserves_headMem
    (Q := fun t =>
      ∃ cw ebw : BitVec 64,
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        ebw.toNat < 2 ^ 37)
    (fun t w hw _ ⟨⟨totw, htot, hpos⟩, _⟩ => by
      change t.locals.lookup (ofString "total") = some (.val (.word w)) at hw
      rw [htot] at hw; injection hw with hw'; injection hw' with hw''; injection hw'' with hweq; subst hweq
      exact hpos)
    (fun _ _ _ ⟨_, hx⟩ _ _ _ _ => hx)
    ?_
  refine CalleeBodyRun.seq_call
    (Q := fun _ => True)
    h_extend_memory
    (fun t values b_em callee rs_em hc _ ⟨cw, ebw, hx, heb_lt⟩ hargs hl => by
      have hx1 : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.rfield 1 (.var .local (ofString "x"))] = some [.val (.word ebw)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hx]
      rw [hx1] at hargs; injection hargs with hvs; subst hvs
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "extend_memory") [.val (.word ebw)] =
          some (b_em, callee, rs_em) := by rwa [← hc]
      obtain ⟨_, _, ebw', heq_eb, hcal_eb⟩ := one_word_arg_lookup lookup_extend_memory hl_orig
      injection heq_eb with heq1; injection heq1 with heq2; subst heq2
      exact ⟨ebw, hcal_eb, heb_lt⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
    (CalleeBodyRun.ret _)

private theorem charge_with_memory_body_run_aligned {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) :
    CalleeBodyRun s0
      (fun t => HeadMemAligned t ∧
        ∃ bw : BitVec 64, t.locals.lookup (ofString "base") = some (.val (.word bw)) ∧ 0 < bw.toNat)
      false
      (sourceFnBody Guest.Software.guestFn_charge_with_memory) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_charge_with_memory,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine CalleeBodyRun.decCall
    (Q := fun t =>
      HeadMemAligned t ∧
      (∃ bw : BitVec 64, t.locals.lookup (ofString "base") = some (.val (.word bw)) ∧ 0 < bw.toNat) ∧
      ∃ cw ebw : BitVec 64,
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        (ebw = 0#64 ∨
          (memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
           (memW t (globN t "ev" + 32) + ebw.toNat) % 8 = 0 ∧
           memW t (globN t "ev" + 24) + memW t (globN t "ev" + 40) = globN t "frame_mem_ptr")))
    eps_extend_memory_cost1_bounds
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ callee _ v cpost _ ⟨hHM, bw, hbw, hpos⟩ _ _ _ _ hQc => by
      obtain ⟨hlf, cw, ebw, rfl, heb_bounds⟩ := hQc
      let ce := callEntryStateHOLFinite t callee
      have hHM_ce : HeadMemAligned ce := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      have hHM_cp : HeadMemAligned cpost :=
        headMemAligned_congr_head_only (by rw [hlf]) (fun off _ => by unfold memW; rw [hlf]) hHM_ce
      let res := setVarHOLFinite (ofString "x") (.rStruct [.val (.word cw), .val (.word ebw)]) { cpost with locals := t.locals }
      have hHM_res : HeadMemAligned res := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp
      have hne_xb : ofString "x" ≠ ofString "base" := by decide
      have hmem32_eq : memW res (globN res "ev" + 32) = memW ce (globN ce "ev" + 32) := by
        have hg : globN res "ev" = globN ce "ev" := globN_eq_of_lookup_eq (by change cpost.globals.lookup _ = ce.globals.lookup _; rw [hlf])
        have hm : res.memory = ce.memory := by change cpost.memory = ce.memory; rw [hlf]
        rw [hg]; unfold memW; rw [hm]
      refine ⟨hHM_res,
              ⟨bw, by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne_xb, Ne.symm hne_xb, hbw], hpos⟩,
              cw, ebw, by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], ?_⟩
      rcases heb_bounds with rfl | ⟨before, after, haft_lt, haft_mod, hbef_lt, heb_sub, hbef_eq⟩
      · exact Or.inl rfl
      · right
        have hbef : before = memW ce (globN ce "ev" + 32) := hbef_eq hHM_ce.1
        have hsum : memW res (globN res "ev" + 32) + ebw.toNat = after := by
          rw [hmem32_eq, ← hbef]; omega
        rw [hsum]
        exact ⟨haft_lt, by omega, hHM_res.2⟩)
    ?_
  refine CalleeBodyRun.decCall
    (Q := fun t =>
      HeadMemAligned t ∧
      (∃ totw : BitVec 64, t.locals.lookup (ofString "total") = some (.val (.word totw)) ∧ 0 < totw.toNat) ∧
      ∃ cw ebw : BitVec 64,
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        (ebw = 0#64 ∨
          (memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
           (memW t (globN t "ev" + 32) + ebw.toNat) % 8 = 0 ∧
           memW t (globN t "ev" + 24) + memW t (globN t "ev" + 40) = globN t "frame_mem_ptr")))
    eps_add_sat_pos
    (fun t values b_as callee rs_as hc _ ⟨_, ⟨bw, hbw, hpos⟩, _⟩ hargs hl => by
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "add_sat") values =
          some (b_as, callee, rs_as) := by rwa [← hc]
      obtain ⟨_, _, w1, w2, rfl, hw1, _⟩ := two_word_arg_lookup (by decide) lookup_add_sat hl_orig
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact] at hargs
      have hb_ev : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.var .local (ofString "base")) = some (.val (.word bw)) := hbw
      rcases he2 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.rfield 0 (.var .local (ofString "x"))) with _ | u2
      · simp [hb_ev, he2] at hargs
      · simp only [hb_ev, he2, Option.some.injEq, List.cons.injEq] at hargs
        obtain ⟨hbw_eq, _⟩ := hargs
        injection hbw_eq with hbw1; injection hbw1 with hbw2; subst hbw2
        exact ⟨bw, hw1, hpos⟩)
    (fun t _ _ callee _ v cpost _ ⟨hHM, _, cw, ebw, hx, heb_cond⟩ _ _ _ _ hQc => by
      obtain ⟨hlf, totw, rfl, hpos⟩ := hQc
      let ce := callEntryStateHOLFinite t callee
      have hHM_ce : HeadMemAligned ce := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      have hHM_cp : HeadMemAligned cpost :=
        headMemAligned_congr_head_only (by rw [hlf]) (fun off _ => by unfold memW; rw [hlf]) hHM_ce
      let res := setVarHOLFinite (ofString "total") (.val (.word totw)) { cpost with locals := t.locals }
      have hHM_res : HeadMemAligned res := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp
      have hne_tx : ofString "total" ≠ ofString "x" := by decide
      have hmem32_eq : memW res (globN res "ev" + 32) = memW t (globN t "ev" + 32) := by
        have hg : globN res "ev" = globN t "ev" := globN_eq_of_lookup_eq (by change cpost.globals.lookup _ = t.globals.lookup _; rw [hlf]; rfl)
        have hm : res.memory = t.memory := by change cpost.memory = t.memory; rw [hlf]; rfl
        rw [hg]; unfold memW; rw [hm]
      refine ⟨hHM_res,
              ⟨totw, by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], hpos⟩,
              cw, ebw, by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne_tx, Ne.symm hne_tx, hx], ?_⟩
      rcases heb_cond with rfl | ⟨hlt37, hmod8, _⟩
      · exact Or.inl rfl
      · right
        rw [hmem32_eq]
        exact ⟨hlt37, hmod8, hHM_res.2⟩)
    ?_
  refine CalleeBodyRun.seq_charge_gas_preserves_headMem
    (Q := fun t =>
      ∃ cw ebw : BitVec 64,
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        (ebw = 0#64 ∨
          (memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
           (memW t (globN t "ev" + 32) + ebw.toNat) % 8 = 0 ∧
           memW t (globN t "ev" + 24) + memW t (globN t "ev" + 40) = globN t "frame_mem_ptr")))
    (fun t w hw _ ⟨_, ⟨totw, htot, hpos⟩, _⟩ => by
      change t.locals.lookup (ofString "total") = some (.val (.word w)) at hw
      rw [htot] at hw; injection hw with hw'; injection hw' with hw''; injection hw'' with hweq; subst hweq
      exact hpos)
    (fun t cpost _ ⟨hHM, _, cw, ebw, hx, heb_cond⟩ _ hglob_cp _ hmem_head_cp => by
      have hHM_cp : HeadMemAligned cpost := headMemAligned_congr_head_only hglob_cp hmem_head_cp hHM
      let res : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
      have hHM_res : HeadMemAligned res := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp
      have hmem32_eq : memW res (globN res "ev" + 32) = memW t (globN t "ev" + 32) := by
        have hg : globN res "ev" = globN t "ev" := globN_eq_of_lookup_eq (by change cpost.globals.lookup _ = t.globals.lookup _; rw [hglob_cp])
        rw [hg]; exact hmem_head_cp 32 (by simp)
      refine ⟨cw, ebw, hx, ?_⟩
      rcases heb_cond with rfl | ⟨hlt37, hmod8, _⟩
      · exact Or.inl rfl
      · right
        rw [hmem32_eq]
        exact ⟨hlt37, hmod8, hHM_res.2⟩)
    ?_
  refine CalleeBodyRun.seq_call
    (Q := fun _ => True)
    eps_extend_memory_aligned
    (fun t values b_em callee rs_em hc _ ⟨cw, ebw, hx, heb_cond⟩ hargs hl => by
      have hx1 : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.rfield 1 (.var .local (ofString "x"))] = some [.val (.word ebw)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hx]
      rw [hx1] at hargs; injection hargs with hvs; subst hvs
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "extend_memory") [.val (.word ebw)] =
          some (b_em, callee, rs_em) := by rwa [← hc]
      obtain ⟨_, _, ebw', heq_eb, hcal_eb⟩ := one_word_arg_lookup lookup_extend_memory hl_orig
      injection heq_eb with heq1; injection heq1 with heq2; subst heq2
      exact ⟨ebw, hcal_eb, heb_cond⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
    (CalleeBodyRun.ret _)

theorem op_mload_spec_of_extend_memory
    {Qem : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h_extend_memory : EvmPreservingSpec
      (fun s => ∃ ebw : BitVec 64,
        s.locals.lookup (ofString "expand_by") = some (.val (.word ebw)) ∧
        ebw.toNat < 2 ^ 37)
      Qem
      (ofString "extend_memory")) :
    OpHandlerSpec (ofString "op_mload") := by
  refine opHandlerSpec_of_run 510 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_mload rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_mload, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRun.decCall_simple eps_stack_pop ?_
  refine seq_call_strict
    lookup_charge_with_memory
    (fun t values callee _ _ _ hargs hl_orig => by
      obtain ⟨basew, v2, v3, rfl, hcal_base⟩ := charge_with_memory_arg0_lookup hl_orig
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact, evalHOLExact] at hargs
      rcases hst : t.locals.lookup (ofString "start") with _ | u2
      · simp [hst] at hargs
      · simp [hst] at hargs
        obtain ⟨rfl, rfl, rfl⟩ := hargs
        exact ⟨3#64, hcal_base, by decide⟩)
    (charge_with_memory_body_run_of_extend_memory s0 h_extend_memory)
    ?_
  refine HandlerRun.decCall_simple eps_sat_word ?_
  refine HandlerRun.decCall_simple eps_u256_from_be_ro ?_
  refine HandlerRun.seq_call_simple eps_stack_push ?_
  refine HandlerRun.seq_call_simple eps_pc_add (HandlerRun.ret _)

theorem op_mload_aligned_spec :
    FunSpec (fun s => EvmRun s ∧ HeadMemAligned s) OpDispatchPost (ofString "op_mload") := by
  refine ⟨_, _, _, lookup_op_mload, ?_⟩
  intro F s0 hcode ⟨hRun, hHM0⟩ _ hnt
  suffices hrun : HandlerRun s0 HeadMemAligned false (sourceFnBody Guest.Software.guestFn_op_mload) from
    hrun s0 hcode hRun.1 rfl (le_refl _) hHM0 hnt
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_op_mload,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRun.decCall
    (Q := HeadMemAligned)
    eps_stack_pop_preserves_headMem
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ callee _ v cpost _ hHM _ _ _ _ ⟨_, _, hHM_step⟩ => by
      have hHM_ce : HeadMemAligned (callEntryStateHOLFinite t callee) :=
        headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      have hHM_cp : HeadMemAligned cpost := hHM_step hHM_ce
      exact headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp)
    ?_
  refine seq_call_strict
    lookup_charge_with_memory
    (fun t values callee _ _ hHM hargs hl_orig => by
      obtain ⟨basew, v2, v3, rfl, hcal_base⟩ := charge_with_memory_arg0_lookup hl_orig
      have hHM_ce : HeadMemAligned (callEntryStateHOLFinite t callee) :=
        headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact, evalHOLExact] at hargs
      rcases hst : t.locals.lookup (ofString "start") with _ | u2
      · simp [hst] at hargs
      · simp [hst] at hargs
        obtain ⟨rfl, rfl, rfl⟩ := hargs
        exact ⟨hHM_ce, 3#64, hcal_base, by decide⟩)
    (charge_with_memory_body_run_aligned s0)
    ?_
  refine HandlerRun.decCall_simple eps_sat_word ?_
  refine HandlerRun.decCall_simple eps_u256_from_be_ro ?_
  refine HandlerRun.seq_call_simple eps_stack_push ?_
  refine HandlerRun.seq_call_simple eps_pc_add (HandlerRun.ret _)

private theorem evmR_lt_gas_sentinel_g08 {F : Type}
    {s : PanSemStateFiniteExact 64 F} (hInv : EvmInv s) :
    evmR s < 2 ^ 64 - 1 := by
  obtain ⟨_, S, _, _, _, _, _, _, _, _, _, _, _, _, hGas⟩ := hInv
  change evmR s + 1 < 2 ^ 64 at hGas
  omega

private theorem charge_gas_return_lt_sentinel_g08 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hInv : EvmInv s)
    {amtw : BitVec 64}
    (hamt : s.locals.lookup (ofString "amount") = some (.val (.word amtw)))
    {v : ValueHOL 64}
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_charge_gas)).1 =
      some (.returned v)) :
    amtw.toNat < 2 ^ 64 - 1 := by
  have hsum := ((charge_gas_body_exact s hInv hamt).1 v hret).2.2.2
  have hbound := evmR_lt_gas_sentinel_g08 hInv
  omega

private theorem add_sat_body_exact_g08 {F : Type}
    (s : PanSemStateFiniteExact 64 F) {aw bw : BitVec 64}
    (ha : s.locals.lookup (ofString "a") = some (.val (.word aw)))
    (hb : s.locals.lookup (ofString "b") = some (.val (.word bw)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_add_sat)).1 =
      some (.returned v)) :
    ∃ rw : BitVec 64, v = .val (.word rw) ∧
      (rw.toNat < 2 ^ 64 - 1 → rw.toNat = aw.toNat + bw.toNat) := by
  have hbody : sourceFnBody Guest.Software.guestFn_add_sat =
      .dec (ofString "s") .one (.op .add [.var .local (ofString "a"), .var .local (ofString "b")])
        (.seq
          (.ite (.cmp .lower (.var .local (ofString "s")) (.var .local (ofString "a")))
            (.return (.const 18446744073709551615#64))
            .skip)
          (.return (.var .local (ofString "s")))) := rfl
  rw [hbody, evaluateHOLFiniteState_dec_total] at hret
  dsimp only at hret
  have hsum : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
      (.op .add [.var .local (ofString "a"), .var .local (ofString "b")]) =
      some (.val (.word (aw + bw))) := by
    simp [evalHOLExact, evalListHOLExact, ha, hb, wordOpHOL, wordOp, valueIsWord, valueWord]
  rw [hsum] at hret
  dsimp only at hret
  have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word (aw + bw)))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh] at hret
  dsimp only at hret
  set s1 := setVarHOLFinite (ofString "s") (.val (.word (aw + bw))) s
  have hs1_s : s1.locals.lookup (ofString "s") = some (.val (.word (aw + bw))) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_a : s1.locals.lookup (ofString "a") = some (.val (.word aw)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ha,
      show ofString "s" ≠ ofString "a" by decide]
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
  have hcmp : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
      (.cmp .lower (.var .local (ofString "s")) (.var .local (ofString "a"))) =
      some (.val (.word (if (aw + bw) < aw then 1 else 0))) := by
    simp [evalHOLExact, hs1_s, hs1_a, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp] at hret
  dsimp only at hret
  by_cases hlt : (aw + bw) < aw
  · have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    simp only [hlt, ↓reduceIte, h10] at hret
    rw [evaluateHOLFiniteState_return] at hret
    dsimp only [evalHOLExact] at hret
    have hsz : sizeOfShapeWithContextHOL s1.structs
        (shapeOfHOLExact (.val (.word 18446744073709551615#64))) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [if_pos hsz] at hret
    dsimp only at hret
    injection hret with h1
    injection h1 with hv
    refine ⟨18446744073709551615#64, hv.symm, ?_⟩
    intro hr
    change 18446744073709551615 < 2 ^ 64 - 1 at hr
    omega
  · simp only [hlt, ↓reduceIte, evaluateHOLFiniteState_skip] at hret
    rw [evaluateHOLFiniteState_return] at hret
    have hev_s : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
        (.var .local (ofString "s")) = some (.val (.word (aw + bw))) := hs1_s
    rw [hev_s] at hret
    dsimp only at hret
    split at hret
    · injection hret with h1
      injection h1 with hv
      refine ⟨aw + bw, hv.symm, ?_⟩
      intro _
      rw [BitVec.lt_def] at hlt
      have ha_lt := aw.isLt
      have hb_lt := bw.isLt
      simp only [BitVec.toNat_add] at hlt ⊢
      omega
    · simp at hret

private theorem evmInv_of_head_mem_bytes_g08 {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s)
    (heff : ByteRegionEffect s post
      [(memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))]) :
    EvmInv post ∧ evmChain post = evmChain s ∧ evmR post = evmR s := by
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    simp [evmChain, evmChainFrom]
  have hFW := hInv.2.choose_spec.2.2.2.2.1 _ hhead
  have hb := (frameWF_bounds hInv.1.2 hFW).1
  dsimp only at hb
  have he8 : globN s "ev" % 8 = 0 := (hFW.1 (globN s "ev", 280) (by simp)).2.1
  have hm8 : memW s (globN s "ev" + 24) % 8 = 0 := hFW.2.2.1.1
  have hrecord := (hFW.1 (globN s "ev", 280) (by simp)).1.1
  have hmem := hFW.2.1.2
  have hfp : globN s "frame_mem_ptr" ≤ globN s "scratch_ptr" := hInv.1.2.2.2.2.1
  have hfields : ∀ off, off + 8 ≤ 280 → off % 8 = 0 →
      memW post (globN s "ev" + off) = memW s (globN s "ev" + off) := by
    intro off hoff hoff8
    unfold memW
    rw [heff.cell_frame (BitVec.ofNat 64 (globN s "ev" + off))]
    intro i hi
    simp only [List.mem_singleton] at hi
    subst i
    have hnat : (BitVec.ofNat 64 (globN s "ev" + off)).toNat = globN s "ev" + off :=
      Nat.mod_eq_of_lt (by omega)
    rw [hnat]
    exact not_cellHits_of_disj_aligned (i := (globN s "ev", 280))
      (by omega) hm8 (Nat.le_add_right _ _) (Nat.add_le_add_left hoff _)
      (Or.inr (Or.inr (Or.inr (by dsimp only at hrecord hmem ⊢; omega))))
  have hArena : ArenaReady post :=
    ⟨guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hInv.1.1,
      arenaOK_congr heff.globals hInv.1.2⟩
  have hglob : ∀ g : String, globN post g = globN s g := by
    intro g
    unfold globN
    rw [heff.globals]
  apply evmInv_of_head_mem_extend (freshIvl := (0, 0)) hInv hArena
    (by rw [hglob])
    ((FrameMemByteEff.of_bre heff).mono (fun i hi => by
      simp only [List.mem_singleton] at hi
      subst i
      exact ⟨_, by simp, le_rfl, le_rfl⟩))
    (Or.inl rfl)
    (fun off hoff hoff8 _ _ => hfields off hoff hoff8)
    (Or.inl ⟨rfl, hfields 40 (by omega) (by omega)⟩)
  rw [hfields 32 (by omega) (by omega), hfields 40 (by omega) (by omega)]
  exact hFW.2.2.2.2.2.2.1

private theorem storeByte_some_eq_error_g08 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {dst val : ExpHOL 64}
    {res : PanSemResultExact 64}
    (h : evaluateHOLFiniteState s (.storeByte dst val) = (some res, post)) :
    res = .error := by
  rw [evaluateHOLFiniteState_storeByte] at h
  revert h
  split
  · split
    · split
      · intro h
        injection h with hr
        cases hr
      · intro h
        injection h with hr
        injection hr with hr'
        exact hr'.symm
    · intro h
      injection h with hr
      injection hr with hr'
      exact hr'.symm
  · intro h
    injection h with hr
    injection hr with hr'
    exact hr'.symm

private theorem HandlerRun.seq_storeByte_head_mem_g08 {F : Type}
    {s0 : PanSemStateFiniteExact 64 F} {charged : Bool}
    {dst val : ExpHOL 64} {cont : ProgHOL 64}
    (hcont : HandlerRun s0 (fun _ => True) charged cont) :
    HandlerRun s0
      (fun t => ∀ addr : BitVec 64,
        @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) dst =
          some (.val (.word addr)) →
        t.memaddrs (panByteAlignHOL addr) →
        memW t (globN t "ev" + 24) ≤ addr.toNat ∧
        addr.toNat < memW t (globN t "ev" + 24) + memW t (globN t "ev" + 40))
      charged (.seq (.storeByte dst val) cont) := by
  intro t hc hInv hlen hR hP hnt
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hstore : evaluateHOLFiniteState t (.storeByte dst val) with ⟨res, post⟩
  simp only [hstore] at hnt ⊢
  cases res with
  | none =>
    dsimp only at hnt ⊢
    have heff := (ByteRegionEffect.of_storeByte
      (Rl := [(memW t (globN t "ev" + 24), memW t (globN t "ev" + 40))])
      hstore
      (fun addr ha hd =>
        ⟨(memW t (globN t "ev" + 24), memW t (globN t "ev" + 40)),
          List.mem_singleton.mpr rfl, (hP addr ha hd).1, (hP addr ha hd).2⟩)).1
    obtain ⟨hInv_post, hch, hgas⟩ := evmInv_of_head_mem_bytes_g08 hInv heff
    exact hcont post (heff.code.trans hc) hInv_post
      (by rw [hch]; exact hlen) (by rw [hgas]; exact hR) trivial hnt
  | some res =>
    have herr := storeByte_some_eq_error_g08 hstore
    subst herr
    exact opDispatchPost_error s0 post

private theorem sat_word_body_exact_g08 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (a b c d : BitVec 64)
    (hv : s.locals.lookup (ofString "v") =
      some (.rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)])) :
    evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sat_word) =
      (some (.returned (.val (.word
        (if b ||| c ||| d = 0#64 then a else 18446744073709551615#64)))),
        s.emptyLocalsHOLFinite) := by
  have hbody : sourceFnBody Guest.Software.guestFn_sat_word =
      .seq
        (.ite (.cmp .notEqual
          (.op .or [.rfield 1 (.var .local (ofString "v")),
            .rfield 2 (.var .local (ofString "v")),
            .rfield 3 (.var .local (ofString "v"))]) (.const 0#64))
          (.return (.const 18446744073709551615#64)) .skip)
        (.return (.rfield 0 (.var .local (ofString "v")))) := rfl
  rw [hbody]
  by_cases hz : b ||| c ||| d = 0#64 <;>
    have hz' := hz <;>
    simp only [BitVec.or_eq_zero_iff, and_assoc] at hz' <;>
    simp [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite,
      evaluateHOLFiniteState_return, evaluateHOLFiniteState_skip,
      evalHOLExact, evalListHOLExact, hv, wordOpHOL, wordOp, valueIsWord, valueWord,
      OrOp.or, Compiler.Encoders.Asm.wordCmpHOL, hz, hz',
      shapeOfHOLExact, sizeOfShapeWithContextHOL]

private theorem ro_word_call_return_g08 {F : Type}
    {s st : PanSemStateFiniteExact 64 F} {nm fname : MlS}
    {args : List (ExpHOL 64)} {cont : ProgHOL 64} {v : ValueHOL 64}
    (hfn : opRoCallees fname = true)
    (hc : st.code = originalRuntimeCode) (hlf : LocFrame s st)
    (hr : (evaluateHOLFiniteState st (.decCall nm .one fname args cont)).1 =
      some (.returned v)) :
    ∃ (w : BitVec 64) (st' : PanSemStateFiniteExact 64 F),
      st'.code = originalRuntimeCode ∧ LocFrame s st' ∧
      st'.locals = st.locals.update (nm, .val (.word w)) ∧
      (∃ vals body callee rs,
        evalListHOLFinite st (h := fun x => Classical.propDecidable (st.memaddrs x)) args = some vals ∧
        lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, callee, rs) ∧
        (evaluateHOLFiniteState (callEntryStateHOLFinite st callee) body).1 =
          some (.returned (.val (.word w)))) ∧
      (evaluateHOLFiniteState st' cont).1 = some (.returned v) := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hr
  rcases hargs : evalListHOLFinite st (h := fun x => Classical.propDecidable (st.memaddrs x)) args with _ | vals
  · rw [hargs] at hr
    simp at hr
  · rw [hargs] at hr
    dsimp only at hr
    rcases hl : lookupCodeHOLFinite st.code.lookup fname vals with _ | ⟨body, callee, rs⟩
    · rw [hl] at hr
      simp at hr
    · rw [hl] at hr
      dsimp only at hr
      split at hr
      · simp at hr
      · have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, callee, rs) := by
          rwa [← hc]
        have hsafe := evaluate_readOnlyProg opRoCallees opRoCallees_good body
          (opRoCallees_good fname hfn vals body callee rs hl_orig)
          (callEntryStateHOLFinite st callee) hc
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite st callee) body with ⟨rb, pb⟩
        rw [hrun] at hr
        have hpb_c : pb.code = originalRuntimeCode := by
          have hm := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite st callee) body).1
          rw [hrun] at hm
          exact hm.trans hc
        rcases rb with _ | rb
        · simp at hr
        · cases rb with
          | returned vb =>
            dsimp only at hr
            split at hr
            · rename_i hsh
              dsimp only at hr
              have hone : shapeEqHOL (shapeOfHOLExact vb) .one = true := by
                simp [Bool.and_eq_true] at hsh
                exact hsh.1
              rcases vb with ⟨⟨w⟩⟩ | _ | _
              · have hlf_ce : LocFrame (callEntryStateHOLFinite st callee) pb := by
                  have hres := hsafe.to_resumes (by rw [hrun]; exact Or.inl ⟨.val (.word w), rfl⟩)
                  simpa [hrun] using hres
                have hlf_st : LocFrame st pb := by
                  unfold LocFrame at hlf_ce ⊢
                  rw [hlf_ce]
                  rfl
                let st' := setVarHOLFinite nm (.val (.word w)) { pb with locals := st.locals }
                exact ⟨w, st', hpb_c,
                  hlf.trans (hlf_st.with_locals_clock (st.locals.update (nm, .val (.word w))) pb.clock),
                  rfl, ⟨vals, body, callee, rs, rfl, hl_orig, by rw [hrun]⟩, hr⟩
              · simp [shapeOfHOLExact, shapeEqHOL] at hone
              · simp [shapeOfHOLExact, shapeEqHOL] at hone
            · simp at hr
          | _ => simp at hr

private theorem single_comb_arg_lookup_g08
    {fname param : MlS} {body : ProgHOL 64} {rs argShape : ShapeHOL}
    {values : List (ValueHOL 64)} {body' : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs' : ShapeHOL}
    (hlook : originalRuntimeCode.lookup fname = some ([(param, argShape)], body, rs))
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body', callee, rs')) :
    body' = body ∧ rs' = rs ∧ ∃ v,
      values = [v] ∧ callee.lookup param = some v := by
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
    originalRuntimeCode.lookup fname values body' callee rs' hl
  simp only [Flapjack.lookupCodeHOLExact, hlook] at hx
  rcases values with _ | ⟨v, _ | ⟨v', vs⟩⟩
  · simp at hx
  · split at hx
    · have hp := Option.some.inj hx
      rcases Prod.mk.inj hp with ⟨hb, hp⟩
      rcases Prod.mk.inj hp with ⟨hc, hr⟩
      refine ⟨hb.symm, hr.symm, v, rfl, ?_⟩
      have hfn := congrFun hc.symm param
      simpa [FUPDATE_LIST, FUPDATE] using hfn
    · cases hx
  · simp at hx

private theorem u256_is_zero_nonzero_body_g08 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (k : BitVec 64) (hk : k ≠ 0#64)
    (hv : s.locals.lookup (ofString "a") =
      some (.rStruct [.val (.word k), .val (.word 0#64), .val (.word 0#64), .val (.word 0#64)])) :
    evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_is_zero) =
      (some (.returned (.val (.word 0#64))), s.emptyLocalsHOLFinite) := by
  have hbody : sourceFnBody Guest.Software.guestFn_u256_is_zero =
      .seq
        (.ite (.cmp .equal
          (.op .or [.rfield 0 (.var .local (ofString "a")),
            .rfield 1 (.var .local (ofString "a")),
            .rfield 2 (.var .local (ofString "a")),
            .rfield 3 (.var .local (ofString "a"))]) (.const 0#64))
          (.return (.const 1#64)) .skip)
        (.return (.const 0#64)) := rfl
  rw [hbody]
  simp [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite,
    evaluateHOLFiniteState_return, evaluateHOLFiniteState_skip,
    evalHOLExact, evalListHOLExact, hv, wordOpHOL, wordOp, valueIsWord, valueWord,
    OrOp.or, Compiler.Encoders.Asm.wordCmpHOL, hk,
    shapeOfHOLExact, sizeOfShapeWithContextHOL]

private theorem ceil32_return_bounds_g08 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vw cw : BitVec 64)
    (hc : s.code = originalRuntimeCode)
    (hv : s.locals.lookup (ofString "v") = some (.val (.word vw)))
    (hr : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_ceil32)).1 =
      some (.returned (.val (.word cw)))) :
    (cw.toNat < 2 ^ 64 - 1 → vw.toNat ≤ cw.toNat) ∧
    (vw.toNat % 32 = 0 → cw = vw) := by
  have hb : sourceFnBody Guest.Software.guestFn_ceil32 =
      .dec (ofString "r") .one (.op .and [.var .local (ofString "v"), .const 31#64])
        (.seq
          (.ite (.cmp .equal (.var .local (ofString "r")) (.const 0#64))
            (.return (.var .local (ofString "v"))) .skip)
          (.decCall (ofString "s") .one (ofString "add_sat")
            [.var .local (ofString "v"), .op .sub [.const 32#64, .var .local (ofString "r")]]
            (.return (.var .local (ofString "s"))))) := rfl
  rw [hb, evaluateHOLFiniteState_dec_total] at hr
  have he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .and [.var .local (ofString "v"), .const 31#64]) =
      some (.val (.word (vw &&& 31#64))) := by
    simp [evalHOLExact, evalListHOLExact, hv, wordOpHOL, wordOp, valueIsWord, valueWord]
  simp only [he] at hr
  have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word (vw &&& 31#64)))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  simp only [hsh, ↓reduceIte] at hr
  let rw := vw &&& 31#64
  have hrn : rw.toNat = vw.toNat % 32 := by
    change (vw &&& 31#64).toNat = vw.toNat % 32
    rw [BitVec.toNat_and, show (31#64 : BitVec 64).toNat = 2 ^ 5 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod]
  set t := setVarHOLFinite (ofString "r") (.val (.word rw)) s
  have htc : t.code = originalRuntimeCode := hc
  have htr : t.locals.lookup (ofString "r") = some (.val (.word rw)) := by
    simp [t, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have htv : t.locals.lookup (ofString "v") = some (.val (.word vw)) := by
    simp [t, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hv,
      show ofString "r" ≠ ofString "v" by decide]
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr
  have hcmp : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.cmp .equal (.var .local (ofString "r")) (.const 0#64)) =
      some (.val (.word (if rw = 0#64 then 1 else 0))) := by
    simp [evalHOLExact, htr, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp] at hr
  dsimp only at hr
  by_cases hz : rw = 0#64
  · simp only [hz, ↓reduceIte, show ¬ (1 : BitVec 64) = 0 by decide] at hr
    rw [evaluateHOLFiniteState_return] at hr
    have hev : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        (.var .local (ofString "v")) = some (.val (.word vw)) := htv
    rw [hev] at hr
    dsimp only at hr
    have hsz : sizeOfShapeWithContextHOL t.structs
        (shapeOfHOLExact (.val (.word vw))) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [if_pos hsz] at hr
    dsimp only at hr
    have heq : vw = cw := by simpa using hr
    subst cw
    exact ⟨fun _ => le_rfl, fun _ => rfl⟩
  · simp only [hz, ↓reduceIte, evaluateHOLFiniteState_skip] at hr
    have hm : vw.toNat % 32 ≠ 0 := by
      intro hm
      apply hz
      apply BitVec.eq_of_toNat_eq
      simpa [hrn] using hm
    obtain ⟨sw, u, _, _, hul, ⟨vals, body, cal, rs, ha, hl, hrun⟩, htail⟩ :=
      ro_word_call_return_g08 (s := t) (st := t) (by decide) htc (LocFrame.refl t) hr
    have hav : vals = [.val (.word vw), .val (.word (32#64 - rw))] := by
      simpa [evalListHOLFinite, evalListHOLExact, evalHOLExact, htv, htr,
        wordOpHOL, wordOp, valueIsWord, valueWord] using ha.symm
    subst vals
    obtain ⟨rfl, _, aw, bw, hvls, hca, hcb⟩ := two_word_arg_lookup (by decide) lookup_add_sat hl
    have hw : aw = vw ∧ bw = 32#64 - rw := by simpa using hvls.symm
    rcases hw with ⟨rfl, rfl⟩
    obtain ⟨sw', hsw, hex⟩ := add_sat_body_exact_g08 (callEntryStateHOLFinite t cal)
      hca hcb (.val (.word sw)) hrun
    have hsw' : sw = sw' := by simpa using hsw
    subst sw'
    have hus : u.locals.lookup (ofString "s") = some (.val (.word sw)) := by
      rw [hul]
      simp [HolFiniteMapExact.lookup_update, FUPDATE]
    rw [evaluateHOLFiniteState_return] at htail
    have hue : @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
        (.var .local (ofString "s")) = some (.val (.word sw)) := hus
    rw [hue] at htail
    dsimp only at htail
    have hsz : sizeOfShapeWithContextHOL u.structs
        (shapeOfHOLExact (.val (.word sw))) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [if_pos hsz] at htail
    dsimp only at htail
    have heq : sw = cw := by simpa using htail
    subst cw
    exact ⟨fun hlt => by rw [hex hlt]; omega, fun hmod => False.elim (hm hmod)⟩

private theorem lookup_u256_is_zero_g08 :
    originalRuntimeCode.lookup (ofString "u256_is_zero") =
      some ([(ofString "a", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_u256_is_zero, .one) :=
  lookup_of_guestAst_getElem 42 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_is_zero) rfl

private theorem lookup_sat_word_g08 :
    originalRuntimeCode.lookup (ofString "sat_word") =
      some ([(ofString "v", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_sat_word, .one) :=
  lookup_of_guestAst_getElem 440 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_sat_word) rfl

private theorem u256_value_of_shape_g08 {v : ValueHOL 64}
    (h : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact v) = true) :
    ∃ a b c d : BitVec 64,
      v = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)] := by
  cases v with
  | val x => simp [shapeOfHOLExact, shapeEqHOL] at h
  | nStruct x xs => simp [shapeOfHOLExact, shapeEqHOL] at h
  | rStruct vs =>
    rcases vs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩⟩
    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
      rcases h with ⟨h0, h1, h2, h3⟩
      rcases v0 with ⟨⟨a⟩⟩ | _ | _ <;> try simp [shapeOfHOLExact, shapeEqHOL] at h0
      rcases v1 with ⟨⟨b⟩⟩ | _ | _ <;> try simp [shapeOfHOLExact, shapeEqHOL] at h1
      rcases v2 with ⟨⟨c⟩⟩ | _ | _ <;> try simp [shapeOfHOLExact, shapeEqHOL] at h2
      rcases v3 with ⟨⟨d⟩⟩ | _ | _ <;> try simp [shapeOfHOLExact, shapeEqHOL] at h3
      exact ⟨a, b, c, d, rfl⟩
    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h

private def satValue_g08 (v : ValueHOL 64) : BitVec 64 :=
  match v with
  | .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)] =>
    if b ||| c ||| d = 0#64 then a else 18446744073709551615#64
  | _ => 18446744073709551615#64

private theorem eps_sat_word_exact_g08 :
    EvmPreservingSpec
      (fun s => ∃ v, s.locals.lookup (ofString "v") = some v ∧
        shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact v) = true)
      (fun s ret post => LocFrame s post ∧
        ∀ v, s.locals.lookup (ofString "v") = some v → ret = .val (.word (satValue_g08 v)))
      (ofString "sat_word") := by
  refine ⟨_, _, _, lookup_sat_word_g08, ?_⟩
  intro F s hc hInv ⟨v, hv, hshape⟩ _ _
  obtain ⟨a, b, c, d, rfl⟩ := u256_value_of_shape_g08 hshape
  rw [sat_word_body_exact_g08 s a b c d hv]
  dsimp only
  refine ⟨fun ret hret => ?_, ?_⟩
  · have heq : ret = .val (.word (satValue_g08
        (.rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]))) := by
      simpa [satValue_g08] using hret.symm
    subst ret
    refine ⟨localsFree_evmInv s _ s.clock hInv, evmChain_congr rfl rfl,
      le_of_eq (evm_congr (s := s) (t := s.emptyLocalsHOLFinite) rfl rfl).2.1,
      (LocFrame.refl s).with_locals_clock _ _, ?_⟩
    intro v' hv'
    rw [hv] at hv'
    injection hv' with hv'
    subst v'
    rfl
  · rintro ⟨_, h⟩
    cases h

private theorem extend_memory_cost1_nonzero_coverage_g08 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (stVal : ValueHOL 64) (kw : BitVec 64)
    (hc : s.code = originalRuntimeCode)
    (hst : s.locals.lookup (ofString "start") = some stVal)
    (hst_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true)
    (hsz : s.locals.lookup (ofString "size") =
      some (.rStruct [.val (.word kw), .val (.word 0#64), .val (.word 0#64), .val (.word 0#64)]))
    (hkw : kw ≠ 0#64)
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_extend_memory_cost1)).1 =
      some (.returned v)) :
    ∀ cw ebw : BitVec 64,
      v = .rStruct [.val (.word cw), .val (.word ebw)] →
      cw.toNat < 2 ^ 64 - 1 →
      memW s (globN s "ev" + 32) % 32 = 0 →
      (satValue_g08 stVal).toNat + kw.toNat ≤ memW s (globN s "ev" + 32) + ebw.toNat := by
  intro cw ebw hv hcw_lt hcur_mod
  subst hv
  obtain ⟨a, b, c, d, rfl⟩ := u256_value_of_shape_g08 hst_sh
  have hbody : sourceFnBody Guest.Software.guestFn_extend_memory_cost1 =
      .decCall (ofString "z") .one (ofString "u256_is_zero") [.var .local (ofString "size")]
        (.seq
          (.ite (.cmp .notEqual (.var .local (ofString "z")) (.const 0#64))
            (.return (.rstruct [.const 0#64, .const 0#64]))
            .skip)
          (.decCall (ofString "s") .one (ofString "sat_word") [.var .local (ofString "start")]
            (.decCall (ofString "n") .one (ofString "sat_word") [.var .local (ofString "size")]
              (.decCall (ofString "endp") .one (ofString "add_sat")
                [.var .local (ofString "s"), .var .local (ofString "n")]
                (.seq
                  (.ite (.cmp .equal (.var .local (ofString "endp")) (.const 18446744073709551615#64))
                    (.return (.rstruct [.const 18446744073709551615#64, .const 0#64]))
                    .skip)
                  (.dec (ofString "cur") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 32#64]))
                    (.decCall (ofString "before") .one (ofString "ceil32") [.var .local (ofString "cur")]
                      (.decCall (ofString "after") .one (ofString "ceil32") [.var .local (ofString "endp")]
                        (.seq
                          (.ite (.cmp .notLower (.var .local (ofString "before")) (.var .local (ofString "after")))
                            (.return (.rstruct [.const 0#64, .const 0#64]))
                            .skip)
                          (.decCall (ofString "ca") .one (ofString "memory_gas_cost") [.var .local (ofString "after")]
                            (.decCall (ofString "cb") .one (ofString "memory_gas_cost") [.var .local (ofString "before")]
                              (.seq
                                (.ite (.cmp .equal (.var .local (ofString "ca")) (.const 18446744073709551615#64))
                                  (.return (.rstruct [.const 18446744073709551615#64, .const 0#64]))
                                  .skip)
                                (.return (.rstruct
                                  [.op .sub [.var .local (ofString "ca"), .var .local (ofString "cb")],
                                   .op .sub [.var .local (ofString "after"), .var .local (ofString "before")]])))))))))))))) := rfl
  have hret_pair : ∀ (st : PanSemStateFiniteExact 64 F) (w1 w2 : BitVec 64),
      evaluateHOLFiniteState st (.return (.rstruct [.const w1, .const w2])) =
        (some (.returned (.rStruct [.val (.word w1), .val (.word w2)])), st.emptyLocalsHOLFinite) := by
    intro st w1 w2
    rw [evaluateHOLFiniteState_return]
    have hev : @evalHOLExact 64 F _ st.toExact (fun x => Classical.propDecidable (st.memaddrs x))
        (.rstruct [.const w1, .const w2]) =
        some (.rStruct [.val (.word w1), .val (.word w2)]) := by
      simp [evalHOLExact, evalListHOLExact]
    rw [hev]
    dsimp only
    have hsz2 : sizeOfShapeWithContextHOL st.structs
        (shapeOfHOLExact (.rStruct [.val (.word w1), .val (.word w2)] : ValueHOL 64)) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
    rw [if_pos hsz2]
  have h10 : ¬ ((1#64 : BitVec 64) = 0) := by decide
  have h00 : (0#64 : BitVec 64) = 0 := rfl
  rw [hbody] at hret
  obtain ⟨zw, s1, hs1_c, hs1_lf, hs1_loc, ⟨vals1, body1, cal1, rs1, ha1, hl1, hrun1⟩, hr1⟩ :=
    ro_word_call_return_g08 (s := s) (st := s) (by decide) hc (LocFrame.refl s) hret
  have hvals1 : vals1 = [.rStruct [.val (.word kw), .val (.word 0#64), .val (.word 0#64), .val (.word 0#64)]] := by
    simpa [evalListHOLFinite, evalListHOLExact, evalHOLExact, hsz] using ha1.symm
  subst vals1
  obtain ⟨rfl, _, uzv, huzv_eq, hcal1⟩ := single_comb_arg_lookup_g08 lookup_u256_is_zero_g08 hl1
  injection huzv_eq with huzv_eq
  subst uzv
  rw [u256_is_zero_nonzero_body_g08 _ kw hkw hcal1] at hrun1
  have hzw0 : zw = 0#64 := by simpa using hrun1.symm
  subst zw
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr1
  have hs1_z : s1.locals.lookup (ofString "z") = some (.val (.word 0#64)) := by
    rw [hs1_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hcmp_z : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
      (.cmp .notEqual (.var .local (ofString "z")) (.const 0#64)) =
      some (.val (.word 0#64)) := by
    simp [evalHOLExact, hs1_z, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp_z] at hr1
  dsimp only at hr1
  rw [if_pos h00, evaluateHOLFiniteState_skip] at hr1
  dsimp only at hr1
  have hs1_st : s1.locals.lookup (ofString "start") =
      some (.rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) := by
    rw [hs1_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, hst,
      show ofString "z" ≠ ofString "start" by decide]
  obtain ⟨sw, s2, hs2_c, hs2_lf, hs2_loc, ⟨vals2, body2, cal2, rs2, ha2, hl2, hrun2⟩, hr2⟩ :=
    ro_word_call_return_g08 (s := s) (st := s1) (by decide) hs1_c hs1_lf hr1
  have hvals2 : vals2 = [.rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]] := by
    simpa [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs1_st] using ha2.symm
  subst vals2
  obtain ⟨rfl, _, sv2, hsv2_eq, hcal2⟩ := single_comb_arg_lookup_g08 lookup_sat_word_g08 hl2
  injection hsv2_eq with hsv2_eq
  subst sv2
  rw [sat_word_body_exact_g08 _ a b c d hcal2] at hrun2
  have hsw_eq : sw = satValue_g08 (.rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) := by
    simpa [satValue_g08] using hrun2.symm
  have hs2_sz : s2.locals.lookup (ofString "size") =
      some (.rStruct [.val (.word kw), .val (.word 0#64), .val (.word 0#64), .val (.word 0#64)]) := by
    rw [hs2_loc, hs1_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, hsz,
      show ofString "s" ≠ ofString "size" by decide,
      show ofString "z" ≠ ofString "size" by decide]
  obtain ⟨nw, s3, hs3_c, hs3_lf, hs3_loc, ⟨vals3, body3, cal3, rs3, ha3, hl3, hrun3⟩, hr3⟩ :=
    ro_word_call_return_g08 (s := s) (st := s2) (by decide) hs2_c hs2_lf hr2
  have hvals3 : vals3 = [.rStruct [.val (.word kw), .val (.word 0#64), .val (.word 0#64), .val (.word 0#64)]] := by
    simpa [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs2_sz] using ha3.symm
  subst vals3
  obtain ⟨rfl, _, sv3, hsv3_eq, hcal3⟩ := single_comb_arg_lookup_g08 lookup_sat_word_g08 hl3
  injection hsv3_eq with hsv3_eq
  subst sv3
  rw [sat_word_body_exact_g08 _ kw 0#64 0#64 0#64 hcal3] at hrun3
  have hnw_eq : nw = kw := by simpa using hrun3.symm
  subst nw
  have hs3_s : s3.locals.lookup (ofString "s") = some (.val (.word sw)) := by
    rw [hs3_loc, hs2_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "n" ≠ ofString "s" by decide]
  have hs3_n : s3.locals.lookup (ofString "n") = some (.val (.word kw)) := by
    rw [hs3_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE]
  obtain ⟨endpw, s4, hs4_c, hs4_lf, hs4_loc, ⟨vals4, body4, cal4, rs4, ha4, hl4, hrun4⟩, hr4⟩ :=
    ro_word_call_return_g08 (s := s) (st := s3) (by decide) hs3_c hs3_lf hr3
  have hvals4 : vals4 = [.val (.word sw), .val (.word kw)] := by
    simpa [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs3_s, hs3_n] using ha4.symm
  subst vals4
  obtain ⟨rfl, _, aw4, bw4, hvls4, hca4, hcb4⟩ := two_word_arg_lookup (by decide) lookup_add_sat hl4
  have hw4 : sw = aw4 ∧ kw = bw4 := by simpa using hvls4
  rcases hw4 with ⟨rfl, rfl⟩
  obtain ⟨endpw', hendpw_inj, hendp_ex⟩ := add_sat_body_exact_g08 (callEntryStateHOLFinite s3 cal4)
    hca4 hcb4 (.val (.word endpw)) hrun4
  have hendpw_eq : endpw = endpw' := by simpa using hendpw_inj
  subst endpw'
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr4
  have hs4_endp : s4.locals.lookup (ofString "endp") = some (.val (.word endpw)) := by
    rw [hs4_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hcmp_endp : @evalHOLExact 64 F _ s4.toExact (fun x => Classical.propDecidable (s4.memaddrs x))
      (.cmp .equal (.var .local (ofString "endp")) (.const 18446744073709551615#64)) =
      some (.val (.word (if endpw = 18446744073709551615#64 then 1#64 else 0#64))) := by
    simp [evalHOLExact, hs4_endp, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp_endp] at hr4
  dsimp only at hr4
  by_cases hendp_max : endpw = 18446744073709551615#64
  · rw [if_pos hendp_max, if_neg h10, hret_pair s4 18446744073709551615#64 0#64] at hr4
    have hcw_eq : cw = 18446744073709551615#64 := by
      have hp : cw = 18446744073709551615#64 ∧ ebw = 0#64 := by simpa using hr4.symm
      exact hp.1
    subst cw
    change 18446744073709551615 < 2 ^ 64 - 1 at hcw_lt
    omega
  · rw [if_neg hendp_max, if_pos h00, evaluateHOLFiniteState_skip] at hr4
    dsimp only at hr4
    have hendp_lt : endpw.toNat < 2 ^ 64 - 1 := by
      have hlt64 := endpw.isLt
      by_contra hge
      apply hendp_max
      apply BitVec.eq_of_toNat_eq
      change endpw.toNat = 18446744073709551615
      omega
    have hendp_sum := hendp_ex hendp_lt
    rw [evaluateHOLFiniteState_dec_total] at hr4
    dsimp only at hr4
    rcases hld_cur : @evalHOLExact 64 F _ s4.toExact (fun x => Classical.propDecidable (s4.memaddrs x))
        (.load .one (.op .add [.var .global (ofString "ev"), .const 32#64])) with _ | curv
    · rw [hld_cur] at hr4
      simp at hr4
    · obtain ⟨curw, rfl, hcurw_nat⟩ := evalAt_loadG_word s4 "ev" 32#64 curv hld_cur
      rw [hld_cur] at hr4
      dsimp only at hr4
      have hsh_cur : shapeEqHOL .one (shapeOfHOLExact (.val (.word curw))) = true := by
        simp [shapeEqHOL, shapeOfHOLExact]
      rw [if_pos hsh_cur] at hr4
      dsimp only at hr4
      have hs4_mem : s4.memory = s.memory := by unfold LocFrame at hs4_lf; conv_lhs => rw [hs4_lf]
      have hs4_glob : s4.globals = s.globals := by unfold LocFrame at hs4_lf; conv_lhs => rw [hs4_lf]
      have hcur_eq : curw.toNat = memW s (globN s "ev" + 32) := by
        have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
        rw [hcurw_nat, h32]
        simp [memW, globN, hs4_mem, hs4_glob]
      set s5 := setVarHOLFinite (ofString "cur") (.val (.word curw)) s4 with hs5_def
      have hs5_c : s5.code = originalRuntimeCode := hs4_c
      have hs5_lf : LocFrame s s5 := hs4_lf.with_locals_clock _ s4.clock
      have hs5_cur : s5.locals.lookup (ofString "cur") = some (.val (.word curw)) := by
        simp [hs5_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      obtain ⟨befw, s6, hs6_c, hs6_lf, hs6_loc, ⟨vals6, body6, cal6, rs6, ha6, hl6, hrun6⟩, hr6⟩ :=
        ro_word_call_return_g08 (s := s) (st := s5) (by decide) hs5_c hs5_lf hr4
      have hvals6 : vals6 = [.val (.word curw)] := by
        simpa [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs5_cur] using ha6.symm
      subst vals6
      obtain ⟨rfl, _, curw', hcur_inj, hcal6⟩ := one_word_arg_lookup lookup_ceil32 hl6
      have hcur_inj' : curw = curw' := by simpa using hcur_inj
      subst curw'
      have hbef_b := ceil32_return_bounds_g08 (callEntryStateHOLFinite s5 cal6) curw befw hs5_c hcal6 hrun6
      have hbef_eq_cur : befw = curw := hbef_b.2 (by rwa [hcur_eq])
      subst befw
      have hs6_endp : s6.locals.lookup (ofString "endp") = some (.val (.word endpw)) := by
        rw [hs6_loc]
        simp [hs5_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs4_endp,
          show ofString "before" ≠ ofString "endp" by decide,
          show ofString "cur" ≠ ofString "endp" by decide]
      obtain ⟨aftw, s7, hs7_c, hs7_lf, hs7_loc, ⟨vals7, body7, cal7, rs7, ha7, hl7, hrun7⟩, hr7⟩ :=
        ro_word_call_return_g08 (s := s) (st := s6) (by decide) hs6_c hs6_lf hr6
      have hvals7 : vals7 = [.val (.word endpw)] := by
        simpa [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs6_endp] using ha7.symm
      subst vals7
      obtain ⟨rfl, _, endpw2, hendp_inj2, hcal7⟩ := one_word_arg_lookup lookup_ceil32 hl7
      have hendp_inj2' : endpw = endpw2 := by simpa using hendp_inj2
      subst endpw2
      have haft_b := ceil32_return_bounds_g08 (callEntryStateHOLFinite s6 cal7) endpw aftw hs6_c hcal7 hrun7
      have hs7_bef : s7.locals.lookup (ofString "before") = some (.val (.word curw)) := by
        rw [hs7_loc, hs6_loc]
        simp [HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "after" ≠ ofString "before" by decide]
      have hs7_aft : s7.locals.lookup (ofString "after") = some (.val (.word aftw)) := by
        rw [hs7_loc]
        simp [HolFiniteMapExact.lookup_update, FUPDATE]
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr7
      have hcmp_ba : @evalHOLExact 64 F _ s7.toExact (fun x => Classical.propDecidable (s7.memaddrs x))
          (.cmp .notLower (.var .local (ofString "before")) (.var .local (ofString "after"))) =
          some (.val (.word (if ¬ (curw < aftw) then 1#64 else 0#64))) := by
        simp [evalHOLExact, hs7_bef, hs7_aft, Compiler.Encoders.Asm.wordCmpHOL]
      rw [hcmp_ba] at hr7
      dsimp only at hr7
      by_cases hba : ¬ (curw < aftw)
      · rw [if_pos hba, if_neg h10, hret_pair s7 0#64 0#64] at hr7
        have heb0 : ebw = 0#64 := by
          have hp : cw = 0#64 ∧ ebw = 0#64 := by simpa using hr7.symm
          exact hp.2
        subst ebw
        have haft_le_cur : aftw.toNat ≤ curw.toNat := by
          rw [BitVec.lt_def] at hba
          omega
        by_cases haft_max : aftw.toNat < 2 ^ 64 - 1
        · have hendp_le_aft := haft_b.1 haft_max
          rw [← hsw_eq, ← hendp_sum]
          omega
        · have hcur_lt64 := curw.isLt
          have hcur_eq_max : curw.toNat = 2 ^ 64 - 1 := by omega
          rw [hcur_eq_max] at hcur_eq
          rw [← hcur_eq] at hcur_mod
          omega
      · rw [if_neg hba, if_pos h00, evaluateHOLFiniteState_skip] at hr7
        dsimp only at hr7
        have hba_lt : curw.toNat < aftw.toNat := BitVec.lt_def.1 (Classical.not_not.1 hba)
        obtain ⟨caw, s8, hs8_c, hs8_lf, hs8_loc, _, hr8⟩ :=
          ro_word_call_return_g08 (s := s) (st := s7) (by decide) hs7_c hs7_lf hr7
        obtain ⟨cbw, s9, hs9_c, hs9_lf, hs9_loc, _, hr9⟩ :=
          ro_word_call_return_g08 (s := s) (st := s8) (by decide) hs8_c hs8_lf hr8
        have hs9_ca : s9.locals.lookup (ofString "ca") = some (.val (.word caw)) := by
          rw [hs9_loc, hs8_loc]
          simp [HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "cb" ≠ ofString "ca" by decide]
        have hs9_cb : s9.locals.lookup (ofString "cb") = some (.val (.word cbw)) := by
          rw [hs9_loc]
          simp [HolFiniteMapExact.lookup_update, FUPDATE]
        have hs9_bef : s9.locals.lookup (ofString "before") = some (.val (.word curw)) := by
          rw [hs9_loc, hs8_loc]
          simp [HolFiniteMapExact.lookup_update, FUPDATE, hs7_bef,
            show ofString "cb" ≠ ofString "before" by decide,
            show ofString "ca" ≠ ofString "before" by decide]
        have hs9_aft : s9.locals.lookup (ofString "after") = some (.val (.word aftw)) := by
          rw [hs9_loc, hs8_loc]
          simp [HolFiniteMapExact.lookup_update, FUPDATE, hs7_aft,
            show ofString "cb" ≠ ofString "after" by decide,
            show ofString "ca" ≠ ofString "after" by decide]
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr9
        have hcmp_ca : @evalHOLExact 64 F _ s9.toExact (fun x => Classical.propDecidable (s9.memaddrs x))
            (.cmp .equal (.var .local (ofString "ca")) (.const 18446744073709551615#64)) =
            some (.val (.word (if caw = 18446744073709551615#64 then 1#64 else 0#64))) := by
          simp [evalHOLExact, hs9_ca, Compiler.Encoders.Asm.wordCmpHOL]
        rw [hcmp_ca] at hr9
        dsimp only at hr9
        by_cases hca_max : caw = 18446744073709551615#64
        · rw [if_pos hca_max, if_neg h10, hret_pair s9 18446744073709551615#64 0#64] at hr9
          have hcw_eq : cw = 18446744073709551615#64 := by
            have hp : cw = 18446744073709551615#64 ∧ ebw = 0#64 := by simpa using hr9.symm
            exact hp.1
          subst cw
          change 18446744073709551615 < 2 ^ 64 - 1 at hcw_lt
          omega
        · rw [if_neg hca_max, if_pos h00, evaluateHOLFiniteState_skip] at hr9
          dsimp only at hr9
          rw [evaluateHOLFiniteState_return] at hr9
          have hev_ret : @evalHOLExact 64 F _ s9.toExact (fun x => Classical.propDecidable (s9.memaddrs x))
              (.rstruct
                [.op .sub [.var .local (ofString "ca"), .var .local (ofString "cb")],
                 .op .sub [.var .local (ofString "after"), .var .local (ofString "before")]]) =
              some (.rStruct [.val (.word (caw - cbw)), .val (.word (aftw - curw))]) := by
            simp [evalHOLExact, evalListHOLExact, hs9_ca, hs9_cb, hs9_aft, hs9_bef,
              wordOpHOL, wordOp, valueIsWord, valueWord]
          rw [hev_ret] at hr9
          dsimp only at hr9
          have hsz2 : sizeOfShapeWithContextHOL s9.structs
              (shapeOfHOLExact (.rStruct [.val (.word (caw - cbw)), .val (.word (aftw - curw))] : ValueHOL 64)) ≤ 32 := by
            simp [shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
          rw [if_pos hsz2] at hr9
          dsimp only at hr9
          have heb_eq : ebw = aftw - curw := by
            have hp : caw - cbw = cw ∧ aftw - curw = ebw := by simpa using hr9
            exact hp.2.symm
          subst ebw
          have hsub_nat : (aftw - curw).toNat = aftw.toNat - curw.toNat :=
            BitVec.toNat_sub_of_le (BitVec.le_def.2 (Nat.le_of_lt hba_lt))
          by_cases haft_lt : aftw.toNat < 2 ^ 64 - 1
          · have hendp_le_aft := haft_b.1 haft_lt
            rw [← hsw_eq, ← hendp_sum, hsub_nat, ← hcur_eq]
            omega
          · have haft_lt64 := aftw.isLt
            rw [← hsw_eq, ← hendp_sum, hsub_nat, ← hcur_eq]
            omega

private theorem resVarEq_lookup_ne_g08 {V : Type}
    (mp : HolFiniteMapExact MlS V) (key q : MlS) (old : Option V)
    (hne : key ≠ q) :
    (mp.resVarEq (key, old)).lookup q = mp.lookup q := by
  unfold HolFiniteMapExact.resVarEq
  cases old with
  | none => simp [HolFiniteMapExact.eraseEq, FDOMSUB_HOL, hne.symm]
  | some u => simp [HolFiniteMapExact.updateEq, FUPDATE_HOL, hne.symm]

private theorem call_void_not_returned_g08 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {fn : MlS} {args : List (ExpHOL 64)} {v : ValueHOL 64}
    (h : evaluateHOLFiniteState s (.call (some (none, none)) fn args) = (some (.returned v), post)) :
    False := by
  rw [evaluateHOLFiniteState_call] at h
  revert h
  split
  · intro h; cases h
  · split
    · intro h; cases h
    · split
      · intro h; cases h
      · split
        · intro h; cases h
        · intro h; cases h
        · intro h; cases h
        · split
          · intro h; cases h
          · intro h; cases h
        · intro h; cases h
        · intro h
          cases h
          aesop

private theorem call_void_preserves_locals_g08 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {fn : MlS} {args : List (ExpHOL 64)}
    (h : evaluateHOLFiniteState s (.call (some (none, none)) fn args) = (none, post)) :
    post.locals = s.locals := by
  rw [evaluateHOLFiniteState_call] at h
  revert h
  split
  · intro h; cases h
  · split
    · intro h; cases h
    · split
      · intro h; cases h
      · split
        · intro h; cases h
        · intro h; cases h
        · intro h; cases h
        · split
          · intro h
            injection h with _ hp
            subst hp
            rfl
          · intro h; cases h
        · intro h; cases h
        · intro h; cases h

private theorem store_preserves_locals_globals_g08 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {dst val : ExpHOL 64}
    (h : evaluateHOLFiniteState s (.store dst val) = (none, post)) :
    post.locals = s.locals ∧ post.globals = s.globals := by
  rw [evaluateHOLFiniteState_store] at h
  revert h
  split
  · split
    · split
      · intro h
        injection h with _ hp
        subst hp
        exact ⟨rfl, rfl⟩
      · intro h; cases h
    · intro h; cases h
  · intro h; cases h

private theorem eps_extend_memory_cost1_bounds_cov_g08 :
    EvmPreservingSpec (fun _ => True)
      (fun s v post =>
        LocFrame s post ∧
        ∃ cw ebw : BitVec 64,
          v = .rStruct [.val (.word cw), .val (.word ebw)] ∧
          (ebw = 0#64 ∨
            ∃ before after : Nat,
              after < 2 ^ 37 ∧
              after % 32 = 0 ∧
              before < after ∧
              ebw.toNat = after - before ∧
              (memW s (globN s "ev" + 32) % 32 = 0 → before = memW s (globN s "ev" + 32))) ∧
          (∀ (stVal : ValueHOL 64) (kw : BitVec 64),
            s.locals.lookup (ofString "start") = some stVal →
            shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true →
            s.locals.lookup (ofString "size") =
              some (.rStruct [.val (.word kw), .val (.word 0#64), .val (.word 0#64), .val (.word 0#64)]) →
            kw ≠ 0#64 →
            cw.toNat < 2 ^ 64 - 1 →
            memW s (globN s "ev" + 32) % 32 = 0 →
            (satValue_g08 stVal).toNat + kw.toNat ≤ memW s (globN s "ev" + 32) + ebw.toNat))
      (ofString "extend_memory_cost1") := by
  obtain ⟨params, body, retShape, hlk, hspec⟩ := eps_extend_memory_cost1_bounds
  have hlk_eq := lookup_extend_memory_cost1.symm.trans hlk
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_eq, rfl⟩
  subst hbody_eq
  refine ⟨_, _, _, lookup_extend_memory_cost1, ?_⟩
  intro F s hcode hInv hP hlookup hnt
  have hs := hspec s hcode hInv hP hlookup hnt
  dsimp only at hs ⊢
  refine ⟨fun v hv => ?_, hs.2⟩
  obtain ⟨h1, h2, h3, hlf, cw, ebw, hv_eq, heb_bounds⟩ := hs.1 v hv
  refine ⟨h1, h2, h3, hlf, cw, ebw, hv_eq, heb_bounds, ?_⟩
  intro stVal kw hst hst_sh hsz hkw hcw_lt hcur_mod
  exact extend_memory_cost1_nonzero_coverage_g08 s stVal kw hcode hst hst_sh hsz hkw v hv cw ebw hv_eq hcw_lt hcur_mod

private theorem eps_add_sat_pos_exact_g08 :
    EvmPreservingSpec
      (fun s => ∃ aw bw : BitVec 64,
        s.locals.lookup (ofString "a") = some (.val (.word aw)) ∧
        s.locals.lookup (ofString "b") = some (.val (.word bw)) ∧
        0 < aw.toNat)
      (fun s v post =>
        LocFrame s post ∧
        ∃ rw : BitVec 64, v = .val (.word rw) ∧ 0 < rw.toNat ∧
          ∀ aw bw : BitVec 64,
            s.locals.lookup (ofString "a") = some (.val (.word aw)) →
            s.locals.lookup (ofString "b") = some (.val (.word bw)) →
            rw.toNat < 2 ^ 64 - 1 →
            rw.toNat = aw.toNat + bw.toNat)
      (ofString "add_sat") := by
  obtain ⟨params, body, retShape, hlk, hspec⟩ := eps_add_sat_pos
  have hlk_eq := lookup_add_sat.symm.trans hlk
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_eq, rfl⟩
  subst hbody_eq
  refine ⟨_, _, _, lookup_add_sat, ?_⟩
  intro F s hcode hInv ⟨aw, bw, ha, hb, hpos⟩ hlookup hnt
  have hs := hspec s hcode hInv ⟨aw, ha, hpos⟩ hlookup hnt
  dsimp only at hs ⊢
  refine ⟨fun v hv => ?_, hs.2⟩
  obtain ⟨h1, h2, h3, hlf, rw, hrw_eq, hrw_pos⟩ := hs.1 v hv
  obtain ⟨rw', hrw_eq', hex⟩ := add_sat_body_exact_g08 s ha hb v hv
  have hrw_same : rw = rw' := by simpa [hrw_eq] using hrw_eq'
  subst rw'
  refine ⟨h1, h2, h3, hlf, rw, hrw_eq, hrw_pos, ?_⟩
  intro aw' bw' ha' hb' hlt
  have haw : aw' = aw := by rw [ha] at ha'; simpa using ha'.symm
  have hbw : bw' = bw := by rw [hb] at hb'; simpa using hb'.symm
  subst haw hbw
  exact hex hlt

private theorem extend_memory_return_len_g08 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (ebw : BitVec 64) (v : ValueHOL 64)
    (hInv : EvmInv s)
    (heb : s.locals.lookup (ofString "expand_by") = some (.val (.word ebw)))
    (hbound : ebw = 0#64 ∨ memW s (globN s "ev" + 32) + ebw.toNat < 2 ^ 37)
    (hev_eq : globN (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_extend_memory)).2 "ev" =
      globN s "ev")
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_extend_memory)).1 =
      some (.returned v)) :
    memW (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_extend_memory)).2
      (globN (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_extend_memory)).2 "ev" + 32) =
      memW s (globN s "ev" + 32) + ebw.toNat := by
  rw [hev_eq]
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by simp [evmChain, evmChainFrom]
  have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead
  have hb_ev := (frameWF_bounds hInv.1.2 hFW0).1
  dsimp only at hb_ev
  have hev_pos : 0 < globN s "ev" := by
    obtain ⟨hin1, _⟩ := (hFW0.1 (globN s "ev", 280) (by simp)).1
    have h1 := hInv.1.2.2.2.1
    have h2 := hInv.1.2.2.2.2.1
    rw [R11Shards.scratchStart_val] at h1
    dsimp only at hin1
    omega
  obtain ⟨evw, hevw, hevw_nat⟩ := global_word_of_pos s "ev" hev_pos
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
  rw [hbody] at hret ⊢
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret ⊢
  have hcmp0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.var .local (ofString "expand_by")) (.const 0#64)) =
      some (.val (.word (if ebw = 0#64 then 1 else 0))) := by
    simp [evalHOLExact, heb, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp0] at hret ⊢
  dsimp only at hret ⊢
  by_cases heb0 : ebw = 0#64
  · simp only [heb0, ↓reduceIte, show ¬ ((1 : BitVec 64) = 0) by decide] at hret ⊢
    rw [evaluateHOLFiniteState_return]
    have hc0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.const 0#64) =
        some (.val (.word 0#64)) := rfl
    rw [hc0]
    dsimp only
    have hsz0 : sizeOfShapeWithContextHOL s.structs
        (shapeOfHOLExact (.val (.word 0#64))) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [if_pos hsz0]
    dsimp only
    simp [emptyLocalsHOLFinite, memW]
  · have hnlen_bound : memW s (globN s "ev" + 32) + ebw.toNat < 2 ^ 37 := by
      rcases hbound with rfl | hb
      · exact absurd rfl heb0
      · exact hb
    simp only [heb0, ↓reduceIte, evaluateHOLFiniteState_skip] at hret ⊢
    rw [evaluateHOLFiniteState_dec_total] at hret ⊢
    dsimp only at hret ⊢
    rcases hload_len : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one (.op .add [.var .global (ofString "ev"), .const 32#64])) with _ | vlen
    · rw [hload_len] at hret
      simp at hret
    · simp only [hload_len] at hret ⊢
      obtain ⟨lenw, rfl, hlenw_eq⟩ := evalAt_loadG_word s "ev" 32#64 vlen hload_len
      have h32_n : (32#64 : BitVec 64).toNat = 32 := rfl
      rw [h32_n] at hlenw_eq
      have hsh_len : shapeEqHOL .one (shapeOfHOLExact (.val (.word lenw))) = true := by
        simp [shapeEqHOL, shapeOfHOLExact]
      rw [if_pos hsh_len] at hret ⊢
      dsimp only at hret ⊢
      set s1 := setVarHOLFinite (ofString "len") (.val (.word lenw)) s with hs1
      rw [evaluateHOLFiniteState_dec_total] at hret ⊢
      dsimp only at hret ⊢
      rcases hload_cap : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
          (.load .one (.op .add [.var .global (ofString "ev"), .const 40#64])) with _ | vcap
      · rw [hload_cap] at hret
        simp at hret
      · simp only [hload_cap] at hret ⊢
        obtain ⟨capw, rfl, _⟩ := evalAt_loadG_word s1 "ev" 40#64 vcap hload_cap
        have hsh_cap : shapeEqHOL .one (shapeOfHOLExact (.val (.word capw))) = true := by
          simp [shapeEqHOL, shapeOfHOLExact]
        rw [if_pos hsh_cap] at hret ⊢
        dsimp only at hret ⊢
        set s2 := setVarHOLFinite (ofString "cap") (.val (.word capw)) s1 with hs2
        have hs2_len : s2.locals.lookup (ofString "len") = some (.val (.word lenw)) := by
          simp [hs2, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "cap" ≠ ofString "len" by decide]
        have hs2_eb : s2.locals.lookup (ofString "expand_by") = some (.val (.word ebw)) := by
          simp [hs2, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, heb,
            show ofString "cap" ≠ ofString "expand_by" by decide,
            show ofString "len" ≠ ofString "expand_by" by decide]
        rw [evaluateHOLFiniteState_dec_total] at hret ⊢
        dsimp only at hret ⊢
        have hnlen_ev : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
            (.op .add [.var .local (ofString "len"), .var .local (ofString "expand_by")]) =
            some (.val (.word (lenw + ebw))) := by
          simp [evalHOLExact, evalListHOLExact, hs2_len, hs2_eb, wordOpHOL, wordOp, valueIsWord, valueWord]
        rw [hnlen_ev] at hret ⊢
        dsimp only at hret ⊢
        set nlenw := lenw + ebw
        have hnlenw_nat : nlenw.toNat = memW s (globN s "ev" + 32) + ebw.toNat := by
          rw [BitVec.toNat_add, hlenw_eq, Nat.mod_eq_of_lt (by omega)]
        have hsh_nlen : shapeEqHOL .one (shapeOfHOLExact (.val (.word nlenw))) = true := by
          simp [shapeEqHOL, shapeOfHOLExact]
        rw [if_pos hsh_nlen] at hret ⊢
        dsimp only at hret ⊢
        set s3 := setVarHOLFinite (ofString "nlen") (.val (.word nlenw)) s2 with hs3
        have hs3_nlen : s3.locals.lookup (ofString "nlen") = some (.val (.word nlenw)) := by
          simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hs3_cap : s3.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
          simp [hs3, hs2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "nlen" ≠ ofString "cap" by decide]
        rw [evaluateHOLFiniteState_seq_line780] at hret ⊢
        rcases hgrow_ev : evaluateHOLFiniteState s3
            (.ite (.cmp .lower (.var .local (ofString "cap")) (.var .local (ofString "nlen"))) growBranch .skip)
            with ⟨rg, sg⟩
        simp only [hgrow_ev] at hret ⊢
        cases rg with
        | some rg0 =>
          dsimp only at hret
          injection hret with hret0
          subst hret0
          exfalso
          rw [evaluateHOLFiniteState_ite] at hgrow_ev
          have hcmp_grow : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
              (.cmp .lower (.var .local (ofString "cap")) (.var .local (ofString "nlen"))) =
              some (.val (.word (if capw < nlenw then 1 else 0))) := by
            simp [evalHOLExact, hs3_cap, hs3_nlen, Compiler.Encoders.Asm.wordCmpHOL]
          rw [hcmp_grow] at hgrow_ev
          dsimp only at hgrow_ev
          by_cases hgrow : capw < nlenw
          · simp only [hgrow, ↓reduceIte, show ¬ ((1 : BitVec 64) = 0) by decide] at hgrow_ev
            dsimp only [growBranch] at hgrow_ev
            rw [evaluateHOLFiniteState_dec_total] at hgrow_ev
            dsimp only at hgrow_ev
            have hmul2 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
                (.panop .mul [.var .local (ofString "cap"), .const 2#64]) =
                some (.val (.word (capw * 2#64))) := by
              simp [evalHOLExact, evalListHOLExact, hs3_cap, panOpHOL, valueIsWord, valueWord]
            have hsh_ncap : shapeEqHOL .one (shapeOfHOLExact (.val (.word (capw * 2#64)))) = true := by
              simp [shapeEqHOL, shapeOfHOLExact]
            rw [hmul2] at hgrow_ev; dsimp only at hgrow_ev
            rw [if_pos hsh_ncap] at hgrow_ev
            set g1 := setVarHOLFinite (ofString "ncap") (.val (.word (capw * 2#64))) s3
            rw [evaluateHOLFiniteState_seq_line780] at hgrow_ev
            rcases hg_ite : evaluateHOLFiniteState g1
                (.ite (.cmp .lower (.var .local (ofString "ncap")) (.var .local (ofString "nlen")))
                  (.assign .local (ofString "ncap") (.op .add [.var .local (ofString "nlen"), .const 1024#64]))
                  .skip) with ⟨rg2, g2⟩
            rw [hg_ite] at hgrow_ev
            cases rg2 with
            | some rg20 =>
              dsimp only at hgrow_ev
              injection hgrow_ev with hg0 _
              injection hg0 with hg0'
              subst hg0'
              rw [evaluateHOLFiniteState_ite] at hg_ite
              revert hg_ite
              split
              · split
                · rw [evaluateHOLFiniteState_skip]; intro h; cases h
                · rw [evaluateHOLFiniteState_assign]
                  split
                  · intro h; cases h
                  · split <;> (intro h; cases h)
              · intro h; cases h
            | none =>
              dsimp only at hgrow_ev
              rw [evaluateHOLFiniteState_seq_line780] at hgrow_ev
              rcases hg_fma : evaluateHOLFiniteState g2
                  (.call (some (none, none)) (ofString "frame_mem_alloc")
                    [.op .sub [.var .local (ofString "ncap"), .var .local (ofString "cap")]]) with ⟨rg3, g3⟩
              rw [hg_fma] at hgrow_ev
              cases rg3 with
              | some rg30 =>
                dsimp only at hgrow_ev
                injection hgrow_ev with hg0 _
                injection hg0 with hg0'
                subst hg0'
                exact call_void_not_returned_g08 hg_fma
              | none =>
                dsimp only at hgrow_ev
                rw [evaluateHOLFiniteState_seq_line780] at hgrow_ev
                rcases hg_mz : evaluateHOLFiniteState g3
                    (.call (some (none, none)) (ofString "memzero")
                      [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "cap")],
                       .op .sub [.var .local (ofString "ncap"), .var .local (ofString "cap")]]) with ⟨rg4, g4⟩
                rw [hg_mz] at hgrow_ev
                cases rg4 with
                | some rg40 =>
                  dsimp only at hgrow_ev
                  injection hgrow_ev with hg0 _
                  injection hg0 with hg0'
                  subst hg0'
                  exact call_void_not_returned_g08 hg_mz
                | none =>
                  dsimp only at hgrow_ev
                  rcases hg_st : evaluateHOLFiniteState g4
                      (.store (.op .add [.var .global (ofString "ev"), .const 40#64]) (.var .local (ofString "ncap"))) with ⟨rg5, g5⟩
                  rw [hg_st] at hgrow_ev
                  cases rg5 with
                  | some rg50 =>
                    dsimp only at hgrow_ev
                    injection hgrow_ev with hg0 _
                    injection hg0 with hg0'
                    subst hg0'
                    have herr := store_some_eq_error_g08 hg_st
                    cases herr
                  | none =>
                    cases hgrow_ev
          · simp only [hgrow, ↓reduceIte, evaluateHOLFiniteState_skip] at hgrow_ev
            cases hgrow_ev
        | none =>
          dsimp only at hret ⊢
          have hsg_nl : sg.locals.lookup (ofString "nlen") = some (.val (.word nlenw)) := by
            rw [evaluateHOLFiniteState_ite] at hgrow_ev
            have hcmp_grow : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
                (.cmp .lower (.var .local (ofString "cap")) (.var .local (ofString "nlen"))) =
                some (.val (.word (if capw < nlenw then 1 else 0))) := by
              simp [evalHOLExact, hs3_cap, hs3_nlen, Compiler.Encoders.Asm.wordCmpHOL]
            rw [hcmp_grow] at hgrow_ev
            dsimp only at hgrow_ev
            by_cases hgrow : capw < nlenw
            · simp only [hgrow, ↓reduceIte, show ¬ ((1 : BitVec 64) = 0) by decide] at hgrow_ev
              dsimp only [growBranch] at hgrow_ev
              rw [evaluateHOLFiniteState_dec_total] at hgrow_ev
              dsimp only at hgrow_ev
              have hmul2 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
                  (.panop .mul [.var .local (ofString "cap"), .const 2#64]) =
                  some (.val (.word (capw * 2#64))) := by
                simp [evalHOLExact, evalListHOLExact, hs3_cap, panOpHOL, valueIsWord, valueWord]
              have hsh_ncap : shapeEqHOL .one (shapeOfHOLExact (.val (.word (capw * 2#64)))) = true := by
                simp [shapeEqHOL, shapeOfHOLExact]
              rw [hmul2] at hgrow_ev; dsimp only at hgrow_ev
              rw [if_pos hsh_ncap] at hgrow_ev
              set g1 := setVarHOLFinite (ofString "ncap") (.val (.word (capw * 2#64))) s3
              have hg1_nl : g1.locals.lookup (ofString "nlen") = some (.val (.word nlenw)) := by
                simp [g1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_nlen,
                  show ofString "ncap" ≠ ofString "nlen" by decide]
              rw [evaluateHOLFiniteState_seq_line780] at hgrow_ev
              rcases hg_ite : evaluateHOLFiniteState g1
                  (.ite (.cmp .lower (.var .local (ofString "ncap")) (.var .local (ofString "nlen")))
                    (.assign .local (ofString "ncap") (.op .add [.var .local (ofString "nlen"), .const 1024#64]))
                    .skip) with ⟨rg2, g2⟩
              rw [hg_ite] at hgrow_ev
              cases rg2 with
              | some _ => cases hgrow_ev
              | none =>
                dsimp only at hgrow_ev
                have hg2_nl : g2.locals.lookup (ofString "nlen") = some (.val (.word nlenw)) := by
                  rw [evaluateHOLFiniteState_ite] at hg_ite
                  revert hg_ite
                  split
                  · split
                    · rw [evaluateHOLFiniteState_skip]
                      intro h; injection h with _ hp; subst hp; exact hg1_nl
                    · rw [evaluateHOLFiniteState_assign]
                      split
                      · intro h; cases h
                      · split
                        · intro h; injection h with _ hp; subst hp
                          simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hg1_nl,
                            show ofString "ncap" ≠ ofString "nlen" by decide]
                        · intro h; cases h
                  · intro h; cases h
                rw [evaluateHOLFiniteState_seq_line780] at hgrow_ev
                rcases hg_fma : evaluateHOLFiniteState g2
                    (.call (some (none, none)) (ofString "frame_mem_alloc")
                      [.op .sub [.var .local (ofString "ncap"), .var .local (ofString "cap")]]) with ⟨rg3, g3⟩
                rw [hg_fma] at hgrow_ev
                cases rg3 with
                | some _ => cases hgrow_ev
                | none =>
                  dsimp only at hgrow_ev
                  have hg3_loc := call_void_preserves_locals_g08 hg_fma
                  rw [evaluateHOLFiniteState_seq_line780] at hgrow_ev
                  rcases hg_mz : evaluateHOLFiniteState g3
                      (.call (some (none, none)) (ofString "memzero")
                        [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "cap")],
                         .op .sub [.var .local (ofString "ncap"), .var .local (ofString "cap")]]) with ⟨rg4, g4⟩
                  rw [hg_mz] at hgrow_ev
                  cases rg4 with
                  | some _ => cases hgrow_ev
                  | none =>
                    dsimp only at hgrow_ev
                    have hg4_loc := call_void_preserves_locals_g08 hg_mz
                    rcases hg_st : evaluateHOLFiniteState g4
                        (.store (.op .add [.var .global (ofString "ev"), .const 40#64]) (.var .local (ofString "ncap"))) with ⟨rg5, g5⟩
                    rw [hg_st] at hgrow_ev
                    cases rg5 with
                    | some _ => cases hgrow_ev
                    | none =>
                      dsimp only at hgrow_ev
                      have hg5_loc := (store_preserves_locals_globals_g08 hg_st).1
                      injection hgrow_ev with _ hp
                      subst hp
                      dsimp only
                      rw [resVarEq_lookup_ne_g08 _ _ _ _ (by decide), hg5_loc, hg4_loc, hg3_loc]
                      exact hg2_nl
            · simp only [hgrow, ↓reduceIte, evaluateHOLFiniteState_skip] at hgrow_ev
              injection hgrow_ev with _ hp
              subst hp
              exact hs3_nlen
          dsimp only [tailProg] at hret ⊢
          rw [evaluateHOLFiniteState_seq_line780] at hret ⊢
          rcases hmz_tail : evaluateHOLFiniteState sg
              (.call (some (none, none)) (ofString "memzero")
                [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "len")],
                 .var .local (ofString "expand_by")]) with ⟨rmz, smz⟩
          simp only [hmz_tail] at hret ⊢
          cases rmz with
          | some rmz0 =>
            dsimp only at hret
            injection hret with hret0
            subst hret0
            exact (call_void_not_returned_g08 hmz_tail).elim
          | none =>
            dsimp only at hret ⊢
            have hsmz_loc := call_void_preserves_locals_g08 hmz_tail
            have hsmz_nl : smz.locals.lookup (ofString "nlen") = some (.val (.word nlenw)) := by
              rw [hsmz_loc]; exact hsg_nl
            rw [evaluateHOLFiniteState_seq_line780] at hret ⊢
            rcases hst32 : evaluateHOLFiniteState smz
                (.store (.op .add [.var .global (ofString "ev"), .const 32#64]) (.var .local (ofString "nlen"))) with ⟨rst, sst⟩
            simp only [hst32] at hret ⊢
            cases rst with
            | some rst0 =>
              dsimp only at hret
              injection hret with hret0
              subst hret0
              have herr := store_some_eq_error_g08 hst32
              cases herr
            | none =>
              dsimp only at hret ⊢
              have hret_ev : evaluateHOLFiniteState sst (.return (.const 0#64)) =
                  (some (.returned (.val (.word 0#64))), sst.emptyLocalsHOLFinite) := by
                rw [evaluateHOLFiniteState_return]
                have hc0 : @evalHOLExact 64 F _ sst.toExact (fun a => Classical.propDecidable (sst.memaddrs a)) (.const 0#64) =
                    some (.val (.word 0#64)) := rfl
                rw [hc0]; dsimp only
                have hsz0 : sizeOfShapeWithContextHOL sst.structs
                    (shapeOfHOLExact (.val (.word 0#64))) ≤ 32 := by
                  simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
                rw [if_pos hsz0]
              have hpost_glob :
                  (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_extend_memory)).2.globals = sst.globals := by
                rw [hbody, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hcmp0]
                dsimp only
                simp only [heb0, ↓reduceIte, evaluateHOLFiniteState_skip]
                rw [evaluateHOLFiniteState_dec_total]; dsimp only
                simp only [hload_len]
                rw [if_pos hsh_len]; dsimp only
                rw [← hs1, evaluateHOLFiniteState_dec_total]; dsimp only
                simp only [hload_cap]
                rw [if_pos hsh_cap]; dsimp only
                rw [← hs2, evaluateHOLFiniteState_dec_total]; dsimp only
                rw [hnlen_ev]; dsimp only
                rw [if_pos hsh_nlen]; dsimp only
                rw [← hs3, evaluateHOLFiniteState_seq_line780, hgrow_ev]; dsimp only
                dsimp only [tailProg]
                rw [evaluateHOLFiniteState_seq_line780, hmz_tail]; dsimp only
                rw [evaluateHOLFiniteState_seq_line780, hst32]; dsimp only
                rw [hret_ev]
                rfl
              have hsmz_glob : smz.globals = sst.globals := (store_preserves_locals_globals_g08 hst32).2.symm
              have hsmz_ev_nat : globN smz "ev" = globN s "ev" := by
                have h1 : globN smz "ev" =
                    globN (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_extend_memory)).2 "ev" :=
                  globN_eq_of_lookup_eq (by rw [hsmz_glob, hpost_glob])
                exact h1.trans hev_eq
              have hsmz_ev_lk : smz.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
                obtain ⟨evw', hevw', hevw'_nat⟩ := global_word_of_pos smz "ev" (by rw [hsmz_ev_nat]; exact hev_pos)
                have hsame : evw' = evw := BitVec.eq_of_toNat_eq (by rw [hevw'_nat, hsmz_ev_nat, hevw_nat])
                subst hsame
                exact hevw'
              obtain ⟨w32, hw32_eq, hsst_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := smz) (post := sst)
                (gname := "ev") (gbase := globN s "ev") (off := 32) hsmz_ev_lk hevw_nat (by omega)
                (fun u hu => by
                  change smz.locals.lookup (ofString "nlen") = some u at hu
                  rw [hsmz_nl] at hu; injection hu with hu'; exact ⟨nlenw, hu'.symm⟩) hst32
              have hw32_nl : w32 = nlenw := by
                change smz.locals.lookup (ofString "nlen") = some (.val (.word w32)) at hw32_eq
                rw [hsmz_nl] at hw32_eq
                simpa using hw32_eq.symm
              subst hw32_nl
              simp only [hret_ev]
              dsimp only [emptyLocalsHOLFinite]
              change memW sst (globN s "ev" + 32) = memW s (globN s "ev" + 32) + ebw.toNat
              rw [hsst_eq, R14Shards.OpHandlersA.memW_updW_same smz (globN s "ev" + 32) nlenw]
              exact hnlenw_nat

private theorem eps_extend_memory_aligned_len_g08 :
    EvmPreservingSpec ExtendMemoryPre
      (fun s _ post =>
        (∀ g : String, ofString g ≠ ofString "frame_mem_ptr" → globN post g = globN s g) ∧
        ∀ ebw : BitVec 64,
          s.locals.lookup (ofString "expand_by") = some (.val (.word ebw)) →
          memW post (globN post "ev" + 32) = memW s (globN s "ev" + 32) + ebw.toNat)
      (ofString "extend_memory") := by
  obtain ⟨params, body, retShape, hlk, hspec⟩ := eps_extend_memory_aligned
  have hlk_eq := lookup_extend_memory.symm.trans hlk
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_eq, rfl⟩
  subst hbody_eq
  refine ⟨_, _, _, lookup_extend_memory, ?_⟩
  intro F s hcode hInv hPre hlookup hnt
  have hs := hspec s hcode hInv hPre hlookup hnt
  dsimp only at hs ⊢
  refine ⟨fun v hv => ?_, hs.2⟩
  obtain ⟨h1, h2, h3, hglob⟩ := hs.1 v hv
  refine ⟨h1, h2, h3, hglob, ?_⟩
  intro ebw heb
  obtain ⟨ebw0, heb0, hcond0⟩ := hPre
  have heb_eq : ebw = ebw0 := by
    rw [heb0] at heb; simpa using heb.symm
  subst heb_eq
  have hbound : ebw = 0#64 ∨ memW s (globN s "ev" + 32) + ebw.toNat < 2 ^ 37 := by
    rcases hcond0 with rfl | ⟨hb, _, _⟩
    · exact Or.inl rfl
    · exact Or.inr hb
  exact extend_memory_return_len_g08 s ebw v hInv heb hbound (hglob "ev" (by decide)) hv

private theorem head_mem_store_address_g08 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hInv : EvmInv s)
    (base start : BitVec 64) (width : Nat)
    (hbase : base.toNat = memW s (globN s "ev" + 24))
    (hwidth : 0 < width)
    (hcoverage : start.toNat + width ≤ memW s (globN s "ev" + 32)) :
    (base + start).toNat = base.toNat + start.toNat ∧
    memW s (globN s "ev" + 24) ≤ (base + start).toNat ∧
    (base + start).toNat + width ≤
      memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) := by
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    simp [evmChain, evmChainFrom]
  have hFW := hInv.2.choose_spec.2.2.2.2.1 _ hhead
  have hcap := hFW.2.2.2.2.2.2.1
  have hmem := hFW.2.1.2
  have hfp := hInv.1.2.2.2.2.1
  have hsp := hInv.1.2.2.2.2.2.1
  have hse := hInv.1.2.2.2.2.2.2.1
  dsimp only at hcap hmem
  have hsum : base.toNat + start.toNat < 2 ^ 64 := by
    rw [R11Shards.scratchEnd_val] at hsp
    omega
  have hadd : (base + start).toNat = base.toNat + start.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hsum]
  exact ⟨hadd, by omega, by omega⟩

private def CalleeBodyRunQ_g08 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (P : PanSemStateFiniteExact 64 F → Prop)
    (R : PanSemStateFiniteExact 64 F → Prop)
    (charged : Bool)
    (prog : ProgHOL 64) : Prop :=
  ∀ (t : PanSemStateFiniteExact 64 F),
    t.code = originalRuntimeCode →
    EvmInv t →
    (evmChain t).length = (evmChain s0).length →
    (if charged then evmR t < evmR s0 else evmR t ≤ evmR s0) →
    P t →
    (evaluateHOLFiniteState t prog).1 ≠ some .timeOut →
    let out := evaluateHOLFiniteState t prog
    ((∃ v, out.1 = some (.returned v)) →
      EvmInv out.2 ∧ (evmChain out.2).length = (evmChain s0).length ∧ evmR out.2 < evmR s0 ∧ R out.2) ∧
    (IsEvmErr out.1 →
      EvmInv out.2 ∧ (evmChain out.2).length = (evmChain s0).length ∧ evmR out.2 ≤ evmR s0) ∧
    (∀ r0, out.1 = some r0 →
      (∀ v, r0 ≠ .returned v) → ¬ IsEvmErr out.1 →
      ∀ v', out.1 ≠ some (.returned v'))

private theorem calleeBodyRunQ_congr_lc_g08 {F : Type}
    {s0 post post' : PanSemStateFiniteExact 64 F}
    {R : PanSemStateFiniteExact 64 F → Prop}
    {r : Option (PanSemResultExact 64)}
    (hp_lc : post' = { post with locals := post'.locals, clock := post'.clock })
    (hR_lc : ∀ (a b : PanSemStateFiniteExact 64 F),
      b = { a with locals := b.locals, clock := b.clock } → R a → R b)
    (h : ((∃ v, r = some (.returned v)) →
           EvmInv post ∧ (evmChain post).length = (evmChain s0).length ∧ evmR post < evmR s0 ∧ R post) ∧
         (IsEvmErr r →
           EvmInv post ∧ (evmChain post).length = (evmChain s0).length ∧ evmR post ≤ evmR s0)) :
    ((∃ v, r = some (.returned v)) →
      EvmInv post' ∧ (evmChain post').length = (evmChain s0).length ∧ evmR post' < evmR s0 ∧ R post') ∧
    (IsEvmErr r →
      EvmInv post' ∧ (evmChain post').length = (evmChain s0).length ∧ evmR post' ≤ evmR s0) := by
  have hp_m : post'.memory = post.memory := by rw [hp_lc]
  have hp_g : post'.globals = post.globals := by rw [hp_lc]
  have hp := evm_congr hp_m hp_g
  have hinv : EvmInv post → EvmInv post' := fun h0 => by
    rw [hp_lc]; exact localsFree_evmInv post post'.locals post'.clock h0
  refine ⟨fun hret => ?_, fun herr => ?_⟩
  · obtain ⟨hi, hlen, hlt, hr⟩ := h.1 hret
    exact ⟨hinv hi, by rw [hp.2.2.1]; exact hlen, by rw [hp.2.1]; exact hlt, hR_lc post post' hp_lc hr⟩
  · obtain ⟨hi, hlen, hR0⟩ := h.2 herr
    exact ⟨hinv hi, by rw [hp.2.2.1]; exact hlen, by rw [hp.2.1]; exact hR0⟩

private theorem calleeBodyRunQ_error_g08 {F : Type} (s0 t : PanSemStateFiniteExact 64 F)
    {R : PanSemStateFiniteExact 64 F → Prop} :
    (((∃ v, (some PanSemResultExact.error : Option (PanSemResultExact 64)) = some (.returned v)) →
      EvmInv t ∧ (evmChain t).length = (evmChain s0).length ∧ evmR t < evmR s0 ∧ R t) ∧
     (IsEvmErr (some PanSemResultExact.error) →
      EvmInv t ∧ (evmChain t).length = (evmChain s0).length ∧ evmR t ≤ evmR s0) ∧
     (∀ r0, (some PanSemResultExact.error : Option (PanSemResultExact 64)) = some r0 →
      (∀ v, r0 ≠ .returned v) → ¬ IsEvmErr (some PanSemResultExact.error) →
      ∀ v', (some PanSemResultExact.error : Option (PanSemResultExact 64)) ≠ some (.returned v'))) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, h⟩; cases h
  · rintro ⟨_, h⟩; cases h
  · intro _ _ _ _ _ h; cases h

private theorem calleeBodyRunQ_other_g08 {F : Type} {s0 t : PanSemStateFiniteExact 64 F}
    {R : PanSemStateFiniteExact 64 F → Prop}
    {r : Option (PanSemResultExact 64)}
    (hnret : ∀ v, r ≠ some (.returned v)) (hnerr : ¬ IsEvmErr r) :
    (((∃ v, r = some (.returned v)) →
      EvmInv t ∧ (evmChain t).length = (evmChain s0).length ∧ evmR t < evmR s0 ∧ R t) ∧
     (IsEvmErr r →
      EvmInv t ∧ (evmChain t).length = (evmChain s0).length ∧ evmR t ≤ evmR s0) ∧
     (∀ r0, r = some r0 → (∀ v, r0 ≠ .returned v) → ¬ IsEvmErr r → ∀ v', r ≠ some (.returned v'))) :=
  ⟨fun ⟨v, hv⟩ => (hnret v hv).elim, fun he => (hnerr he).elim, fun _ _ _ _ v' => hnret v'⟩

private theorem CalleeBodyRunQ_g08.ret {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P R : PanSemStateFiniteExact 64 F → Prop}
    (hPR : ∀ t, P t → R (emptyLocalsHOLFinite t))
    (e : ExpHOL 64) :
    CalleeBodyRunQ_g08 s0 P R true (.return e) := by
  intro t _ hInv hlen hR hP _
  simp only [↓reduceIte] at hR
  dsimp only
  rw [evaluateHOLFiniteState_return]
  split
  · exact calleeBodyRunQ_error_g08 s0 t
  · split
    · have hInv' : EvmInv (emptyLocalsHOLFinite t) :=
        localsFree_evmInv t (emptyLocalsHOLFinite t).locals t.clock hInv
      have hc := evm_congr (s := t) (t := emptyLocalsHOLFinite t) rfl rfl
      refine ⟨fun _ => ⟨hInv', by rw [hc.2.2.1]; exact hlen, by rw [hc.2.1]; exact hR, hPR t hP⟩, ?_, ?_⟩
      · rintro ⟨_, h⟩; cases h
      · intro r0 hr hnr _ _
        injection hr with hr'
        subst hr'
        exact (hnr _ rfl).elim
    · exact calleeBodyRunQ_error_g08 s0 t

private theorem CalleeBodyRunQ_g08.decCall {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q R : PanSemStateFiniteExact 64 F → Prop}
    {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    {charged : Bool}
    {nm : MlS} {sh : ShapeHOL} {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hR_lc : ∀ (a b : PanSemStateFiniteExact 64 F),
      b = { a with locals := b.locals, clock := b.clock } → R a → R b)
    (hf : EvmPreservingSpec Pc Qc fname)
    (hentry : ∀ t values body' callee ret',
      t.code = originalRuntimeCode → EvmInv t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite t.code.lookup fname values = some (body', callee, ret') →
      Pc (callEntryStateHOLFinite t callee))
    (hstep : ∀ t values body callee retShape v cpost,
      EvmInv t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, callee, retShape) →
      EvmInv cpost → evmChain cpost = evmChain (callEntryStateHOLFinite t callee) →
      Qc (callEntryStateHOLFinite t callee) v cpost →
      Q (setVarHOLFinite nm v { cpost with locals := t.locals }))
    (hcont : CalleeBodyRunQ_g08 s0 Q R charged cont) :
    CalleeBodyRunQ_g08 s0 P R charged (.decCall nm sh fname args cont) := by
  intro t hc hInv hlen hR hP hnt
  obtain ⟨params, body, retShape, hlook, hspec⟩ := hf
  dsimp only
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args with _ | values
  · exact calleeBodyRunQ_error_g08 s0 t
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact calleeBodyRunQ_error_g08 s0 t
    · simp only [hl] at hnt ⊢
      by_cases hz : t.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
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
        have hInv_ce : EvmInv (callEntryStateHOLFinite t callee) := localsFree_evmInv t callee (t.clock - 1) hInv
        have hPc : Pc (callEntryStateHOLFinite t callee) := hentry t values body callee retShape hc hInv hP hargs hl
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
            some (body, callee, retShape) := by rwa [← hc]
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite t callee) body).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body with ⟨res, cpost⟩
        simp only [hrun] at hnt hmeta ⊢
        change cpost.code = t.code at hmeta
        have hc_ce := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
        have hQ (hsafe : res ≠ some .timeOut) :
            (∀ v, res = some (.returned v) →
              EvmInv cpost ∧ evmChain cpost = evmChain (callEntryStateHOLFinite t callee) ∧
              evmR cpost ≤ evmR (callEntryStateHOLFinite t callee) ∧
              Qc (callEntryStateHOLFinite t callee) v cpost) ∧
            (IsEvmErr res →
              EvmInv cpost ∧ evmChain cpost = evmChain (callEntryStateHOLFinite t callee) ∧
              evmR cpost ≤ evmR (callEntryStateHOLFinite t callee)) := by
          have hs := hspec (callEntryStateHOLFinite t callee) hc hInv_ce hPc ⟨values, hl_orig⟩
            (by rw [hrun]; exact hsafe)
          dsimp only at hs; rw [hrun] at hs; exact hs
        cases res with
        | none => exact calleeBodyRunQ_error_g08 s0 cpost
        | some r0 =>
          cases r0 with
          | timeOut => simp at hnt
          | returned v =>
            dsimp only at hnt ⊢
            split
            · rename_i hsh_ok
              rw [if_pos hsh_ok] at hnt
              obtain ⟨hInv_cp, hch_cp, hR_cp, hQc_cp⟩ := (hQ (by simp)).1 v rfl
              let resumed := setVarHOLFinite nm v { cpost with locals := t.locals }
              have hcode_res : resumed.code = originalRuntimeCode := hmeta.trans hc
              have hInv_res : EvmInv resumed := localsFree_evmInv cpost resumed.locals cpost.clock hInv_cp
              have hc_res := evm_congr (s := cpost) (t := resumed) rfl rfl
              have hlen_res : (evmChain resumed).length = (evmChain s0).length := by
                rw [hc_res.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              have hR_res : if charged then evmR resumed < evmR s0 else evmR resumed ≤ evmR s0 := by
                cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at hR ⊢ <;>
                  (rw [hc_res.2.1]; rw [hc_ce.2.1] at hR_cp; omega)
              have hQ_res : Q resumed := hstep t values body callee retShape v cpost hInv hP hargs hl_orig hInv_cp hch_cp hQc_cp
              have hb := hcont resumed hcode_res hInv_res hlen_res hR_res hQ_res (by simpa [resumed] using hnt)
              dsimp only at hb
              refine ⟨?_, ?_, fun r1 hr1 hnr1 hnerr1 v' => hb.2.2 r1 hr1 hnr1 hnerr1 v'⟩
              · exact (calleeBodyRunQ_congr_lc_g08 rfl hR_lc ⟨hb.1, hb.2.1⟩).1
              · exact (calleeBodyRunQ_congr_lc_g08 rfl hR_lc ⟨hb.1, hb.2.1⟩).2
            · exact calleeBodyRunQ_error_g08 s0 cpost
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨hInv_cp, hch_cp, hR_cp⟩ := (hQ (by simp)).2 ⟨ev, rfl⟩
              have hInv_el : EvmInv cpost.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost _ cpost.clock hInv_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              have hR_le : evmR t ≤ evmR s0 := by
                cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at hR <;> omega
              refine ⟨?_, fun _ => ⟨hInv_el, ?_, ?_⟩, ?_⟩
              · rintro ⟨_, h⟩; cases h
              · rw [hc_el.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              · rw [hc_el.2.1]; rw [hc_ce.2.1] at hR_cp; omega
              · intro _ _ _ _ _ h; cases h
            · refine calleeBodyRunQ_other_g08 (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => exact calleeBodyRunQ_error_g08 s0 cpost
          | «continue» => exact calleeBodyRunQ_error_g08 s0 cpost
          | finalFfi f =>
            refine calleeBodyRunQ_other_g08 (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => exact calleeBodyRunQ_error_g08 s0 cpost.emptyLocalsHOLFinite

private theorem CalleeBodyRunQ_g08.seq_call {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q R : PanSemStateFiniteExact 64 F → Prop}
    {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    {charged : Bool}
    {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hf : EvmPreservingSpec Pc Qc fname)
    (hentry : ∀ t values body' callee ret',
      t.code = originalRuntimeCode → EvmInv t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite t.code.lookup fname values = some (body', callee, ret') →
      Pc (callEntryStateHOLFinite t callee))
    (hstep : ∀ t values body callee retShape v cpost,
      EvmInv t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, callee, retShape) →
      EvmInv cpost → evmChain cpost = evmChain (callEntryStateHOLFinite t callee) →
      Qc (callEntryStateHOLFinite t callee) v cpost →
      Q { cpost with locals := t.locals })
    (hcont : CalleeBodyRunQ_g08 s0 Q R charged cont) :
    CalleeBodyRunQ_g08 s0 P R charged (.seq (.call (some (none, none)) fname args) cont) := by
  intro t hc hInv hlen hR hP hnt
  obtain ⟨params, body, retShape, hlook, hspec⟩ := hf
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args with _ | values
  · exact calleeBodyRunQ_error_g08 s0 t
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact calleeBodyRunQ_error_g08 s0 t
    · simp only [hl] at hnt ⊢
      by_cases hz : t.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
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
        have hInv_ce : EvmInv (callEntryStateHOLFinite t callee) := localsFree_evmInv t callee (t.clock - 1) hInv
        have hPc : Pc (callEntryStateHOLFinite t callee) := hentry t values body callee retShape hc hInv hP hargs hl
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
            some (body, callee, retShape) := by rwa [← hc]
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite t callee) body).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body with ⟨res, cpost⟩
        simp only [hrun] at hnt hmeta ⊢
        change cpost.code = t.code at hmeta
        have hc_ce := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
        have hQ (hsafe : res ≠ some .timeOut) :
            (∀ v, res = some (.returned v) →
              EvmInv cpost ∧ evmChain cpost = evmChain (callEntryStateHOLFinite t callee) ∧
              evmR cpost ≤ evmR (callEntryStateHOLFinite t callee) ∧
              Qc (callEntryStateHOLFinite t callee) v cpost) ∧
            (IsEvmErr res →
              EvmInv cpost ∧ evmChain cpost = evmChain (callEntryStateHOLFinite t callee) ∧
              evmR cpost ≤ evmR (callEntryStateHOLFinite t callee)) := by
          have hs := hspec (callEntryStateHOLFinite t callee) hc hInv_ce hPc ⟨values, hl_orig⟩
            (by rw [hrun]; exact hsafe)
          dsimp only at hs; rw [hrun] at hs; exact hs
        cases res with
        | none => exact calleeBodyRunQ_error_g08 s0 cpost
        | some r0 =>
          cases r0 with
          | timeOut => simp at hnt
          | returned v =>
            by_cases hsh_ok : shapeEqHOL (shapeOfHOLExact v) retShape = true
            · simp only [hsh_ok, ↓reduceIte] at hnt ⊢
              obtain ⟨hInv_cp, hch_cp, hR_cp, hQc_cp⟩ := (hQ (by simp)).1 v rfl
              let resumed : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
              have hcode_res : resumed.code = originalRuntimeCode := hmeta.trans hc
              have hInv_res : EvmInv resumed := localsFree_evmInv cpost t.locals cpost.clock hInv_cp
              have hc_res := evm_congr (s := cpost) (t := resumed) rfl rfl
              have hlen_res : (evmChain resumed).length = (evmChain s0).length := by
                rw [hc_res.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              have hR_res : if charged then evmR resumed < evmR s0 else evmR resumed ≤ evmR s0 := by
                cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at hR ⊢ <;>
                  (rw [hc_res.2.1]; rw [hc_ce.2.1] at hR_cp; omega)
              have hQ_res : Q resumed := hstep t values body callee retShape v cpost hInv hP hargs hl_orig hInv_cp hch_cp hQc_cp
              exact hcont resumed hcode_res hInv_res hlen_res hR_res hQ_res (by simpa [resumed] using hnt)
            · simp only [hsh_ok, Bool.false_eq_true, ↓reduceIte]
              exact calleeBodyRunQ_error_g08 s0 cpost
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨hInv_cp, hch_cp, hR_cp⟩ := (hQ (by simp)).2 ⟨ev, rfl⟩
              have hInv_el : EvmInv cpost.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost _ cpost.clock hInv_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              have hR_le : evmR t ≤ evmR s0 := by
                cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at hR <;> omega
              refine ⟨?_, fun _ => ⟨hInv_el, ?_, ?_⟩, ?_⟩
              · rintro ⟨_, h⟩; cases h
              · rw [hc_el.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              · rw [hc_el.2.1]; rw [hc_ce.2.1] at hR_cp; omega
              · intro _ _ _ _ _ h; cases h
            · refine calleeBodyRunQ_other_g08 (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => exact calleeBodyRunQ_error_g08 s0 cpost
          | «continue» => exact calleeBodyRunQ_error_g08 s0 cpost
          | finalFfi f =>
            refine calleeBodyRunQ_other_g08 (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => exact calleeBodyRunQ_error_g08 s0 cpost.emptyLocalsHOLFinite

private theorem CalleeBodyRunQ_g08.seq_charge_gas_preserves_headMem {F : Type}
    {s0 : PanSemStateFiniteExact 64 F}
    {P Q R : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {amtExp : ExpHOL 64} {cont : ProgHOL 64}
    (hpos : ∀ t (w : BitVec 64),
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp =
        some (.val (.word w)) →
      EvmInv t → P t → 0 < w.toNat)
    (hstep : ∀ t (amtw : BitVec 64) cpost,
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp =
        some (.val (.word amtw)) →
      amtw.toNat < 2 ^ 64 - 1 →
      EvmInv t → P t → EvmInv cpost → cpost.globals = t.globals →
      evmChain cpost = evmChain t →
      (∀ off : Nat, off ∈ ([24, 32, 40] : List Nat) →
        memW cpost (globN t "ev" + off) = memW t (globN t "ev" + off)) →
      Q { cpost with locals := t.locals })
    (hcont : CalleeBodyRunQ_g08 s0 Q R true cont) :
    CalleeBodyRunQ_g08 s0 P R charged (.seq (.call (some (none, none)) (ofString "charge_gas") [amtExp]) cont) := by
  intro t hc hInv hlen hR hP hnt
  have hR_le : evmR t ≤ evmR s0 := by
    cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at hR <;> omega
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) [amtExp] with _ | values
  · exact calleeBodyRunQ_error_g08 s0 t
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup (ofString "charge_gas") values with _ | ⟨body', callee, ret'⟩
    · exact calleeBodyRunQ_error_g08 s0 t
    · simp only [hl] at hnt ⊢
      by_cases hz : t.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hv_list : ∃ v0, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp = some v0 ∧ values = [v0] := by
          rw [evalListHOLFinite_eq_toExact] at hargs
          simp only [evalListHOLExact] at hargs
          rcases he : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp with _ | v0
          · simp [he] at hargs
          · simp only [he, Option.some.injEq] at hargs; exact ⟨v0, rfl, hargs.symm⟩
        obtain ⟨v0, hv0_ev, rfl⟩ := hv_list
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "charge_gas") [v0] =
            some (body', callee, ret') := by rwa [← hc]
        obtain ⟨rfl, rfl, amtw, rfl, hamt_cal⟩ := one_word_arg_lookup M21.lookup_charge_gas hl_orig
        have hamt_pos : 0 < amtw.toNat := hpos t amtw hv0_ev hInv hP
        have hInv_ce : EvmInv (callEntryStateHOLFinite t callee) := localsFree_evmInv t callee (t.clock - 1) hInv
        have hc_ce := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
          (callEntryStateHOLFinite t callee) (sourceFnBody Guest.Software.guestFn_charge_gas)).1
        have hcg := charge_gas_body_exact (callEntryStateHOLFinite t callee) hInv_ce hamt_cal
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee)
            (sourceFnBody Guest.Software.guestFn_charge_gas) with ⟨res, cpost⟩
        simp only [hrun] at hnt hmeta hcg ⊢
        let ce := callEntryStateHOLFinite t callee
        change cpost.code = t.code at hmeta
        cases res with
        | none => exact calleeBodyRunQ_error_g08 s0 cpost
        | some r0 =>
          cases r0 with
          | timeOut => simp at hnt
          | returned v =>
            by_cases hsh_ok : shapeEqHOL (shapeOfHOLExact v) .one = true
            · simp only [hsh_ok, ↓reduceIte] at hnt ⊢
              obtain ⟨hInv_cp, hglob_cp, hch_cp, hR_cp⟩ := hcg.1 v rfl
              have hamt_lt : amtw.toNat < 2 ^ 64 - 1 :=
                charge_gas_return_lt_sentinel_g08 ce hInv_ce hamt_cal (by rw [hrun])
              have hmem_head_cp : ∀ off : Nat, off ∈ ([24, 32, 40] : List Nat) →
                  memW cpost (globN t "ev" + off) = memW t (globN t "ev" + off) := by
                intro off hoff
                have hhead_mem : (globN t "ev", globN t "cur_cont") ∈ evmChain t := by simp [evmChain, evmChainFrom]
                have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead_mem
                have hb_ev := (frameWF_bounds hInv.1.2 hFW0).1
                dsimp only at hb_ev
                have hev_pos : 0 < globN t "ev" := by
                  obtain ⟨hin, _⟩ := (hFW0.1 (globN t "ev", 280) (by simp)).1
                  have h1 := hInv.1.2.2.2.1; have h2 := hInv.1.2.2.2.2.1
                  rw [R11Shards.scratchStart_val] at h1; dsimp only at hin; omega
                obtain ⟨evw, hevw, hevw_nat⟩ := global_word_of_pos t "ev" hev_pos
                have hevw_ce : ce.globals.lookup (ofString "ev") = some (.val (.word evw)) := hevw
                have hbody_cg : sourceFnBody Guest.Software.guestFn_charge_gas =
                    .dec (ofString "gl") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 64]))
                      (.seq
                        (.ite (.cmp .lower (.var .local (ofString "gl")) (.var .local (ofString "amount")))
                          (.raise (ofString "EvmErr") (.const 4))
                          .skip)
                        (.seq
                          (.store (.op .add [.var .global (ofString "ev"), .const 64])
                            (.op .sub [.var .local (ofString "gl"), .var .local (ofString "amount")]))
                          (.seq
                            (.store (.op .add [.var .global (ofString "ev"), .const 184])
                              (.op .add
                                [.load .one (.op .add [.var .global (ofString "ev"), .const 184]),
                                 .var .local (ofString "amount")]))
                            (.return (.const 0))))) := rfl
                have hmem_ne : ∀ x : BitVec 64,
                    x ≠ BitVec.ofNat 64 (globN t "ev" + 64) →
                    x ≠ BitVec.ofNat 64 (globN t "ev" + 184) →
                    cpost.memory x = t.memory x := by
                  have hrun' := hrun
                  rw [hbody_cg, evaluateHOLFiniteState_dec_total] at hrun'; dsimp only at hrun'
                  split at hrun'
                  · simp at hrun'
                  · rename_i glv _
                    split at hrun'
                    · set s1 := setVarHOLFinite (ofString "gl") glv ce
                      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hrun'
                      split at hrun'
                      · split at hrun'
                        · simp only [evaluateHOLFiniteState_skip] at hrun'
                          rw [evaluateHOLFiniteState_seq_line780] at hrun'
                          rcases hst1 : evaluateHOLFiniteState s1
                              (.store (.op .add [.var .global (ofString "ev"), .const 64])
                                (.op .sub [.var .local (ofString "gl"), .var .local (ofString "amount")])) with ⟨r1, s2⟩
                          rw [hst1] at hrun'
                          cases r1 with
                          | some res1 =>
                            have herr1 := store_some_eq_error_g08 hst1; subst herr1; simp at hrun'
                          | none =>
                            dsimp only at hrun'
                            obtain ⟨w1, _, hs2_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s1) (post := s2)
                              (gname := "ev") (gbase := globN t "ev") (off := 64) hevw_ce hevw_nat (by omega)
                              (fun u hu => by
                                simp only [evalHOLExact, wordOpHOL] at hu; revert hu
                                rcases @evalListHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a)) _ with _ | vs
                                · simp
                                · dsimp only; split
                                  · simp only [Option.map]
                                    rcases wordOp .sub (vs.map valueWord) with _ | w
                                    · simp
                                    · intro h'; injection h' with h''; exact ⟨w, h''.symm⟩
                                  · simp) hst1
                            rw [evaluateHOLFiniteState_seq_line780] at hrun'
                            rcases hst2 : evaluateHOLFiniteState s2
                                (.store (.op .add [.var .global (ofString "ev"), .const 184])
                                  (.op .add
                                    [.load .one (.op .add [.var .global (ofString "ev"), .const 184]),
                                     .var .local (ofString "amount")])) with ⟨r2, s3⟩
                            rw [hst2] at hrun'
                            cases r2 with
                            | some res2 =>
                              have herr2 := store_some_eq_error_g08 hst2; subst herr2; simp at hrun'
                            | none =>
                              dsimp only at hrun'
                              obtain ⟨w2, _, hs3_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s2) (post := s3)
                                (gname := "ev") (gbase := globN t "ev") (off := 184)
                                (by rw [hs2_eq]; exact hevw_ce) hevw_nat (by omega)
                                (fun u hu => by
                                  simp only [evalHOLExact, wordOpHOL] at hu; revert hu
                                  rcases @evalListHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a)) _ with _ | vs
                                  · simp
                                  · dsimp only; split
                                    · simp only [Option.map]
                                      rcases wordOp .add (vs.map valueWord) with _ | w
                                      · simp
                                      · intro h'; injection h' with h''; exact ⟨w, h''.symm⟩
                                    · simp) hst2
                              rw [evaluateHOLFiniteState_return] at hrun'; dsimp only [evalHOLExact] at hrun'
                              have hsz0 : sizeOfShapeWithContextHOL s3.structs
                                  (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
                                simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
                              rw [if_pos hsz0] at hrun'; dsimp only at hrun'
                              injection hrun' with _ hcpost_eq
                              subst hcpost_eq
                              intro x hx64 hx184
                              dsimp only [emptyLocalsHOLFinite]
                              rw [hs3_eq]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hx184]
                              rw [hs2_eq]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hx64]
                              rfl
                        · rcases hraise : evaluateHOLFiniteState s1 (.raise (ofString "EvmErr") (.const 4)) with ⟨rr, sr⟩
                          rw [hraise] at hrun'
                          have hr_nn : rr ≠ none := by
                            rw [evaluateHOLFiniteState_raise] at hraise; dsimp only [evalHOLExact] at hraise
                            split at hraise
                            · split at hraise <;> (injection hraise with h1 _; subst h1; simp)
                            · injection hraise with h1 _; subst h1; simp
                          cases rr with
                          | none => exact absurd rfl hr_nn
                          | some r0 =>
                            dsimp only at hrun'
                            have hr_not_ret : ∀ vr, r0 ≠ .returned vr := by
                              rw [evaluateHOLFiniteState_raise] at hraise; dsimp only [evalHOLExact] at hraise
                              split at hraise
                              · split at hraise <;> (injection hraise with h1 _; injection h1 with h1'; subst h1'; simp)
                              · injection hraise with h1 _; injection h1 with h1'; subst h1'; simp
                            cases r0 with
                            | returned vr => exact absurd rfl (hr_not_ret vr)
                            | _ => simp at hrun'
                      · simp at hrun'
                    · simp at hrun'
                have hne64 : BitVec.ofNat 64 (globN t "ev" + off) ≠ BitVec.ofNat 64 (globN t "ev" + 64) := by
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
                  intro heq; have htn := congrArg BitVec.toNat heq
                  rcases hoff with rfl | rfl | rfl <;>
                    (rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at htn; omega)
                have hne184 : BitVec.ofNat 64 (globN t "ev" + off) ≠ BitVec.ofNat 64 (globN t "ev" + 184) := by
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
                  intro heq; have htn := congrArg BitVec.toNat heq
                  rcases hoff with rfl | rfl | rfl <;>
                    (rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at htn; omega)
                unfold memW; rw [hmem_ne _ hne64 hne184]
              let resumed : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
              have hInv_res : EvmInv resumed := localsFree_evmInv cpost t.locals cpost.clock hInv_cp
              have hc_res := evm_congr (s := cpost) (t := resumed) rfl rfl
              have hlen_res : (evmChain resumed).length = (evmChain s0).length := by
                rw [hc_res.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              have hR_lt : evmR resumed < evmR s0 := by
                rw [hc_res.2.1]; rw [hc_ce.2.1] at hR_cp; omega
              exact hcont resumed (hmeta.trans hc) hInv_res hlen_res (by simp [hR_lt])
                (hstep t amtw cpost hv0_ev hamt_lt hInv hP hInv_cp hglob_cp (hch_cp.trans (evmChain_congr rfl rfl)) hmem_head_cp)
                (by simpa [resumed] using hnt)
            · simp only [hsh_ok, Bool.false_eq_true, ↓reduceIte]
              exact calleeBodyRunQ_error_g08 s0 cpost
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨hInv_cp, _, hch_cp, hR_cp⟩ := hcg.2 ⟨ev, rfl⟩
              have hInv_el : EvmInv cpost.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost _ cpost.clock hInv_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              refine ⟨?_, fun _ => ⟨hInv_el, ?_, ?_⟩, ?_⟩
              · rintro ⟨_, h⟩; cases h
              · rw [hc_el.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              · rw [hc_el.2.1, hR_cp, hc_ce.2.1]; exact hR_le
              · intro _ _ _ _ _ h; cases h
            · refine calleeBodyRunQ_other_g08 (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => exact calleeBodyRunQ_error_g08 s0 cpost
          | «continue» => exact calleeBodyRunQ_error_g08 s0 cpost
          | finalFfi f =>
            refine calleeBodyRunQ_other_g08 (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => exact calleeBodyRunQ_error_g08 s0 cpost.emptyLocalsHOLFinite

private theorem seq_call_strict_q_g08 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop}
    {Pc : PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop}
    {R : PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop}
    {charged : Bool}
    {fname : MlS} {params : List (MlS × ShapeHOL)} {body : ProgHOL 64}
    {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hlook : originalRuntimeCode.lookup fname = some (params, body, .one))
    (hentry : ∀ t values callee,
      t.code = originalRuntimeCode → EvmInv t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, callee, .one) →
      Pc t (callEntryStateHOLFinite t callee))
    (hbody : ∀ t, P t → CalleeBodyRunQ_g08 s0 (Pc t) (R t) charged body)
    (hstep : ∀ t cpost, EvmInv t → P t → EvmInv cpost → R t cpost → Q { cpost with locals := t.locals })
    (hcont : HandlerRun s0 Q true cont) :
    HandlerRun s0 P charged (.seq (.call (some (none, none)) fname args) cont) := by
  intro t hc hInv hlen hR hP hnt
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args with _ | values
  · exact opDispatchPost_error s0 t
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact opDispatchPost_error s0 t
    · simp only [hl] at hnt ⊢
      by_cases hz : t.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hbody_eq : body' = body :=
          lookupCodeHOLFinite_installed_body t.code.lookup fname params body body'
            .one ret' values callee (by rw [hc]; exact hlook) hl
        subst body'
        have hret_eq : ret' = .one := by
          have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
            t.code.lookup fname values body callee ret' hl
          rw [hc] at hx; simp only [Flapjack.lookupCodeHOLExact, hlook] at hx
          split at hx
          · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
          · cases hx
        subst ret'
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
            some (body, callee, .one) := by rwa [← hc]
        have hInv_ce : EvmInv (callEntryStateHOLFinite t callee) := localsFree_evmInv t callee (t.clock - 1) hInv
        have hc_ce := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
        have hPc : Pc t (callEntryStateHOLFinite t callee) := hentry t values callee hc hInv hP hargs hl_orig
        have hlen_ce : (evmChain (callEntryStateHOLFinite t callee)).length = (evmChain s0).length := hc_ce.2.2.1.trans hlen
        have hR_ce : if charged then evmR (callEntryStateHOLFinite t callee) < evmR s0 else evmR (callEntryStateHOLFinite t callee) ≤ evmR s0 := by
          rw [hc_ce.2.1]; exact hR
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite t callee) body).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body with ⟨res, cpost⟩
        simp only [hrun] at hnt hmeta ⊢
        change cpost.code = t.code at hmeta
        have hB (hsafe : res ≠ some .timeOut) :
            ((∃ v, res = some (.returned v)) →
              EvmInv cpost ∧ (evmChain cpost).length = (evmChain s0).length ∧ evmR cpost < evmR s0 ∧ R t cpost) ∧
            (IsEvmErr res →
              EvmInv cpost ∧ (evmChain cpost).length = (evmChain s0).length ∧ evmR cpost ≤ evmR s0) := by
          have hs := hbody t hP (callEntryStateHOLFinite t callee) hc hInv_ce hlen_ce hR_ce hPc (by rw [hrun]; exact hsafe)
          dsimp only at hs; rw [hrun] at hs; exact ⟨hs.1, hs.2.1⟩
        cases res with
        | none => exact opDispatchPost_error s0 cpost
        | some r0 =>
          cases r0 with
          | timeOut => simp at hnt
          | returned v =>
            by_cases hsh_ok : shapeEqHOL (shapeOfHOLExact v) .one = true
            · simp only [hsh_ok, ↓reduceIte] at hnt ⊢
              obtain ⟨hInv_cp, hlen_cp, hR_cp, hRt_cp⟩ := (hB (by simp)).1 ⟨v, rfl⟩
              let resumed : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
              have hInv_res : EvmInv resumed := localsFree_evmInv cpost t.locals cpost.clock hInv_cp
              have hc_res := evm_congr (s := cpost) (t := resumed) rfl rfl
              exact hcont resumed (hmeta.trans hc) hInv_res
                (by rw [hc_res.2.2.1]; exact hlen_cp)
                (by simp only [↓reduceIte, hc_res.2.1]; exact hR_cp)
                (hstep t cpost hInv hP hInv_cp hRt_cp)
                (by simpa [resumed] using hnt)
            · simp only [hsh_ok, Bool.false_eq_true, ↓reduceIte]
              exact opDispatchPost_error s0 cpost
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨hInv_cp, hlen_cp, hR_cp⟩ := (hB (by simp)).2 ⟨ev, rfl⟩
              have hInv_el : EvmInv cpost.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost _ cpost.clock hInv_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              refine ⟨?_, fun _ => ⟨hInv_el, ?_, ?_⟩⟩
              · rintro ⟨_, h⟩; cases h
              · rw [hc_el.2.2.1]; exact hlen_cp
              · rw [hc_el.2.1]; exact hR_cp
            · refine opDispatchPost_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => exact opDispatchPost_error s0 cpost
          | «continue» => exact opDispatchPost_error s0 cpost
          | finalFfi f =>
            refine opDispatchPost_other (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => exact opDispatchPost_error s0 cpost.emptyLocalsHOLFinite

private theorem charge_with_memory_args_lookup_g08 {vals : List (ValueHOL 64)} {body' : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret' : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "charge_with_memory") vals =
      some (body', callee, ret')) :
    ∃ (basew : BitVec 64) (v2 v3 : ValueHOL 64),
      vals = [.val (.word basew), v2, v3] ∧
      shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact v2) = true ∧
      shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact v3) = true ∧
      callee.lookup (ofString "base") = some (.val (.word basew)) ∧
      callee.lookup (ofString "start") = some v2 ∧
      callee.lookup (ofString "size") = some v3 := by
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
    originalRuntimeCode.lookup (ofString "charge_with_memory") vals body' callee ret' hl
  simp only [Flapjack.lookupCodeHOLExact, lookup_charge_with_memory] at hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩
  · simp at hx
  · simp at hx
  · simp at hx
  · split at hx
    · rename_i hcond
      have heq := Option.some.inj hx
      rcases Prod.mk.inj heq with ⟨_, hrest⟩
      rcases Prod.mk.inj hrest with ⟨hloc, _⟩
      have hs := hcond.2.2
      simp only [List.map, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, List.zip_cons_cons, List.zip_nil_left] at hs
      rcases hs with ⟨hsh1, hsh2, hsh3⟩
      rcases v1 with ⟨⟨w1⟩⟩ | _ | _
      · refine ⟨w1, v2, v3, rfl, hsh2, hsh3, ?_, ?_, ?_⟩
        · have hfn := congrFun hloc.symm (ofString "base")
          have hne_bs : ofString "base" ≠ ofString "start" := by decide
          have hne_bz : ofString "base" ≠ ofString "size" := by decide
          simpa [FUPDATE_LIST, FUPDATE, hne_bs, Ne.symm hne_bs, hne_bz, Ne.symm hne_bz] using hfn
        · have hfn := congrFun hloc.symm (ofString "start")
          have hne_sz : ofString "start" ≠ ofString "size" := by decide
          simpa [FUPDATE_LIST, FUPDATE, hne_sz, Ne.symm hne_sz] using hfn
        · have hfn := congrFun hloc.symm (ofString "size")
          simpa [FUPDATE_LIST, FUPDATE] using hfn
      · simp [shapeOfHOLExact, shapeEqHOL] at hsh1
      · simp [shapeOfHOLExact, shapeEqHOL] at hsh1
    · cases hx
  · simp at hx

private theorem extend_memory_cost1_two_args_lookup_g08 {vals : List (ValueHOL 64)} {body' : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret' : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "extend_memory_cost1") vals =
      some (body', callee, ret')) :
    ∃ (v1 v2 : ValueHOL 64),
      vals = [v1, v2] ∧
      shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact v1) = true ∧
      shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact v2) = true ∧
      callee.lookup (ofString "start") = some v1 ∧
      callee.lookup (ofString "size") = some v2 := by
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
    originalRuntimeCode.lookup (ofString "extend_memory_cost1") vals body' callee ret' hl
  simp only [Flapjack.lookupCodeHOLExact, lookup_extend_memory_cost1] at hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩
  · simp at hx
  · simp at hx
  · split at hx
    · rename_i hcond
      have heq := Option.some.inj hx
      rcases Prod.mk.inj heq with ⟨_, hrest⟩
      rcases Prod.mk.inj hrest with ⟨hloc, _⟩
      have hs := hcond.2.2
      simp only [List.map, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, List.zip_cons_cons, List.zip_nil_left] at hs
      rcases hs with ⟨hsh1, hsh2⟩
      refine ⟨v1, v2, rfl, hsh1, hsh2, ?_, ?_⟩
      · have hfn := congrFun hloc.symm (ofString "start")
        have hne_sz : ofString "start" ≠ ofString "size" := by decide
        simpa [FUPDATE_LIST, FUPDATE, hne_sz, Ne.symm hne_sz] using hfn
      · have hfn := congrFun hloc.symm (ofString "size")
        simpa [FUPDATE_LIST, FUPDATE] using hfn
    · cases hx
  · simp at hx

private theorem charge_with_memory_body_run_aligned_cov_g08 {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (stVal : ValueHOL 64) (kw : BitVec 64)
    (hst_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true)
    (hkw : kw ≠ 0#64) :
    CalleeBodyRunQ_g08 s0
      (fun t => HeadMemAligned t ∧
        (∃ bw : BitVec 64, t.locals.lookup (ofString "base") = some (.val (.word bw)) ∧ 0 < bw.toNat) ∧
        t.locals.lookup (ofString "start") = some stVal ∧
        t.locals.lookup (ofString "size") =
          some (.rStruct [.val (.word kw), .val (.word 0#64), .val (.word 0#64), .val (.word 0#64)]))
      (fun post => (satValue_g08 stVal).toNat + kw.toNat ≤ memW post (globN post "ev" + 32))
      false
      (sourceFnBody Guest.Software.guestFn_charge_with_memory) := by
  have hR_lc : ∀ (a b : PanSemStateFiniteExact 64 F),
      b = { a with locals := b.locals, clock := b.clock } →
      (satValue_g08 stVal).toNat + kw.toNat ≤ memW a (globN a "ev" + 32) →
      (satValue_g08 stVal).toNat + kw.toNat ≤ memW b (globN b "ev" + 32) := by
    intro a b hab hcov
    have hg : globN b "ev" = globN a "ev" := globN_eq_of_lookup_eq (by rw [hab])
    have hm : b.memory = a.memory := by rw [hab]
    rw [hg]; unfold memW; rw [hm]; exact hcov
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_charge_with_memory,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine CalleeBodyRunQ_g08.decCall
    (Q := fun t =>
      HeadMemAligned t ∧
      (∃ bw : BitVec 64, t.locals.lookup (ofString "base") = some (.val (.word bw)) ∧ 0 < bw.toNat) ∧
      ∃ cw ebw : BitVec 64,
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        (ebw = 0#64 ∨
          (memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
           (memW t (globN t "ev" + 32) + ebw.toNat) % 8 = 0 ∧
           memW t (globN t "ev" + 24) + memW t (globN t "ev" + 40) = globN t "frame_mem_ptr")) ∧
        (cw.toNat < 2 ^ 64 - 1 →
          (satValue_g08 stVal).toNat + kw.toNat ≤ memW t (globN t "ev" + 32) + ebw.toNat))
    hR_lc
    eps_extend_memory_cost1_bounds_cov_g08
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t values _ callee _ v cpost _ ⟨hHM, ⟨bw, hbw, hpos⟩, hst_lk, hsz_lk⟩ hargs hl_orig _ _ hQc => by
      obtain ⟨hlf, cw, ebw, rfl, heb_bounds, hcov_ce⟩ := hQc
      obtain ⟨v1, v2, rfl, _, _, hcal_st, hcal_sz⟩ := extend_memory_cost1_two_args_lookup_g08 hl_orig
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact, evalHOLExact, hst_lk, hsz_lk, Option.some.injEq, List.cons.injEq] at hargs
      rcases hargs with ⟨rfl, rfl, _⟩
      let ce := callEntryStateHOLFinite t callee
      have hHM_ce : HeadMemAligned ce := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      have hHM_cp : HeadMemAligned cpost :=
        headMemAligned_congr_head_only (by rw [hlf]) (fun off _ => by unfold memW; rw [hlf]) hHM_ce
      let res := setVarHOLFinite (ofString "x") (.rStruct [.val (.word cw), .val (.word ebw)]) { cpost with locals := t.locals }
      have hHM_res : HeadMemAligned res := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp
      have hne_xb : ofString "x" ≠ ofString "base" := by decide
      have hmem32_eq : memW res (globN res "ev" + 32) = memW ce (globN ce "ev" + 32) := by
        have hg : globN res "ev" = globN ce "ev" := globN_eq_of_lookup_eq (by change cpost.globals.lookup _ = ce.globals.lookup _; rw [hlf])
        have hm : res.memory = ce.memory := by change cpost.memory = ce.memory; rw [hlf]
        rw [hg]; unfold memW; rw [hm]
      refine ⟨hHM_res,
              ⟨bw, by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne_xb, Ne.symm hne_xb, hbw], hpos⟩,
              cw, ebw, by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], ?_, ?_⟩
      · rcases heb_bounds with rfl | ⟨before, after, haft_lt, haft_mod, hbef_lt, heb_sub, hbef_eq⟩
        · exact Or.inl rfl
        · right
          have hbef : before = memW ce (globN ce "ev" + 32) := hbef_eq hHM_ce.1
          have hsum : memW res (globN res "ev" + 32) + ebw.toNat = after := by
            rw [hmem32_eq, ← hbef]; omega
          rw [hsum]
          exact ⟨haft_lt, by omega, hHM_res.2⟩
      · intro hcw_lt
        rw [hmem32_eq]
        exact hcov_ce stVal kw hcal_st hst_sh hcal_sz hkw hcw_lt hHM_ce.1)
    ?_
  refine CalleeBodyRunQ_g08.decCall
    (Q := fun t =>
      HeadMemAligned t ∧
      (∃ totw bw cw ebw : BitVec 64,
        t.locals.lookup (ofString "total") = some (.val (.word totw)) ∧
        0 < totw.toNat ∧
        (totw.toNat < 2 ^ 64 - 1 → totw.toNat = bw.toNat + cw.toNat) ∧
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        (ebw = 0#64 ∨
          (memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
           (memW t (globN t "ev" + 32) + ebw.toNat) % 8 = 0 ∧
           memW t (globN t "ev" + 24) + memW t (globN t "ev" + 40) = globN t "frame_mem_ptr")) ∧
        (cw.toNat < 2 ^ 64 - 1 →
          (satValue_g08 stVal).toNat + kw.toNat ≤ memW t (globN t "ev" + 32) + ebw.toNat)))
    hR_lc
    eps_add_sat_pos_exact_g08
    (fun t values b_as callee rs_as hc _ ⟨_, ⟨bw, hbw, hpos⟩, cw, ebw, hx, _⟩ hargs hl => by
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "add_sat") values =
          some (b_as, callee, rs_as) := by rwa [← hc]
      obtain ⟨_, _, w1, w2, rfl, hw1, hw2⟩ := two_word_arg_lookup (by decide) lookup_add_sat hl_orig
      have hargs_ok : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.var .local (ofString "base"), .rfield 0 (.var .local (ofString "x"))] =
          some [.val (.word bw), .val (.word cw)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hbw, hx]
      rw [hargs_ok] at hargs
      injection hargs with hvs
      rcases List.cons.inj hvs with ⟨hw1_eq, hvs'⟩
      rcases List.cons.inj hvs' with ⟨hw2_eq, _⟩
      injection hw1_eq with hw1'; injection hw1' with hw1''; subst hw1''
      injection hw2_eq with hw2'; injection hw2' with hw2''; subst hw2''
      exact ⟨bw, cw, hw1, hw2, hpos⟩)
    (fun t values _ callee _ v cpost _ ⟨hHM, ⟨bw, hbw, _⟩, cw, ebw, hx, heb_cond, hcov_imp⟩ hargs hl_orig _ _ hQc => by
      obtain ⟨hlf, totw, rfl, hpos, htot_ex⟩ := hQc
      obtain ⟨_, _, w1, w2, rfl, hw1, hw2⟩ := two_word_arg_lookup (by decide) lookup_add_sat hl_orig
      have hargs_ok : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.var .local (ofString "base"), .rfield 0 (.var .local (ofString "x"))] =
          some [.val (.word bw), .val (.word cw)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hbw, hx]
      rw [hargs_ok] at hargs
      injection hargs with hvs
      rcases List.cons.inj hvs with ⟨hw1_eq, hvs'⟩
      rcases List.cons.inj hvs' with ⟨hw2_eq, _⟩
      injection hw1_eq with hw1'; injection hw1' with hw1''; subst hw1''
      injection hw2_eq with hw2'; injection hw2' with hw2''; subst hw2''
      let ce := callEntryStateHOLFinite t callee
      have hHM_ce : HeadMemAligned ce := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      have hHM_cp : HeadMemAligned cpost :=
        headMemAligned_congr_head_only (by rw [hlf]) (fun off _ => by unfold memW; rw [hlf]) hHM_ce
      let res := setVarHOLFinite (ofString "total") (.val (.word totw)) { cpost with locals := t.locals }
      have hHM_res : HeadMemAligned res := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp
      have hne_tx : ofString "total" ≠ ofString "x" := by decide
      have hmem32_eq : memW res (globN res "ev" + 32) = memW t (globN t "ev" + 32) := by
        have hg : globN res "ev" = globN t "ev" := globN_eq_of_lookup_eq (by change cpost.globals.lookup _ = t.globals.lookup _; rw [hlf]; rfl)
        have hm : res.memory = t.memory := by change cpost.memory = t.memory; rw [hlf]; rfl
        rw [hg]; unfold memW; rw [hm]
      refine ⟨hHM_res, totw, bw, cw, ebw,
              by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
              hpos, htot_ex bw cw hw1 hw2,
              by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne_tx, Ne.symm hne_tx, hx],
              ?_, ?_⟩
      · rcases heb_cond with rfl | ⟨hlt37, hmod8, _⟩
        · exact Or.inl rfl
        · right
          rw [hmem32_eq]
          exact ⟨hlt37, hmod8, hHM_res.2⟩
      · intro hcw_lt
        rw [hmem32_eq]
        exact hcov_imp hcw_lt)
    ?_
  refine CalleeBodyRunQ_g08.seq_charge_gas_preserves_headMem
    (Q := fun t =>
      ∃ cw ebw : BitVec 64,
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        (ebw = 0#64 ∨
          (memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
           (memW t (globN t "ev" + 32) + ebw.toNat) % 8 = 0 ∧
           memW t (globN t "ev" + 24) + memW t (globN t "ev" + 40) = globN t "frame_mem_ptr")) ∧
        (satValue_g08 stVal).toNat + kw.toNat ≤ memW t (globN t "ev" + 32) + ebw.toNat)
    (fun t w hw _ ⟨_, totw, _, _, _, htot, hpos, _⟩ => by
      change t.locals.lookup (ofString "total") = some (.val (.word w)) at hw
      rw [htot] at hw; injection hw with hw'; injection hw' with hw''; injection hw'' with hweq; subst hweq
      exact hpos)
    (fun t amtw cpost hw hamt_lt _ ⟨hHM, totw, bw, cw, ebw, htot, _, htot_ex, hx, heb_cond, hcov_imp⟩ _ hglob_cp _ hmem_head_cp => by
      change t.locals.lookup (ofString "total") = some (.val (.word amtw)) at hw
      rw [htot] at hw; injection hw with hw'; injection hw' with hw''; injection hw'' with hweq; subst hweq
      have htot_sum := htot_ex hamt_lt
      have hcw_lt : cw.toNat < 2 ^ 64 - 1 := by omega
      have hHM_cp : HeadMemAligned cpost := headMemAligned_congr_head_only hglob_cp hmem_head_cp hHM
      let res : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
      have hHM_res : HeadMemAligned res := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp
      have hmem32_eq : memW res (globN res "ev" + 32) = memW t (globN t "ev" + 32) := by
        have hg : globN res "ev" = globN t "ev" := globN_eq_of_lookup_eq (by change cpost.globals.lookup _ = t.globals.lookup _; rw [hglob_cp])
        rw [hg]; exact hmem_head_cp 32 (by simp)
      refine ⟨cw, ebw, hx, ?_, ?_⟩
      · rcases heb_cond with rfl | ⟨hlt37, hmod8, _⟩
        · exact Or.inl rfl
        · right
          rw [hmem32_eq]
          exact ⟨hlt37, hmod8, hHM_res.2⟩
      · rw [hmem32_eq]
        exact hcov_imp hcw_lt)
    ?_
  refine CalleeBodyRunQ_g08.seq_call
    (Q := fun t => (satValue_g08 stVal).toNat + kw.toNat ≤ memW t (globN t "ev" + 32))
    eps_extend_memory_aligned_len_g08
    (fun t values b_em callee rs_em hc _ ⟨cw, ebw, hx, heb_cond, _⟩ hargs hl => by
      have hx1 : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.rfield 1 (.var .local (ofString "x"))] = some [.val (.word ebw)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hx]
      rw [hx1] at hargs; injection hargs with hvs; subst hvs
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "extend_memory") [.val (.word ebw)] =
          some (b_em, callee, rs_em) := by rwa [← hc]
      obtain ⟨_, _, ebw', heq_eb, hcal_eb⟩ := one_word_arg_lookup lookup_extend_memory hl_orig
      injection heq_eb with heq1; injection heq1 with heq2; subst heq2
      exact ⟨ebw, hcal_eb, heb_cond⟩)
    (fun t values _ callee _ _ cpost _ ⟨cw, ebw, hx, _, hcov⟩ hargs hl_orig _ _ ⟨_, hlen_eq⟩ => by
      have hx1 : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.rfield 1 (.var .local (ofString "x"))] = some [.val (.word ebw)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hx]
      rw [hx1] at hargs; injection hargs with hvs; subst hvs
      obtain ⟨_, _, ebw', heq_eb, hcal_eb⟩ := one_word_arg_lookup lookup_extend_memory hl_orig
      injection heq_eb with heq1; injection heq1 with heq2; subst heq2
      have hpost_len := hlen_eq ebw hcal_eb
      change (satValue_g08 stVal).toNat + kw.toNat ≤ memW cpost (globN cpost "ev" + 32)
      rw [hpost_len]
      exact hcov)
    (CalleeBodyRunQ_g08.ret (fun t ht => hR_lc t t.emptyLocalsHOLFinite rfl ht) _)

theorem lookup_op_mstore :
    originalRuntimeCode.lookup (ofString "op_mstore") =
      some ([], sourceFnBody Guest.Software.guestFn_op_mstore, .one) :=
  lookup_of_guestAst_getElem 508 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_op_mstore) rfl

theorem lookup_op_mstore8 :
    originalRuntimeCode.lookup (ofString "op_mstore8") =
      some ([], sourceFnBody Guest.Software.guestFn_op_mstore8, .one) :=
  lookup_of_guestAst_getElem 509 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_op_mstore8) rfl

private theorem eval_head_mem_plus_s_g08 {F : Type}
    (t : PanSemStateFiniteExact 64 F) (hInv : EvmInv t)
    (sw : BitVec 64)
    (hsw : t.locals.lookup (ofString "s") = some (.val (.word sw))) :
    ∃ basew : BitVec 64,
      basew.toNat = memW t (globN t "ev" + 24) ∧
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        (.op .add
          [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]),
           .var .local (ofString "s")]) =
        some (.val (.word (basew + sw))) := by
  have hhead : (globN t "ev", globN t "cur_cont") ∈ evmChain t := by
    simp [evmChain, evmChainFrom]
  have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead
  have hb_ev := (frameWF_bounds hInv.1.2 hFW0).1
  dsimp only at hb_ev
  have hev_pos : 0 < globN t "ev" := by
    obtain ⟨hin, _⟩ := (hFW0.1 (globN t "ev", 280) (by simp)).1
    have h1 := hInv.1.2.2.2.1; have h2 := hInv.1.2.2.2.2.1
    rw [R11Shards.scratchStart_val] at h1; dsimp only at hin; omega
  obtain ⟨evw, hevw, hevw_nat⟩ := global_word_of_pos t "ev" hev_pos
  have hrec_w := (hFW0.1 (globN t "ev", 280) (by simp)).2
  obtain ⟨basew, hdom24_raw, hmem24_raw⟩ := hrec_w.2.2 3 (by omega)
  have h24_eq : globN t "ev" + 8 * 3 = globN t "ev" + 24 := by omega
  rw [h24_eq] at hdom24_raw hmem24_raw
  have had24 : evw + (24#64 + 0) = BitVec.ofNat 64 (globN t "ev" + 24) := by
    apply BitVec.eq_of_toNat_eq
    have hz0 : (0 : BitVec 64).toNat = 0 := rfl
    have h24n : (24#64 : BitVec 64).toNat = 24 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hevw_nat, hz0, h24n, Nat.add_zero,
      Nat.mod_eq_of_lt (show 24 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show globN t "ev" + 24 < 2 ^ 64 by omega)]
  have hml24 : @memLoadHOLExact 64 _ .one (BitVec.ofNat 64 (globN t "ev" + 24))
      t.memaddrs (fun a => Classical.propDecidable (t.memaddrs a))
      t.memory t.structs = some (.val (.word basew)) := by
    unfold memLoadHOLExact; rw [if_pos hdom24_raw, hmem24_raw]
  have hwf0 : isWfShapeExactHOL t.structs .one = true := rfl
  have hload24' : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.load .one (.op .add [.var .global (ofString "ev"), .const 24#64])) =
      some (.val (.word basew)) := by
    simp only [evalHOLExact, evalListHOLExact, PanSemStateFiniteExact.toExact,
      hevw, hwf0, wordOpHOL, wordOp, valueIsWord, valueWord,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      had24, hml24]
  have hbasew_nat : basew.toNat = memW t (globN t "ev" + 24) := by
    unfold memW; rw [hmem24_raw]
  refine ⟨basew, hbasew_nat, ?_⟩
  have hlist_ev : @evalListHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]),
       .var .local (ofString "s")] =
      some [.val (.word basew), .val (.word sw)] := by
    have hs_ev : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        (.var .local (ofString "s")) = some (.val (.word sw)) := hsw
    simp only [evalListHOLExact, hload24', hs_ev]
  simp only [evalHOLExact, hlist_ev, wordOpHOL, wordOp,
    valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
  have hz : sw + (0 : BitVec 64) = sw := BitVec.add_zero _
  exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word (basew + w)))) hz

theorem op_mstore8_aligned_spec :
    FunSpec (fun s => EvmRun s ∧ HeadMemAligned s) OpDispatchPost (ofString "op_mstore8") := by
  refine ⟨_, _, _, lookup_op_mstore8, ?_⟩
  intro F s0 hcode ⟨hRun, hHM0⟩ _ hnt
  suffices hrun : HandlerRun s0 HeadMemAligned false (sourceFnBody Guest.Software.guestFn_op_mstore8) from
    hrun s0 hcode hRun.1 rfl (le_refl _) hHM0 hnt
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_op_mstore8,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRun.decCall
    (Q := fun t =>
      HeadMemAligned t ∧
      ∃ stVal : ValueHOL 64,
        t.locals.lookup (ofString "start") = some stVal ∧
        shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true)
    eps_stack_pop_preserves_headMem
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ callee _ v cpost _ hHM _ _ _ _ ⟨_, hsh_v, hHM_step⟩ => by
      have hHM_ce : HeadMemAligned (callEntryStateHOLFinite t callee) :=
        headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      have hHM_cp : HeadMemAligned cpost := hHM_step hHM_ce
      have hHM_res : HeadMemAligned (setVarHOLFinite (ofString "start") v { cpost with locals := t.locals }) :=
        headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp
      exact ⟨hHM_res, v, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], hsh_v⟩)
    ?_
  refine HandlerRun.decCall
    (Q := fun t =>
      HeadMemAligned t ∧
      ∃ stVal : ValueHOL 64,
        t.locals.lookup (ofString "start") = some stVal ∧
        shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true)
    eps_stack_pop_preserves_headMem
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ callee _ v cpost _ ⟨hHM, stVal, hst, hsh_st⟩ _ _ _ _ ⟨_, _, hHM_step⟩ => by
      have hHM_ce : HeadMemAligned (callEntryStateHOLFinite t callee) :=
        headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      have hHM_cp : HeadMemAligned cpost := hHM_step hHM_ce
      have hHM_res : HeadMemAligned (setVarHOLFinite (ofString "value") v { cpost with locals := t.locals }) :=
        headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp
      have hne_vs : ofString "value" ≠ ofString "start" := by decide
      exact ⟨hHM_res, stVal,
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne_vs, Ne.symm hne_vs, hst],
        hsh_st⟩)
    ?_
  refine seq_call_strict_q_g08
    (Pc := fun t ce =>
      HeadMemAligned ce ∧
      (∃ bw : BitVec 64, ce.locals.lookup (ofString "base") = some (.val (.word bw)) ∧ 0 < bw.toNat) ∧
      ∃ stVal : ValueHOL 64,
        t.locals.lookup (ofString "start") = some stVal ∧
        ce.locals.lookup (ofString "start") = some stVal ∧
        shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true ∧
        ce.locals.lookup (ofString "size") =
          some (.rStruct [.val (.word 1#64), .val (.word 0#64), .val (.word 0#64), .val (.word 0#64)]))
    (R := fun t cpost =>
      ∀ stVal : ValueHOL 64,
        t.locals.lookup (ofString "start") = some stVal →
        (satValue_g08 stVal).toNat + 1 ≤ memW cpost (globN cpost "ev" + 32))
    (Q := fun t =>
      ∃ stVal : ValueHOL 64,
        t.locals.lookup (ofString "start") = some stVal ∧
        shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true ∧
        (satValue_g08 stVal).toNat + 1 ≤ memW t (globN t "ev" + 32))
    lookup_charge_with_memory
    (fun t values callee _ _ ⟨hHM, stVal, hst, hsh_st⟩ hargs hl_orig => by
      obtain ⟨basew, v2, v3, rfl, _, _, hcal_b, hcal_st, hcal_sz⟩ := charge_with_memory_args_lookup_g08 hl_orig
      have hHM_ce : HeadMemAligned (callEntryStateHOLFinite t callee) :=
        headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      have hargs_ok : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.const 3#64, .var .local (ofString "start"),
           .rstruct [.const 1#64, .const 0#64, .const 0#64, .const 0#64]] =
          some [.val (.word 3#64), stVal,
                .rStruct [.val (.word 1#64), .val (.word 0#64), .val (.word 0#64), .val (.word 0#64)]] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hst]
      rw [hargs_ok] at hargs
      injection hargs with hvs
      rcases List.cons.inj hvs with ⟨hb_eq, hvs1⟩
      rcases List.cons.inj hvs1 with ⟨rfl, hvs2⟩
      rcases List.cons.inj hvs2 with ⟨rfl, _⟩
      injection hb_eq with hb1; injection hb1 with hb2; subst hb2
      exact ⟨hHM_ce, ⟨3#64, hcal_b, by decide⟩, stVal, hst, hcal_st, hsh_st, hcal_sz⟩)
    (fun t ⟨_, stVal, hst, hsh_st⟩ => by
      intro ce hc hInv_ce hlen_ce hR_ce ⟨hHM_ce, hbw_ce, stVal', hst', hcal_st, hsh_st', hcal_sz⟩ hnt_ce
      have hst_eq : stVal' = stVal := by rw [hst] at hst'; exact Option.some.inj hst'.symm
      subst stVal'
      have hrun_cov := charge_with_memory_body_run_aligned_cov_g08 s0 stVal 1#64 hsh_st (by decide)
        ce hc hInv_ce hlen_ce hR_ce ⟨hHM_ce, hbw_ce, hcal_st, hcal_sz⟩ hnt_ce
      dsimp only at hrun_cov ⊢
      refine ⟨fun hret => ?_, hrun_cov.2.1, hrun_cov.2.2⟩
      obtain ⟨h1, h2, h3, hcov⟩ := hrun_cov.1 hret
      refine ⟨h1, h2, h3, fun stVal0 hst0 => ?_⟩
      have hst0_eq : stVal0 = stVal := by rw [hst] at hst0; exact Option.some.inj hst0.symm
      subst stVal0
      simpa using hcov)
    (fun t cpost _ ⟨_, stVal, hst, hsh_st⟩ _ hRt => by
      exact ⟨stVal, hst, hsh_st, hRt stVal hst⟩)
    ?_
  refine HandlerRun.decCall
    (Q := fun t =>
      ∀ addr : BitVec 64,
        @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.op .add
            [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]),
             .var .local (ofString "s")]) =
          some (.val (.word addr)) →
        t.memaddrs (panByteAlignHOL addr) →
        memW t (globN t "ev" + 24) ≤ addr.toNat ∧
        addr.toNat < memW t (globN t "ev" + 24) + memW t (globN t "ev" + 40))
    eps_sat_word_exact_g08
    (fun t values b_sw callee rs_sw hc _ ⟨stVal, hst, hsh_st, _⟩ hargs hl => by
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "sat_word") values =
          some (b_sw, callee, rs_sw) := by rwa [← hc]
      obtain ⟨_, _, v0, rfl, hcal_v⟩ := single_comb_arg_lookup_g08 lookup_sat_word_g08 hl_orig
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact, evalHOLExact, hst, Option.some.injEq, List.cons.injEq] at hargs
      rcases hargs with ⟨rfl, _⟩
      exact ⟨stVal, hcal_v, hsh_st⟩)
    (fun t values _ callee _ v cpost _ ⟨stVal, hst, _, hcov⟩ hargs hl_orig hInv_cp _ ⟨hlf, hv_eq⟩ => by
      obtain ⟨_, _, v0, rfl, hcal_v⟩ := single_comb_arg_lookup_g08 lookup_sat_word_g08 hl_orig
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact, evalHOLExact, hst, Option.some.injEq, List.cons.injEq] at hargs
      rcases hargs with ⟨rfl, _⟩
      have hv_sat := hv_eq stVal hcal_v
      subst v
      let res := setVarHOLFinite (ofString "s") (.val (.word (satValue_g08 stVal))) { cpost with locals := t.locals }
      have hInv_res : EvmInv res := localsFree_evmInv cpost res.locals cpost.clock hInv_cp
      have hmem32_eq : memW res (globN res "ev" + 32) = memW t (globN t "ev" + 32) := by
        have hg : globN res "ev" = globN t "ev" := globN_eq_of_lookup_eq (by change cpost.globals.lookup _ = t.globals.lookup _; rw [hlf]; rfl)
        have hm : res.memory = t.memory := by change cpost.memory = t.memory; rw [hlf]; rfl
        rw [hg]; unfold memW; rw [hm]
      have hres_s : res.locals.lookup (ofString "s") = some (.val (.word (satValue_g08 stVal))) := by
        simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      obtain ⟨basew, hbasew_nat, hev_dst⟩ := eval_head_mem_plus_s_g08 res hInv_res (satValue_g08 stVal) hres_s
      have hbounds := head_mem_store_address_g08 res hInv_res basew (satValue_g08 stVal) 1 hbasew_nat (by omega)
        (by rw [hmem32_eq]; exact hcov)
      intro addr haddr _
      rw [hev_dst] at haddr
      injection haddr with h1; injection h1 with h2; injection h2 with h3; subst h3
      change memW res (globN res "ev" + 24) ≤ (basew + satValue_g08 stVal).toNat ∧
        (basew + satValue_g08 stVal).toNat < memW res (globN res "ev" + 24) + memW res (globN res "ev" + 40)
      have hb1 := hbounds.2.1
      have hb2 := hbounds.2.2
      exact ⟨hb1, by omega⟩)
    ?_
  exact HandlerRun.seq_storeByte_head_mem_g08 (HandlerRun.seq_call_simple eps_pc_add (HandlerRun.ret _))

private def noCatchableRaise_g08 (good : MlS → Bool) : ProgHOL 64 → Bool
  | .dec _ _ _ b => noCatchableRaise_g08 good b
  | .seq a b => noCatchableRaise_g08 good a && noCatchableRaise_g08 good b
  | .ite _ a b => noCatchableRaise_g08 good a && noCatchableRaise_g08 good b
  | .while _ b => noCatchableRaise_g08 good b
  | .decCall _ _ f _ cont => good f && noCatchableRaise_g08 good cont
  | .call (some (_, none)) f _ => good f
  | .raise eid _ => eid == ofString "TrapErr"
  | .skip | .break | .continue | .annot _ _ | .return _
  | .assign _ _ _ | .primitive _ _ _ | .store _ _ | .storeByte _ _ | .store32 _ _
  | .shMemStore _ _ _ | .extCall _ _ _ _ _ => true
  | _ => false

private theorem lex_ncr_g08 {a1 a2 b1 b2 : Nat} (h : a1 < a2 ∨ a1 = a2 ∧ b1 < b2) :
    Prod.Lex (· < ·) (· < ·) (a1, b1) (a2, b2) := by
  rcases h with h | ⟨rfl, h⟩
  · exact Prod.Lex.left _ _ h
  · exact Prod.Lex.right _ h

private theorem evaluate_noCatchableRaise_g08 {F : Type} (good : MlS → Bool)
    (hgood : ∀ f, good f = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup f values =
        some (body, callee, rs) →
      noCatchableRaise_g08 good body = true)
    (p : ProgHOL 64) (hp : noCatchableRaise_g08 good p = true)
    (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode) :
    ∀ eid v, eid ≠ ofString "TrapErr" → (evaluateHOLFiniteState s p).1 ≠ some (.exception eid v) := by
  cases shape : p with
  | skip => rw [evaluateHOLFiniteState_skip]; simp
  | «break» => rw [evaluateHOLFiniteState_break]; simp
  | «continue» => rw [evaluateHOLFiniteState_continue]; simp
  | annot _ _ => rw [evaluateHOLFiniteState_annot]; simp
  | «return» _ =>
    rw [evaluateHOLFiniteState_return]
    split
    · simp
    · split <;> simp
  | assign _ _ _ =>
    rw [evaluateHOLFiniteState_assign]
    split
    · simp
    · split <;> simp
  | primitive _ _ _ =>
    rw [evaluateHOLFiniteState_primitive]
    split
    · simp
    · split
      · simp
      · split <;> simp
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | store32 _ _ =>
    rw [evaluateHOLFiniteState_store32]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | shMemStore _ _ _ =>
    rw [evaluateHOLFiniteState_shMemStore_total]
    dsimp only
    split
    · unfold shMemStoreHOLExact
      split <;> split
      all_goals simp [ofExact, toExact]
      all_goals split <;> simp
    · simp
  | raise name _ =>
    have htrap : name = ofString "TrapErr" := by
      simpa [shape, noCatchableRaise_g08, beq_iff_eq] using hp
    subst htrap
    intro eid v hne
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only
      split
      · simp [hne.symm]
      · simp
    · simp
  | extCall _ _ _ _ _ =>
    rw [evaluateHOLFiniteState_extCall_source]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | dec name _ _ body =>
    have hb : noCatchableRaise_g08 good body = true := by simpa [shape, noCatchableRaise_g08] using hp
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · rename_i val _
      split
      · exact evaluate_noCatchableRaise_g08 good hgood body hb (setVarHOLFinite name val s) hcode
      · simp
  | seq a b =>
    have hab : noCatchableRaise_g08 good a = true ∧ noCatchableRaise_g08 good b = true := by
      simpa [shape, noCatchableRaise_g08, Bool.and_eq_true] using hp
    have ih1 := evaluate_noCatchableRaise_g08 good hgood a hab.1 s hcode
    have rem := evaluateHOLFiniteState_clock_le s a
    have meta' := PanRunBounded.evaluateHOLFiniteState_metadata s a
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hr : evaluateHOLFiniteState s a with ⟨r1, mid⟩
    rw [hr] at ih1 rem meta'
    dsimp only at ih1 rem meta' ⊢
    cases r1 with
    | none =>
      have mclock : mid.clock ≤ s.clock := rem
      exact evaluate_noCatchableRaise_g08 good hgood b hab.2 mid (meta'.1.trans hcode)
    | some _ => exact ih1
  | ite _ yes no =>
    have hy : noCatchableRaise_g08 good yes = true ∧ noCatchableRaise_g08 good no = true := by
      simpa [shape, noCatchableRaise_g08, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noCatchableRaise_g08 good hgood no hy.2 s hcode
      · exact evaluate_noCatchableRaise_g08 good hgood yes hy.1 s hcode
    · simp
  | «while» cond body =>
    have hb : noCatchableRaise_g08 good body = true := by simpa [shape, noCatchableRaise_g08] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp
        · dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := evaluate_noCatchableRaise_g08 good hgood body hb (decClockHOLFinite s) hcode
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          have meta' := PanRunBounded.evaluateHOLFiniteState_metadata (decClockHOLFinite s) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at ih1 rem meta'
          dsimp only at ih1 rem meta' ⊢
          have smaller : mid.clock < s.clock := by change mid.clock ≤ s.clock - 1 at rem; omega
          have mCode : mid.code = originalRuntimeCode := meta'.1.trans hcode
          cases r1 with
          | none =>
            exact evaluate_noCatchableRaise_g08 good hgood (.while cond body) (by simpa [noCatchableRaise_g08] using hb) mid mCode
          | some r =>
            cases r with
            | «continue» =>
              exact evaluate_noCatchableRaise_g08 good hgood (.while cond body) (by simpa [noCatchableRaise_g08] using hb) mid mCode
            | «break» => simp
            | _ => exact ih1
      · simp
    · simp
  | decCall name _ fn args cont =>
    have hc : good fn = true ∧ noCatchableRaise_g08 good cont = true := by
      simpa [shape, noCatchableRaise_g08, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
    · simp
    · dsimp only
      rcases hl : lookupCodeHOLFinite s.code.lookup fn values with _ | ⟨body, callee, rs⟩
      · simp
      · dsimp only
        have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup fn values = some (body, callee, rs) := by rwa [← hcode]
        have bodyOk := hgood fn hc.1 values body callee rs hl'
        split
        · simp
        · have ih1 := evaluate_noCatchableRaise_g08 good hgood body bodyOk (callEntryStateHOLFinite s callee) hcode
          have meta' := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
          rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, st⟩
          rw [hrun] at ih1 meta' cl
          dsimp only at ih1 meta' cl ⊢
          change st.clock ≤ s.clock - 1 at cl
          have small : st.clock < s.clock := by omega
          have stCode : st.code = originalRuntimeCode := meta'.1.trans hcode
          cases res with
          | none => simp
          | some r =>
            cases r with
            | returned v =>
              dsimp only
              split
              · set resumed := setVarHOLFinite name v { st with locals := s.locals }
                have smallR : resumed.clock < s.clock := small
                have rCode : resumed.code = originalRuntimeCode := stCode
                exact evaluate_noCatchableRaise_g08 good hgood cont hc.2 resumed rCode
              · simp
            | «break» => simp
            | «continue» => simp
            | _ => exact ih1
  | call tail fn args =>
    rcases tail with _ | ⟨retOpt, hdlOpt⟩
    · simp [shape, noCatchableRaise_g08] at hp
    · rcases hdlOpt with _ | _
      · have hf : good fn = true := by simpa [shape, noCatchableRaise_g08] using hp
        rw [evaluateHOLFiniteState_call]
        rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
        · simp
        · dsimp only
          rcases hl : lookupCodeHOLFinite s.code.lookup fn values with _ | ⟨body, callee, rs⟩
          · simp
          · dsimp only
            have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup fn values = some (body, callee, rs) := by rwa [← hcode]
            have bodyOk := hgood fn hf values body callee rs hl'
            split
            · simp
            · have ih1 := evaluate_noCatchableRaise_g08 good hgood body bodyOk (callEntryStateHOLFinite s callee) hcode
              have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
              rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, st⟩
              rw [hrun] at ih1 cl
              dsimp only at ih1 cl ⊢
              change st.clock ≤ s.clock - 1 at cl
              have small : st.clock < s.clock := by omega
              cases res with
              | none => simp
              | some r =>
                cases r with
                | returned _ =>
                  dsimp only
                  split
                  · rcases retOpt with _ | ⟨_, _⟩
                    · simp
                    · dsimp only; split <;> simp
                  · simp
                | «break» => simp
                | «continue» => simp
                | exception _ _ => dsimp only; exact ih1
                | timeOut => simp
                | finalFfi _ => simp
                | error => simp
      · simp [shape, noCatchableRaise_g08] at hp
  | _ => simp [shape, noCatchableRaise_g08] at hp
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals
    simp_wf
    apply lex_ncr_g08
    try subst shape
    try simp only [setVarHOLFinite, decClockHOLFinite, callEntryStateHOLFinite,
      ProgHOL.seq.sizeOf_spec, ProgHOL.ite.sizeOf_spec, ProgHOL.dec.sizeOf_spec,
      ProgHOL.while.sizeOf_spec, ProgHOL.decCall.sizeOf_spec, ProgHOL.call.sizeOf_spec, true_and]
    first
      | exact Or.inl smallR
      | exact Or.inl smaller
      | exact Or.inl small
      | omega
      | (rcases Nat.lt_or_eq_of_le mclock with h | h
         · exact Or.inl h
         · exact Or.inr ⟨h, by simp +arith⟩)
      | exact Or.inr ⟨rfl, by simp +arith⟩

private def u256NcrCallees_g08 (f : MlS) : Bool :=
  f == ofString "bswap64" ||
  f == ofString "st_be32" ||
  f == ofString "st_be64"

private theorem lookup_bswap64_g08 :
    originalRuntimeCode.lookup (ofString "bswap64") =
      some ([(ofString "x", .one)], sourceFnBody Guest.Software.guestFn_bswap64, .one) :=
  lookup_of_guestAst_getElem 23 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_bswap64) rfl

private theorem lookup_st_be32_g08 :
    originalRuntimeCode.lookup (ofString "st_be32") =
      some ([(ofString "p", .one), (ofString "v", .one)], sourceFnBody Guest.Software.guestFn_st_be32, .one) :=
  lookup_of_guestAst_getElem 27 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_st_be32) rfl

private theorem lookup_st_be64_g08 :
    originalRuntimeCode.lookup (ofString "st_be64") =
      some ([(ofString "p", .one), (ofString "v", .one)], sourceFnBody Guest.Software.guestFn_st_be64, .one) :=
  lookup_of_guestAst_getElem 28 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_st_be64) rfl

private theorem lookup_u256_to_be32_g08 :
    originalRuntimeCode.lookup (ofString "u256_to_be32") =
      some ([(ofString "a", .comb [.one, .one, .one, .one]), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_u256_to_be32, .one) :=
  lookup_of_guestAst_getElem 87 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_to_be32) rfl

private theorem u256NcrCallees_good_g08 :
    ∀ f, u256NcrCallees_g08 f = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup f values =
        some (body, callee, rs) →
      noCatchableRaise_g08 u256NcrCallees_g08 body = true := by
  have hb0 : noCatchableRaise_g08 u256NcrCallees_g08 (sourceFnBody Guest.Software.guestFn_bswap64) = true := by decide
  have hb1 : noCatchableRaise_g08 u256NcrCallees_g08 (sourceFnBody Guest.Software.guestFn_st_be32) = true := by decide
  have hb2 : noCatchableRaise_g08 u256NcrCallees_g08 (sourceFnBody Guest.Software.guestFn_st_be64) = true := by decide
  intro f hf values body callee rs hfound
  obtain ⟨params, rs', hinst⟩ := lookupCode_installed hfound
  simp only [u256NcrCallees_g08, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with (rfl | rfl) | rfl
  · rw [lookup_bswap64_g08] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; exact hb0
  · rw [lookup_st_be32_g08] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; exact hb1
  · rw [lookup_st_be64_g08] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; exact hb2

private theorem not_resumes_error_g08 : ¬ Resumes (some (.error : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

private theorem byteAlign_lt_heapEnd_g08 {s_ma : BitVec 64 → Prop} (hma : s_ma = ordinaryDomain)
    (addr : BitVec 64) (hdom : s_ma (panByteAlignHOL addr)) :
    addr.toNat < heapEnd := by
  rw [hma, ordinaryDomain_iff] at hdom
  have hal := panByteAlign_toNat64 addr
  rw [R11Shards.heapEnd_val]
  omega

private theorem word_dom_lt_heapEnd_g08 {s_ma : BitVec 64 → Prop} (hma : s_ma = ordinaryDomain)
    (addr : BitVec 64) (hdom : s_ma addr) :
    addr.toNat + 8 ≤ heapEnd := by
  rw [hma, ordinaryDomain_iff] at hdom
  rw [R11Shards.heapEnd_val]
  omega

private theorem bv_add_off_nat_g08 (base : BitVec 64) (off : Nat)
    (hbase : base.toNat < heapEnd) (hoff : off ≤ 32) :
    (base + BitVec.ofNat 64 off).toNat = base.toNat + off := by
  rw [R11Shards.heapEnd_val] at hbase
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by norm_num
  have ho_lt : off < 18446744073709551616 := by omega
  have hsum_lt : base.toNat + off < 18446744073709551616 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, h264, Nat.mod_eq_of_lt ho_lt, Nat.mod_eq_of_lt hsum_lt]

private theorem eval_var_local_g08 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nm : String) (w : BitVec 64)
    (hloc : s.locals.lookup (ofString nm) = some (.val (.word w))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString nm)) =
      some (.val (.word w)) := hloc

private theorem eval_var_local_zero_g08 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nm : String) (base : BitVec 64)
    (hloc : s.locals.lookup (ofString nm) = some (.val (.word base))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString nm)) =
      some (.val (.word (base + BitVec.ofNat 64 0))) := by
  have hz : base + BitVec.ofNat 64 0 = base := BitVec.add_zero base
  rw [hz]; exact hloc

private theorem eval_add_local_const_g08 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nm : String) (base : BitVec 64) (off : Nat)
    (hloc : s.locals.lookup (ofString nm) = some (.val (.word base))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString nm), .const (BitVec.ofNat 64 off)]) =
      some (.val (.word (base + BitVec.ofNat 64 off))) := by
  simp only [evalHOLExact, evalListHOLExact, hloc, wordOpHOL, wordOp, valueIsWord, valueWord,
    List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
  have hz : BitVec.ofNat 64 off + (0 : BitVec 64) = BitVec.ofNat 64 off := BitVec.add_zero _
  exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word (base + w)))) hz

private theorem eval_align8_eq0_g08 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nm : String) (base : BitVec 64)
    (hloc : s.locals.lookup (ofString nm) = some (.val (.word base))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.op .and [.var .local (ofString nm), .const 7#64]) (.const 0#64)) =
      some (.val (.word (if (base &&& 7#64) = 0#64 then 1 else 0))) := by
  simp only [evalHOLExact, evalListHOLExact, hloc, wordOpHOL, wordOp, valueIsWord, valueWord,
    List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
    Compiler.Encoders.Asm.wordCmpHOL]
  have h7 : (7#64 : BitVec 64) &&& 18446744073709551615#64 = 7#64 := by decide
  change some (ValueHOL.val (HolWordLab.word (if decide ((base &&& (7#64 &&& 18446744073709551615#64)) = 0#64) = true then 1 else 0))) = _
  rw [h7]
  by_cases hc : (base &&& 7#64) = 0#64 <;> simp [hc]

private theorem return_const0_step_g08 {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s (.return (.const 0#64))).1 = some (.returned (.val (.word 0))) ∧
    (evaluateHOLFiniteState s (.return (.const 0#64))).2 = emptyLocalsHOLFinite s := by
  rw [evaluateHOLFiniteState_return]
  have he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.const 0#64) = some (.val (.word 0)) := rfl
  rw [he]
  have hsz : sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
  dsimp only; rw [if_pos hsz]; exact ⟨rfl, rfl⟩

private theorem return_eff_g08 {F : Type} (s : PanSemStateFiniteExact 64 F) (ex : ExpHOL 64) (Rl : List Ivl) :
    ByteRegionEffect s (evaluateHOLFiniteState s (.return ex)).2 Rl := by
  have hret : (evaluateHOLFiniteState s (.return ex)).2 =
      { s with locals := (evaluateHOLFiniteState s (.return ex)).2.locals } := by
    rw [evaluateHOLFiniteState_return]
    split
    · rfl
    · split <;> rfl
  conv => arg 2; rw [hret]
  exact (ByteRegionEffect.refl s Rl).with_locals_clock _ s.clock

private theorem bre_of_mem_globals_eq_g08 {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (Rl : List Ivl)
    (hg : post.globals = s.globals) (hm : post.memory = s.memory)
    (hc : post.code = s.code) (hma : post.memaddrs = s.memaddrs)
    (hsh : post.shMemaddrs = s.shMemaddrs) (hba : post.baseAddr = s.baseAddr)
    (hbe : post.be = s.be) :
    ByteRegionEffect s post Rl :=
  ⟨hc, hma, hsh, hba, hbe, hg, fun _ _ => by rw [hm], fun _ _ => by rw [hm],
   fun _ _ _ => by simp [memB, hm, hbe]⟩

private theorem bswap64_body_ro_g08 {F : Type} (s : PanSemStateFiniteExact 64 F) (Rl : List Ivl) :
    ByteRegionEffect s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_bswap64)).2 Rl := by
  have hb : sourceFnBody Guest.Software.guestFn_bswap64 =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_bswap64).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_bswap64,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  have hasgn : ∀ (st : PanSemStateFiniteExact 64 F) (nm : MlS) (ex : ExpHOL 64),
      (evaluateHOLFiniteState st (.assign .local nm ex)).2 =
        { st with locals := (evaluateHOLFiniteState st (.assign .local nm ex)).2.locals } := by
    intro st nm ex; rw [evaluateHOLFiniteState_assign]; split <;> [rfl; (split <;> rfl)]
  have hseq_ro : ∀ (st : PanSemStateFiniteExact 64 F) (a b : ProgHOL 64),
      ByteRegionEffect st (evaluateHOLFiniteState st a).2 Rl →
      (∀ m, ByteRegionEffect st m Rl → ByteRegionEffect st (evaluateHOLFiniteState m b).2 Rl) →
      ByteRegionEffect st (evaluateHOLFiniteState st (.seq a b)).2 Rl := by
    intro st a b ha hb'
    rw [evaluateHOLFiniteState_seq_line780]
    rcases h1 : evaluateHOLFiniteState st a with ⟨r1, s1⟩
    rw [h1] at ha
    cases r1 with
    | none => exact hb' s1 ha
    | some _ => exact ha
  have hasgn_eff : ∀ (st : PanSemStateFiniteExact 64 F) (nm : MlS) (ex : ExpHOL 64),
      ByteRegionEffect st (evaluateHOLFiniteState st (.assign .local nm ex)).2 Rl := by
    intro st nm ex
    conv => arg 2; rw [hasgn st nm ex]
    exact (ByteRegionEffect.refl st Rl).with_locals_clock _ st.clock
  refine hseq_ro s _ _ (hasgn_eff s _ _) fun s1 hs1 => ?_
  exact hs1.trans (hseq_ro s1 _ _ (hasgn_eff s1 _ _) (fun s2 hs2 => hs2.trans (return_eff_g08 s2 _ Rl)))

private theorem bswap64_body_mem_eq_g08 {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_bswap64)).2.memory = s.memory := by
  have h := bswap64_body_ro_g08 s []
  funext a
  exact h.cell_frame a (fun _ hi => by simp at hi)

private theorem decCall_bswap64_eff_g08 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {argExp : ExpHOL 64} {cont : ProgHOL 64} {Rl : List Ivl}
    (hcode : s.code = originalRuntimeCode)
    (hcont : ∀ mid : PanSemStateFiniteExact 64 F,
      mid.code = originalRuntimeCode →
      mid.memaddrs = s.memaddrs →
      mid.locals.lookup (ofString "out") = s.locals.lookup (ofString "out") →
      mid.locals.lookup (ofString "p") = s.locals.lookup (ofString "p") →
      mid.locals.lookup (ofString "a") = s.locals.lookup (ofString "a") →
      (∃ wv : BitVec 64, mid.locals.lookup (ofString "w") = some (.val (.word wv))) →
      ByteRegionEffect mid (evaluateHOLFiniteState mid cont).2 Rl) :
    ByteRegionEffect s
      (evaluateHOLFiniteState s (.decCall (ofString "w") .one (ofString "bswap64") [argExp] cont)).2
      Rl := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [argExp] with _ | vals
  · exact ByteRegionEffect.refl s Rl
  · dsimp only
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "bswap64") vals with _ | ⟨body', callee, ret'⟩
    · exact ByteRegionEffect.refl s Rl
    · dsimp only
      have hinst := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "bswap64")
        _ _ body' _ ret' vals callee (by rw [hcode]; exact lookup_bswap64_g08) hl
      subst hinst
      have hret_eq : ret' = .one := by
        unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
        split at hl
        · cases hl
        · rename_i eb el es hraw
          have hinj := Option.some.inj hl
          rcases Prod.mk.inj hinj with ⟨_, hr2⟩; rcases Prod.mk.inj hr2 with ⟨_, rfl⟩
          unfold lookupCodeHOLExact at hraw; rw [hcode, lookup_bswap64_g08] at hraw; dsimp only at hraw
          split at hraw <;> [ (injection hraw with h'; exact (Prod.mk.inj (Prod.mk.inj h').2).2.symm); cases hraw ]
      subst hret_eq
      split
      · exact (ByteRegionEffect.refl s Rl).with_locals_clock _ _
      · have heff_entry : ByteRegionEffect s (callEntryStateHOLFinite s callee) Rl :=
          (ByteRegionEffect.refl s Rl).with_locals_clock _ _
        have heff_b := bswap64_body_ro_g08 (callEntryStateHOLFinite s callee) Rl
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
            (sourceFnBody Guest.Software.guestFn_bswap64) with ⟨rb, sb⟩
        rw [hb] at heff_b; dsimp only at heff_b ⊢
        have heff_sb : ByteRegionEffect s sb Rl := heff_entry.trans heff_b
        cases rb with
        | none => exact heff_sb
        | some r =>
          cases r with
          | returned v =>
            dsimp only; split
            · rename_i hsh
              have hvw : ∃ wv : BitVec 64, v = .val (.word wv) := by
                rcases v with ⟨⟨wv⟩⟩ | _ | _ <;>
                  [exact ⟨wv, rfl⟩; simp [shapeOfHOLExact, shapeEqHOL] at hsh; simp [shapeOfHOLExact, shapeEqHOL] at hsh]
              obtain ⟨wv, rfl⟩ := hvw
              let mid := setVarHOLFinite (ofString "w") (.val (.word wv)) { sb with locals := s.locals }
              have heff_mid : ByteRegionEffect s mid Rl := heff_sb.with_locals_clock _ _
              have hc_mid : mid.code = originalRuntimeCode := heff_mid.code.trans hcode
              have hm_mid : mid.memaddrs = s.memaddrs := heff_mid.memaddrs
              have hout_mid : mid.locals.lookup (ofString "out") = s.locals.lookup (ofString "out") := by
                simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "w" ≠ ofString "out" by decide]
              have hp_mid : mid.locals.lookup (ofString "p") = s.locals.lookup (ofString "p") := by
                simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "w" ≠ ofString "p" by decide]
              have ha_mid : mid.locals.lookup (ofString "a") = s.locals.lookup (ofString "a") := by
                simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "w" ≠ ofString "a" by decide]
              have hw_mid : ∃ wv : BitVec 64, mid.locals.lookup (ofString "w") = some (.val (.word wv)) :=
                ⟨wv, by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
              exact (heff_mid.trans (hcont mid hc_mid hm_mid hout_mid hp_mid ha_mid hw_mid)).with_locals_clock _ _
            · exact heff_sb
          | timeOut | error | exception _ _ | finalFfi _ => exact heff_sb.with_locals_clock _ _
          | «break» | «continue» => exact heff_sb

private theorem seq_call_bswap64_eff_g08 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {argExp : ExpHOL 64} {cont : ProgHOL 64} {Rl : List Ivl}
    (hcode : s.code = originalRuntimeCode)
    (hcont : ∀ mid : PanSemStateFiniteExact 64 F,
      mid.code = originalRuntimeCode →
      mid.memaddrs = s.memaddrs →
      mid.locals.lookup (ofString "out") = s.locals.lookup (ofString "out") →
      mid.locals.lookup (ofString "a") = s.locals.lookup (ofString "a") →
      (∃ wv : BitVec 64, mid.locals.lookup (ofString "w") = some (.val (.word wv))) →
      ByteRegionEffect mid (evaluateHOLFiniteState mid cont).2 Rl) :
    ByteRegionEffect s
      (evaluateHOLFiniteState s
        (.seq (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [argExp]) cont)).2
      Rl := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hc : evaluateHOLFiniteState s
      (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [argExp]) with ⟨rc, sc⟩
  rw [evaluateHOLFiniteState_call] at hc
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [argExp] with _ | vals
  · rw [hargs] at hc; injection hc with hr hsc; subst hr hsc; exact ByteRegionEffect.refl s Rl
  · rw [hargs] at hc; dsimp only at hc
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "bswap64") vals with _ | ⟨body', callee, ret'⟩
    · rw [hl] at hc; injection hc with hr hsc; subst hr hsc; exact ByteRegionEffect.refl s Rl
    · rw [hl] at hc; dsimp only at hc
      have hinst := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "bswap64")
        _ _ body' _ ret' vals callee (by rw [hcode]; exact lookup_bswap64_g08) hl
      subst hinst
      have hret_eq : ret' = .one := by
        unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
        split at hl
        · cases hl
        · rename_i eb el es hraw
          have hinj := Option.some.inj hl
          rcases Prod.mk.inj hinj with ⟨_, hr2⟩; rcases Prod.mk.inj hr2 with ⟨_, rfl⟩
          unfold lookupCodeHOLExact at hraw; rw [hcode, lookup_bswap64_g08] at hraw; dsimp only at hraw
          split at hraw <;> [ (injection hraw with h'; exact (Prod.mk.inj (Prod.mk.inj h').2).2.symm); cases hraw ]
      subst hret_eq
      split at hc
      · injection hc with hr hsc; subst hr hsc; exact (ByteRegionEffect.refl s Rl).with_locals_clock _ _
      · have heff_entry : ByteRegionEffect s (callEntryStateHOLFinite s callee) Rl :=
          (ByteRegionEffect.refl s Rl).with_locals_clock _ _
        have heff_b := bswap64_body_ro_g08 (callEntryStateHOLFinite s callee) Rl
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
            (sourceFnBody Guest.Software.guestFn_bswap64) with ⟨rb, sb⟩
        rw [hb] at hc heff_b; dsimp only at heff_b
        have heff_sb : ByteRegionEffect s sb Rl := heff_entry.trans heff_b
        cases rb with
        | none => injection hc with hr hsc; subst hr hsc; exact heff_sb
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hc; split at hc
            · rename_i hsh
              have hvw : ∃ wv : BitVec 64, v = .val (.word wv) := by
                rcases v with ⟨⟨wv⟩⟩ | _ | _ <;>
                  [exact ⟨wv, rfl⟩; simp [shapeOfHOLExact, shapeEqHOL] at hsh; simp [shapeOfHOLExact, shapeEqHOL] at hsh]
              obtain ⟨wv, rfl⟩ := hvw
              split at hc
              · injection hc with hr hsc; subst hr hsc; dsimp only
                let mid := setKvarHOLFinite .local (ofString "w") (.val (.word wv)) { sb with locals := s.locals }
                have heff_mid : ByteRegionEffect s mid Rl := heff_sb.with_locals_clock _ _
                have hc_mid : mid.code = originalRuntimeCode := heff_mid.code.trans hcode
                have hm_mid : mid.memaddrs = s.memaddrs := heff_mid.memaddrs
                have hout_mid : mid.locals.lookup (ofString "out") = s.locals.lookup (ofString "out") := by
                  simp [mid, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                    show ofString "w" ≠ ofString "out" by decide]
                have ha_mid : mid.locals.lookup (ofString "a") = s.locals.lookup (ofString "a") := by
                  simp [mid, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                    show ofString "w" ≠ ofString "a" by decide]
                have hw_mid : ∃ wv : BitVec 64, mid.locals.lookup (ofString "w") = some (.val (.word wv)) :=
                  ⟨wv, by simp [mid, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
                exact heff_mid.trans (hcont mid hc_mid hm_mid hout_mid ha_mid hw_mid)
              · injection hc with hr hsc; subst hr hsc; exact heff_sb
            · injection hc with hr hsc; subst hr hsc; exact heff_sb
          | timeOut | error | exception _ _ | finalFfi _ =>
            injection hc with hr hsc; subst hr hsc; exact heff_sb.with_locals_clock _ _
          | «break» | «continue» =>
            injection hc with hr hsc; subst hr hsc; exact heff_sb

private theorem seq_store_word_eff_g08 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {dstExp valExp : ExpHOL 64} {base w : BitVec 64} {off len : Nat} {cont : ProgHOL 64}
    (hma : s.memaddrs = ordinaryDomain) (hlen : len ≤ 32) (hoff : off + 8 ≤ len)
    (hprev : off > 0 → base.toNat < heapEnd)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word (base + BitVec.ofNat 64 off))))
    (hval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
      some (.val (.word w)))
    (hcont : ∀ s1 : PanSemStateFiniteExact 64 F,
      base.toNat < heapEnd → s1.code = s.code → s1.memaddrs = s.memaddrs → s1.locals = s.locals →
      ByteRegionEffect s1 (evaluateHOLFiniteState s1 cont).2 [(base.toNat, len)]) :
    ByteRegionEffect s (evaluateHOLFiniteState s (.seq (.store dstExp valExp) cont)).2 [(base.toNat, len)] := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases h1 : evaluateHOLFiniteState s (.store dstExp valExp) with ⟨r1, s1⟩
  cases r1 with
  | some _ =>
    have h1' := h1
    rw [evaluateHOLFiniteState_store, hdst, hval] at h1'; dsimp only at h1'
    split at h1'
    · cases h1'
    · injection h1' with _ hs1; subst hs1; exact ByteRegionEffect.refl s _
  | none =>
    have hbase_lt : base.toNat < heapEnd := by
      have hrun' := h1
      rw [evaluateHOLFiniteState_store, hdst, hval] at hrun'; dsimp only at hrun'
      split at hrun'
      · rename_i m' hst
        unfold flattenHOL panMemStoresHOL panMemStoreHOL at hst
        by_cases hd : s.memaddrs (base + BitVec.ofNat 64 off)
        · by_cases hz : off = 0
          · subst hz; have h0 : base + BitVec.ofNat 64 0 = base := by simp
            rw [h0] at hd; have := word_dom_lt_heapEnd_g08 hma base hd; omega
          · exact hprev (by omega)
        · simp [hd] at hst
      · cases hrun'
    have heff1 := ByteRegionEffect.of_store_word (Rl := [(base.toNat, len)]) hma h1
      (fun v hv => by rw [hval] at hv; injection hv with h; exact ⟨w, h.symm⟩)
      (fun addr ha _ => by
        rw [hdst] at ha
        injection ha with e1; injection e1 with e2; injection e2 with e3; subst e3
        have hnat := bv_add_off_nat_g08 base off hbase_lt (by omega)
        exact ⟨(base.toNat, len), List.mem_singleton.2 rfl, by rw [hnat]; omega, by rw [hnat]; omega⟩)
    exact heff1.1.trans (hcont s1 hbase_lt heff1.1.code heff1.1.memaddrs heff1.2)

private theorem seq_storeByte_eff_g08 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {dstExp valExp : ExpHOL 64} {base : BitVec 64} {off len : Nat} {cont : ProgHOL 64}
    (hma : s.memaddrs = ordinaryDomain) (hlen : len ≤ 32) (hoff : off < len)
    (hprev : off > 0 → base.toNat < heapEnd)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word (base + BitVec.ofNat 64 off))))
    (hcont : ∀ s1 : PanSemStateFiniteExact 64 F,
      base.toNat < heapEnd → s1.code = s.code → s1.memaddrs = s.memaddrs → s1.locals = s.locals →
      ByteRegionEffect s1 (evaluateHOLFiniteState s1 cont).2 [(base.toNat, len)]) :
    ByteRegionEffect s (evaluateHOLFiniteState s (.seq (.storeByte dstExp valExp) cont)).2 [(base.toNat, len)] := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases h1 : evaluateHOLFiniteState s (.storeByte dstExp valExp) with ⟨r1, s1⟩
  cases r1 with
  | some _ =>
    have h1' := h1
    rw [evaluateHOLFiniteState_storeByte, hdst] at h1'
    rcases hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp with _ | vv
    · rw [hv] at h1'; dsimp only at h1'; injection h1' with _ hs1; subst hs1; exact ByteRegionEffect.refl s _
    · rw [hv] at h1'
      rcases vv with ⟨⟨v⟩⟩ | _ | _
      · dsimp only at h1'; split at h1'
        · cases h1'
        · injection h1' with _ hs1; subst hs1; exact ByteRegionEffect.refl s _
      · dsimp only at h1'; injection h1' with _ hs1; subst hs1; exact ByteRegionEffect.refl s _
      · dsimp only at h1'; injection h1' with _ hs1; subst hs1; exact ByteRegionEffect.refl s _
  | none =>
    have hbase_lt_of_dom : s.memaddrs (panByteAlignHOL (base + BitVec.ofNat 64 off)) → base.toNat < heapEnd := by
      intro hd
      by_cases hz : off = 0
      · subst hz; have h0 : base + BitVec.ofNat 64 0 = base := by simp
        rw [h0] at hd; exact byteAlign_lt_heapEnd_g08 hma base hd
      · exact hprev (by omega)
    have hbase_lt : base.toNat < heapEnd := by
      have hrun' := h1
      rw [evaluateHOLFiniteState_storeByte, hdst] at hrun'
      rcases hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp with _ | vv
      · rw [hv] at hrun'; simp at hrun'
      · rw [hv] at hrun'
        rcases vv with ⟨⟨v⟩⟩ | _ | _
        · dsimp only at hrun'; split at hrun'
          · rename_i m' hst
            unfold panMemStoreByteWord8HOL at hst
            rcases hm : s.memory (panByteAlignHOL (base + BitVec.ofNat 64 off)) with ⟨cell⟩
            have hm' : (s.memory (panByteAlignHOL (base + BitVec.ofNat 64 off))).1 = cell := by rw [hm]
            dsimp only at hst; rw [hm'] at hst
            by_cases hd : s.memaddrs (panByteAlignHOL (base + BitVec.ofNat 64 off))
            · exact hbase_lt_of_dom hd
            · simp [hd] at hst
          · simp at hrun'
        · simp at hrun'
        · simp at hrun'
    have heff1 := ByteRegionEffect.of_storeByte (Rl := [(base.toNat, len)]) h1
      (fun addr ha _ => by
        rw [hdst] at ha
        injection ha with e1; injection e1 with e2; injection e2 with e3; subst e3
        have hnat := bv_add_off_nat_g08 base off hbase_lt (by omega)
        exact ⟨(base.toNat, len), List.mem_singleton.2 rfl, by rw [hnat]; omega, by rw [hnat]; omega⟩)
    exact heff1.1.trans (hcont s1 hbase_lt heff1.1.code heff1.1.memaddrs heff1.2)

private theorem st_be32_body_eff_g08 {F : Type} (s : PanSemStateFiniteExact 64 F) (p : BitVec 64)
    (hma : s.memaddrs = ordinaryDomain)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word p))) :
    ByteRegionEffect s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_st_be32)).2 [(p.toNat, 4)] ∧
    ((evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_st_be32)).2.memory = s.memory ∨ p.toNat < heapEnd) ∧
    (∀ rv, (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_st_be32)).1 = some (.returned rv) →
      p.toNat < heapEnd) := by
  have hb : sourceFnBody Guest.Software.guestFn_st_be32 =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_st_be32).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_st_be32,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural]
  have hp_ev0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString "p")) = some (.val (.word p)) := hp
  have hmem_or_lt :
      ((evaluateHOLFiniteState s
        (.seq (.storeByte (.var .local (ofString "p")) (.shift .lsr (.var .local (ofString "v")) (.const 24#64)))
          (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 1#64]) (.shift .lsr (.var .local (ofString "v")) (.const 16#64)))
            (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 2#64]) (.shift .lsr (.var .local (ofString "v")) (.const 8#64)))
              (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 3#64]) (.var .local (ofString "v")))
                (.return (.const 0#64))))))).2.memory = s.memory ∧
       ∀ rv, (evaluateHOLFiniteState s
        (.seq (.storeByte (.var .local (ofString "p")) (.shift .lsr (.var .local (ofString "v")) (.const 24#64)))
          (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 1#64]) (.shift .lsr (.var .local (ofString "v")) (.const 16#64)))
            (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 2#64]) (.shift .lsr (.var .local (ofString "v")) (.const 8#64)))
              (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 3#64]) (.var .local (ofString "v")))
                (.return (.const 0#64))))))).1 ≠ some (.returned rv)) ∨ p.toNat < heapEnd := by
    rw [evaluateHOLFiniteState_seq_line780]
    rcases h1 : evaluateHOLFiniteState s
        (.storeByte (.var .local (ofString "p")) (.shift .lsr (.var .local (ofString "v")) (.const 24#64))) with ⟨r1, s1⟩
    rw [evaluateHOLFiniteState_storeByte, hp_ev0] at h1
    rcases hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.shift .lsr (.var .local (ofString "v")) (.const 24#64)) with _ | vv
    · rw [hv] at h1; dsimp only at h1; injection h1 with hr1 hs1; subst hr1 hs1
      exact Or.inl ⟨rfl, by simp⟩
    · rw [hv] at h1
      rcases vv with ⟨⟨vw⟩⟩ | _ | _
      · dsimp only at h1; split at h1
        · rename_i m' hst
          unfold panMemStoreByteWord8HOL at hst
          rcases hm : s.memory (panByteAlignHOL p) with ⟨cell⟩
          have hm' : (s.memory (panByteAlignHOL p)).1 = cell := by rw [hm]
          dsimp only at hst; rw [hm'] at hst
          by_cases hd : s.memaddrs (panByteAlignHOL p)
          · exact Or.inr (byteAlign_lt_heapEnd_g08 hma p hd)
          · simp [hd] at hst
        · injection h1 with hr1 hs1; subst hr1 hs1; exact Or.inl ⟨rfl, by simp⟩
      · dsimp only at h1; injection h1 with hr1 hs1; subst hr1 hs1; exact Or.inl ⟨rfl, by simp⟩
      · dsimp only at h1; injection h1 with hr1 hs1; subst hr1 hs1; exact Or.inl ⟨rfl, by simp⟩
  refine ⟨?_, ?_, ?_⟩
  · refine seq_storeByte_eff_g08 (base := p) (off := 0) (len := 4) hma (by omega) (by omega) (fun h => by omega)
      (eval_var_local_zero_g08 s "p" p hp) fun s1 hp_lt _ hm1 hl1 => ?_
    have hp1 : s1.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hl1]; exact hp
    refine seq_storeByte_eff_g08 (s := s1) (base := p) (off := 1) (len := 4) (hm1.trans hma) (by omega) (by omega)
      (fun _ => hp_lt) (eval_add_local_const_g08 s1 "p" p 1 hp1) fun s2 _ _ hm2 hl2 => ?_
    have hp2 : s2.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hl2]; exact hp1
    refine seq_storeByte_eff_g08 (s := s2) (base := p) (off := 2) (len := 4) (hm2.trans (hm1.trans hma)) (by omega) (by omega)
      (fun _ => hp_lt) (eval_add_local_const_g08 s2 "p" p 2 hp2) fun s3 _ _ hm3 hl3 => ?_
    have hp3 : s3.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hl3]; exact hp2
    refine seq_storeByte_eff_g08 (s := s3) (base := p) (off := 3) (len := 4) (hm3.trans (hm2.trans (hm1.trans hma))) (by omega) (by omega)
      (fun _ => hp_lt) (eval_add_local_const_g08 s3 "p" p 3 hp3) fun s4 _ _ _ _ => return_eff_g08 s4 _ _
  · rcases hmem_or_lt with ⟨hm_eq, _⟩ | hp_lt <;> [exact Or.inl hm_eq; exact Or.inr hp_lt]
  · intro rv hret; rcases hmem_or_lt with ⟨_, hne⟩ | hp_lt <;> [exact absurd hret (hne rv); exact hp_lt]

private theorem lookup_two_words_reject_nonword_g08 {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (fname p1 p2 : MlS) (body : ProgHOL width) (w1 : BitVec width) (v2 : ValueHOL width)
    (hlook : code fname = some ([(p1, .one), (p2, .one)], body, .one))
    (hnot : ∀ w2 : BitVec width, v2 ≠ .val (.word w2)) :
    lookupCodeHOLFinite code fname [.val (.word w1), v2] = none := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rfl
  · rename_i eb el es hraw
    unfold lookupCodeHOLExact at hraw; rw [hlook] at hraw
    rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;>
      [exact absurd rfl (hnot w2); simp [shapeOfHOLExact, shapeEqHOL] at hraw; simp [shapeOfHOLExact, shapeEqHOL] at hraw]

private theorem seq_call_st_be32_eff_g08 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {pExp vExp : ExpHOL 64} {base : BitVec 64} {off len : Nat} {cont : ProgHOL 64}
    (hcode : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain)
    (hlen : len ≤ 32) (hoff : off + 4 ≤ len) (hprev : off > 0 → base.toNat < heapEnd)
    (hp_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) pExp =
      some (.val (.word (base + BitVec.ofNat 64 off))))
    (hcont : ∀ s1 : PanSemStateFiniteExact 64 F,
      base.toNat < heapEnd → s1.code = originalRuntimeCode → s1.memaddrs = ordinaryDomain → s1.locals = s.locals →
      ByteRegionEffect s1 (evaluateHOLFiniteState s1 cont).2 [(base.toNat, len)]) :
    ByteRegionEffect s
      (evaluateHOLFiniteState s (.seq (.call (some (none, none)) (ofString "st_be32") [pExp, vExp]) cont)).2
      [(base.toNat, len)] := by
  let pArg := base + BitVec.ofNat 64 off
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hc : evaluateHOLFiniteState s (.call (some (none, none)) (ofString "st_be32") [pExp, vExp]) with ⟨rc, sc⟩
  rw [evaluateHOLFiniteState_call] at hc
  rcases hv_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) vExp with _ | vv
  · have hnone : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [pExp, vExp] = none := by
      simp [evalListHOLFinite, evalListHOLExact, hp_ev, hv_ev]
    rw [hnone] at hc; injection hc with hr hsc; subst hr hsc; exact ByteRegionEffect.refl s _
  · have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [pExp, vExp] =
        some [.val (.word pArg), vv] := by
      simp [evalListHOLFinite, evalListHOLExact, hp_ev, hv_ev, pArg]
    rw [hargs] at hc; dsimp only at hc
    by_cases hvw : ∃ vW : BitVec 64, vv = .val (.word vW)
    · obtain ⟨vW, rfl⟩ := hvw
      have hl := pan_two_word_lookup s.code.lookup (ofString "st_be32") (ofString "p") (ofString "v")
        (sourceFnBody Guest.Software.guestFn_st_be32) pArg vW (by decide) (by rw [hcode]; exact lookup_st_be32_g08)
      rw [hl] at hc; dsimp only at hc
      split at hc
      · injection hc with hr hsc; subst hr hsc; exact (ByteRegionEffect.refl s _).with_locals_clock _ _
      · let entry := callEntryStateHOLFinite s
          ((HolFiniteMapExact.empty.update (ofString "p", .val (.word pArg))).update (ofString "v", .val (.word vW)))
        have hp_in : entry.locals.lookup (ofString "p") = some (.val (.word pArg)) := by
          simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "v" ≠ ofString "p" by decide]
        obtain ⟨heff_b, hlt_or_eq, hlt_b⟩ := st_be32_body_eff_g08 entry pArg hma hp_in
        rcases hb : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_st_be32) with ⟨rb, sb⟩
        have hb_entry : evaluateHOLFiniteState
            (callEntryStateHOLFinite s
              ((HolFiniteMapExact.empty.update (ofString "p", .val (.word pArg))).update (ofString "v", .val (.word vW))))
            (sourceFnBody Guest.Software.guestFn_st_be32) = (rb, sb) := hb
        rw [hb_entry] at hc; rw [hb] at heff_b hlt_or_eq; dsimp only at heff_b hlt_or_eq
        have heff_entry : ByteRegionEffect s entry [(base.toNat, len)] :=
          (ByteRegionEffect.refl s _).with_locals_clock _ _
        have heff_sb : ByteRegionEffect s sb [(base.toNat, len)] := by
          rcases hlt_or_eq with hmem_eq | hpArg_lt
          · exact bre_of_mem_globals_eq_g08 [(base.toNat, len)]
              heff_b.globals hmem_eq heff_b.code heff_b.memaddrs heff_b.shMemaddrs heff_b.baseAddr heff_b.be
          · have hbase_lt : base.toNat < heapEnd := by
              by_cases hz_off : off = 0
              · subst hz_off; have h0 : pArg = base := by simp [pArg]
                rwa [h0] at hpArg_lt
              · exact hprev (by omega)
            have hpArg_nat : pArg.toNat = base.toNat + off := bv_add_off_nat_g08 base off hbase_lt (by omega)
            exact heff_entry.trans (heff_b.mono fun i hi => by
              simp only [List.mem_singleton] at hi; subst hi
              exact ⟨(base.toNat, len), List.mem_singleton.2 rfl, by rw [hpArg_nat]; omega, by rw [hpArg_nat]; omega⟩)
        cases rb with
        | none => injection hc with hr hsc; subst hr hsc; exact heff_sb
        | some r =>
          cases r with
          | returned rv =>
            dsimp only at hc; split at hc
            · injection hc with hr hsc; subst hr hsc; dsimp only
              have hpArg_lt := hlt_b rv (by rw [hb])
              have hbase_lt : base.toNat < heapEnd := by
                by_cases hz_off : off = 0
                · subst hz_off; have h0 : pArg = base := by simp [pArg]
                  rwa [h0] at hpArg_lt
                · exact hprev (by omega)
              let s1 : PanSemStateFiniteExact 64 F := { sb with locals := s.locals }
              have heff_s1 : ByteRegionEffect s s1 [(base.toNat, len)] := heff_sb.with_locals_clock _ _
              exact heff_s1.trans (hcont s1 hbase_lt (heff_s1.code.trans hcode) (heff_s1.memaddrs.trans hma) rfl)
            · injection hc with hr hsc; subst hr hsc; exact heff_sb
          | timeOut | error | exception _ _ | finalFfi _ =>
            injection hc with hr hsc; subst hr hsc; exact heff_sb.with_locals_clock _ _
          | «break» | «continue» =>
            injection hc with hr hsc; subst hr hsc; exact heff_sb
    · have hln := lookup_two_words_reject_nonword_g08 s.code.lookup (ofString "st_be32") (ofString "p") (ofString "v")
        _ pArg vv (by rw [hcode]; exact lookup_st_be32_g08) (fun w hw => hvw ⟨w, hw⟩)
      rw [hln] at hc; injection hc with hr hsc; subst hr hsc; exact ByteRegionEffect.refl s _

private theorem st_be64_body_eff_g08 {F : Type} (s : PanSemStateFiniteExact 64 F) (p : BitVec 64)
    (hcode : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word p))) :
    ByteRegionEffect s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_st_be64)).2 [(p.toNat, 8)] ∧
    ((evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_st_be64)).2.memory = s.memory ∨ p.toNat < heapEnd) ∧
    (∀ rv, (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_st_be64)).1 = some (.returned rv) →
      p.toNat < heapEnd) := by
  have hb : sourceFnBody Guest.Software.guestFn_st_be64 =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_st_be64).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_st_be64,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    List.map, Option.map]
  have hcond := eval_align8_eq0_g08 s "p" p hp
  by_cases hal : (p &&& 7#64) = 0#64
  · let yesProg : ProgHOL 64 :=
      .decCall (ofString "w") .one (ofString "bswap64") [.var .local (ofString "v")]
        (.seq (.store (.var .local (ofString "p")) (.var .local (ofString "w")))
          (.return (.const 0#64)))
    have hyes_info :
        (evaluateHOLFiniteState s yesProg).1 ≠ none ∧
        (((evaluateHOLFiniteState s yesProg).2.memory = s.memory ∧
          ∀ rv, (evaluateHOLFiniteState s yesProg).1 ≠ some (.returned rv)) ∨ p.toNat < heapEnd) := by
      dsimp only [yesProg]
      rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
      rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.var .local (ofString "v")] with _ | vals
      · exact ⟨by simp, Or.inl ⟨rfl, by simp⟩⟩
      · dsimp only
        rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "bswap64") vals with _ | ⟨b', cal', rs'⟩
        · exact ⟨by simp, Or.inl ⟨rfl, by simp⟩⟩
        · dsimp only
          have hinst := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "bswap64")
            _ _ b' _ rs' vals cal' (by rw [hcode]; exact lookup_bswap64_g08) hl
          subst hinst
          have hrs_eq : rs' = .one := by
            unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
            split at hl
            · cases hl
            · rename_i eb el es hraw
              have hinj := Option.some.inj hl
              rcases Prod.mk.inj hinj with ⟨_, hr2⟩; rcases Prod.mk.inj hr2 with ⟨_, rfl⟩
              unfold lookupCodeHOLExact at hraw; rw [hcode, lookup_bswap64_g08] at hraw; dsimp only at hraw
              split at hraw <;> [ (injection hraw with h'; exact (Prod.mk.inj (Prod.mk.inj h').2).2.symm); cases hraw ]
          subst hrs_eq
          split
          · exact ⟨by simp, Or.inl ⟨rfl, by simp⟩⟩
          · have hro0 := bswap64_body_ro_g08 (callEntryStateHOLFinite s cal') []
            have hmem0 := bswap64_body_mem_eq_g08 (callEntryStateHOLFinite s cal')
            rcases hb_run : evaluateHOLFiniteState (callEntryStateHOLFinite s cal')
                (sourceFnBody Guest.Software.guestFn_bswap64) with ⟨rb, sb⟩
            rw [hb_run] at hro0 hmem0; dsimp only at hro0 hmem0 ⊢
            have hsb_ma : sb.memaddrs = ordinaryDomain := hro0.memaddrs.trans hma
            cases rb with
            | none => exact ⟨by simp, Or.inl ⟨hmem0, by simp⟩⟩
            | some r =>
              cases r with
              | returned v =>
                dsimp only; split
                · rename_i hsh_v
                  have hvw : ∃ wv : BitVec 64, v = .val (.word wv) := by
                    rcases v with ⟨⟨wv⟩⟩ | _ | _ <;>
                      [exact ⟨wv, rfl⟩; simp [shapeOfHOLExact, shapeEqHOL] at hsh_v; simp [shapeOfHOLExact, shapeEqHOL] at hsh_v]
                  obtain ⟨wv, rfl⟩ := hvw
                  let mid := setVarHOLFinite (ofString "w") (.val (.word wv)) { sb with locals := s.locals }
                  have hp_mid : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
                      (.var .local (ofString "p")) = some (.val (.word p)) := by
                    simp [evalHOLExact, mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp,
                      show ofString "w" ≠ ofString "p" by decide]
                  have hw_mid : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
                      (.var .local (ofString "w")) = some (.val (.word wv)) := by
                    simp [evalHOLExact, mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  rw [evaluateHOLFiniteState_seq_line780]
                  rcases hst_pair : evaluateHOLFiniteState mid
                      (.store (.var .local (ofString "p")) (.var .local (ofString "w"))) with ⟨rst, sst⟩
                  rw [evaluateHOLFiniteState_store, hp_mid, hw_mid] at hst_pair
                  dsimp only at hst_pair
                  split at hst_pair
                  · rename_i m' hst_p
                    injection hst_pair with hrst hsst; subst hrst hsst
                    unfold flattenHOL panMemStoresHOL panMemStoreHOL at hst_p
                    by_cases hd : sb.memaddrs p
                    · dsimp only; rw [(return_const0_step_g08 _).1]
                      exact ⟨by simp, Or.inr (by have := word_dom_lt_heapEnd_g08 hsb_ma p hd; omega)⟩
                    · have hdm : ¬ mid.memaddrs p := hd
                      simp [hdm] at hst_p
                  · injection hst_pair with hrst hsst; subst hrst hsst
                    exact ⟨by simp, Or.inl ⟨hmem0, by simp⟩⟩
                · exact ⟨by simp, Or.inl ⟨hmem0, by simp⟩⟩
              | timeOut | error | exception _ _ | finalFfi _ | «break» | «continue» =>
                exact ⟨by simp, Or.inl ⟨hmem0, by simp⟩⟩
    have hnn := hyes_info.1
    have hml := hyes_info.2
    have hgoal_ite : evaluateHOLFiniteState s
        (.seq (.ite (.cmp .equal (.op .and [.var .local (ofString "p"), .const 7#64]) (.const 0#64)) yesProg .skip)
          (.seq (.call (some (none, none)) (ofString "st_be32")
              [.var .local (ofString "p"), .shift .lsr (.var .local (ofString "v")) (.const 32#64)])
            (.seq (.call (some (none, none)) (ofString "st_be32")
                [.op .add [.var .local (ofString "p"), .const 4#64], .var .local (ofString "v")])
              (.return (.const 0#64))))) = evaluateHOLFiniteState s yesProg := by
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hcond]
      simp only [hal, ↓reduceIte]
      have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
      rw [if_neg h10]
      rcases hy : evaluateHOLFiniteState s yesProg with ⟨ry, sy⟩
      rw [hy] at hnn
      cases ry with
      | none => exact absurd rfl hnn
      | some _ => rfl
    rw [hgoal_ite]
    have heff_yes : ByteRegionEffect s (evaluateHOLFiniteState s yesProg).2 [(p.toNat, 8)] :=
      decCall_bswap64_eff_g08 (s := s) (argExp := .var .local (ofString "v"))
        (Rl := [(p.toNat, 8)]) hcode fun mid _ hm_mid _ hp_mid _ ⟨wv, hw_mid⟩ => by
          have hp_m : mid.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hp_mid]; exact hp
          exact seq_store_word_eff_g08 (s := mid) (base := p) (w := wv) (off := 0) (len := 8)
            (hm_mid.trans hma) (by omega) (by omega) (fun h => by omega)
            (eval_var_local_zero_g08 mid "p" p hp_m)
            (eval_var_local_g08 mid "w" wv hw_mid) fun s1 _ _ _ _ => return_eff_g08 s1 _ _
    refine ⟨heff_yes, ?_, ?_⟩
    · rcases hml with ⟨hm_eq, _⟩ | hp_lt <;> [exact Or.inl hm_eq; exact Or.inr hp_lt]
    · intro rv hret; rcases hml with ⟨_, hne⟩ | hp_lt <;> [exact absurd hret (hne rv); exact hp_lt]
  · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hcond]
    simp only [hal, ↓reduceIte, evaluateHOLFiniteState_skip]
    have hp_ev0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.var .local (ofString "p")) = some (.val (.word p)) := hp
    have hfirst_call :
        ((evaluateHOLFiniteState s
          (.seq (.call (some (none, none)) (ofString "st_be32")
              [.var .local (ofString "p"), .shift .lsr (.var .local (ofString "v")) (.const 32#64)])
            (.seq (.call (some (none, none)) (ofString "st_be32")
                [.op .add [.var .local (ofString "p"), .const 4#64], .var .local (ofString "v")])
              (.return (.const 0#64))))).2.memory = s.memory ∧
         ∀ rv, (evaluateHOLFiniteState s
          (.seq (.call (some (none, none)) (ofString "st_be32")
              [.var .local (ofString "p"), .shift .lsr (.var .local (ofString "v")) (.const 32#64)])
            (.seq (.call (some (none, none)) (ofString "st_be32")
                [.op .add [.var .local (ofString "p"), .const 4#64], .var .local (ofString "v")])
              (.return (.const 0#64))))).1 ≠ some (.returned rv)) ∨ p.toNat < heapEnd := by
      rw [evaluateHOLFiniteState_seq_line780]
      rcases hc1 : evaluateHOLFiniteState s
          (.call (some (none, none)) (ofString "st_be32")
            [.var .local (ofString "p"), .shift .lsr (.var .local (ofString "v")) (.const 32#64)]) with ⟨rc1, sc1⟩
      dsimp only
      rw [evaluateHOLFiniteState_call] at hc1
      rcases hv_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.shift .lsr (.var .local (ofString "v")) (.const 32#64)) with _ | vv
      · have hnone : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
            [.var .local (ofString "p"), .shift .lsr (.var .local (ofString "v")) (.const 32#64)] = none := by
          simp [evalListHOLFinite, evalListHOLExact, hp_ev0, hv_ev]
        rw [hnone] at hc1; injection hc1 with hr hsc1; subst hr hsc1; exact Or.inl ⟨rfl, by simp⟩
      · have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
            [.var .local (ofString "p"), .shift .lsr (.var .local (ofString "v")) (.const 32#64)] =
            some [.val (.word p), vv] := by
          simp [evalListHOLFinite, evalListHOLExact, hp_ev0, hv_ev]
        rw [hargs] at hc1; dsimp only at hc1
        by_cases hvw : ∃ vW : BitVec 64, vv = .val (.word vW)
        · obtain ⟨vW, rfl⟩ := hvw
          have hl := pan_two_word_lookup s.code.lookup (ofString "st_be32") (ofString "p") (ofString "v")
            (sourceFnBody Guest.Software.guestFn_st_be32) p vW (by decide) (by rw [hcode]; exact lookup_st_be32_g08)
          rw [hl] at hc1; dsimp only at hc1
          split at hc1
          · injection hc1 with hr hsc1; subst hr hsc1; exact Or.inl ⟨rfl, by simp⟩
          · let entry := callEntryStateHOLFinite s
              ((HolFiniteMapExact.empty.update (ofString "p", .val (.word p))).update (ofString "v", .val (.word vW)))
            have hp_in : entry.locals.lookup (ofString "p") = some (.val (.word p)) := by
              simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "v" ≠ ofString "p" by decide]
            obtain ⟨_, hlt_or_eq, hlt_b⟩ := st_be32_body_eff_g08 entry p hma hp_in
            rcases hb : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_st_be32) with ⟨rb, sb⟩
            have hb_entry : evaluateHOLFiniteState
                (callEntryStateHOLFinite s
                  ((HolFiniteMapExact.empty.update (ofString "p", .val (.word p))).update (ofString "v", .val (.word vW))))
                (sourceFnBody Guest.Software.guestFn_st_be32) = (rb, sb) := hb
            rw [hb_entry] at hc1; rw [hb] at hlt_or_eq; dsimp only at hlt_or_eq
            rcases hlt_or_eq with hmem_eq | hp_lt
            · cases rb with
              | none => injection hc1 with hr hsc1; subst hr hsc1; exact Or.inl ⟨hmem_eq, by simp⟩
              | some r =>
                cases r with
                | returned rv' => exact Or.inr (hlt_b rv' (by rw [hb]))
                | timeOut | error | exception _ _ | finalFfi _ | «break» | «continue» =>
                  injection hc1 with hr hsc1; subst hr hsc1; exact Or.inl ⟨hmem_eq, by simp⟩
            · exact Or.inr hp_lt
        · have hln := lookup_two_words_reject_nonword_g08 s.code.lookup (ofString "st_be32") (ofString "p") (ofString "v")
            _ p vv (by rw [hcode]; exact lookup_st_be32_g08) (fun w hw => hvw ⟨w, hw⟩)
          rw [hln] at hc1; injection hc1 with hr hsc1; subst hr hsc1; exact Or.inl ⟨rfl, by simp⟩
    refine ⟨?_, ?_, ?_⟩
    · refine seq_call_st_be32_eff_g08 (base := p) (off := 0) (len := 8) hcode hma (by omega) (by omega)
        (fun h => by omega) (eval_var_local_zero_g08 s "p" p hp) fun s1 hp_lt hc1 hm1 hl1 => ?_
      have hp1 : s1.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hl1]; exact hp
      refine seq_call_st_be32_eff_g08 (s := s1) (base := p) (off := 4) (len := 8) hc1 hm1 (by omega) (by omega)
        (fun _ => hp_lt) (eval_add_local_const_g08 s1 "p" p 4 hp1) fun s2 _ _ _ _ => return_eff_g08 s2 _ _
    · rcases hfirst_call with ⟨hm_eq, _⟩ | hp_lt <;> [exact Or.inl hm_eq; exact Or.inr hp_lt]
    · intro rv hret; rcases hfirst_call with ⟨_, hne⟩ | hp_lt <;> [exact absurd hret (hne rv); exact hp_lt]

private theorem seq_call_st_be64_eff_g08 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {pExp vExp : ExpHOL 64} {base : BitVec 64} {off : Nat} {cont : ProgHOL 64}
    (hcode : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain)
    (hoff : off + 8 ≤ 32) (hprev : off > 0 → base.toNat < heapEnd)
    (hp_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) pExp =
      some (.val (.word (base + BitVec.ofNat 64 off))))
    (hcont : ∀ s1 : PanSemStateFiniteExact 64 F,
      base.toNat < heapEnd → s1.code = originalRuntimeCode → s1.memaddrs = ordinaryDomain → s1.locals = s.locals →
      ByteRegionEffect s1 (evaluateHOLFiniteState s1 cont).2 [(base.toNat, 32)]) :
    ByteRegionEffect s
      (evaluateHOLFiniteState s (.seq (.call (some (none, none)) (ofString "st_be64") [pExp, vExp]) cont)).2
      [(base.toNat, 32)] := by
  let pArg := base + BitVec.ofNat 64 off
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hc : evaluateHOLFiniteState s (.call (some (none, none)) (ofString "st_be64") [pExp, vExp]) with ⟨rc, sc⟩
  rw [evaluateHOLFiniteState_call] at hc
  rcases hv_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) vExp with _ | vv
  · have hnone : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [pExp, vExp] = none := by
      simp [evalListHOLFinite, evalListHOLExact, hp_ev, hv_ev]
    rw [hnone] at hc; injection hc with hr hsc; subst hr hsc; exact ByteRegionEffect.refl s _
  · have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [pExp, vExp] =
        some [.val (.word pArg), vv] := by
      simp [evalListHOLFinite, evalListHOLExact, hp_ev, hv_ev, pArg]
    rw [hargs] at hc; dsimp only at hc
    by_cases hvw : ∃ vW : BitVec 64, vv = .val (.word vW)
    · obtain ⟨vW, rfl⟩ := hvw
      have hl := pan_two_word_lookup s.code.lookup (ofString "st_be64") (ofString "p") (ofString "v")
        (sourceFnBody Guest.Software.guestFn_st_be64) pArg vW (by decide) (by rw [hcode]; exact lookup_st_be64_g08)
      rw [hl] at hc; dsimp only at hc
      split at hc
      · injection hc with hr hsc; subst hr hsc; exact (ByteRegionEffect.refl s _).with_locals_clock _ _
      · let entry := callEntryStateHOLFinite s
          ((HolFiniteMapExact.empty.update (ofString "p", .val (.word pArg))).update (ofString "v", .val (.word vW)))
        have hp_in : entry.locals.lookup (ofString "p") = some (.val (.word pArg)) := by
          simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "v" ≠ ofString "p" by decide]
        obtain ⟨heff_b, hlt_or_eq, hlt_b⟩ := st_be64_body_eff_g08 entry pArg hcode hma hp_in
        rcases hb : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_st_be64) with ⟨rb, sb⟩
        have hb_entry : evaluateHOLFiniteState
            (callEntryStateHOLFinite s
              ((HolFiniteMapExact.empty.update (ofString "p", .val (.word pArg))).update (ofString "v", .val (.word vW))))
            (sourceFnBody Guest.Software.guestFn_st_be64) = (rb, sb) := hb
        rw [hb_entry] at hc; rw [hb] at heff_b hlt_or_eq; dsimp only at heff_b hlt_or_eq
        have heff_entry : ByteRegionEffect s entry [(base.toNat, 32)] :=
          (ByteRegionEffect.refl s _).with_locals_clock _ _
        have heff_sb : ByteRegionEffect s sb [(base.toNat, 32)] := by
          rcases hlt_or_eq with hmem_eq | hpArg_lt
          · exact bre_of_mem_globals_eq_g08 [(base.toNat, 32)]
              heff_b.globals hmem_eq heff_b.code heff_b.memaddrs heff_b.shMemaddrs heff_b.baseAddr heff_b.be
          · have hbase_lt : base.toNat < heapEnd := by
              by_cases hz_off : off = 0
              · subst hz_off; have h0 : pArg = base := by simp [pArg]
                rwa [h0] at hpArg_lt
              · exact hprev (by omega)
            have hpArg_nat : pArg.toNat = base.toNat + off := bv_add_off_nat_g08 base off hbase_lt (by omega)
            exact heff_entry.trans (heff_b.mono fun i hi => by
              simp only [List.mem_singleton] at hi; subst hi
              exact ⟨(base.toNat, 32), List.mem_singleton.2 rfl, by rw [hpArg_nat]; omega, by rw [hpArg_nat]; omega⟩)
        cases rb with
        | none => injection hc with hr hsc; subst hr hsc; exact heff_sb
        | some r =>
          cases r with
          | returned rv =>
            dsimp only at hc; split at hc
            · injection hc with hr hsc; subst hr hsc; dsimp only
              have hpArg_lt := hlt_b rv (by rw [hb])
              have hbase_lt : base.toNat < heapEnd := by
                by_cases hz_off : off = 0
                · subst hz_off; have h0 : pArg = base := by simp [pArg]
                  rwa [h0] at hpArg_lt
                · exact hprev (by omega)
              let s1 : PanSemStateFiniteExact 64 F := { sb with locals := s.locals }
              have heff_s1 : ByteRegionEffect s s1 [(base.toNat, 32)] := heff_sb.with_locals_clock _ _
              exact heff_s1.trans (hcont s1 hbase_lt (heff_s1.code.trans hcode) (heff_s1.memaddrs.trans hma) rfl)
            · injection hc with hr hsc; subst hr hsc; exact heff_sb
          | timeOut | error | exception _ _ | finalFfi _ =>
            injection hc with hr hsc; subst hr hsc; exact heff_sb.with_locals_clock _ _
          | «break» | «continue» =>
            injection hc with hr hsc; subst hr hsc; exact heff_sb
    · have hln := lookup_two_words_reject_nonword_g08 s.code.lookup (ofString "st_be64") (ofString "p") (ofString "v")
        _ pArg vv (by rw [hcode]; exact lookup_st_be64_g08) (fun w hw => hvw ⟨w, hw⟩)
      rw [hln] at hc; injection hc with hr hsc; subst hr hsc; exact ByteRegionEffect.refl s _

private theorem u256_to_be32_body_bre_g08 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_to_be32)).1) :
    ByteRegionEffect s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_to_be32)).2
      [(locN s "out", 32)] := by
  have hb : sourceFnBody Guest.Software.guestFn_u256_to_be32 =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_u256_to_be32).body := rfl
  rw [hb] at hres ⊢
  dsimp only [extractFn, Guest.Software.guestFn_u256_to_be32,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    List.map, Option.map] at hres ⊢
  rcases hout_lu : s.locals.lookup (ofString "out") with _ | vout
  · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres
    simp [evalHOLExact, evalListHOLExact, hout_lu] at hres
    exact absurd hres not_resumes_error_g08
  · rcases vout with ⟨⟨out⟩⟩ | _ | _
    · have hloc_out : locN s "out" = out.toNat := by simp [locN, hout_lu]
      rw [hloc_out]
      have hcond := eval_align8_eq0_g08 s "out" out hout_lu
      by_cases hal : (out &&& 7#64) = 0#64
      · have hdc_ne_none : ∀ (st : PanSemStateFiniteExact 64 F) (nm : MlS) (sh : ShapeHOL)
            (fn : MlS) (args : List (ExpHOL 64)) (c : ProgHOL 64),
            (∀ (m : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState m c).1 ≠ none) →
            (evaluateHOLFiniteState st (.decCall nm sh fn args c)).1 ≠ none := by
          intro st nm sh fn args c hc_nn
          rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
          rcases evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a)) args with _ | _
          · simp
          · dsimp only
            rcases lookupCodeHOLFinite st.code.lookup fn _ with _ | ⟨b', cal', rs'⟩
            · simp
            · dsimp only; split
              · simp
              · rcases evaluateHOLFiniteState (callEntryStateHOLFinite st cal') b' with ⟨rb, sb⟩
                cases rb with
                | none => simp
                | some r =>
                  cases r with
                  | returned _ => dsimp only; split <;> [ exact hc_nn _; simp ]
                  | _ => simp
        have hseq_ne_none : ∀ {p1 p2 : ProgHOL 64},
            (∀ (m : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState m p2).1 ≠ none) →
            ∀ (m : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState m (.seq p1 p2)).1 ≠ none := by
          intro p1 p2 hp2 m
          rw [evaluateHOLFiniteState_seq_line780]
          rcases evaluateHOLFiniteState m p1 with ⟨r1, m1⟩
          cases r1 with
          | none => exact hp2 m1
          | some _ => simp
        have hret_ne_none : ∀ (m : PanSemStateFiniteExact 64 F),
            (evaluateHOLFiniteState m (.return (.const 0#64))).1 ≠ none := by
          intro m; rw [(return_const0_step_g08 m).1]; simp
        let yesProg256 : ProgHOL 64 :=
          .decCall (ofString "w") .one (ofString "bswap64") [.rfield 3 (.var .local (ofString "a"))]
            (.seq (.store (.var .local (ofString "out")) (.var .local (ofString "w")))
              (.seq (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [.rfield 2 (.var .local (ofString "a"))])
                (.seq (.store (.op .add [.var .local (ofString "out"), .const 8#64]) (.var .local (ofString "w")))
                  (.seq (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [.rfield 1 (.var .local (ofString "a"))])
                    (.seq (.store (.op .add [.var .local (ofString "out"), .const 16#64]) (.var .local (ofString "w")))
                      (.seq (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [.rfield 0 (.var .local (ofString "a"))])
                        (.seq (.store (.op .add [.var .local (ofString "out"), .const 24#64]) (.var .local (ofString "w")))
                          (.return (.const 0#64)))))))))
        have hyes256_nn : (evaluateHOLFiniteState s yesProg256).1 ≠ none :=
          hdc_ne_none s _ _ _ _ _
            (hseq_ne_none (hseq_ne_none (hseq_ne_none (hseq_ne_none
              (hseq_ne_none (hseq_ne_none (hseq_ne_none hret_ne_none)))))))
        have hgoal_yes256 : evaluateHOLFiniteState s
            (.seq (.ite (.cmp .equal (.op .and [.var .local (ofString "out"), .const 7#64]) (.const 0#64)) yesProg256 .skip)
              (.seq (.call (some (none, none)) (ofString "st_be64") [.var .local (ofString "out"), .rfield 3 (.var .local (ofString "a"))])
                (.seq (.call (some (none, none)) (ofString "st_be64") [.op .add [.var .local (ofString "out"), .const 8#64], .rfield 2 (.var .local (ofString "a"))])
                  (.seq (.call (some (none, none)) (ofString "st_be64") [.op .add [.var .local (ofString "out"), .const 16#64], .rfield 1 (.var .local (ofString "a"))])
                    (.seq (.call (some (none, none)) (ofString "st_be64") [.op .add [.var .local (ofString "out"), .const 24#64], .rfield 0 (.var .local (ofString "a"))])
                      (.return (.const 0#64))))))) = evaluateHOLFiniteState s yesProg256 := by
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hcond]
          simp only [hal, ↓reduceIte]
          have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
          rw [if_neg h10]
          rcases hy : evaluateHOLFiniteState s yesProg256 with ⟨ry, sy⟩
          rw [hy] at hyes256_nn
          cases ry with
          | none => exact absurd rfl hyes256_nn
          | some _ => rfl
        rw [hgoal_yes256]
        exact decCall_bswap64_eff_g08 (s := s) (Rl := [(out.toNat, 32)]) hcode
          fun mid0 hc_m0 hm_m0 hout_m0 _ _ ⟨wv0, hw_m0⟩ => by
            have ho0 : mid0.locals.lookup (ofString "out") = some (.val (.word out)) := by rw [hout_m0]; exact hout_lu
            refine seq_store_word_eff_g08 (s := mid0) (base := out) (w := wv0) (off := 0) (len := 32)
              (hm_m0.trans hma) (by omega) (by omega) (fun h => by omega)
              (eval_var_local_zero_g08 mid0 "out" out ho0)
              (eval_var_local_g08 mid0 "w" wv0 hw_m0) fun s1 hout_lt hc_s1 hm_s1 hl_s1 => ?_
            refine seq_call_bswap64_eff_g08 (s := s1) (Rl := [(out.toNat, 32)])
              (hc_s1.trans hc_m0) fun mid1 hc_m1 hm_m1 hout_m1 _ ⟨wv1, hw_m1⟩ => ?_
            have ho1 : mid1.locals.lookup (ofString "out") = some (.val (.word out)) := by rw [hout_m1, hl_s1]; exact ho0
            refine seq_store_word_eff_g08 (s := mid1) (base := out) (w := wv1) (off := 8) (len := 32)
              (hm_m1.trans (hm_s1.trans (hm_m0.trans hma))) (by omega) (by omega) (fun _ => hout_lt)
              (eval_add_local_const_g08 mid1 "out" out 8 ho1)
              (eval_var_local_g08 mid1 "w" wv1 hw_m1) fun s2 _ hc_s2 hm_s2 hl_s2 => ?_
            refine seq_call_bswap64_eff_g08 (s := s2) (Rl := [(out.toNat, 32)])
              (hc_s2.trans hc_m1) fun mid2 hc_m2 hm_m2 hout_m2 _ ⟨wv2, hw_m2⟩ => ?_
            have ho2 : mid2.locals.lookup (ofString "out") = some (.val (.word out)) := by rw [hout_m2, hl_s2]; exact ho1
            refine seq_store_word_eff_g08 (s := mid2) (base := out) (w := wv2) (off := 16) (len := 32)
              (hm_m2.trans (hm_s2.trans (hm_m1.trans (hm_s1.trans (hm_m0.trans hma))))) (by omega) (by omega)
              (fun _ => hout_lt)
              (eval_add_local_const_g08 mid2 "out" out 16 ho2)
              (eval_var_local_g08 mid2 "w" wv2 hw_m2) fun s3 _ hc_s3 hm_s3 hl_s3 => ?_
            refine seq_call_bswap64_eff_g08 (s := s3) (Rl := [(out.toNat, 32)])
              (hc_s3.trans hc_m2) fun mid3 _ hm_m3 hout_m3 _ ⟨wv3, hw_m3⟩ => ?_
            have ho3 : mid3.locals.lookup (ofString "out") = some (.val (.word out)) := by rw [hout_m3, hl_s3]; exact ho2
            refine seq_store_word_eff_g08 (s := mid3) (base := out) (w := wv3) (off := 24) (len := 32)
              (hm_m3.trans (hm_s3.trans (hm_m2.trans (hm_s2.trans (hm_m1.trans (hm_s1.trans (hm_m0.trans hma)))))))
              (by omega) (by omega) (fun _ => hout_lt)
              (eval_add_local_const_g08 mid3 "out" out 24 ho3)
              (eval_var_local_g08 mid3 "w" wv3 hw_m3) fun s4 _ _ _ _ => return_eff_g08 s4 _ _
      · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hcond]
        simp only [hal, ↓reduceIte, evaluateHOLFiniteState_skip]
        refine seq_call_st_be64_eff_g08 (base := out) (off := 0) hcode hma (by omega) (fun h => by omega)
          (eval_var_local_zero_g08 s "out" out hout_lu) fun s1 hout_lt hc1 hm1 hl1 => ?_
        have hout1 : s1.locals.lookup (ofString "out") = some (.val (.word out)) := by rw [hl1]; exact hout_lu
        refine seq_call_st_be64_eff_g08 (s := s1) (base := out) (off := 8) hc1 hm1 (by omega) (fun _ => hout_lt)
          (eval_add_local_const_g08 s1 "out" out 8 hout1) fun s2 _ hc2 hm2 hl2 => ?_
        have hout2 : s2.locals.lookup (ofString "out") = some (.val (.word out)) := by rw [hl2]; exact hout1
        refine seq_call_st_be64_eff_g08 (s := s2) (base := out) (off := 16) hc2 hm2 (by omega) (fun _ => hout_lt)
          (eval_add_local_const_g08 s2 "out" out 16 hout2) fun s3 _ hc3 hm3 hl3 => ?_
        have hout3 : s3.locals.lookup (ofString "out") = some (.val (.word out)) := by rw [hl3]; exact hout2
        refine seq_call_st_be64_eff_g08 (s := s3) (base := out) (off := 24) hc3 hm3 (by omega) (fun _ => hout_lt)
          (eval_add_local_const_g08 s3 "out" out 24 hout3) fun s4 _ _ _ _ => return_eff_g08 s4 _ _
    · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres
      simp [evalHOLExact, evalListHOLExact, hout_lu, valueIsWord] at hres
      exact absurd hres not_resumes_error_g08
    · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres
      simp [evalHOLExact, evalListHOLExact, hout_lu, valueIsWord] at hres
      exact absurd hres not_resumes_error_g08

private theorem u256_to_be32_args_lookup_g08
    {vals : List (ValueHOL 64)} {body' : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret' : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "u256_to_be32") vals =
      some (body', callee, ret')) :
    ∃ (va : ValueHOL 64) (outw : BitVec 64),
      vals = [va, .val (.word outw)] ∧
      callee.lookup (ofString "out") = some (.val (.word outw)) := by
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
    originalRuntimeCode.lookup (ofString "u256_to_be32") vals body' callee ret' hl
  simp only [Flapjack.lookupCodeHOLExact, lookup_u256_to_be32_g08] at hx
  rcases vals with _ | ⟨va, _ | ⟨vo, _ | _⟩⟩
  · simp at hx
  · simp at hx
  · split at hx
    · rename_i hcond
      have heq := Option.some.inj hx
      rcases Prod.mk.inj heq with ⟨_, hrest⟩
      rcases Prod.mk.inj hrest with ⟨hloc, _⟩
      have hs := hcond.2.2
      simp only [List.map, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, List.zip_cons_cons, List.zip_nil_left] at hs
      rcases hs with ⟨_, hsho⟩
      rcases vo with ⟨⟨outw⟩⟩ | _ | _
      · refine ⟨va, outw, rfl, ?_⟩
        have hfn := congrFun hloc.symm (ofString "out")
        simpa [FUPDATE_LIST, FUPDATE] using hfn
      · simp [shapeOfHOLExact, shapeEqHOL] at hsho
      · simp [shapeOfHOLExact, shapeEqHOL] at hsho
    · cases hx
  · simp at hx

private theorem eps_u256_to_be32_head_mem_g08 :
    EvmPreservingSpec
      (fun s =>
        memW s (globN s "ev" + 24) ≤ locN s "out" ∧
        locN s "out" + 32 ≤ memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40))
      (fun _ _ _ => True)
      (ofString "u256_to_be32") := by
  refine ⟨_, _, _, lookup_u256_to_be32_g08, ?_⟩
  intro F s hcode hInv ⟨hlo, hhi⟩ _ _
  have hncr := evaluate_noCatchableRaise_g08 u256NcrCallees_g08 u256NcrCallees_good_g08
    (sourceFnBody Guest.Software.guestFn_u256_to_be32) (by decide) s hcode
  refine ⟨fun v hv => ?_, fun ⟨v, hv⟩ => False.elim (hncr _ v (by decide) hv)⟩
  have heff0 := u256_to_be32_body_bre_g08 s hcode hInv.1.1.memaddrs (Or.inl ⟨v, hv⟩)
  have heff_hm : ByteRegionEffect s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_to_be32)).2
      [(memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))] :=
    heff0.mono (fun i hi => by
      simp only [List.mem_singleton] at hi
      subst i
      exact ⟨(memW s (globN s "ev" + 24), memW s (globN s "ev" + 40)),
        List.mem_singleton.mpr rfl, hlo, hhi⟩)
  obtain ⟨hInv_post, hch, hR⟩ := evmInv_of_head_mem_bytes_g08 hInv heff_hm
  exact ⟨hInv_post, hch, le_of_eq hR, trivial⟩

theorem op_mstore_aligned_spec :
    FunSpec (fun s => EvmRun s ∧ HeadMemAligned s) OpDispatchPost (ofString "op_mstore") := by
  refine ⟨_, _, _, lookup_op_mstore, ?_⟩
  intro F s0 hcode ⟨hRun, hHM0⟩ _ hnt
  suffices hrun : HandlerRun s0 HeadMemAligned false (sourceFnBody Guest.Software.guestFn_op_mstore) from
    hrun s0 hcode hRun.1 rfl (le_refl _) hHM0 hnt
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_op_mstore,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRun.decCall
    (Q := fun t =>
      HeadMemAligned t ∧
      ∃ stVal : ValueHOL 64,
        t.locals.lookup (ofString "start") = some stVal ∧
        shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true)
    eps_stack_pop_preserves_headMem
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ callee _ v cpost _ hHM _ _ _ _ ⟨_, hsh_v, hHM_step⟩ => by
      have hHM_ce : HeadMemAligned (callEntryStateHOLFinite t callee) :=
        headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      have hHM_cp : HeadMemAligned cpost := hHM_step hHM_ce
      have hHM_res : HeadMemAligned (setVarHOLFinite (ofString "start") v { cpost with locals := t.locals }) :=
        headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp
      exact ⟨hHM_res, v, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], hsh_v⟩)
    ?_
  refine HandlerRun.decCall
    (Q := fun t =>
      HeadMemAligned t ∧
      ∃ stVal : ValueHOL 64,
        t.locals.lookup (ofString "start") = some stVal ∧
        shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true)
    eps_stack_pop_preserves_headMem
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ callee _ v cpost _ ⟨hHM, stVal, hst, hsh_st⟩ _ _ _ _ ⟨_, _, hHM_step⟩ => by
      have hHM_ce : HeadMemAligned (callEntryStateHOLFinite t callee) :=
        headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      have hHM_cp : HeadMemAligned cpost := hHM_step hHM_ce
      have hHM_res : HeadMemAligned (setVarHOLFinite (ofString "value") v { cpost with locals := t.locals }) :=
        headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp
      have hne_vs : ofString "value" ≠ ofString "start" := by decide
      exact ⟨hHM_res, stVal,
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne_vs, Ne.symm hne_vs, hst],
        hsh_st⟩)
    ?_
  refine seq_call_strict_q_g08
    (Pc := fun t ce =>
      HeadMemAligned ce ∧
      (∃ bw : BitVec 64, ce.locals.lookup (ofString "base") = some (.val (.word bw)) ∧ 0 < bw.toNat) ∧
      ∃ stVal : ValueHOL 64,
        t.locals.lookup (ofString "start") = some stVal ∧
        ce.locals.lookup (ofString "start") = some stVal ∧
        shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true ∧
        ce.locals.lookup (ofString "size") =
          some (.rStruct [.val (.word 32#64), .val (.word 0#64), .val (.word 0#64), .val (.word 0#64)]))
    (R := fun t cpost =>
      ∀ stVal : ValueHOL 64,
        t.locals.lookup (ofString "start") = some stVal →
        (satValue_g08 stVal).toNat + 32 ≤ memW cpost (globN cpost "ev" + 32))
    (Q := fun t =>
      ∃ stVal : ValueHOL 64,
        t.locals.lookup (ofString "start") = some stVal ∧
        shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true ∧
        (satValue_g08 stVal).toNat + 32 ≤ memW t (globN t "ev" + 32))
    lookup_charge_with_memory
    (fun t values callee _ _ ⟨hHM, stVal, hst, hsh_st⟩ hargs hl_orig => by
      obtain ⟨basew, v2, v3, rfl, _, _, hcal_b, hcal_st, hcal_sz⟩ := charge_with_memory_args_lookup_g08 hl_orig
      have hHM_ce : HeadMemAligned (callEntryStateHOLFinite t callee) :=
        headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      have hargs_ok : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.const 3#64, .var .local (ofString "start"),
           .rstruct [.const 32#64, .const 0#64, .const 0#64, .const 0#64]] =
          some [.val (.word 3#64), stVal,
                .rStruct [.val (.word 32#64), .val (.word 0#64), .val (.word 0#64), .val (.word 0#64)]] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hst]
      rw [hargs_ok] at hargs
      injection hargs with hvs
      rcases List.cons.inj hvs with ⟨hb_eq, hvs1⟩
      rcases List.cons.inj hvs1 with ⟨rfl, hvs2⟩
      rcases List.cons.inj hvs2 with ⟨rfl, _⟩
      injection hb_eq with hb1; injection hb1 with hb2; subst hb2
      exact ⟨hHM_ce, ⟨3#64, hcal_b, by decide⟩, stVal, hst, hcal_st, hsh_st, hcal_sz⟩)
    (fun t ⟨_, stVal, hst, hsh_st⟩ => by
      intro ce hc hInv_ce hlen_ce hR_ce ⟨hHM_ce, hbw_ce, stVal', hst', hcal_st, hsh_st', hcal_sz⟩ hnt_ce
      have hst_eq : stVal' = stVal := by rw [hst] at hst'; exact Option.some.inj hst'.symm
      subst stVal'
      have hrun_cov := charge_with_memory_body_run_aligned_cov_g08 s0 stVal 32#64 hsh_st (by decide)
        ce hc hInv_ce hlen_ce hR_ce ⟨hHM_ce, hbw_ce, hcal_st, hcal_sz⟩ hnt_ce
      dsimp only at hrun_cov ⊢
      refine ⟨fun hret => ?_, hrun_cov.2.1, hrun_cov.2.2⟩
      obtain ⟨h1, h2, h3, hcov⟩ := hrun_cov.1 hret
      refine ⟨h1, h2, h3, fun stVal0 hst0 => ?_⟩
      have hst0_eq : stVal0 = stVal := by rw [hst] at hst0; exact Option.some.inj hst0.symm
      subst stVal0
      simpa using hcov)
    (fun t cpost _ ⟨_, stVal, hst, hsh_st⟩ _ hRt => by
      exact ⟨stVal, hst, hsh_st, hRt stVal hst⟩)
    ?_
  refine HandlerRun.decCall
    (Q := fun t =>
      ∀ addr : BitVec 64,
        @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.op .add
            [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]),
             .var .local (ofString "s")]) =
          some (.val (.word addr)) →
        memW t (globN t "ev" + 24) ≤ addr.toNat ∧
        addr.toNat + 32 ≤ memW t (globN t "ev" + 24) + memW t (globN t "ev" + 40))
    eps_sat_word_exact_g08
    (fun t values b_sw callee rs_sw hc _ ⟨stVal, hst, hsh_st, _⟩ hargs hl => by
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "sat_word") values =
          some (b_sw, callee, rs_sw) := by rwa [← hc]
      obtain ⟨_, _, v0, rfl, hcal_v⟩ := single_comb_arg_lookup_g08 lookup_sat_word_g08 hl_orig
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact, evalHOLExact, hst, Option.some.injEq, List.cons.injEq] at hargs
      rcases hargs with ⟨rfl, _⟩
      exact ⟨stVal, hcal_v, hsh_st⟩)
    (fun t values _ callee _ v cpost _ ⟨stVal, hst, _, hcov⟩ hargs hl_orig hInv_cp _ ⟨hlf, hv_eq⟩ => by
      obtain ⟨_, _, v0, rfl, hcal_v⟩ := single_comb_arg_lookup_g08 lookup_sat_word_g08 hl_orig
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact, evalHOLExact, hst, Option.some.injEq, List.cons.injEq] at hargs
      rcases hargs with ⟨rfl, _⟩
      have hv_sat := hv_eq stVal hcal_v
      subst v
      let res := setVarHOLFinite (ofString "s") (.val (.word (satValue_g08 stVal))) { cpost with locals := t.locals }
      have hInv_res : EvmInv res := localsFree_evmInv cpost res.locals cpost.clock hInv_cp
      have hmem32_eq : memW res (globN res "ev" + 32) = memW t (globN t "ev" + 32) := by
        have hg : globN res "ev" = globN t "ev" := globN_eq_of_lookup_eq (by change cpost.globals.lookup _ = t.globals.lookup _; rw [hlf]; rfl)
        have hm : res.memory = t.memory := by change cpost.memory = t.memory; rw [hlf]; rfl
        rw [hg]; unfold memW; rw [hm]
      have hres_s : res.locals.lookup (ofString "s") = some (.val (.word (satValue_g08 stVal))) := by
        simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      obtain ⟨basew, hbasew_nat, hev_dst⟩ := eval_head_mem_plus_s_g08 res hInv_res (satValue_g08 stVal) hres_s
      have hbounds := head_mem_store_address_g08 res hInv_res basew (satValue_g08 stVal) 32 hbasew_nat (by omega)
        (by rw [hmem32_eq]; exact hcov)
      intro addr haddr
      rw [hev_dst] at haddr
      injection haddr with h1; injection h1 with h2; injection h2 with h3; subst h3
      exact ⟨hbounds.2.1, hbounds.2.2⟩)
    ?_
  refine HandlerRun.seq_call
    (Q := fun _ => True)
    eps_u256_to_be32_head_mem_g08
    (fun t values b_u callee rs_u hc _ hP hargs hl => by
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "u256_to_be32") values =
          some (b_u, callee, rs_u) := by rwa [← hc]
      obtain ⟨va, outw, rfl, hcal_out⟩ := u256_to_be32_args_lookup_g08 hl_orig
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact] at hargs
      rcases hv1 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.var .local (ofString "value")) with _ | u1
      · simp [hv1] at hargs
      · rcases hv2 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
            (.op .add
              [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]),
               .var .local (ofString "s")]) with _ | u2
        · simp [hv1, hv2] at hargs
        · simp only [hv1, hv2, Option.some.injEq, List.cons.injEq] at hargs
          rcases hargs with ⟨rfl, rfl, _⟩
          have hb := hP outw hv2
          have hloc_out : locN (callEntryStateHOLFinite t callee) "out" = outw.toNat := by
            simp [locN, callEntryStateHOLFinite, hcal_out]
          rw [hloc_out]
          exact hb)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
    (HandlerRun.seq_call_simple eps_pc_add (HandlerRun.ret _))

private theorem extend_memory_cost1_copy_coverage_g08 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (stVal : ValueHOL 64) (k0 k1 k2 k3 : BitVec 64)
    (hc : s.code = originalRuntimeCode)
    (hst : s.locals.lookup (ofString "start") = some stVal)
    (hst_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true)
    (hsz : s.locals.lookup (ofString "size") =
      some (.rStruct [.val (.word k0), .val (.word k1), .val (.word k2), .val (.word k3)]))
    (hkw : satValue_g08 (.rStruct [.val (.word k0), .val (.word k1), .val (.word k2), .val (.word k3)]) ≠ 0#64)
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_extend_memory_cost1)).1 =
      some (.returned v)) :
    ∀ cw ebw : BitVec 64,
      v = .rStruct [.val (.word cw), .val (.word ebw)] →
      cw.toNat < 2 ^ 64 - 1 →
      memW s (globN s "ev" + 32) % 32 = 0 →
      (satValue_g08 stVal).toNat + (satValue_g08 (.rStruct [.val (.word k0), .val (.word k1), .val (.word k2), .val (.word k3)])).toNat ≤ memW s (globN s "ev" + 32) + ebw.toNat := by
  let kw := satValue_g08 (.rStruct [.val (.word k0), .val (.word k1), .val (.word k2), .val (.word k3)])
  intro cw ebw hv hcw_lt hcur_mod
  subst hv
  obtain ⟨a, b, c, d, rfl⟩ := u256_value_of_shape_g08 hst_sh
  have hbody : sourceFnBody Guest.Software.guestFn_extend_memory_cost1 =
      .decCall (ofString "z") .one (ofString "u256_is_zero") [.var .local (ofString "size")]
        (.seq
          (.ite (.cmp .notEqual (.var .local (ofString "z")) (.const 0#64))
            (.return (.rstruct [.const 0#64, .const 0#64]))
            .skip)
          (.decCall (ofString "s") .one (ofString "sat_word") [.var .local (ofString "start")]
            (.decCall (ofString "n") .one (ofString "sat_word") [.var .local (ofString "size")]
              (.decCall (ofString "endp") .one (ofString "add_sat")
                [.var .local (ofString "s"), .var .local (ofString "n")]
                (.seq
                  (.ite (.cmp .equal (.var .local (ofString "endp")) (.const 18446744073709551615#64))
                    (.return (.rstruct [.const 18446744073709551615#64, .const 0#64]))
                    .skip)
                  (.dec (ofString "cur") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 32#64]))
                    (.decCall (ofString "before") .one (ofString "ceil32") [.var .local (ofString "cur")]
                      (.decCall (ofString "after") .one (ofString "ceil32") [.var .local (ofString "endp")]
                        (.seq
                          (.ite (.cmp .notLower (.var .local (ofString "before")) (.var .local (ofString "after")))
                            (.return (.rstruct [.const 0#64, .const 0#64]))
                            .skip)
                          (.decCall (ofString "ca") .one (ofString "memory_gas_cost") [.var .local (ofString "after")]
                            (.decCall (ofString "cb") .one (ofString "memory_gas_cost") [.var .local (ofString "before")]
                              (.seq
                                (.ite (.cmp .equal (.var .local (ofString "ca")) (.const 18446744073709551615#64))
                                  (.return (.rstruct [.const 18446744073709551615#64, .const 0#64]))
                                  .skip)
                                (.return (.rstruct
                                  [.op .sub [.var .local (ofString "ca"), .var .local (ofString "cb")],
                                   .op .sub [.var .local (ofString "after"), .var .local (ofString "before")]])))))))))))))) := rfl
  have hret_pair : ∀ (st : PanSemStateFiniteExact 64 F) (w1 w2 : BitVec 64),
      evaluateHOLFiniteState st (.return (.rstruct [.const w1, .const w2])) =
        (some (.returned (.rStruct [.val (.word w1), .val (.word w2)])), st.emptyLocalsHOLFinite) := by
    intro st w1 w2
    rw [evaluateHOLFiniteState_return]
    have hev : @evalHOLExact 64 F _ st.toExact (fun x => Classical.propDecidable (st.memaddrs x))
        (.rstruct [.const w1, .const w2]) =
        some (.rStruct [.val (.word w1), .val (.word w2)]) := by
      simp [evalHOLExact, evalListHOLExact]
    rw [hev]
    dsimp only
    have hsz2 : sizeOfShapeWithContextHOL st.structs
        (shapeOfHOLExact (.rStruct [.val (.word w1), .val (.word w2)] : ValueHOL 64)) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
    rw [if_pos hsz2]
  have h10 : ¬ ((1#64 : BitVec 64) = 0) := by decide
  have h00 : (0#64 : BitVec 64) = 0 := rfl
  rw [hbody] at hret
  obtain ⟨zw, s1, hs1_c, hs1_lf, hs1_loc, ⟨vals1, body1, cal1, rs1, ha1, hl1, hrun1⟩, hr1⟩ :=
    ro_word_call_return_g08 (s := s) (st := s) (by decide) hc (LocFrame.refl s) hret
  have hvals1 : vals1 = [.rStruct [.val (.word k0), .val (.word k1), .val (.word k2), .val (.word k3)]] := by
    simpa [evalListHOLFinite, evalListHOLExact, evalHOLExact, hsz] using ha1.symm
  subst vals1
  obtain ⟨rfl, _, uzv, huzv_eq, hcal1⟩ := single_comb_arg_lookup_g08 lookup_u256_is_zero_g08 hl1
  injection huzv_eq with huzv_eq
  subst uzv
  have hor : k0 ||| k1 ||| k2 ||| k3 ≠ 0#64 := by
    intro hz
    have hh := hz
    simp only [BitVec.or_eq_zero_iff] at hh
    rcases hh with ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
    exact hkw rfl
  have hzret : evaluateHOLFiniteState (callEntryStateHOLFinite s cal1)
      (sourceFnBody Guest.Software.guestFn_u256_is_zero) =
      (some (.returned (.val (.word 0#64))), (callEntryStateHOLFinite s cal1).emptyLocalsHOLFinite) := by
    dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_u256_is_zero,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map, List.map]
    simp [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite,
      evaluateHOLFiniteState_return, evaluateHOLFiniteState_skip,
      evalHOLExact, evalListHOLExact, hcal1, wordOpHOL, wordOp, valueIsWord, valueWord,
      OrOp.or, Compiler.Encoders.Asm.wordCmpHOL, callEntryStateHOLFinite, BitVec.or_assoc,
      show k0 ||| (k1 ||| (k2 ||| k3)) ≠ 0#64 by simpa [BitVec.or_assoc] using hor,
      shapeOfHOLExact, sizeOfShapeWithContextHOL]
  rw [hzret] at hrun1
  have hzw0 : zw = 0#64 := by simpa using hrun1.symm
  subst zw
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr1
  have hs1_z : s1.locals.lookup (ofString "z") = some (.val (.word 0#64)) := by
    rw [hs1_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hcmp_z : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
      (.cmp .notEqual (.var .local (ofString "z")) (.const 0#64)) =
      some (.val (.word 0#64)) := by
    simp [evalHOLExact, hs1_z, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp_z] at hr1
  dsimp only at hr1
  rw [if_pos h00, evaluateHOLFiniteState_skip] at hr1
  dsimp only at hr1
  have hs1_st : s1.locals.lookup (ofString "start") =
      some (.rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) := by
    rw [hs1_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, hst,
      show ofString "z" ≠ ofString "start" by decide]
  obtain ⟨sw, s2, hs2_c, hs2_lf, hs2_loc, ⟨vals2, body2, cal2, rs2, ha2, hl2, hrun2⟩, hr2⟩ :=
    ro_word_call_return_g08 (s := s) (st := s1) (by decide) hs1_c hs1_lf hr1
  have hvals2 : vals2 = [.rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]] := by
    simpa [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs1_st] using ha2.symm
  subst vals2
  obtain ⟨rfl, _, sv2, hsv2_eq, hcal2⟩ := single_comb_arg_lookup_g08 lookup_sat_word_g08 hl2
  injection hsv2_eq with hsv2_eq
  subst sv2
  rw [sat_word_body_exact_g08 _ a b c d hcal2] at hrun2
  have hsw_eq : sw = satValue_g08 (.rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) := by
    simpa [satValue_g08] using hrun2.symm
  have hs2_sz : s2.locals.lookup (ofString "size") =
      some (.rStruct [.val (.word k0), .val (.word k1), .val (.word k2), .val (.word k3)]) := by
    rw [hs2_loc, hs1_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, hsz,
      show ofString "s" ≠ ofString "size" by decide,
      show ofString "z" ≠ ofString "size" by decide]
  obtain ⟨nw, s3, hs3_c, hs3_lf, hs3_loc, ⟨vals3, body3, cal3, rs3, ha3, hl3, hrun3⟩, hr3⟩ :=
    ro_word_call_return_g08 (s := s) (st := s2) (by decide) hs2_c hs2_lf hr2
  have hvals3 : vals3 = [.rStruct [.val (.word k0), .val (.word k1), .val (.word k2), .val (.word k3)]] := by
    simpa [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs2_sz] using ha3.symm
  subst vals3
  obtain ⟨rfl, _, sv3, hsv3_eq, hcal3⟩ := single_comb_arg_lookup_g08 lookup_sat_word_g08 hl3
  injection hsv3_eq with hsv3_eq
  subst sv3
  rw [sat_word_body_exact_g08 _ k0 k1 k2 k3 hcal3] at hrun3
  have hnw_eq : nw = kw := by simpa [kw, satValue_g08] using hrun3.symm
  subst nw
  have hs3_s : s3.locals.lookup (ofString "s") = some (.val (.word sw)) := by
    rw [hs3_loc, hs2_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "n" ≠ ofString "s" by decide]
  have hs3_n : s3.locals.lookup (ofString "n") = some (.val (.word kw)) := by
    rw [hs3_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE]
  obtain ⟨endpw, s4, hs4_c, hs4_lf, hs4_loc, ⟨vals4, body4, cal4, rs4, ha4, hl4, hrun4⟩, hr4⟩ :=
    ro_word_call_return_g08 (s := s) (st := s3) (by decide) hs3_c hs3_lf hr3
  have hvals4 : vals4 = [.val (.word sw), .val (.word kw)] := by
    simpa [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs3_s, hs3_n] using ha4.symm
  subst vals4
  obtain ⟨rfl, _, aw4, bw4, hvls4, hca4, hcb4⟩ := two_word_arg_lookup (by decide) lookup_add_sat hl4
  have hw4 : sw = aw4 ∧ kw = bw4 := by simpa using hvls4
  rcases hw4 with ⟨rfl, rfl⟩
  obtain ⟨endpw', hendpw_inj, hendp_ex⟩ := add_sat_body_exact_g08 (callEntryStateHOLFinite s3 cal4)
    hca4 hcb4 (.val (.word endpw)) hrun4
  have hendpw_eq : endpw = endpw' := by simpa using hendpw_inj
  subst endpw'
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr4
  have hs4_endp : s4.locals.lookup (ofString "endp") = some (.val (.word endpw)) := by
    rw [hs4_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hcmp_endp : @evalHOLExact 64 F _ s4.toExact (fun x => Classical.propDecidable (s4.memaddrs x))
      (.cmp .equal (.var .local (ofString "endp")) (.const 18446744073709551615#64)) =
      some (.val (.word (if endpw = 18446744073709551615#64 then 1#64 else 0#64))) := by
    simp [evalHOLExact, hs4_endp, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp_endp] at hr4
  dsimp only at hr4
  by_cases hendp_max : endpw = 18446744073709551615#64
  · rw [if_pos hendp_max, if_neg h10, hret_pair s4 18446744073709551615#64 0#64] at hr4
    have hcw_eq : cw = 18446744073709551615#64 := by
      have hp : cw = 18446744073709551615#64 ∧ ebw = 0#64 := by simpa using hr4.symm
      exact hp.1
    subst cw
    change 18446744073709551615 < 2 ^ 64 - 1 at hcw_lt
    omega
  · rw [if_neg hendp_max, if_pos h00, evaluateHOLFiniteState_skip] at hr4
    dsimp only at hr4
    have hendp_lt : endpw.toNat < 2 ^ 64 - 1 := by
      have hlt64 := endpw.isLt
      by_contra hge
      apply hendp_max
      apply BitVec.eq_of_toNat_eq
      change endpw.toNat = 18446744073709551615
      omega
    have hendp_sum := hendp_ex hendp_lt
    rw [evaluateHOLFiniteState_dec_total] at hr4
    dsimp only at hr4
    rcases hld_cur : @evalHOLExact 64 F _ s4.toExact (fun x => Classical.propDecidable (s4.memaddrs x))
        (.load .one (.op .add [.var .global (ofString "ev"), .const 32#64])) with _ | curv
    · rw [hld_cur] at hr4
      simp at hr4
    · obtain ⟨curw, rfl, hcurw_nat⟩ := evalAt_loadG_word s4 "ev" 32#64 curv hld_cur
      rw [hld_cur] at hr4
      dsimp only at hr4
      have hsh_cur : shapeEqHOL .one (shapeOfHOLExact (.val (.word curw))) = true := by
        simp [shapeEqHOL, shapeOfHOLExact]
      rw [if_pos hsh_cur] at hr4
      dsimp only at hr4
      have hs4_mem : s4.memory = s.memory := by unfold LocFrame at hs4_lf; conv_lhs => rw [hs4_lf]
      have hs4_glob : s4.globals = s.globals := by unfold LocFrame at hs4_lf; conv_lhs => rw [hs4_lf]
      have hcur_eq : curw.toNat = memW s (globN s "ev" + 32) := by
        have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
        rw [hcurw_nat, h32]
        simp [memW, globN, hs4_mem, hs4_glob]
      set s5 := setVarHOLFinite (ofString "cur") (.val (.word curw)) s4 with hs5_def
      have hs5_c : s5.code = originalRuntimeCode := hs4_c
      have hs5_lf : LocFrame s s5 := hs4_lf.with_locals_clock _ s4.clock
      have hs5_cur : s5.locals.lookup (ofString "cur") = some (.val (.word curw)) := by
        simp [hs5_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      obtain ⟨befw, s6, hs6_c, hs6_lf, hs6_loc, ⟨vals6, body6, cal6, rs6, ha6, hl6, hrun6⟩, hr6⟩ :=
        ro_word_call_return_g08 (s := s) (st := s5) (by decide) hs5_c hs5_lf hr4
      have hvals6 : vals6 = [.val (.word curw)] := by
        simpa [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs5_cur] using ha6.symm
      subst vals6
      obtain ⟨rfl, _, curw', hcur_inj, hcal6⟩ := one_word_arg_lookup lookup_ceil32 hl6
      have hcur_inj' : curw = curw' := by simpa using hcur_inj
      subst curw'
      have hbef_b := ceil32_return_bounds_g08 (callEntryStateHOLFinite s5 cal6) curw befw hs5_c hcal6 hrun6
      have hbef_eq_cur : befw = curw := hbef_b.2 (by rwa [hcur_eq])
      subst befw
      have hs6_endp : s6.locals.lookup (ofString "endp") = some (.val (.word endpw)) := by
        rw [hs6_loc]
        simp [hs5_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs4_endp,
          show ofString "before" ≠ ofString "endp" by decide,
          show ofString "cur" ≠ ofString "endp" by decide]
      obtain ⟨aftw, s7, hs7_c, hs7_lf, hs7_loc, ⟨vals7, body7, cal7, rs7, ha7, hl7, hrun7⟩, hr7⟩ :=
        ro_word_call_return_g08 (s := s) (st := s6) (by decide) hs6_c hs6_lf hr6
      have hvals7 : vals7 = [.val (.word endpw)] := by
        simpa [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs6_endp] using ha7.symm
      subst vals7
      obtain ⟨rfl, _, endpw2, hendp_inj2, hcal7⟩ := one_word_arg_lookup lookup_ceil32 hl7
      have hendp_inj2' : endpw = endpw2 := by simpa using hendp_inj2
      subst endpw2
      have haft_b := ceil32_return_bounds_g08 (callEntryStateHOLFinite s6 cal7) endpw aftw hs6_c hcal7 hrun7
      have hs7_bef : s7.locals.lookup (ofString "before") = some (.val (.word curw)) := by
        rw [hs7_loc, hs6_loc]
        simp [HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "after" ≠ ofString "before" by decide]
      have hs7_aft : s7.locals.lookup (ofString "after") = some (.val (.word aftw)) := by
        rw [hs7_loc]
        simp [HolFiniteMapExact.lookup_update, FUPDATE]
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr7
      have hcmp_ba : @evalHOLExact 64 F _ s7.toExact (fun x => Classical.propDecidable (s7.memaddrs x))
          (.cmp .notLower (.var .local (ofString "before")) (.var .local (ofString "after"))) =
          some (.val (.word (if ¬ (curw < aftw) then 1#64 else 0#64))) := by
        simp [evalHOLExact, hs7_bef, hs7_aft, Compiler.Encoders.Asm.wordCmpHOL]
      rw [hcmp_ba] at hr7
      dsimp only at hr7
      by_cases hba : ¬ (curw < aftw)
      · rw [if_pos hba, if_neg h10, hret_pair s7 0#64 0#64] at hr7
        have heb0 : ebw = 0#64 := by
          have hp : cw = 0#64 ∧ ebw = 0#64 := by simpa using hr7.symm
          exact hp.2
        subst ebw
        have haft_le_cur : aftw.toNat ≤ curw.toNat := by
          rw [BitVec.lt_def] at hba
          omega
        by_cases haft_max : aftw.toNat < 2 ^ 64 - 1
        · have hendp_le_aft := haft_b.1 haft_max
          rw [← hsw_eq, ← hendp_sum]
          omega
        · have hcur_lt64 := curw.isLt
          have hcur_eq_max : curw.toNat = 2 ^ 64 - 1 := by omega
          rw [hcur_eq_max] at hcur_eq
          rw [← hcur_eq] at hcur_mod
          omega
      · rw [if_neg hba, if_pos h00, evaluateHOLFiniteState_skip] at hr7
        dsimp only at hr7
        have hba_lt : curw.toNat < aftw.toNat := BitVec.lt_def.1 (Classical.not_not.1 hba)
        obtain ⟨caw, s8, hs8_c, hs8_lf, hs8_loc, _, hr8⟩ :=
          ro_word_call_return_g08 (s := s) (st := s7) (by decide) hs7_c hs7_lf hr7
        obtain ⟨cbw, s9, hs9_c, hs9_lf, hs9_loc, _, hr9⟩ :=
          ro_word_call_return_g08 (s := s) (st := s8) (by decide) hs8_c hs8_lf hr8
        have hs9_ca : s9.locals.lookup (ofString "ca") = some (.val (.word caw)) := by
          rw [hs9_loc, hs8_loc]
          simp [HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "cb" ≠ ofString "ca" by decide]
        have hs9_cb : s9.locals.lookup (ofString "cb") = some (.val (.word cbw)) := by
          rw [hs9_loc]
          simp [HolFiniteMapExact.lookup_update, FUPDATE]
        have hs9_bef : s9.locals.lookup (ofString "before") = some (.val (.word curw)) := by
          rw [hs9_loc, hs8_loc]
          simp [HolFiniteMapExact.lookup_update, FUPDATE, hs7_bef,
            show ofString "cb" ≠ ofString "before" by decide,
            show ofString "ca" ≠ ofString "before" by decide]
        have hs9_aft : s9.locals.lookup (ofString "after") = some (.val (.word aftw)) := by
          rw [hs9_loc, hs8_loc]
          simp [HolFiniteMapExact.lookup_update, FUPDATE, hs7_aft,
            show ofString "cb" ≠ ofString "after" by decide,
            show ofString "ca" ≠ ofString "after" by decide]
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr9
        have hcmp_ca : @evalHOLExact 64 F _ s9.toExact (fun x => Classical.propDecidable (s9.memaddrs x))
            (.cmp .equal (.var .local (ofString "ca")) (.const 18446744073709551615#64)) =
            some (.val (.word (if caw = 18446744073709551615#64 then 1#64 else 0#64))) := by
          simp [evalHOLExact, hs9_ca, Compiler.Encoders.Asm.wordCmpHOL]
        rw [hcmp_ca] at hr9
        dsimp only at hr9
        by_cases hca_max : caw = 18446744073709551615#64
        · rw [if_pos hca_max, if_neg h10, hret_pair s9 18446744073709551615#64 0#64] at hr9
          have hcw_eq : cw = 18446744073709551615#64 := by
            have hp : cw = 18446744073709551615#64 ∧ ebw = 0#64 := by simpa using hr9.symm
            exact hp.1
          subst cw
          change 18446744073709551615 < 2 ^ 64 - 1 at hcw_lt
          omega
        · rw [if_neg hca_max, if_pos h00, evaluateHOLFiniteState_skip] at hr9
          dsimp only at hr9
          rw [evaluateHOLFiniteState_return] at hr9
          have hev_ret : @evalHOLExact 64 F _ s9.toExact (fun x => Classical.propDecidable (s9.memaddrs x))
              (.rstruct
                [.op .sub [.var .local (ofString "ca"), .var .local (ofString "cb")],
                 .op .sub [.var .local (ofString "after"), .var .local (ofString "before")]]) =
              some (.rStruct [.val (.word (caw - cbw)), .val (.word (aftw - curw))]) := by
            simp [evalHOLExact, evalListHOLExact, hs9_ca, hs9_cb, hs9_aft, hs9_bef,
              wordOpHOL, wordOp, valueIsWord, valueWord]
          rw [hev_ret] at hr9
          dsimp only at hr9
          have hsz2 : sizeOfShapeWithContextHOL s9.structs
              (shapeOfHOLExact (.rStruct [.val (.word (caw - cbw)), .val (.word (aftw - curw))] : ValueHOL 64)) ≤ 32 := by
            simp [shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
          rw [if_pos hsz2] at hr9
          dsimp only at hr9
          have heb_eq : ebw = aftw - curw := by
            have hp : caw - cbw = cw ∧ aftw - curw = ebw := by simpa using hr9
            exact hp.2.symm
          subst ebw
          have hsub_nat : (aftw - curw).toNat = aftw.toNat - curw.toNat :=
            BitVec.toNat_sub_of_le (BitVec.le_def.2 (Nat.le_of_lt hba_lt))
          by_cases haft_lt : aftw.toNat < 2 ^ 64 - 1
          · have hendp_le_aft := haft_b.1 haft_lt
            rw [← hsw_eq, ← hendp_sum, hsub_nat, ← hcur_eq]
            omega
          · have haft_lt64 := aftw.isLt
            rw [← hsw_eq, ← hendp_sum, hsub_nat, ← hcur_eq]
            omega

private theorem eps_extend_memory_cost1_copy_cov_g08 :
    EvmPreservingSpec (fun _ => True)
      (fun s v post =>
        LocFrame s post ∧
        ∃ cw ebw : BitVec 64,
          v = .rStruct [.val (.word cw), .val (.word ebw)] ∧
          (ebw = 0#64 ∨
            ∃ before after : Nat,
              after < 2 ^ 37 ∧
              after % 32 = 0 ∧
              before < after ∧
              ebw.toNat = after - before ∧
              (memW s (globN s "ev" + 32) % 32 = 0 → before = memW s (globN s "ev" + 32))) ∧
          (∀ (stVal szVal : ValueHOL 64),
            s.locals.lookup (ofString "start") = some stVal →
            shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true →
            s.locals.lookup (ofString "size") = some szVal →
            shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact szVal) = true →
            satValue_g08 szVal ≠ 0#64 →
            cw.toNat < 2 ^ 64 - 1 →
            memW s (globN s "ev" + 32) % 32 = 0 →
            (satValue_g08 stVal).toNat + (satValue_g08 szVal).toNat ≤ memW s (globN s "ev" + 32) + ebw.toNat))
      (ofString "extend_memory_cost1") := by
  obtain ⟨params, body, retShape, hlk, hspec⟩ := eps_extend_memory_cost1_bounds
  have hlk_eq := lookup_extend_memory_cost1.symm.trans hlk
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_eq, rfl⟩
  subst hbody_eq
  refine ⟨_, _, _, lookup_extend_memory_cost1, ?_⟩
  intro F s hcode hInv hP hlookup hnt
  have hs := hspec s hcode hInv hP hlookup hnt
  dsimp only at hs ⊢
  refine ⟨fun v hv => ?_, hs.2⟩
  obtain ⟨h1, h2, h3, hlf, cw, ebw, hv_eq, heb_bounds⟩ := hs.1 v hv
  refine ⟨h1, h2, h3, hlf, cw, ebw, hv_eq, heb_bounds, ?_⟩
  intro stVal szVal hst hst_sh hsz hsz_sh hkw hcw_lt hcur_mod
  obtain ⟨k0, k1, k2, k3, rfl⟩ := u256_value_of_shape_g08 hsz_sh
  exact extend_memory_cost1_copy_coverage_g08 s stVal k0 k1 k2 k3 hcode hst hst_sh hsz hkw v hv cw ebw hv_eq hcw_lt hcur_mod

private theorem HandlerRun.seq_charge_copy_g08 {F : Type}
    {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {amtExp : ExpHOL 64} {cont : ProgHOL 64}
    (hpos : ∀ t (w : BitVec 64),
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp =
        some (.val (.word w)) →
      EvmInv t → P t → 0 < w.toNat)
    (hstep : ∀ t (amtw : BitVec 64) cpost,
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp =
        some (.val (.word amtw)) →
      amtw.toNat < 2 ^ 64 - 1 →
      EvmInv t → P t → EvmInv cpost → cpost.globals = t.globals →
      evmChain cpost = evmChain t →
      (∀ off : Nat, off ∈ ([24, 32, 40] : List Nat) →
        memW cpost (globN t "ev" + off) = memW t (globN t "ev" + off)) →
      Q { cpost with locals := t.locals })
    (hcont : HandlerRun s0 Q true cont) :
    HandlerRun s0 P charged (.seq (.call (some (none, none)) (ofString "charge_gas") [amtExp]) cont) := by
  intro t hc hInv hlen hR hP hnt
  have hR_le : evmR t ≤ evmR s0 := by
    cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at hR <;> omega
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) [amtExp] with _ | values
  · exact opDispatchPost_error s0 t
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup (ofString "charge_gas") values with _ | ⟨body', callee, ret'⟩
    · exact opDispatchPost_error s0 t
    · simp only [hl] at hnt ⊢
      by_cases hz : t.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hv_list : ∃ v0, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp = some v0 ∧ values = [v0] := by
          rw [evalListHOLFinite_eq_toExact] at hargs
          simp only [evalListHOLExact] at hargs
          rcases he : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp with _ | v0
          · simp [he] at hargs
          · simp only [he, Option.some.injEq] at hargs; exact ⟨v0, rfl, hargs.symm⟩
        obtain ⟨v0, hv0_ev, rfl⟩ := hv_list
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "charge_gas") [v0] =
            some (body', callee, ret') := by rwa [← hc]
        obtain ⟨rfl, rfl, amtw, rfl, hamt_cal⟩ := one_word_arg_lookup M21.lookup_charge_gas hl_orig
        have hamt_pos : 0 < amtw.toNat := hpos t amtw hv0_ev hInv hP
        have hInv_ce : EvmInv (callEntryStateHOLFinite t callee) := localsFree_evmInv t callee (t.clock - 1) hInv
        have hc_ce := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
          (callEntryStateHOLFinite t callee) (sourceFnBody Guest.Software.guestFn_charge_gas)).1
        have hcg := charge_gas_body_exact (callEntryStateHOLFinite t callee) hInv_ce hamt_cal
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee)
            (sourceFnBody Guest.Software.guestFn_charge_gas) with ⟨res, cpost⟩
        simp only [hrun] at hnt hmeta hcg ⊢
        let ce := callEntryStateHOLFinite t callee
        change cpost.code = t.code at hmeta
        cases res with
        | none => exact opDispatchPost_error s0 cpost
        | some r0 =>
          cases r0 with
          | timeOut => simp at hnt
          | returned v =>
            by_cases hsh_ok : shapeEqHOL (shapeOfHOLExact v) .one = true
            · simp only [hsh_ok, ↓reduceIte] at hnt ⊢
              obtain ⟨hInv_cp, hglob_cp, hch_cp, hR_cp⟩ := hcg.1 v rfl
              have hamt_lt : amtw.toNat < 2 ^ 64 - 1 :=
                charge_gas_return_lt_sentinel_g08 ce hInv_ce hamt_cal (by rw [hrun])
              have hmem_head_cp : ∀ off : Nat, off ∈ ([24, 32, 40] : List Nat) →
                  memW cpost (globN t "ev" + off) = memW t (globN t "ev" + off) := by
                intro off hoff
                have hhead_mem : (globN t "ev", globN t "cur_cont") ∈ evmChain t := by simp [evmChain, evmChainFrom]
                have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead_mem
                have hb_ev := (frameWF_bounds hInv.1.2 hFW0).1
                dsimp only at hb_ev
                have hev_pos : 0 < globN t "ev" := by
                  obtain ⟨hin, _⟩ := (hFW0.1 (globN t "ev", 280) (by simp)).1
                  have h1 := hInv.1.2.2.2.1; have h2 := hInv.1.2.2.2.2.1
                  rw [R11Shards.scratchStart_val] at h1; dsimp only at hin; omega
                obtain ⟨evw, hevw, hevw_nat⟩ := global_word_of_pos t "ev" hev_pos
                have hevw_ce : ce.globals.lookup (ofString "ev") = some (.val (.word evw)) := hevw
                have hbody_cg : sourceFnBody Guest.Software.guestFn_charge_gas =
                    .dec (ofString "gl") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 64]))
                      (.seq
                        (.ite (.cmp .lower (.var .local (ofString "gl")) (.var .local (ofString "amount")))
                          (.raise (ofString "EvmErr") (.const 4))
                          .skip)
                        (.seq
                          (.store (.op .add [.var .global (ofString "ev"), .const 64])
                            (.op .sub [.var .local (ofString "gl"), .var .local (ofString "amount")]))
                          (.seq
                            (.store (.op .add [.var .global (ofString "ev"), .const 184])
                              (.op .add
                                [.load .one (.op .add [.var .global (ofString "ev"), .const 184]),
                                 .var .local (ofString "amount")]))
                            (.return (.const 0))))) := rfl
                have hmem_ne : ∀ x : BitVec 64,
                    x ≠ BitVec.ofNat 64 (globN t "ev" + 64) →
                    x ≠ BitVec.ofNat 64 (globN t "ev" + 184) →
                    cpost.memory x = t.memory x := by
                  have hrun' := hrun
                  rw [hbody_cg, evaluateHOLFiniteState_dec_total] at hrun'; dsimp only at hrun'
                  split at hrun'
                  · simp at hrun'
                  · rename_i glv _
                    split at hrun'
                    · set s1 := setVarHOLFinite (ofString "gl") glv ce
                      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hrun'
                      split at hrun'
                      · split at hrun'
                        · simp only [evaluateHOLFiniteState_skip] at hrun'
                          rw [evaluateHOLFiniteState_seq_line780] at hrun'
                          rcases hst1 : evaluateHOLFiniteState s1
                              (.store (.op .add [.var .global (ofString "ev"), .const 64])
                                (.op .sub [.var .local (ofString "gl"), .var .local (ofString "amount")])) with ⟨r1, s2⟩
                          rw [hst1] at hrun'
                          cases r1 with
                          | some res1 =>
                            have herr1 := store_some_eq_error_g08 hst1; subst herr1; simp at hrun'
                          | none =>
                            dsimp only at hrun'
                            obtain ⟨w1, _, hs2_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s1) (post := s2)
                              (gname := "ev") (gbase := globN t "ev") (off := 64) hevw_ce hevw_nat (by omega)
                              (fun u hu => by
                                simp only [evalHOLExact, wordOpHOL] at hu; revert hu
                                rcases @evalListHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a)) _ with _ | vs
                                · simp
                                · dsimp only; split
                                  · simp only [Option.map]
                                    rcases wordOp .sub (vs.map valueWord) with _ | w
                                    · simp
                                    · intro h'; injection h' with h''; exact ⟨w, h''.symm⟩
                                  · simp) hst1
                            rw [evaluateHOLFiniteState_seq_line780] at hrun'
                            rcases hst2 : evaluateHOLFiniteState s2
                                (.store (.op .add [.var .global (ofString "ev"), .const 184])
                                  (.op .add
                                    [.load .one (.op .add [.var .global (ofString "ev"), .const 184]),
                                     .var .local (ofString "amount")])) with ⟨r2, s3⟩
                            rw [hst2] at hrun'
                            cases r2 with
                            | some res2 =>
                              have herr2 := store_some_eq_error_g08 hst2; subst herr2; simp at hrun'
                            | none =>
                              dsimp only at hrun'
                              obtain ⟨w2, _, hs3_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s2) (post := s3)
                                (gname := "ev") (gbase := globN t "ev") (off := 184)
                                (by rw [hs2_eq]; exact hevw_ce) hevw_nat (by omega)
                                (fun u hu => by
                                  simp only [evalHOLExact, wordOpHOL] at hu; revert hu
                                  rcases @evalListHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a)) _ with _ | vs
                                  · simp
                                  · dsimp only; split
                                    · simp only [Option.map]
                                      rcases wordOp .add (vs.map valueWord) with _ | w
                                      · simp
                                      · intro h'; injection h' with h''; exact ⟨w, h''.symm⟩
                                    · simp) hst2
                              rw [evaluateHOLFiniteState_return] at hrun'; dsimp only [evalHOLExact] at hrun'
                              have hsz0 : sizeOfShapeWithContextHOL s3.structs
                                  (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
                                simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
                              rw [if_pos hsz0] at hrun'; dsimp only at hrun'
                              injection hrun' with _ hcpost_eq
                              subst hcpost_eq
                              intro x hx64 hx184
                              dsimp only [emptyLocalsHOLFinite]
                              rw [hs3_eq]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hx184]
                              rw [hs2_eq]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hx64]
                              rfl
                        · rcases hraise : evaluateHOLFiniteState s1 (.raise (ofString "EvmErr") (.const 4)) with ⟨rr, sr⟩
                          rw [hraise] at hrun'
                          have hr_nn : rr ≠ none := by
                            rw [evaluateHOLFiniteState_raise] at hraise; dsimp only [evalHOLExact] at hraise
                            split at hraise
                            · split at hraise <;> (injection hraise with h1 _; subst h1; simp)
                            · injection hraise with h1 _; subst h1; simp
                          cases rr with
                          | none => exact absurd rfl hr_nn
                          | some r0 =>
                            dsimp only at hrun'
                            have hr_not_ret : ∀ vr, r0 ≠ .returned vr := by
                              rw [evaluateHOLFiniteState_raise] at hraise; dsimp only [evalHOLExact] at hraise
                              split at hraise
                              · split at hraise <;> (injection hraise with h1 _; injection h1 with h1'; subst h1'; simp)
                              · injection hraise with h1 _; injection h1 with h1'; subst h1'; simp
                            cases r0 with
                            | returned vr => exact absurd rfl (hr_not_ret vr)
                            | _ => simp at hrun'
                      · simp at hrun'
                    · simp at hrun'
                have hne64 : BitVec.ofNat 64 (globN t "ev" + off) ≠ BitVec.ofNat 64 (globN t "ev" + 64) := by
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
                  intro heq; have htn := congrArg BitVec.toNat heq
                  rcases hoff with rfl | rfl | rfl <;>
                    (rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at htn; omega)
                have hne184 : BitVec.ofNat 64 (globN t "ev" + off) ≠ BitVec.ofNat 64 (globN t "ev" + 184) := by
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
                  intro heq; have htn := congrArg BitVec.toNat heq
                  rcases hoff with rfl | rfl | rfl <;>
                    (rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at htn; omega)
                unfold memW; rw [hmem_ne _ hne64 hne184]
              let resumed : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
              have hInv_res : EvmInv resumed := localsFree_evmInv cpost t.locals cpost.clock hInv_cp
              have hc_res := evm_congr (s := cpost) (t := resumed) rfl rfl
              have hlen_res : (evmChain resumed).length = (evmChain s0).length := by
                rw [hc_res.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              have hR_lt : evmR resumed < evmR s0 := by
                rw [hc_res.2.1]; rw [hc_ce.2.1] at hR_cp; omega
              exact hcont resumed (hmeta.trans hc) hInv_res hlen_res (by simp [hR_lt])
                (hstep t amtw cpost hv0_ev hamt_lt hInv hP hInv_cp hglob_cp (hch_cp.trans (evmChain_congr rfl rfl)) hmem_head_cp)
                (by simpa [resumed] using hnt)
            · simp only [hsh_ok, Bool.false_eq_true, ↓reduceIte]
              exact opDispatchPost_error s0 cpost
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨hInv_cp, _, hch_cp, hR_cp⟩ := hcg.2 ⟨ev, rfl⟩
              have hInv_el : EvmInv cpost.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost _ cpost.clock hInv_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              refine ⟨?_, fun _ => ⟨hInv_el, ?_, ?_⟩⟩
              · rintro ⟨_, h⟩; cases h
              · rw [hc_el.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              · rw [hc_el.2.1, hR_cp, hc_ce.2.1]; exact hR_le
            · refine opDispatchPost_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => exact opDispatchPost_error s0 cpost
          | «continue» => exact opDispatchPost_error s0 cpost
          | finalFfi f =>
            refine opDispatchPost_other (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => exact opDispatchPost_error s0 cpost.emptyLocalsHOLFinite

private theorem copy_words_base_pos_g08 (w : BitVec 64) (hw : w.toNat < 2 ^ 59) :
    (3#64 + 3#64 * w).toNat = 3 + 3 * w.toNat ∧
    0 < (3#64 + 3#64 * w).toNat := by
  have hm : (3#64 * w).toNat = 3 * w.toNat := by
    rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (by change 3 * w.toNat < 2 ^ 64; omega)]
    rfl
  have ha : (3#64 + 3#64 * w).toNat = 3 + 3 * w.toNat := by
    rw [BitVec.toNat_add, hm, Nat.mod_eq_of_lt (by change 3 + 3 * w.toNat < 2 ^ 64; omega)]
    rfl
  exact ⟨ha, by rw [ha]; omega⟩

private def CopyExpand_g08 {F : Type} (stVal szVal : ValueHOL 64)
    (t : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ cw ebw : BitVec 64,
    t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
    (ebw = 0#64 ∨
      (memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
       (memW t (globN t "ev" + 32) + ebw.toNat) % 8 = 0 ∧
       memW t (globN t "ev" + 24) + memW t (globN t "ev" + 40) = globN t "frame_mem_ptr")) ∧
    (satValue_g08 szVal ≠ 0#64 →
      (satValue_g08 stVal).toNat + (satValue_g08 szVal).toNat ≤
        memW t (globN t "ev" + 32) + ebw.toNat)

private theorem copy_cost_phase_run_g08 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (stVal szVal : ValueHOL 64)
    (hst_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true)
    (hsz_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact szVal) = true)
    (K : HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (baseExp : ExpHOL 64)
    (hKb : ∀ t : PanSemStateFiniteExact 64 F, K t.locals →
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) baseExp = some (.val (.word 3#64)))
    (hKx : ∀ l v, K l → K (l.update (ofString "x", v)))
    (hKcost : ∀ l v, K l → K (l.update (ofString "cost", v)))
    (hKst : ∀ l, K l → l.lookup (ofString "mstart") = some stVal)
    (hKsz : ∀ l, K l → l.lookup (ofString "size") = some szVal)
    (hKw : ∀ l, K l → ∃ ww : BitVec 64,
      l.lookup (ofString "w") = some (.val (.word ww)) ∧ ww.toNat < 2 ^ 59)
    {cont : ProgHOL 64}
    (hcont : HandlerRun s0 (fun t => K t.locals ∧ CopyExpand_g08 stVal szVal t) true cont) :
    HandlerRun s0 (fun t => HeadMemAligned t ∧ K t.locals) false
      (.decCall (ofString "x") (.comb [.one, .one]) (ofString "extend_memory_cost1")
        [.var .local (ofString "mstart"), .var .local (ofString "size")]
        (.decCall (ofString "cost") .one (ofString "add_sat")
          [.op .add [baseExp, .panop .mul [.const 3#64, .var .local (ofString "w")]],
           .rfield 0 (.var .local (ofString "x"))]
          (.seq (.call (some (none, none)) (ofString "charge_gas") [.var .local (ofString "cost")]) cont))) := by
  refine HandlerRun.decCall
    (Q := fun t => HeadMemAligned t ∧ K t.locals ∧
      ∃ cw ebw : BitVec 64,
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        (ebw = 0#64 ∨
          (memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
           (memW t (globN t "ev" + 32) + ebw.toNat) % 8 = 0 ∧
           memW t (globN t "ev" + 24) + memW t (globN t "ev" + 40) = globN t "frame_mem_ptr")) ∧
        (cw.toNat < 2 ^ 64 - 1 → satValue_g08 szVal ≠ 0#64 →
          (satValue_g08 stVal).toNat + (satValue_g08 szVal).toNat ≤ memW t (globN t "ev" + 32) + ebw.toNat))
    eps_extend_memory_cost1_copy_cov_g08
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t values _ callee _ v cpost _ ⟨hHM, hK⟩ hargs hl_orig _ _ hQc => by
      obtain ⟨hlf, cw, ebw, rfl, heb_bounds, hcov_ce⟩ := hQc
      obtain ⟨v1, v2, rfl, _, _, hcal_st, hcal_sz⟩ := extend_memory_cost1_two_args_lookup_g08 hl_orig
      rw [evalListHOLFinite_eq_toExact] at hargs
      have hst := hKst t.locals hK
      have hsz := hKsz t.locals hK
      simp only [evalListHOLExact, evalHOLExact, hst, hsz, Option.some.injEq, List.cons.injEq] at hargs
      rcases hargs with ⟨rfl, rfl, _⟩
      let ce := callEntryStateHOLFinite t callee
      have hHM_ce : HeadMemAligned ce := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      have hHM_cp : HeadMemAligned cpost :=
        headMemAligned_congr_head_only (by rw [hlf]) (fun off _ => by unfold memW; rw [hlf]) hHM_ce
      let res := setVarHOLFinite (ofString "x") (.rStruct [.val (.word cw), .val (.word ebw)]) { cpost with locals := t.locals }
      have hHM_res : HeadMemAligned res := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp
      have hmem32_eq : memW res (globN res "ev" + 32) = memW ce (globN ce "ev" + 32) := by
        have hg : globN res "ev" = globN ce "ev" := globN_eq_of_lookup_eq (by change cpost.globals.lookup _ = ce.globals.lookup _; rw [hlf])
        have hm : res.memory = ce.memory := by change cpost.memory = ce.memory; rw [hlf]
        rw [hg]; unfold memW; rw [hm]
      refine ⟨hHM_res, hKx _ _ hK, cw, ebw,
        by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], ?_, ?_⟩
      · rcases heb_bounds with rfl | ⟨before, after, haft_lt, haft_mod, hbef_lt, heb_sub, hbef_eq⟩
        · exact Or.inl rfl
        · right
          have hbef : before = memW ce (globN ce "ev" + 32) := hbef_eq hHM_ce.1
          have hsum : memW res (globN res "ev" + 32) + ebw.toNat = after := by
            rw [hmem32_eq, ← hbef]; omega
          rw [hsum]
          exact ⟨haft_lt, by omega, hHM_res.2⟩
      · intro hcw_lt hn
        rw [hmem32_eq]
        exact hcov_ce stVal szVal hcal_st hst_sh hcal_sz hsz_sh hn hcw_lt hHM_ce.1)
    ?_
  refine HandlerRun.decCall
    (Q := fun t => HeadMemAligned t ∧ K t.locals ∧
      ∃ totw bw cw ebw : BitVec 64,
        t.locals.lookup (ofString "cost") = some (.val (.word totw)) ∧
        0 < totw.toNat ∧
        (totw.toNat < 2 ^ 64 - 1 → totw.toNat = bw.toNat + cw.toNat) ∧
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        (ebw = 0#64 ∨
          (memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
           (memW t (globN t "ev" + 32) + ebw.toNat) % 8 = 0 ∧
           memW t (globN t "ev" + 24) + memW t (globN t "ev" + 40) = globN t "frame_mem_ptr")) ∧
        (cw.toNat < 2 ^ 64 - 1 → satValue_g08 szVal ≠ 0#64 →
          (satValue_g08 stVal).toNat + (satValue_g08 szVal).toNat ≤ memW t (globN t "ev" + 32) + ebw.toNat))
    eps_add_sat_pos_exact_g08
    (fun t values b_as callee rs_as hc _ ⟨_, hK, cw, ebw, hx, _⟩ hargs hl => by
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "add_sat") values =
          some (b_as, callee, rs_as) := by rwa [← hc]
      obtain ⟨_, _, w1, w2, rfl, hw1, hw2⟩ := two_word_arg_lookup (by decide) lookup_add_sat hl_orig
      obtain ⟨ww, hw, hwb⟩ := hKw t.locals hK
      have hargs_ok : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.op .add [baseExp, .panop .mul [.const 3#64, .var .local (ofString "w")]],
           .rfield 0 (.var .local (ofString "x"))] =
          some [.val (.word (3#64 + 3#64 * ww)), .val (.word cw)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hKb t hK, hw, hx, wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord]
      rw [hargs_ok] at hargs
      injection hargs with hvs
      rcases List.cons.inj hvs with ⟨hw1_eq, hvs'⟩
      rcases List.cons.inj hvs' with ⟨hw2_eq, _⟩
      injection hw1_eq with hw1'; injection hw1' with hw1''; subst hw1''
      injection hw2_eq with hw2'; injection hw2' with hw2''; subst hw2''
      exact ⟨3#64 + 3#64 * ww, cw, hw1, hw2, (copy_words_base_pos_g08 ww hwb).2⟩)
    (fun t values _ callee _ v cpost _ ⟨hHM, hK, cw, ebw, hx, heb_cond, hcov_imp⟩ hargs hl_orig _ _ hQc => by
      obtain ⟨hlf, totw, rfl, hpos, htot_ex⟩ := hQc
      obtain ⟨_, _, w1, w2, rfl, hw1, hw2⟩ := two_word_arg_lookup (by decide) lookup_add_sat hl_orig
      obtain ⟨ww, hw, hwb⟩ := hKw t.locals hK
      have hargs_ok : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.op .add [baseExp, .panop .mul [.const 3#64, .var .local (ofString "w")]],
           .rfield 0 (.var .local (ofString "x"))] =
          some [.val (.word (3#64 + 3#64 * ww)), .val (.word cw)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hKb t hK, hw, hx, wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord]
      rw [hargs_ok] at hargs
      injection hargs with hvs
      rcases List.cons.inj hvs with ⟨hw1_eq, hvs'⟩
      rcases List.cons.inj hvs' with ⟨hw2_eq, _⟩
      injection hw1_eq with hw1'; injection hw1' with hw1''; subst hw1''
      injection hw2_eq with hw2'; injection hw2' with hw2''; subst hw2''
      let ce := callEntryStateHOLFinite t callee
      have hHM_ce : HeadMemAligned ce := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      have hHM_cp : HeadMemAligned cpost :=
        headMemAligned_congr_head_only (by rw [hlf]) (fun off _ => by unfold memW; rw [hlf]) hHM_ce
      let res := setVarHOLFinite (ofString "cost") (.val (.word totw)) { cpost with locals := t.locals }
      have hHM_res : HeadMemAligned res := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp
      have hmem32_eq : memW res (globN res "ev" + 32) = memW t (globN t "ev" + 32) := by
        have hg : globN res "ev" = globN t "ev" := globN_eq_of_lookup_eq (by change cpost.globals.lookup _ = t.globals.lookup _; rw [hlf]; rfl)
        have hm : res.memory = t.memory := by change cpost.memory = t.memory; rw [hlf]; rfl
        rw [hg]; unfold memW; rw [hm]
      refine ⟨hHM_res, hKcost _ _ hK, totw, 3#64 + 3#64 * ww, cw, ebw,
        by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
        hpos, htot_ex _ _ hw1 hw2,
        by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hx,
          show ofString "cost" ≠ ofString "x" by decide], ?_, ?_⟩
      · rcases heb_cond with rfl | ⟨hlt37, hmod8, _⟩
        · exact Or.inl rfl
        · right
          rw [hmem32_eq]
          exact ⟨hlt37, hmod8, hHM_res.2⟩
      · intro hcw_lt hn
        rw [hmem32_eq]
        exact hcov_imp hcw_lt hn)
    ?_
  refine HandlerRun.seq_charge_copy_g08
    (Q := fun t => K t.locals ∧ CopyExpand_g08 stVal szVal t)
    (fun t w hw _ ⟨_, _, totw, _, _, _, htot, hpos, _⟩ => by
      change t.locals.lookup (ofString "cost") = some (.val (.word w)) at hw
      rw [htot] at hw; injection hw with hw'; injection hw' with hw''; injection hw'' with hweq; subst hweq
      exact hpos)
    (fun t amtw cpost hw hamt_lt _ ⟨hHM, hK, totw, bw, cw, ebw, htot, _, htot_ex, hx, heb_cond, hcov_imp⟩ _ hglob_cp _ hmem_head_cp => by
      change t.locals.lookup (ofString "cost") = some (.val (.word amtw)) at hw
      rw [htot] at hw; injection hw with hw'; injection hw' with hw''; injection hw'' with hweq; subst hweq
      have htot_sum := htot_ex hamt_lt
      have hcw_lt : cw.toNat < 2 ^ 64 - 1 := by omega
      have hHM_cp : HeadMemAligned cpost := headMemAligned_congr_head_only hglob_cp hmem_head_cp hHM
      let res : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
      have hHM_res : HeadMemAligned res := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp
      have hmem32_eq : memW res (globN res "ev" + 32) = memW t (globN t "ev" + 32) := by
        have hg : globN res "ev" = globN t "ev" := globN_eq_of_lookup_eq (by change cpost.globals.lookup _ = t.globals.lookup _; rw [hglob_cp])
        rw [hg]; exact hmem_head_cp 32 (by simp)
      refine ⟨hK, cw, ebw, hx, ?_, ?_⟩
      · rcases heb_cond with rfl | ⟨hlt37, hmod8, _⟩
        · exact Or.inl rfl
        · right
          rw [hmem32_eq]
          exact ⟨hlt37, hmod8, hHM_res.2⟩
      · intro hn
        rw [hmem32_eq]
        exact hcov_imp hcw_lt hn)
    hcont

private theorem copy_extend_phase_run_g08 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (stVal szVal : ValueHOL 64) (K : HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    {cont : ProgHOL 64}
    (hcont : HandlerRun s0 (fun t => K t.locals ∧
      (satValue_g08 szVal ≠ 0#64 →
        (satValue_g08 stVal).toNat + (satValue_g08 szVal).toNat ≤ memW t (globN t "ev" + 32))) true cont) :
    HandlerRun s0 (fun t => K t.locals ∧ CopyExpand_g08 stVal szVal t) true
      (.seq (.call (some (none, none)) (ofString "extend_memory")
        [.rfield 1 (.var .local (ofString "x"))]) cont) := by
  refine HandlerRun.seq_call
    (Q := fun t => K t.locals ∧
      (satValue_g08 szVal ≠ 0#64 →
        (satValue_g08 stVal).toNat + (satValue_g08 szVal).toNat ≤ memW t (globN t "ev" + 32)))
    eps_extend_memory_aligned_len_g08
    (fun t values b_em callee rs_em hc _ ⟨_, cw, ebw, hx, heb_cond, _⟩ hargs hl => by
      have hx1 : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.rfield 1 (.var .local (ofString "x"))] = some [.val (.word ebw)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hx]
      rw [hx1] at hargs; injection hargs with hvs; subst hvs
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "extend_memory") [.val (.word ebw)] =
          some (b_em, callee, rs_em) := by rwa [← hc]
      obtain ⟨_, _, ebw', heq_eb, hcal_eb⟩ := one_word_arg_lookup lookup_extend_memory hl_orig
      injection heq_eb with heq1; injection heq1 with heq2; subst heq2
      exact ⟨ebw, hcal_eb, heb_cond⟩)
    (fun t values _ callee _ _ cpost _ ⟨hK, cw, ebw, hx, _, hcov⟩ hargs hl_orig _ _ ⟨_, hlen_eq⟩ => by
      have hx1 : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.rfield 1 (.var .local (ofString "x"))] = some [.val (.word ebw)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hx]
      rw [hx1] at hargs; injection hargs with hvs; subst hvs
      obtain ⟨_, _, ebw', heq_eb, hcal_eb⟩ := one_word_arg_lookup lookup_extend_memory hl_orig
      injection heq_eb with heq1; injection heq1 with heq2; subst heq2
      refine ⟨hK, ?_⟩
      intro hn
      change (satValue_g08 stVal).toNat + (satValue_g08 szVal).toNat ≤ memW cpost (globN cpost "ev" + 32)
      rw [hlen_eq ebw hcal_eb]
      exact hcov hn)
    hcont

private theorem seq_call_return_g08 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop}
    {Pc : PanSemStateFiniteExact 64 F → Prop}
    {charged : Bool}
    {fname : MlS} {params : List (MlS × ShapeHOL)} {body : ProgHOL 64}
    {args : List (ExpHOL 64)}
    (hlook : originalRuntimeCode.lookup fname = some (params, body, .one))
    (hentry : ∀ t values callee,
      t.code = originalRuntimeCode → EvmInv t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, callee, .one) →
      Pc (callEntryStateHOLFinite t callee))
    (hbody : HandlerRun s0 Pc charged body) :
    HandlerRun s0 P charged (.seq (.call (some (none, none)) fname args) (.return (.const 0#64))) := by
  intro t hc hInv hlen hR hP hnt
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args with _ | values
  · exact opDispatchPost_error s0 t
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact opDispatchPost_error s0 t
    · simp only [hl] at hnt ⊢
      by_cases hz : t.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hbody_eq : body' = body :=
          lookupCodeHOLFinite_installed_body t.code.lookup fname params body body'
            .one ret' values callee (by rw [hc]; exact hlook) hl
        subst body'
        have hret_eq : ret' = .one := by
          have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
            t.code.lookup fname values body callee ret' hl
          rw [hc] at hx; simp only [Flapjack.lookupCodeHOLExact, hlook] at hx
          split at hx
          · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
          · cases hx
        subst ret'
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
            some (body, callee, .one) := by rwa [← hc]
        have hInv_ce : EvmInv (callEntryStateHOLFinite t callee) := localsFree_evmInv t callee (t.clock - 1) hInv
        have hc_ce := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
        have hPc : Pc (callEntryStateHOLFinite t callee) := hentry t values callee hc hInv hP hargs hl_orig
        have hlen_ce : (evmChain (callEntryStateHOLFinite t callee)).length = (evmChain s0).length := hc_ce.2.2.1.trans hlen
        have hR_ce : if charged then evmR (callEntryStateHOLFinite t callee) < evmR s0 else evmR (callEntryStateHOLFinite t callee) ≤ evmR s0 := by
          rw [hc_ce.2.1]; exact hR
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite t callee) body).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body with ⟨res, cpost⟩
        simp only [hrun] at hnt hmeta ⊢
        change cpost.code = t.code at hmeta
        have hB (hsafe : res ≠ some .timeOut) : OpDispatchPost s0 res cpost := by
          have hs := hbody (callEntryStateHOLFinite t callee) hc hInv_ce hlen_ce hR_ce hPc (by rw [hrun]; exact hsafe)
          rw [hrun] at hs
          exact hs
        cases res with
        | none => exact opDispatchPost_error s0 cpost
        | some r0 =>
          cases r0 with
          | timeOut => simp at hnt
          | returned v =>
            by_cases hsh_ok : shapeEqHOL (shapeOfHOLExact v) .one = true
            · simp only [hsh_ok, ↓reduceIte] at hnt ⊢
              let resumed : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
              rw [(return_const0_step_g08 resumed).1, (return_const0_step_g08 resumed).2]
              have hp : OpDispatchPost s0 (some (.returned (.val (.word 0#64)))) cpost :=
                ⟨fun _ => (hB (by simp)).1 ⟨v, rfl⟩, fun ⟨_, he⟩ => by cases he⟩
              exact opDispatchPost_congr_lc (post := cpost) rfl rfl rfl hp
            · simp only [hsh_ok, Bool.false_eq_true, ↓reduceIte]
              exact opDispatchPost_error s0 cpost
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨hInv_cp, hlen_cp, hR_cp⟩ := (hB (by simp)).2 ⟨ev, rfl⟩
              have hInv_el : EvmInv cpost.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost _ cpost.clock hInv_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              refine ⟨?_, fun _ => ⟨hInv_el, ?_, ?_⟩⟩
              · rintro ⟨_, h⟩; cases h
              · rw [hc_el.2.2.1]; exact hlen_cp
              · rw [hc_el.2.1]; exact hR_cp
            · refine opDispatchPost_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => exact opDispatchPost_error s0 cpost
          | «continue» => exact opDispatchPost_error s0 cpost
          | finalFfi f =>
              refine opDispatchPost_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; cases h
          | error => exact opDispatchPost_error s0 cpost.emptyLocalsHOLFinite

private theorem HandlerRun.seq_ite_copy_g08 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {cond : ExpHOL 64} {yes no cont : ProgHOL 64}
    (hyes : HandlerRun s0 (fun t => P t ∧
      ∃ w : BitVec 64, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) cond = some (.val (.word w)) ∧ w ≠ 0) charged (.seq yes cont))
    (hno : HandlerRun s0 (fun t => P t ∧
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) cond = some (.val (.word 0))) charged (.seq no cont)) :
    HandlerRun s0 P charged (.seq (.ite cond yes no) cont) := by
  intro t hc hInv hlen hR hP hnt
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
  revert hnt
  split
  · rename_i w hw
    by_cases hw0 : w = 0
    · subst hw0; simp only [↓reduceIte]
      intro hnt
      have hh := hno t hc hInv hlen hR ⟨hP, hw⟩
      simpa only [evaluateHOLFiniteState_seq_line780] using hh (by simpa only [evaluateHOLFiniteState_seq_line780] using hnt)
    · simp only [hw0, ↓reduceIte]
      intro hnt
      have hh := hyes t hc hInv hlen hR ⟨hP, w, hw, hw0⟩
      simpa only [evaluateHOLFiniteState_seq_line780] using hh (by simpa only [evaluateHOLFiniteState_seq_line780] using hnt)
  · intro _; exact opDispatchPost_error s0 t

private theorem HandlerRun.seq_head_mem_eff_g08 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {call cont : ProgHOL 64}
    (heff : ∀ t, t.code = originalRuntimeCode → EvmInv t → P t →
      (evaluateHOLFiniteState t call).1 ≠ some .timeOut →
      let out := evaluateHOLFiniteState t call
      (out.1 = none → ByteRegionEffect t out.2
        [(memW t (globN t "ev" + 24), memW t (globN t "ev" + 40))]) ∧
      (out.1 ≠ none → (∀ v, out.1 ≠ some (.returned v)) ∧ ¬ IsEvmErr out.1))
    (hcont : HandlerRun s0 (fun _ => True) charged cont) :
    HandlerRun s0 P charged (.seq call cont) := by
  intro t hc hInv hlen hR hP hnt
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hcall : evaluateHOLFiniteState t call with ⟨res, post⟩
  simp only [hcall] at hnt ⊢
  have hnt_call : (evaluateHOLFiniteState t call).1 ≠ some .timeOut := by
    rw [hcall]; intro h; change res = some .timeOut at h; subst res; exact hnt rfl
  have hh := heff t hc hInv hP hnt_call
  rw [hcall] at hh
  cases res with
  | none =>
    dsimp only at hnt ⊢
    have hb := hh.1 rfl
    obtain ⟨hInv_post, hch, hgas⟩ := evmInv_of_head_mem_bytes_g08 hInv hb
    exact hcont post (hb.code.trans hc) hInv_post
      (by rw [hch]; exact hlen) (by rw [hgas]; exact hR) trivial hnt
  | some r0 => exact opDispatchPost_other (hh.2 (by simp)).1 (hh.2 (by simp)).2

private theorem HandlerRun.decCall_sat_copy_g08 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {nm : MlS} {arg : ExpHOL 64} {cont : ProgHOL 64}
    (varg : ValueHOL 64)
    (hshape : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact varg) = true)
    (harg : ∀ t, P t → @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) arg = some varg)
    (hstep : ∀ t cpost, P t → LocFrame t cpost →
      Q (setVarHOLFinite nm (.val (.word (satValue_g08 varg))) { cpost with locals := t.locals }))
    (hcont : HandlerRun s0 Q charged cont) :
    HandlerRun s0 P charged (.decCall nm .one (ofString "sat_word") [arg] cont) := by
  refine HandlerRun.decCall eps_sat_word_exact_g08
    (fun t values b_sw callee rs_sw hc _ hP hargs hl => by
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "sat_word") values =
          some (b_sw, callee, rs_sw) := by rwa [← hc]
      obtain ⟨_, _, v0, rfl, hcal_v⟩ := single_comb_arg_lookup_g08 lookup_sat_word_g08 hl_orig
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact, harg t hP, Option.some.injEq, List.cons.injEq] at hargs
      rcases hargs with ⟨rfl, _⟩
      exact ⟨varg, hcal_v, hshape⟩)
    (fun t values _ callee _ v cpost _ hP hargs hl_orig _ _ ⟨hlf, hv_eq⟩ => by
      obtain ⟨_, _, v0, rfl, hcal_v⟩ := single_comb_arg_lookup_g08 lookup_sat_word_g08 hl_orig
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact, harg t hP, Option.some.injEq, List.cons.injEq] at hargs
      rcases hargs with ⟨rfl, _⟩
      have hv := hv_eq varg hcal_v
      subst v
      exact hstep t cpost hP (by rw [hlf]; rfl))
    hcont

private theorem HandlerRun.decCall_stack_copy_g08 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (K L : HolFiniteMapExact MlS (ValueHOL 64) → Prop) {charged : Bool}
    {nm : MlS} {cont : ProgHOL 64}
    (hstep : ∀ l v, K l →
      shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact v) = true → L (l.update (nm, v)))
    (hcont : HandlerRun s0 (fun t => HeadMemAligned t ∧ L t.locals) charged cont) :
    HandlerRun s0 (fun t => HeadMemAligned t ∧ K t.locals) charged
      (.decCall nm (.comb [.one, .one, .one, .one]) (ofString "stack_pop") [] cont) := by
  refine HandlerRun.decCall eps_stack_pop_preserves_headMem
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ callee _ v cpost _ ⟨hHM, hK⟩ _ _ _ _ ⟨_, hsh, hHM_step⟩ => by
      have hHM_ce : HeadMemAligned (callEntryStateHOLFinite t callee) :=
        headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      have hHM_cp : HeadMemAligned cpost := hHM_step hHM_ce
      exact ⟨headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp, hstep t.locals v hK hsh⟩)
    hcont

private theorem eval_head_mem_plus_local_g08 {F : Type}
    (t : PanSemStateFiniteExact 64 F) (hInv : EvmInv t)
    (nm : String) (sw : BitVec 64)
    (hsw : t.locals.lookup (ofString nm) = some (.val (.word sw))) :
    ∃ basew : BitVec 64,
      basew.toNat = memW t (globN t "ev" + 24) ∧
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        (.op .add
          [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]),
           .var .local (ofString nm)]) =
        some (.val (.word (basew + sw))) := by
  have hhead : (globN t "ev", globN t "cur_cont") ∈ evmChain t := by
    simp [evmChain, evmChainFrom]
  have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead
  have hb_ev := (frameWF_bounds hInv.1.2 hFW0).1
  dsimp only at hb_ev
  have hev_pos : 0 < globN t "ev" := by
    obtain ⟨hin, _⟩ := (hFW0.1 (globN t "ev", 280) (by simp)).1
    have h1 := hInv.1.2.2.2.1; have h2 := hInv.1.2.2.2.2.1
    rw [R11Shards.scratchStart_val] at h1; dsimp only at hin; omega
  obtain ⟨evw, hevw, hevw_nat⟩ := global_word_of_pos t "ev" hev_pos
  have hrec_w := (hFW0.1 (globN t "ev", 280) (by simp)).2
  obtain ⟨basew, hdom24_raw, hmem24_raw⟩ := hrec_w.2.2 3 (by omega)
  have h24_eq : globN t "ev" + 8 * 3 = globN t "ev" + 24 := by omega
  rw [h24_eq] at hdom24_raw hmem24_raw
  have had24 : evw + (24#64 + 0) = BitVec.ofNat 64 (globN t "ev" + 24) := by
    apply BitVec.eq_of_toNat_eq
    have hz0 : (0 : BitVec 64).toNat = 0 := rfl
    have h24n : (24#64 : BitVec 64).toNat = 24 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hevw_nat, hz0, h24n, Nat.add_zero,
      Nat.mod_eq_of_lt (show 24 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show globN t "ev" + 24 < 2 ^ 64 by omega)]
  have hml24 : @memLoadHOLExact 64 _ .one (BitVec.ofNat 64 (globN t "ev" + 24))
      t.memaddrs (fun a => Classical.propDecidable (t.memaddrs a))
      t.memory t.structs = some (.val (.word basew)) := by
    unfold memLoadHOLExact; rw [if_pos hdom24_raw, hmem24_raw]
  have hwf0 : isWfShapeExactHOL t.structs .one = true := rfl
  have hload24' : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.load .one (.op .add [.var .global (ofString "ev"), .const 24#64])) =
      some (.val (.word basew)) := by
    simp only [evalHOLExact, evalListHOLExact, PanSemStateFiniteExact.toExact,
      hevw, hwf0, wordOpHOL, wordOp, valueIsWord, valueWord,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      had24, hml24]
  have hbasew_nat : basew.toNat = memW t (globN t "ev" + 24) := by
    unfold memW; rw [hmem24_raw]
  refine ⟨basew, hbasew_nat, ?_⟩
  have hlist_ev : @evalListHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]),
       .var .local (ofString nm)] =
      some [.val (.word basew), .val (.word sw)] := by
    have hs_ev : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        (.var .local (ofString nm)) = some (.val (.word sw)) := hsw
    simp only [evalListHOLExact, hload24', hs_ev]
  simp only [evalHOLExact, hlist_ev, wordOpHOL, wordOp,
    valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
  have hz : sw + (0 : BitVec 64) = sw := BitVec.add_zero _
  exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word (basew + w)))) hz

private theorem head_mem_cap_lt_g08 {F : Type} (t : PanSemStateFiniteExact 64 F) (hInv : EvmInv t) :
    memW t (globN t "ev" + 24) + memW t (globN t "ev" + 40) < 2 ^ 64 := by
  have hhead : (globN t "ev", globN t "cur_cont") ∈ evmChain t := by simp [evmChain, evmChainFrom]
  have hFW := hInv.2.choose_spec.2.2.2.2.1 _ hhead
  have hmem := hFW.2.1.2
  have hfp := hInv.1.2.2.2.2.1
  have hsp := hInv.1.2.2.2.2.2.1
  dsimp only at hmem
  rw [R11Shards.scratchEnd_val] at hsp
  omega

private def CopyEff_g08 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (prog : ProgHOL 64) (Rl : List Ivl) : Prop :=
  let out := evaluateHOLFiniteState s prog
  (out.1 = none → ByteRegionEffect s out.2 Rl) ∧
  (out.1 ≠ none → (∀ v, out.1 ≠ some (.returned v)) ∧ ¬ IsEvmErr out.1)

private theorem copyEff_error_g08 {F : Type} (s : PanSemStateFiniteExact 64 F) (Rl : List Ivl) :
    (some (.error : PanSemResultExact 64) = none → ByteRegionEffect s s Rl) ∧
    (some (.error : PanSemResultExact 64) ≠ none →
      (∀ v, some (.error : PanSemResultExact 64) ≠ some (.returned v)) ∧ ¬ IsEvmErr (some .error)) := by
  refine ⟨?_, ?_⟩
  · intro h; cases h
  · intro _
    refine ⟨?_, ?_⟩
    · intro v h; cases h
    · rintro ⟨_, h⟩; cases h

private theorem decCall_sat_copy_eff_g08 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nm : MlS) (arg : ExpHOL 64) (varg : ValueHOL 64) (cont : ProgHOL 64) (Rl : List Ivl)
    (hc : s.code = originalRuntimeCode)
    (hshape : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact varg) = true)
    (harg : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) arg = some varg)
    (hcont : ∀ mid : PanSemStateFiniteExact 64 F, LocFrame s mid →
      mid.locals = s.locals.update (nm, .val (.word (satValue_g08 varg))) →
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut → CopyEff_g08 mid cont Rl)
    (hnt : (evaluateHOLFiniteState s (.decCall nm .one (ofString "sat_word") [arg] cont)).1 ≠ some .timeOut) :
    CopyEff_g08 s (.decCall nm .one (ofString "sat_word") [arg] cont) Rl := by
  dsimp only [CopyEff_g08]
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [arg] = some [varg] := by
    rw [evalListHOLFinite_eq_toExact]; simp only [evalListHOLExact, harg]
  rw [hargs] at hnt ⊢
  dsimp only at hnt ⊢
  rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "sat_word") [varg] with _ | ⟨b, callee, rs⟩
  · exact copyEff_error_g08 s Rl
  · simp only [hl] at hnt ⊢
    have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "sat_word") [varg] = some (b, callee, rs) := by rwa [← hc]
    obtain ⟨rfl, rfl, v0, hvs, hcal⟩ := single_comb_arg_lookup_g08 lookup_sat_word_g08 hl_orig
    have hv0 : varg = v0 := by simpa using hvs
    subst v0
    by_cases hz : s.clock = 0
    · simp [hz] at hnt
    · rw [if_neg hz] at hnt ⊢
      obtain ⟨a, b, c, d, rfl⟩ := u256_value_of_shape_g08 hshape
      rw [sat_word_body_exact_g08 _ a b c d hcal] at hnt ⊢
      dsimp only at hnt ⊢
      have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word
          (if b ||| c ||| d = 0#64 then a else 18446744073709551615#64)))) .one = true := by simp [shapeOfHOLExact, shapeEqHOL]
      simp only [hsh, Bool.and_self, ↓reduceIte] at hnt ⊢
      let nw := satValue_g08 (.rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)])
      let mid := setVarHOLFinite nm (.val (.word nw))
        { (callEntryStateHOLFinite s callee).emptyLocalsHOLFinite with locals := s.locals }
      have hmid : LocFrame s mid := rfl
      have hml : mid.locals = s.locals.update (nm, .val (.word nw)) := rfl
      change (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut at hnt
      rcases hr : evaluateHOLFiniteState mid cont with ⟨r, post⟩
      rw [hr] at hnt
      have hnt_mid : (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut := by rw [hr]; exact hnt
      have hh := hcont mid hmid hml hnt_mid
      dsimp only [CopyEff_g08] at hh
      rw [hr] at hh
      change ((evaluateHOLFiniteState mid cont).1 = none → ByteRegionEffect s
        { (evaluateHOLFiniteState mid cont).2 with locals := (evaluateHOLFiniteState mid cont).2.locals.resVarEq (nm, s.locals.lookup nm) } Rl) ∧
        ((evaluateHOLFiniteState mid cont).1 ≠ none → (∀ v, (evaluateHOLFiniteState mid cont).1 ≠ some (.returned v)) ∧ ¬ IsEvmErr (evaluateHOLFiniteState mid cont).1)
      rw [hr]
      change (r = none → ByteRegionEffect s { post with locals := post.locals.resVarEq (nm, s.locals.lookup nm) } Rl) ∧
        (r ≠ none → (∀ v, r ≠ some (.returned v)) ∧ ¬ IsEvmErr r)
      refine ⟨fun hn => ?_, hh.2⟩
      exact (((ByteRegionEffect.refl s Rl).with_locals_clock mid.locals mid.clock).trans
        (hh.1 hn)).with_locals_clock _ _

private theorem copy_buffer_write_eff_g08 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (stVal dsVal szVal : ValueHOL 64) (buf buflen : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hInv : EvmInv s)
    (hst_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true)
    (hds_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact dsVal) = true)
    (hst : s.locals.lookup (ofString "mstart") = some stVal)
    (hds : s.locals.lookup (ofString "dstart") = some dsVal)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word (satValue_g08 szVal))))
    (hbuf : s.locals.lookup (ofString "buf") = some (.val (.word buf)))
    (hbl : s.locals.lookup (ofString "buf_len") = some (.val (.word buflen)))
    (hnz : satValue_g08 szVal ≠ 0#64)
    (hcov : (satValue_g08 stVal).toNat + (satValue_g08 szVal).toNat ≤ memW s (globN s "ev" + 32))
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString "ms") .one (ofString "sat_word") [.var .local (ofString "mstart")]
        (.decCall (ofString "ds") .one (ofString "sat_word") [.var .local (ofString "dstart")]
          (.call (some (none, none)) (ofString "buffer_read")
            [.var .local (ofString "buf"), .var .local (ofString "buf_len"),
             .var .local (ofString "ds"), .var .local (ofString "n"),
             .op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]),
               .var .local (ofString "ms")]])))).1 ≠ some .timeOut) :
    CopyEff_g08 s
      (.decCall (ofString "ms") .one (ofString "sat_word") [.var .local (ofString "mstart")]
        (.decCall (ofString "ds") .one (ofString "sat_word") [.var .local (ofString "dstart")]
          (.call (some (none, none)) (ofString "buffer_read")
            [.var .local (ofString "buf"), .var .local (ofString "buf_len"),
             .var .local (ofString "ds"), .var .local (ofString "n"),
             .op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]),
               .var .local (ofString "ms")]])))
      [(memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))] := by
  refine decCall_sat_copy_eff_g08 s _ _ stVal _ _ hc hst_sh hst ?_ hnt
  intro mid1 hlf1 hl1 hnt1
  have hds1 : mid1.locals.lookup (ofString "dstart") = some dsVal := by
    simp [hl1, HolFiniteMapExact.lookup_update, FUPDATE, hds,
      show ofString "ms" ≠ ofString "dstart" by decide]
  have hc1 : mid1.code = originalRuntimeCode := by rw [hlf1]; exact hc
  refine decCall_sat_copy_eff_g08 mid1 _ _ dsVal _ _ hc1 hds_sh hds1 ?_ hnt1
  intro mid2 hlf2 hl2 hnt2
  have hInv2 : EvmInv mid2 := by
    rw [hlf2, hlf1]
    exact localsFree_evmInv s _ _ hInv
  have hc2 : mid2.code = originalRuntimeCode := by rw [hlf2, hlf1]; exact hc
  have hma2 : mid2.memaddrs = ordinaryDomain := hInv2.1.1.memaddrs
  have hms2 : mid2.locals.lookup (ofString "ms") = some (.val (.word (satValue_g08 stVal))) := by
    simp [hl2, hl1, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "ds" ≠ ofString "ms" by decide]
  have hds2 : mid2.locals.lookup (ofString "ds") = some (.val (.word (satValue_g08 dsVal))) := by
    simp [hl2, HolFiniteMapExact.lookup_update, FUPDATE]
  have hn2 : mid2.locals.lookup (ofString "n") = some (.val (.word (satValue_g08 szVal))) := by
    simp [hl2, hl1, HolFiniteMapExact.lookup_update, FUPDATE, hn,
      show ofString "ds" ≠ ofString "n" by decide, show ofString "ms" ≠ ofString "n" by decide]
  have hbuf2 : mid2.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
    simp [hl2, hl1, HolFiniteMapExact.lookup_update, FUPDATE, hbuf,
      show ofString "ds" ≠ ofString "buf" by decide, show ofString "ms" ≠ ofString "buf" by decide]
  have hbl2 : mid2.locals.lookup (ofString "buf_len") = some (.val (.word buflen)) := by
    simp [hl2, hl1, HolFiniteMapExact.lookup_update, FUPDATE, hbl,
      show ofString "ds" ≠ ofString "buf_len" by decide, show ofString "ms" ≠ ofString "buf_len" by decide]
  have hmem : ∀ off : Nat, memW mid2 (globN mid2 "ev" + off) = memW s (globN s "ev" + off) := by
    intro off; rw [hlf2, hlf1]; rfl
  have hcov2 : (satValue_g08 stVal).toNat + (satValue_g08 szVal).toNat ≤ memW mid2 (globN mid2 "ev" + 32) := by
    rw [hmem]; exact hcov
  have hnpos : 0 < (satValue_g08 szVal).toNat := by
    have hne : (satValue_g08 szVal).toNat ≠ 0 := by
      intro h; apply hnz; exact BitVec.eq_of_toNat_eq h
    omega
  obtain ⟨base, hbase, hout⟩ := eval_head_mem_plus_local_g08 mid2 hInv2 "ms" (satValue_g08 stVal) hms2
  have hbounds := head_mem_store_address_g08 mid2 hInv2 base (satValue_g08 stVal)
    (satValue_g08 szVal).toNat hbase hnpos hcov2
  have hcap := head_mem_cap_lt_g08 mid2 hInv2
  have hh := eval_call_buffer_read_bre mid2
    (.var .local (ofString "buf")) (.var .local (ofString "buf_len"))
    (.var .local (ofString "ds")) (.var .local (ofString "n"))
    (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "ms")])
    buf buflen (satValue_g08 dsVal) (satValue_g08 szVal) (base + satValue_g08 stVal)
    [(memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))]
    hc2 hma2 hbuf2 hbl2 hds2 hn2 hout (by omega)
    (fun _ => ⟨_, List.mem_singleton.mpr rfl, by rw [← hmem 24]; exact hbounds.2.1,
      by rw [← hmem 24, ← hmem 40]; exact hbounds.2.2⟩) hnt2
  exact ⟨fun h => (hh.1 h).1, hh.2⟩

private def CopyLocals_g08 (args : List (MlS × ValueHOL 64))
    (l : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  ∀ kv ∈ args, l.lookup kv.1 = some kv.2

private theorem copyLocals_get_g08 {args : List (MlS × ValueHOL 64)}
    {l : HolFiniteMapExact MlS (ValueHOL 64)} {nm : MlS} {v : ValueHOL 64}
    (hK : CopyLocals_g08 args l) (hmem : (nm, v) ∈ args) : l.lookup nm = some v :=
  hK (nm, v) hmem

private theorem copyLocals_update_g08 (args : List (MlS × ValueHOL 64))
    (l : HolFiniteMapExact MlS (ValueHOL 64)) (nm : MlS) (v : ValueHOL 64)
    (hne : ∀ kv ∈ args, nm ≠ kv.1) (hK : CopyLocals_g08 args l) :
    CopyLocals_g08 args (l.update (nm, v)) := by
  intro kv hkv
  simp [HolFiniteMapExact.lookup_update, FUPDATE, hne kv hkv, Ne.symm (hne kv hkv), hK kv hkv]

private theorem copyLocals_cons_update_g08 (args : List (MlS × ValueHOL 64))
    (l : HolFiniteMapExact MlS (ValueHOL 64)) (nm : MlS) (v : ValueHOL 64)
    (hne : ∀ kv ∈ args, nm ≠ kv.1) (hK : CopyLocals_g08 args l) :
    CopyLocals_g08 ((nm, v) :: args) (l.update (nm, v)) := by
  intro kv hkv
  rcases List.mem_cons.mp hkv with rfl | hkv
  · simp [HolFiniteMapExact.lookup_update, FUPDATE]
  · exact copyLocals_update_g08 args l nm v hne hK kv hkv

private def copyBufferArgs_g08 (stVal dsVal szVal : ValueHOL 64) (buf buflen : BitVec 64) :
    List (MlS × ValueHOL 64) :=
  [(ofString "n", .val (.word (satValue_g08 szVal))),
   (ofString "size", szVal), (ofString "dstart", dsVal), (ofString "mstart", stVal),
   (ofString "base", .val (.word 3#64)), (ofString "buf", .val (.word buf)),
   (ofString "buf_len", .val (.word buflen))]

private def copyBufferWriteProg_g08 : ProgHOL 64 :=
  .decCall (ofString "ms") .one (ofString "sat_word") [.var .local (ofString "mstart")]
    (.decCall (ofString "ds") .one (ofString "sat_word") [.var .local (ofString "dstart")]
      (.call (some (none, none)) (ofString "buffer_read")
        [.var .local (ofString "buf"), .var .local (ofString "buf_len"),
         .var .local (ofString "ds"), .var .local (ofString "n"),
         .op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]),
           .var .local (ofString "ms")]]))

private def copyFinishProg_g08 : ProgHOL 64 :=
  .seq (.call (some (none, none)) (ofString "pc_add") [.const 1#64]) (.return (.const 0#64))

private def copyBufferTailProg_g08 : ProgHOL 64 :=
  .seq (.ite (.cmp .notEqual (.var .local (ofString "n")) (.const 0#64)) copyBufferWriteProg_g08 .skip)
    copyFinishProg_g08

private theorem copy_buffer_tail_run_g08 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (stVal dsVal szVal : ValueHOL 64) (buf buflen : BitVec 64)
    (hst_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true)
    (hds_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact dsVal) = true) :
    HandlerRun s0 (fun t => CopyLocals_g08 (copyBufferArgs_g08 stVal dsVal szVal buf buflen) t.locals ∧
      (satValue_g08 szVal ≠ 0#64 →
        (satValue_g08 stVal).toNat + (satValue_g08 szVal).toNat ≤ memW t (globN t "ev" + 32))) true
      copyBufferTailProg_g08 := by
  have hfinish : HandlerRun s0 (fun _ => True) true copyFinishProg_g08 :=
    HandlerRun.seq_call_simple eps_pc_add (HandlerRun.ret _)
  refine HandlerRun.seq_ite_copy_g08 ?_ ?_
  · refine HandlerRun.seq_head_mem_eff_g08 ?_ hfinish
    intro t hc hInv ⟨⟨hK, hcov⟩, w, hw, hwne⟩ hnt
    have hn := hK (ofString "n", .val (.word (satValue_g08 szVal))) (by simp [copyBufferArgs_g08])
    have hnz : satValue_g08 szVal ≠ 0#64 := by
      intro hz
      have hev : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.cmp .notEqual (.var .local (ofString "n")) (.const 0#64)) = some (.val (.word 0#64)) := by
        simp [evalHOLExact, hn, hz, Compiler.Encoders.Asm.wordCmpHOL]
      rw [hev] at hw
      have hw0 : w = 0#64 := by simpa using hw.symm
      exact hwne hw0
    exact copy_buffer_write_eff_g08 t stVal dsVal szVal buf buflen hc hInv hst_sh hds_sh
      (copyLocals_get_g08 hK (by simp [copyBufferArgs_g08])) (copyLocals_get_g08 hK (by simp [copyBufferArgs_g08])) hn
      (copyLocals_get_g08 hK (by simp [copyBufferArgs_g08])) (copyLocals_get_g08 hK (by simp [copyBufferArgs_g08])) hnz (hcov hnz) hnt
  · exact HandlerRun.seq_skip (HandlerRun.weaken (fun _ _ _ => trivial) hfinish)

private def copyBufferCostProg_g08 : ProgHOL 64 :=
  .decCall (ofString "x") (.comb [.one, .one]) (ofString "extend_memory_cost1")
    [.var .local (ofString "mstart"), .var .local (ofString "size")]
    (.decCall (ofString "cost") .one (ofString "add_sat")
      [.op .add [.var .local (ofString "base"), .panop .mul [.const 3#64, .var .local (ofString "w")]],
       .rfield 0 (.var .local (ofString "x"))]
      (.seq (.call (some (none, none)) (ofString "charge_gas") [.var .local (ofString "cost")])
        (.seq (.call (some (none, none)) (ofString "extend_memory") [.rfield 1 (.var .local (ofString "x"))])
          copyBufferTailProg_g08)))

private def copyBufferNumsProg_g08 : ProgHOL 64 :=
  .decCall (ofString "n") .one (ofString "sat_word") [.var .local (ofString "size")]
    (.decCall (ofString "w") .one (ofString "words_of") [.var .local (ofString "n")] copyBufferCostProg_g08)

private theorem copy_buffer_after_pops_run_g08 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (stVal dsVal szVal : ValueHOL 64) (buf buflen : BitVec 64)
    (hst_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true)
    (hds_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact dsVal) = true)
    (hsz_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact szVal) = true) :
    HandlerRun s0 (fun t => HeadMemAligned t ∧
      CopyLocals_g08 (copyBufferArgs_g08 stVal dsVal szVal buf buflen).tail t.locals) false
      copyBufferNumsProg_g08 := by
  have hcost : ∀ ww : BitVec 64, ww.toNat < 2 ^ 59 →
      HandlerRun s0 (fun t => HeadMemAligned t ∧ CopyLocals_g08
        ((ofString "w", .val (.word ww)) :: copyBufferArgs_g08 stVal dsVal szVal buf buflen) t.locals) false
        copyBufferCostProg_g08 := by
    intro ww hwb
    let args := (ofString "w", ValueHOL.val (.word ww)) :: copyBufferArgs_g08 stVal dsVal szVal buf buflen
    refine copy_cost_phase_run_g08 s0 stVal szVal hst_sh hsz_sh (CopyLocals_g08 args)
      (.var .local (ofString "base"))
      (fun t hK => copyLocals_get_g08 hK (by simp [args, copyBufferArgs_g08]))
      ?_ ?_
      (fun l hK => copyLocals_get_g08 hK (by simp [args, copyBufferArgs_g08]))
      (fun l hK => copyLocals_get_g08 hK (by simp [args, copyBufferArgs_g08]))
      (fun l hK => ⟨ww, copyLocals_get_g08 hK (by simp [args]), hwb⟩)
      ?_
    · intro l v hK
      apply copyLocals_update_g08 args l _ v _ hK
      intro kv hk
      simp only [args, copyBufferArgs_g08, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
    · intro l v hK
      apply copyLocals_update_g08 args l _ v _ hK
      intro kv hk
      simp only [args, copyBufferArgs_g08, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
    · refine copy_extend_phase_run_g08 s0 stVal szVal (CopyLocals_g08 args) ?_
      refine HandlerRun.weaken ?_ (copy_buffer_tail_run_g08 s0 stVal dsVal szVal buf buflen hst_sh hds_sh)
      intro t _ ⟨hK, hcov⟩
      exact ⟨fun kv hk => hK kv (List.mem_cons_of_mem _ hk), hcov⟩
  refine HandlerRun.decCall_sat_copy_g08 szVal hsz_sh
    (fun t ⟨_, hK⟩ => copyLocals_get_g08 hK (by simp [copyBufferArgs_g08]))
    (Q := fun t => HeadMemAligned t ∧ CopyLocals_g08 (copyBufferArgs_g08 stVal dsVal szVal buf buflen) t.locals)
    ?_ ?_
  · intro t cpost ⟨hHM, hK⟩ hlf
    have hHM_cp : HeadMemAligned cpost := headMemAligned_congr_head_only
      (by rw [hlf]) (fun off _ => by unfold memW; rw [hlf]) hHM
    refine ⟨headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp, ?_⟩
    change CopyLocals_g08
      ((ofString "n", .val (.word (satValue_g08 szVal))) :: (copyBufferArgs_g08 stVal dsVal szVal buf buflen).tail)
      (t.locals.update (ofString "n", .val (.word (satValue_g08 szVal))))
    apply copyLocals_cons_update_g08 _ _ _ _ _ hK
    intro kv hk
    simp only [copyBufferArgs_g08, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
  · refine HandlerRun.decCall
      (Q := fun t => HeadMemAligned t ∧ ∃ ww : BitVec 64, ww.toNat < 2 ^ 59 ∧
        CopyLocals_g08 ((ofString "w", .val (.word ww)) :: copyBufferArgs_g08 stVal dsVal szVal buf buflen) t.locals)
      eps_words_of_lt (fun _ _ _ _ _ _ _ _ _ _ => trivial) ?_ ?_
    · intro t _ _ callee _ v cpost _ ⟨hHM, hK⟩ _ _ _ _ hQc
      obtain ⟨hlf, ww, hv, hwb⟩ := hQc
      subst v
      have hHM_ce : HeadMemAligned (callEntryStateHOLFinite t callee) :=
        headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      have hHM_cp : HeadMemAligned cpost := headMemAligned_congr_head_only
        (by rw [hlf]) (fun off _ => by unfold memW; rw [hlf]) hHM_ce
      refine ⟨headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp, ww, hwb, ?_⟩
      apply copyLocals_cons_update_g08 _ _ _ _ _ hK
      intro kv hk
      simp only [copyBufferArgs_g08, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
    · intro t hc hInv hlen hR ⟨hHM, ww, hwb, hK⟩ hnt
      exact hcost ww hwb t hc hInv hlen hR ⟨hHM, hK⟩ hnt

private def copyBufferEntryArgs_g08 (buf buflen : BitVec 64) : List (MlS × ValueHOL 64) :=
  [(ofString "base", .val (.word 3#64)), (ofString "buf", .val (.word buf)),
   (ofString "buf_len", .val (.word buflen))]

private theorem copy_from_buffer_body_run_aligned {F : Type} (s0 : PanSemStateFiniteExact 64 F) :
    HandlerRun s0 (fun t => HeadMemAligned t ∧ ∃ buf buflen : BitVec 64,
      CopyLocals_g08 (copyBufferEntryArgs_g08 buf buflen) t.locals) false
      (sourceFnBody Guest.Software.guestFn_copy_from_buffer) := by
  intro t0 hc0 hInv0 hlen0 hR0 ⟨hHM0, buf, buflen, hK0⟩ hnt0
  have hbody : HandlerRun s0 (fun t => HeadMemAligned t ∧
      CopyLocals_g08 (copyBufferEntryArgs_g08 buf buflen) t.locals) false
      (sourceFnBody Guest.Software.guestFn_copy_from_buffer) := by
    dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_copy_from_buffer,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
      Option.map, List.map]
    refine HandlerRun.decCall_stack_copy_g08 (CopyLocals_g08 (copyBufferEntryArgs_g08 buf buflen))
      (fun l => ∃ stVal, shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true ∧
        CopyLocals_g08 ((ofString "mstart", stVal) :: copyBufferEntryArgs_g08 buf buflen) l) ?_ ?_
    · intro l v hK hsh
      refine ⟨v, hsh, copyLocals_cons_update_g08 _ _ _ _ ?_ hK⟩
      intro kv hk
      simp only [copyBufferEntryArgs_g08, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> dsimp only <;> decide
    · refine HandlerRun.decCall_stack_copy_g08
        (fun l => ∃ stVal, shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true ∧
          CopyLocals_g08 ((ofString "mstart", stVal) :: copyBufferEntryArgs_g08 buf buflen) l)
        (fun l => ∃ stVal dsVal,
          shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true ∧
          shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact dsVal) = true ∧
          CopyLocals_g08 ((ofString "dstart", dsVal) :: (ofString "mstart", stVal) :: copyBufferEntryArgs_g08 buf buflen) l) ?_ ?_
      · intro l v ⟨stVal, hst, hK⟩ hsh
        refine ⟨stVal, v, hst, hsh, copyLocals_cons_update_g08 _ _ _ _ ?_ hK⟩
        intro kv hk
        simp only [copyBufferEntryArgs_g08, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl <;> dsimp only <;> decide
      · refine HandlerRun.decCall_stack_copy_g08
          (fun l => ∃ stVal dsVal,
            shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true ∧
            shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact dsVal) = true ∧
            CopyLocals_g08 ((ofString "dstart", dsVal) :: (ofString "mstart", stVal) :: copyBufferEntryArgs_g08 buf buflen) l)
          (fun l => ∃ stVal dsVal szVal,
            shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true ∧
            shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact dsVal) = true ∧
            shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact szVal) = true ∧
            CopyLocals_g08 ((ofString "size", szVal) :: (ofString "dstart", dsVal) ::
              (ofString "mstart", stVal) :: copyBufferEntryArgs_g08 buf buflen) l) ?_ ?_
        · intro l v ⟨stVal, dsVal, hst, hds, hK⟩ hsh
          refine ⟨stVal, dsVal, v, hst, hds, hsh, copyLocals_cons_update_g08 _ _ _ _ ?_ hK⟩
          intro kv hk
          simp only [copyBufferEntryArgs_g08, List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
        · intro t hc hInv hlen hR ⟨hHM, stVal, dsVal, szVal, hst, hds, hsz, hK⟩ hnt
          exact copy_buffer_after_pops_run_g08 s0 stVal dsVal szVal buf buflen hst hds hsz
            t hc hInv hlen hR ⟨hHM, hK⟩ hnt
  exact hbody t0 hc0 hInv0 hlen0 hR0 ⟨hHM0, hK0⟩ hnt0

private theorem lookup_copy_from_buffer_g08 :
    originalRuntimeCode.lookup (ofString "copy_from_buffer") =
      some ([(ofString "base", .one), (ofString "buf", .one), (ofString "buf_len", .one)],
        sourceFnBody Guest.Software.guestFn_copy_from_buffer, .one) :=
  lookup_of_guestAst_getElem 538 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_copy_from_buffer) rfl

private theorem copy_from_buffer_args_lookup_g08 {vals : List (ValueHOL 64)} {body' : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret' : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "copy_from_buffer") vals =
      some (body', callee, ret')) :
    ∃ bw buf buflen : BitVec 64,
      vals = [.val (.word bw), .val (.word buf), .val (.word buflen)] ∧
      callee.lookup (ofString "base") = some (.val (.word bw)) ∧
      callee.lookup (ofString "buf") = some (.val (.word buf)) ∧
      callee.lookup (ofString "buf_len") = some (.val (.word buflen)) := by
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
    originalRuntimeCode.lookup (ofString "copy_from_buffer") vals body' callee ret' hl
  simp only [Flapjack.lookupCodeHOLExact, lookup_copy_from_buffer_g08] at hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩
  · simp at hx
  · simp at hx
  · simp at hx
  · split at hx
    · rename_i hcond
      have heq := Option.some.inj hx
      rcases Prod.mk.inj heq with ⟨_, hrest⟩
      rcases Prod.mk.inj hrest with ⟨hloc, _⟩
      have hs := hcond.2.2
      simp only [List.map, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
        List.zip_cons_cons, List.zip_nil_left] at hs
      rcases hs with ⟨hsh1, hsh2, hsh3⟩
      rcases v1 with ⟨⟨bw⟩⟩ | _ | _
      · rcases v2 with ⟨⟨buf⟩⟩ | _ | _
        · rcases v3 with ⟨⟨buflen⟩⟩ | _ | _
          · refine ⟨bw, buf, buflen, rfl, ?_, ?_, ?_⟩
            · have hh := congrFun hloc.symm (ofString "base")
              simpa [FUPDATE_LIST, FUPDATE,
                show ofString "base" ≠ ofString "buf" by decide,
                show ofString "base" ≠ ofString "buf_len" by decide] using hh
            · have hh := congrFun hloc.symm (ofString "buf")
              simpa [FUPDATE_LIST, FUPDATE, show ofString "buf" ≠ ofString "buf_len" by decide] using hh
            · have hh := congrFun hloc.symm (ofString "buf_len")
              simpa [FUPDATE_LIST, FUPDATE] using hh
          · simp [shapeOfHOLExact, shapeEqHOL] at hsh3
          · simp [shapeOfHOLExact, shapeEqHOL] at hsh3
        · simp [shapeOfHOLExact, shapeEqHOL] at hsh2
        · simp [shapeOfHOLExact, shapeEqHOL] at hsh2
      · simp [shapeOfHOLExact, shapeEqHOL] at hsh1
      · simp [shapeOfHOLExact, shapeEqHOL] at hsh1
    · cases hx
  · simp at hx

private theorem evalList_const_first_g08 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (tail : List (ExpHOL 64)) (w bw : BitVec 64) (vals : List (ValueHOL 64))
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) (.const w :: tail) =
      some (.val (.word bw) :: vals)) : bw = w := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact, evalHOLExact] at hargs
  rcases ht : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) tail with _ | vs
  · simp [ht] at hargs
  · rw [ht] at hargs
    simpa using (List.cons.inj (Option.some.inj hargs)).1.symm

private theorem copy_from_buffer_call_return_run_g08 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (tail : List (ExpHOL 64)) :
    HandlerRun s0 HeadMemAligned false
      (.seq (.call (some (none, none)) (ofString "copy_from_buffer") (.const 3#64 :: tail))
        (.return (.const 0#64))) := by
  refine seq_call_return_g08 lookup_copy_from_buffer_g08 ?_ (copy_from_buffer_body_run_aligned s0)
  intro t values callee hc hInv hHM hargs hl
  obtain ⟨bw, buf, buflen, rfl, hb, hbuf, hbl⟩ := copy_from_buffer_args_lookup_g08 hl
  have heq := evalList_const_first_g08 t tail 3#64 bw _ hargs
  subst bw
  refine ⟨headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM, buf, buflen, ?_⟩
  intro kv hk
  simp only [copyBufferEntryArgs_g08, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact hb
  · exact hbuf
  · exact hbl

private theorem lookup_op_calldatacopy_g08 :
    originalRuntimeCode.lookup (ofString "op_calldatacopy") =
      some ([], sourceFnBody Guest.Software.guestFn_op_calldatacopy, .one) :=
  lookup_of_guestAst_getElem 539 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_op_calldatacopy) rfl

private theorem lookup_op_codecopy_g08 :
    originalRuntimeCode.lookup (ofString "op_codecopy") =
      some ([], sourceFnBody Guest.Software.guestFn_op_codecopy, .one) :=
  lookup_of_guestAst_getElem 541 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_op_codecopy) rfl

theorem op_codecopy_aligned_spec :
    FunSpec (fun s => EvmRun s ∧ HeadMemAligned s) OpDispatchPost (ofString "op_codecopy") := by
  refine ⟨_, _, _, lookup_op_codecopy_g08, ?_⟩
  intro F s0 hcode ⟨hRun, hHM⟩ _ hnt
  exact copy_from_buffer_call_return_run_g08 s0 _ s0 hcode hRun.1 rfl (le_refl _) hHM hnt

theorem op_calldatacopy_aligned_spec :
    FunSpec (fun s => EvmRun s ∧ HeadMemAligned s) OpDispatchPost (ofString "op_calldatacopy") := by
  refine ⟨_, _, _, lookup_op_calldatacopy_g08, ?_⟩
  intro F s0 hcode ⟨hRun, hHM⟩ _ hnt
  have hrun : HandlerRun s0 HeadMemAligned false (sourceFnBody Guest.Software.guestFn_op_calldatacopy) :=
    HandlerRun.dec (Q := HeadMemAligned)
      (fun _ _ _ _ h => headMemAligned_congr_head_only rfl (fun _ _ => rfl) h)
      (copy_from_buffer_call_return_run_g08 s0 _)
  exact hrun s0 hcode hRun.1 rfl (le_refl _) hHM hnt

private theorem eval_ret_mem_plus_local_g08 {F : Type}
    (t : PanSemStateFiniteExact 64 F) (hInv : EvmInv t)
    (nm : String) (sw : BitVec 64)
    (hsw : t.locals.lookup (ofString nm) = some (.val (.word sw))) :
    ∃ basew : BitVec 64,
      basew.toNat = memW t (globN t "ev" + 144) ∧
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        (.op .add
          [.load .one (.op .add [.var .global (ofString "ev"), .const 144#64]),
           .var .local (ofString nm)]) =
        some (.val (.word (basew + sw))) := by
  have hhead : (globN t "ev", globN t "cur_cont") ∈ evmChain t := by
    simp [evmChain, evmChainFrom]
  have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead
  have hb_ev := (frameWF_bounds hInv.1.2 hFW0).1
  dsimp only at hb_ev
  have hev_pos : 0 < globN t "ev" := by
    obtain ⟨hin, _⟩ := (hFW0.1 (globN t "ev", 280) (by simp)).1
    have h1 := hInv.1.2.2.2.1; have h2 := hInv.1.2.2.2.2.1
    rw [R11Shards.scratchStart_val] at h1; dsimp only at hin; omega
  obtain ⟨evw, hevw, hevw_nat⟩ := global_word_of_pos t "ev" hev_pos
  have hrec_w := (hFW0.1 (globN t "ev", 280) (by simp)).2
  obtain ⟨basew, hdom144_raw, hmem144_raw⟩ := hrec_w.2.2 18 (by omega)
  have h144_eq : globN t "ev" + 8 * 18 = globN t "ev" + 144 := by omega
  rw [h144_eq] at hdom144_raw hmem144_raw
  have had144 : evw + (144#64 + 0) = BitVec.ofNat 64 (globN t "ev" + 144) := by
    apply BitVec.eq_of_toNat_eq
    have hz0 : (0 : BitVec 64).toNat = 0 := rfl
    have h144n : (144#64 : BitVec 64).toNat = 144 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hevw_nat, hz0, h144n, Nat.add_zero,
      Nat.mod_eq_of_lt (show 144 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show globN t "ev" + 144 < 2 ^ 64 by omega)]
  have hml144 : @memLoadHOLExact 64 _ .one (BitVec.ofNat 64 (globN t "ev" + 144))
      t.memaddrs (fun a => Classical.propDecidable (t.memaddrs a))
      t.memory t.structs = some (.val (.word basew)) := by
    unfold memLoadHOLExact; rw [if_pos hdom144_raw, hmem144_raw]
  have hwf0 : isWfShapeExactHOL t.structs .one = true := rfl
  have hload144' : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.load .one (.op .add [.var .global (ofString "ev"), .const 144#64])) =
      some (.val (.word basew)) := by
    simp only [evalHOLExact, evalListHOLExact, PanSemStateFiniteExact.toExact,
      hevw, hwf0, wordOpHOL, wordOp, valueIsWord, valueWord,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      had144, hml144]
  have hbasew_nat : basew.toNat = memW t (globN t "ev" + 144) := by
    unfold memW; rw [hmem144_raw]
  refine ⟨basew, hbasew_nat, ?_⟩
  have hlist_ev : @evalListHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      [.load .one (.op .add [.var .global (ofString "ev"), .const 144#64]),
       .var .local (ofString nm)] =
      some [.val (.word basew), .val (.word sw)] := by
    have hs_ev : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        (.var .local (ofString nm)) = some (.val (.word sw)) := hsw
    simp only [evalListHOLExact, hload144', hs_ev]
  simp only [evalHOLExact, hlist_ev, wordOpHOL, wordOp,
    valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
  have hz : sw + (0 : BitVec 64) = sw := BitVec.add_zero _
  exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word (basew + w)))) hz

private theorem copy_returndata_write_eff_g08 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (stVal szVal : ValueHOL 64) (rsw : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hInv : EvmInv s)
    (hst_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true)
    (hst : s.locals.lookup (ofString "mstart") = some stVal)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word (satValue_g08 szVal))))
    (hrs : s.locals.lookup (ofString "rs") = some (.val (.word rsw)))
    (hnz : satValue_g08 szVal ≠ 0#64)
    (hcov : (satValue_g08 stVal).toNat + (satValue_g08 szVal).toNat ≤ memW s (globN s "ev" + 32))
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString "ms") .one (ofString "sat_word") [.var .local (ofString "mstart")]
        (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "ms")],
           .op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 144#64]), .var .local (ofString "rs")],
           .var .local (ofString "n")]))).1 ≠ some .timeOut) :
    CopyEff_g08 s
      (.decCall (ofString "ms") .one (ofString "sat_word") [.var .local (ofString "mstart")]
        (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "ms")],
           .op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 144#64]), .var .local (ofString "rs")],
           .var .local (ofString "n")]))
      [(memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))] := by
  refine decCall_sat_copy_eff_g08 s _ _ stVal _ _ hc hst_sh hst ?_ hnt
  intro mid hlf hl hnt_mid
  have hInv_mid : EvmInv mid := by rw [hlf]; exact localsFree_evmInv s _ _ hInv
  have hc_mid : mid.code = originalRuntimeCode := by rw [hlf]; exact hc
  have hms : mid.locals.lookup (ofString "ms") = some (.val (.word (satValue_g08 stVal))) := by
    simp [hl, HolFiniteMapExact.lookup_update, FUPDATE]
  have hn_mid : mid.locals.lookup (ofString "n") = some (.val (.word (satValue_g08 szVal))) := by
    simp [hl, HolFiniteMapExact.lookup_update, FUPDATE, hn, show ofString "ms" ≠ ofString "n" by decide]
  have hrs_mid : mid.locals.lookup (ofString "rs") = some (.val (.word rsw)) := by
    simp [hl, HolFiniteMapExact.lookup_update, FUPDATE, hrs, show ofString "ms" ≠ ofString "rs" by decide]
  have hmem : ∀ off : Nat, memW mid (globN mid "ev" + off) = memW s (globN s "ev" + off) := by
    intro off; rw [hlf]; rfl
  have hcov_mid : (satValue_g08 stVal).toNat + (satValue_g08 szVal).toNat ≤ memW mid (globN mid "ev" + 32) := by
    rw [hmem]; exact hcov
  have hnpos : 0 < (satValue_g08 szVal).toNat := by
    have hne : (satValue_g08 szVal).toNat ≠ 0 := by
      intro h; apply hnz; exact BitVec.eq_of_toNat_eq h
    omega
  obtain ⟨base, hbase, hout⟩ := eval_head_mem_plus_local_g08 mid hInv_mid "ms" (satValue_g08 stVal) hms
  obtain ⟨srcbase, _, hsrc⟩ := eval_ret_mem_plus_local_g08 mid hInv_mid "rs" rsw hrs_mid
  have hbounds := head_mem_store_address_g08 mid hInv_mid base (satValue_g08 stVal)
    (satValue_g08 szVal).toNat hbase hnpos hcov_mid
  have hh := M11.eval_call_memcpy_bre mid
    (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "ms")])
    (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 144#64]), .var .local (ofString "rs")])
    (.var .local (ofString "n")) (base + satValue_g08 stVal) (srcbase + rsw) (satValue_g08 szVal)
    [(memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))]
    hc_mid hInv_mid.1.1.memaddrs hout hsrc hn_mid
    (fun _ => ⟨_, List.mem_singleton.mpr rfl, by rw [← hmem 24]; exact hbounds.2.1,
      by rw [← hmem 24, ← hmem 40]; exact hbounds.2.2⟩) hnt_mid
  refine ⟨fun h => bre_of_m11 (hh.1 h).1, ?_⟩
  intro hne
  have hnr := hh.2 hne
  exact ⟨fun v hv => hnr (Or.inl ⟨v, hv⟩), fun ⟨ev, he⟩ => hnr (Or.inr ⟨ofString "EvmErr", ev, he, by decide⟩)⟩

private def copyRetArgs_g08 (stVal rsVal szVal : ValueHOL 64) : List (MlS × ValueHOL 64) :=
  [(ofString "n", .val (.word (satValue_g08 szVal))), (ofString "size", szVal),
   (ofString "rstart", rsVal), (ofString "mstart", stVal)]

private def copyRetWriteProg_g08 : ProgHOL 64 :=
  .decCall (ofString "ms") .one (ofString "sat_word") [.var .local (ofString "mstart")]
    (.call (some (none, none)) (ofString "memcpy")
      [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "ms")],
       .op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 144#64]), .var .local (ofString "rs")],
       .var .local (ofString "n")])

private def copyRetTailProg_g08 : ProgHOL 64 :=
  .seq (.ite (.cmp .notEqual (.var .local (ofString "n")) (.const 0#64)) copyRetWriteProg_g08 .skip)
    copyFinishProg_g08

private theorem copy_ret_tail_run_g08 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (stVal rsVal szVal : ValueHOL 64)
    (hst_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true) :
    HandlerRun s0 (fun t => CopyLocals_g08
      ((ofString "rs", .val (.word (satValue_g08 rsVal))) :: copyRetArgs_g08 stVal rsVal szVal) t.locals ∧
      (satValue_g08 szVal ≠ 0#64 →
        (satValue_g08 stVal).toNat + (satValue_g08 szVal).toNat ≤ memW t (globN t "ev" + 32))) true
      copyRetTailProg_g08 := by
  have hfinish : HandlerRun s0 (fun _ => True) true copyFinishProg_g08 :=
    HandlerRun.seq_call_simple eps_pc_add (HandlerRun.ret _)
  refine HandlerRun.seq_ite_copy_g08 ?_ ?_
  · refine HandlerRun.seq_head_mem_eff_g08 ?_ hfinish
    intro t hc hInv ⟨⟨hK, hcov⟩, w, hw, hwne⟩ hnt
    have hn : t.locals.lookup (ofString "n") = some (.val (.word (satValue_g08 szVal))) :=
      copyLocals_get_g08 hK (by simp [copyRetArgs_g08])
    have hnz : satValue_g08 szVal ≠ 0#64 := by
      intro hz
      have hev : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.cmp .notEqual (.var .local (ofString "n")) (.const 0#64)) = some (.val (.word 0#64)) := by
        simp [evalHOLExact, hn, hz, Compiler.Encoders.Asm.wordCmpHOL]
      rw [hev] at hw
      have hw0 : w = 0#64 := by simpa using hw.symm
      exact hwne hw0
    exact copy_returndata_write_eff_g08 t stVal szVal (satValue_g08 rsVal) hc hInv hst_sh
      (copyLocals_get_g08 hK (by simp [copyRetArgs_g08])) hn
      (copyLocals_get_g08 hK (by simp)) hnz (hcov hnz) hnt
  · exact HandlerRun.seq_skip (HandlerRun.weaken (fun _ _ _ => trivial) hfinish)

private theorem copyExpand_update_g08 {F : Type} (t cpost : PanSemStateFiniteExact 64 F)
    (stVal szVal : ValueHOL 64) (nm : MlS) (v : ValueHOL 64)
    (hlf : LocFrame t cpost) (hne : nm ≠ ofString "x")
    (h : CopyExpand_g08 stVal szVal t) :
    CopyExpand_g08 stVal szVal (setVarHOLFinite nm v { cpost with locals := t.locals }) := by
  obtain ⟨cw, ebw, hx, heb, hcov⟩ := h
  let res := setVarHOLFinite nm v { cpost with locals := t.locals }
  have hlfres : LocFrame t res := by dsimp only [res]; rw [hlf]; rfl
  refine ⟨cw, ebw, ?_, ?_, ?_⟩
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hx]
  · change (ebw = 0#64 ∨
      (memW res (globN res "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
       (memW res (globN res "ev" + 32) + ebw.toNat) % 8 = 0 ∧
       memW res (globN res "ev" + 24) + memW res (globN res "ev" + 40) = globN res "frame_mem_ptr"))
    rw [hlfres]; exact heb
  · change satValue_g08 szVal ≠ 0#64 →
      (satValue_g08 stVal).toNat + (satValue_g08 szVal).toNat ≤ memW res (globN res "ev" + 32) + ebw.toNat
    rw [hlfres]; exact hcov

private theorem eps_add_sat_ro_copy_g08 :
    EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "add_sat") :=
  eps_of_readOnly 441 (by rw [guestAst_len]; decide) Guest.Software.guestFn_add_sat rfl opRoCallees opRoCallees_good rfl

private def copyRetBoundProg_g08 : ProgHOL 64 :=
  .decCall (ofString "rs") .one (ofString "sat_word") [.var .local (ofString "rstart")]
    (.decCall (ofString "endp") .one (ofString "add_sat")
      [.var .local (ofString "rs"), .var .local (ofString "n")]
      (.seq (.ite (.cmp .lower
          (.load .one (.op .add [.var .global (ofString "ev"), .const 152#64]))
          (.var .local (ofString "endp"))) (.raise (ofString "EvmErr") (.const 9#64)) .skip)
        (.seq (.call (some (none, none)) (ofString "extend_memory") [.rfield 1 (.var .local (ofString "x"))])
          copyRetTailProg_g08)))

private theorem copy_ret_bounds_run_g08 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (stVal rsVal szVal : ValueHOL 64) (ww : BitVec 64)
    (hst_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true)
    (hrs_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact rsVal) = true) :
    HandlerRun s0 (fun t => CopyLocals_g08
      ((ofString "w", .val (.word ww)) :: copyRetArgs_g08 stVal rsVal szVal) t.locals ∧
      CopyExpand_g08 stVal szVal t) true copyRetBoundProg_g08 := by
  let args := (ofString "w", ValueHOL.val (.word ww)) :: copyRetArgs_g08 stVal rsVal szVal
  let args1 := (ofString "rs", ValueHOL.val (.word (satValue_g08 rsVal))) :: args
  refine HandlerRun.decCall_sat_copy_g08 rsVal hrs_sh
    (Q := fun t => CopyLocals_g08 args1 t.locals ∧ CopyExpand_g08 stVal szVal t)
    (fun t ⟨hK, _⟩ => copyLocals_get_g08 hK (by simp [copyRetArgs_g08])) ?_ ?_
  · intro t cpost ⟨hK, hEx⟩ hlf
    refine ⟨copyLocals_cons_update_g08 args t.locals _ _ ?_ hK,
      copyExpand_update_g08 t cpost stVal szVal _ _ hlf (by decide) hEx⟩
    intro kv hk
    simp only [args, copyRetArgs_g08, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
  · refine HandlerRun.decCall (Q := fun t => CopyLocals_g08 args1 t.locals ∧ CopyExpand_g08 stVal szVal t)
      eps_add_sat_ro_copy_g08 (fun _ _ _ _ _ _ _ _ _ _ => trivial) ?_ ?_
    · intro t _ _ callee _ v cpost _ ⟨hK, hEx⟩ _ _ _ _ hlf
      have hlf_t : LocFrame t cpost := by rw [hlf]; rfl
      refine ⟨copyLocals_update_g08 args1 t.locals _ v ?_ hK,
        copyExpand_update_g08 t cpost stVal szVal _ v hlf_t (by decide) hEx⟩
      intro kv hk
      simp only [args1, args, copyRetArgs_g08, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
    · refine HandlerRun.seq_ite_raise_skip (fun _ _ _ h => h) ?_
      refine copy_extend_phase_run_g08 s0 stVal szVal (CopyLocals_g08 args1) ?_
      refine HandlerRun.weaken ?_ (copy_ret_tail_run_g08 s0 stVal rsVal szVal hst_sh)
      intro t _ ⟨hK, hcov⟩
      refine ⟨?_, hcov⟩
      intro kv hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact hK _ List.mem_cons_self
      · exact hK kv (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hk))

private def copyRetCostProg_g08 : ProgHOL 64 :=
  .decCall (ofString "x") (.comb [.one, .one]) (ofString "extend_memory_cost1")
    [.var .local (ofString "mstart"), .var .local (ofString "size")]
    (.decCall (ofString "cost") .one (ofString "add_sat")
      [.op .add [.const 3#64, .panop .mul [.const 3#64, .var .local (ofString "w")]],
       .rfield 0 (.var .local (ofString "x"))]
      (.seq (.call (some (none, none)) (ofString "charge_gas") [.var .local (ofString "cost")]) copyRetBoundProg_g08))

private def copyRetNumsProg_g08 : ProgHOL 64 :=
  .decCall (ofString "n") .one (ofString "sat_word") [.var .local (ofString "size")]
    (.decCall (ofString "w") .one (ofString "words_of") [.var .local (ofString "n")] copyRetCostProg_g08)

private theorem copy_ret_after_pops_run_g08 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (stVal rsVal szVal : ValueHOL 64)
    (hst_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true)
    (hrs_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact rsVal) = true)
    (hsz_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact szVal) = true) :
    HandlerRun s0 (fun t => HeadMemAligned t ∧
      CopyLocals_g08 (copyRetArgs_g08 stVal rsVal szVal).tail t.locals) false
      copyRetNumsProg_g08 := by
  have hcost : ∀ ww : BitVec 64, ww.toNat < 2 ^ 59 →
      HandlerRun s0 (fun t => HeadMemAligned t ∧ CopyLocals_g08
        ((ofString "w", .val (.word ww)) :: copyRetArgs_g08 stVal rsVal szVal) t.locals) false
        copyRetCostProg_g08 := by
    intro ww hwb
    let args := (ofString "w", ValueHOL.val (.word ww)) :: copyRetArgs_g08 stVal rsVal szVal
    refine copy_cost_phase_run_g08 s0 stVal szVal hst_sh hsz_sh (CopyLocals_g08 args)
      (.const 3#64)
      (fun _ _ => rfl)
      ?_ ?_
      (fun l hK => copyLocals_get_g08 hK (by simp [args, copyRetArgs_g08]))
      (fun l hK => copyLocals_get_g08 hK (by simp [args, copyRetArgs_g08]))
      (fun l hK => ⟨ww, copyLocals_get_g08 hK (by simp [args]), hwb⟩)
      ?_
    · intro l v hK
      apply copyLocals_update_g08 args l _ v _ hK
      intro kv hk
      simp only [args, copyRetArgs_g08, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
    · intro l v hK
      apply copyLocals_update_g08 args l _ v _ hK
      intro kv hk
      simp only [args, copyRetArgs_g08, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
    · exact copy_ret_bounds_run_g08 s0 stVal rsVal szVal ww hst_sh hrs_sh
  refine HandlerRun.decCall_sat_copy_g08 szVal hsz_sh
    (fun t ⟨_, hK⟩ => copyLocals_get_g08 hK (by simp [copyRetArgs_g08]))
    (Q := fun t => HeadMemAligned t ∧ CopyLocals_g08 (copyRetArgs_g08 stVal rsVal szVal) t.locals)
    ?_ ?_
  · intro t cpost ⟨hHM, hK⟩ hlf
    have hHM_cp : HeadMemAligned cpost := headMemAligned_congr_head_only
      (by rw [hlf]) (fun off _ => by unfold memW; rw [hlf]) hHM
    refine ⟨headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp, ?_⟩
    change CopyLocals_g08
      ((ofString "n", .val (.word (satValue_g08 szVal))) :: (copyRetArgs_g08 stVal rsVal szVal).tail)
      (t.locals.update (ofString "n", .val (.word (satValue_g08 szVal))))
    apply copyLocals_cons_update_g08 _ _ _ _ _ hK
    intro kv hk
    simp only [copyRetArgs_g08, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl <;> dsimp only <;> decide
  · refine HandlerRun.decCall
      (Q := fun t => HeadMemAligned t ∧ ∃ ww : BitVec 64, ww.toNat < 2 ^ 59 ∧
        CopyLocals_g08 ((ofString "w", .val (.word ww)) :: copyRetArgs_g08 stVal rsVal szVal) t.locals)
      eps_words_of_lt (fun _ _ _ _ _ _ _ _ _ _ => trivial) ?_ ?_
    · intro t _ _ callee _ v cpost _ ⟨hHM, hK⟩ _ _ _ _ hQc
      obtain ⟨hlf, ww, hv, hwb⟩ := hQc
      subst v
      have hHM_ce : HeadMemAligned (callEntryStateHOLFinite t callee) :=
        headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      have hHM_cp : HeadMemAligned cpost := headMemAligned_congr_head_only
        (by rw [hlf]) (fun off _ => by unfold memW; rw [hlf]) hHM_ce
      refine ⟨headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp, ww, hwb, ?_⟩
      apply copyLocals_cons_update_g08 _ _ _ _ _ hK
      intro kv hk
      simp only [copyRetArgs_g08, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> dsimp only <;> decide
    · intro t hc hInv hlen hR ⟨hHM, ww, hwb, hK⟩ hnt
      exact hcost ww hwb t hc hInv hlen hR ⟨hHM, hK⟩ hnt

private theorem lookup_op_returndatacopy_g08 :
    originalRuntimeCode.lookup (ofString "op_returndatacopy") =
      some ([], sourceFnBody Guest.Software.guestFn_op_returndatacopy, .one) :=
  lookup_of_guestAst_getElem 547 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_op_returndatacopy) rfl

theorem op_returndatacopy_aligned_spec :
    FunSpec (fun s => EvmRun s ∧ HeadMemAligned s) OpDispatchPost (ofString "op_returndatacopy") := by
  refine ⟨_, _, _, lookup_op_returndatacopy_g08, ?_⟩
  intro F s0 hcode ⟨hRun, hHM⟩ _ hnt
  suffices hrun : HandlerRun s0 (fun t => HeadMemAligned t ∧ CopyLocals_g08 [] t.locals) false
      (sourceFnBody Guest.Software.guestFn_op_returndatacopy) from
    hrun s0 hcode hRun.1 rfl (le_refl _) ⟨hHM, fun _ h => by cases h⟩ hnt
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_op_returndatacopy,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map, List.map]
  refine HandlerRun.decCall_stack_copy_g08 (CopyLocals_g08 [])
    (fun l => ∃ stVal, shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true ∧
      CopyLocals_g08 [(ofString "mstart", stVal)] l) ?_ ?_
  · intro l v hK hsh
    refine ⟨v, hsh, copyLocals_cons_update_g08 _ _ _ _ ?_ hK⟩
    intro kv hk; cases hk
  · refine HandlerRun.decCall_stack_copy_g08
      (fun l => ∃ stVal, shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true ∧
        CopyLocals_g08 [(ofString "mstart", stVal)] l)
      (fun l => ∃ stVal rsVal,
        shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true ∧
        shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact rsVal) = true ∧
        CopyLocals_g08 [(ofString "rstart", rsVal), (ofString "mstart", stVal)] l) ?_ ?_
    · intro l v ⟨stVal, hst, hK⟩ hsh
      refine ⟨stVal, v, hst, hsh, copyLocals_cons_update_g08 _ _ _ _ ?_ hK⟩
      intro kv hk
      simp only [List.mem_singleton] at hk
      subst kv
      dsimp only
      decide
    · refine HandlerRun.decCall_stack_copy_g08
        (fun l => ∃ stVal rsVal,
          shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true ∧
          shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact rsVal) = true ∧
          CopyLocals_g08 [(ofString "rstart", rsVal), (ofString "mstart", stVal)] l)
        (fun l => ∃ stVal rsVal szVal,
          shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true ∧
          shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact rsVal) = true ∧
          shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact szVal) = true ∧
          CopyLocals_g08 [(ofString "size", szVal), (ofString "rstart", rsVal), (ofString "mstart", stVal)] l) ?_ ?_
      · intro l v ⟨stVal, rsVal, hst, hrs, hK⟩ hsh
        refine ⟨stVal, rsVal, v, hst, hrs, hsh, copyLocals_cons_update_g08 _ _ _ _ ?_ hK⟩
        intro kv hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> dsimp only <;> decide
      · intro t hc hInv hlen hR ⟨hHM_t, stVal, rsVal, szVal, hst, hrs, hsz, hK⟩ hnt_t
        exact copy_ret_after_pops_run_g08 s0 stVal rsVal szVal hst hrs hsz
          t hc hInv hlen hR ⟨hHM_t, hK⟩ hnt_t

def ExtCodeOfHeadSpec : Prop :=
  EvmPreservingSpec (fun _ => True)
    (fun s _ post =>
      GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧
      OpDispatchSpec.evmR post = OpDispatchSpec.evmR s ∧
      ∀ off, off + 8 ≤ 280 → off % 8 = 0 →
        memW post (globN s "ev" + off) = memW s (globN s "ev" + off))
    (ofString "ext_code_of")

private theorem lookup_op_mcopy_g08 :
    originalRuntimeCode.lookup (ofString "op_mcopy") =
      some ([], sourceFnBody Guest.Software.guestFn_op_mcopy, .one) :=
  lookup_of_guestAst_getElem 512 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_op_mcopy) rfl

private theorem lookup_op_extcodecopy_g08 :
    originalRuntimeCode.lookup (ofString "op_extcodecopy") =
      some ([], sourceFnBody Guest.Software.guestFn_op_extcodecopy, .one) :=
  lookup_of_guestAst_getElem 545 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_op_extcodecopy) rfl

private theorem head_ev_bounds_g08 {F : Type} {s : PanSemStateFiniteExact 64 F} (hInv : EvmInv s) :
    0 < globN s "ev" ∧ globN s "ev" + 280 ≤ heapEnd ∧ globN s "ev" + 280 ≤ 2 ^ 64 ∧ globN s "ev" % 8 = 0 := by
  obtain ⟨hAs, _, _, _, _, _, hFW_all, _⟩ := hInv
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    simp [evmChain, evmChainFrom]
  have hFW0 := hFW_all _ hhead
  have hin1 := (hFW0.1 (globN s "ev", 280) (by simp)).1.1
  have hin2 := (hFW0.1 (globN s "ev", 280) (by simp)).1.2
  have hev8 := (hFW0.1 (globN s "ev", 280) (by simp)).2.1
  dsimp only at hin1 hin2 hev8
  have hfm1 := hAs.2.2.2.1
  have hfm2 := hAs.2.2.2.2.1
  rw [R11Shards.scratchStart_val] at hfm1
  rw [R11Shards.scratchEnd_val] at hin2
  rw [R11Shards.heapEnd_val]
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by norm_num
  rw [h264]
  exact ⟨by omega, by omega, by omega, hev8⟩

private theorem eps_to_address_masked_head_g08 :
    EvmPreservingSpec (fun _ => True)
      (fun s v post =>
        post.globals = s.globals ∧
        evmR post = evmR s ∧
        (∃ aw : BitVec 64, v = .val (.word aw)) ∧
        ∀ off, off ∈ ([24, 32, 40] : List Nat) →
          memW post (globN s "ev" + off) = memW s (globN s "ev" + off))
      (ofString "to_address_masked") := by
  refine ⟨_, _, _, lookup_to_address_masked, ?_⟩
  intro F s hcode hInv _ _ hnt
  have hnc := R16Shards.StateRestoreEpilogue.evaluate_noCatchableRaise warmAccessNcrCallees warmAccessNcrCallees_good
    (sourceFnBody Guest.Software.guestFn_to_address_masked) (by decide) s hcode
  dsimp only
  refine ⟨?_, fun ⟨ev, hev⟩ => False.elim (hnc (ofString "EvmErr") ev (by decide) hev)⟩
  intro v hv
  have hma : s.memaddrs = ordinaryDomain := hInv.1.1.memaddrs
  obtain ⟨hev_pos, hev_he, hb_ev, hev8⟩ := head_ev_bounds_g08 hInv
  obtain ⟨evw, hevw_lk, hevw_nat⟩ := global_word_of_pos s "ev" hev_pos
  let aW : BitVec 64 := evw + BitVec.ofNat 64 240
  have haW_nat : aW.toNat = globN s "ev" + 240 := by
    have hev_lt : evw.toNat < heapEnd := by rw [hevw_nat]; omega
    rw [R11Shards.heapEnd_val] at hev_lt
    have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by norm_num
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, hevw_nat, h264,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have haW_lt : aW.toNat < heapEnd := by rw [haW_nat]; omega
  have hev_init : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 240)]) =
      some (.val (.word aW)) := by
    simp only [evalHOLExact, evalListHOLExact, hevw_lk, wordOpHOL, wordOp, valueIsWord, valueWord,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
    have hz : (240#64 : BitVec 64) + 0 = 240#64 := BitVec.add_zero _
    exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word (evw + w)))) hz
  have hb : sourceFnBody Guest.Software.guestFn_to_address_masked =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_to_address_masked).body := rfl
  have heff_and_ret :
      ByteRegionEffect s
        (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_to_address_masked)).2
        [(globN s "ev" + 240, 20)] ∧
      ∃ aw : BitVec 64, v = .val (.word aw) := by
    rw [hb] at hv ⊢
    dsimp only [extractFn, Guest.Software.guestFn_to_address_masked,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
      List.map, Option.map] at hv ⊢
    rw [evaluateHOLFiniteState_dec_total] at hv ⊢
    dsimp only at hv ⊢
    rw [hev_init] at hv ⊢
    dsimp only at hv ⊢
    have hsh_ok : shapeEqHOL .one (shapeOfHOLExact (.val (.word aW) : ValueHOL 64)) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    rw [if_pos hsh_ok] at hv ⊢
    dsimp only at hv ⊢
    let s0 := setVarHOLFinite (ofString "a") (.val (.word aW)) s
    have hs0_eff : ByteRegionEffect s s0 [(aW.toNat, 32)] :=
      (ByteRegionEffect.refl s _).with_locals_clock _ _
    have ha_s0 : s0.locals.lookup (ofString "a") = some (.val (.word aW)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    let seqBody : ProgHOL 64 :=
      .seq
        (.call (some (none, none)) (ofString "st_be32")
          [.var .local (ofString "a"), .rfield 2 (.var .local (ofString "v"))])
        (.seq
          (.call (some (none, none)) (ofString "st_be64")
            [.op .add [.var .local (ofString "a"), .const 4#64],
             .rfield 1 (.var .local (ofString "v"))])
          (.seq
            (.call (some (none, none)) (ofString "st_be64")
              [.op .add [.var .local (ofString "a"), .const 12#64],
               .rfield 0 (.var .local (ofString "v"))])
            (.return (.var .local (ofString "a")))))
    have hbody_eff : ByteRegionEffect s0 (evaluateHOLFiniteState s0 seqBody).2 [(aW.toNat, 20)] ∧
        ((evaluateHOLFiniteState s0 seqBody).1 = some (.returned v) → v = .val (.word aW)) := by
      dsimp only [seqBody]
      have heff_32 : ByteRegionEffect s0 (evaluateHOLFiniteState s0 seqBody).2 [(aW.toNat, 32)] := by
        dsimp only [seqBody]
        refine seq_call_st_be32_eff_g08 (s := s0) (base := aW) (off := 0) (len := 32)
          hcode hma (by omega) (by omega) (fun _ => haW_lt)
          (eval_var_local_zero_g08 s0 "a" aW ha_s0) fun s1 _ hc1 hm1 hl1 => ?_
        have ha1 : s1.locals.lookup (ofString "a") = some (.val (.word aW)) := by rw [hl1]; exact ha_s0
        refine seq_call_st_be64_eff_g08 (s := s1) (base := aW) (off := 4)
          hc1 hm1 (by omega) (fun _ => haW_lt)
          (eval_add_local_const_g08 s1 "a" aW 4 ha1) fun s2 _ hc2 hm2 hl2 => ?_
        have ha2 : s2.locals.lookup (ofString "a") = some (.val (.word aW)) := by rw [hl2]; exact ha1
        refine seq_call_st_be64_eff_g08 (s := s2) (base := aW) (off := 12)
          hc2 hm2 (by omega) (fun _ => haW_lt)
          (eval_add_local_const_g08 s2 "a" aW 12 ha2) fun s3 _ _ _ _ => return_eff_g08 s3 _ _
      have heff_20 : ByteRegionEffect s0 (evaluateHOLFiniteState s0 seqBody).2 [(aW.toNat, 20)] := by
        refine seq_call_st_be32_eff_g08 (s := s0) (base := aW) (off := 0) (len := 20)
          hcode hma (by omega) (by omega) (fun _ => haW_lt)
          (eval_var_local_zero_g08 s0 "a" aW ha_s0) fun s1 _ hc1 hm1 hl1 => ?_
        have ha1 : s1.locals.lookup (ofString "a") = some (.val (.word aW)) := by rw [hl1]; exact ha_s0
        rw [evaluateHOLFiniteState_seq_line780]
        rcases hc_c1 : evaluateHOLFiniteState s1
            (.call (some (none, none)) (ofString "st_be64")
              [.op .add [.var .local (ofString "a"), .const 4#64],
               .rfield 1 (.var .local (ofString "v"))]) with ⟨rc1, sc1⟩
        have hstep_be64 : ∀ (st : PanSemStateFiniteExact 64 F) (off : Nat) (vExp : ExpHOL 64),
            off + 8 ≤ 20 → st.code = originalRuntimeCode → st.memaddrs = ordinaryDomain →
            st.locals.lookup (ofString "a") = some (.val (.word aW)) →
            let cRes := evaluateHOLFiniteState st
              (.call (some (none, none)) (ofString "st_be64")
                [.op .add [.var .local (ofString "a"), .const (BitVec.ofNat 64 off)], vExp])
            ByteRegionEffect st cRes.2 [(aW.toNat, 20)] ∧
            (cRes.1 = none → cRes.2.code = originalRuntimeCode ∧
              cRes.2.memaddrs = ordinaryDomain ∧ cRes.2.locals = st.locals) := by
          intro st off vExp hoff hcst hmst hast
          dsimp only
          rcases hc_st : evaluateHOLFiniteState st
              (.call (some (none, none)) (ofString "st_be64")
                [.op .add [.var .local (ofString "a"), .const (BitVec.ofNat 64 off)], vExp]) with ⟨rc, sc⟩
          rw [evaluateHOLFiniteState_call] at hc_st
          have hp_ev := eval_add_local_const_g08 st "a" aW off hast
          rcases hv_ev : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) vExp with _ | vv
          · have hnone : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
                [.op .add [.var .local (ofString "a"), .const (BitVec.ofNat 64 off)], vExp] = none := by
              simp [evalListHOLFinite, evalListHOLExact, hp_ev, hv_ev]
            rw [hnone] at hc_st; injection hc_st with hr hsc; subst hr hsc
            exact ⟨ByteRegionEffect.refl st _, fun h => by cases h⟩
          · let pArg := aW + BitVec.ofNat 64 off
            have hargs : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
                [.op .add [.var .local (ofString "a"), .const (BitVec.ofNat 64 off)], vExp] =
                some [.val (.word pArg), vv] := by
              simp [evalListHOLFinite, evalListHOLExact, hp_ev, hv_ev, pArg]
            rw [hargs] at hc_st; dsimp only at hc_st
            by_cases hvw : ∃ vW : BitVec 64, vv = .val (.word vW)
            · obtain ⟨vW, rfl⟩ := hvw
              have hl := pan_two_word_lookup st.code.lookup (ofString "st_be64") (ofString "p") (ofString "v")
                (sourceFnBody Guest.Software.guestFn_st_be64) pArg vW (by decide) (by rw [hcst]; exact lookup_st_be64_g08)
              rw [hl] at hc_st; dsimp only at hc_st
              split at hc_st
              · injection hc_st with hr hsc; subst hr hsc
                exact ⟨(ByteRegionEffect.refl st _).with_locals_clock _ _, fun h => by cases h⟩
              · let entry := callEntryStateHOLFinite st
                  ((HolFiniteMapExact.empty.update (ofString "p", .val (.word pArg))).update (ofString "v", .val (.word vW)))
                have hp_in : entry.locals.lookup (ofString "p") = some (.val (.word pArg)) := by
                  simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "v" ≠ ofString "p" by decide]
                obtain ⟨heff_b, hlt_or_eq, _⟩ := st_be64_body_eff_g08 entry pArg hcst hmst hp_in
                rcases hb_st : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_st_be64) with ⟨rb, sb⟩
                have hb_entry : evaluateHOLFiniteState
                    (callEntryStateHOLFinite st
                      ((HolFiniteMapExact.empty.update (ofString "p", .val (.word pArg))).update (ofString "v", .val (.word vW))))
                    (sourceFnBody Guest.Software.guestFn_st_be64) = (rb, sb) := hb_st
                rw [hb_entry] at hc_st; rw [hb_st] at heff_b hlt_or_eq; dsimp only at heff_b hlt_or_eq
                have heff_entry : ByteRegionEffect st entry [(aW.toNat, 20)] :=
                  (ByteRegionEffect.refl st _).with_locals_clock _ _
                have hpArg_nat : pArg.toNat = aW.toNat + off := bv_add_off_nat_g08 aW off haW_lt (by omega)
                have heff_sb : ByteRegionEffect st sb [(aW.toNat, 20)] :=
                  heff_entry.trans (heff_b.mono fun i hi => by
                    simp only [List.mem_singleton] at hi; subst hi
                    exact ⟨(aW.toNat, 20), List.mem_singleton.2 rfl, by rw [hpArg_nat]; omega, by rw [hpArg_nat]; omega⟩)
                cases rb with
                | none => injection hc_st with hr hsc; subst hr hsc; exact ⟨heff_sb, fun h => by cases h⟩
                | some r =>
                  cases r with
                  | returned rv =>
                    dsimp only at hc_st; split at hc_st
                    · injection hc_st with hr hsc; subst hr hsc
                      have heff_s1 : ByteRegionEffect st { sb with locals := st.locals } [(aW.toNat, 20)] :=
                        heff_sb.with_locals_clock _ _
                      exact ⟨heff_s1, fun _ => ⟨heff_s1.code.trans hcst, heff_s1.memaddrs.trans hmst, rfl⟩⟩
                    · injection hc_st with hr hsc; subst hr hsc; exact ⟨heff_sb, fun h => by cases h⟩
                  | timeOut | error | exception _ _ | finalFfi _ =>
                    injection hc_st with hr hsc; subst hr hsc
                    exact ⟨heff_sb.with_locals_clock _ _, fun h => by cases h⟩
                  | «break» | «continue» =>
                    injection hc_st with hr hsc; subst hr hsc; exact ⟨heff_sb, fun h => by cases h⟩
            · have hln := lookup_two_words_reject_nonword_g08 st.code.lookup (ofString "st_be64") (ofString "p") (ofString "v")
                _ pArg vv (by rw [hcst]; exact lookup_st_be64_g08) (fun w hw => hvw ⟨w, hw⟩)
              rw [hln] at hc_st; injection hc_st with hr hsc; subst hr hsc
              exact ⟨ByteRegionEffect.refl st _, fun h => by cases h⟩
        have h1 := hstep_be64 s1 4 (.rfield 1 (.var .local (ofString "v"))) (by omega) hc1 hm1 ha1
        dsimp only at h1; rw [hc_c1] at h1; dsimp only at h1 ⊢
        cases rc1 with
        | some _ => exact h1.1
        | none =>
          dsimp only
          obtain ⟨hc_sc1, hm_sc1, hl_sc1⟩ := h1.2 rfl
          have ha_sc1 : sc1.locals.lookup (ofString "a") = some (.val (.word aW)) := by rw [hl_sc1]; exact ha1
          rw [evaluateHOLFiniteState_seq_line780]
          have h2 := hstep_be64 sc1 12 (.rfield 0 (.var .local (ofString "v"))) (by omega) hc_sc1 hm_sc1 ha_sc1
          dsimp only at h2
          rcases hc_c2 : evaluateHOLFiniteState sc1
              (.call (some (none, none)) (ofString "st_be64")
                [.op .add [.var .local (ofString "a"), .const 12#64],
                 .rfield 0 (.var .local (ofString "v"))]) with ⟨rc2, sc2⟩
          rw [hc_c2] at h2; dsimp only at h2 ⊢
          cases rc2 with
          | some _ => exact h1.1.trans h2.1
          | none => exact h1.1.trans (h2.1.trans (return_eff_g08 sc2 _ _))
      refine ⟨heff_20, ?_⟩
      intro hret_seq
      have hcall_not_ret : ∀ (st : PanSemStateFiniteExact 64 F) fn args rv,
          (evaluateHOLFiniteState st (.call (some (none, none)) fn args)).1 ≠ some (.returned rv) := by
        intro st fn args rv hc_eq
        rw [evaluateHOLFiniteState_call] at hc_eq
        split at hc_eq
        · simp at hc_eq
        · split at hc_eq
          · simp at hc_eq
          · split at hc_eq
            · simp at hc_eq
            · split at hc_eq
              · simp at hc_eq
              · simp at hc_eq
              · simp at hc_eq
              · split at hc_eq <;> simp at hc_eq
              · simp at hc_eq
              · rename_i other _ _ hne _ _
                have h1 := Option.some.inj hc_eq
                subst h1; exact hne rv rfl
      rw [evaluateHOLFiniteState_seq_line780] at hret_seq
      rcases hk1 : evaluateHOLFiniteState s0
          (.call (some (none, none)) (ofString "st_be32")
            [.var .local (ofString "a"), .rfield 2 (.var .local (ofString "v"))]) with ⟨rk1, sk1⟩
      rw [hk1] at hret_seq
      cases rk1 with
      | some rk1' =>
        dsimp only at hret_seq
        exact False.elim (hcall_not_ret s0 _ _ v (by rw [hk1, hret_seq]))
      | none =>
        dsimp only at hret_seq
        have hloc1 : sk1.locals = s0.locals := by
          rw [evaluateHOLFiniteState_call] at hk1
          split at hk1
          · simp at hk1
          · split at hk1
            · simp at hk1
            · split at hk1
              · simp at hk1
              · split at hk1 <;> try simp at hk1
                split at hk1
                · injection hk1 with _ hsk1; rw [← hsk1]
                · simp at hk1
        rw [evaluateHOLFiniteState_seq_line780] at hret_seq
        rcases hk2 : evaluateHOLFiniteState sk1
            (.call (some (none, none)) (ofString "st_be64")
              [.op .add [.var .local (ofString "a"), .const 4#64],
               .rfield 1 (.var .local (ofString "v"))]) with ⟨rk2, sk2⟩
        rw [hk2] at hret_seq
        cases rk2 with
        | some _ =>
          dsimp only at hret_seq
          exact False.elim (hcall_not_ret sk1 _ _ v (by rw [hk2, hret_seq]))
        | none =>
          dsimp only at hret_seq
          have hloc2 : sk2.locals = sk1.locals := by
            rw [evaluateHOLFiniteState_call] at hk2
            split at hk2
            · simp at hk2
            · split at hk2
              · simp at hk2
              · split at hk2
                · simp at hk2
                · split at hk2 <;> try simp at hk2
                  split at hk2
                  · injection hk2 with _ hsk2; rw [← hsk2]
                  · simp at hk2
          rw [evaluateHOLFiniteState_seq_line780] at hret_seq
          rcases hk3 : evaluateHOLFiniteState sk2
              (.call (some (none, none)) (ofString "st_be64")
                [.op .add [.var .local (ofString "a"), .const 12#64],
                 .rfield 0 (.var .local (ofString "v"))]) with ⟨rk3, sk3⟩
          rw [hk3] at hret_seq
          cases rk3 with
          | some _ =>
            dsimp only at hret_seq
            exact False.elim (hcall_not_ret sk2 _ _ v (by rw [hk3, hret_seq]))
          | none =>
            dsimp only at hret_seq
            have hloc3 : sk3.locals = sk2.locals := by
              rw [evaluateHOLFiniteState_call] at hk3
              split at hk3
              · simp at hk3
              · split at hk3
                · simp at hk3
                · split at hk3
                  · simp at hk3
                  · split at hk3 <;> try simp at hk3
                    split at hk3
                    · injection hk3 with _ hsk3; rw [← hsk3]
                    · simp at hk3
            have ha3 : sk3.locals.lookup (ofString "a") = some (.val (.word aW)) := by
              rw [hloc3, hloc2, hloc1]; exact ha_s0
            rw [evaluateHOLFiniteState_return] at hret_seq
            have hev_a : @evalHOLExact 64 F _ sk3.toExact (fun a => Classical.propDecidable (sk3.memaddrs a))
                (.var .local (ofString "a")) = some (.val (.word aW)) := ha3
            rw [hev_a] at hret_seq; dsimp only at hret_seq
            split at hret_seq
            · injection hret_seq with h1; injection h1 with h2; exact h2.symm
            · simp at hret_seq
    have hs0_eff20 : ByteRegionEffect s s0 [(aW.toNat, 20)] :=
      (ByteRegionEffect.refl s _).with_locals_clock _ _
    refine ⟨?_, aW, hbody_eff.2 hv⟩
    rw [← haW_nat]
    exact (hs0_eff20.trans hbody_eff.1).with_locals_clock _ _
  obtain ⟨heff, hv_word⟩ := heff_and_ret
  let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_to_address_masked)).2
  have hGp : GuestInv post :=
    guestInv_congr (s := s) (t := post) heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hInv.1.1
  have hmem_out : ∀ x : BitVec 64,
      (∀ off ∈ nonStructFrameOffs, x ≠ BitVec.ofNat 64 (globN s "ev" + off)) →
      post.memory x = s.memory x := by
    intro x hne
    by_cases hx_dom : s.memaddrs x
    · have hx8 : x.toNat % 8 = 0 := by
        rw [hma, ordinaryDomain_iff] at hx_dom; exact hx_dom.2.2
      apply heff.cell_frame x
      intro i hi hch
      simp only [List.mem_singleton] at hi; subst hi
      obtain ⟨hc1, hc2⟩ := hch
      dsimp only at hc1 hc2
      have hk : x.toNat = globN s "ev" + 240 ∨ x.toNat = globN s "ev" + 248 ∨ x.toNat = globN s "ev" + 256 := by
        omega
      rcases hk with h240 | h248 | h256
      · exact hne 240 (by decide) (BitVec.eq_of_toNat_eq (by
          rw [h240, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]))
      · exact hne 248 (by decide) (BitVec.eq_of_toNat_eq (by
          rw [h248, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]))
      · exact hne 256 (by decide) (BitVec.eq_of_toNat_eq (by
          rw [h256, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]))
    · exact heff.out_dom x hx_dom
  obtain ⟨hInv_p, hch_p, hR_p⟩ := evmInv_of_head_nonstruct hInv hGp heff.globals heff.be hmem_out
  refine ⟨hInv_p, hch_p, le_of_eq hR_p, heff.globals, hR_p, hv_word, ?_⟩
  intro off hoff
  have hoff_le : off ≤ 40 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl | rfl <;> omega
  have hcell : post.memory (BitVec.ofNat 64 (globN s "ev" + off)) =
      s.memory (BitVec.ofNat 64 (globN s "ev" + off)) := by
    apply hmem_out
    intro o ho heq
    have htn := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by
        have ho_lt : o ≤ 272 := by
          simp only [nonStructFrameOffs, List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
        omega)] at htn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    simp only [nonStructFrameOffs, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases hoff with rfl | rfl | rfl <;>
      (rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  unfold memW
  change (match post.memory (BitVec.ofNat 64 (globN s "ev" + off)) with | .word w => w.toNat) = _
  rw [hcell]

private theorem head_frame_addr_role_props_g08 {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hInv : EvmInvAt s S) :
    let t0 := memW s (globN s "ev" + 168)
    t0 ∈ S ∧
    (∀ (i : Nat) (_hi : i + 1 < (evmChain s).length), ¬ DelExclusive s S (evmChain s) i t0) ∧
    (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t0) ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
    globN s "bal_accounts" ≠ t0 ∧
    (∀ ad ∈ balRecords s, memW s ad ≠ t0) ∧
    (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) := by
  dsimp only
  set t0 := memW s (globN s "ev" + 168)
  obtain ⟨⟨hT, _, _, _⟩, hch_ne, _, _, hFW_all, _, _, _, _, _, _, hRoles, _⟩ := hInv
  have hch_cons : ∃ tail, evmChain s = (globN s "ev", globN s "cur_cont") :: tail := by
    unfold evmChain
    have hpos : ∃ m, Wave8GuestInv.maxChain + 1 = m + 1 := ⟨Wave8GuestInv.maxChain, rfl⟩
    obtain ⟨m, hm⟩ := hpos; rw [hm, evmChainFrom]; exact ⟨_, rfl⟩
  obtain ⟨chTail, hch⟩ := hch_cons
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by rw [hch]; exact List.mem_cons_self
  have ht0_S : t0 ∈ S := (hFW_all _ hhead).2.2.2.2.2.2.2.2.1
  have ht0_pos : 0 < t0 := by
    have := ((hT.2.1 t0 ht0_S).1.1 (t0, 88) (by simp [htabFootprint])).1.1
    have hsb : 0 < sourceBase := by decide
    dsimp at this; omega
  have hnot_world_role : ∀ rname : String, rname ≠ "frame.addr" → (t0, rname) ∉ worldRoleSlots s := by
    intro rname hr_ne hmem
    have hpw : (worldRoleSlots s ++ frameRoleSlots s (evmChain s)).Pairwise
        (fun a b => a.1 = b.1 → a.2 = b.2 ∧ a.2 ∈ sharedRoles) := hRoles.2.1
    have hcross := (List.pairwise_append.1 hpw).2.2 (t0, rname) hmem (t0, "frame.addr")
      (by
        unfold frameRoleSlots
        exact List.mem_flatMap.2 ⟨(globN s "ev", globN s "cur_cont"), hhead, by simp [t0]⟩)
      rfl
    exact hr_ne hcross.1
  refine ⟨ht0_S, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi hdel
    have h0_lt : 0 < (evmChain s).length := by omega
    have hch0 : (evmChain s)[0].1 = globN s "ev" := by simp [hch]
    have h168 := hdel.2 0 h0_lt 168 (by decide) (by rw [hch0])
    omega
  · intro hws heq
    apply hnot_world_role "ws+32" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    unfold recRoles; simp [hws, heq]
  · intro hbs heq
    apply hnot_world_role "bs+32" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
    unfold recRoles; simp [hbs, heq]
  · intro heq
    apply hnot_world_role "bal_accounts" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_right; simp [heq]
  · intro ad had heq
    apply hnot_world_role "bal.stor" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_right
    exact List.mem_flatMap.2 ⟨ad, had, by simp [heq]⟩
  · intro hts heq
    apply hnot_world_role "ts+32" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_right
    unfold recRoles; simp [hts, heq]

private theorem three_one_word_call_args_g08 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (fn : MlS) (e1 e2 e3 : ExpHOL 64)
    (body : ProgHOL 64) (retShape : ShapeHOL)
    (p1 p2 p3 : MlS)
    (hcode : s.code.lookup fn = some ([(p1, .one), (p2, .one), (p3, .one)], body, retShape))
    (hok : (evaluateHOLFiniteState s (.call (some (none, none)) fn [e1, e2, e3])).1 ≠ some .error) :
    ∃ w1 w2 w3 : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 = some (.val (.word w1)) ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 = some (.val (.word w2)) ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e3 = some (.val (.word w3)) := by
  rw [evaluateHOLFiniteState_call] at hok
  rcases hv1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | v1
  · simp [evalListHOLFinite, evalListHOLExact, hv1] at hok
  · rcases hv2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 with _ | v2
    · simp [evalListHOLFinite, evalListHOLExact, hv1, hv2] at hok
    · rcases hv3 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e3 with _ | v3
      · simp [evalListHOLFinite, evalListHOLExact, hv1, hv2, hv3] at hok
      · have hevl : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1, e2, e3] =
            some [v1, v2, v3] := by
          simp [evalListHOLFinite, evalListHOLExact, hv1, hv2, hv3]
        rw [hevl] at hok; dsimp only at hok
        rcases hl : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fn [v1, v2, v3] with _ | ⟨b, c, rs⟩
        · rw [hl] at hok; exact absurd rfl hok
        · have hraw : lookupCodeHOLExact s.code.lookup fn [v1, v2, v3] ≠ none := by
            intro hn
            unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
            split at hl
            · simp at hl
            · rename_i hsome; rw [hn] at hsome; simp at hsome
          simp only [lookupCodeHOLExact, hcode, List.length_cons, List.length_nil, ↓reduceIte,
            List.zip, List.zipWith, List.all, Bool.and_true, Bool.and_eq_true] at hraw
          have hshapes : shapeEqHOL .one (shapeOfHOLExact v1) = true ∧
              shapeEqHOL .one (shapeOfHOLExact v2) = true ∧
              shapeEqHOL .one (shapeOfHOLExact v3) = true := by
            by_contra hns; simp [hns] at hraw
          have hw : ∀ v : ValueHOL 64, shapeEqHOL .one (shapeOfHOLExact v) = true → ∃ w, v = .val (.word w) := by
            intro v hsv
            rcases v with ⟨⟨w⟩⟩ | _ | _
            · exact ⟨w, rfl⟩
            · simp [shapeOfHOLExact, shapeEqHOL] at hsv
            · simp [shapeOfHOLExact, shapeEqHOL] at hsv
          obtain ⟨w1, rfl⟩ := hw v1 hshapes.1
          obtain ⟨w2, rfl⟩ := hw v2 hshapes.2.1
          obtain ⟨w3, rfl⟩ := hw v3 hshapes.2.2
          exact ⟨w1, w2, w3, rfl, rfl, rfl⟩

private theorem eps_warm_address_head_g08 :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post =>
        GlobalsKept ["heap_ptr"] s post ∧
        evmR post = evmR s ∧
        ∀ off, off + 8 ≤ 280 → off % 8 = 0 →
          memW post (globN s "ev" + off) = memW s (globN s "ev" + off))
      (ofString "warm_address") := by
  refine ⟨_, _, _, lookup_warm_address, ?_⟩
  intro F s hcode hInv _ _ hnt
  have hnc := R16Shards.StateRestoreEpilogue.evaluate_noCatchableRaise warmAccessNcrCallees warmAccessNcrCallees_good
    (sourceFnBody Guest.Software.guestFn_warm_address) (by decide) s hcode
  dsimp only
  refine ⟨?_, fun ⟨ev, hev⟩ => False.elim (hnc (ofString "EvmErr") ev (by decide) hev)⟩
  intro v_ret hv
  have hb : sourceFnBody Guest.Software.guestFn_warm_address =
      .seq
        (.call (some (none, none)) (ofString "htab_set")
          [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 168)]),
           .var .local (ofString "addr"), .const (BitVec.ofNat 64 1)])
        (.return (.const (BitVec.ofNat 64 0))) := rfl
  rw [hb] at hv ⊢
  obtain ⟨hAs, S, hW, hrest⟩ := hInv
  have hInvAt : EvmInvAt s S := ⟨hW, hrest⟩
  rcases hrun_c : evaluateHOLFiniteState s
      (.seq
        (.call (some (none, none)) (ofString "htab_set")
          [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 168)]),
           .var .local (ofString "addr"), .const (BitVec.ofNat 64 1)])
        (.return (.const (BitVec.ofNat 64 0)))) with ⟨res_c, post_c⟩
  have hret' : res_c = some (.returned v_ret) := by
    have := hv; rw [hrun_c] at this; exact this
  subst hret'
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780] at hrun_c
  rcases hc_set : evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set")
        [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 168)]),
         .var .local (ofString "addr"), .const (BitVec.ofNat 64 1)]) with ⟨r_set, s2⟩
  rw [hc_set] at hrun_c
  cases r_set with
  | some rs =>
    dsimp only at hrun_c
    exfalso
    have hrs_ret : rs = .returned v_ret := Option.some.inj (Prod.mk.inj hrun_c).1
    rw [evaluateHOLFiniteState_call] at hc_set
    split at hc_set
    · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
    · split at hc_set
      · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
      · split at hc_set
        · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
        · split at hc_set
          · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
          · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
          · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
          · split at hc_set
            · simp at hc_set
            · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
          · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
          · rename_i other _ _ heq_other _ _
            have h1 := Option.some.inj (Prod.mk.inj hc_set).1
            rw [hrs_ret] at h1; subst h1; exact heq_other v_ret rfl
  | none =>
    dsimp only at hrun_c
    rw [evaluateHOLFiniteState_return] at hrun_c
    have hev0_s2 : @evalHOLExact 64 F _ s2.toExact
        (fun a => Classical.propDecidable (s2.memaddrs a)) (.const (BitVec.ofNat 64 0)) =
        some (.val (.word 0)) := rfl
    have hsz0_s2 : sizeOfShapeWithContextHOL s2.structs
        (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) ≤ 32 := by
      simp [shapeOfHOLExact]
    rw [hev0_s2] at hrun_c; dsimp only at hrun_c; rw [if_pos hsz0_s2] at hrun_c
    injection hrun_c with _ hpost_c
    obtain ⟨tw, kw, vw, htw_ev, hkw_ev, hvw_ev⟩ :=
      three_one_word_call_args_g08 s (ofString "htab_set")
        (.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 168)]))
        (.var .local (ofString "addr")) (.const (BitVec.ofNat 64 1))
        _ _ (ofString "t") (ofString "key") (ofString "value")
        (by rw [hcode]; exact SoloHtabSet.lookup_htab_set)
        (by rw [hc_set]; simp)
    obtain ⟨hev_pos, _, hb_ev, hev8⟩ := head_ev_bounds_g08 ⟨hAs, S, hInvAt⟩
    obtain ⟨evw, hevw_lk, hevw_nat⟩ := global_word_of_pos s "ev" hev_pos
    have htw_nat : tw.toNat = memW s (globN s "ev" + 168) := by
      have had_eq : @evalHOLExact 64 F _ s.toExact
          (fun a => Classical.propDecidable (s.memaddrs a))
          (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 168)]) =
          some (.val (.word (BitVec.ofNat 64 (globN s "ev" + 168)))) := by
        simp only [evalHOLExact, evalListHOLExact, hevw_lk, wordOpHOL, wordOp, valueIsWord, valueWord,
          List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr, BitVec.add_zero]
        congr 3
        apply BitVec.eq_of_toNat_eq
        have hz0 : (0 : BitVec 64).toNat = 0 := rfl
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hevw_nat, hz0, Nat.add_zero,
          Nat.mod_eq_of_lt (show 168 < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (show globN s "ev" + 168 < 2 ^ 64 by omega)]
      unfold evalHOLExact at htw_ev
      rw [had_eq] at htw_ev; dsimp only at htw_ev
      unfold memLoadHOLExact at htw_ev
      split at htw_ev
      · split at htw_ev
        · injection htw_ev with htw_m
          unfold memW
          cases hm_cell : s.memory (BitVec.ofNat 64 (globN s "ev" + 168)) with
          | word cw =>
            change ValueHOL.val (s.memory (BitVec.ofNat 64 (globN s "ev" + 168))) = .val (.word tw) at htw_m
            rw [hm_cell] at htw_m
            injection htw_m with htw_m; injection htw_m with htw_m; subst htw_m; rfl
        · cases htw_ev
      · cases htw_ev
    rw [evaluateHOLFiniteState_call] at hc_set
    have hargs_set : evalListHOLFinite s
        (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 168)]),
         .var .local (ofString "addr"), .const (BitVec.ofNat 64 1)] =
        some [.val (.word tw), .val (.word kw), .val (.word vw)] := by
      simp [evalListHOLFinite, evalListHOLExact, htw_ev, hkw_ev, hvw_ev]
    have hlook_set := InitECandidate.Solver.GuestTrapAndLookup.pan_three_word_lookup s.code.lookup (ofString "htab_set")
      (ofString "t") (ofString "key") (ofString "value")
      (sourceFnBody Guest.Software.guestFn_htab_set) tw kw vw
      (by decide) (by decide) (by decide)
      (by rw [hcode]; exact SoloHtabSet.lookup_htab_set)
    rw [hargs_set] at hc_set; dsimp only at hc_set
    rw [hlook_set] at hc_set; dsimp only at hc_set
    by_cases hclk_s : s.clock = 0
    · rw [if_pos hclk_s] at hc_set; simp at hc_set
    · rw [if_neg hclk_s] at hc_set
      let cmap_s : HolFiniteMapExact MlS (ValueHOL 64) :=
        ((HolFiniteMapExact.empty.update (ofString "t", ValueHOL.val (.word tw))).update
          (ofString "key", ValueHOL.val (.word kw))).update (ofString "value", ValueHOL.val (.word vw))
      let entry_s := callEntryStateHOLFinite s cmap_s
      rcases hb_set : evaluateHOLFiniteState entry_s (sourceFnBody Guest.Software.guestFn_htab_set) with
        ⟨r_bs, cpost_s⟩
      have hb_set' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap_s)
          (sourceFnBody Guest.Software.guestFn_htab_set) = (r_bs, cpost_s) := hb_set
      rw [hb_set'] at hc_set
      have hr_bs_ret : ∃ rv_bs, r_bs = some (.returned rv_bs) ∧ s2 = { cpost_s with locals := s.locals } := by
        cases r_bs with
        | none => simp at hc_set
        | some rbi =>
          cases rbi with
          | returned rv_bs =>
            dsimp only at hc_set
            split at hc_set
            · exact ⟨rv_bs, rfl, (Prod.mk.inj hc_set).2.symm⟩
            · simp at hc_set
          | _ => simp at hc_set
      obtain ⟨rv_bs, rfl, hs2_eq⟩ := hr_bs_ret
      obtain ⟨ht0_S, ht0_ndel, ht0_nws32, ht0_nbs32, ht0_nba, ht0_nad, ht0_nts32⟩ :=
        head_frame_addr_role_props_g08 hInvAt
      have hcal_t : entry_s.locals.lookup (ofString "t") = some (.val (.word tw)) := by
        have h1 : ofString "value" ≠ ofString "t" := by decide
        have h2 : ofString "key" ≠ ofString "t" := by decide
        simp [entry_s, cmap_s, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h1, h2, Ne.symm h1, Ne.symm h2]
      have hloc_ts : locN entry_s "t" = memW s (globN s "ev" + 168) := by
        simp [locN, hcal_t, htw_nat]
      have hArg_s : HtabArgWF entry_s := by
        refine ⟨⟨guestInv_congr (s := s) rfl rfl rfl rfl hAs.1, hAs.2⟩, ?_, ?_⟩
        · rw [hloc_ts]
          exact (R16Shards.StateRestoreEpilogue.htabWF_lc s entry_s.locals s.globals entry_s.clock _).mpr
            (hInvAt.1.1.2.1 _ ht0_S).1
        · rw [hloc_ts]
          intro i hi
          exact ((hInvAt.1.1.2.1 _ ht0_S).2 i hi).1
      have hhl_entry : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "htab_set")
          [.val (.word tw), .val (.word kw), .val (.word vw)] =
          some (sourceFnBody Guest.Software.guestFn_htab_set, entry_s.locals, .one) := by
        rw [← hcode]; exact hlook_set
      obtain ⟨params_sp, body_sp, rs_sp, hlk_spec, hfn_spec⟩ := SoloHtabSet.htab_set_spec_proof
      have hbody_eq : ([(ofString "t", ShapeHOL.one), (ofString "key", ShapeHOL.one), (ofString "value", ShapeHOL.one)],
          sourceFnBody Guest.Software.guestFn_htab_set, ShapeHOL.one) = (params_sp, body_sp, rs_sp) :=
        Option.some.inj (SoloHtabSet.lookup_htab_set.symm.trans hlk_spec)
      rcases Prod.mk.inj hbody_eq with ⟨_, hbr⟩
      rcases Prod.mk.inj hbr with ⟨hb_eq, hrs_eq⟩
      subst hb_eq hrs_eq
      have hexit_s := hfn_spec entry_s hcode hArg_s ⟨_, hhl_entry⟩
        (by rw [hb_set]; simp) rv_bs (by rw [hb_set])
      have hbe_s : cpost_s.be = s.be := by
        have hbe0 := R16Shards.evaluate_be_eq entry_s (sourceFnBody Guest.Software.guestFn_htab_set)
        rw [hb_set] at hbe0; exact hbe0
      have hcpost_eq : (evaluateHOLFiniteState entry_s (sourceFnBody Guest.Software.guestFn_htab_set)).2 = cpost_s := by
        rw [hb_set]
      rw [hcpost_eq] at hexit_s
      unfold HtabExit at hexit_s; dsimp only at hexit_s
      rw [hloc_ts] at hexit_s
      obtain ⟨hAp_s, hwf_s, hhdr0_s, _, hhp_s, hfp_s, hfr_s, hg_s⟩ := hexit_s
      obtain ⟨hInv_cs, hch_cs, hR_cs, hunhit_cs⟩ := R16Shards.evmInvAt_of_htab_step
        hAs hInvAt hAp_s hbe_s hwf_s hhdr0_s hhp_s hfp_s hfr_s
        (fun k hk => hg_s k (fun h => hk (by simp at h; simp [h])))
        (by
          have hjn : globN cpost_s "journal_n" = globN entry_s "journal_n" :=
            globN_eq_of_lookup_eq (hg_s (ofString "journal_n") (by decide)).symm
          have hjn_ent : globN entry_s "journal_n" = globN s "journal_n" := rfl
          omega)
        ht0_S ht0_ndel ht0_nws32 ht0_nbs32 ht0_nba ht0_nad (Or.inl ht0_nts32)
      have hcpost_inv : EvmInv cpost_s := ⟨hAp_s, S, hInv_cs⟩
      have hpost_eq : post_c = { cpost_s with locals := post_c.locals, clock := cpost_s.clock } := by
        rw [← hpost_c, hs2_eq]; rfl
      have hch_p : evmChain post_c = evmChain s := by
        rw [hpost_eq]; exact (StateRestoreEpilogue.evmChain_lc cpost_s _ _).trans hch_cs
      have hR_p : evmR post_c = evmR s := by
        have hR1 : evmR post_c = R16Shards.evmR cpost_s := by
          rw [hpost_eq]; exact StateRestoreEpilogue.evmR_lc cpost_s _ _
        exact hR1.trans hR_cs
      have hInv_p : EvmInv post_c := by
        have h := localsFree_evmInv cpost_s post_c.locals cpost_s.clock hcpost_inv
        rwa [← hpost_eq] at h
      refine ⟨hInv_p, hch_p, le_of_eq hR_p, fun k hk => by rw [hpost_eq]; exact hg_s k hk, hR_p, ?_⟩
      intro off hoff hoff8
      have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
        simp [evmChain, evmChainFrom]
      have hu_ev := (hunhit_cs _ hhead).1
      have hmw_cs := R16Shards.memW_eq_of_ivlUnhit hu_ev (a := globN s "ev" + off)
        (by omega) (by dsimp; omega) (by dsimp; omega)
      have hmw_post : memW post_c (globN s "ev" + off) = memW cpost_s (globN s "ev" + off) := by
        rw [hpost_eq]; rfl
      exact hmw_post.trans hmw_cs

private theorem eps_warm_after_charge_head_g08 :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post =>
        GlobalsKept ["heap_ptr"] s post ∧
        evmR post = evmR s ∧
        ∀ off, off + 8 ≤ 280 → off % 8 = 0 →
          memW post (globN s "ev" + off) = memW s (globN s "ev" + off))
      (ofString "warm_after_charge") := by
  refine ⟨_, _, _, lookup_warm_after_charge, ?_⟩
  intro F s hcode hInv _ _ hnt
  have hnc := R16Shards.StateRestoreEpilogue.evaluate_noCatchableRaise warmAccessNcrCallees warmAccessNcrCallees_good
    (sourceFnBody Guest.Software.guestFn_warm_after_charge) (by decide) s hcode
  dsimp only
  refine ⟨?_, fun ⟨ev, hev⟩ => False.elim (hnc (ofString "EvmErr") ev (by decide) hev)⟩
  intro v hv
  have hb : sourceFnBody Guest.Software.guestFn_warm_after_charge =
      .seq
        (.ite (.cmp .equal (.var .local (ofString "c")) (.const (BitVec.ofNat 64 3000)))
          (.call (some (none, none)) (ofString "warm_address") [.var .local (ofString "addr")])
          .skip)
        (.return (.const (BitVec.ofNat 64 0))) := rfl
  rcases hrun : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_warm_after_charge) with ⟨res, post⟩
  rw [hrun] at hv hnt; dsimp only at hv hnt ⊢
  subst hv
  rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hrun
  rcases hcond : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.var .local (ofString "c")) (.const (BitVec.ofNat 64 3000))) with _ | cv
  · rw [hcond] at hrun; simp at hrun
  · rcases cv with ⟨⟨cw⟩⟩ | _ | _
    · rw [hcond] at hrun; dsimp only at hrun
      by_cases hcw0 : cw = 0
      · subst hcw0; simp only [↓reduceIte, evaluateHOLFiniteState_skip] at hrun
        rw [evaluateHOLFiniteState_return] at hrun
        have hev0 : @evalHOLExact 64 F _ s.toExact
            (fun a => Classical.propDecidable (s.memaddrs a)) (.const (BitVec.ofNat 64 0)) =
            some (.val (.word 0)) := rfl
        have hsz0 : sizeOfShapeWithContextHOL s.structs
            (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) ≤ 32 := by
          simp [shapeOfHOLExact]
        rw [hev0] at hrun; dsimp only at hrun; rw [if_pos hsz0] at hrun
        injection hrun with _ hp_eq
        rw [← hp_eq]
        have hInv_el : EvmInv s.emptyLocalsHOLFinite := localsFree_evmInv s _ s.clock hInv
        have hch_el : evmChain s.emptyLocalsHOLFinite = evmChain s := StateRestoreEpilogue.evmChain_lc s _ _
        have hR_el : evmR s.emptyLocalsHOLFinite = evmR s := StateRestoreEpilogue.evmR_lc s _ _
        exact ⟨hInv_el, hch_el, le_of_eq hR_el, fun _ _ => rfl, hR_el, fun _ _ _ => rfl⟩
      · simp only [hcw0, ↓reduceIte] at hrun
        rcases hc_wa : evaluateHOLFiniteState s
            (.call (some (none, none)) (ofString "warm_address") [.var .local (ofString "addr")]) with ⟨r_wa, s1⟩
        rw [hc_wa] at hrun; dsimp only at hrun
        cases r_wa with
        | none =>
          rw [evaluateHOLFiniteState_call] at hc_wa
          rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
              [.var .local (ofString "addr")] with _ | vals
          · rw [hargs] at hc_wa; simp at hc_wa
          · rw [hargs] at hc_wa; dsimp only at hc_wa
            rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "warm_address") vals with _ | ⟨b_wa, cal_wa, rs_wa⟩
            · rw [hl] at hc_wa; simp at hc_wa
            · rw [hl] at hc_wa; dsimp only at hc_wa
              by_cases hz : s.clock = 0
              · rw [if_pos hz] at hc_wa; simp at hc_wa
              · rw [if_neg hz] at hc_wa
                obtain ⟨params_wa, body_wa, ret_wa, hlook_wa, hspec_wa⟩ := eps_warm_address_head_g08
                have hbody_eq := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "warm_address")
                  params_wa body_wa b_wa ret_wa rs_wa vals cal_wa (by rw [hcode]; exact hlook_wa) hl
                subst b_wa
                have hret_eq : rs_wa = ret_wa := by
                  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
                    s.code.lookup (ofString "warm_address") vals body_wa cal_wa rs_wa hl
                  rw [hcode] at hx; simp only [Flapjack.lookupCodeHOLExact, hlook_wa] at hx
                  split at hx
                  · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
                  · cases hx
                subst rs_wa
                have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "warm_address") vals =
                    some (body_wa, cal_wa, ret_wa) := by rwa [← hcode]
                let ce := callEntryStateHOLFinite s cal_wa
                have hInv_ce : EvmInv ce := localsFree_evmInv s cal_wa (s.clock - 1) hInv
                rcases hrun_wa : evaluateHOLFiniteState (callEntryStateHOLFinite s cal_wa) body_wa with ⟨res_wa, cpost⟩
                rw [hrun_wa] at hc_wa
                cases res_wa with
                | none => simp at hc_wa
                | some rw0 =>
                  cases rw0 with
                  | returned v_wa =>
                    dsimp only at hc_wa
                    split at hc_wa
                    · injection hc_wa with _ hs1
                      rw [evaluateHOLFiniteState_return] at hrun
                      have hev0 : @evalHOLExact 64 F _ s1.toExact
                          (fun a => Classical.propDecidable (s1.memaddrs a)) (.const (BitVec.ofNat 64 0)) =
                          some (.val (.word 0)) := rfl
                      have hsz0 : sizeOfShapeWithContextHOL s1.structs
                          (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) ≤ 32 := by
                        simp [shapeOfHOLExact]
                      rw [hev0] at hrun; dsimp only at hrun; rw [if_pos hsz0] at hrun
                      injection hrun with _ hp_eq
                      have hs_wa := (hspec_wa ce hcode hInv_ce trivial ⟨vals, hl_orig⟩
                        (by rw [hrun_wa]; simp)).1 v_wa (by rw [hrun_wa])
                      dsimp only at hs_wa; rw [hrun_wa] at hs_wa
                      obtain ⟨hInv_cp, hch_cp, _, hg_cp, hR_cp, hmw_cp⟩ := hs_wa
                      have hp_cp : post = { cpost with locals := post.locals, clock := cpost.clock } := by
                        rw [← hp_eq, ← hs1]; rfl
                      have hInv_p : EvmInv post := by
                        have h := localsFree_evmInv cpost post.locals cpost.clock hInv_cp
                        rwa [← hp_cp] at h
                      have hch_p : evmChain post = evmChain s := by
                        rw [hp_cp]
                        exact (StateRestoreEpilogue.evmChain_lc cpost _ _).trans (hch_cp.trans (StateRestoreEpilogue.evmChain_lc s _ _))
                      have hR_p : evmR post = evmR s := by
                        rw [hp_cp]
                        exact (StateRestoreEpilogue.evmR_lc cpost _ _).trans (hR_cp.trans (StateRestoreEpilogue.evmR_lc s _ _))
                      refine ⟨hInv_p, hch_p, le_of_eq hR_p, fun k hk => by rw [hp_cp]; exact hg_cp k hk, hR_p, ?_⟩
                      intro off hoff hoff8
                      have hmw1 : memW post (globN s "ev" + off) = memW cpost (globN ce "ev" + off) := by
                        rw [hp_cp]; rfl
                      exact hmw1.trans (hmw_cp off hoff hoff8)
                    · simp at hc_wa
                  | _ => simp at hc_wa
        | some r0 =>
          cases r0 with
          | returned _ =>
            rw [evaluateHOLFiniteState_call] at hc_wa
            rcases hargs2 : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
                [.var .local (ofString "addr")] with _ | vals
            · rw [hargs2] at hc_wa; simp at hc_wa
            · rw [hargs2] at hc_wa; dsimp only at hc_wa
              rcases hl2 : lookupCodeHOLFinite s.code.lookup (ofString "warm_address") vals with _ | ⟨b_wa, cal_wa, rs_wa⟩
              · rw [hl2] at hc_wa; simp at hc_wa
              · rw [hl2] at hc_wa; dsimp only at hc_wa
                split at hc_wa
                · simp at hc_wa
                · rcases hrun2 : evaluateHOLFiniteState (callEntryStateHOLFinite s cal_wa) b_wa with ⟨rw1, _⟩
                  rw [hrun2] at hc_wa
                  cases rw1 with
                  | none => simp at hc_wa
                  | some rw2 =>
                    cases rw2 with
                    | returned _ => dsimp only at hc_wa; split at hc_wa <;> simp at hc_wa
                    | _ => simp at hc_wa
          | _ => simp at hrun
    · rw [hcond] at hrun; simp at hrun
    · rw [hcond] at hrun; simp at hrun

private theorem extcode_words_base_pos_g08 (accw w : BitVec 64)
    (hacc : accw.toNat = 100 ∨ accw.toNat = 3000) (hw : w.toNat < 2 ^ 59) :
    0 < (accw + (100#64 + 3#64 * w)).toNat := by
  have hm : (3#64 * w).toNat = 3 * w.toNat := by
    rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (by change 3 * w.toNat < 2 ^ 64; omega)]
    rfl
  have ha1 : (100#64 + 3#64 * w).toNat = 100 + 3 * w.toNat := by
    rw [BitVec.toNat_add, hm, Nat.mod_eq_of_lt (by change 100 + 3 * w.toNat < 2 ^ 64; omega)]
    rfl
  have hacc_le : accw.toNat ≤ 3000 := by rcases hacc with h | h <;> omega
  have hacc_pos : 100 ≤ accw.toNat := by rcases hacc with h | h <;> omega
  have ha2 : (accw + (100#64 + 3#64 * w)).toNat = accw.toNat + (100 + 3 * w.toNat) := by
    rw [BitVec.toNat_add, ha1, Nat.mod_eq_of_lt (by change accw.toNat + (100 + 3 * w.toNat) < 2 ^ 64; omega)]
  rw [ha2]; omega

private def copyExtWriteProg_g08 : ProgHOL 64 :=
  .decCall (ofString "ms") .one (ofString "sat_word") [.var .local (ofString "mstart")]
    (.decCall (ofString "cs") .one (ofString "sat_word") [.var .local (ofString "cstart")]
      (.call (some (none, none)) (ofString "buffer_read")
        [.rfield 0 (.var .local (ofString "code")),
         .rfield 1 (.var .local (ofString "code")),
         .var .local (ofString "cs"), .var .local (ofString "n"),
         .op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]),
           .var .local (ofString "ms")]]))

private theorem copy_extcode_write_eff_g08 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (stVal csVal szVal : ValueHOL 64) (buf buflen : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hInv : EvmInv s)
    (hst_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true)
    (hcs_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact csVal) = true)
    (hst : s.locals.lookup (ofString "mstart") = some stVal)
    (hcs : s.locals.lookup (ofString "cstart") = some csVal)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word (satValue_g08 szVal))))
    (hcode_loc : s.locals.lookup (ofString "code") = some (.rStruct [.val (.word buf), .val (.word buflen)]))
    (hnz : satValue_g08 szVal ≠ 0#64)
    (hcov : (satValue_g08 stVal).toNat + (satValue_g08 szVal).toNat ≤ memW s (globN s "ev" + 32))
    (hnt : (evaluateHOLFiniteState s copyExtWriteProg_g08).1 ≠ some .timeOut) :
    CopyEff_g08 s copyExtWriteProg_g08
      [(memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))] := by
  dsimp only [copyExtWriteProg_g08] at hnt ⊢
  refine decCall_sat_copy_eff_g08 s _ _ stVal _ _ hc hst_sh hst ?_ hnt
  intro mid1 hlf1 hl1 hnt1
  have hcs1 : mid1.locals.lookup (ofString "cstart") = some csVal := by
    simp [hl1, HolFiniteMapExact.lookup_update, FUPDATE, hcs,
      show ofString "ms" ≠ ofString "cstart" by decide]
  have hc1 : mid1.code = originalRuntimeCode := by rw [hlf1]; exact hc
  refine decCall_sat_copy_eff_g08 mid1 _ _ csVal _ _ hc1 hcs_sh hcs1 ?_ hnt1
  intro mid2 hlf2 hl2 hnt2
  have hInv2 : EvmInv mid2 := by
    rw [hlf2, hlf1]
    exact localsFree_evmInv s _ _ hInv
  have hc2 : mid2.code = originalRuntimeCode := by rw [hlf2, hlf1]; exact hc
  have hma2 : mid2.memaddrs = ordinaryDomain := hInv2.1.1.memaddrs
  have hms2 : mid2.locals.lookup (ofString "ms") = some (.val (.word (satValue_g08 stVal))) := by
    simp [hl2, hl1, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "cs" ≠ ofString "ms" by decide]
  have hcs2 : mid2.locals.lookup (ofString "cs") = some (.val (.word (satValue_g08 csVal))) := by
    simp [hl2, HolFiniteMapExact.lookup_update, FUPDATE]
  have hn2 : mid2.locals.lookup (ofString "n") = some (.val (.word (satValue_g08 szVal))) := by
    simp [hl2, hl1, HolFiniteMapExact.lookup_update, FUPDATE, hn,
      show ofString "cs" ≠ ofString "n" by decide, show ofString "ms" ≠ ofString "n" by decide]
  have hcd2 : mid2.locals.lookup (ofString "code") = some (.rStruct [.val (.word buf), .val (.word buflen)]) := by
    simp [hl2, hl1, HolFiniteMapExact.lookup_update, FUPDATE, hcode_loc,
      show ofString "cs" ≠ ofString "code" by decide, show ofString "ms" ≠ ofString "code" by decide]
  have hbuf2 : @evalHOLExact 64 F _ mid2.toExact (fun a => Classical.propDecidable (mid2.memaddrs a))
      (.rfield 0 (.var .local (ofString "code"))) = some (.val (.word buf)) := by
    simp [evalHOLExact, hcd2]
  have hbl2 : @evalHOLExact 64 F _ mid2.toExact (fun a => Classical.propDecidable (mid2.memaddrs a))
      (.rfield 1 (.var .local (ofString "code"))) = some (.val (.word buflen)) := by
    simp [evalHOLExact, hcd2]
  have hmem : ∀ off : Nat, memW mid2 (globN mid2 "ev" + off) = memW s (globN s "ev" + off) := by
    intro off; rw [hlf2, hlf1]; rfl
  have hcov2 : (satValue_g08 stVal).toNat + (satValue_g08 szVal).toNat ≤ memW mid2 (globN mid2 "ev" + 32) := by
    rw [hmem]; exact hcov
  have hnpos : 0 < (satValue_g08 szVal).toNat := by
    have hne : (satValue_g08 szVal).toNat ≠ 0 := by
      intro h; apply hnz; exact BitVec.eq_of_toNat_eq h
    omega
  obtain ⟨base, hbase, hout⟩ := eval_head_mem_plus_local_g08 mid2 hInv2 "ms" (satValue_g08 stVal) hms2
  have hbounds := head_mem_store_address_g08 mid2 hInv2 base (satValue_g08 stVal)
    (satValue_g08 szVal).toNat hbase hnpos hcov2
  have hcap := head_mem_cap_lt_g08 mid2 hInv2
  have hh := eval_call_buffer_read_bre mid2
    (.rfield 0 (.var .local (ofString "code"))) (.rfield 1 (.var .local (ofString "code")))
    (.var .local (ofString "cs")) (.var .local (ofString "n"))
    (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "ms")])
    buf buflen (satValue_g08 csVal) (satValue_g08 szVal) (base + satValue_g08 stVal)
    [(memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))]
    hc2 hma2 hbuf2 hbl2 hcs2 hn2 hout (by omega)
    (fun _ => ⟨_, List.mem_singleton.mpr rfl, by rw [← hmem 24]; exact hbounds.2.1,
      by rw [← hmem 24, ← hmem 40]; exact hbounds.2.2⟩) hnt2
  exact ⟨fun h => (hh.1 h).1, hh.2⟩

private def copyExtTailProg_g08 : ProgHOL 64 :=
  .seq (.ite (.cmp .notEqual (.var .local (ofString "n")) (.const 0#64)) copyExtWriteProg_g08 .skip)
    copyFinishProg_g08

private def copyExtArgs_g08 (stVal csVal szVal : ValueHOL 64) (addrw : BitVec 64) :
    List (MlS × ValueHOL 64) :=
  [(ofString "n", .val (.word (satValue_g08 szVal))),
   (ofString "size", szVal), (ofString "cstart", csVal), (ofString "mstart", stVal),
   (ofString "addr", .val (.word addrw))]

private theorem comb2_value_of_shape_g08 {v : ValueHOL 64}
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

private theorem copy_ext_tail_run_g08 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (stVal csVal szVal : ValueHOL 64) (addrw buf buflen : BitVec 64)
    (hst_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true)
    (hcs_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact csVal) = true) :
    HandlerRun s0 (fun t =>
      CopyLocals_g08 ((ofString "code", .rStruct [.val (.word buf), .val (.word buflen)]) ::
        copyExtArgs_g08 stVal csVal szVal addrw) t.locals ∧
      (satValue_g08 szVal ≠ 0#64 →
        (satValue_g08 stVal).toNat + (satValue_g08 szVal).toNat ≤ memW t (globN t "ev" + 32))) true
      copyExtTailProg_g08 := by
  have hfinish : HandlerRun s0 (fun _ => True) true copyFinishProg_g08 :=
    HandlerRun.seq_call_simple eps_pc_add (HandlerRun.ret _)
  refine HandlerRun.seq_ite_copy_g08 ?_ ?_
  · refine HandlerRun.seq_head_mem_eff_g08 ?_ hfinish
    intro t hc hInv ⟨⟨hK, hcov⟩, w, hw, hwne⟩ hnt
    have hn := hK (ofString "n", .val (.word (satValue_g08 szVal))) (by simp [copyExtArgs_g08])
    have hnz : satValue_g08 szVal ≠ 0#64 := by
      intro hz
      have hev : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.cmp .notEqual (.var .local (ofString "n")) (.const 0#64)) = some (.val (.word 0#64)) := by
        simp [evalHOLExact, hn, hz, Compiler.Encoders.Asm.wordCmpHOL]
      rw [hev] at hw
      have hw0 : w = 0#64 := by simpa using hw.symm
      exact hwne hw0
    exact copy_extcode_write_eff_g08 t stVal csVal szVal buf buflen hc hInv hst_sh hcs_sh
      (hK (ofString "mstart", stVal) (by simp [copyExtArgs_g08]))
      (hK (ofString "cstart", csVal) (by simp [copyExtArgs_g08]))
      hn
      (hK (ofString "code", .rStruct [.val (.word buf), .val (.word buflen)]) (by simp))
      hnz (hcov hnz) hnt
  · exact HandlerRun.seq_skip (HandlerRun.weaken (fun _ _ _ => trivial) hfinish)

private theorem decCall_ext_code_of_run_g08 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (h_ext_code_of : ExtCodeOfHeadSpec)
    (stVal csVal szVal : ValueHOL 64) (addrw : BitVec 64)
    (hst_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true)
    (hcs_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact csVal) = true) :
    HandlerRun s0 (fun t =>
      CopyLocals_g08 (copyExtArgs_g08 stVal csVal szVal addrw) t.locals ∧
      (satValue_g08 szVal ≠ 0#64 →
        (satValue_g08 stVal).toNat + (satValue_g08 szVal).toNat ≤ memW t (globN t "ev" + 32))) true
      (.decCall (ofString "code") (.comb [.one, .one]) (ofString "ext_code_of")
        [.var .local (ofString "addr")] copyExtTailProg_g08) := by
  intro t hc hInv hlen hR ⟨hK, hcov⟩ hnt
  obtain ⟨params, body, retShape, hlook, hspec⟩ := h_ext_code_of
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
      [.var .local (ofString "addr")] with _ | values
  · exact opDispatchPost_error s0 t
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup (ofString "ext_code_of") values with _ | ⟨body', callee, ret'⟩
    · exact opDispatchPost_error s0 t
    · simp only [hl] at hnt ⊢
      by_cases hz : t.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hbody_eq : body' = body :=
          lookupCodeHOLFinite_installed_body t.code.lookup (ofString "ext_code_of") params body body'
            retShape ret' values callee (by rw [hc]; exact hlook) hl
        subst body'
        have hret_eq : ret' = retShape := by
          have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
            t.code.lookup (ofString "ext_code_of") values body callee ret' hl
          rw [hc] at hx; simp only [Flapjack.lookupCodeHOLExact, hlook] at hx
          split at hx
          · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
          · cases hx
        subst ret'
        have hInv_ce : EvmInv (callEntryStateHOLFinite t callee) :=
          localsFree_evmInv t callee (t.clock - 1) hInv
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "ext_code_of") values =
            some (body, callee, retShape) := by rwa [← hc]
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite t callee) body).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body with ⟨res, cpost⟩
        simp only [hrun] at hnt hmeta ⊢
        change cpost.code = t.code at hmeta
        have hc_ce := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
        have hQ (hsafe : res ≠ some .timeOut) :
            (∀ v, res = some (.returned v) →
              EvmInv cpost ∧ evmChain cpost = evmChain (callEntryStateHOLFinite t callee) ∧
              evmR cpost ≤ evmR (callEntryStateHOLFinite t callee) ∧
              (GlobalsKept ["heap_ptr", "scratch_ptr"] (callEntryStateHOLFinite t callee) cpost ∧
               evmR cpost = evmR (callEntryStateHOLFinite t callee) ∧
               ∀ off, off + 8 ≤ 280 → off % 8 = 0 →
                 memW cpost (globN (callEntryStateHOLFinite t callee) "ev" + off) =
                   memW (callEntryStateHOLFinite t callee) (globN (callEntryStateHOLFinite t callee) "ev" + off))) ∧
            (IsEvmErr res →
              EvmInv cpost ∧ evmChain cpost = evmChain (callEntryStateHOLFinite t callee) ∧
              evmR cpost ≤ evmR (callEntryStateHOLFinite t callee)) := by
          have hs := hspec (callEntryStateHOLFinite t callee) hc hInv_ce trivial ⟨values, hl_orig⟩ (by rw [hrun]; exact hsafe)
          dsimp only at hs; rw [hrun] at hs; exact hs
        cases res with
        | none => exact opDispatchPost_error s0 cpost
        | some r0 =>
          cases r0 with
          | timeOut => simp at hnt
          | returned v =>
            dsimp only at hnt ⊢
            split
            · rename_i hsh_ok
              rw [if_pos hsh_ok] at hnt
              have hsh_comb : shapeEqHOL (shapeOfHOLExact v) (.comb [.one, .one]) = true := by
                have hb_and := Bool.and_eq_true_iff.mp hsh_ok
                exact hb_and.1
              obtain ⟨buf, buflen, rfl⟩ := comb2_value_of_shape_g08 hsh_comb
              obtain ⟨hInv_cp, hch_cp, hR_cp, hg_cp, _, hmw_cp⟩ := (hQ (by simp)).1 _ rfl
              let resumed := setVarHOLFinite (ofString "code")
                (.rStruct [.val (.word buf), .val (.word buflen)]) { cpost with locals := t.locals }
              have hcode_res : resumed.code = originalRuntimeCode := hmeta.trans hc
              have hInv_res : EvmInv resumed := localsFree_evmInv cpost resumed.locals cpost.clock hInv_cp
              have hc_res := evm_congr (s := cpost) (t := resumed) rfl rfl
              have hlen_res : (evmChain resumed).length = (evmChain s0).length := by
                rw [hc_res.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              have hR_res : evmR resumed < evmR s0 := by
                rw [hc_res.2.1]; rw [hc_ce.2.1] at hR_cp
                simp only [↓reduceIte] at hR; omega
              have hgev : globN resumed "ev" = globN t "ev" :=
                globN_eq_of_lookup_eq (hg_cp (ofString "ev") (by decide)).symm
              have hmem32 : memW resumed (globN resumed "ev" + 32) = memW t (globN t "ev" + 32) := by
                rw [hgev]
                exact hmw_cp 32 (by omega) (by omega)
              have hK_res : CopyLocals_g08
                  ((ofString "code", .rStruct [.val (.word buf), .val (.word buflen)]) ::
                    copyExtArgs_g08 stVal csVal szVal addrw) resumed.locals := by
                apply copyLocals_cons_update_g08 _ t.locals _ _ ?_ hK
                intro kv hk
                simp only [copyExtArgs_g08, List.mem_cons, List.not_mem_nil, or_false] at hk
                rcases hk with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
              have hb := copy_ext_tail_run_g08 s0 stVal csVal szVal addrw buf buflen hst_sh hcs_sh
                resumed hcode_res hInv_res hlen_res (by simp [hR_res])
                ⟨hK_res, fun hn => by rw [hmem32]; exact hcov hn⟩ (by simpa [resumed] using hnt)
              exact opDispatchPost_congr_lc rfl rfl rfl hb
            · exact opDispatchPost_error s0 cpost
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨hInv_cp, hch_cp, hR_cp⟩ := (hQ (by simp)).2 ⟨ev, rfl⟩
              have hInv_el : EvmInv cpost.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost _ cpost.clock hInv_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              refine ⟨?_, fun _ => ⟨hInv_el, ?_, ?_⟩⟩
              · rintro ⟨_, h⟩; cases h
              · rw [hc_el.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              · simp only [↓reduceIte] at hR
                rw [hc_el.2.1]; rw [hc_ce.2.1] at hR_cp; omega
            · refine opDispatchPost_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => exact opDispatchPost_error s0 cpost
          | «continue» => exact opDispatchPost_error s0 cpost
          | finalFfi _ =>
            refine opDispatchPost_other (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => exact opDispatchPost_error s0 cpost.emptyLocalsHOLFinite

private def copyExtCostProg_g08 : ProgHOL 64 :=
  .decCall (ofString "x") (.comb [.one, .one]) (ofString "extend_memory_cost1")
    [.var .local (ofString "mstart"), .var .local (ofString "size")]
    (.decCall (ofString "acc") .one (ofString "access_gas_cost") [.var .local (ofString "addr")]
      (.decCall (ofString "cost") .one (ofString "add_sat")
        [.op .add [.var .local (ofString "acc"), .const 100#64,
           .panop .mul [.const 3#64, .var .local (ofString "w")]],
         .rfield 0 (.var .local (ofString "x"))]
        (.seq (.call (some (none, none)) (ofString "charge_gas") [.var .local (ofString "cost")])
          (.seq (.call (some (none, none)) (ofString "warm_after_charge")
              [.var .local (ofString "addr"), .var .local (ofString "acc")])
            (.seq (.call (some (none, none)) (ofString "extend_memory") [.rfield 1 (.var .local (ofString "x"))])
              (.decCall (ofString "code") (.comb [.one, .one]) (ofString "ext_code_of")
                [.var .local (ofString "addr")] copyExtTailProg_g08))))))

private theorem copy_ext_cost_phase_run_g08 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (h_ext_code_of : ExtCodeOfHeadSpec)
    (stVal csVal szVal : ValueHOL 64) (addrw ww : BitVec 64)
    (hst_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true)
    (hcs_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact csVal) = true)
    (hsz_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact szVal) = true)
    (hwb : ww.toNat < 2 ^ 59) :
    HandlerRun s0 (fun t => HeadMemAligned t ∧ CopyLocals_g08
      ((ofString "w", .val (.word ww)) :: copyExtArgs_g08 stVal csVal szVal addrw) t.locals) false
      copyExtCostProg_g08 := by
  let args0 := (ofString "w", ValueHOL.val (.word ww)) :: copyExtArgs_g08 stVal csVal szVal addrw
  refine HandlerRun.decCall
    (Q := fun t => HeadMemAligned t ∧ CopyLocals_g08 args0 t.locals ∧
      ∃ cw ebw : BitVec 64,
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        (ebw = 0#64 ∨
          (memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
           (memW t (globN t "ev" + 32) + ebw.toNat) % 8 = 0 ∧
           memW t (globN t "ev" + 24) + memW t (globN t "ev" + 40) = globN t "frame_mem_ptr")) ∧
        (cw.toNat < 2 ^ 64 - 1 → satValue_g08 szVal ≠ 0#64 →
          (satValue_g08 stVal).toNat + (satValue_g08 szVal).toNat ≤ memW t (globN t "ev" + 32) + ebw.toNat))
    eps_extend_memory_cost1_copy_cov_g08
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t values _ callee _ v cpost _ ⟨hHM, hK⟩ hargs hl_orig _ _ hQc => by
      obtain ⟨hlf, cw, ebw, hv, heb_bounds, hcov_ce⟩ := hQc
      subst hv
      obtain ⟨v1, v2, rfl, _, _, hcal_st, hcal_sz⟩ := extend_memory_cost1_two_args_lookup_g08 hl_orig
      rw [evalListHOLFinite_eq_toExact] at hargs
      have hst := hK (ofString "mstart", stVal) (by simp [args0, copyExtArgs_g08])
      have hsz := hK (ofString "size", szVal) (by simp [args0, copyExtArgs_g08])
      simp only [evalListHOLExact, evalHOLExact, hst, hsz, Option.some.injEq, List.cons.injEq] at hargs
      rcases hargs with ⟨rfl, rfl, _⟩
      let ce := callEntryStateHOLFinite t callee
      have hHM_ce : HeadMemAligned ce := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      have hHM_cp : HeadMemAligned cpost :=
        headMemAligned_congr_head_only (by rw [hlf]) (fun off _ => by unfold memW; rw [hlf]) hHM_ce
      let res := setVarHOLFinite (ofString "x") (.rStruct [.val (.word cw), .val (.word ebw)]) { cpost with locals := t.locals }
      have hHM_res : HeadMemAligned res := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp
      have hmem32_eq : memW res (globN res "ev" + 32) = memW ce (globN ce "ev" + 32) := by
        have hg : globN res "ev" = globN ce "ev" := globN_eq_of_lookup_eq (by change cpost.globals.lookup _ = ce.globals.lookup _; rw [hlf])
        have hm : res.memory = ce.memory := by change cpost.memory = ce.memory; rw [hlf]
        rw [hg]; unfold memW; rw [hm]
      have hK_res : CopyLocals_g08 args0 res.locals := by
        apply copyLocals_update_g08 args0 t.locals _ _ ?_ hK
        intro kv hk
        simp only [args0, copyExtArgs_g08, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
      refine ⟨hHM_res, hK_res, cw, ebw,
        by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], ?_, ?_⟩
      · rcases heb_bounds with rfl | ⟨before, after, haft_lt, haft_mod, hbef_lt, heb_sub, hbef_eq⟩
        · exact Or.inl rfl
        · right
          have hbef : before = memW ce (globN ce "ev" + 32) := hbef_eq hHM_ce.1
          have hsum : memW res (globN res "ev" + 32) + ebw.toNat = after := by
            rw [hmem32_eq, ← hbef]; omega
          rw [hsum]
          exact ⟨haft_lt, by omega, hHM_res.2⟩
      · intro hcw_lt hn
        rw [hmem32_eq]
        exact hcov_ce stVal szVal hcal_st hst_sh hcal_sz hsz_sh hn hcw_lt hHM_ce.1)
    ?_
  refine HandlerRun.decCall
    (Q := fun t => HeadMemAligned t ∧ CopyLocals_g08 args0 t.locals ∧
      ∃ accw cw ebw : BitVec 64,
        t.locals.lookup (ofString "acc") = some (.val (.word accw)) ∧
        (accw.toNat = 100 ∨ accw.toNat = 3000) ∧
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        (ebw = 0#64 ∨
          (memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
           (memW t (globN t "ev" + 32) + ebw.toNat) % 8 = 0 ∧
           memW t (globN t "ev" + 24) + memW t (globN t "ev" + 40) = globN t "frame_mem_ptr")) ∧
        (cw.toNat < 2 ^ 64 - 1 → satValue_g08 szVal ≠ 0#64 →
          (satValue_g08 stVal).toNat + (satValue_g08 szVal).toNat ≤ memW t (globN t "ev" + 32) + ebw.toNat))
    eps_access_gas_cost_bounds
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ callee _ v cpost _ ⟨hHM, hK, cw, ebw, hx, heb_cond, hcov_imp⟩ _ _ _ _ hQc => by
      obtain ⟨hlf, accw, hv, hacc_b⟩ := hQc
      subst hv
      let ce := callEntryStateHOLFinite t callee
      have hHM_ce : HeadMemAligned ce := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      have hHM_cp : HeadMemAligned cpost :=
        headMemAligned_congr_head_only (by rw [hlf]) (fun off _ => by unfold memW; rw [hlf]) hHM_ce
      let res := setVarHOLFinite (ofString "acc") (.val (.word accw)) { cpost with locals := t.locals }
      have hHM_res : HeadMemAligned res := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp
      have hmem32_eq : memW res (globN res "ev" + 32) = memW t (globN t "ev" + 32) := by
        have hg : globN res "ev" = globN t "ev" := globN_eq_of_lookup_eq (by change cpost.globals.lookup _ = t.globals.lookup _; rw [hlf]; rfl)
        have hm : res.memory = t.memory := by change cpost.memory = t.memory; rw [hlf]; rfl
        rw [hg]; unfold memW; rw [hm]
      have hK_res : CopyLocals_g08 args0 res.locals := by
        apply copyLocals_update_g08 args0 t.locals _ _ ?_ hK
        intro kv hk
        simp only [args0, copyExtArgs_g08, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
      refine ⟨hHM_res, hK_res, accw, cw, ebw,
        by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
        hacc_b,
        by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hx,
          show ofString "acc" ≠ ofString "x" by decide], ?_, ?_⟩
      · rcases heb_cond with rfl | ⟨hlt37, hmod8, _⟩
        · exact Or.inl rfl
        · right; rw [hmem32_eq]; exact ⟨hlt37, hmod8, hHM_res.2⟩
      · intro hcw_lt hn; rw [hmem32_eq]; exact hcov_imp hcw_lt hn)
    ?_
  refine HandlerRun.decCall
    (Q := fun t => HeadMemAligned t ∧ CopyLocals_g08 args0 t.locals ∧
      ∃ totw bw cw ebw : BitVec 64,
        t.locals.lookup (ofString "cost") = some (.val (.word totw)) ∧
        0 < totw.toNat ∧
        (totw.toNat < 2 ^ 64 - 1 → totw.toNat = bw.toNat + cw.toNat) ∧
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        (ebw = 0#64 ∨
          (memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
           (memW t (globN t "ev" + 32) + ebw.toNat) % 8 = 0 ∧
           memW t (globN t "ev" + 24) + memW t (globN t "ev" + 40) = globN t "frame_mem_ptr")) ∧
        (cw.toNat < 2 ^ 64 - 1 → satValue_g08 szVal ≠ 0#64 →
          (satValue_g08 stVal).toNat + (satValue_g08 szVal).toNat ≤ memW t (globN t "ev" + 32) + ebw.toNat))
    eps_add_sat_pos_exact_g08
    (fun t values b_as callee rs_as hc _ ⟨_, hK, accw, cw, ebw, hacc, hacc_b, hx, _⟩ hargs hl => by
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "add_sat") values =
          some (b_as, callee, rs_as) := by rwa [← hc]
      obtain ⟨_, _, w1, w2, rfl, hw1, hw2⟩ := two_word_arg_lookup (by decide) lookup_add_sat hl_orig
      have hw := hK (ofString "w", .val (.word ww)) (by simp [args0])
      have hargs_ok : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.op .add [.var .local (ofString "acc"), .const 100#64, .panop .mul [.const 3#64, .var .local (ofString "w")]],
           .rfield 0 (.var .local (ofString "x"))] =
          some [.val (.word (accw + (100#64 + 3#64 * ww))), .val (.word cw)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hacc, hw, hx, wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord]
      rw [hargs_ok] at hargs
      injection hargs with hvs
      rcases List.cons.inj hvs with ⟨hw1_eq, hvs'⟩
      rcases List.cons.inj hvs' with ⟨hw2_eq, _⟩
      injection hw1_eq with hw1'; injection hw1' with hw1''; subst hw1''
      injection hw2_eq with hw2'; injection hw2' with hw2''; subst hw2''
      exact ⟨accw + (100#64 + 3#64 * ww), cw, hw1, hw2, extcode_words_base_pos_g08 accw ww hacc_b hwb⟩)
    (fun t values _ callee _ v cpost _ ⟨hHM, hK, accw, cw, ebw, hacc, hacc_b, hx, heb_cond, hcov_imp⟩ hargs hl_orig _ _ hQc => by
      obtain ⟨hlf, totw, hv, hpos, htot_ex⟩ := hQc
      subst hv
      obtain ⟨_, _, w1, w2, rfl, hw1, hw2⟩ := two_word_arg_lookup (by decide) lookup_add_sat hl_orig
      have hw := hK (ofString "w", .val (.word ww)) (by simp [args0])
      have hargs_ok : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.op .add [.var .local (ofString "acc"), .const 100#64, .panop .mul [.const 3#64, .var .local (ofString "w")]],
           .rfield 0 (.var .local (ofString "x"))] =
          some [.val (.word (accw + (100#64 + 3#64 * ww))), .val (.word cw)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hacc, hw, hx, wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord]
      rw [hargs_ok] at hargs
      injection hargs with hvs
      rcases List.cons.inj hvs with ⟨hw1_eq, hvs'⟩
      rcases List.cons.inj hvs' with ⟨hw2_eq, _⟩
      injection hw1_eq with hw1'; injection hw1' with hw1''; subst hw1''
      injection hw2_eq with hw2'; injection hw2' with hw2''; subst hw2''
      let ce := callEntryStateHOLFinite t callee
      have hHM_ce : HeadMemAligned ce := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      have hHM_cp : HeadMemAligned cpost :=
        headMemAligned_congr_head_only (by rw [hlf]) (fun off _ => by unfold memW; rw [hlf]) hHM_ce
      let res := setVarHOLFinite (ofString "cost") (.val (.word totw)) { cpost with locals := t.locals }
      have hHM_res : HeadMemAligned res := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp
      have hmem32_eq : memW res (globN res "ev" + 32) = memW t (globN t "ev" + 32) := by
        have hg : globN res "ev" = globN t "ev" := globN_eq_of_lookup_eq (by change cpost.globals.lookup _ = t.globals.lookup _; rw [hlf]; rfl)
        have hm : res.memory = t.memory := by change cpost.memory = t.memory; rw [hlf]; rfl
        rw [hg]; unfold memW; rw [hm]
      have hK_res : CopyLocals_g08 args0 res.locals := by
        apply copyLocals_update_g08 args0 t.locals _ _ ?_ hK
        intro kv hk
        simp only [args0, copyExtArgs_g08, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
      refine ⟨hHM_res, hK_res, totw, accw + (100#64 + 3#64 * ww), cw, ebw,
        by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
        hpos, htot_ex _ _ hw1 hw2,
        by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hx,
          show ofString "cost" ≠ ofString "x" by decide], ?_, ?_⟩
      · rcases heb_cond with rfl | ⟨hlt37, hmod8, _⟩
        · exact Or.inl rfl
        · right; rw [hmem32_eq]; exact ⟨hlt37, hmod8, hHM_res.2⟩
      · intro hcw_lt hn; rw [hmem32_eq]; exact hcov_imp hcw_lt hn)
    ?_
  refine HandlerRun.seq_charge_copy_g08
    (Q := fun t => CopyLocals_g08 args0 t.locals ∧ CopyExpand_g08 stVal szVal t)
    (fun t w hw _ ⟨_, _, totw, _, _, _, htot, hpos, _⟩ => by
      change t.locals.lookup (ofString "cost") = some (.val (.word w)) at hw
      rw [htot] at hw; injection hw with hw'; injection hw' with hw''; injection hw'' with hweq; subst hweq
      exact hpos)
    (fun t amtw cpost hw hamt_lt _ ⟨hHM, hK, totw, bw, cw, ebw, htot, _, htot_ex, hx, heb_cond, hcov_imp⟩ _ hglob_cp _ hmem_head_cp => by
      change t.locals.lookup (ofString "cost") = some (.val (.word amtw)) at hw
      rw [htot] at hw; injection hw with hw'; injection hw' with hw''; injection hw'' with hweq; subst hweq
      have htot_sum := htot_ex hamt_lt
      have hcw_lt : cw.toNat < 2 ^ 64 - 1 := by omega
      have hHM_cp : HeadMemAligned cpost := headMemAligned_congr_head_only hglob_cp hmem_head_cp hHM
      let res : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
      have hHM_res : HeadMemAligned res := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp
      have hmem32_eq : memW res (globN res "ev" + 32) = memW t (globN t "ev" + 32) := by
        have hg : globN res "ev" = globN t "ev" := globN_eq_of_lookup_eq (by change cpost.globals.lookup _ = t.globals.lookup _; rw [hglob_cp])
        rw [hg]; exact hmem_head_cp 32 (by simp)
      refine ⟨hK, cw, ebw, hx, ?_, ?_⟩
      · rcases heb_cond with rfl | ⟨hlt37, hmod8, _⟩
        · exact Or.inl rfl
        · right; rw [hmem32_eq]; exact ⟨hlt37, hmod8, hHM_res.2⟩
      · intro hn; rw [hmem32_eq]; exact hcov_imp hcw_lt hn)
    ?_
  refine HandlerRun.seq_call
    (Q := fun t => CopyLocals_g08 args0 t.locals ∧ CopyExpand_g08 stVal szVal t)
    eps_warm_after_charge_head_g08
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ callee _ _ cpost _ ⟨hK, cw, ebw, hx, heb_cond, hcov⟩ _ _ _ _ ⟨hg_cp, _, hmw_cp⟩ => by
      let res : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
      have hgev : globN res "ev" = globN t "ev" :=
        globN_eq_of_lookup_eq (hg_cp (ofString "ev") (by decide)).symm
      have hgfp : globN res "frame_mem_ptr" = globN t "frame_mem_ptr" :=
        globN_eq_of_lookup_eq (hg_cp (ofString "frame_mem_ptr") (by decide)).symm
      have hmem24 : memW res (globN res "ev" + 24) = memW t (globN t "ev" + 24) := by
        rw [hgev]; exact hmw_cp 24 (by omega) (by omega)
      have hmem32 : memW res (globN res "ev" + 32) = memW t (globN t "ev" + 32) := by
        rw [hgev]; exact hmw_cp 32 (by omega) (by omega)
      have hmem40 : memW res (globN res "ev" + 40) = memW t (globN t "ev" + 40) := by
        rw [hgev]; exact hmw_cp 40 (by omega) (by omega)
      refine ⟨hK, cw, ebw, hx, ?_, ?_⟩
      · rcases heb_cond with rfl | ⟨hlt37, hmod8, hfm⟩
        · exact Or.inl rfl
        · right
          rw [hmem32, hmem24, hmem40, hgfp]
          exact ⟨hlt37, hmod8, hfm⟩
      · intro hn; rw [hmem32]; exact hcov hn)
    ?_
  refine copy_extend_phase_run_g08 s0 stVal szVal (CopyLocals_g08 args0) ?_
  refine HandlerRun.weaken ?_ (decCall_ext_code_of_run_g08 s0 h_ext_code_of stVal csVal szVal addrw hst_sh hcs_sh)
  intro t _ ⟨hK, hcov⟩
  exact ⟨fun kv hk => hK kv (List.mem_cons_of_mem _ hk), hcov⟩

private def copyExtNumsProg_g08 : ProgHOL 64 :=
  .decCall (ofString "n") .one (ofString "sat_word") [.var .local (ofString "size")]
    (.decCall (ofString "w") .one (ofString "words_of") [.var .local (ofString "n")] copyExtCostProg_g08)

private theorem copy_ext_after_pops_run_g08 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (h_ext_code_of : ExtCodeOfHeadSpec)
    (stVal csVal szVal : ValueHOL 64) (addrw : BitVec 64)
    (hst_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true)
    (hcs_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact csVal) = true)
    (hsz_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact szVal) = true) :
    HandlerRun s0 (fun t => HeadMemAligned t ∧
      CopyLocals_g08 (copyExtArgs_g08 stVal csVal szVal addrw).tail t.locals) false
      copyExtNumsProg_g08 := by
  refine HandlerRun.decCall_sat_copy_g08 szVal hsz_sh
    (fun t ⟨_, hK⟩ => copyLocals_get_g08 hK (by simp [copyExtArgs_g08]))
    (Q := fun t => HeadMemAligned t ∧ CopyLocals_g08 (copyExtArgs_g08 stVal csVal szVal addrw) t.locals)
    ?_ ?_
  · intro t cpost ⟨hHM, hK⟩ hlf
    have hHM_cp : HeadMemAligned cpost := headMemAligned_congr_head_only
      (by rw [hlf]) (fun off _ => by unfold memW; rw [hlf]) hHM
    refine ⟨headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp, ?_⟩
    change CopyLocals_g08
      ((ofString "n", .val (.word (satValue_g08 szVal))) :: (copyExtArgs_g08 stVal csVal szVal addrw).tail)
      (t.locals.update (ofString "n", .val (.word (satValue_g08 szVal))))
    apply copyLocals_cons_update_g08 _ _ _ _ _ hK
    intro kv hk
    simp only [copyExtArgs_g08, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> dsimp only <;> decide
  · refine HandlerRun.decCall
      (Q := fun t => HeadMemAligned t ∧ ∃ ww : BitVec 64, ww.toNat < 2 ^ 59 ∧
        CopyLocals_g08 ((ofString "w", .val (.word ww)) :: copyExtArgs_g08 stVal csVal szVal addrw) t.locals)
      eps_words_of_lt (fun _ _ _ _ _ _ _ _ _ _ => trivial) ?_ ?_
    · intro t _ _ callee _ v cpost _ ⟨hHM, hK⟩ _ _ _ _ hQc
      obtain ⟨hlf, ww, hv, hwb⟩ := hQc
      subst v
      have hHM_ce : HeadMemAligned (callEntryStateHOLFinite t callee) :=
        headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      have hHM_cp : HeadMemAligned cpost := headMemAligned_congr_head_only
        (by rw [hlf]) (fun off _ => by unfold memW; rw [hlf]) hHM_ce
      refine ⟨headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp, ww, hwb, ?_⟩
      apply copyLocals_cons_update_g08 _ _ _ _ _ hK
      intro kv hk
      simp only [copyExtArgs_g08, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
    · intro t hc hInv hlen hR ⟨hHM, ww, hwb, hK⟩ hnt
      exact copy_ext_cost_phase_run_g08 s0 h_ext_code_of stVal csVal szVal addrw ww
        hst_sh hcs_sh hsz_sh hwb t hc hInv hlen hR ⟨hHM, hK⟩ hnt

theorem op_extcodecopy_aligned_spec (h_ext_code_of : ExtCodeOfHeadSpec) :
    FunSpec (fun s => EvmRun s ∧ HeadMemAligned s)
      OpDispatchPost (ofString "op_extcodecopy") := by
  refine ⟨_, _, _, lookup_op_extcodecopy_g08, ?_⟩
  intro F s0 hcode ⟨hRun, hHM⟩ _ hnt
  suffices hrun : HandlerRun s0 (fun t => HeadMemAligned t ∧ CopyLocals_g08 [] t.locals) false
      (sourceFnBody Guest.Software.guestFn_op_extcodecopy) from
    hrun s0 hcode hRun.1 rfl (le_refl _) ⟨hHM, fun _ h => by cases h⟩ hnt
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_op_extcodecopy,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map, List.map]
  refine HandlerRun.decCall_stack_copy_g08 (CopyLocals_g08 [])
    (fun l => ∃ avVal, shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact avVal) = true ∧
      CopyLocals_g08 [(ofString "av", avVal)] l) ?_ ?_
  · intro l v hK hsh
    refine ⟨v, hsh, copyLocals_cons_update_g08 _ _ _ _ ?_ hK⟩
    intro kv hk; cases hk
  · refine HandlerRun.decCall
      (Q := fun t => HeadMemAligned t ∧ ∃ addrw : BitVec 64,
        CopyLocals_g08 [(ofString "addr", .val (.word addrw))] t.locals)
      eps_to_address_masked_head_g08
      (fun _ _ _ _ _ _ _ _ _ _ => trivial)
      (fun t _ _ callee _ v cpost _ ⟨hHM_t, _⟩ _ _ _ _ hQc => by
        obtain ⟨hg_cp, _, ⟨addrw, hv⟩, hmem_cp⟩ := hQc
        subst hv
        let ce := callEntryStateHOLFinite t callee
        have hHM_ce : HeadMemAligned ce := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_t
        have hHM_cp : HeadMemAligned cpost := headMemAligned_congr_head_only hg_cp hmem_cp hHM_ce
        let res := setVarHOLFinite (ofString "addr") (.val (.word addrw)) { cpost with locals := t.locals }
        refine ⟨headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp, addrw, ?_⟩
        intro kv hk
        simp only [List.mem_singleton] at hk; subst hk
        simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      ?_
    refine HandlerRun.decCall_stack_copy_g08
      (fun l => ∃ addrw : BitVec 64, CopyLocals_g08 [(ofString "addr", .val (.word addrw))] l)
      (fun l => ∃ addrw : BitVec 64, ∃ stVal,
        shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true ∧
        CopyLocals_g08 [(ofString "mstart", stVal), (ofString "addr", .val (.word addrw))] l) ?_ ?_
    · intro l v ⟨addrw, hK⟩ hsh
      refine ⟨addrw, v, hsh, copyLocals_cons_update_g08 _ _ _ _ ?_ hK⟩
      intro kv hk; simp only [List.mem_singleton] at hk; subst hk; dsimp only; decide
    · refine HandlerRun.decCall_stack_copy_g08
        (fun l => ∃ addrw : BitVec 64, ∃ stVal,
          shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true ∧
          CopyLocals_g08 [(ofString "mstart", stVal), (ofString "addr", .val (.word addrw))] l)
        (fun l => ∃ addrw : BitVec 64, ∃ stVal csVal,
          shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true ∧
          shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact csVal) = true ∧
          CopyLocals_g08 [(ofString "cstart", csVal), (ofString "mstart", stVal),
            (ofString "addr", .val (.word addrw))] l) ?_ ?_
      · intro l v ⟨addrw, stVal, hst, hK⟩ hsh
        refine ⟨addrw, stVal, v, hst, hsh, copyLocals_cons_update_g08 _ _ _ _ ?_ hK⟩
        intro kv hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> dsimp only <;> decide
      · refine HandlerRun.decCall_stack_copy_g08
          (fun l => ∃ addrw : BitVec 64, ∃ stVal csVal,
            shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true ∧
            shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact csVal) = true ∧
            CopyLocals_g08 [(ofString "cstart", csVal), (ofString "mstart", stVal),
              (ofString "addr", .val (.word addrw))] l)
          (fun l => ∃ addrw : BitVec 64, ∃ stVal csVal szVal,
            shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact stVal) = true ∧
            shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact csVal) = true ∧
            shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact szVal) = true ∧
            CopyLocals_g08 [(ofString "size", szVal), (ofString "cstart", csVal), (ofString "mstart", stVal),
              (ofString "addr", .val (.word addrw))] l) ?_ ?_
        · intro l v ⟨addrw, stVal, csVal, hst, hcs, hK⟩ hsh
          refine ⟨addrw, stVal, csVal, v, hst, hcs, hsh, copyLocals_cons_update_g08 _ _ _ _ ?_ hK⟩
          intro kv hk
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl <;> dsimp only <;> decide
        · intro t hc hInv hlen hR ⟨hHM_t, addrw, stVal, csVal, szVal, hst, hcs, hsz, hK⟩ hnt_t
          exact copy_ext_after_pops_run_g08 s0 h_ext_code_of stVal csVal szVal addrw hst hcs hsz
            t hc hInv hlen hR ⟨hHM_t, hK⟩ hnt_t

private theorem heapGap_disj_world_and_frames_g08 {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {x : Ivl}
    (hA : ArenaOK s) (hWT : WorldTypedWith s S Nd)
    (hFW_all : ∀ ec ∈ evmChain s, FrameWF s S ec)
    (hx : Inside x (globN s "heap_ptr") heapLimit) :
    IvlsDisj [x] (worldTypedIvls s S Nd ++ ((evmChain s).map (frameObjects s)).flatten) := by
  intro y hy i hi
  simp only [List.mem_singleton] at hy; subst hy
  have hlim_ss : heapLimit = scratchStart := rfl
  have hfm : scratchStart ≤ globN s "frame_mem_ptr" := hA.2.2.1
  have hsp : globN s "frame_mem_ptr" ≤ globN s "scratch_ptr" := hA.2.2.2.1
  have hy1 : globN s "heap_ptr" ≤ y.1 := hx.1
  have hy2 : y.1 + y.2 ≤ heapLimit := hx.2
  have hdj_heap : ∀ j : Ivl, Inside j sourceBase (globN s "heap_ptr") → Disj y j := fun j hj =>
    Or.inr (Or.inr (Or.inr (by have hj2 := hj.2; omega)))
  have hdj_above : ∀ j : Ivl, scratchStart ≤ j.1 → Disj y j := fun j hj =>
    Or.inr (Or.inr (Or.inl (by omega)))
  rcases List.mem_append.1 hi with hwti | hfo
  · rcases worldTypedIvls_allocated hWT hwti with hz | hal
    · exact Or.inr (Or.inl hz)
    · rcases hal with hh | hsc
      · exact hdj_heap i hh
      · exact hdj_above i (by have hsc1 := hsc.1; omega)
  · obtain ⟨fo, hfo_map, hi_fo⟩ := List.mem_flatten.1 hfo
    obtain ⟨ec, hec, rfl⟩ := List.mem_map.1 hfo_map
    have hFW := hFW_all ec hec
    unfold frameObjects at hi_fo
    rcases List.mem_append.1 hi_fo with hhead7 | hlogobj
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hhead7
      rcases hhead7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hdj_above _ (by have h : globN s "scratch_ptr" ≤ ec.1 := (hFW.1 (ec.1, 280) (by simp)).1.1; omega)
      · exact hdj_above _ (by have h : globN s "scratch_ptr" ≤ ec.2 := (hFW.1 (ec.2, 104) (by simp)).1.1; omega)
      · exact hdj_above _ (by have h : globN s "scratch_ptr" ≤ memW s (ec.1 + 8) := (hFW.1 (memW s (ec.1 + 8), 32 * memW s (ec.1 + 232)) (by simp)).1.1; omega)
      · exact hdj_above _ (by have h : scratchStart ≤ memW s (ec.1 + 24) := hFW.2.1.1; omega)
      · exact hdj_above _ (by have h : globN s "scratch_ptr" ≤ memW s (ec.1 + 88) := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1.1; omega)
      · rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.1 with hh | hsc
        · exact hdj_heap _ hh
        · exact hdj_above _ (by have hsc1 : globN s "scratch_ptr" ≤ (frameLogs s ec).1 := hsc.1; omega)
      · rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with ⟨hz, _⟩ | ⟨hh, _⟩
        · unfold frameRet; rw [if_pos hz]; exact Or.inr (Or.inl rfl)
        · exact hdj_heap _ hh
    · unfold frameLogObjects at hlogobj
      obtain ⟨idx, hidx_mem, hi_own⟩ := List.mem_flatMap.1 hlogobj
      have hidx : idx < memW s (memW s (ec.1 + 88) + 8) := List.mem_range.1 hidx_mem
      have hi_rec : i ∈ logRecordIvls s (memW s (memW s (memW s (ec.1 + 88)) + 8 * idx)) :=
        (List.mem_filter.1 hi_own).1
      rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
      · have he88_in : globN s "scratch_ptr" ≤ memW s (ec.1 + 88) := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1.1
        have hss : 0 < scratchStart := by rw [R11Shards.scratchStart_val]; decide
        omega
      · obtain ⟨_, _, h_r0, _, _, h_r1, h_r2, h_r3⟩ := hent idx hidx
        unfold logRecordIvls at hi_rec
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi_rec
        rcases hi_rec with rfl | rfl | rfl | rfl
        · exact hdj_heap _ h_r0
        · exact hdj_heap _ h_r1
        · exact hdj_heap _ h_r2
        · exact hdj_heap _ h_r3

private theorem heapGap_bre_to_evmStep_g08 {F : Type}
    {t post : PanSemStateFiniteExact 64 F} {markw : BitVec 64} {len : Nat}
    (hInv : EvmInv t)
    (hmark_nat : markw.toNat = globN t "heap_ptr")
    (hmark_le : markw.toNat + len ≤ InitECandidate.Solver.HeapPotential.cMax.toNat)
    (hmark_8 : markw.toNat % 8 = 0)
    (heff : ByteRegionEffect t post [(markw.toNat, len)]) :
    EvmInv post ∧ evmChain post = evmChain t ∧ evmR post = evmR t := by
  obtain ⟨hAt, S_t, hInvAt_t⟩ := hInv
  have hWt := hInvAt_t.1
  have hFW_all := hInvAt_t.2.2.2.2.1
  have hAT := hInvAt_t.2.2.2.2.2.2.2.2.2.1
  obtain ⟨Nd1, hTr1⟩ := hWt.2.2.2
  obtain ⟨Nd2, hTr2, hAT2⟩ := hAT
  obtain ⟨hTr_int, hne_int⟩ := R11Shards.triesTypedWith_inter hTr1 hTr2
  set Nd := Nd1.filter (fun n => decide (n ∈ Nd2))
  have hAT_Nd : ∀ o ∈ ((evmChain t).map (frameObjects t)).flatten, ∀ j ∈ nodeExtents t Nd, Disj o j :=
    fun o ho j hj => hAT2 o ho j (hne_int j hj).2
  have hx_in : Inside (markw.toNat, len) (globN t "heap_ptr") heapLimit := by
    refine ⟨by dsimp only; omega, ?_⟩
    dsimp only
    have hcMax_val : InitECandidate.Solver.HeapPotential.cMax.toNat = 2952790016 := rfl
    have hhl_val : heapLimit = 2952790016 := rfl
    omega
  have hdj := heapGap_disj_world_and_frames_g08 hAt.2
    ⟨hWt.1, hWt.2.1, hWt.2.2.1, hTr_int⟩ hFW_all hx_in
  have hStep : EvmStep [] t post :=
    ByteRegionEffect.to_evmStep_nil_with hAt hInvAt_t hTr_int hAT_Nd hdj heff
  have hch : evmChain post = evmChain t := hStep.2.2.2
  have hRl8 : ∀ x ∈ ([(markw.toNat, len)] : List Ivl), x.1 % 8 = 0 := by
    intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact hmark_8
  have hR : evmR post = evmR t := by
    refine evmR_eq_of_chain_and_words hch (fun ec hec => ?_)
    have hFW_ec := hFW_all ec hec
    have hb1 := (frameWF_bounds hAt.2 hFW_ec).1
    have he1_8 : ec.1 % 8 = 0 := (hFW_ec.1 (ec.1, 280) (by simp)).2.1
    have hdj_ec : ∀ x ∈ ([(markw.toNat, len)] : List Ivl), Disj x (ec.1, 280) := by
      intro x hx
      apply hdj x hx (ec.1, 280)
      apply List.mem_append_right
      exact List.mem_flatten.2 ⟨frameObjects t ec, List.mem_map.2 ⟨ec, hec, rfl⟩, by simp [frameObjects]⟩
    exact ⟨memW_eq_of_disj_eff heff hRl8 hb1 he1_8 (by omega) (by omega) hdj_ec,
           memW_eq_of_disj_eff heff hRl8 hb1 he1_8 (by omega) (by omega) hdj_ec⟩
  exact ⟨hStep.1, hch, hR⟩

private theorem lookup_extend_memory_cost2_g08 :
    originalRuntimeCode.lookup (ofString "extend_memory_cost2") =
      some ([(ofString "s1", .comb [.one, .one, .one, .one]),
             (ofString "n1", .comb [.one, .one, .one, .one]),
             (ofString "s2", .comb [.one, .one, .one, .one]),
             (ofString "n2", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_extend_memory_cost2, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 459 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_extend_memory_cost2) rfl

private theorem add_sat_body_full_g08 {F : Type}
    (s : PanSemStateFiniteExact 64 F) {aw bw : BitVec 64}
    (ha : s.locals.lookup (ofString "a") = some (.val (.word aw)))
    (hb : s.locals.lookup (ofString "b") = some (.val (.word bw)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_add_sat)).1 =
      some (.returned v)) :
    ∃ rw : BitVec 64, v = .val (.word rw) ∧
      rw.toNat = if aw.toNat + bw.toNat < 2 ^ 64 then aw.toNat + bw.toNat else 2 ^ 64 - 1 := by
  have hbody : sourceFnBody Guest.Software.guestFn_add_sat =
      .dec (ofString "s") .one (.op .add [.var .local (ofString "a"), .var .local (ofString "b")])
        (.seq
          (.ite (.cmp .lower (.var .local (ofString "s")) (.var .local (ofString "a")))
            (.return (.const 18446744073709551615#64))
            .skip)
          (.return (.var .local (ofString "s")))) := rfl
  rw [hbody, evaluateHOLFiniteState_dec_total] at hret; dsimp only at hret
  have hsum : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
      (.op .add [.var .local (ofString "a"), .var .local (ofString "b")]) =
      some (.val (.word (aw + bw))) := by
    simp [evalHOLExact, evalListHOLExact, ha, hb, wordOpHOL, wordOp, valueIsWord, valueWord]
  rw [hsum] at hret; dsimp only at hret
  have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word (aw + bw)))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh] at hret; dsimp only at hret
  set s1 := setVarHOLFinite (ofString "s") (.val (.word (aw + bw))) s
  have hs1_s : s1.locals.lookup (ofString "s") = some (.val (.word (aw + bw))) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_a : s1.locals.lookup (ofString "a") = some (.val (.word aw)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ha,
      show ofString "s" ≠ ofString "a" by decide]
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
  have hcmp : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
      (.cmp .lower (.var .local (ofString "s")) (.var .local (ofString "a"))) =
      some (.val (.word (if (aw + bw) < aw then 1 else 0))) := by
    simp [evalHOLExact, hs1_s, hs1_a, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp] at hret; dsimp only at hret
  have haw_lt := aw.isLt
  have hbw_lt := bw.isLt
  by_cases hlt : (aw + bw) < aw
  · have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    simp only [hlt, ↓reduceIte, h10] at hret
    rw [evaluateHOLFiniteState_return] at hret; dsimp only [evalHOLExact] at hret
    have hsz : sizeOfShapeWithContextHOL s1.structs
        (shapeOfHOLExact (.val (.word 18446744073709551615#64))) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [if_pos hsz] at hret; dsimp only at hret
    injection hret with h1; injection h1 with hv
    refine ⟨18446744073709551615#64, hv.symm, ?_⟩
    rw [BitVec.lt_def, BitVec.toNat_add] at hlt
    have hover : ¬ (aw.toNat + bw.toNat < 2 ^ 64) := by
      intro hok; rw [Nat.mod_eq_of_lt hok] at hlt; omega
    rw [if_neg hover]; decide
  · simp only [hlt, ↓reduceIte, evaluateHOLFiniteState_skip] at hret
    rw [evaluateHOLFiniteState_return] at hret
    have hev_s : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
        (.var .local (ofString "s")) = some (.val (.word (aw + bw))) := hs1_s
    rw [hev_s] at hret; dsimp only at hret
    split at hret
    · injection hret with h1; injection h1 with hv
      refine ⟨aw + bw, hv.symm, ?_⟩
      rw [BitVec.lt_def, BitVec.toNat_add] at hlt
      have hok : aw.toNat + bw.toNat < 2 ^ 64 := by
        by_contra hover
        have hmod : (aw.toNat + bw.toNat) % 2 ^ 64 = aw.toNat + bw.toNat - 2 ^ 64 := by omega
        omega
      rw [if_pos hok, BitVec.toNat_add, Nat.mod_eq_of_lt hok]
    · simp at hret

private theorem ceil32_body_exact_g08 {F : Type} (s : PanSemStateFiniteExact 64 F) {vw : BitVec 64}
    (hcode : s.code = originalRuntimeCode)
    (hv_lk : s.locals.lookup (ofString "v") = some (.val (.word vw)))
    (ret : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_ceil32)).1 =
      some (.returned ret)) :
    ∃ cw : BitVec 64, ret = .val (.word cw) ∧
      (vw.toNat ≤ 2 ^ 64 - 32 →
        cw.toNat = ((vw.toNat + 31) / 32) * 32 ∧ vw.toNat ≤ cw.toNat ∧
        cw.toNat ≤ 2 ^ 64 - 32 ∧ cw.toNat % 32 = 0 ∧ (vw.toNat % 32 = 0 → cw.toNat = vw.toNat)) ∧
      (2 ^ 64 - 31 ≤ vw.toNat → cw.toNat = 2 ^ 64 - 1) := by
  have hbody : sourceFnBody Guest.Software.guestFn_ceil32 =
      .dec (ofString "r") .one (.op .and [.var .local (ofString "v"), .const 31#64])
        (.seq
          (.ite (.cmp .equal (.var .local (ofString "r")) (.const 0#64))
            (.return (.var .local (ofString "v")))
            .skip)
          (.decCall (ofString "s") .one (ofString "add_sat")
            [.var .local (ofString "v"), .op .sub [.const 32#64, .var .local (ofString "r")]]
            (.return (.var .local (ofString "s"))))) := rfl
  rw [hbody, evaluateHOLFiniteState_dec_total] at hret; dsimp only at hret
  have hand : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
      (.op .and [.var .local (ofString "v"), .const 31#64]) =
      some (.val (.word (vw &&& 31#64))) := by
    simp [evalHOLExact, evalListHOLExact, hv_lk, wordOpHOL, wordOp, valueIsWord, valueWord]
  rw [hand] at hret; dsimp only at hret
  have hsh_r : shapeEqHOL .one (shapeOfHOLExact (.val (.word (vw &&& 31#64)))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh_r] at hret; dsimp only at hret
  set rw := vw &&& 31#64
  have hrw_nat : rw.toNat = vw.toNat % 32 := by
    change (vw &&& 31#64).toNat = vw.toNat % 32
    rw [BitVec.toNat_and, show (31#64 : BitVec 64).toNat = 2 ^ 5 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  set s1 := setVarHOLFinite (ofString "r") (.val (.word rw)) s
  have hs1_r : s1.locals.lookup (ofString "r") = some (.val (.word rw)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_v : s1.locals.lookup (ofString "v") = some (.val (.word vw)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hv_lk,
      show ofString "r" ≠ ofString "v" by decide]
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
  have hcmp : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
      (.cmp .equal (.var .local (ofString "r")) (.const 0#64)) =
      some (.val (.word (if rw = 0#64 then 1 else 0))) := by
    simp [evalHOLExact, hs1_r, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp] at hret; dsimp only at hret
  have hvw_lt := vw.isLt
  by_cases hr0 : rw = 0#64
  · have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    simp only [hr0, ↓reduceIte, h10] at hret
    rw [evaluateHOLFiniteState_return] at hret
    have hev_v : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
        (.var .local (ofString "v")) = some (.val (.word vw)) := hs1_v
    rw [hev_v] at hret; dsimp only at hret
    have hsz : sizeOfShapeWithContextHOL s1.structs
        (shapeOfHOLExact (.val (.word vw))) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [if_pos hsz] at hret; dsimp only at hret
    injection hret with h1; injection h1 with hv
    have hmod0 : vw.toNat % 32 = 0 := by rw [← hrw_nat, hr0]; rfl
    refine ⟨vw, hv.symm, ?_, ?_⟩
    · intro hle; exact ⟨by omega, le_rfl, hle, hmod0, fun _ => rfl⟩
    · intro hge; omega
  · simp only [hr0, ↓reduceIte, evaluateHOLFiniteState_skip] at hret
    have hmod_pos : 0 < vw.toNat % 32 := by
      rw [← hrw_nat]
      by_contra hz
      apply hr0
      apply BitVec.eq_of_toNat_eq
      change rw.toNat = 0; omega
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
    have hargs : evalListHOLFinite s1 (h := fun x => Classical.propDecidable (s1.memaddrs x))
        [.var .local (ofString "v"), .op .sub [.const 32#64, .var .local (ofString "r")]] =
        some [.val (.word vw), .val (.word (32#64 - rw))] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs1_v, hs1_r, wordOpHOL, wordOp, valueIsWord, valueWord]
    rw [hargs] at hret; dsimp only at hret
    have hlk := pan_two_word_lookup s1.code.lookup (ofString "add_sat") (ofString "a") (ofString "b")
      (sourceFnBody Guest.Software.guestFn_add_sat) vw (32#64 - rw) (by decide)
      (by change s.code.lookup _ = _; rw [hcode]; exact lookup_add_sat)
    rw [hlk] at hret; dsimp only at hret
    split at hret
    · simp at hret
    · let cal := (HolFiniteMapExact.empty.update (ofString "a", ValueHOL.val (.word vw))).update
        (ofString "b", ValueHOL.val (.word (32#64 - rw)))
      rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s1 cal)
          (sourceFnBody Guest.Software.guestFn_add_sat) with ⟨rb, pb⟩
      rw [hrun] at hret
      rcases rb with _ | rb
      · simp at hret
      · cases rb with
        | returned vb =>
          dsimp only at hret
          split at hret
          · dsimp only at hret
            have ha_lk : (callEntryStateHOLFinite s1 cal).locals.lookup (ofString "a") = some (.val (.word vw)) := by
              have hne : ofString "b" ≠ ofString "a" := by decide
              simp [cal, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne]
            have hb_lk : (callEntryStateHOLFinite s1 cal).locals.lookup (ofString "b") = some (.val (.word (32#64 - rw))) := by
              simp [cal, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            obtain ⟨sw, rfl, hsw_nat⟩ := add_sat_body_full_g08 (callEntryStateHOLFinite s1 cal) ha_lk hb_lk vb
              (by rw [hrun])
            set cs := setVarHOLFinite (ofString "s") (.val (.word sw)) { pb with locals := s1.locals }
            rw [evaluateHOLFiniteState_return] at hret
            have hev_s : @evalHOLExact 64 F _ cs.toExact (fun x => Classical.propDecidable (cs.memaddrs x))
                (.var .local (ofString "s")) = some (.val (.word sw)) := by
              simp [evalHOLExact, cs, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            rw [hev_s] at hret; dsimp only at hret
            split at hret
            · injection hret with h1; injection h1 with hv
              have hsub_nat : (32#64 - rw).toNat = 32 - vw.toNat % 32 := by
                have hle_rw : rw.toNat ≤ 32 := by omega
                rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle_rw), hrw_nat]
                rfl
              rw [hsub_nat] at hsw_nat
              refine ⟨sw, hv.symm, ?_, ?_⟩
              · intro hle
                have hok : vw.toNat + (32 - vw.toNat % 32) < 2 ^ 64 := by omega
                rw [if_pos hok] at hsw_nat
                refine ⟨by omega, by omega, by omega, by omega, fun hm => by omega⟩
              · intro hge
                have hover : ¬ (vw.toNat + (32 - vw.toNat % 32) < 2 ^ 64) := by omega
                rw [if_neg hover] at hsw_nat
                exact hsw_nat
            · simp at hret
          · simp at hret
        | _ => simp at hret

private theorem eval_mul64x64_square_g08 {F : Type}
    (s : PanSemStateFiniteExact 64 F) {ww : BitVec 64}
    (ha : s.locals.lookup (ofString "a") = some (.val (.word ww)))
    (hb : s.locals.lookup (ofString "b") = some (.val (.word ww)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_mul64x64)).1 =
      some (.returned v)) :
    ∃ lo hi : BitVec 64, v = .rStruct [.val (.word lo), .val (.word hi)] ∧
      (2 ^ 32 ≤ ww.toNat → ww.toNat < 2 ^ 59 → hi ≠ 0#64) ∧
      (ww.toNat < 2 ^ 32 → hi = 0#64 ∧ lo.toNat = ww.toNat * ww.toNat) := by
  have hbody : sourceFnBody Guest.Software.guestFn_mul64x64 =
      .dec (ofString "a0") .one (.op .and [.var .local (ofString "a"), .const (4294967295#64)])
        (.dec (ofString "a1") .one (.shift .lsr (.var .local (ofString "a")) (.const (32#64)))
          (.dec (ofString "b0") .one (.op .and [.var .local (ofString "b"), .const (4294967295#64)])
            (.dec (ofString "b1") .one (.shift .lsr (.var .local (ofString "b")) (.const (32#64)))
              (.dec (ofString "p00") .one (.panop .mul [.var .local (ofString "a0"), .var .local (ofString "b0")])
                (.dec (ofString "p11") .one (.panop .mul [.var .local (ofString "a1"), .var .local (ofString "b1")])
                  (.dec (ofString "mid") (.comb [.one, .one]) (.rstruct [.const (0#64), .const (0#64)])
                    (.seq
                      (.primitive (ofString "mid") .addCarry
                        [.panop .mul [.var .local (ofString "a0"), .var .local (ofString "b1")],
                         .panop .mul [.var .local (ofString "a1"), .var .local (ofString "b0")],
                         .const (0#64)])
                      (.dec (ofString "lo") (.comb [.one, .one]) (.rstruct [.const (0#64), .const (0#64)])
                        (.seq
                          (.primitive (ofString "lo") .addCarry
                            [.var .local (ofString "p00"),
                             .shift .lsl (.rfield 0 (.var .local (ofString "mid"))) (.const (32#64)),
                             .const (0#64)])
                          (.dec (ofString "hi") .one
                            (.op .add
                              [.var .local (ofString "p11"),
                               .shift .lsr (.rfield 0 (.var .local (ofString "mid"))) (.const (32#64)),
                               .shift .lsl (.rfield 1 (.var .local (ofString "mid"))) (.const (32#64)),
                               .rfield 1 (.var .local (ofString "lo"))])
                            (.return (.rstruct [.rfield 0 (.var .local (ofString "lo")), .var .local (ofString "hi")])))))))))))) := rfl
  let a0 := ww &&& 4294967295#64
  let a1 := ww >>> (32 : Nat)
  let p00 := a0 * a0
  let p11 := a1 * a1
  let p01 := a0 * a1
  let mid := wordAddCarryHOL p01 p01 0#64
  let lo := wordAddCarryHOL p00 (mid.1 <<< (32 : Nat)) 0#64
  let hi := p11 + (mid.1 >>> (32 : Nat)) + (mid.2 <<< (32 : Nat)) + lo.2
  have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
  have hand_w : wordOpHOL .and [ww, 4294967295#64] = some a0 := rfl
  have hlsr_w : wordShiftHOL .lsr ww 32 = some a1 := by simp [wordShiftHOL, a1]
  have hpo_mid : panPrimopHOLExact PrimOp.addCarry
      ([.val (.word p01), .val (.word p01), .val (.word 0#64)] : List (ValueHOL 64)) =
      some (.rStruct [.val (.word mid.1), .val (.word mid.2)]) := by
    simp [panPrimopHOLExact, mid]
  have hlsl_mid0 : wordShiftHOL .lsl mid.1 32 = some (mid.1 <<< (32 : Nat)) := by simp [wordShiftHOL]
  have hlsr_mid0 : wordShiftHOL .lsr mid.1 32 = some (mid.1 >>> (32 : Nat)) := by simp [wordShiftHOL]
  have hlsl_mid1 : wordShiftHOL .lsl mid.2 32 = some (mid.2 <<< (32 : Nat)) := by simp [wordShiftHOL]
  have hpo_lo : panPrimopHOLExact PrimOp.addCarry
      ([.val (.word p00), .val (.word (mid.1 <<< (32 : Nat))), .val (.word 0#64)] : List (ValueHOL 64)) =
      some (.rStruct [.val (.word lo.1), .val (.word lo.2)]) := by
    simp [panPrimopHOLExact, lo]
  have hadd4 : wordOpHOL .add [p11, mid.1 >>> (32 : Nat), mid.2 <<< (32 : Nat), lo.2] = some hi := by
    simp [wordOpHOL, wordOp, hi, BitVec.add_assoc]
  have hlk_eq {st : PanSemStateFiniteExact 64 F} (k : MlS) (u : ValueHOL 64) :
      (setVarHOLFinite k u st).locals.lookup k = some u := by
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hlk_ne {st : PanSemStateFiniteExact 64 F} (k1 k2 : MlS) (u : ValueHOL 64) (hne : k1 ≠ k2) :
      (setVarHOLFinite k1 u st).locals.lookup k2 = st.locals.lookup k2 := by
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
  have step_dec : ∀ {nm : MlS} {sh : ShapeHOL} {e : ExpHOL 64} {b : ProgHOL 64}
      {st : PanSemStateFiniteExact 64 F} {u : ValueHOL 64},
      @evalHOLExact 64 F _ st.toExact (fun x => Classical.propDecidable (st.memaddrs x)) e = some u →
      shapeEqHOL sh (shapeOfHOLExact u) = true →
      (evaluateHOLFiniteState st (.dec nm sh e b)).1 =
        (evaluateHOLFiniteState (setVarHOLFinite nm u st) b).1 := by
    intro nm sh e b st u hev hsh
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    rw [hev]; dsimp only; rw [if_pos hsh]
  have step_prim : ∀ {nm : MlS} {op : PrimOp} {args : List (ExpHOL 64)} {tl : ProgHOL 64}
      {st : PanSemStateFiniteExact 64 F} {vals : List (ValueHOL 64)} {u : ValueHOL 64},
      @evalListHOLExact 64 F _ st.toExact (fun x => Classical.propDecidable (st.memaddrs x)) args = some vals →
      panPrimopHOLExact op vals = some u →
      st.isValidValueHOLFinite .local nm u = true →
      (evaluateHOLFiniteState st (.seq (.primitive nm op args) tl)).1 =
        (evaluateHOLFiniteState (setVarHOLFinite nm u st) tl).1 := by
    intro nm op args tl st vals u hargs hpo hval
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_primitive, hargs]; dsimp only
    rw [hpo]; dsimp only; rw [if_pos hval]
  have hsh1 : ∀ w : BitVec 64, shapeEqHOL .one (shapeOfHOLExact (.val (.word w) : ValueHOL 64)) = true :=
    fun _ => by simp [shapeEqHOL, shapeOfHOLExact]
  have hsh2 : shapeEqHOL (.comb [.one, .one]) (shapeOfHOLExact (.rStruct [.val (.word (0#64)), .val (.word (0#64))] : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeEqHOL.shapeEqListHOL, shapeOfHOLExact]
  rw [hbody] at hret
  rw [step_dec (u := .val (.word a0)) (by simp [evalHOLExact, evalListHOLExact, ha, valueIsWord, valueWord, hand_w]) (hsh1 _)] at hret
  set s1 := setVarHOLFinite (ofString "a0") (.val (.word a0)) s
  have hs1_a0 : s1.locals.lookup (ofString "a0") = some (.val (.word a0)) := hlk_eq _ _
  have hs1_a : s1.locals.lookup (ofString "a") = some (.val (.word ww)) := by
    rw [hlk_ne (ofString "a0") (ofString "a") _ (by decide)]; exact ha
  have hs1_b : s1.locals.lookup (ofString "b") = some (.val (.word ww)) := by
    rw [hlk_ne (ofString "a0") (ofString "b") _ (by decide)]; exact hb
  rw [step_dec (u := .val (.word a1)) (by simp [evalHOLExact, hs1_a, h32, hlsr_w]) (hsh1 _)] at hret
  set s2 := setVarHOLFinite (ofString "a1") (.val (.word a1)) s1
  have hs2_a1 : s2.locals.lookup (ofString "a1") = some (.val (.word a1)) := hlk_eq _ _
  have hs2_a0 : s2.locals.lookup (ofString "a0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "a1") (ofString "a0") _ (by decide)]; exact hs1_a0
  have hs2_b : s2.locals.lookup (ofString "b") = some (.val (.word ww)) := by
    rw [hlk_ne (ofString "a1") (ofString "b") _ (by decide)]; exact hs1_b
  rw [step_dec (u := .val (.word a0)) (by simp [evalHOLExact, evalListHOLExact, hs2_b, valueIsWord, valueWord, hand_w]) (hsh1 _)] at hret
  set s3 := setVarHOLFinite (ofString "b0") (.val (.word a0)) s2
  have hs3_b0 : s3.locals.lookup (ofString "b0") = some (.val (.word a0)) := hlk_eq _ _
  have hs3_a1 : s3.locals.lookup (ofString "a1") = some (.val (.word a1)) := by
    rw [hlk_ne (ofString "b0") (ofString "a1") _ (by decide)]; exact hs2_a1
  have hs3_a0 : s3.locals.lookup (ofString "a0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "b0") (ofString "a0") _ (by decide)]; exact hs2_a0
  have hs3_b : s3.locals.lookup (ofString "b") = some (.val (.word ww)) := by
    rw [hlk_ne (ofString "b0") (ofString "b") _ (by decide)]; exact hs2_b
  rw [step_dec (u := .val (.word a1)) (by simp [evalHOLExact, hs3_b, h32, hlsr_w]) (hsh1 _)] at hret
  set s4 := setVarHOLFinite (ofString "b1") (.val (.word a1)) s3
  have hs4_b1 : s4.locals.lookup (ofString "b1") = some (.val (.word a1)) := hlk_eq _ _
  have hs4_b0 : s4.locals.lookup (ofString "b0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "b1") (ofString "b0") _ (by decide)]; exact hs3_b0
  have hs4_a1 : s4.locals.lookup (ofString "a1") = some (.val (.word a1)) := by
    rw [hlk_ne (ofString "b1") (ofString "a1") _ (by decide)]; exact hs3_a1
  have hs4_a0 : s4.locals.lookup (ofString "a0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "b1") (ofString "a0") _ (by decide)]; exact hs3_a0
  rw [step_dec (u := .val (.word p00)) (by simp [evalHOLExact, evalListHOLExact, hs4_a0, hs4_b0, valueIsWord, valueWord, panOpHOL, p00]) (hsh1 _)] at hret
  set s5 := setVarHOLFinite (ofString "p00") (.val (.word p00)) s4
  have hs5_p00 : s5.locals.lookup (ofString "p00") = some (.val (.word p00)) := hlk_eq _ _
  have hs5_b1 : s5.locals.lookup (ofString "b1") = some (.val (.word a1)) := by
    rw [hlk_ne (ofString "p00") (ofString "b1") _ (by decide)]; exact hs4_b1
  have hs5_b0 : s5.locals.lookup (ofString "b0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "p00") (ofString "b0") _ (by decide)]; exact hs4_b0
  have hs5_a1 : s5.locals.lookup (ofString "a1") = some (.val (.word a1)) := by
    rw [hlk_ne (ofString "p00") (ofString "a1") _ (by decide)]; exact hs4_a1
  have hs5_a0 : s5.locals.lookup (ofString "a0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "p00") (ofString "a0") _ (by decide)]; exact hs4_a0
  rw [step_dec (u := .val (.word p11)) (by simp [evalHOLExact, evalListHOLExact, hs5_a1, hs5_b1, valueIsWord, valueWord, panOpHOL, p11]) (hsh1 _)] at hret
  set s6 := setVarHOLFinite (ofString "p11") (.val (.word p11)) s5
  have hs6_p11 : s6.locals.lookup (ofString "p11") = some (.val (.word p11)) := hlk_eq _ _
  have hs6_p00 : s6.locals.lookup (ofString "p00") = some (.val (.word p00)) := by
    rw [hlk_ne (ofString "p11") (ofString "p00") _ (by decide)]; exact hs5_p00
  have hs6_b1 : s6.locals.lookup (ofString "b1") = some (.val (.word a1)) := by
    rw [hlk_ne (ofString "p11") (ofString "b1") _ (by decide)]; exact hs5_b1
  have hs6_b0 : s6.locals.lookup (ofString "b0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "p11") (ofString "b0") _ (by decide)]; exact hs5_b0
  have hs6_a1 : s6.locals.lookup (ofString "a1") = some (.val (.word a1)) := by
    rw [hlk_ne (ofString "p11") (ofString "a1") _ (by decide)]; exact hs5_a1
  have hs6_a0 : s6.locals.lookup (ofString "a0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "p11") (ofString "a0") _ (by decide)]; exact hs5_a0
  rw [step_dec (u := .rStruct [.val (.word 0#64), .val (.word 0#64)]) (by simp [evalHOLExact, evalListHOLExact]) hsh2] at hret
  set s7 := setVarHOLFinite (ofString "mid") (.rStruct [.val (.word 0#64), .val (.word 0#64)]) s6
  have hs7_mid : s7.locals.lookup (ofString "mid") = some (.rStruct [.val (.word 0#64), .val (.word 0#64)]) := hlk_eq _ _
  have hs7_p11 : s7.locals.lookup (ofString "p11") = some (.val (.word p11)) := by
    rw [hlk_ne (ofString "mid") (ofString "p11") _ (by decide)]; exact hs6_p11
  have hs7_p00 : s7.locals.lookup (ofString "p00") = some (.val (.word p00)) := by
    rw [hlk_ne (ofString "mid") (ofString "p00") _ (by decide)]; exact hs6_p00
  have hs7_b1 : s7.locals.lookup (ofString "b1") = some (.val (.word a1)) := by
    rw [hlk_ne (ofString "mid") (ofString "b1") _ (by decide)]; exact hs6_b1
  have hs7_b0 : s7.locals.lookup (ofString "b0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "mid") (ofString "b0") _ (by decide)]; exact hs6_b0
  have hs7_a1 : s7.locals.lookup (ofString "a1") = some (.val (.word a1)) := by
    rw [hlk_ne (ofString "mid") (ofString "a1") _ (by decide)]; exact hs6_a1
  have hs7_a0 : s7.locals.lookup (ofString "a0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "mid") (ofString "a0") _ (by decide)]; exact hs6_a0
  have hp10 : a1 * a0 = p01 := BitVec.mul_comm a1 a0
  rw [step_prim
    (by simp [evalListHOLExact, evalHOLExact, hs7_a0, hs7_a1, hs7_b0, hs7_b1, valueIsWord, valueWord, panOpHOL, p01, hp10])
    hpo_mid
    (by simp [isValidValueHOLFinite, lookupKvarHOLFinite, hs7_mid, shapeEqHOL, shapeEqHOL.shapeEqListHOL, shapeOfHOLExact])] at hret
  set s8 := setVarHOLFinite (ofString "mid") (.rStruct [.val (.word mid.1), .val (.word mid.2)]) s7
  have hs8_mid : s8.locals.lookup (ofString "mid") = some (.rStruct [.val (.word mid.1), .val (.word mid.2)]) := hlk_eq _ _
  have hs8_p11 : s8.locals.lookup (ofString "p11") = some (.val (.word p11)) := by
    rw [hlk_ne (ofString "mid") (ofString "p11") _ (by decide)]; exact hs7_p11
  have hs8_p00 : s8.locals.lookup (ofString "p00") = some (.val (.word p00)) := by
    rw [hlk_ne (ofString "mid") (ofString "p00") _ (by decide)]; exact hs7_p00
  rw [step_dec (u := .rStruct [.val (.word 0#64), .val (.word 0#64)]) (by simp [evalHOLExact, evalListHOLExact]) hsh2] at hret
  set s9 := setVarHOLFinite (ofString "lo") (.rStruct [.val (.word 0#64), .val (.word 0#64)]) s8
  have hs9_lo : s9.locals.lookup (ofString "lo") = some (.rStruct [.val (.word 0#64), .val (.word 0#64)]) := hlk_eq _ _
  have hs9_mid : s9.locals.lookup (ofString "mid") = some (.rStruct [.val (.word mid.1), .val (.word mid.2)]) := by
    rw [hlk_ne (ofString "lo") (ofString "mid") _ (by decide)]; exact hs8_mid
  have hs9_p11 : s9.locals.lookup (ofString "p11") = some (.val (.word p11)) := by
    rw [hlk_ne (ofString "lo") (ofString "p11") _ (by decide)]; exact hs8_p11
  have hs9_p00 : s9.locals.lookup (ofString "p00") = some (.val (.word p00)) := by
    rw [hlk_ne (ofString "lo") (ofString "p00") _ (by decide)]; exact hs8_p00
  rw [step_prim
    (by simp [evalListHOLExact, evalHOLExact, hs9_p00, hs9_mid, h32, hlsl_mid0])
    hpo_lo
    (by simp [isValidValueHOLFinite, lookupKvarHOLFinite, hs9_lo, shapeEqHOL, shapeEqHOL.shapeEqListHOL, shapeOfHOLExact])] at hret
  set s10 := setVarHOLFinite (ofString "lo") (.rStruct [.val (.word lo.1), .val (.word lo.2)]) s9
  have hs10_lo : s10.locals.lookup (ofString "lo") = some (.rStruct [.val (.word lo.1), .val (.word lo.2)]) := hlk_eq _ _
  have hs10_mid : s10.locals.lookup (ofString "mid") = some (.rStruct [.val (.word mid.1), .val (.word mid.2)]) := by
    rw [hlk_ne (ofString "lo") (ofString "mid") _ (by decide)]; exact hs9_mid
  have hs10_p11 : s10.locals.lookup (ofString "p11") = some (.val (.word p11)) := by
    rw [hlk_ne (ofString "lo") (ofString "p11") _ (by decide)]; exact hs9_p11
  rw [step_dec (u := .val (.word hi))
    (by simp [evalHOLExact, evalListHOLExact, hs10_p11, hs10_mid, hs10_lo, valueIsWord, valueWord, h32, hlsr_mid0, hlsl_mid1, hadd4]) (hsh1 _)] at hret
  set s11 := setVarHOLFinite (ofString "hi") (.val (.word hi)) s10
  have hs11_hi : s11.locals.lookup (ofString "hi") = some (.val (.word hi)) := hlk_eq _ _
  have hs11_lo : s11.locals.lookup (ofString "lo") = some (.rStruct [.val (.word lo.1), .val (.word lo.2)]) := by
    rw [hlk_ne (ofString "hi") (ofString "lo") _ (by decide)]; exact hs10_lo
  rw [evaluateHOLFiniteState_return] at hret
  have hev_ret : @evalHOLExact 64 F _ s11.toExact (fun a => Classical.propDecidable (s11.memaddrs a))
      (.rstruct [.rfield 0 (.var .local (ofString "lo")), .var .local (ofString "hi")]) =
      some (.rStruct [.val (.word lo.1), .val (.word hi)]) := by
    simp [evalHOLExact, evalListHOLExact, hs11_lo, hs11_hi]
  rw [hev_ret] at hret; dsimp only at hret
  have hsz : sizeOfShapeWithContextHOL s11.structs
      (shapeOfHOLExact (.rStruct [.val (.word lo.1), .val (.word hi)] : ValueHOL 64)) ≤ 32 := by
    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
  rw [if_pos hsz] at hret; dsimp only at hret
  injection hret with h1; injection h1 with hv
  refine ⟨lo.1, hi, hv.symm, ?_, ?_⟩
  · intro hw_ge hw_lt
    have ha1_nat : a1.toNat = ww.toNat / 2 ^ 32 := by
      dsimp only [a1]; rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have ha1_pos : 1 ≤ a1.toNat := by omega
    have ha1_lt : a1.toNat < 2 ^ 27 := by
      have : (2 ^ 59 : Nat) = 2 ^ 27 * 2 ^ 32 := by decide
      omega
    have hp11_lt : a1.toNat * a1.toNat < 2 ^ 54 := by
      have hmul : a1.toNat * a1.toNat < 2 ^ 27 * 2 ^ 27 := Nat.mul_lt_mul'' ha1_lt ha1_lt
      have : (2 ^ 27 : Nat) * 2 ^ 27 = 2 ^ 54 := by decide
      omega
    have hp11_nat : p11.toNat = a1.toNat * a1.toNat := by
      dsimp only [p11]; rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (by omega)]
    have hp11_pos : 1 ≤ p11.toNat := by
      rw [hp11_nat]; exact Nat.mul_le_mul ha1_pos ha1_pos
    have hmid0_lsr : (mid.1 >>> (32 : Nat)).toNat < 2 ^ 32 := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      have := mid.1.isLt
      have : (2 ^ 64 : Nat) = 2 ^ 32 * 2 ^ 32 := by decide
      omega
    have hcarry_bit : ∀ x y z : BitVec 64, (wordAddCarryHOL x y z).2 = 0 ∨ (wordAddCarryHOL x y z).2 = 1 := by
      intro x y z; unfold wordAddCarryHOL; split_ifs <;> simp <;> omega
    have hmid2_le : mid.2.toNat ≤ 1 := by
      rcases hcarry_bit p01 p01 0#64 with h | h
      · dsimp only [mid]; rw [h]; decide
      · dsimp only [mid]; rw [h]; decide
    have hmid2_lsl : (mid.2 <<< (32 : Nat)).toNat ≤ 2 ^ 32 := by
      rw [BitVec.toNat_shiftLeft]
      have : mid.2.toNat <<< 32 = mid.2.toNat * 2 ^ 32 := Nat.shiftLeft_eq mid.2.toNat 32
      rw [this, Nat.mod_eq_of_lt (by omega)]
      omega
    have hlo2_le : lo.2.toNat ≤ 1 := by
      rcases hcarry_bit p00 (mid.1 <<< (32 : Nat)) 0#64 with h | h
      · dsimp only [lo]; rw [h]; decide
      · dsimp only [lo]; rw [h]; decide
    have hhi_pos : 0 < hi.toNat := by
      dsimp only [hi]
      have hsum1 : (p11 + (mid.1 >>> (32 : Nat))).toNat = p11.toNat + (mid.1 >>> (32 : Nat)).toNat := by
        rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
      have hsum2 : (p11 + (mid.1 >>> (32 : Nat)) + (mid.2 <<< (32 : Nat))).toNat =
          p11.toNat + (mid.1 >>> (32 : Nat)).toNat + (mid.2 <<< (32 : Nat)).toNat := by
        rw [BitVec.toNat_add, hsum1, Nat.mod_eq_of_lt (by omega)]
      have hsum3 : (p11 + (mid.1 >>> (32 : Nat)) + (mid.2 <<< (32 : Nat)) + lo.2).toNat =
          p11.toNat + (mid.1 >>> (32 : Nat)).toNat + (mid.2 <<< (32 : Nat)).toNat + lo.2.toNat := by
        rw [BitVec.toNat_add, hsum2, Nat.mod_eq_of_lt (by omega)]
      omega
    intro hz; rw [hz] at hhi_pos; simp at hhi_pos
  · intro hw_lt32
    have ha1_z : a1 = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      dsimp only [a1]
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      change ww.toNat / 2 ^ 32 = 0
      omega
    have ha0_eq : a0 = ww := by
      apply BitVec.eq_of_toNat_eq
      dsimp only [a0]
      rw [BitVec.toNat_and, show (4294967295#64 : BitVec 64).toNat = 2 ^ 32 - 1 by decide,
        Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hw_lt32]
    have hp11_z : p11 = 0#64 := by dsimp only [p11]; rw [ha1_z]; rfl
    have hp01_z : p01 = 0#64 := by dsimp only [p01]; rw [ha1_z]; simp
    have hmid_z : mid = (0#64, 0#64) := by
      dsimp only [mid]; rw [hp01_z]; unfold wordAddCarryHOL; simp
    have hmid_lsl : mid.1 <<< (32 : Nat) = 0#64 := by rw [hmid_z]; rfl
    have hp00_lt : p00.toNat < 2 ^ 64 := p00.isLt
    have hp00_nat : p00.toNat = ww.toNat * ww.toNat := by
      dsimp only [p00]; rw [ha0_eq, BitVec.toNat_mul]
      have hmul : ww.toNat * ww.toNat < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' hw_lt32 hw_lt32
      have h64 : (2 ^ 32 : Nat) * 2 ^ 32 = 2 ^ 64 := by decide
      rw [Nat.mod_eq_of_lt (by omega)]
    have hlo_eq : lo = (p00, 0#64) := by
      dsimp only [lo]; rw [hmid_lsl]
      unfold wordAddCarryHOL
      have hz0 : (0#64 : BitVec 64).toNat = 0 := rfl
      have hno_ov : ¬ (2 ^ 64 ≤ p00.toNat + (0#64 : BitVec 64).toNat + (0#64 : BitVec 64).toNat) := by
        rw [hz0]; omega
      simp [hno_ov, BitVec.add_zero]
      omega
    have hhi_z : hi = 0#64 := by
      dsimp only [hi]; rw [hp11_z, hmid_z, hlo_eq]; rfl
    exact ⟨hhi_z, by rw [hlo_eq]; exact hp00_nat⟩

private theorem words_of_exact_g08 {F : Type}
    (s : PanSemStateFiniteExact 64 F) {nw : BitVec 64}
    (hcode : s.code = originalRuntimeCode)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_words_of)).1 =
      some (.returned v)) :
    ∃ ww : BitVec 64, v = .val (.word ww) ∧
      (2 ^ 37 ≤ nw.toNat → 2 ^ 32 ≤ ww.toNat ∧ ww.toNat < 2 ^ 59) ∧
      (nw.toNat < 2 ^ 37 → nw.toNat % 32 = 0 → ww.toNat = nw.toNat / 32 ∧ ww.toNat < 2 ^ 32) := by
  have hbody : sourceFnBody Guest.Software.guestFn_words_of =
      .decCall (ofString "c") .one (ofString "ceil32") [.var .local (ofString "n")]
        (.return (.shift .lsr (.var .local (ofString "c")) (.const 5#64))) := rfl
  rw [hbody, evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
  have hargs : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x))
      [.var .local (ofString "n")] = some [.val (.word nw)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hn]
  rw [hargs] at hret; dsimp only at hret
  have hlk := pan_one_word_lookup s.code.lookup (ofString "ceil32") (ofString "v")
    (sourceFnBody Guest.Software.guestFn_ceil32) nw
    (by rw [hcode]; exact lookup_ceil32)
  rw [hlk] at hret; dsimp only at hret
  split at hret
  · simp at hret
  · let cal := HolFiniteMapExact.empty.update (ofString "v", ValueHOL.val (.word nw))
    rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s cal)
        (sourceFnBody Guest.Software.guestFn_ceil32) with ⟨rb, pb⟩
    rw [hrun] at hret
    rcases rb with _ | rb
    · simp at hret
    · cases rb with
      | returned vb =>
        dsimp only at hret
        split at hret
        · dsimp only at hret
          have hv_lk : (callEntryStateHOLFinite s cal).locals.lookup (ofString "v") =
              some (.val (.word nw)) := by
            simp [cal, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          obtain ⟨cw, rfl, hlo, hhi⟩ := ceil32_body_exact_g08 (callEntryStateHOLFinite s cal) hcode hv_lk vb
            (by rw [hrun])
          set cs := setVarHOLFinite (ofString "c") (.val (.word cw)) { pb with locals := s.locals }
          rw [evaluateHOLFiniteState_return] at hret
          have hcs_c : cs.locals.lookup (ofString "c") = some (.val (.word cw)) := by
            simp [cs, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have h5 : (5#64 : BitVec 64).toNat = 5 := rfl
          have hshf : wordShiftHOL .lsr cw 5 = some (cw >>> (5 : Nat)) := by simp [wordShiftHOL]
          have hev : @evalHOLExact 64 F _ cs.toExact (fun a => Classical.propDecidable (cs.memaddrs a))
              (.shift .lsr (.var .local (ofString "c")) (.const 5#64)) =
              some (.val (.word (cw >>> (5 : Nat)))) := by
            simp [evalHOLExact, hcs_c, h5, hshf]
          rw [hev] at hret; dsimp only at hret
          split at hret
          · injection hret with h1; injection h1 with hv
            refine ⟨cw >>> (5 : Nat), hv.symm, ?_, ?_⟩
            · intro hn_ge
              have hcw_ge : 2 ^ 37 ≤ cw.toNat := by
                by_cases hle : nw.toNat ≤ 2 ^ 64 - 32
                · have := (hlo hle).1; omega
                · have := hhi (by omega); omega
              refine ⟨?_, ?_⟩
              · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                have : (2 ^ 37 : Nat) = 2 ^ 32 * 2 ^ 5 := by decide
                omega
              · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                have := cw.isLt
                have : (2 ^ 64 : Nat) = 2 ^ 59 * 2 ^ 5 := by decide
                omega
            · intro hn_lt hn_mod
              have hle : nw.toNat ≤ 2 ^ 64 - 32 := by omega
              have hcw_eq : cw.toNat = nw.toNat := (hlo hle).2.2.2.2 hn_mod
              rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hcw_eq]
              have h32 : (2 ^ 5 : Nat) = 32 := rfl
              have h37 : (2 ^ 37 : Nat) = 2 ^ 32 * 32 := by decide
              exact ⟨by rw [h32], by omega⟩
          · simp at hret
        · simp at hret
      | _ => simp at hret

private theorem memory_gas_cost_exact_g08 {F : Type}
    (s : PanSemStateFiniteExact 64 F) {szw : BitVec 64}
    (hcode : s.code = originalRuntimeCode)
    (hsz_lk : s.locals.lookup (ofString "size") = some (.val (.word szw)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memory_gas_cost)).1 =
      some (.returned v)) :
    ∃ cw : BitVec 64, v = .val (.word cw) ∧
      (2 ^ 37 ≤ szw.toNat → cw = 18446744073709551615#64) ∧
      (szw.toNat < 2 ^ 37 → szw.toNat % 32 = 0 →
        cw.toNat = 3 * (szw.toNat / 32) + ((szw.toNat / 32) * (szw.toNat / 32)) / 512 ∧
        cw.toNat < 2 ^ 56) := by
  have hbody : sourceFnBody Guest.Software.guestFn_memory_gas_cost =
      .decCall (ofString "w") .one (ofString "words_of") [.var .local (ofString "size")]
        (.decCall (ofString "sq") (.comb [.one, .one]) (ofString "mul64x64")
          [.var .local (ofString "w"), .var .local (ofString "w")]
          (.seq
            (.ite (.cmp .notEqual (.rfield 1 (.var .local (ofString "sq"))) (.const 0#64))
              (.return (.const 18446744073709551615#64))
              .skip)
            (.decCall (ofString "a") .one (ofString "add_sat")
              [.panop .mul [.var .local (ofString "w"), .const 3#64],
               .shift .lsr (.rfield 0 (.var .local (ofString "sq"))) (.const 9#64)]
              (.return (.var .local (ofString "a")))))) := rfl
  rw [hbody, evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
  have hargs1 : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x))
      [.var .local (ofString "size")] = some [.val (.word szw)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hsz_lk]
  rw [hargs1] at hret; dsimp only at hret
  have hlk1 := pan_one_word_lookup s.code.lookup (ofString "words_of") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_words_of) szw
    (by rw [hcode]; exact lookup_words_of)
  rw [hlk1] at hret; dsimp only at hret
  split at hret
  · simp at hret
  · let cal1 := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word szw))
    rcases hrun1 : evaluateHOLFiniteState (callEntryStateHOLFinite s cal1)
        (sourceFnBody Guest.Software.guestFn_words_of) with ⟨rb1, pb1⟩
    rw [hrun1] at hret
    have hpb1_code : pb1.code = originalRuntimeCode := by
      have hm := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s cal1)
        (sourceFnBody Guest.Software.guestFn_words_of)).1
      rw [hrun1] at hm; exact hm.trans hcode
    rcases rb1 with _ | rb1
    · simp at hret
    · cases rb1 with
      | returned vb1 =>
        dsimp only at hret
        split at hret
        · dsimp only at hret
          have hn1 : (callEntryStateHOLFinite s cal1).locals.lookup (ofString "n") =
              some (.val (.word szw)) := by
            simp [cal1, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          obtain ⟨ww, rfl, hww_big, hww_small⟩ :=
            words_of_exact_g08 (callEntryStateHOLFinite s cal1) hcode hn1 vb1 (by rw [hrun1])
          set s1 := setVarHOLFinite (ofString "w") (.val (.word ww)) { pb1 with locals := s.locals }
          have hs1_w : s1.locals.lookup (ofString "w") = some (.val (.word ww)) := by
            simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hs1_code : s1.code = originalRuntimeCode := hpb1_code
          rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
          have hargs2 : evalListHOLFinite s1 (h := fun x => Classical.propDecidable (s1.memaddrs x))
              [.var .local (ofString "w"), .var .local (ofString "w")] =
              some [.val (.word ww), .val (.word ww)] := by
            simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs1_w]
          rw [hargs2] at hret; dsimp only at hret
          have hlk2 : lookupCodeHOLFinite s1.code.lookup (ofString "mul64x64")
              [.val (.word ww), .val (.word ww)] =
              some (sourceFnBody Guest.Software.guestFn_mul64x64,
                (HolFiniteMapExact.empty.update (ofString "a", ValueHOL.val (.word ww))).update
                  (ofString "b", ValueHOL.val (.word ww)),
                .comb [.one, .one]) := by
            have hd : ofString "a" ≠ ofString "b" := by decide
            have raw : lookupCodeHOLExact s1.code.lookup (ofString "mul64x64")
                [.val (.word ww), .val (.word ww)] =
                some (sourceFnBody Guest.Software.guestFn_mul64x64,
                  (fun key => if key = ofString "b" then some (.val (.word ww))
                    else if key = ofString "a" then some (.val (.word ww)) else none),
                  .comb [.one, .one]) := by
              simp [lookupCodeHOLExact, hs1_code, lookup_mul64x64, shapeOfHOLExact, shapeEqHOL, hd]
            unfold PanSemStateFiniteExact.lookupCodeHOLFinite
            split
            · rename_i missing; rw [raw] at missing; cases missing
            · rename_i foundBody foundLocals foundShape found
              have equal := Option.some.inj (found.symm.trans raw)
              obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
              apply congrArg (fun locals => some (sourceFnBody Guest.Software.guestFn_mul64x64, locals, ShapeHOL.comb [.one, .one]))
              apply HolFiniteMapExact.ext
              funext key
              by_cases hb_k : key = ofString "b"
              · subst key; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]
              · have hb_k' : ofString "b" ≠ key := Ne.symm hb_k
                by_cases ha_k : key = ofString "a"
                · subst key; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, hd, Ne.symm hd]
                · have ha_k' : ofString "a" ≠ key := Ne.symm ha_k
                  simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, ha_k, hb_k, ha_k', hb_k']
          rw [hlk2] at hret; dsimp only at hret
          split at hret
          · simp at hret
          · let cal2 := (HolFiniteMapExact.empty.update (ofString "a", ValueHOL.val (.word ww))).update
              (ofString "b", ValueHOL.val (.word ww))
            rcases hrun2 : evaluateHOLFiniteState (callEntryStateHOLFinite s1 cal2)
                (sourceFnBody Guest.Software.guestFn_mul64x64) with ⟨rb2, pb2⟩
            rw [hrun2] at hret
            have hpb2_code : pb2.code = originalRuntimeCode := by
              have hm := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s1 cal2)
                (sourceFnBody Guest.Software.guestFn_mul64x64)).1
              rw [hrun2] at hm; exact hm.trans hs1_code
            rcases rb2 with _ | rb2
            · simp at hret
            · cases rb2 with
              | returned vb2 =>
                dsimp only at hret
                split at hret
                · dsimp only at hret
                  have ha2 : (callEntryStateHOLFinite s1 cal2).locals.lookup (ofString "a") =
                      some (.val (.word ww)) := by
                    have hne : ofString "b" ≠ ofString "a" := by decide
                    simp [cal2, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne]
                  have hb2 : (callEntryStateHOLFinite s1 cal2).locals.lookup (ofString "b") =
                      some (.val (.word ww)) := by
                    simp [cal2, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  obtain ⟨low, hiw, rfl, hhi_big, hhi_small⟩ :=
                    eval_mul64x64_square_g08 (callEntryStateHOLFinite s1 cal2) ha2 hb2 vb2 (by rw [hrun2])
                  set s2 := setVarHOLFinite (ofString "sq")
                    (.rStruct [.val (.word low), .val (.word hiw)]) { pb2 with locals := s1.locals }
                  have hs2_sq : s2.locals.lookup (ofString "sq") =
                      some (.rStruct [.val (.word low), .val (.word hiw)]) := by
                    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  have hs2_w : s2.locals.lookup (ofString "w") = some (.val (.word ww)) := by
                    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_w,
                      show ofString "sq" ≠ ofString "w" by decide]
                  have hs2_code : s2.code = originalRuntimeCode := hpb2_code
                  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
                  have h10 : ¬ ((1#64 : BitVec 64) = 0) := by decide
                  have h00 : (0#64 : BitVec 64) = 0 := rfl
                  have hcmp : @evalHOLExact 64 F _ s2.toExact (fun x => Classical.propDecidable (s2.memaddrs x))
                      (.cmp .notEqual (.rfield 1 (.var .local (ofString "sq"))) (.const 0#64)) =
                      some (.val (.word (if hiw ≠ 0#64 then 1#64 else 0#64))) := by
                    simp [evalHOLExact, hs2_sq, Compiler.Encoders.Asm.wordCmpHOL]
                  rw [hcmp] at hret; dsimp only at hret
                  by_cases hhi0 : hiw ≠ 0#64
                  · rw [if_pos hhi0, if_neg h10] at hret
                    rw [evaluateHOLFiniteState_return] at hret; dsimp only [evalHOLExact] at hret
                    have hsz : sizeOfShapeWithContextHOL s2.structs
                        (shapeOfHOLExact (.val (.word 18446744073709551615#64))) ≤ 32 := by
                      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
                    rw [if_pos hsz] at hret; dsimp only at hret
                    injection hret with h1; injection h1 with hv
                    refine ⟨18446744073709551615#64, hv.symm, fun _ => rfl, ?_⟩
                    intro hlt37 hmod32
                    obtain ⟨_, hww_lt32⟩ := hww_small hlt37 hmod32
                    exact False.elim (hhi0 (hhi_small hww_lt32).1)
                  · rw [if_neg hhi0, if_pos h00, evaluateHOLFiniteState_skip] at hret; dsimp only at hret
                    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
                    have h9 : (9#64 : BitVec 64).toNat = 9 := rfl
                    have hshf9 : wordShiftHOL .lsr low 9 = some (low >>> (9 : Nat)) := by simp [wordShiftHOL]
                    have hargs3 : evalListHOLFinite s2 (h := fun x => Classical.propDecidable (s2.memaddrs x))
                        [.panop .mul [.var .local (ofString "w"), .const 3#64],
                         .shift .lsr (.rfield 0 (.var .local (ofString "sq"))) (.const 9#64)] =
                        some [.val (.word (ww * 3#64)), .val (.word (low >>> (9 : Nat)))] := by
                      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs2_w, hs2_sq,
                        panOpHOL, valueIsWord, valueWord, h9, hshf9]
                    rw [hargs3] at hret; dsimp only at hret
                    have hlk3 := pan_two_word_lookup s2.code.lookup (ofString "add_sat") (ofString "a") (ofString "b")
                      (sourceFnBody Guest.Software.guestFn_add_sat) (ww * 3#64) (low >>> (9 : Nat)) (by decide)
                      (by rw [hs2_code]; exact lookup_add_sat)
                    rw [hlk3] at hret; dsimp only at hret
                    split at hret
                    · simp at hret
                    · let cal3 := (HolFiniteMapExact.empty.update (ofString "a", ValueHOL.val (.word (ww * 3#64)))).update
                        (ofString "b", ValueHOL.val (.word (low >>> (9 : Nat))))
                      rcases hrun3 : evaluateHOLFiniteState (callEntryStateHOLFinite s2 cal3)
                          (sourceFnBody Guest.Software.guestFn_add_sat) with ⟨rb3, pb3⟩
                      rw [hrun3] at hret
                      rcases rb3 with _ | rb3
                      · simp at hret
                      · cases rb3 with
                        | returned vb3 =>
                          dsimp only at hret
                          split at hret
                          · dsimp only at hret
                            have ha3 : (callEntryStateHOLFinite s2 cal3).locals.lookup (ofString "a") =
                                some (.val (.word (ww * 3#64))) := by
                              have hne : ofString "b" ≠ ofString "a" := by decide
                              simp [cal3, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne]
                            have hb3 : (callEntryStateHOLFinite s2 cal3).locals.lookup (ofString "b") =
                                some (.val (.word (low >>> (9 : Nat)))) := by
                              simp [cal3, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                            obtain ⟨aw, rfl, haw_nat⟩ := add_sat_body_full_g08 (callEntryStateHOLFinite s2 cal3) ha3 hb3 vb3
                              (by rw [hrun3])
                            set s3 := setVarHOLFinite (ofString "a") (.val (.word aw)) { pb3 with locals := s2.locals }
                            rw [evaluateHOLFiniteState_return] at hret
                            have hev_a : @evalHOLExact 64 F _ s3.toExact (fun x => Classical.propDecidable (s3.memaddrs x))
                                (.var .local (ofString "a")) = some (.val (.word aw)) := by
                              simp [evalHOLExact, s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                            rw [hev_a] at hret; dsimp only at hret
                            split at hret
                            · injection hret with h1; injection h1 with hv
                              refine ⟨aw, hv.symm, ?_, ?_⟩
                              · intro hge37
                                obtain ⟨hww_ge, hww_lt⟩ := hww_big hge37
                                exact False.elim (hhi0 (hhi_big hww_ge hww_lt))
                              · intro hlt37 hmod32
                                obtain ⟨hww_eq, hww_lt32⟩ := hww_small hlt37 hmod32
                                obtain ⟨_, hlow_eq⟩ := hhi_small hww_lt32
                                have hm3 : (ww * 3#64).toNat = 3 * ww.toNat := by
                                  rw [BitVec.toNat_mul, show (3#64 : BitVec 64).toNat = 3 by rfl]
                                  have : ww.toNat * 3 < 2 ^ 64 := by omega
                                  rw [Nat.mod_eq_of_lt this, Nat.mul_comm]
                                have hdiv512 : (low >>> (9 : Nat)).toNat = (ww.toNat * ww.toNat) / 512 := by
                                  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hlow_eq]
                                have hsq_lt : ww.toNat * ww.toNat < 2 ^ 64 := by
                                  have hmul : ww.toNat * ww.toNat < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' hww_lt32 hww_lt32
                                  have : (2 ^ 32 : Nat) * 2 ^ 32 = 2 ^ 64 := by decide
                                  omega
                                have hdiv_lt : (ww.toNat * ww.toNat) / 512 < 2 ^ 55 := by
                                  have : (2 ^ 64 : Nat) = 2 ^ 55 * 512 := by decide
                                  omega
                                have hsum_lt56 : 3 * ww.toNat + (ww.toNat * ww.toNat) / 512 < 2 ^ 56 := by omega
                                have hsum_lt64 : (ww * 3#64).toNat + (low >>> (9 : Nat)).toNat < 2 ^ 64 := by
                                  rw [hm3, hdiv512]; omega
                                rw [if_pos hsum_lt64, hm3, hdiv512, hww_eq] at haw_nat
                                exact ⟨haw_nat, by rw [haw_nat, ← hww_eq]; exact hsum_lt56⟩
                            · simp at hret
                          · simp at hret
                        | _ => simp at hret
                · simp at hret
              | _ => simp at hret
        · simp at hret
      | _ => simp at hret

private theorem extend_memory_cost1_raw_bounds_g08 {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_extend_memory_cost1)).1 =
      some (.returned v)) :
    ∃ cw ebw : BitVec 64,
      v = .rStruct [.val (.word cw), .val (.word ebw)] ∧
      (cw = 18446744073709551615#64 → ebw = 0#64) ∧
      (cw ≠ 18446744073709551615#64 → cw.toNat < 2 ^ 56) ∧
      (ebw = 0#64 ∨
        ∃ before after : Nat,
          after < 2 ^ 37 ∧
          after % 32 = 0 ∧
          before < after ∧
          ebw.toNat = after - before ∧
          (memW s (globN s "ev" + 32) % 32 = 0 → before = memW s (globN s "ev" + 32))) := by
  have hbody : sourceFnBody Guest.Software.guestFn_extend_memory_cost1 =
      .decCall (ofString "z") .one (ofString "u256_is_zero") [.var .local (ofString "size")]
        (.seq
          (.ite (.cmp .notEqual (.var .local (ofString "z")) (.const 0#64))
            (.return (.rstruct [.const 0#64, .const 0#64]))
            .skip)
          (.decCall (ofString "s") .one (ofString "sat_word") [.var .local (ofString "start")]
            (.decCall (ofString "n") .one (ofString "sat_word") [.var .local (ofString "size")]
              (.decCall (ofString "endp") .one (ofString "add_sat") [.var .local (ofString "s"), .var .local (ofString "n")]
                (.seq
                  (.ite (.cmp .equal (.var .local (ofString "endp")) (.const 18446744073709551615#64))
                    (.return (.rstruct [.const 18446744073709551615#64, .const 0#64]))
                    .skip)
                  (.dec (ofString "cur") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 32#64]))
                    (.decCall (ofString "before") .one (ofString "ceil32") [.var .local (ofString "cur")]
                      (.decCall (ofString "after") .one (ofString "ceil32") [.var .local (ofString "endp")]
                        (.seq
                          (.ite (.cmp .notLower (.var .local (ofString "before")) (.var .local (ofString "after")))
                            (.return (.rstruct [.const 0#64, .const 0#64]))
                            .skip)
                          (.decCall (ofString "ca") .one (ofString "memory_gas_cost") [.var .local (ofString "after")]
                            (.decCall (ofString "cb") .one (ofString "memory_gas_cost") [.var .local (ofString "before")]
                              (.seq
                                (.ite (.cmp .equal (.var .local (ofString "ca")) (.const 18446744073709551615#64))
                                  (.return (.rstruct [.const 18446744073709551615#64, .const 0#64]))
                                  .skip)
                                (.return (.rstruct
                                  [.op .sub [.var .local (ofString "ca"), .var .local (ofString "cb")],
                                   .op .sub [.var .local (ofString "after"), .var .local (ofString "before")]])))))))))))))) := rfl
  have hret_rstruct : ∀ (st : PanSemStateFiniteExact 64 F) (w1 w2 : BitVec 64),
      evaluateHOLFiniteState st (.return (.rstruct [.const w1, .const w2])) =
        (some (.returned (.rStruct [.val (.word w1), .val (.word w2)])), st.emptyLocalsHOLFinite) := by
    intro st w1 w2
    rw [evaluateHOLFiniteState_return]
    have hev : @evalHOLExact 64 F _ st.toExact (fun x => Classical.propDecidable (st.memaddrs x))
        (.rstruct [.const w1, .const w2]) =
        some (.rStruct [.val (.word w1), .val (.word w2)]) := by
      simp [evalHOLExact, evalListHOLExact]
    rw [hev]; dsimp only
    have hsz : sizeOfShapeWithContextHOL st.structs
        (shapeOfHOLExact (.rStruct [.val (.word w1), .val (.word w2)] : ValueHOL 64)) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
    rw [if_pos hsz]
  have h10 : ¬ ((1#64 : BitVec 64) = 0) := by decide
  have h00 : (0#64 : BitVec 64) = 0 := rfl
  rw [hbody] at hret
  obtain ⟨zw, s1, hs1_c, hs1_lf, hs1_loc, _, hr1⟩ :=
    ro_word_call_return_g08 (s := s) (st := s) (by decide) hcode (LocFrame.refl s) hret
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr1
  have hs1_z : s1.locals.lookup (ofString "z") = some (.val (.word zw)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hcmp_z : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
      (.cmp .notEqual (.var .local (ofString "z")) (.const 0#64)) =
      some (.val (.word (if zw ≠ 0#64 then (1#64 : BitVec 64) else 0#64))) := by
    simp [evalHOLExact, hs1_z, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp_z] at hr1; dsimp only at hr1
  by_cases hzw : zw ≠ 0#64
  · rw [if_pos hzw, if_neg h10, hret_rstruct s1 0#64 0#64] at hr1
    injection hr1 with h1; injection h1 with hv
    exact ⟨0#64, 0#64, hv.symm, fun _ => rfl, fun _ => by decide, Or.inl rfl⟩
  · rw [if_neg hzw, if_pos h00, evaluateHOLFiniteState_skip] at hr1; dsimp only at hr1
    obtain ⟨sw, s2, hs2_c, hs2_lf, hs2_loc, _, hr2⟩ :=
      ro_word_call_return_g08 (s := s) (st := s1) (by decide) hs1_c hs1_lf hr1
    obtain ⟨nw, s3, hs3_c, hs3_lf, hs3_loc, _, hr3⟩ :=
      ro_word_call_return_g08 (s := s) (st := s2) (by decide) hs2_c hs2_lf hr2
    obtain ⟨endpw, s4, hs4_c, hs4_lf, hs4_loc, _, hr4⟩ :=
      ro_word_call_return_g08 (s := s) (st := s3) (by decide) hs3_c hs3_lf hr3
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr4
    have hs4_endp : s4.locals.lookup (ofString "endp") = some (.val (.word endpw)) := by
      rw [hs4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hcmp_endp : @evalHOLExact 64 F _ s4.toExact (fun x => Classical.propDecidable (s4.memaddrs x))
        (.cmp .equal (.var .local (ofString "endp")) (.const 18446744073709551615#64)) =
        some (.val (.word (if endpw = 18446744073709551615#64 then (1#64 : BitVec 64) else 0#64))) := by
      simp [evalHOLExact, hs4_endp, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hcmp_endp] at hr4; dsimp only at hr4
    by_cases hendp : endpw = 18446744073709551615#64
    · rw [if_pos hendp, if_neg h10, hret_rstruct s4 18446744073709551615#64 0#64] at hr4
      injection hr4 with h1; injection h1 with hv
      exact ⟨18446744073709551615#64, 0#64, hv.symm, fun _ => rfl, fun h => False.elim (h rfl), Or.inl rfl⟩
    · rw [if_neg hendp, if_pos h00, evaluateHOLFiniteState_skip] at hr4; dsimp only at hr4
      rw [evaluateHOLFiniteState_dec_total] at hr4; dsimp only at hr4
      rcases hld_cur : @evalHOLExact 64 F _ s4.toExact (fun x => Classical.propDecidable (s4.memaddrs x))
          (.load .one (.op .add [.var .global (ofString "ev"), .const 32#64])) with _ | curv
      · rw [hld_cur] at hr4; simp at hr4
      · obtain ⟨curw, rfl, hcurw_nat⟩ := evalAt_loadG_word s4 "ev" 32#64 curv hld_cur
        rw [hld_cur] at hr4; dsimp only at hr4
        have hsh_cur : shapeEqHOL .one (shapeOfHOLExact (.val (.word curw))) = true := by
          simp [shapeEqHOL, shapeOfHOLExact]
        rw [if_pos hsh_cur] at hr4; dsimp only at hr4
        have hs4_mem : s4.memory = s.memory := by unfold LocFrame at hs4_lf; conv_lhs => rw [hs4_lf]
        have hs4_glob : s4.globals = s.globals := by unfold LocFrame at hs4_lf; conv_lhs => rw [hs4_lf]
        have hcur_eq : curw.toNat = memW s (globN s "ev" + 32) := by
          have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
          rw [hcurw_nat, h32]
          simp [memW, globN, hs4_mem, hs4_glob]
        set s5 := setVarHOLFinite (ofString "cur") (.val (.word curw)) s4 with hs5_def
        have hs5_c : s5.code = originalRuntimeCode := hs4_c
        have hs5_lf : LocFrame s s5 := hs4_lf.with_locals_clock _ s4.clock
        have hs5_cur : s5.locals.lookup (ofString "cur") = some (.val (.word curw)) := by
          simp [hs5_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        obtain ⟨befw, s6, hs6_c, hs6_lf, hs6_loc, ⟨vals6, body6, cal6, rs6, hargs6, hl6, hrun6⟩, hr6⟩ :=
          ro_word_call_return_g08 (s := s) (st := s5) (by decide) hs5_c hs5_lf hr4
        have hvals6 : vals6 = [.val (.word curw)] := by
          simpa [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs5_cur] using hargs6.symm
        subst hvals6
        obtain ⟨rfl, rfl, curw', hcur_inj, hcal6_v⟩ := one_word_arg_lookup lookup_ceil32 hl6
        injection hcur_inj with hcur_inj'; injection hcur_inj' with hcur_inj''; subst hcur_inj''
        obtain ⟨befw', hbef_inj, hbef_lo, hbef_hi⟩ := ceil32_body_exact_g08 (callEntryStateHOLFinite s5 cal6) hs5_c
          hcal6_v (.val (.word befw)) hrun6
        injection hbef_inj with hbef_inj'; injection hbef_inj' with hbef_inj''; subst hbef_inj''
        have hs6_endp : s6.locals.lookup (ofString "endp") = some (.val (.word endpw)) := by
          rw [hs6_loc]; simp [hs5_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs4_endp,
            show ofString "before" ≠ ofString "endp" by decide,
            show ofString "cur" ≠ ofString "endp" by decide]
        obtain ⟨aftw, s7, hs7_c, hs7_lf, hs7_loc, ⟨vals7, body7, cal7, rs7, hargs7, hl7, hrun7⟩, hr7⟩ :=
          ro_word_call_return_g08 (s := s) (st := s6) (by decide) hs6_c hs6_lf hr6
        have hvals7 : vals7 = [.val (.word endpw)] := by
          simpa [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs6_endp] using hargs7.symm
        subst hvals7
        obtain ⟨rfl, rfl, endpw', hendp_inj, hcal7_v⟩ := one_word_arg_lookup lookup_ceil32 hl7
        injection hendp_inj with hendp_inj'; injection hendp_inj' with hendp_inj''; subst hendp_inj''
        obtain ⟨aftw', haft_inj, haft_lo, haft_hi⟩ := ceil32_body_exact_g08 (callEntryStateHOLFinite s6 cal7) hs6_c
          hcal7_v (.val (.word aftw)) hrun7
        injection haft_inj with haft_inj'; injection haft_inj' with haft_inj''; subst haft_inj''
        have hs7_bef : s7.locals.lookup (ofString "before") = some (.val (.word befw)) := by
          rw [hs7_loc, hs6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "after" ≠ ofString "before" by decide]
        have hs7_aft : s7.locals.lookup (ofString "after") = some (.val (.word aftw)) := by
          rw [hs7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr7
        have hcmp_ba : @evalHOLExact 64 F _ s7.toExact (fun x => Classical.propDecidable (s7.memaddrs x))
            (.cmp .notLower (.var .local (ofString "before")) (.var .local (ofString "after"))) =
            some (.val (.word (if ¬ (befw < aftw) then (1#64 : BitVec 64) else 0#64))) := by
          simp [evalHOLExact, hs7_bef, hs7_aft, Compiler.Encoders.Asm.wordCmpHOL]
        rw [hcmp_ba] at hr7; dsimp only at hr7
        by_cases hba : ¬ (befw < aftw)
        · rw [if_pos hba, if_neg h10, hret_rstruct s7 0#64 0#64] at hr7
          injection hr7 with h1; injection h1 with hv
          exact ⟨0#64, 0#64, hv.symm, fun _ => rfl, fun _ => by decide, Or.inl rfl⟩
        · rw [if_neg hba, if_pos h00, evaluateHOLFiniteState_skip] at hr7; dsimp only at hr7
          have hba_lt : befw.toNat < aftw.toNat := BitVec.lt_def.1 (Classical.not_not.1 hba)
          obtain ⟨caw, s8, hs8_c, hs8_lf, hs8_loc, ⟨vals8, body8, cal8, rs8, hargs8, hl8, hrun8⟩, hr8⟩ :=
            ro_word_call_return_g08 (s := s) (st := s7) (by decide) hs7_c hs7_lf hr7
          have hvals8 : vals8 = [.val (.word aftw)] := by
            simpa [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs7_aft] using hargs8.symm
          subst hvals8
          obtain ⟨rfl, rfl, aftw_arg, haft_arg_inj, hcal8_sz⟩ := one_word_arg_lookup lookup_memory_gas_cost hl8
          injection haft_arg_inj with h1; injection h1 with h2; subst h2
          have hs8_bef : s8.locals.lookup (ofString "before") = some (.val (.word befw)) := by
            rw [hs8_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs7_bef,
              show ofString "ca" ≠ ofString "before" by decide]
          obtain ⟨cbw, s9, hs9_c, hs9_lf, hs9_loc, ⟨vals9, body9, cal9, rs9, hargs9, hl9, hrun9⟩, hr9⟩ :=
            ro_word_call_return_g08 (s := s) (st := s8) (by decide) hs8_c hs8_lf hr8
          have hvals9 : vals9 = [.val (.word befw)] := by
            simpa [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs8_bef] using hargs9.symm
          subst hvals9
          obtain ⟨rfl, rfl, befw_arg, hbef_arg_inj, hcal9_sz⟩ := one_word_arg_lookup lookup_memory_gas_cost hl9
          injection hbef_arg_inj with h1; injection h1 with h2; subst h2
          have hs9_ca : s9.locals.lookup (ofString "ca") = some (.val (.word caw)) := by
            rw [hs9_loc, hs8_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "cb" ≠ ofString "ca" by decide]
          have hs9_cb : s9.locals.lookup (ofString "cb") = some (.val (.word cbw)) := by
            rw [hs9_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
          have hs9_bef : s9.locals.lookup (ofString "before") = some (.val (.word befw)) := by
            rw [hs9_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs8_bef,
              show ofString "cb" ≠ ofString "before" by decide]
          have hs9_aft : s9.locals.lookup (ofString "after") = some (.val (.word aftw)) := by
            rw [hs9_loc, hs8_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs7_aft,
              show ofString "cb" ≠ ofString "after" by decide,
              show ofString "ca" ≠ ofString "after" by decide]
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr9
          have hcmp_ca : @evalHOLExact 64 F _ s9.toExact (fun x => Classical.propDecidable (s9.memaddrs x))
              (.cmp .equal (.var .local (ofString "ca")) (.const 18446744073709551615#64)) =
              some (.val (.word (if caw = 18446744073709551615#64 then (1#64 : BitVec 64) else 0#64))) := by
            simp [evalHOLExact, hs9_ca, Compiler.Encoders.Asm.wordCmpHOL]
          rw [hcmp_ca] at hr9; dsimp only at hr9
          by_cases hca_max : caw = 18446744073709551615#64
          · rw [if_pos hca_max, if_neg h10, hret_rstruct s9 18446744073709551615#64 0#64] at hr9
            injection hr9 with h1; injection h1 with hv
            exact ⟨18446744073709551615#64, 0#64, hv.symm, fun _ => rfl, fun h => False.elim (h rfl), Or.inl rfl⟩
          · rw [if_neg hca_max, if_pos h00, evaluateHOLFiniteState_skip] at hr9; dsimp only at hr9
            rw [evaluateHOLFiniteState_return] at hr9
            have hev_ret : @evalHOLExact 64 F _ s9.toExact (fun x => Classical.propDecidable (s9.memaddrs x))
                (.rstruct
                  [.op .sub [.var .local (ofString "ca"), .var .local (ofString "cb")],
                   .op .sub [.var .local (ofString "after"), .var .local (ofString "before")]]) =
                some (.rStruct [.val (.word (caw - cbw)), .val (.word (aftw - befw))]) := by
              simp [evalHOLExact, evalListHOLExact, hs9_ca, hs9_cb, hs9_aft, hs9_bef,
                wordOpHOL, wordOp, valueIsWord, valueWord]
            rw [hev_ret] at hr9; dsimp only at hr9
            have hsz : sizeOfShapeWithContextHOL s9.structs
                (shapeOfHOLExact (.rStruct [.val (.word (caw - cbw)), .val (.word (aftw - befw))] : ValueHOL 64)) ≤ 32 := by
              simp [shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
            rw [if_pos hsz] at hr9; dsimp only at hr9
            injection hr9 with h1; injection h1 with hv
            obtain ⟨caw', hcaw_inj, hca_big, hca_small⟩ :=
              memory_gas_cost_exact_g08 (callEntryStateHOLFinite s7 cal8) hs7_c hcal8_sz (.val (.word caw)) hrun8
            injection hcaw_inj with hc1; injection hc1 with hc2; subst hc2
            obtain ⟨cbw', hcbw_inj, _, hcb_small⟩ :=
              memory_gas_cost_exact_g08 (callEntryStateHOLFinite s8 cal9) hs8_c hcal9_sz (.val (.word cbw)) hrun9
            injection hcbw_inj with hc1; injection hc1 with hc2; subst hc2
            have haft_lt37 : aftw.toNat < 2 ^ 37 := by
              by_contra hge
              exact hca_max (hca_big (Nat.le_of_not_lt hge))
            have hendp_le : endpw.toNat ≤ 2 ^ 64 - 32 := by
              by_contra hgt
              have haft_max_nat := haft_hi (by omega)
              omega
            have haft_eq := haft_lo hendp_le
            have haft_mod : aftw.toNat % 32 = 0 := haft_eq.2.2.2.1
            have hcur_le : curw.toNat ≤ 2 ^ 64 - 32 := by
              by_contra hgt
              have := hbef_hi (by omega)
              omega
            have hbef_eq := hbef_lo hcur_le
            have hbef_mod : befw.toNat % 32 = 0 := hbef_eq.2.2.2.1
            have hbef_lt37 : befw.toNat < 2 ^ 37 := Nat.lt_trans hba_lt haft_lt37
            obtain ⟨hca_val, hca_lt56⟩ := hca_small haft_lt37 haft_mod
            obtain ⟨hcb_val, _⟩ := hcb_small hbef_lt37 hbef_mod
            have hw_le : befw.toNat / 32 ≤ aftw.toNat / 32 := Nat.div_le_div_right (Nat.le_of_lt hba_lt)
            have hsq_le : (befw.toNat / 32) * (befw.toNat / 32) ≤ (aftw.toNat / 32) * (aftw.toNat / 32) :=
              Nat.mul_le_mul hw_le hw_le
            have hdiv_le : ((befw.toNat / 32) * (befw.toNat / 32)) / 512 ≤ ((aftw.toNat / 32) * (aftw.toNat / 32)) / 512 :=
              Nat.div_le_div_right hsq_le
            have hcb_le_ca : cbw.toNat ≤ caw.toNat := by omega
            have hcost_nat : (caw - cbw).toNat = caw.toNat - cbw.toNat :=
              BitVec.toNat_sub_of_le (BitVec.le_def.2 hcb_le_ca)
            have hcost_lt56 : (caw - cbw).toNat < 2 ^ 56 := by omega
            have hcost_ne_max : caw - cbw ≠ 18446744073709551615#64 := by
              intro hmax
              rw [hmax] at hcost_lt56
              revert hcost_lt56; decide
            have hsub_nat : (aftw - befw).toNat = aftw.toNat - befw.toNat :=
              BitVec.toNat_sub_of_le (BitVec.le_def.2 (Nat.le_of_lt hba_lt))
            refine ⟨caw - cbw, aftw - befw, hv.symm, fun h => False.elim (hcost_ne_max h),
              fun _ => hcost_lt56,
              Or.inr ⟨befw.toNat, aftw.toNat, haft_lt37, haft_mod, hba_lt, hsub_nat, ?_⟩⟩
            intro hcur_al
            rw [← hcur_eq] at hcur_al ⊢
            exact hbef_eq.2.2.2.2 hcur_al

private def emc2NcrCallees_g08 (f : MlS) : Bool :=
  f == ofString "u256_is_zero" ||
  f == ofString "sat_word" ||
  f == ofString "add_sat" ||
  f == ofString "ceil32" ||
  f == ofString "words_of" ||
  f == ofString "mul64x64" ||
  f == ofString "memory_gas_cost" ||
  f == ofString "extend_memory_cost1"

private theorem lookup_words_of_g08 :
    originalRuntimeCode.lookup (ofString "words_of") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_words_of, .one) :=
  lookup_of_guestAst_getElem 443 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_words_of) rfl

private theorem emc2NcrCallees_good_g08 :
    ∀ f, emc2NcrCallees_g08 f = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup f values =
        some (body, callee, rs) →
      noCatchableRaise_g08 emc2NcrCallees_g08 body = true := by
  have hb0 : noCatchableRaise_g08 emc2NcrCallees_g08 (sourceFnBody Guest.Software.guestFn_u256_is_zero) = true := by decide
  have hb1 : noCatchableRaise_g08 emc2NcrCallees_g08 (sourceFnBody Guest.Software.guestFn_sat_word) = true := by decide
  have hb2 : noCatchableRaise_g08 emc2NcrCallees_g08 (sourceFnBody Guest.Software.guestFn_add_sat) = true := by decide
  have hb3 : noCatchableRaise_g08 emc2NcrCallees_g08 (sourceFnBody Guest.Software.guestFn_ceil32) = true := by decide
  have hb4 : noCatchableRaise_g08 emc2NcrCallees_g08 (sourceFnBody Guest.Software.guestFn_words_of) = true := by decide
  have hb5 : noCatchableRaise_g08 emc2NcrCallees_g08 (sourceFnBody Guest.Software.guestFn_mul64x64) = true := by decide
  have hb6 : noCatchableRaise_g08 emc2NcrCallees_g08 (sourceFnBody Guest.Software.guestFn_memory_gas_cost) = true := by decide
  have hb7 : noCatchableRaise_g08 emc2NcrCallees_g08 (sourceFnBody Guest.Software.guestFn_extend_memory_cost1) = true := by decide
  intro f hf values body callee rs hfound
  obtain ⟨params, rs', hinst⟩ := lookupCode_installed hfound
  simp only [emc2NcrCallees_g08, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with ((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl
  · rw [lookup_u256_is_zero_g08] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; exact hb0
  · rw [lookup_sat_word_g08] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; exact hb1
  · rw [lookup_add_sat] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; exact hb2
  · rw [lookup_ceil32] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; exact hb3
  · rw [lookup_words_of_g08] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; exact hb4
  · rw [lookup_mul64x64] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; exact hb5
  · rw [lookup_memory_gas_cost] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; exact hb6
  · rw [lookup_extend_memory_cost1] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; exact hb7

private theorem extend_memory_cost2_four_args_lookup_g08 {vals : List (ValueHOL 64)} {body' : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret' : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "extend_memory_cost2") vals =
      some (body', callee, ret')) :
    ∃ (v1 v2 v3 v4 : ValueHOL 64),
      vals = [v1, v2, v3, v4] ∧
      shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact v1) = true ∧
      shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact v2) = true ∧
      shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact v3) = true ∧
      shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact v4) = true ∧
      callee.lookup (ofString "s1") = some v1 ∧
      callee.lookup (ofString "n1") = some v2 ∧
      callee.lookup (ofString "s2") = some v3 ∧
      callee.lookup (ofString "n2") = some v4 := by
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
    originalRuntimeCode.lookup (ofString "extend_memory_cost2") vals body' callee ret' hl
  simp only [Flapjack.lookupCodeHOLExact, lookup_extend_memory_cost2_g08] at hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, _ | _⟩⟩⟩⟩
  · simp at hx
  · simp at hx
  · simp at hx
  · simp at hx
  · split at hx
    · rename_i hcond
      have heq := Option.some.inj hx
      rcases Prod.mk.inj heq with ⟨_, hrest⟩
      rcases Prod.mk.inj hrest with ⟨hloc, _⟩
      have hs := hcond.2.2
      simp only [List.map, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
        List.zip_cons_cons, List.zip_nil_left] at hs
      rcases hs with ⟨hsh1, hsh2, hsh3, hsh4⟩
      refine ⟨v1, v2, v3, v4, rfl, hsh1, hsh2, hsh3, hsh4, ?_, ?_, ?_, ?_⟩
      · have hfn := congrFun hloc.symm (ofString "s1")
        have h1 : ofString "s1" ≠ ofString "n1" := by decide
        have h2 : ofString "s1" ≠ ofString "s2" := by decide
        have h3 : ofString "s1" ≠ ofString "n2" := by decide
        simpa [FUPDATE_LIST, FUPDATE, h1, Ne.symm h1, h2, Ne.symm h2, h3, Ne.symm h3] using hfn
      · have hfn := congrFun hloc.symm (ofString "n1")
        have h2 : ofString "n1" ≠ ofString "s2" := by decide
        have h3 : ofString "n1" ≠ ofString "n2" := by decide
        simpa [FUPDATE_LIST, FUPDATE, h2, Ne.symm h2, h3, Ne.symm h3] using hfn
      · have hfn := congrFun hloc.symm (ofString "s2")
        have h3 : ofString "s2" ≠ ofString "n2" := by decide
        simpa [FUPDATE_LIST, FUPDATE, h3, Ne.symm h3] using hfn
      · have hfn := congrFun hloc.symm (ofString "n2")
        simpa [FUPDATE_LIST, FUPDATE] using hfn
    · cases hx
  · simp at hx

private theorem ro_rstruct2_call_return_g08 {F : Type}
    {s st : PanSemStateFiniteExact 64 F} {nm fname : MlS}
    {args : List (ExpHOL 64)} {cont : ProgHOL 64} {v : ValueHOL 64}
    (hfn : opRoCallees fname = true)
    (hc : st.code = originalRuntimeCode) (hlf : LocFrame s st)
    (hr : (evaluateHOLFiniteState st (.decCall nm (.comb [.one, .one]) fname args cont)).1 =
      some (.returned v)) :
    ∃ (w0 w1 : BitVec 64) (st' : PanSemStateFiniteExact 64 F),
      st'.code = originalRuntimeCode ∧ LocFrame s st' ∧
      st'.locals = st.locals.update (nm, .rStruct [.val (.word w0), .val (.word w1)]) ∧
      (∃ vals body callee rs,
        evalListHOLFinite st (h := fun x => Classical.propDecidable (st.memaddrs x)) args = some vals ∧
        lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, callee, rs) ∧
        (evaluateHOLFiniteState (callEntryStateHOLFinite st callee) body).1 =
          some (.returned (.rStruct [.val (.word w0), .val (.word w1)]))) ∧
      (evaluateHOLFiniteState st' cont).1 = some (.returned v) := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hr
  rcases hargs : evalListHOLFinite st (h := fun x => Classical.propDecidable (st.memaddrs x)) args with _ | vals
  · rw [hargs] at hr; simp at hr
  · rw [hargs] at hr; dsimp only at hr
    rcases hl : lookupCodeHOLFinite st.code.lookup fname vals with _ | ⟨body, callee, rs⟩
    · rw [hl] at hr; simp at hr
    · rw [hl] at hr; dsimp only at hr
      split at hr
      · simp at hr
      · have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, callee, rs) := by
          rwa [← hc]
        have hsafe := evaluate_readOnlyProg opRoCallees opRoCallees_good body
          (opRoCallees_good fname hfn vals body callee rs hl_orig)
          (callEntryStateHOLFinite st callee) hc
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite st callee) body with ⟨rb, pb⟩
        rw [hrun] at hr
        have hpb_c : pb.code = originalRuntimeCode := by
          have hm := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite st callee) body).1
          rw [hrun] at hm; exact hm.trans hc
        rcases rb with _ | rb
        · simp at hr
        · cases rb with
          | returned vb =>
            dsimp only at hr
            split at hr
            · rename_i hsh
              dsimp only at hr
              have htwo : shapeEqHOL (shapeOfHOLExact vb) (.comb [.one, .one]) = true := by
                simp [Bool.and_eq_true] at hsh; exact hsh.1
              rcases vb with _ | vs | _
              · simp [shapeOfHOLExact, shapeEqHOL] at htwo
              · rcases vs with _ | ⟨u0, _ | ⟨u1, _ | _⟩⟩
                · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at htwo
                · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at htwo
                · rcases u0 with ⟨⟨w0⟩⟩ | _ | _ <;> rcases u1 with ⟨⟨w1⟩⟩ | _ | _
                  · have hlf_ce : LocFrame (callEntryStateHOLFinite st callee) pb := by
                      have hres := hsafe.to_resumes (by rw [hrun]; exact Or.inl ⟨.rStruct [.val (.word w0), .val (.word w1)], rfl⟩)
                      simpa [hrun] using hres
                    have hlf_st : LocFrame st pb := by
                      unfold LocFrame at hlf_ce ⊢; rw [hlf_ce]; rfl
                    let st' := setVarHOLFinite nm (.rStruct [.val (.word w0), .val (.word w1)]) { pb with locals := st.locals }
                    exact ⟨w0, w1, st', hpb_c,
                      hlf.trans (hlf_st.with_locals_clock _ pb.clock),
                      rfl, ⟨vals, body, callee, rs, rfl, hl_orig, by rw [hrun]⟩, hr⟩
                  all_goals simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at htwo
                · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at htwo
              · simp [shapeOfHOLExact, shapeEqHOL] at htwo
            · simp at hr
          | _ => simp at hr

private theorem eps_extend_memory_cost2_copy_cov_g08 :
    EvmPreservingSpec (fun _ => True)
      (fun s v post =>
        LocFrame s post ∧
        ∃ cw ebw : BitVec 64,
          v = .rStruct [.val (.word cw), .val (.word ebw)] ∧
          (ebw = 0#64 ∨
            (memW s (globN s "ev" + 32) % 32 = 0 →
              memW s (globN s "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
              (memW s (globN s "ev" + 32) + ebw.toNat) % 8 = 0)) ∧
          (∀ (s1Val s2Val szVal : ValueHOL 64),
            s.locals.lookup (ofString "s1") = some s1Val →
            shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact s1Val) = true →
            s.locals.lookup (ofString "n1") = some szVal →
            s.locals.lookup (ofString "s2") = some s2Val →
            shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact s2Val) = true →
            s.locals.lookup (ofString "n2") = some szVal →
            shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact szVal) = true →
            satValue_g08 szVal ≠ 0#64 →
            cw.toNat < 2 ^ 64 - 1 →
            memW s (globN s "ev" + 32) % 32 = 0 →
            (satValue_g08 s1Val).toNat + (satValue_g08 szVal).toNat ≤ memW s (globN s "ev" + 32) + ebw.toNat ∧
            (satValue_g08 s2Val).toNat + (satValue_g08 szVal).toNat ≤ memW s (globN s "ev" + 32) + ebw.toNat))
      (ofString "extend_memory_cost2") := by
  refine ⟨_, _, _, lookup_extend_memory_cost2_g08, ?_⟩
  intro F s hcode hInv _ _ _
  have hnc := evaluate_noCatchableRaise_g08 emc2NcrCallees_g08 emc2NcrCallees_good_g08
    (sourceFnBody Guest.Software.guestFn_extend_memory_cost2) (by decide) s hcode
  dsimp only
  refine ⟨?_, fun ⟨ev, hev⟩ => False.elim (hnc (ofString "EvmErr") ev (by decide) hev)⟩
  intro v hv
  obtain ⟨hev_pos, _, hb_ev, _⟩ := head_ev_bounds_g08 hInv
  obtain ⟨evw, hevw_lk, hevw_nat⟩ := global_word_of_pos s "ev" hev_pos
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by simp [evmChain, evmChainFrom]
  have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead
  have hrec_w := (hFW0.1 (globN s "ev", 280) (by simp)).2
  obtain ⟨savedw, hdom32_raw, hmem32_raw⟩ := hrec_w.2.2 4 (by omega)
  have h32_eq : globN s "ev" + 8 * 4 = globN s "ev" + 32 := by omega
  rw [h32_eq] at hdom32_raw hmem32_raw
  have hsaved_nat : savedw.toNat = memW s (globN s "ev" + 32) := by
    unfold memW; rw [hmem32_raw]
  have h10 : ¬ ((1#64 : BitVec 64) = 0) := by decide
  have h00 : (0#64 : BitVec 64) = 0 := rfl
  have hbody : sourceFnBody Guest.Software.guestFn_extend_memory_cost2 =
      .decCall (ofString "a") (.comb [.one, .one]) (ofString "extend_memory_cost1")
        [.var .local (ofString "s1"), .var .local (ofString "n1")]
        (.seq
          (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "a"))) (.const 18446744073709551615#64))
            (.return (.var .local (ofString "a")))
            .skip)
          (.dec (ofString "saved") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 32#64]))
            (.seq
              (.store (.op .add [.var .global (ofString "ev"), .const 32#64])
                (.op .add [.var .local (ofString "saved"), .rfield 1 (.var .local (ofString "a"))]))
              (.decCall (ofString "b") (.comb [.one, .one]) (ofString "extend_memory_cost1")
                [.var .local (ofString "s2"), .var .local (ofString "n2")]
                (.seq
                  (.store (.op .add [.var .global (ofString "ev"), .const 32#64])
                    (.var .local (ofString "saved")))
                  (.seq
                    (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "b"))) (.const 18446744073709551615#64))
                      (.return (.var .local (ofString "b")))
                      .skip)
                    (.return (.rstruct
                      [.op .add [.rfield 0 (.var .local (ofString "a")), .rfield 0 (.var .local (ofString "b"))],
                       .op .add [.rfield 1 (.var .local (ofString "a")), .rfield 1 (.var .local (ofString "b"))]])))))))) := rfl
  rcases hfull : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_extend_memory_cost2) with ⟨res_top, post⟩
  rw [hfull] at hv; dsimp only at hv ⊢
  suffices hmain :
      LocFrame s post ∧
      ∃ cw ebw : BitVec 64,
        v = .rStruct [.val (.word cw), .val (.word ebw)] ∧
        (ebw = 0#64 ∨
          (memW s (globN s "ev" + 32) % 32 = 0 →
            memW s (globN s "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
            (memW s (globN s "ev" + 32) + ebw.toNat) % 8 = 0)) ∧
        (∀ (s1Val s2Val szVal : ValueHOL 64),
          s.locals.lookup (ofString "s1") = some s1Val →
          shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact s1Val) = true →
          s.locals.lookup (ofString "n1") = some szVal →
          s.locals.lookup (ofString "s2") = some s2Val →
          shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact s2Val) = true →
          s.locals.lookup (ofString "n2") = some szVal →
          shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact szVal) = true →
          satValue_g08 szVal ≠ 0#64 →
          cw.toNat < 2 ^ 64 - 1 →
          memW s (globN s "ev" + 32) % 32 = 0 →
          (satValue_g08 s1Val).toNat + (satValue_g08 szVal).toNat ≤ memW s (globN s "ev" + 32) + ebw.toNat ∧
          (satValue_g08 s2Val).toNat + (satValue_g08 szVal).toNat ≤ memW s (globN s "ev" + 32) + ebw.toNat) by
    obtain ⟨hlf, hrest⟩ := hmain
    have hInv_p : EvmInv post := by
      have h := localsFree_evmInv s post.locals post.clock hInv
      rwa [← hlf] at h
    have hm : post.memory = s.memory := by unfold LocFrame at hlf; conv_lhs => rw [hlf]
    have hg : post.globals = s.globals := by unfold LocFrame at hlf; conv_lhs => rw [hlf]
    have hc_eq := evm_congr hm hg
    exact ⟨hInv_p, evmChain_congr hm hg, le_of_eq hc_eq.2.1, hlf, hrest⟩
  have hret_top : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_extend_memory_cost2)).1 =
      some (.returned v) := by rw [hfull]; exact hv
  have hpost_eq : post = (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_extend_memory_cost2)).2 := by
    rw [hfull]
  rw [hbody] at hret_top hpost_eq
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hret_top hpost_eq
  rcases hargs1 : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x))
      [.var .local (ofString "s1"), .var .local (ofString "n1")] with _ | vals1
  · rw [hargs1] at hret_top; simp at hret_top
  · rw [hargs1] at hret_top hpost_eq; dsimp only at hret_top hpost_eq
    rcases hl1 : lookupCodeHOLFinite s.code.lookup (ofString "extend_memory_cost1") vals1 with _ | ⟨body1, cal1, rs1⟩
    · rw [hl1] at hret_top; simp at hret_top
    · rw [hl1] at hret_top hpost_eq; dsimp only at hret_top hpost_eq
      have hl1_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "extend_memory_cost1") vals1 =
          some (body1, cal1, rs1) := by rwa [← hcode]
      have hbody1_eq : body1 = sourceFnBody Guest.Software.guestFn_extend_memory_cost1 :=
        lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ _ _ _ vals1 cal1 lookup_extend_memory_cost1 hl1_orig
      subst hbody1_eq
      split at hret_top
      · simp at hret_top
      · rename_i hclk_s
        rw [if_neg hclk_s] at hpost_eq
        have hsafe1 := evaluate_readOnlyProg opRoCallees opRoCallees_good
          (sourceFnBody Guest.Software.guestFn_extend_memory_cost1)
          (opRoCallees_good (ofString "extend_memory_cost1") (by decide) vals1 _ cal1 rs1 hl1_orig)
          (callEntryStateHOLFinite s cal1) hcode
        rcases hrun1 : evaluateHOLFiniteState (callEntryStateHOLFinite s cal1)
            (sourceFnBody Guest.Software.guestFn_extend_memory_cost1) with ⟨rb1, pb1⟩
        rw [hrun1] at hret_top hpost_eq
        have hpb1_c : pb1.code = originalRuntimeCode := by
          have hm := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s cal1)
            (sourceFnBody Guest.Software.guestFn_extend_memory_cost1)).1
          rw [hrun1] at hm; exact hm.trans hcode
        rcases rb1 with _ | rb1
        · simp at hret_top
        · cases rb1 with
          | returned va =>
            dsimp only at hret_top hpost_eq
            split at hret_top
            · rename_i hsh_va
              rw [if_pos hsh_va] at hpost_eq; dsimp only at hret_top hpost_eq
              have hlf_ce1 : LocFrame (callEntryStateHOLFinite s cal1) pb1 := by
                have hres := hsafe1.to_resumes (by rw [hrun1]; exact Or.inl ⟨va, rfl⟩)
                simpa [hrun1] using hres
              have hlf_s_pb1 : LocFrame s pb1 := by unfold LocFrame at hlf_ce1 ⊢; rw [hlf_ce1]; rfl
              obtain ⟨a0, a1, rfl, ha0_max, ha0_lt56, ha_eb⟩ :=
                extend_memory_cost1_raw_bounds_g08 (callEntryStateHOLFinite s cal1) hcode va (by rw [hrun1])
              set s1 := setVarHOLFinite (ofString "a") (.rStruct [.val (.word a0), .val (.word a1)])
                { pb1 with locals := s.locals } with hs1_def
              have hs1_lf : LocFrame s s1 := hlf_s_pb1.with_locals_clock _ pb1.clock
              have hs1_c : s1.code = originalRuntimeCode := hpb1_c
              have hs1_a : s1.locals.lookup (ofString "a") = some (.rStruct [.val (.word a0), .val (.word a1)]) := by
                simp [hs1_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret_top hpost_eq
              have hcmp_a : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
                  (.cmp .equal (.rfield 0 (.var .local (ofString "a"))) (.const 18446744073709551615#64)) =
                  some (.val (.word (if a0 = 18446744073709551615#64 then (1#64 : BitVec 64) else 0#64))) := by
                simp [evalHOLExact, hs1_a, Compiler.Encoders.Asm.wordCmpHOL]
              rw [hcmp_a] at hret_top hpost_eq; dsimp only at hret_top hpost_eq
              by_cases ha0_eq_max : a0 = 18446744073709551615#64
              · rw [if_pos ha0_eq_max, if_neg h10] at hret_top hpost_eq
                rw [evaluateHOLFiniteState_return] at hret_top hpost_eq
                have hev_a : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
                    (.var .local (ofString "a")) = some (.rStruct [.val (.word a0), .val (.word a1)]) := hs1_a
                rw [hev_a] at hret_top hpost_eq; dsimp only at hret_top hpost_eq
                have hsz_a : sizeOfShapeWithContextHOL s1.structs
                    (shapeOfHOLExact (.rStruct [.val (.word a0), .val (.word a1)] : ValueHOL 64)) ≤ 32 := by
                  simp [shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
                rw [if_pos hsz_a] at hret_top hpost_eq; dsimp only at hret_top hpost_eq
                injection hret_top with h1; injection h1 with hv_eq
                have ha1_0 : a1 = 0#64 := ha0_max ha0_eq_max
                subst hv_eq ha0_eq_max ha1_0
                have hlf_post : LocFrame s post := by
                  rw [hpost_eq]
                  exact (hs1_lf.with_locals_clock _ s1.clock).with_locals_clock _ _
                refine ⟨hlf_post, 18446744073709551615#64, 0#64, rfl, Or.inl rfl, ?_⟩
                intro _ _ _ _ _ _ _ _ _ _ _ hlt _
                exact False.elim ((by decide : ¬ ((18446744073709551615#64 : BitVec 64).toNat < 2 ^ 64 - 1)) hlt)
              · rw [if_neg ha0_eq_max, if_pos h00, evaluateHOLFiniteState_skip] at hret_top hpost_eq
                dsimp only at hret_top hpost_eq
                have ha0_lt : a0.toNat < 2 ^ 56 := ha0_lt56 ha0_eq_max
                rw [evaluateHOLFiniteState_dec_total] at hret_top hpost_eq; dsimp only at hret_top hpost_eq
                have hs1_mem : s1.memory = s.memory := by unfold LocFrame at hs1_lf; conv_lhs => rw [hs1_lf]
                have hs1_glob : s1.globals = s.globals := by unfold LocFrame at hs1_lf; conv_lhs => rw [hs1_lf]
                have hs1_ma : s1.memaddrs = s.memaddrs := by unfold LocFrame at hs1_lf; conv_lhs => rw [hs1_lf]
                have hs1_st : s1.structs = s.structs := by unfold LocFrame at hs1_lf; conv_lhs => rw [hs1_lf]
                have had32 : evw + (32#64 + 0) = BitVec.ofNat 64 (globN s "ev" + 32) := by
                  apply BitVec.eq_of_toNat_eq
                  have hz0 : (0 : BitVec 64).toNat = 0 := rfl
                  have h32n : (32#64 : BitVec 64).toNat = 32 := rfl
                  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hevw_nat, hz0, h32n, Nat.add_zero,
                    Nat.mod_eq_of_lt (show 32 < 2 ^ 64 by omega),
                    Nat.mod_eq_of_lt (show globN s "ev" + 32 < 2 ^ 64 by omega)]
                have hml32 : @memLoadHOLExact 64 _ .one (BitVec.ofNat 64 (globN s "ev" + 32))
                    s1.memaddrs (fun a => Classical.propDecidable (s1.memaddrs a))
                    s1.memory s1.structs = some (.val (.word savedw)) := by
                  unfold memLoadHOLExact; rw [hs1_ma, hs1_mem, if_pos hdom32_raw, hmem32_raw]
                have hwf0 : isWfShapeExactHOL s1.structs .one = true := rfl
                have hld_saved : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
                    (.load .one (.op .add [.var .global (ofString "ev"), .const 32#64])) =
                    some (.val (.word savedw)) := by
                  have hevw_s1 : s1.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
                    rw [hs1_glob]; exact hevw_lk
                  simp only [evalHOLExact, evalListHOLExact, PanSemStateFiniteExact.toExact,
                    hevw_s1, hwf0, wordOpHOL, wordOp, valueIsWord, valueWord,
                    List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
                    had32, hml32]
                rw [hld_saved] at hret_top hpost_eq; dsimp only at hret_top hpost_eq
                have hsh_sav : shapeEqHOL .one (shapeOfHOLExact (.val (.word savedw))) = true := by
                  simp [shapeEqHOL, shapeOfHOLExact]
                rw [if_pos hsh_sav] at hret_top hpost_eq; dsimp only at hret_top hpost_eq
                set s2 := setVarHOLFinite (ofString "saved") (.val (.word savedw)) s1 with hs2_def
                have hs2_lf : LocFrame s s2 := hs1_lf.with_locals_clock _ s1.clock
                have hs2_saved : s2.locals.lookup (ofString "saved") = some (.val (.word savedw)) := by
                  simp [hs2_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                have hs2_a : s2.locals.lookup (ofString "a") = some (.rStruct [.val (.word a0), .val (.word a1)]) := by
                  simp [hs2_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_a,
                    show ofString "saved" ≠ ofString "a" by decide]
                rw [evaluateHOLFiniteState_seq_line780] at hret_top hpost_eq
                rcases hst1 : evaluateHOLFiniteState s2
                    (.store (.op .add [.var .global (ofString "ev"), .const 32#64])
                      (.op .add [.var .local (ofString "saved"), .rfield 1 (.var .local (ofString "a"))])) with ⟨rst1, s3⟩
                rw [hst1] at hret_top hpost_eq
                cases rst1 with
                | some err1 =>
                  have herr := store_some_eq_error_g08 hst1; subst herr; simp at hret_top
                | none =>
                  dsimp only at hret_top hpost_eq
                  have hs2_ev_lk : s2.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
                    change s1.globals.lookup _ = _; rw [hs1_glob]; exact hevw_lk
                  have hev_add_sa : @evalHOLExact 64 F _ s2.toExact (fun x => Classical.propDecidable (s2.memaddrs x))
                      (.op .add [.var .local (ofString "saved"), .rfield 1 (.var .local (ofString "a"))]) =
                      some (.val (.word (savedw + a1))) := by
                    simp [evalHOLExact, evalListHOLExact, hs2_saved, hs2_a, wordOpHOL, wordOp, valueIsWord, valueWord]
                  obtain ⟨w_st1, hw_st1_ev, hs3_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s2) (post := s3)
                    (gname := "ev") (gbase := globN s "ev") (off := 32) hs2_ev_lk hevw_nat (by omega)
                    (fun u hu => by rw [hev_add_sa] at hu; injection hu with hu'; exact ⟨savedw + a1, hu'.symm⟩) hst1
                  rw [hev_add_sa] at hw_st1_ev; injection hw_st1_ev with hw1'; injection hw1' with hw1''; injection hw1'' with hw1_eq; subst hw1_eq
                  have hs3_c : s3.code = originalRuntimeCode := by rw [hs3_eq]; exact hs1_c
                  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hret_top hpost_eq
                  rcases hargs2 : evalListHOLFinite s3 (h := fun x => Classical.propDecidable (s3.memaddrs x))
                      [.var .local (ofString "s2"), .var .local (ofString "n2")] with _ | vals2
                  · rw [hargs2] at hret_top; simp at hret_top
                  · rw [hargs2] at hret_top hpost_eq; dsimp only at hret_top hpost_eq
                    rcases hl2 : lookupCodeHOLFinite s3.code.lookup (ofString "extend_memory_cost1") vals2 with _ | ⟨body2, cal2, rs2⟩
                    · rw [hl2] at hret_top; simp at hret_top
                    · rw [hl2] at hret_top hpost_eq; dsimp only at hret_top hpost_eq
                      have hl2_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "extend_memory_cost1") vals2 =
                          some (body2, cal2, rs2) := by rwa [← hs3_c]
                      have hbody2_eq : body2 = sourceFnBody Guest.Software.guestFn_extend_memory_cost1 :=
                        lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ _ _ _ vals2 cal2 lookup_extend_memory_cost1 hl2_orig
                      subst hbody2_eq
                      split at hret_top
                      · simp at hret_top
                      · rename_i hclk_s3
                        rw [if_neg hclk_s3] at hpost_eq
                        have hsafe2 := evaluate_readOnlyProg opRoCallees opRoCallees_good
                          (sourceFnBody Guest.Software.guestFn_extend_memory_cost1)
                          (opRoCallees_good (ofString "extend_memory_cost1") (by decide) vals2 _ cal2 rs2 hl2_orig)
                          (callEntryStateHOLFinite s3 cal2) hs3_c
                        rcases hrun2 : evaluateHOLFiniteState (callEntryStateHOLFinite s3 cal2)
                            (sourceFnBody Guest.Software.guestFn_extend_memory_cost1) with ⟨rb2, pb2⟩
                        rw [hrun2] at hret_top hpost_eq
                        have hpb2_c : pb2.code = originalRuntimeCode := by
                          have hm := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s3 cal2)
                            (sourceFnBody Guest.Software.guestFn_extend_memory_cost1)).1
                          rw [hrun2] at hm; exact hm.trans hs3_c
                        rcases rb2 with _ | rb2
                        · simp at hret_top
                        · cases rb2 with
                          | returned vb =>
                            dsimp only at hret_top hpost_eq
                            split at hret_top
                            · rename_i hsh_vb
                              rw [if_pos hsh_vb] at hpost_eq; dsimp only at hret_top hpost_eq
                              have hlf_ce2 : LocFrame (callEntryStateHOLFinite s3 cal2) pb2 := by
                                have hres := hsafe2.to_resumes (by rw [hrun2]; exact Or.inl ⟨vb, rfl⟩)
                                simpa [hrun2] using hres
                              have hlf_s3_pb2 : LocFrame s3 pb2 := by unfold LocFrame at hlf_ce2 ⊢; rw [hlf_ce2]; rfl
                              obtain ⟨b0, b1, rfl, hb0_max, hb0_lt56, hb_eb⟩ :=
                                extend_memory_cost1_raw_bounds_g08 (callEntryStateHOLFinite s3 cal2) hs3_c vb (by rw [hrun2])
                              set s4 := setVarHOLFinite (ofString "b") (.rStruct [.val (.word b0), .val (.word b1)])
                                { pb2 with locals := s3.locals } with hs4_def
                              have hs4_lf_s3 : LocFrame s3 s4 := hlf_s3_pb2.with_locals_clock _ pb2.clock
                              have hs4_saved : s4.locals.lookup (ofString "saved") = some (.val (.word savedw)) := by
                                simp [hs4_def, hs3_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_saved,
                                  show ofString "b" ≠ ofString "saved" by decide]
                              have hs4_a : s4.locals.lookup (ofString "a") = some (.rStruct [.val (.word a0), .val (.word a1)]) := by
                                simp [hs4_def, hs3_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_a,
                                  show ofString "b" ≠ ofString "a" by decide]
                              have hs4_b : s4.locals.lookup (ofString "b") = some (.rStruct [.val (.word b0), .val (.word b1)]) := by
                                simp [hs4_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                              rw [evaluateHOLFiniteState_seq_line780] at hret_top hpost_eq
                              rcases hst2 : evaluateHOLFiniteState s4
                                  (.store (.op .add [.var .global (ofString "ev"), .const 32#64])
                                    (.var .local (ofString "saved"))) with ⟨rst2, s5⟩
                              rw [hst2] at hret_top hpost_eq
                              cases rst2 with
                              | some err2 =>
                                have herr := store_some_eq_error_g08 hst2; subst herr; simp at hret_top
                              | none =>
                                dsimp only at hret_top hpost_eq
                                have hs4_glob : s4.globals = s.globals := by
                                  have hg43 : s4.globals = s3.globals := by unfold LocFrame at hs4_lf_s3; conv_lhs => rw [hs4_lf_s3]
                                  rw [hg43, hs3_eq]; exact hs1_glob
                                have hs4_ev_lk : s4.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
                                  rw [hs4_glob]; exact hevw_lk
                                obtain ⟨w_st2, hw_st2_ev, hs5_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s4) (post := s5)
                                  (gname := "ev") (gbase := globN s "ev") (off := 32) hs4_ev_lk hevw_nat (by omega)
                                  (fun u hu => by
                                    change s4.locals.lookup (ofString "saved") = some u at hu
                                    rw [hs4_saved] at hu; injection hu with hu'; exact ⟨savedw, hu'.symm⟩) hst2
                                change s4.locals.lookup (ofString "saved") = some (.val (.word w_st2)) at hw_st2_ev
                                rw [hs4_saved] at hw_st2_ev; injection hw_st2_ev with hw2'; injection hw2' with hw2''; injection hw2'' with hw2_eq; subst hw2_eq
                                have hs5_mem : s5.memory = s.memory := by
                                  have hm43 : s4.memory = s3.memory := by unfold LocFrame at hs4_lf_s3; conv_lhs => rw [hs4_lf_s3]
                                  rw [hs5_eq, hm43, hs3_eq]
                                  funext x
                                  dsimp only [R14Shards.OpHandlersA.updW]
                                  by_cases hx : x = BitVec.ofNat 64 (globN s "ev" + 32)
                                  · subst hx; simp [hmem32_raw]
                                  · simp [hx, hs2_def, setVarHOLFinite, hs1_mem]
                                have hs5_lf : LocFrame s s5 := by
                                  have hs5_eq_from_s3 : s5 = { s3 with locals := s4.locals, clock := s4.clock, memory := s.memory } := by
                                    rw [hs5_eq]
                                    unfold LocFrame at hs4_lf_s3
                                    have hupd_eq : R14Shards.OpHandlersA.updW s4.memory (BitVec.ofNat 64 (globN s "ev" + 32)) savedw = s.memory := by
                                      rw [← hs5_mem, hs5_eq]
                                    rw [hupd_eq]
                                    conv_lhs => rw [hs4_lf_s3]
                                  rw [hs5_eq_from_s3, hs3_eq]
                                  unfold LocFrame at hs2_lf ⊢
                                  conv_lhs => rw [hs2_lf]
                                rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret_top hpost_eq
                                have hs5_b : s5.locals.lookup (ofString "b") = some (.rStruct [.val (.word b0), .val (.word b1)]) := by
                                  rw [hs5_eq]; exact hs4_b
                                have hs5_a : s5.locals.lookup (ofString "a") = some (.rStruct [.val (.word a0), .val (.word a1)]) := by
                                  rw [hs5_eq]; exact hs4_a
                                have hcmp_b : @evalHOLExact 64 F _ s5.toExact (fun x => Classical.propDecidable (s5.memaddrs x))
                                    (.cmp .equal (.rfield 0 (.var .local (ofString "b"))) (.const 18446744073709551615#64)) =
                                    some (.val (.word (if b0 = 18446744073709551615#64 then (1#64 : BitVec 64) else 0#64))) := by
                                  simp [evalHOLExact, hs5_b, Compiler.Encoders.Asm.wordCmpHOL]
                                rw [hcmp_b] at hret_top hpost_eq; dsimp only at hret_top hpost_eq
                                by_cases hb0_eq_max : b0 = 18446744073709551615#64
                                · rw [if_pos hb0_eq_max, if_neg h10] at hret_top hpost_eq
                                  rw [evaluateHOLFiniteState_return] at hret_top hpost_eq
                                  have hev_b : @evalHOLExact 64 F _ s5.toExact (fun x => Classical.propDecidable (s5.memaddrs x))
                                      (.var .local (ofString "b")) = some (.rStruct [.val (.word b0), .val (.word b1)]) := hs5_b
                                  rw [hev_b] at hret_top hpost_eq; dsimp only at hret_top hpost_eq
                                  have hsz_b : sizeOfShapeWithContextHOL s5.structs
                                      (shapeOfHOLExact (.rStruct [.val (.word b0), .val (.word b1)] : ValueHOL 64)) ≤ 32 := by
                                    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
                                  rw [if_pos hsz_b] at hret_top hpost_eq; dsimp only at hret_top hpost_eq
                                  injection hret_top with h1; injection h1 with hv_eq
                                  have hb1_0 : b1 = 0#64 := hb0_max hb0_eq_max
                                  subst hv_eq hb0_eq_max hb1_0
                                  have hlf_post : LocFrame s post := by
                                    rw [hpost_eq]
                                    exact (((hs5_lf.with_locals_clock _ s5.clock).with_locals_clock _ _).with_locals_clock _ _).with_locals_clock _ _
                                  refine ⟨hlf_post, 18446744073709551615#64, 0#64, rfl, Or.inl rfl, ?_⟩
                                  intro _ _ _ _ _ _ _ _ _ _ _ hlt _
                                  exact False.elim ((by decide : ¬ ((18446744073709551615#64 : BitVec 64).toNat < 2 ^ 64 - 1)) hlt)
                                · rw [if_neg hb0_eq_max, if_pos h00, evaluateHOLFiniteState_skip] at hret_top hpost_eq
                                  dsimp only at hret_top hpost_eq
                                  have hb0_lt : b0.toNat < 2 ^ 56 := hb0_lt56 hb0_eq_max
                                  rw [evaluateHOLFiniteState_return] at hret_top hpost_eq
                                  have hev_ret : @evalHOLExact 64 F _ s5.toExact (fun x => Classical.propDecidable (s5.memaddrs x))
                                      (.rstruct
                                        [.op .add [.rfield 0 (.var .local (ofString "a")), .rfield 0 (.var .local (ofString "b"))],
                                         .op .add [.rfield 1 (.var .local (ofString "a")), .rfield 1 (.var .local (ofString "b"))]]) =
                                      some (.rStruct [.val (.word (a0 + b0)), .val (.word (a1 + b1))]) := by
                                    simp [evalHOLExact, evalListHOLExact, hs5_a, hs5_b, wordOpHOL, wordOp, valueIsWord, valueWord]
                                  rw [hev_ret] at hret_top hpost_eq; dsimp only at hret_top hpost_eq
                                  have hsz_ret : sizeOfShapeWithContextHOL s5.structs
                                      (shapeOfHOLExact (.rStruct [.val (.word (a0 + b0)), .val (.word (a1 + b1))] : ValueHOL 64)) ≤ 32 := by
                                    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
                                  rw [if_pos hsz_ret] at hret_top hpost_eq; dsimp only at hret_top hpost_eq
                                  injection hret_top with h1; injection h1 with hv_eq
                                  subst hv_eq
                                  have hlf_post : LocFrame s post := by
                                    rw [hpost_eq]
                                    exact (((hs5_lf.with_locals_clock _ s5.clock).with_locals_clock _ _).with_locals_clock _ _).with_locals_clock _ _
                                  have hce1_ev32 : memW (callEntryStateHOLFinite s cal1)
                                      (globN (callEntryStateHOLFinite s cal1) "ev" + 32) = memW s (globN s "ev" + 32) := rfl
                                  have ha_align_props : memW s (globN s "ev" + 32) % 32 = 0 →
                                      (a1 = 0#64 ∨ (memW s (globN s "ev" + 32) + a1.toNat < 2 ^ 37 ∧
                                        (memW s (globN s "ev" + 32) + a1.toNat) % 32 = 0)) := by
                                    intro hmod32
                                    rcases ha_eb with rfl | ⟨bef1, aft1, haft1_lt, haft1_mod, hbef1_lt, ha1_sub, hbef1_eq⟩
                                    · exact Or.inl rfl
                                    · right
                                      have hb1_eq := hbef1_eq (by rw [hce1_ev32]; exact hmod32)
                                      rw [hce1_ev32] at hb1_eq
                                      have hsum1 : memW s (globN s "ev" + 32) + a1.toNat = aft1 := by omega
                                      rw [hsum1]
                                      exact ⟨haft1_lt, haft1_mod⟩
                                  have hs3_ev_eq : globN s3 "ev" = globN s "ev" :=
                                    globN_eq_of_lookup_eq (by rw [hs3_eq]; exact hs1_glob.symm ▸ rfl)
                                  have hs3_mem32_raw : memW s3 (globN s3 "ev" + 32) = (savedw + a1).toNat := by
                                    rw [hs3_ev_eq, hs3_eq, R14Shards.OpHandlersA.memW_updW_same s2 (globN s "ev" + 32) (savedw + a1)]
                                  have hce2_ev32 : memW (callEntryStateHOLFinite s3 cal2)
                                      (globN (callEntryStateHOLFinite s3 cal2) "ev" + 32) = (savedw + a1).toNat := hs3_mem32_raw
                                  refine ⟨hlf_post, a0 + b0, a1 + b1, rfl, ?_, ?_⟩
                                  · by_cases hab0 : a1 + b1 = 0#64
                                    · exact Or.inl hab0
                                    · right
                                      intro hmod32
                                      have ha_pr := ha_align_props hmod32
                                      rcases ha_pr with ha1_z | ⟨ha_lt37, ha_mod32⟩
                                      · subst ha1_z
                                        have h1_zero : (0#64 : BitVec 64).toNat = 0 := rfl
                                        have hsav_add0 : savedw + 0#64 = savedw := BitVec.add_zero savedw
                                        have hce2_eq_s : memW (callEntryStateHOLFinite s3 cal2)
                                            (globN (callEntryStateHOLFinite s3 cal2) "ev" + 32) = memW s (globN s "ev" + 32) := by
                                          rw [hce2_ev32, hsav_add0, hsaved_nat]
                                        rcases hb_eb with hb1_z | ⟨bef2, aft2, haft2_lt, haft2_mod, hbef2_lt, hb1_sub, hbef2_eq⟩
                                        · subst hb1_z; exact absurd rfl hab0
                                        · have hb2_eq := hbef2_eq (by rw [hce2_eq_s]; exact hmod32)
                                          rw [hce2_eq_s] at hb2_eq
                                          have h0b : (0#64 + b1).toNat = b1.toNat := by simp
                                          rw [h0b]
                                          have hsum2 : memW s (globN s "ev" + 32) + b1.toNat = aft2 := by omega
                                          rw [hsum2]
                                          exact ⟨haft2_lt, by omega⟩
                                      · have hsav_a1_nat : (savedw + a1).toNat = memW s (globN s "ev" + 32) + a1.toNat := by
                                          rw [BitVec.toNat_add, hsaved_nat,
                                            Nat.mod_eq_of_lt (show memW s (globN s "ev" + 32) + a1.toNat < 2 ^ 64 by omega)]
                                        have hce2_eq : memW (callEntryStateHOLFinite s3 cal2)
                                            (globN (callEntryStateHOLFinite s3 cal2) "ev" + 32) = memW s (globN s "ev" + 32) + a1.toNat := by
                                          rw [hce2_ev32, hsav_a1_nat]
                                        rcases hb_eb with hb1_z | ⟨bef2, aft2, haft2_lt, haft2_mod, hbef2_lt, hb1_sub, hbef2_eq⟩
                                        · subst hb1_z
                                          have ha0_b : (a1 + 0#64).toNat = a1.toNat := by simp
                                          rw [ha0_b]
                                          exact ⟨ha_lt37, by omega⟩
                                        · have hb2_eq := hbef2_eq (by rw [hce2_eq]; exact ha_mod32)
                                          rw [hce2_eq] at hb2_eq
                                          have hab_sum_lt : a1.toNat + b1.toNat < 2 ^ 64 := by omega
                                          have hab_nat : (a1 + b1).toNat = a1.toNat + b1.toNat := by
                                            rw [BitVec.toNat_add, Nat.mod_eq_of_lt hab_sum_lt]
                                          rw [hab_nat]
                                          have hsum2 : memW s (globN s "ev" + 32) + (a1.toNat + b1.toNat) = aft2 := by omega
                                          rw [hsum2]
                                          exact ⟨haft2_lt, by omega⟩
                                  · intro s1Val s2Val szVal hs1_lk hs1_sh hn1_lk hs2_lk hs2_sh hn2_lk hsz_sh hsz_nz _ hmod32
                                    obtain ⟨k0, k1, k2, k3, rfl⟩ := u256_value_of_shape_g08 hsz_sh
                                    have hvals1_eq : vals1 = [s1Val, .rStruct [.val (.word k0), .val (.word k1), .val (.word k2), .val (.word k3)]] := by
                                      rw [evalListHOLFinite_eq_toExact] at hargs1
                                      simpa [evalListHOLExact, evalHOLExact, hs1_lk, hn1_lk] using hargs1.symm
                                    subst hvals1_eq
                                    obtain ⟨w1a, w1b, hw1_eq, _, _, hcal1_st, hcal1_sz⟩ := extend_memory_cost1_two_args_lookup_g08 hl1_orig
                                    injection hw1_eq with hw1a_eq hw1b_tail
                                    injection hw1b_tail with hw1b_eq _
                                    subst hw1a_eq hw1b_eq
                                    have hs3_s2_lk : s3.locals.lookup (ofString "s2") = some s2Val := by
                                      rw [hs3_eq]
                                      simp [hs2_def, hs1_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_lk,
                                        show ofString "saved" ≠ ofString "s2" by decide,
                                        show ofString "a" ≠ ofString "s2" by decide]
                                    have hs3_n2_lk : s3.locals.lookup (ofString "n2") =
                                        some (.rStruct [.val (.word k0), .val (.word k1), .val (.word k2), .val (.word k3)]) := by
                                      rw [hs3_eq]
                                      simp [hs2_def, hs1_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn2_lk,
                                        show ofString "saved" ≠ ofString "n2" by decide,
                                        show ofString "a" ≠ ofString "n2" by decide]
                                    have hvals2_eq : vals2 = [s2Val, .rStruct [.val (.word k0), .val (.word k1), .val (.word k2), .val (.word k3)]] := by
                                      rw [evalListHOLFinite_eq_toExact] at hargs2
                                      simpa [evalListHOLExact, evalHOLExact, hs3_s2_lk, hs3_n2_lk] using hargs2.symm
                                    subst hvals2_eq
                                    obtain ⟨w2a, w2b, hw2_eq, _, _, hcal2_st, hcal2_sz⟩ := extend_memory_cost1_two_args_lookup_g08 hl2_orig
                                    injection hw2_eq with hw2a_eq hw2b_tail
                                    injection hw2b_tail with hw2b_eq _
                                    subst hw2a_eq hw2b_eq
                                    have hcov1 := extend_memory_cost1_copy_coverage_g08
                                      (callEntryStateHOLFinite s cal1) s1Val k0 k1 k2 k3 hcode
                                      (by simpa [callEntryStateHOLFinite] using hcal1_st) hs1_sh
                                      (by simpa [callEntryStateHOLFinite] using hcal1_sz) hsz_nz (.rStruct [.val (.word a0), .val (.word a1)])
                                      (by rw [hrun1]) a0 a1 rfl (by omega) (by rw [hce1_ev32]; exact hmod32)
                                    rw [hce1_ev32] at hcov1
                                    have ha_pr := ha_align_props hmod32
                                    have ha1_bound : memW s (globN s "ev" + 32) + a1.toNat < 2 ^ 37 ∧
                                        (memW s (globN s "ev" + 32) + a1.toNat) % 32 = 0 := by
                                      rcases ha_pr with ha1_z | hpr
                                      · subst ha1_z
                                        have h1_zero : (0#64 : BitVec 64).toNat = 0 := rfl
                                        rw [h1_zero, Nat.add_zero]
                                        have hlen_lt : memW s (globN s "ev" + 32) < 2 ^ 37 := by
                                          have hnz_pos : 0 < (satValue_g08 (.rStruct [.val (.word k0), .val (.word k1), .val (.word k2), .val (.word k3)])).toNat := by
                                            by_contra hz
                                            apply hsz_nz
                                            exact BitVec.eq_of_toNat_eq (by omega)
                                          rcases ha_eb with ha1_0_again | ⟨bef1, aft1, haft1_lt, _, _, ha1_sub, _⟩
                                          · have hmem := hFW0.2.1.2
                                            have hcap := hFW0.2.2.2.2.2.2.1
                                            have hfp := hInv.1.2.2.2.2.1
                                            have hsp := hInv.1.2.2.2.2.2.1
                                            dsimp only at hmem hcap
                                            rw [R11Shards.scratchEnd_val] at hsp
                                            omega
                                          · omega
                                        exact ⟨hlen_lt, hmod32⟩
                                      · exact hpr
                                    have hsav_a1_nat : (savedw + a1).toNat = memW s (globN s "ev" + 32) + a1.toNat := by
                                      rw [BitVec.toNat_add, hsaved_nat,
                                        Nat.mod_eq_of_lt (show memW s (globN s "ev" + 32) + a1.toNat < 2 ^ 64 by omega)]
                                    have hce2_eq : memW (callEntryStateHOLFinite s3 cal2)
                                        (globN (callEntryStateHOLFinite s3 cal2) "ev" + 32) = memW s (globN s "ev" + 32) + a1.toNat := by
                                      rw [hce2_ev32, hsav_a1_nat]
                                    have hcov2 := extend_memory_cost1_copy_coverage_g08
                                      (callEntryStateHOLFinite s3 cal2) s2Val k0 k1 k2 k3 hs3_c
                                      (by simpa [callEntryStateHOLFinite] using hcal2_st) hs2_sh
                                      (by simpa [callEntryStateHOLFinite] using hcal2_sz) hsz_nz (.rStruct [.val (.word b0), .val (.word b1)])
                                      (by rw [hrun2]) b0 b1 rfl (by omega) (by rw [hce2_eq]; exact ha1_bound.2)
                                    rw [hce2_eq] at hcov2
                                    have hb1_lt37 : memW s (globN s "ev" + 32) + a1.toNat + b1.toNat < 2 ^ 37 := by
                                      rcases hb_eb with rfl | ⟨bef2, aft2, haft2_lt, _, _, hb1_sub, hbef2_eq⟩
                                      · have hz : (0#64 : BitVec 64).toNat = 0 := rfl
                                        rw [hz]; omega
                                      · have hb2_eq := hbef2_eq (by rw [hce2_eq]; exact ha1_bound.2)
                                        rw [hce2_eq] at hb2_eq
                                        omega
                                    have hab_nat : (a1 + b1).toNat = a1.toNat + b1.toNat := by
                                      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (show a1.toNat + b1.toNat < 2 ^ 64 by omega)]
                                    rw [hab_nat]
                                    exact ⟨by omega, by omega⟩
                            · simp at hret_top
                          | _ => simp at hret_top
            · simp at hret_top
          | _ => simp at hret_top

private theorem eval_ev24_add_local_globals_congr_g08 {F : Type}
    (u v : PanSemStateFiniteExact 64 F) (nm : MlS)
    (hev : u.globals.lookup (ofString "ev") = v.globals.lookup (ofString "ev"))
    (hloc : u.locals.lookup nm = v.locals.lookup nm)
    (hma : u.memaddrs = v.memaddrs)
    (hmem : u.memory = v.memory)
    (hst : u.structs = v.structs) :
    @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
      (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local nm]) =
    @evalHOLExact 64 F _ v.toExact (fun a => Classical.propDecidable (v.memaddrs a))
      (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local nm]) := by
  cases u; cases v
  dsimp only at hev hloc hma hmem hst
  subst hma; subst hmem; subst hst
  simp only [evalHOLExact, evalListHOLExact, PanSemStateFiniteExact.toExact, hev, hloc]

private theorem memB_eq_of_memory_be_g08 {F : Type}
    (u v : PanSemStateFiniteExact 64 F) (b : Nat)
    (hmem : u.memory = v.memory) (hbe : u.be = v.be) :
    memB u b = memB v b := by
  unfold memB
  rw [hmem, hbe]

private def mcopyArgs_g08 (dstVal srcVal lenVal : ValueHOL 64) : List (MlS × ValueHOL 64) :=
  [(ofString "n", .val (.word (satValue_g08 lenVal))), (ofString "len", lenVal),
   (ofString "src", srcVal), (ofString "dst", dstVal)]

private def mcopyWriteInnerProg_g08 : ProgHOL 64 :=
  .decCall (ofString "mark") .one (ofString "heap_mark") []
    (.decCall (ofString "tmp") .one (ofString "alloc") [.var .local (ofString "n")]
      (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "tmp"),
           .op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]),
             .var .local (ofString "s")],
           .var .local (ofString "n")])
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]),
               .var .local (ofString "d")],
             .var .local (ofString "tmp"),
             .var .local (ofString "n")])
          (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")]))))

private def mcopyWriteProg_g08 : ProgHOL 64 :=
  .decCall (ofString "d") .one (ofString "sat_word") [.var .local (ofString "dst")]
    (.decCall (ofString "s") .one (ofString "sat_word") [.var .local (ofString "src")]
      mcopyWriteInnerProg_g08)

private def mcopyTailProg_g08 : ProgHOL 64 :=
  .seq (.ite (.cmp .notEqual (.var .local (ofString "n")) (.const 0#64)) mcopyWriteProg_g08 .skip)
    copyFinishProg_g08

private theorem mcopy_err_pair_g08 :
    ((some (.error : PanSemResultExact 64) = none →
      ∀ P : Prop, P) ∧
     (some (.error : PanSemResultExact 64) ≠ none →
      (∀ v, some (.error : PanSemResultExact 64) ≠ some (.returned v)) ∧ ¬ IsEvmErr (some .error))) := by
  refine ⟨?_, ?_⟩
  · intro h; cases h
  · intro _
    refine ⟨?_, ?_⟩
    · intro _ h; cases h
    · rintro ⟨_, h⟩; cases h

private theorem mcopy_other_pair_g08 {r : Option (PanSemResultExact 64)}
    (hne : r ≠ none) (hnr : ∀ v, r ≠ some (.returned v)) (hne_err : ¬ IsEvmErr r) :
    (r = none → ∀ P : Prop, P) ∧
    (r ≠ none → (∀ v, r ≠ some (.returned v)) ∧ ¬ IsEvmErr r) :=
  ⟨fun h => False.elim (hne h), fun _ => ⟨hnr, hne_err⟩⟩

private theorem mcopy_write_inner_eff_g08 {F : Type}
    (t : PanSemStateFiniteExact 64 F) (dw sw nw : BitVec 64)
    (hc : t.code = originalRuntimeCode) (hInv : EvmInv t)
    (hd : t.locals.lookup (ofString "d") = some (.val (.word dw)))
    (hs : t.locals.lookup (ofString "s") = some (.val (.word sw)))
    (hn : t.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hnz : nw ≠ 0#64)
    (hcov : dw.toNat + nw.toNat ≤ memW t (globN t "ev" + 32))
    (hnt : (evaluateHOLFiniteState t mcopyWriteInnerProg_g08).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState t mcopyWriteInnerProg_g08
    (out.1 = none → out.2.code = originalRuntimeCode ∧ EvmInv out.2 ∧
      evmChain out.2 = evmChain t ∧ evmR out.2 = evmR t) ∧
    (out.1 ≠ none → (∀ v, out.1 ≠ some (.returned v)) ∧ ¬ IsEvmErr out.1) := by
  dsimp only [mcopyWriteInnerProg_g08] at hnt ⊢
  have hhp_mem : "heap_ptr" ∈ guestGlobalNames := by decide
  obtain ⟨markw, hmark_gw⟩ := hInv.1.2.2.2.2.2.2.2.2.2 "heap_ptr" hhp_mem
  have hmark_lk : t.globals.lookup (ofString "heap_ptr") = some (.val (.word markw)) := hmark_gw
  have hmark_nat : markw.toNat = globN t "heap_ptr" := by simp [globN, hmark_lk]
  have hmark_le : markw.toNat ≤ InitECandidate.Solver.HeapPotential.cMax.toNat := by
    have h1 := hInv.1.2.2.1; rw [hmark_nat]; exact h1
  have hmark_8 : markw.toNat % 8 = 0 := by
    rw [hmark_nat]; exact hInv.1.2.2.2.2.2.2.1
  have hnpos : 0 < nw.toNat := by
    have hne : nw.toNat ≠ 0 := by
      intro h; apply hnz; exact BitVec.eq_of_toNat_eq h
    omega
  -- Step 1: `decCall "mark" .one "heap_mark" []`
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  have hargs_hm : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) [] = some [] := rfl
  have hlook_hm := pan_zero_arg_lookup t.code.lookup (ofString "heap_mark")
    (sourceFnBody Guest.Software.guestFn_heap_mark) .one (by rw [hc]; exact lookup_heap_mark)
  rw [hargs_hm] at hnt ⊢; dsimp only at hnt ⊢
  rw [hlook_hm] at hnt ⊢; dsimp only at hnt ⊢
  by_cases hclk0 : t.clock = 0
  · simp [hclk0] at hnt
  · rw [if_neg hclk0] at hnt ⊢
    have hhm_body : evaluateHOLFiniteState (callEntryStateHOLFinite t HolFiniteMapExact.empty)
        (sourceFnBody Guest.Software.guestFn_heap_mark) =
        (some (.returned (.val (.word markw))),
         emptyLocalsHOLFinite (callEntryStateHOLFinite t HolFiniteMapExact.empty)) := by
      dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_heap_mark,
        InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural]
      rw [evaluateHOLFiniteState_return]
      have hev_hp : @evalHOLExact 64 F _ (callEntryStateHOLFinite t HolFiniteMapExact.empty).toExact
          (fun a => Classical.propDecidable ((callEntryStateHOLFinite t HolFiniteMapExact.empty).memaddrs a))
          (.var .global (ofString "heap_ptr")) = some (.val (.word markw)) := hmark_lk
      rw [hev_hp]; dsimp only
      have hsz : sizeOfShapeWithContextHOL (callEntryStateHOLFinite t HolFiniteMapExact.empty).structs
          (shapeOfHOLExact (.val (.word markw) : ValueHOL 64)) ≤ 32 := by
        simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
      rw [if_pos hsz]
    rw [hhm_body] at hnt ⊢; dsimp only at hnt ⊢
    have hsh_hm : shapeEqHOL (shapeOfHOLExact (.val (.word markw) : ValueHOL 64)) .one = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    simp only [hsh_hm, Bool.and_self, ↓reduceIte] at hnt ⊢
    let t1 := setVarHOLFinite (ofString "mark") (.val (.word markw))
      { emptyLocalsHOLFinite (callEntryStateHOLFinite t HolFiniteMapExact.empty) with locals := t.locals }
    have ht1_n : t1.locals.lookup (ofString "n") = some (.val (.word nw)) := by
      simp [t1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
        show ofString "mark" ≠ ofString "n" by decide]
    have ht1_d : t1.locals.lookup (ofString "d") = some (.val (.word dw)) := by
      simp [t1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd,
        show ofString "mark" ≠ ofString "d" by decide]
    have ht1_s : t1.locals.lookup (ofString "s") = some (.val (.word sw)) := by
      simp [t1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs,
        show ofString "mark" ≠ ofString "s" by decide]
    have ht1_mark : t1.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
      simp [t1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    -- Step 2: `decCall "tmp" .one "alloc" [.var .local "n"]` on `t1`
    have hnt1 : (evaluateHOLFiniteState t1
        (.decCall (ofString "tmp") .one (ofString "alloc") [.var .local (ofString "n")]
          (.seq
            (.call (some (none, none)) (ofString "memcpy")
              [.var .local (ofString "tmp"),
               .op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]),
                 .var .local (ofString "s")],
               .var .local (ofString "n")])
            (.seq
              (.call (some (none, none)) (ofString "memcpy")
                [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]),
                   .var .local (ofString "d")],
                 .var .local (ofString "tmp"),
                 .var .local (ofString "n")])
              (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")]))))).1 ≠ some .timeOut := hnt
    clear hnt
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt1 ⊢
    have hargs_al : evalListHOLFinite t1 (h := fun a => Classical.propDecidable (t1.memaddrs a))
        [.var .local (ofString "n")] = some [.val (.word nw)] := by
      rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, evalHOLExact, ht1_n]
    have hlook_al := pan_one_word_lookup t1.code.lookup (ofString "alloc") (ofString "n")
      (sourceFnBody Guest.Software.guestFn_alloc) nw (by change t.code.lookup _ = _; rw [hc]; exact lookup_alloc)
    rw [hargs_al] at hnt1 ⊢; dsimp only at hnt1 ⊢
    rw [hlook_al] at hnt1 ⊢; dsimp only at hnt1 ⊢
    by_cases hclk1 : t1.clock = 0
    · simp [hclk1] at hnt1
    · rw [if_neg hclk1] at hnt1 ⊢
      let cal_al := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word nw))
      let ent_al := callEntryStateHOLFinite t1 cal_al
      have hne_al : ¬ IsEvmErr (evaluateHOLFiniteState ent_al (sourceFnBody Guest.Software.guestFn_alloc)).1 :=
        alloc_body_no_evmErr ent_al hc
      have hal_gen := Wave8GuestInv.M13.evaluate_alloc_body_general ent_al markw nw hc hmark_le hmark_lk
        (by simp [ent_al, cal_al, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      have hal_meta := PanRunBounded.evaluateHOLFiniteState_metadata ent_al (sourceFnBody Guest.Software.guestFn_alloc)
      have hal_ba := evaluate_baseAddr ent_al (sourceFnBody Guest.Software.guestFn_alloc)
      rcases hrun_al : evaluateHOLFiniteState ent_al (sourceFnBody Guest.Software.guestFn_alloc) with ⟨ral, sal⟩
      change (match evaluateHOLFiniteState ent_al (sourceFnBody Guest.Software.guestFn_alloc) with | _ => _) ≠ _ at hnt1
      rw [hrun_al] at hne_al hal_gen hal_meta hal_ba
      try rw [hrun_al] at hnt1
      dsimp only at hnt1 hal_gen hal_meta hal_ba ⊢
      cases ral with
      | none =>
        dsimp only
        exact ⟨fun h => mcopy_err_pair_g08.1 h _, mcopy_err_pair_g08.2⟩
      | some ral0 =>
        cases ral0 with
        | timeOut => simp at hnt1
        | «break» | «continue» | error =>
          dsimp only
          exact ⟨fun h => mcopy_err_pair_g08.1 h _, mcopy_err_pair_g08.2⟩
        | finalFfi ev_ffi =>
          dsimp only
          have hp := mcopy_other_pair_g08 (r := some (.finalFfi ev_ffi)) (by simp) (fun _ h => by cases h) (by rintro ⟨_, h⟩; cases h)
          exact ⟨fun h => hp.1 h _, hp.2⟩
        | exception eid ev =>
          dsimp only
          have hp := mcopy_other_pair_g08 (r := some (.exception eid ev)) (by simp) (fun _ h => by cases h)
            (by rintro ⟨v, h⟩; injection h with h'; injection h' with he hw; exact hne_al ⟨v, by rw [he, hw]⟩)
          exact ⟨fun h => hp.1 h _, hp.2⟩
        | returned val_al =>
          obtain ⟨rfl, hsal_glob, hsal_mem, hq_ge, hq_le_cMax, _⟩ := hal_gen val_al rfl
          let q : BitVec 64 := (markw + (nw + 7)) &&& ((0 : BitVec 64) - 8)
          have hsal_glob' : sal.globals = t.globals.update (ofString "heap_ptr", .val (.word q)) := hsal_glob
          have hsal_mem' : sal.memory = t.memory := hsal_mem
          have hsh_al : shapeEqHOL (shapeOfHOLExact (.val (.word markw) : ValueHOL 64)) .one = true := by
            simp [shapeOfHOLExact, shapeEqHOL]
          simp only [hsh_al, Bool.and_self, ↓reduceIte] at hnt1 ⊢
          let t2 := setVarHOLFinite (ofString "tmp") (.val (.word markw)) { sal with locals := t1.locals }
          have ht2_code : t2.code = originalRuntimeCode := hal_meta.1.trans hc
          have ht2_ma : t2.memaddrs = t.memaddrs := hal_meta.2.1
          have ht2_be : t2.be = t.be := hal_meta.2.2.1
          have ht2_sh : t2.shMemaddrs = t.shMemaddrs := hal_meta.2.2.2.1
          have ht2_ba : t2.baseAddr = t.baseAddr := hal_ba
          have ht2_glob : t2.globals = t.globals.update (ofString "heap_ptr", .val (.word q)) := hsal_glob'
          have ht2_mem : t2.memory = t.memory := hsal_mem'
          have ht2_tmp : t2.locals.lookup (ofString "tmp") = some (.val (.word markw)) := by
            simp [t2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have ht2_n : t2.locals.lookup (ofString "n") = some (.val (.word nw)) := by
            simp [t2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht1_n,
              show ofString "tmp" ≠ ofString "n" by decide]
          have ht2_d : t2.locals.lookup (ofString "d") = some (.val (.word dw)) := by
            simp [t2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht1_d,
              show ofString "tmp" ≠ ofString "d" by decide]
          have ht2_s : t2.locals.lookup (ofString "s") = some (.val (.word sw)) := by
            simp [t2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht1_s,
              show ofString "tmp" ≠ ofString "s" by decide]
          have ht2_mark : t2.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
            simp [t2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht1_mark,
              show ofString "tmp" ≠ ofString "mark" by decide]
          -- Synthetic state `u0 := { t2 with globals := t.globals }` to evaluate `*(ev+24) + s`
          let u0 : PanSemStateFiniteExact 64 F := { t2 with globals := t.globals }
          have heff_t_u0 : ByteRegionEffect t u0 [(markw.toNat, 0)] :=
            ⟨ht2_code.trans hc.symm, ht2_ma, ht2_sh, ht2_ba, ht2_be, rfl,
             fun a _ => by change t2.memory a = t.memory a; rw [ht2_mem],
             fun a _ => by change t2.memory a = t.memory a; rw [ht2_mem],
             fun b _ _ => memB_eq_of_memory_be_g08 u0 t b ht2_mem ht2_be⟩
          obtain ⟨hInv_u0, _, _⟩ := heapGap_bre_to_evmStep_g08 hInv hmark_nat (by omega) hmark_8 heff_t_u0
          obtain ⟨srcbase, _, hsrc_u0⟩ := eval_head_mem_plus_local_g08 u0 hInv_u0 "s" sw ht2_s
          have hev_t2_u0 : t2.globals.lookup (ofString "ev") = u0.globals.lookup (ofString "ev") := by
            change t2.globals.lookup (ofString "ev") = t.globals.lookup (ofString "ev")
            rw [ht2_glob]
            simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "ev" by decide]
          have hsrc_t2 : @evalHOLExact 64 F _ t2.toExact (fun a => Classical.propDecidable (t2.memaddrs a))
              (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]),
                .var .local (ofString "s")]) = some (.val (.word (srcbase + sw))) := by
            rw [eval_ev24_add_local_globals_congr_g08 t2 u0 (ofString "s") hev_t2_u0 rfl rfl rfl rfl]
            exact hsrc_u0
          -- Step 3: first `memcpy(tmp, *(ev+24) + s, n)` on `t2`
          let mc1 : ProgHOL 64 := ProgHOL.call (some (none, none)) (ofString "memcpy")
            [.var .local (ofString "tmp"),
             .op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]),
               .var .local (ofString "s")],
             .var .local (ofString "n")]
          let mc2 : ProgHOL 64 := ProgHOL.call (some (none, none)) (ofString "memcpy")
            [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]),
               .var .local (ofString "d")],
             .var .local (ofString "tmp"),
             .var .local (ofString "n")]
          let hrp : ProgHOL 64 := ProgHOL.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")]
          change (evaluateHOLFiniteState t2 (.seq mc1 (.seq mc2 hrp))).1 ≠ some .timeOut at hnt1
          let post_outer := fun out : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F =>
            (out.1 = none → out.2.code = originalRuntimeCode ∧ EvmInv out.2 ∧
              evmChain out.2 = evmChain t ∧ evmR out.2 = evmR t) ∧
            (out.1 ≠ none → (∀ v, out.1 ≠ some (.returned v)) ∧ ¬ IsEvmErr out.1)
          suffices hseq1 : post_outer (evaluateHOLFiniteState t2 (.seq mc1 (.seq mc2 hrp))) by
            dsimp only [post_outer] at hseq1
            change ((evaluateHOLFiniteState t2 (.seq mc1 (.seq mc2 hrp))).1 = none →
              (let post1 := { (evaluateHOLFiniteState t2 (.seq mc1 (.seq mc2 hrp))).2 with
                locals := (evaluateHOLFiniteState t2 (.seq mc1 (.seq mc2 hrp))).2.locals.resVarEq (ofString "tmp", t1.locals.lookup (ofString "tmp")) }
               let post0 := { post1 with locals := post1.locals.resVarEq (ofString "mark", t.locals.lookup (ofString "mark")) }
               post0.code = originalRuntimeCode ∧ EvmInv post0 ∧ evmChain post0 = evmChain t ∧ evmR post0 = evmR t)) ∧
              ((evaluateHOLFiniteState t2 (.seq mc1 (.seq mc2 hrp))).1 ≠ none →
                (∀ v, (evaluateHOLFiniteState t2 (.seq mc1 (.seq mc2 hrp))).1 ≠ some (.returned v)) ∧
                ¬ IsEvmErr (evaluateHOLFiniteState t2 (.seq mc1 (.seq mc2 hrp))).1)
            obtain ⟨rf, sf, hfinal⟩ : ∃ rf sf, evaluateHOLFiniteState t2 (.seq mc1 (.seq mc2 hrp)) = (rf, sf) :=
              ⟨_, _, rfl⟩
            rw [hfinal] at hseq1 ⊢
            cases rf with
            | none =>
              dsimp only at hseq1 ⊢
              obtain ⟨hfc, hfInv, hfch, hfg⟩ := hseq1.1 rfl
              let post1 := { sf with locals := sf.locals.resVarEq (ofString "tmp", t1.locals.lookup (ofString "tmp")) }
              let post0 := { post1 with locals := post1.locals.resVarEq (ofString "mark", t.locals.lookup (ofString "mark")) }
              refine ⟨fun _ => ⟨hfc, ?_, ?_, ?_⟩, fun h => False.elim (h rfl)⟩
              · exact localsFree_evmInv sf post0.locals sf.clock hfInv
              · exact (evmChain_congr (s := post0) (t := sf) rfl rfl).symm.trans hfch
              · exact (evm_congr (s := post0) (t := sf) rfl rfl).2.1.symm.trans hfg
            | some rf0 =>
              dsimp only at hseq1 ⊢
              have hnr_f := hseq1.2 (by simp)
              have hp_f := mcopy_other_pair_g08 (r := some rf0) (by simp) hnr_f.1 hnr_f.2
              exact ⟨fun h => hp_f.1 h _, hp_f.2⟩
          dsimp only [post_outer]
          rw [evaluateHOLFiniteState_seq_line780] at hnt1 ⊢
          obtain ⟨rm1, t3, hrun_mc1⟩ : ∃ rm1 t3, evaluateHOLFiniteState t2 mc1 = (rm1, t3) :=
            ⟨_, _, rfl⟩
          rw [hrun_mc1] at hnt1 ⊢
          have hnt_mc1 : rm1 ≠ some .timeOut := by
            rintro rfl; exact hnt1 rfl
          have hmc1 := M11.eval_call_memcpy_bre t2
            (.var .local (ofString "tmp"))
            (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]),
              .var .local (ofString "s")])
            (.var .local (ofString "n"))
            markw (srcbase + sw) nw [(markw.toNat, nw.toNat)]
            ht2_code (ht2_ma.trans hInv.1.1.memaddrs) ht2_tmp hsrc_t2 ht2_n
            (fun _ => ⟨_, List.mem_singleton.mpr rfl, le_refl _, le_refl _⟩)
            (by change (evaluateHOLFiniteState t2 mc1).1 ≠ _; rw [hrun_mc1]; exact hnt_mc1)
          dsimp only at hmc1
          change ((evaluateHOLFiniteState t2 mc1).1 = none → _) ∧
            ((evaluateHOLFiniteState t2 mc1).1 ≠ none → _) at hmc1
          rw [hrun_mc1] at hmc1
          dsimp only at hmc1
          cases rm1 with
          | some rm1_0 =>
            dsimp only
            have hnr1 := hmc1.2 (by simp)
            have hp := mcopy_other_pair_g08 (r := some rm1_0) (by simp)
              (fun v hv => hnr1 (Or.inl ⟨v, hv⟩))
              (fun ⟨ev, he⟩ => hnr1 (Or.inr ⟨ofString "EvmErr", ev, he, by decide⟩))
            exact ⟨fun h => hp.1 h _, hp.2⟩
          | none =>
            dsimp only at hnt1 ⊢
            obtain ⟨hm11_1, ht3_loc⟩ := hmc1.1 rfl
            have heff1 : ByteRegionEffect t2 t3 [(markw.toNat, nw.toNat)] := bre_of_m11 hm11_1
            -- Synthetic state `u1 := { t3 with globals := t.globals }`
            let u1 : PanSemStateFiniteExact 64 F := { t3 with globals := t.globals }
            have heff_t_u1 : ByteRegionEffect t u1 [(markw.toNat, nw.toNat)] :=
              ⟨heff1.code.trans (ht2_code.trans hc.symm),
               heff1.memaddrs.trans ht2_ma,
               heff1.shMemaddrs.trans ht2_sh,
               heff1.baseAddr.trans ht2_ba,
               heff1.be.trans ht2_be,
               rfl,
               fun a ha => (heff1.out_dom a (by rwa [ht2_ma])).trans (congrFun ht2_mem a),
               fun a ha => (heff1.cell_frame a ha).trans (congrFun ht2_mem a),
               fun b hb ha =>
                 (memB_eq_of_memory_be_g08 u1 t3 b rfl rfl).trans
                   ((heff1.byte_frame b hb ha).trans (memB_eq_of_memory_be_g08 t2 t b ht2_mem ht2_be))⟩
            obtain ⟨hInv_u1, hch_u1, hgas_u1⟩ :=
              heapGap_bre_to_evmStep_g08 hInv hmark_nat (by omega) hmark_8 heff_t_u1
            have hmem32_u1 : memW u1 (globN u1 "ev" + 32) = memW t (globN t "ev" + 32) := by
              have hgev : globN u1 "ev" = globN t "ev" := rfl
              rw [hgev]
              unfold memW
              rw [heff_t_u1.cell_frame (BitVec.ofNat 64 (globN t "ev" + 32))]
              intro i hi
              simp only [List.mem_singleton] at hi
              subst i
              obtain ⟨_, _, hb_ev, _⟩ := head_ev_bounds_g08 hInv
              have hhead : (globN t "ev", globN t "cur_cont") ∈ evmChain t := by
                simp [evmChain, evmChainFrom]
              have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead
              have hin1 := (hFW0.1 (globN t "ev", 280) (by simp)).1.1
              dsimp only at hin1
              have hfm1 := hInv.1.2.2.2.1
              have hfm2 := hInv.1.2.2.2.2.1
              rw [R11Shards.scratchStart_val] at hfm1
              have hcMax_val : InitECandidate.Solver.HeapPotential.cMax.toNat = 2952790016 := rfl
              have hnat32 : (BitVec.ofNat 64 (globN t "ev" + 32)).toNat = globN t "ev" + 32 :=
                Nat.mod_eq_of_lt (by omega)
              rw [hnat32]
              unfold CellHits
              dsimp only
              omega
            have hcov_u1 : dw.toNat + nw.toNat ≤ memW u1 (globN u1 "ev" + 32) := by
              rw [hmem32_u1]; exact hcov
            have ht3_d : t3.locals.lookup (ofString "d") = some (.val (.word dw)) := by
              rw [ht3_loc]; exact ht2_d
            have ht3_tmp : t3.locals.lookup (ofString "tmp") = some (.val (.word markw)) := by
              rw [ht3_loc]; exact ht2_tmp
            have ht3_n : t3.locals.lookup (ofString "n") = some (.val (.word nw)) := by
              rw [ht3_loc]; exact ht2_n
            have ht3_mark : t3.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
              rw [ht3_loc]; exact ht2_mark
            obtain ⟨dstbase, hdstbase, hdst_u1⟩ := eval_head_mem_plus_local_g08 u1 hInv_u1 "d" dw ht3_d
            have hbounds := head_mem_store_address_g08 u1 hInv_u1 dstbase dw nw.toNat hdstbase hnpos hcov_u1
            have ht3_glob : t3.globals = t.globals.update (ofString "heap_ptr", .val (.word q)) :=
              heff1.globals.trans ht2_glob
            have hev_t3_u1 : t3.globals.lookup (ofString "ev") = u1.globals.lookup (ofString "ev") := by
              change t3.globals.lookup (ofString "ev") = t.globals.lookup (ofString "ev")
              rw [ht3_glob]
              simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "ev" by decide]
            have hdst_t3 : @evalHOLExact 64 F _ t3.toExact (fun a => Classical.propDecidable (t3.memaddrs a))
                (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]),
                  .var .local (ofString "d")]) = some (.val (.word (dstbase + dw))) := by
              rw [eval_ev24_add_local_globals_congr_g08 t3 u1 (ofString "d") hev_t3_u1 rfl rfl rfl rfl]
              exact hdst_u1
            -- Step 4: second `memcpy(*(ev+24) + d, tmp, n)` on `t3`
            rw [evaluateHOLFiniteState_seq_line780] at hnt1 ⊢
            have ht3_code : t3.code = originalRuntimeCode := heff1.code.trans ht2_code
            have ht3_ma : t3.memaddrs = ordinaryDomain :=
              heff1.memaddrs.trans (ht2_ma.trans hInv.1.1.memaddrs)
            obtain ⟨rm2, t4, hrun_mc2⟩ : ∃ rm2 t4, evaluateHOLFiniteState t3 mc2 = (rm2, t4) :=
              ⟨_, _, rfl⟩
            rw [hrun_mc2] at hnt1 ⊢
            have hnt_mc2 : rm2 ≠ some .timeOut := by
              rintro rfl; exact hnt1 rfl
            have hmc2 := M11.eval_call_memcpy_bre t3
              (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]),
                .var .local (ofString "d")])
              (.var .local (ofString "tmp"))
              (.var .local (ofString "n"))
              (dstbase + dw) markw nw
              [(memW u1 (globN u1 "ev" + 24), memW u1 (globN u1 "ev" + 40))]
              ht3_code ht3_ma hdst_t3 ht3_tmp ht3_n
              (fun _ => ⟨_, List.mem_singleton.mpr rfl, hbounds.2.1, hbounds.2.2⟩)
              (by change (evaluateHOLFiniteState t3 mc2).1 ≠ _; rw [hrun_mc2]; exact hnt_mc2)
            dsimp only at hmc2
            change ((evaluateHOLFiniteState t3 mc2).1 = none → _) ∧
              ((evaluateHOLFiniteState t3 mc2).1 ≠ none → _) at hmc2
            rw [hrun_mc2] at hmc2
            dsimp only at hmc2
            cases rm2 with
            | some rm2_0 =>
              dsimp only
              have hnr2 := hmc2.2 (by simp)
              have hp := mcopy_other_pair_g08 (r := some rm2_0) (by simp)
                (fun v hv => hnr2 (Or.inl ⟨v, hv⟩))
                (fun ⟨ev, he⟩ => hnr2 (Or.inr ⟨ofString "EvmErr", ev, he, by decide⟩))
              exact ⟨fun h => hp.1 h _, hp.2⟩
            | none =>
              dsimp only at hnt1 ⊢
              obtain ⟨hm11_2, ht4_loc⟩ := hmc2.1 rfl
              have heff2 : ByteRegionEffect t3 t4
                  [(memW u1 (globN u1 "ev" + 24), memW u1 (globN u1 "ev" + 40))] := bre_of_m11 hm11_2
              -- Step 5: `heap_release(mark)` on `t4`
              dsimp only [hrp] at hnt1 ⊢
              rw [evaluateHOLFiniteState_call] at hnt1 ⊢
              have ht4_mark : t4.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
                rw [ht4_loc]; exact ht3_mark
              have ht4_code : t4.code = originalRuntimeCode := heff2.code.trans ht3_code
              have hargs_hr : evalListHOLFinite t4
                  (h := fun a => Classical.propDecidable (t4.memaddrs a))
                  [.var .local (ofString "mark")] = some [.val (.word markw)] := by
                rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, evalHOLExact, ht4_mark]
              have hlook_hr := pan_one_word_lookup t4.code.lookup (ofString "heap_release")
                (ofString "m") (sourceFnBody Guest.Software.guestFn_heap_release) markw
                (by rw [ht4_code]; exact lookup_heap_release)
              rw [hargs_hr] at hnt1 ⊢; dsimp only at hnt1 ⊢
              rw [hlook_hr] at hnt1 ⊢; dsimp only at hnt1 ⊢
              by_cases hclk4 : t4.clock = 0
              · simp [hclk4] at hnt1
              · rw [if_neg hclk4] at hnt1 ⊢
                let cal_hr := HolFiniteMapExact.empty.update (ofString "m", ValueHOL.val (.word markw))
                let ent_hr := callEntryStateHOLFinite t4 cal_hr
                have ht4_glob : t4.globals = t.globals.update (ofString "heap_ptr", .val (.word q)) :=
                  heff2.globals.trans ht3_glob
                have hhr_body : evaluateHOLFiniteState ent_hr
                    (sourceFnBody Guest.Software.guestFn_heap_release) =
                    (some (.returned (.val (.word 0))),
                     emptyLocalsHOLFinite (setKvarHOLFinite .global (ofString "heap_ptr") (.val (.word markw)) ent_hr)) := by
                  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_heap_release,
                    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
                    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
                    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
                    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural]
                  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
                  have hm_loc : ent_hr.locals.lookup (ofString "m") = some (.val (.word markw)) := by
                    simp [ent_hr, cal_hr, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  have hlk_hp4 : ent_hr.globals.lookup (ofString "heap_ptr") = some (.val (.word q)) := by
                    change t4.globals.lookup (ofString "heap_ptr") = _
                    rw [ht4_glob]
                    simp [HolFiniteMapExact.lookup_update, FUPDATE]
                  simp [evalHOLExact, hm_loc, isValidValueHOLFinite, isValidValueHOLExact,
                    lookupKvarHOLFinite, lookupKvarHOLExact, hlk_hp4,
                    shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite,
                    evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
                rw [hhr_body]; dsimp only
                have hsh0_one : shapeEqHOL (shapeOfHOLExact (.val (.word (0 : BitVec 64)) : ValueHOL 64)) .one = true := by
                  simp [shapeOfHOLExact, shapeEqHOL]
                rw [if_pos hsh0_one]; dsimp only
                let t5 : PanSemStateFiniteExact 64 F :=
                  { emptyLocalsHOLFinite (setKvarHOLFinite .global (ofString "heap_ptr") (.val (.word markw)) ent_hr) with
                    locals := t4.locals }
                have ht5_glob : t5.globals = u1.globals := by
                  change ent_hr.globals.update (ofString "heap_ptr", .val (.word markw)) = t.globals
                  change t4.globals.update (ofString "heap_ptr", .val (.word markw)) = t.globals
                  rw [ht4_glob]
                  exact globals_update_twice_restore t.globals (ofString "heap_ptr")
                    (.val (.word markw)) (.val (.word q)) hmark_lk
                have heff_u1_t5 : ByteRegionEffect u1 t5
                    [(memW u1 (globN u1 "ev" + 24), memW u1 (globN u1 "ev" + 40))] :=
                  ⟨heff2.code, heff2.memaddrs, heff2.shMemaddrs, heff2.baseAddr, heff2.be, ht5_glob,
                   heff2.out_dom, heff2.cell_frame,
                   fun b hb ha =>
                     (memB_eq_of_memory_be_g08 t5 t4 b rfl rfl).trans
                       ((heff2.byte_frame b hb ha).trans (memB_eq_of_memory_be_g08 t3 u1 b rfl rfl))⟩
                obtain ⟨hInv_t5, hch_t5, hgas_t5⟩ := evmInv_of_head_mem_bytes_g08 hInv_u1 heff_u1_t5
                exact ⟨fun _ => ⟨ht4_code, hInv_t5, hch_t5.trans hch_u1, hgas_t5.trans hgas_u1⟩,
                  fun h => False.elim (h rfl)⟩

private def mcopyEff_g08 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (prog : ProgHOL 64) : Prop :=
  let out := evaluateHOLFiniteState s prog
  (out.1 = none → out.2.code = originalRuntimeCode ∧ EvmInv out.2 ∧
    evmChain out.2 = evmChain s ∧ evmR out.2 = evmR s) ∧
  (out.1 ≠ none → (∀ v, out.1 ≠ some (.returned v)) ∧ ¬ IsEvmErr out.1)

private theorem mcopyEff_error_g08 {F : Type} (s t : PanSemStateFiniteExact 64 F) :
    (some (.error : PanSemResultExact 64) = none →
      t.code = originalRuntimeCode ∧ EvmInv t ∧ evmChain t = evmChain s ∧ evmR t = evmR s) ∧
    (some (.error : PanSemResultExact 64) ≠ none →
      (∀ v, some (.error : PanSemResultExact 64) ≠ some (.returned v)) ∧ ¬ IsEvmErr (some .error)) := by
  refine ⟨?_, ?_⟩
  · intro h; cases h
  · intro _
    refine ⟨?_, ?_⟩
    · intro _ h; cases h
    · rintro ⟨_, h⟩; cases h

private theorem decCall_sat_mcopy_eff_g08 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nm : MlS) (arg : ExpHOL 64) (varg : ValueHOL 64) (cont : ProgHOL 64)
    (hc : s.code = originalRuntimeCode)
    (hshape : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact varg) = true)
    (harg : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) arg = some varg)
    (hcont : ∀ mid : PanSemStateFiniteExact 64 F, LocFrame s mid →
      mid.locals = s.locals.update (nm, .val (.word (satValue_g08 varg))) →
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut → mcopyEff_g08 mid cont)
    (hnt : (evaluateHOLFiniteState s (.decCall nm .one (ofString "sat_word") [arg] cont)).1 ≠ some .timeOut) :
    mcopyEff_g08 s (.decCall nm .one (ofString "sat_word") [arg] cont) := by
  dsimp only [mcopyEff_g08]
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [arg] = some [varg] := by
    rw [evalListHOLFinite_eq_toExact]; simp only [evalListHOLExact, harg]
  rw [hargs] at hnt ⊢
  dsimp only at hnt ⊢
  rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "sat_word") [varg] with _ | ⟨b, callee, rs⟩
  · exact mcopyEff_error_g08 s s
  · simp only [hl] at hnt ⊢
    have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "sat_word") [varg] = some (b, callee, rs) := by rwa [← hc]
    obtain ⟨rfl, rfl, v0, hvs, hcal⟩ := single_comb_arg_lookup_g08 lookup_sat_word_g08 hl_orig
    have hv0 : varg = v0 := by simpa using hvs
    subst v0
    by_cases hz : s.clock = 0
    · simp [hz] at hnt
    · rw [if_neg hz] at hnt ⊢
      obtain ⟨a, b0, c, d, rfl⟩ := u256_value_of_shape_g08 hshape
      rw [sat_word_body_exact_g08 _ a b0 c d hcal] at hnt ⊢
      dsimp only at hnt ⊢
      have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word
          (if b0 ||| c ||| d = 0#64 then a else 18446744073709551615#64)))) .one = true := by simp [shapeOfHOLExact, shapeEqHOL]
      simp only [hsh, Bool.and_self, ↓reduceIte] at hnt ⊢
      let nw := satValue_g08 (.rStruct [.val (.word a), .val (.word b0), .val (.word c), .val (.word d)])
      let mid := setVarHOLFinite nm (.val (.word nw))
        { (callEntryStateHOLFinite s callee).emptyLocalsHOLFinite with locals := s.locals }
      have hmid : LocFrame s mid := rfl
      have hml : mid.locals = s.locals.update (nm, .val (.word nw)) := rfl
      change (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut at hnt
      rcases hr : evaluateHOLFiniteState mid cont with ⟨r, post⟩
      rw [hr] at hnt
      have hnt_mid : (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut := by rw [hr]; exact hnt
      have hh := hcont mid hmid hml hnt_mid
      dsimp only [mcopyEff_g08] at hh
      rw [hr] at hh
      change ((evaluateHOLFiniteState mid cont).1 = none →
        { (evaluateHOLFiniteState mid cont).2 with locals := (evaluateHOLFiniteState mid cont).2.locals.resVarEq (nm, s.locals.lookup nm) }.code = originalRuntimeCode ∧
        EvmInv { (evaluateHOLFiniteState mid cont).2 with locals := (evaluateHOLFiniteState mid cont).2.locals.resVarEq (nm, s.locals.lookup nm) } ∧
        evmChain { (evaluateHOLFiniteState mid cont).2 with locals := (evaluateHOLFiniteState mid cont).2.locals.resVarEq (nm, s.locals.lookup nm) } = evmChain s ∧
        evmR { (evaluateHOLFiniteState mid cont).2 with locals := (evaluateHOLFiniteState mid cont).2.locals.resVarEq (nm, s.locals.lookup nm) } = evmR s) ∧
        ((evaluateHOLFiniteState mid cont).1 ≠ none → (∀ v, (evaluateHOLFiniteState mid cont).1 ≠ some (.returned v)) ∧ ¬ IsEvmErr (evaluateHOLFiniteState mid cont).1)
      rw [hr]
      change (r = none →
        { post with locals := post.locals.resVarEq (nm, s.locals.lookup nm) }.code = originalRuntimeCode ∧
        EvmInv { post with locals := post.locals.resVarEq (nm, s.locals.lookup nm) } ∧
        evmChain { post with locals := post.locals.resVarEq (nm, s.locals.lookup nm) } = evmChain s ∧
        evmR { post with locals := post.locals.resVarEq (nm, s.locals.lookup nm) } = evmR s) ∧
        (r ≠ none → (∀ v, r ≠ some (.returned v)) ∧ ¬ IsEvmErr r)
      refine ⟨fun hn => ?_, hh.2⟩
      obtain ⟨hpc, hpInv, hpch, hpg⟩ := hh.1 hn
      let post_res := { post with locals := post.locals.resVarEq (nm, s.locals.lookup nm) }
      have hch_mid : evmChain mid = evmChain s := evmChain_congr (s := s) (t := mid) rfl rfl
      have hg_mid : evmR mid = evmR s := (evm_congr (s := s) (t := mid) rfl rfl).2.1
      have hch_res : evmChain post_res = evmChain post := evmChain_congr (s := post) (t := post_res) rfl rfl
      have hg_res : evmR post_res = evmR post := (evm_congr (s := post) (t := post_res) rfl rfl).2.1
      exact ⟨hpc, localsFree_evmInv post post_res.locals post.clock hpInv,
        hch_res.trans (hpch.trans hch_mid),
        hg_res.trans (hpg.trans hg_mid)⟩

private theorem mcopy_write_eff_g08 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dstVal srcVal lenVal : ValueHOL 64)
    (hc : s.code = originalRuntimeCode) (hInv : EvmInv s)
    (hdst_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact dstVal) = true)
    (hsrc_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact srcVal) = true)
    (hdst : s.locals.lookup (ofString "dst") = some dstVal)
    (hsrc : s.locals.lookup (ofString "src") = some srcVal)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word (satValue_g08 lenVal))))
    (hnz : satValue_g08 lenVal ≠ 0#64)
    (hcov : (satValue_g08 dstVal).toNat + (satValue_g08 lenVal).toNat ≤ memW s (globN s "ev" + 32))
    (hnt : (evaluateHOLFiniteState s mcopyWriteProg_g08).1 ≠ some .timeOut) :
    mcopyEff_g08 s mcopyWriteProg_g08 := by
  refine decCall_sat_mcopy_eff_g08 s (ofString "d") (.var .local (ofString "dst")) dstVal
    (.decCall (ofString "s") .one (ofString "sat_word") [.var .local (ofString "src")] mcopyWriteInnerProg_g08)
    hc hdst_sh hdst ?_ hnt
  intro mid1 hlf1 hl1 hnt1
  have hc1 : mid1.code = originalRuntimeCode := by rw [hlf1]; exact hc
  have hInv1 : EvmInv mid1 := by rw [hlf1]; exact localsFree_evmInv s _ _ hInv
  have hsrc1 : mid1.locals.lookup (ofString "src") = some srcVal := by
    simp [hl1, HolFiniteMapExact.lookup_update, FUPDATE, hsrc, show ofString "d" ≠ ofString "src" by decide]
  refine decCall_sat_mcopy_eff_g08 mid1 (ofString "s") (.var .local (ofString "src")) srcVal
    mcopyWriteInnerProg_g08 hc1 hsrc_sh hsrc1 ?_ hnt1
  intro mid2 hlf2 hl2 hnt2
  have hc2 : mid2.code = originalRuntimeCode := by rw [hlf2]; exact hc1
  have hInv2 : EvmInv mid2 := by rw [hlf2]; exact localsFree_evmInv mid1 _ _ hInv1
  have hd2 : mid2.locals.lookup (ofString "d") = some (.val (.word (satValue_g08 dstVal))) := by
    simp [hl2, hl1, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "s" ≠ ofString "d" by decide]
  have hs2 : mid2.locals.lookup (ofString "s") = some (.val (.word (satValue_g08 srcVal))) := by
    simp [hl2, HolFiniteMapExact.lookup_update, FUPDATE]
  have hn2 : mid2.locals.lookup (ofString "n") = some (.val (.word (satValue_g08 lenVal))) := by
    simp [hl2, hl1, HolFiniteMapExact.lookup_update, FUPDATE, hn,
      show ofString "s" ≠ ofString "n" by decide, show ofString "d" ≠ ofString "n" by decide]
  have hcov2 : (satValue_g08 dstVal).toNat + (satValue_g08 lenVal).toNat ≤ memW mid2 (globN mid2 "ev" + 32) := by
    have hm : memW mid2 (globN mid2 "ev" + 32) = memW s (globN s "ev" + 32) := by
      rw [hlf2, hlf1]; rfl
    rw [hm]; exact hcov
  exact mcopy_write_inner_eff_g08 mid2 (satValue_g08 dstVal) (satValue_g08 srcVal) (satValue_g08 lenVal)
    hc2 hInv2 hd2 hs2 hn2 hnz hcov2 hnt2

private theorem mcopy_tail_run_g08 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (dstVal srcVal lenVal : ValueHOL 64)
    (hdst_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact dstVal) = true)
    (hsrc_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact srcVal) = true) :
    HandlerRun s0 (fun t => CopyLocals_g08 (mcopyArgs_g08 dstVal srcVal lenVal) t.locals ∧
      (satValue_g08 lenVal ≠ 0#64 →
        (satValue_g08 dstVal).toNat + (satValue_g08 lenVal).toNat ≤ memW t (globN t "ev" + 32))) true
      mcopyTailProg_g08 := by
  have hfinish : HandlerRun s0 (fun _ => True) true copyFinishProg_g08 :=
    HandlerRun.seq_call_simple eps_pc_add (HandlerRun.ret _)
  refine HandlerRun.seq_ite_copy_g08 ?_ ?_
  · intro t hc hInv hlen hR ⟨⟨hK, hcov⟩, w, hw, hwne⟩ hnt
    have hn : t.locals.lookup (ofString "n") = some (.val (.word (satValue_g08 lenVal))) :=
      copyLocals_get_g08 hK (by simp [mcopyArgs_g08])
    have hnz : satValue_g08 lenVal ≠ 0#64 := by
      intro hz
      have hev : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.cmp .notEqual (.var .local (ofString "n")) (.const 0#64)) = some (.val (.word 0#64)) := by
        simp [evalHOLExact, hn, hz, Compiler.Encoders.Asm.wordCmpHOL]
      rw [hev] at hw
      have hw0 : w = 0#64 := by simpa using hw.symm
      exact hwne hw0
    refine seq_step s0 t mcopyWriteProg_g08 copyFinishProg_g08 hnt ?_
    intro hnt_w
    have hw_eff := mcopy_write_eff_g08 t dstVal srcVal lenVal hc hInv hdst_sh hsrc_sh
      (copyLocals_get_g08 hK (by simp [mcopyArgs_g08]))
      (copyLocals_get_g08 hK (by simp [mcopyArgs_g08]))
      hn hnz (hcov hnz) hnt_w
    refine ⟨fun hnone hnt_f => ?_, hw_eff.2⟩
    obtain ⟨hpc, hpInv, hpch, hpg⟩ := hw_eff.1 hnone
    exact hfinish (evaluateHOLFiniteState t mcopyWriteProg_g08).2 hpc hpInv
      (by rw [hpch]; exact hlen) (by rw [hpg]; exact hR) trivial hnt_f
  · exact HandlerRun.seq_skip (HandlerRun.weaken (fun _ _ _ => trivial) hfinish)

private theorem mcopy_cost_phase_run_g08 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (dstVal srcVal lenVal : ValueHOL 64)
    (hdst_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact dstVal) = true)
    (hsrc_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact srcVal) = true)
    (hlen_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact lenVal) = true)
    (K : HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (hKx : ∀ l v, K l → K (l.update (ofString "x", v)))
    (hKcost : ∀ l v, K l → K (l.update (ofString "cost", v)))
    (hKdst : ∀ l, K l → l.lookup (ofString "dst") = some dstVal)
    (hKsrc : ∀ l, K l → l.lookup (ofString "src") = some srcVal)
    (hKlen : ∀ l, K l → l.lookup (ofString "len") = some lenVal)
    (hKw : ∀ l, K l → ∃ ww : BitVec 64,
      l.lookup (ofString "w") = some (.val (.word ww)) ∧ ww.toNat < 2 ^ 59)
    {cont : ProgHOL 64}
    (hcont : HandlerRun s0 (fun t => K t.locals ∧ CopyExpand_g08 dstVal lenVal t) true cont) :
    HandlerRun s0 (fun t => HeadMemAligned t ∧ K t.locals) false
      (.decCall (ofString "x") (.comb [.one, .one]) (ofString "extend_memory_cost2")
        [.var .local (ofString "src"), .var .local (ofString "len"),
         .var .local (ofString "dst"), .var .local (ofString "len")]
        (.decCall (ofString "cost") .one (ofString "add_sat")
          [.op .add [.const 3#64, .panop .mul [.const 3#64, .var .local (ofString "w")]],
           .rfield 0 (.var .local (ofString "x"))]
          (.seq (.call (some (none, none)) (ofString "charge_gas") [.var .local (ofString "cost")]) cont))) := by
  refine HandlerRun.decCall
    (Q := fun t => HeadMemAligned t ∧ K t.locals ∧
      ∃ cw ebw : BitVec 64,
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        (ebw = 0#64 ∨
          (memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
           (memW t (globN t "ev" + 32) + ebw.toNat) % 8 = 0 ∧
           memW t (globN t "ev" + 24) + memW t (globN t "ev" + 40) = globN t "frame_mem_ptr")) ∧
        (cw.toNat < 2 ^ 64 - 1 → satValue_g08 lenVal ≠ 0#64 →
          (satValue_g08 dstVal).toNat + (satValue_g08 lenVal).toNat ≤ memW t (globN t "ev" + 32) + ebw.toNat))
    eps_extend_memory_cost2_copy_cov_g08
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t values _ callee _ v cpost _ ⟨hHM, hK⟩ hargs hl_orig _ _ hQc => by
      obtain ⟨hlf, cw, ebw, rfl, heb_bounds, hcov_ce⟩ := hQc
      obtain ⟨v1, v2, v3, v4, rfl, _, _, _, _, hcal_s1, hcal_n1, hcal_s2, hcal_n2⟩ :=
        extend_memory_cost2_four_args_lookup_g08 hl_orig
      rw [evalListHOLFinite_eq_toExact] at hargs
      have hsrc := hKsrc t.locals hK
      have hdst := hKdst t.locals hK
      have hlen := hKlen t.locals hK
      simp only [evalListHOLExact, evalHOLExact, hsrc, hdst, hlen, Option.some.injEq, List.cons.injEq] at hargs
      rcases hargs with ⟨rfl, rfl, rfl, rfl, _⟩
      let ce := callEntryStateHOLFinite t callee
      have hHM_ce : HeadMemAligned ce := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      have hHM_cp : HeadMemAligned cpost :=
        headMemAligned_congr_head_only (by rw [hlf]) (fun off _ => by unfold memW; rw [hlf]) hHM_ce
      let res := setVarHOLFinite (ofString "x") (.rStruct [.val (.word cw), .val (.word ebw)]) { cpost with locals := t.locals }
      have hHM_res : HeadMemAligned res := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp
      have hmem32_eq : memW res (globN res "ev" + 32) = memW ce (globN ce "ev" + 32) := by
        have hg : globN res "ev" = globN ce "ev" := globN_eq_of_lookup_eq (by change cpost.globals.lookup _ = ce.globals.lookup _; rw [hlf])
        have hm : res.memory = ce.memory := by change cpost.memory = ce.memory; rw [hlf]
        rw [hg]; unfold memW; rw [hm]
      refine ⟨hHM_res, hKx _ _ hK, cw, ebw,
        by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], ?_, ?_⟩
      · rcases heb_bounds with rfl | heb_fn
        · exact Or.inl rfl
        · right
          obtain ⟨hlt37, hmod8⟩ := heb_fn hHM_ce.1
          rw [hmem32_eq]
          exact ⟨hlt37, hmod8, hHM_res.2⟩
      · intro hcw_lt hn
        rw [hmem32_eq]
        exact (hcov_ce srcVal dstVal lenVal hcal_s1 hsrc_sh hcal_n1 hcal_s2 hdst_sh hcal_n2 hlen_sh hn hcw_lt hHM_ce.1).2)
    ?_
  refine HandlerRun.decCall
    (Q := fun t => HeadMemAligned t ∧ K t.locals ∧
      ∃ totw bw cw ebw : BitVec 64,
        t.locals.lookup (ofString "cost") = some (.val (.word totw)) ∧
        0 < totw.toNat ∧
        (totw.toNat < 2 ^ 64 - 1 → totw.toNat = bw.toNat + cw.toNat) ∧
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        (ebw = 0#64 ∨
          (memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
           (memW t (globN t "ev" + 32) + ebw.toNat) % 8 = 0 ∧
           memW t (globN t "ev" + 24) + memW t (globN t "ev" + 40) = globN t "frame_mem_ptr")) ∧
        (cw.toNat < 2 ^ 64 - 1 → satValue_g08 lenVal ≠ 0#64 →
          (satValue_g08 dstVal).toNat + (satValue_g08 lenVal).toNat ≤ memW t (globN t "ev" + 32) + ebw.toNat))
    eps_add_sat_pos_exact_g08
    (fun t values b_as callee rs_as hc _ ⟨_, hK, cw, ebw, hx, _⟩ hargs hl => by
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "add_sat") values =
          some (b_as, callee, rs_as) := by rwa [← hc]
      obtain ⟨_, _, w1, w2, rfl, hw1, hw2⟩ := two_word_arg_lookup (by decide) lookup_add_sat hl_orig
      obtain ⟨ww, hw, hwb⟩ := hKw t.locals hK
      have hargs_ok : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.op .add [.const 3#64, .panop .mul [.const 3#64, .var .local (ofString "w")]],
           .rfield 0 (.var .local (ofString "x"))] =
          some [.val (.word (3#64 + 3#64 * ww)), .val (.word cw)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hw, hx, wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord]
      rw [hargs_ok] at hargs
      injection hargs with hvs
      rcases List.cons.inj hvs with ⟨hw1_eq, hvs'⟩
      rcases List.cons.inj hvs' with ⟨hw2_eq, _⟩
      injection hw1_eq with hw1'; injection hw1' with hw1''; subst hw1''
      injection hw2_eq with hw2'; injection hw2' with hw2''; subst hw2''
      exact ⟨3#64 + 3#64 * ww, cw, hw1, hw2, (copy_words_base_pos_g08 ww hwb).2⟩)
    (fun t values _ callee _ v cpost _ ⟨hHM, hK, cw, ebw, hx, heb_cond, hcov_imp⟩ hargs hl_orig _ _ hQc => by
      obtain ⟨hlf, totw, rfl, hpos, htot_ex⟩ := hQc
      obtain ⟨_, _, w1, w2, rfl, hw1, hw2⟩ := two_word_arg_lookup (by decide) lookup_add_sat hl_orig
      obtain ⟨ww, hw, hwb⟩ := hKw t.locals hK
      have hargs_ok : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.op .add [.const 3#64, .panop .mul [.const 3#64, .var .local (ofString "w")]],
           .rfield 0 (.var .local (ofString "x"))] =
          some [.val (.word (3#64 + 3#64 * ww)), .val (.word cw)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hw, hx, wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord]
      rw [hargs_ok] at hargs
      injection hargs with hvs
      rcases List.cons.inj hvs with ⟨hw1_eq, hvs'⟩
      rcases List.cons.inj hvs' with ⟨hw2_eq, _⟩
      injection hw1_eq with hw1'; injection hw1' with hw1''; subst hw1''
      injection hw2_eq with hw2'; injection hw2' with hw2''; subst hw2''
      let ce := callEntryStateHOLFinite t callee
      have hHM_ce : HeadMemAligned ce := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      have hHM_cp : HeadMemAligned cpost :=
        headMemAligned_congr_head_only (by rw [hlf]) (fun off _ => by unfold memW; rw [hlf]) hHM_ce
      let res := setVarHOLFinite (ofString "cost") (.val (.word totw)) { cpost with locals := t.locals }
      have hHM_res : HeadMemAligned res := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp
      have hmem32_eq : memW res (globN res "ev" + 32) = memW t (globN t "ev" + 32) := by
        have hg : globN res "ev" = globN t "ev" := globN_eq_of_lookup_eq (by change cpost.globals.lookup _ = t.globals.lookup _; rw [hlf]; rfl)
        have hm : res.memory = t.memory := by change cpost.memory = t.memory; rw [hlf]; rfl
        rw [hg]; unfold memW; rw [hm]
      refine ⟨hHM_res, hKcost _ _ hK, totw, 3#64 + 3#64 * ww, cw, ebw,
        by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
        hpos, htot_ex _ _ hw1 hw2,
        by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hx, show ofString "cost" ≠ ofString "x" by decide],
        ?_, ?_⟩
      · rcases heb_cond with rfl | ⟨hlt37, hmod8, _⟩
        · exact Or.inl rfl
        · right
          rw [hmem32_eq]
          exact ⟨hlt37, hmod8, hHM_res.2⟩
      · intro hcw_lt hn
        rw [hmem32_eq]
        exact hcov_imp hcw_lt hn)
    ?_
  refine HandlerRun.seq_charge_copy_g08
    (Q := fun t => K t.locals ∧ CopyExpand_g08 dstVal lenVal t)
    (fun t w hw _ ⟨_, _, totw, _, _, _, htot, hpos, _⟩ => by
      change t.locals.lookup (ofString "cost") = some (.val (.word w)) at hw
      rw [htot] at hw; injection hw with hw'; injection hw' with hw''; injection hw'' with hweq; subst hweq
      exact hpos)
    (fun t amtw cpost hw hamt_lt _ ⟨hHM, hK, totw, bw, cw, ebw, htot, _, htot_ex, hx, heb_cond, hcov_imp⟩ _ hglob_cp _ hmem_head_cp => by
      change t.locals.lookup (ofString "cost") = some (.val (.word amtw)) at hw
      rw [htot] at hw; injection hw with hw'; injection hw' with hw''; injection hw'' with hweq; subst hweq
      have htot_sum := htot_ex hamt_lt
      have hcw_lt : cw.toNat < 2 ^ 64 - 1 := by omega
      have hHM_cp : HeadMemAligned cpost := headMemAligned_congr_head_only hglob_cp hmem_head_cp hHM
      let res : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
      have hHM_res : HeadMemAligned res := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp
      have hmem32_eq : memW res (globN res "ev" + 32) = memW t (globN t "ev" + 32) := by
        have hg : globN res "ev" = globN t "ev" := globN_eq_of_lookup_eq (by change cpost.globals.lookup _ = t.globals.lookup _; rw [hglob_cp])
        rw [hg]; exact hmem_head_cp 32 (by simp)
      refine ⟨hK, cw, ebw, hx, ?_, ?_⟩
      · rcases heb_cond with rfl | ⟨hlt37, hmod8, _⟩
        · exact Or.inl rfl
        · right
          rw [hmem32_eq]
          exact ⟨hlt37, hmod8, hHM_res.2⟩
      · intro hn
        rw [hmem32_eq]
        exact hcov_imp hcw_lt hn)
    hcont

private def mcopyCostProg_g08 : ProgHOL 64 :=
  .decCall (ofString "x") (.comb [.one, .one]) (ofString "extend_memory_cost2")
    [.var .local (ofString "src"), .var .local (ofString "len"),
     .var .local (ofString "dst"), .var .local (ofString "len")]
    (.decCall (ofString "cost") .one (ofString "add_sat")
      [.op .add [.const 3#64, .panop .mul [.const 3#64, .var .local (ofString "w")]],
       .rfield 0 (.var .local (ofString "x"))]
      (.seq (.call (some (none, none)) (ofString "charge_gas") [.var .local (ofString "cost")])
        (.seq (.call (some (none, none)) (ofString "extend_memory") [.rfield 1 (.var .local (ofString "x"))])
          mcopyTailProg_g08)))

private def mcopyNumsProg_g08 : ProgHOL 64 :=
  .decCall (ofString "n") .one (ofString "sat_word") [.var .local (ofString "len")]
    (.decCall (ofString "w") .one (ofString "words_of") [.var .local (ofString "n")] mcopyCostProg_g08)

private theorem mcopy_after_pops_run_g08 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (dstVal srcVal lenVal : ValueHOL 64)
    (hdst_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact dstVal) = true)
    (hsrc_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact srcVal) = true)
    (hlen_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact lenVal) = true) :
    HandlerRun s0 (fun t => HeadMemAligned t ∧
      CopyLocals_g08 (mcopyArgs_g08 dstVal srcVal lenVal).tail t.locals) false
      mcopyNumsProg_g08 := by
  have hcost : ∀ ww : BitVec 64, ww.toNat < 2 ^ 59 →
      HandlerRun s0 (fun t => HeadMemAligned t ∧ CopyLocals_g08
        ((ofString "w", .val (.word ww)) :: mcopyArgs_g08 dstVal srcVal lenVal) t.locals) false
        mcopyCostProg_g08 := by
    intro ww hwb
    let args := (ofString "w", .val (.word ww)) :: mcopyArgs_g08 dstVal srcVal lenVal
    refine mcopy_cost_phase_run_g08 s0 dstVal srcVal lenVal hdst_sh hsrc_sh hlen_sh
      (CopyLocals_g08 args)
      ?_ ?_
      (fun _ hK => copyLocals_get_g08 hK (by simp [args, mcopyArgs_g08]))
      (fun _ hK => copyLocals_get_g08 hK (by simp [args, mcopyArgs_g08]))
      (fun _ hK => copyLocals_get_g08 hK (by simp [args, mcopyArgs_g08]))
      (fun _ hK => ⟨ww, copyLocals_get_g08 hK (by simp [args]), hwb⟩) ?_
    · intro l v hK
      apply copyLocals_update_g08 args l _ v _ hK
      intro kv hk
      simp only [args, mcopyArgs_g08, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
    · intro l v hK
      apply copyLocals_update_g08 args l _ v _ hK
      intro kv hk
      simp only [args, mcopyArgs_g08, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
    · refine copy_extend_phase_run_g08 s0 dstVal lenVal (CopyLocals_g08 args) ?_
      refine HandlerRun.weaken ?_ (mcopy_tail_run_g08 s0 dstVal srcVal lenVal hdst_sh hsrc_sh)
      intro t _ ⟨hK, hcov⟩
      exact ⟨fun kv hk => hK kv (List.mem_cons_of_mem _ hk), hcov⟩
  refine HandlerRun.decCall_sat_copy_g08 lenVal hlen_sh
    (fun t ⟨_, hK⟩ => copyLocals_get_g08 hK (by simp [mcopyArgs_g08]))
    (Q := fun t => HeadMemAligned t ∧ CopyLocals_g08 (mcopyArgs_g08 dstVal srcVal lenVal) t.locals)
    ?_ ?_
  · intro t cpost ⟨hHM, hK⟩ hlf
    have hHM_cp : HeadMemAligned cpost := headMemAligned_congr_head_only
      (by rw [hlf]) (fun off _ => by unfold memW; rw [hlf]) hHM
    refine ⟨headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp, ?_⟩
    change CopyLocals_g08
      ((ofString "n", .val (.word (satValue_g08 lenVal))) :: (mcopyArgs_g08 dstVal srcVal lenVal).tail)
      (t.locals.update (ofString "n", .val (.word (satValue_g08 lenVal))))
    apply copyLocals_cons_update_g08 _ _ _ _ _ hK
    intro kv hk
    simp only [mcopyArgs_g08, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl <;> dsimp only <;> decide
  · refine HandlerRun.decCall
      (Q := fun t => HeadMemAligned t ∧ ∃ ww : BitVec 64, ww.toNat < 2 ^ 59 ∧
        CopyLocals_g08 ((ofString "w", .val (.word ww)) :: mcopyArgs_g08 dstVal srcVal lenVal) t.locals)
      eps_words_of_lt (fun _ _ _ _ _ _ _ _ _ _ => trivial) ?_ ?_
    · intro t _ _ callee _ v cpost _ ⟨hHM, hK⟩ _ _ _ _ hQc
      obtain ⟨hlf, ww, hv, hwb⟩ := hQc
      subst v
      have hHM_ce : HeadMemAligned (callEntryStateHOLFinite t callee) :=
        headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      have hHM_cp : HeadMemAligned cpost := headMemAligned_congr_head_only
        (by rw [hlf]) (fun off _ => by unfold memW; rw [hlf]) hHM_ce
      refine ⟨headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp, ww, hwb, ?_⟩
      apply copyLocals_cons_update_g08 _ _ _ _ _ hK
      intro kv hk
      simp only [mcopyArgs_g08, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> dsimp only <;> decide
    · intro t hc hInv hlen hR ⟨hHM, ww, hwb, hK⟩ hnt
      exact hcost ww hwb t hc hInv hlen hR ⟨hHM, hK⟩ hnt

theorem op_mcopy_aligned_spec :
    FunSpec (fun s => EvmRun s ∧ HeadMemAligned s) OpDispatchPost (ofString "op_mcopy") := by
  refine ⟨_, _, _, lookup_op_mcopy_g08, ?_⟩
  intro F s0 hcode ⟨hRun, hHM⟩ _ hnt
  suffices hrun : HandlerRun s0 (fun t => HeadMemAligned t ∧ CopyLocals_g08 [] t.locals) false
      (sourceFnBody Guest.Software.guestFn_op_mcopy) from
    hrun s0 hcode hRun.1 rfl (le_refl _) ⟨hHM, fun _ h => by cases h⟩ hnt
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_op_mcopy,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map, List.map]
  refine HandlerRun.decCall_stack_copy_g08 (CopyLocals_g08 [])
    (fun l => ∃ dstVal, shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact dstVal) = true ∧
      CopyLocals_g08 [(ofString "dst", dstVal)] l) ?_ ?_
  · intro l v hK hsh
    refine ⟨v, hsh, copyLocals_cons_update_g08 _ _ _ _ ?_ hK⟩
    intro kv hk; cases hk
  · refine HandlerRun.decCall_stack_copy_g08
      (fun l => ∃ dstVal, shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact dstVal) = true ∧
        CopyLocals_g08 [(ofString "dst", dstVal)] l)
      (fun l => ∃ dstVal srcVal,
        shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact dstVal) = true ∧
        shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact srcVal) = true ∧
        CopyLocals_g08 [(ofString "src", srcVal), (ofString "dst", dstVal)] l) ?_ ?_
    · intro l v ⟨dstVal, hdst, hK⟩ hsh
      refine ⟨dstVal, v, hdst, hsh, copyLocals_cons_update_g08 _ _ _ _ ?_ hK⟩
      intro kv hk
      simp only [List.mem_singleton] at hk
      subst kv
      dsimp only
      decide
    · refine HandlerRun.decCall_stack_copy_g08
        (fun l => ∃ dstVal srcVal,
          shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact dstVal) = true ∧
          shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact srcVal) = true ∧
          CopyLocals_g08 [(ofString "src", srcVal), (ofString "dst", dstVal)] l)
        (fun l => ∃ dstVal srcVal lenVal,
          shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact dstVal) = true ∧
          shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact srcVal) = true ∧
          shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact lenVal) = true ∧
          CopyLocals_g08 [(ofString "len", lenVal), (ofString "src", srcVal), (ofString "dst", dstVal)] l) ?_ ?_
      · intro l v ⟨dstVal, srcVal, hdst, hsrc, hK⟩ hsh
        refine ⟨dstVal, srcVal, v, hdst, hsrc, hsh, copyLocals_cons_update_g08 _ _ _ _ ?_ hK⟩
        intro kv hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> dsimp only <;> decide
      · intro t hc hInv hlen hR ⟨hHM, dstVal, srcVal, lenVal, hdst, hsrc, hlen_sh, hK⟩ hnt
        exact mcopy_after_pops_run_g08 s0 dstVal srcVal lenVal hdst hsrc hlen_sh t hc hInv hlen hR ⟨hHM, hK⟩ hnt

end ExistingGroup08

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
