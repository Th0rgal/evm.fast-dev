import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.Common
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.ReadOnly
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.Group04
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group06ControlFlow
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.StateGasHelpers
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.UntypedBufHelpers

/-! # OpHandlerSpec Group 09: `op_log`, `op_return`, `op_revert` -/

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

/-! ## 1. Shared `HeadMemAligned` and `extend_memory` helpers -/

private theorem store_some_eq_error_g09 {F : Type} {s post : PanSemStateFiniteExact 64 F}
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

private theorem headMemAligned_congr_head {F : Type}
    {s t : PanSemStateFiniteExact 64 F}
    (hg : t.globals = s.globals)
    (hmem : ∀ off : Nat, off ∈ ([24, 32, 40] : List Nat) →
      memW t (globN s "ev" + off) = memW s (globN s "ev" + off))
    (h : HeadMemAligned s) : HeadMemAligned t := by
  have hgev : globN t "ev" = globN s "ev" := globN_congr hg ▸ rfl
  have hgfp : globN t "frame_mem_ptr" = globN s "frame_mem_ptr" := globN_congr hg ▸ rfl
  refine ⟨?_, ?_⟩
  · rw [hgev, hmem 32 (by simp)]; exact h.1
  · rw [hgev, hgfp, hmem 24 (by simp), hmem 40 (by simp)]; exact h.2

private theorem eps_stack_pop_headMem :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post =>
        post.globals = s.globals ∧
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
  refine ⟨hInv_p, hch_p, hR_p, hglob_p, ?_⟩
  intro hHM
  obtain ⟨hb_ev, evw, hevw, hevw_nat⟩ := ev_word_bounds hInv
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
  have hmem_ne16 : ∀ x : BitVec 64, x ≠ BitVec.ofNat 64 (globN s "ev" + 16) →
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
                  have herr := store_some_eq_error_g09 hst; subst herr; simp
                | none =>
                  dsimp only
                  obtain ⟨w2, _, hs3_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s2) (post := s3)
                    (gname := "ev") (gbase := globN s "ev") (off := 16) hevw hevw_nat (by omega)
                    (fun u hu => by
                      have hsp2 : s2.locals.lookup (ofString "sp") = some (.val (.word spw)) := by
                        simp [s2, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                      change s2.locals.lookup (ofString "sp") = some u at hu
                      rw [hsp2] at hu; injection hu with hu'; exact ⟨spw, hu'.symm⟩) hst
                  intro _ x hx
                  rw [evaluateHOLFiniteState_return]
                  split
                  · dsimp only; rw [hs3_eq]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hx]; rfl
                  · split
                    · dsimp only [emptyLocalsHOLFinite]; rw [hs3_eq]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hx]; rfl
                    · dsimp only; rw [hs3_eq]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hx]; rfl
              · simp
          · rcases hraise : evaluateHOLFiniteState s1 (.raise (ofString "EvmErr") (.const 2)) with ⟨rr, sr⟩
            have hr_nn : rr ≠ none ∧ sr.globals = s.globals ∧ sr.memory = s.memory := by
              rw [evaluateHOLFiniteState_raise] at hraise; dsimp only [evalHOLExact] at hraise
              split at hraise
              · split at hraise <;> (injection hraise with h1 h2; subst h1 h2; exact ⟨by simp, rfl, rfl⟩)
              · injection hraise with h1 h2; subst h1 h2; exact ⟨by simp, rfl, rfl⟩
            cases rr with
            | none => exact absurd rfl hr_nn.1
            | some r0 =>
              dsimp only
              intro hres
              cases r0 <;> simp at hres
              rename_i vr
              subst hres
              intro x _
              change sr.memory x = s.memory x
              rw [hr_nn.2.2]
        · simp
      · simp
  refine headMemAligned_congr_head hglob_p (fun off hoff => ?_) hHM
  have hne_bv : BitVec.ofNat 64 (globN s "ev" + off) ≠ BitVec.ofNat 64 (globN s "ev" + 16) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    intro heq
    have htn := congrArg BitVec.toNat heq
    rcases hoff with rfl | rfl | rfl <;>
      (rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at htn; omega)
  unfold memW; rw [hmem_ne16 _ hne_bv]

private theorem eps_charge_gas_any_headMem :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post =>
        post.globals = s.globals ∧
        ∀ off : Nat, off ∈ ([24, 32, 40] : List Nat) →
          memW post (globN s "ev" + off) = memW s (globN s "ev" + off))
      (ofString "charge_gas") := by
  refine ⟨_, _, _, M21.lookup_charge_gas, ?_⟩
  intro F s _ hInv _ ⟨vals, hl⟩ _
  have hlen1 : ∃ v0, vals = [v0] := by
    have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
      originalRuntimeCode.lookup (ofString "charge_gas") vals _ _ _ hl
    simp only [Flapjack.lookupCodeHOLExact, M21.lookup_charge_gas] at hx
    rcases vals with _ | ⟨v0, _ | _⟩ <;> simp at hx
    exact ⟨v0, rfl⟩
  obtain ⟨v0, rfl⟩ := hlen1
  obtain ⟨_, _, amtw, rfl, hamt⟩ := one_word_arg_lookup M21.lookup_charge_gas hl
  have hcg := charge_gas_body_exact s hInv hamt
  dsimp only at hcg ⊢
  refine ⟨fun v hv => ?_, fun herr => ?_⟩
  · obtain ⟨hI, hg, hch, hR⟩ := hcg.1 v hv
    refine ⟨hI, hch, by omega, hg, ?_⟩
    intro off hoff
    obtain ⟨hb_ev, evw, hevw, hevw_nat⟩ := ev_word_bounds hInv
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
        x ≠ BitVec.ofNat 64 (globN s "ev" + 64) →
        x ≠ BitVec.ofNat 64 (globN s "ev" + 184) →
        (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_charge_gas)).2.memory x = s.memory x := by
      rcases hrun : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_charge_gas) with ⟨res, cpost⟩
      rw [hrun] at hv; dsimp only at hv ⊢
      rw [hbody_cg, evaluateHOLFiniteState_dec_total] at hrun; dsimp only at hrun
      split at hrun
      · injection hrun with hr_eq _; rw [← hr_eq] at hv; cases hv
      · rename_i glv _
        split at hrun
        · set s1 := setVarHOLFinite (ofString "gl") glv s
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hrun
          split at hrun
          · split at hrun
            · simp only [evaluateHOLFiniteState_skip] at hrun
              rw [evaluateHOLFiniteState_seq_line780] at hrun
              rcases hst1 : evaluateHOLFiniteState s1
                  (.store (.op .add [.var .global (ofString "ev"), .const 64])
                    (.op .sub [.var .local (ofString "gl"), .var .local (ofString "amount")])) with ⟨r1, s2⟩
              rw [hst1] at hrun
              cases r1 with
              | some res1 =>
                have herr1 := store_some_eq_error_g09 hst1; subst herr1
                dsimp only at hrun; injection hrun with hr_eq _; rw [← hr_eq] at hv; cases hv
              | none =>
                dsimp only at hrun
                obtain ⟨w1, _, hs2_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s1) (post := s2)
                  (gname := "ev") (gbase := globN s "ev") (off := 64) hevw hevw_nat (by omega)
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
                rw [evaluateHOLFiniteState_seq_line780] at hrun
                rcases hst2 : evaluateHOLFiniteState s2
                    (.store (.op .add [.var .global (ofString "ev"), .const 184])
                      (.op .add
                        [.load .one (.op .add [.var .global (ofString "ev"), .const 184]),
                         .var .local (ofString "amount")])) with ⟨r2, s3⟩
                rw [hst2] at hrun
                cases r2 with
                | some res2 =>
                  have herr2 := store_some_eq_error_g09 hst2; subst herr2
                  dsimp only at hrun; injection hrun with hr_eq _; rw [← hr_eq] at hv; cases hv
                | none =>
                  dsimp only at hrun
                  obtain ⟨w2, _, hs3_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s2) (post := s3)
                    (gname := "ev") (gbase := globN s "ev") (off := 184)
                    (by rw [hs2_eq]; exact hevw) hevw_nat (by omega)
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
                  rw [evaluateHOLFiniteState_return] at hrun; dsimp only [evalHOLExact] at hrun
                  have hsz0 : sizeOfShapeWithContextHOL s3.structs
                      (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
                    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
                  rw [if_pos hsz0] at hrun; dsimp only at hrun
                  injection hrun with _ hcpost_eq
                  subst hcpost_eq
                  intro x hx64 hx184
                  dsimp only [emptyLocalsHOLFinite]
                  rw [hs3_eq]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hx184]
                  rw [hs2_eq]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hx64]
                  rfl
            · rcases hraise : evaluateHOLFiniteState s1 (.raise (ofString "EvmErr") (.const 4)) with ⟨rr, sr⟩
              rw [hraise] at hrun
              have hr_not_ret : rr ≠ some (.returned v) := by
                rw [evaluateHOLFiniteState_raise] at hraise; dsimp only [evalHOLExact] at hraise
                split at hraise
                · split at hraise <;> (injection hraise with h1 _; subst h1; simp)
                · injection hraise with h1 _; subst h1; simp
              cases rr with
              | none =>
                rw [evaluateHOLFiniteState_raise] at hraise; dsimp only [evalHOLExact] at hraise
                split at hraise
                · split at hraise <;> cases hraise
                · cases hraise
              | some r0 =>
                dsimp only at hrun
                injection hrun with hr_eq _
                subst hr_eq
                exact absurd hv hr_not_ret
          · dsimp only at hrun; injection hrun with hr_eq _; rw [← hr_eq] at hv; cases hv
        · injection hrun with hr_eq _; rw [← hr_eq] at hv; cases hv
    obtain ⟨hb_ev, _, _, _⟩ := ev_word_bounds hInv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    have hne64 : BitVec.ofNat 64 (globN s "ev" + off) ≠ BitVec.ofNat 64 (globN s "ev" + 64) := by
      intro heq; have htn := congrArg BitVec.toNat heq
      rcases hoff with rfl | rfl | rfl <;>
        (rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at htn; omega)
    have hne184 : BitVec.ofNat 64 (globN s "ev" + off) ≠ BitVec.ofNat 64 (globN s "ev" + 184) := by
      intro heq; have htn := congrArg BitVec.toNat heq
      rcases hoff with rfl | rfl | rfl <;>
        (rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at htn; omega)
    unfold memW; rw [hmem_ne _ hne64 hne184]
  · obtain ⟨hI, _, hch, hR⟩ := hcg.2 herr
    exact ⟨hI, hch, le_of_eq hR⟩

private def XCostAligned {F : Type} (t : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ cw ebw : BitVec 64,
    t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
    (ebw = 0#64 ∨
      (memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
       (memW t (globN t "ev" + 32) + ebw.toNat) % 8 = 0 ∧
       memW t (globN t "ev" + 24) + memW t (globN t "ev" + 40) = globN t "frame_mem_ptr"))

private theorem xCostAligned_of_cost1 {F : Type}
    {t ce cpost : PanSemStateFiniteExact 64 F} {cw ebw : BitVec 64}
    (hHM : HeadMemAligned t) (hlf : LocFrame ce cpost)
    (hce_m : ce.memory = t.memory) (hce_g : ce.globals = t.globals)
    (heb : ebw = 0#64 ∨
      ∃ before after : Nat, after < 2 ^ 37 ∧ after % 32 = 0 ∧ before < after ∧
        ebw.toNat = after - before ∧
        (memW ce (globN ce "ev" + 32) % 32 = 0 → before = memW ce (globN ce "ev" + 32))) :
    HeadMemAligned (setVarHOLFinite (ofString "x")
        (.rStruct [.val (.word cw), .val (.word ebw)]) { cpost with locals := t.locals }) ∧
    XCostAligned (setVarHOLFinite (ofString "x")
        (.rStruct [.val (.word cw), .val (.word ebw)]) { cpost with locals := t.locals }) := by
  let res := setVarHOLFinite (ofString "x")
    (.rStruct [.val (.word cw), .val (.word ebw)]) { cpost with locals := t.locals }
  have hHM_ce : HeadMemAligned ce :=
    headMemAligned_congr_head hce_g (fun _ _ => by unfold memW; rw [hce_m]) hHM
  have hHM_cp : HeadMemAligned cpost :=
    headMemAligned_congr_head (by rw [hlf]) (fun _ _ => by unfold memW; rw [hlf]) hHM_ce
  have hHM_res : HeadMemAligned res := headMemAligned_congr_head rfl (fun _ _ => rfl) hHM_cp
  have hmem32 : memW res (globN res "ev" + 32) = memW ce (globN ce "ev" + 32) := by
    have hg : globN res "ev" = globN ce "ev" :=
      globN_congr (show cpost.globals = ce.globals by rw [hlf]) ▸ rfl
    have hm : res.memory = ce.memory := show cpost.memory = ce.memory by rw [hlf]
    rw [hg]; unfold memW; rw [hm]
  refine ⟨hHM_res, cw, ebw, by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], ?_⟩
  rcases heb with rfl | ⟨before, after, haft_lt, haft_mod, hbef_lt, heb_sub, hbef_eq⟩
  · exact Or.inl rfl
  · right
    have hbef : before = memW ce (globN ce "ev" + 32) := hbef_eq hHM_ce.1
    have hsum : memW res (globN res "ev" + 32) + ebw.toNat = after := by
      rw [hmem32, ← hbef]; omega
    rw [hsum]
    exact ⟨haft_lt, by omega, hHM_res.2⟩

private theorem extendMemoryPre_of_xCostAligned {F : Type}
    {t : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {b_em : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs_em : ShapeHOL}
    (hc : t.code = originalRuntimeCode) (hx : XCostAligned t)
    (hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
      [.rfield 1 (.var .local (ofString "x"))] = some values)
    (hl : lookupCodeHOLFinite t.code.lookup (ofString "extend_memory") values =
      some (b_em, callee, rs_em)) :
    ExtendMemoryPre (callEntryStateHOLFinite t callee) := by
  obtain ⟨cw, ebw, hx_lk, heb_cond⟩ := hx
  have hx1 : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
      [.rfield 1 (.var .local (ofString "x"))] = some [.val (.word ebw)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact, evalHOLExact, hx_lk]
  rw [hx1] at hargs; injection hargs with hvs; subst hvs
  have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "extend_memory") [.val (.word ebw)] =
      some (b_em, callee, rs_em) := by rwa [← hc]
  obtain ⟨_, _, ebw', heq_eb, hcal_eb⟩ := one_word_arg_lookup lookup_extend_memory hl_orig
  injection heq_eb with heq1; injection heq1 with heq2; subst heq2
  exact ⟨ebw, hcal_eb, heb_cond⟩

/-! ## 2. `op_return` and `op_revert` -/

theorem lookup_op_return :
    originalRuntimeCode.lookup (ofString "op_return") =
      some ([], sourceFnBody Guest.Software.guestFn_op_return, .one) :=
  lookup_of_guestAst_getElem 568 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_op_return) rfl

theorem lookup_op_revert :
    originalRuntimeCode.lookup (ofString "op_revert") =
      some ([], sourceFnBody Guest.Software.guestFn_op_revert, .one) :=
  lookup_of_guestAst_getElem 569 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_op_revert) rfl

private theorem eval_ev24_plus_s_word {F : Type} (t : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hv : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.op .add
        [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]),
         .var .local (ofString "s")]) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  simp only [evalHOLExact, wordOpHOL] at hv; revert hv
  rcases @evalListHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) _ with _ | vs
  · simp
  · dsimp only; split
    · simp only [Option.map]
      rcases wordOp .add (vs.map valueWord) with _ | w
      · simp
      · intro hv; injection hv with hv'; exact ⟨w, hv'.symm⟩
    · simp

private theorem eval_local_n_word {F : Type} (t : PanSemStateFiniteExact 64 F) (nw : BitVec 64)
    (hn : t.locals.lookup (ofString "n") = some (.val (.word nw))) (v : ValueHOL 64)
    (hv : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.var .local (ofString "n")) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  simp only [evalHOLExact, hn] at hv
  injection hv with hv'
  exact ⟨nw, hv'.symm⟩

private theorem seq_raise_evmErr_ret {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    (e r : ExpHOL 64) :
    HandlerRun s0 P charged (.seq (.raise (ofString "EvmErr") e) (.return r)) := by
  intro t _ hInv hlen hR _ _
  have hR_le : OpDispatchSpec.evmR t ≤ OpDispatchSpec.evmR s0 := by
    cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at hR <;> omega
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_raise]
  rcases t.eshapes.lookup (ofString "EvmErr") with _ | sh
  · exact opDispatchPost_error s0 t
  · rcases @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e with _ | ve
    · exact opDispatchPost_error s0 t
    · dsimp only
      by_cases hok : shapeOfHOLExact ve = sh ∧ sizeOfShapeWithContextHOL t.structs (shapeOfHOLExact ve) ≤ 32
      · rw [if_pos hok]; dsimp only
        have hInv' : EvmInv (emptyLocalsHOLFinite t) :=
          localsFree_evmInv t (emptyLocalsHOLFinite t).locals t.clock hInv
        have hc := evm_congr (s := t) (t := emptyLocalsHOLFinite t) rfl rfl
        refine ⟨?_, fun _ => ⟨hInv', by rw [hc.2.2.1]; exact hlen, by rw [hc.2.1]; exact hR_le⟩⟩
        rintro ⟨_, h⟩; cases h
      · rw [if_neg hok]; dsimp only
        exact opDispatchPost_error s0 t

/-- Conditional `OpHandlerSpec` for `op_return` given an `EvmPreservingSpec` for `extend_memory`
    under bounded `expand_by < 2 ^ 37`. -/
theorem op_return_spec_of_extend_memory
    {Qem : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h_extend_memory : EvmPreservingSpec
      (fun s => ∃ ebw : BitVec 64,
        s.locals.lookup (ofString "expand_by") = some (.val (.word ebw)) ∧
        ebw.toNat < 2 ^ 37)
      Qem
      (ofString "extend_memory")) :
    OpHandlerSpec (ofString "op_return") := by
  refine opHandlerSpec_of_run 568 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_return rfl ?_
  intro F s0 hRun
  dsimp only [Guest.Software.guestFn_op_return, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRun.decCall_simple eps_stack_pop ?_
  refine HandlerRun.decCall_simple eps_stack_pop ?_
  refine HandlerRun.decCall
    (Q := fun t => ∃ cw ebw : BitVec 64,
      t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
      ebw.toNat < 2 ^ 37)
    eps_extend_memory_cost1_bounds
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ v _ _ _ _ _ _ _ hQc => by
      obtain ⟨_, cw, ebw, rfl, heb_bounds⟩ := hQc
      refine ⟨cw, ebw, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], ?_⟩
      rcases heb_bounds with rfl | ⟨_, after, haft_lt, _, _, heb_sub, _⟩
      · decide
      · omega)
    ?_
  refine HandlerRun.seq_call
    (Q := fun t => ∃ cw ebw : BitVec 64,
      t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
      ebw.toNat < 2 ^ 37)
    eps_charge_gas_any
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ hx _ _ _ _ _ => hx)
    ?_
  refine HandlerRun.seq_call (Q := fun _ => True) h_extend_memory
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
    ?_
  refine HandlerRun.decCall_shaped eps_sat_word
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ v _ _ _ hsh _ _ _ _ _ => by
      rcases v with ⟨⟨nw⟩⟩ | _ | _
      · exact ⟨nw, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
      · simp [shapeOfHOLExact, shapeEqHOL] at hsh
      · simp [shapeOfHOLExact, shapeEqHOL] at hsh)
    (P := fun _ => True)
    (Q := fun t => ∃ nw : BitVec 64, t.locals.lookup (ofString "n") = some (.val (.word nw)))
    ?_
  refine HandlerRun.decCall
    (Q := fun t => ∃ nw : BitVec 64, t.locals.lookup (ofString "n") = some (.val (.word nw)))
    eps_sat_word
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ ⟨nw, hnw⟩ _ _ _ _ _ => by
      have hne_sn : ofString "s" ≠ ofString "n" := by decide
      exact ⟨nw, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne_sn, Ne.symm hne_sn, hnw]⟩)
    ?_
  refine HandlerRun.seq_store_ev_nonstruct
    (Q := fun t => ∃ nw : BitVec 64, t.locals.lookup (ofString "n") = some (.val (.word nw)))
    120 (by simp [nonStructFrameOffs])
    (fun t v _ hv => eval_ev24_plus_s_word t v hv)
    (fun _ _ _ _ hP => hP)
    ?_
  refine HandlerRun.seq_store_ev_nonstruct (Q := fun _ => True)
    128 (by simp [nonStructFrameOffs])
    (fun t v ⟨nw, hnw⟩ hv => eval_local_n_word t nw hnw v hv)
    (fun _ _ _ _ _ => trivial)
    ?_
  refine HandlerRun.seq_store_ev_nonstruct (Q := fun t => memW t (globN t "ev" + 104) = 0)
    104 (by simp [nonStructFrameOffs])
    (fun _ v _ hv => by
      change some (ValueHOL.val (.word 0#64)) = some v at hv
      injection hv with hv'; exact ⟨0, hv'.symm⟩)
    (fun t w hw _ _ => by
      change some (ValueHOL.val (.word 0#64)) = some (.val (.word w)) at hw
      injection hw with hw1; injection hw1 with hw2; injection hw2 with hw3; subst hw3
      simpa [globN] using R14Shards.OpHandlersA.memW_updW_same t (globN t "ev" + 104) 0)
    (HandlerRun.ret_done hRun (fun _ _ hP => Or.inr (Or.inl hP)) _)

/-- Unconditional `FunSpec` for `op_return` under `EvmRun s ∧ HeadMemAligned s`. -/
theorem op_return_aligned_spec :
    FunSpec (fun s => EvmRun s ∧ HeadMemAligned s) OpDispatchPost (ofString "op_return") := by
  refine ⟨_, _, _, lookup_op_return, ?_⟩
  intro F s0 hcode ⟨hRun, hHM0⟩ _ hnt
  suffices hrun : HandlerRun s0 HeadMemAligned false (sourceFnBody Guest.Software.guestFn_op_return) from
    hrun s0 hcode hRun.1 rfl (le_refl _) hHM0 hnt
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_op_return,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRun.decCall (Q := HeadMemAligned) eps_stack_pop_headMem
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ callee _ _ cpost _ hHM _ _ _ _ ⟨_, hHM_step⟩ =>
      headMemAligned_congr_head rfl (fun _ _ => rfl)
        (hHM_step (headMemAligned_congr_head rfl (fun _ _ => rfl) hHM)))
    ?_
  refine HandlerRun.decCall (Q := HeadMemAligned) eps_stack_pop_headMem
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ callee _ _ cpost _ hHM _ _ _ _ ⟨_, hHM_step⟩ =>
      headMemAligned_congr_head rfl (fun _ _ => rfl)
        (hHM_step (headMemAligned_congr_head rfl (fun _ _ => rfl) hHM)))
    ?_
  refine HandlerRun.decCall (Q := fun t => HeadMemAligned t ∧ XCostAligned t)
    eps_extend_memory_cost1_bounds
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ _ _ _ _ _ hHM _ _ _ _ hQc => by
      obtain ⟨hlf, cw, ebw, rfl, heb⟩ := hQc
      exact xCostAligned_of_cost1 hHM hlf rfl rfl heb)
    ?_
  refine HandlerRun.seq_call (Q := XCostAligned) eps_charge_gas_any_headMem
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ _ _ _ cpost _ ⟨hHM, cw, ebw, hx, heb⟩ _ _ _ _ ⟨hglob_cp, hmem_cp⟩ => by
      have hHM_cp : HeadMemAligned cpost :=
        headMemAligned_congr_head hglob_cp hmem_cp
          (headMemAligned_congr_head rfl (fun _ _ => rfl) hHM)
      let res : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
      have hHM_res : HeadMemAligned res := headMemAligned_congr_head rfl (fun _ _ => rfl) hHM_cp
      have hmem32 : memW res (globN res "ev" + 32) = memW t (globN t "ev" + 32) := by
        have hg : globN res "ev" = globN t "ev" := globN_congr hglob_cp ▸ rfl
        rw [hg]; exact hmem_cp 32 (by simp)
      refine ⟨cw, ebw, hx, ?_⟩
      rcases heb with rfl | ⟨hlt37, hmod8, _⟩
      · exact Or.inl rfl
      · right; rw [hmem32]; exact ⟨hlt37, hmod8, hHM_res.2⟩)
    ?_
  refine HandlerRun.seq_call (Q := fun _ => True) eps_extend_memory_aligned
    (fun t values b_em callee rs_em hc _ hx hargs hl =>
      extendMemoryPre_of_xCostAligned hc hx hargs hl)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
    ?_
  refine HandlerRun.decCall_shaped eps_sat_word
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ v _ _ _ hsh _ _ _ _ _ => by
      rcases v with ⟨⟨nw⟩⟩ | _ | _
      · exact ⟨nw, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
      · simp [shapeOfHOLExact, shapeEqHOL] at hsh
      · simp [shapeOfHOLExact, shapeEqHOL] at hsh)
    (P := fun _ => True)
    (Q := fun t => ∃ nw : BitVec 64, t.locals.lookup (ofString "n") = some (.val (.word nw)))
    ?_
  refine HandlerRun.decCall
    (Q := fun t => ∃ nw : BitVec 64, t.locals.lookup (ofString "n") = some (.val (.word nw)))
    eps_sat_word
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ ⟨nw, hnw⟩ _ _ _ _ _ => by
      have hne_sn : ofString "s" ≠ ofString "n" := by decide
      exact ⟨nw, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne_sn, Ne.symm hne_sn, hnw]⟩)
    ?_
  refine HandlerRun.seq_store_ev_nonstruct
    (Q := fun t => ∃ nw : BitVec 64, t.locals.lookup (ofString "n") = some (.val (.word nw)))
    120 (by simp [nonStructFrameOffs])
    (fun t v _ hv => eval_ev24_plus_s_word t v hv)
    (fun _ _ _ _ hP => hP)
    ?_
  refine HandlerRun.seq_store_ev_nonstruct (Q := fun _ => True)
    128 (by simp [nonStructFrameOffs])
    (fun t v ⟨nw, hnw⟩ hv => eval_local_n_word t nw hnw v hv)
    (fun _ _ _ _ _ => trivial)
    ?_
  refine HandlerRun.seq_store_ev_nonstruct (Q := fun t => memW t (globN t "ev" + 104) = 0)
    104 (by simp [nonStructFrameOffs])
    (fun _ v _ hv => by
      change some (ValueHOL.val (.word 0#64)) = some v at hv
      injection hv with hv'; exact ⟨0, hv'.symm⟩)
    (fun t w hw _ _ => by
      change some (ValueHOL.val (.word 0#64)) = some (.val (.word w)) at hw
      injection hw with hw1; injection hw1 with hw2; injection hw2 with hw3; subst hw3
      simpa [globN] using R14Shards.OpHandlersA.memW_updW_same t (globN t "ev" + 104) 0)
    (HandlerRun.ret_done hRun (fun _ _ hP => Or.inr (Or.inl hP)) _)

/-- Conditional `OpHandlerSpec` for `op_revert` given an `EvmPreservingSpec` for `extend_memory`
    under bounded `expand_by < 2 ^ 37`. -/
theorem op_revert_spec_of_extend_memory
    {Qem : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h_extend_memory : EvmPreservingSpec
      (fun s => ∃ ebw : BitVec 64,
        s.locals.lookup (ofString "expand_by") = some (.val (.word ebw)) ∧
        ebw.toNat < 2 ^ 37)
      Qem
      (ofString "extend_memory")) :
    OpHandlerSpec (ofString "op_revert") := by
  refine opHandlerSpec_of_run 569 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_revert rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_revert, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRun.decCall_simple eps_stack_pop ?_
  refine HandlerRun.decCall_simple eps_stack_pop ?_
  refine HandlerRun.decCall
    (Q := fun t => ∃ cw ebw : BitVec 64,
      t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
      ebw.toNat < 2 ^ 37)
    eps_extend_memory_cost1_bounds
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ v _ _ _ _ _ _ _ hQc => by
      obtain ⟨_, cw, ebw, rfl, heb_bounds⟩ := hQc
      refine ⟨cw, ebw, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], ?_⟩
      rcases heb_bounds with rfl | ⟨_, after, haft_lt, _, _, heb_sub, _⟩
      · decide
      · omega)
    ?_
  refine HandlerRun.seq_call
    (Q := fun t => ∃ cw ebw : BitVec 64,
      t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
      ebw.toNat < 2 ^ 37)
    eps_charge_gas_any
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ hx _ _ _ _ _ => hx)
    ?_
  refine HandlerRun.seq_call (Q := fun _ => True) h_extend_memory
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
    ?_
  refine HandlerRun.decCall_shaped eps_sat_word
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ v _ _ _ hsh _ _ _ _ _ => by
      rcases v with ⟨⟨nw⟩⟩ | _ | _
      · exact ⟨nw, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
      · simp [shapeOfHOLExact, shapeEqHOL] at hsh
      · simp [shapeOfHOLExact, shapeEqHOL] at hsh)
    (P := fun _ => True)
    (Q := fun t => ∃ nw : BitVec 64, t.locals.lookup (ofString "n") = some (.val (.word nw)))
    ?_
  refine HandlerRun.decCall
    (Q := fun t => ∃ nw : BitVec 64, t.locals.lookup (ofString "n") = some (.val (.word nw)))
    eps_sat_word
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ ⟨nw, hnw⟩ _ _ _ _ _ => by
      have hne_sn : ofString "s" ≠ ofString "n" := by decide
      exact ⟨nw, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne_sn, Ne.symm hne_sn, hnw]⟩)
    ?_
  refine HandlerRun.seq_store_ev_nonstruct
    (Q := fun t => ∃ nw : BitVec 64, t.locals.lookup (ofString "n") = some (.val (.word nw)))
    120 (by simp [nonStructFrameOffs])
    (fun t v _ hv => eval_ev24_plus_s_word t v hv)
    (fun _ _ _ _ hP => hP)
    ?_
  refine HandlerRun.seq_store_ev_nonstruct (Q := fun _ => True)
    128 (by simp [nonStructFrameOffs])
    (fun t v ⟨nw, hnw⟩ hv => eval_local_n_word t nw hnw v hv)
    (fun _ _ _ _ _ => trivial)
    (seq_raise_evmErr_ret _ _)

/-- Unconditional `FunSpec` for `op_revert` under `EvmRun s ∧ HeadMemAligned s`. -/
theorem op_revert_aligned_spec :
    FunSpec (fun s => EvmRun s ∧ HeadMemAligned s) OpDispatchPost (ofString "op_revert") := by
  refine ⟨_, _, _, lookup_op_revert, ?_⟩
  intro F s0 hcode ⟨hRun, hHM0⟩ _ hnt
  suffices hrun : HandlerRun s0 HeadMemAligned false (sourceFnBody Guest.Software.guestFn_op_revert) from
    hrun s0 hcode hRun.1 rfl (le_refl _) hHM0 hnt
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_op_revert,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRun.decCall (Q := HeadMemAligned) eps_stack_pop_headMem
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ callee _ _ cpost _ hHM _ _ _ _ ⟨_, hHM_step⟩ =>
      headMemAligned_congr_head rfl (fun _ _ => rfl)
        (hHM_step (headMemAligned_congr_head rfl (fun _ _ => rfl) hHM)))
    ?_
  refine HandlerRun.decCall (Q := HeadMemAligned) eps_stack_pop_headMem
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ callee _ _ cpost _ hHM _ _ _ _ ⟨_, hHM_step⟩ =>
      headMemAligned_congr_head rfl (fun _ _ => rfl)
        (hHM_step (headMemAligned_congr_head rfl (fun _ _ => rfl) hHM)))
    ?_
  refine HandlerRun.decCall (Q := fun t => HeadMemAligned t ∧ XCostAligned t)
    eps_extend_memory_cost1_bounds
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ _ _ _ _ _ hHM _ _ _ _ hQc => by
      obtain ⟨hlf, cw, ebw, rfl, heb⟩ := hQc
      exact xCostAligned_of_cost1 hHM hlf rfl rfl heb)
    ?_
  refine HandlerRun.seq_call (Q := XCostAligned) eps_charge_gas_any_headMem
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ _ _ _ cpost _ ⟨hHM, cw, ebw, hx, heb⟩ _ _ _ _ ⟨hglob_cp, hmem_cp⟩ => by
      have hHM_cp : HeadMemAligned cpost :=
        headMemAligned_congr_head hglob_cp hmem_cp
          (headMemAligned_congr_head rfl (fun _ _ => rfl) hHM)
      let res : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
      have hHM_res : HeadMemAligned res := headMemAligned_congr_head rfl (fun _ _ => rfl) hHM_cp
      have hmem32 : memW res (globN res "ev" + 32) = memW t (globN t "ev" + 32) := by
        have hg : globN res "ev" = globN t "ev" := globN_congr hglob_cp ▸ rfl
        rw [hg]; exact hmem_cp 32 (by simp)
      refine ⟨cw, ebw, hx, ?_⟩
      rcases heb with rfl | ⟨hlt37, hmod8, _⟩
      · exact Or.inl rfl
      · right; rw [hmem32]; exact ⟨hlt37, hmod8, hHM_res.2⟩)
    ?_
  refine HandlerRun.seq_call (Q := fun _ => True) eps_extend_memory_aligned
    (fun t values b_em callee rs_em hc _ hx hargs hl =>
      extendMemoryPre_of_xCostAligned hc hx hargs hl)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
    ?_
  refine HandlerRun.decCall_shaped eps_sat_word
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ v _ _ _ hsh _ _ _ _ _ => by
      rcases v with ⟨⟨nw⟩⟩ | _ | _
      · exact ⟨nw, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
      · simp [shapeOfHOLExact, shapeEqHOL] at hsh
      · simp [shapeOfHOLExact, shapeEqHOL] at hsh)
    (P := fun _ => True)
    (Q := fun t => ∃ nw : BitVec 64, t.locals.lookup (ofString "n") = some (.val (.word nw)))
    ?_
  refine HandlerRun.decCall
    (Q := fun t => ∃ nw : BitVec 64, t.locals.lookup (ofString "n") = some (.val (.word nw)))
    eps_sat_word
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ ⟨nw, hnw⟩ _ _ _ _ _ => by
      have hne_sn : ofString "s" ≠ ofString "n" := by decide
      exact ⟨nw, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne_sn, Ne.symm hne_sn, hnw]⟩)
    ?_
  refine HandlerRun.seq_store_ev_nonstruct
    (Q := fun t => ∃ nw : BitVec 64, t.locals.lookup (ofString "n") = some (.val (.word nw)))
    120 (by simp [nonStructFrameOffs])
    (fun t v _ hv => eval_ev24_plus_s_word t v hv)
    (fun _ _ _ _ hP => hP)
    ?_
  refine HandlerRun.seq_store_ev_nonstruct (Q := fun _ => True)
    128 (by simp [nonStructFrameOffs])
    (fun t v ⟨nw, hnw⟩ hv => eval_local_n_word t nw hnw v hv)
    (fun _ _ _ _ _ => trivial)
    (seq_raise_evmErr_ret _ _)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
