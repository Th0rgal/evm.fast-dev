import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.Common
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.ReadOnly
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.StoreAllocHelpers
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.Group04
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group06ControlFlow
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.StateGasHelpers
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.UntypedBufHelpers
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.AllocJournalStep

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

private theorem evmR_lt_saturated_g09 {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s) : OpDispatchSpec.evmR s < 2 ^ 64 - 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hGas⟩ := hInv
  change OpDispatchSpec.evmR s + 1 < 2 ^ 64 at hGas
  omega

private theorem charge_gas_return_amount_lt_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hInv : EvmInv s) {amtw : BitVec 64}
    (hamt : s.locals.lookup (ofString "amount") = some (.val (.word amtw)))
    {v : ValueHOL 64}
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_charge_gas)).1 =
      some (.returned v)) : amtw.toNat < 2 ^ 64 - 1 := by
  have hcharged := (charge_gas_body_exact s hInv hamt).1 v hret
  have hbound := evmR_lt_saturated_g09 hInv
  omega

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

def satWordG09 (v : ValueHOL 64) : BitVec 64 :=
  match v with
  | .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)] =>
      if b ||| c ||| d ≠ 0#64 then 18446744073709551615#64 else a
  | _ => 18446744073709551615#64

theorem sat_word_body_exact_g09 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b c d : BitVec 64)
    (hv : s.locals.lookup (ofString "v") =
      some (.rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sat_word)).1 =
      some (.returned v)) :
    v = .val (.word (satWordG09
      (.rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]))) := by
  have hbody : sourceFnBody Guest.Software.guestFn_sat_word =
      .seq
        (.ite (.cmp .notEqual
          (.op .or [.rfield 1 (.var .local (ofString "v")),
            .rfield 2 (.var .local (ofString "v")),
            .rfield 3 (.var .local (ofString "v"))]) (.const 0#64))
          (.return (.const 18446744073709551615#64)) .skip)
        (.return (.rfield 0 (.var .local (ofString "v")))) := rfl
  rw [hbody, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
  have hor : OrOp.or b (OrOp.or c (OrOp.or d 0#64)) = b ||| c ||| d := by
    change b ||| (c ||| (d ||| 0#64)) = (b ||| c) ||| d
    simp [BitVec.or_assoc]
  by_cases h : b ||| c ||| d ≠ 0#64
  · simpa [evalHOLExact, evalListHOLExact, hv, wordOpHOL, wordOp, valueIsWord,
      valueWord, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hor, h,
      evaluateHOLFiniteState_return, shapeOfHOLExact, sizeOfShapeWithContextHOL,
      satWordG09] using hret.symm
  · simpa [evalHOLExact, evalListHOLExact, hv, wordOpHOL, wordOp, valueIsWord,
      valueWord, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hor, h,
      evaluateHOLFiniteState_return, evaluateHOLFiniteState_skip,
      shapeOfHOLExact, sizeOfShapeWithContextHOL, satWordG09] using hret.symm

theorem eps_sat_word_exact_g09 :
    EvmPreservingSpec
      (fun s => ∃ a b c d : BitVec 64,
        s.locals.lookup (ofString "v") =
          some (.rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]))
      (fun s v post => LocFrame s post ∧
        ∀ x : ValueHOL 64, s.locals.lookup (ofString "v") = some x →
          v = .val (.word (satWordG09 x)))
      (ofString "sat_word") := by
  obtain ⟨params, body, retShape, hlk, hro⟩ := eps_sat_word
  have hlookup : originalRuntimeCode.lookup (ofString "sat_word") =
      some ([(ofString "v", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_sat_word, .one) :=
    lookup_of_guestAst_getElem 440 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_sat_word) rfl
  have heq := hlookup.symm.trans hlk
  injection heq with hp
  rcases Prod.mk.inj hp with ⟨rfl, hrest⟩
  rcases Prod.mk.inj hrest with ⟨hb, rfl⟩
  subst hb
  refine ⟨_, _, _, hlookup, ?_⟩
  intro F s hcode hInv hP hargs hnt
  have hs := hro s hcode hInv trivial hargs hnt
  refine ⟨?_, hs.2⟩
  intro v hv
  obtain ⟨hInv', hchain, hR, hlf⟩ := hs.1 v hv
  refine ⟨hInv', hchain, hR, hlf, ?_⟩
  intro x hx
  obtain ⟨a, b, c, d, hl⟩ := hP
  have hval := Option.some.inj (hx.symm.trans hl)
  subst hval
  exact sat_word_body_exact_g09 s a b c d hl v hv

def ceil32NatG09 (n : Nat) : Nat := ((n + 31) / 32) * 32

private theorem one_u256_arg_lookup_g09 {fname param : MlS} {body : ProgHOL 64}
    {v0 : ValueHOL 64} {body' : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret' : ShapeHOL}
    (hlook : originalRuntimeCode.lookup fname =
      some ([(param, .comb [.one, .one, .one, .one])], body, .one))
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname [v0] = some (body', callee, ret')) :
    body' = body ∧ ret' = .one ∧ callee.lookup param = some v0 := by
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
    originalRuntimeCode.lookup fname [v0] body' callee ret' hl
  simp only [Flapjack.lookupCodeHOLExact, hlook] at hx
  split at hx
  · have heq := Option.some.inj hx
    rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨hloc, rfl⟩
    refine ⟨rfl, rfl, ?_⟩
    have hfn := congrFun hloc.symm param
    simpa [FUPDATE_LIST, FUPDATE] using hfn
  · cases hx

private theorem u256_is_zero_body_exact_g09 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b c d : BitVec 64)
    (ha : s.locals.lookup (ofString "a") =
      some (.rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_is_zero)).1 =
      some (.returned v)) :
    v = .val (.word (if a ||| b ||| c ||| d = 0#64 then 1#64 else 0#64)) := by
  have hbody : sourceFnBody Guest.Software.guestFn_u256_is_zero =
      .seq (.ite (.cmp .equal (.op .or [.rfield 0 (.var .local (ofString "a")),
          .rfield 1 (.var .local (ofString "a")),
          .rfield 2 (.var .local (ofString "a")),
          .rfield 3 (.var .local (ofString "a"))]) (.const 0#64))
        (.return (.const 1#64)) .skip)
        (.return (.const 0#64)) := rfl
  rw [hbody, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
  have hor : OrOp.or a (OrOp.or b (OrOp.or c (OrOp.or d 0#64))) = a ||| b ||| c ||| d := by
    change a ||| (b ||| (c ||| (d ||| 0#64))) = ((a ||| b) ||| c) ||| d
    simp [BitVec.or_assoc]
  by_cases h : a ||| b ||| c ||| d = 0#64
  · simpa [evalHOLExact, evalListHOLExact, ha, wordOpHOL, wordOp, valueIsWord,
      valueWord, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hor, h,
      evaluateHOLFiniteState_return, shapeOfHOLExact, sizeOfShapeWithContextHOL] using hret.symm
  · simpa [evalHOLExact, evalListHOLExact, ha, wordOpHOL, wordOp, valueIsWord,
      valueWord, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hor, h,
      evaluateHOLFiniteState_return, evaluateHOLFiniteState_skip,
      shapeOfHOLExact, sizeOfShapeWithContextHOL] using hret.symm

private theorem add_sat_body_exact_g09 {F : Type} (s : PanSemStateFiniteExact 64 F) {aw bw : BitVec 64}
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
    simp [evalHOLExact, hs1_s, hs1_a, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
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

private theorem ceil32_body_exact_g09 {F : Type} (s : PanSemStateFiniteExact 64 F) {vw : BitVec 64}
    (hcode : s.code = originalRuntimeCode)
    (hv_lk : s.locals.lookup (ofString "v") = some (.val (.word vw)))
    (ret : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_ceil32)).1 =
      some (.returned ret)) :
    ∃ cw : BitVec 64, ret = .val (.word cw) ∧
      (vw.toNat ≤ 2 ^ 64 - 32 →
        cw.toNat = ceil32NatG09 vw.toNat ∧ vw.toNat ≤ cw.toNat ∧
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
    simp [evalHOLExact, hs1_r, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
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
    · intro hle; exact ⟨by unfold ceil32NatG09; omega, le_rfl, hle, hmod0, fun _ => rfl⟩
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
    have hlk := pan_two_word_lookup s1.code.lookup
      (ofString "add_sat") (ofString "a") (ofString "b")
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
            obtain ⟨sw, rfl, hsw_nat⟩ := add_sat_body_exact_g09 (callEntryStateHOLFinite s1 cal) ha_lk hb_lk vb
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
                refine ⟨by unfold ceil32NatG09; omega, by omega, by omega, by omega, fun hm => by omega⟩
              · intro hge
                have hover : ¬ (vw.toNat + (32 - vw.toNat % 32) < 2 ^ 64) := by omega
                rw [if_neg hover] at hsw_nat
                exact hsw_nat
            · simp at hret
          · simp at hret
        | _ => simp at hret

private theorem satWordG09_ne_zero_of_or_ne_zero (a b c d : BitVec 64)
    (h : a ||| b ||| c ||| d ≠ 0#64) :
    satWordG09 (.rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ≠ 0#64 := by
  dsimp only [satWordG09]
  by_cases hhi : b ||| c ||| d ≠ 0#64
  · rw [if_pos hhi]; decide
  · rw [if_neg hhi]
    have hhi0 : b ||| c ||| d = 0#64 := Classical.not_not.1 hhi
    intro ha0
    apply h
    subst ha0
    have : (((0#64 ||| b) ||| c) ||| d) = b ||| c ||| d := by simp [BitVec.or_assoc]
    exact this.trans hhi0

private theorem or_ne_zero_of_satWordG09_ne_zero (a b c d : BitVec 64)
    (h : satWordG09 (.rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ≠ 0#64) :
    a ||| b ||| c ||| d ≠ 0#64 := by
  intro hz
  apply h
  have hd0 : d = 0#64 := by
    ext i hi
    have hbit := congrArg (fun x : BitVec 64 => x[i]) hz
    simp only [BitVec.getElem_or, BitVec.getElem_zero, Bool.or_eq_false_iff] at hbit
    simp [hbit.2]
  have hc0 : c = 0#64 := by
    ext i hi
    have hbit := congrArg (fun x : BitVec 64 => x[i]) hz
    simp only [BitVec.getElem_or, BitVec.getElem_zero, Bool.or_eq_false_iff] at hbit
    simp [hbit.1.2]
  have hb0 : b = 0#64 := by
    ext i hi
    have hbit := congrArg (fun x : BitVec 64 => x[i]) hz
    simp only [BitVec.getElem_or, BitVec.getElem_zero, Bool.or_eq_false_iff] at hbit
    simp [hbit.1.1.2]
  have ha0 : a = 0#64 := by
    ext i hi
    have hbit := congrArg (fun x : BitVec 64 => x[i]) hz
    simp only [BitVec.getElem_or, BitVec.getElem_zero, Bool.or_eq_false_iff] at hbit
    simp [hbit.1.1.1]
  simp [satWordG09, ha0, hb0, hc0, hd0]

theorem extend_memory_cost1_window_body_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (s0 s1w s2w s3w z0 z1 z2 z3 cw ebw : BitVec 64)
    (hstart : s.locals.lookup (ofString "start") =
      some (.rStruct [.val (.word s0), .val (.word s1w), .val (.word s2w), .val (.word s3w)]))
    (hsize : s.locals.lookup (ofString "size") =
      some (.rStruct [.val (.word z0), .val (.word z1), .val (.word z2), .val (.word z3)]))
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_extend_memory_cost1)).1 =
      some (.returned (.rStruct [.val (.word cw), .val (.word ebw)])))
    (hcw : cw ≠ 18446744073709551615#64)
    (hsz_nz : satWordG09
      (.rStruct [.val (.word z0), .val (.word z1), .val (.word z2), .val (.word z3)]) ≠ 0#64) :
    (satWordG09
      (.rStruct [.val (.word s0), .val (.word s1w), .val (.word s2w), .val (.word s3w)])).toNat +
    (satWordG09
      (.rStruct [.val (.word z0), .val (.word z1), .val (.word z2), .val (.word z3)])).toNat ≤
      ceil32NatG09 (memW s (globN s "ev" + 32)) + ebw.toNat := by
  let startVal : ValueHOL 64 :=
    .rStruct [.val (.word s0), .val (.word s1w), .val (.word s2w), .val (.word s3w)]
  let sizeVal : ValueHOL 64 :=
    .rStruct [.val (.word z0), .val (.word z1), .val (.word z2), .val (.word z3)]
  let v : ValueHOL 64 := .rStruct [.val (.word cw), .val (.word ebw)]
  have hlk_u256_is_zero : originalRuntimeCode.lookup (ofString "u256_is_zero") =
      some ([(ofString "a", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_u256_is_zero, .one) :=
    lookup_of_guestAst_getElem 42 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_u256_is_zero) rfl
  have hlk_sat_word : originalRuntimeCode.lookup (ofString "sat_word") =
      some ([(ofString "v", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_sat_word, .one) :=
    lookup_of_guestAst_getElem 440 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_sat_word) rfl
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
  have step_ro_call : ∀ {st : PanSemStateFiniteExact 64 F} {nm fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64},
      opRoCallees fname = true →
      st.code = originalRuntimeCode →
      LocFrame s st →
      (evaluateHOLFiniteState st (.decCall nm .one fname args cont)).1 = some (.returned v) →
      ∃ (w : BitVec 64) (st' : PanSemStateFiniteExact 64 F),
        st'.code = originalRuntimeCode ∧
        LocFrame s st' ∧
        st'.locals = st.locals.update (nm, .val (.word w)) ∧
        (∃ vals body callee rs,
          evalListHOLFinite st (h := fun x => Classical.propDecidable (st.memaddrs x)) args = some vals ∧
          lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, callee, rs) ∧
          (evaluateHOLFiniteState (callEntryStateHOLFinite st callee) body).1 = some (.returned (.val (.word w)))) ∧
        (evaluateHOLFiniteState st' cont).1 = some (.returned v) := by
    intro st nm fname args cont hfn hst_c hst_lf hr
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
            rwa [← hst_c]
          have hbody_ro := opRoCallees_good fname hfn vals body callee rs hl_orig
          have hsafe := evaluate_readOnlyProg opRoCallees opRoCallees_good body hbody_ro
            (callEntryStateHOLFinite st callee) hst_c
          rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite st callee) body with ⟨rb, pb⟩
          rw [hrun] at hr
          have hpb_c : pb.code = originalRuntimeCode := by
            have hm := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite st callee) body).1
            rw [hrun] at hm; exact hm.trans hst_c
          rcases rb with _ | rb
          · simp at hr
          · cases rb with
            | returned vb =>
              dsimp only at hr
              split at hr
              · rename_i hsh_vb
                dsimp only at hr
                have hsh_one : shapeEqHOL (shapeOfHOLExact vb) .one = true := by
                  simp [Bool.and_eq_true] at hsh_vb; exact hsh_vb.1
                rcases vb with ⟨⟨w⟩⟩ | _ | _
                · have hlf_ce : LocFrame (callEntryStateHOLFinite st callee) pb := by
                    have hres := hsafe.to_resumes (by rw [hrun]; exact Or.inl ⟨.val (.word w), rfl⟩)
                    simpa [hrun] using hres
                  have hlf_st : LocFrame st pb := by
                    unfold LocFrame at hlf_ce ⊢; rw [hlf_ce]; rfl
                  let st' := setVarHOLFinite nm (.val (.word w)) { pb with locals := st.locals }
                  have hlf_st' : LocFrame s st' :=
                    hst_lf.trans (hlf_st.with_locals_clock (st.locals.update (nm, .val (.word w))) pb.clock)
                  exact ⟨w, st', hpb_c, hlf_st', rfl,
                    ⟨vals, body, callee, rs, rfl, hl_orig, by rw [hrun]⟩, hr⟩
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh_one
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh_one
              · simp at hr
            | _ => simp at hr
  have h10 : ¬ ((1#64 : BitVec 64) = 0) := by decide
  have h00 : (0#64 : BitVec 64) = 0 := rfl
  change (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_extend_memory_cost1)).1 =
    some (.returned v) at hret
  rw [hbody] at hret
  obtain ⟨zw, s1, hs1_c, hs1_lf, hs1_loc, ⟨vals1, body1, cal1, rs1, hargs1, hl1, hrun1⟩, hr1⟩ :=
    step_ro_call (by decide) hcode (LocFrame.refl s) hret
  have hvals1 : vals1 = [sizeVal] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hsize, sizeVal] at hargs1
    exact hargs1.symm
  subst hvals1
  obtain ⟨rfl, rfl, hcal1_a⟩ := one_u256_arg_lookup_g09 hlk_u256_is_zero hl1
  have hz_ex := u256_is_zero_body_exact_g09 (callEntryStateHOLFinite s cal1) z0 z1 z2 z3 hcal1_a
    (.val (.word zw)) hrun1
  have hz_or_nz : z0 ||| z1 ||| z2 ||| z3 ≠ 0#64 :=
    or_ne_zero_of_satWordG09_ne_zero z0 z1 z2 z3 hsz_nz
  rw [if_neg hz_or_nz] at hz_ex
  injection hz_ex with hz1; injection hz1 with hzw0
  have hzw : ¬ (zw ≠ 0#64) := by intro hne; exact hne hzw0
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr1
  have hs1_z : s1.locals.lookup (ofString "z") = some (.val (.word zw)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hcmp_z : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
      (.cmp .notEqual (.var .local (ofString "z")) (.const 0#64)) =
      some (.val (.word (if zw ≠ 0#64 then (1#64 : BitVec 64) else 0#64))) := by
    simp [evalHOLExact, hs1_z, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp_z, if_neg hzw] at hr1; dsimp only at hr1
  rw [if_pos h00, evaluateHOLFiniteState_skip] at hr1; dsimp only at hr1
  have hs1_start : s1.locals.lookup (ofString "start") = some startVal := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hstart, startVal,
      show ofString "z" ≠ ofString "start" by decide]
  have hs1_size : s1.locals.lookup (ofString "size") = some sizeVal := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hsize, sizeVal,
      show ofString "z" ≠ ofString "size" by decide]
  obtain ⟨sw, s2, hs2_c, hs2_lf, hs2_loc, ⟨vals2, body2, cal2, rs2, hargs2, hl2, hrun2⟩, hr2⟩ :=
    step_ro_call (by decide) hs1_c hs1_lf hr1
  have hvals2 : vals2 = [startVal] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs1_start] at hargs2
    exact hargs2.symm
  subst hvals2
  obtain ⟨rfl, rfl, hcal2_v⟩ := one_u256_arg_lookup_g09 hlk_sat_word hl2
  have hs_ex := sat_word_body_exact_g09 (callEntryStateHOLFinite s1 cal2) s0 s1w s2w s3w hcal2_v
    (.val (.word sw)) hrun2
  injection hs_ex with hs1'; injection hs1' with hsw_eq
  have hs2_size : s2.locals.lookup (ofString "size") = some sizeVal := by
    rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_size,
      show ofString "s" ≠ ofString "size" by decide]
  obtain ⟨nw, s3, hs3_c, hs3_lf, hs3_loc, ⟨vals3, body3, cal3, rs3, hargs3, hl3, hrun3⟩, hr3⟩ :=
    step_ro_call (by decide) hs2_c hs2_lf hr2
  have hvals3 : vals3 = [sizeVal] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs2_size] at hargs3
    exact hargs3.symm
  subst hvals3
  obtain ⟨rfl, rfl, hcal3_v⟩ := one_u256_arg_lookup_g09 hlk_sat_word hl3
  have hn_ex := sat_word_body_exact_g09 (callEntryStateHOLFinite s2 cal3) z0 z1 z2 z3 hcal3_v
    (.val (.word nw)) hrun3
  injection hn_ex with hn1'; injection hn1' with hnw_eq
  have hs3_s : s3.locals.lookup (ofString "s") = some (.val (.word sw)) := by
    rw [hs3_loc, hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "n" ≠ ofString "s" by decide]
  have hs3_n : s3.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    rw [hs3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  obtain ⟨endpw, s4, hs4_c, hs4_lf, hs4_loc, ⟨vals4, body4, cal4, rs4, hargs4, hl4, hrun4⟩, hr4⟩ :=
    step_ro_call (by decide) hs3_c hs3_lf hr3
  have hvals4 : vals4 = [.val (.word sw), .val (.word nw)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs3_s, hs3_n] at hargs4
    exact hargs4.symm
  subst hvals4
  obtain ⟨rfl, rfl, w1, w2, hw_inj, hcal4_a, hcal4_b⟩ :=
    two_word_arg_lookup (by decide) lookup_add_sat hl4
  injection hw_inj with hw1 hrest
  injection hw1 with hw1'; injection hw1' with hw1''; subst hw1''
  injection hrest with hw2 _
  injection hw2 with hw2'; injection hw2' with hw2''; subst hw2''
  obtain ⟨endpw', hendp_inj, hendp_nat⟩ :=
    add_sat_body_exact_g09 (callEntryStateHOLFinite s3 cal4) hcal4_a hcal4_b (.val (.word endpw)) hrun4
  injection hendp_inj with h1; injection h1 with h2; subst h2
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr4
  have hs4_endp : s4.locals.lookup (ofString "endp") = some (.val (.word endpw)) := by
    rw [hs4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hcmp_endp : @evalHOLExact 64 F _ s4.toExact (fun x => Classical.propDecidable (s4.memaddrs x))
      (.cmp .equal (.var .local (ofString "endp")) (.const 18446744073709551615#64)) =
      some (.val (.word (if endpw = 18446744073709551615#64 then (1#64 : BitVec 64) else 0#64))) := by
    simp [evalHOLExact, hs4_endp, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp_endp] at hr4; dsimp only at hr4
  by_cases hendp : endpw = 18446744073709551615#64
  · rw [if_pos hendp] at hr4; rw [if_neg h10] at hr4; rw [hret_rstruct s4 18446744073709551615#64 0#64] at hr4
    injection hr4 with h1; injection h1 with hv
    dsimp only [v] at hv
    injection hv with hl
    injection hl with hc _
    injection hc with hc'; injection hc' with hc''
    exact absurd hc''.symm hcw
  · have hsum_lt : sw.toNat + nw.toNat < 2 ^ 64 := by
      by_contra hover
      rw [if_neg hover] at hendp_nat
      apply hendp
      apply BitVec.eq_of_toNat_eq
      simpa using hendp_nat
    rw [if_pos hsum_lt] at hendp_nat
    rw [if_neg hendp] at hr4; rw [if_pos h00] at hr4; rw [evaluateHOLFiniteState_skip] at hr4; dsimp only at hr4
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
        step_ro_call (by decide) hs5_c hs5_lf hr4
      have hvals6 : vals6 = [.val (.word curw)] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs5_cur] at hargs6
        exact hargs6.symm
      subst hvals6
      obtain ⟨rfl, rfl, curw', hcur_inj, hcal6_v⟩ := one_word_arg_lookup lookup_ceil32 hl6
      injection hcur_inj with hcur_inj'; injection hcur_inj' with hcur_inj''; subst hcur_inj''
      obtain ⟨befw', hbef_inj, hbef_lo, hbef_hi⟩ := ceil32_body_exact_g09 (callEntryStateHOLFinite s5 cal6) hs5_c
        hcal6_v (.val (.word befw)) hrun6
      injection hbef_inj with hbef_inj'; injection hbef_inj' with hbef_inj''; subst hbef_inj''
      have hbef_le_ceil : befw.toNat ≤ ceil32NatG09 curw.toNat := by
        by_cases hcur_le : curw.toNat ≤ 2 ^ 64 - 32
        · exact le_of_eq (hbef_lo hcur_le).1
        · have hhi := hbef_hi (by omega)
          have hlt := curw.isLt
          unfold ceil32NatG09
          omega
      have hs6_endp : s6.locals.lookup (ofString "endp") = some (.val (.word endpw)) := by
        rw [hs6_loc]; simp [hs5_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs4_endp,
          show ofString "before" ≠ ofString "endp" by decide,
          show ofString "cur" ≠ ofString "endp" by decide]
      obtain ⟨aftw, s7, hs7_c, hs7_lf, hs7_loc, ⟨vals7, body7, cal7, rs7, hargs7, hl7, hrun7⟩, hr7⟩ :=
        step_ro_call (by decide) hs6_c hs6_lf hr6
      have hvals7 : vals7 = [.val (.word endpw)] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs6_endp] at hargs7
        exact hargs7.symm
      subst hvals7
      obtain ⟨rfl, rfl, endpw', hendp_inj, hcal7_v⟩ := one_word_arg_lookup lookup_ceil32 hl7
      injection hendp_inj with hendp_inj'; injection hendp_inj' with hendp_inj''; subst hendp_inj''
      obtain ⟨aftw', haft_inj, haft_lo, haft_hi⟩ := ceil32_body_exact_g09 (callEntryStateHOLFinite s6 cal7) hs6_c
        hcal7_v (.val (.word aftw)) hrun7
      injection haft_inj with haft_inj'; injection haft_inj' with haft_inj''; subst haft_inj''
      have hendp_le_aft : endpw.toNat ≤ aftw.toNat := by
        by_cases hendp_le : endpw.toNat ≤ 2 ^ 64 - 32
        · exact (haft_lo hendp_le).2.1
        · have hhi := haft_hi (by omega)
          have hlt := endpw.isLt
          omega
      have hs7_bef : s7.locals.lookup (ofString "before") = some (.val (.word befw)) := by
        rw [hs7_loc, hs6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "after" ≠ ofString "before" by decide]
      have hs7_aft : s7.locals.lookup (ofString "after") = some (.val (.word aftw)) := by
        rw [hs7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr7
      have hcmp_ba : @evalHOLExact 64 F _ s7.toExact (fun x => Classical.propDecidable (s7.memaddrs x))
          (.cmp .notLower (.var .local (ofString "before")) (.var .local (ofString "after"))) =
          some (.val (.word (if ¬ (befw < aftw) then (1#64 : BitVec 64) else 0#64))) := by
        simp [evalHOLExact, hs7_bef, hs7_aft, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      rw [hcmp_ba] at hr7; dsimp only at hr7
      by_cases hba : ¬ (befw < aftw)
      · rw [if_pos hba] at hr7; rw [if_neg h10] at hr7; rw [hret_rstruct s7 0#64 0#64] at hr7
        injection hr7 with h1; injection h1 with hv
        have haft_le_bef : aftw.toNat ≤ befw.toNat := by
          rw [BitVec.lt_def] at hba; omega
        rw [← hsw_eq, ← hnw_eq, ← hcur_eq]
        omega
      · rw [if_neg hba] at hr7; rw [if_pos h00] at hr7; rw [evaluateHOLFiniteState_skip] at hr7; dsimp only at hr7
        have hba_lt : befw.toNat < aftw.toNat := BitVec.lt_def.1 (Classical.not_not.1 hba)
        obtain ⟨caw, s8, hs8_c, hs8_lf, hs8_loc, _, hr8⟩ :=
          step_ro_call (by decide) hs7_c hs7_lf hr7
        obtain ⟨cbw, s9, hs9_c, hs9_lf, hs9_loc, _, hr9⟩ :=
          step_ro_call (by decide) hs8_c hs8_lf hr8
        have hs9_ca : s9.locals.lookup (ofString "ca") = some (.val (.word caw)) := by
          rw [hs9_loc, hs8_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "cb" ≠ ofString "ca" by decide]
        have hs9_cb : s9.locals.lookup (ofString "cb") = some (.val (.word cbw)) := by
          rw [hs9_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        have hs9_bef : s9.locals.lookup (ofString "before") = some (.val (.word befw)) := by
          rw [hs9_loc, hs8_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs7_bef,
            show ofString "cb" ≠ ofString "before" by decide,
            show ofString "ca" ≠ ofString "before" by decide]
        have hs9_aft : s9.locals.lookup (ofString "after") = some (.val (.word aftw)) := by
          rw [hs9_loc, hs8_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs7_aft,
            show ofString "cb" ≠ ofString "after" by decide,
            show ofString "ca" ≠ ofString "after" by decide]
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr9
        have hcmp_ca : @evalHOLExact 64 F _ s9.toExact (fun x => Classical.propDecidable (s9.memaddrs x))
            (.cmp .equal (.var .local (ofString "ca")) (.const 18446744073709551615#64)) =
            some (.val (.word (if caw = 18446744073709551615#64 then (1#64 : BitVec 64) else 0#64))) := by
          simp [evalHOLExact, hs9_ca, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        rw [hcmp_ca] at hr9; dsimp only at hr9
        by_cases hca_max : caw = 18446744073709551615#64
        · rw [if_pos hca_max] at hr9; rw [if_neg h10] at hr9; rw [hret_rstruct s9 18446744073709551615#64 0#64] at hr9
          injection hr9 with h1; injection h1 with hv
          dsimp only [v] at hv
          injection hv with hl
          injection hl with hc _
          injection hc with hc'; injection hc' with hc''
          exact absurd hc''.symm hcw
        · rw [if_neg hca_max] at hr9; rw [if_pos h00] at hr9; rw [evaluateHOLFiniteState_skip] at hr9; dsimp only at hr9
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
          dsimp only [v] at hv
          injection hv with hl
          injection hl with _ hrest
          injection hrest with heb _
          injection heb with heb'; injection heb' with heb_eq
          have hsub_nat : ebw.toNat = aftw.toNat - befw.toNat := by
            rw [← heb_eq]
            exact BitVec.toNat_sub_of_le (BitVec.le_def.2 (Nat.le_of_lt hba_lt))
          rw [← hsw_eq, ← hnw_eq, ← hcur_eq]
          omega

theorem eps_extend_memory_cost1_window_bounds_g09 :
    EvmPreservingSpec
      (fun s => ∃ s0 s1 s2 s3 z0 z1 z2 z3 : BitVec 64,
        s.locals.lookup (ofString "start") =
          some (.rStruct [.val (.word s0), .val (.word s1), .val (.word s2), .val (.word s3)]) ∧
        s.locals.lookup (ofString "size") =
          some (.rStruct [.val (.word z0), .val (.word z1), .val (.word z2), .val (.word z3)]))
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
          ((memW s (globN s "ev" + 32) % 32 = 0 ∧ memW s (globN s "ev" + 32) < 2 ^ 37) →
            memW s (globN s "ev" + 32) + ebw.toNat < 2 ^ 37) ∧
          (∀ sv zv : ValueHOL 64,
            s.locals.lookup (ofString "start") = some sv →
            s.locals.lookup (ofString "size") = some zv →
            cw ≠ 18446744073709551615#64 →
            satWordG09 zv ≠ 0#64 →
            (satWordG09 sv).toNat + (satWordG09 zv).toNat ≤
              ceil32NatG09 (memW s (globN s "ev" + 32)) + ebw.toNat))
      (ofString "extend_memory_cost1") := by
  obtain ⟨params, body, retShape, hlk, hspec⟩ := eps_extend_memory_cost1_bounds
  have hlk_eq := lookup_extend_memory_cost1.symm.trans hlk
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_eq, rfl⟩
  subst hbody_eq
  refine ⟨_, _, _, lookup_extend_memory_cost1, ?_⟩
  intro F s hcode hInv hP hlookup hnt
  have hs := hspec s hcode hInv trivial hlookup hnt
  refine ⟨?_, hs.2⟩
  intro v hv
  obtain ⟨hInv', hchain, hR, hlf, cw, ebw, hv_eq, hb⟩ := hs.1 v hv
  refine ⟨hInv', hchain, hR, hlf, cw, ebw, hv_eq, hb, ?_, ?_⟩
  · intro ⟨hal, hlt37⟩
    rcases hb with rfl | ⟨before, after, ha, _, hlt, heb, hbefore⟩
    · simpa using hlt37
    · have := hbefore hal
      omega
  · intro sv zv hsv hzv hcw hsz_nz
    obtain ⟨s0, s1w, s2w, s3w, z0, z1, z2, z3, hstart, hsize⟩ := hP
    have hsv_eq := Option.some.inj (hsv.symm.trans hstart)
    have hzv_eq := Option.some.inj (hzv.symm.trans hsize)
    subst hsv_eq; subst hzv_eq; subst hv_eq
    exact extend_memory_cost1_window_body_g09 s hcode s0 s1w s2w s3w z0 z1 z2 z3 cw ebw
      hstart hsize hv hcw hsz_nz

theorem eps_extend_memory_cost1_aligned_bound_g09 :
    EvmPreservingSpec
      (fun s => memW s (globN s "ev" + 32) % 32 = 0 ∧
        memW s (globN s "ev" + 32) < 2 ^ 37)
      (fun s v post => LocFrame s post ∧
        ∃ cw ebw : BitVec 64,
          v = .rStruct [.val (.word cw), .val (.word ebw)] ∧
          memW s (globN s "ev" + 32) + ebw.toNat < 2 ^ 37)
      (ofString "extend_memory_cost1") := by
  obtain ⟨params, body, retShape, hlk, hspec⟩ := eps_extend_memory_cost1_bounds
  refine ⟨params, body, retShape, hlk, ?_⟩
  intro F s hcode hInv hP hlookup hnt
  have hs := hspec s hcode hInv trivial hlookup hnt
  refine ⟨?_, hs.2⟩
  intro v hv
  obtain ⟨hInv', hchain, hR, hlf, cw, ebw, heq, hb⟩ := hs.1 v hv
  refine ⟨hInv', hchain, hR, hlf, cw, ebw, heq, ?_⟩
  rcases hb with rfl | ⟨before, after, ha, _, hlt, heb, hbefore⟩
  · simpa using hP.2
  · have := hbefore hP.1
    omega

theorem eps_extend_memory_length_g09 :
    EvmPreservingSpec ExtendMemoryPre
      (fun s _ post =>
        (∀ g : String, ofString g ≠ ofString "frame_mem_ptr" → globN post g = globN s g) ∧
        ∀ ebw : BitVec 64,
          s.locals.lookup (ofString "expand_by") = some (.val (.word ebw)) →
          memW post (globN s "ev" + 32) = memW s (globN s "ev" + 32) + ebw.toNat)
      (ofString "extend_memory") := by
  refine ⟨_, _, _, lookup_extend_memory, ?_⟩
  intro F s hcode hInv ⟨ebw, heb_loc, heb_cond⟩ _ hnt
  have herr_triv : ∀ {P1 P2 : Prop},
      (∀ v, (some PanSemResultExact.error : Option (PanSemResultExact 64)) = some (.returned v) → P1) ∧
      (IsEvmErr (some PanSemResultExact.error) → P2) := by
    intro _ _; constructor
    · intro _ h; cases h
    · rintro ⟨_, h⟩; cases h
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by simp [evmChain, evmChainFrom]
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
    have hInv_el : EvmInv s.emptyLocalsHOLFinite := localsFree_evmInv s _ s.clock hInv
    have hc_el := evm_congr (s := s) (t := s.emptyLocalsHOLFinite) rfl rfl
    have hch_el : evmChain s.emptyLocalsHOLFinite = evmChain s := evmChain_congr rfl rfl
    exact ⟨fun _ _ => ⟨hInv_el, hch_el, le_of_eq hc_el.2.1, fun _ _ => rfl, fun ebw' heb' => by
      rw [heb_loc] at heb'
      injection heb' with h1; injection h1 with h2; injection h2 with h3
      subst h3; subst heb0
      rfl⟩,
      by rintro ⟨_, h⟩; cases h⟩
  · rcases heb_cond with rfl | ⟨hnlen_bound, hnlen_al8, hmem_end_fp⟩
    · exact absurd rfl heb0
    have heb_pos : 0 < ebw.toNat := by
      by_contra hz
      apply heb0
      apply BitVec.eq_of_toNat_eq
      have : (0#64 : BitVec 64).toNat = 0 := rfl
      omega
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
        have hlen_le_cap0 : lenw.toNat ≤ capw.toNat := by
          rw [hlenw_eq, hcapw_eq]; exact hFW0.2.2.2.2.2.2.1
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
            ((freshIvl.2 = 0 ∧ memW m (globN s "ev" + 40) = memW s (globN s "ev" + 40)) ∨
              (freshIvl.2 ≠ 0 ∧
                memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = freshIvl.1 ∧
                memW m (globN s "ev" + 40) = memW s (globN s "ev" + 40) + freshIvl.2)) →
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
              EvmInv post ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s ∧
              (∀ g : String, ofString g ≠ ofString "frame_mem_ptr" → globN post g = globN s g) ∧
              ∀ ebw' : BitVec 64,
                s.locals.lookup (ofString "expand_by") = some (.val (.word ebw')) →
                memW post (globN s "ev" + 32) = memW s (globN s "ev" + 32) + ebw'.toNat) ∧
            (IsEvmErr out.1 →
              EvmInv post ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s) := by
          intro m freshIvl hAm hfm_m hm_glob_other heff_m hfresh_m he0_m hnew_m hnlen_le_mcap hm_len hm_nlen hm_eb hnt_t
          dsimp only [tailProg] at hnt_t ⊢
          have hm_ev : m.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
            rw [hm_glob_other "ev" (by decide)]; exact hevw
          have hm_code : m.code = originalRuntimeCode := heff_m.code.trans hcode
          have hm_ma : m.memaddrs = ordinaryDomain := hAm.1.memaddrs
          have hm_dom24 : m.memaddrs (evw + 24#64) := by
            rw [hm_ma, ← hInv.1.1.memaddrs]
            have hev24_eq : evw + 24#64 = BitVec.ofNat 64 (globN s "ev" + 24) := by
              apply BitVec.eq_of_toNat_eq
              have : (24#64 : BitVec 64).toNat = 24 := rfl
              rw [BitVec.toNat_add, hevw_nat, this, BitVec.toNat_ofNat]
            rw [hev24_eq]
            exact ((hFW0.1 (globN s "ev", 280) (by simp)).2.2.2 3 (by omega)).choose_spec.1
          rcases hm_m24 : m.memory (evw + 24#64) with ⟨memPtrW⟩
          have hmemPtrW_nat : memPtrW.toNat = memW s (globN s "ev" + 24) := by
            have hev24_eq : evw + 24#64 = BitVec.ofNat 64 (globN s "ev" + 24) := by
              apply BitVec.eq_of_toNat_eq
              have : (24#64 : BitVec 64).toNat = 24 := rfl
              rw [BitVec.toNat_add, hevw_nat, this, BitVec.toNat_ofNat]
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
            rcases hnew_m with ⟨_, h40_eq⟩ | ⟨hnz, hfr1, h40_eq⟩
            · rw [h40_eq]; dsimp only [Inside] at hmem_in; omega
            · rcases hfresh_m with rfl | ⟨_, _, _, hfin2⟩
              · exact absurd rfl hnz
              · have hm_fp_se : globN m "frame_mem_ptr" ≤ scratchEnd :=
                  le_trans hAm.2.2.2.2.1 hAm.2.2.2.2.2.1
                omega
          have hdst_nat : (memPtrW + lenw).toNat = memW s (globN s "ev" + 24) + lenw.toNat := by
            rw [BitVec.toNat_add, hmemPtrW_nat, Nat.mod_eq_of_lt (by omega)]
          let combinedMem : Ivl := (memW s (globN s "ev" + 24), memW m (globN s "ev" + 40))
          let mzTailCall : ProgHOL 64 := .call (some (none, none)) (ofString "memzero") [mzDstExp, .var .local (ofString "expand_by")]
          rw [evaluateHOLFiniteState_seq_line780] at hnt_t ⊢
          have hnt_mz : (evaluateHOLFiniteState m mzTailCall).1 ≠ some .timeOut := by
            intro hto
            rcases hmz_to : evaluateHOLFiniteState m
                (.call (some (none, none)) (ofString "memzero") [mzDstExp, .var .local (ofString "expand_by")]) with ⟨rmz_to, smz_to⟩
            have hto' : rmz_to = some .timeOut := by
              dsimp only [mzTailCall] at hto; rw [hmz_to] at hto; exact hto
            subst hto'
            have hmz_to_raw : evaluateHOLFiniteState m
                (.call (some (none, none)) (ofString "memzero")
                  [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "len")],
                   .var .local (ofString "expand_by")]) = (some .timeOut, smz_to) := hmz_to
            simp only [hmz_to_raw] at hnt_t
            exact hnt_t rfl
          have hmz := eval_call_memzero_bre m mzDstExp (.var .local (ofString "expand_by"))
            (memPtrW + lenw) ebw [combinedMem] hm_code hm_ma hev_mz_dst hev_mz_n
            (fun _ => ⟨combinedMem, by simp, by rw [hdst_nat]; dsimp only [combinedMem]; omega,
              by rw [hdst_nat]; dsimp only [combinedMem]; omega⟩) hnt_mz
          dsimp only at hmz
          rcases hmz_run : evaluateHOLFiniteState m mzTailCall with ⟨rmz, m1⟩
          rw [hmz_run] at hmz
          have hmz_run_raw : evaluateHOLFiniteState m
              (.call (some (none, none)) (ofString "memzero")
                [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "len")],
                 .var .local (ofString "expand_by")]) = (rmz, m1) := hmz_run
          simp only [hmz_run_raw] at hnt_t ⊢
          cases rmz with
          | some rmz0 =>
            dsimp only at hnt_t ⊢
            have hnr := hmz.2 (by simp)
            refine ⟨fun v hv => absurd (Or.inl ⟨v, hv⟩) hnr, ?_⟩
            rintro ⟨ev, hv⟩
            injection hv with hv'; subst hv'
            exact absurd (Or.inr ⟨ofString "EvmErr", ev, rfl, by decide⟩) hnr
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
                rcases hnew_m with ⟨_, h40_eq⟩ | ⟨hnz, hfr1, h40_eq⟩
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
                rcases hnew_m with ⟨_, h40_eq⟩ | ⟨hnz, hfr1, h40_eq⟩
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
              rcases hnew_m with ⟨_, h40_eq⟩ | ⟨hnz, hfr1, h40_eq⟩
              · dsimp only [combinedMem]; rw [h40_eq]
                have hpw_fo := hInv.2.choose_spec.2.2.2.2.2.2.2.1
                have hch_s : ∃ tl, evmChain s = (globN s "ev", globN s "cur_cont") :: tl := ⟨_, rfl⟩
                obtain ⟨tl_s, hch_s_eq⟩ := hch_s
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
              have hc0_m2 : @evalHOLExact 64 F _ m2.toExact (fun a => Classical.propDecidable (m2.memaddrs a)) (.const (0 : BitVec 64)) =
                  some (.val (.word 0)) := rfl
              have hc0_m2' : @evalHOLExact 64 F _ m2.toExact (fun a => Classical.propDecidable (m2.memaddrs a)) (.const 0#64) =
                  some (.val (.word 0#64)) := rfl
              simp only [hc0_m2, hc0_m2']
              have hsz0 : sizeOfShapeWithContextHOL m2.structs
                  (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
                simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
              have hsz0' : sizeOfShapeWithContextHOL m2.structs
                  (shapeOfHOLExact (.val (.word 0#64))) ≤ 32 := by
                simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
              simp only [hsz0, hsz0', ↓reduceIte]
              let post := { m2.emptyLocalsHOLFinite with
                locals := ((m2.emptyLocalsHOLFinite.locals.resVarEq (ofString "nlen", s2.locals.lookup (ofString "nlen"))).resVarEq
                  (ofString "cap", s1.locals.lookup (ofString "cap"))).resVarEq
                  (ofString "len", s.locals.lookup (ofString "len")) }
              have heff_total : FrameMemByteEff s post
                  [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))] :=
                ((heff_m.trans heff_mz).trans heff_st32_fm).with_locals_clock post.locals m2.clock
              have hm1_glob_m : m1.globals = m.globals := heff_mz_comb.globals
              have hm1_code_m : m1.code = m.code := heff_mz_comb.code
              have hm1_ma_m : m1.memaddrs = m.memaddrs := heff_mz_comb.memaddrs
              have hm1_sh_m : m1.shMemaddrs = m.shMemaddrs := heff_mz_comb.shMemaddrs
              have hm1_ba_m : m1.baseAddr = m.baseAddr := heff_mz_comb.baseAddr
              have hpost_glob_m : post.globals = m.globals := by
                simp [post, emptyLocalsHOLFinite, hm2_eq, hm1_glob_m]
              have hApost : ArenaReady post :=
                ⟨guestInv_congr (s := m) (by simp [post, emptyLocalsHOLFinite, hm2_eq, hm1_code_m])
                  (by simp [post, emptyLocalsHOLFinite, hm2_eq, hm1_ma_m])
                  (by simp [post, emptyLocalsHOLFinite, hm2_eq, hm1_sh_m])
                  (by simp [post, emptyLocalsHOLFinite, hm2_eq, hm1_ba_m]) hAm.1,
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
                  (freshIvl.2 = 0 ∧ memW post (globN s "ev" + 40) = memW s (globN s "ev" + 40)) ∨
                  (freshIvl.2 ≠ 0 ∧
                    memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = freshIvl.1 ∧
                    memW post (globN s "ev" + 40) = memW s (globN s "ev" + 40) + freshIvl.2) := by
                rw [hm2_memW_ne32 40 (by omega) (by omega) (by omega)]
                exact hnew_m
              have hlen_le_cap_post : memW post (globN s "ev" + 32) ≤ memW post (globN s "ev" + 40) := by
                rw [hm2_memW_32, hm2_memW_ne32 40 (by omega) (by omega) (by omega)]
                exact hnlen_le_mcap
              obtain ⟨hInv_p, hch_p, hR_p⟩ := evmInv_of_head_mem_extend hInv hApost hfm_post
                heff_total hfresh_post he0_post hnew_post hlen_le_cap_post
              constructor
              · intro _ _
                refine ⟨hInv_p, hch_p, le_of_eq hR_p, fun g hg => ?_, fun ebw' heb' => ?_⟩
                · unfold globN; rw [hpost_glob_m, hm_glob_other g hg]
                · rw [heb_loc] at heb'
                  injection heb' with h1; injection h1 with h2; injection h2 with h3
                  subst h3
                  rw [hm2_memW_32, hnlenw_nat, hlenw_eq]
              · rintro ⟨_, h⟩; cases h
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
              have h1024_n : (1024#64 : BitVec 64).toNat = 1024 := rfl
              have hnl1024_nat : (nlenw + 1024#64).toNat = nlenw.toNat + 1024 := by
                rw [BitVec.toNat_add, h1024_n, Nat.mod_eq_of_lt (by omega)]
              refine ⟨s5, nlenw + 1024#64, rfl, by cases s; rfl, ?_, ?_, ?_, ?_, ?_, by omega, by omega, by omega, by omega⟩
              · simp [s5, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              · simp [s5, hs4, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_cap,
                  show ofString "ncap" ≠ ofString "cap" by decide]
              · simp [s5, hs4, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_len,
                  show ofString "ncap" ≠ ofString "len" by decide]
              · simp [s5, hs4, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_nlen,
                  show ofString "ncap" ≠ ofString "nlen" by decide]
              · simp [s5, hs4, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_eb,
                  show ofString "ncap" ≠ ofString "expand_by" by decide]
            · simp only [hlt_nl, ↓reduceIte, evaluateHOLFiniteState_skip]
              have hge_nl : nlenw.toNat ≤ (capw * 2#64).toNat := by
                rw [BitVec.lt_def] at hlt_nl; omega
              refine ⟨s4, capw * 2#64, rfl, by cases s; rfl, hs4_ncap, ?_, ?_, hs4_nlen, ?_, hge_nl, by omega, by omega, by omega⟩
              · simp [hs4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_cap,
                  show ofString "ncap" ≠ ofString "cap" by decide]
              · simp [hs4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_len,
                  show ofString "ncap" ≠ ofString "len" by decide]
              · simp [hs4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_eb,
                  show ofString "ncap" ≠ ofString "expand_by" by decide]
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
            have hfma_run_raw : evaluateHOLFiniteState
                (callEntryStateHOLFinite s5 (HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word diffw))))
                (sourceFnBody Guest.Software.guestFn_frame_mem_alloc) = (rfma, fmaPost) := hfma_run
            simp only [hfma_run_raw] at hnt ⊢
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
                  · rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact (heid h1).elim
              | «break» => exact herr_triv
              | «continue» => exact herr_triv
              | finalFfi _ =>
                constructor
                · intro _ h; cases h
                · rintro ⟨_, h⟩; cases h
              | error => exact herr_triv
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
                have hqw_nat : qw.toNat = fp_w.toNat + diffw.toNat := by
                  have hdiff_al8' : diffw.toNat % 8 = 0 := by
                    have hcapw_al8 : capw.toNat % 8 = 0 := by rw [hcapw_eq]; exact hmem40_8
                    omega
                  have halign_eq : (diffw.toNat + 7) / 8 * 8 = diffw.toNat := by omega
                  change qw.toNat = _ at hq_nat
                  omega
                have hqw_al8 : qw.toNat % 8 = 0 := hq_al8
                have hqw_le_sp : qw.toNat ≤ sp_g_w.toNat := hq_le_sp
                have hdiff_al8 : diffw.toNat % 8 = 0 := by
                  have hcapw_al8 : capw.toNat % 8 = 0 := by rw [hcapw_eq]; exact hmem40_8
                  omega
                have hdiff_pos : 0 < diffw.toNat := by omega
                set s6 : PanSemStateFiniteExact 64 F := { fmaPost with locals := s5.locals } with hs6_def
                have hs6_glob : s6.globals = s.globals.update (ofString "frame_mem_ptr", .val (.word qw)) := by
                  change fmaPost.globals = _
                  rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq]
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
                have hs6_dom24 : s6.memaddrs (evw + 24#64) := by
                  rw [hs6_ma, ← hInv.1.1.memaddrs]
                  have hev24_eq : evw + 24#64 = BitVec.ofNat 64 (globN s "ev" + 24) := by
                    apply BitVec.eq_of_toNat_eq
                    have : (24#64 : BitVec 64).toNat = 24 := rfl
                    rw [BitVec.toNat_add, hevw_nat, this, BitVec.toNat_ofNat]
                  rw [hev24_eq]
                  exact ((hFW0.1 (globN s "ev", 280) (by simp)).2.2.2 3 (by omega)).choose_spec.1
                rcases hs_m24 : s.memory (evw + 24#64) with ⟨memPtrW⟩
                have hs6_m24 : s6.memory (evw + 24#64) = .word memPtrW := by rw [hs6_mem, hs_m24]
                have hmemPtrW_nat : memPtrW.toNat = memW s (globN s "ev" + 24) := by
                  have hev24_eq : evw + 24#64 = BitVec.ofNat 64 (globN s "ev" + 24) := by
                    apply BitVec.eq_of_toNat_eq
                    have : (24#64 : BitVec 64).toNat = 24 := rfl
                    rw [BitVec.toNat_add, hevw_nat, this, BitVec.toNat_ofNat]
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
                let mzGrowCall : ProgHOL 64 := .call (some (none, none)) (ofString "memzero") [mzGrowDst, mzGrowN]
                rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
                have hnt_mzg : (evaluateHOLFiniteState s6 mzGrowCall).1 ≠ some .timeOut := by
                  intro hto
                  rcases hmzg_to : evaluateHOLFiniteState s6
                      (.call (some (none, none)) (ofString "memzero") [mzGrowDst, mzGrowN]) with ⟨rmzg_to, smzg_to⟩
                  have hto' : rmzg_to = some .timeOut := by
                    dsimp only [mzGrowCall] at hto; rw [hmzg_to] at hto; exact hto
                  subst hto'
                  have hmzg_to_raw : evaluateHOLFiniteState s6
                      (.call (some (none, none)) (ofString "memzero")
                        [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "cap")],
                         .op .sub [.var .local (ofString "ncap"), .var .local (ofString "cap")]]) = (some .timeOut, smzg_to) := hmzg_to
                  simp only [hmzg_to_raw] at hnt
                  exact hnt rfl
                have hmzg := eval_call_memzero_bre s6 mzGrowDst mzGrowN
                  (memPtrW + capw) diffw [freshIvl] hs6_code hs6_ma hev_mzg_dst hev_mzg_n
                  (fun _ => ⟨freshIvl, by simp, by rw [hmzg_dst_nat]; dsimp only [freshIvl]; omega⟩) hnt_mzg
                dsimp only at hmzg
                rcases hmzg_run : evaluateHOLFiniteState s6 mzGrowCall with ⟨rmzg, s7⟩
                rw [hmzg_run] at hmzg
                have hmzg_run_raw : evaluateHOLFiniteState s6
                    (.call (some (none, none)) (ofString "memzero")
                      [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "cap")],
                       .op .sub [.var .local (ofString "ncap"), .var .local (ofString "cap")]]) = (rmzg, s7) := hmzg_run
                simp only [hmzg_run_raw] at hnt ⊢
                cases rmzg with
                | some rmzg0 =>
                  dsimp only at hnt ⊢
                  have hnr := hmzg.2 (by simp)
                  refine ⟨fun v hv => absurd (Or.inl ⟨v, hv⟩) hnr, ?_⟩
                  rintro ⟨ev, hv⟩
                  injection hv with hv'; subst hv'
                  exact absurd (Or.inr ⟨ofString "EvmErr", ev, rfl, by decide⟩) hnr
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
                    change (let out := evaluateHOLFiniteState m tailProg
                      let post := { out.2 with
                        locals := ((out.2.locals.resVarEq (ofString "nlen", s2.locals.lookup (ofString "nlen"))).resVarEq
                          (ofString "cap", s1.locals.lookup (ofString "cap"))).resVarEq
                          (ofString "len", s.locals.lookup (ofString "len")) }
                      (∀ v, out.1 = some (.returned v) →
                        EvmInv post ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s ∧
                        (∀ g : String, ofString g ≠ ofString "frame_mem_ptr" → globN post g = globN s g) ∧
                        ∀ ebw' : BitVec 64,
                          s.locals.lookup (ofString "expand_by") = some (.val (.word ebw')) →
                          memW post (globN s "ev" + 32) = memW s (globN s "ev" + 32) + ebw'.toNat) ∧
                      (IsEvmErr out.1 →
                        EvmInv post ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s))
                    have hm_glob : m.globals = s.globals.update (ofString "frame_mem_ptr", .val (.word qw)) := by
                      dsimp only [m]; rw [hs8_eq]; dsimp only; rw [heff_mzg.globals, hs6_glob]
                    have hm_fp_glob : globN m "frame_mem_ptr" = qw.toNat := by
                      unfold globN; rw [hm_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
                    have hm_other_glob : ∀ g : String, ofString g ≠ ofString "frame_mem_ptr" →
                        m.globals.lookup (ofString g) = s.globals.lookup (ofString g) := by
                      intro g hg; rw [hm_glob]
                      simp [HolFiniteMapExact.lookup_update, FUPDATE, hg, Ne.symm hg]
                    have hm_G : GuestInv m := by
                      have hcode_m : m.code = s.code := by
                        dsimp only [m]; rw [hs8_eq]; dsimp only; rw [heff_mzg.code, hs6_code, hcode]
                      have hma_m : m.memaddrs = s.memaddrs := by
                        dsimp only [m]; rw [hs8_eq]; dsimp only; rw [heff_mzg.memaddrs, hs6_ma, hInv.1.1.memaddrs]
                      have hsh_m : m.shMemaddrs = s.shMemaddrs := by
                        dsimp only [m]; rw [hs8_eq]; dsimp only; rw [heff_mzg.shMemaddrs]
                        change fmaPost.shMemaddrs = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq]
                      have hba_m : m.baseAddr = s.baseAddr := by
                        dsimp only [m]; rw [hs8_eq]; dsimp only; rw [heff_mzg.baseAddr]
                        change fmaPost.baseAddr = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq]
                      exact guestInv_congr hcode_m hma_m hsh_m hba_m hInv.1.1
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
                        (freshIvl.2 = 0 ∧ memW m (globN s "ev" + 40) = memW s (globN s "ev" + 40)) ∨
                        (freshIvl.2 ≠ 0 ∧
                          memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = freshIvl.1 ∧
                          memW m (globN s "ev" + 40) = memW s (globN s "ev" + 40) + freshIvl.2) := by
                      refine Or.inr ⟨by dsimp only [freshIvl]; omega, hmem_end_fp, ?_⟩
                      rw [hm_e0_40]; dsimp only [freshIvl]; omega
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
                      dsimp only [m]
                      exact hnt
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
            (Or.inl ⟨rfl, rfl⟩)
            (by change nlenw.toNat ≤ memW s (globN s "ev" + 40); rw [← hcapw_eq]; exact hnlen_le_cap)
            hs3_len hs3_nlen hs3_eb hnt

private theorem eval_mul64x64_lt_twoPow32_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) {ww : BitVec 64}
    (hw_lt : ww.toNat < 2 ^ 32)
    (ha : s.locals.lookup (ofString "a") = some (.val (.word ww)))
    (hb : s.locals.lookup (ofString "b") = some (.val (.word ww)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_mul64x64)).1 =
      some (.returned v)) :
    ∃ lo : BitVec 64, v = .rStruct [.val (.word lo), .val (.word 0#64)] ∧
      lo.toNat = ww.toNat * ww.toNat := by
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
  have ha0_eq : a0 = ww := by
    apply BitVec.eq_of_toNat_eq
    dsimp only [a0]
    rw [BitVec.toNat_and, show (4294967295#64 : BitVec 64).toNat = 2 ^ 32 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hw_lt]
  have ha1_eq : a1 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    dsimp only [a1]
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    change ww.toNat / 2 ^ 32 = 0
    omega
  have hp11_eq : p11 = 0#64 := by simp [p11, ha1_eq]
  have hp01_eq : p01 = 0#64 := by simp [p01, ha1_eq]
  have hmid_eq : mid = (0#64, 0#64) := by
    dsimp only [mid]; rw [hp01_eq]; decide
  have hlo_eq : lo = (p00, 0#64) := by
    dsimp only [lo]
    rw [hmid_eq]
    have hsh0 : (0#64 : BitVec 64) <<< (32 : Nat) = 0#64 := by decide
    rw [hsh0]
    unfold wordAddCarryHOL
    have hp00_lt := p00.isLt
    have h0_nat : (0#64 : BitVec 64).toNat = 0 := rfl
    have hc0 : (0#64 : BitVec 64) == 0 := by decide
    simp only [hc0, ↓reduceIte, h0_nat, Nat.add_zero]
    rw [if_neg (by omega)]
    ext1
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp00_lt]
    · rfl
  have hhi_eq : hi = 0#64 := by
    dsimp only [hi]
    rw [hp11_eq, hmid_eq, hlo_eq]
    dsimp only
    decide
  have hp00_nat : p00.toNat = ww.toNat * ww.toNat := by
    dsimp only [p00]
    rw [ha0_eq, BitVec.toNat_mul]
    have hmul : ww.toNat * ww.toNat < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' hw_lt hw_lt
    have hpow : (2 ^ 32 : Nat) * 2 ^ 32 = 2 ^ 64 := by decide
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨lo.1, ?_, ?_⟩
  · rw [← hv, hhi_eq]
  · rw [hlo_eq]; exact hp00_nat

private theorem words_of_exact_lt37_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) {nw : BitVec 64}
    (hn_bound : nw.toNat ≤ 2 ^ 37 - 32 ∨ (nw.toNat < 2 ^ 37 ∧ nw.toNat % 32 = 0))
    (hcode : s.code = originalRuntimeCode)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_words_of)).1 =
      some (.returned v)) :
    ∃ ww : BitVec 64, v = .val (.word ww) ∧
      ww.toNat = (nw.toNat + 31) / 32 ∧ ww.toNat < 2 ^ 32 := by
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
          obtain ⟨cw, rfl, hlo, _⟩ := ceil32_body_exact_g09 (callEntryStateHOLFinite s cal) hcode hv_lk vb
            (by rw [hrun])
          have hcw_eq : cw.toNat = ((nw.toNat + 31) / 32) * 32 := by
            have h := (hlo (by omega)).1
            unfold ceil32NatG09 at h
            exact h
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
            have hsh_nat : (cw >>> (5 : Nat)).toNat = (nw.toNat + 31) / 32 := by
              rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hcw_eq]
              change ((nw.toNat + 31) / 32) * 32 / 32 = (nw.toNat + 31) / 32
              omega
            refine ⟨cw >>> (5 : Nat), hv.symm, hsh_nat, ?_⟩
            rw [hsh_nat]
            have : (2 ^ 37 : Nat) = 2 ^ 32 * 32 := by decide
            omega
          · simp at hret
        · simp at hret
      | _ => simp at hret

private theorem memory_gas_cost_exact_lt37_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) {szw : BitVec 64}
    (hsz_bound : szw.toNat ≤ 2 ^ 37 - 32 ∨ (szw.toNat < 2 ^ 37 ∧ szw.toNat % 32 = 0))
    (hcode : s.code = originalRuntimeCode)
    (hsz_lk : s.locals.lookup (ofString "size") = some (.val (.word szw)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memory_gas_cost)).1 =
      some (.returned v)) :
    ∃ cw : BitVec 64, v = .val (.word cw) ∧
      cw.toNat = 3 * ((szw.toNat + 31) / 32) + (((szw.toNat + 31) / 32) * ((szw.toNat + 31) / 32)) / 512 ∧
      cw.toNat < 2 ^ 63 := by
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
          obtain ⟨ww, rfl, hww_eq, hww_lt⟩ :=
            words_of_exact_lt37_g09 (callEntryStateHOLFinite s cal1) hsz_bound hcode hn1 vb1 (by rw [hrun1])
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
                  obtain ⟨low, rfl, hlow_nat⟩ :=
                    eval_mul64x64_lt_twoPow32_g09 (callEntryStateHOLFinite s1 cal2) hww_lt ha2 hb2 vb2 (by rw [hrun2])
                  set s2 := setVarHOLFinite (ofString "sq")
                    (.rStruct [.val (.word low), .val (.word 0#64)]) { pb2 with locals := s1.locals }
                  have hs2_sq : s2.locals.lookup (ofString "sq") =
                      some (.rStruct [.val (.word low), .val (.word 0#64)]) := by
                    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  have hs2_w : s2.locals.lookup (ofString "w") = some (.val (.word ww)) := by
                    have hne : ofString "sq" ≠ ofString "w" := by decide
                    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hs1_w]
                  have hs2_code : s2.code = originalRuntimeCode := hpb2_code
                  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
                  have hcmp : @evalHOLExact 64 F _ s2.toExact (fun x => Classical.propDecidable (s2.memaddrs x))
                      (.cmp .notEqual (.rfield 1 (.var .local (ofString "sq"))) (.const 0#64)) =
                      some (.val (.word 0#64)) := by
                    simp [evalHOLExact, hs2_sq, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
                  rw [hcmp] at hret; dsimp only at hret
                  have h00 : (0#64 : BitVec 64) = 0 := rfl
                  rw [if_pos h00, evaluateHOLFiniteState_skip] at hret; dsimp only at hret
                  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
                  have h9 : (9#64 : BitVec 64).toNat = 9 := rfl
                  have hshf9 : wordShiftHOL .lsr low 9 = some (low >>> (9 : Nat)) := by simp [wordShiftHOL]
                  have hargs3 : evalListHOLFinite s2 (h := fun x => Classical.propDecidable (s2.memaddrs x))
                      [.panop .mul [.var .local (ofString "w"), .const 3#64],
                       .shift .lsr (.rfield 0 (.var .local (ofString "sq"))) (.const 9#64)] =
                      some [.val (.word (ww * 3#64)), .val (.word (low >>> (9 : Nat)))] := by
                    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs2_w, hs2_sq,
                      valueIsWord, valueWord, panOpHOL, h9, hshf9]
                  rw [hargs3] at hret; dsimp only at hret
                  have hlk3 := pan_two_word_lookup s2.code.lookup
                    (ofString "add_sat") (ofString "a") (ofString "b")
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
                          obtain ⟨aw, rfl, haw_nat⟩ :=
                            add_sat_body_exact_g09 (callEntryStateHOLFinite s2 cal3) ha3 hb3 vb3 (by rw [hrun3])
                          set s3 := setVarHOLFinite (ofString "a") (.val (.word aw)) { pb3 with locals := s2.locals }
                          rw [evaluateHOLFiniteState_return] at hret
                          have hs3_a : @evalHOLExact 64 F _ s3.toExact (fun x => Classical.propDecidable (s3.memaddrs x))
                              (.var .local (ofString "a")) = some (.val (.word aw)) := by
                            simp [evalHOLExact, s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                          rw [hs3_a] at hret; dsimp only at hret
                          split at hret
                          · injection hret with h1; injection h1 with hv
                            have hw3_nat : (ww * 3#64).toNat = 3 * ww.toNat := by
                              rw [BitVec.toNat_mul]
                              have h3 : (3#64 : BitVec 64).toNat = 3 := rfl
                              rw [h3, Nat.mod_eq_of_lt (by omega)]
                              omega
                            have hlsr9_nat : (low >>> (9 : Nat)).toNat = (ww.toNat * ww.toNat) / 512 := by
                              rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hlow_nat]
                            have hsq_lt : ww.toNat * ww.toNat < 2 ^ 64 := by
                              have hmul : ww.toNat * ww.toNat < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' hww_lt hww_lt
                              have : (2 ^ 32 : Nat) * 2 ^ 32 = 2 ^ 64 := by decide
                              omega
                            have hsum_lt63 : 3 * ww.toNat + (ww.toNat * ww.toNat) / 512 < 2 ^ 63 := by omega
                            have hsum_lt64 : (ww * 3#64).toNat + (low >>> (9 : Nat)).toNat < 2 ^ 64 := by
                              rw [hw3_nat, hlsr9_nat]; omega
                            rw [if_pos hsum_lt64, hw3_nat, hlsr9_nat] at haw_nat
                            refine ⟨aw, hv.symm, ?_, ?_⟩
                            · rw [haw_nat, hww_eq]
                            · rw [haw_nat]; exact hsum_lt63
                          · simp at hret
                        · simp at hret
                      | _ => simp at hret
                · simp at hret
              | _ => simp at hret
        · simp at hret
      | _ => simp at hret

theorem memory_gas_cost_lt_twoPow63_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) {szw : BitVec 64}
    (hsz_bound : szw.toNat ≤ 2 ^ 37 - 32 ∨ (szw.toNat < 2 ^ 37 ∧ szw.toNat % 32 = 0))
    (hcode : s.code = originalRuntimeCode)
    (hsz_lk : s.locals.lookup (ofString "size") = some (.val (.word szw)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memory_gas_cost)).1 =
      some (.returned v)) :
    ∃ cw : BitVec 64, v = .val (.word cw) ∧ cw.toNat < 2 ^ 63 := by
  obtain ⟨cw, hv, _, hlt⟩ := memory_gas_cost_exact_lt37_g09 s hsz_bound hcode hsz_lk v hret
  exact ⟨cw, hv, hlt⟩

theorem memory_gas_cost_mono_lt37_g09 {F : Type}
    (s1 s2 : PanSemStateFiniteExact 64 F) {sz1 sz2 c1 c2 : BitVec 64}
    (h12 : sz1.toNat ≤ sz2.toNat)
    (h2_bound : sz2.toNat ≤ 2 ^ 37 - 32 ∨ (sz2.toNat < 2 ^ 37 ∧ sz2.toNat % 32 = 0))
    (hc1 : s1.code = originalRuntimeCode)
    (hc2 : s2.code = originalRuntimeCode)
    (hlk1 : s1.locals.lookup (ofString "size") = some (.val (.word sz1)))
    (hlk2 : s2.locals.lookup (ofString "size") = some (.val (.word sz2)))
    (hret1 : (evaluateHOLFiniteState s1 (sourceFnBody Guest.Software.guestFn_memory_gas_cost)).1 =
      some (.returned (.val (.word c1))))
    (hret2 : (evaluateHOLFiniteState s2 (sourceFnBody Guest.Software.guestFn_memory_gas_cost)).1 =
      some (.returned (.val (.word c2)))) :
    c1.toNat ≤ c2.toNat ∧ c2.toNat < 2 ^ 63 := by
  have h2_le : sz2.toNat ≤ 2 ^ 37 - 32 := by omega
  obtain ⟨cw1, hv1, heq1, _⟩ :=
    memory_gas_cost_exact_lt37_g09 s1 (Or.inl (Nat.le_trans h12 h2_le)) hc1 hlk1 (.val (.word c1)) hret1
  obtain ⟨cw2, hv2, heq2, hlt2⟩ :=
    memory_gas_cost_exact_lt37_g09 s2 (Or.inl h2_le) hc2 hlk2 (.val (.word c2)) hret2
  injection hv1 with h1'; injection h1' with hc1_eq; subst hc1_eq
  injection hv2 with h2'; injection h2' with hc2_eq; subst hc2_eq
  have hw_le : (sz1.toNat + 31) / 32 ≤ (sz2.toNat + 31) / 32 := by omega
  have hsq_le : ((sz1.toNat + 31) / 32) * ((sz1.toNat + 31) / 32) ≤
      ((sz2.toNat + 31) / 32) * ((sz2.toNat + 31) / 32) := Nat.mul_le_mul hw_le hw_le
  have hdiv_le : (((sz1.toNat + 31) / 32) * ((sz1.toNat + 31) / 32)) / 512 ≤
      (((sz2.toNat + 31) / 32) * ((sz2.toNat + 31) / 32)) / 512 := Nat.div_le_div_right hsq_le
  refine ⟨?_, hlt2⟩
  rw [heq1, heq2]
  omega

private def cost2NoRaiseCalleesG09 (f : MlS) : Bool :=
  f == ofString "u256_is_zero" ||
  f == ofString "sat_word" ||
  f == ofString "add_sat" ||
  f == ofString "ceil32" ||
  f == ofString "words_of" ||
  f == ofString "mul64x64" ||
  f == ofString "memory_gas_cost" ||
  f == ofString "extend_memory_cost1"

private theorem cost2NoRaiseCalleesG09_good :
    ∀ function, cost2NoRaiseCalleesG09 function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) →
      noRaiseProg cost2NoRaiseCalleesG09 body = true := by
  intro function hfn values body callee rs hfound
  obtain ⟨params, rs', hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
  simp only [cost2NoRaiseCalleesG09, Bool.or_eq_true, beq_iff_eq] at hfn
  rcases hfn with ((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl
  · have hlk : originalRuntimeCode.lookup (ofString "u256_is_zero") =
        some ([(ofString "a", .comb [.one, .one, .one, .one])],
          sourceFnBody Guest.Software.guestFn_u256_is_zero, .one) :=
      lookup_of_guestAst_getElem 42 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_u256_is_zero) rfl
    rw [hlk] at hinst
    have heq := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
    rw [← heq]; decide
  · have hlk : originalRuntimeCode.lookup (ofString "sat_word") =
        some ([(ofString "v", .comb [.one, .one, .one, .one])],
          sourceFnBody Guest.Software.guestFn_sat_word, .one) :=
      lookup_of_guestAst_getElem 440 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_sat_word) rfl
    rw [hlk] at hinst
    have heq := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
    rw [← heq]; decide
  · rw [lookup_add_sat] at hinst
    have heq := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
    rw [← heq]; decide
  · rw [lookup_ceil32] at hinst
    have heq := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
    rw [← heq]; decide
  · rw [lookup_words_of] at hinst
    have heq := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
    rw [← heq]; decide
  · rw [lookup_mul64x64] at hinst
    have heq := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
    rw [← heq]; decide
  · rw [lookup_memory_gas_cost] at hinst
    have heq := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
    rw [← heq]; decide
  · rw [lookup_extend_memory_cost1] at hinst
    have heq := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
    rw [← heq]; decide

private theorem eval_mul64x64_hi_nonzero_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) {ww : BitVec 64}
    (hw_ge : 2 ^ 32 ≤ ww.toNat) (hw_lt : ww.toNat < 2 ^ 59)
    (ha : s.locals.lookup (ofString "a") = some (.val (.word ww)))
    (hb : s.locals.lookup (ofString "b") = some (.val (.word ww)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_mul64x64)).1 =
      some (.returned v)) :
    ∃ lo hi : BitVec 64, v = .rStruct [.val (.word lo), .val (.word hi)] ∧ hi ≠ 0#64 := by
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
  refine ⟨lo.1, hi, hv.symm, ?_⟩
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

private theorem words_of_ge_of_ge_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) {nw : BitVec 64}
    (hn_ge : 2 ^ 37 ≤ nw.toNat)
    (hcode : s.code = originalRuntimeCode)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_words_of)).1 =
      some (.returned v)) :
    ∃ ww : BitVec 64, v = .val (.word ww) ∧ 2 ^ 32 ≤ ww.toNat ∧ ww.toNat < 2 ^ 59 := by
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
          obtain ⟨cw, rfl, hlo, hhi⟩ := ceil32_body_exact_g09 (callEntryStateHOLFinite s cal) hcode hv_lk vb
            (by rw [hrun])
          have hcw_ge : 2 ^ 37 ≤ cw.toNat := by
            by_cases hle : nw.toNat ≤ 2 ^ 64 - 32
            · have h1 := (hlo hle).1; unfold ceil32NatG09 at h1; omega
            · have := hhi (by omega); omega
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
            · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
              have : (2 ^ 37 : Nat) = 2 ^ 32 * 2 ^ 5 := by decide
              omega
            · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
              have := cw.isLt
              have : (2 ^ 64 : Nat) = 2 ^ 59 * 2 ^ 5 := by decide
              omega
          · simp at hret
        · simp at hret
      | _ => simp at hret

private theorem memory_gas_cost_ge_twoPow37_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) {szw : BitVec 64}
    (hsz_ge : 2 ^ 37 ≤ szw.toNat)
    (hcode : s.code = originalRuntimeCode)
    (hsz_lk : s.locals.lookup (ofString "size") = some (.val (.word szw)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memory_gas_cost)).1 =
      some (.returned v)) :
    v = .val (.word 18446744073709551615#64) := by
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
          obtain ⟨ww, rfl, hww_ge, hww_lt⟩ :=
            words_of_ge_of_ge_g09 (callEntryStateHOLFinite s cal1) hsz_ge hcode hn1 vb1 (by rw [hrun1])
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
                  obtain ⟨low, hiw, rfl, hhi_ne0⟩ :=
                    eval_mul64x64_hi_nonzero_g09 (callEntryStateHOLFinite s1 cal2) hww_ge hww_lt ha2 hb2 vb2 (by rw [hrun2])
                  set s2 := setVarHOLFinite (ofString "sq")
                    (.rStruct [.val (.word low), .val (.word hiw)]) { pb2 with locals := s1.locals }
                  have hs2_sq : s2.locals.lookup (ofString "sq") =
                      some (.rStruct [.val (.word low), .val (.word hiw)]) := by
                    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
                  have h10 : ¬ ((1#64 : BitVec 64) = 0) := by decide
                  have hcmp : @evalHOLExact 64 F _ s2.toExact (fun x => Classical.propDecidable (s2.memaddrs x))
                      (.cmp .notEqual (.rfield 1 (.var .local (ofString "sq"))) (.const 0#64)) =
                      some (.val (.word 1#64)) := by
                    simp [evalHOLExact, hs2_sq, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hhi_ne0]
                  rw [hcmp] at hret; dsimp only at hret
                  rw [if_neg h10] at hret
                  rw [evaluateHOLFiniteState_return] at hret; dsimp only [evalHOLExact] at hret
                  have hsz : sizeOfShapeWithContextHOL s2.structs
                      (shapeOfHOLExact (.val (.word 18446744073709551615#64))) ≤ 32 := by
                    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
                  rw [if_pos hsz] at hret; dsimp only at hret
                  injection hret with h1; injection h1 with hv; exact hv.symm
                · simp at hret
              | _ => simp at hret
        · simp at hret
      | _ => simp at hret

private theorem extend_memory_cost1_body_full_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_extend_memory_cost1)).1 =
      some (.returned v)) :
    ∃ cw ebw : BitVec 64,
      v = .rStruct [.val (.word cw), .val (.word ebw)] ∧
      (cw ≠ 18446744073709551615#64 → cw.toNat < 2 ^ 63) ∧
      (ebw = 0#64 ∨
        ∃ before after : Nat,
          after < 2 ^ 37 ∧
          after % 32 = 0 ∧
          before % 32 = 0 ∧
          before = ceil32NatG09 (memW s (globN s "ev" + 32)) ∧
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
  have step_ro_call : ∀ {st : PanSemStateFiniteExact 64 F} {nm fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64},
      opRoCallees fname = true →
      st.code = originalRuntimeCode →
      LocFrame s st →
      (evaluateHOLFiniteState st (.decCall nm .one fname args cont)).1 = some (.returned v) →
      ∃ (w : BitVec 64) (st' : PanSemStateFiniteExact 64 F),
        st'.code = originalRuntimeCode ∧
        LocFrame s st' ∧
        st'.locals = st.locals.update (nm, .val (.word w)) ∧
        (∃ vals body callee rs,
          evalListHOLFinite st (h := fun x => Classical.propDecidable (st.memaddrs x)) args = some vals ∧
          lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, callee, rs) ∧
          (evaluateHOLFiniteState (callEntryStateHOLFinite st callee) body).1 = some (.returned (.val (.word w)))) ∧
        (evaluateHOLFiniteState st' cont).1 = some (.returned v) := by
    intro st nm fname args cont hfn hst_c hst_lf hr
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
            rwa [← hst_c]
          have hbody_ro := opRoCallees_good fname hfn vals body callee rs hl_orig
          have hsafe := evaluate_readOnlyProg opRoCallees opRoCallees_good body hbody_ro
            (callEntryStateHOLFinite st callee) hst_c
          rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite st callee) body with ⟨rb, pb⟩
          rw [hrun] at hr
          have hpb_c : pb.code = originalRuntimeCode := by
            have hm := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite st callee) body).1
            rw [hrun] at hm; exact hm.trans hst_c
          rcases rb with _ | rb
          · simp at hr
          · cases rb with
            | returned vb =>
              dsimp only at hr
              split at hr
              · rename_i hsh_vb
                dsimp only at hr
                have hsh_one : shapeEqHOL (shapeOfHOLExact vb) .one = true := by
                  simp [Bool.and_eq_true] at hsh_vb; exact hsh_vb.1
                rcases vb with ⟨⟨w⟩⟩ | _ | _
                · have hlf_ce : LocFrame (callEntryStateHOLFinite st callee) pb := by
                    have hres := hsafe.to_resumes (by rw [hrun]; exact Or.inl ⟨.val (.word w), rfl⟩)
                    simpa [hrun] using hres
                  have hlf_st : LocFrame st pb := by
                    unfold LocFrame at hlf_ce ⊢; rw [hlf_ce]; rfl
                  let st' := setVarHOLFinite nm (.val (.word w)) { pb with locals := st.locals }
                  have hlf_st' : LocFrame s st' :=
                    hst_lf.trans (hlf_st.with_locals_clock (st.locals.update (nm, .val (.word w))) pb.clock)
                  exact ⟨w, st', hpb_c, hlf_st', rfl,
                    ⟨vals, body, callee, rs, rfl, hl_orig, by rw [hrun]⟩, hr⟩
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh_one
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh_one
              · simp at hr
            | _ => simp at hr
  have h10 : ¬ ((1#64 : BitVec 64) = 0) := by decide
  have h00 : (0#64 : BitVec 64) = 0 := rfl
  rw [hbody] at hret
  obtain ⟨zw, s1, hs1_c, hs1_lf, hs1_loc, _, hr1⟩ :=
    step_ro_call (by decide) hcode (LocFrame.refl s) hret
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr1
  have hs1_z : s1.locals.lookup (ofString "z") = some (.val (.word zw)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hcmp_z : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
      (.cmp .notEqual (.var .local (ofString "z")) (.const 0#64)) =
      some (.val (.word (if zw ≠ 0#64 then (1#64 : BitVec 64) else 0#64))) := by
    simp [evalHOLExact, hs1_z, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp_z] at hr1; dsimp only at hr1
  by_cases hzw : zw ≠ 0#64
  · rw [if_pos hzw] at hr1; rw [if_neg h10] at hr1; rw [hret_rstruct s1 0#64 0#64] at hr1
    injection hr1 with h1; injection h1 with hv
    exact ⟨0#64, 0#64, hv.symm, fun _ => by decide, Or.inl rfl⟩
  · rw [if_neg hzw] at hr1; rw [if_pos h00] at hr1; rw [evaluateHOLFiniteState_skip] at hr1; dsimp only at hr1
    obtain ⟨sw, s2, hs2_c, hs2_lf, hs2_loc, _, hr2⟩ :=
      step_ro_call (by decide) hs1_c hs1_lf hr1
    obtain ⟨nw, s3, hs3_c, hs3_lf, hs3_loc, _, hr3⟩ :=
      step_ro_call (by decide) hs2_c hs2_lf hr2
    obtain ⟨endpw, s4, hs4_c, hs4_lf, hs4_loc, _, hr4⟩ :=
      step_ro_call (by decide) hs3_c hs3_lf hr3
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr4
    have hs4_endp : s4.locals.lookup (ofString "endp") = some (.val (.word endpw)) := by
      rw [hs4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hcmp_endp : @evalHOLExact 64 F _ s4.toExact (fun x => Classical.propDecidable (s4.memaddrs x))
        (.cmp .equal (.var .local (ofString "endp")) (.const 18446744073709551615#64)) =
        some (.val (.word (if endpw = 18446744073709551615#64 then (1#64 : BitVec 64) else 0#64))) := by
      simp [evalHOLExact, hs4_endp, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [hcmp_endp] at hr4; dsimp only at hr4
    by_cases hendp : endpw = 18446744073709551615#64
    · rw [if_pos hendp] at hr4; rw [if_neg h10] at hr4; rw [hret_rstruct s4 18446744073709551615#64 0#64] at hr4
      injection hr4 with h1; injection h1 with hv
      exact ⟨18446744073709551615#64, 0#64, hv.symm, fun hne => absurd rfl hne, Or.inl rfl⟩
    · rw [if_neg hendp] at hr4; rw [if_pos h00] at hr4; rw [evaluateHOLFiniteState_skip] at hr4; dsimp only at hr4
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
          step_ro_call (by decide) hs5_c hs5_lf hr4
        have hvals6 : vals6 = [.val (.word curw)] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs5_cur] at hargs6
          exact hargs6.symm
        subst hvals6
        obtain ⟨rfl, rfl, curw', hcur_inj, hcal6_v⟩ := one_word_arg_lookup lookup_ceil32 hl6
        injection hcur_inj with hcur_inj'; injection hcur_inj' with hcur_inj''; subst hcur_inj''
        obtain ⟨befw', hbef_inj, hbef_lo, hbef_hi⟩ := ceil32_body_exact_g09 (callEntryStateHOLFinite s5 cal6) hs5_c
          hcal6_v (.val (.word befw)) hrun6
        injection hbef_inj with hbef_inj'; injection hbef_inj' with hbef_inj''; subst hbef_inj''
        have hs6_endp : s6.locals.lookup (ofString "endp") = some (.val (.word endpw)) := by
          rw [hs6_loc]; simp [hs5_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs4_endp,
            show ofString "before" ≠ ofString "endp" by decide,
            show ofString "cur" ≠ ofString "endp" by decide]
        obtain ⟨aftw, s7, hs7_c, hs7_lf, hs7_loc, ⟨vals7, body7, cal7, rs7, hargs7, hl7, hrun7⟩, hr7⟩ :=
          step_ro_call (by decide) hs6_c hs6_lf hr6
        have hvals7 : vals7 = [.val (.word endpw)] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs6_endp] at hargs7
          exact hargs7.symm
        subst hvals7
        obtain ⟨rfl, rfl, endpw', hendp_inj, hcal7_v⟩ := one_word_arg_lookup lookup_ceil32 hl7
        injection hendp_inj with hendp_inj'; injection hendp_inj' with hendp_inj''; subst hendp_inj''
        obtain ⟨aftw', haft_inj, haft_lo, haft_hi⟩ := ceil32_body_exact_g09 (callEntryStateHOLFinite s6 cal7) hs6_c
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
          simp [evalHOLExact, hs7_bef, hs7_aft, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        rw [hcmp_ba] at hr7; dsimp only at hr7
        by_cases hba : ¬ (befw < aftw)
        · rw [if_pos hba] at hr7; rw [if_neg h10] at hr7; rw [hret_rstruct s7 0#64 0#64] at hr7
          injection hr7 with h1; injection h1 with hv
          exact ⟨0#64, 0#64, hv.symm, fun _ => by decide, Or.inl rfl⟩
        · rw [if_neg hba] at hr7; rw [if_pos h00] at hr7; rw [evaluateHOLFiniteState_skip] at hr7; dsimp only at hr7
          have hba_lt : befw.toNat < aftw.toNat := BitVec.lt_def.1 (Classical.not_not.1 hba)
          obtain ⟨caw, s8, hs8_c, hs8_lf, hs8_loc, ⟨vals8, body8, cal8, rs8, hargs8, hl8, hrun8⟩, hr8⟩ :=
            step_ro_call (by decide) hs7_c hs7_lf hr7
          have hvals8 : vals8 = [.val (.word aftw)] := by
            simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs7_aft] at hargs8
            exact hargs8.symm
          subst hvals8
          obtain ⟨rfl, rfl, aftw_arg, haft_arg_inj, hcal8_sz⟩ := one_word_arg_lookup lookup_memory_gas_cost hl8
          injection haft_arg_inj with h1; injection h1 with h2; subst h2
          have hs8_bef : s8.locals.lookup (ofString "before") = some (.val (.word befw)) := by
            rw [hs8_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs7_bef,
              show ofString "ca" ≠ ofString "before" by decide]
          obtain ⟨cbw, s9, hs9_c, hs9_lf, hs9_loc, ⟨vals9, body9, cal9, rs9, hargs9, hl9, hrun9⟩, hr9⟩ :=
            step_ro_call (by decide) hs8_c hs8_lf hr8
          have hvals9 : vals9 = [.val (.word befw)] := by
            simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs8_bef] at hargs9
            exact hargs9.symm
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
            simp [evalHOLExact, hs9_ca, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
          rw [hcmp_ca] at hr9; dsimp only at hr9
          by_cases hca_max : caw = 18446744073709551615#64
          · rw [if_pos hca_max] at hr9; rw [if_neg h10] at hr9; rw [hret_rstruct s9 18446744073709551615#64 0#64] at hr9
            injection hr9 with h1; injection h1 with hv
            exact ⟨18446744073709551615#64, 0#64, hv.symm, fun hne => absurd rfl hne, Or.inl rfl⟩
          · rw [if_neg hca_max] at hr9; rw [if_pos h00] at hr9; rw [evaluateHOLFiniteState_skip] at hr9; dsimp only at hr9
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
            have haft_lt37 : aftw.toNat < 2 ^ 37 := by
              by_contra hge
              have hca_eq := memory_gas_cost_ge_twoPow37_g09 (callEntryStateHOLFinite s7 cal8)
                (Nat.le_of_not_lt hge) hs7_c hcal8_sz (.val (.word caw)) hrun8
              injection hca_eq with h1; injection h1 with h2
              exact hca_max h2
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
            have hbef_ceil : befw.toNat = ceil32NatG09 (memW s (globN s "ev" + 32)) := by
              rw [hbef_eq.1, hcur_eq]
            have ⟨hc_le, hca_lt63⟩ := memory_gas_cost_mono_lt37_g09
              (callEntryStateHOLFinite s8 cal9) (callEntryStateHOLFinite s7 cal8)
              (Nat.le_of_lt hba_lt) (Or.inr ⟨haft_lt37, haft_mod⟩) hs8_c hs7_c hcal9_sz hcal8_sz hrun9 hrun8
            have hcost_sub : (caw - cbw).toNat = caw.toNat - cbw.toNat :=
              BitVec.toNat_sub_of_le (BitVec.le_def.2 hc_le)
            have hsub_nat : (aftw - befw).toNat = aftw.toNat - befw.toNat :=
              BitVec.toNat_sub_of_le (BitVec.le_def.2 (Nat.le_of_lt hba_lt))
            refine ⟨caw - cbw, aftw - befw, hv.symm, fun _ => by rw [hcost_sub]; omega,
              Or.inr ⟨befw.toNat, aftw.toNat, haft_lt37, haft_mod, hbef_mod, hbef_ceil, hba_lt, hsub_nat, ?_⟩⟩
            intro hcur_al
            rw [← hcur_eq] at hcur_al ⊢
            exact hbef_eq.2.2.2.2 hcur_al

theorem lookup_extend_memory_cost2_g09 :
    originalRuntimeCode.lookup (ofString "extend_memory_cost2") =
      some ([(ofString "s1", .comb [.one, .one, .one, .one]),
             (ofString "n1", .comb [.one, .one, .one, .one]),
             (ofString "s2", .comb [.one, .one, .one, .one]),
             (ofString "n2", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_extend_memory_cost2, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 459 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_extend_memory_cost2) rfl

private theorem two_u256_arg_lookup_cost1_g09
    {v0 v1 : ValueHOL 64} {body' : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret' : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "extend_memory_cost1") [v0, v1] =
      some (body', callee, ret')) :
    body' = sourceFnBody Guest.Software.guestFn_extend_memory_cost1 ∧
    ret' = .comb [.one, .one] ∧
    callee.lookup (ofString "start") = some v0 ∧
    callee.lookup (ofString "size") = some v1 := by
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
    originalRuntimeCode.lookup (ofString "extend_memory_cost1") [v0, v1] body' callee ret' hl
  simp only [Flapjack.lookupCodeHOLExact, lookup_extend_memory_cost1] at hx
  split at hx
  · have heq := Option.some.inj hx
    rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨hloc, rfl⟩
    have hne : ofString "size" ≠ ofString "start" := by decide
    refine ⟨rfl, rfl, ?_, ?_⟩
    · have hfn := congrFun hloc.symm (ofString "start")
      simpa [FUPDATE_LIST, FUPDATE, hne, Ne.symm hne] using hfn
    · have hfn := congrFun hloc.symm (ofString "size")
      simpa [FUPDATE_LIST, FUPDATE] using hfn
  · cases hx

theorem eps_extend_memory_cost2_bounds_g09 :
    EvmPreservingSpec
      (fun s => ∃ s10 s11 s12 s13 n10 n11 n12 n13 s20 s21 s22 s23 n20 n21 n22 n23 : BitVec 64,
        s.locals.lookup (ofString "s1") =
          some (.rStruct [.val (.word s10), .val (.word s11), .val (.word s12), .val (.word s13)]) ∧
        s.locals.lookup (ofString "n1") =
          some (.rStruct [.val (.word n10), .val (.word n11), .val (.word n12), .val (.word n13)]) ∧
        s.locals.lookup (ofString "s2") =
          some (.rStruct [.val (.word s20), .val (.word s21), .val (.word s22), .val (.word s23)]) ∧
        s.locals.lookup (ofString "n2") =
          some (.rStruct [.val (.word n20), .val (.word n21), .val (.word n22), .val (.word n23)]))
      (fun s v post =>
        LocFrame s post ∧
        ∃ cw ebw : BitVec 64,
          v = .rStruct [.val (.word cw), .val (.word ebw)] ∧
          ebw.toNat < 2 ^ 37 ∧
          ebw.toNat % 32 = 0 ∧
          (ebw = 0#64 ∨ ceil32NatG09 (memW s (globN s "ev" + 32)) + ebw.toNat < 2 ^ 37) ∧
          (∀ s1v n1v s2v n2v : ValueHOL 64,
            s.locals.lookup (ofString "s1") = some s1v →
            s.locals.lookup (ofString "n1") = some n1v →
            s.locals.lookup (ofString "s2") = some s2v →
            s.locals.lookup (ofString "n2") = some n2v →
            cw ≠ 18446744073709551615#64 →
            ((satWordG09 n1v ≠ 0#64 →
              (satWordG09 s1v).toNat + (satWordG09 n1v).toNat ≤
                ceil32NatG09 (memW s (globN s "ev" + 32)) + ebw.toNat) ∧
             (satWordG09 n2v ≠ 0#64 →
              (satWordG09 s2v).toNat + (satWordG09 n2v).toNat ≤
                ceil32NatG09 (memW s (globN s "ev" + 32)) + ebw.toNat))))
      (ofString "extend_memory_cost2") := by
  refine ⟨_, _, _, lookup_extend_memory_cost2_g09, ?_⟩
  intro F s hcode hInv hP _ _
  have hnoRaise : ¬ IsEvmErr
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_extend_memory_cost2)).1 :=
    evaluate_noRaiseProg cost2NoRaiseCalleesG09 cost2NoRaiseCalleesG09_good
      (sourceFnBody Guest.Software.guestFn_extend_memory_cost2) (by decide) s hcode
  refine ⟨?_, fun herr => absurd herr hnoRaise⟩
  intro v hv
  obtain ⟨s10, s11, s12, s13, n10, n11, n12, n13, s20, s21, s22, s23, n20, n21, n22, n23,
    hs1_lk, hn1_lk, hs2_lk, hn2_lk⟩ := hP
  obtain ⟨hb_ev, evw, hevw, hevw_nat⟩ := ev_word_bounds hInv
  have finish_lf : ∀ {post : PanSemStateFiniteExact 64 F} {Q : Prop},
      LocFrame s post → Q →
      EvmInv post ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s ∧ LocFrame s post ∧ Q := by
    intro post Q hlf hQ
    have hInv_p : EvmInv post := by
      have h := localsFree_evmInv s post.locals post.clock hInv
      rwa [← hlf] at h
    have hm : post.memory = s.memory := by unfold LocFrame at hlf; conv_lhs => rw [hlf]
    have hg : post.globals = s.globals := by unfold LocFrame at hlf; conv_lhs => rw [hlf]
    have hc := evm_congr hm hg
    exact ⟨hInv_p, evmChain_congr hm hg, le_of_eq hc.2.1, hlf, hQ⟩
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
  let s1Val : ValueHOL 64 := .rStruct [.val (.word s10), .val (.word s11), .val (.word s12), .val (.word s13)]
  let n1Val : ValueHOL 64 := .rStruct [.val (.word n10), .val (.word n11), .val (.word n12), .val (.word n13)]
  let s2Val : ValueHOL 64 := .rStruct [.val (.word s20), .val (.word s21), .val (.word s22), .val (.word s23)]
  let n2Val : ValueHOL 64 := .rStruct [.val (.word n20), .val (.word n21), .val (.word n22), .val (.word n23)]
  have h10 : ¬ ((1#64 : BitVec 64) = 0) := by decide
  have h00 : (0#64 : BitVec 64) = 0 := rfl
  rcases hrun_main : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_extend_memory_cost2) with ⟨rmain, post⟩
  rw [hrun_main] at hv; dsimp only at hv ⊢
  rw [hbody, evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun_main
  have hargs1 : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x))
      [.var .local (ofString "s1"), .var .local (ofString "n1")] = some [s1Val, n1Val] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs1_lk, hn1_lk, s1Val, n1Val]
  rw [hargs1] at hrun_main; dsimp only at hrun_main
  rcases hl1 : lookupCodeHOLFinite s.code.lookup (ofString "extend_memory_cost1") [s1Val, n1Val] with _ | ⟨body1, cal1, rs1⟩
  · rw [hl1] at hrun_main; injection hrun_main with hr _; rw [← hr] at hv; cases hv
  · rw [hl1] at hrun_main; dsimp only at hrun_main
    have hl1_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "extend_memory_cost1") [s1Val, n1Val] =
        some (body1, cal1, rs1) := by rwa [← hcode]
    obtain ⟨rfl, rfl, hcal1_start, hcal1_size⟩ := two_u256_arg_lookup_cost1_g09 hl1_orig
    split at hrun_main
    · injection hrun_main with hr _; rw [← hr] at hv; cases hv
    · have hro1 := installed_body_readOnly 458 (by rw [guestAst_len]; decide)
        Guest.Software.guestFn_extend_memory_cost1 rfl opRoCallees rfl hl1_orig
      have hsafe1 := evaluate_readOnlyProg opRoCallees opRoCallees_good
        (sourceFnBody Guest.Software.guestFn_extend_memory_cost1) hro1
        (callEntryStateHOLFinite s cal1) hcode
      rcases hrun1 : evaluateHOLFiniteState (callEntryStateHOLFinite s cal1)
          (sourceFnBody Guest.Software.guestFn_extend_memory_cost1) with ⟨rb1, pb1⟩
      rw [hrun1] at hrun_main hsafe1
      rcases rb1 with _ | rb1
      · injection hrun_main with hr _; rw [← hr] at hv; cases hv
      · cases rb1 with
        | returned va =>
          dsimp only at hrun_main
          split at hrun_main
          · have hlf_ce1 : LocFrame (callEntryStateHOLFinite s cal1) pb1 :=
              hsafe1.to_resumes (Or.inl ⟨va, rfl⟩)
            have hlf_pb1 : LocFrame s pb1 := by
              unfold LocFrame at hlf_ce1 ⊢; rw [hlf_ce1]; rfl
            obtain ⟨c1w, eb1w, rfl, hc1_lt63, heb1_cases⟩ :=
              extend_memory_cost1_body_full_g09 (callEntryStateHOLFinite s cal1) hcode va (by rw [hrun1])
            have hce1_mem : memW (callEntryStateHOLFinite s cal1) (globN (callEntryStateHOLFinite s cal1) "ev" + 32) =
                memW s (globN s "ev" + 32) := rfl
            rw [hce1_mem] at heb1_cases
            have hwin1 : c1w ≠ 18446744073709551615#64 → satWordG09 n1Val ≠ 0#64 →
                (satWordG09 s1Val).toNat + (satWordG09 n1Val).toNat ≤
                  ceil32NatG09 (memW s (globN s "ev" + 32)) + eb1w.toNat := by
              intro hc1_ne hnz1
              exact extend_memory_cost1_window_body_g09 (callEntryStateHOLFinite s cal1) hcode
                s10 s11 s12 s13 n10 n11 n12 n13 c1w eb1w hcal1_start hcal1_size
                (by rw [hrun1]) hc1_ne hnz1
            set t1 := setVarHOLFinite (ofString "a") (.rStruct [.val (.word c1w), .val (.word eb1w)])
              { pb1 with locals := s.locals }
            have ht1_lf : LocFrame s t1 := hlf_pb1.with_locals_clock _ pb1.clock
            have ht1_code : t1.code = originalRuntimeCode := by unfold LocFrame at ht1_lf; rw [ht1_lf]; exact hcode
            have ht1_mem : t1.memory = s.memory := by unfold LocFrame at ht1_lf; conv_lhs => rw [ht1_lf]
            have ht1_glob : t1.globals = s.globals := by unfold LocFrame at ht1_lf; conv_lhs => rw [ht1_lf]
            have ht1_a : t1.locals.lookup (ofString "a") =
                some (.rStruct [.val (.word c1w), .val (.word eb1w)]) := by
              simp [t1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have ht1_s2 : t1.locals.lookup (ofString "s2") = some s2Val := by
              simp [t1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_lk, s2Val,
                show ofString "a" ≠ ofString "s2" by decide]
            have ht1_n2 : t1.locals.lookup (ofString "n2") = some n2Val := by
              simp [t1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn2_lk, n2Val,
                show ofString "a" ≠ ofString "n2" by decide]
            rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hrun_main
            have hcmp_a : @evalHOLExact 64 F _ t1.toExact (fun x => Classical.propDecidable (t1.memaddrs x))
                (.cmp .equal (.rfield 0 (.var .local (ofString "a"))) (.const 18446744073709551615#64)) =
                some (.val (.word (if c1w = 18446744073709551615#64 then (1#64 : BitVec 64) else 0#64))) := by
              simp [evalHOLExact, ht1_a, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
            rw [hcmp_a] at hrun_main; dsimp only at hrun_main
            by_cases hc1_max : c1w = 18446744073709551615#64
            · rw [if_pos hc1_max, if_neg h10, evaluateHOLFiniteState_return] at hrun_main
              have hev_a : @evalHOLExact 64 F _ t1.toExact (fun x => Classical.propDecidable (t1.memaddrs x))
                  (.var .local (ofString "a")) =
                  some (.rStruct [.val (.word c1w), .val (.word eb1w)]) := ht1_a
              rw [hev_a] at hrun_main; dsimp only at hrun_main
              have hsz_a : sizeOfShapeWithContextHOL t1.structs
                  (shapeOfHOLExact (.rStruct [.val (.word c1w), .val (.word eb1w)] : ValueHOL 64)) ≤ 32 := by
                simp [shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
              rw [if_pos hsz_a] at hrun_main; dsimp only at hrun_main
              injection hrun_main with hr_eq hpost_eq
              rw [← hr_eq] at hv; injection hv with hv1; injection hv1 with hv_eq
              have hpost_lf : LocFrame s post := by
                rw [← hpost_eq]
                exact ht1_lf.with_locals_clock _ t1.clock
              refine finish_lf hpost_lf ⟨c1w, eb1w, hv_eq.symm, ?_, ?_, ?_, ?_⟩
              · rcases heb1_cases with rfl | ⟨bef1, aft1, haft1_lt, _, _, _, hlt1, heb1_eq, _⟩
                · decide
                · omega
              · rcases heb1_cases with rfl | ⟨bef1, aft1, _, haft1_m, hbef1_m, _, hlt1, heb1_eq, _⟩
                · decide
                · omega
              · rcases heb1_cases with rfl | ⟨bef1, aft1, haft1_lt, _, _, hbef1_c, _, heb1_eq, _⟩
                · exact Or.inl rfl
                · exact Or.inr (by omega)
              · intro _ _ _ _ _ _ _ _ hne; exact absurd hc1_max hne
            · rw [if_neg hc1_max, if_pos h00, evaluateHOLFiniteState_skip] at hrun_main; dsimp only at hrun_main
              have hc1_lt : c1w.toNat < 2 ^ 63 := hc1_lt63 hc1_max
              rw [evaluateHOLFiniteState_dec_total] at hrun_main; dsimp only at hrun_main
              rcases hld_saved : @evalHOLExact 64 F _ t1.toExact (fun x => Classical.propDecidable (t1.memaddrs x))
                  (.load .one (.op .add [.var .global (ofString "ev"), .const 32#64])) with _ | savedv
              · rw [hld_saved] at hrun_main; injection hrun_main with hr _; rw [← hr] at hv; cases hv
              · obtain ⟨savedw, rfl, hsavedw_nat⟩ := evalAt_loadG_word t1 "ev" 32#64 savedv hld_saved
                rw [hld_saved] at hrun_main; dsimp only at hrun_main
                have hsh_saved : shapeEqHOL .one (shapeOfHOLExact (.val (.word savedw))) = true := by
                  simp [shapeEqHOL, shapeOfHOLExact]
                rw [if_pos hsh_saved] at hrun_main; dsimp only at hrun_main
                have h32_nat : (32#64 : BitVec 64).toNat = 32 := rfl
                have hsaved_eq : savedw.toNat = memW s (globN s "ev" + 32) := by
                  rw [hsavedw_nat, h32_nat]; simp [memW, globN, ht1_mem, ht1_glob]
                have haddr_mem_saved : s.memory (BitVec.ofNat 64 (globN s "ev" + 32)) = .word savedw := by
                  have hld_orig : @evalHOLExact 64 F _ t1.toExact (fun x => Classical.propDecidable (t1.memaddrs x))
                      (.load .one (.op .add [.var .global (ofString "ev"), .const 32#64])) =
                      some (.val (.word savedw)) := hld_saved
                  have hg1 : t1.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
                    rw [ht1_glob]; exact hevw
                  simp [evalHOLExact, evalListHOLExact, hg1, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at hld_orig
                  rcases hm : t1.memory (evw + 32#64) with ⟨y⟩
                  rw [hm] at hld_orig
                  have hy : y = savedw := by cases hld_orig.2; rfl
                  subst hy
                  have hadd_bv : BitVec.ofNat 64 (globN s "ev" + 32) = evw + 32#64 := by
                    apply BitVec.eq_of_toNat_eq
                    rw [BitVec.toNat_add, hevw_nat, h32_nat, BitVec.toNat_ofNat]
                  rw [hadd_bv, ← ht1_mem]
                  exact hm
                set t2 := setVarHOLFinite (ofString "saved") (.val (.word savedw)) t1
                have ht2_lf : LocFrame s t2 := ht1_lf.with_locals_clock _ t1.clock
                have ht2_code : t2.code = originalRuntimeCode := ht1_code
                have ht2_mem : t2.memory = s.memory := ht1_mem
                have ht2_glob : t2.globals = s.globals := ht1_glob
                have ht2_saved : t2.locals.lookup (ofString "saved") = some (.val (.word savedw)) := by
                  simp [t2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                have ht2_a : t2.locals.lookup (ofString "a") =
                    some (.rStruct [.val (.word c1w), .val (.word eb1w)]) := by
                  simp [t2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht1_a,
                    show ofString "saved" ≠ ofString "a" by decide]
                have ht2_s2 : t2.locals.lookup (ofString "s2") = some s2Val := by
                  simp [t2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht1_s2,
                    show ofString "saved" ≠ ofString "s2" by decide]
                have ht2_n2 : t2.locals.lookup (ofString "n2") = some n2Val := by
                  simp [t2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht1_n2,
                    show ofString "saved" ≠ ofString "n2" by decide]
                rw [evaluateHOLFiniteState_seq_line780] at hrun_main
                rcases hst1 : evaluateHOLFiniteState t2
                    (.store (.op .add [.var .global (ofString "ev"), .const 32#64])
                      (.op .add [.var .local (ofString "saved"), .rfield 1 (.var .local (ofString "a"))])) with ⟨rst1, t3⟩
                rw [hst1] at hrun_main
                cases rst1 with
                | some res1 =>
                  have herr1 := store_some_eq_error_g09 hst1; subst herr1
                  dsimp only at hrun_main; injection hrun_main with hr _; rw [← hr] at hv; cases hv
                | none =>
                  dsimp only at hrun_main
                  obtain ⟨w1, hw1_ev, ht3_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := t2) (post := t3)
                    (gname := "ev") (gbase := globN s "ev") (off := 32)
                    (by rw [ht2_glob]; exact hevw) hevw_nat (by omega)
                    (fun u hu => by
                      simp only [evalHOLExact, evalListHOLExact, ht2_saved, ht2_a, wordOpHOL, wordOp,
                        valueIsWord, valueWord] at hu
                      injection hu with hu'; exact ⟨_, hu'.symm⟩) hst1
                  have hw1_eq : w1 = savedw + eb1w := by
                    simp [evalHOLExact, evalListHOLExact, ht2_saved, ht2_a, wordOpHOL, wordOp,
                      valueIsWord, valueWord] at hw1_ev
                    exact hw1_ev.symm
                  subst hw1_eq
                  have ht3_code : t3.code = originalRuntimeCode := by rw [ht3_eq]; exact ht2_code
                  have ht3_glob : t3.globals = s.globals := by rw [ht3_eq]; exact ht2_glob
                  have ht3_mem : t3.memory = R14Shards.OpHandlersA.updW s.memory (BitVec.ofNat 64 (globN s "ev" + 32)) (savedw + eb1w) := by
                    rw [ht3_eq, ht2_mem]
                  have ht3_saved : t3.locals.lookup (ofString "saved") = some (.val (.word savedw)) := by
                    rw [ht3_eq]; exact ht2_saved
                  have ht3_a : t3.locals.lookup (ofString "a") =
                      some (.rStruct [.val (.word c1w), .val (.word eb1w)]) := by
                    rw [ht3_eq]; exact ht2_a
                  have ht3_s2 : t3.locals.lookup (ofString "s2") = some s2Val := by
                    rw [ht3_eq]; exact ht2_s2
                  have ht3_n2 : t3.locals.lookup (ofString "n2") = some n2Val := by
                    rw [ht3_eq]; exact ht2_n2
                  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun_main
                  have hargs2 : evalListHOLFinite t3 (h := fun x => Classical.propDecidable (t3.memaddrs x))
                      [.var .local (ofString "s2"), .var .local (ofString "n2")] = some [s2Val, n2Val] := by
                    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ht3_s2, ht3_n2, s2Val, n2Val]
                  rw [hargs2] at hrun_main; dsimp only at hrun_main
                  rcases hl2 : lookupCodeHOLFinite t3.code.lookup (ofString "extend_memory_cost1") [s2Val, n2Val] with _ | ⟨body2, cal2, rs2⟩
                  · rw [hl2] at hrun_main; injection hrun_main with hr _; rw [← hr] at hv; cases hv
                  · rw [hl2] at hrun_main; dsimp only at hrun_main
                    have hl2_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "extend_memory_cost1") [s2Val, n2Val] =
                        some (body2, cal2, rs2) := by rwa [← ht3_code]
                    obtain ⟨rfl, rfl, hcal2_start, hcal2_size⟩ := two_u256_arg_lookup_cost1_g09 hl2_orig
                    split at hrun_main
                    · injection hrun_main with hr _; rw [← hr] at hv; cases hv
                    · have hro2 := installed_body_readOnly 458 (by rw [guestAst_len]; decide)
                        Guest.Software.guestFn_extend_memory_cost1 rfl opRoCallees rfl hl2_orig
                      have hsafe2 := evaluate_readOnlyProg opRoCallees opRoCallees_good
                        (sourceFnBody Guest.Software.guestFn_extend_memory_cost1) hro2
                        (callEntryStateHOLFinite t3 cal2) ht3_code
                      rcases hrun2 : evaluateHOLFiniteState (callEntryStateHOLFinite t3 cal2)
                          (sourceFnBody Guest.Software.guestFn_extend_memory_cost1) with ⟨rb2, pb2⟩
                      rw [hrun2] at hrun_main hsafe2
                      rcases rb2 with _ | rb2
                      · injection hrun_main with hr _; rw [← hr] at hv; cases hv
                      · cases rb2 with
                        | returned vb =>
                          dsimp only at hrun_main
                          split at hrun_main
                          · have hlf_ce2 : LocFrame (callEntryStateHOLFinite t3 cal2) pb2 :=
                              hsafe2.to_resumes (Or.inl ⟨vb, rfl⟩)
                            have hlf_pb2 : LocFrame t3 pb2 := by
                              unfold LocFrame at hlf_ce2 ⊢; rw [hlf_ce2]; rfl
                            obtain ⟨c2w, eb2w, rfl, hc2_lt63, heb2_cases⟩ :=
                              extend_memory_cost1_body_full_g09 (callEntryStateHOLFinite t3 cal2) ht3_code vb (by rw [hrun2])
                            have hce2_mem : memW (callEntryStateHOLFinite t3 cal2)
                                (globN (callEntryStateHOLFinite t3 cal2) "ev" + 32) = (savedw + eb1w).toNat := by
                              have hg_ev : globN (callEntryStateHOLFinite t3 cal2) "ev" = globN s "ev" :=
                                globN_congr ht3_glob ▸ rfl
                              rw [hg_ev]
                              change memW t3 (globN s "ev" + 32) = (savedw + eb1w).toNat
                              unfold memW; rw [ht3_mem]; simp [R14Shards.OpHandlersA.updW]
                            rw [hce2_mem] at heb2_cases
                            have hwin2 : c2w ≠ 18446744073709551615#64 → satWordG09 n2Val ≠ 0#64 →
                                (satWordG09 s2Val).toNat + (satWordG09 n2Val).toNat ≤
                                  ceil32NatG09 (savedw + eb1w).toNat + eb2w.toNat := by
                              intro hc2_ne hnz2
                              have hw := extend_memory_cost1_window_body_g09 (callEntryStateHOLFinite t3 cal2) ht3_code
                                s20 s21 s22 s23 n20 n21 n22 n23 c2w eb2w hcal2_start hcal2_size
                                (by rw [hrun2]) hc2_ne hnz2
                              rwa [hce2_mem] at hw
                            set t4 := setVarHOLFinite (ofString "b") (.rStruct [.val (.word c2w), .val (.word eb2w)])
                              { pb2 with locals := t3.locals }
                            have ht4_lf : LocFrame t3 t4 := hlf_pb2.with_locals_clock _ pb2.clock
                            have ht4_glob : t4.globals = s.globals := by
                              unfold LocFrame at ht4_lf; rw [ht4_lf]; exact ht3_glob
                            have ht4_mem : t4.memory = R14Shards.OpHandlersA.updW s.memory (BitVec.ofNat 64 (globN s "ev" + 32)) (savedw + eb1w) := by
                              unfold LocFrame at ht4_lf; conv_lhs => rw [ht4_lf]
                              exact ht3_mem
                            have ht4_saved : t4.locals.lookup (ofString "saved") = some (.val (.word savedw)) := by
                              simp [t4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht3_saved,
                                show ofString "b" ≠ ofString "saved" by decide]
                            have ht4_a : t4.locals.lookup (ofString "a") =
                                some (.rStruct [.val (.word c1w), .val (.word eb1w)]) := by
                              simp [t4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht3_a,
                                show ofString "b" ≠ ofString "a" by decide]
                            have ht4_b : t4.locals.lookup (ofString "b") =
                                some (.rStruct [.val (.word c2w), .val (.word eb2w)]) := by
                              simp [t4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                            rw [evaluateHOLFiniteState_seq_line780] at hrun_main
                            rcases hst2 : evaluateHOLFiniteState t4
                                (.store (.op .add [.var .global (ofString "ev"), .const 32#64])
                                  (.var .local (ofString "saved"))) with ⟨rst2, t5⟩
                            rw [hst2] at hrun_main
                            cases rst2 with
                            | some res2 =>
                              have herr2 := store_some_eq_error_g09 hst2; subst herr2
                              dsimp only at hrun_main; injection hrun_main with hr _; rw [← hr] at hv; cases hv
                            | none =>
                              dsimp only at hrun_main
                              obtain ⟨w2, hw2_ev, ht5_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := t4) (post := t5)
                                (gname := "ev") (gbase := globN s "ev") (off := 32)
                                (by rw [ht4_glob]; exact hevw) hevw_nat (by omega)
                                (fun u hu => by
                                  simp only [evalHOLExact, ht4_saved] at hu
                                  injection hu with hu'; exact ⟨_, hu'.symm⟩) hst2
                              have hw2_eq : w2 = savedw := by
                                simp only [evalHOLExact, ht4_saved] at hw2_ev
                                injection hw2_ev with h1; injection h1 with h2; injection h2 with h3; exact h3.symm
                              subst w2
                              have ht5_mem : t5.memory = s.memory := by
                                rw [ht5_eq, ht4_mem]
                                funext addr
                                unfold R14Shards.OpHandlersA.updW
                                by_cases haddr : addr = BitVec.ofNat 64 (globN s "ev" + 32)
                                · subst haddr; simp [haddr_mem_saved]
                                · simp [haddr]
                              have ht5_lf : LocFrame s t5 := by
                                unfold LocFrame at ht4_lf ht2_lf ⊢
                                have h4 : t4 = { s with locals := t4.locals, memory := t3.memory, clock := t4.clock } := by
                                  conv_lhs => rw [ht4_lf]
                                  rw [ht3_eq, ht2_lf]
                                cases t5
                                injection ht5_eq with _ hg5 hs5 hc5 he5 _ hma5 hsh5 _ hbe5 hff5 hba5 hta5
                                dsimp only at ht5_mem ⊢
                                rw [ht5_mem, hg5, hs5, hc5, he5, hma5, hsh5, hbe5, hff5, hba5, hta5]
                                rw [congrArg PanSemStateFiniteExact.globals h4,
                                  congrArg PanSemStateFiniteExact.structs h4,
                                  congrArg PanSemStateFiniteExact.code h4,
                                  congrArg PanSemStateFiniteExact.eshapes h4,
                                  congrArg PanSemStateFiniteExact.memaddrs h4,
                                  congrArg PanSemStateFiniteExact.shMemaddrs h4,
                                  congrArg PanSemStateFiniteExact.be h4,
                                  congrArg PanSemStateFiniteExact.ffi h4,
                                  congrArg PanSemStateFiniteExact.baseAddr h4,
                                  congrArg PanSemStateFiniteExact.topAddr h4]
                              have ht5_a : t5.locals.lookup (ofString "a") =
                                  some (.rStruct [.val (.word c1w), .val (.word eb1w)]) := by
                                rw [ht5_eq]; exact ht4_a
                              have ht5_b : t5.locals.lookup (ofString "b") =
                                  some (.rStruct [.val (.word c2w), .val (.word eb2w)]) := by
                                rw [ht5_eq]; exact ht4_b
                              have hceil_step : ∀ {eb : BitVec 64},
                                  (eb = 0#64 ∨ ∃ bef aft : Nat,
                                    aft < 2 ^ 37 ∧ aft % 32 = 0 ∧ bef % 32 = 0 ∧
                                    bef = ceil32NatG09 (memW s (globN s "ev" + 32)) ∧
                                    bef < aft ∧ eb.toNat = aft - bef ∧
                                    (memW s (globN s "ev" + 32) % 32 = 0 → bef = memW s (globN s "ev" + 32))) →
                                  ceil32NatG09 (savedw + eb).toNat =
                                    ceil32NatG09 (memW s (globN s "ev" + 32)) + eb.toNat := by
                                intro eb hcases
                                rcases hcases with rfl | ⟨bef, aft, haft_lt, haft_m, hbef_m, hbef_c, hlt_ba, heb_nat, _⟩
                                · simp [hsaved_eq]
                                · have hsaved_le_bef : savedw.toNat ≤ bef := by
                                    rw [hbef_c, hsaved_eq]; unfold ceil32NatG09; omega
                                  have hadd_lt : savedw.toNat + eb.toNat < 2 ^ 64 := by omega
                                  have hadd_nat : (savedw + eb).toNat = savedw.toNat + eb.toNat := by
                                    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hadd_lt]
                                  have heb_mod : eb.toNat % 32 = 0 := by omega
                                  rw [hadd_nat, hsaved_eq]
                                  unfold ceil32NatG09
                                  omega
                              rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hrun_main
                              have hcmp_b : @evalHOLExact 64 F _ t5.toExact (fun x => Classical.propDecidable (t5.memaddrs x))
                                  (.cmp .equal (.rfield 0 (.var .local (ofString "b"))) (.const 18446744073709551615#64)) =
                                  some (.val (.word (if c2w = 18446744073709551615#64 then (1#64 : BitVec 64) else 0#64))) := by
                                simp [evalHOLExact, ht5_b, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
                              rw [hcmp_b] at hrun_main; dsimp only at hrun_main
                              by_cases hc2_max : c2w = 18446744073709551615#64
                              · rw [if_pos hc2_max, if_neg h10, evaluateHOLFiniteState_return] at hrun_main
                                have hev_b : @evalHOLExact 64 F _ t5.toExact (fun x => Classical.propDecidable (t5.memaddrs x))
                                    (.var .local (ofString "b")) =
                                    some (.rStruct [.val (.word c2w), .val (.word eb2w)]) := ht5_b
                                rw [hev_b] at hrun_main; dsimp only at hrun_main
                                have hsz_b : sizeOfShapeWithContextHOL t5.structs
                                    (shapeOfHOLExact (.rStruct [.val (.word c2w), .val (.word eb2w)] : ValueHOL 64)) ≤ 32 := by
                                  simp [shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
                                rw [if_pos hsz_b] at hrun_main; dsimp only at hrun_main
                                injection hrun_main with hr_eq hpost_eq
                                rw [← hr_eq] at hv; injection hv with hv1; injection hv1 with hv_eq
                                have hpost_lf : LocFrame s post := by
                                  rw [← hpost_eq]
                                  exact ht5_lf.with_locals_clock _ t5.clock
                                refine finish_lf hpost_lf ⟨c2w, eb2w, hv_eq.symm, ?_, ?_, ?_, ?_⟩
                                · rcases heb2_cases with rfl | ⟨bef2, aft2, haft2_lt, _, _, _, hlt2, heb2_eq, _⟩
                                  · decide
                                  · omega
                                · rcases heb2_cases with rfl | ⟨bef2, aft2, _, haft2_m, hbef2_m, _, hlt2, heb2_eq, _⟩
                                  · decide
                                  · omega
                                · rcases heb2_cases with rfl | ⟨bef2, aft2, haft2_lt, _, _, hbef2_c, _, heb2_eq, _⟩
                                  · exact Or.inl rfl
                                  · right
                                    have hc_step := hceil_step heb1_cases
                                    omega
                                · intro _ _ _ _ _ _ _ _ hne; exact absurd hc2_max hne
                              · rw [if_neg hc2_max, if_pos h00, evaluateHOLFiniteState_skip] at hrun_main; dsimp only at hrun_main
                                have hc2_lt : c2w.toNat < 2 ^ 63 := hc2_lt63 hc2_max
                                rw [evaluateHOLFiniteState_return] at hrun_main
                                have hev_ret : @evalHOLExact 64 F _ t5.toExact (fun x => Classical.propDecidable (t5.memaddrs x))
                                    (.rstruct
                                      [.op .add [.rfield 0 (.var .local (ofString "a")), .rfield 0 (.var .local (ofString "b"))],
                                       .op .add [.rfield 1 (.var .local (ofString "a")), .rfield 1 (.var .local (ofString "b"))]]) =
                                    some (.rStruct [.val (.word (c1w + c2w)), .val (.word (eb1w + eb2w))]) := by
                                  simp [evalHOLExact, evalListHOLExact, ht5_a, ht5_b, wordOpHOL, wordOp, valueIsWord, valueWord]
                                rw [hev_ret] at hrun_main; dsimp only at hrun_main
                                have hsz_ret : sizeOfShapeWithContextHOL t5.structs
                                    (shapeOfHOLExact (.rStruct [.val (.word (c1w + c2w)), .val (.word (eb1w + eb2w))] : ValueHOL 64)) ≤ 32 := by
                                  simp [shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
                                rw [if_pos hsz_ret] at hrun_main; dsimp only at hrun_main
                                injection hrun_main with hr_eq hpost_eq
                                rw [← hr_eq] at hv; injection hv with hv1; injection hv1 with hv_eq
                                have hpost_lf : LocFrame s post := by
                                  rw [← hpost_eq]
                                  exact ht5_lf.with_locals_clock _ t5.clock
                                have hc_step := hceil_step heb1_cases
                                have heb1_lt37 : eb1w.toNat < 2 ^ 37 := by
                                  rcases heb1_cases with rfl | ⟨_, aft1, haft1_lt, _, _, _, _, heb1_eq, _⟩
                                  · decide
                                  · omega
                                have heb2_lt37 : eb2w.toNat < 2 ^ 37 := by
                                  rcases heb2_cases with rfl | ⟨_, aft2, haft2_lt, _, _, _, _, heb2_eq, _⟩
                                  · decide
                                  · omega
                                have heb1_mod : eb1w.toNat % 32 = 0 := by
                                  rcases heb1_cases with rfl | ⟨_, _, _, hm1, hm2, _, _, heb1_eq, _⟩
                                  · decide
                                  · omega
                                have heb2_mod : eb2w.toNat % 32 = 0 := by
                                  rcases heb2_cases with rfl | ⟨_, _, _, hm1, hm2, _, _, heb2_eq, _⟩
                                  · decide
                                  · omega
                                have heb_sum_lt64 : eb1w.toNat + eb2w.toNat < 2 ^ 64 := by omega
                                have heb_add_nat : (eb1w + eb2w).toNat = eb1w.toNat + eb2w.toNat := by
                                  rw [BitVec.toNat_add, Nat.mod_eq_of_lt heb_sum_lt64]
                                have heb_bound : eb1w + eb2w = 0#64 ∨
                                    ceil32NatG09 (memW s (globN s "ev" + 32)) + (eb1w + eb2w).toNat < 2 ^ 37 := by
                                  rcases heb2_cases with rfl | ⟨bef2, aft2, haft2_lt, _, _, hbef2_c, _, heb2_eq, _⟩
                                  · rcases heb1_cases with rfl | ⟨bef1, aft1, haft1_lt, _, _, hbef1_c, _, heb1_eq, _⟩
                                    · exact Or.inl rfl
                                    · right; rw [heb_add_nat]; simpa using (by omega : ceil32NatG09 (memW s (globN s "ev" + 32)) + eb1w.toNat < 2 ^ 37)
                                  · right; rw [heb_add_nat]; omega
                                have heb_sum_lt37 : (eb1w + eb2w).toNat < 2 ^ 37 := by
                                  rcases heb_bound with hz | hlt
                                  · rw [hz]; decide
                                  · omega
                                refine finish_lf hpost_lf ⟨c1w + c2w, eb1w + eb2w, hv_eq.symm,
                                  heb_sum_lt37, by rw [heb_add_nat]; omega, heb_bound, ?_⟩
                                intro s1v n1v s2v n2v hs1v hn1v hs2v hn2v _
                                have hs1v_eq := Option.some.inj (hs1v.symm.trans hs1_lk)
                                have hn1v_eq := Option.some.inj (hn1v.symm.trans hn1_lk)
                                have hs2v_eq := Option.some.inj (hs2v.symm.trans hs2_lk)
                                have hn2v_eq := Option.some.inj (hn2v.symm.trans hn2_lk)
                                subst hs1v_eq; subst hn1v_eq; subst hs2v_eq; subst hn2v_eq
                                refine ⟨fun hnz1 => ?_, fun hnz2 => ?_⟩
                                · have hw1 := hwin1 hc1_max hnz1
                                  dsimp only [s1Val, n1Val] at hw1
                                  rw [heb_add_nat]; omega
                                · have hw2 := hwin2 hc2_max hnz2
                                  dsimp only [s2Val, n2Val] at hw2
                                  rw [hc_step] at hw2
                                  rw [heb_add_nat]; omega
                          · injection hrun_main with hr _; rw [← hr] at hv; cases hv
                        | exception _ _ =>
                          dsimp only at hrun_main; injection hrun_main with hr _; rw [← hr] at hv; cases hv
                        | «break» | «continue» | error | timeOut | finalFfi _ =>
                          dsimp only at hrun_main; injection hrun_main with hr _; rw [← hr] at hv; cases hv
          · injection hrun_main with hr _; rw [← hr] at hv; cases hv
        | exception _ _ =>
          dsimp only at hrun_main; injection hrun_main with hr _; rw [← hr] at hv; cases hv
        | «break» | «continue» | error | timeOut | finalFfi _ =>
          dsimp only at hrun_main; injection hrun_main with hr _; rw [← hr] at hv; cases hv

theorem lookup_op_mcopy :
    originalRuntimeCode.lookup (ofString "op_mcopy") =
      some ([], sourceFnBody Guest.Software.guestFn_op_mcopy, .one) :=
  lookup_of_guestAst_getElem 512 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_op_mcopy) rfl

private theorem eps_add_sat_pos_ge_b_g09 :
    EvmPreservingSpec
      (fun s => ∃ aw bw : BitVec 64,
        s.locals.lookup (ofString "a") = some (.val (.word aw)) ∧
        s.locals.lookup (ofString "b") = some (.val (.word bw)) ∧
        0 < aw.toNat)
      (fun s v post => LocFrame s post ∧
        ∃ rw : BitVec 64, v = .val (.word rw) ∧ 0 < rw.toNat ∧
          ∀ bw : BitVec 64, s.locals.lookup (ofString "b") = some (.val (.word bw)) → bw.toNat ≤ rw.toNat)
      (ofString "add_sat") := by
  obtain ⟨params, body, retShape, hlk, hro⟩ :=
    eps_of_readOnly 441 (by rw [guestAst_len]; decide) Guest.Software.guestFn_add_sat rfl
      opRoCallees opRoCallees_good rfl
  have hlk_eq : some ([(ofString "a", ShapeHOL.one), (ofString "b", ShapeHOL.one)],
      sourceFnBody Guest.Software.guestFn_add_sat, ShapeHOL.one) =
      some (params, body, retShape) := lookup_add_sat.symm.trans hlk
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_eq, rfl⟩
  subst hbody_eq
  refine ⟨_, _, _, lookup_add_sat, ?_⟩
  intro F s hcode hInv ⟨aw, bw, haw, hbw, hpos⟩ ⟨vals, hl⟩ hnt
  have hs := hro s hcode hInv trivial ⟨vals, hl⟩ hnt
  dsimp only at hs ⊢
  refine ⟨fun v hv => ?_, hs.2⟩
  obtain ⟨h1, h2, h3, hlf⟩ := hs.1 v hv
  obtain ⟨rw, rfl, hrw_exact⟩ := add_sat_body_exact_g09 s haw hbw v hv
  have hbw_lt := bw.isLt
  have hrw_pos : 0 < rw.toNat := by
    rw [hrw_exact]
    split <;> omega
  refine ⟨h1, h2, h3, hlf, rw, rfl, hrw_pos, ?_⟩
  intro bw' hbw'
  rw [hbw] at hbw'
  injection hbw' with h1'; injection h1' with h2'; injection h2' with h3'
  subst h3'
  rw [hrw_exact]
  split <;> omega

private theorem seq_charge_gas_exact_g09 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {amtExp : ExpHOL 64} {cont : ProgHOL 64}
    (hpos : ∀ t (w : BitVec 64),
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp =
        some (.val (.word w)) →
      EvmInv t → P t → 0 < w.toNat)
    (hstep : ∀ t cpost (amtw : BitVec 64),
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
  have hR_le : OpDispatchSpec.evmR t ≤ OpDispatchSpec.evmR s0 := by
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
        let ce := callEntryStateHOLFinite t callee
        have hInv_ce : EvmInv ce := localsFree_evmInv t callee (t.clock - 1) hInv
        have hc_ce := evm_congr (s := t) (t := ce) rfl rfl
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata ce
          (sourceFnBody Guest.Software.guestFn_charge_gas)).1
        have hcg := charge_gas_body_exact ce hInv_ce hamt_cal
        obtain ⟨params_hm, body_hm, rs_hm, hl_hm, hspec_hm⟩ := eps_charge_gas_any_headMem
        have heq_hm := M21.lookup_charge_gas.symm.trans hl_hm
        injection heq_hm with hp_hm
        rcases Prod.mk.inj hp_hm with ⟨rfl, hp_hm'⟩
        rcases Prod.mk.inj hp_hm' with ⟨hb_hm, rfl⟩
        subst hb_hm
        have hhm := hspec_hm ce hc hInv_ce trivial ⟨[.val (.word amtw)], hl_orig⟩
        rcases hrun : evaluateHOLFiniteState ce (sourceFnBody Guest.Software.guestFn_charge_gas) with ⟨res, cpost⟩
        change evaluateHOLFiniteState ce (sourceFnBody Guest.Software.guestFn_charge_gas) = (res, cpost) at hrun
        simp only [ce, hrun] at hnt hmeta hcg hhm ⊢
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
                charge_gas_return_amount_lt_g09 ce hInv_ce hamt_cal (v := v) (by simp only [ce]; rw [hrun])
              have hmem_head_cp : ∀ off : Nat, off ∈ ([24, 32, 40] : List Nat) →
                  memW cpost (globN t "ev" + off) = memW t (globN t "ev" + off) :=
                ((hhm (by simp)).1 v rfl).2.2.2.2
              let resumed : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
              have hInv_res : EvmInv resumed := localsFree_evmInv cpost t.locals cpost.clock hInv_cp
              have hc_res := evm_congr (s := cpost) (t := resumed) rfl rfl
              have hlen_res : (evmChain resumed).length = (evmChain s0).length := by
                rw [hc_res.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              have hR_lt : OpDispatchSpec.evmR resumed < OpDispatchSpec.evmR s0 := by
                rw [hc_res.2.1]; rw [hc_ce.2.1] at hR_cp; omega
              have hR_lt_if : if true then OpDispatchSpec.evmR resumed < OpDispatchSpec.evmR s0 else OpDispatchSpec.evmR resumed ≤ OpDispatchSpec.evmR s0 := by
                simp only [↓reduceIte]; exact hR_lt
              exact hcont resumed (hmeta.trans hc) hInv_res hlen_res hR_lt_if
                (hstep t cpost amtw hv0_ev hamt_lt hInv hP hInv_cp hglob_cp
                  (hch_cp.trans (evmChain_congr rfl rfl)) hmem_head_cp)
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
          | finalFfi _ =>
            refine opDispatchPost_other (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => exact opDispatchPost_error s0 cpost.emptyLocalsHOLFinite

private theorem op_mcopy_post_extend_run {F : Type} (s0 : PanSemStateFiniteExact 64 F) :
    HandlerRun s0
      (fun t => ∃ (dstVal srcVal lenVal : ValueHOL 64),
        (∃ a b c d : BitVec 64, dstVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
        (∃ a b c d : BitVec 64, srcVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
        t.locals.lookup (ofString "dst") = some dstVal ∧
        t.locals.lookup (ofString "src") = some srcVal ∧
        t.locals.lookup (ofString "n") = some (.val (.word (satWordG09 lenVal))) ∧
        (satWordG09 lenVal ≠ 0#64 →
          (satWordG09 srcVal).toNat + (satWordG09 lenVal).toNat ≤ memW t (globN t "ev" + 32) ∧
          (satWordG09 dstVal).toNat + (satWordG09 lenVal).toNat ≤ memW t (globN t "ev" + 32)))
      true
      (.seq
        (.ite (.cmp .notEqual (.var .local (ofString "n")) (.const 0#64))
          (.decCall (ofString "d") .one (ofString "sat_word") [.var .local (ofString "dst")]
            (.decCall (ofString "s") .one (ofString "sat_word") [.var .local (ofString "src")]
              (.decCall (ofString "mark") .one (ofString "heap_mark") []
                (.decCall (ofString "tmp") .one (ofString "alloc") [.var .local (ofString "n")]
                  (.seq
                    (.call (some (none, none)) (ofString "memcpy")
                      [.var .local (ofString "tmp"),
                       .op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "s")],
                       .var .local (ofString "n")])
                    (.seq
                      (.call (some (none, none)) (ofString "memcpy")
                        [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "d")],
                         .var .local (ofString "tmp"),
                         .var .local (ofString "n")])
                      (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")])))))))
          .skip)
        (.seq
          (.call (some (none, none)) (ofString "pc_add") [.const 1#64])
          (.return (.const 0#64)))) := by
  intro t0 hc0 hInv0 hlen0 hR0 hP0 hnt0
  obtain ⟨dstVal, srcVal, lenVal, hdst4, hsrc4, hdst_lk0, hsrc_lk0, hn_lk0, hwin0⟩ := hP0
  set nw := satWordG09 lenVal
  set dw := satWordG09 dstVal
  set sw := satWordG09 srcVal
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt0 ⊢
  have hcmp_n : @evalHOLExact 64 F _ t0.toExact (fun a => Classical.propDecidable (t0.memaddrs a))
      (.cmp .notEqual (.var .local (ofString "n")) (.const 0#64)) =
      some (.val (.word (if nw ≠ 0#64 then 1 else 0))) := by
    simp [evalHOLExact, hn_lk0, nw, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp_n] at hnt0 ⊢; dsimp only at hnt0 ⊢
  have htail_pc_ret : ∀ {u : PanSemStateFiniteExact 64 F},
      u.code = originalRuntimeCode →
      EvmInv u →
      (evmChain u).length = (evmChain s0).length →
      (if true then OpDispatchSpec.evmR u < OpDispatchSpec.evmR s0 else OpDispatchSpec.evmR u ≤ OpDispatchSpec.evmR s0) →
      (evaluateHOLFiniteState u
        (.seq (.call (some (none, none)) (ofString "pc_add") [.const 1#64])
          (.return (.const 0#64)))).1 ≠ some .timeOut →
      OpDispatchPost s0
        (evaluateHOLFiniteState u
          (.seq (.call (some (none, none)) (ofString "pc_add") [.const 1#64])
            (.return (.const 0#64)))).1
        (evaluateHOLFiniteState u
          (.seq (.call (some (none, none)) (ofString "pc_add") [.const 1#64])
            (.return (.const 0#64)))).2 := by
    intro u huc huI hul huR hunt
    exact (HandlerRun.seq_call_simple eps_pc_add (HandlerRun.ret _)) u huc huI hul huR trivial hunt
  by_cases hnz : nw = 0#64
  · simp only [hnz, not_true_eq_false, ↓reduceIte, evaluateHOLFiniteState_skip] at hnt0 ⊢
    exact htail_pc_ret hc0 hInv0 hlen0 hR0 hnt0
  · have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    have hcond_nz : (if nw ≠ 0#64 then (1 : BitVec 64) else 0) = 1 := if_pos hnz
    rw [hcond_nz, if_neg h10] at hnt0 ⊢
    obtain ⟨hsrc_win0, hdst_win0⟩ := hwin0 hnz
    have hrun_branch : HandlerRun s0
        (fun u =>
          u.locals.lookup (ofString "dst") = some dstVal ∧
          u.locals.lookup (ofString "src") = some srcVal ∧
          u.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
          sw.toNat + nw.toNat ≤ memW u (globN u "ev" + 32) ∧
          dw.toNat + nw.toNat ≤ memW u (globN u "ev" + 32))
        true
        (.seq
          (.decCall (ofString "d") .one (ofString "sat_word") [.var .local (ofString "dst")]
            (.decCall (ofString "s") .one (ofString "sat_word") [.var .local (ofString "src")]
              (.decCall (ofString "mark") .one (ofString "heap_mark") []
                (.decCall (ofString "tmp") .one (ofString "alloc") [.var .local (ofString "n")]
                  (.seq
                    (.call (some (none, none)) (ofString "memcpy")
                      [.var .local (ofString "tmp"),
                       .op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "s")],
                       .var .local (ofString "n")])
                    (.seq
                      (.call (some (none, none)) (ofString "memcpy")
                        [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "d")],
                         .var .local (ofString "tmp"),
                         .var .local (ofString "n")])
                      (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")])))))))
          (.seq
            (.call (some (none, none)) (ofString "pc_add") [.const 1#64])
            (.return (.const 0#64)))) := by
      clear hnt0 hcmp_n
      intro u0 huc0 huInv0 hulen0 huR0 huP0 hunt0
      obtain ⟨hudst, husrc, hun, husrc_w, hudst_w⟩ := huP0
      obtain ⟨da, db, dc, dd, hdst_eq⟩ := hdst4
      obtain ⟨sa, sb, sc, sd, hsrc_eq⟩ := hsrc4
      let sw_lookup : originalRuntimeCode.lookup (ofString "sat_word") =
          some ([(ofString "v", .comb [.one, .one, .one, .one])],
            sourceFnBody Guest.Software.guestFn_sat_word, .one) :=
        lookup_of_guestAst_getElem 440 (by rw [guestAst_len]; decide)
          (extractFn Guest.Software.guestFn_sat_word) rfl
      refine seq_step s0 u0 _ _ hunt0 ?_
      clear hunt0
      intro hnt_blk
      rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt_blk ⊢
      have hargs_d : evalListHOLFinite u0 (h := fun a => Classical.propDecidable (u0.memaddrs a))
          [.var .local (ofString "dst")] = some [dstVal] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hudst]
      rw [hargs_d] at hnt_blk ⊢; dsimp only at hnt_blk ⊢
      rcases hlk_d : lookupCodeHOLFinite u0.code.lookup (ofString "sat_word") [dstVal] with _ | ⟨body_d, cal_d, rs_d⟩
      · refine ⟨fun h => by simp at h, fun _ => ⟨fun _ h => by simp at h, ?_⟩⟩
        rintro ⟨_, h⟩; simp at h
      · rw [hlk_d] at hnt_blk; dsimp only at hnt_blk ⊢
        by_cases hclk_u0 : u0.clock = 0
        · simp [hclk_u0] at hnt_blk
        · simp only [hclk_u0, ↓reduceIte] at hnt_blk ⊢
          have hlk_d_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "sat_word") [dstVal] =
              some (body_d, cal_d, rs_d) := by rwa [← huc0]
          obtain ⟨rfl, rfl, hcal_d_v⟩ := one_u256_arg_lookup_g09 sw_lookup hlk_d_orig
          have hro_sw := installed_body_readOnly 440 (by rw [guestAst_len]; decide)
            Guest.Software.guestFn_sat_word rfl opRoCallees rfl hlk_d_orig
          have hsafe_d := evaluate_readOnlyProg opRoCallees opRoCallees_good
            (sourceFnBody Guest.Software.guestFn_sat_word) hro_sw
            (callEntryStateHOLFinite u0 cal_d) huc0
          have hnr_d : ¬ IsEvmErr (evaluateHOLFiniteState (callEntryStateHOLFinite u0 cal_d)
              (sourceFnBody Guest.Software.guestFn_sat_word)).1 := by
            let satCallees : MlS → Bool := fun f => f == ofString "sat_word"
            have hsat_good : ∀ function, satCallees function = true → ∀ values body callee rs,
                PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
                  some (body, callee, rs) →
                noRaiseProg satCallees body = true := by
              intro function hfn values body callee rs hfound
              obtain ⟨params, rs', hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
              simp only [satCallees, beq_iff_eq] at hfn; subst hfn
              rw [sw_lookup] at hinst
              have hbeq := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
              rw [← hbeq]; decide
            exact evaluate_noRaiseProg satCallees hsat_good _
              (hsat_good (ofString "sat_word") (by decide) [dstVal] _ cal_d .one hlk_d_orig)
              (callEntryStateHOLFinite u0 cal_d) huc0
          rcases hrun_d : evaluateHOLFiniteState (callEntryStateHOLFinite u0 cal_d)
              (sourceFnBody Guest.Software.guestFn_sat_word) with ⟨rd, sd_st⟩
          change evaluateHOLFiniteState (callEntryStateHOLFinite u0 cal_d)
              (sourceFnBody Guest.Software.guestFn_sat_word) = (rd, sd_st) at hrun_d
          simp only [hrun_d] at hnt_blk hsafe_d hnr_d ⊢
          cases rd with
          | none =>
            refine ⟨fun h => by simp at h, fun _ => ⟨fun _ h => by simp at h, ?_⟩⟩
            rintro ⟨_, h⟩; simp at h
          | some rd0 =>
            cases rd0 with
            | timeOut => simp at hnt_blk
            | «break» | «continue» | error | finalFfi _ =>
              refine ⟨fun h => by simp at h, fun _ => ⟨fun _ h => by simp at h, ?_⟩⟩
              rintro ⟨_, h⟩; simp at h
            | exception eid ev =>
              refine ⟨fun h => by simp at h, fun _ => ⟨fun _ h => by simp at h, ?_⟩⟩
              rintro ⟨v, h⟩; injection h with h'; injection h' with he hw
              exact hnr_d ⟨v, by rw [he, hw]⟩
            | returned vd =>
              have hvd_eq : vd = .val (.word dw) := by
                have hcal_d_v' : (callEntryStateHOLFinite u0 cal_d).locals.lookup (ofString "v") =
                    some (.rStruct [.val (.word da), .val (.word db), .val (.word dc), .val (.word dd)]) := by
                  rw [← hdst_eq]; exact hcal_d_v
                have hret_d := sat_word_body_exact_g09 (callEntryStateHOLFinite u0 cal_d) da db dc dd hcal_d_v' vd
                  (by rw [hrun_d])
                rw [← hdst_eq] at hret_d
                exact hret_d
              subst hvd_eq
              have hsh_dw : (shapeEqHOL (shapeOfHOLExact (.val (.word dw) : ValueHOL 64)) .one &&
                  shapeEqHOL (shapeOfHOLExact (.val (.word dw) : ValueHOL 64)) .one) = true := by
                simp [shapeOfHOLExact, shapeEqHOL]
              simp only [hsh_dw, ↓reduceIte] at hnt_blk ⊢
              have hlf_d : LocFrame (callEntryStateHOLFinite u0 cal_d) sd_st :=
                hsafe_d.to_resumes (Or.inl ⟨_, rfl⟩)
              set u1 := setVarHOLFinite (ofString "d") (.val (.word dw)) { sd_st with locals := u0.locals }
              have hu1_lf : LocFrame u0 u1 := by
                unfold LocFrame at hlf_d ⊢; simp only [u1, setVarHOLFinite]; rw [hlf_d]; cases u0; rfl
              have hu1_code : u1.code = originalRuntimeCode := by rw [hu1_lf]; exact huc0
              have hu1_Inv : EvmInv u1 := by
                have h := localsFree_evmInv u0 u1.locals u1.clock huInv0
                rwa [← hu1_lf] at h
              have hu1_src : u1.locals.lookup (ofString "src") = some srcVal := by
                simp [u1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, husrc,
                  show ofString "d" ≠ ofString "src" by decide]
              have hu1_n : u1.locals.lookup (ofString "n") = some (.val (.word nw)) := by
                simp [u1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hun,
                  show ofString "d" ≠ ofString "n" by decide]
              have hu1_d : u1.locals.lookup (ofString "d") = some (.val (.word dw)) := by
                simp [u1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              have hres_wrap_d : ∀ {r : Option (PanSemResultExact 64)} {st : PanSemStateFiniteExact 64 F},
                  ((r = none →
                    ∀ L,
                    (evaluateHOLFiniteState { st with locals := L }
                      (.seq (.call (some (none, none)) (ofString "pc_add") [.const 1#64]) (.return (.const 0#64)))).1 ≠ some .timeOut →
                    OpDispatchPost s0
                      (evaluateHOLFiniteState { st with locals := L }
                        (.seq (.call (some (none, none)) (ofString "pc_add") [.const 1#64]) (.return (.const 0#64)))).1
                      (evaluateHOLFiniteState { st with locals := L }
                        (.seq (.call (some (none, none)) (ofString "pc_add") [.const 1#64]) (.return (.const 0#64)))).2) ∧
                   (r ≠ none → (∀ rv, r ≠ some (.returned rv)) ∧ ¬ IsEvmErr r)) →
                  ((r = none →
                    (evaluateHOLFiniteState { st with locals := st.locals.resVarEq (ofString "d", u0.locals.lookup (ofString "d")) }
                      (.seq (.call (some (none, none)) (ofString "pc_add") [.const 1#64]) (.return (.const 0#64)))).1 ≠ some .timeOut →
                    OpDispatchPost s0
                      (evaluateHOLFiniteState { st with locals := st.locals.resVarEq (ofString "d", u0.locals.lookup (ofString "d")) }
                        (.seq (.call (some (none, none)) (ofString "pc_add") [.const 1#64]) (.return (.const 0#64)))).1
                      (evaluateHOLFiniteState { st with locals := st.locals.resVarEq (ofString "d", u0.locals.lookup (ofString "d")) }
                        (.seq (.call (some (none, none)) (ofString "pc_add") [.const 1#64]) (.return (.const 0#64)))).2) ∧
                   (r ≠ none → (∀ rv, r ≠ some (.returned rv)) ∧ ¬ IsEvmErr r)) := by
                intro r st hpair
                exact ⟨fun hr => hpair.1 hr _, hpair.2⟩
              apply hres_wrap_d
              have hnt_u1 : (evaluateHOLFiniteState u1
                  (.decCall (ofString "s") .one (ofString "sat_word") [.var .local (ofString "src")]
                    (.decCall (ofString "mark") .one (ofString "heap_mark") []
                      (.decCall (ofString "tmp") .one (ofString "alloc") [.var .local (ofString "n")]
                        (.seq
                          (.call (some (none, none)) (ofString "memcpy")
                            [.var .local (ofString "tmp"),
                             .op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "s")],
                             .var .local (ofString "n")])
                          (.seq
                            (.call (some (none, none)) (ofString "memcpy")
                              [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "d")],
                               .var .local (ofString "tmp"),
                               .var .local (ofString "n")])
                            (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")]))))))).1 ≠ some .timeOut := hnt_blk
              clear hnt_blk
              rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt_u1 ⊢
              have hargs_s : evalListHOLFinite u1 (h := fun a => Classical.propDecidable (u1.memaddrs a))
                  [.var .local (ofString "src")] = some [srcVal] := by
                simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hu1_src]
              rw [hargs_s] at hnt_u1 ⊢; dsimp only at hnt_u1 ⊢
              rcases hlk_s : lookupCodeHOLFinite u1.code.lookup (ofString "sat_word") [srcVal] with _ | ⟨body_s, cal_s, rs_s⟩
              · refine ⟨fun h => by simp at h, fun _ => ⟨fun _ h => by simp at h, ?_⟩⟩
                rintro ⟨_, h⟩; simp at h
              · rw [hlk_s] at hnt_u1; dsimp only at hnt_u1 ⊢
                by_cases hclk_u1 : u1.clock = 0
                · simp [hclk_u1] at hnt_u1
                · simp only [hclk_u1, ↓reduceIte] at hnt_u1 ⊢
                  have hlk_s_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "sat_word") [srcVal] =
                      some (body_s, cal_s, rs_s) := by rwa [← hu1_code]
                  obtain ⟨rfl, rfl, hcal_s_v⟩ := one_u256_arg_lookup_g09 sw_lookup hlk_s_orig
                  have hro_sw_s := installed_body_readOnly 440 (by rw [guestAst_len]; decide)
                    Guest.Software.guestFn_sat_word rfl opRoCallees rfl hlk_s_orig
                  have hsafe_s := evaluate_readOnlyProg opRoCallees opRoCallees_good
                    (sourceFnBody Guest.Software.guestFn_sat_word) hro_sw_s
                    (callEntryStateHOLFinite u1 cal_s) hu1_code
                  have hnr_s : ¬ IsEvmErr (evaluateHOLFiniteState (callEntryStateHOLFinite u1 cal_s)
                      (sourceFnBody Guest.Software.guestFn_sat_word)).1 := by
                    let satCallees : MlS → Bool := fun f => f == ofString "sat_word"
                    have hsat_good : ∀ function, satCallees function = true → ∀ values body callee rs,
                        PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
                          some (body, callee, rs) →
                        noRaiseProg satCallees body = true := by
                      intro function hfn values body callee rs hfound
                      obtain ⟨params, rs', hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
                      simp only [satCallees, beq_iff_eq] at hfn; subst hfn
                      rw [sw_lookup] at hinst
                      have hbeq := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
                      rw [← hbeq]; decide
                    exact evaluate_noRaiseProg satCallees hsat_good _
                      (hsat_good (ofString "sat_word") (by decide) [srcVal] _ cal_s .one hlk_s_orig)
                      (callEntryStateHOLFinite u1 cal_s) hu1_code
                  rcases hrun_s : evaluateHOLFiniteState (callEntryStateHOLFinite u1 cal_s)
                      (sourceFnBody Guest.Software.guestFn_sat_word) with ⟨rs_res, ss_st⟩
                  change evaluateHOLFiniteState (callEntryStateHOLFinite u1 cal_s)
                      (sourceFnBody Guest.Software.guestFn_sat_word) = (rs_res, ss_st) at hrun_s
                  simp only [hrun_s] at hnt_u1 hsafe_s hnr_s ⊢
                  cases rs_res with
                  | none =>
                    refine ⟨fun h => by simp at h, fun _ => ⟨fun _ h => by simp at h, ?_⟩⟩
                    rintro ⟨_, h⟩; simp at h
                  | some rs0 =>
                    cases rs0 with
                    | timeOut => simp at hnt_u1
                    | «break» | «continue» | error | finalFfi _ =>
                      refine ⟨fun h => by simp at h, fun _ => ⟨fun _ h => by simp at h, ?_⟩⟩
                      rintro ⟨_, h⟩; simp at h
                    | exception eid ev =>
                      refine ⟨fun h => by simp at h, fun _ => ⟨fun _ h => by simp at h, ?_⟩⟩
                      rintro ⟨v, h⟩; injection h with h'; injection h' with he hw
                      exact hnr_s ⟨v, by rw [he, hw]⟩
                    | returned vs =>
                      have hvs_eq : vs = .val (.word sw) := by
                        have hcal_s_v' : (callEntryStateHOLFinite u1 cal_s).locals.lookup (ofString "v") =
                            some (.rStruct [.val (.word sa), .val (.word sb), .val (.word sc), .val (.word sd)]) := by
                          rw [← hsrc_eq]; exact hcal_s_v
                        have hret_s := sat_word_body_exact_g09 (callEntryStateHOLFinite u1 cal_s) sa sb sc sd hcal_s_v' vs
                          (by rw [hrun_s])
                        rw [← hsrc_eq] at hret_s
                        exact hret_s
                      subst hvs_eq
                      have hsh_sw : (shapeEqHOL (shapeOfHOLExact (.val (.word sw) : ValueHOL 64)) .one &&
                          shapeEqHOL (shapeOfHOLExact (.val (.word sw) : ValueHOL 64)) .one) = true := by
                        simp [shapeOfHOLExact, shapeEqHOL]
                      simp only [hsh_sw, ↓reduceIte] at hnt_u1 ⊢
                      have hlf_s : LocFrame (callEntryStateHOLFinite u1 cal_s) ss_st :=
                        hsafe_s.to_resumes (Or.inl ⟨_, rfl⟩)
                      set u2 := setVarHOLFinite (ofString "s") (.val (.word sw)) { ss_st with locals := u1.locals }
                      have hu2_lf : LocFrame u0 u2 := by
                        have h12 : LocFrame u1 u2 := by
                          unfold LocFrame at hlf_s ⊢; simp only [u2, setVarHOLFinite]; rw [hlf_s]; cases u1; rfl
                        exact hu1_lf.trans h12
                      have hu2_code : u2.code = originalRuntimeCode := by rw [hu2_lf]; exact huc0
                      have hu2_Inv : EvmInv u2 := by
                        have h := localsFree_evmInv u0 u2.locals u2.clock huInv0
                        rwa [← hu2_lf] at h
                      have hu2_n : u2.locals.lookup (ofString "n") = some (.val (.word nw)) := by
                        simp [u2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu1_n,
                          show ofString "s" ≠ ofString "n" by decide]
                      have hu2_d : u2.locals.lookup (ofString "d") = some (.val (.word dw)) := by
                        simp [u2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu1_d,
                          show ofString "s" ≠ ofString "d" by decide]
                      have hu2_s : u2.locals.lookup (ofString "s") = some (.val (.word sw)) := by
                        simp [u2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                      have hhp_mem : "heap_ptr" ∈ guestGlobalNames := by decide
                      obtain ⟨markw, hmark_gw⟩ := hu2_Inv.1.2.2.2.2.2.2.2.2.2 "heap_ptr" hhp_mem
                      have hmark_lk : u2.globals.lookup (ofString "heap_ptr") = some (.val (.word markw)) := hmark_gw
                      have hmark_nat : markw.toNat = globN u2 "heap_ptr" := by simp [globN, hmark_lk]
                      have hmark_le : markw.toNat ≤ InitECandidate.Solver.HeapPotential.cMax.toNat := by
                        rw [hmark_nat]; exact hu2_Inv.1.2.2.1
                      have hmark_8 : markw.toNat % 8 = 0 := by
                        rw [hmark_nat]; exact hu2_Inv.1.2.2.2.2.2.2.1
                      have hnt_u2 : (evaluateHOLFiniteState u2
                          (.decCall (ofString "mark") .one (ofString "heap_mark") []
                            (.decCall (ofString "tmp") .one (ofString "alloc") [.var .local (ofString "n")]
                              (.seq
                                (.call (some (none, none)) (ofString "memcpy")
                                  [.var .local (ofString "tmp"),
                                   .op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "s")],
                                   .var .local (ofString "n")])
                                (.seq
                                  (.call (some (none, none)) (ofString "memcpy")
                                    [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "d")],
                                     .var .local (ofString "tmp"),
                                     .var .local (ofString "n")])
                                  (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")])))))).1 ≠ some .timeOut := hnt_u1
                      clear hnt_u1
                      rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt_u2 ⊢
                      have hargs_hm : evalListHOLFinite u2 (h := fun a => Classical.propDecidable (u2.memaddrs a)) [] = some [] := rfl
                      have hlook_hm := pan_zero_arg_lookup u2.code.lookup (ofString "heap_mark")
                        (sourceFnBody Guest.Software.guestFn_heap_mark) .one (by rw [hu2_code]; exact lookup_heap_mark)
                      rw [hargs_hm] at hnt_u2 ⊢; dsimp only at hnt_u2 ⊢
                      rw [hlook_hm] at hnt_u2 ⊢; dsimp only at hnt_u2 ⊢
                      by_cases hclk_u2 : u2.clock = 0
                      · simp [hclk_u2] at hnt_u2
                      · simp only [hclk_u2, ↓reduceIte] at hnt_u2 ⊢
                        have hhm_body : evaluateHOLFiniteState (callEntryStateHOLFinite u2 HolFiniteMapExact.empty)
                            (sourceFnBody Guest.Software.guestFn_heap_mark) =
                            (some (.returned (.val (.word markw))),
                             emptyLocalsHOLFinite (callEntryStateHOLFinite u2 HolFiniteMapExact.empty)) := by
                          dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_heap_mark,
                            InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
                            InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
                            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
                            InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural]
                          rw [evaluateHOLFiniteState_return]
                          have hev_hp : @evalHOLExact 64 F _ (callEntryStateHOLFinite u2 HolFiniteMapExact.empty).toExact
                              (fun a => Classical.propDecidable ((callEntryStateHOLFinite u2 HolFiniteMapExact.empty).memaddrs a))
                              (.var .global (ofString "heap_ptr")) = some (.val (.word markw)) := hmark_lk
                          rw [hev_hp]; dsimp only
                          have hsz : sizeOfShapeWithContextHOL (callEntryStateHOLFinite u2 HolFiniteMapExact.empty).structs
                              (shapeOfHOLExact (.val (.word markw) : ValueHOL 64)) ≤ 32 := by
                            simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
                          rw [if_pos hsz]
                        rw [hhm_body] at hnt_u2 ⊢; dsimp only at hnt_u2 ⊢
                        have hsh_mw : (shapeEqHOL (shapeOfHOLExact (.val (.word markw) : ValueHOL 64)) .one &&
                            shapeEqHOL (shapeOfHOLExact (.val (.word markw) : ValueHOL 64)) .one) = true := by
                          simp [shapeOfHOLExact, shapeEqHOL]
                        simp only [hsh_mw, ↓reduceIte] at hnt_u2 ⊢
                        set u3 := setVarHOLFinite (ofString "mark") (.val (.word markw))
                          { emptyLocalsHOLFinite (callEntryStateHOLFinite u2 HolFiniteMapExact.empty) with locals := u2.locals }
                        have hu3_n : u3.locals.lookup (ofString "n") = some (.val (.word nw)) := by
                          simp [u3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu2_n,
                            show ofString "mark" ≠ ofString "n" by decide]
                        have hu3_d : u3.locals.lookup (ofString "d") = some (.val (.word dw)) := by
                          simp [u3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu2_d,
                            show ofString "mark" ≠ ofString "d" by decide]
                        have hu3_s : u3.locals.lookup (ofString "s") = some (.val (.word sw)) := by
                          simp [u3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu2_s,
                            show ofString "mark" ≠ ofString "s" by decide]
                        have hu3_mark : u3.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
                          simp [u3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                        have hnt_u3 : (evaluateHOLFiniteState u3
                            (.decCall (ofString "tmp") .one (ofString "alloc") [.var .local (ofString "n")]
                              (.seq
                                (.call (some (none, none)) (ofString "memcpy")
                                  [.var .local (ofString "tmp"),
                                   .op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "s")],
                                   .var .local (ofString "n")])
                                (.seq
                                  (.call (some (none, none)) (ofString "memcpy")
                                    [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "d")],
                                     .var .local (ofString "tmp"),
                                     .var .local (ofString "n")])
                                  (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")]))))).1 ≠ some .timeOut := hnt_u2
                        clear hnt_u2
                        rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt_u3 ⊢
                        have hargs_al : evalListHOLFinite u3 (h := fun a => Classical.propDecidable (u3.memaddrs a))
                            [.var .local (ofString "n")] = some [.val (.word nw)] := by
                          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hu3_n]
                        have hlook_al := pan_one_word_lookup u3.code.lookup (ofString "alloc") (ofString "n")
                          (sourceFnBody Guest.Software.guestFn_alloc) nw
                          (by change u2.code.lookup _ = _; rw [hu2_code]; exact OpHandlers.lookup_alloc)
                        rw [hargs_al] at hnt_u3 ⊢; dsimp only at hnt_u3 ⊢
                        rw [hlook_al] at hnt_u3 ⊢; dsimp only at hnt_u3 ⊢
                        by_cases hclk_u3 : u3.clock = 0
                        · simp [hclk_u3] at hnt_u3
                        · simp only [hclk_u3, ↓reduceIte] at hnt_u3 ⊢
                          let cal_al := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word nw))
                          let ent_al := callEntryStateHOLFinite u3 cal_al
                          have hne_al : ¬ IsEvmErr (evaluateHOLFiniteState ent_al (sourceFnBody Guest.Software.guestFn_alloc)).1 :=
                            alloc_body_no_evmErr ent_al hu2_code
                          have hal_gen := Wave8GuestInv.M13.evaluate_alloc_body_general ent_al markw nw hu2_code hmark_le hmark_lk
                            (by simp [ent_al, cal_al, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
                          have hal_meta := PanRunBounded.evaluateHOLFiniteState_metadata ent_al (sourceFnBody Guest.Software.guestFn_alloc)
                          have hal_ba := evaluate_baseAddr ent_al (sourceFnBody Guest.Software.guestFn_alloc)
                          rcases hrun_al : evaluateHOLFiniteState ent_al (sourceFnBody Guest.Software.guestFn_alloc) with ⟨ral, sal⟩
                          change evaluateHOLFiniteState ent_al (sourceFnBody Guest.Software.guestFn_alloc) = (ral, sal) at hrun_al
                          simp only [ent_al, cal_al, hrun_al] at hnt_u3 hne_al hal_gen hal_meta hal_ba ⊢
                          cases ral with
                          | none =>
                            refine ⟨fun h => by simp at h, fun _ => ⟨fun _ h => by simp at h, ?_⟩⟩
                            rintro ⟨_, h⟩; simp at h
                          | some ral0 =>
                            cases ral0 with
                            | timeOut => simp at hnt_u3
                            | «break» | «continue» | error | finalFfi _ =>
                              refine ⟨fun h => by simp at h, fun _ => ⟨fun _ h => by simp at h, ?_⟩⟩
                              rintro ⟨_, h⟩; simp at h
                            | exception eid ev =>
                              refine ⟨fun h => by simp at h, fun _ => ⟨fun _ h => by simp at h, ?_⟩⟩
                              rintro ⟨v, h⟩; injection h with h'; injection h' with he hw
                              exact hne_al ⟨v, by rw [he, hw]⟩
                            | returned val_al =>
                              obtain ⟨rfl, hsal_glob, hsal_mem, hq_ge, hq_le_cMax, hq_mod8⟩ := hal_gen val_al rfl
                              let q : BitVec 64 := (markw + (nw + 7)) &&& ((0 : BitVec 64) - 8)
                              change markw.toNat + nw.toNat ≤ q.toNat at hq_ge
                              change q.toNat ≤ InitECandidate.Solver.HeapPotential.cMax.toNat at hq_le_cMax
                              change q.toNat % 8 = 0 at hq_mod8
                              have hsh_al : (shapeEqHOL (shapeOfHOLExact (.val (.word markw) : ValueHOL 64)) .one &&
                                  shapeEqHOL (shapeOfHOLExact (.val (.word markw) : ValueHOL 64)) .one) = true := by
                                simp [shapeOfHOLExact, shapeEqHOL]
                              simp only [hsh_al, ↓reduceIte] at hnt_u3 ⊢
                              set u4 := setVarHOLFinite (ofString "tmp") (.val (.word markw)) { sal with locals := u3.locals }
                              have hu4_code : u4.code = originalRuntimeCode := hal_meta.1.trans hu2_code
                              have hu4_ma : u4.memaddrs = ordinaryDomain := hal_meta.2.1.trans hu2_Inv.1.1.memaddrs
                              have hu4_be : u4.be = u2.be := hal_meta.2.2.1
                              have hu4_sh : u4.shMemaddrs = u2.shMemaddrs := hal_meta.2.2.2.1
                              have hu4_ba : u4.baseAddr = u2.baseAddr := hal_ba
                              have hu4_glob : u4.globals = u2.globals.update (ofString "heap_ptr", .val (.word q)) := hsal_glob
                              have hu4_mem : u4.memory = u2.memory := hsal_mem
                              have hu4_tmp : u4.locals.lookup (ofString "tmp") = some (.val (.word markw)) := by
                                simp [u4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                              have hu4_n : u4.locals.lookup (ofString "n") = some (.val (.word nw)) := by
                                simp [u4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu3_n,
                                  show ofString "tmp" ≠ ofString "n" by decide]
                              have hu4_d : u4.locals.lookup (ofString "d") = some (.val (.word dw)) := by
                                simp [u4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu3_d,
                                  show ofString "tmp" ≠ ofString "d" by decide]
                              have hu4_s : u4.locals.lookup (ofString "s") = some (.val (.word sw)) := by
                                simp [u4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu3_s,
                                  show ofString "tmp" ≠ ofString "s" by decide]
                              have hu4_mark : u4.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
                                simp [u4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu3_mark,
                                  show ofString "tmp" ≠ ofString "mark" by decide]
                              obtain ⟨hb_ev, evw, hevw, hevw_nat⟩ := ev_word_bounds hu2_Inv
                              have hhead_mem : (globN u2 "ev", globN u2 "cur_cont") ∈ evmChain u2 := by
                                simp [evmChain, evmChainFrom]
                              have hFW0 := hu2_Inv.2.choose_spec.2.2.2.2.1 _ hhead_mem
                              have hmem_cap_le : memW u2 (globN u2 "ev" + 32) ≤ memW u2 (globN u2 "ev" + 40) :=
                                hFW0.2.2.2.2.2.2.1
                              have hmem_in : Inside (memW u2 (globN u2 "ev" + 24), memW u2 (globN u2 "ev" + 40))
                                  scratchStart (globN u2 "frame_mem_ptr") :=
                                hFW0.2.1
                              have hss_le_sp : scratchStart ≤ globN u2 "scratch_ptr" :=
                                le_trans hu2_Inv.1.2.2.2.1 hu2_Inv.1.2.2.2.2.1
                              have hfp_le_se : globN u2 "frame_mem_ptr" ≤ scratchEnd :=
                                le_trans hu2_Inv.1.2.2.2.2.1 hu2_Inv.1.2.2.2.2.2.1
                              have hse_lt64 : scratchEnd < 2 ^ 64 := by
                                rw [R11Shards.scratchEnd_val]; decide
                              have hu2_u0_mem : u2.memory = u0.memory := by unfold LocFrame at hu2_lf; rw [hu2_lf]
                              have hu2_u0_glob : u2.globals = u0.globals := by unfold LocFrame at hu2_lf; rw [hu2_lf]
                              have husrc_w2 : sw.toNat + nw.toNat ≤ memW u2 (globN u2 "ev" + 32) := by
                                unfold memW globN; rw [hu2_u0_mem, hu2_u0_glob]; exact husrc_w
                              have hudst_w2 : dw.toNat + nw.toNat ≤ memW u2 (globN u2 "ev" + 32) := by
                                unfold memW globN; rw [hu2_u0_mem, hu2_u0_glob]; exact hudst_w
                              have hu4_ev : u4.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
                                rw [hu4_glob]
                                simp [HolFiniteMapExact.lookup_update, FUPDATE, hevw,
                                  show ofString "heap_ptr" ≠ ofString "ev" by decide]
                              have hev24_eq : evw + 24#64 = BitVec.ofNat 64 (globN u2 "ev" + 24) := by
                                apply BitVec.eq_of_toNat_eq
                                have : (24#64 : BitVec 64).toNat = 24 := rfl
                                rw [BitVec.toNat_add, hevw_nat, this, BitVec.toNat_ofNat]
                              have hu2_dom24 : u2.memaddrs (evw + 24#64) := by
                                rw [hev24_eq]
                                exact ((hFW0.1 (globN u2 "ev", 280) (by simp)).2.2.2 3 (by omega)).choose_spec.1
                              have hu4_dom24 : u4.memaddrs (evw + 24#64) := by
                                rw [hu4_ma, ← hu2_Inv.1.1.memaddrs]; exact hu2_dom24
                              rcases hm24 : u2.memory (evw + 24#64) with ⟨memPtrW⟩
                              have hmemPtrW_nat : memPtrW.toNat = memW u2 (globN u2 "ev" + 24) := by
                                unfold memW; rw [← hev24_eq, hm24]
                              have hu4_m24 : u4.memory (evw + 24#64) = .word memPtrW := by
                                rw [hu4_mem, hm24]
                              let srcPtrExp : ExpHOL 64 :=
                                .op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "s")]
                              let dstPtrExp : ExpHOL 64 :=
                                .op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "d")]
                              let heapIvl : Ivl := (markw.toNat, q.toNat - markw.toNat)
                              let memIvl : Ivl := (memW u2 (globN u2 "ev" + 24), memW u2 (globN u2 "ev" + 40))
                              have hev_mc1_dst : @evalHOLExact 64 F _ u4.toExact (fun a => Classical.propDecidable (u4.memaddrs a))
                                  (.var .local (ofString "tmp")) = some (.val (.word markw)) := hu4_tmp
                              have hev_mc1_src : @evalHOLExact 64 F _ u4.toExact (fun a => Classical.propDecidable (u4.memaddrs a))
                                  srcPtrExp = some (.val (.word (memPtrW + sw))) := by
                                simp [srcPtrExp, evalHOLExact, evalListHOLExact, hu4_ev, hu4_s, wordOpHOL, wordOp,
                                  valueIsWord, valueWord, memLoadHOLExact, hu4_dom24, hu4_m24]
                              have hev_mc1_n : @evalHOLExact 64 F _ u4.toExact (fun a => Classical.propDecidable (u4.memaddrs a))
                                  (.var .local (ofString "n")) = some (.val (.word nw)) := hu4_n
                              have hnt_u4 : (evaluateHOLFiniteState u4
                                  (.seq
                                    (.call (some (none, none)) (ofString "memcpy")
                                      [.var .local (ofString "tmp"), srcPtrExp, .var .local (ofString "n")])
                                    (.seq
                                      (.call (some (none, none)) (ofString "memcpy")
                                        [dstPtrExp, .var .local (ofString "tmp"), .var .local (ofString "n")])
                                      (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")])))).1 ≠ some .timeOut := hnt_u3
                              clear hnt_u3
                              rw [evaluateHOLFiniteState_seq_line780] at hnt_u4 ⊢
                              rcases hmc1_run : evaluateHOLFiniteState u4
                                  (.call (some (none, none)) (ofString "memcpy")
                                    [.var .local (ofString "tmp"), srcPtrExp, .var .local (ofString "n")]) with ⟨rmc1, u5⟩
                              change evaluateHOLFiniteState u4
                                  (.call (some (none, none)) (ofString "memcpy")
                                    [.var .local (ofString "tmp"), srcPtrExp, .var .local (ofString "n")]) = (rmc1, u5) at hmc1_run
                              have hnt_mc1 : rmc1 ≠ some .timeOut := by
                                rintro rfl; simp [srcPtrExp, hmc1_run] at hnt_u4
                              have hmc1 := Wave8GuestInv.M11.eval_call_memcpy_bre u4
                                (.var .local (ofString "tmp")) srcPtrExp (.var .local (ofString "n"))
                                markw (memPtrW + sw) nw [heapIvl] hu4_code hu4_ma
                                hev_mc1_dst hev_mc1_src hev_mc1_n
                                (fun _ => ⟨heapIvl, by simp, by dsimp only [heapIvl]; omega, by dsimp only [heapIvl]; omega⟩)
                                (by rw [hmc1_run]; exact hnt_mc1)
                              dsimp only at hmc1; rw [hmc1_run] at hmc1
                              simp only [srcPtrExp, hmc1_run] at hnt_u4 ⊢
                              cases rmc1 with
                              | some rmc1_0 =>
                                dsimp only
                                have hnr1 := hmc1.2 (by simp)
                                refine ⟨fun h => by simp at h, fun _ => ⟨fun rv hrv => hnr1 (Or.inl ⟨rv, hrv⟩), ?_⟩⟩
                                rintro ⟨ev, hv⟩; injection hv with hv'; subst hv'
                                exact hnr1 (Or.inr ⟨ofString "EvmErr", ev, rfl, by decide⟩)
                              | none =>
                                dsimp only at hnt_u4 ⊢
                                obtain ⟨heff_mc1, hu5_loc⟩ := hmc1.1 rfl
                                have hu5_code : u5.code = originalRuntimeCode := heff_mc1.code.trans hu4_code
                                have hu5_ma : u5.memaddrs = ordinaryDomain := heff_mc1.memaddrs.trans hu4_ma
                                have hu5_ev : u5.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
                                  rw [heff_mc1.globals]; exact hu4_ev
                                have hu5_dom24 : u5.memaddrs (evw + 24#64) := by
                                  rw [hu5_ma]; exact hu4_ma ▸ hu4_dom24
                                have hu5_m24 : u5.memory (evw + 24#64) = .word memPtrW := by
                                  rw [heff_mc1.cell_frame (evw + 24#64)]
                                  · exact hu4_m24
                                  · intro i hi
                                    simp at hi; subst hi
                                    have htn24 : (evw + 24#64).toNat = globN u2 "ev" + 24 := by
                                      rw [hev24_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                                    rw [htn24]
                                    obtain ⟨he0_scr, _⟩ := (hFW0.1 (globN u2 "ev", 280) (by simp)).1
                                    have hcMax_le_scr : InitECandidate.Solver.HeapPotential.cMax.toNat ≤ scratchStart := by
                                      have hcMax_val : InitECandidate.Solver.HeapPotential.cMax.toNat = 2952790016 := rfl
                                      rw [R11Shards.scratchStart_val, hcMax_val]
                                    intro ⟨hc1, hc2⟩
                                    dsimp only [heapIvl, Inside] at hc1 hc2 he0_scr
                                    omega
                                have hu5_tmp : u5.locals.lookup (ofString "tmp") = some (.val (.word markw)) := by
                                  rw [hu5_loc]; exact hu4_tmp
                                have hu5_n : u5.locals.lookup (ofString "n") = some (.val (.word nw)) := by
                                  rw [hu5_loc]; exact hu4_n
                                have hu5_d : u5.locals.lookup (ofString "d") = some (.val (.word dw)) := by
                                  rw [hu5_loc]; exact hu4_d
                                have hu5_mark : u5.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
                                  rw [hu5_loc]; exact hu4_mark
                                have hev_mc2_dst : @evalHOLExact 64 F _ u5.toExact (fun a => Classical.propDecidable (u5.memaddrs a))
                                    dstPtrExp = some (.val (.word (memPtrW + dw))) := by
                                  simp [dstPtrExp, evalHOLExact, evalListHOLExact, hu5_ev, hu5_d, wordOpHOL, wordOp,
                                    valueIsWord, valueWord, memLoadHOLExact, hu5_dom24, hu5_m24]
                                have hev_mc2_src : @evalHOLExact 64 F _ u5.toExact (fun a => Classical.propDecidable (u5.memaddrs a))
                                    (.var .local (ofString "tmp")) = some (.val (.word markw)) := hu5_tmp
                                have hev_mc2_n : @evalHOLExact 64 F _ u5.toExact (fun a => Classical.propDecidable (u5.memaddrs a))
                                    (.var .local (ofString "n")) = some (.val (.word nw)) := hu5_n
                                have hdst_nat2 : (memPtrW + dw).toNat = memW u2 (globN u2 "ev" + 24) + dw.toNat := by
                                  dsimp only [Inside] at hmem_in
                                  rw [BitVec.toNat_add, hmemPtrW_nat, Nat.mod_eq_of_lt (by omega)]
                                rw [evaluateHOLFiniteState_seq_line780] at hnt_u4 ⊢
                                rcases hmc2_run : evaluateHOLFiniteState u5
                                    (.call (some (none, none)) (ofString "memcpy")
                                      [dstPtrExp, .var .local (ofString "tmp"), .var .local (ofString "n")]) with ⟨rmc2, u6⟩
                                change evaluateHOLFiniteState u5
                                    (.call (some (none, none)) (ofString "memcpy")
                                      [dstPtrExp, .var .local (ofString "tmp"), .var .local (ofString "n")]) = (rmc2, u6) at hmc2_run
                                have hnt_mc2 : rmc2 ≠ some .timeOut := by
                                  rintro rfl; simp [dstPtrExp, hmc2_run] at hnt_u4
                                have hmc2 := Wave8GuestInv.M11.eval_call_memcpy_bre u5
                                  dstPtrExp (.var .local (ofString "tmp")) (.var .local (ofString "n"))
                                  (memPtrW + dw) markw nw [memIvl] hu5_code hu5_ma
                                  hev_mc2_dst hev_mc2_src hev_mc2_n
                                  (fun _ => ⟨memIvl, by simp,
                                    by dsimp only [memIvl]; rw [hdst_nat2]; omega,
                                    by dsimp only [memIvl]; rw [hdst_nat2]; omega⟩)
                                  (by rw [hmc2_run]; exact hnt_mc2)
                                dsimp only at hmc2; rw [hmc2_run] at hmc2
                                simp only [dstPtrExp, hmc2_run] at hnt_u4 ⊢
                                cases rmc2 with
                                | some rmc2_0 =>
                                  dsimp only
                                  have hnr2 := hmc2.2 (by simp)
                                  refine ⟨fun h => by simp at h, fun _ => ⟨fun rv hrv => hnr2 (Or.inl ⟨rv, hrv⟩), ?_⟩⟩
                                  rintro ⟨ev, hv⟩; injection hv with hv'; subst hv'
                                  exact hnr2 (Or.inr ⟨ofString "EvmErr", ev, rfl, by decide⟩)
                                | none =>
                                  dsimp only at hnt_u4 ⊢
                                  obtain ⟨heff_mc2, hu6_loc⟩ := hmc2.1 rfl
                                  have hu6_code : u6.code = originalRuntimeCode := heff_mc2.code.trans hu5_code
                                  have hu6_mark : u6.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
                                    rw [hu6_loc]; exact hu5_mark
                                  rw [evaluateHOLFiniteState_call] at hnt_u4 ⊢
                                  have hargs_hr : evalListHOLFinite u6
                                      (h := fun a => Classical.propDecidable (u6.memaddrs a))
                                      [.var .local (ofString "mark")] = some [.val (.word markw)] := by
                                    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hu6_mark]
                                  have hlook_hr := pan_one_word_lookup u6.code.lookup (ofString "heap_release")
                                    (ofString "m") (sourceFnBody Guest.Software.guestFn_heap_release) markw
                                    (by rw [hu6_code]; exact lookup_heap_release)
                                  rw [hargs_hr] at hnt_u4 ⊢; dsimp only at hnt_u4 ⊢
                                  rw [hlook_hr] at hnt_u4 ⊢; dsimp only at hnt_u4 ⊢
                                  by_cases hclk_u6 : u6.clock = 0
                                  · simp [hclk_u6] at hnt_u4
                                  · simp only [hclk_u6, ↓reduceIte] at hnt_u4 ⊢
                                    let cal_hr := HolFiniteMapExact.empty.update (ofString "m", ValueHOL.val (.word markw))
                                    let ent_hr := callEntryStateHOLFinite u6 cal_hr
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
                                      have hlk_hp6 : ent_hr.globals.lookup (ofString "heap_ptr") = some (.val (.word q)) := by
                                        have hg6 : ent_hr.globals = u4.globals := by
                                          change u6.globals = u4.globals
                                          rw [heff_mc2.globals, heff_mc1.globals]
                                        rw [hg6, hu4_glob]
                                        simp [HolFiniteMapExact.lookup_update, FUPDATE]
                                      simp [evalHOLExact, hm_loc, isValidValueHOLFinite, isValidValueHOLExact,
                                        lookupKvarHOLFinite, lookupKvarHOLExact, hlk_hp6,
                                        shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite,
                                        evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
                                    rw [hhr_body]; dsimp only
                                    have hsh0_one : shapeEqHOL (shapeOfHOLExact (.val (.word (0 : BitVec 64)) : ValueHOL 64)) .one = true := by
                                      simp [shapeOfHOLExact, shapeEqHOL]
                                    rw [if_pos hsh0_one]; dsimp only
                                    refine ⟨?_, fun hne => absurd rfl hne⟩
                                    intro _ L hnt_fin
                                    let u5_mid : PanSemStateFiniteExact 64 F := { u5 with globals := u2.globals }
                                    have heff_u2_mid : ByteRegionEffect u2 u5_mid [heapIvl] := by
                                      refine ⟨(heff_mc1.code.trans hu4_code).trans hu2_code.symm,
                                        (heff_mc1.memaddrs.trans hu4_ma).trans hu2_Inv.1.1.memaddrs.symm,
                                        heff_mc1.shMemaddrs.trans hu4_sh,
                                        heff_mc1.baseAddr.trans hu4_ba,
                                        heff_mc1.be.trans hu4_be,
                                        rfl, ?_, ?_, ?_⟩
                                      · intro a hna
                                        have hna4 : ¬ u4.memaddrs a := by
                                          rw [hu4_ma, ← hu2_Inv.1.1.memaddrs]; exact hna
                                        change u5.memory a = u2.memory a
                                        rw [heff_mc1.out_dom a hna4, hu4_mem]
                                      · intro a ha
                                        change u5.memory a = u2.memory a
                                        rw [heff_mc1.cell_frame a ha, hu4_mem]
                                      · intro b hb hno
                                        have hmb5 : memB u5_mid b = memB u5 b := rfl
                                        have hmb4 : memB u4 b = memB u2 b := by unfold memB; rw [hu4_mem, hu4_be]
                                        rw [hmb5, heff_mc1.byte_frame b hb hno, hmb4]
                                    have hInv_mid : EvmInv u5_mid ∧ evmChain u5_mid = evmChain u2 ∧ OpDispatchSpec.evmR u5_mid = OpDispatchSpec.evmR u2 := by
                                      obtain ⟨hAt, S_t, hInvAt_t⟩ := hu2_Inv
                                      have hWt := hInvAt_t.1
                                      have hFW_all := hInvAt_t.2.2.2.2.1
                                      have hAT := hInvAt_t.2.2.2.2.2.2.2.2.2.1
                                      obtain ⟨Nd1, hTr1⟩ := hWt.2.2.2
                                      obtain ⟨Nd2, hTr2, hAT2⟩ := hAT
                                      obtain ⟨hTr_int, hne_int⟩ := R11Shards.triesTypedWith_inter hTr1 hTr2
                                      set Nd := Nd1.filter (fun n => decide (n ∈ Nd2))
                                      have hAT_Nd : ∀ o ∈ ((evmChain u2).map (frameObjects u2)).flatten, ∀ j ∈ nodeExtents u2 Nd, Disj o j :=
                                        fun o ho j hj => hAT2 o ho j (hne_int j hj).2
                                      have hx_in : Inside heapIvl (globN u2 "heap_ptr") heapLimit := by
                                        refine ⟨by dsimp only [heapIvl]; omega, ?_⟩
                                        dsimp only [heapIvl]
                                        have hcMax_val : InitECandidate.Solver.HeapPotential.cMax.toNat = 2952790016 := rfl
                                        have hhl_val : heapLimit = 2952790016 := rfl
                                        omega
                                      have hWT : WorldTypedWith u2 S_t Nd := ⟨hWt.1, hWt.2.1, hWt.2.2.1, hTr_int⟩
                                      have hdj_mid : IvlsDisj [heapIvl] (worldTypedIvls u2 S_t Nd ++ ((evmChain u2).map (frameObjects u2)).flatten) := by
                                        intro y hy i hi
                                        simp only [List.mem_singleton] at hy; subst hy
                                        have hlim_ss : heapLimit = scratchStart := rfl
                                        have hdj_heap : ∀ j : Ivl, Inside j sourceBase (globN u2 "heap_ptr") → Disj heapIvl j := by
                                          intro j hj
                                          exact Or.inr (Or.inr (Or.inr (by have hj2 := hj.2; have hx1 := hx_in.1; omega)))
                                        have hdj_above : ∀ j : Ivl, scratchStart ≤ j.1 → Disj heapIvl j := by
                                          intro j hj
                                          exact Or.inr (Or.inr (Or.inl (by have hx2 := hx_in.2; omega)))
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
                                            · exact hdj_above _ (by have h := (hFW.1 (ec.1, 280) (by simp)).1.1; omega)
                                            · exact hdj_above _ (by have h := (hFW.1 (ec.2, 104) (by simp)).1.1; omega)
                                            · exact hdj_above _ (by have h := (hFW.1 (memW u2 (ec.1 + 8), 32 * memW u2 (ec.1 + 232)) (by simp)).1.1; omega)
                                            · exact hdj_above _ (by have h := hFW.2.1.1; omega)
                                            · exact hdj_above _ (by have h := (hFW.1 (memW u2 (ec.1 + 88), 24) (by simp)).1.1; omega)
                                            · rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.1 with hh | hsc
                                              · exact hdj_heap _ hh
                                              · exact hdj_above _ (by have h := hsc.1; omega)
                                            · rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with ⟨hz, _⟩ | ⟨hh, _⟩
                                              · unfold frameRet; rw [if_pos hz]; exact Or.inr (Or.inl rfl)
                                              · exact hdj_heap _ hh
                                          · unfold frameLogObjects at hlogobj
                                            obtain ⟨idx, hidx_mem, hi_own⟩ := List.mem_flatMap.1 hlogobj
                                            have hidx : idx < memW u2 (memW u2 (ec.1 + 88) + 8) := List.mem_range.1 hidx_mem
                                            have hi_rec : i ∈ logRecordIvls u2 (memW u2 (memW u2 (memW u2 (ec.1 + 88)) + 8 * idx)) := (List.mem_filter.1 hi_own).1
                                            rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
                                            · have he88_in := (hFW.1 (memW u2 (ec.1 + 88), 24) (by simp)).1.1
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
                                      have hStep_mid : EvmStep [] u2 u5_mid :=
                                        ByteRegionEffect.to_evmStep_nil_with hAt hInvAt_t hTr_int hAT_Nd hdj_mid heff_u2_mid
                                      have hch_mid : evmChain u5_mid = evmChain u2 := hStep_mid.2.2.2
                                      have hRl8_m : ∀ x ∈ ([heapIvl] : List Ivl), x.1 % 8 = 0 := by
                                        intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact hmark_8
                                      have hR_mid : OpDispatchSpec.evmR u5_mid = OpDispatchSpec.evmR u2 := by
                                        refine evmR_eq_of_chain_and_words hch_mid (fun ec hec => ?_)
                                        have hFW_ec := hFW_all ec hec
                                        have hb1 := (frameWF_bounds hAt.2 hFW_ec).1
                                        have he1_8 : ec.1 % 8 = 0 := (hFW_ec.1 (ec.1, 280) (by simp)).2.1
                                        have hdj_ec : ∀ x ∈ ([heapIvl] : List Ivl), Disj x (ec.1, 280) := by
                                          intro x hx
                                          apply hdj_mid x hx (ec.1, 280)
                                          apply List.mem_append_right
                                          exact List.mem_flatten.2 ⟨frameObjects u2 ec, List.mem_map.2 ⟨ec, hec, rfl⟩, by simp [frameObjects]⟩
                                        exact ⟨memW_eq_of_disj_eff heff_u2_mid hRl8_m hb1 he1_8 (by omega) (by omega) hdj_ec,
                                               memW_eq_of_disj_eff heff_u2_mid hRl8_m hb1 he1_8 (by omega) (by omega) hdj_ec⟩
                                      exact ⟨hStep_mid.1, hch_mid, hR_mid⟩
                                    obtain ⟨hInv_u5m, hch_u5m, hR_u5m⟩ := hInv_mid
                                    have hmid_ev_words : ∀ off, off + 8 ≤ 280 → off % 8 = 0 →
                                        memW u5_mid (globN u2 "ev" + off) = memW u2 (globN u2 "ev" + off) := by
                                      intro off hoff hoff8
                                      have hRl8_m : ∀ x ∈ ([heapIvl] : List Ivl), x.1 % 8 = 0 := by
                                        intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact hmark_8
                                      have he0_8 : (globN u2 "ev") % 8 = 0 := (hFW0.1 (globN u2 "ev", 280) (by simp)).2.1
                                      obtain ⟨he0_scr, _⟩ := (hFW0.1 (globN u2 "ev", 280) (by simp)).1
                                      have hcMax_le_scr : InitECandidate.Solver.HeapPotential.cMax.toNat ≤ scratchStart := by
                                        have hcMax_val : InitECandidate.Solver.HeapPotential.cMax.toNat = 2952790016 := rfl
                                        rw [R11Shards.scratchStart_val, hcMax_val]
                                      have hdj_ev : ∀ x ∈ ([heapIvl] : List Ivl), Disj x (globN u2 "ev", 280) := by
                                        intro x hx; simp only [List.mem_singleton] at hx; subst hx
                                        exact Or.inr (Or.inr (Or.inl (by dsimp only [heapIvl, Inside] at he0_scr ⊢; omega)))
                                      exact memW_eq_of_disj_eff heff_u2_mid hRl8_m hb_ev he0_8 hoff8 hoff hdj_ev
                                    let u7 : PanSemStateFiniteExact 64 F :=
                                      { { emptyLocalsHOLFinite (setKvarHOLFinite .global (ofString "heap_ptr") (.val (.word markw)) ent_hr) with
                                          locals := u6.locals } with locals := L }
                                    have hu7_glob : u7.globals = u2.globals := by
                                      have hg6 : ent_hr.globals = u4.globals := by
                                        change u6.globals = u4.globals; rw [heff_mc2.globals, heff_mc1.globals]
                                      change ent_hr.globals.update (ofString "heap_ptr", .val (.word markw)) = u2.globals
                                      rw [hg6, hu4_glob]
                                      exact globals_update_twice_restore u2.globals (ofString "heap_ptr")
                                        (.val (.word markw)) (.val (.word q)) hmark_lk
                                    have hu7_code : u7.code = originalRuntimeCode := hu6_code
                                    have hmemIvl_mid : (memW u5_mid (globN u5_mid "ev" + 24), memW u5_mid (globN u5_mid "ev" + 40)) = memIvl := by
                                      have hg_mid : globN u5_mid "ev" = globN u2 "ev" := rfl
                                      rw [hg_mid, hmid_ev_words 24 (by omega) (by omega), hmid_ev_words 40 (by omega) (by omega)]
                                    have heff_mid_u7 : FrameMemByteEff u5_mid u7
                                        [(0, 0), (globN u5_mid "ev", 280), (memW u5_mid (globN u5_mid "ev" + 24), memW u5_mid (globN u5_mid "ev" + 40))] := by
                                      rw [hmemIvl_mid]
                                      have hbre_mid_u7 : ByteRegionEffect u5_mid u7 [memIvl] := by
                                        refine ⟨heff_mc2.code, heff_mc2.memaddrs, heff_mc2.shMemaddrs,
                                          heff_mc2.baseAddr, heff_mc2.be, hu7_glob,
                                          heff_mc2.out_dom, heff_mc2.cell_frame, ?_⟩
                                        intro b hb hno
                                        have hmb7 : memB u7 b = memB u6 b := rfl
                                        have hmb5 : memB u5_mid b = memB u5 b := rfl
                                        rw [hmb7, heff_mc2.byte_frame b hb hno, hmb5]
                                      exact (FrameMemByteEff.of_bre hbre_mid_u7).mono (fun i hi => by
                                        simp at hi; subst hi
                                        exact ⟨memIvl, by simp, le_refl _, le_refl _⟩)
                                    have hAu7 : ArenaReady u7 :=
                                      ⟨guestInv_congr (s := u5_mid) heff_mc2.code heff_mc2.memaddrs heff_mc2.shMemaddrs heff_mc2.baseAddr hInv_u5m.1.1,
                                       arenaOK_congr hu7_glob hInv_u5m.1.2⟩
                                    have hu7_ev_words : ∀ off, off + 8 ≤ 280 → off % 8 = 0 →
                                        memW u7 (globN u5_mid "ev" + off) = memW u5_mid (globN u5_mid "ev" + off) := by
                                      intro off hoff hoff8
                                      unfold memW
                                      have hcell : u7.memory (BitVec.ofNat 64 (globN u5_mid "ev" + off)) = u5_mid.memory (BitVec.ofNat 64 (globN u5_mid "ev" + off)) := by
                                        change u6.memory (BitVec.ofNat 64 (globN u2 "ev" + off)) = u5.memory (BitVec.ofNat 64 (globN u2 "ev" + off))
                                        apply heff_mc2.cell_frame
                                        intro x hx; simp at hx; subst hx
                                        have htn : (BitVec.ofNat 64 (globN u2 "ev" + off)).toNat = globN u2 "ev" + off :=
                                          Nat.mod_eq_of_lt (by omega)
                                        rw [htn]
                                        have hmem24_8 : (memW u2 (globN u2 "ev" + 24)) % 8 = 0 := hFW0.2.2.1.1
                                        have hpw_fo := hu2_Inv.2.choose_spec.2.2.2.2.2.2.2.1
                                        have hch_u2 : ∃ tl, evmChain u2 = (globN u2 "ev", globN u2 "cur_cont") :: tl := ⟨_, rfl⟩
                                        obtain ⟨tl_u2, hch_u2_eq⟩ := hch_u2
                                        rw [hch_u2_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw_fo
                                        have hd_mem : Disj (globN u2 "ev", 280) memIvl := by
                                          have hp0 := hpw_fo.1; unfold frameObjects at hp0
                                          exact (List.pairwise_cons.1 hp0).1 _ (by simp [memIvl])
                                        have he0_8 : globN u2 "ev" % 8 = 0 := (hFW0.1 (globN u2 "ev", 280) (by simp)).2.1
                                        exact not_cellHits_of_disj_aligned (i := (globN u2 "ev", 280)) (by omega) hmem24_8
                                          (Nat.le_add_right _ off) (Nat.add_le_add_left hoff _) hd_mem
                                      rw [hcell]
                                    obtain ⟨hInv_u7, hch_u7, hR_u7⟩ := evmInv_of_head_mem_extend hInv_u5m hAu7
                                      (by unfold globN; rw [hu7_glob])
                                      heff_mid_u7
                                      (Or.inl rfl)
                                      (fun off hoff hoff8 _ _ => hu7_ev_words off hoff hoff8)
                                      (Or.inl ⟨rfl, hu7_ev_words 40 (by omega) (by omega)⟩)
                                      (by
                                        rw [hu7_ev_words 32 (by omega) (by omega), hu7_ev_words 40 (by omega) (by omega)]
                                        change memW u5_mid (globN u2 "ev" + 32) ≤ memW u5_mid (globN u2 "ev" + 40)
                                        rw [hmid_ev_words 32 (by omega) (by omega), hmid_ev_words 40 (by omega) (by omega)]
                                        exact hmem_cap_le)
                                    have hch_u2_u0 : evmChain u2 = evmChain u0 :=
                                      evmChain_congr hu2_u0_mem hu2_u0_glob
                                    have hR_u2_u0 : OpDispatchSpec.evmR u2 = OpDispatchSpec.evmR u0 :=
                                      (evm_congr hu2_u0_mem hu2_u0_glob).2.1
                                    have hlen_u7 : (evmChain u7).length = (evmChain s0).length := by
                                      rw [hch_u7, hch_u5m, hch_u2_u0]; exact hulen0
                                    have hR_u7_s0 : if true then OpDispatchSpec.evmR u7 < OpDispatchSpec.evmR s0 else OpDispatchSpec.evmR u7 ≤ OpDispatchSpec.evmR s0 := by
                                      simp only [↓reduceIte] at huR0 ⊢
                                      change OpDispatchSpec.evmR u7 = OpDispatchSpec.evmR u5_mid at hR_u7
                                      rw [hR_u7, hR_u5m, hR_u2_u0]; exact huR0
                                    exact htail_pc_ret hu7_code hInv_u7 hlen_u7 hR_u7_s0 hnt_fin
    have hseq_eq := evaluateHOLFiniteState_seq_line780 t0
      (.decCall (ofString "d") .one (ofString "sat_word") [.var .local (ofString "dst")]
        (.decCall (ofString "s") .one (ofString "sat_word") [.var .local (ofString "src")]
          (.decCall (ofString "mark") .one (ofString "heap_mark") []
            (.decCall (ofString "tmp") .one (ofString "alloc") [.var .local (ofString "n")]
              (.seq
                (.call (some (none, none)) (ofString "memcpy")
                  [.var .local (ofString "tmp"),
                   .op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "s")],
                   .var .local (ofString "n")])
                (.seq
                  (.call (some (none, none)) (ofString "memcpy")
                    [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "d")],
                     .var .local (ofString "tmp"),
                     .var .local (ofString "n")])
                  (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")])))))))
      (.seq
        (.call (some (none, none)) (ofString "pc_add") [.const 1#64])
        (.return (.const 0#64)))
    have hgoal := hrun_branch t0 hc0 hInv0 hlen0 hR0 ⟨hdst_lk0, hsrc_lk0, hn_lk0, hsrc_win0, hdst_win0⟩
      (by rw [hseq_eq]; exact hnt0)
    rw [hseq_eq] at hgoal
    exact hgoal

private theorem four_u256_arg_lookup_cost2_g09
    {v0 v1 v2 v3 : ValueHOL 64} {body' : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret' : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "extend_memory_cost2") [v0, v1, v2, v3] =
      some (body', callee, ret')) :
    callee.lookup (ofString "s1") = some v0 ∧
    callee.lookup (ofString "n1") = some v1 ∧
    callee.lookup (ofString "s2") = some v2 ∧
    callee.lookup (ofString "n2") = some v3 := by
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
    originalRuntimeCode.lookup (ofString "extend_memory_cost2") [v0, v1, v2, v3] body' callee ret' hl
  simp only [Flapjack.lookupCodeHOLExact, lookup_extend_memory_cost2_g09] at hx
  split at hx
  · have heq := Option.some.inj hx
    rcases Prod.mk.inj heq with ⟨_, hrest⟩
    rcases Prod.mk.inj hrest with ⟨hloc, _⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hfn := congrFun hloc.symm (ofString "s1")
      simpa [FUPDATE_LIST, FUPDATE,
        show ofString "s1" ≠ ofString "n1" by decide,
        show ofString "s1" ≠ ofString "s2" by decide,
        show ofString "s1" ≠ ofString "n2" by decide] using hfn
    · have hfn := congrFun hloc.symm (ofString "n1")
      simpa [FUPDATE_LIST, FUPDATE,
        show ofString "n1" ≠ ofString "s2" by decide,
        show ofString "n1" ≠ ofString "n2" by decide] using hfn
    · have hfn := congrFun hloc.symm (ofString "s2")
      simpa [FUPDATE_LIST, FUPDATE,
        show ofString "s2" ≠ ofString "n2" by decide] using hfn
    · have hfn := congrFun hloc.symm (ofString "n2")
      simpa [FUPDATE_LIST, FUPDATE] using hfn
  · cases hx

theorem op_mcopy_spec_of_extend_memory
    (h_extend : EvmPreservingSpec
      (fun s => ∃ w : BitVec 64,
        s.locals.lookup (ofString "expand_by") = some (.val (.word w)) ∧
        w.toNat < 2 ^ 38 ∧ w.toNat % 8 = 0)
      (fun s _ post =>
        (∀ g : String, ofString g ≠ ofString "frame_mem_ptr" → globN post g = globN s g) ∧
        ∀ ebw : BitVec 64,
          s.locals.lookup (ofString "expand_by") = some (.val (.word ebw)) →
          ceil32NatG09 (memW s (globN s "ev" + 32)) + ebw.toNat ≤ memW post (globN post "ev" + 32))
      (ofString "extend_memory")) :
    OpHandlerSpec (ofString "op_mcopy") := by
  refine opHandlerSpec_of_run 512 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_mcopy rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_mcopy, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRun.decCall_shaped eps_stack_pop
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ v _ _ _ hsh _ _ _ _ _ => by
      obtain ⟨a, b, c, d, rfl⟩ := shapeEq_comb4_iff v hsh
      exact ⟨.rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)], ⟨a, b, c, d, rfl⟩, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩)
    (Q := fun t => ∃ dstVal : ValueHOL 64,
      (∃ a b c d : BitVec 64, dstVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      t.locals.lookup (ofString "dst") = some dstVal)
    ?_
  refine HandlerRun.decCall_shaped eps_stack_pop
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ v _ _ ⟨dstVal, hdst4, hdst_lk⟩ hsh _ _ _ _ _ => by
      obtain ⟨a, b, c, d, rfl⟩ := shapeEq_comb4_iff v hsh
      have hne : ofString "src" ≠ ofString "dst" := by decide
      exact ⟨dstVal, .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)], hdst4, ⟨a, b, c, d, rfl⟩,
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hdst_lk],
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩)
    (Q := fun t => ∃ dstVal srcVal : ValueHOL 64,
      (∃ a b c d : BitVec 64, dstVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      (∃ a b c d : BitVec 64, srcVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      t.locals.lookup (ofString "dst") = some dstVal ∧
      t.locals.lookup (ofString "src") = some srcVal)
    ?_
  refine HandlerRun.decCall_shaped eps_stack_pop
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ v _ _ ⟨dstVal, srcVal, hdst4, hsrc4, hdst_lk, hsrc_lk⟩ hsh _ _ _ _ _ => by
      obtain ⟨a, b, c, d, rfl⟩ := shapeEq_comb4_iff v hsh
      have hne1 : ofString "len" ≠ ofString "dst" := by decide
      have hne2 : ofString "len" ≠ ofString "src" := by decide
      exact ⟨dstVal, srcVal, .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)], hdst4, hsrc4, ⟨a, b, c, d, rfl⟩,
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne1, Ne.symm hne1, hdst_lk],
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne2, Ne.symm hne2, hsrc_lk],
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩)
    (Q := fun t => ∃ dstVal srcVal lenVal : ValueHOL 64,
      (∃ a b c d : BitVec 64, dstVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      (∃ a b c d : BitVec 64, srcVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      (∃ a b c d : BitVec 64, lenVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      t.locals.lookup (ofString "dst") = some dstVal ∧
      t.locals.lookup (ofString "src") = some srcVal ∧
      t.locals.lookup (ofString "len") = some lenVal)
    ?_
  refine HandlerRun.decCall
    (Q := fun t => ∃ dstVal srcVal lenVal : ValueHOL 64,
      (∃ a b c d : BitVec 64, dstVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      (∃ a b c d : BitVec 64, srcVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      (∃ a b c d : BitVec 64, lenVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      t.locals.lookup (ofString "dst") = some dstVal ∧
      t.locals.lookup (ofString "src") = some srcVal ∧
      t.locals.lookup (ofString "len") = some lenVal ∧
      t.locals.lookup (ofString "n") = some (.val (.word (satWordG09 lenVal))))
    eps_sat_word_exact_g09
    (fun t values b_sw callee rs_sw hc _ ⟨_, _, lenVal, _, _, hlen4, _, _, hlen_lk⟩ hargs hl => by
      have hev : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.var .local (ofString "len")] = some [lenVal] := by
        rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, evalHOLExact, hlen_lk]
      rw [hev] at hargs; injection hargs with hvs; subst hvs
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "sat_word") [lenVal] =
          some (b_sw, callee, rs_sw) := by rwa [← hc]
      have hlookup : originalRuntimeCode.lookup (ofString "sat_word") =
          some ([(ofString "v", .comb [.one, .one, .one, .one])],
            sourceFnBody Guest.Software.guestFn_sat_word, .one) :=
        lookup_of_guestAst_getElem 440 (by rw [guestAst_len]; decide)
          (extractFn Guest.Software.guestFn_sat_word) rfl
      obtain ⟨_, _, hcal_v⟩ := one_u256_arg_lookup_g09 hlookup hl_orig
      obtain ⟨a, b, c, d, rfl⟩ := hlen4
      exact ⟨a, b, c, d, hcal_v⟩)
    (fun t values _ callee _ v _ _ ⟨dstVal, srcVal, lenVal, hdst4, hsrc4, hlen4, hdst_lk, hsrc_lk, hlen_lk⟩ hargs hl_orig _ _ ⟨_, hv_exact⟩ => by
      have hev : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.var .local (ofString "len")] = some [lenVal] := by
        rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, evalHOLExact, hlen_lk]
      rw [hev] at hargs; injection hargs with hvs; subst hvs
      have hlookup : originalRuntimeCode.lookup (ofString "sat_word") =
          some ([(ofString "v", .comb [.one, .one, .one, .one])],
            sourceFnBody Guest.Software.guestFn_sat_word, .one) :=
        lookup_of_guestAst_getElem 440 (by rw [guestAst_len]; decide)
          (extractFn Guest.Software.guestFn_sat_word) rfl
      obtain ⟨_, _, hcal_v⟩ := one_u256_arg_lookup_g09 hlookup hl_orig
      have hv_eq := hv_exact lenVal hcal_v
      subst hv_eq
      have hne1 : ofString "n" ≠ ofString "dst" := by decide
      have hne2 : ofString "n" ≠ ofString "src" := by decide
      have hne3 : ofString "n" ≠ ofString "len" := by decide
      exact ⟨dstVal, srcVal, lenVal, hdst4, hsrc4, hlen4,
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne1, Ne.symm hne1, hdst_lk],
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne2, Ne.symm hne2, hsrc_lk],
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne3, Ne.symm hne3, hlen_lk],
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩)
    ?_
  refine HandlerRun.decCall
    (Q := fun t => ∃ (dstVal srcVal lenVal : ValueHOL 64) (ww : BitVec 64),
      (∃ a b c d : BitVec 64, dstVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      (∃ a b c d : BitVec 64, srcVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      (∃ a b c d : BitVec 64, lenVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      t.locals.lookup (ofString "dst") = some dstVal ∧
      t.locals.lookup (ofString "src") = some srcVal ∧
      t.locals.lookup (ofString "len") = some lenVal ∧
      t.locals.lookup (ofString "n") = some (.val (.word (satWordG09 lenVal))) ∧
      t.locals.lookup (ofString "w") = some (.val (.word ww)) ∧
      ww.toNat < 2 ^ 59)
    eps_words_of_lt
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ ⟨dstVal, srcVal, lenVal, hdst4, hsrc4, hlen4, hdst_lk, hsrc_lk, hlen_lk, hn_lk⟩ _ _ _ _ ⟨_, ww, hv_eq, hww_lt⟩ => by
      subst hv_eq
      have hne1 : ofString "w" ≠ ofString "dst" := by decide
      have hne2 : ofString "w" ≠ ofString "src" := by decide
      have hne3 : ofString "w" ≠ ofString "len" := by decide
      have hne4 : ofString "w" ≠ ofString "n" := by decide
      exact ⟨dstVal, srcVal, lenVal, ww, hdst4, hsrc4, hlen4,
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne1, Ne.symm hne1, hdst_lk],
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne2, Ne.symm hne2, hsrc_lk],
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne3, Ne.symm hne3, hlen_lk],
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne4, Ne.symm hne4, hn_lk],
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
        hww_lt⟩)
    ?_
  refine HandlerRun.decCall
    (Q := fun t => ∃ (dstVal srcVal lenVal : ValueHOL 64) (ww cw ebw : BitVec 64),
      (∃ a b c d : BitVec 64, dstVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      (∃ a b c d : BitVec 64, srcVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      t.locals.lookup (ofString "dst") = some dstVal ∧
      t.locals.lookup (ofString "src") = some srcVal ∧
      t.locals.lookup (ofString "n") = some (.val (.word (satWordG09 lenVal))) ∧
      t.locals.lookup (ofString "w") = some (.val (.word ww)) ∧
      t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
      ww.toNat < 2 ^ 59 ∧
      ebw.toNat < 2 ^ 37 ∧
      ebw.toNat % 32 = 0 ∧
      (cw ≠ 18446744073709551615#64 →
        (satWordG09 lenVal ≠ 0#64 →
          (satWordG09 srcVal).toNat + (satWordG09 lenVal).toNat ≤
            ceil32NatG09 (memW t (globN t "ev" + 32)) + ebw.toNat) ∧
        (satWordG09 lenVal ≠ 0#64 →
          (satWordG09 dstVal).toNat + (satWordG09 lenVal).toNat ≤
            ceil32NatG09 (memW t (globN t "ev" + 32)) + ebw.toNat)))
    eps_extend_memory_cost2_bounds_g09
    (fun t values _ callee _ hc _ ⟨dstVal, srcVal, lenVal, _, hdst4, hsrc4, hlen4, hdst_lk, hsrc_lk, hlen_lk, _⟩ hargs hl => by
      have hev : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.var .local (ofString "src"), .var .local (ofString "len"),
           .var .local (ofString "dst"), .var .local (ofString "len")] =
          some [srcVal, lenVal, dstVal, lenVal] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hsrc_lk, hlen_lk, hdst_lk]
      rw [hev] at hargs; injection hargs with hvs; subst hvs
      have hl_orig := hc ▸ hl
      obtain ⟨hs1, hn1, hs2, hn2⟩ := four_u256_arg_lookup_cost2_g09 hl_orig
      obtain ⟨s10, s11, s12, s13, rfl⟩ := hsrc4
      obtain ⟨n10, n11, n12, n13, rfl⟩ := hlen4
      obtain ⟨s20, s21, s22, s23, rfl⟩ := hdst4
      exact ⟨s10, s11, s12, s13, n10, n11, n12, n13, s20, s21, s22, s23, n10, n11, n12, n13, hs1, hn1, hs2, hn2⟩)
    (fun t values _ callee _ _ cpost _ ⟨dstVal, srcVal, lenVal, ww, hdst4, hsrc4, _, hdst_lk, hsrc_lk, hlen_lk, hn_lk, hw_lk, hww_lt⟩ hargs hl_orig _ _ ⟨hlf, cw, ebw, hv_eq, heb_lt, heb_mod, _, hwin⟩ => by
      subst hv_eq
      have hev : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.var .local (ofString "src"), .var .local (ofString "len"),
           .var .local (ofString "dst"), .var .local (ofString "len")] =
          some [srcVal, lenVal, dstVal, lenVal] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hsrc_lk, hlen_lk, hdst_lk]
      rw [hev] at hargs; injection hargs with hvs; subst hvs
      obtain ⟨hs1, hn1, hs2, hn2⟩ := four_u256_arg_lookup_cost2_g09 hl_orig
      let res := setVarHOLFinite (ofString "x") (.rStruct [.val (.word cw), .val (.word ebw)]) { cpost with locals := t.locals }
      have hmem32 : memW res (globN res "ev" + 32) = memW (callEntryStateHOLFinite t callee) (globN (callEntryStateHOLFinite t callee) "ev" + 32) := by
        have hg : globN res "ev" = globN (callEntryStateHOLFinite t callee) "ev" :=
          globN_congr (show cpost.globals = (callEntryStateHOLFinite t callee).globals by rw [hlf]) ▸ rfl
        have hm : res.memory = (callEntryStateHOLFinite t callee).memory :=
          show cpost.memory = (callEntryStateHOLFinite t callee).memory by rw [hlf]
        rw [hg]; unfold memW; rw [hm]
      have hne1 : ofString "x" ≠ ofString "dst" := by decide
      have hne2 : ofString "x" ≠ ofString "src" := by decide
      have hne3 : ofString "x" ≠ ofString "n" := by decide
      have hne4 : ofString "x" ≠ ofString "w" := by decide
      refine ⟨dstVal, srcVal, lenVal, ww, cw, ebw, hdst4, hsrc4,
        by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne1, Ne.symm hne1, hdst_lk],
        by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne2, Ne.symm hne2, hsrc_lk],
        by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne3, Ne.symm hne3, hn_lk],
        by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne4, Ne.symm hne4, hw_lk],
        by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
        hww_lt, heb_lt, heb_mod, ?_⟩
      intro hcw
      rw [hmem32]
      exact hwin srcVal lenVal dstVal lenVal hs1 hn1 hs2 hn2 hcw)
    ?_
  refine HandlerRun.decCall
    (Q := fun t => ∃ (dstVal srcVal lenVal : ValueHOL 64) (cw ebw costw : BitVec 64),
      (∃ a b c d : BitVec 64, dstVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      (∃ a b c d : BitVec 64, srcVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      t.locals.lookup (ofString "dst") = some dstVal ∧
      t.locals.lookup (ofString "src") = some srcVal ∧
      t.locals.lookup (ofString "n") = some (.val (.word (satWordG09 lenVal))) ∧
      t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
      t.locals.lookup (ofString "cost") = some (.val (.word costw)) ∧
      0 < costw.toNat ∧
      cw.toNat ≤ costw.toNat ∧
      ebw.toNat < 2 ^ 37 ∧
      ebw.toNat % 32 = 0 ∧
      (cw ≠ 18446744073709551615#64 →
        (satWordG09 lenVal ≠ 0#64 →
          (satWordG09 srcVal).toNat + (satWordG09 lenVal).toNat ≤
            ceil32NatG09 (memW t (globN t "ev" + 32)) + ebw.toNat) ∧
        (satWordG09 lenVal ≠ 0#64 →
          (satWordG09 dstVal).toNat + (satWordG09 lenVal).toNat ≤
            ceil32NatG09 (memW t (globN t "ev" + 32)) + ebw.toNat)))
    eps_add_sat_pos_ge_b_g09
    (fun t values _ callee _ hc _ ⟨_, _, _, ww, cw, ebw, _, _, _, _, _, hw_lk, hx_lk, hww_lt, _⟩ hargs hl => by
      have hev : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.op .add [.const 3#64, .panop .mul [.const 3#64, .var .local (ofString "w")]],
           .rfield 0 (.var .local (ofString "x"))] =
          some [.val (.word (3#64 + 3#64 * ww)), .val (.word cw)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hw_lk, hx_lk, valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp]
      rw [hev] at hargs; injection hargs with hvs; subst hvs
      have hl_orig := hc ▸ hl
      obtain ⟨_, _, w1, w2, heq_vs, ha_lk, hb_lk⟩ :=
        two_word_arg_lookup (by decide) lookup_add_sat hl_orig
      injection heq_vs with hhd htl
      injection hhd with hh1; injection hh1 with hh2; subst hh2
      have hpos : 0 < (3#64 + 3#64 * ww).toNat := by
        have h3 : (3#64 : BitVec 64).toNat = 3 := rfl
        have hm : (3#64 * ww).toNat = 3 * ww.toNat := by
          rw [BitVec.toNat_mul, h3, Nat.mod_eq_of_lt (by omega)]
        rw [BitVec.toNat_add, h3, hm, Nat.mod_eq_of_lt (by omega)]
        omega
      exact ⟨3#64 + 3#64 * ww, w2, ha_lk, hb_lk, hpos⟩)
    (fun t values _ callee _ _ cpost _ ⟨dstVal, srcVal, lenVal, ww, cw, ebw, hdst4, hsrc4, hdst_lk, hsrc_lk, hn_lk, hw_lk, hx_lk, hww_lt, heb_lt, heb_mod, hwin⟩ hargs hl_orig _ _ ⟨hlf, costw, hv_eq, hcost_pos, hcost_ge⟩ => by
      subst hv_eq
      have hev : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.op .add [.const 3#64, .panop .mul [.const 3#64, .var .local (ofString "w")]],
           .rfield 0 (.var .local (ofString "x"))] =
          some [.val (.word (3#64 + 3#64 * ww)), .val (.word cw)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hw_lk, hx_lk, valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp]
      rw [hev] at hargs; injection hargs with hvs; subst hvs
      obtain ⟨_, _, w1, w2, heq_vs, _, hb_lk⟩ :=
        two_word_arg_lookup (by decide) lookup_add_sat hl_orig
      injection heq_vs with _ htl
      injection htl with hhd2 _; injection hhd2 with hh1; injection hh1 with hh2; subst hh2
      let res := setVarHOLFinite (ofString "cost") (.val (.word costw)) { cpost with locals := t.locals }
      have hmem32 : memW res (globN res "ev" + 32) = memW t (globN t "ev" + 32) := by
        have hg : globN res "ev" = globN t "ev" :=
          globN_congr (show cpost.globals = t.globals by rw [hlf]; rfl) ▸ rfl
        have hm : res.memory = t.memory :=
          show cpost.memory = t.memory by rw [hlf]; rfl
        rw [hg]; unfold memW; rw [hm]
      have hne1 : ofString "cost" ≠ ofString "dst" := by decide
      have hne2 : ofString "cost" ≠ ofString "src" := by decide
      have hne3 : ofString "cost" ≠ ofString "n" := by decide
      have hne4 : ofString "cost" ≠ ofString "x" := by decide
      refine ⟨dstVal, srcVal, lenVal, cw, ebw, costw, hdst4, hsrc4,
        by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne1, Ne.symm hne1, hdst_lk],
        by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne2, Ne.symm hne2, hsrc_lk],
        by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne3, Ne.symm hne3, hn_lk],
        by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne4, Ne.symm hne4, hx_lk],
        by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
        hcost_pos, hcost_ge cw hb_lk, heb_lt, heb_mod, ?_⟩
      rw [hmem32]; exact hwin)
    ?_
  refine seq_charge_gas_exact_g09
    (Q := fun t => ∃ (dstVal srcVal lenVal : ValueHOL 64) (cw ebw : BitVec 64),
      (∃ a b c d : BitVec 64, dstVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      (∃ a b c d : BitVec 64, srcVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      t.locals.lookup (ofString "dst") = some dstVal ∧
      t.locals.lookup (ofString "src") = some srcVal ∧
      t.locals.lookup (ofString "n") = some (.val (.word (satWordG09 lenVal))) ∧
      t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
      ebw.toNat < 2 ^ 37 ∧
      ebw.toNat % 32 = 0 ∧
      (satWordG09 lenVal ≠ 0#64 →
        (satWordG09 srcVal).toNat + (satWordG09 lenVal).toNat ≤
          ceil32NatG09 (memW t (globN t "ev" + 32)) + ebw.toNat ∧
        (satWordG09 dstVal).toNat + (satWordG09 lenVal).toNat ≤
          ceil32NatG09 (memW t (globN t "ev" + 32)) + ebw.toNat))
    (fun t w hev _ ⟨_, _, _, _, _, costw, _, _, _, _, _, _, hcost_lk, hcost_pos, _⟩ => by
      simp only [evalHOLExact, hcost_lk] at hev
      injection hev with h1; injection h1 with h2; injection h2 with h3; subst h3
      exact hcost_pos)
    (fun t cpost amtw hev hamt_lt _ ⟨dstVal, srcVal, lenVal, cw, ebw, costw, hdst4, hsrc4, hdst_lk, hsrc_lk, hn_lk, hx_lk, hcost_lk, _, hcw_le, heb_lt, heb_mod, hwin⟩ _ hglob_cp _ hmem_cp => by
      simp only [evalHOLExact, hcost_lk] at hev
      injection hev with h1; injection h1 with h2; injection h2 with h3; subst h3
      have hcw_ne : cw ≠ 18446744073709551615#64 := by
        intro hsat; subst hsat
        have : (18446744073709551615#64 : BitVec 64).toNat = 2 ^ 64 - 1 := rfl
        omega
      let res : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
      have hmem32 : memW res (globN res "ev" + 32) = memW t (globN t "ev" + 32) := by
        have hg : globN res "ev" = globN t "ev" := globN_congr hglob_cp ▸ rfl
        rw [hg]; exact hmem_cp 32 (by simp)
      obtain ⟨hw1, hw2⟩ := hwin hcw_ne
      refine ⟨dstVal, srcVal, lenVal, cw, ebw, hdst4, hsrc4, hdst_lk, hsrc_lk, hn_lk, hx_lk, heb_lt, heb_mod, ?_⟩
      intro hnz; rw [hmem32]; exact ⟨hw1 hnz, hw2 hnz⟩)
    ?_
  refine HandlerRun.seq_call h_extend
    (fun t values _ callee _ hc _ ⟨_, _, _, cw, ebw, _, _, _, _, _, hx_lk, heb_lt, heb_mod, _⟩ hargs hl => by
      have hx1 : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.rfield 1 (.var .local (ofString "x"))] = some [.val (.word ebw)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hx_lk]
      rw [hx1] at hargs; injection hargs with hvs; subst hvs
      have hl_orig := hc ▸ hl
      obtain ⟨_, _, ebw', heq_eb, hcal_eb⟩ := one_word_arg_lookup lookup_extend_memory hl_orig
      injection heq_eb with h1; injection h1 with h2; subst h2
      exact ⟨ebw, hcal_eb, by omega, by omega⟩)
    (fun t values _ callee _ _ cpost _ ⟨dstVal, srcVal, lenVal, cw, ebw, hdst4, hsrc4, hdst_lk, hsrc_lk, hn_lk, hx_lk, _, _, hwin⟩ hargs hl_orig _ _ ⟨hglob_em, hlen_em⟩ => by
      have hx1 : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.rfield 1 (.var .local (ofString "x"))] = some [.val (.word ebw)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hx_lk]
      rw [hx1] at hargs; injection hargs with hvs; subst hvs
      have hlk_em : originalRuntimeCode.lookup (ofString "extend_memory") =
          some ([(ofString "expand_by", .one)], sourceFnBody Guest.Software.guestFn_extend_memory, .one) :=
        lookup_extend_memory
      obtain ⟨_, _, ebw', heq_eb, hcal_eb⟩ := one_word_arg_lookup hlk_em hl_orig
      injection heq_eb with h1; injection h1 with h2; subst h2
      have hlen_le := hlen_em ebw hcal_eb
      have hgev : globN { cpost with locals := t.locals } "ev" = globN cpost "ev" := rfl
      have hce_ev : globN (callEntryStateHOLFinite t callee) "ev" = globN t "ev" := rfl
      have hce_m32 : memW (callEntryStateHOLFinite t callee) (globN (callEntryStateHOLFinite t callee) "ev" + 32) = memW t (globN t "ev" + 32) := rfl
      rw [hce_m32] at hlen_le
      refine ⟨dstVal, srcVal, lenVal, hdst4, hsrc4, hdst_lk, hsrc_lk, hn_lk, ?_⟩
      intro hnz
      obtain ⟨hw1, hw2⟩ := hwin hnz
      have hm_res : memW { cpost with locals := t.locals } (globN { cpost with locals := t.locals } "ev" + 32) =
          memW cpost (globN cpost "ev" + 32) := rfl
      rw [hm_res]
      exact ⟨le_trans hw1 hlen_le, le_trans hw2 hlen_le⟩)
    (op_mcopy_post_extend_run s0)

theorem op_mcopy_aligned_spec :
    FunSpec (fun s => EvmRun s ∧ HeadMemAligned s) OpDispatchPost (ofString "op_mcopy") := by
  refine ⟨_, _, _, lookup_op_mcopy, ?_⟩
  intro F s0 hcode ⟨hRun, hHM0⟩ _ hnt
  suffices hrun : HandlerRun s0 HeadMemAligned false (sourceFnBody Guest.Software.guestFn_op_mcopy) from
    hrun s0 hcode hRun.1 rfl (le_refl _) hHM0 hnt
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_op_mcopy,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRun.decCall_shaped eps_stack_pop_headMem
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ _ _ v cpost _ hHM hsh _ _ _ _ ⟨_, hHM_step⟩ => by
      obtain ⟨a, b, c, d, rfl⟩ := shapeEq_comb4_iff v hsh
      exact ⟨headMemAligned_congr_head rfl (fun _ _ => rfl)
        (hHM_step (headMemAligned_congr_head rfl (fun _ _ => rfl) hHM)),
        .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)], ⟨a, b, c, d, rfl⟩, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩)
    (Q := fun t => HeadMemAligned t ∧ ∃ dstVal : ValueHOL 64,
      (∃ a b c d : BitVec 64, dstVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      t.locals.lookup (ofString "dst") = some dstVal)
    ?_
  refine HandlerRun.decCall_shaped eps_stack_pop_headMem
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ _ _ v cpost _ ⟨hHM, dstVal, hdst4, hdst_lk⟩ hsh _ _ _ _ ⟨_, hHM_step⟩ => by
      obtain ⟨a, b, c, d, rfl⟩ := shapeEq_comb4_iff v hsh
      have hne : ofString "src" ≠ ofString "dst" := by decide
      exact ⟨headMemAligned_congr_head rfl (fun _ _ => rfl)
        (hHM_step (headMemAligned_congr_head rfl (fun _ _ => rfl) hHM)),
        dstVal, .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)], hdst4, ⟨a, b, c, d, rfl⟩,
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hdst_lk],
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩)
    (Q := fun t => HeadMemAligned t ∧ ∃ dstVal srcVal : ValueHOL 64,
      (∃ a b c d : BitVec 64, dstVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      (∃ a b c d : BitVec 64, srcVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      t.locals.lookup (ofString "dst") = some dstVal ∧
      t.locals.lookup (ofString "src") = some srcVal)
    ?_
  refine HandlerRun.decCall_shaped eps_stack_pop_headMem
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ _ _ v cpost _ ⟨hHM, dstVal, srcVal, hdst4, hsrc4, hdst_lk, hsrc_lk⟩ hsh _ _ _ _ ⟨_, hHM_step⟩ => by
      obtain ⟨a, b, c, d, rfl⟩ := shapeEq_comb4_iff v hsh
      have hne1 : ofString "len" ≠ ofString "dst" := by decide
      have hne2 : ofString "len" ≠ ofString "src" := by decide
      exact ⟨headMemAligned_congr_head rfl (fun _ _ => rfl)
        (hHM_step (headMemAligned_congr_head rfl (fun _ _ => rfl) hHM)),
        dstVal, srcVal, .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)], hdst4, hsrc4, ⟨a, b, c, d, rfl⟩,
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne1, Ne.symm hne1, hdst_lk],
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne2, Ne.symm hne2, hsrc_lk],
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩)
    (Q := fun t => HeadMemAligned t ∧ ∃ dstVal srcVal lenVal : ValueHOL 64,
      (∃ a b c d : BitVec 64, dstVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      (∃ a b c d : BitVec 64, srcVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      (∃ a b c d : BitVec 64, lenVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      t.locals.lookup (ofString "dst") = some dstVal ∧
      t.locals.lookup (ofString "src") = some srcVal ∧
      t.locals.lookup (ofString "len") = some lenVal)
    ?_
  refine HandlerRun.decCall
    (Q := fun t => HeadMemAligned t ∧ ∃ dstVal srcVal lenVal : ValueHOL 64,
      (∃ a b c d : BitVec 64, dstVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      (∃ a b c d : BitVec 64, srcVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      (∃ a b c d : BitVec 64, lenVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      t.locals.lookup (ofString "dst") = some dstVal ∧
      t.locals.lookup (ofString "src") = some srcVal ∧
      t.locals.lookup (ofString "len") = some lenVal ∧
      t.locals.lookup (ofString "n") = some (.val (.word (satWordG09 lenVal))))
    eps_sat_word_exact_g09
    (fun t values b_sw callee rs_sw hc _ ⟨_, _, _, lenVal, _, _, hlen4, _, _, hlen_lk⟩ hargs hl => by
      have hev : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.var .local (ofString "len")] = some [lenVal] := by
        rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, evalHOLExact, hlen_lk]
      rw [hev] at hargs; injection hargs with hvs; subst hvs
      have hl_orig := hc ▸ hl
      have hlookup : originalRuntimeCode.lookup (ofString "sat_word") =
          some ([(ofString "v", .comb [.one, .one, .one, .one])],
            sourceFnBody Guest.Software.guestFn_sat_word, .one) :=
        lookup_of_guestAst_getElem 440 (by rw [guestAst_len]; decide)
          (extractFn Guest.Software.guestFn_sat_word) rfl
      obtain ⟨_, _, hcal_v⟩ := one_u256_arg_lookup_g09 hlookup hl_orig
      obtain ⟨a, b, c, d, rfl⟩ := hlen4
      exact ⟨a, b, c, d, hcal_v⟩)
    (fun t values _ callee _ v cpost _ ⟨hHM, dstVal, srcVal, lenVal, hdst4, hsrc4, hlen4, hdst_lk, hsrc_lk, hlen_lk⟩ hargs hl_orig _ _ ⟨hlf, hv_exact⟩ => by
      have hev : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.var .local (ofString "len")] = some [lenVal] := by
        rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, evalHOLExact, hlen_lk]
      rw [hev] at hargs; injection hargs with hvs; subst hvs
      have hlookup : originalRuntimeCode.lookup (ofString "sat_word") =
          some ([(ofString "v", .comb [.one, .one, .one, .one])],
            sourceFnBody Guest.Software.guestFn_sat_word, .one) :=
        lookup_of_guestAst_getElem 440 (by rw [guestAst_len]; decide)
          (extractFn Guest.Software.guestFn_sat_word) rfl
      obtain ⟨_, _, hcal_v⟩ := one_u256_arg_lookup_g09 hlookup hl_orig
      have hv_eq := hv_exact lenVal hcal_v; subst hv_eq
      have hHM_res : HeadMemAligned (setVarHOLFinite (ofString "n") (.val (.word (satWordG09 lenVal))) { cpost with locals := t.locals }) :=
        headMemAligned_congr_head (show cpost.globals = t.globals by rw [hlf]; rfl)
          (fun _ _ => by
            have hm : (setVarHOLFinite (ofString "n") (.val (.word (satWordG09 lenVal))) { cpost with locals := t.locals }).memory = t.memory :=
              show cpost.memory = t.memory by rw [hlf]; rfl
            unfold memW; rw [hm]) hHM
      have hne1 : ofString "n" ≠ ofString "dst" := by decide
      have hne2 : ofString "n" ≠ ofString "src" := by decide
      have hne3 : ofString "n" ≠ ofString "len" := by decide
      exact ⟨hHM_res, dstVal, srcVal, lenVal, hdst4, hsrc4, hlen4,
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne1, Ne.symm hne1, hdst_lk],
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne2, Ne.symm hne2, hsrc_lk],
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne3, Ne.symm hne3, hlen_lk],
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩)
    ?_
  refine HandlerRun.decCall
    (Q := fun t => HeadMemAligned t ∧ ∃ (dstVal srcVal lenVal : ValueHOL 64) (ww : BitVec 64),
      (∃ a b c d : BitVec 64, dstVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      (∃ a b c d : BitVec 64, srcVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      (∃ a b c d : BitVec 64, lenVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      t.locals.lookup (ofString "dst") = some dstVal ∧
      t.locals.lookup (ofString "src") = some srcVal ∧
      t.locals.lookup (ofString "len") = some lenVal ∧
      t.locals.lookup (ofString "n") = some (.val (.word (satWordG09 lenVal))) ∧
      t.locals.lookup (ofString "w") = some (.val (.word ww)) ∧
      ww.toNat < 2 ^ 59)
    eps_words_of_lt
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ _ _ _ cpost _ ⟨hHM, dstVal, srcVal, lenVal, hdst4, hsrc4, hlen4, hdst_lk, hsrc_lk, hlen_lk, hn_lk⟩ _ _ _ _ ⟨hlf, ww, hv_eq, hww_lt⟩ => by
      subst hv_eq
      have hHM_res : HeadMemAligned (setVarHOLFinite (ofString "w") (.val (.word ww)) { cpost with locals := t.locals }) :=
        headMemAligned_congr_head (show cpost.globals = t.globals by rw [hlf]; rfl)
          (fun _ _ => by
            have hm : (setVarHOLFinite (ofString "w") (.val (.word ww)) { cpost with locals := t.locals }).memory = t.memory :=
              show cpost.memory = t.memory by rw [hlf]; rfl
            unfold memW; rw [hm]) hHM
      have hne1 : ofString "w" ≠ ofString "dst" := by decide
      have hne2 : ofString "w" ≠ ofString "src" := by decide
      have hne3 : ofString "w" ≠ ofString "len" := by decide
      have hne4 : ofString "w" ≠ ofString "n" := by decide
      exact ⟨hHM_res, dstVal, srcVal, lenVal, ww, hdst4, hsrc4, hlen4,
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne1, Ne.symm hne1, hdst_lk],
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne2, Ne.symm hne2, hsrc_lk],
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne3, Ne.symm hne3, hlen_lk],
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne4, Ne.symm hne4, hn_lk],
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
        hww_lt⟩)
    ?_
  refine HandlerRun.decCall
    (Q := fun t => HeadMemAligned t ∧ ∃ (dstVal srcVal lenVal : ValueHOL 64) (ww cw ebw : BitVec 64),
      (∃ a b c d : BitVec 64, dstVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      (∃ a b c d : BitVec 64, srcVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      t.locals.lookup (ofString "dst") = some dstVal ∧
      t.locals.lookup (ofString "src") = some srcVal ∧
      t.locals.lookup (ofString "n") = some (.val (.word (satWordG09 lenVal))) ∧
      t.locals.lookup (ofString "w") = some (.val (.word ww)) ∧
      t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
      ww.toNat < 2 ^ 59 ∧
      ebw.toNat % 32 = 0 ∧
      (ebw = 0#64 ∨ memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37) ∧
      (cw ≠ 18446744073709551615#64 →
        (satWordG09 lenVal ≠ 0#64 →
          (satWordG09 srcVal).toNat + (satWordG09 lenVal).toNat ≤
            memW t (globN t "ev" + 32) + ebw.toNat) ∧
        (satWordG09 lenVal ≠ 0#64 →
          (satWordG09 dstVal).toNat + (satWordG09 lenVal).toNat ≤
            memW t (globN t "ev" + 32) + ebw.toNat)))
    eps_extend_memory_cost2_bounds_g09
    (fun t values _ callee _ hc _ ⟨_, dstVal, srcVal, lenVal, _, hdst4, hsrc4, hlen4, hdst_lk, hsrc_lk, hlen_lk, _⟩ hargs hl => by
      have hev : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.var .local (ofString "src"), .var .local (ofString "len"),
           .var .local (ofString "dst"), .var .local (ofString "len")] =
          some [srcVal, lenVal, dstVal, lenVal] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hsrc_lk, hlen_lk, hdst_lk]
      rw [hev] at hargs; injection hargs with hvs; subst hvs
      have hl_orig := hc ▸ hl
      obtain ⟨hs1, hn1, hs2, hn2⟩ := four_u256_arg_lookup_cost2_g09 hl_orig
      obtain ⟨s10, s11, s12, s13, rfl⟩ := hsrc4
      obtain ⟨n10, n11, n12, n13, rfl⟩ := hlen4
      obtain ⟨s20, s21, s22, s23, rfl⟩ := hdst4
      exact ⟨s10, s11, s12, s13, n10, n11, n12, n13, s20, s21, s22, s23, n10, n11, n12, n13, hs1, hn1, hs2, hn2⟩)
    (fun t values _ callee _ _ cpost _ ⟨hHM, dstVal, srcVal, lenVal, ww, hdst4, hsrc4, _, hdst_lk, hsrc_lk, hlen_lk, hn_lk, hw_lk, hww_lt⟩ hargs hl_orig _ _ ⟨hlf, cw, ebw, hv_eq, _, heb_mod, heb_alt, hwin⟩ => by
      subst hv_eq
      have hev : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.var .local (ofString "src"), .var .local (ofString "len"),
           .var .local (ofString "dst"), .var .local (ofString "len")] =
          some [srcVal, lenVal, dstVal, lenVal] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hsrc_lk, hlen_lk, hdst_lk]
      rw [hev] at hargs; injection hargs with hvs; subst hvs
      obtain ⟨hs1, hn1, hs2, hn2⟩ := four_u256_arg_lookup_cost2_g09 hl_orig
      let res := setVarHOLFinite (ofString "x") (.rStruct [.val (.word cw), .val (.word ebw)]) { cpost with locals := t.locals }
      have hHM_res : HeadMemAligned res :=
        headMemAligned_congr_head (show cpost.globals = t.globals by rw [hlf]; rfl)
          (fun _ _ => by
            have hm : res.memory = t.memory := show cpost.memory = t.memory by rw [hlf]; rfl
            unfold memW; rw [hm]) hHM
      have hmem32_ce : memW (callEntryStateHOLFinite t callee) (globN (callEntryStateHOLFinite t callee) "ev" + 32) = memW t (globN t "ev" + 32) := rfl
      have hmem32_res : memW res (globN res "ev" + 32) = memW t (globN t "ev" + 32) := by
        have hg : globN res "ev" = globN t "ev" :=
          globN_congr (show cpost.globals = t.globals by rw [hlf]; rfl) ▸ rfl
        have hm : res.memory = t.memory :=
          show cpost.memory = t.memory by rw [hlf]; rfl
        rw [hg]; unfold memW; rw [hm]
      have hceil_eq : ceil32NatG09 (memW t (globN t "ev" + 32)) = memW t (globN t "ev" + 32) := by
        unfold ceil32NatG09; have := hHM.1; omega
      rw [hmem32_ce, hceil_eq] at heb_alt
      have hne1 : ofString "x" ≠ ofString "dst" := by decide
      have hne2 : ofString "x" ≠ ofString "src" := by decide
      have hne3 : ofString "x" ≠ ofString "n" := by decide
      have hne4 : ofString "x" ≠ ofString "w" := by decide
      refine ⟨hHM_res, dstVal, srcVal, lenVal, ww, cw, ebw, hdst4, hsrc4,
        by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne1, Ne.symm hne1, hdst_lk],
        by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne2, Ne.symm hne2, hsrc_lk],
        by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne3, Ne.symm hne3, hn_lk],
        by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne4, Ne.symm hne4, hw_lk],
        by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
        hww_lt, heb_mod, by rwa [hmem32_res], ?_⟩
      intro hcw
      rw [hmem32_res, ← hceil_eq, ← hmem32_ce]
      exact hwin srcVal lenVal dstVal lenVal hs1 hn1 hs2 hn2 hcw)
    ?_
  refine HandlerRun.decCall
    (Q := fun t => HeadMemAligned t ∧ ∃ (dstVal srcVal lenVal : ValueHOL 64) (cw ebw costw : BitVec 64),
      (∃ a b c d : BitVec 64, dstVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      (∃ a b c d : BitVec 64, srcVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      t.locals.lookup (ofString "dst") = some dstVal ∧
      t.locals.lookup (ofString "src") = some srcVal ∧
      t.locals.lookup (ofString "n") = some (.val (.word (satWordG09 lenVal))) ∧
      t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
      t.locals.lookup (ofString "cost") = some (.val (.word costw)) ∧
      0 < costw.toNat ∧
      cw.toNat ≤ costw.toNat ∧
      ebw.toNat % 32 = 0 ∧
      (ebw = 0#64 ∨ memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37) ∧
      (cw ≠ 18446744073709551615#64 →
        (satWordG09 lenVal ≠ 0#64 →
          (satWordG09 srcVal).toNat + (satWordG09 lenVal).toNat ≤
            memW t (globN t "ev" + 32) + ebw.toNat) ∧
        (satWordG09 lenVal ≠ 0#64 →
          (satWordG09 dstVal).toNat + (satWordG09 lenVal).toNat ≤
            memW t (globN t "ev" + 32) + ebw.toNat)))
    eps_add_sat_pos_ge_b_g09
    (fun t values _ callee _ hc _ ⟨_, _, _, _, ww, cw, _, _, _, _, _, _, hw_lk, hx_lk, hww_lt, _⟩ hargs hl => by
      have hev : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.op .add [.const 3#64, .panop .mul [.const 3#64, .var .local (ofString "w")]],
           .rfield 0 (.var .local (ofString "x"))] =
          some [.val (.word (3#64 + 3#64 * ww)), .val (.word cw)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hw_lk, hx_lk, valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp]
      rw [hev] at hargs; injection hargs with hvs; subst hvs
      have hl_orig := hc ▸ hl
      obtain ⟨_, _, w1, w2, heq_vs, ha_lk, hb_lk⟩ :=
        two_word_arg_lookup (by decide) lookup_add_sat hl_orig
      injection heq_vs with hhd htl
      injection hhd with hh1; injection hh1 with hh2; subst hh2
      have hpos : 0 < (3#64 + 3#64 * ww).toNat := by
        have h3 : (3#64 : BitVec 64).toNat = 3 := rfl
        have hm : (3#64 * ww).toNat = 3 * ww.toNat := by
          rw [BitVec.toNat_mul, h3, Nat.mod_eq_of_lt (by omega)]
        rw [BitVec.toNat_add, h3, hm, Nat.mod_eq_of_lt (by omega)]
        omega
      exact ⟨3#64 + 3#64 * ww, w2, ha_lk, hb_lk, hpos⟩)
    (fun t values _ callee _ _ cpost _ ⟨hHM, dstVal, srcVal, lenVal, ww, cw, ebw, hdst4, hsrc4, hdst_lk, hsrc_lk, hn_lk, hw_lk, hx_lk, hww_lt, heb_mod, heb_alt, hwin⟩ hargs hl_orig _ _ ⟨hlf, costw, hv_eq, hcost_pos, hcost_ge⟩ => by
      subst hv_eq
      have hev : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.op .add [.const 3#64, .panop .mul [.const 3#64, .var .local (ofString "w")]],
           .rfield 0 (.var .local (ofString "x"))] =
          some [.val (.word (3#64 + 3#64 * ww)), .val (.word cw)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hw_lk, hx_lk, valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp]
      rw [hev] at hargs; injection hargs with hvs; subst hvs
      obtain ⟨_, _, w1, w2, heq_vs, _, hb_lk⟩ :=
        two_word_arg_lookup (by decide) lookup_add_sat hl_orig
      injection heq_vs with _ htl
      injection htl with hhd2 _; injection hhd2 with hh1; injection hh1 with hh2; subst hh2
      let res := setVarHOLFinite (ofString "cost") (.val (.word costw)) { cpost with locals := t.locals }
      have hHM_res : HeadMemAligned res :=
        headMemAligned_congr_head (show cpost.globals = t.globals by rw [hlf]; rfl)
          (fun _ _ => by
            have hm : res.memory = t.memory := show cpost.memory = t.memory by rw [hlf]; rfl
            unfold memW; rw [hm]) hHM
      have hmem32 : memW res (globN res "ev" + 32) = memW t (globN t "ev" + 32) := by
        have hg : globN res "ev" = globN t "ev" :=
          globN_congr (show cpost.globals = t.globals by rw [hlf]; rfl) ▸ rfl
        have hm : res.memory = t.memory :=
          show cpost.memory = t.memory by rw [hlf]; rfl
        rw [hg]; unfold memW; rw [hm]
      have hne1 : ofString "cost" ≠ ofString "dst" := by decide
      have hne2 : ofString "cost" ≠ ofString "src" := by decide
      have hne3 : ofString "cost" ≠ ofString "n" := by decide
      have hne4 : ofString "cost" ≠ ofString "x" := by decide
      refine ⟨hHM_res, dstVal, srcVal, lenVal, cw, ebw, costw, hdst4, hsrc4,
        by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne1, Ne.symm hne1, hdst_lk],
        by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne2, Ne.symm hne2, hsrc_lk],
        by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne3, Ne.symm hne3, hn_lk],
        by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne4, Ne.symm hne4, hx_lk],
        by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
        hcost_pos, hcost_ge cw hb_lk, heb_mod, by rwa [hmem32], ?_⟩
      rw [hmem32]; exact hwin)
    ?_
  refine seq_charge_gas_exact_g09
    (Q := fun t => XCostAligned t ∧ ∃ (dstVal srcVal lenVal : ValueHOL 64) (cw ebw : BitVec 64),
      (∃ a b c d : BitVec 64, dstVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      (∃ a b c d : BitVec 64, srcVal = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) ∧
      t.locals.lookup (ofString "dst") = some dstVal ∧
      t.locals.lookup (ofString "src") = some srcVal ∧
      t.locals.lookup (ofString "n") = some (.val (.word (satWordG09 lenVal))) ∧
      t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
      (satWordG09 lenVal ≠ 0#64 →
        (satWordG09 srcVal).toNat + (satWordG09 lenVal).toNat ≤
          memW t (globN t "ev" + 32) + ebw.toNat ∧
        (satWordG09 dstVal).toNat + (satWordG09 lenVal).toNat ≤
          memW t (globN t "ev" + 32) + ebw.toNat))
    (fun t w hev _ ⟨_, _, _, _, _, _, costw, _, _, _, _, _, _, hcost_lk, hcost_pos, _⟩ => by
      simp only [evalHOLExact, hcost_lk] at hev
      injection hev with h1; injection h1 with h2; injection h2 with h3; subst h3
      exact hcost_pos)
    (fun t cpost amtw hev hamt_lt _ ⟨hHM, dstVal, srcVal, lenVal, cw, ebw, costw, hdst4, hsrc4, hdst_lk, hsrc_lk, hn_lk, hx_lk, hcost_lk, _, hcw_le, heb_mod, heb_alt, hwin⟩ _ hglob_cp _ hmem_cp => by
      simp only [evalHOLExact, hcost_lk] at hev
      injection hev with h1; injection h1 with h2; injection h2 with h3; subst h3
      have hcw_ne : cw ≠ 18446744073709551615#64 := by
        intro hsat; subst hsat
        have : (18446744073709551615#64 : BitVec 64).toNat = 2 ^ 64 - 1 := rfl
        omega
      let res : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
      have hHM_res : HeadMemAligned res :=
        headMemAligned_congr_head hglob_cp hmem_cp hHM
      have hmem32 : memW res (globN res "ev" + 32) = memW t (globN t "ev" + 32) := by
        have hg : globN res "ev" = globN t "ev" := globN_congr hglob_cp ▸ rfl
        rw [hg]; exact hmem_cp 32 (by simp)
      have hxca : XCostAligned res := by
        refine ⟨cw, ebw, hx_lk, ?_⟩
        rcases heb_alt with rfl | hlt37
        · exact Or.inl rfl
        · right
          rw [hmem32]
          have hm32_al := hHM.1
          exact ⟨hlt37, by omega, hHM_res.2⟩
      obtain ⟨hw1, hw2⟩ := hwin hcw_ne
      refine ⟨hxca, dstVal, srcVal, lenVal, cw, ebw, hdst4, hsrc4, hdst_lk, hsrc_lk, hn_lk, hx_lk, ?_⟩
      intro hnz; rw [hmem32]; exact ⟨hw1 hnz, hw2 hnz⟩)
    ?_
  refine HandlerRun.seq_call eps_extend_memory_length_g09
    (fun t values b_em callee rs_em hc _ ⟨hxca, _⟩ hargs hl =>
      extendMemoryPre_of_xCostAligned hc hxca hargs hl)
    (fun t values _ callee _ _ cpost _ ⟨_, dstVal, srcVal, lenVal, cw, ebw, hdst4, hsrc4, hdst_lk, hsrc_lk, hn_lk, hx_lk, hwin⟩ hargs hl_orig _ _ ⟨hglob_em, hlen_em⟩ => by
      have hx1 : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.rfield 1 (.var .local (ofString "x"))] = some [.val (.word ebw)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hx_lk]
      rw [hx1] at hargs; injection hargs with hvs; subst hvs
      obtain ⟨_, _, ebw', heq_eb, hcal_eb⟩ := one_word_arg_lookup lookup_extend_memory hl_orig
      injection heq_eb with h1; injection h1 with h2; subst h2
      have hlen_eq := hlen_em ebw hcal_eb
      have hgev_cp : globN cpost "ev" = globN (callEntryStateHOLFinite t callee) "ev" :=
        hglob_em "ev" (by decide)
      have hce_ev : globN (callEntryStateHOLFinite t callee) "ev" = globN t "ev" := rfl
      have hce_m32 : memW (callEntryStateHOLFinite t callee) (globN (callEntryStateHOLFinite t callee) "ev" + 32) = memW t (globN t "ev" + 32) := rfl
      have hm_res : memW { cpost with locals := t.locals } (globN { cpost with locals := t.locals } "ev" + 32) =
          memW t (globN t "ev" + 32) + ebw.toNat := by
        change memW cpost (globN cpost "ev" + 32) = _
        rw [hgev_cp, hlen_eq, hce_m32]
      refine ⟨dstVal, srcVal, lenVal, hdst4, hsrc4, hdst_lk, hsrc_lk, hn_lk, ?_⟩
      intro hnz
      obtain ⟨hw1, hw2⟩ := hwin hnz
      rw [hm_res]
      exact ⟨hw1, hw2⟩)
    (op_mcopy_post_extend_run s0)

theorem lookup_lst_push_g09 :
    originalRuntimeCode.lookup (ofString "lst_push") =
      some ([(ofString "l", .one), (ofString "esz", .one)],
        sourceFnBody Guest.Software.guestFn_lst_push, .one) :=
  lookup_of_guestAst_getElem 410 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_lst_push) rfl

theorem lookup_log_append_g09 :
    originalRuntimeCode.lookup (ofString "log_append") =
      some ([(ofString "e", .one), (ofString "log", .one)],
        sourceFnBody Guest.Software.guestFn_log_append, .one) :=
  lookup_of_guestAst_getElem 523 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_log_append) rfl

theorem lookup_op_log :
    originalRuntimeCode.lookup (ofString "op_log") =
      some ([(ofString "ntopics", .one)],
        sourceFnBody Guest.Software.guestFn_op_log, .one) :=
  lookup_of_guestAst_getElem 524 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_op_log) rfl

theorem frameWF_logs_cap_bounds {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S : List Nat} {ec : Ivl}
    (hA : ArenaOK s) (hFW : FrameWF s S ec) :
    let l := memW s (ec.1 + 88)
    1 ≤ memW s (l + 16) ∧
    memW s (l + 8) ≤ memW s (l + 16) ∧
    memW s (l + 16) ≤ 31457280 ∧
    memW s (l + 8) + 1 < 2 ^ 28 ∧
    8 * memW s (l + 16) * 2 < 2 ^ 64 ∧
    memW s l + 8 * memW s (l + 16) ≤ scratchEnd := by
  dsimp only
  have h1 := hFW.2.2.2.2.2.2.2.2.2.2.1
  have h2 := hFW.2.2.2.2.2.2.2.2.2.2.2.1
  have h3 := hFW.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold frameLogs Inside at h3
  dsimp only at h3
  have hsb := R11Shards.sourceBase_val
  have hhl := R11Shards.heapLimit_val
  have hss := R11Shards.scratchStart_val
  have hse := R11Shards.scratchEnd_val
  have hp_hi := hA.2.1
  have hsp_lo : scratchStart ≤ globN s "scratch_ptr" := le_trans hA.2.2.1 hA.2.2.2.1
  have hsp_hi : globN s "scratch_ptr" ≤ scratchEnd := hA.2.2.2.2.1
  rcases h3 with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
  · refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩ <;> omega
  · refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩ <;> omega

theorem heap_alloc_size_lt_twoPow32 {p n q : Nat}
    (hlo : sourceBase ≤ p) (hfit : p + n ≤ q) (hhi : q ≤ heapLimit) :
    n < 2 ^ 32 := by
  have hsb := R11Shards.sourceBase_val
  have hhl := R11Shards.heapLimit_val
  omega

theorem logOwnedIvls_eq_record_of_ne_sys {F : Type}
    (s : PanSemStateFiniteExact 64 F) (log : Nat)
    (hne0 : memW s log ≠ globN s "vm_system_address")
    (hne24 : memW s (log + 24) ≠ globN s "vm_system_address") :
    logOwnedIvls s log =
      [(log, 40), (memW s log, 20),
       (memW s (log + 8), 32 * memW s (log + 16)),
       (memW s (log + 24), memW s (log + 32))] := by
  have h1 : ((log, 40) != (globN s "vm_system_address", 20)) = true := by simp
  have h2 : ((memW s log, 20) != (globN s "vm_system_address", 20)) = true := by
    simp [hne0]
  have h3 : ((memW s (log + 8), 32 * memW s (log + 16)) !=
      (globN s "vm_system_address", 20)) = true := by
    simp only [bne_iff_ne, ne_eq, Prod.mk.injEq]
    rintro ⟨_, hmul⟩
    omega
  have h4 : ((memW s (log + 24), memW s (log + 32)) !=
      (globN s "vm_system_address", 20)) = true := by
    simp [hne24]
  unfold logOwnedIvls logRecordIvls
  simp [h1, h2, h3, h4]

private def EvmInvWith {F : Type} (s : PanSemStateFiniteExact 64 F) (S Nd : List Nat) : Prop :=
  ArenaReady s ∧ EvmInvAt s S ∧ TriesTypedWith s S Nd ∧
  ∀ o ∈ ((evmChain s).map (frameObjects s)).flatten, ∀ j ∈ nodeExtents s Nd, Disj o j

private theorem mem_eq_of_byte_eq_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hbe : post.be = s.be)
    {a : BitVec 64} (ha_dom : ordinaryDomain a)
    (hb : ∀ k : Nat, k < 8 → memB post (a.toNat + k) = memB s (a.toNat + k)) :
    post.memory a = s.memory a := by
  have hdom' := (ordinaryDomain_iff a).mp ha_dom
  have ha_ord : a.toNat % 8 = 0 ∧ sourceBase ≤ a.toNat ∧ a.toNat < heapEnd := by
    rw [R11Shards.sourceBase_val, R11Shards.heapEnd_val]; omega
  have hhe_lt : heapEnd ≤ 2 ^ 64 := by rw [R11Shards.heapEnd_val]; decide
  have hhe_8 : heapEnd % 8 = 0 := by decide
  have ha_hi : a.toNat + 8 ≤ 2 ^ 64 := by omega
  rcases hp_m : post.memory a with ⟨wp⟩
  rcases hs_m : s.memory a with ⟨ws⟩
  congr 1
  apply BitVec.eq_of_toNat_eq
  have hbyte_val : ∀ k : Nat, k < 8 →
      (panGetByteHOL (BitVec.ofNat 64 (a.toNat + k)) wp s.be).toNat =
      (panGetByteHOL (BitVec.ofNat 64 (a.toNat + k)) ws s.be).toNat := by
    intro k hk
    have hal_eq : panByteAlignHOL (BitVec.ofNat 64 (a.toNat + k)) = a := by
      apply BitVec.eq_of_toNat_eq
      rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hbk := hb k hk
    unfold memB at hbk
    rw [hal_eq, hp_m, hs_m, hbe] at hbk
    exact hbk
  have hshift : ∀ (w : BitVec 64) (idx : Nat), idx < 8 →
      w.toNat / 256 ^ idx % 256 =
      (panGetByteHOL (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))) w s.be).toNat := by
    intro w idx hidx
    unfold panGetByteHOL
    change w.toNat / 256 ^ idx % 256 =
      (UInt8.ofNat (w.toNat / 256 ^
        (if s.be then 8 - 1 - (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat % 8
          else (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat % 8) % 256)).toNat
    have hexp :
        (if s.be then 8 - 1 - (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat % 8
          else (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat % 8) = idx := by
      have hmod_lt : (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat =
          a.toNat + (if s.be then 7 - idx else idx) :=
        Nat.mod_eq_of_lt (by cases s.be <;> simp <;> omega)
      rw [hmod_lt]
      cases s.be <;> simp <;> omega
    rw [hexp, UInt8.toNat_ofNat']
    have h256 : (2 ^ 8 : Nat) = 256 := by decide
    rw [h256, Nat.mod_mod]
  have hpow_eq : ∀ idx : Nat, idx < 8 → wp.toNat / 256 ^ idx % 256 = ws.toNat / 256 ^ idx % 256 := by
    intro idx hidx
    rw [hshift wp idx hidx, hshift ws idx hidx]
    exact hbyte_val (if s.be then 7 - idx else idx) (by cases s.be <;> simp <;> omega)
  have hdecomp : ∀ n : Nat, n < 2 ^ 64 →
      n = (n / 256 ^ 0 % 256) +
          (n / 256 ^ 1 % 256) * 256 ^ 1 +
          (n / 256 ^ 2 % 256) * 256 ^ 2 +
          (n / 256 ^ 3 % 256) * 256 ^ 3 +
          (n / 256 ^ 4 % 256) * 256 ^ 4 +
          (n / 256 ^ 5 % 256) * 256 ^ 5 +
          (n / 256 ^ 6 % 256) * 256 ^ 6 +
          (n / 256 ^ 7 % 256) * 256 ^ 7 := by
    intro n hn; omega
  rw [hdecomp wp.toNat wp.isLt, hdecomp ws.toNat ws.isLt]
  rw [hpow_eq 0 (by omega), hpow_eq 1 (by omega), hpow_eq 2 (by omega), hpow_eq 3 (by omega),
      hpow_eq 4 (by omega), hpow_eq 5 (by omega), hpow_eq 6 (by omega), hpow_eq 7 (by omega)]

private theorem memW_eq_of_frameDisj_g09 {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hma_s : s.memaddrs = ordinaryDomain)
    {Rl : List Ivl} (heff : ByteRegionEffect s post Rl)
    {base sz k : Nat} (hbnd : base + sz ≤ 2 ^ 64) (_hb8 : base % 8 = 0) (_hk8 : k % 8 = 0)
    (hk : k + 8 ≤ sz)
    (hdj : ∀ x ∈ Rl, Disj x (base, sz)) :
    memW post (base + k) = memW s (base + k) := by
  have ha : base + k < 2 ^ 64 := by omega
  have hbit : (BitVec.ofNat 64 (base + k)).toNat = base + k := Nat.mod_eq_of_lt ha
  unfold memW
  by_cases hdom : ordinaryDomain (BitVec.ofNat 64 (base + k))
  · rw [mem_eq_of_byte_eq_g09 heff.be hdom]
    intro idx hidx
    rw [hbit]
    apply heff.byte_frame (base + k + idx) (by omega)
    intro x hx ⟨h1, h2⟩
    rcases hdj x hx with h0 | h0 | h | h
    · omega
    · dsimp only at h0; omega
    · dsimp only at h; omega
    · dsimp only at h; omega
  · rw [heff.out_dom _ (by rwa [hma_s])]

private theorem wordAt_congr_of_dom_g09 {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hma : post.memaddrs = s.memaddrs) {a : Nat} :
    WordAt post a ↔ WordAt s a := by
  unfold WordAt
  rw [hma]
  constructor
  · rintro ⟨_, hdom, _⟩
    cases hs : s.memory (BitVec.ofNat 64 a) with
    | word w => exact ⟨w, hdom, rfl⟩
  · rintro ⟨_, hdom, _⟩
    cases hp : post.memory (BitVec.ofNat 64 a) with
    | word w => exact ⟨w, hdom, rfl⟩

private theorem wordsOK_congr_of_dom_g09 {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hma : post.memaddrs = s.memaddrs) {i : Ivl} :
    WordsOK post i ↔ WordsOK s i := by
  unfold WordsOK
  exact and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun _ => imp_congr_right fun _ =>
    wordAt_congr_of_dom_g09 hma))

private theorem logRecord_in_frameObjects_g09 {F : Type} {s : PanSemStateFiniteExact 64 F} {ec : Ivl}
    {i : Nat} (hi : i < memW s (memW s (ec.1 + 88) + 8)) :
    (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40) ∈ frameObjects s ec := by
  unfold frameObjects
  apply List.mem_append_right
  unfold frameLogObjects
  dsimp only
  apply List.mem_flatMap.2
  refine ⟨i, List.mem_range.2 hi, ?_⟩
  unfold logOwnedIvls logRecordIvls
  exact List.mem_filter.2 ⟨by simp, by simp⟩

private theorem logsList_and_objects_congr_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} {ec : Ivl}
    (hFW : FrameWF s S ec)
    (hdom : post.memaddrs = s.memaddrs)
    (hglob : ∀ nm, globN post nm = globN s nm)
    (he88 : memW post (ec.1 + 88) = memW s (ec.1 + 88))
    (h88_eq : ∀ k, k + 8 ≤ 24 → k % 8 = 0 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k))
    (harr_eq : ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      memW post (memW s (memW s (ec.1 + 88)) + 8 * i) = memW s (memW s (memW s (ec.1 + 88)) + 8 * i))
    (hlog_rec_eq : ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      ∀ off, off + 8 ≤ 40 → off % 8 = 0 →
        memW post (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + off) =
          memW s (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + off)) :
    frameLogObjects post ec = frameLogObjects s ec ∧
    LogsListOK post (memW post (ec.1 + 88)) := by
  set logs := memW s (ec.1 + 88)
  have hl0 : memW post logs = memW s logs := by simpa [logs] using h88_eq 0 (by omega) (by omega)
  have hl8 : memW post (logs + 8) = memW s (logs + 8) := h88_eq 8 (by omega) (by omega)
  have hl16 : memW post (logs + 16) = memW s (logs + 16) := h88_eq 16 (by omega) (by omega)
  have hlogOwned_eq : ∀ i, i < memW s (logs + 8) →
      logOwnedIvls post (memW post (memW post logs + 8 * i)) =
        logOwnedIvls s (memW s (memW s logs + 8 * i)) := by
    intro i hi
    rw [hl0, harr_eq i hi]
    set lg := memW s (memW s logs + 8 * i)
    have r0 : memW post lg = memW s lg := by simpa [lg] using hlog_rec_eq i hi 0 (by omega) (by omega)
    have r8 : memW post (lg + 8) = memW s (lg + 8) := hlog_rec_eq i hi 8 (by omega) (by omega)
    have r16 : memW post (lg + 16) = memW s (lg + 16) := hlog_rec_eq i hi 16 (by omega) (by omega)
    have r24 : memW post (lg + 24) = memW s (lg + 24) := hlog_rec_eq i hi 24 (by omega) (by omega)
    have r32 : memW post (lg + 32) = memW s (lg + 32) := hlog_rec_eq i hi 32 (by omega) (by omega)
    unfold logOwnedIvls logRecordIvls
    rw [r0, r8, r16, r24, r32, hglob "vm_system_address"]
  refine ⟨?_, ?_⟩
  · unfold frameLogObjects
    dsimp only
    rw [he88, hl8]
    apply List.flatMap_congr
    intro i hi
    rw [List.mem_range] at hi
    exact hlogOwned_eq i hi
  · rw [he88]
    rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨hw_l, hal_l, hlt28, hle_cap, hent⟩
    · exact Or.inl hz
    · right
      have hal_post : Allocated post (logs, 24) := by
        unfold Allocated at hal_l ⊢; simp only [hglob]; exact hal_l
      refine ⟨(wordsOK_congr_of_dom_g09 hdom).2 hw_l, hal_post, by rw [hl8]; exact hlt28,
        by rw [hl8, hl16]; exact hle_cap, fun i hi => ?_⟩
      rw [hl8] at hi
      rw [hl0]
      obtain ⟨hwa, hle⟩ := hent i hi
      refine ⟨(wordAt_congr_of_dom_g09 hdom).2 hwa, ?_⟩
      rw [harr_eq i hi]
      set lg := memW s (memW s logs + 8 * i)
      have r0 : memW post lg = memW s lg := by simpa [lg] using hlog_rec_eq i hi 0 (by omega) (by omega)
      have r8 : memW post (lg + 8) = memW s (lg + 8) := hlog_rec_eq i hi 8 (by omega) (by omega)
      have r16 : memW post (lg + 16) = memW s (lg + 16) := hlog_rec_eq i hi 16 (by omega) (by omega)
      have r24 : memW post (lg + 24) = memW s (lg + 24) := hlog_rec_eq i hi 24 (by omega) (by omega)
      have r32 : memW post (lg + 32) = memW s (lg + 32) := hlog_rec_eq i hi 32 (by omega) (by omega)
      unfold LogEntryOK at hle ⊢
      rw [r0, r8, r16, r24, r32, hglob "heap_ptr"]
      exact ⟨(wordsOK_congr_of_dom_g09 hdom).2 hle.1, hle.2⟩

private theorem worldTableRefs_eq_of_cell_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hAs : ArenaOK s) (hWT : WorldTypedWith s S Nd)
    (hcell : SameTypedCells s post S Nd)
    (hglob_eq : ∀ nm ∈ coreWorldGlobals, globN post nm = globN s nm) :
    worldTableRefs post S = worldTableRefs s S := by
  have hg : ∀ nm, nm ∈ coreWorldGlobals → globN post nm = globN s nm := hglob_eq
  have hws := hg "ws" (by decide)
  have hbs := hg "bs" (by decide)
  have hts := hg "ts" (by decide)
  have hbal := hg "bal_accounts" (by decide)
  have hjn := hg "journal_n" (by decide)
  have hj := hg "journal" (by decide)
  unfold worldTableRefs recordSlots
  rw [hws, hbs, hts,
      show globalTableRoots.map (globN post) = globalTableRoots.map (globN s) by
        simp only [globalTableRoots, List.map,
          hg "bal_accounts" (by decide), hg "bal_idx_accts" (by decide), hg "bal_idx_stor" (by decide)],
      balRecords_eq hWT.1 hcell hbal, hjn, hj]
  have hws_sl : (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW post (globN s "ws" + k)) =
      (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW s (globN s "ws" + k)) := by
    split
    · rfl
    · rename_i hnz
      apply List.map_congr_left; intro k hk
      have hk_le : k + 8 ≤ 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega
      exact memW_typedRec_eq hAs hWT.2.2.1 hcell (sz := 40) (by decide) hnz hk_le
  have hbs_sl : (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW post (globN s "bs" + k)) =
      (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW s (globN s "bs" + k)) := by
    split
    · rfl
    · rename_i hnz
      apply List.map_congr_left; intro k hk
      have hk_le : k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      exact memW_typedRec_eq hAs hWT.2.2.1 hcell (sz := 80) (by decide) hnz hk_le
  have hts_sl : (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW post (globN s "ts" + k)) =
      (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW s (globN s "ts" + k)) := by
    split
    · rfl
    · rename_i hnz
      apply List.map_congr_left; intro k hk
      have hk_le : k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      exact memW_typedRec_eq hAs hWT.2.2.1 hcell (sz := 72) (by decide) hnz hk_le
  have hnest_bs : (if globN s "bs" ≠ 0 ∧ memW post (globN s "bs" + 32) ∈ S then htabValues post (memW post (globN s "bs" + 32)) else []) =
      (if globN s "bs" ≠ 0 ∧ memW s (globN s "bs" + 32) ∈ S then htabValues s (memW s (globN s "bs" + 32)) else []) := by
    by_cases hnz : globN s "bs" = 0
    · simp [hnz]
    · rw [memW_typedRec_eq hAs hWT.2.2.1 hcell (sz := 80) (by decide) hnz (by omega)]
      by_cases hmS : memW s (globN s "bs" + 32) ∈ S
      · simp [hnz, hmS, htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1]
      · simp [hnz, hmS]
  have hnest_ts : (if globN s "ts" ≠ 0 ∧ memW post (globN s "ts" + 32) ∈ S then htabValues post (memW post (globN s "ts" + 32)) else []) =
      (if globN s "ts" ≠ 0 ∧ memW s (globN s "ts" + 32) ∈ S then htabValues s (memW s (globN s "ts" + 32)) else []) := by
    by_cases hnz : globN s "ts" = 0
    · simp [hnz]
    · rw [memW_typedRec_eq hAs hWT.2.2.1 hcell (sz := 72) (by decide) hnz (by omega)]
      by_cases hmS : memW s (globN s "ts" + 32) ∈ S
      · simp [hnz, hmS, htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1]
      · simp [hnz, hmS]
  have hbal_fl : (balRecords s).flatMap (fun ad => [memW post ad, memW post (ad + 8)]) =
      (balRecords s).flatMap (fun ad => [memW s ad, memW s (ad + 8)]) := by
    apply List.flatMap_congr; intro ad had
    have had_mem := balRecord_ivl_mem had
    rcases fixedObject_le_2pow64 hAs hWT.2.2.1 (bal_in_fixedObjects had_mem) with h0 | had_bnd
    · dsimp only at h0; omega
    · dsimp only at had_bnd
      have hwti_ad := mem_worldTypedIvls_bal (S := S) (Nd := Nd) had_mem
      rw [memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩,
          memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩]
  have hjrn_mp : (List.range (globN s "journal_n")).map (fun k => memW post (globN s "journal" + 32 * k)) =
      (List.range (globN s "journal_n")).map (fun k => memW s (globN s "journal" + 32 * k)) := by
    apply List.map_congr_left; intro k hk
    rw [List.mem_range] at hk
    have hjc_ne : globN s "journal_cap" ≠ 0 := by have := hWT.2.1.1; omega
    rcases hWT.2.1.2.2.1 with h0 | ⟨hal, _⟩
    · exact absurd h0 hjc_ne
    · have hbnd := allocated_le_2pow64 hAs hal
      dsimp only at hbnd
      have hlt : 32 * k + 8 ≤ 32 * globN s "journal_cap" := by have := hWT.2.1.1; omega
      exact memW_eq_of_cellHits hcell (by omega) (mem_worldTypedIvls_journal (S := S) (Nd := Nd) hjc_ne)
        ⟨by dsimp only; omega, by dsimp only; omega⟩
  dsimp only
  rw [hbs, hts, hws_sl, hbs_sl, hts_sl, hnest_bs, hnest_ts, hbal_fl, hjrn_mp]

private theorem sameTypedCells_sub_nd_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd Ndi : List Nat}
    (hsub : ∀ n ∈ Ndi, n ∈ Nd)
    (hcell : SameTypedCells s post S Nd) :
    SameTypedCells s post S Ndi := by
  have hwti_sub : ∀ i ∈ worldTypedIvls s S Ndi, i ∈ worldTypedIvls s S Nd := by
    intro i hi
    unfold worldTypedIvls at hi ⊢
    rcases List.mem_append.1 hi with hpre | hne
    · exact List.mem_append_left _ hpre
    · apply List.mem_append_right
      unfold nodeExtents at hne ⊢
      obtain ⟨n, hn, hnx⟩ := List.mem_flatMap.1 hne
      exact List.mem_flatMap.2 ⟨n, hsub n hn, hnx⟩
  refine ⟨hcell.1, hcell.2.1, hcell.2.2.1, hcell.2.2.2.1, ?_, ?_⟩
  · intro a ha ha8 ⟨i, hi, h1, h2⟩
    exact hcell.2.2.2.2.1 a ha ha8 ⟨i, hwti_sub i hi, h1, h2⟩
  · intro b hb ⟨i, hi, h1, h2⟩
    exact hcell.2.2.2.2.2 b hb ⟨i, hwti_sub i hi, h1, h2⟩

private theorem msgOwned_congr_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {m : Nat}
    (hAs : ArenaReady s) (hApost : ArenaReady post)
    (hh : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr")
    (hg : ∀ g ∈ coreWorldGlobals, globN post g = globN s g)
    (hdom : post.memaddrs = s.memaddrs)
    (hglob : ∀ nm, globN post nm = globN s nm)
    (hWT_base : TablesTyped s S ∧ JournalTyped s S ∧ FixedTyped s)
    (hFT_post : FixedTyped post)
    (hfeq : fixedObjects post = fixedObjects s)
    (hTr : TriesTypedWith s S Nd)
    (hcell : SameTypedCells s post S Nd)
    (hfp_eq : ∀ t ∈ S, htabFootprint post t = htabFootprint s t)
    (hchain_eq : evmChain post = evmChain s)
    (hfo_eq : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec)
    (hmsg : MsgOwned s S m) :
    MsgOwned post S m := by
  obtain ⟨hal, hw, hdt, hdf, hdfo, Nd_m, hTr_m, hdj_m⟩ := hmsg
  obtain ⟨hTr_int, hsub_int⟩ := Wave8Contracts.M23.triesTypedWith_inter hTr hTr_m
  set Ndi := Nd.filter (fun n => decide (n ∈ Nd_m))
  have hsub_nd : ∀ n ∈ Ndi, n ∈ Nd := fun n hn => (List.mem_filter.1 hn).1
  have hcell_i : SameTypedCells s post S Ndi := sameTypedCells_sub_nd_g09 hsub_nd hcell
  have hWT_i : WorldTypedWith s S Ndi := ⟨hWT_base.1, hWT_base.2.1, hWT_base.2.2, hTr_int⟩
  obtain ⟨hWT_i_post, _⟩ := worldTypedWith_congr_w1 hAs hApost hh hsc hg hcell_i hWT_i
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hne_i_eq := nodeExtents_eq hTr_int.1 hcell_i
  have hal_post : Allocated post (m, 176) := by
    unfold Allocated at hal ⊢; simp only [hglob]; exact hal
  refine ⟨hal_post, (wordsOK_congr_of_dom_g09 hdom).2 hw, ?_, ?_, ?_, Ndi, hWT_i_post.2.2.2, ?_⟩
  · intro t ht i hi
    rw [hfp_eq t ht] at hi
    exact hdt t ht i hi
  · rw [hfeq]; exact hdf
  · rw [hchain_eq]
    intro ec hec o ho
    rw [hfo_eq ec hec] at ho
    exact hdfo ec hec o ho
  · intro o ho j hj
    rw [hne_i_eq] at hj
    exact hdj_m o ho j (hsub_int j hj).2

private theorem evmInvWith_of_evmInv {F : Type} {s : PanSemStateFiniteExact 64 F} (h : EvmInv s) :
    ∃ S Nd, EvmInvWith s S Nd := by
  obtain ⟨hAs, S, hW, hrest⟩ := h
  have hInvAt : EvmInvAt s S := ⟨hW, hrest⟩
  obtain ⟨Nd, hTr, hAT⟩ := hInvAt.2.2.2.2.2.2.2.2.2.1
  exact ⟨S, Nd, hAs, hInvAt, hTr, hAT⟩

private theorem evmInvWith_to_evmInv {F : Type} {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (h : EvmInvWith s S Nd) : EvmInv s :=
  ⟨h.1, S, h.2.1.1, h.2.1.2⟩

private theorem worldTypedIvls_eq_of_cell_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hAs : ArenaOK s) (hWT : WorldTypedWith s S Nd) (hcell : SameTypedCells s post S Nd)
    (hcg : ∀ g : String, ofString g ≠ ofString "heap_ptr" →
      ofString g ≠ ofString "scratch_ptr" →
      ofString g ≠ ofString "frame_mem_ptr" →
      globN post g = globN s g) :
    worldTypedIvls post S Nd = worldTypedIvls s S Nd := by
  unfold worldTypedIvls
  have hfp : S.flatMap (htabFootprint post) = S.flatMap (htabFootprint s) := by
    apply List.flatMap_congr
    intro t ht
    exact htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1
  have htr : typedRecords.map (fun gs => (globN post gs.1, if globN post gs.1 = 0 then 0 else gs.2)) =
      typedRecords.map (fun gs => (globN s gs.1, if globN s gs.1 = 0 then 0 else gs.2)) := by
    apply List.map_congr_left
    intro gs hgs
    have hne : ofString gs.1 ≠ ofString "heap_ptr" ∧
        ofString gs.1 ≠ ofString "scratch_ptr" ∧
        ofString gs.1 ≠ ofString "frame_mem_ptr" := by
      revert gs hgs; decide
    rw [hcg gs.1 hne.1 hne.2.1 hne.2.2]
  have hjc := hcg "journal_cap" (by decide) (by decide) (by decide)
  have hj := hcg "journal" (by decide) (by decide) (by decide)
  have hbo := blockOutObjects_eq hAs hWT.2.2.1 hcell (hcg "bo" (by decide) (by decide) (by decide))
  have hbal := balObjects_eq hAs hWT.1 hWT.2.2.1 hcell (hcg "bal_accounts" (by decide) (by decide) (by decide))
  have hne_ext := nodeExtents_eq hWT.2.2.2.1 hcell
  rw [hfp, htr, hjc, hj, hbo, hbal, hne_ext]

private theorem evmInvWith_of_bre {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {S Nd : List Nat}
    (hInvW : EvmInvWith s S Nd)
    (hdj : IvlsDisj Rl (worldTypedIvls s S Nd ++ ((evmChain s).map (frameObjects s)).flatten))
    (heff : ByteRegionEffect s post Rl) :
    EvmInvWith post S Nd ∧
    worldTypedIvls post S Nd = worldTypedIvls s S Nd ∧
    (evmChain post).map (frameObjects post) = (evmChain s).map (frameObjects s) ∧
    post.globals = s.globals ∧
    evmChain post = evmChain s ∧
    evmR post = evmR s ∧
    (HeadMemAligned s → HeadMemAligned post) := by
  obtain ⟨hAs, hInvAt, hTr, hAT⟩ := hInvW
  have hstep := ByteRegionEffect.to_evmStep_nil_with hAs hInvAt hTr hAT hdj heff
  have hWT : WorldTypedWith s S Nd := ⟨hInvAt.1.1, hInvAt.1.2.1, hInvAt.1.2.2.1, hTr⟩
  have hdj_w : IvlsDisj Rl (worldTypedIvls s S Nd) :=
    fun x hx i hi => hdj x hx i (List.mem_append_left _ hi)
  have heff' : ByteRegionEffect s post (Rl ++ []) := by simpa using heff
  have hWS : WorldStep (fun {F} _ => Rl) [] stdKeep NoExtra s none post :=
    ByteRegionEffect.to_worldStep (R := fun {F} _ => Rl) (extra := fun {F} _ => []) (r := none)
      ⟨hAs, S, hInvAt.1⟩ (fun _ h => by simp at h) heff'
  have hApost : ArenaReady post := hWS.1
  have hglob_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, heff.globals]
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hglob_eq]
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hglob_eq]
  have hcell : SameTypedCells s post S Nd :=
    ByteRegionEffect.sameTypedCells hAs.1.memaddrs hWT hdj_w (fun _ h => by simp at h) heff'
  have hfeq := fixedObjects_eq_of_nonHeapGlobalsKept hAs.2 hWT.1 hWT.2.2.1 hcell
    (fun name _ _ _ => by rw [heff.globals])
  have hFT_post := fixedTyped_of_eq hApost hWT.2.2.1 hh hsc hfeq
  obtain ⟨hWT_post, _⟩ := worldTypedWith_congr_w1 hAs hApost hh hsc
    (fun g _ => hglob_eq g) hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hW_post : WorldTyped post S :=
    ⟨hWT_post.1, hWT_post.2.1, hWT_post.2.2.1, Nd, hWT_post.2.2.2⟩
  have hwti_eq := worldTypedIvls_eq_of_cell_g09 hAs.2 hWT hcell (fun g _ _ _ => hglob_eq g)
  have hdj_f : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, ∀ x ∈ Rl, Disj x o := by
    intro ec hec o ho x hx
    exact hdj x hx o (List.mem_append_right _ (List.mem_flatten.2
      ⟨frameObjects s ec, List.mem_map.2 ⟨ec, hec, rfl⟩, ho⟩))
  obtain ⟨_, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW, hFO_pw, hFO_disj, _, hMarks, hRoles, hGas⟩ := hInvAt
  have hrec_eq : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → k % 8 = 0 → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → k % 8 = 0 → memW post (ec.2 + k) = memW s (ec.2 + k)) ∧
      (∀ k, k + 8 ≤ 24 → k % 8 = 0 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨hb1, hb2, hb88, _⟩ := frameWF_bounds hAs.2 hFW
    have he1_8 : ec.1 % 8 = 0 := (hFW.1 (ec.1, 280) (by simp)).2.1
    have he2_8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
    have he88_8 : (memW s (ec.1 + 88)) % 8 = 0 := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).2.1
    refine ⟨fun k hk hk8 => memW_eq_of_frameDisj_g09 hAs.1.memaddrs heff hb1 he1_8 hk8 hk
              (hdj_f ec hec (ec.1, 280) (by simp [frameObjects])),
            fun k hk hk8 => memW_eq_of_frameDisj_g09 hAs.1.memaddrs heff hb2 he2_8 hk8 hk
              (hdj_f ec hec (ec.2, 104) (by simp [frameObjects])),
            fun k hk hk8 => memW_eq_of_frameDisj_g09 hAs.1.memaddrs heff hb88 he88_8 hk8 hk
              (hdj_f ec hec (memW s (ec.1 + 88), 24) (by simp [frameObjects]))⟩
  have hch_eq : evmChain post = evmChain s := hstep.2.2.2
  have hframeLogs_eq : ∀ ec ∈ evmChain s, frameLogs post ec = frameLogs s ec := by
    intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    unfold frameLogs
    rw [he_eq 88 (by omega) (by omega),
        show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by simpa using h88_eq 0 (by omega) (by omega),
        h88_eq 16 (by omega) (by omega)]
  have hframeRet_eq : ∀ ec ∈ evmChain s, frameRet post ec = frameRet s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameRet
    rw [he_eq 216 (by omega) (by omega), he_eq 144 (by omega) (by omega)]
  have hlogs_congr : ∀ ec ∈ evmChain s,
      frameLogObjects post ec = frameLogObjects s ec ∧ LogsListOK post (memW post (ec.1 + 88)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨_, _, _, hfob⟩ := frameWF_bounds hAs.2 hFW
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    refine logsList_and_objects_congr_g09 hFW heff.memaddrs hglob_eq
      (he_eq 88 (by omega) (by omega)) h88_eq ?_ ?_
    · intro i hi
      have hfl_in : frameLogs s ec ∈ frameObjects s ec := by simp [frameObjects]
      have hlen_le : memW s (memW s (ec.1 + 88) + 8) ≤ memW s (memW s (ec.1 + 88) + 16) :=
        hFW.2.2.2.2.2.2.2.2.2.2.2.1
      have hfl_b : (frameLogs s ec).1 + (frameLogs s ec).2 ≤ 2 ^ 64 := by
        rcases hfob _ hfl_in with h0 | hb
        · unfold frameLogs at h0; dsimp only at h0; omega
        · exact hb
      have hfl_8 : (memW s (memW s (ec.1 + 88))) % 8 = 0 :=
        hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
      exact memW_eq_of_frameDisj_g09 hAs.1.memaddrs heff hfl_b hfl_8 (by omega)
        (by unfold frameLogs; dsimp only; omega) (hdj_f ec hec (frameLogs s ec) hfl_in)
    · intro i hi off hoff hoff8
      have hlr_in := logRecord_in_frameObjects_g09 (s := s) (ec := ec) hi
      have hlr_b : memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + 40 ≤ 2 ^ 64 := by
        rcases hfob _ hlr_in with h0 | hb
        · dsimp only at h0; omega
        · exact hb
      have hlr_8 : (memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) % 8 = 0 := by
        rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
        · have he88_in := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1
          have hss : 0 < scratchStart := by rw [R11Shards.scratchStart_val]; decide
          have := hAs.2.2.2.1; have := hAs.2.2.2.2.1; have := he88_in.1
          dsimp only at this
          omega
        · exact (hent i hi).2.1.1
      exact memW_eq_of_frameDisj_g09 hAs.1.memaddrs heff hlr_b hlr_8 hoff8 hoff
        (hdj_f ec hec _ hlr_in)
  have hframeObjects_eq : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameObjects
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
        he_eq 24 (by omega) (by omega), he_eq 40 (by omega) (by omega),
        he_eq 88 (by omega) (by omega), hframeLogs_eq ec hec, hframeRet_eq ec hec,
        (hlogs_congr ec hec).1]
  have hframeScratch_eq : ∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameScratch
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega), he_eq 88 (by omega) (by omega)]
  have hmap_fo : (evmChain post).map (frameObjects post) = (evmChain s).map (frameObjects s) := by
    rw [hch_eq]; exact List.map_congr_left hframeObjects_eq
  have hmap_fo_s : (evmChain s).map (frameObjects post) = (evmChain s).map (frameObjects s) :=
    List.map_congr_left hframeObjects_eq
  have hframeRoleSlots_eq : frameRoleSlots post (evmChain s) = frameRoleSlots s (evmChain s) := by
    unfold frameRoleSlots
    apply List.flatMap_congr
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    rw [he_eq 136 (by omega) (by omega), he_eq 168 (by omega) (by omega), he_eq 176 (by omega) (by omega)]
  have hfp_eq_all : ∀ t ∈ S, htabFootprint post t = htabFootprint s t :=
    fun t ht => htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1
  have hne_eq : nodeExtents post Nd = nodeExtents s Nd := nodeExtents_eq hTr.1 hcell
  have hInvAt_post : EvmInvAt post S := by
    refine ⟨hW_post, ?_⟩
    dsimp only
    rw [hch_eq]
    refine ⟨hch_ne, hch_len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨ec, hec, hk0⟩ := hch_last
      have hec_mem : ec ∈ evmChain s := List.mem_of_mem_getLast? hec
      exact ⟨ec, hec, by rw [(hrec_eq ec hec_mem).2.1 16 (by omega) (by omega)]; exact hk0⟩
    · intro ec hec
      obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
      obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, _, c17⟩ := hFW_all ec hec
      have hlo_ok := (hlogs_congr ec hec).2
      have hmsg_ok : MsgOwned post S (memW post (ec.1 + 112)) := by
        rw [he_eq 112 (by omega) (by omega)]
        exact msgOwned_congr_g09 hAs hApost hh hsc (fun g _ => hglob_eq g) heff.memaddrs hglob_eq
          ⟨hWT.1, hWT.2.1, hWT.2.2.1⟩ hFT_post hfeq hTr hcell hfp_eq_all hch_eq hframeObjects_eq c17
      unfold FrameWF
      dsimp only
      rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
          he_eq 88 (by omega) (by omega), he_eq 24 (by omega) (by omega),
          he_eq 40 (by omega) (by omega), he_eq 16 (by omega) (by omega),
          he_eq 32 (by omega) (by omega), he_eq 136 (by omega) (by omega),
          he_eq 168 (by omega) (by omega), he_eq 176 (by omega) (by omega),
          h88_eq 16 (by omega) (by omega), h88_eq 8 (by omega) (by omega),
          hframeLogs_eq ec hec, he_eq 216 (by omega) (by omega), he_eq 144 (by omega) (by omega),
          hframeRet_eq ec hec,
          hglob_eq "scratch_ptr", hglob_eq "frame_mem_ptr", hglob_eq "heap_ptr", hglob_eq "evm_empty"]
      rw [he_eq 88 (by omega) (by omega)] at hlo_ok
      refine ⟨?_, c2, (wordsOK_congr_of_dom_g09 heff.memaddrs).2 c3, c4, c5, c6, c7, c8, c9, c10, c11, c12,
        c13, (wordsOK_congr_of_dom_g09 heff.memaddrs).2 c14, ?_, hlo_ok, hmsg_ok⟩
      · intro i hi
        obtain ⟨hin, hw⟩ := c1 i hi
        exact ⟨hin, (wordsOK_congr_of_dom_g09 heff.memaddrs).2 hw⟩
      · rcases c15 with h0 | ⟨hin, hw⟩
        · exact Or.inl h0
        · exact Or.inr ⟨hin, (wordsOK_congr_of_dom_g09 heff.memaddrs).2 hw⟩
    · intro ec hec
      have hec_mem : ec ∈ evmChain s := List.mem_of_mem_tail hec
      unfold FrameRoom
      rw [(hrec_eq ec hec_mem).1 16 (by omega) (by omega), (hrec_eq ec hec_mem).1 232 (by omega) (by omega)]
      exact hFR_all ec hec
    · intro i hi
      have hi0 : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
      have hi1 : (evmChain s)[i + 1] ∈ evmChain s := List.getElem_mem _
      rw [(hrec_eq _ hi0).2.1 80 (by omega) (by omega), (hrec_eq _ hi0).2.1 72 (by omega) (by omega),
          (hrec_eq _ hi1).1 40 (by omega) (by omega)]
      exact hRW i hi
    · rw [hmap_fo_s]; exact hFO_pw
    · intro ec hec o ho
      rw [hframeObjects_eq ec hec] at ho
      rw [hfeq]
      refine ⟨fun t ht i hi => ?_, (hFO_disj ec hec o ho).2⟩
      rw [hfp_eq_all t ht] at hi
      exact (hFO_disj ec hec o ho).1 t ht i hi
    · rw [hmap_fo_s]
      refine ⟨Nd, hWT_post.2.2.2, fun o ho j hj => ?_⟩
      rw [hne_eq] at hj
      exact hAT o ho j hj
    · have hworldRefs_eq := worldTableRefs_eq_of_cell_g09 hAs.2 hWT hcell (fun g _ => hglob_eq g)
      have hdelEx_iff : ∀ i t, DelExclusive post S (evmChain s) i t ↔ DelExclusive s S (evmChain s) i t := by
        intro i t
        unfold DelExclusive
        rw [hworldRefs_eq]
        refine and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun hj =>
          forall_congr' fun k => imp_congr_right fun hk => ?_)
        have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
        have hk_le : k + 8 ≤ 280 ∧ k % 8 = 0 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
        rw [(hrec_eq _ hj_mem).1 k hk_le.1 hk_le.2]
      intro i hi
      have hi_mem : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
      have hm_eq := (hrec_eq _ hi_mem).2.1 48 (by omega) (by omega)
      have hmm_eq := (hrec_eq _ hi_mem).2.1 56 (by omega) (by omega)
      have he24_eq := (hrec_eq _ hi_mem).1 24 (by omega) (by omega)
      have htake_eq : ((evmChain s).take (i + 1)).map (fun ec => memW post (ec.1 + 136)) =
          ((evmChain s).take (i + 1)).map (fun ec => memW s (ec.1 + 136)) := by
        apply List.map_congr_left; intro ec hec
        exact (hrec_eq ec (List.mem_of_mem_take hec)).1 136 (by omega) (by omega)
      have hM := hMarks i hi
      dsimp only at hM ⊢
      rw [hm_eq, hmm_eq, he24_eq, hframeScratch_eq _ hi_mem, hfeq, htake_eq]
      obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM
      refine ⟨m1, m2, m3, m4, ?_, m6, m7, ?_, m9⟩
      · intro j hj hij
        have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
        rw [hframeScratch_eq _ hj_mem, hframeObjects_eq _ hj_mem, hframeLogs_eq _ hj_mem,
            (hrec_eq _ hj_mem).1 112 (by omega) (by omega)]
        exact m5 j hj hij
      · intro t ht
        rw [hfp_eq_all t ht, hdelEx_iff i t]
        exact m8 t ht
    · have hcg : ∀ g ∈ coreWorldGlobals, globN post g = globN s g := fun g _ => hglob_eq g
      rw [worldRoleSlots_eq hAs.2 hWT.1 hWT.2.2.1 hcell hcg,
          hframeRoleSlots_eq,
          journalRoleSlots_eq hAs.2 hWT.2.1 hWT.2.2.1 hcell hcg]
      unfold RolesOK at hRoles ⊢
      refine ⟨fun a ha => ?_, hRoles.2⟩
      obtain ⟨haS, hkl⟩ := hRoles.1 a ha
      have htb := ((hWT.1.2.1 a.1 haS).1.1 (a.1, 88) (by simp [htabFootprint])).1
      rw [htab_hdr_eq hcell haS htb 0 (by omega)]
      exact ⟨haS, hkl⟩
    · have hmap_gas : ((evmChain s).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)) =
          ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)) := by
        apply List.map_congr_left; intro ec hec
        rw [(hrec_eq ec hec).1 64 (by omega) (by omega), (hrec_eq ec hec).1 192 (by omega) (by omega)]
      rw [hmap_gas]
      exact hGas
  have hR_eq : evmR post = evmR s := by
    refine evmR_eq_of_chain_and_words hch_eq (fun ec hec => ?_)
    exact ⟨(hrec_eq ec hec).1 64 (by omega) (by omega), (hrec_eq ec hec).1 192 (by omega) (by omega)⟩
  have hHM_imp : HeadMemAligned s → HeadMemAligned post := by
    intro hHM
    have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
      simp [evmChain, evmChainFrom]
    refine headMemAligned_congr_head heff.globals (fun off hoff => ?_) hHM
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl | rfl
    · exact (hrec_eq _ hhead_mem).1 24 (by omega) (by omega)
    · exact (hrec_eq _ hhead_mem).1 32 (by omega) (by omega)
    · exact (hrec_eq _ hhead_mem).1 40 (by omega) (by omega)
  refine ⟨⟨hApost, hInvAt_post, hWT_post.2.2.2, ?_⟩, hwti_eq, hmap_fo, heff.globals, hch_eq, hR_eq, hHM_imp⟩
  rw [hmap_fo, hne_eq]
  exact hAT

private theorem evmInvWith_localsFree {F : Type} {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (locs : HolFiniteMapExact MlS (ValueHOL 64)) (clk : Nat) (h : EvmInvWith s S Nd) :
    EvmInvWith { s with locals := locs, clock := clk } S Nd :=
  (evmInvWith_of_bre h (fun _ hx _ _ => by simp at hx)
    ((ByteRegionEffect.refl s []).with_locals_clock locs clk)).1

private theorem frameObject_disj_fresh_heap_g09 {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S : List Nat} {ec o : Ivl} {hp_post : Nat}
    (hA : ArenaOK s) (hhp_lim : hp_post ≤ heapLimit)
    (hFW : FrameWF s S ec) (ho : o ∈ frameObjects s ec) :
    o.2 = 0 ∨ hp_post ≤ o.1 ∨ o.1 + o.2 ≤ globN s "heap_ptr" := by
  have hhl_ss : heapLimit ≤ scratchStart := by
    rw [R11Shards.heapLimit_val, R11Shards.scratchStart_val]
  have hfm_ge : scratchStart ≤ globN s "frame_mem_ptr" := hA.2.2.1
  have hsp_ge : scratchStart ≤ globN s "scratch_ptr" := le_trans hfm_ge hA.2.2.2.1
  obtain ⟨hscr, hmem_in, _, _, _, _, _, _, _, _, _, _, hlogs_in, _, hret_in, hll_ok, _⟩ := hFW
  unfold frameObjects at ho
  rcases List.mem_append.1 ho with ho7 | holog
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho7
    rcases ho7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h := (hscr (ec.1, 280) (by simp)).1.1
      dsimp only at h ⊢; exact Or.inr (Or.inl (by omega))
    · have h := (hscr (ec.2, 104) (by simp)).1.1
      dsimp only at h ⊢; exact Or.inr (Or.inl (by omega))
    · have h := (hscr (memW s (ec.1 + 8), 32 * memW s (ec.1 + 232)) (by simp)).1.1
      dsimp only at h ⊢; exact Or.inr (Or.inl (by omega))
    · have h := hmem_in.1
      dsimp only at h ⊢; exact Or.inr (Or.inl (by omega))
    · have h := (hscr (memW s (ec.1 + 88), 24) (by simp)).1.1
      dsimp only at h ⊢; exact Or.inr (Or.inl (by omega))
    · rcases hlogs_in with h | h
      · exact Or.inr (Or.inr h.2)
      · exact Or.inr (Or.inl (by have := h.1; omega))
    · rcases hret_in with ⟨hz, _⟩ | ⟨h, _⟩
      · unfold frameRet; exact Or.inl (by simp [hz])
      · exact Or.inr (Or.inr h.2)
  · unfold frameLogObjects at holog
    dsimp only at holog
    obtain ⟨idx, hidx_mem, ho_own⟩ := List.mem_flatMap.1 holog
    rw [List.mem_range] at hidx_mem
    rcases hll_ok with hz | ⟨_, _, _, _, hent⟩
    · exfalso
      have hlo := (hscr (memW s (ec.1 + 88), 24) (by simp)).1.1
      dsimp only at hlo
      have hss : 0 < scratchStart := by rw [R11Shards.scratchStart_val]; decide
      omega
    · have hle := (hent idx hidx_mem).2
      have ho_rec : o ∈ logRecordIvls s (memW s (memW s (memW s (ec.1 + 88)) + 8 * idx)) :=
        (List.mem_filter.1 ho_own).1
      simp only [logRecordIvls, List.mem_cons, List.not_mem_nil, or_false] at ho_rec
      rcases ho_rec with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inr hle.2.1.2)
      · exact Or.inr (Or.inr hle.2.2.2.2.1.2)
      · exact Or.inr (Or.inr hle.2.2.2.2.2.1.2)
      · exact Or.inr (Or.inr hle.2.2.2.2.2.2.2)

private theorem evmInvWith_of_alloc_pure {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {pw qw : BitVec 64} {sz : Nat}
    (hInvW : EvmInvWith s S Nd)
    (hp_lk : s.globals.lookup (ofString "heap_ptr") = some (.val (.word pw)))
    (hfit : pw.toNat + sz ≤ qw.toNat)
    (hq_lim : qw.toNat ≤ heapLimit)
    (hq_mod8 : qw.toNat % 8 = 0)
    (hcode : post.code = s.code)
    (hma : post.memaddrs = s.memaddrs)
    (hsh : post.shMemaddrs = s.shMemaddrs)
    (hba : post.baseAddr = s.baseAddr)
    (hbe : post.be = s.be)
    (hglob : post.globals = s.globals.update (ofString "heap_ptr", .val (.word qw)))
    (hmem : post.memory = s.memory) :
    EvmInvWith post S Nd ∧
    worldTypedIvls post S Nd = worldTypedIvls s S Nd ∧
    (evmChain post).map (frameObjects post) = (evmChain s).map (frameObjects s) ∧
    evmChain post = evmChain s ∧
    evmR post = evmR s ∧
    (HeadMemAligned s → HeadMemAligned post) ∧
    globN s "heap_ptr" = pw.toNat ∧
    globN post "heap_ptr" = qw.toNat ∧
    pw.toNat % 8 = 0 ∧
    sourceBase ≤ pw.toNat ∧
    WordsOK post (pw.toNat, qw.toNat - pw.toNat) ∧
    IvlsDisj [(pw.toNat, qw.toNat - pw.toNat)]
      (worldTypedIvls post S Nd ++ ((evmChain post).map (frameObjects post)).flatten) := by
  obtain ⟨hAs, hInvAt, hTr, hAT⟩ := hInvW
  have hp_glob : globN s "heap_ptr" = pw.toNat := by simp [globN, hp_lk]
  have hq_glob : globN post "heap_ptr" = qw.toNat := by
    simp [globN, hglob, HolFiniteMapExact.lookup_update, FUPDATE]
  have hg_kept : GlobalsKept ["heap_ptr"] s post := by
    intro g hg
    have hne : g ≠ ofString "heap_ptr" := by simpa using hg
    rw [hglob]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne]
  have hglob_nonHeap : ∀ nm : String, ofString nm ≠ ofString "heap_ptr" → globN post nm = globN s nm := by
    intro nm hne
    exact (InitECandidate.Solver.Wave8Contracts.M23.globN_eq_of_lookup_eq
      (hg_kept (ofString nm) (by simp [hne]))).symm
  have hp_lo : sourceBase ≤ pw.toNat := by rw [← hp_glob]; exact hAs.2.1
  have hp_mod8 : pw.toNat % 8 = 0 := by rw [← hp_glob]; exact hAs.2.2.2.2.2.2.1
  have hAp_ok : ArenaOK post := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, globalsWord_update _ _ hglob hAs.2.2.2.2.2.2.2.2.2⟩
    · rw [hq_glob]; omega
    · rw [hq_glob]; exact hq_lim
    · rw [hglob_nonHeap "frame_mem_ptr" (by decide)]; exact hAs.2.2.2.1
    · rw [hglob_nonHeap "frame_mem_ptr" (by decide), hglob_nonHeap "scratch_ptr" (by decide)]; exact hAs.2.2.2.2.1
    · rw [hglob_nonHeap "scratch_ptr" (by decide)]; exact hAs.2.2.2.2.2.1
    · rw [hq_glob]; exact hq_mod8
    · rw [hglob_nonHeap "frame_mem_ptr" (by decide)]; exact hAs.2.2.2.2.2.2.2.1
    · rw [hglob_nonHeap "scratch_ptr" (by decide)]; exact hAs.2.2.2.2.2.2.2.2.1
  have hGp : GuestInv post :=
    ⟨hcode.trans hAs.1.code, hma.trans hAs.1.memaddrs, hsh.trans hAs.1.shMemaddrs, hba.trans hAs.1.baseAddr⟩
  have hAp : ArenaReady post := ⟨hGp, hAp_ok⟩
  have hhp : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hp_glob, hq_glob]; omega
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by
    rw [hglob_nonHeap "scratch_ptr" (by decide)]
  obtain ⟨hInvAt_post_raw, hch_eq, hR_eq⟩ := evmInvAt_of_fresh_heap_step hAs hInvAt hAp hbe hhp hg_kept
    (fun _ _ => by rw [hmem]) (fun _ _ _ => by simp [memB, hmem, hbe])
  have hWT : WorldTypedWith s S Nd := ⟨hInvAt.1.1, hInvAt.1.2.1, hInvAt.1.2.2.1, hTr⟩
  have hcell : SameTypedCells s post S Nd :=
    ⟨hbe, hma, hAs.1.memaddrs, fun _ _ => by rw [hmem], fun _ _ _ _ => by rw [hmem],
     fun _ _ _ => by simp [memB, hmem, hbe]⟩
  have hfeq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [blockOutObjects_eq hAs.2 hWT.2.2.1 hcell (hglob_nonHeap "bo" (by decide)),
        balObjects_eq hAs.2 hWT.1 hWT.2.2.1 hcell (hglob_nonHeap "bal_accounts" (by decide)),
        hglob_nonHeap "journal" (by decide),
        hglob_nonHeap "journal_cap" (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne : ofString gn.1 ≠ ofString "heap_ptr" := by revert gn hgn; decide
    rw [hglob_nonHeap gn.1 hne]
  have hFT_post := fixedTyped_of_eq hAp hWT.2.2.1 hhp hsc hfeq
  have hcg : ∀ g ∈ coreWorldGlobals, globN post g = globN s g := by
    intro g hg
    have hne : ofString g ≠ ofString "heap_ptr" := by revert g hg; decide
    exact hglob_nonHeap g hne
  obtain ⟨hWT_post, _⟩ := worldTypedWith_congr_w1 hAs hAp hhp hsc hcg hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hwti_eq := worldTypedIvls_eq_of_cell_g09 hAs.2 hWT hcell (fun g h1 _ _ => hglob_nonHeap g h1)
  have hfo_eq : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec := by
    intro ec _
    have hge_empty : globN post "evm_empty" = globN s "evm_empty" := hglob_nonHeap "evm_empty" (by decide)
    have hge_sys : globN post "vm_system_address" = globN s "vm_system_address" :=
      hglob_nonHeap "vm_system_address" (by decide)
    have hmw_eq : ∀ a : Nat, memW post a = memW s a := fun a => by unfold memW; rw [hmem]
    unfold frameObjects frameLogs frameRet frameLogObjects logOwnedIvls logRecordIvls
    simp only [hmw_eq, hge_empty, hge_sys]
  have hmap_fo : (evmChain post).map (frameObjects post) = (evmChain s).map (frameObjects s) := by
    rw [hch_eq]; exact List.map_congr_left hfo_eq
  have hne_eq : nodeExtents post Nd = nodeExtents s Nd := nodeExtents_eq hTr.1 hcell
  have hInvAt_post : EvmInvAt post S :=
    ⟨⟨hWT_post.1, hWT_post.2.1, hWT_post.2.2.1, Nd, hWT_post.2.2.2⟩, hInvAt_post_raw.2⟩
  have hHM_imp : HeadMemAligned s → HeadMemAligned post := by
    intro hHM
    have hgev : globN post "ev" = globN s "ev" := hglob_nonHeap "ev" (by decide)
    have hgfp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" :=
      hglob_nonHeap "frame_mem_ptr" (by decide)
    have hmw_eq : ∀ a : Nat, memW post a = memW s a := fun a => by unfold memW; rw [hmem]
    refine ⟨?_, ?_⟩
    · rw [hgev, hmw_eq]; exact hHM.1
    · rw [hgev, hgfp, hmw_eq, hmw_eq]; exact hHM.2
  have hal_blk : Allocated post (pw.toNat, qw.toNat - pw.toNat) := by
    left; unfold Inside; dsimp only; rw [hq_glob]; exact ⟨hp_lo, by omega⟩
  have hw_blk : WordsOK post (pw.toNat, qw.toNat - pw.toNat) :=
    wordsOK_of_allocated hAp hal_blk hp_mod8 (by omega)
  have hdj_blk : IvlsDisj [(pw.toNat, qw.toNat - pw.toNat)]
      (worldTypedIvls post S Nd ++ ((evmChain post).map (frameObjects post)).flatten) := by
    rw [hwti_eq, hmap_fo]
    intro x hx i hi
    simp only [List.mem_singleton] at hx; subst hx
    rcases List.mem_append.1 hi with hi_w | hi_f
    · rcases worldTypedIvls_allocated hWT hi_w with hi0 | hal_s
      · exact Or.inr (Or.inl hi0)
      · rcases hal_s with ⟨_, hi2⟩ | ⟨hi1, _⟩
        · rw [hp_glob] at hi2
          exact Or.inr (Or.inr (Or.inr (by dsimp only; omega)))
        · have hs_fr := hAs.2.2.2.1
          have hs_gap := hAs.2.2.2.2.1
          have hhl_ss : heapLimit ≤ scratchStart := by
            rw [R11Shards.heapLimit_val, R11Shards.scratchStart_val]
          exact Or.inr (Or.inr (Or.inl (by dsimp only at hi1 ⊢; omega)))
    · obtain ⟨fo, hfo_m, hi_fo⟩ := List.mem_flatten.1 hi_f
      obtain ⟨ec, hec, rfl⟩ := List.mem_map.1 hfo_m
      rcases frameObject_disj_fresh_heap_g09 hAs.2 hq_lim (hInvAt.2.2.2.2.1 ec hec) hi_fo with hi0 | h1 | h2
      · exact Or.inr (Or.inl hi0)
      · exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
      · rw [hp_glob] at h2
        exact Or.inr (Or.inr (Or.inr (by dsimp only; omega)))
  refine ⟨⟨hAp, hInvAt_post, hWT_post.2.2.2, ?_⟩,
    hwti_eq, hmap_fo, hch_eq, hR_eq, hHM_imp, hp_glob, hq_glob, hp_mod8, hp_lo, hw_blk, hdj_blk⟩
  rw [hmap_fo, hne_eq]
  exact hAT

private theorem evmInvWith_of_head_sp_cell {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hInvW : EvmInvWith s S Nd)
    (hGp : GuestInv post)
    (hbe : post.be = s.be)
    (hglob : post.globals = s.globals)
    (hmem_out : ∀ a : BitVec 64, a ≠ BitVec.ofNat 64 (globN s "ev" + 16) → post.memory a = s.memory a)
    (hsp_le : memW post (globN s "ev" + 16) ≤ memW s (globN s "ev" + 16)) :
    EvmInvWith post S Nd ∧
    worldTypedIvls post S Nd = worldTypedIvls s S Nd ∧
    (evmChain post).map (frameObjects post) = (evmChain s).map (frameObjects s) ∧
    evmChain post = evmChain s ∧
    evmR post = evmR s ∧
    (HeadMemAligned s → HeadMemAligned post) := by
  obtain ⟨hAs, hInvAt, hTr_at, hAT_at⟩ := hInvW
  have hWT : WorldTypedWith s S Nd := ⟨hInvAt.1.1, hInvAt.1.2.1, hInvAt.1.2.2.1, hTr_at⟩
  obtain ⟨_, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW, hFO_pw, hFO_disj, _, hMarks, hRoles, hGas⟩ := hInvAt
  let e0 := globN s "ev"
  let c0 := globN s "cur_cont"
  have hch_eq_cons : ∃ tl, evmChain s = (e0, c0) :: tl := ⟨_, rfl⟩
  obtain ⟨chTail, hch_cons⟩ := hch_eq_cons
  have hhead_mem : (e0, c0) ∈ evmChain s := by rw [hch_cons]; exact List.mem_cons_self
  have hhead_FW := hFW_all _ hhead_mem
  obtain ⟨hb1, _, _, _⟩ := frameWF_bounds hAs.2 hhead_FW
  dsimp only at hb1
  have he0_align : e0 % 8 = 0 := (hhead_FW.1 (e0, 280) (by simp)).2.1
  have ha16_nat : (BitVec.ofNat 64 (e0 + 16)).toNat = e0 + 16 := Nat.mod_eq_of_lt (by omega)
  have hdom16 : s.memaddrs (BitVec.ofNat 64 (e0 + 16)) := by
    obtain ⟨_, hdom, _⟩ := (hhead_FW.1 (e0, 280) (by simp)).2.2.2 2 (by omega)
    simpa using hdom
  have hdom_eq : post.memaddrs = s.memaddrs := hGp.memaddrs.trans hAs.1.memaddrs.symm
  have heff : ByteRegionEffect s post [(e0, 280)] := by
    refine ⟨hGp.code.trans hAs.1.code.symm, hdom_eq,
      hGp.shMemaddrs.trans hAs.1.shMemaddrs.symm,
      hGp.baseAddr.trans hAs.1.baseAddr.symm, hbe, hglob, ?_, ?_, ?_⟩
    · intro a hna
      exact hmem_out a (by rintro rfl; exact hna hdom16)
    · intro a ha
      exact hmem_out a (by rintro rfl; exact ha (e0, 280) (by simp) ⟨by rw [ha16_nat]; omega, by rw [ha16_nat]; omega⟩)
    · intro b hb hno
      unfold memB
      have hal_b : (panByteAlignHOL (BitVec.ofNat 64 b)).toNat = b / 8 * 8 := by
        rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
      rw [hmem_out (panByteAlignHOL (BitVec.ofNat 64 b)), hbe]
      intro heq
      have := congrArg BitVec.toNat heq
      rw [hal_b, ha16_nat] at this
      exact hno (e0, 280) (by simp) ⟨by dsimp only; omega, by dsimp only; omega⟩
  have hglob_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, hglob]
  have hApost : ArenaReady post := ⟨hGp, arenaOK_congr hglob hAs.2⟩
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hglob_eq]
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hglob_eq]
  have hrec_fo : (e0, 280) ∈ frameObjects s (e0, c0) := by simp [frameObjects]
  have hrec_disj_wti : ∀ i ∈ worldTypedIvls s S Nd, i.2 = 0 ∨ Disj (e0, 280) i := by
    intro i hi
    unfold worldTypedIvls at hi
    simp only [List.mem_append] at hi
    rcases hi with ((((h1 | h2) | h3) | h4) | h5) | h6
    · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
      exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).1 t ht i hfp)
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
      exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _ (typedRec_in_fixedObjects s hr))
    · simp only [List.mem_singleton] at h3; subst h3
      have hfix_j : (if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap") ∈ fixedObjects s := by
        unfold fixedObjects
        apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right; simp
      exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _ hfix_j)
    · exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _ (blockOut_in_fixedObjects h4))
    · exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _ (bal_in_fixedObjects h5))
    · have hfl : (e0, 280) ∈ ((evmChain s).map (frameObjects s)).flatten := by
        rw [List.mem_flatten]
        exact ⟨frameObjects s (e0, c0), List.mem_map.2 ⟨_, hhead_mem, rfl⟩, hrec_fo⟩
      exact Or.inr (hAT_at _ hfl i h6)
  have hcell : SameTypedCells s post S Nd :=
    ByteRegionEffect.sameTypedCells (Rl := []) (extra := [(e0, 280)]) hAs.1.memaddrs hWT
      (fun _ h => by simp at h)
      (fun x hx => by simp at hx; subst hx; exact hrec_disj_wti)
      (by simpa using heff)
  have hfeq := fixedObjects_eq_of_nonHeapGlobalsKept hAs.2 hWT.1 hWT.2.2.1 hcell
    (fun name _ _ _ => by rw [hglob])
  have hFT_post := fixedTyped_of_eq hApost hWT.2.2.1 hh hsc hfeq
  obtain ⟨hWT_post, _⟩ := worldTypedWith_congr_w1 hAs hApost hh hsc
    (fun g _ => hglob_eq g) hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hW_post : WorldTyped post S :=
    ⟨hWT_post.1, hWT_post.2.1, hWT_post.2.2.1, Nd, hWT_post.2.2.2⟩
  have hwti_eq := worldTypedIvls_eq_of_cell_g09 hAs.2 hWT hcell (fun g _ _ _ => hglob_eq g)
  have hmemW_ne : ∀ a : Nat, a < 2 ^ 64 → a ≠ e0 + 16 → memW post a = memW s a := by
    intro a ha h1
    unfold memW
    rw [hmem_out (BitVec.ofNat 64 a)]
    intro heq
    have := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, ha16_nat] at this
    exact h1 this
  have hpw_head_tail :
      (frameObjects s (e0, c0)).Pairwise Disj ∧
      (∀ o1 ∈ frameObjects s (e0, c0),
        ∀ ec ∈ chTail, ∀ o2 ∈ frameObjects s ec, Disj o1 o2) := by
    have hpw := hFO_pw
    rw [hch_cons, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
    refine ⟨hpw.1, fun o1 ho1 ec hec o2 ho2 => hpw.2.2 o1 ho1 o2 ?_⟩
    rw [List.mem_flatten]
    exact ⟨frameObjects s ec, List.mem_map.2 ⟨ec, hec, rfl⟩, ho2⟩
  have hhead_disj_tail_fo : ∀ o ∈ ((c0, 104) :: (memW s (e0 + 8), 32 * memW s (e0 + 232)) ::
      (memW s (e0 + 24), memW s (e0 + 40)) :: (memW s (e0 + 88), 24) ::
      frameLogs s (e0, c0) :: frameRet s (e0, c0) :: frameLogObjects s (e0, c0)),
      Disj (e0, 280) o := by
    have hpw0 := hpw_head_tail.1
    unfold frameObjects at hpw0
    change ((e0, 280) :: ((c0, 104) :: (memW s (e0 + 8), 32 * memW s (e0 + 232)) ::
      (memW s (e0 + 24), memW s (e0 + 40)) :: (memW s (e0 + 88), 24) ::
      frameLogs s (e0, c0) :: frameRet s (e0, c0) :: frameLogObjects s (e0, c0))).Pairwise Disj at hpw0
    exact (List.pairwise_cons.1 hpw0).1
  have hdisj_e0_nonrec : ∀ ec ∈ evmChain s,
      Disj (e0, 280) (ec.2, 104) ∧
      Disj (e0, 280) (memW s (ec.1 + 88), 24) ∧
      Disj (e0, 280) (frameLogs s ec) ∧
      (∀ i < memW s (memW s (ec.1 + 88) + 8),
        Disj (e0, 280) (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40)) := by
    intro ec hec
    rw [hch_cons, List.mem_cons] at hec
    rcases hec with rfl | htail
    · refine ⟨hhead_disj_tail_fo _ (by simp), hhead_disj_tail_fo _ (by simp),
        hhead_disj_tail_fo _ (by simp), fun i hi => hhead_disj_tail_fo _ ?_⟩
      simp only [List.mem_cons]
      right; right; right; right; right; right
      unfold frameLogObjects; dsimp only
      exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
    · refine ⟨hpw_head_tail.2 _ hrec_fo ec htail _ (by simp [frameObjects]),
        hpw_head_tail.2 _ hrec_fo ec htail _ (by simp [frameObjects]),
        hpw_head_tail.2 _ hrec_fo ec htail _ (by simp [frameObjects]),
        fun i hi => hpw_head_tail.2 _ hrec_fo ec htail _ (logRecord_in_frameObjects_g09 hi)⟩
  have hrec_other_eq : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → k ≠ 16 → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → k % 8 = 0 → memW post (ec.2 + k) = memW s (ec.2 + k)) ∧
      (∀ k, k + 8 ≤ 24 → k % 8 = 0 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨hb_e, hb_c, hb_88, _⟩ := frameWF_bounds hAs.2 hFW
    have hc8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
    have h88_8 : (memW s (ec.1 + 88)) % 8 = 0 := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).2.1
    obtain ⟨hd_c, hd_88, _, _⟩ := hdisj_e0_nonrec ec hec
    refine ⟨?_,
      fun k hk hk8 => memW_eq_of_frameDisj_g09 hAs.1.memaddrs heff hb_c hc8 hk8 hk
        (fun x hx => by simp at hx; subst hx; exact hd_c),
      fun k hk hk8 => memW_eq_of_frameDisj_g09 hAs.1.memaddrs heff hb_88 h88_8 hk8 hk
        (fun x hx => by simp at hx; subst hx; exact hd_88)⟩
    intro k hk hk16
    apply hmemW_ne (ec.1 + k) (by omega)
    rw [hch_cons, List.mem_cons] at hec
    rcases hec with rfl | htail
    · dsimp only; omega
    · have hd := hpw_head_tail.2 (e0, 280) hrec_fo ec htail (ec.1, 280) (by simp [frameObjects])
      rcases hd with h0 | h0 | h1 | h2
      · dsimp only at h0; omega
      · dsimp only at h0; omega
      · dsimp only at h1 ⊢; omega
      · dsimp only at h2 ⊢; omega
  have htail_all_eq : ∀ ec ∈ chTail, ∀ k, k + 8 ≤ 280 → k % 8 = 0 → memW post (ec.1 + k) = memW s (ec.1 + k) := by
    intro ec htail k hk hk8
    have hec : ec ∈ evmChain s := by rw [hch_cons]; exact List.mem_cons_of_mem _ htail
    have hFW := hFW_all ec hec
    obtain ⟨hb_e, _, _, _⟩ := frameWF_bounds hAs.2 hFW
    have he8 : ec.1 % 8 = 0 := (hFW.1 (ec.1, 280) (by simp)).2.1
    have hd := hpw_head_tail.2 (e0, 280) hrec_fo ec htail (ec.1, 280) (by simp [frameObjects])
    exact memW_eq_of_frameDisj_g09 hAs.1.memaddrs heff hb_e he8 hk8 hk
      (fun x hx => by simp at hx; subst hx; exact hd)
  have hchain_aux : ∀ (fuel e c : Nat),
      (∀ ec ∈ evmChainFrom s fuel e c, ec ∈ evmChain s) →
      evmChainFrom post fuel e c = evmChainFrom s fuel e c := by
    intro fuel
    induction fuel with
    | zero => intros; rfl
    | succ fuel ih =>
      intro e c hsub
      have hec : (e, c) ∈ evmChain s := hsub (e, c) (by simp [evmChainFrom])
      obtain ⟨_, hc_eq, _⟩ := hrec_other_eq (e, c) hec
      have hc16 := hc_eq 16 (by omega) (by omega)
      have hc0 : memW post c = memW s c := by simpa using hc_eq 0 (by omega) (by omega)
      have hc8 := hc_eq 8 (by omega) (by omega)
      simp only [evmChainFrom, hc16, hc0, hc8]
      split
      · rfl
      · rename_i hne16
        rw [ih (memW s c) (memW s (c + 8))]
        intro ec' hec'
        apply hsub ec'
        simp only [evmChainFrom, hne16, ↓reduceIte, List.mem_cons]
        exact Or.inr hec'
  have hchain_eq : evmChain post = evmChain s := by
    unfold evmChain
    rw [hglob_eq "ev", hglob_eq "cur_cont"]
    exact hchain_aux (Wave8GuestInv.maxChain + 1) (globN s "ev") (globN s "cur_cont") (fun _ h => h)
  have hframeLogs_eq : ∀ ec ∈ evmChain s, frameLogs post ec = frameLogs s ec := by
    intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_other_eq ec hec
    unfold frameLogs
    rw [he_eq 88 (by omega) (by omega),
        show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by simpa using h88_eq 0 (by omega) (by omega),
        h88_eq 16 (by omega) (by omega)]
  have hframeRet_eq : ∀ ec ∈ evmChain s, frameRet post ec = frameRet s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_other_eq ec hec
    unfold frameRet
    rw [he_eq 216 (by omega) (by omega), he_eq 144 (by omega) (by omega)]
  have hlogs_congr : ∀ ec ∈ evmChain s,
      frameLogObjects post ec = frameLogObjects s ec ∧ LogsListOK post (memW post (ec.1 + 88)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨_, _, _, hfob⟩ := frameWF_bounds hAs.2 hFW
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_other_eq ec hec
    obtain ⟨_, _, hd_fl, hd_lr⟩ := hdisj_e0_nonrec ec hec
    refine logsList_and_objects_congr_g09 hFW hdom_eq hglob_eq
      (he_eq 88 (by omega) (by omega)) h88_eq ?_ ?_
    · intro i hi
      have hfl_in : frameLogs s ec ∈ frameObjects s ec := by simp [frameObjects]
      have hlen_le : memW s (memW s (ec.1 + 88) + 8) ≤ memW s (memW s (ec.1 + 88) + 16) :=
        hFW.2.2.2.2.2.2.2.2.2.2.2.1
      have hfl_b : (frameLogs s ec).1 + (frameLogs s ec).2 ≤ 2 ^ 64 := by
        rcases hfob _ hfl_in with h0 | hb
        · unfold frameLogs at h0; dsimp only at h0; omega
        · exact hb
      have hfl_8 : (memW s (memW s (ec.1 + 88))) % 8 = 0 :=
        hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
      exact memW_eq_of_frameDisj_g09 hAs.1.memaddrs heff hfl_b hfl_8 (by omega) (by unfold frameLogs; dsimp only; omega)
        (fun x hx => by simp at hx; subst hx; exact hd_fl)
    · intro i hi off hoff hoff8
      have hlr_in := logRecord_in_frameObjects_g09 (s := s) (ec := ec) hi
      have hlr_b : memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + 40 ≤ 2 ^ 64 := by
        rcases hfob _ hlr_in with h0 | hb
        · dsimp only at h0; omega
        · exact hb
      have hlr_8 : (memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) % 8 = 0 := by
        rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
        · have he88_in := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1
          have hss : 0 < scratchStart := by rw [R11Shards.scratchStart_val]; decide
          have := hAs.2.2.2.1; have := hAs.2.2.2.2.1; have := he88_in.1
          dsimp only at this
          omega
        · exact (hent i hi).2.1.1
      exact memW_eq_of_frameDisj_g09 hAs.1.memaddrs heff hlr_b hlr_8 hoff8 hoff
        (fun x hx => by simp at hx; subst hx; exact hd_lr i hi)
  have hframeObjects_eq : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_other_eq ec hec
    unfold frameObjects
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
        he_eq 24 (by omega) (by omega), he_eq 40 (by omega) (by omega),
        he_eq 88 (by omega) (by omega), hframeLogs_eq ec hec, hframeRet_eq ec hec,
        (hlogs_congr ec hec).1]
  have hframeScratch_eq : ∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_other_eq ec hec
    unfold frameScratch
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega), he_eq 88 (by omega) (by omega)]
  have hmap_fo : (evmChain post).map (frameObjects post) = (evmChain s).map (frameObjects s) := by
    rw [hchain_eq]; exact List.map_congr_left hframeObjects_eq
  have hmap_fo_s : (evmChain s).map (frameObjects post) = (evmChain s).map (frameObjects s) :=
    List.map_congr_left hframeObjects_eq
  have hframeRoleSlots_eq : frameRoleSlots post (evmChain s) = frameRoleSlots s (evmChain s) := by
    unfold frameRoleSlots
    apply List.flatMap_congr; intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_other_eq ec hec
    rw [he_eq 136 (by omega) (by omega), he_eq 168 (by omega) (by omega), he_eq 176 (by omega) (by omega)]
  have hfp_eq_all : ∀ t ∈ S, htabFootprint post t = htabFootprint s t :=
    fun t ht => htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1
  have hne_eq : nodeExtents post Nd = nodeExtents s Nd := nodeExtents_eq hTr_at.1 hcell
  have hR_eq : evmR post = evmR s :=
    evmR_eq_of_chain_and_words hchain_eq fun ec hec =>
      ⟨(hrec_other_eq ec hec).1 64 (by omega) (by omega),
       (hrec_other_eq ec hec).1 192 (by omega) (by omega)⟩
  have hInvAt_post : EvmInvAt post S := by
    refine ⟨hW_post, ?_⟩
    dsimp only
    rw [hchain_eq]
    refine ⟨hch_ne, hch_len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨ec, hec, hk0⟩ := hch_last
      have hec_mem : ec ∈ evmChain s := List.mem_of_mem_getLast? hec
      exact ⟨ec, hec, by rw [(hrec_other_eq ec hec_mem).2.1 16 (by omega) (by omega)]; exact hk0⟩
    · intro ec hec
      obtain ⟨he_eq, _, h88_eq⟩ := hrec_other_eq ec hec
      obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, _, c17⟩ := hFW_all ec hec
      have he16_le : memW post (ec.1 + 16) ≤ memW s (ec.1 + 16) := by
        have hec' := hec
        rw [hch_cons, List.mem_cons] at hec'
        rcases hec' with rfl | htail
        · exact hsp_le
        · rw [htail_all_eq ec htail 16 (by omega) (by omega)]
      have hlo_ok := (hlogs_congr ec hec).2
      have hmsg_ok : MsgOwned post S (memW post (ec.1 + 112)) := by
        rw [he_eq 112 (by omega) (by omega)]
        exact msgOwned_congr_g09 hAs hApost hh hsc (fun g _ => hglob_eq g) hdom_eq hglob_eq
          ⟨hWT.1, hWT.2.1, hWT.2.2.1⟩ hFT_post hfeq hTr_at hcell hfp_eq_all hchain_eq hframeObjects_eq c17
      unfold FrameWF
      dsimp only
      rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
          he_eq 88 (by omega) (by omega), he_eq 24 (by omega) (by omega),
          he_eq 40 (by omega) (by omega), he_eq 32 (by omega) (by omega),
          he_eq 136 (by omega) (by omega), he_eq 168 (by omega) (by omega),
          he_eq 176 (by omega) (by omega),
          h88_eq 16 (by omega) (by omega), h88_eq 8 (by omega) (by omega),
          hframeLogs_eq ec hec, he_eq 216 (by omega) (by omega), he_eq 144 (by omega) (by omega),
          hframeRet_eq ec hec,
          hglob_eq "scratch_ptr", hglob_eq "frame_mem_ptr", hglob_eq "heap_ptr", hglob_eq "evm_empty"]
      rw [he_eq 88 (by omega) (by omega)] at hlo_ok
      refine ⟨?_, c2, (wordsOK_congr_of_dom_g09 hdom_eq).2 c3, c4, le_trans he16_le c5, c6, c7,
        c8, c9, c10, c11, c12, c13, (wordsOK_congr_of_dom_g09 hdom_eq).2 c14, ?_, hlo_ok, hmsg_ok⟩
      · intro i hi
        obtain ⟨hin, hw⟩ := c1 i hi
        exact ⟨hin, (wordsOK_congr_of_dom_g09 hdom_eq).2 hw⟩
      · rcases c15 with h0 | ⟨hin, hw⟩
        · exact Or.inl h0
        · exact Or.inr ⟨hin, (wordsOK_congr_of_dom_g09 hdom_eq).2 hw⟩
    · intro ec hec
      have hec_tail : ec ∈ chTail := by rw [hch_cons, List.tail_cons] at hec; exact hec
      unfold FrameRoom
      rw [htail_all_eq ec hec_tail 16 (by omega) (by omega),
          htail_all_eq ec hec_tail 232 (by omega) (by omega)]
      exact hFR_all ec hec
    · intro i hi
      have hi0 : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
      have hi1 : (evmChain s)[i + 1] ∈ evmChain s := List.getElem_mem _
      rw [(hrec_other_eq _ hi0).2.1 80 (by omega) (by omega),
          (hrec_other_eq _ hi0).2.1 72 (by omega) (by omega),
          (hrec_other_eq _ hi1).1 40 (by omega) (by omega)]
      exact hRW i hi
    · rw [hmap_fo_s]; exact hFO_pw
    · intro ec hec o ho
      rw [hframeObjects_eq ec hec] at ho
      rw [hfeq]
      refine ⟨fun t ht i hi => ?_, (hFO_disj ec hec o ho).2⟩
      rw [hfp_eq_all t ht] at hi
      exact (hFO_disj ec hec o ho).1 t ht i hi
    · rw [hmap_fo_s]
      refine ⟨Nd, hWT_post.2.2.2, fun o ho j hj => ?_⟩
      rw [hne_eq] at hj
      exact hAT_at o ho j hj
    · have hworldRefs_eq := worldTableRefs_eq_of_cell_g09 hAs.2 hWT hcell (fun g _ => hglob_eq g)
      have hdelEx_iff : ∀ i t, DelExclusive post S (evmChain s) i t ↔ DelExclusive s S (evmChain s) i t := by
        intro i t
        unfold DelExclusive
        rw [hworldRefs_eq]
        refine and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun hj =>
          forall_congr' fun k => imp_congr_right fun hk => ?_)
        have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
        have hk_le : k + 8 ≤ 280 ∧ k ≠ 16 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
        rw [(hrec_other_eq _ hj_mem).1 k hk_le.1 hk_le.2]
      intro i hi
      have hi_mem : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
      have hm_eq := (hrec_other_eq _ hi_mem).2.1 48 (by omega) (by omega)
      have hmm_eq := (hrec_other_eq _ hi_mem).2.1 56 (by omega) (by omega)
      have he24_eq := (hrec_other_eq _ hi_mem).1 24 (by omega) (by omega)
      have htake_eq : ((evmChain s).take (i + 1)).map (fun ec => memW post (ec.1 + 136)) =
          ((evmChain s).take (i + 1)).map (fun ec => memW s (ec.1 + 136)) := by
        apply List.map_congr_left; intro ec hec
        exact (hrec_other_eq ec (List.mem_of_mem_take hec)).1 136 (by omega) (by omega)
      have hM := hMarks i hi
      dsimp only at hM ⊢
      rw [hm_eq, hmm_eq, he24_eq, hframeScratch_eq _ hi_mem, hfeq, htake_eq]
      obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM
      refine ⟨m1, m2, m3, m4, ?_, m6, m7, ?_, m9⟩
      · intro j hj hij
        have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
        rw [hframeScratch_eq _ hj_mem, hframeObjects_eq _ hj_mem, hframeLogs_eq _ hj_mem,
            (hrec_other_eq _ hj_mem).1 112 (by omega) (by omega)]
        exact m5 j hj hij
      · intro t ht
        rw [hfp_eq_all t ht, hdelEx_iff i t]
        exact m8 t ht
    · have hcg : ∀ g ∈ coreWorldGlobals, globN post g = globN s g := fun g _ => hglob_eq g
      rw [worldRoleSlots_eq hAs.2 hWT.1 hWT.2.2.1 hcell hcg,
          hframeRoleSlots_eq,
          journalRoleSlots_eq hAs.2 hWT.2.1 hWT.2.2.1 hcell hcg]
      unfold RolesOK at hRoles ⊢
      refine ⟨fun a ha => ?_, hRoles.2⟩
      obtain ⟨haS, hkl⟩ := hRoles.1 a ha
      have htb := ((hWT.1.2.1 a.1 haS).1.1 (a.1, 88) (by simp [htabFootprint])).1
      rw [htab_hdr_eq hcell haS htb 0 (by omega)]
      exact ⟨haS, hkl⟩
    · have hsum_eq : ((evmChain s).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)).sum =
          ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum := by
        unfold evmR at hR_eq; rw [hchain_eq] at hR_eq; exact hR_eq
      rw [hsum_eq]; exact hGas
  have hHM_imp : HeadMemAligned s → HeadMemAligned post :=
    headMemAligned_congr_head hglob fun off hoff => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl <;> exact (hrec_other_eq _ hhead_mem).1 _ (by omega) (by omega)
  refine ⟨⟨hApost, hInvAt_post, hWT_post.2.2.2, ?_⟩, hwti_eq, hmap_fo, hchain_eq, hR_eq, hHM_imp⟩
  rw [hmap_fo, hne_eq]
  exact hAT_at

private theorem stack_pop_body_evmInvWith {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hInvW : EvmInvWith s S Nd)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_stack_pop)).1) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_stack_pop)).2
    EvmInvWith post S Nd ∧
    worldTypedIvls post S Nd = worldTypedIvls s S Nd ∧
    (evmChain post).map (frameObjects post) = (evmChain s).map (frameObjects s) ∧
    post.globals = s.globals ∧
    post.memaddrs = s.memaddrs ∧
    evmChain post = evmChain s ∧
    evmR post = evmR s ∧
    (HeadMemAligned s → HeadMemAligned post) ∧
    (∀ a : BitVec 64, a ≠ BitVec.ofNat 64 (globN s "ev" + 16) → post.memory a = s.memory a) := by
  dsimp only
  have hInv : EvmInv s := evmInvWith_to_evmInv hInvW
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
  have hnot_err : ¬ Resumes (some (.error : PanSemResultExact 64)) := by
    rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata s (sourceFnBody Guest.Software.guestFn_stack_pop)
  have hba := evaluate_baseAddr s (sourceFnBody Guest.Software.guestFn_stack_pop)
  let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_stack_pop)).2
  have hGp : GuestInv post :=
    ⟨hmeta.1.trans hInvW.1.1.code, hmeta.2.1.trans hInvW.1.1.memaddrs,
     hmeta.2.2.2.1.trans hInvW.1.1.shMemaddrs, hba.trans hInvW.1.1.baseAddr⟩
  have hbe : post.be = s.be := hmeta.2.2.1
  have hcore :
      post.globals = s.globals ∧
      (∀ a : BitVec 64, a ≠ BitVec.ofNat 64 (globN s "ev" + 16) → post.memory a = s.memory a) ∧
      memW post (globN s "ev" + 16) ≤ memW s (globN s "ev" + 16) := by
    change (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_stack_pop)).2.globals = s.globals ∧
      (∀ a : BitVec 64, a ≠ BitVec.ofNat 64 (globN s "ev" + 16) →
        (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_stack_pop)).2.memory a = s.memory a) ∧
      memW (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_stack_pop)).2 (globN s "ev" + 16) ≤
        memW s (globN s "ev" + 16)
    revert hres
    rw [hb, evaluateHOLFiniteState_dec_total]; dsimp only
    split
    · intro hres; exact absurd hres hnot_err
    · rename_i vsp hload
      have hvsp_w : ∃ sp : BitVec 64, vsp = .val (.word sp) ∧ sp.toNat = memW s (globN s "ev" + 16) := by
        simp only [evalHOLExact, evalListHOLExact, hevw, valueIsWord, valueWord, wordOpHOL, wordOp,
          List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr, BitVec.add_zero,
          memLoadHOLExact] at hload
        split at hload
        · have h16z : (16 : BitVec 64) + 0 = 16#64 := rfl
          rw [h16z] at hload
          rcases hm16 : s.memory (evw + 16#64) with ⟨sp⟩
          rw [hm16] at hload
          split at hload
          · injection hload with hload'
            refine ⟨sp, hload'.symm, ?_⟩
            have heq16 : BitVec.ofNat 64 (globN s "ev" + 16) = evw + 16#64 := by
              apply BitVec.eq_of_toNat_eq
              have : (16#64 : BitVec 64).toNat = 16 := rfl
              rw [BitVec.toNat_ofNat, BitVec.toNat_add, hevw_nat, this]
            unfold memW; rw [heq16, hm16]
          · simp at hload
        · simp at hload
      obtain ⟨sp, rfl, hsp_nat⟩ := hvsp_w
      split
      · dsimp only
        set s1 := setVarHOLFinite (ofString "sp") (.val (.word sp)) s
        have hs1_sp : s1.locals.lookup (ofString "sp") = some (.val (.word sp)) := by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
        have hcmp : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
            (.cmp .equal (.var .local (ofString "sp")) (.const 0)) =
            some (.val (.word (if sp = 0 then 1 else 0))) := by
          simp [evalHOLExact, hs1_sp, Compiler.Encoders.Asm.wordCmpHOL]
        rw [hcmp]; dsimp only
        by_cases hsp0 : sp = 0
        · subst hsp0
          have h10 : ((1 : BitVec 64) = 0) = False := by decide
          simp only [↓reduceIte, h10]
          rcases hraise : evaluateHOLFiniteState s1 (.raise (ofString "EvmErr") (.const 2)) with ⟨rr, sr⟩
          have hr_nn : rr ≠ none ∧ sr.globals = s.globals ∧ sr.memory = s.memory := by
            rw [evaluateHOLFiniteState_raise] at hraise; dsimp only [evalHOLExact] at hraise
            split at hraise
            · split at hraise <;> (injection hraise with h1 h2; subst h1 h2; exact ⟨by simp, rfl, rfl⟩)
            · injection hraise with h1 h2; subst h1 h2; exact ⟨by simp, rfl, rfl⟩
          cases rr with
          | none => exact absurd rfl hr_nn.1
          | some _ =>
            dsimp only; intro _
            refine ⟨hr_nn.2.1, fun x _ => ?_, ?_⟩
            · change sr.memory x = s.memory x; rw [hr_nn.2.2]
            · unfold memW; change (match sr.memory _ with | .word w => w.toNat) ≤ _; rw [hr_nn.2.2]
        · have hsp_pos : 0 < memW s (globN s "ev" + 16) := by
            rw [← hsp_nat]
            exact Nat.pos_of_ne_zero (fun hz => hsp0 (BitVec.eq_of_toNat_eq hz))
          rw [if_neg hsp0]
          simp only [↓reduceIte, evaluateHOLFiniteState_skip]
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
          have hsub : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
              (.op .sub [.var .local (ofString "sp"), .const 1]) = some (.val (.word (sp - 1))) := by
            simp [evalHOLExact, evalListHOLExact, hs1_sp, valueIsWord, valueWord, wordOpHOL, wordOp]
          have hval_sp : s1.isValidValueHOLFinite .local (ofString "sp") (.val (.word (sp - 1))) = true := by
            simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hs1_sp,
              shapeOfHOLExact, shapeEqHOL]
          rw [hsub]; dsimp only
          rw [if_pos hval_sp]; dsimp only
          set s2 := setKvarHOLFinite .local (ofString "sp") (.val (.word (sp - 1))) s1
          rw [evaluateHOLFiniteState_seq_line780]
          rcases hst : evaluateHOLFiniteState s2
              (.store (.op .add [.var .global (ofString "ev"), .const 16]) (.var .local (ofString "sp"))) with ⟨r2, s3⟩
          cases r2 with
          | some res2 =>
            have herr := store_some_eq_error_g09 hst; subst herr
            dsimp only; intro hres; exact absurd hres hnot_err
          | none =>
            dsimp only
            obtain ⟨w2, hw2_ev, hs3_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s2) (post := s3)
              (gname := "ev") (gbase := globN s "ev") (off := 16) hevw hevw_nat (by omega)
              (fun u hu => by
                have hsp2 : s2.locals.lookup (ofString "sp") = some (.val (.word (sp - 1))) := by
                  simp [s2, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                change s2.locals.lookup (ofString "sp") = some u at hu
                rw [hsp2] at hu; injection hu with hu'; exact ⟨sp - 1, hu'.symm⟩) hst
            have hw2_eq : w2 = sp - 1 := by
              have hsp2 : s2.locals.lookup (ofString "sp") = some (.val (.word (sp - 1))) := by
                simp [s2, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              change s2.locals.lookup (ofString "sp") = some (.val (.word w2)) at hw2_ev
              rw [hsp2] at hw2_ev
              injection hw2_ev with h'; injection h' with h''; injection h'' with h'''; exact h'''.symm
            subst hw2_eq
            have hsp1_le : (sp - 1).toNat ≤ memW s (globN s "ev" + 16) := by
              rw [BitVec.toNat_sub, hsp_nat]
              have : (1 : BitVec 64).toNat = 1 := rfl
              rw [this]; omega
            intro _
            have hret_mem_glob :
                (evaluateHOLFiniteState s3 (.return retExp)).2.globals = s3.globals ∧
                (evaluateHOLFiniteState s3 (.return retExp)).2.memory = s3.memory := by
              rw [evaluateHOLFiniteState_return]
              split
              · exact ⟨rfl, rfl⟩
              · split <;> exact ⟨rfl, rfl⟩
            refine ⟨hret_mem_glob.1.trans (by simp [hs3_eq, s2, s1, setKvarHOLFinite, setVarHOLFinite]),
              fun x hx => ?_, ?_⟩
            · have hm_eq := congrFun hret_mem_glob.2 x
              rw [hm_eq, hs3_eq]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hx]; rfl
            · unfold memW
              have hm_eq := congrFun hret_mem_glob.2 (BitVec.ofNat 64 (globN s "ev" + 16))
              rw [hm_eq, hs3_eq]; dsimp only [R14Shards.OpHandlersA.updW]
              rw [if_pos rfl]
              exact hsp1_le
      · intro hres; exact absurd hres hnot_err
  obtain ⟨hInvW_p, hwti_p, hfo_p, hch_p, hR_p, hHM_p⟩ :=
    evmInvWith_of_head_sp_cell hInvW hGp hbe hcore.1 hcore.2.1 hcore.2.2
  exact ⟨hInvW_p, hwti_p, hfo_p, hcore.1, hmeta.2.1, hch_p, hR_p, hHM_p, hcore.2.1⟩

private theorem decCall_alloc_step_g09 {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {charged : Bool} {nm : MlS} {szExp : ExpHOL 64} {nw : BitVec 64} {cont : ProgHOL 64}
    (hcode : s.code = originalRuntimeCode)
    (hInvW : EvmInvWith s S Nd)
    (_hlen : (evmChain s).length = (evmChain s0).length)
    (_hR : if charged then evmR s < evmR s0 else evmR s ≤ evmR s0)
    (hsz : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) szExp =
      some (.val (.word nw)))
    (hnt : (evaluateHOLFiniteState s (.decCall nm .one (ofString "alloc") [szExp] cont)).1 ≠ some .timeOut)
    (hcont : ∀ (pw qw : BitVec 64) (s' : PanSemStateFiniteExact 64 F),
      s'.code = originalRuntimeCode →
      EvmInvWith s' S Nd →
      worldTypedIvls s' S Nd = worldTypedIvls s S Nd →
      (evmChain s').map (frameObjects s') = (evmChain s).map (frameObjects s) →
      evmChain s' = evmChain s →
      evmR s' = evmR s →
      (HeadMemAligned s → HeadMemAligned s') →
      s'.globals = s.globals.update (ofString "heap_ptr", .val (.word qw)) →
      s'.memory = s.memory →
      s'.memaddrs = s.memaddrs →
      s'.locals = s.locals.update (nm, .val (.word pw)) →
      globN s "heap_ptr" = pw.toNat →
      globN s' "heap_ptr" = qw.toNat →
      pw.toNat + nw.toNat ≤ qw.toNat →
      qw.toNat ≤ heapLimit →
      pw.toNat % 8 = 0 →
      qw.toNat % 8 = 0 →
      sourceBase ≤ pw.toNat →
      WordsOK s' (pw.toNat, qw.toNat - pw.toNat) →
      IvlsDisj [(pw.toNat, qw.toNat - pw.toNat)]
        (worldTypedIvls s' S Nd ++ ((evmChain s').map (frameObjects s')).flatten) →
      (evaluateHOLFiniteState s' cont).1 ≠ some .timeOut →
      OpDispatchPost s0 (evaluateHOLFiniteState s' cont).1 (evaluateHOLFiniteState s' cont).2) :
    OpDispatchPost s0
      (evaluateHOLFiniteState s (.decCall nm .one (ofString "alloc") [szExp] cont)).1
      (evaluateHOLFiniteState s (.decCall nm .one (ofString "alloc") [szExp] cont)).2 := by
  have hp_pos : 0 < globN s "heap_ptr" := by
    have h1 := hInvW.1.2.1
    rw [R11Shards.sourceBase_val] at h1
    omega
  obtain ⟨pw, hp_lk, hp_nat⟩ := global_word_of_pos s "heap_ptr" hp_pos
  have hp_le_cMax : pw.toNat ≤ InitECandidate.Solver.HeapPotential.cMax.toNat := by
    have hlim := hInvW.1.2.2.1
    have hcMax_val : InitECandidate.Solver.HeapPotential.cMax.toNat = 2952790016 := rfl
    rw [R11Shards.heapLimit_val] at hlim
    omega
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [szExp] =
      some [.val (.word nw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hsz]
  have hlook := pan_one_word_lookup s.code.lookup (ofString "alloc") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_alloc) nw (by rw [hcode]; exact OpHandlers.lookup_alloc)
  rw [hargs] at hnt ⊢; dsimp only at hnt ⊢
  rw [hlook] at hnt ⊢; dsimp only at hnt ⊢
  by_cases hclk : s.clock = 0
  · simp [hclk] at hnt
  · simp only [hclk, ↓reduceIte] at hnt ⊢
    let cal := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word nw))
    let ent := callEntryStateHOLFinite s cal
    have hne_err : ¬ IsEvmErr (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_alloc)).1 :=
      alloc_body_no_evmErr ent hcode
    have hal_gen := Wave8GuestInv.M13.evaluate_alloc_body_general ent pw nw hcode hp_le_cMax hp_lk
      (by simp [ent, cal, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    have hal_meta := PanRunBounded.evaluateHOLFiniteState_metadata ent (sourceFnBody Guest.Software.guestFn_alloc)
    have hal_ba := evaluate_baseAddr ent (sourceFnBody Guest.Software.guestFn_alloc)
    rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_alloc) with ⟨ral, sal⟩
    change evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_alloc) = (ral, sal) at hrun
    simp only [ent, cal, hrun] at hnt hne_err hal_gen hal_meta hal_ba ⊢
    cases ral with
    | none => exact opDispatchPost_error s0 sal
    | some ral0 =>
      cases ral0 with
      | timeOut => simp at hnt
      | «break» | «continue» => exact opDispatchPost_error s0 sal
      | error => exact opDispatchPost_error s0 sal.emptyLocalsHOLFinite
      | finalFfi _ =>
        refine opDispatchPost_other (fun _ h => by cases h) ?_
        rintro ⟨_, h⟩; cases h
      | exception eid ev =>
        refine opDispatchPost_other (fun _ h => by cases h) ?_
        rintro ⟨v, h⟩; injection h with h'; injection h' with he hw
        exact hne_err ⟨v, by rw [he, hw]⟩
      | returned val_al =>
        obtain ⟨rfl, hsal_glob, hsal_mem, hq_ge, hq_le_cMax, hq_mod8⟩ := hal_gen val_al rfl
        let qw : BitVec 64 := (pw + (nw + 7)) &&& ((0 : BitVec 64) - 8)
        change pw.toNat + nw.toNat ≤ qw.toNat at hq_ge
        change qw.toNat ≤ InitECandidate.Solver.HeapPotential.cMax.toNat at hq_le_cMax
        change qw.toNat % 8 = 0 at hq_mod8
        have hq_lim : qw.toNat ≤ heapLimit := by
          have hcMax_val : InitECandidate.Solver.HeapPotential.cMax.toNat = 2952790016 := rfl
          rw [R11Shards.heapLimit_val]; omega
        have hsh_al : (shapeEqHOL (shapeOfHOLExact (.val (.word pw) : ValueHOL 64)) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word pw) : ValueHOL 64)) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        simp only [hsh_al, ↓reduceIte] at hnt ⊢
        let s' := setVarHOLFinite nm (.val (.word pw)) { sal with locals := s.locals }
        have hs'_code : s'.code = originalRuntimeCode := hal_meta.1.trans hcode
        have hs'_step := evmInvWith_of_alloc_pure (post := s') hInvW hp_lk hq_ge hq_lim hq_mod8
          hal_meta.1 hal_meta.2.1 hal_meta.2.2.2.1 hal_ba hal_meta.2.2.1 hsal_glob hsal_mem
        obtain ⟨hs'_InvW, hs'_wti, hs'_fo, hs'_ch, hs'_R, hs'_HM, hp_g, hq_g, hp_m8, hp_lo, hw_blk, hdj_blk⟩ := hs'_step
        have hb_cont := hcont pw qw s' hs'_code hs'_InvW hs'_wti hs'_fo hs'_ch hs'_R hs'_HM
          hsal_glob hsal_mem hal_meta.2.1 rfl hp_g hq_g hq_ge hq_lim hp_m8 hq_mod8 hp_lo hw_blk hdj_blk hnt
        exact opDispatchPost_congr_lc rfl rfl rfl hb_cont

private theorem bswap64_body_ro_g09 {F : Type} (s : PanSemStateFiniteExact 64 F) (Rl : List Ivl) :
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
  have hret_eff : ∀ (st : PanSemStateFiniteExact 64 F) (ex : ExpHOL 64),
      ByteRegionEffect st (evaluateHOLFiniteState st (.return ex)).2 Rl := by
    intro st ex
    have hret : (evaluateHOLFiniteState st (.return ex)).2 =
        { st with locals := (evaluateHOLFiniteState st (.return ex)).2.locals } := by
      rw [evaluateHOLFiniteState_return]; split <;> [rfl; (split <;> rfl)]
    conv => arg 2; rw [hret]
    exact (ByteRegionEffect.refl st Rl).with_locals_clock _ st.clock
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
  exact hs1.trans (hseq_ro s1 _ _ (hasgn_eff s1 _ _) (fun s2 hs2 => hs2.trans (hret_eff s2 _)))

private theorem decCall_bswap64_eff_g09 {F : Type} {s : PanSemStateFiniteExact 64 F}
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
        _ _ body' _ ret' vals callee (by rw [hcode]; exact lookup_bswap64_b) hl
      subst hinst
      have hret_eq : ret' = .one := by
        unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
        split at hl
        · cases hl
        · rename_i eb el es hraw
          have hinj := Option.some.inj hl
          rcases Prod.mk.inj hinj with ⟨_, hr2⟩; rcases Prod.mk.inj hr2 with ⟨_, rfl⟩
          unfold lookupCodeHOLExact at hraw; rw [hcode, lookup_bswap64_b] at hraw; dsimp only at hraw
          split at hraw <;> [ (injection hraw with h'; exact (Prod.mk.inj (Prod.mk.inj h').2).2.symm); cases hraw ]
      subst hret_eq
      split
      · exact (ByteRegionEffect.refl s Rl).with_locals_clock _ _
      · have heff_entry : ByteRegionEffect s (callEntryStateHOLFinite s callee) Rl :=
          (ByteRegionEffect.refl s Rl).with_locals_clock _ _
        have heff_b := bswap64_body_ro_g09 (callEntryStateHOLFinite s callee) Rl
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
              have ha_mid : mid.locals.lookup (ofString "a") = s.locals.lookup (ofString "a") := by
                simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "w" ≠ ofString "a" by decide]
              have hw_mid : ∃ wv : BitVec 64, mid.locals.lookup (ofString "w") = some (.val (.word wv)) :=
                ⟨wv, by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
              exact (heff_mid.trans (hcont mid hc_mid hm_mid hout_mid ha_mid hw_mid)).with_locals_clock _ _
            · exact heff_sb
          | timeOut | error | exception _ _ | finalFfi _ => exact heff_sb.with_locals_clock _ _
          | «break» | «continue» => exact heff_sb

private theorem seq_call_bswap64_eff_g09 {F : Type} {s : PanSemStateFiniteExact 64 F}
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
        _ _ body' _ ret' vals callee (by rw [hcode]; exact lookup_bswap64_b) hl
      subst hinst
      have hret_eq : ret' = .one := by
        unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
        split at hl
        · cases hl
        · rename_i eb el es hraw
          have hinj := Option.some.inj hl
          rcases Prod.mk.inj hinj with ⟨_, hr2⟩; rcases Prod.mk.inj hr2 with ⟨_, rfl⟩
          unfold lookupCodeHOLExact at hraw; rw [hcode, lookup_bswap64_b] at hraw; dsimp only at hraw
          split at hraw <;> [ (injection hraw with h'; exact (Prod.mk.inj (Prod.mk.inj h').2).2.symm); cases hraw ]
      subst hret_eq
      split at hc
      · injection hc with hr hsc; subst hr hsc; exact (ByteRegionEffect.refl s Rl).with_locals_clock _ _
      · have heff_entry : ByteRegionEffect s (callEntryStateHOLFinite s callee) Rl :=
          (ByteRegionEffect.refl s Rl).with_locals_clock _ _
        have heff_b := bswap64_body_ro_g09 (callEntryStateHOLFinite s callee) Rl
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

private theorem seq_store_word_eff_g09 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {dstExp valExp : ExpHOL 64} {base w : BitVec 64} {off len : Nat} {cont : ProgHOL 64}
    (hma : s.memaddrs = ordinaryDomain) (hbase_lt : base.toNat + len ≤ heapEnd) (hoff : off + 8 ≤ len)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word (base + BitVec.ofNat 64 off))))
    (hval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
      some (.val (.word w)))
    (hcont : ∀ s1 : PanSemStateFiniteExact 64 F,
      s1.code = s.code → s1.memaddrs = s.memaddrs → s1.locals = s.locals →
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
    have hnat : (base + BitVec.ofNat 64 off).toNat = base.toNat + off := by
      have he_val := R11Shards.heapEnd_val
      have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by norm_num
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, h264, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have heff1 := ByteRegionEffect.of_store_word (Rl := [(base.toNat, len)]) hma h1
      (fun v hv => by rw [hval] at hv; injection hv with h; exact ⟨w, h.symm⟩)
      (fun addr ha _ => by
        rw [hdst] at ha
        injection ha with e1; injection e1 with e2; injection e2 with e3; subst e3
        exact ⟨(base.toNat, len), List.mem_singleton.2 rfl, by rw [hnat]; omega, by rw [hnat]; omega⟩)
    exact heff1.1.trans (hcont s1 heff1.1.code heff1.1.memaddrs heff1.2)

private theorem bswap64_body_no_evmErr_g09 {F : Type} (s : PanSemStateFiniteExact 64 F) :
    ¬ IsEvmErr (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_bswap64)).1 := by
  have hb : sourceFnBody Guest.Software.guestFn_bswap64 =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_bswap64).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_bswap64,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  have hasgn_ne : ∀ (st : PanSemStateFiniteExact 64 F) (nm : MlS) (ex : ExpHOL 64),
      ¬ IsEvmErr (evaluateHOLFiniteState st (.assign .local nm ex)).1 := by
    intro st nm ex
    rw [evaluateHOLFiniteState_assign]
    split
    · rintro ⟨_, h⟩; cases h
    · split <;> (rintro ⟨_, h⟩; cases h)
  have hret_ne : ∀ (st : PanSemStateFiniteExact 64 F) (ex : ExpHOL 64),
      ¬ IsEvmErr (evaluateHOLFiniteState st (.return ex)).1 := by
    intro st ex
    rw [evaluateHOLFiniteState_return]
    split
    · rintro ⟨_, h⟩; cases h
    · split <;> (rintro ⟨_, h⟩; cases h)
  have hseq_ne : ∀ (st : PanSemStateFiniteExact 64 F) (a b : ProgHOL 64),
      ¬ IsEvmErr (evaluateHOLFiniteState st a).1 →
      (∀ (m : PanSemStateFiniteExact 64 F), ¬ IsEvmErr (evaluateHOLFiniteState m b).1) →
      ¬ IsEvmErr (evaluateHOLFiniteState st (.seq a b)).1 := by
    intro st a b ha hb'
    rw [evaluateHOLFiniteState_seq_line780]
    rcases h1 : evaluateHOLFiniteState st a with ⟨r1, s1⟩
    rw [h1] at ha
    cases r1 with
    | none => exact hb' s1
    | some _ => exact ha
  exact hseq_ne s _ _ (hasgn_ne s _ _) fun s1 => hseq_ne s1 _ _ (hasgn_ne s1 _ _) fun s2 => hret_ne s2 _

private theorem bswap64_body_no_ffi_exc_g09 {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (∀ ff, (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_bswap64)).1 ≠ some (.finalFfi ff)) ∧
    (∀ eid ev, (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_bswap64)).1 ≠ some (.exception eid ev)) := by
  have hbp : sourceFnBody Guest.Software.guestFn_bswap64 =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_bswap64).body := rfl
  rw [hbp]; dsimp only [extractFn, Guest.Software.guestFn_bswap64,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  refine ⟨fun ff => ?_, fun eid ev => ?_⟩
  · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
    split
    · simp
    · split
      · dsimp only; rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
        split
        · simp
        · split
          · dsimp only; rw [evaluateHOLFiniteState_return]
            split <;> [simp; (split <;> simp)]
          · simp
      · simp
  · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
    split
    · simp
    · split
      · dsimp only; rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
        split
        · simp
        · split
          · dsimp only; rw [evaluateHOLFiniteState_return]
            split <;> [simp; (split <;> simp)]
          · simp
      · simp

private theorem u256_to_be32_aligned_no_ffi_exc_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (out : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (hout_lu : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (hal8 : out.toNat % 8 = 0) :
    (∀ ff, (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_to_be32)).1 ≠ some (.finalFfi ff)) ∧
    (∀ eid ev, (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_to_be32)).1 ≠ some (.exception eid ev)) := by
  have hb : sourceFnBody Guest.Software.guestFn_u256_to_be32 =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_u256_to_be32).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_u256_to_be32,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    List.map, Option.map]
  have hal : (out &&& 7#64) = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    have h7 : (7#64 : BitVec 64).toNat = 7 := rfl
    have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
    rw [BitVec.toNat_and, h7, h0]
    have hmod : out.toNat &&& 7 = out.toNat % 8 := Nat.and_two_pow_sub_one_eq_mod out.toNat 3
    omega
  have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.op .and [.var .local (ofString "out"), .const 7#64]) (.const 0#64)) =
      some (.val (.word 1)) := by
    simp only [evalHOLExact, evalListHOLExact, hout_lu, wordOpHOL, wordOp, valueIsWord, valueWord,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      Compiler.Encoders.Asm.wordCmpHOL]
    have h7 : (7#64 : BitVec 64) &&& 18446744073709551615#64 = 7#64 := by decide
    change some (ValueHOL.val (HolWordLab.word (if decide ((out &&& (7#64 &&& 18446744073709551615#64)) = 0#64) = true then 1 else 0))) = _
    rw [h7, hal]; simp
  have hst : ∀ (m : PanSemStateFiniteExact 64 F) (d v : ExpHOL 64) (c : ProgHOL 64),
      (∀ (m' : PanSemStateFiniteExact 64 F), m'.code = m.code →
        (∀ ff, (evaluateHOLFiniteState m' c).1 ≠ some (.finalFfi ff)) ∧
        (∀ eid ev, (evaluateHOLFiniteState m' c).1 ≠ some (.exception eid ev)) ∧
        (evaluateHOLFiniteState m' c).1 ≠ none) →
      (∀ ff, (evaluateHOLFiniteState m (.seq (.store d v) c)).1 ≠ some (.finalFfi ff)) ∧
      (∀ eid ev, (evaluateHOLFiniteState m (.seq (.store d v) c)).1 ≠ some (.exception eid ev)) ∧
      (evaluateHOLFiniteState m (.seq (.store d v) c)).1 ≠ none := by
    intro m d v c hc
    rw [evaluateHOLFiniteState_seq_line780]
    rcases h1 : evaluateHOLFiniteState m (.store d v) with ⟨r1, m1⟩
    cases r1 with
    | none =>
      have hm1c := (PanRunBounded.evaluateHOLFiniteState_metadata m (.store d v)).1
      rw [h1] at hm1c; exact hc m1 hm1c
    | some res1 =>
      have herr := store_some_eq_error_g09 h1; subst herr; simp
  have hdc : ∀ (m : PanSemStateFiniteExact 64 F) (ae : ExpHOL 64) (c : ProgHOL 64),
      m.code = originalRuntimeCode →
      (∀ (m' : PanSemStateFiniteExact 64 F), m'.code = originalRuntimeCode →
        (∀ ff, (evaluateHOLFiniteState m' c).1 ≠ some (.finalFfi ff)) ∧
        (∀ eid ev, (evaluateHOLFiniteState m' c).1 ≠ some (.exception eid ev)) ∧
        (evaluateHOLFiniteState m' c).1 ≠ none) →
      (∀ ff, (evaluateHOLFiniteState m (.decCall (ofString "w") .one (ofString "bswap64") [ae] c)).1 ≠ some (.finalFfi ff)) ∧
      (∀ eid ev, (evaluateHOLFiniteState m (.decCall (ofString "w") .one (ofString "bswap64") [ae] c)).1 ≠ some (.exception eid ev)) ∧
      (evaluateHOLFiniteState m (.decCall (ofString "w") .one (ofString "bswap64") [ae] c)).1 ≠ none := by
    intro m ae c hmc hc
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    rcases evalListHOLFinite m (h := fun a => Classical.propDecidable (m.memaddrs a)) [ae] with _ | vals
    · simp
    · dsimp only
      rcases hl : lookupCodeHOLFinite m.code.lookup (ofString "bswap64") vals with _ | ⟨b', cal', rs'⟩
      · simp
      · dsimp only
        have hinst := lookupCodeHOLFinite_installed_body m.code.lookup (ofString "bswap64")
          _ _ b' _ rs' vals cal' (by rw [hmc]; exact lookup_bswap64_b) hl
        subst hinst
        split
        · simp
        · have hnf := bswap64_body_no_ffi_exc_g09 (callEntryStateHOLFinite m cal')
          have hmc' := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite m cal')
            (sourceFnBody Guest.Software.guestFn_bswap64)).1
          rcases hb0 : evaluateHOLFiniteState (callEntryStateHOLFinite m cal')
              (sourceFnBody Guest.Software.guestFn_bswap64) with ⟨rb0, sb0⟩
          rw [hb0] at hnf hmc'; dsimp only at hnf hmc' ⊢
          cases rb0 with
          | none => simp
          | some r0 =>
            cases r0 with
            | returned _ => dsimp only; split <;> [ exact hc _ (hmc'.trans hmc); simp ]
            | finalFfi ff => exact absurd rfl (hnf.1 ff)
            | exception eid ev => exact absurd rfl (hnf.2 eid ev)
            | _ => simp
  have hsc : ∀ (m : PanSemStateFiniteExact 64 F) (ae : ExpHOL 64) (c : ProgHOL 64),
      m.code = originalRuntimeCode →
      (∀ (m' : PanSemStateFiniteExact 64 F), m'.code = originalRuntimeCode →
        (∀ ff, (evaluateHOLFiniteState m' c).1 ≠ some (.finalFfi ff)) ∧
        (∀ eid ev, (evaluateHOLFiniteState m' c).1 ≠ some (.exception eid ev)) ∧
        (evaluateHOLFiniteState m' c).1 ≠ none) →
      (∀ ff, (evaluateHOLFiniteState m (.seq (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [ae]) c)).1 ≠ some (.finalFfi ff)) ∧
      (∀ eid ev, (evaluateHOLFiniteState m (.seq (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [ae]) c)).1 ≠ some (.exception eid ev)) ∧
      (evaluateHOLFiniteState m (.seq (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [ae]) c)).1 ≠ none := by
    intro m ae c hmc hc
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hcall0 : evaluateHOLFiniteState m
        (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [ae]) with ⟨rc0, sc0⟩
    rw [evaluateHOLFiniteState_call] at hcall0
    rcases ha0 : evalListHOLFinite m (h := fun a => Classical.propDecidable (m.memaddrs a)) [ae] with _ | vals
    · rw [ha0] at hcall0; injection hcall0 with hr _; subst hr; simp
    · rw [ha0] at hcall0; dsimp only at hcall0
      rcases hl : lookupCodeHOLFinite m.code.lookup (ofString "bswap64") vals with _ | ⟨b', cal', rs'⟩
      · rw [hl] at hcall0; injection hcall0 with hr _; subst hr; simp
      · rw [hl] at hcall0; dsimp only at hcall0
        have hinst := lookupCodeHOLFinite_installed_body m.code.lookup (ofString "bswap64")
          _ _ b' _ rs' vals cal' (by rw [hmc]; exact lookup_bswap64_b) hl
        subst hinst
        split at hcall0
        · injection hcall0 with hr _; subst hr; simp
        · have hnf := bswap64_body_no_ffi_exc_g09 (callEntryStateHOLFinite m cal')
          have hmc' := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite m cal')
            (sourceFnBody Guest.Software.guestFn_bswap64)).1
          rcases hb0 : evaluateHOLFiniteState (callEntryStateHOLFinite m cal')
              (sourceFnBody Guest.Software.guestFn_bswap64) with ⟨rb0, sb0⟩
          rw [hb0] at hcall0 hnf hmc'; dsimp only at hnf hmc'
          cases rb0 with
          | none => injection hcall0 with hr _; subst hr; simp
          | some r0 =>
            cases r0 with
            | returned _ =>
              dsimp only at hcall0; split at hcall0
              · split at hcall0
                · injection hcall0 with hr hsc'; subst hr hsc'; exact hc _ (hmc'.trans hmc)
                · injection hcall0 with hr _; subst hr; simp
              · injection hcall0 with hr _; subst hr; simp
            | finalFfi ff => exact absurd rfl (hnf.1 ff)
            | exception eid ev => exact absurd rfl (hnf.2 eid ev)
            | _ => injection hcall0 with hr _; subst hr; simp
  have hret : ∀ (m : PanSemStateFiniteExact 64 F),
      (∀ ff, (evaluateHOLFiniteState m (.return (.const 0#64))).1 ≠ some (.finalFfi ff)) ∧
      (∀ eid ev, (evaluateHOLFiniteState m (.return (.const 0#64))).1 ≠ some (.exception eid ev)) ∧
      (evaluateHOLFiniteState m (.return (.const 0#64))).1 ≠ none := by
    intro m; rw [evaluateHOLFiniteState_return]
    have he : @evalHOLExact 64 F _ m.toExact (fun a => Classical.propDecidable (m.memaddrs a))
        (.const 0#64) = some (.val (.word 0)) := rfl
    rw [he]
    have hsz : sizeOfShapeWithContextHOL m.structs (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
    dsimp only; rw [if_pos hsz]; simp
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
  have hcomb :
      (∀ ff, (evaluateHOLFiniteState s yesProg256).1 ≠ some (.finalFfi ff)) ∧
      (∀ eid ev, (evaluateHOLFiniteState s yesProg256).1 ≠ some (.exception eid ev)) ∧
      (evaluateHOLFiniteState s yesProg256).1 ≠ none :=
    hdc s _ _ hcode fun m0 hm0 =>
      hst m0 _ _ _ fun a1 ha1 =>
        hsc a1 _ _ (ha1.trans hm0) fun m1 hm1 =>
          hst m1 _ _ _ fun a2 ha2 =>
            hsc a2 _ _ (ha2.trans hm1) fun m2 hm2 =>
              hst m2 _ _ _ fun a3 ha3 =>
                hsc a3 _ _ (ha3.trans hm2) fun m3 _ =>
                  hst m3 _ _ _ fun a4 _ => hret a4
  have hgoal_yes256 : evaluateHOLFiniteState s
      (.seq (.ite (.cmp .equal (.op .and [.var .local (ofString "out"), .const 7#64]) (.const 0#64)) yesProg256 .skip)
        (.seq (.call (some (none, none)) (ofString "st_be64") [.var .local (ofString "out"), .rfield 3 (.var .local (ofString "a"))])
          (.seq (.call (some (none, none)) (ofString "st_be64") [.op .add [.var .local (ofString "out"), .const 8#64], .rfield 2 (.var .local (ofString "a"))])
            (.seq (.call (some (none, none)) (ofString "st_be64") [.op .add [.var .local (ofString "out"), .const 16#64], .rfield 1 (.var .local (ofString "a"))])
              (.seq (.call (some (none, none)) (ofString "st_be64") [.op .add [.var .local (ofString "out"), .const 24#64], .rfield 0 (.var .local (ofString "a"))])
                (.return (.const 0#64))))))) = evaluateHOLFiniteState s yesProg256 := by
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hcond]
    dsimp only
    have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    rw [if_neg h10]
    rcases hy : evaluateHOLFiniteState s yesProg256 with ⟨ry, sy⟩
    have hnn := hcomb.2.2
    rw [hy] at hnn
    cases ry with
    | none => exact absurd rfl hnn
    | some _ => rfl
  rw [hgoal_yes256]
  exact ⟨hcomb.1, hcomb.2.1⟩

private theorem u256_to_be32_aligned_body_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (out : BitVec 64)
    (hcode : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain)
    (hout_lu : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (hal8 : out.toNat % 8 = 0)
    (hout_end : out.toNat + 32 ≤ heapEnd) :
    ByteRegionEffect s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_to_be32)).2
      [(out.toNat, 32)] ∧
    ¬ IsEvmErr (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_to_be32)).1 := by
  have hb : sourceFnBody Guest.Software.guestFn_u256_to_be32 =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_u256_to_be32).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_u256_to_be32,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    List.map, Option.map]
  have hal : (out &&& 7#64) = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    have h7 : (7#64 : BitVec 64).toNat = 7 := rfl
    have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
    rw [BitVec.toNat_and, h7, h0]
    have hmod : out.toNat &&& 7 = out.toNat % 8 := Nat.and_two_pow_sub_one_eq_mod out.toNat 3
    omega
  have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.op .and [.var .local (ofString "out"), .const 7#64]) (.const 0#64)) =
      some (.val (.word 1)) := by
    simp only [evalHOLExact, evalListHOLExact, hout_lu, wordOpHOL, wordOp, valueIsWord, valueWord,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      Compiler.Encoders.Asm.wordCmpHOL]
    have h7 : (7#64 : BitVec 64) &&& 18446744073709551615#64 = 7#64 := by decide
    change some (ValueHOL.val (HolWordLab.word (if decide ((out &&& (7#64 &&& 18446744073709551615#64)) = 0#64) = true then 1 else 0))) = _
    rw [h7, hal]; simp
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
  have hdc_ne_none : ∀ (st : PanSemStateFiniteExact 64 F) (nm : MlS) (sh : ShapeHOL)
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
    intro m
    rw [evaluateHOLFiniteState_return]
    have he : @evalHOLExact 64 F _ m.toExact (fun a => Classical.propDecidable (m.memaddrs a))
        (.const 0#64) = some (.val (.word 0)) := rfl
    rw [he]
    have hsz : sizeOfShapeWithContextHOL m.structs (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
    dsimp only; rw [if_pos hsz]; simp
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
    dsimp only
    have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    rw [if_neg h10]
    rcases hy : evaluateHOLFiniteState s yesProg256 with ⟨ry, sy⟩
    rw [hy] at hyes256_nn
    cases ry with
    | none => exact absurd rfl hyes256_nn
    | some _ => rfl
  rw [hgoal_yes256]
  have hev_zero : ∀ (m : PanSemStateFiniteExact 64 F),
      m.locals.lookup (ofString "out") = some (.val (.word out)) →
      @evalHOLExact 64 F _ m.toExact (fun a => Classical.propDecidable (m.memaddrs a))
        (.var .local (ofString "out")) = some (.val (.word (out + BitVec.ofNat 64 0))) := by
    intro m hm; rw [BitVec.add_zero]; exact hm
  have hev_off : ∀ (m : PanSemStateFiniteExact 64 F) (off : Nat),
      m.locals.lookup (ofString "out") = some (.val (.word out)) →
      @evalHOLExact 64 F _ m.toExact (fun a => Classical.propDecidable (m.memaddrs a))
        (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 off)]) =
        some (.val (.word (out + BitVec.ofNat 64 off))) := by
    intro m off hm
    simp only [evalHOLExact, evalListHOLExact, hm, wordOpHOL, wordOp, valueIsWord, valueWord,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
    exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word (out + w)))) (BitVec.add_zero _)
  have hret_eff : ∀ (m : PanSemStateFiniteExact 64 F),
      ByteRegionEffect m (evaluateHOLFiniteState m (.return (.const 0#64))).2 [(out.toNat, 32)] := by
    intro m
    have hret : (evaluateHOLFiniteState m (.return (.const 0#64))).2 =
        { m with locals := (evaluateHOLFiniteState m (.return (.const 0#64))).2.locals } := by
      rw [evaluateHOLFiniteState_return]; split <;> [rfl; (split <;> rfl)]
    conv => arg 2; rw [hret]
    exact (ByteRegionEffect.refl m _).with_locals_clock _ m.clock
  refine ⟨?_, ?_⟩
  · exact decCall_bswap64_eff_g09 (s := s) (Rl := [(out.toNat, 32)]) hcode
      fun mid0 hc_m0 hm_m0 hout_m0 _ ⟨wv0, hw_m0⟩ => by
        have ho0 : mid0.locals.lookup (ofString "out") = some (.val (.word out)) := by rw [hout_m0]; exact hout_lu
        refine seq_store_word_eff_g09 (s := mid0) (base := out) (w := wv0) (off := 0) (len := 32)
          (hm_m0.trans hma) hout_end (by omega) (hev_zero mid0 ho0) hw_m0 fun s1 hc_s1 hm_s1 hl_s1 => ?_
        refine seq_call_bswap64_eff_g09 (s := s1) (Rl := [(out.toNat, 32)])
          (hc_s1.trans hc_m0) fun mid1 hc_m1 hm_m1 hout_m1 _ ⟨wv1, hw_m1⟩ => ?_
        have ho1 : mid1.locals.lookup (ofString "out") = some (.val (.word out)) := by rw [hout_m1, hl_s1]; exact ho0
        refine seq_store_word_eff_g09 (s := mid1) (base := out) (w := wv1) (off := 8) (len := 32)
          (hm_m1.trans (hm_s1.trans (hm_m0.trans hma))) hout_end (by omega) (hev_off mid1 8 ho1) hw_m1
          fun s2 hc_s2 hm_s2 hl_s2 => ?_
        refine seq_call_bswap64_eff_g09 (s := s2) (Rl := [(out.toNat, 32)])
          (hc_s2.trans hc_m1) fun mid2 hc_m2 hm_m2 hout_m2 _ ⟨wv2, hw_m2⟩ => ?_
        have ho2 : mid2.locals.lookup (ofString "out") = some (.val (.word out)) := by rw [hout_m2, hl_s2]; exact ho1
        refine seq_store_word_eff_g09 (s := mid2) (base := out) (w := wv2) (off := 16) (len := 32)
          (hm_m2.trans (hm_s2.trans (hm_m1.trans (hm_s1.trans (hm_m0.trans hma))))) hout_end (by omega)
          (hev_off mid2 16 ho2) hw_m2 fun s3 hc_s3 hm_s3 hl_s3 => ?_
        refine seq_call_bswap64_eff_g09 (s := s3) (Rl := [(out.toNat, 32)])
          (hc_s3.trans hc_m2) fun mid3 _ hm_m3 hout_m3 _ ⟨wv3, hw_m3⟩ => ?_
        have ho3 : mid3.locals.lookup (ofString "out") = some (.val (.word out)) := by rw [hout_m3, hl_s3]; exact ho2
        refine seq_store_word_eff_g09 (s := mid3) (base := out) (w := wv3) (off := 24) (len := 32)
          (hm_m3.trans (hm_s3.trans (hm_m2.trans (hm_s2.trans (hm_m1.trans (hm_s1.trans (hm_m0.trans hma)))))))
          hout_end (by omega) (hev_off mid3 24 ho3) hw_m3 fun s4 _ _ _ => hret_eff s4
  · have hst_ne : ∀ (m : PanSemStateFiniteExact 64 F) (d v : ExpHOL 64) (c : ProgHOL 64),
        (∀ (m' : PanSemStateFiniteExact 64 F), m'.code = m.code → ¬ IsEvmErr (evaluateHOLFiniteState m' c).1) →
        ¬ IsEvmErr (evaluateHOLFiniteState m (.seq (.store d v) c)).1 := by
      intro m d v c hc
      rw [evaluateHOLFiniteState_seq_line780]
      rcases h1 : evaluateHOLFiniteState m (.store d v) with ⟨r1, m1⟩
      cases r1 with
      | none =>
        have hm1c := (PanRunBounded.evaluateHOLFiniteState_metadata m (.store d v)).1
        rw [h1] at hm1c; exact hc m1 hm1c
      | some res1 =>
        have herr := store_some_eq_error_g09 h1; subst herr
        rintro ⟨_, h⟩; cases h
    have hdc_ne : ∀ (m : PanSemStateFiniteExact 64 F) (ae : ExpHOL 64) (c : ProgHOL 64),
        m.code = originalRuntimeCode →
        (∀ (m' : PanSemStateFiniteExact 64 F), m'.code = originalRuntimeCode → ¬ IsEvmErr (evaluateHOLFiniteState m' c).1) →
        ¬ IsEvmErr (evaluateHOLFiniteState m (.decCall (ofString "w") .one (ofString "bswap64") [ae] c)).1 := by
      intro m ae c hmc hc
      rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
      rcases evalListHOLFinite m (h := fun a => Classical.propDecidable (m.memaddrs a)) [ae] with _ | vals
      · rintro ⟨_, h⟩; cases h
      · dsimp only
        rcases hl : lookupCodeHOLFinite m.code.lookup (ofString "bswap64") vals with _ | ⟨b', cal', rs'⟩
        · rintro ⟨_, h⟩; cases h
        · dsimp only
          have hinst := lookupCodeHOLFinite_installed_body m.code.lookup (ofString "bswap64")
            _ _ b' _ rs' vals cal' (by rw [hmc]; exact lookup_bswap64_b) hl
          subst hinst
          split
          · rintro ⟨_, h⟩; cases h
          · have hnb := bswap64_body_no_evmErr_g09 (callEntryStateHOLFinite m cal')
            have hm_b := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite m cal')
              (sourceFnBody Guest.Software.guestFn_bswap64)).1
            rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite m cal')
                (sourceFnBody Guest.Software.guestFn_bswap64) with ⟨rb, sb⟩
            rw [hb] at hnb hm_b; dsimp only at hm_b ⊢
            cases rb with
            | none => rintro ⟨_, h⟩; cases h
            | some r =>
              cases r with
              | returned v =>
                dsimp only; split
                · exact hc _ (hm_b.trans hmc)
                · rintro ⟨_, h⟩; cases h
              | exception eid ev =>
                rintro ⟨v0, h⟩; injection h with h'; injection h' with he hw
                exact hnb ⟨v0, by rw [he, hw]⟩
              | timeOut | error | «break» | «continue» | finalFfi _ => rintro ⟨_, h⟩; cases h
    have hsc_ne : ∀ (m : PanSemStateFiniteExact 64 F) (ae : ExpHOL 64) (c : ProgHOL 64),
        m.code = originalRuntimeCode →
        (∀ (m' : PanSemStateFiniteExact 64 F), m'.code = originalRuntimeCode → ¬ IsEvmErr (evaluateHOLFiniteState m' c).1) →
        ¬ IsEvmErr (evaluateHOLFiniteState m
          (.seq (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [ae]) c)).1 := by
      intro m ae c hmc hc
      rw [evaluateHOLFiniteState_seq_line780]
      rcases hcall : evaluateHOLFiniteState m
          (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [ae]) with ⟨rc, sc⟩
      rw [evaluateHOLFiniteState_call] at hcall
      rcases hargs : evalListHOLFinite m (h := fun a => Classical.propDecidable (m.memaddrs a)) [ae] with _ | vals
      · rw [hargs] at hcall; injection hcall with hr _; subst hr; rintro ⟨_, h⟩; cases h
      · rw [hargs] at hcall; dsimp only at hcall
        rcases hl : lookupCodeHOLFinite m.code.lookup (ofString "bswap64") vals with _ | ⟨b', cal', rs'⟩
        · rw [hl] at hcall; injection hcall with hr _; subst hr; rintro ⟨_, h⟩; cases h
        · rw [hl] at hcall; dsimp only at hcall
          have hinst := lookupCodeHOLFinite_installed_body m.code.lookup (ofString "bswap64")
            _ _ b' _ rs' vals cal' (by rw [hmc]; exact lookup_bswap64_b) hl
          subst hinst
          split at hcall
          · injection hcall with hr _; subst hr; rintro ⟨_, h⟩; cases h
          · have hnb := bswap64_body_no_evmErr_g09 (callEntryStateHOLFinite m cal')
            have hm_b := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite m cal')
              (sourceFnBody Guest.Software.guestFn_bswap64)).1
            rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite m cal')
                (sourceFnBody Guest.Software.guestFn_bswap64) with ⟨rb, sb⟩
            rw [hb] at hcall hnb hm_b; dsimp only at hm_b
            cases rb with
            | none => injection hcall with hr _; subst hr; rintro ⟨_, h⟩; cases h
            | some r =>
              cases r with
              | returned v =>
                dsimp only at hcall; split at hcall
                · split at hcall
                  · injection hcall with hr hsc; subst hr hsc; exact hc _ (hm_b.trans hmc)
                  · injection hcall with hr _; subst hr; rintro ⟨_, h⟩; cases h
                · injection hcall with hr _; subst hr; rintro ⟨_, h⟩; cases h
              | exception eid ev =>
                injection hcall with hr _; subst hr
                rintro ⟨v0, h⟩; injection h with h'; injection h' with he hw
                exact hnb ⟨v0, by rw [he, hw]⟩
              | timeOut | error | «break» | «continue» | finalFfi _ =>
                injection hcall with hr _; subst hr; rintro ⟨_, h⟩; cases h
    have hret0_ne : ∀ (m : PanSemStateFiniteExact 64 F),
        ¬ IsEvmErr (evaluateHOLFiniteState m (.return (.const 0#64))).1 := by
      intro m; rw [evaluateHOLFiniteState_return]; split <;> [ (rintro ⟨_, h⟩; cases h); (split <;> (rintro ⟨_, h⟩; cases h)) ]
    exact hdc_ne s _ _ hcode fun m0 hm0 =>
      hst_ne m0 _ _ _ fun s1 hs1 =>
        hsc_ne s1 _ _ (hs1.trans hm0) fun m1 hm1 =>
          hst_ne m1 _ _ _ fun s2 hs2 =>
            hsc_ne s2 _ _ (hs2.trans hm1) fun m2 hm2 =>
              hst_ne m2 _ _ _ fun s3 hs3 =>
                hsc_ne s3 _ _ (hs3.trans hm2) fun m3 _ =>
                  hst_ne m3 _ _ _ fun s4 _ => hret0_ne s4

private theorem holAsmSignedLess_eq_slt_g09 (left right : BitVec 64) :
    Compiler.Encoders.Asm.holAsmSignedLess left right = left.slt right := by
  have bl := left.isLt
  have br := right.isLt
  simp only [Compiler.Encoders.Asm.holAsmSignedLess, BitVec.slt_eq_decide, BitVec.toInt_eq_msb_cond,
    BitVec.msb_eq_decide]
  repeat (any_goals first | split)
  all_goals simp_all only [decide_eq_true_eq]
  all_goals apply Bool.eq_iff_iff.mpr
  all_goals simp_all [decide_eq_true_eq]
  all_goals omega

private def opLogWhileBody : ProgHOL 64 :=
  InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
    (Prog.decCall "t" (Shape.comb [Shape.one, Shape.one, Shape.one, Shape.one]) "stack_pop" []
      (Prog.seq
        (Prog.call (some (none, none)) "u256_to_be32"
          [(Exp.var VarKind.local "t"),
           (Exp.op BinOp.add [(Exp.var VarKind.local "topics"),
             (Exp.panOp PanOp.mul [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 32))])])])
        (Prog.assign VarKind.local "i"
          (Exp.op BinOp.add [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 1))]))))

private def opLogWhileProg : ProgHOL 64 :=
  .while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "ntopics")))
    opLogWhileBody

private theorem worldTypedIvls_congr_mg_g09 {F : Type}
    {s t : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hm : t.memory = s.memory) (hg : t.globals = s.globals) :
    worldTypedIvls t S Nd = worldTypedIvls s S Nd := by
  have hmw : ∀ a, memW t a = memW s a := fun a => congrFun (memW_congr hm) a
  have hgn : ∀ nm, globN t nm = globN s nm := fun nm => congrFun (globN_congr hg) nm
  have hfp : S.flatMap (htabFootprint t) = S.flatMap (htabFootprint s) :=
    List.flatMap_congr fun tab _ => by simp only [htabFootprint, hdr, hmw]
  have htr : typedRecords.map (fun r => (globN t r.1, if globN t r.1 = 0 then 0 else r.2)) =
      typedRecords.map (fun r => (globN s r.1, if globN s r.1 = 0 then 0 else r.2)) :=
    List.map_congr_left fun r _ => by simp only [hgn]
  have hjrn : (if globN t "journal_cap" = 0 then 0 else globN t "journal", 32 * globN t "journal_cap") =
      (if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap") := by
    simp only [hgn]
  have hbo : blockOutObjects t = blockOutObjects s := by
    simp only [blockOutObjects, hgn, hmw]
  have hlst : ∀ l esz, lstObjects t l esz = lstObjects s l esz := fun l esz => by
    simp only [lstObjects, hmw]
  have hhval : ∀ tab, htabValues t tab = htabValues s tab := fun tab => by
    simp only [htabValues, hdr, nodeF, hmw]
  have hbal : balObjects t = balObjects s := by
    have hbr : balRecords t = balRecords s := by
      simp only [balRecords, hdr, nodeF, hgn, hmw]
    unfold balObjects
    rw [hbr]
    exact List.flatMap_congr fun ad _ => by simp only [hmw, hlst, hhval]
  have hne : nodeExtents t Nd = nodeExtents s Nd := by
    unfold nodeExtents
    exact List.flatMap_congr fun n _ => by simp only [nodeIvl, nodePath, hmw]
  unfold worldTypedIvls
  rw [hfp, htr, hjrn, hbo, hbal, hne]

private theorem map_frameObjects_congr_mg_g09 {F : Type}
    {s t : PanSemStateFiniteExact 64 F}
    (hm : t.memory = s.memory) (hg : t.globals = s.globals) :
    (evmChain t).map (frameObjects t) = (evmChain s).map (frameObjects s) := by
  have hmw : ∀ a, memW t a = memW s a := fun a => congrFun (memW_congr hm) a
  have hgn : ∀ nm, globN t nm = globN s nm := fun nm => congrFun (globN_congr hg) nm
  rw [evmChain_congr hm hg]
  refine List.map_congr_left fun ec _ => ?_
  have hfl : frameLogs t ec = frameLogs s ec := by simp only [frameLogs, hmw]
  have hfr : frameRet t ec = frameRet s ec := by simp only [frameRet, hmw]
  have hflo : frameLogObjects t ec = frameLogObjects s ec := by
    unfold frameLogObjects
    simp only [hmw]
    exact List.flatMap_congr fun i _ => by simp only [logOwnedIvls, logRecordIvls, hmw, hgn]
  unfold frameObjects
  rw [hmw (ec.1 + 8), hmw (ec.1 + 232), hmw (ec.1 + 24), hmw (ec.1 + 40), hmw (ec.1 + 88),
      hfl, hfr, hflo]

private theorem op_log_while_body_step_g09 {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {nt topics qw iv : BitVec 64}
    (hiv_lt : iv.toNat < nt.toNat)
    (hnt4 : nt.toNat ≤ 4)
    (hcode : s.code = originalRuntimeCode)
    (hInvW : EvmInvWith s S Nd)
    (htop_le : topics.toNat + (32 * nt.toNat + 8) ≤ qw.toNat)
    (hq_lim : qw.toNat ≤ heapLimit)
    (htop_mod8 : topics.toNat % 8 = 0)
    (hdj : IvlsDisj [(topics.toNat, qw.toNat - topics.toNat)]
      (worldTypedIvls s S Nd ++ ((evmChain s).map (frameObjects s)).flatten))
    (hi_lu : s.locals.lookup (ofString "i") = some (.val (.word iv)))
    (htop_lu : s.locals.lookup (ofString "topics") = some (.val (.word topics))) :
    let s_dc := decClockHOLFinite s
    let out := evaluateHOLFiniteState s_dc opLogWhileBody
    (out.1 = none →
      out.2.code = originalRuntimeCode ∧
      EvmInvWith out.2 S Nd ∧
      worldTypedIvls out.2 S Nd = worldTypedIvls s S Nd ∧
      (evmChain out.2).map (frameObjects out.2) = (evmChain s).map (frameObjects s) ∧
      evmChain out.2 = evmChain s ∧
      evmR out.2 = evmR s ∧
      globN out.2 "heap_ptr" = globN s "heap_ptr" ∧
      (HeadMemAligned s → HeadMemAligned out.2) ∧
      out.2.locals.lookup (ofString "i") = some (.val (.word (iv + 1))) ∧
      (∀ nm : MlS, nm ≠ ofString "i" → nm ≠ ofString "t" → out.2.locals.lookup nm = s.locals.lookup nm)) ∧
    (∀ ev, out.1 = some (.exception (ofString "EvmErr") ev) →
      EvmInvWith out.2 S Nd ∧
      evmChain out.2 = evmChain s ∧
      evmR out.2 = evmR s) ∧
    out.1 ≠ some .«break» ∧
    out.1 ≠ some .«continue» ∧
    (∀ v, out.1 ≠ some (.returned v)) := by
  dsimp only
  let s_dc := decClockHOLFinite s
  have hs_dc_InvW : EvmInvWith s_dc S Nd := evmInvWith_localsFree s.locals (s.clock - 1) hInvW
  have hs_dc_code : s_dc.code = originalRuntimeCode := hcode
  rcases hbody : evaluateHOLFiniteState s_dc opLogWhileBody with ⟨rb, sb⟩
  change evaluateHOLFiniteState s_dc opLogWhileBody = (rb, sb) at hbody
  dsimp only
  have hnot_to_err : ∀ {r : Option (PanSemResultExact 64)} {st : PanSemStateFiniteExact 64 F},
      (r = some .timeOut ∨ r = some .error) →
      (r = none →
        st.code = originalRuntimeCode ∧
        EvmInvWith st S Nd ∧
        worldTypedIvls st S Nd = worldTypedIvls s S Nd ∧
        (evmChain st).map (frameObjects st) = (evmChain s).map (frameObjects s) ∧
        evmChain st = evmChain s ∧
        evmR st = evmR s ∧
        globN st "heap_ptr" = globN s "heap_ptr" ∧
        (HeadMemAligned s → HeadMemAligned st) ∧
        st.locals.lookup (ofString "i") = some (.val (.word (iv + 1))) ∧
        (∀ nm : MlS, nm ≠ ofString "i" → nm ≠ ofString "t" → st.locals.lookup nm = s.locals.lookup nm)) ∧
      (∀ ev, r = some (.exception (ofString "EvmErr") ev) →
        EvmInvWith st S Nd ∧
        evmChain st = evmChain s ∧
        evmR st = evmR s) ∧
      r ≠ some .«break» ∧
      r ≠ some .«continue» ∧
      (∀ v, r ≠ some (.returned v)) := by
    intro r st hor
    rcases hor with rfl | rfl
    · exact And.intro (fun h => by cases h) (And.intro (fun _ h => by cases h)
        (And.intro (by simp) (And.intro (by simp) (fun _ h => by cases h))))
    · exact And.intro (fun h => by cases h) (And.intro (fun _ h => by cases h)
        (And.intro (by simp) (And.intro (by simp) (fun _ h => by cases h))))
  have hbody' := hbody
  unfold opLogWhileBody at hbody'
  dsimp only [InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    List.map, Option.map] at hbody'
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hbody'
  have hargs_sp : evalListHOLFinite s_dc (h := fun a => Classical.propDecidable (s_dc.memaddrs a)) [] = some [] := rfl
  have hlk_sp : lookupCodeHOLFinite s_dc.code.lookup (ofString "stack_pop") [] =
      some (sourceFnBody Guest.Software.guestFn_stack_pop, HolFiniteMapExact.empty,
        ShapeHOL.comb [.one, .one, .one, .one]) := by
    have raw : lookupCodeHOLExact s_dc.code.lookup (ofString "stack_pop") [] =
        some (sourceFnBody Guest.Software.guestFn_stack_pop, (fun _ => none),
          ShapeHOL.comb [.one, .one, .one, .one]) := by
      simp [lookupCodeHOLExact, hs_dc_code, lookup_stack_pop_pub]
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite
    split
    · rename_i missing; rw [raw] at missing; cases missing
    · rename_i foundBody foundLocals foundShape found
      have equal := Option.some.inj (found.symm.trans raw)
      obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
      apply congrArg (fun locals => some (sourceFnBody Guest.Software.guestFn_stack_pop, locals, ShapeHOL.comb [.one, .one, .one, .one]))
      apply HolFiniteMapExact.ext
      funext key
      rfl
  rw [hargs_sp] at hbody'; dsimp only at hbody'
  rw [hlk_sp] at hbody'; dsimp only at hbody'
  by_cases hclk_sp : s_dc.clock = 0
  · simp [hclk_sp] at hbody'
    exact hnot_to_err (Or.inl hbody'.1.symm)
  · simp only [hclk_sp, ↓reduceIte] at hbody'
    let ent_sp := callEntryStateHOLFinite s_dc HolFiniteMapExact.empty
    have hent_sp_InvW : EvmInvWith ent_sp S Nd :=
      evmInvWith_localsFree _ _ hs_dc_InvW
    have hm_sp := (PanRunBounded.evaluateHOLFiniteState_metadata ent_sp
      (sourceFnBody Guest.Software.guestFn_stack_pop)).1
    rcases hsp_run : evaluateHOLFiniteState ent_sp (sourceFnBody Guest.Software.guestFn_stack_pop) with ⟨rsp, ssp⟩
    change evaluateHOLFiniteState ent_sp (sourceFnBody Guest.Software.guestFn_stack_pop) = (rsp, ssp) at hsp_run
    simp only [ent_sp, hsp_run] at hbody' hm_sp
    cases rsp with
    | none =>
      injection hbody' with hrb _
      exact hnot_to_err (Or.inr hrb.symm)
    | some rsp0 =>
      cases rsp0 with
      | timeOut =>
        injection hbody' with hrb _
        exact hnot_to_err (Or.inl hrb.symm)
      | error | «break» | «continue» =>
        injection hbody' with hrb _
        exact hnot_to_err (Or.inr hrb.symm)
      | finalFfi f0 =>
        injection hbody' with hrb _
        subst hrb
        exact And.intro (fun h => by cases h) (And.intro (fun _ h => by cases h)
          (And.intro (by simp) (And.intro (by simp) (fun _ h => by cases h))))
      | exception eid0 ev0 =>
        by_cases heid0 : eid0 = ofString "EvmErr"
        · subst heid0
          have hsp_st := stack_pop_body_evmInvWith hent_sp_InvW
            (by rw [hsp_run]; exact Or.inr ⟨_, ev0, rfl, by decide⟩)
          rw [hsp_run] at hsp_st; dsimp only at hsp_st
          injection hbody' with hrb hsb; subst hrb hsb
          refine And.intro (fun h => by cases h) (And.intro (fun ev h => ?_)
            (And.intro (by simp) (And.intro (by simp) (fun _ h => by cases h))))
          injection h with h'; injection h' with _ hev; subst hev
          have hInv_el := evmInvWith_localsFree (s := ssp) HolFiniteMapExact.empty ssp.clock hsp_st.1
          have hc_el := evm_congr (s := ssp) (t := ssp.emptyLocalsHOLFinite) rfl rfl
          have hc_ent := evm_congr (s := s) (t := ent_sp) rfl rfl
          exact ⟨hInv_el, (evmChain_congr (s := ssp) (t := ssp.emptyLocalsHOLFinite) rfl rfl).trans
              (hsp_st.2.2.2.2.2.1.trans (evmChain_congr (s := s) (t := ent_sp) rfl rfl)),
            hc_el.2.1.trans (hsp_st.2.2.2.2.2.2.1.trans hc_ent.2.1)⟩
        · injection hbody' with hrb _
          subst hrb
          refine And.intro (fun h => by cases h) (And.intro (fun ev h => ?_)
            (And.intro (by simp) (And.intro (by simp) (fun _ h => by cases h))))
          injection h with h'; injection h' with h1 _; exact absurd h1 heid0
      | returned tv =>
        dsimp only at hbody'
        split at hbody'
        · rename_i hsh_tv
          have hsp_st := stack_pop_body_evmInvWith hent_sp_InvW
            (by rw [hsp_run]; exact Or.inl ⟨tv, rfl⟩)
          rw [hsp_run] at hsp_st; dsimp only at hsp_st
          obtain ⟨hssp_InvW, hssp_wti, hssp_fo, hssp_glob, hssp_ma, hssp_ch, hssp_R, hssp_HM, _⟩ := hsp_st
          let s1 : PanSemStateFiniteExact 64 F := setVarHOLFinite (ofString "t") tv { ssp with locals := s_dc.locals }
          have hs1_InvW : EvmInvWith s1 S Nd := evmInvWith_localsFree (s := ssp) s1.locals ssp.clock hssp_InvW
          have hs1_code : s1.code = originalRuntimeCode := hm_sp.trans hs_dc_code
          have hs1_ma : s1.memaddrs = ordinaryDomain := hs1_InvW.1.1.memaddrs
          have hs1_t : s1.locals.lookup (ofString "t") = some tv := by
            simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hs1_i : s1.locals.lookup (ofString "i") = some (.val (.word iv)) := by
            simp [s1, s_dc, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "t" ≠ ofString "i" by decide, hi_lu]
          have hs1_top : s1.locals.lookup (ofString "topics") = some (.val (.word topics)) := by
            simp [s1, s_dc, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "t" ≠ ofString "topics" by decide, htop_lu]
          let out_i : BitVec 64 := topics + BitVec.ofNat 64 (32 * iv.toNat)
          have hout_i_nat : out_i.toNat = topics.toNat + 32 * iv.toNat := by
            have hlim_v : heapLimit = 2952790016 := R11Shards.heapLimit_val
            have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by norm_num
            dsimp only [out_i]
            rw [BitVec.toNat_add, BitVec.toNat_ofNat, h264, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          have hout_i_mod8 : out_i.toNat % 8 = 0 := by omega
          have hout_i_end : out_i.toNat + 32 ≤ heapEnd := by
            have hlim_v := R11Shards.heapLimit_val
            have hend_v := R11Shards.heapEnd_val
            omega
          have hmul_eval : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
              (.panop .mul [.var .local (ofString "i"), .const 32#64]) =
              some (.val (.word (BitVec.ofNat 64 (32 * iv.toNat)))) := by
            have hmul_eq : iv * 32#64 = BitVec.ofNat 64 (32 * iv.toNat) := by
              apply BitVec.eq_of_toNat_eq
              have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by norm_num
              rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h264,
                  Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
                  Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
            simp [evalHOLExact, evalListHOLExact, hs1_i, valueIsWord, valueWord, panOpHOL, hmul_eq]
          have hout_eval : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
              (.op .add [.var .local (ofString "topics"),
                .panop .mul [.var .local (ofString "i"), .const 32#64]]) =
              some (.val (.word out_i)) := by
            have htop_ev : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
                (.var .local (ofString "topics")) = some (.val (.word topics)) := by
              simp [evalHOLExact, hs1_top]
            conv_lhs => unfold evalHOLExact
            rw [evalListHOLExact, evalListHOLExact, evalListHOLExact, htop_ev, hmul_eval]
            simp [valueIsWord, valueWord, wordOpHOL, wordOp, out_i]
          have hargs_u256 : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
              [.var .local (ofString "t"),
               .op .add [.var .local (ofString "topics"),
                 .panop .mul [.var .local (ofString "i"), .const 32#64]]] =
              some [tv, .val (.word out_i)] := by
            unfold evalListHOLFinite
            rw [evalListHOLExact, evalListHOLExact]
            have ht_ev : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
                (.var .local (ofString "t")) = some tv := by
              simp [evalHOLExact, hs1_t]
            rw [ht_ev, hout_eval]; rfl
          have htv_sh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact tv) = true := by
            simp only [Bool.and_eq_true] at hsh_tv
            exact (shapeEqHOL_eq_true _ _).mpr ((shapeEqHOL_eq_true _ _).mp hsh_tv.1).symm
          have hlk_u256 : lookupCodeHOLFinite s1.code.lookup (ofString "u256_to_be32") [tv, .val (.word out_i)] =
              some (sourceFnBody Guest.Software.guestFn_u256_to_be32,
                (HolFiniteMapExact.empty.update (ofString "a", tv)).update (ofString "out", .val (.word out_i)),
                .one) := by
            have hd_ao : ofString "a" ≠ ofString "out" := by decide
            have raw : lookupCodeHOLExact s1.code.lookup (ofString "u256_to_be32") [tv, .val (.word out_i)] =
                some (sourceFnBody Guest.Software.guestFn_u256_to_be32,
                  (fun key => if key = ofString "out" then some (.val (.word out_i))
                    else if key = ofString "a" then some tv else none),
                  .one) := by
              simp [lookupCodeHOLExact, hs1_code, lookup_u256_to_be32_b, htv_sh, shapeOfHOLExact, shapeEqHOL, hd_ao]
            unfold PanSemStateFiniteExact.lookupCodeHOLFinite
            split
            · rename_i missing; rw [raw] at missing; cases missing
            · rename_i foundBody foundLocals foundShape found
              have equal := Option.some.inj (found.symm.trans raw)
              obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
              apply congrArg (fun locals => some (sourceFnBody Guest.Software.guestFn_u256_to_be32, locals, ShapeHOL.one))
              apply HolFiniteMapExact.ext
              funext key
              by_cases ho_k : key = ofString "out"
              · subst key; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]
              · have ho_k' : ofString "out" ≠ key := Ne.symm ho_k
                by_cases ha_k : key = ofString "a"
                · subst key; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, hd_ao, Ne.symm hd_ao]
                · have ha_k' : ofString "a" ≠ key := Ne.symm ha_k
                  simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, ha_k, ho_k, ha_k', ho_k']
          rw [evaluateHOLFiniteState_seq_line780] at hbody'
          let ucallProg : ProgHOL 64 :=
            .call (some (none, none)) (ofString "u256_to_be32")
              [.var .local (ofString "t"),
               .op .add [.var .local (ofString "topics"),
                 .panop .mul [.var .local (ofString "i"), .const 32#64]]]
          rcases hu_call : evaluateHOLFiniteState s1 ucallProg with ⟨ru, su⟩
          have hu_call' := hu_call
          rw [evaluateHOLFiniteState_call, hargs_u256] at hu_call'; dsimp only at hu_call'
          rw [hlk_u256] at hu_call'; dsimp only at hu_call'
          have hs1_def : setVarHOLFinite (ofString "t") tv { ssp with locals := s_dc.locals } = s1 := rfl
          have huc_def : (.call (some (none, none)) (ofString "u256_to_be32")
              [.var .local (ofString "t"),
               .op .add [.var .local (ofString "topics"),
                 .panop .mul [.var .local (ofString "i"), .const 32#64]]] : ProgHOL 64) = ucallProg := rfl
          rw [hs1_def, huc_def, hu_call] at hbody'
          by_cases hclk_u : s1.clock = 0
          · simp [hclk_u] at hu_call'
            have hru := hu_call'.1.symm; subst hru; dsimp only at hbody'
            injection hbody' with hrb _
            exact hnot_to_err (Or.inl hrb.symm)
          · simp only [hclk_u, ↓reduceIte] at hu_call'
            let cal_u := (HolFiniteMapExact.empty.update (ofString "a", tv)).update (ofString "out", .val (.word out_i))
            let ent_u := callEntryStateHOLFinite s1 cal_u
            have hout_ent_lu : ent_u.locals.lookup (ofString "out") = some (.val (.word out_i)) := by
              simp [ent_u, cal_u, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have hu_eff_ne := u256_to_be32_aligned_body_g09 ent_u out_i hs1_code hs1_ma
              hout_ent_lu hout_i_mod8 hout_i_end
            have hu_nfe := u256_to_be32_aligned_no_ffi_exc_g09 ent_u out_i hs1_code
              hout_ent_lu hout_i_mod8
            rcases hu_b : evaluateHOLFiniteState ent_u (sourceFnBody Guest.Software.guestFn_u256_to_be32) with ⟨rub, sub⟩
            change evaluateHOLFiniteState ent_u (sourceFnBody Guest.Software.guestFn_u256_to_be32) = (rub, sub) at hu_b
            simp only [ent_u, cal_u, hu_b] at hu_call' hu_eff_ne
            rw [hu_b] at hu_nfe
            cases rub with
            | none =>
              injection hu_call' with hru _; subst hru; dsimp only at hbody'
              injection hbody' with hrb _
              exact hnot_to_err (Or.inr hrb.symm)
            | some rub0 =>
              cases rub0 with
              | timeOut =>
                injection hu_call' with hru _; subst hru; dsimp only at hbody'
                injection hbody' with hrb _
                exact hnot_to_err (Or.inl hrb.symm)
              | error | «break» | «continue» =>
                injection hu_call' with hru _; subst hru; dsimp only at hbody'
                injection hbody' with hrb _
                exact hnot_to_err (Or.inr hrb.symm)
              | finalFfi f1 =>
                exact absurd rfl (hu_nfe.1 f1)
              | exception eidu evu =>
                exact absurd rfl (hu_nfe.2 eidu evu)
              | returned rvu =>
                dsimp only at hu_call'
                split at hu_call'
                · injection hu_call' with hru hsu; subst hru hsu
                  dsimp only at hbody'
                  let s2 : PanSemStateFiniteExact 64 F := { sub with locals := s1.locals }
                  have hs2_eff : ByteRegionEffect s1 s2 [(out_i.toNat, 32)] :=
                    ((ByteRegionEffect.refl s1 _).with_locals_clock _ _).trans
                      (hu_eff_ne.1.with_locals_clock _ _)
                  have hs1_mem_ssp : s1.memory = ssp.memory := rfl
                  have hs1_glob_ssp : s1.globals = ssp.globals := rfl
                  have hent_mem_s : ent_sp.memory = s.memory := rfl
                  have hent_glob_s : ent_sp.globals = s.globals := rfl
                  have hwti_s1 : worldTypedIvls s1 S Nd = worldTypedIvls s S Nd :=
                    (worldTypedIvls_congr_mg_g09 hs1_mem_ssp hs1_glob_ssp).trans
                      (hssp_wti.trans (worldTypedIvls_congr_mg_g09 hent_mem_s hent_glob_s))
                  have hfo_s1 : (evmChain s1).map (frameObjects s1) = (evmChain s).map (frameObjects s) :=
                    (map_frameObjects_congr_mg_g09 hs1_mem_ssp hs1_glob_ssp).trans
                      (hssp_fo.trans (map_frameObjects_congr_mg_g09 hent_mem_s hent_glob_s))
                  have hdj_out : IvlsDisj [(out_i.toNat, 32)]
                      (worldTypedIvls s1 S Nd ++ ((evmChain s1).map (frameObjects s1)).flatten) := by
                    rw [hwti_s1, hfo_s1]
                    intro x hx j hj
                    simp only [List.mem_singleton] at hx; subst hx
                    have hdj_top := hdj (topics.toNat, qw.toNat - topics.toNat) (List.mem_singleton.2 rfl) j hj
                    rcases hdj_top with h0 | h0 | h1 | h2
                    · omega
                    · exact Or.inr (Or.inl h0)
                    · exact Or.inr (Or.inr (Or.inl (by dsimp only at h1 ⊢; omega)))
                    · exact Or.inr (Or.inr (Or.inr (by dsimp only at h2 ⊢; omega)))
                  have hs2_step := evmInvWith_of_bre hs1_InvW hdj_out hs2_eff
                  obtain ⟨hs2_InvW, hs2_wti, hs2_fo, hs2_glob, hs2_ch, hs2_R, hs2_HM⟩ := hs2_step
                  rw [evaluateHOLFiniteState_assign] at hbody'
                  have hs2_i : s2.locals.lookup (ofString "i") = some (.val (.word iv)) := hs1_i
                  have hadd_i : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
                      (.op .add [.var .local (ofString "i"), .const 1#64]) =
                      some (.val (.word (iv + 1))) := by
                    simp [evalHOLExact, evalListHOLExact, hs2_i, valueIsWord, valueWord, wordOpHOL, wordOp]
                  have hval_i : s2.isValidValueHOLFinite .local (ofString "i") (.val (.word (iv + 1))) = true := by
                    simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hs2_i,
                      shapeOfHOLExact, shapeEqHOL]
                  have hs2_def : ({ sub with locals := s1.locals } : PanSemStateFiniteExact 64 F) = s2 := rfl
                  rw [hs2_def, hadd_i] at hbody'; dsimp only at hbody'
                  rw [if_pos hval_i] at hbody'
                  dsimp only at hbody'
                  injection hbody' with hrb hsb; subst hrb
                  refine And.intro (fun _ => ?_) (And.intro (fun _ h => by cases h)
                    (And.intro (by simp) (And.intro (by simp) (fun _ h => by cases h))))
                  let s3 : PanSemStateFiniteExact 64 F :=
                    { setKvarHOLFinite .local (ofString "i") (.val (.word (iv + 1))) s2 with
                      locals := (setKvarHOLFinite .local (ofString "i") (.val (.word (iv + 1))) s2).locals.resVarEq
                        (ofString "t", s_dc.locals.lookup (ofString "t")) }
                  have hsb_eq : sb = s3 := hsb.symm
                  subst hsb_eq
                  have hs3_mem : s3.memory = s2.memory := rfl
                  have hs3_glob : s3.globals = s2.globals := rfl
                  have hc_s1 := evm_congr hs1_mem_ssp hs1_glob_ssp
                  have hc_ent := evm_congr hent_mem_s hent_glob_s
                  have hc_s3 := evm_congr hs3_mem hs3_glob
                  refine ⟨hs2_eff.code.trans hs1_code,
                    evmInvWith_localsFree (s := s2) s3.locals s3.clock hs2_InvW,
                    (worldTypedIvls_congr_mg_g09 hs3_mem hs3_glob).trans (hs2_wti.trans hwti_s1),
                    (map_frameObjects_congr_mg_g09 hs3_mem hs3_glob).trans (hs2_fo.trans hfo_s1),
                    (evmChain_congr hs3_mem hs3_glob).trans
                      (hs2_ch.trans ((evmChain_congr hs1_mem_ssp hs1_glob_ssp).trans
                        (hssp_ch.trans (evmChain_congr hent_mem_s hent_glob_s)))),
                    hc_s3.2.1.trans (hs2_R.trans (hc_s1.2.1.trans (hssp_R.trans hc_ent.2.1))),
                    ?_, ?_, ?_, ?_⟩
                  · have hg_eq : s3.globals = s.globals :=
                      hs3_glob.trans (hs2_glob.trans (hs1_glob_ssp.trans (hssp_glob.trans hent_glob_s)))
                    exact congrFun (globN_congr hg_eq) "heap_ptr"
                  · intro hHM_s
                    have hHM_ent : HeadMemAligned ent_sp :=
                      headMemAligned_congr_head hent_glob_s (fun off _ => congrFun (memW_congr hent_mem_s) _) hHM_s
                    have hHM_s1 : HeadMemAligned s1 :=
                      headMemAligned_congr_head hs1_glob_ssp (fun off _ => congrFun (memW_congr hs1_mem_ssp) _) (hssp_HM hHM_ent)
                    exact headMemAligned_congr_head hs3_glob (fun off _ => congrFun (memW_congr hs3_mem) _) (hs2_HM hHM_s1)
                  · have hit : ofString "i" ≠ ofString "t" := by decide
                    change ((setKvarHOLFinite .local (ofString "i") (.val (.word (iv + 1))) s2).locals.resVarEq
                      (ofString "t", s_dc.locals.lookup (ofString "t"))).lookup (ofString "i") =
                      some (.val (.word (iv + 1)))
                    rw [PanRunBounded.resVarEq_lookup, if_neg hit]
                    simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  · intro nm hnm_i' hnm_t'
                    have hnm_i : ofString "i" ≠ nm := Ne.symm hnm_i'
                    have hnm_t : ofString "t" ≠ nm := Ne.symm hnm_t'
                    change ((setKvarHOLFinite .local (ofString "i") (.val (.word (iv + 1))) s2).locals.resVarEq
                      (ofString "t", s_dc.locals.lookup (ofString "t"))).lookup nm = s.locals.lookup nm
                    rw [PanRunBounded.resVarEq_lookup, if_neg hnm_t']
                    simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                      hnm_i, hnm_t, hnm_i', hnm_t', s2, s1, s_dc, decClockHOLFinite]
                · injection hu_call' with hru _; subst hru; dsimp only at hbody'
                  injection hbody' with hrb _
                  exact hnot_to_err (Or.inr hrb.symm)
        · injection hbody' with hrb _
          exact hnot_to_err (Or.inr hrb.symm)

private theorem op_log_topic_while_step_g09 {F : Type}
    {s0 : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {nt topics qw : BitVec 64} {cont : ProgHOL 64} :
    ∀ (rem : Nat) (s : PanSemStateFiniteExact 64 F) (iv : BitVec 64),
      iv.toNat + rem = nt.toNat →
      nt.toNat ≤ 4 →
      s.code = originalRuntimeCode →
      EvmInvWith s S Nd →
      (evmChain s).length = (evmChain s0).length →
      evmR s < evmR s0 →
      topics.toNat + (32 * nt.toNat + 8) ≤ qw.toNat →
      qw.toNat ≤ heapLimit →
      topics.toNat % 8 = 0 →
      sourceBase ≤ topics.toNat →
      IvlsDisj [(topics.toNat, qw.toNat - topics.toNat)]
        (worldTypedIvls s S Nd ++ ((evmChain s).map (frameObjects s)).flatten) →
      s.locals.lookup (ofString "i") = some (.val (.word iv)) →
      s.locals.lookup (ofString "ntopics") = some (.val (.word nt)) →
      s.locals.lookup (ofString "topics") = some (.val (.word topics)) →
      (∀ (s_end : PanSemStateFiniteExact 64 F),
        s_end.code = originalRuntimeCode →
        EvmInvWith s_end S Nd →
        (evmChain s_end).length = (evmChain s0).length →
        evmR s_end < evmR s0 →
        globN s_end "heap_ptr" = globN s "heap_ptr" →
        (HeadMemAligned s → HeadMemAligned s_end) →
        IvlsDisj [(topics.toNat, qw.toNat - topics.toNat)]
          (worldTypedIvls s_end S Nd ++ ((evmChain s_end).map (frameObjects s_end)).flatten) →
        (∀ nm : MlS, nm ≠ ofString "i" → nm ≠ ofString "t" → s_end.locals.lookup nm = s.locals.lookup nm) →
        (evaluateHOLFiniteState s_end cont).1 ≠ some .timeOut →
        OpDispatchPost s0 (evaluateHOLFiniteState s_end cont).1 (evaluateHOLFiniteState s_end cont).2) →
      (evaluateHOLFiniteState s (.seq opLogWhileProg cont)).1 ≠ some .timeOut →
      OpDispatchPost s0
        (evaluateHOLFiniteState s (.seq opLogWhileProg cont)).1
        (evaluateHOLFiniteState s (.seq opLogWhileProg cont)).2 := by
  intro rem
  induction rem with
  | zero =>
    intro s iv hiv hnt4 hcode hInvW hlen hR htop_le hq_lim htop_mod8 htop_lo hdj hi_lu hnt_lu htop_lu hcont hnt_seq
    have hiv_eq : iv = nt := BitVec.eq_of_toNat_eq (by omega)
    subst hiv_eq
    have hslt_ff : Compiler.Encoders.Asm.holAsmSignedLess iv iv = false := by
      rw [holAsmSignedLess_eq_slt_g09]; simp [BitVec.slt]
    rw [evaluateHOLFiniteState_seq_line780] at hnt_seq ⊢
    rcases hw : evaluateHOLFiniteState s opLogWhileProg with ⟨rw0, sw0⟩
    have hw' := hw
    unfold opLogWhileProg at hw'
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hw'
    have hcmp0 : PanSemStateFiniteExact.evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "ntopics"))) =
        some (.val (.word 0)) := by
      simp [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact, hi_lu, hnt_lu,
        Compiler.Encoders.Asm.wordCmpHOL, hslt_ff]
    rw [hcmp0] at hw'
    simp only [ne_eq, not_true_eq_false, ↓reduceIte] at hw'
    injection hw' with hrw hsw
    subst hrw hsw
    rw [hw] at hnt_seq
    dsimp only at hnt_seq ⊢
    exact hcont s hcode hInvW hlen hR rfl id hdj (fun _ _ _ => rfl) hnt_seq
  | succ rem ih =>
    intro s iv hiv hnt4 hcode hInvW hlen hR htop_le hq_lim htop_mod8 htop_lo hdj hi_lu hnt_lu htop_lu hcont hnt_seq
    have hiv_lt : iv.toNat < nt.toNat := by omega
    have hslt_tt : Compiler.Encoders.Asm.holAsmSignedLess iv nt = true := by
      rw [holAsmSignedLess_eq_slt_g09, BitVec.slt_eq_decide, BitVec.toInt_eq_msb_cond,
        BitVec.toInt_eq_msb_cond, BitVec.msb_eq_decide, BitVec.msb_eq_decide]
      have h263 : (2 ^ 63 : Nat) = 9223372036854775808 := by norm_num
      have h1 : decide (2 ^ 63 ≤ iv.toNat) = false := decide_eq_false (by omega)
      have h2 : decide (2 ^ 63 ≤ nt.toNat) = false := decide_eq_false (by omega)
      rw [h1, h2]; simp [decide_eq_true_eq]; omega
    rw [evaluateHOLFiniteState_seq_line780] at hnt_seq ⊢
    rcases hw : evaluateHOLFiniteState s opLogWhileProg with ⟨rw0, sw0⟩
    have hw' := hw
    conv_lhs at hw' => unfold opLogWhileProg; rw [evaluateHOLFiniteState_while_fixClockRewrite]
    have hcmp1 : PanSemStateFiniteExact.evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "ntopics"))) =
        some (.val (.word 1)) := by
      simp [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact, hi_lu, hnt_lu,
        Compiler.Encoders.Asm.wordCmpHOL, hslt_tt]
    rw [hcmp1] at hw'
    have h10 : ((1 : BitVec 64) ≠ 0) := by decide
    simp only [ne_eq, h10, not_false_eq_true, ↓reduceIte] at hw'
    by_cases hclk0 : s.clock = 0
    · simp only [hclk0, ↓reduceIte] at hw'
      injection hw' with hrw hsw; subst hrw hsw; rw [hw] at hnt_seq; simp at hnt_seq
    · simp only [hclk0, ↓reduceIte] at hw'
      have hbody_step := op_log_while_body_step_g09 hiv_lt hnt4 hcode hInvW htop_le hq_lim htop_mod8 hdj hi_lu htop_lu
      dsimp only at hbody_step
      rcases hbody : evaluateHOLFiniteState (decClockHOLFinite s) opLogWhileBody with ⟨rb, sb⟩
      change evaluateHOLFiniteState (decClockHOLFinite s) opLogWhileBody = (rb, sb) at hbody
      rw [hbody] at hw' hbody_step
      dsimp only at hw' hbody_step
      cases rb with
      | none =>
        obtain ⟨hsb_code, hsb_InvW, hsb_wti, hsb_fo, hsb_ch, hsb_R, hsb_hp, hsb_HM, hsb_i, hsb_loc⟩ :=
          hbody_step.1 rfl
        have hdj_sb : IvlsDisj [(topics.toNat, qw.toNat - topics.toNat)]
            (worldTypedIvls sb S Nd ++ ((evmChain sb).map (frameObjects sb)).flatten) := by
          rwa [hsb_wti, hsb_fo]
        have hiv1_nat : (iv + 1).toNat = iv.toNat + 1 := by
          have : (1 : BitVec 64).toNat = 1 := rfl
          rw [BitVec.toNat_add, this, Nat.mod_eq_of_lt (by omega)]
        change evaluateHOLFiniteState sb opLogWhileProg = (rw0, sw0) at hw'
        have hnt_sb : (evaluateHOLFiniteState sb (.seq opLogWhileProg cont)).1 ≠ some .timeOut := by
          rw [evaluateHOLFiniteState_seq_line780, hw']
          dsimp only at hnt_seq ⊢
          try rw [hw] at hnt_seq
          exact hnt_seq
        have hih := ih sb (iv + 1) (by omega) hnt4 hsb_code hsb_InvW
          (by rw [hsb_ch]; exact hlen) (by rw [hsb_R]; exact hR)
          htop_le hq_lim htop_mod8 htop_lo hdj_sb hsb_i
          (by rw [hsb_loc _ (by decide) (by decide)]; exact hnt_lu)
          (by rw [hsb_loc _ (by decide) (by decide)]; exact htop_lu)
          (fun s_end hc_e hInv_e hlen_e hR_e hhp_e hHM_e hdj_e hloc_e hnt_e =>
            hcont s_end hc_e hInv_e hlen_e hR_e (hhp_e.trans hsb_hp)
              (fun hHM_s => hHM_e (hsb_HM hHM_s)) hdj_e
              (fun nm hnm_i hnm_t => (hloc_e nm hnm_i hnm_t).trans (hsb_loc nm hnm_i hnm_t)) hnt_e)
          hnt_sb
        rw [evaluateHOLFiniteState_seq_line780, hw'] at hih
        dsimp only at hih ⊢
        exact hih
      | some rb0 =>
        cases rb0 with
        | timeOut =>
          injection hw' with hrw hsw; subst hrw hsw; try rw [hw] at hnt_seq
          dsimp only at hnt_seq; exact absurd rfl hnt_seq
        | error =>
          injection hw' with hrw hsw; subst hrw hsw; dsimp only; exact opDispatchPost_error s0 sb
        | «break» => exact absurd rfl hbody_step.2.2.1
        | «continue» => exact absurd rfl hbody_step.2.2.2.1
        | returned rv => exact absurd rfl (hbody_step.2.2.2.2 rv)
        | finalFfi ff =>
          injection hw' with hrw hsw; subst hrw hsw; dsimp only
          refine And.intro (fun ⟨_, h⟩ => by cases h) (fun ⟨_, h⟩ => by cases h)
        | exception eid ev =>
          injection hw' with hrw hsw; subst hrw hsw; dsimp only
          by_cases heid : eid = ofString "EvmErr"
          · subst heid
            obtain ⟨hsb_InvW, hsb_ch, hsb_R⟩ := hbody_step.2.1 ev rfl
            refine And.intro (fun ⟨_, h⟩ => by cases h) (fun _ => ⟨evmInvWith_to_evmInv hsb_InvW, ?_, ?_⟩)
            · rw [hsb_ch]; exact hlen
            · change evmR sb ≤ evmR s0; rw [hsb_R]; exact Nat.le_of_lt hR
          · refine And.intro (fun ⟨_, h⟩ => by cases h) (fun ⟨_, h⟩ => ?_)
            injection h with h'; injection h' with h1 _; exact absurd h1 heid

private def MemcpyWordInvG09 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (dst0 src0 n0 : BitVec 64) (t : PanSemStateFiniteExact 64 F) : Prop :=
  ByteRegionEffect s0 t [(dst0.toNat, n0.toNat)] ∧
  t.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
  t.locals.lookup (ofString "src") = some (.val (.word src0)) ∧
  t.locals.lookup (ofString "n") = some (.val (.word n0)) ∧
  ∃ iv : BitVec 64,
    t.locals.lookup (ofString "i") = some (.val (.word iv)) ∧
    iv.toNat ≤ n0.toNat ∧
    iv.toNat % 8 = 0 ∧
    ∀ k, 8 * k < iv.toNat → memW t (dst0.toNat + 8 * k) = memW s0 (src0.toNat + 8 * k)

private theorem memcpy_word_one_step_g09 {F : Type}
    {s0 st : PanSemStateFiniteExact 64 F}
    {dst0 src0 n0 iv : BitVec 64} {c : Nat}
    {addrExp srcExp : ExpHOL 64}
    (hma0 : s0.memaddrs = ordinaryDomain)
    (hd8 : dst0.toNat % 8 = 0)
    (hs8 : src0.toNat % 8 = 0)
    (hiv8 : iv.toNat % 8 = 0)
    (hc8 : c % 8 = 0)
    (hstep_le : iv.toNat + c + 8 ≤ n0.toNat)
    (hd_nw : dst0.toNat + n0.toNat ≤ 2 ^ 64)
    (hs_nw : src0.toNat + n0.toNat ≤ 2 ^ 64)
    (hdisj : Disj (dst0.toNat, n0.toNat) (src0.toNat, n0.toNat))
    (heff : ByteRegionEffect s0 st [(dst0.toNat, n0.toNat)])
    (hcopied : ∀ k, 8 * k < iv.toNat + c → memW st (dst0.toNat + 8 * k) = memW s0 (src0.toNat + 8 * k))
    (haddr : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) addrExp =
      some (.val (.word (dst0 + (iv + BitVec.ofNat 64 c)))))
    (hsrc_ev : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) srcExp =
      some (.val (.word (src0 + (iv + BitVec.ofNat 64 c))))) :
    (∀ sm, evaluateHOLFiniteState st (.store addrExp (.load .one srcExp)) = (none, sm) →
      ByteRegionEffect s0 sm [(dst0.toNat, n0.toNat)] ∧
      sm.locals = st.locals ∧
      (∀ k, 8 * k < iv.toNat + c + 8 → memW sm (dst0.toNat + 8 * k) = memW s0 (src0.toNat + 8 * k))) ∧
    (∀ r, r ≠ none → (evaluateHOLFiniteState st (.store addrExp (.load .one srcExp))).1 = r → r = some .error) := by
  have hma_st : st.memaddrs = ordinaryDomain := heff.memaddrs.trans hma0
  have hivc_nat : (iv + BitVec.ofNat 64 c).toNat = iv.toNat + c := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hx_nat : (dst0 + (iv + BitVec.ofNat 64 c)).toNat = dst0.toNat + (iv.toNat + c) := by
    rw [BitVec.toNat_add, hivc_nat, Nat.mod_eq_of_lt (by omega)]
  have hy_nat : (src0 + (iv + BitVec.ofNat 64 c)).toNat = src0.toNat + (iv.toNat + c) := by
    rw [BitVec.toNat_add, hivc_nat, Nat.mod_eq_of_lt (by omega)]
  set x := dst0 + (iv + BitVec.ofNat 64 c)
  set y := src0 + (iv + BitVec.ofNat 64 c)
  refine ⟨fun sm hsm => ?_, fun r hrne hreq => ?_⟩
  · have hsm_raw := hsm
    rw [evaluateHOLFiniteState_store, haddr] at hsm_raw
    dsimp only at hsm_raw
    have hload_eq : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
        (.load .one srcExp) =
        @memLoadHOLExact 64 _ .one y st.memaddrs (fun a => Classical.propDecidable (st.memaddrs a)) st.memory st.structs := by
      simp [evalHOLExact, isWfShapeExactHOL, hsrc_ev]
    rw [hload_eq] at hsm_raw
    by_cases hdom_y : st.memaddrs y
    · rcases hmem_y : st.memory y with ⟨wy⟩
      have hml_y : @memLoadHOLExact 64 _ .one y st.memaddrs
          (fun a => Classical.propDecidable (st.memaddrs a)) st.memory st.structs = some (.val (.word wy)) := by
        simp [memLoadHOLExact, isWfShapeExactHOL, hdom_y, hmem_y]
      rw [hml_y] at hsm_raw
      dsimp only at hsm_raw
      by_cases hdom_x : st.memaddrs x
      · obtain ⟨heff_step, hloc_sm⟩ := ByteRegionEffect.of_store_word hma_st hsm
          (fun v hv => by rw [hload_eq, hml_y] at hv; injection hv with hv'; exact ⟨wy, hv'.symm⟩)
          (fun addr ha _ => by
            rw [haddr] at ha; injection ha with h1; injection h1 with h2; injection h2 with h3; subst h3
            exact ⟨(dst0.toNat, n0.toNat), List.mem_singleton.2 rfl,
              by dsimp only; rw [hx_nat]; omega, by dsimp only; rw [hx_nat]; omega⟩)
        have hsm_mem : sm.memory = (fun a => if a = x then .word wy else st.memory a) := by
          simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom_x, ↓reduceIte] at hsm_raw
          injection hsm_raw with _ hst_eq
          have hmem_eq := congrArg PanSemStateFiniteExact.memory hst_eq
          dsimp only at hmem_eq
          exact hmem_eq.symm.trans (by
            funext a
            by_cases hax : a = x
            · subst hax; simp [FUPDATE]
            · simp [FUPDATE, hax])
        have hwy_eq : wy.toNat = memW s0 (src0.toNat + (iv.toNat + c)) := by
          have hst_mw : memW st (src0.toNat + (iv.toNat + c)) = wy.toNat := by
            unfold memW
            have hy_bv : BitVec.ofNat 64 (src0.toNat + (iv.toNat + c)) = y :=
              BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hy_nat])
            rw [hy_bv, hmem_y]
          have hfr_src : memW st (src0.toNat + (iv.toNat + c)) = memW s0 (src0.toNat + (iv.toNat + c)) :=
            memW_eq_of_frameDisj_g09 hma0 heff hs_nw hs8 (by omega) (by omega)
              (fun z hz => by simp at hz; subst hz; exact hdisj)
          omega
        refine ⟨heff.trans heff_step, hloc_sm, fun k hk => ?_⟩
        by_cases hk_old : 8 * k < iv.toNat + c
        · have hne_kx : BitVec.ofNat 64 (dst0.toNat + 8 * k) ≠ x := by
            intro heq
            have := congrArg BitVec.toNat heq
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hx_nat] at this
            omega
          have hsm_old : memW sm (dst0.toNat + 8 * k) = memW st (dst0.toNat + 8 * k) := by
            unfold memW; rw [hsm_mem]; simp [hne_kx]
          exact hsm_old.trans (hcopied k hk_old)
        · have hk_eq : 8 * k = iv.toNat + c := by omega
          have hx_bv : BitVec.ofNat 64 (dst0.toNat + 8 * k) = x :=
            BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hx_nat, hk_eq])
          have hsm_new : memW sm (dst0.toNat + 8 * k) = wy.toNat := by
            unfold memW; rw [hsm_mem, hx_bv]; dsimp only; rw [if_pos rfl]
          rw [hsm_new, hwy_eq, hk_eq]
      · simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom_x] at hsm_raw
    · simp [memLoadHOLExact, hdom_y] at hsm_raw
  · rw [evaluateHOLFiniteState_store] at hreq
    split at hreq
    · split at hreq
      · split at hreq
        · simp at hreq; exact absurd hreq.symm hrne
        · exact hreq.symm
      · exact hreq.symm
    · exact hreq.symm

private theorem memcpy_word_loop_runner_g09 {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (dst0 src0 n0 : BitVec 64) (step : Nat)
    (cond : ExpHOL 64) (body : ProgHOL 64)
    (hcond_eq : cond = .cmp .notLower (.var .local (ofString "n"))
      (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 step)]))
    (hstep_le32 : step ≤ 32)
    (hn_small : n0.toNat + 32 < 2 ^ 63)
    (hbody : ∀ st : PanSemStateFiniteExact 64 F,
      MemcpyWordInvG09 s0 dst0 src0 n0 st →
      (∃ iv : BitVec 64, st.locals.lookup (ofString "i") = some (.val (.word iv)) ∧ iv.toNat + step ≤ n0.toNat) →
      (∀ sb, evaluateHOLFiniteState (decClockHOLFinite st) body = (none, sb) →
        MemcpyWordInvG09 s0 dst0 src0 n0 sb) ∧
      (∀ r, r ≠ none → (evaluateHOLFiniteState (decClockHOLFinite st) body).1 = r → r = some .error))
    (t0 : PanSemStateFiniteExact 64 F)
    (hinv0 : MemcpyWordInvG09 s0 dst0 src0 n0 t0)
    (hnt0 : (evaluateHOLFiniteState t0 (.while cond body)).1 ≠ some .timeOut) :
    ((evaluateHOLFiniteState t0 (.while cond body)).1 = none →
      MemcpyWordInvG09 s0 dst0 src0 n0 (evaluateHOLFiniteState t0 (.while cond body)).2 ∧
      ∃ iv_end : BitVec 64,
        (evaluateHOLFiniteState t0 (.while cond body)).2.locals.lookup (ofString "i") = some (.val (.word iv_end)) ∧
        n0.toNat < iv_end.toNat + step) ∧
    ((evaluateHOLFiniteState t0 (.while cond body)).1 ≠ none →
      (evaluateHOLFiniteState t0 (.while cond body)).1 = some .error) := by
  suffices hmain : ∀ (k : Nat) (s : PanSemStateFiniteExact 64 F), s.clock = k →
      MemcpyWordInvG09 s0 dst0 src0 n0 s →
      (evaluateHOLFiniteState s (.while cond body)).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState s (.while cond body)).1 = none →
        MemcpyWordInvG09 s0 dst0 src0 n0 (evaluateHOLFiniteState s (.while cond body)).2 ∧
        ∃ iv_end : BitVec 64,
          (evaluateHOLFiniteState s (.while cond body)).2.locals.lookup (ofString "i") = some (.val (.word iv_end)) ∧
          n0.toNat < iv_end.toNat + step) ∧
      ((evaluateHOLFiniteState s (.while cond body)).1 ≠ none →
        (evaluateHOLFiniteState s (.while cond body)).1 = some .error) by
    exact hmain t0.clock t0 rfl hinv0 hnt0
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro s hclk hPs hnt_s
    obtain ⟨heff_s, hs_dst, hs_src, hs_n, iv, hs_i, hiv_le, hiv8, hcop_s⟩ := hPs
    have h263 : (2 ^ 63 : Nat) < 2 ^ 64 := by decide
    have hc_ev : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) cond =
        some (.val (.word (if iv.toNat + step ≤ n0.toNat then 1 else 0))) := by
      rw [hcond_eq, evalHOLFinite_eq_toExact]
      have hz_s : BitVec.ofNat 64 step + (0 : BitVec 64) = BitVec.ofNat 64 step := BitVec.add_zero _
      have hadd : (iv + (BitVec.ofNat 64 step + (0 : BitVec 64))).toNat = iv.toNat + step := by
        rw [hz_s, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      simp only [evalHOLExact, evalListHOLExact, hs_n, hs_i, wordOpHOL, wordOp, valueIsWord, valueWord,
        List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
        Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, Bool.not_eq_true', decide_eq_false_iff_not]
      change some (ValueHOL.val (HolWordLab.word
        (if ¬n0.toNat < (iv + (BitVec.ofNat 64 step + (0 : BitVec 64))).toNat then 1 else 0))) = _
      rw [hadd]
      by_cases hle : iv.toNat + step ≤ n0.toNat
      · have hnl : ¬ (n0.toNat < iv.toNat + step) := by omega
        simp [hle, hnl]
      · have hlt : n0.toNat < iv.toNat + step := by omega
        simp [hle, hlt]
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt_s ⊢
    simp only [hc_ev] at hnt_s ⊢
    by_cases hle_st : iv.toNat + step ≤ n0.toNat
    · simp only [hle_st, ↓reduceIte] at hnt_s ⊢
      have h10 : (1 : BitVec 64) ≠ 0 := by decide
      rw [if_pos h10] at hnt_s ⊢
      by_cases hk0 : s.clock = 0
      · simp [hk0] at hnt_s
      · rw [if_neg hk0] at hnt_s ⊢
        obtain ⟨hb_none, hb_err⟩ := hbody s ⟨heff_s, hs_dst, hs_src, hs_n, iv, hs_i, hiv_le, hiv8, hcop_s⟩
          ⟨iv, hs_i, hle_st⟩
        have hb_clk := Flapjack.evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
        have hd_clk : (decClockHOLFinite s).clock < k := by simp [decClockHOLFinite, hclk]; omega
        rcases hbo : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨rb, sb⟩
        simp only [hbo] at hnt_s hb_clk ⊢
        cases rb with
        | none =>
          dsimp only at hnt_s hb_clk ⊢
          exact ih sb.clock (lt_of_le_of_lt hb_clk hd_clk) sb rfl (hb_none sb hbo) hnt_s
        | some r =>
          have herr := hb_err (some r) (by simp) (by rw [hbo])
          injection herr with hr; subst hr
          exact ⟨fun h => by simp at h, fun _ => rfl⟩
    · simp only [hle_st, ↓reduceIte] at hnt_s ⊢
      have h00 : ¬ ((0 : BitVec 64) ≠ 0) := by decide
      rw [if_neg h00]
      exact ⟨fun _ => ⟨⟨heff_s, hs_dst, hs_src, hs_n, iv, hs_i, hiv_le, hiv8, hcop_s⟩, iv, hs_i, by omega⟩,
        fun h => False.elim (h rfl)⟩

theorem eval_call_memcpy_words_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dstExp srcExp nExp : ExpHOL 64)
    (dst0 src0 n0 : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) srcExp =
      some (.val (.word src0)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n0)))
    (hd8 : dst0.toNat % 8 = 0)
    (hs8 : src0.toNat % 8 = 0)
    (hn8 : n0.toNat % 8 = 0)
    (hn_small : n0.toNat + 32 < 2 ^ 63)
    (hd_nw : dst0.toNat + n0.toNat ≤ 2 ^ 64)
    (hs_nw : src0.toNat + n0.toNat ≤ 2 ^ 64)
    (hdisj : Disj (dst0.toNat, n0.toNat) (src0.toNat, n0.toNat))
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp])
    (out.1 = none →
      ByteRegionEffect s out.2 [(dst0.toNat, n0.toNat)] ∧
      out.2.locals = s.locals ∧
      (∀ k, 8 * k < n0.toNat → memW out.2 (dst0.toNat + 8 * k) = memW s (src0.toNat + 8 * k))) ∧
    (out.1 ≠ none → ¬ IsEvmErr out.1) := by
  dsimp only
  have h263 : (2 ^ 63 : Nat) < 2 ^ 64 := by decide
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) [dstExp, srcExp, nExp] =
      some [.val (.word dst0), .val (.word src0), .val (.word n0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hsrc, hn]
  have hlook := pan_three_word_lookup s.code.lookup (ofString "memcpy")
    (ofString "dst") (ofString "src") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_memcpy) dst0 src0 n0
    (by decide) (by decide) (by decide)
    (by rw [hcode]; exact Wave8GuestInv.M11.lookup_memcpy)
  rw [hargs] at hnt ⊢; dsimp only at hnt ⊢
  rw [hlook] at hnt ⊢; dsimp only at hnt ⊢
  by_cases hclk0 : s.clock = 0
  · rw [if_pos hclk0] at hnt; exact absurd rfl hnt
  · rw [if_neg hclk0] at hnt ⊢
    let cmap : HolFiniteMapExact MlS (ValueHOL 64) :=
      ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
        (ofString "src", ValueHOL.val (.word src0))).update (ofString "n", ValueHOL.val (.word n0))
    let entry := callEntryStateHOLFinite s cmap
    have hent_dst : entry.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      have h1 : ofString "n" ≠ ofString "dst" := by decide
      have h2 : ofString "src" ≠ ofString "dst" := by decide
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h1, h2, Ne.symm h1, Ne.symm h2]
    have hent_src : entry.locals.lookup (ofString "src") = some (.val (.word src0)) := by
      have h1 : ofString "n" ≠ ofString "src" := by decide
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h1, Ne.symm h1]
    have hent_n : entry.locals.lookup (ofString "n") = some (.val (.word n0)) := by
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hbody_words :
        let bout := evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_memcpy)
        (∀ rv, bout.1 = some (.returned rv) →
          rv = .val (.word 0) ∧
          ByteRegionEffect entry bout.2 [(dst0.toNat, n0.toNat)] ∧
          (∀ k, 8 * k < n0.toNat → memW bout.2 (dst0.toNat + 8 * k) = memW entry (src0.toNat + 8 * k))) ∧
        (∀ eid ev, bout.1 ≠ some (.exception eid ev)) := by
      have hnt_ent : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_memcpy)).1 ≠ some .timeOut := by
        rintro hto
        change (evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
          (sourceFnBody Guest.Software.guestFn_memcpy)).1 = some .timeOut at hto
        rcases hb_eq : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
          (sourceFnBody Guest.Software.guestFn_memcpy) with ⟨r0, s0'⟩
        rw [hb_eq] at hto hnt; dsimp only at hto; subst hto; exact hnt rfl
      dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memcpy,
        InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
        Option.map, List.map] at hnt_ent ⊢
      rw [evaluateHOLFiniteState_dec_total] at hnt_ent ⊢
      dsimp only at hnt_ent ⊢
      have hev0 : @evalHOLExact 64 F _ entry.toExact (fun a => Classical.propDecidable (entry.memaddrs a))
          (.const (BitVec.ofNat 64 0)) = some (.val (.word 0)) := rfl
      have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) = true := by
        simp [shapeEqHOL, shapeOfHOLExact]
      rw [hev0] at hnt_ent ⊢; dsimp only at hnt_ent ⊢; rw [if_pos hsh0] at hnt_ent ⊢
      set s1 := setVarHOLFinite (ofString "i") (.val (.word 0)) entry
      have hs1_dst : s1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        have hne : ofString "i" ≠ ofString "dst" := by decide
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hent_dst]
      have hs1_src : s1.locals.lookup (ofString "src") = some (.val (.word src0)) := by
        have hne : ofString "i" ≠ ofString "src" := by decide
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hent_src]
      have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word n0)) := by
        have hne : ofString "i" ≠ ofString "n" := by decide
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hent_n]
      have hs1_i : s1.locals.lookup (ofString "i") = some (.val (.word 0)) := by
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hinv1 : MemcpyWordInvG09 entry dst0 src0 n0 s1 :=
        ⟨(ByteRegionEffect.refl entry [(dst0.toNat, n0.toNat)]).with_locals_clock s1.locals s1.clock,
         hs1_dst, hs1_src, hs1_n, 0, hs1_i, Nat.zero_le _, rfl, fun _ hk => by simp at hk⟩
      have ev_add2 : ∀ (st : PanSemStateFiniteExact 64 F) (nm : String) (base iv : BitVec 64),
          st.locals.lookup (ofString nm) = some (.val (.word base)) →
          st.locals.lookup (ofString "i") = some (.val (.word iv)) →
          @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
            (.op .add [.var .local (ofString nm), .var .local (ofString "i")]) =
            some (.val (.word (base + (iv + BitVec.ofNat 64 0)))) := by
        intro st nm base iv hb hi
        simp only [evalHOLExact, evalListHOLExact, hb, hi, wordOpHOL, wordOp, valueIsWord, valueWord,
          List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
        rfl
      have ev_add3 : ∀ (st : PanSemStateFiniteExact 64 F) (nm : String) (base iv : BitVec 64) (c : Nat),
          st.locals.lookup (ofString nm) = some (.val (.word base)) →
          st.locals.lookup (ofString "i") = some (.val (.word iv)) →
          @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
            (.op .add [.var .local (ofString nm), .var .local (ofString "i"), .const (BitVec.ofNat 64 c)]) =
            some (.val (.word (base + (iv + BitVec.ofNat 64 c)))) := by
        intro st nm base iv c hb hi
        simp only [evalHOLExact, evalListHOLExact, hb, hi, wordOpHOL, wordOp, valueIsWord, valueWord,
          List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
        congr 3
        have hz : BitVec.ofNat 64 c + (0 : BitVec 64) = BitVec.ofNat 64 c := BitVec.add_zero _
        exact congrArg (fun x => base + (iv + x)) hz
      have hasgn_step : ∀ (st : PanSemStateFiniteExact 64 F) (iv : BitVec 64) (step : Nat),
          ByteRegionEffect entry st [(dst0.toNat, n0.toNat)] →
          st.locals.lookup (ofString "dst") = some (.val (.word dst0)) →
          st.locals.lookup (ofString "src") = some (.val (.word src0)) →
          st.locals.lookup (ofString "n") = some (.val (.word n0)) →
          st.locals.lookup (ofString "i") = some (.val (.word iv)) →
          iv.toNat + step ≤ n0.toNat →
          (iv.toNat + step) % 8 = 0 →
          (∀ k, 8 * k < iv.toNat + step → memW st (dst0.toNat + 8 * k) = memW entry (src0.toNat + 8 * k)) →
          (∀ p, evaluateHOLFiniteState st
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 step)])) = (none, p) →
            MemcpyWordInvG09 entry dst0 src0 n0 p) ∧
          (∀ r, r ≠ none →
            (evaluateHOLFiniteState st
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 step)]))).1 = r →
            r = some .error) := by
        intro st iv step heff_st hdst_st hsrc_st hn_st hi_st hle_st hmod_st hcop_st
        have hev : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
            (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 step)]) =
            some (.val (.word (iv + BitVec.ofNat 64 step))) := by
          simp only [evalHOLExact, evalListHOLExact, hi_st, wordOpHOL, wordOp, valueIsWord, valueWord,
            List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
          congr 3
          have hz : BitVec.ofNat 64 step + (0 : BitVec 64) = BitVec.ofNat 64 step := BitVec.add_zero _
          exact congrArg (fun x => iv + x) hz
        have hvld : isValidValueHOLFinite st .local (ofString "i") (.val (.word (iv + BitVec.ofNat 64 step))) = true := by
          simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hi_st, shapeOfHOLExact, shapeEqHOL]
        have hrun : evaluateHOLFiniteState st
            (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 step)])) =
            (none, setVarHOLFinite (ofString "i") (.val (.word (iv + BitVec.ofNat 64 step))) st) := by
          rw [evaluateHOLFiniteState_assign, hev]; dsimp only; rw [if_pos hvld]; rfl
        have hiv_add : (iv + BitVec.ofNat 64 step).toNat = iv.toNat + step := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [hrun]
        refine ⟨fun p hp => ?_, fun r hrne hr => absurd hr.symm hrne⟩
        injection hp with _ hp_eq; subst hp_eq
        refine ⟨heff_st.with_locals_clock _ st.clock, ?_, ?_, ?_, iv + BitVec.ofNat 64 step, ?_,
          by omega, by omega, fun k hk => hcop_st k (by omega)⟩
        · have hne : ofString "i" ≠ ofString "dst" := by decide
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hdst_st]
        · have hne : ofString "i" ≠ ofString "src" := by decide
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hsrc_st]
        · have hne : ofString "i" ≠ ofString "n" := by decide
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hn_st]
        · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hseq_step : ∀ {st : PanSemStateFiniteExact 64 F} {c1 c2 : ProgHOL 64}
          {P1 : PanSemStateFiniteExact 64 F → Prop},
          ((∀ m, evaluateHOLFiniteState st c1 = (none, m) → P1 m) ∧
           (∀ r, r ≠ none → (evaluateHOLFiniteState st c1).1 = r → r = some .error)) →
          (∀ m, P1 m →
            (∀ p, evaluateHOLFiniteState m c2 = (none, p) → MemcpyWordInvG09 entry dst0 src0 n0 p) ∧
            (∀ r, r ≠ none → (evaluateHOLFiniteState m c2).1 = r → r = some .error)) →
          (∀ p, evaluateHOLFiniteState st (.seq c1 c2) = (none, p) → MemcpyWordInvG09 entry dst0 src0 n0 p) ∧
          (∀ r, r ≠ none → (evaluateHOLFiniteState st (.seq c1 c2)).1 = r → r = some .error) := by
        intro st c1 c2 P1 hc1 hc2
        rw [evaluateHOLFiniteState_seq_line780]
        rcases h1 : evaluateHOLFiniteState st c1 with ⟨r1, m⟩
        cases r1 with
        | none => exact hc2 m (hc1.1 m h1)
        | some r =>
          dsimp only
          have herr := hc1.2 (some r) (by simp) (by rw [h1])
          exact ⟨fun _ hp => by simp at hp, fun r' _ hr' => by rw [← hr', herr]⟩
      let lp1 : ProgHOL 64 := .while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 32)]))
        (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
                (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
          (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 8)])
                  (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 8)])))
            (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 16)])
                    (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 16)])))
              (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 24)])
                      (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 24)])))
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 32)]))))))
      let lp2 : ProgHOL 64 := .while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]))
        (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
                (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)])))
      let lp3 : ProgHOL 64 := .while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]))
        (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
                (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
          (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 1)])
                  (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 1)])))
            (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 2)])
                    (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 2)])))
              (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 3)])
                      (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 3)])))
                (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 4)])
                        (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 4)])))
                  (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 5)])
                          (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 5)])))
                    (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 6)])
                            (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 6)])))
                      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 7)])
                              (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 7)])))
                        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]))))))))))
      let lp4 : ProgHOL 64 := .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")))
        (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
                (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])))
      let iteP : ProgHOL 64 := .ite
        (.cmp .equal (.op .and [.op .or [.var .local (ofString "dst"), .var .local (ofString "src")], .const (BitVec.ofNat 64 7)]) (.const (BitVec.ofNat 64 0)))
        (.seq lp1 lp2)
        .skip
      have halign_cond : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
          (.cmp .equal (.op .and [.op .or [.var .local (ofString "dst"), .var .local (ofString "src")], .const (BitVec.ofNat 64 7)]) (.const (BitVec.ofNat 64 0))) =
          some (.val (.word 1)) := by
        have hor7 : ((dst0 ||| (src0 ||| (0 : BitVec 64))) &&& ((7 : BitVec 64) &&& ~~~(0 : BitVec 64))) = 0 := by
          apply BitVec.eq_of_toNat_eq
          have h1 : src0 ||| (0 : BitVec 64) = src0 := by simp
          have h2 : (7 : BitVec 64) &&& ~~~(0 : BitVec 64) = (7 : BitVec 64) := by decide
          rw [h1, h2, BitVec.toNat_and, show (7 : BitVec 64).toNat = 2 ^ 3 - 1 from rfl,
            Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_or]
          have hm : (dst0.toNat ||| src0.toNat) % 2 ^ 3 = (dst0.toNat % 2 ^ 3) ||| (src0.toNat % 2 ^ 3) :=
            Nat.or_mod_two_pow
          change (dst0.toNat ||| src0.toNat) % 8 = (dst0.toNat % 8) ||| (src0.toNat % 8) at hm
          rw [hm, hd8, hs8]; rfl
        simp only [evalHOLExact, evalListHOLExact, hs1_dst, hs1_src, wordOpHOL, wordOp, valueIsWord, valueWord,
          List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr, Compiler.Encoders.Asm.wordCmpHOL]
        change some (ValueHOL.val (HolWordLab.word
          (if (((dst0 ||| (src0 ||| (0 : BitVec 64))) &&& ((7 : BitVec 64) &&& ~~~(0 : BitVec 64))) == (0 : BitVec 64)) = true then 1 else 0))) = _
        rw [hor7]; simp
      have hL1 : ∀ t0 : PanSemStateFiniteExact 64 F, MemcpyWordInvG09 entry dst0 src0 n0 t0 →
          (evaluateHOLFiniteState t0 lp1).1 ≠ some .timeOut →
          ((evaluateHOLFiniteState t0 lp1).1 = none →
            MemcpyWordInvG09 entry dst0 src0 n0 (evaluateHOLFiniteState t0 lp1).2) ∧
          ((evaluateHOLFiniteState t0 lp1).1 ≠ none → (evaluateHOLFiniteState t0 lp1).1 = some .error) := by
        intro t0 hinv0 hnt1
        have hr := memcpy_word_loop_runner_g09 entry dst0 src0 n0 32 _ _ rfl (by omega) hn_small
          (fun st hinv_st hex_iv => by
            rcases hinv_st with ⟨heff_st, st_dst, st_src, st_n, iv, st_i, hiv_n, hiv8, hcop_st⟩
            rcases hex_iv with ⟨iv', st_i', hle32⟩
            have hiv_eq : iv' = iv := by
              rw [st_i] at st_i'; injection st_i' with h1; injection h1 with h2; injection h2 with h3; exact h3.symm
            subst iv'
            let d0 := decClockHOLFinite st
            have heff_d0 : ByteRegionEffect entry d0 [(dst0.toNat, n0.toNat)] :=
              heff_st.with_locals_clock st.locals (st.clock - 1)
            have w0 := memcpy_word_one_step_g09 (s0 := entry) (st := d0) (dst0 := dst0) (src0 := src0)
              (n0 := n0) (iv := iv) (c := 0) hma hd8 hs8 hiv8 (by omega) (by omega) hd_nw hs_nw hdisj heff_d0
              (fun k hk => hcop_st k (by omega))
              (ev_add2 d0 "dst" dst0 iv st_dst st_i) (ev_add2 d0 "src" src0 iv st_src st_i)
            refine hseq_step w0 (fun m1 ⟨heff1, hl1, hcop1⟩ => ?_)
            have w8 := memcpy_word_one_step_g09 (s0 := entry) (st := m1) (dst0 := dst0) (src0 := src0)
              (n0 := n0) (iv := iv) (c := 8) hma hd8 hs8 hiv8 (by omega) (by omega) hd_nw hs_nw hdisj heff1
              hcop1 (ev_add3 m1 "dst" dst0 iv 8 (hl1.symm ▸ st_dst) (hl1.symm ▸ st_i))
              (ev_add3 m1 "src" src0 iv 8 (hl1.symm ▸ st_src) (hl1.symm ▸ st_i))
            refine hseq_step w8 (fun m2 ⟨heff2, hl2, hcop2⟩ => ?_)
            have hl2' : m2.locals = st.locals := hl2.trans hl1
            have w16 := memcpy_word_one_step_g09 (s0 := entry) (st := m2) (dst0 := dst0) (src0 := src0)
              (n0 := n0) (iv := iv) (c := 16) hma hd8 hs8 hiv8 (by omega) (by omega) hd_nw hs_nw hdisj heff2
              hcop2 (ev_add3 m2 "dst" dst0 iv 16 (hl2'.symm ▸ st_dst) (hl2'.symm ▸ st_i))
              (ev_add3 m2 "src" src0 iv 16 (hl2'.symm ▸ st_src) (hl2'.symm ▸ st_i))
            refine hseq_step w16 (fun m3 ⟨heff3, hl3, hcop3⟩ => ?_)
            have hl3' : m3.locals = st.locals := hl3.trans hl2'
            have w24 := memcpy_word_one_step_g09 (s0 := entry) (st := m3) (dst0 := dst0) (src0 := src0)
              (n0 := n0) (iv := iv) (c := 24) hma hd8 hs8 hiv8 (by omega) (by omega) hd_nw hs_nw hdisj heff3
              hcop3 (ev_add3 m3 "dst" dst0 iv 24 (hl3'.symm ▸ st_dst) (hl3'.symm ▸ st_i))
              (ev_add3 m3 "src" src0 iv 24 (hl3'.symm ▸ st_src) (hl3'.symm ▸ st_i))
            refine hseq_step w24 (fun m4 ⟨heff4, hl4, hcop4⟩ => ?_)
            have hl4' : m4.locals = st.locals := hl4.trans hl3'
            exact hasgn_step m4 iv 32 heff4 (hl4'.symm ▸ st_dst) (hl4'.symm ▸ st_src)
              (hl4'.symm ▸ st_n) (hl4'.symm ▸ st_i) hle32 (by omega) hcop4)
          t0 hinv0 hnt1
        exact ⟨fun hn => (hr.1 hn).1, hr.2⟩
      have hL2 : ∀ t0 : PanSemStateFiniteExact 64 F, MemcpyWordInvG09 entry dst0 src0 n0 t0 →
          (evaluateHOLFiniteState t0 lp2).1 ≠ some .timeOut →
          ((evaluateHOLFiniteState t0 lp2).1 = none →
            MemcpyWordInvG09 entry dst0 src0 n0 (evaluateHOLFiniteState t0 lp2).2 ∧
            ∃ iv_end : BitVec 64,
              (evaluateHOLFiniteState t0 lp2).2.locals.lookup (ofString "i") = some (.val (.word iv_end)) ∧
              n0.toNat < iv_end.toNat + 8) ∧
          ((evaluateHOLFiniteState t0 lp2).1 ≠ none → (evaluateHOLFiniteState t0 lp2).1 = some .error) := by
        intro t0 hinv0 hnt2
        exact memcpy_word_loop_runner_g09 entry dst0 src0 n0 8 _ _ rfl (by omega) hn_small
          (fun st hinv_st hex_iv => by
            rcases hinv_st with ⟨heff_st, st_dst, st_src, st_n, iv, st_i, hiv_n, hiv8, hcop_st⟩
            rcases hex_iv with ⟨iv', st_i', hle8⟩
            have hiv_eq : iv' = iv := by
              rw [st_i] at st_i'; injection st_i' with h1; injection h1 with h2; injection h2 with h3; exact h3.symm
            subst iv'
            let d0 := decClockHOLFinite st
            have heff_d0 : ByteRegionEffect entry d0 [(dst0.toNat, n0.toNat)] :=
              heff_st.with_locals_clock st.locals (st.clock - 1)
            have w0 := memcpy_word_one_step_g09 (s0 := entry) (st := d0) (dst0 := dst0) (src0 := src0)
              (n0 := n0) (iv := iv) (c := 0) hma hd8 hs8 hiv8 (by omega) (by omega) hd_nw hs_nw hdisj heff_d0
              (fun k hk => hcop_st k (by omega))
              (ev_add2 d0 "dst" dst0 iv st_dst st_i) (ev_add2 d0 "src" src0 iv st_src st_i)
            refine hseq_step w0 (fun m1 ⟨heff1, hl1, hcop1⟩ => ?_)
            exact hasgn_step m1 iv 8 heff1 (hl1.symm ▸ st_dst) (hl1.symm ▸ st_src)
              (hl1.symm ▸ st_n) (hl1.symm ▸ st_i) hle8 (by omega) hcop1)
          t0 hinv0 hnt2
      change (let bout := (let res := evaluateHOLFiniteState s1 (.seq iteP (.seq lp3 (.seq lp4 (.return (.const (BitVec.ofNat 64 0))))))
        (res.1, { res.2 with locals := HolFiniteMapExact.resVarEq res.2.locals (ofString "i", entry.locals.lookup (ofString "i")) }))
        (∀ rv, bout.1 = some (.returned rv) →
          rv = .val (.word 0) ∧
          ByteRegionEffect entry bout.2 [(dst0.toNat, n0.toNat)] ∧
          (∀ k, 8 * k < n0.toNat → memW bout.2 (dst0.toNat + 8 * k) = memW entry (src0.toNat + 8 * k))) ∧
        (∀ eid ev, bout.1 ≠ some (.exception eid ev)))
      have hnt' : (evaluateHOLFiniteState s1 (.seq iteP (.seq lp3 (.seq lp4 (.return (.const (BitVec.ofNat 64 0))))))).1 ≠
          some .timeOut := hnt_ent
      clear hnt_ent
      rw [evaluateHOLFiniteState_seq_line780] at hnt' ⊢
      have hite_eq : evaluateHOLFiniteState s1 iteP = evaluateHOLFiniteState s1 (.seq lp1 lp2) := by
        dsimp only [iteP]; rw [evaluateHOLFiniteState_ite, halign_cond]; dsimp only
        have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
        rw [if_neg h10]
      rw [hite_eq, evaluateHOLFiniteState_seq_line780] at hnt' ⊢
      rcases hr1 : evaluateHOLFiniteState s1 lp1 with ⟨r1, m1⟩
      simp only [hr1] at hnt' ⊢
      have hnt1 : r1 ≠ some .timeOut := by rintro rfl; exact hnt' rfl
      have hs1_res := hL1 s1 hinv1 (by rw [hr1]; exact hnt1)
      rw [hr1] at hs1_res
      cases r1 with
      | some r =>
        dsimp only at hnt' ⊢
        have herr := hs1_res.2 (by simp)
        injection herr with hr_eq; subst hr_eq
        exact ⟨fun _ h => by simp at h, fun _ _ h => by simp at h⟩
      | none =>
        dsimp only at hnt' ⊢
        have hm1_inv := hs1_res.1 rfl
        rcases hr2 : evaluateHOLFiniteState m1 lp2 with ⟨r2, s2⟩
        simp only [hr2] at hnt' ⊢
        have hnt2 : r2 ≠ some .timeOut := by rintro rfl; exact hnt' rfl
        have hs2_res := hL2 m1 hm1_inv (by rw [hr2]; exact hnt2)
        rw [hr2] at hs2_res
        cases r2 with
        | some r =>
          dsimp only at hnt' ⊢
          have herr := hs2_res.2 (by simp)
          injection herr with hr_eq; subst hr_eq
          exact ⟨fun _ h => by simp at h, fun _ _ h => by simp at h⟩
        | none =>
          dsimp only at hnt' ⊢
          obtain ⟨⟨heff2, hs2_dst, hs2_src, hs2_n, iv2, hs2_i, hiv2_le, hiv2_8, hcop2⟩, iv2', hs2_i', hiv2_gt⟩ := hs2_res.1 rfl
          dsimp only at heff2 hs2_dst hs2_src hs2_n hs2_i hcop2 hs2_i'
          have hiv2_n : iv2.toNat = n0.toNat := by
            have hiv2_eq : iv2' = iv2 := by
              rw [hs2_i] at hs2_i'; injection hs2_i' with h1; injection h1 with h2; injection h2 with h3; exact h3.symm
            subst iv2'
            omega
          have hiv2_bv : iv2 = n0 := BitVec.eq_of_toNat_eq hiv2_n
          have hs2_i_n0 : s2.locals.lookup (ofString "i") = some (.val (.word n0)) := hiv2_bv ▸ hs2_i
          have hcop2_n0 : ∀ k, 8 * k < n0.toNat → memW s2 (dst0.toNat + 8 * k) = memW entry (src0.toNat + 8 * k) := by
            intro k hk; exact hcop2 k (by omega)
          have hlp3_exit : evaluateHOLFiniteState s2 lp3 = (none, s2) := by
            dsimp only [lp3]
            rw [evaluateHOLFiniteState_while_fixClockRewrite, evalHOLFinite_eq_toExact]
            have hz8 : BitVec.ofNat 64 8 + (0 : BitVec 64) = BitVec.ofNat 64 8 := BitVec.add_zero _
            have hadd8 : (n0 + (BitVec.ofNat 64 8 + (0 : BitVec 64))).toNat = n0.toNat + 8 := by
              rw [hz8, BitVec.toNat_add, show (BitVec.ofNat 64 8).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
            have hlt8 : n0.toNat < (n0 + (BitVec.ofNat 64 8 + (0 : BitVec 64))).toNat := by omega
            have hc3 : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
                (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)])) =
                some (.val (.word 0)) := by
              simp only [evalHOLExact, evalListHOLExact, hs2_n, hs2_i_n0, wordOpHOL, wordOp, valueIsWord, valueWord,
                List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
                Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, Bool.not_eq_true', decide_eq_false_iff_not]
              change some (ValueHOL.val (HolWordLab.word
                (if ¬n0.toNat < (n0 + (BitVec.ofNat 64 8 + (0 : BitVec 64))).toNat then 1 else 0))) = _
              rw [if_neg (not_not.mpr hlt8)]
            rw [hc3]; dsimp only
            have h00 : ¬ ((0 : BitVec 64) ≠ 0) := by decide
            rw [if_neg h00]
          have hlp4_exit : evaluateHOLFiniteState s2 lp4 = (none, s2) := by
            dsimp only [lp4]
            rw [evaluateHOLFiniteState_while_fixClockRewrite, evalHOLFinite_eq_toExact]
            have hc4 : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
                (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
                some (.val (.word 0)) := by
              simp [evalHOLExact, hs2_n, hs2_i_n0, Compiler.Encoders.Asm.wordCmpHOL]
            rw [hc4]; dsimp only
            have h00 : ¬ ((0 : BitVec 64) ≠ 0) := by decide
            rw [if_neg h00]
          rw [evaluateHOLFiniteState_seq_line780, hlp3_exit]; dsimp only
          rw [evaluateHOLFiniteState_seq_line780, hlp4_exit]; dsimp only
          rw [evaluateHOLFiniteState_return]
          have hev_r0 : @evalHOLExact 64 F _ s2.toExact
              (fun a => Classical.propDecidable (s2.memaddrs a)) (.const (BitVec.ofNat 64 0)) =
              some (.val (.word 0)) := rfl
          have hsz : sizeOfShapeWithContextHOL s2.structs (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) ≤ 32 := by
            simp [shapeOfHOLExact]
          rw [hev_r0]; dsimp only; rw [if_pos hsz]; dsimp only
          refine ⟨fun rv hrv => ?_, fun _ _ h => by simp at h⟩
          injection hrv with hrv'; injection hrv' with hrv''
          exact ⟨hrv''.symm, heff2.with_locals_clock _ s2.clock, hcop2_n0⟩
    rcases hb : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_memcpy) with ⟨br, bs⟩
    change evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_memcpy) = (br, bs) at hb
    have hnt_b : br ≠ some .timeOut := by
      rintro rfl
      change evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_memcpy) = (some .timeOut, bs) at hb
      rw [hb] at hnt; exact hnt rfl
    obtain ⟨hret_b, hexn_b⟩ := hbody_words
    rw [hb] at hret_b hexn_b
    dsimp only at hret_b hexn_b
    cases br with
    | none =>
      exact ⟨fun h => by simp at h, fun _ ⟨_, h⟩ => by cases h⟩
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt_b
      | exception eid ev => exact absurd rfl (hexn_b eid ev)
      | returned rv =>
        obtain ⟨rfl, heff_b, hcop_b⟩ := hret_b rv rfl
        dsimp only
        have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) .one = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        rw [if_pos hsh]
        have heff_s_ent : ByteRegionEffect s entry [(dst0.toNat, n0.toNat)] :=
          (ByteRegionEffect.refl s [(dst0.toNat, n0.toNat)]).with_locals_clock entry.locals entry.clock
        exact ⟨fun _ => ⟨(heff_s_ent.trans heff_b).with_locals_clock s.locals bs.clock, rfl, hcop_b⟩,
          fun h => False.elim (h rfl)⟩
      | error | «break» | «continue» | finalFfi _ =>
        exact ⟨fun h => by simp at h, fun _ ⟨_, h⟩ => by cases h⟩

private theorem frameMemByteEff_heap_frame_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (heff : FrameMemByteEff s post Rl)
    (hregions : ∀ i ∈ Rl, i = (0, 0) ∨ heapLimit ≤ i.1) :
    globN post "heap_ptr" = globN s "heap_ptr" ∧
    (∀ a : BitVec 64, a.toNat % 8 = 0 → a.toNat < heapLimit →
      post.memory a = s.memory a) ∧
    (∀ b : Nat, b < heapLimit → memB post b = memB s b) := by
  refine ⟨R16Shards.OpHandlers.globN_eq_of_lookup_eq (heff.glob_other "heap_ptr" (by decide)), ?_, ?_⟩
  · intro a ha8 ha
    apply heff.cell_frame a
    intro i hi
    rcases hregions i hi with rfl | hlo
    · simp [CellHits]
    · have hlim8 : heapLimit % 8 = 0 := by decide
      have hcell : a.toNat + 8 ≤ heapLimit := by omega
      unfold CellHits
      omega
  · intro b hb
    apply heff.byte_frame b (by
      have hlim : heapLimit < 2 ^ 64 := by decide
      omega)
    intro i hi
    rcases hregions i hi with rfl | hlo
    · simp [InIvl]
    · unfold InIvl
      omega

private theorem evmInvWith_of_head_mem_extend_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {freshIvl : Ivl}
    (hInvW : EvmInvWith s S Nd)
    (hApost : ArenaReady post)
    (hfm_le : globN s "frame_mem_ptr" ≤ globN post "frame_mem_ptr")
    (heff : FrameMemByteEff s post
      [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))])
    (hfresh : freshIvl = (0, 0) ∨
      (freshIvl.1 % 8 = 0 ∧ freshIvl.2 % 8 = 0 ∧
        Inside freshIvl (globN s "frame_mem_ptr") (globN post "frame_mem_ptr")))
    (he0_other : ∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 32 → off ≠ 40 →
      memW post (globN s "ev" + off) = memW s (globN s "ev" + off))
    (hnew_mem :
      (freshIvl.2 = 0 ∧ memW post (globN s "ev" + 40) = memW s (globN s "ev" + 40)) ∨
      (freshIvl.2 ≠ 0 ∧
        memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = freshIvl.1 ∧
        memW post (globN s "ev" + 40) = memW s (globN s "ev" + 40) + freshIvl.2))
    (hlen_le_cap : memW post (globN s "ev" + 32) ≤ memW post (globN s "ev" + 40)) :
    EvmInvWith post S Nd ∧
    worldTypedIvls post S Nd = worldTypedIvls s S Nd ∧
    evmChain post = evmChain s ∧
    evmR post = evmR s ∧
    (∀ ec ∈ evmChain s, ∀ o ∈ frameObjects post ec,
      o ∈ frameObjects s ec ∨
      (ec = (globN s "ev", globN s "cur_cont") ∧
        o = (memW post (globN s "ev" + 24), memW post (globN s "ev" + 40)))) := by
  have hInv_p_full := evmInv_of_head_mem_extend (evmInvWith_to_evmInv hInvW) hApost hfm_le
    heff hfresh he0_other hnew_mem hlen_le_cap
  obtain ⟨hAs, ⟨hW, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW, hFO_pw, hFO_disj, _, hMarks, hRoles, hGas⟩, hTr_at, hAT_at⟩ := hInvW
  have hWT : WorldTypedWith s S Nd := ⟨hW.1, hW.2.1, hW.2.2.1, hTr_at⟩
  set e0 := globN s "ev"
  set c0 := globN s "cur_cont"
  set oldMem : Ivl := (memW s (e0 + 24), memW s (e0 + 40))
  have hch_cons : ∃ tl, evmChain s = (e0, c0) :: tl := ⟨_, rfl⟩
  obtain ⟨chTail, hch_eq⟩ := hch_cons
  have hhead_mem : (e0, c0) ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_self
  have hhead_FW := hFW_all _ hhead_mem
  obtain ⟨hb1, _, _, _⟩ := frameWF_bounds hAs.2 hhead_FW
  dsimp only at hb1
  have he0_8 : e0 % 8 = 0 := (hhead_FW.1 (e0, 280) (by simp)).2.1
  have holdMem_8 : oldMem.1 % 8 = 0 := hhead_FW.2.2.1.1
  have holdMem_sz8 : oldMem.2 % 8 = 0 := hhead_FW.2.2.1.2.1
  have hRl_list : ∀ x ∈ ([freshIvl, (e0, 280), oldMem] : List Ivl), x.1 % 8 = 0 := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rcases hfresh with rfl | ⟨h8, _⟩
      · rfl
      · exact h8
    · exact he0_8
    · exact holdMem_8
  have hdom_eq : post.memaddrs = s.memaddrs := heff.memaddrs
  have hglob_eq : ∀ g, ofString g ≠ ofString "frame_mem_ptr" → globN post g = globN s g :=
    fun g hg => R16Shards.OpHandlers.globN_eq_of_lookup_eq (heff.glob_other g hg)
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hglob_eq "heap_ptr" (by decide)]
  have hsc_le : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hglob_eq "scratch_ptr" (by decide)]
  have hfo_disj_wti : ∀ o ∈ frameObjects s (e0, c0), ∀ i ∈ worldTypedIvls s S Nd, i.2 = 0 ∨ Disj o i := by
    intro o ho i hi
    unfold worldTypedIvls at hi; simp only [List.mem_append] at hi
    rcases hi with ((((h1 | h2) | h3) | h4) | h5) | h6
    · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
      exact Or.inr ((hFO_disj _ hhead_mem o ho).1 t ht i hfp)
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
      exact Or.inr ((hFO_disj _ hhead_mem o ho).2 _ (typedRec_in_fixedObjects s hr))
    · simp only [List.mem_singleton] at h3; subst h3
      have hfix_j : (if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap") ∈ fixedObjects s := by
        unfold fixedObjects; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))
      exact Or.inr ((hFO_disj _ hhead_mem o ho).2 _ hfix_j)
    · exact Or.inr ((hFO_disj _ hhead_mem o ho).2 _ (blockOut_in_fixedObjects h4))
    · exact Or.inr ((hFO_disj _ hhead_mem o ho).2 _ (bal_in_fixedObjects h5))
    · exact Or.inr (hAT_at o (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨_, hhead_mem, rfl⟩, ho⟩) i h6)
  have hfresh_disj_alloc : ∀ i : Ivl, Allocated s i → Disj freshIvl i := by
    intro i hal
    rcases hfresh with rfl | ⟨_, _, hfin⟩
    · exact Or.inl rfl
    · obtain ⟨hfin1, hfin2⟩ := hfin
      have h1 := hAs.2.2.1; have h2 := hAs.2.2.2.1
      have h3 := hApost.2.2.2.2.1
      rw [hglob_eq "scratch_ptr" (by decide)] at h3
      rw [R11Shards.heapLimit_val] at h1; rw [R11Shards.scratchStart_val] at h2
      rcases hal with hheap | hscr
      · obtain ⟨_, hhi2⟩ := hheap
        exact Or.inr (Or.inr (Or.inr (by omega)))
      · obtain ⟨hlo1, _⟩ := hscr
        exact Or.inr (Or.inr (Or.inl (by omega)))
  have hwrite_disj_wti : ∀ x ∈ ([freshIvl, (e0, 280), oldMem] : List Ivl),
      ∀ i ∈ worldTypedIvls s S Nd, i.2 = 0 ∨ Disj x i := by
    intro x hx i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rcases worldTypedIvls_allocated hWT hi with hi0 | hal
      · exact Or.inl hi0
      · exact Or.inr (hfresh_disj_alloc i hal)
    · exact hfo_disj_wti (e0, 280) (by simp [frameObjects]) i hi
    · exact hfo_disj_wti oldMem (by simp [frameObjects, oldMem]) i hi
  have hcellG : SameTypedCells s { post with globals := s.globals } S Nd :=
    ByteRegionEffect.sameTypedCells (Rl := []) (extra := [freshIvl, (e0, 280), oldMem])
      hAs.1.memaddrs hWT (fun _ h => by simp at h) hwrite_disj_wti (by simpa using heff.to_bre_dummy)
  have hcell : SameTypedCells s post S Nd := hcellG
  have hwti_eq : worldTypedIvls post S Nd = worldTypedIvls s S Nd :=
    worldTypedIvls_eq_of_cell_g09 hAs.2 hWT hcell (fun g _ _ hg => hglob_eq g hg)
  have hfeq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [blockOutObjects_eq hAs.2 hWT.2.2.1 hcell (hglob_eq "bo" (by decide)),
        balObjects_eq hAs.2 hWT.1 hWT.2.2.1 hcell (hglob_eq "bal_accounts" (by decide)),
        hglob_eq "journal" (by decide),
        hglob_eq "journal_cap" (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne : ofString gn.1 ≠ ofString "frame_mem_ptr" := by clear * - hgn; revert gn hgn; decide
    rw [hglob_eq gn.1 hne]
  have hFT_post := fixedTyped_of_eq hApost hWT.2.2.1 hh hsc_le hfeq
  have hcg : ∀ g ∈ coreWorldGlobals, globN post g = globN s g := by
    intro g hg
    have hne : ofString g ≠ ofString "frame_mem_ptr" := by clear * - hg; revert g hg; decide
    exact hglob_eq g hne
  obtain ⟨hWT_post, _⟩ := worldTypedWith_congr_w1 hAs hApost hh hsc_le hcg hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hW_post : WorldTyped post S :=
    ⟨hWT_post.1, hWT_post.2.1, hWT_post.2.2.1, Nd, hWT_post.2.2.2⟩
  have hmemW_disj : ∀ {base sz k : Nat}, base + sz ≤ 2 ^ 64 → base % 8 = 0 → k % 8 = 0 → k + 8 ≤ sz →
      (∀ x ∈ ([freshIvl, (e0, 280), oldMem] : List Ivl), Disj x (base, sz)) →
      memW post (base + k) = memW s (base + k) := by
    intro base sz k hbnd hb8 hk8 hk hdj
    unfold memW
    have ha : base + k < 2 ^ 64 := by omega
    have hbk8 : (base + k) % 8 = 0 := by omega
    have hbit : (BitVec.ofNat 64 (base + k)).toNat = base + k := Nat.mod_eq_of_lt ha
    rw [heff.cell_frame (BitVec.ofNat 64 (base + k))]
    intro x hx; rw [hbit]
    exact not_cellHits_of_disj_aligned (i := (base, sz)) hbk8 (hRl_list x hx)
      (Nat.le_add_right base k) (Nat.add_le_add_left hk base) (R11Shards.Disj.symm (hdj x hx))
  have hpw_head_tail :
      (frameObjects s (e0, c0)).Pairwise Disj ∧
      (∀ o1 ∈ frameObjects s (e0, c0),
        ∀ ec ∈ chTail, ∀ o2 ∈ frameObjects s ec, Disj o1 o2) := by
    have hpw := hFO_pw
    rw [hch_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
    refine ⟨hpw.1, fun o1 ho1 ec hec o2 ho2 => hpw.2.2 o1 ho1 o2 ?_⟩
    exact List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ec, hec, rfl⟩, ho2⟩
  have hfresh_disj_fo : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, Disj freshIvl o := by
    intro ec hec o ho
    rcases hfresh with rfl | ⟨_, _, hfin⟩
    · exact Or.inl rfl
    · obtain ⟨hfin1, hfin2⟩ := hfin
      have hFW := hFW_all ec hec
      have h1 := hAs.2.2.1; have h2 := hAs.2.2.2.1
      have h3 := hApost.2.2.2.2.1
      rw [hglob_eq "scratch_ptr" (by decide)] at h3
      rw [R11Shards.heapLimit_val] at h1; rw [R11Shards.scratchStart_val] at h2
      unfold frameObjects at ho
      rcases List.mem_append.1 ho with ho7 | holog
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho7
        rcases ho7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨hin1, _⟩ := (hFW.1 (ec.1, 280) (by simp)).1
          exact Or.inr (Or.inr (Or.inl (by dsimp only at hin1 ⊢; omega)))
        · obtain ⟨hin1, _⟩ := (hFW.1 (ec.2, 104) (by simp)).1
          exact Or.inr (Or.inr (Or.inl (by dsimp only at hin1 ⊢; omega)))
        · obtain ⟨hin1, _⟩ := (hFW.1 (memW s (ec.1 + 8), 32 * memW s (ec.1 + 232)) (by simp)).1
          exact Or.inr (Or.inr (Or.inl (by dsimp only at hin1 ⊢; omega)))
        · obtain ⟨_, hin2⟩ := hFW.2.1
          exact Or.inr (Or.inr (Or.inr (by dsimp only at hin2 ⊢; omega)))
        · obtain ⟨hin1, _⟩ := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1
          exact Or.inr (Or.inr (Or.inl (by dsimp only at hin1 ⊢; omega)))
        · rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.1 with ⟨_, hin2⟩ | ⟨hin1, _⟩
          · exact Or.inr (Or.inr (Or.inr (by omega)))
          · exact Or.inr (Or.inr (Or.inl (by omega)))
        · rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with ⟨hz, _⟩ | ⟨⟨_, hin2⟩, _⟩
          · unfold frameRet; simp [hz]; exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inr (by omega)))
      · unfold frameLogObjects at holog; dsimp only at holog
        obtain ⟨idx, hidx_mem, ho_own⟩ := List.mem_flatMap.1 holog
        rw [List.mem_range] at hidx_mem
        rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
        · obtain ⟨hin1, _⟩ := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1
          dsimp only at hin1; omega
        · have hle := (hent idx hidx_mem).2
          have ho_rec := (List.mem_filter.1 ho_own).1
          simp only [logRecordIvls, List.mem_cons, List.not_mem_nil, or_false] at ho_rec
          rcases ho_rec with rfl | rfl | rfl | rfl
          · obtain ⟨_, hin2⟩ := hle.2.1; exact Or.inr (Or.inr (Or.inr (by dsimp only at hin2 ⊢; omega)))
          · obtain ⟨_, hin2⟩ := hle.2.2.2.2.1; exact Or.inr (Or.inr (Or.inr (by dsimp only at hin2 ⊢; omega)))
          · obtain ⟨_, hin2⟩ := hle.2.2.2.2.2.1; exact Or.inr (Or.inr (Or.inr (by dsimp only at hin2 ⊢; omega)))
          · obtain ⟨_, hin2⟩ := hle.2.2.2.2.2.2; exact Or.inr (Or.inr (Or.inr (by dsimp only at hin2 ⊢; omega)))
  have hdisj_old_fresh : ∀ o : Ivl, Disj oldMem o → Disj freshIvl o →
      Disj (memW post (e0 + 24), memW post (e0 + 40)) o := by
    intro o hd_old hd_fr
    have he24_eq := he0_other 24 (by omega) (by omega) (by omega) (by omega)
    rw [he24_eq]
    rcases hnew_mem with ⟨_, h40_eq⟩ | ⟨hnz, hcontig, h40_eq⟩
    · rw [h40_eq]; exact hd_old
    · rw [h40_eq]
      rcases hd_fr with hz | hz | hlt | hgt
      · exact absurd hz hnz
      · exact Or.inr (Or.inl hz)
      · exact Or.inr (Or.inr (Or.inl (by dsimp only [oldMem] at hcontig hlt ⊢; omega)))
      · rcases hd_old with hoz | hoz | holt | hogt
        · dsimp only [oldMem] at hoz
          rw [hoz] at hcontig ⊢
          simp only [Nat.add_zero, Nat.zero_add] at hcontig ⊢
          rw [hcontig]
          exact Or.inr (Or.inr (Or.inr hgt))
        · exact Or.inr (Or.inl hoz)
        · by_cases hoz0 : o.2 = 0
          · exact Or.inr (Or.inl hoz0)
          · have hle_f : freshIvl.1 ≤ o.1 := by rw [← hcontig]; exact holt
            exact False.elim (by omega)
        · exact Or.inr (Or.inr (Or.inr hogt))
  have hhead_pw := hpw_head_tail.1
  unfold frameObjects at hhead_pw
  have hp0 := List.pairwise_cons.1 hhead_pw
  have hp1 := List.pairwise_cons.1 hp0.2
  have hp2 := List.pairwise_cons.1 hp1.2
  have hp3 := List.pairwise_cons.1 hp2.2
  have hdisj_write_nonmem : ∀ ec ∈ evmChain s,
      (∀ x ∈ ([freshIvl, (e0, 280), oldMem] : List Ivl), Disj x (ec.2, 104)) ∧
      (∀ x ∈ ([freshIvl, (e0, 280), oldMem] : List Ivl), Disj x (memW s (ec.1 + 88), 24)) ∧
      (∀ x ∈ ([freshIvl, (e0, 280), oldMem] : List Ivl), Disj x (frameLogs s ec)) ∧
      (∀ i < memW s (memW s (ec.1 + 88) + 8),
        ∀ x ∈ ([freshIvl, (e0, 280), oldMem] : List Ivl),
          Disj x (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40)) := by
    intro ec hec
    have hlog_in : ∀ i < memW s (memW s (ec.1 + 88) + 8),
        (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40) ∈ frameLogObjects s ec := by
      intro i hi; unfold frameLogObjects; dsimp only
      exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
        by unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with rfl | htail
    · have hmem_head : (e0, c0) ∈ evmChain s := hhead_mem
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact hfresh_disj_fo _ hmem_head _ (by simp [frameObjects])
        · exact hp0.1 _ (by simp)
        · exact R11Shards.Disj.symm (hp1.1 _ (by simp [oldMem]))
      · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact hfresh_disj_fo _ hmem_head _ (by simp [frameObjects])
        · exact hp0.1 _ (by simp)
        · exact hp3.1 _ (by simp)
      · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact hfresh_disj_fo _ hmem_head _ (by simp [frameObjects])
        · exact hp0.1 _ (by simp)
        · exact hp3.1 _ (by simp)
      · intro i hi x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        have hli := hlog_in i hi
        rcases hx with rfl | rfl | rfl
        · exact hfresh_disj_fo _ hmem_head _ (by unfold frameObjects; exact List.mem_append_right _ hli)
        · exact hp0.1 _ (by simp [hli])
        · exact hp3.1 _ (by simp [hli])
    · have hmem_ec : ec ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_of_mem _ htail
      have hall : ∀ o2 ∈ frameObjects s ec, ∀ x ∈ ([freshIvl, (e0, 280), oldMem] : List Ivl), Disj x o2 := by
        intro o2 ho2 x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact hfresh_disj_fo ec hmem_ec o2 ho2
        · exact hpw_head_tail.2 _ (by simp [frameObjects]) ec htail o2 ho2
        · exact hpw_head_tail.2 _ (by simp [frameObjects, oldMem]) ec htail o2 ho2
      exact ⟨hall _ (by simp [frameObjects]),
             hall _ (by simp [frameObjects]),
             hall _ (by simp [frameObjects]),
             fun i hi => hall _ (by unfold frameObjects; exact List.mem_append_right _ (hlog_in i hi))⟩
  have htail_rec_eq : ∀ ec ∈ chTail, ∀ k, k + 8 ≤ 280 → k % 8 = 0 → memW post (ec.1 + k) = memW s (ec.1 + k) := by
    intro ec htail k hk hk8
    have hec : ec ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_of_mem _ htail
    have hFW := hFW_all ec hec
    obtain ⟨hb_e, _, _, _⟩ := frameWF_bounds hAs.2 hFW
    have he8 : ec.1 % 8 = 0 := (hFW.1 (ec.1, 280) (by simp)).2.1
    apply hmemW_disj hb_e he8 hk8 hk
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hfresh_disj_fo ec hec (ec.1, 280) (by simp [frameObjects])
    · exact hpw_head_tail.2 _ (by simp [frameObjects]) ec htail _ (by simp [frameObjects])
    · exact hpw_head_tail.2 _ (by simp [frameObjects, oldMem]) ec htail _ (by simp [frameObjects])
  have hrec_eq : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → k % 8 = 0 → k ≠ 32 → k ≠ 40 → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → k % 8 = 0 → memW post (ec.2 + k) = memW s (ec.2 + k)) ∧
      (∀ k, k + 8 ≤ 24 → k % 8 = 0 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨_, hb_c, hb_88, _⟩ := frameWF_bounds hAs.2 hFW
    have hc8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
    have h88_8 : (memW s (ec.1 + 88)) % 8 = 0 := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).2.1
    obtain ⟨hd_c, hd_88, _, _⟩ := hdisj_write_nonmem ec hec
    refine ⟨?_,
      fun k hk hk8 => hmemW_disj hb_c hc8 hk8 hk hd_c,
      fun k hk hk8 => hmemW_disj hb_88 h88_8 hk8 hk hd_88⟩
    intro k hk hk8 hk_32 hk_40
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with rfl | htail
    · exact he0_other k hk hk8 hk_32 hk_40
    · exact htail_rec_eq ec htail k hk hk8
  have hchain_aux : ∀ (fuel e c : Nat),
      (∀ ec ∈ evmChainFrom s fuel e c, ec ∈ evmChain s) →
      evmChainFrom post fuel e c = evmChainFrom s fuel e c := by
    intro fuel; induction fuel with
    | zero => intros; rfl
    | succ fuel ih =>
      intro e c hsub
      have hec : (e, c) ∈ evmChain s := hsub (e, c) (by simp [evmChainFrom])
      obtain ⟨_, hc_eq, _⟩ := hrec_eq (e, c) hec
      have hc16 := hc_eq 16 (by omega) (by omega)
      have hc0 : memW post c = memW s c := by simpa using hc_eq 0 (by omega) (by omega)
      have hc8 := hc_eq 8 (by omega) (by omega)
      simp only [evmChainFrom, hc16, hc0, hc8]
      split
      · rfl
      · rename_i hne16
        rw [ih]; intro ec' hec'; exact hsub ec' (by simp [evmChainFrom, hne16, hec'])
  have hchain_eq : evmChain post = evmChain s := by
    unfold evmChain
    rw [hglob_eq "ev" (by decide), hglob_eq "cur_cont" (by decide)]
    exact hchain_aux _ _ _ (fun _ h => h)
  have hframeLogs_eq : ∀ ec ∈ evmChain s, frameLogs post ec = frameLogs s ec := by
    intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    unfold frameLogs
    rw [he_eq 88 (by omega) (by omega) (by omega) (by omega),
        show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by simpa using h88_eq 0 (by omega) (by omega),
        h88_eq 16 (by omega) (by omega)]
  have hframeRet_eq : ∀ ec ∈ evmChain s, frameRet post ec = frameRet s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameRet
    rw [he_eq 216 (by omega) (by omega) (by omega) (by omega),
        he_eq 144 (by omega) (by omega) (by omega) (by omega)]
  have hlogs_congr : ∀ ec ∈ evmChain s,
      frameLogObjects post ec = frameLogObjects s ec ∧ LogsListOK post (memW post (ec.1 + 88)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨_, _, _, hfob⟩ := frameWF_bounds hAs.2 hFW
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    obtain ⟨_, _, hd_fl, hd_lr⟩ := hdisj_write_nonmem ec hec
    have hl0 : memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) := by
      simpa using h88_eq 0 (by omega) (by omega)
    have hl8 := h88_eq 8 (by omega) (by omega)
    have hl16 := h88_eq 16 (by omega) (by omega)
    have harr_eq : ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
        memW post ((memW s (memW s (ec.1 + 88))) + 8 * i) = memW s ((memW s (memW s (ec.1 + 88))) + 8 * i) := by
      intro i hi
      have hfl_in : frameLogs s ec ∈ frameObjects s ec := by simp [frameObjects]
      have hlen_le : memW s (memW s (ec.1 + 88) + 8) ≤ memW s (memW s (ec.1 + 88) + 16) :=
        hFW.2.2.2.2.2.2.2.2.2.2.2.1
      have hfl_b : (frameLogs s ec).1 + (frameLogs s ec).2 ≤ 2 ^ 64 := by
        rcases hfob _ hfl_in with h0 | hb
        · unfold frameLogs at h0; dsimp only at h0; omega
        · exact hb
      have hfl_8 : (memW s (memW s (ec.1 + 88))) % 8 = 0 := hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
      exact hmemW_disj hfl_b hfl_8 (by omega) (by unfold frameLogs; dsimp only; omega) hd_fl
    have hlr_eq : ∀ i (_hi : i < memW s (memW s (ec.1 + 88) + 8)) off, off + 8 ≤ 40 → off % 8 = 0 →
        memW post ((memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) + off) =
          memW s ((memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) + off) := by
      intro i hi off hoff hoff8
      have hlr_in : (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40) ∈ frameObjects s ec := by
        unfold frameObjects; apply List.mem_append_right
        unfold frameLogObjects; dsimp only
        exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
          by unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
      have hlr_b : memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + 40 ≤ 2 ^ 64 := by
        rcases hfob _ hlr_in with h0 | hb
        · dsimp only at h0; omega
        · exact hb
      have hlr_8 : (memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) % 8 = 0 := by
        rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
        · obtain ⟨he88_in, _⟩ := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1
          have h1 := hAs.2.2.2.1; have h2 := hAs.2.2.2.2.1
          rw [R11Shards.scratchStart_val] at h1; dsimp only at he88_in; omega
        · exact (hent i hi).2.1.1
      exact hmemW_disj hlr_b hlr_8 hoff8 hoff (hd_lr i hi)
    refine ⟨?_, ?_⟩
    · unfold frameLogObjects; dsimp only
      rw [he_eq 88 (by omega) (by omega) (by omega) (by omega), hl8]
      apply List.flatMap_congr; intro i hi; rw [List.mem_range] at hi
      rw [hl0, harr_eq i hi]
      have r0 := hlr_eq i hi 0 (by omega) (by omega)
      have r8 := hlr_eq i hi 8 (by omega) (by omega)
      have r16 := hlr_eq i hi 16 (by omega) (by omega)
      have r24 := hlr_eq i hi 24 (by omega) (by omega)
      have r32 := hlr_eq i hi 32 (by omega) (by omega)
      simp only [Nat.add_zero] at r0
      unfold logOwnedIvls logRecordIvls
      rw [r0, r8, r16, r24, r32, hglob_eq "vm_system_address" (by decide)]
    · rw [he_eq 88 (by omega) (by omega) (by omega) (by omega)]
      rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨hw_l, hal_l, hlt28, hle_cap, hent⟩
      · exact Or.inl hz
      · right
        refine ⟨(wordsOK_congr_dom hdom_eq).2 hw_l, allocated_mono_scr hh hsc_le hal_l,
          by rw [hl8]; exact hlt28, by rw [hl8, hl16]; exact hle_cap, fun i hi => ?_⟩
        rw [hl8] at hi; rw [hl0]
        obtain ⟨hwa, hle⟩ := hent i hi
        refine ⟨(wordAt_congr_dom hdom_eq).2 hwa, ?_⟩
        rw [harr_eq i hi]
        have r0 := hlr_eq i hi 0 (by omega) (by omega)
        have r8 := hlr_eq i hi 8 (by omega) (by omega)
        have r16 := hlr_eq i hi 16 (by omega) (by omega)
        have r24 := hlr_eq i hi 24 (by omega) (by omega)
        have r32 := hlr_eq i hi 32 (by omega) (by omega)
        simp only [Nat.add_zero] at r0
        unfold LogEntryOK at hle ⊢
        rw [r0, r8, r16, r24, r32, hglob_eq "heap_ptr" (by decide)]
        exact ⟨(wordsOK_congr_dom hdom_eq).2 hle.1, hle.2⟩
  have htail_fo_eq : ∀ ec ∈ chTail, frameObjects post ec = frameObjects s ec := by
    intro ec htail
    have hec : ec ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_of_mem _ htail
    unfold frameObjects
    rw [htail_rec_eq ec htail 8 (by omega) (by omega),
        htail_rec_eq ec htail 232 (by omega) (by omega),
        htail_rec_eq ec htail 24 (by omega) (by omega),
        htail_rec_eq ec htail 40 (by omega) (by omega),
        htail_rec_eq ec htail 88 (by omega) (by omega),
        hframeLogs_eq ec hec, hframeRet_eq ec hec, (hlogs_congr ec hec).1]
  have hfs_eq : ∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameScratch
    rw [he_eq 8 (by omega) (by omega) (by omega) (by omega),
        he_eq 232 (by omega) (by omega) (by omega) (by omega),
        he_eq 88 (by omega) (by omega) (by omega) (by omega)]
  have hfo_post_cases : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects post ec,
      o ∈ frameObjects s ec ∨ (ec = (e0, c0) ∧ o = (memW post (e0 + 24), memW post (e0 + 40))) := by
    intro ec hec o ho
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with rfl | htail
    · unfold frameObjects at ho
      rw [he0_other 8 (by omega) (by omega) (by omega) (by omega),
          he0_other 232 (by omega) (by omega) (by omega) (by omega),
          he0_other 88 (by omega) (by omega) (by omega) (by omega),
          hframeLogs_eq _ hhead_mem, hframeRet_eq _ hhead_mem, (hlogs_congr _ hhead_mem).1] at ho
      rcases List.mem_append.1 ho with ho7 | holog
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho7
        rcases ho7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact Or.inl (by simp [frameObjects])
        · exact Or.inl (by simp [frameObjects])
        · exact Or.inl (by simp [frameObjects])
        · exact Or.inr ⟨rfl, rfl⟩
        · exact Or.inl (by simp [frameObjects])
        · exact Or.inl (by simp [frameObjects])
        · exact Or.inl (by simp [frameObjects])
      · exact Or.inl (by unfold frameObjects; exact List.mem_append_right _ holog)
    · left; rwa [htail_fo_eq ec htail] at ho
  have hframeRoleSlots_eq : frameRoleSlots post (evmChain s) = frameRoleSlots s (evmChain s) := by
    unfold frameRoleSlots; apply List.flatMap_congr; intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    rw [he_eq 136 (by omega) (by omega) (by omega) (by omega),
        he_eq 168 (by omega) (by omega) (by omega) (by omega),
        he_eq 176 (by omega) (by omega) (by omega) (by omega)]
  have hfp_eq_all : ∀ t ∈ S, htabFootprint post t = htabFootprint s t :=
    fun t ht => htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1
  have hR_eq : evmR post = evmR s :=
    evmR_eq_of_chain_and_words hchain_eq (fun ec hec =>
      ⟨(hrec_eq ec hec).1 64 (by omega) (by omega) (by omega) (by omega),
       (hrec_eq ec hec).1 192 (by omega) (by omega) (by omega) (by omega)⟩)
  have hAT_post : ∀ o ∈ ((evmChain post).map (frameObjects post)).flatten,
      ∀ j ∈ nodeExtents post Nd, Disj o j := by
    intro o ho j hj
    rw [hchain_eq] at ho
    rw [nodeExtents_eq hTr_at.1 hcell] at hj
    obtain ⟨fo, hfo_map, ho_in⟩ := List.mem_flatten.1 ho
    obtain ⟨ec, hec, rfl⟩ := List.mem_map.1 hfo_map
    rcases hfo_post_cases ec hec o ho_in with ho_old | ⟨_, rfl⟩
    · exact hAT_at o (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ec, hec, rfl⟩, ho_old⟩) j hj
    · rcases worldTypedIvls_allocated hWT (mem_worldTypedIvls_nodeExtents hj) with hj0 | hal_j
      · exact Or.inr (Or.inl hj0)
      · exact hdisj_old_fresh j
          (hAT_at oldMem (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨_, hhead_mem, rfl⟩, by simp [frameObjects, oldMem]⟩) j hj)
          (hfresh_disj_alloc j hal_j)
  have hInvAt_post : EvmInvAt post S := by
    refine ⟨hW_post, ?_⟩
    dsimp only; rw [hchain_eq]
    refine ⟨hch_ne, hch_len, ?_, ?_, ?_, ?_, ?_, ?_, ⟨Nd, hWT_post.2.2.2, ?_⟩, ?_, ?_, ?_⟩
    · obtain ⟨ec, hec, hk0⟩ := hch_last
      have hec_mem := List.mem_of_mem_getLast? hec
      exact ⟨ec, hec, by rw [(hrec_eq ec hec_mem).2.1 16 (by omega) (by omega)]; exact hk0⟩
    · intro ec hec
      obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
      obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, _, c17⟩ := hFW_all ec hec
      have hlo_ok := (hlogs_congr ec hec).2
      have hmsg_ok : MsgOwned post S (memW post (ec.1 + 112)) := by
        rw [he_eq 112 (by omega) (by omega) (by omega) (by omega)]
        obtain ⟨hal_m, hw_m, hdt, hdf, hdfo, Nd_m, hTr_m, hdj_m⟩ := c17
        obtain ⟨hTr_int, hsub_int⟩ := R11Shards.triesTypedWith_inter hTr_at hTr_m
        set Ndi := Nd.filter (fun n => decide (n ∈ Nd_m))
        have hcell_i : SameTypedCells s post S Ndi := by
          have hwti_sub : ∀ i ∈ worldTypedIvls s S Ndi, i ∈ worldTypedIvls s S Nd := by
            intro i hi; unfold worldTypedIvls at hi ⊢
            rcases List.mem_append.1 hi with hpre | hne
            · exact List.mem_append_left _ hpre
            · apply List.mem_append_right; unfold nodeExtents at hne ⊢
              obtain ⟨n, hn, hnx⟩ := List.mem_flatMap.1 hne
              exact List.mem_flatMap.2 ⟨n, (List.mem_filter.1 hn).1, hnx⟩
          refine ⟨hcell.1, hcell.2.1, hcell.2.2.1, hcell.2.2.2.1,
            fun a ha ha8 ⟨i, hi, h1, h2⟩ => hcell.2.2.2.2.1 a ha ha8 ⟨i, hwti_sub i hi, h1, h2⟩,
            fun b hb ⟨i, hi, h1, h2⟩ => hcell.2.2.2.2.2 b hb ⟨i, hwti_sub i hi, h1, h2⟩⟩
        obtain ⟨hWT_i_post, _⟩ := worldTypedWith_congr_w1 hAs hApost hh hsc_le hcg hcell_i
          ⟨hWT.1, hWT.2.1, hWT.2.2.1, hTr_int⟩
          ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
        refine ⟨allocated_mono_scr hh hsc_le hal_m, (wordsOK_congr_dom hdom_eq).2 hw_m,
          fun t ht i hi => by rw [hfp_eq_all t ht] at hi; exact hdt t ht i hi,
          by rw [hfeq]; exact hdf,
          ?_,
          Ndi, hWT_i_post.2.2.2, fun o ho j hj => ?_⟩
        · rw [hchain_eq]; intro ec' hec' o ho
          rcases hfo_post_cases ec' hec' o ho with ho_old | ⟨_, rfl⟩
          · exact hdfo ec' hec' o ho_old
          · exact R11Shards.Disj.symm (hdisj_old_fresh (memW s (ec.1 + 112), 176)
              (R11Shards.Disj.symm (hdfo _ hhead_mem oldMem (by simp [frameObjects, oldMem])))
              (hfresh_disj_alloc (memW s (ec.1 + 112), 176) hal_m))
        · rw [nodeExtents_eq hTr_int.1 hcell_i] at hj
          exact hdj_m o ho j (hsub_int j hj).2
      unfold FrameWF; dsimp only
      rw [he_eq 8 (by omega) (by omega) (by omega) (by omega),
          he_eq 16 (by omega) (by omega) (by omega) (by omega),
          he_eq 232 (by omega) (by omega) (by omega) (by omega),
          he_eq 88 (by omega) (by omega) (by omega) (by omega),
          he_eq 24 (by omega) (by omega) (by omega) (by omega),
          he_eq 136 (by omega) (by omega) (by omega) (by omega),
          he_eq 168 (by omega) (by omega) (by omega) (by omega),
          he_eq 176 (by omega) (by omega) (by omega) (by omega),
          h88_eq 16 (by omega) (by omega), h88_eq 8 (by omega) (by omega),
          hframeLogs_eq ec hec,
          he_eq 216 (by omega) (by omega) (by omega) (by omega),
          he_eq 144 (by omega) (by omega) (by omega) (by omega),
          hframeRet_eq ec hec,
          hglob_eq "scratch_ptr" (by decide),
          hglob_eq "heap_ptr" (by decide),
          hglob_eq "evm_empty" (by decide)]
      rw [he_eq 88 (by omega) (by omega) (by omega) (by omega)] at hlo_ok
      have hret_in_post : (memW s (ec.1 + 216) = 0 ∧ memW s (ec.1 + 144) = globN s "evm_empty") ∨
          Inside (frameRet s ec) sourceBase (globN s "heap_ptr") ∧ WordsOK post (frameRet s ec) := by
        rcases c15 with h0 | ⟨hin, hw⟩
        · exact Or.inl h0
        · exact Or.inr ⟨hin, (wordsOK_congr_dom hdom_eq).2 hw⟩
      rw [hch_eq, List.mem_cons] at hec
      rcases hec with rfl | htail
      · have hc2_post : Inside (memW s (e0 + 24), memW post (e0 + 40)) scratchStart (globN post "frame_mem_ptr") ∧
            WordsOK post (memW s (e0 + 24), memW post (e0 + 40)) := by
          rcases hnew_mem with ⟨_, h40_eq⟩ | ⟨hnz, hcontig, h40_eq⟩
          · rw [h40_eq]
            exact ⟨⟨c2.1, le_trans c2.2 hfm_le⟩, (wordsOK_congr_dom hdom_eq).2 c3⟩
          · rcases hfresh with rfl | ⟨_, hfsz8, hfin1, hfin2⟩
            · exact absurd rfl hnz
            · rw [h40_eq]
              have hin_new : Inside (memW s (e0 + 24), memW s (e0 + 40) + freshIvl.2) scratchStart (globN post "frame_mem_ptr") :=
                ⟨c2.1, by dsimp only at hcontig hfin2 ⊢; omega⟩
              have hsb_le_ss : sourceBase ≤ scratchStart := by decide
              have hse_le_he : scratchEnd ≤ heapEnd := by decide
              have hfp_le_se : globN post "frame_mem_ptr" ≤ scratchEnd :=
                le_trans hApost.2.2.2.2.1 hApost.2.2.2.2.2.1
              have hw_new : WordsOK post (memW s (e0 + 24), memW s (e0 + 40) + freshIvl.2) :=
                Wave8Contracts.M26.wordsOK_of_guestInv post hApost.1
                  (memW s (e0 + 24)) (memW s (e0 + 40) + freshIvl.2)
                  holdMem_8 (by dsimp only [oldMem] at holdMem_sz8; omega)
                  (le_trans hsb_le_ss c2.1) (le_trans hin_new.2 (le_trans hfp_le_se hse_le_he))
              exact ⟨hin_new, hw_new⟩
        exact ⟨fun i hi => ⟨(c1 i hi).1, (wordsOK_congr_dom hdom_eq).2 (c1 i hi).2⟩,
          hc2_post.1, hc2_post.2, c4, c5, c6, hlen_le_cap, c8, c9, c10, c11, c12,
          c13, (wordsOK_congr_dom hdom_eq).2 c14, hret_in_post, hlo_ok, hmsg_ok⟩
      · rw [htail_rec_eq ec htail 32 (by omega) (by omega),
            htail_rec_eq ec htail 40 (by omega) (by omega)]
        exact ⟨fun i hi => ⟨(c1 i hi).1, (wordsOK_congr_dom hdom_eq).2 (c1 i hi).2⟩,
          ⟨c2.1, le_trans c2.2 hfm_le⟩, (wordsOK_congr_dom hdom_eq).2 c3, c4, c5, c6, c7, c8, c9, c10, c11, c12,
          c13, (wordsOK_congr_dom hdom_eq).2 c14, hret_in_post, hlo_ok, hmsg_ok⟩
    · intro ec hec
      have htail : ec ∈ chTail := by rw [hch_eq, List.tail_cons] at hec; exact hec
      unfold FrameRoom
      rw [htail_rec_eq ec htail 16 (by omega) (by omega),
          htail_rec_eq ec htail 232 (by omega) (by omega)]
      exact hFR_all ec hec
    · intro i hi
      have hi0 : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
      have hi1_tail : (evmChain s)[i + 1] ∈ chTail := by simp [hch_eq]
      rw [(hrec_eq _ hi0).2.1 80 (by omega) (by omega),
          (hrec_eq _ hi0).2.1 72 (by omega) (by omega),
          htail_rec_eq _ hi1_tail 40 (by omega) (by omega)]
      exact hRW i hi
    · have hpw_post := hInv_p_full.1.2.choose_spec.2.2.2.2.2.2.2.1
      rwa [hchain_eq] at hpw_post
    · intro ec hec o ho
      rw [hfeq]
      rcases hfo_post_cases ec hec o ho with ho_old | ⟨_, rfl⟩
      · exact ⟨fun t ht i hi => by rw [hfp_eq_all t ht] at hi; exact (hFO_disj ec hec o ho_old).1 t ht i hi,
          (hFO_disj ec hec o ho_old).2⟩
      · refine ⟨fun t ht i hi => ?_, fun j hj => ?_⟩
        · rw [hfp_eq_all t ht] at hi
          exact hdisj_old_fresh i
            ((hFO_disj _ hhead_mem oldMem (by simp [frameObjects, oldMem])).1 t ht i hi)
            (hfresh_disj_alloc i ((hWT.1.2.1 t ht).2 i hi).1)
        · rcases hWT.2.2.1.1 j hj with hj0 | ⟨hal_j, _⟩
          · exact Or.inr (Or.inl hj0)
          · exact hdisj_old_fresh j
              ((hFO_disj _ hhead_mem oldMem (by simp [frameObjects, oldMem])).2 j hj)
              (hfresh_disj_alloc j hal_j)
    · rw [← hchain_eq]; exact hAT_post
    · have hworldRefs_eq : worldTableRefs post S = worldTableRefs s S := by
        unfold worldTableRefs recordSlots
        rw [hglob_eq "ws" (by decide), hglob_eq "bs" (by decide), hglob_eq "ts" (by decide),
            show globalTableRoots.map (globN post) = globalTableRoots.map (globN s) by
              simp only [globalTableRoots, List.map,
                hglob_eq "bal_accounts" (by decide),
                hglob_eq "bal_idx_accts" (by decide),
                hglob_eq "bal_idx_stor" (by decide)],
            balRecords_eq hWT.1 hcell (hglob_eq "bal_accounts" (by decide)),
            hglob_eq "journal_n" (by decide), hglob_eq "journal" (by decide)]
        have hws_sl : (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW post (globN s "ws" + k)) =
            (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW s (globN s "ws" + k)) := by
          split; · rfl
          rename_i hnz; apply List.map_congr_left; intro k hk
          exact memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 40) (by decide) hnz
            (by simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl <;> omega)
        have hbs_sl : (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW post (globN s "bs" + k)) =
            (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW s (globN s "bs" + k)) := by
          split; · rfl
          rename_i hnz; apply List.map_congr_left; intro k hk
          exact memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 80) (by decide) hnz
            (by simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
        have hts_sl : (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW post (globN s "ts" + k)) =
            (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW s (globN s "ts" + k)) := by
          split; · rfl
          rename_i hnz; apply List.map_congr_left; intro k hk
          exact memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 72) (by decide) hnz
            (by simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
        have hnest_bs : (if globN s "bs" ≠ 0 ∧ memW post (globN s "bs" + 32) ∈ S then htabValues post (memW post (globN s "bs" + 32)) else []) =
            (if globN s "bs" ≠ 0 ∧ memW s (globN s "bs" + 32) ∈ S then htabValues s (memW s (globN s "bs" + 32)) else []) := by
          by_cases hnz : globN s "bs" = 0
          · simp [hnz]
          · rw [memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 80) (by decide) hnz (by omega)]
            by_cases hmS : memW s (globN s "bs" + 32) ∈ S
            · simp [hnz, hmS, htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1]
            · simp [hnz, hmS]
        have hnest_ts : (if globN s "ts" ≠ 0 ∧ memW post (globN s "ts" + 32) ∈ S then htabValues post (memW post (globN s "ts" + 32)) else []) =
            (if globN s "ts" ≠ 0 ∧ memW s (globN s "ts" + 32) ∈ S then htabValues s (memW s (globN s "ts" + 32)) else []) := by
          by_cases hnz : globN s "ts" = 0
          · simp [hnz]
          · rw [memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 72) (by decide) hnz (by omega)]
            by_cases hmS : memW s (globN s "ts" + 32) ∈ S
            · simp [hnz, hmS, htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1]
            · simp [hnz, hmS]
        have hbal_fl : (balRecords s).flatMap (fun ad => [memW post ad, memW post (ad + 8)]) =
            (balRecords s).flatMap (fun ad => [memW s ad, memW s (ad + 8)]) := by
          apply List.flatMap_congr; intro ad had
          have had_mem := balRecord_ivl_mem had
          rcases fixedObject_le_2pow64 hAs.2 hWT.2.2.1 (bal_in_fixedObjects had_mem) with h0 | had_bnd
          · dsimp only at h0; omega
          · dsimp only at had_bnd
            have hwti_ad := mem_worldTypedIvls_bal (S := S) (Nd := Nd) had_mem
            rw [memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩,
                memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩]
        have hjrn_mp : (List.range (globN s "journal_n")).map (fun k => memW post (globN s "journal" + 32 * k)) =
            (List.range (globN s "journal_n")).map (fun k => memW s (globN s "journal" + 32 * k)) := by
          apply List.map_congr_left; intro k hk; rw [List.mem_range] at hk
          have hjc_le := hWT.2.1.1
          have hjc_ne : globN s "journal_cap" ≠ 0 := by omega
          rcases hWT.2.1.2.2.1 with h0 | ⟨hal, _⟩
          · exact absurd h0 hjc_ne
          · have hbnd := allocated_le_2pow64 hAs.2 hal; dsimp only at hbnd
            have hkle : 32 * k + 8 ≤ 32 * globN s "journal_cap" := by omega
            exact memW_eq_of_cellHits hcell (by omega) (mem_worldTypedIvls_journal (S := S) (Nd := Nd) hjc_ne)
              ⟨by dsimp only; omega, by dsimp only; omega⟩
        dsimp only
        rw [hglob_eq "bs" (by decide), hglob_eq "ts" (by decide),
            hws_sl, hbs_sl, hts_sl, hnest_bs, hnest_ts, hbal_fl, hjrn_mp]
      have hdelEx_iff : ∀ i t, DelExclusive post S (evmChain s) i t ↔ DelExclusive s S (evmChain s) i t := by
        intro i t; unfold DelExclusive; rw [hworldRefs_eq]
        refine and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun hj =>
          forall_congr' fun k => imp_congr_right fun hk => ?_)
        have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
        have hk_ok : k + 8 ≤ 280 ∧ k % 8 = 0 ∧ k ≠ 32 ∧ k ≠ 40 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl <;> exact ⟨by omega, by omega, by omega, by omega⟩
        rw [(hrec_eq _ hj_mem).1 k hk_ok.1 hk_ok.2.1 hk_ok.2.2.1 hk_ok.2.2.2]
      intro i hi
      have hi_mem : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
      have hm_eq := (hrec_eq _ hi_mem).2.1 48 (by omega) (by omega)
      have hmm_eq := (hrec_eq _ hi_mem).2.1 56 (by omega) (by omega)
      have he24_eq := (hrec_eq _ hi_mem).1 24 (by omega) (by omega) (by omega) (by omega)
      have htake_eq : ((evmChain s).take (i + 1)).map (fun ec => memW post (ec.1 + 136)) =
          ((evmChain s).take (i + 1)).map (fun ec => memW s (ec.1 + 136)) := by
        apply List.map_congr_left; intro ec hec
        exact (hrec_eq ec (List.mem_of_mem_take hec)).1 136 (by omega) (by omega) (by omega) (by omega)
      have hM := hMarks i hi; dsimp only at hM ⊢
      rw [hm_eq, hmm_eq, he24_eq, hfeq, htake_eq]
      obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM
      refine ⟨m1, m2, m3, m4, ?_, ?_, m7, ?_, m9⟩
      · intro j hj hij
        have hj_tail : (evmChain s)[j] ∈ chTail := by
          rcases j with _ | j'
          · omega
          · simp [hch_eq]
        have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
        rw [hfs_eq _ hj_mem, htail_fo_eq _ hj_tail, hframeLogs_eq _ hj_mem,
            (hrec_eq _ hj_mem).1 112 (by omega) (by omega) (by omega) (by omega)]
        exact m5 j hj hij
      · rw [hfs_eq _ hi_mem]; exact m6
      · intro t ht
        rw [hfp_eq_all t ht, hdelEx_iff i t]; exact m8 t ht
    · rw [worldRoleSlots_eq hAs.2 hWT.1 hWT.2.2.1 hcell hcg,
          hframeRoleSlots_eq,
          journalRoleSlots_eq hAs.2 hWT.2.1 hWT.2.2.1 hcell hcg]
      unfold RolesOK at hRoles ⊢
      refine ⟨fun a ha => ?_, hRoles.2⟩
      obtain ⟨haS, hkl⟩ := hRoles.1 a ha
      have htb := ((hWT.1.2.1 a.1 haS).1.1 (a.1, 88) (by simp [htabFootprint])).1
      rw [htab_hdr_eq hcell haS htb 0 (by omega)]; exact ⟨haS, hkl⟩
    · have hsum_eq : ((evmChain s).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)).sum =
          ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum := by
        unfold evmR at hR_eq; rw [hchain_eq] at hR_eq; exact hR_eq
      rw [hsum_eq]; exact hGas
  exact ⟨⟨hApost, hInvAt_post, hWT_post.2.2.2, hAT_post⟩, hwti_eq, hchain_eq, hR_eq, hfo_post_cases⟩

private theorem heap_buffer_disj_after_head_mem_extend_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {buf : Ivl}
    (hInvW : EvmInvWith post S Nd)
    (hbuf_hi : buf.1 + buf.2 ≤ heapLimit)
    (hwti : worldTypedIvls post S Nd = worldTypedIvls s S Nd)
    (hchain : evmChain post = evmChain s)
    (hobjects : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects post ec,
      o ∈ frameObjects s ec ∨
      (ec = (globN s "ev", globN s "cur_cont") ∧
        o = (memW post (globN s "ev" + 24), memW post (globN s "ev" + 40))))
    (hdisj : IvlsDisj [buf]
      (worldTypedIvls s S Nd ++ ((evmChain s).map (frameObjects s)).flatten)) :
    IvlsDisj [buf]
      (worldTypedIvls post S Nd ++ ((evmChain post).map (frameObjects post)).flatten) := by
  intro b hb o ho
  simp only [List.mem_singleton] at hb
  subst b
  rcases List.mem_append.1 ho with hworld | hframe
  · apply hdisj buf (by simp) o
    apply List.mem_append_left
    rwa [hwti] at hworld
  · obtain ⟨objects, hmap, ho⟩ := List.mem_flatten.1 hframe
    obtain ⟨ec, hec, rfl⟩ := List.mem_map.1 hmap
    have hec_old : ec ∈ evmChain s := by rwa [hchain] at hec
    rcases hobjects ec hec_old o ho with hold | ⟨rfl, rfl⟩
    · exact hdisj buf (by simp) o (List.mem_append_right _
        (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ec, hec_old, rfl⟩, hold⟩))
    · have hFW := hInvW.2.1.2.2.2.2.1 _ hec
      have hlo := hFW.2.1.1
      have hlim : heapLimit ≤ scratchStart := by decide
      exact Or.inr (Or.inr (Or.inl (by dsimp only at hlo ⊢; omega)))

theorem logEntryOK_of_allocated_fields_g09 {F : Type}
    {s : PanSemStateFiniteExact 64 F} {log address topics data nt n : Nat}
    (hheap : globN s "heap_ptr" ≤ heapLimit)
    (hwords : WordsOK s (log, 40))
    (hlog : Inside (log, 40) sourceBase (globN s "heap_ptr"))
    (haddress : Inside (address, 24) sourceBase (globN s "heap_ptr"))
    (htopics : Inside (topics, 32 * nt + 8) sourceBase (globN s "heap_ptr"))
    (hdata : Inside (data, n + 8) sourceBase (globN s "heap_ptr"))
    (hnt : nt ≤ 4)
    (h0 : memW s log = address)
    (h8 : memW s (log + 8) = topics)
    (h16 : memW s (log + 16) = nt)
    (h24 : memW s (log + 24) = data)
    (h32 : memW s (log + 32) = n) :
    LogEntryOK s log := by
  have hn : n < 2 ^ 32 := by
    exact heap_alloc_size_lt_twoPow32 hdata.1
      (by have := hdata.2; dsimp only at this ⊢; omega) hheap
  unfold LogEntryOK
  rw [h0, h8, h16, h24, h32]
  exact ⟨hwords, hlog, hnt, hn,
    ⟨haddress.1, by have := haddress.2; dsimp only at this ⊢; omega⟩,
    ⟨htopics.1, by have := htopics.2; dsimp only at this ⊢; omega⟩,
    ⟨hdata.1, by have := hdata.2; dsimp only at this ⊢; omega⟩⟩

theorem logsListOK_append_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {logs log : Nat}
    (hwords : WordsOK post (logs, 24))
    (hallocated : Allocated post (logs, 24))
    (hlen : memW post (logs + 8) = memW s (logs + 8) + 1)
    (hlen_bound : memW s (logs + 8) + 1 < 2 ^ 28)
    (hcap : memW s (logs + 8) + 1 ≤ memW post (logs + 16))
    (hold : ∀ i, i < memW s (logs + 8) →
      WordAt post (memW post logs + 8 * i) ∧
      memW post (memW post logs + 8 * i) = memW s (memW s logs + 8 * i) ∧
      LogEntryOK post (memW s (memW s logs + 8 * i)))
    (hslot : WordAt post (memW post logs + 8 * memW s (logs + 8)))
    (hstore : memW post (memW post logs + 8 * memW s (logs + 8)) = log)
    (hlog : LogEntryOK post log) :
    LogsListOK post logs := by
  right
  refine ⟨hwords, hallocated, by rw [hlen]; exact hlen_bound,
    by rw [hlen]; exact hcap, fun i hi => ?_⟩
  rw [hlen] at hi
  by_cases hold_i : i < memW s (logs + 8)
  · obtain ⟨hw, heq, hentry⟩ := hold i hold_i
    exact ⟨hw, by rw [heq]; exact hentry⟩
  · have hi_eq : i = memW s (logs + 8) := by omega
    subst i
    exact ⟨hslot, by rw [hstore]; exact hlog⟩

theorem frameLogObjects_append_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {ec : Ivl} {log : Nat}
    (hheader : memW post (ec.1 + 88) = memW s (ec.1 + 88))
    (hlen : memW post (memW s (ec.1 + 88) + 8) =
      memW s (memW s (ec.1 + 88) + 8) + 1)
    (hold : ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      logOwnedIvls post (memW post (memW post (memW s (ec.1 + 88)) + 8 * i)) =
      logOwnedIvls s (memW s (memW s (memW s (ec.1 + 88)) + 8 * i)))
    (hnew : memW post
      (memW post (memW s (ec.1 + 88)) + 8 * memW s (memW s (ec.1 + 88) + 8)) = log) :
    frameLogObjects post ec = frameLogObjects s ec ++ logOwnedIvls post log := by
  unfold frameLogObjects
  dsimp only
  rw [hheader, hlen, List.range_succ, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hnew]
  congr 1
  apply List.flatMap_congr
  intro i hi
  exact hold i (List.mem_range.1 hi)

theorem logOwnedIvls_disj_of_record_fields_g09 {F : Type}
    {s : PanSemStateFiniteExact 64 F} {log : Nat} {other : Ivl}
    (hrecord : Disj (log, 40) other)
    (haddress : Disj (memW s log, 20) other)
    (htopics : Disj (memW s (log + 8), 32 * memW s (log + 16)) other)
    (hdata : Disj (memW s (log + 24), memW s (log + 32)) other) :
    ∀ i ∈ logOwnedIvls s log, Disj i other := by
  intro i hi
  have hi' := (List.mem_filter.1 hi).1
  simp only [logRecordIvls, List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with rfl | rfl | rfl | rfl
  · exact hrecord
  · exact haddress
  · exact htopics
  · exact hdata

theorem frameObjects_of_log_append_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {ec : Ivl} {log : Nat}
    (hfields : ∀ k ∈ ([8, 24, 40, 88, 232] : List Nat),
      memW post (ec.1 + k) = memW s (ec.1 + k))
    (hret : frameRet post ec = frameRet s ec)
    (hlogs : frameLogObjects post ec = frameLogObjects s ec ++ logOwnedIvls post log) :
    frameObjects post ec =
      [(ec.1, 280), (ec.2, 104), (memW s (ec.1 + 8), 32 * memW s (ec.1 + 232)),
       (memW s (ec.1 + 24), memW s (ec.1 + 40)), (memW s (ec.1 + 88), 24),
       frameLogs post ec, frameRet s ec] ++
      frameLogObjects s ec ++ logOwnedIvls post log := by
  unfold frameObjects
  rw [hfields 8 (by simp), hfields 232 (by simp), hfields 24 (by simp),
    hfields 40 (by simp), hfields 88 (by simp), hret, hlogs, List.append_assoc]

theorem log_append_owned_disj_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {ec : Ivl} {log : Nat} {other : Ivl}
    (hlogs : frameLogObjects post ec = frameLogObjects s ec ++ logOwnedIvls post log)
    (hold : ∀ i ∈ frameLogObjects s ec, Disj i other)
    (hnew : ∀ i ∈ logOwnedIvls post log, Disj i other) :
    ∀ i ∈ frameLogObjects post ec, Disj i other := by
  intro i hi
  rw [hlogs] at hi
  rcases List.mem_append.1 hi with hi | hi
  · exact hold i hi
  · exact hnew i hi

theorem logEntryOK_of_record_agree_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {log : Nat}
    (hdom : post.memaddrs = s.memaddrs)
    (hheap : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hrecord : ∀ k ∈ ([0, 8, 16, 24, 32] : List Nat),
      memW post (log + k) = memW s (log + k))
    (h : LogEntryOK s log) : LogEntryOK post log := by
  have h0 : memW post log = memW s log := by
    simpa only [Nat.add_zero] using hrecord 0 (by simp)
  unfold LogEntryOK at h ⊢
  rw [h0, hrecord 8 (by simp), hrecord 16 (by simp),
    hrecord 24 (by simp), hrecord 32 (by simp)]
  obtain ⟨hw, hl, hn, hsize, ha, ht, hd⟩ := h
  exact ⟨(wordsOK_congr_of_dom_g09 hdom).2 hw,
    ⟨hl.1, le_trans hl.2 hheap⟩, hn, hsize,
    ⟨ha.1, le_trans ha.2 hheap⟩,
    ⟨ht.1, le_trans ht.2 hheap⟩,
    ⟨hd.1, le_trans hd.2 hheap⟩⟩

theorem logOwnedIvls_of_record_agree_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {log : Nat}
    (hsys : globN post "vm_system_address" = globN s "vm_system_address")
    (hrecord : ∀ k ∈ ([0, 8, 16, 24, 32] : List Nat),
      memW post (log + k) = memW s (log + k)) :
    logOwnedIvls post log = logOwnedIvls s log := by
  have h0 : memW post log = memW s log := by
    simpa only [Nat.add_zero] using hrecord 0 (by simp)
  unfold logOwnedIvls logRecordIvls
  rw [h0, hrecord 8 (by simp), hrecord 16 (by simp),
    hrecord 24 (by simp), hrecord 32 (by simp), hsys]

theorem log_entries_preserved_of_frame_effect_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} {ec : Ivl} {Rl : List Ivl}
    (hA : ArenaReady s) (hFW : FrameWF s S ec)
    (heff : ByteRegionEffect s post Rl)
    (hheap : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hsys : globN post "vm_system_address" = globN s "vm_system_address")
    (hdisj : ∀ x ∈ Rl, ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      Disj x (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40)) :
    ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      let log := memW s (memW s (memW s (ec.1 + 88)) + 8 * i)
      LogEntryOK post log ∧ logOwnedIvls post log = logOwnedIvls s log := by
  intro i hi
  have hlog_ok : LogEntryOK s (memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) := by
    rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | hlogs
    · have hlo := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1.1
      have hss : 0 < scratchStart := by decide
      have hsp : scratchStart ≤ globN s "scratch_ptr" :=
        le_trans hA.2.2.2.1 hA.2.2.2.2.1
      dsimp only at hlo
      omega
    · exact (hlogs.2.2.2.2 i hi).2
  have hrecord : ∀ k ∈ ([0, 8, 16, 24, 32] : List Nat),
      memW post (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + k) =
        memW s (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + k) := by
    intro k hk
    have hk_bounds : k + 8 ≤ 40 ∧ k % 8 = 0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
    have hhi : memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + 40 ≤ 2 ^ 64 := by
      have hheap_bound := hA.2.2.1
      have hlog_inside := hlog_ok.2.1.2
      have hlimit : heapLimit ≤ 2 ^ 64 := by decide
      omega
    exact memW_eq_of_frameDisj_g09 hA.1.2 heff hhi hlog_ok.1.1
      hk_bounds.2 hk_bounds.1 (fun x hx => hdisj x hx i hi)
  exact ⟨logEntryOK_of_record_agree_g09 heff.memaddrs hheap hrecord hlog_ok,
    logOwnedIvls_of_record_agree_g09 hsys hrecord⟩

/-- Semantic append postcondition, including preservation of every pre-existing
entry and the exact extension of the frame's owned log intervals. -/
theorem log_append_post_of_frame_effect_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} {ec : Ivl}
    {Rl : List Ivl} {log : Nat}
    (hA : ArenaReady s) (hFW : FrameWF s S ec)
    (heff : ByteRegionEffect s post Rl)
    (hheap : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hsys : globN post "vm_system_address" = globN s "vm_system_address")
    (hdisj : ∀ x ∈ Rl, ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      Disj x (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40))
    (hheader : memW post (ec.1 + 88) = memW s (ec.1 + 88))
    (hwords : WordsOK post (memW s (ec.1 + 88), 24))
    (hallocated : Allocated post (memW s (ec.1 + 88), 24))
    (hlen : memW post (memW s (ec.1 + 88) + 8) =
      memW s (memW s (ec.1 + 88) + 8) + 1)
    (hcap : memW s (memW s (ec.1 + 88) + 8) + 1 ≤
      memW post (memW s (ec.1 + 88) + 16))
    (hold : ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      WordAt post (memW post (memW s (ec.1 + 88)) + 8 * i) ∧
      memW post (memW post (memW s (ec.1 + 88)) + 8 * i) =
        memW s (memW s (memW s (ec.1 + 88)) + 8 * i))
    (hslot : WordAt post (memW post (memW s (ec.1 + 88)) +
      8 * memW s (memW s (ec.1 + 88) + 8)))
    (hstore : memW post (memW post (memW s (ec.1 + 88)) +
      8 * memW s (memW s (ec.1 + 88) + 8)) = log)
    (hlog : LogEntryOK post log) :
    LogsListOK post (memW post (ec.1 + 88)) ∧
    frameLogObjects post ec = frameLogObjects s ec ++ logOwnedIvls post log := by
  have hpres := log_entries_preserved_of_frame_effect_g09 hA hFW heff hheap hsys hdisj
  constructor
  · rw [hheader]
    apply logsListOK_append_g09 hwords hallocated hlen
      (frameWF_logs_cap_bounds hA.2 hFW).2.2.2.1 hcap
      (fun i hi => ⟨(hold i hi).1, (hold i hi).2, (hpres i hi).1⟩)
      hslot hstore hlog
  · apply frameLogObjects_append_g09 hheader hlen _ hstore
    intro i hi
    rw [(hold i hi).2]
    exact (hpres i hi).2

/-- The final store in `log_append` writes exactly the returned list slot;
all other word cells retain their values. -/
theorem log_append_slot_store_exact_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {slot log : BitVec 64}
    (hslot : s.locals.lookup (ofString "slot") = some (.val (.word slot)))
    (hlog : s.locals.lookup (ofString "log") = some (.val (.word log)))
    (hstore : evaluateHOLFiniteState s
      (.store (.var .local (ofString "slot")) (.var .local (ofString "log"))) =
      (none, post)) :
    post.locals = s.locals ∧ post.globals = s.globals ∧
    post.memaddrs = s.memaddrs ∧ post.code = s.code ∧
    memW post slot.toNat = log.toNat ∧
    (∀ a, BitVec.ofNat 64 a ≠ slot → memW post a = memW s a) := by
  have hraw := hstore
  rw [evaluateHOLFiniteState_store] at hraw
  simp only [evalHOLExact, hslot, hlog] at hraw
  by_cases hdom : s.memaddrs slot
  · simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom, ↓reduceIte] at hraw
    injection hraw with _ hpost
    have hmem : post.memory = fun a => if a = slot then .word log else s.memory a := by
      have hm := congrArg PanSemStateFiniteExact.memory hpost
      dsimp only at hm
      exact hm.symm.trans (by
        funext a
        by_cases ha : a = slot
        · subst a; simp [FUPDATE]
        · simp [FUPDATE, ha])
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (congrArg PanSemStateFiniteExact.locals hpost).symm
    · exact (congrArg PanSemStateFiniteExact.globals hpost).symm
    · exact (congrArg PanSemStateFiniteExact.memaddrs hpost).symm
    · exact (congrArg PanSemStateFiniteExact.code hpost).symm
    · simp [memW, hmem]
    · intro a ha; simp [memW, hmem, ha]
  · simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom] at hraw

/-- Exact no-growth execution: only the length cell is changed and the old
length determines the returned slot. Return clears locals before the enclosing
declarations restore their saved bindings. -/
theorem lst_push_no_growth_exact_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (l esz n cap p : BitVec 64)
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (he : s.locals.lookup (ofString "esz") = some (.val (.word esz)))
    (hd0 : s.memaddrs l) (hd8 : s.memaddrs (l + 8#64)) (hd16 : s.memaddrs (l + 16#64))
    (hm0 : s.memory l = .word p) (hm8 : s.memory (l + 8#64) = .word n)
    (hm16 : s.memory (l + 16#64) = .word cap)
    (hlt : n.toNat < cap.toNat) (hne : l ≠ l + 8#64) :
    evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_lst_push) =
      (some (.returned (.val (.word (p + n * esz)))),
        {s with
          locals := ((HolFiniteMapExact.empty.resVarEq
            (ofString "cap", s.locals.lookup (ofString "cap"))).resVarEq
            (ofString "n", s.locals.lookup (ofString "n"))),
          memory := fun a => if a = l + 8#64 then .word (n + 1#64) else s.memory a}) := by
  have hb : sourceFnBody Guest.Software.guestFn_lst_push =
    .dec (ofString "n") .one (.load .one (.op .add [.var .local (ofString "l"), .const 8]))
      (.dec (ofString "cap") .one (.load .one (.op .add [.var .local (ofString "l"), .const 16]))
        (.seq (.ite (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap")))
          (.decCall (ofString "np") .one (ofString "alloc")
            [.panop .mul [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2]]
            (.seq (.call (some (none, none)) (ofString "memcpy")
              [.var .local (ofString "np"), .load .one (.op .add [.var .local (ofString "l"), .const 0]),
                .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
              (.seq (.store (.op .add [.var .local (ofString "l"), .const 0]) (.var .local (ofString "np")))
                (.store (.op .add [.var .local (ofString "l"), .const 16])
                  (.panop .mul [.var .local (ofString "cap"), .const 2]))))) .skip)
          (.seq (.store (.op .add [.var .local (ofString "l"), .const 8])
            (.op .add [.var .local (ofString "n"), .const 1]))
            (.return (.op .add [.load .one (.op .add [.var .local (ofString "l"), .const 0]),
              .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]]))))) := rfl
  rw [hb]
  have hcn : ofString "cap" ≠ ofString "n" := by decide
  have hnl : ofString "n" ≠ ofString "l" := by decide
  have hcl : ofString "cap" ≠ ofString "l" := by decide
  have hne' : ofString "n" ≠ ofString "esz" := by decide
  have hce : ofString "cap" ≠ ofString "esz" := by decide
  have hcmp : ¬ cap ≤ n := by exact Nat.not_le_of_lt hlt
  have hlt' : n < cap := hlt
  have hload : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .local (ofString "l"), .const 8])) = some (.val (.word n)) := by
    simp [evalHOLExact, evalListHOLExact, hl, valueIsWord, valueWord, wordOpHOL, wordOp,
      memLoadHOLExact, hd8, hm8]
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [hload]
  simp only [shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
  have hloadcap : @evalHOLExact 64 F _
      (setVarHOLFinite (ofString "n") (.val (.word n)) s).toExact
      (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .local (ofString "l"), .const 16])) = some (.val (.word cap)) := by
    simp [evalHOLExact, evalListHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update,
      FUPDATE, hnl, Ne.symm hnl, hl, valueIsWord, valueWord, wordOpHOL, wordOp,
      memLoadHOLExact, hd16, hm16]
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  erw [hloadcap]
  simp only [shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
  simp only [
    evaluateHOLFiniteState_dec_total, evaluateHOLFiniteState_seq_line780,
    evaluateHOLFiniteState_ite, evaluateHOLFiniteState_skip,
    evaluateHOLFiniteState_store, evaluateHOLFiniteState_return,
    evalHOLExact, evalListHOLExact, hl, he, hd0, hd8, hd16, hm0, hm8, hm16,
    setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
    valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact,
    hlt, hne, hcn, hnl, hcl, hne', hce,
    Ne.symm hcn, Ne.symm hnl, Ne.symm hcl, Ne.symm hne', Ne.symm hce,
    shapeOfHOLExact, shapeEqHOL, hcmp, flattenHOL, panMemStoresHOL, panMemStoreHOL,
    List.all, List.map, Option.map, List.foldr, Bool.and_self, BitVec.add_zero,
    ↓reduceIte]
  simp [hd8, hm8, hd16, hm16, hd0, hm0, shapeOfHOLExact, shapeEqHOL,
    Compiler.Encoders.Asm.wordCmpHOL, hcmp, hlt', hcn, Ne.symm hcn]
  simp [evalHOLExact, evalListHOLExact, hl, he, hd0, hd8, hm0, hm8,
    setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
    valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact,
    hcn, hnl, hcl, hne', hce, Ne.symm hcn, Ne.symm hnl, Ne.symm hcl,
    Ne.symm hne', Ne.symm hce, flattenHOL, panMemStoresHOL, panMemStoreHOL,
    evaluateHOLFiniteState_return, hne, hlt', panOpHOL,
    shapeOfHOLExact, sizeOfShapeWithContextHOL, emptyLocalsHOLFinite]
  rfl

/-- The common length increment and slot-return tail, valid after either branch. -/
theorem lst_push_finish_exact_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (l esz n p : BitVec 64)
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (he : s.locals.lookup (ofString "esz") = some (.val (.word esz)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hd0 : s.memaddrs l) (hd8 : s.memaddrs (l + 8#64))
    (hm0 : s.memory l = .word p) (hne : l ≠ l + 8#64) :
    evaluateHOLFiniteState s
      (.seq (.store (.op .add [.var .local (ofString "l"), .const 8])
        (.op .add [.var .local (ofString "n"), .const 1]))
        (.return (.op .add [.load .one (.op .add [.var .local (ofString "l"), .const 0]),
          .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]]))) =
      (some (.returned (.val (.word (p + n * esz)))),
        {s with
          locals := HolFiniteMapExact.empty
          memory := fun a => if a = l + 8#64 then .word (n + 1#64) else s.memory a}) := by
  simp only [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store,
    evalHOLExact, evalListHOLExact, hl, he, hn, valueIsWord, valueWord, wordOpHOL, wordOp,
    List.all, List.map, List.foldr, Option.map, BitVec.add_zero, Bool.and_self, ↓reduceIte]
  simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hd8, evaluateHOLFiniteState_return,
    evalHOLExact, evalListHOLExact, hl, he, hn, valueIsWord, valueWord, wordOpHOL, wordOp,
    memLoadHOLExact, hd0, hm0, hne, panOpHOL, shapeOfHOLExact,
    sizeOfShapeWithContextHOL, emptyLocalsHOLFinite, FUPDATE]
  rfl

/-- Exact header installation after allocation and copying in the growth branch. -/
theorem lst_push_growth_header_exact_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (l np cap : BitVec 64)
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (hp : s.locals.lookup (ofString "np") = some (.val (.word np)))
    (hc : s.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (hd0 : s.memaddrs l) (hd16 : s.memaddrs (l + 16#64)) :
    evaluateHOLFiniteState s
      (.seq (.store (.op .add [.var .local (ofString "l"), .const 0]) (.var .local (ofString "np")))
        (.store (.op .add [.var .local (ofString "l"), .const 16])
          (.panop .mul [.var .local (ofString "cap"), .const 2]))) =
      (none, {s with memory := fun a => if a = l + 16#64 then .word (cap * 2#64)
        else if a = l then .word np else s.memory a}) := by
  simp only [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store,
    evalHOLExact, evalListHOLExact, hl, hp, hc, valueIsWord, valueWord, wordOpHOL, wordOp,
    List.all, List.map, List.foldr, Option.map, BitVec.add_zero, Bool.and_self, ↓reduceIte,
    flattenHOL, panMemStoresHOL, panMemStoreHOL, hd0, hd16, panOpHOL, FUPDATE]
  simp [BitVec.add_zero, hd0, hd16, evalHOLExact, evalListHOLExact, hl, hp, hc,
    valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, flattenHOL,
    panMemStoresHOL, panMemStoreHOL, FUPDATE]

/-- Complete post-copy growth tail: install the buffer and doubled capacity,
increment the original length, and return the new buffer's insertion slot. -/
theorem lst_push_after_copy_exact_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (l np cap n esz : BitVec 64)
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (hp : s.locals.lookup (ofString "np") = some (.val (.word np)))
    (hc : s.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (he : s.locals.lookup (ofString "esz") = some (.val (.word esz)))
    (hd0 : s.memaddrs l) (hd8 : s.memaddrs (l + 8#64)) (hd16 : s.memaddrs (l + 16#64))
    (hne8 : l ≠ l + 8#64) (hne16 : l ≠ l + 16#64) :
    let header : ProgHOL 64 :=
      .seq (.store (.op .add [.var .local (ofString "l"), .const 0]) (.var .local (ofString "np")))
        (.store (.op .add [.var .local (ofString "l"), .const 16])
          (.panop .mul [.var .local (ofString "cap"), .const 2]))
    let finish : ProgHOL 64 :=
      .seq (.store (.op .add [.var .local (ofString "l"), .const 8])
        (.op .add [.var .local (ofString "n"), .const 1]))
        (.return (.op .add [.load .one (.op .add [.var .local (ofString "l"), .const 0]),
          .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]]))
    evaluateHOLFiniteState s (.seq header finish) =
      (some (.returned (.val (.word (np + n * esz)))),
        {s with
          locals := HolFiniteMapExact.empty
          memory := fun a => if a = l + 8#64 then .word (n + 1#64)
            else if a = l + 16#64 then .word (cap * 2#64)
            else if a = l then .word np else s.memory a}) := by
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780,
    lst_push_growth_header_exact_g09 s l np cap hl hp hc hd0 hd16]
  dsimp only
  exact lst_push_finish_exact_g09 _ l esz n np hl he hn hd0 hd8
    (by simp [hne16]) hne8

/-- Concrete final store and return in `log_append`. -/
theorem log_append_store_return_exact_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (slot log : BitVec 64)
    (hs : s.locals.lookup (ofString "slot") = some (.val (.word slot)))
    (hl : s.locals.lookup (ofString "log") = some (.val (.word log)))
    (hd : s.memaddrs slot) :
    evaluateHOLFiniteState s
      (.seq (.store (.var .local (ofString "slot")) (.var .local (ofString "log")))
        (.return (.const 0))) =
      (some (.returned (.val (.word 0))),
        {s with
          locals := HolFiniteMapExact.empty
          memory := fun a => if a = slot then .word log else s.memory a}) := by
  simp [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store,
    evaluateHOLFiniteState_return, evalHOLExact, hs, hl, flattenHOL,
    panMemStoresHOL, panMemStoreHOL, hd, FUPDATE, shapeOfHOLExact,
    sizeOfShapeWithContextHOL, emptyLocalsHOLFinite]
  rfl

theorem log_append_of_lst_push_execution_g09 {F : Type}
    (s pushPost : PanSemStateFiniteExact 64 F)
    (values : List (ValueHOL 64)) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (slot log : BitVec 64)
    (hl : s.locals.lookup (ofString "log") = some (.val (.word log)))
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.load .one (.op .add [.var .local (ofString "e"), .const 88]), .const 8] = some values)
    (hlookup : lookupCodeHOLFinite s.code.lookup (ofString "lst_push") values =
      some (sourceFnBody Guest.Software.guestFn_lst_push, callee, .one))
    (hclock : s.clock ≠ 0)
    (hpush : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (sourceFnBody Guest.Software.guestFn_lst_push) =
      (some (.returned (.val (.word slot))), pushPost))
    (hd : pushPost.memaddrs slot) :
    evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_log_append) =
      (some (.returned (.val (.word 0))),
        {pushPost with
          locals := HolFiniteMapExact.empty.resVarEq (ofString "slot", s.locals.lookup (ofString "slot"))
          memory := fun a => if a = slot then .word log else pushPost.memory a}) := by
  have hb : sourceFnBody Guest.Software.guestFn_log_append =
      .decCall (ofString "slot") .one (ofString "lst_push")
        [.load .one (.op .add [.var .local (ofString "e"), .const 88]), .const 8]
        (.seq (.store (.var .local (ofString "slot")) (.var .local (ofString "log")))
          (.return (.const 0))) := rfl
  rw [hb, evaluateHOLFiniteState_decCall_fixClockRewrite, hargs]
  dsimp only
  rw [hlookup]
  simp only [hclock, ↓reduceIte, hpush, shapeOfHOLExact, shapeEqHOL, Bool.and_self]
  have hsl : ofString "slot" ≠ ofString "log" := by decide
  have hs : (setVarHOLFinite (ofString "slot") (.val (.word slot))
      {pushPost with locals := s.locals}).locals.lookup (ofString "slot") = some (.val (.word slot)) := by
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hlog : (setVarHOLFinite (ofString "slot") (.val (.word slot))
      {pushPost with locals := s.locals}).locals.lookup (ofString "log") = some (.val (.word log)) := by
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsl, Ne.symm hsl, hl]
  rw [log_append_store_return_exact_g09 _ slot log hs hlog hd]
  rfl

theorem lst_push_alloc_copy_header_exact_g09 {F : Type}
    (s allocPost copyPost : PanSemStateFiniteExact 64 F) (l esz cap np : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (he : s.locals.lookup (ofString "esz") = some (.val (.word esz)))
    (hc : s.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (hclock : s.clock ≠ 0)
    (halloc : evaluateHOLFiniteState
      (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update
        (ofString "n", .val (.word (esz * cap * 2#64)))))
      (sourceFnBody Guest.Software.guestFn_alloc) =
        (some (.returned (.val (.word np))), allocPost))
    (hcopy : evaluateHOLFiniteState
      (setVarHOLFinite (ofString "np") (.val (.word np)) {allocPost with locals := s.locals})
      (.call (some (none, none)) (ofString "memcpy")
        [.var .local (ofString "np"), .load .one (.op .add [.var .local (ofString "l"), .const 0]),
          .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]]) =
        (none, copyPost))
    (hcl : copyPost.locals.lookup (ofString "l") = some (.val (.word l)))
    (hcp : copyPost.locals.lookup (ofString "np") = some (.val (.word np)))
    (hcc : copyPost.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (hd0 : copyPost.memaddrs l) (hd16 : copyPost.memaddrs (l + 16#64)) :
    evaluateHOLFiniteState s
      (.decCall (ofString "np") .one (ofString "alloc")
        [.panop .mul [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2]]
        (.seq (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "np"), .load .one (.op .add [.var .local (ofString "l"), .const 0]),
            .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
          (.seq (.store (.op .add [.var .local (ofString "l"), .const 0]) (.var .local (ofString "np")))
            (.store (.op .add [.var .local (ofString "l"), .const 16])
              (.panop .mul [.var .local (ofString "cap"), .const 2]))))) =
      (none, {copyPost with
        locals := copyPost.locals.resVarEq (ofString "np", s.locals.lookup (ofString "np"))
        memory := fun a => if a = l + 16#64 then .word (cap * 2#64)
          else if a = l then .word np else copyPost.memory a}) := by
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.panop .mul [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2]] =
        some [.val (.word (esz * cap * 2#64))] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, he, hc, panOpHOL,
      valueIsWord, valueWord]
  have hlook := pan_one_word_lookup s.code.lookup (ofString "alloc") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_alloc) (esz * cap * 2#64)
    (by rw [hcode]; exact OpHandlers.lookup_alloc)
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hargs]
  dsimp only
  rw [hlook]
  simp only [hclock, ↓reduceIte, halloc, shapeOfHOLExact, shapeEqHOL, Bool.and_self]
  rw [evaluateHOLFiniteState_seq_line780, hcopy]
  dsimp only
  rw [lst_push_growth_header_exact_g09 copyPost l np cap hcl hcp hcc hd0 hd16]

theorem lst_push_growth_of_branch_execution_g09 {F : Type}
    (s growPost : PanSemStateFiniteExact 64 F) (l esz n cap np : BitVec 64)
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (hd8 : s.memaddrs (l + 8#64)) (hd16 : s.memaddrs (l + 16#64))
    (hm8 : s.memory (l + 8#64) = .word n)
    (hm16 : s.memory (l + 16#64) = .word cap)
    (hge : cap.toNat ≤ n.toNat)
    (hbranch : evaluateHOLFiniteState
      (setVarHOLFinite (ofString "cap") (.val (.word cap))
        (setVarHOLFinite (ofString "n") (.val (.word n)) s))
      (.decCall (ofString "np") .one (ofString "alloc")
        [.panop .mul [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2]]
        (.seq (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "np"), .load .one (.op .add [.var .local (ofString "l"), .const 0]),
            .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
          (.seq (.store (.op .add [.var .local (ofString "l"), .const 0]) (.var .local (ofString "np")))
            (.store (.op .add [.var .local (ofString "l"), .const 16])
              (.panop .mul [.var .local (ofString "cap"), .const 2]))))) = (none, growPost))
    (hgl : growPost.locals.lookup (ofString "l") = some (.val (.word l)))
    (hge' : growPost.locals.lookup (ofString "esz") = some (.val (.word esz)))
    (hgn : growPost.locals.lookup (ofString "n") = some (.val (.word n)))
    (hgd0 : growPost.memaddrs l) (hgd8 : growPost.memaddrs (l + 8#64))
    (hgm0 : growPost.memory l = .word np) (hne : l ≠ l + 8#64) :
    evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_lst_push) =
      (some (.returned (.val (.word (np + n * esz)))),
        {growPost with
          locals := ((HolFiniteMapExact.empty.resVarEq
            (ofString "cap", s.locals.lookup (ofString "cap"))).resVarEq
            (ofString "n", s.locals.lookup (ofString "n"))),
          memory := fun a => if a = l + 8#64 then .word (n + 1#64) else growPost.memory a}) := by
  have hcn : ofString "cap" ≠ ofString "n" := by decide
  have hnl : ofString "n" ≠ ofString "l" := by decide
  have hload : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .local (ofString "l"), .const 8])) = some (.val (.word n)) := by
    simp [evalHOLExact, evalListHOLExact, hl, valueIsWord, valueWord, wordOpHOL, wordOp,
      memLoadHOLExact, hd8, hm8]
  change evaluateHOLFiniteState s
    (.dec (ofString "n") .one (.load .one (.op .add [.var .local (ofString "l"), .const 8]))
      (.dec (ofString "cap") .one (.load .one (.op .add [.var .local (ofString "l"), .const 16]))
        (.seq (.ite (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap")))
          (.decCall (ofString "np") .one (ofString "alloc")
            [.panop .mul [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2]]
            (.seq (.call (some (none, none)) (ofString "memcpy")
              [.var .local (ofString "np"), .load .one (.op .add [.var .local (ofString "l"), .const 0]),
                .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
              (.seq (.store (.op .add [.var .local (ofString "l"), .const 0]) (.var .local (ofString "np")))
                (.store (.op .add [.var .local (ofString "l"), .const 16])
                  (.panop .mul [.var .local (ofString "cap"), .const 2]))))) .skip)
          (.seq (.store (.op .add [.var .local (ofString "l"), .const 8])
            (.op .add [.var .local (ofString "n"), .const 1]))
            (.return (.op .add [.load .one (.op .add [.var .local (ofString "l"), .const 0]),
              .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]])))))) = _
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [hload]
  simp only [shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
  have hloadcap : @evalHOLExact 64 F _
      (setVarHOLFinite (ofString "n") (.val (.word n)) s).toExact
      (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .local (ofString "l"), .const 16])) = some (.val (.word cap)) := by
    simp [evalHOLExact, evalListHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update,
      FUPDATE, hnl, Ne.symm hnl, hl, valueIsWord, valueWord, wordOpHOL, wordOp,
      memLoadHOLExact, hd16, hm16]
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  erw [hloadcap]
  simp only [shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
  have hcmp : cap ≤ n := hge
  have hcond : @evalHOLExact 64 F _
      (setVarHOLFinite (ofString "cap") (.val (.word cap))
        (setVarHOLFinite (ofString "n") (.val (.word n)) s)).toExact
      (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap"))) =
        some (.val (.word 1)) := by
    simp [evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      hcn, Ne.symm hcn, valueIsWord, valueWord, Compiler.Encoders.Asm.wordCmpHOL, hcmp]
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  dsimp only
  erw [hcond]
  simp only [valueIsWord, valueWord, ↓reduceIte]
  rw [hbranch]
  have hone : (1 : BitVec 64) ≠ 0 := by decide
  simp only [hone, ↓reduceIte]
  rw [lst_push_finish_exact_g09 growPost l esz n np hgl hge' hgn hgd0 hgd8 hgm0 hne]
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hcn, Ne.symm hcn]

theorem log_append_no_growth_exact_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (e log l n cap p : BitVec 64)
    (hcode : s.code = originalRuntimeCode) (hclock : s.clock ≠ 0)
    (he : s.locals.lookup (ofString "e") = some (.val (.word e)))
    (hlg : s.locals.lookup (ofString "log") = some (.val (.word log)))
    (hde : s.memaddrs (e + 88#64)) (hme : s.memory (e + 88#64) = .word l)
    (hd0 : s.memaddrs l) (hd8 : s.memaddrs (l + 8#64)) (hd16 : s.memaddrs (l + 16#64))
    (hm0 : s.memory l = .word p) (hm8 : s.memory (l + 8#64) = .word n)
    (hm16 : s.memory (l + 16#64) = .word cap)
    (hlt : n.toNat < cap.toNat) (hne : l ≠ l + 8#64)
    (hdslot : s.memaddrs (p + n * 8#64)) :
    evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_log_append) =
      (some (.returned (.val (.word 0))),
        {s with
          clock := s.clock - 1
          locals := HolFiniteMapExact.empty.resVarEq (ofString "slot", s.locals.lookup (ofString "slot"))
          memory := fun a => if a = p + n * 8#64 then .word log
            else if a = l + 8#64 then .word (n + 1#64) else s.memory a}) := by
  let cal : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "l", .val (.word l))).update
      (ofString "esz", .val (.word 8#64))
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.load .one (.op .add [.var .local (ofString "e"), .const 88]), .const 8] =
        some [.val (.word l), .val (.word 8#64)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, he, hde, hme,
      valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact]
  have hlook := pan_two_word_lookup s.code.lookup (ofString "lst_push")
    (ofString "l") (ofString "esz") (sourceFnBody Guest.Software.guestFn_lst_push)
    l 8#64 (by decide) (by rw [hcode]; exact lookup_lst_push_g09)
  let entry := callEntryStateHOLFinite s cal
  have hel : entry.locals.lookup (ofString "l") = some (.val (.word l)) := by
    have hne' : ofString "esz" ≠ ofString "l" := by decide
    simp [entry, cal, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne']
  have hez : entry.locals.lookup (ofString "esz") = some (.val (.word 8#64)) := by
    simp [entry, cal, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hpush := lst_push_no_growth_exact_g09 entry l 8#64 n cap p hel hez
    hd0 hd8 hd16 hm0 hm8 hm16 hlt hne
  have hres := log_append_of_lst_push_execution_g09 s _ _ cal (p + n * 8#64) log
    hlg hargs hlook hclock hpush hdslot
  simpa [entry, cal, callEntryStateHOLFinite] using hres

theorem lst_push_alloc_return_effect_g09 {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (p esz cap : BitVec 64) (v : ValueHOL 64)
    (hcode : s.code = originalRuntimeCode)
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hlimit : p.toNat ≤ InitECandidate.Solver.HeapPotential.cMax.toNat)
    (hrun : evaluateHOLFiniteState
      (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update
        (ofString "n", .val (.word (esz * cap * 2#64)))))
      (sourceFnBody Guest.Software.guestFn_alloc) = (some (.returned v), post)) :
    let q := (p + (esz * cap * 2#64 + 7)) &&& ((0 : BitVec 64) - 8)
    v = .val (.word p) ∧
    post.globals = s.globals.update (ofString "heap_ptr", .val (.word q)) ∧
    post.memory = s.memory ∧ post.memaddrs = s.memaddrs ∧
    post.code = s.code ∧
    p.toNat + (esz * cap * 2#64).toNat ≤ q.toNat ∧
    q.toNat ≤ InitECandidate.Solver.HeapPotential.cMax.toNat ∧ q.toNat % 8 = 0 := by
  let entry := callEntryStateHOLFinite s (HolFiniteMapExact.empty.update
    (ofString "n", .val (.word (esz * cap * 2#64))))
  have hg := M13.evaluate_alloc_body_general entry p (esz * cap * 2#64) hcode hlimit hp
    (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
  have hm := PanRunBounded.evaluateHOLFiniteState_metadata entry
    (sourceFnBody Guest.Software.guestFn_alloc)
  change evaluateHOLFiniteState entry _ = _ at hrun
  rw [hrun] at hg hm
  obtain ⟨hv, hglob, hmem, hsize, hmax, halign⟩ := hg v rfl
  exact ⟨hv, hglob, hmem, hm.2.1, hm.1, hsize, hmax, halign⟩

/-- Allocation followed by the growth copy preserves the old source words,
frames the copy destination, and exposes the exact new heap pointer. -/
theorem lst_push_alloc_memcpy_effect_g09 {F : Type}
    (s allocPost copyPost : PanSemStateFiniteExact 64 F)
    (p src l esz cap n : BitVec 64) (v : ValueHOL 64)
    (hcode : s.code = originalRuntimeCode)
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hlimit : p.toNat ≤ InitECandidate.Solver.HeapPotential.cMax.toNat)
    (halloc : evaluateHOLFiniteState
      (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update
        (ofString "n", .val (.word (esz * cap * 2#64)))))
      (sourceFnBody Guest.Software.guestFn_alloc) = (some (.returned v), allocPost))
    (hma : s.memaddrs = ordinaryDomain)
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (he : s.locals.lookup (ofString "esz") = some (.val (.word esz)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hdl : s.memaddrs l) (hml : s.memory l = .word src)
    (hd8 : p.toNat % 8 = 0) (hs8 : src.toNat % 8 = 0)
    (hn8 : (esz * n).toNat % 8 = 0)
    (hsmall : (esz * n).toNat + 32 < 2 ^ 63)
    (hdnw : p.toNat + (esz * n).toNat ≤ 2 ^ 64)
    (hsnw : src.toNat + (esz * n).toNat ≤ 2 ^ 64)
    (hdisj : Disj (p.toNat, (esz * n).toNat) (src.toNat, (esz * n).toNat))
    (hcopy : evaluateHOLFiniteState
      (setVarHOLFinite (ofString "np") (.val (.word p)) {allocPost with locals := s.locals})
      (.call (some (none, none)) (ofString "memcpy")
        [.var .local (ofString "np"), .load .one (.op .add [.var .local (ofString "l"), .const 0]),
          .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]]) =
        (none, copyPost)) :
    let q := (p + (esz * cap * 2#64 + 7)) &&& ((0 : BitVec 64) - 8)
    let copyEntry := setVarHOLFinite (ofString "np") (.val (.word p))
      {allocPost with locals := s.locals}
    v = .val (.word p) ∧
    copyPost.globals = s.globals.update (ofString "heap_ptr", .val (.word q)) ∧
    copyPost.memaddrs = s.memaddrs ∧ copyPost.code = s.code ∧
    copyPost.locals = copyEntry.locals ∧
    ByteRegionEffect copyEntry copyPost [(p.toNat, (esz * n).toNat)] ∧
    (∀ k, 8 * k < (esz * n).toNat →
      memW copyPost (p.toNat + 8 * k) = memW s (src.toNat + 8 * k)) ∧
    p.toNat + (esz * cap * 2#64).toNat ≤ q.toNat ∧
    q.toNat ≤ InitECandidate.Solver.HeapPotential.cMax.toNat ∧ q.toNat % 8 = 0 := by
  dsimp only
  obtain ⟨hv, hg, hm, hd, hc, hfit, hmax, halign⟩ :=
    lst_push_alloc_return_effect_g09 s allocPost p esz cap v hcode hp hlimit halloc
  let entry := setVarHOLFinite (ofString "np") (.val (.word p))
    {allocPost with locals := s.locals}
  have hnp_l : ofString "np" ≠ ofString "l" := by decide
  have hnp_e : ofString "np" ≠ ofString "esz" := by decide
  have hnp_n : ofString "np" ≠ ofString "n" := by decide
  have hdl' : allocPost.memaddrs l := hd ▸ hdl
  have hdst : @evalHOLExact 64 F _ entry.toExact
      (fun a => Classical.propDecidable (entry.memaddrs a)) (.var .local (ofString "np")) =
        some (.val (.word p)) := by
    simp [entry, setVarHOLFinite, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE]
  have hsrc : @evalHOLExact 64 F _ entry.toExact
      (fun a => Classical.propDecidable (entry.memaddrs a))
      (.load .one (.op .add [.var .local (ofString "l"), .const 0])) =
        some (.val (.word src)) := by
    have hload : @memLoadHOLExact 64 _ .one l entry.memaddrs
        (fun a => Classical.propDecidable (entry.memaddrs a)) entry.memory entry.structs =
          some (.val (.word src)) := by
      rw [memLoadHOLExact]
      exact if_pos hdl' |>.trans (by rw [show entry.memory l = .word src from hm ▸ hml])
    simp [entry, setVarHOLFinite, evalHOLExact, evalListHOLExact,
      HolFiniteMapExact.lookup_update, FUPDATE, hnp_l, Ne.symm hnp_l, hl,
      valueIsWord, valueWord, wordOpHOL, wordOp] at hload ⊢
    exact hload
  have hsize : @evalHOLExact 64 F _ entry.toExact
      (fun a => Classical.propDecidable (entry.memaddrs a))
      (.panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]) =
        some (.val (.word (esz * n))) := by
    simp [entry, setVarHOLFinite, evalHOLExact, evalListHOLExact,
      HolFiniteMapExact.lookup_update, FUPDATE, hnp_e, Ne.symm hnp_e,
      hnp_n, Ne.symm hnp_n, he, hn, panOpHOL, valueIsWord, valueWord]
  have hnt : (evaluateHOLFiniteState entry
      (.call (some (none, none)) (ofString "memcpy")
        [.var .local (ofString "np"), .load .one (.op .add [.var .local (ofString "l"), .const 0]),
          .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])).1 ≠ some .timeOut := by
    rw [hcopy]; simp
  have heff := eval_call_memcpy_words_g09 entry _ _ _ p src (esz * n)
    (by exact hc.trans hcode) (by exact hd.trans hma)
    hdst hsrc hsize hd8 hs8 hn8 hsmall hdnw hsnw hdisj hnt
  dsimp only at heff
  rw [hcopy] at heff
  obtain ⟨heff, hlocals, hcopied⟩ := heff.1 rfl
  refine ⟨hv, heff.globals.trans hg, heff.memaddrs.trans hd, heff.code.trans hc,
    hlocals, heff, ?_, hfit, hmax, halign⟩
  intro k hk
  exact (hcopied k hk).trans (by simp [memW, entry, setVarHOLFinite, hm])

/-- Exact growth execution assembled from allocation, copying, header installation,
and the shared length increment and slot-return tail. -/
theorem lst_push_growth_alloc_copy_exact_g09 {F : Type}
    (s allocPost copyPost : PanSemStateFiniteExact 64 F) (l esz n cap p : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (he : s.locals.lookup (ofString "esz") = some (.val (.word esz)))
    (hd8 : s.memaddrs (l + 8#64)) (hd16 : s.memaddrs (l + 16#64))
    (hm8 : s.memory (l + 8#64) = .word n)
    (hm16 : s.memory (l + 16#64) = .word cap)
    (hge : cap.toNat ≤ n.toNat)
    (hclock : s.clock ≠ 0)
    (halloc : evaluateHOLFiniteState
      (callEntryStateHOLFinite
        (setVarHOLFinite (ofString "cap") (.val (.word cap))
          (setVarHOLFinite (ofString "n") (.val (.word n)) s))
        (HolFiniteMapExact.empty.update (ofString "n", .val (.word (esz * cap * 2#64)))))
      (sourceFnBody Guest.Software.guestFn_alloc) =
        (some (.returned (.val (.word p))), allocPost))
    (hcopy : evaluateHOLFiniteState
      (setVarHOLFinite (ofString "np") (.val (.word p)) {allocPost with locals :=
        (setVarHOLFinite (ofString "cap") (.val (.word cap))
          (setVarHOLFinite (ofString "n") (.val (.word n)) s)).locals})
      (.call (some (none, none)) (ofString "memcpy")
        [.var .local (ofString "np"), .load .one (.op .add [.var .local (ofString "l"), .const 0]),
          .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]]) =
        (none, copyPost))
    (hcopyLoc : copyPost.locals =
      (setVarHOLFinite (ofString "np") (.val (.word p)) {allocPost with locals :=
        (setVarHOLFinite (ofString "cap") (.val (.word cap))
          (setVarHOLFinite (ofString "n") (.val (.word n)) s)).locals}).locals)
    (hcd0 : copyPost.memaddrs l) (hcd8 : copyPost.memaddrs (l + 8#64))
    (hcd16 : copyPost.memaddrs (l + 16#64))
    (hne8 : l ≠ l + 8#64) (hne16 : l ≠ l + 16#64) :
    evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_lst_push) =
      (some (.returned (.val (.word (p + n * esz)))),
        {copyPost with
          locals := ((HolFiniteMapExact.empty.resVarEq
            (ofString "cap", s.locals.lookup (ofString "cap"))).resVarEq
            (ofString "n", s.locals.lookup (ofString "n"))),
          memory := fun a => if a = l + 8#64 then .word (n + 1#64)
            else if a = l + 16#64 then .word (cap * 2#64)
            else if a = l then .word p else copyPost.memory a}) := by
  let entry := setVarHOLFinite (ofString "cap") (.val (.word cap))
    (setVarHOLFinite (ofString "n") (.val (.word n)) s)
  have hcn : ofString "cap" ≠ ofString "n" := by decide
  have hce : ofString "cap" ≠ ofString "esz" := by decide
  have hne : ofString "n" ≠ ofString "esz" := by decide
  have hcl : ofString "cap" ≠ ofString "l" := by decide
  have hnl : ofString "n" ≠ ofString "l" := by decide
  have hnpl : ofString "np" ≠ ofString "l" := by decide
  have hnpe : ofString "np" ≠ ofString "esz" := by decide
  have hnpc : ofString "np" ≠ ofString "cap" := by decide
  have hnpn : ofString "np" ≠ ofString "n" := by decide
  have hel : entry.locals.lookup (ofString "l") = some (.val (.word l)) := by
    simp [entry, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hcl, hnl, hl]
  have hee : entry.locals.lookup (ofString "esz") = some (.val (.word esz)) := by
    simp [entry, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hce, hne, he]
  have hec : entry.locals.lookup (ofString "cap") = some (.val (.word cap)) := by
    simp [entry, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hen : entry.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [entry, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hcn]
  have hcl' : copyPost.locals.lookup (ofString "l") = some (.val (.word l)) := by
    rw [hcopyLoc]
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnpl, hcl, hnl, hl]
  have hce' : copyPost.locals.lookup (ofString "esz") = some (.val (.word esz)) := by
    rw [hcopyLoc]
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnpe, hce, hne, he]
  have hcc' : copyPost.locals.lookup (ofString "cap") = some (.val (.word cap)) := by
    rw [hcopyLoc]
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnpc]
  have hcn' : copyPost.locals.lookup (ofString "n") = some (.val (.word n)) := by
    rw [hcopyLoc]
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnpn, hcn]
  have hcp' : copyPost.locals.lookup (ofString "np") = some (.val (.word p)) := by
    rw [hcopyLoc]
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hbranch := lst_push_alloc_copy_header_exact_g09 entry allocPost copyPost l esz cap p
    hcode hee hec hclock halloc hcopy hcl' hcp' hcc' hcd0 hcd16
  have hrestore : ∀ nm : MlS, nm ≠ ofString "np" →
      (copyPost.locals.resVarEq (ofString "np", entry.locals.lookup (ofString "np"))).lookup nm =
        copyPost.locals.lookup nm := by
    intro nm hnm
    cases entry.locals.lookup (ofString "np") <;>
      simp [HolFiniteMapExact.lookup_resVarEq_none, HolFiniteMapExact.lookup_resVarEq_some,
        FDOMSUB_HOL, FUPDATE_HOL, hnm, Ne.symm hnm]
  have hres := lst_push_growth_of_branch_execution_g09 s _ l esz n cap p hl
    hd8 hd16 hm8 hm16 hge hbranch
    ((hrestore _ (Ne.symm hnpl)).trans hcl')
    ((hrestore _ (Ne.symm hnpe)).trans hce')
    ((hrestore _ (Ne.symm hnpn)).trans hcn') hcd0 hcd8
    (by simp [hne16]) hne8
  exact hres

/-- In a well-formed growing log list, all size computations are non-wrapping,
the doubled capacity accommodates the increment, and the insertion slot fits
inside the allocation. -/
theorem log_growth_word_bounds_g09 {n cap p q : BitVec 64}
    (hcap_pos : 1 ≤ cap.toNat) (hcap_bound : cap.toNat ≤ 31457280)
    (hlen : n.toNat ≤ cap.toNat) (hgrow : cap.toNat ≤ n.toNat)
    (hfit : p.toNat + (8#64 * cap * 2#64).toNat ≤ q.toNat) :
    n = cap ∧
    (cap * 2#64).toNat = cap.toNat * 2 ∧
    (8#64 * cap * 2#64).toNat = 16 * cap.toNat ∧
    (8#64 * n).toNat = 8 * n.toNat ∧
    (n + 1#64).toNat = n.toNat + 1 ∧
    n.toNat + 1 ≤ (cap * 2#64).toNat ∧
    (8#64 * n).toNat % 8 = 0 ∧
    (8#64 * n).toNat + 32 < 2 ^ 63 ∧
    p.toNat + (8#64 * n).toNat + 8 ≤ q.toNat ∧
    p.toNat + (8#64 * n).toNat ≤ 2 ^ 64 := by
  have hnc : n = cap := BitVec.eq_of_toNat_eq (by omega)
  subst n
  have h2 : (cap * 2#64).toNat = cap.toNat * 2 := by
    rw [BitVec.toNat_mul]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have h8 : (8#64 * cap).toNat = 8 * cap.toNat := by
    rw [BitVec.toNat_mul]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have h16 : (8#64 * cap * 2#64).toNat = 16 * cap.toNat := by
    rw [BitVec.toNat_mul, h8]; simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have h1 : (cap + 1#64).toNat = cap.toNat + 1 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hq := q.isLt
  rw [h16] at hfit
  refine ⟨rfl, h2, h16, h8, h1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h2]; omega
  · rw [h8]; omega
  · rw [h8]; omega
  · rw [h8]; omega
  · rw [h8]; omega

/-- Concrete growing `log_append`: the allocation/copy execution determines
the final buffer, capacity, length, insertion slot, and returned zero. -/
theorem log_append_growth_exact_g09 {F : Type}
    (s allocPost copyPost : PanSemStateFiniteExact 64 F) (e log l n cap p : BitVec 64)
    (hcode : s.code = originalRuntimeCode) (hclock : s.clock ≠ 0)
    (hpushclock : s.clock - 1 ≠ 0)
    (he : s.locals.lookup (ofString "e") = some (.val (.word e)))
    (hlg : s.locals.lookup (ofString "log") = some (.val (.word log)))
    (hde : s.memaddrs (e + 88#64)) (hme : s.memory (e + 88#64) = .word l)
    (hd8 : s.memaddrs (l + 8#64)) (hd16 : s.memaddrs (l + 16#64))
    (hm8 : s.memory (l + 8#64) = .word n)
    (hm16 : s.memory (l + 16#64) = .word cap)
    (hge : cap.toNat ≤ n.toNat) :
    let cal : HolFiniteMapExact MlS (ValueHOL 64) :=
      (HolFiniteMapExact.empty.update (ofString "l", .val (.word l))).update
        (ofString "esz", .val (.word 8#64))
    let entry := callEntryStateHOLFinite s cal
    let growEntry := setVarHOLFinite (ofString "cap") (.val (.word cap))
      (setVarHOLFinite (ofString "n") (.val (.word n)) entry)
    let copyEntry := setVarHOLFinite (ofString "np") (.val (.word p))
      {allocPost with locals := growEntry.locals}
    evaluateHOLFiniteState
      (callEntryStateHOLFinite growEntry (HolFiniteMapExact.empty.update
        (ofString "n", .val (.word (8#64 * cap * 2#64)))))
      (sourceFnBody Guest.Software.guestFn_alloc) =
        (some (.returned (.val (.word p))), allocPost) →
    evaluateHOLFiniteState copyEntry
      (.call (some (none, none)) (ofString "memcpy")
        [.var .local (ofString "np"), .load .one (.op .add [.var .local (ofString "l"), .const 0]),
          .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]]) =
        (none, copyPost) →
    copyPost.locals = copyEntry.locals →
    copyPost.memaddrs l → copyPost.memaddrs (l + 8#64) → copyPost.memaddrs (l + 16#64) →
    l ≠ l + 8#64 → l ≠ l + 16#64 → copyPost.memaddrs (p + n * 8#64) →
    evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_log_append) =
      (some (.returned (.val (.word 0))),
        {copyPost with
          locals := HolFiniteMapExact.empty.resVarEq (ofString "slot", s.locals.lookup (ofString "slot"))
          memory := fun a => if a = p + n * 8#64 then .word log
            else if a = l + 8#64 then .word (n + 1#64)
            else if a = l + 16#64 then .word (cap * 2#64)
            else if a = l then .word p else copyPost.memory a}) := by
  dsimp only
  intro halloc hcopy hlocals hd0' hd8' hd16' hne8 hne16 hdslot
  let cal : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "l", .val (.word l))).update
      (ofString "esz", .val (.word 8#64))
  let entry := callEntryStateHOLFinite s cal
  have hel : entry.locals.lookup (ofString "l") = some (.val (.word l)) := by
    have hne' : ofString "esz" ≠ ofString "l" := by decide
    simp [entry, cal, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne']
  have hez : entry.locals.lookup (ofString "esz") = some (.val (.word 8#64)) := by
    simp [entry, cal, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hpush := lst_push_growth_alloc_copy_exact_g09 entry allocPost copyPost l 8#64 n cap p
    hcode hel hez hd8 hd16 hm8 hm16 hge hpushclock halloc hcopy hlocals
    hd0' hd8' hd16' hne8 hne16
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.load .one (.op .add [.var .local (ofString "e"), .const 88]), .const 8] =
        some [.val (.word l), .val (.word 8#64)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, he, hde, hme,
      valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact]
  have hlook := pan_two_word_lookup s.code.lookup (ofString "lst_push")
    (ofString "l") (ofString "esz") (sourceFnBody Guest.Software.guestFn_lst_push)
    l 8#64 (by decide) (by rw [hcode]; exact lookup_lst_push_g09)
  exact log_append_of_lst_push_execution_g09 s _ _ cal (p + n * 8#64) log
    hlg hargs hlook hclock hpush hdslot

/-- The allocation and copy prefix of list growth preserves the full EVM
invariant while the fresh buffer is still detached from the list header. -/
theorem lst_push_alloc_copy_preserves_g09 {F : Type}
    (s allocPost copyPost : PanSemStateFiniteExact 64 F)
    (p q esz cap bytes : BitVec 64)
    (hInv : EvmInv s)
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hfit : p.toNat + (esz * cap * 2#64).toNat ≤ q.toNat)
    (hq : q.toNat ≤ heapLimit) (hq8 : q.toNat % 8 = 0)
    (halloc : evaluateHOLFiniteState
      (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update
        (ofString "n", .val (.word (esz * cap * 2#64)))))
      (sourceFnBody Guest.Software.guestFn_alloc) =
        (some (.returned (.val (.word p))), allocPost))
    (hg : allocPost.globals = s.globals.update (ofString "heap_ptr", .val (.word q)))
    (hm : allocPost.memory = s.memory)
    (hbytes : bytes.toNat ≤ (esz * cap * 2#64).toNat)
    (heff : ByteRegionEffect
      (setVarHOLFinite (ofString "np") (.val (.word p)) {allocPost with locals := s.locals})
      copyPost [(p.toNat, bytes.toNat)]) :
    EvmInv copyPost ∧ evmChain copyPost = evmChain s ∧ evmR copyPost = evmR s ∧
    (HeadMemAligned s → HeadMemAligned copyPost) ∧
    globN copyPost "heap_ptr" = q.toNat := by
  obtain ⟨S, Nd, hInvW⟩ := evmInvWith_of_evmInv hInv
  let entry := callEntryStateHOLFinite s (HolFiniteMapExact.empty.update
    (ofString "n", .val (.word (esz * cap * 2#64))))
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata entry
    (sourceFnBody Guest.Software.guestFn_alloc)
  have hbase := evaluate_baseAddr entry (sourceFnBody Guest.Software.guestFn_alloc)
  rw [halloc] at hmeta hbase
  dsimp only at hmeta hbase
  obtain ⟨hInvA, hwti, hfo, hchain, hR, hHM, hpNat, hqNat, hp8, hpLo, hw, hdj⟩ :=
    evmInvWith_of_alloc_pure (post := allocPost) hInvW hp hfit hq hq8
      hmeta.1 hmeta.2.1 hmeta.2.2.2.1 hbase hmeta.2.2.1 hg hm
  let copyEntry := setVarHOLFinite (ofString "np") (.val (.word p))
    {allocPost with locals := s.locals}
  have hlocalEff : ByteRegionEffect allocPost copyEntry [] :=
    (ByteRegionEffect.refl allocPost []).with_locals_clock copyEntry.locals allocPost.clock
  obtain ⟨hInvE, hwtiE, hfoE, _, hchainE, hRE, hHME⟩ :=
    evmInvWith_of_bre hInvA (fun _ hi _ _ => by simp at hi) hlocalEff
  have hdjCopy : IvlsDisj [(p.toNat, bytes.toNat)]
      (worldTypedIvls copyEntry S Nd ++ ((evmChain copyEntry).map (frameObjects copyEntry)).flatten) := by
    rw [hwtiE, hfoE]
    intro i hi j hj
    simp only [List.mem_singleton] at hi
    subst i
    have hfull : Disj (p.toNat, q.toNat - p.toNat) j :=
      hdj (p.toNat, q.toNat - p.toNat) (by simp) j hj
    rcases hfull with hzero | hzero | hleft | hright
    · exact Or.inl (by dsimp only at hzero ⊢; omega)
    · exact Or.inr (Or.inl hzero)
    · exact Or.inr (Or.inr (Or.inl (by dsimp only at hleft ⊢; omega)))
    · exact Or.inr (Or.inr (Or.inr hright))
  obtain ⟨hInvC, _, _, hgC, hchainC, hRC, hHMC⟩ := evmInvWith_of_bre hInvE hdjCopy heff
  exact ⟨evmInvWith_to_evmInv hInvC, hchainC.trans (hchainE.trans hchain),
    hRC.trans (hRE.trans hR), fun h => hHMC (hHME (hHM h)),
    (congrFun (globN_congr hgC) "heap_ptr").trans hqNat⟩

/-- Readback of the four final growth writes, with every copied prefix cell
preserved when it is disjoint from the header and insertion slot. -/
theorem log_growth_final_cells_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (l p n cap log : BitVec 64)
    (h08 : l ≠ l + 8#64) (h016 : l ≠ l + 16#64)
    (h816 : l + 8#64 ≠ l + 16#64)
    (hslot0 : p + n * 8#64 ≠ l)
    (hslot8 : p + n * 8#64 ≠ l + 8#64)
    (hslot16 : p + n * 8#64 ≠ l + 16#64)
    (hold : ∀ i : Nat, i < n.toNat →
      BitVec.ofNat 64 (p.toNat + 8 * i) ≠ p + n * 8#64 ∧
      BitVec.ofNat 64 (p.toNat + 8 * i) ≠ l + 8#64 ∧
      BitVec.ofNat 64 (p.toNat + 8 * i) ≠ l + 16#64 ∧
      BitVec.ofNat 64 (p.toNat + 8 * i) ≠ l) :
    let post := {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64)
      else if a = l + 16#64 then .word (cap * 2#64)
      else if a = l then .word p else s.memory a}
    memW post l.toNat = p.toNat ∧
    memW post (l + 8#64).toNat = (n + 1#64).toNat ∧
    memW post (l + 16#64).toNat = (cap * 2#64).toNat ∧
    memW post (p + n * 8#64).toNat = log.toNat ∧
    (∀ i : Nat, i < n.toNat → memW post (p.toNat + 8 * i) = memW s (p.toNat + 8 * i)) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [memW, Ne.symm hslot0, h08, h016]
  · simp only [memW, BitVec.ofNat_toNat]
    simp [Ne.symm hslot8]
  · simp only [memW, BitVec.ofNat_toNat]
    simp [Ne.symm hslot16, Ne.symm h816]
  · simp only [memW, BitVec.ofNat_toNat]
    simp
  · intro i hi
    obtain ⟨hs, h8, h16, h0⟩ := hold i hi
    simp [memW, hs, h8, h16, h0]

/-- Interval separation of the fresh buffer and list header discharges every
word-address inequality needed for final growth readback. -/
theorem log_growth_write_disjoint_g09 {l p n : BitVec 64}
    (hl : l.toNat + 24 ≤ 2 ^ 64)
    (hp : p.toNat + 8 * n.toNat + 8 ≤ 2 ^ 64)
    (hd : Disj (p.toNat, 8 * n.toNat + 8) (l.toNat, 24)) :
    l ≠ l + 8#64 ∧ l ≠ l + 16#64 ∧ l + 8#64 ≠ l + 16#64 ∧
    p + n * 8#64 ≠ l ∧ p + n * 8#64 ≠ l + 8#64 ∧
    p + n * 8#64 ≠ l + 16#64 ∧
    (∀ i : Nat, i < n.toNat →
      BitVec.ofNat 64 (p.toNat + 8 * i) ≠ p + n * 8#64 ∧
      BitVec.ofNat 64 (p.toNat + 8 * i) ≠ l + 8#64 ∧
      BitVec.ofNat 64 (p.toNat + 8 * i) ≠ l + 16#64 ∧
      BitVec.ofNat 64 (p.toNat + 8 * i) ≠ l) := by
  have hl8 : (l + 8#64).toNat = l.toNat + 8 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hl16 : (l + 16#64).toNat = l.toNat + 16 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hn8 : (n * 8#64).toNat = n.toNat * 8 := by
    rw [BitVec.toNat_mul]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hs : (p + n * 8#64).toNat = p.toNat + 8 * n.toNat := by
    rw [BitVec.toNat_add, hn8]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hsep : p.toNat + 8 * n.toNat + 8 ≤ l.toNat ∨
      l.toNat + 24 ≤ p.toNat := by
    rcases hd with hz | hz | hleft | hright
    · dsimp only at hz; omega
    · dsimp only at hz; omega
    · exact Or.inl hleft
    · exact Or.inr hright
  have hne : ∀ (a b : BitVec 64), a.toNat ≠ b.toNat → a ≠ b := by
    intro a b hab heq; exact hab (congrArg BitVec.toNat heq)
  refine ⟨hne _ _ (by rw [hl8]; omega), hne _ _ (by rw [hl16]; omega),
    hne _ _ (by rw [hl8, hl16]; omega), hne _ _ (by rw [hs]; omega),
    hne _ _ (by rw [hs, hl8]; omega), hne _ _ (by rw [hs, hl16]; omega), ?_⟩
  intro i hi
  have hiNat : (BitVec.ofNat 64 (p.toNat + 8 * i)).toNat = p.toNat + 8 * i := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact ⟨hne _ _ (by rw [hiNat, hs]; omega),
    hne _ _ (by rw [hiNat, hl8]; omega),
    hne _ _ (by rw [hiNat, hl16]; omega), hne _ _ (by rw [hiNat]; omega)⟩

/-- Fresh-allocation separation supplies final growth readback directly,
including natural-number length/capacity values and preservation of the copy. -/
theorem log_growth_readback_of_fresh_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (l p n cap q log : BitVec 64)
    (objects : List Ivl)
    (hheader : (l.toNat, 24) ∈ objects)
    (hfresh : IvlsDisj [(p.toNat, q.toNat - p.toNat)] objects)
    (hl : l.toNat + 24 ≤ 2 ^ 64)
    (hcap_pos : 1 ≤ cap.toNat) (hcap_bound : cap.toNat ≤ 31457280)
    (hlen : n.toNat ≤ cap.toNat) (hgrow : cap.toNat ≤ n.toNat)
    (hfit : p.toNat + (8#64 * cap * 2#64).toNat ≤ q.toNat) :
    let post := {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64)
      else if a = l + 16#64 then .word (cap * 2#64)
      else if a = l then .word p else s.memory a}
    memW post l.toNat = p.toNat ∧
    memW post (l + 8#64).toNat = n.toNat + 1 ∧
    memW post (l + 16#64).toNat = cap.toNat * 2 ∧
    n.toNat + 1 ≤ cap.toNat * 2 ∧
    memW post (p + n * 8#64).toNat = log.toNat ∧
    (∀ i : Nat, i < n.toNat → memW post (p.toNat + 8 * i) = memW s (p.toNat + 8 * i)) := by
  obtain ⟨hnc, hcap2, hsz, hn8, hn1, hcapacity, _, _, hslot, _⟩ :=
    log_growth_word_bounds_g09 hcap_pos hcap_bound hlen hgrow hfit
  have hslot' : p.toNat + 8 * n.toNat + 8 ≤ q.toNat := by
    rwa [hn8] at hslot
  have hdisj : Disj (p.toNat, 8 * n.toNat + 8) (l.toNat, 24) := by
    have hd := hfresh (p.toNat, q.toNat - p.toNat) (by simp) _ hheader
    rcases hd with hz | hz | hleft | hright
    · dsimp only at hz; omega
    · exact Or.inr (Or.inl hz)
    · exact Or.inr (Or.inr (Or.inl (by dsimp only at hleft ⊢; omega)))
    · exact Or.inr (Or.inr (Or.inr hright))
  have hq := q.isLt
  obtain ⟨h08, h016, h816, hs0, hs8, hs16, hold⟩ :=
    log_growth_write_disjoint_g09 hl (by omega) hdisj
  obtain ⟨h0, h8, h16, hstore, hprefix⟩ :=
    log_growth_final_cells_g09 s l p n cap log h08 h016 h816 hs0 hs8 hs16 hold
  exact ⟨h0, h8.trans hn1, h16.trans hcap2, hcap2 ▸ hcapacity, hstore, hprefix⟩

/-- Fresh-buffer readback closes the semantic log append postcondition after
growth, including all old records and their owned intervals. -/
theorem log_growth_post_of_fresh_g09 {F : Type}
    (s copy : PanSemStateFiniteExact 64 F) (ec : Ivl) (S : List Nat)
    (l p n cap q log : BitVec 64) (objects Rl : List Ivl)
    (hA : ArenaReady s) (hFW : FrameWF s S ec)
    (hl : memW s (ec.1 + 88) = l.toNat)
    (hn : memW s (l.toNat + 8) = n.toNat)
    (hheader : (l.toNat, 24) ∈ objects)
    (hfresh : IvlsDisj [(p.toNat, q.toNat - p.toNat)] objects)
    (hl_bound : l.toNat + 24 ≤ 2 ^ 64)
    (hcap_pos : 1 ≤ cap.toNat) (hcap_bound : cap.toNat ≤ 31457280)
    (hlen : n.toNat ≤ cap.toNat) (hgrow : cap.toNat ≤ n.toNat)
    (hfit : p.toNat + (8#64 * cap * 2#64).toNat ≤ q.toNat)
    (hcopy : ∀ i, i < n.toNat →
      memW copy (p.toNat + 8 * i) = memW s (memW s l.toNat + 8 * i)) :
    let post := {copy with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64)
      else if a = l + 16#64 then .word (cap * 2#64)
      else if a = l then .word p else copy.memory a}
    ByteRegionEffect s post Rl →
    globN s "heap_ptr" ≤ globN post "heap_ptr" →
    globN post "vm_system_address" = globN s "vm_system_address" →
    (∀ x ∈ Rl, ∀ i, i < n.toNat →
      Disj x (memW s (memW s l.toNat + 8 * i), 40)) →
    memW post (ec.1 + 88) = l.toNat →
    WordsOK post (l.toNat, 24) → Allocated post (l.toNat, 24) →
    (∀ i, i ≤ n.toNat → WordAt post (p.toNat + 8 * i)) →
    LogEntryOK post log.toNat →
    LogsListOK post (memW post (ec.1 + 88)) ∧
    frameLogObjects post ec = frameLogObjects s ec ++ logOwnedIvls post log.toNat := by
  dsimp only
  intro heff hheap hsys hdisj hframe hwords hallocated hslots hlog
  obtain ⟨h0, h8, h16, hcapacity, hstore, hprefix⟩ :=
    log_growth_readback_of_fresh_g09 copy l p n cap q log objects
      hheader hfresh hl_bound hcap_pos hcap_bound hlen hgrow hfit
  have hl8 : (l + 8#64).toNat = l.toNat + 8 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hl16 : (l + 16#64).toNat = l.toNat + 16 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hn8 : (n * 8#64).toNat = n.toNat * 8 := by
    rw [BitVec.toNat_mul]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hslot : (p + n * 8#64).toNat = p.toNat + 8 * n.toNat := by
    have hq := q.isLt
    obtain ⟨_, _, _, hmul, _, _, _, _, hbound, _⟩ :=
      log_growth_word_bounds_g09 hcap_pos hcap_bound hlen hgrow hfit
    rw [BitVec.toNat_add, hn8, Nat.mod_eq_of_lt (by rw [hmul] at hbound; omega)]
    omega
  rw [hl8] at h8
  rw [hl16] at h16
  rw [hslot] at hstore
  apply log_append_post_of_frame_effect_g09 hA hFW heff hheap hsys
  · simpa only [hl, hn] using hdisj
  · exact hframe.trans hl.symm
  · simpa only [hl] using hwords
  · simpa only [hl] using hallocated
  · simpa only [hl, hn] using h8
  · simpa only [hl, hn, h16] using hcapacity
  · intro i hi
    rw [hl, hn] at hi
    simp only [hl, h0]
    exact ⟨hslots i (Nat.le_of_lt hi), (hprefix i hi).trans (hcopy i hi)⟩
  · simpa only [hl, hn, h0] using hslots n.toNat (le_refl _)
  · simpa only [hl, hn, h0] using hstore
  · exact hlog

/-- The four finishing writes preserve any existing log record separated from
the list header and the fresh buffer, even across a heap-pointer change. -/
theorem log_growth_record_preserved_g09 {F : Type}
    (s copy : PanSemStateFiniteExact 64 F) (l p n cap newLog : BitVec 64) (oldLog : Nat)
    (hl : l.toNat + 24 ≤ 2 ^ 64)
    (hp : p.toNat + 8 * n.toNat + 8 ≤ 2 ^ 64)
    (hold : oldLog + 40 ≤ 2 ^ 64)
    (hdheader : Disj (oldLog, 40) (l.toNat, 24))
    (hdbuffer : Disj (oldLog, 40) (p.toNat, 8 * n.toNat + 8))
    (hdom : copy.memaddrs = s.memaddrs)
    (hheap : globN s "heap_ptr" ≤ globN copy "heap_ptr")
    (hsys : globN copy "vm_system_address" = globN s "vm_system_address")
    (hrecord : ∀ k ∈ ([0, 8, 16, 24, 32] : List Nat),
      memW copy (oldLog + k) = memW s (oldLog + k))
    (hok : LogEntryOK s oldLog) :
    let post := {copy with memory := fun a =>
      if a = p + n * 8#64 then .word newLog
      else if a = l + 8#64 then .word (n + 1#64)
      else if a = l + 16#64 then .word (cap * 2#64)
      else if a = l then .word p else copy.memory a}
    LogEntryOK post oldLog ∧ logOwnedIvls post oldLog = logOwnedIvls s oldLog := by
  dsimp only
  have hl8 : (l + 8#64).toNat = l.toNat + 8 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hl16 : (l + 16#64).toNat = l.toNat + 16 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hn8 : (n * 8#64).toNat = n.toNat * 8 := by
    rw [BitVec.toNat_mul]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hs : (p + n * 8#64).toNat = p.toNat + 8 * n.toNat := by
    rw [BitVec.toNat_add, hn8, Nat.mod_eq_of_lt (by omega)]; omega
  have hsepH : oldLog + 40 ≤ l.toNat ∨ l.toNat + 24 ≤ oldLog := by
    rcases hdheader with hz | hz | h | h
    · cases hz
    · cases hz
    · exact Or.inl h
    · exact Or.inr h
  have hsepB : oldLog + 40 ≤ p.toNat ∨ p.toNat + 8 * n.toNat + 8 ≤ oldLog := by
    rcases hdbuffer with hz | hz | h | h
    · cases hz
    · dsimp only at hz; omega
    · exact Or.inl h
    · exact Or.inr h
  have hagree : ∀ k ∈ ([0, 8, 16, 24, 32] : List Nat),
      memW {copy with memory := fun a =>
        if a = p + n * 8#64 then .word newLog
        else if a = l + 8#64 then .word (n + 1#64)
        else if a = l + 16#64 then .word (cap * 2#64)
        else if a = l then .word p else copy.memory a} (oldLog + k) = memW s (oldLog + k) := by
    intro k hk
    have hk32 : k ≤ 32 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
    have ha : (BitVec.ofNat 64 (oldLog + k)).toNat = oldLog + k := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hne : ∀ b : BitVec 64, oldLog + k ≠ b.toNat → BitVec.ofNat 64 (oldLog + k) ≠ b := by
      intro b hb heq; exact hb (ha.symm.trans (congrArg BitVec.toNat heq))
    have hns := hne (p + n * 8#64) (by rw [hs]; omega)
    have hn8' := hne (l + 8#64) (by rw [hl8]; omega)
    have hn16 := hne (l + 16#64) (by rw [hl16]; omega)
    have hn0 := hne l (by omega)
    exact (show _ = memW copy (oldLog + k) by simp [memW, hns, hn8', hn16, hn0]).trans (hrecord k hk)
  exact ⟨logEntryOK_of_record_agree_g09 hdom hheap hagree hok,
    logOwnedIvls_of_record_agree_g09 hsys hagree⟩

/-- Semantic growth append without a same-globals effect hypothesis: allocation
may increase the heap pointer while every existing record retains its ownership. -/
theorem log_growth_post_of_records_g09 {F : Type}
    (s copy : PanSemStateFiniteExact 64 F) (ec : Ivl)
    (l p n cap q log : BitVec 64) (objects : List Ivl)
    (hl : memW s (ec.1 + 88) = l.toNat)
    (hn : memW s (l.toNat + 8) = n.toNat)
    (hheader : (l.toNat, 24) ∈ objects)
    (hfresh : IvlsDisj [(p.toNat, q.toNat - p.toNat)] objects)
    (hl_bound : l.toNat + 24 ≤ 2 ^ 64)
    (hcap_pos : 1 ≤ cap.toNat) (hcap_bound : cap.toNat ≤ 31457280)
    (hlen : n.toNat ≤ cap.toNat) (hgrow : cap.toNat ≤ n.toNat)
    (hfit : p.toNat + (8#64 * cap * 2#64).toNat ≤ q.toNat)
    (hcopy : ∀ i, i < n.toNat →
      memW copy (p.toNat + 8 * i) = memW s (memW s l.toNat + 8 * i)) :
    let post := {copy with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64)
      else if a = l + 16#64 then .word (cap * 2#64)
      else if a = l then .word p else copy.memory a}
    memW post (ec.1 + 88) = l.toNat →
    WordsOK post (l.toNat, 24) → Allocated post (l.toNat, 24) →
    (∀ i, i ≤ n.toNat → WordAt post (p.toNat + 8 * i)) →
    (∀ i, i < n.toNat →
      LogEntryOK post (memW s (memW s l.toNat + 8 * i)) ∧
      logOwnedIvls post (memW s (memW s l.toNat + 8 * i)) =
        logOwnedIvls s (memW s (memW s l.toNat + 8 * i))) →
    LogEntryOK post log.toNat →
    LogsListOK post (memW post (ec.1 + 88)) ∧
    frameLogObjects post ec = frameLogObjects s ec ++ logOwnedIvls post log.toNat := by
  dsimp only
  intro hframe hwords hallocated hslots hrecords hlog
  obtain ⟨h0, h8, h16, hcapacity, hstore, hprefix⟩ :=
    log_growth_readback_of_fresh_g09 copy l p n cap q log objects
      hheader hfresh hl_bound hcap_pos hcap_bound hlen hgrow hfit
  have hl8 : (l + 8#64).toNat = l.toNat + 8 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hl16 : (l + 16#64).toNat = l.toNat + 16 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hn8 : (n * 8#64).toNat = n.toNat * 8 := by
    rw [BitVec.toNat_mul]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hslot : (p + n * 8#64).toNat = p.toNat + 8 * n.toNat := by
    have hq := q.isLt
    obtain ⟨_, _, _, hmul, _, _, _, _, hbound, _⟩ :=
      log_growth_word_bounds_g09 hcap_pos hcap_bound hlen hgrow hfit
    rw [BitVec.toNat_add, hn8, Nat.mod_eq_of_lt (by rw [hmul] at hbound; omega)]
    omega
  rw [hl8] at h8
  rw [hl16] at h16
  rw [hslot] at hstore
  constructor
  · rw [hframe]
    apply logsListOK_append_g09 (s := s) hwords hallocated
    · simpa only [hn] using h8
    · rw [hn]; omega
    · simpa only [hn, h16] using hcapacity
    · intro i hi
      rw [hn] at hi
      rw [h0]
      exact ⟨hslots i (Nat.le_of_lt hi), (hprefix i hi).trans (hcopy i hi), (hrecords i hi).1⟩
    · simpa only [h0, hn] using hslots n.toNat (le_refl _)
    · simpa only [h0, hn] using hstore
    · exact hlog
  · apply frameLogObjects_append_g09
    · exact hframe.trans hl.symm
    · simpa only [hl, hn] using h8
    · intro i hi
      rw [hl, hn] at hi
      simp only [hl, h0]
      rw [(hprefix i hi).trans (hcopy i hi)]
      exact (hrecords i hi).2
    · simpa only [hl, hn, h0] using hstore

/-- Fresh allocation and old-record separation suffice for semantic growth;
no preservation premise is imposed on the state after the finishing writes. -/
theorem log_growth_post_of_separated_records_g09 {F : Type}
    (s copy : PanSemStateFiniteExact 64 F) (ec : Ivl)
    (l p n cap q log : BitVec 64) (objects : List Ivl)
    (hl : memW s (ec.1 + 88) = l.toNat)
    (hn : memW s (l.toNat + 8) = n.toNat)
    (hheader : (l.toNat, 24) ∈ objects)
    (hfresh : IvlsDisj [(p.toNat, q.toNat - p.toNat)] objects)
    (hl_bound : l.toNat + 24 ≤ 2 ^ 64)
    (hcap_pos : 1 ≤ cap.toNat) (hcap_bound : cap.toNat ≤ 31457280)
    (hlen : n.toNat ≤ cap.toNat) (hgrow : cap.toNat ≤ n.toNat)
    (hfit : p.toNat + (8#64 * cap * 2#64).toNat ≤ q.toNat)
    (hcopy : ∀ i, i < n.toNat →
      memW copy (p.toNat + 8 * i) = memW s (memW s l.toNat + 8 * i))
    (hdom : copy.memaddrs = s.memaddrs)
    (hheap : globN s "heap_ptr" ≤ globN copy "heap_ptr")
    (hsys : globN copy "vm_system_address" = globN s "vm_system_address")
    (hrecords : ∀ i, i < n.toNat →
      let oldLog := memW s (memW s l.toNat + 8 * i)
      LogEntryOK s oldLog ∧ oldLog + 40 ≤ 2 ^ 64 ∧
      Disj (oldLog, 40) (l.toNat, 24) ∧
      Disj (oldLog, 40) (p.toNat, q.toNat - p.toNat) ∧
      ∀ k ∈ ([0, 8, 16, 24, 32] : List Nat),
        memW copy (oldLog + k) = memW s (oldLog + k)) :
    let post := {copy with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64)
      else if a = l + 16#64 then .word (cap * 2#64)
      else if a = l then .word p else copy.memory a}
    memW post (ec.1 + 88) = l.toNat →
    WordsOK post (l.toNat, 24) → Allocated post (l.toNat, 24) →
    (∀ i, i ≤ n.toNat → WordAt post (p.toNat + 8 * i)) →
    LogEntryOK post log.toNat →
    LogsListOK post (memW post (ec.1 + 88)) ∧
    frameLogObjects post ec = frameLogObjects s ec ++ logOwnedIvls post log.toNat := by
  dsimp only
  intro hframe hwords hallocated hslots hlog
  apply log_growth_post_of_records_g09 s copy ec l p n cap q log objects
    hl hn hheader hfresh hl_bound hcap_pos hcap_bound hlen hgrow hfit hcopy
    hframe hwords hallocated hslots
  · intro i hi
    obtain ⟨hok, hbound, hdH, hdB, hagree⟩ := hrecords i hi
    obtain ⟨_, _, _, hmul, _, _, _, _, hslot, _⟩ :=
      log_growth_word_bounds_g09 hcap_pos hcap_bound hlen hgrow hfit
    rw [hmul] at hslot
    have hq := q.isLt
    have hdB' : Disj (memW s (memW s l.toNat + 8 * i), 40)
        (p.toNat, 8 * n.toNat + 8) := by
      rcases hdB with hz | hz | hleft | hright
      · exact Or.inl hz
      · dsimp only at hz; omega
      · exact Or.inr (Or.inr (Or.inl hleft))
      · exact Or.inr (Or.inr (Or.inr (by dsimp only at hright ⊢; omega)))
    exact log_growth_record_preserved_g09 s copy l p n cap log _ hl_bound
      (by omega) hbound hdH hdB' hdom hheap hsys hagree hok
  · exact hlog

/-- Reinstall the structural frame invariant after changing a log list's backing
array, length and capacity. Existing frame fields and non-log buffers are kept. -/
theorem frameWF_of_log_growth_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} {ec : Ivl}
    (hFW : FrameWF s S ec)
    (hdom : post.memaddrs = s.memaddrs)
    (hscratch : globN post "scratch_ptr" = globN s "scratch_ptr")
    (hframe : globN post "frame_mem_ptr" = globN s "frame_mem_ptr")
    (hheap : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hempty : globN post "evm_empty" = globN s "evm_empty")
    (hfields : ∀ k ∈ ([8, 16, 24, 32, 40, 88, 112, 136, 144, 168, 176, 216, 232] : List Nat),
      memW post (ec.1 + k) = memW s (ec.1 + k))
    (hcapacity : 1 ≤ memW post (memW s (ec.1 + 88) + 16))
    (hlist : LogsListOK post (memW s (ec.1 + 88)))
    (hlen : memW post (memW s (ec.1 + 88) + 8) ≤
      memW post (memW s (ec.1 + 88) + 16))
    (hbuffer : Inside (frameLogs post ec) sourceBase (globN post "heap_ptr") ∨
      Inside (frameLogs post ec) (globN post "scratch_ptr") scratchEnd)
    (hwords : WordsOK post (frameLogs post ec))
    (hmsg : MsgOwned post S (memW s (ec.1 + 112))) :
    FrameWF post S ec := by
  have hwcongr : ∀ i, WordsOK post i ↔ WordsOK s i :=
    fun _ => wordsOK_congr_of_dom_g09 hdom
  have hret : frameRet post ec = frameRet s ec := by
    unfold frameRet
    rw [hfields 144 (by simp), hfields 216 (by simp)]
  unfold FrameWF at hFW ⊢
  dsimp only at hFW ⊢
  obtain ⟨hblocks, hmem, hmwords, hcap, hsp, hcapmax, hmemlen,
    ht1, ht2, ht3, _, _, _, _, hreturn, _, _⟩ := hFW
  simp only [hfields 8 (by simp), hfields 16 (by simp), hfields 24 (by simp),
    hfields 32 (by simp), hfields 40 (by simp), hfields 88 (by simp),
    hfields 112 (by simp), hfields 136 (by simp), hfields 144 (by simp),
    hfields 168 (by simp), hfields 176 (by simp), hfields 216 (by simp),
    hfields 232 (by simp)]
  refine ⟨?_, ?_, (hwcongr _).2 hmwords, hcap, hsp, hcapmax, hmemlen,
    ht1, ht2, ht3, hcapacity, hlen, hbuffer, hwords, ?_, hlist, hmsg⟩
  · intro i hi
    obtain ⟨hiB, hiW⟩ := hblocks i hi
    exact ⟨by rw [hscratch]; exact hiB, (hwcongr _).2 hiW⟩
  · rw [hframe]; exact hmem
  · rcases hreturn with hnull | ⟨hinside, hw⟩
    · exact Or.inl ⟨hnull.1, by rw [hempty]; exact hnull.2⟩
    · right
      rw [hret]
      exact ⟨⟨hinside.1, le_trans hinside.2 hheap⟩, (hwcongr _).2 hw⟩

/-- Allocation supplies both the complete doubled backing array and its insertion
slot; final memory writes do not invalidate the allocated word domain. -/
theorem log_growth_buffer_of_allocated_g09 {F : Type}
    (copy : PanSemStateFiniteExact 64 F) (ec : Ivl)
    (l p n cap q log : BitVec 64) (objects : List Ivl)
    (hheader : (l.toNat, 24) ∈ objects)
    (hfresh : IvlsDisj [(p.toNat, q.toNat - p.toNat)] objects)
    (hl_bound : l.toNat + 24 ≤ 2 ^ 64)
    (hcap_pos : 1 ≤ cap.toNat) (hcap_bound : cap.toNat ≤ 31457280)
    (hlen : n.toNat ≤ cap.toNat) (hgrow : cap.toNat ≤ n.toNat)
    (hfit : p.toNat + (8#64 * cap * 2#64).toNat ≤ q.toNat)
    (hwords : WordsOK copy (p.toNat, q.toNat - p.toNat))
    (hlo : sourceBase ≤ p.toNat)
    (hheap : q.toNat ≤ globN copy "heap_ptr") :
    let post := {copy with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64)
      else if a = l + 16#64 then .word (cap * 2#64)
      else if a = l then .word p else copy.memory a}
    memW post (ec.1 + 88) = l.toNat →
    Inside (frameLogs post ec) sourceBase (globN post "heap_ptr") ∧
    WordsOK post (frameLogs post ec) ∧
    (∀ i, i ≤ n.toNat → WordAt post (p.toNat + 8 * i)) := by
  dsimp only
  intro hec
  obtain ⟨h0, _, h16, _, _, _⟩ :=
    log_growth_readback_of_fresh_g09 copy l p n cap q log objects
      hheader hfresh hl_bound hcap_pos hcap_bound hlen hgrow hfit
  have hl16 : (l + 16#64).toNat = l.toNat + 16 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hl16] at h16
  obtain ⟨_, _, hsize, _, _, _, _, _, _, _⟩ :=
    log_growth_word_bounds_g09 hcap_pos hcap_bound hlen hgrow hfit
  rw [hsize] at hfit
  have hword : ∀ i, i < 2 * cap.toNat →
      WordAt {copy with memory := fun a =>
        if a = p + n * 8#64 then .word log
        else if a = l + 8#64 then .word (n + 1#64)
        else if a = l + 16#64 then .word (cap * 2#64)
        else if a = l then .word p else copy.memory a} (p.toNat + 8 * i) := by
    intro i hi
    have hb : i < (q.toNat - p.toNat) / 8 := by omega
    obtain ⟨_, hd, _⟩ := hwords.2.2 i hb
    unfold WordAt
    dsimp only
    cases hm : (if BitVec.ofNat 64 (p.toNat + 8 * i) = p + n * 8#64 then .word log
      else if BitVec.ofNat 64 (p.toNat + 8 * i) = l + 8#64 then .word (n + 1#64)
      else if BitVec.ofNat 64 (p.toNat + 8 * i) = l + 16#64 then .word (cap * 2#64)
      else if BitVec.ofNat 64 (p.toNat + 8 * i) = l then .word p
      else copy.memory (BitVec.ofNat 64 (p.toNat + 8 * i))) with
    | word w => exact ⟨w, hd, rfl⟩
  unfold frameLogs
  rw [hec, h0, h16]
  refine ⟨⟨hlo, ?_⟩, ⟨hwords.1, by omega, ?_⟩, ?_⟩
  · change p.toNat + 8 * (cap.toNat * 2) ≤ globN copy "heap_ptr"
    omega
  · intro i hi
    apply hword i
    omega
  · intro i hi
    apply hword i
    omega

/-- Complete local growth postcondition: valid list and backing array, exact
extension of owned logs, and preservation of the containing frame invariant. -/
theorem log_growth_frame_post_g09 {F : Type}
    (s copy : PanSemStateFiniteExact 64 F) (ec : Ivl) (S : List Nat)
    (l p n cap q log : BitVec 64) (objects : List Ivl)
    (hFW : FrameWF s S ec)
    (hl : memW s (ec.1 + 88) = l.toNat)
    (hn : memW s (l.toNat + 8) = n.toNat)
    (hheader : (l.toNat, 24) ∈ objects)
    (hfresh : IvlsDisj [(p.toNat, q.toNat - p.toNat)] objects)
    (hl_bound : l.toNat + 24 ≤ 2 ^ 64)
    (hcap_pos : 1 ≤ cap.toNat) (hcap_bound : cap.toNat ≤ 31457280)
    (hlen : n.toNat ≤ cap.toNat) (hgrow : cap.toNat ≤ n.toNat)
    (hfit : p.toNat + (8#64 * cap * 2#64).toNat ≤ q.toNat)
    (hcopy : ∀ i, i < n.toNat →
      memW copy (p.toNat + 8 * i) = memW s (memW s l.toNat + 8 * i))
    (hdom : copy.memaddrs = s.memaddrs)
    (hheap : globN s "heap_ptr" ≤ globN copy "heap_ptr")
    (hsys : globN copy "vm_system_address" = globN s "vm_system_address")
    (hscratch : globN copy "scratch_ptr" = globN s "scratch_ptr")
    (hframe : globN copy "frame_mem_ptr" = globN s "frame_mem_ptr")
    (hempty : globN copy "evm_empty" = globN s "evm_empty")
    (hwords : WordsOK copy (p.toNat, q.toNat - p.toNat))
    (hlo : sourceBase ≤ p.toNat) (hq : q.toNat ≤ globN copy "heap_ptr")
    (hrecords : ∀ i, i < n.toNat →
      let oldLog := memW s (memW s l.toNat + 8 * i)
      LogEntryOK s oldLog ∧ oldLog + 40 ≤ 2 ^ 64 ∧
      Disj (oldLog, 40) (l.toNat, 24) ∧
      Disj (oldLog, 40) (p.toNat, q.toNat - p.toNat) ∧
      ∀ k ∈ ([0, 8, 16, 24, 32] : List Nat),
        memW copy (oldLog + k) = memW s (oldLog + k)) :
    let post := {copy with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64)
      else if a = l + 16#64 then .word (cap * 2#64)
      else if a = l then .word p else copy.memory a}
    (∀ k ∈ ([8, 16, 24, 32, 40, 88, 112, 136, 144, 168, 176, 216, 232] : List Nat),
      memW post (ec.1 + k) = memW s (ec.1 + k)) →
    WordsOK post (l.toNat, 24) → Allocated post (l.toNat, 24) →
    MsgOwned post S (memW s (ec.1 + 112)) → LogEntryOK post log.toNat →
    FrameWF post S ec ∧ LogsListOK post (memW post (ec.1 + 88)) ∧
    frameLogObjects post ec = frameLogObjects s ec ++ logOwnedIvls post log.toNat := by
  dsimp only
  intro hfields hheaderWords hallocated hmsg hlog
  have hec := (hfields 88 (by simp)).trans hl
  obtain ⟨hbuffer, hbufferWords, hslots⟩ := log_growth_buffer_of_allocated_g09
    copy ec l p n cap q log objects hheader hfresh hl_bound hcap_pos hcap_bound
    hlen hgrow hfit hwords hlo hq hec
  obtain ⟨hlist, howned⟩ := log_growth_post_of_separated_records_g09
    s copy ec l p n cap q log objects hl hn hheader hfresh hl_bound
    hcap_pos hcap_bound hlen hgrow hfit hcopy hdom hheap hsys hrecords
    hec hheaderWords hallocated hslots hlog
  refine ⟨?_, hlist, howned⟩
  refine frameWF_of_log_growth_g09 hFW ?_ ?_ ?_ ?_ ?_ hfields ?_ ?_ ?_ ?_ ?_ ?_
  · exact hdom
  · exact hscratch
  · exact hframe
  · exact hheap
  · exact hempty
  · obtain ⟨_, _, h16, hcap, _, _⟩ := log_growth_readback_of_fresh_g09
      copy l p n cap q log objects hheader hfresh hl_bound hcap_pos hcap_bound hlen hgrow hfit
    have hl16 : (l + 16#64).toNat = l.toNat + 16 := by
      rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hl, ← hl16, h16]
    omega
  · simpa only [hec, hl] using hlist
  · obtain ⟨_, h8, h16, hcap, _, _⟩ := log_growth_readback_of_fresh_g09
      copy l p n cap q log objects hheader hfresh hl_bound hcap_pos hcap_bound hlen hgrow hfit
    have hl8 : (l + 8#64).toNat = l.toNat + 8 := by
      rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have hl16 : (l + 16#64).toNat = l.toNat + 16 := by
      rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hl, ← hl8, ← hl16, h8, h16]
    exact hcap
  · exact Or.inl hbuffer
  · exact hbufferWords
  · exact hmsg

/-- Existing log records are valid, bounded, and separated from the list header
by the frame's object-disjointness invariant. -/
theorem log_records_of_frame_pairwise_g09 {F : Type}
    {s : PanSemStateFiniteExact 64 F} {ec : Ivl} {S : List Nat}
    (hFW : FrameWF s S ec)
    (hpw : (frameObjects s ec).Pairwise Disj)
    (hheap : globN s "heap_ptr" ≤ 2 ^ 64)
    (hnonnull : memW s (ec.1 + 88) ≠ 0) :
    ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      let oldLog := memW s (memW s (memW s (ec.1 + 88)) + 8 * i)
      LogEntryOK s oldLog ∧ oldLog + 40 ≤ 2 ^ 64 ∧
        Disj (oldLog, 40) (memW s (ec.1 + 88), 24) := by
  intro i hi oldLog
  have hlogs := hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rcases hlogs with hz | ⟨_, _, _, _, hentries⟩
  · exact False.elim (hnonnull hz)
  have hentry := (hentries i hi).2
  refine ⟨hentry, le_trans hentry.2.1.2 hheap, ?_⟩
  unfold frameObjects at hpw
  have hp0 := (List.pairwise_cons.1 hpw).2
  have hp1 := (List.pairwise_cons.1 hp0).2
  have hp2 := (List.pairwise_cons.1 hp1).2
  have hp3 := (List.pairwise_cons.1 hp2).2
  have hh := (List.pairwise_cons.1 hp3).1
  apply R11Shards.Disj.symm
  apply hh (oldLog, 40)
  apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem
  unfold frameLogObjects
  apply List.mem_flatMap.2
  refine ⟨i, List.mem_range.2 hi, ?_⟩
  exact List.mem_filter.2 ⟨by simp [logRecordIvls, oldLog], by simp⟩

/-- Replacing the backing array and appending separated log-owned intervals
preserves pairwise disjointness of the frame's objects. -/
theorem log_growth_objects_pairwise_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {ec : Ivl} {log : Nat}
    (before after : List Ivl)
    (hold : frameObjects s ec = before ++ frameLogs s ec :: after)
    (hpost : frameObjects post ec =
      (before ++ frameLogs post ec :: after) ++ logOwnedIvls post log)
    (hpw : (frameObjects s ec).Pairwise Disj)
    (hbuffer : ∀ o ∈ frameObjects s ec, Disj (frameLogs post ec) o)
    (hnew_pw : (logOwnedIvls post log).Pairwise Disj)
    (hnew_old : ∀ n ∈ logOwnedIvls post log, ∀ o ∈ frameObjects s ec, Disj n o)
    (hnew_buffer : ∀ n ∈ logOwnedIvls post log, Disj n (frameLogs post ec)) :
    (frameObjects post ec).Pairwise Disj := by
  rw [hold, List.pairwise_append] at hpw
  rw [hpost, List.pairwise_append]
  have hmem_before : ∀ o ∈ before, o ∈ frameObjects s ec := by
    intro o ho; rw [hold]; exact List.mem_append_left _ ho
  have hmem_after : ∀ o ∈ after, o ∈ frameObjects s ec := by
    intro o ho; rw [hold]; exact List.mem_append_right _ (List.mem_cons_of_mem _ ho)
  refine ⟨?_, hnew_pw, ?_⟩
  · rw [List.pairwise_append, List.pairwise_cons]
    refine ⟨hpw.1, ⟨?_, (List.pairwise_cons.1 hpw.2.1).2⟩, ?_⟩
    · intro o ho; exact hbuffer o (hmem_after o ho)
    · intro o ho x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact R11Shards.Disj.symm (hbuffer o (hmem_before o ho))
      · exact hpw.2.2 o ho x (List.mem_cons_of_mem _ hx)
  · intro o ho n hn
    apply R11Shards.Disj.symm
    rcases List.mem_append.1 ho with ho | ho
    · exact hnew_old n hn o (hmem_before o ho)
    · rcases List.mem_cons.1 ho with rfl | ho
      · exact hnew_buffer n hn
      · exact hnew_old n hn o (hmem_after o ho)

/-- Concrete frame-layout specialization of growth object disjointness. -/
theorem log_growth_frame_objects_pairwise_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {ec : Ivl} {log : Nat}
    (hfields : ∀ k ∈ ([8, 24, 40, 88, 232] : List Nat),
      memW post (ec.1 + k) = memW s (ec.1 + k))
    (hret : frameRet post ec = frameRet s ec)
    (hlogs : frameLogObjects post ec = frameLogObjects s ec ++ logOwnedIvls post log)
    (hpw : (frameObjects s ec).Pairwise Disj)
    (hbuffer : ∀ o ∈ frameObjects s ec, Disj (frameLogs post ec) o)
    (hnew_pw : (logOwnedIvls post log).Pairwise Disj)
    (hnew_old : ∀ n ∈ logOwnedIvls post log, ∀ o ∈ frameObjects s ec, Disj n o)
    (hnew_buffer : ∀ n ∈ logOwnedIvls post log, Disj n (frameLogs post ec)) :
    (frameObjects post ec).Pairwise Disj := by
  apply log_growth_objects_pairwise_g09
    [(ec.1, 280), (ec.2, 104), (memW s (ec.1 + 8), 32 * memW s (ec.1 + 232)),
      (memW s (ec.1 + 24), memW s (ec.1 + 40)), (memW s (ec.1 + 88), 24)]
    (frameRet s ec :: frameLogObjects s ec)
    (by simp [frameObjects]) ?_ hpw hbuffer hnew_pw hnew_old hnew_buffer
  simpa only [List.cons_append, List.nil_append, List.append_assoc] using
    frameObjects_of_log_append_g09 hfields hret hlogs

/-- Lift head-frame growth disjointness across an unchanged suspended chain. -/
theorem log_growth_chain_objects_pairwise_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {head : Ivl} {tail : List Ivl}
    (hchain : evmChain s = head :: tail)
    (hchain_post : evmChain post = evmChain s)
    (hpw : ((evmChain s).map (frameObjects s)).flatten.Pairwise Disj)
    (hhead_pw : (frameObjects post head).Pairwise Disj)
    (htail : ∀ ec ∈ tail, frameObjects post ec = frameObjects s ec)
    (hhead_cases : ∀ o ∈ frameObjects post head,
      o ∈ frameObjects s head ∨ ∀ ec ∈ tail, ∀ other ∈ frameObjects s ec, Disj o other) :
    ((evmChain post).map (frameObjects post)).flatten.Pairwise Disj := by
  have htail_eq : tail.map (frameObjects post) = tail.map (frameObjects s) :=
    List.map_congr_left htail
  rw [hchain, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
  rw [hchain_post, hchain, List.map_cons, List.flatten_cons, htail_eq,
    List.pairwise_append]
  refine ⟨hhead_pw, hpw.2.1, ?_⟩
  intro o ho other hother
  rcases hhead_cases o ho with hold | hfresh
  · exact hpw.2.2 o hold other hother
  · obtain ⟨objects, hobjects, hother⟩ := List.mem_flatten.1 hother
    obtain ⟨ec, hec, rfl⟩ := List.mem_map.1 hobjects
    exact hfresh ec hec other hother

/-- Log growth changes only the active frame's objects; release marks refer to
surviving ancestors, so unchanged suspended objects preserve every mark. -/
theorem marksOK_of_head_log_growth_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hmarks : MarksOK s S (evmChain s))
    (hfields : ∀ ec ∈ evmChain s, ∀ k, k + 8 ≤ 280 → k % 8 = 0 →
      memW post (ec.1 + k) = memW s (ec.1 + k))
    (hcont : ∀ ec ∈ evmChain s, ∀ k, k + 8 ≤ 104 → k % 8 = 0 →
      memW post (ec.2 + k) = memW s (ec.2 + k))
    (hfixed : fixedObjects post = fixedObjects s)
    (hrefs : worldTableRefs post S = worldTableRefs s S)
    (hfoot : ∀ t ∈ S, htabFootprint post t = htabFootprint s t)
    (hobjects : ∀ ec ∈ (evmChain s).tail, frameObjects post ec = frameObjects s ec)
    (hlogs : ∀ ec ∈ (evmChain s).tail, frameLogs post ec = frameLogs s ec) :
    MarksOK post S (evmChain s) := by
  have hscratch : ∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec := by
    intro ec hec
    unfold frameScratch
    rw [hfields ec hec 8 (by omega) (by omega),
      hfields ec hec 232 (by omega) (by omega), hfields ec hec 88 (by omega) (by omega)]
  have hdel : ∀ i t, DelExclusive post S (evmChain s) i t ↔
      DelExclusive s S (evmChain s) i t := by
    intro i t
    unfold DelExclusive
    rw [hrefs]
    refine and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun hj =>
      forall_congr' fun k => imp_congr_right fun _ => ?_)
    have hk : k + 8 ≤ 280 ∧ k % 8 = 0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ‹k ∈ [136, 168, 176]›
      rcases ‹k = 136 ∨ k = 168 ∨ k = 176› with rfl | rfl | rfl <;> omega
    rw [hfields _ (List.getElem_mem hj) k hk.1 hk.2]
  intro i hi
  have himem : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
  have htake : ((evmChain s).take (i + 1)).map (fun ec => memW post (ec.1 + 136)) =
      ((evmChain s).take (i + 1)).map (fun ec => memW s (ec.1 + 136)) := by
    apply List.map_congr_left
    intro ec hec
    exact hfields ec (List.mem_of_mem_take hec) 136 (by omega) (by omega)
  dsimp only
  rw [hcont _ himem 48 (by omega) (by omega), hcont _ himem 56 (by omega) (by omega),
    hfields _ himem 24 (by omega) (by omega),
    hscratch _ himem, hfixed, htake]
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hmarks i hi
  refine ⟨m1, m2, m3, m4, ?_, m6, m7, ?_, m9⟩
  · intro j hj hij
    have hjmem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
    have hjtail : (evmChain s)[j] ∈ (evmChain s).tail := by
      have ht : j - 1 < (evmChain s).tail.length := by
        simp only [List.length_tail]
        omega
      have he : (evmChain s).tail[j - 1] = (evmChain s)[j] := by
        rw [List.getElem_tail]
        congr 1
        omega
      exact he ▸ List.getElem_mem ht
    rw [hscratch _ hjmem, hobjects _ hjtail, hlogs _ hjtail,
      hfields _ hjmem 112 (by omega) (by omega)]
    exact m5 j hj hij
  · intro t ht
    rw [hfoot t ht, hdel i t]
    exact m8 t ht

/-- Reconstruct the complete exposed EVM invariant after active-frame log growth.
Frame records and world references are unchanged; only the active log objects
need new well-formedness and separation proofs. -/
theorem evmInvAt_of_head_log_growth_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hinv : EvmInvAt s S)
    (hworld : WorldTyped post S)
    (hchain : evmChain post = evmChain s)
    (hfields : ∀ ec ∈ evmChain s, ∀ k, k + 8 ≤ 280 → k % 8 = 0 →
      memW post (ec.1 + k) = memW s (ec.1 + k))
    (hcont : ∀ ec ∈ evmChain s, ∀ k, k + 8 ≤ 104 → k % 8 = 0 →
      memW post (ec.2 + k) = memW s (ec.2 + k))
    (hframes : ∀ ec ∈ evmChain s, FrameWF post S ec)
    (hpairwise : ((evmChain post).map (frameObjects post)).flatten.Pairwise Disj)
    (hseparation : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects post ec,
      (∀ t ∈ S, ∀ i ∈ htabFootprint post t, Disj o i) ∧
        ∀ j ∈ fixedObjects post, Disj o j)
    (htries : AvoidsTries post S ((evmChain post).map (frameObjects post)).flatten)
    (hfixed : fixedObjects post = fixedObjects s)
    (hrefs : worldTableRefs post S = worldTableRefs s S)
    (hfoot : ∀ t ∈ S, htabFootprint post t = htabFootprint s t)
    (hobjects : ∀ ec ∈ (evmChain s).tail, frameObjects post ec = frameObjects s ec)
    (hlogs : ∀ ec ∈ (evmChain s).tail, frameLogs post ec = frameLogs s ec)
    (hworldRoles : worldRoleSlots post = worldRoleSlots s)
    (hjournalRoles : journalRoleSlots post = journalRoleSlots s)
    (hkind : ∀ t ∈ S, memW post t = memW s t) :
    EvmInvAt post S := by
  obtain ⟨_, hne, hlength, hlast, _, hroom, hwindows, _, _, _, hmarks, hroles, hgas⟩ := hinv
  have hframeRoles : frameRoleSlots post (evmChain s) = frameRoleSlots s (evmChain s) := by
    unfold frameRoleSlots
    apply List.flatMap_congr
    intro ec hec
    rw [hfields ec hec 136 (by omega) (by omega), hfields ec hec 168 (by omega) (by omega),
      hfields ec hec 176 (by omega) (by omega)]
  refine ⟨hworld, ?_⟩
  dsimp only
  rw [hchain]
  refine ⟨hne, hlength, ?_, hframes, ?_, ?_, ?_, hseparation, ?_, ?_, ?_, ?_⟩
  · obtain ⟨ec, hec, hk⟩ := hlast
    exact ⟨ec, hec, by rw [hcont ec (List.mem_of_mem_getLast? hec) 16 (by omega) (by omega)]; exact hk⟩
  · intro ec hec
    unfold FrameRoom
    rw [hfields ec (List.mem_of_mem_tail hec) 16 (by omega) (by omega),
      hfields ec (List.mem_of_mem_tail hec) 232 (by omega) (by omega)]
    exact hroom ec hec
  · intro i hi
    rw [hcont _ (List.getElem_mem (by omega)) 80 (by omega) (by omega),
      hcont _ (List.getElem_mem (by omega)) 72 (by omega) (by omega),
      hfields _ (List.getElem_mem (by omega)) 40 (by omega) (by omega)]
    exact hwindows i hi
  · simpa only [hchain] using hpairwise
  · simpa only [hchain] using htries
  · exact marksOK_of_head_log_growth_g09 hmarks hfields hcont hfixed hrefs hfoot hobjects hlogs
  · rw [hworldRoles, hjournalRoles, hframeRoles]
    unfold RolesOK at hroles ⊢
    refine ⟨?_, hroles.2⟩
    intro a ha
    obtain ⟨haS, haKind⟩ := hroles.1 a ha
    exact ⟨haS, by simpa only [hdr, Nat.mul_zero, Nat.add_zero, hkind a.1 haS] using haKind⟩
  · have hsum : (evmChain s).map (fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)) =
        (evmChain s).map (fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)) := by
      apply List.map_congr_left
      intro ec hec
      rw [hfields ec hec 64 (by omega) (by omega), hfields ec hec 192 (by omega) (by omega)]
    rw [hsum]
    exact hgas

/-- Typed-cell preservation supplies all world and role readback facts used in
log-growth reconstruction, while permitting allocation to advance the heap. -/
theorem log_growth_world_preserved_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hWT : WorldTypedWith s S Nd)
    (hheap : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hscratch : globN post "scratch_ptr" ≤ globN s "scratch_ptr")
    (hglobals : ∀ g, ofString g ≠ ofString "heap_ptr" →
      ofString g ≠ ofString "scratch_ptr" → ofString g ≠ ofString "frame_mem_ptr" →
      globN post g = globN s g)
    (hcell : SameTypedCells s post S Nd) :
    WorldTyped post S ∧ TriesTypedWith post S Nd ∧
    worldTypedIvls post S Nd = worldTypedIvls s S Nd ∧
    fixedObjects post = fixedObjects s ∧
    worldTableRefs post S = worldTableRefs s S ∧
    (∀ t ∈ S, htabFootprint post t = htabFootprint s t) ∧
    worldRoleSlots post = worldRoleSlots s ∧
    journalRoleSlots post = journalRoleSlots s ∧
    (∀ t ∈ S, memW post t = memW s t) := by
  have hcore : ∀ g ∈ coreWorldGlobals, globN post g = globN s g := by
    intro g hg
    have hne : ofString g ≠ ofString "heap_ptr" ∧
        ofString g ≠ ofString "scratch_ptr" ∧ ofString g ≠ ofString "frame_mem_ptr" := by
      revert g hg
      decide
    exact hglobals g hne.1 hne.2.1 hne.2.2
  have hfixed : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [blockOutObjects_eq hAs.2 hWT.2.2.1 hcell (hcore "bo" (by decide)),
      balObjects_eq hAs.2 hWT.1 hWT.2.2.1 hcell (hcore "bal_accounts" (by decide)),
      hcore "journal" (by decide), hcore "journal_cap" (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne : ofString gn.1 ≠ ofString "heap_ptr" ∧
        ofString gn.1 ≠ ofString "scratch_ptr" ∧ ofString gn.1 ≠ ofString "frame_mem_ptr" := by
      revert gn hgn
      decide
    rw [hglobals gn.1 hne.1 hne.2.1 hne.2.2]
  have hFT := fixedTyped_of_eq hAp hWT.2.2.1 hheap hscratch hfixed
  obtain ⟨hpost, _⟩ := worldTypedWith_congr_w1 hAs hAp hheap hscratch hcore hcell hWT
    ⟨hFT, fun o ho => Or.inl (by rw [← hfixed]; exact ho)⟩
  refine ⟨⟨hpost.1, hpost.2.1, hpost.2.2.1, Nd, hpost.2.2.2⟩,
    hpost.2.2.2, worldTypedIvls_eq_of_cell_g09 hAs.2 hWT hcell hglobals, hfixed,
    worldTableRefs_eq_of_cell_g09 hAs.2 hWT hcell hcore,
    fun t ht => htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1,
    worldRoleSlots_eq hAs.2 hWT.1 hWT.2.2.1 hcell hcore,
    journalRoleSlots_eq hAs.2 hWT.2.1 hWT.2.2.1 hcell hcore, ?_⟩
  intro t ht
  have hb := ((hWT.1.2.1 t ht).1.1 (t, 88) (by simp [htabFootprint])).1
  simpa only [hdr, Nat.mul_zero, Nat.add_zero] using htab_hdr_eq hcell ht hb 0 (by omega)

/-- The concrete finishing writes leave every word of a separated object intact.
This applies uniformly to active/suspended frame records and world objects. -/
theorem log_growth_protected_words_g09 {F : Type}
    (copy : PanSemStateFiniteExact 64 F) (l p n cap log : BitVec 64) (o : Ivl)
    (hl : l.toNat + 24 ≤ 2 ^ 64)
    (hp : p.toNat + 8 * n.toNat + 8 ≤ 2 ^ 64)
    (ho : o.1 + o.2 ≤ 2 ^ 64)
    (hdheader : Disj o (l.toNat, 24))
    (hdbuffer : Disj o (p.toNat, 8 * n.toNat + 8)) :
    let post := {copy with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64)
      else if a = l + 16#64 then .word (cap * 2#64)
      else if a = l then .word p else copy.memory a}
    ∀ k, k + 8 ≤ o.2 → memW post (o.1 + k) = memW copy (o.1 + k) := by
  dsimp only
  intro k hk
  have hl8 : (l + 8#64).toNat = l.toNat + 8 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hl16 : (l + 16#64).toNat = l.toNat + 16 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hn8 : (n * 8#64).toNat = n.toNat * 8 := by
    rw [BitVec.toNat_mul]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hs : (p + n * 8#64).toNat = p.toNat + 8 * n.toNat := by
    rw [BitVec.toNat_add, hn8, Nat.mod_eq_of_lt (by omega)]; omega
  have hsepH : o.1 + o.2 ≤ l.toNat ∨ l.toNat + 24 ≤ o.1 := by
    rcases hdheader with hz | hz | h | h
    · omega
    · cases hz
    · exact Or.inl h
    · exact Or.inr h
  have hsepB : o.1 + o.2 ≤ p.toNat ∨ p.toNat + 8 * n.toNat + 8 ≤ o.1 := by
    rcases hdbuffer with hz | hz | h | h
    · omega
    · dsimp only at hz; omega
    · exact Or.inl h
    · exact Or.inr h
  have ha : (BitVec.ofNat 64 (o.1 + k)).toNat = o.1 + k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hne : ∀ b : BitVec 64, o.1 + k ≠ b.toNat → BitVec.ofNat 64 (o.1 + k) ≠ b := by
    intro b hb heq; exact hb (ha.symm.trans (congrArg BitVec.toNat heq))
  have hns := hne (p + n * 8#64) (by rw [hs]; omega)
  have hn8' := hne (l + 8#64) (by rw [hl8]; omega)
  have hn16 := hne (l + 16#64) (by rw [hl16]; omega)
  have hn0 := hne l (by omega)
  simp [memW, hns, hn8', hn16, hn0]

/-- A single old-world separation fact supplies both reconstructed frame/world
separation and trie avoidance after the typed cells have been preserved. -/
theorem log_growth_world_separation_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {objects : List Ivl}
    (hWT : WorldTypedWith s S Nd)
    (hcell : SameTypedCells s post S Nd)
    (htries : TriesTypedWith post S Nd)
    (hfixed : fixedObjects post = fixedObjects s)
    (hfoot : ∀ t ∈ S, htabFootprint post t = htabFootprint s t)
    (hdisj : IvlsDisj objects (worldOwned s S Nd)) :
    (∀ o ∈ objects, (∀ t ∈ S, ∀ i ∈ htabFootprint post t, Disj o i) ∧
      ∀ j ∈ fixedObjects post, Disj o j) ∧ AvoidsTries post S objects := by
  have hnodes := nodeExtents_eq hWT.2.2.2.1 hcell
  constructor
  · intro o ho
    constructor
    · intro t ht i hi
      rw [hfoot t ht] at hi
      exact hdisj o ho i (by
        unfold worldOwned
        exact List.mem_append_left _ (List.mem_append_left _
          (List.mem_flatMap.2 ⟨t, ht, hi⟩)))
    · intro j hj
      rw [hfixed] at hj
      exact hdisj o ho j (by
        unfold worldOwned
        exact List.mem_append_left _ (List.mem_append_right _ hj))
  · refine ⟨Nd, htries, ?_⟩
    intro o ho j hj
    rw [hnodes] at hj
    exact hdisj o ho j (by
      unfold worldOwned
      exact List.mem_append_right _ hj)

/-- Assemble log-growth invariant reconstruction from typed-cell preservation
and separation against the pre-growth world. All world readbacks are derived. -/
theorem evmInvAt_of_log_growth_cells_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hinv : EvmInvAt s S) (hWT : WorldTypedWith s S Nd)
    (hheap : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hscratch : globN post "scratch_ptr" ≤ globN s "scratch_ptr")
    (hglobals : ∀ g, ofString g ≠ ofString "heap_ptr" →
      ofString g ≠ ofString "scratch_ptr" → ofString g ≠ ofString "frame_mem_ptr" →
      globN post g = globN s g)
    (hcell : SameTypedCells s post S Nd)
    (hchain : evmChain post = evmChain s)
    (hfields : ∀ ec ∈ evmChain s, ∀ k, k + 8 ≤ 280 → k % 8 = 0 →
      memW post (ec.1 + k) = memW s (ec.1 + k))
    (hcont : ∀ ec ∈ evmChain s, ∀ k, k + 8 ≤ 104 → k % 8 = 0 →
      memW post (ec.2 + k) = memW s (ec.2 + k))
    (hframes : ∀ ec ∈ evmChain s, FrameWF post S ec)
    (hpairwise : ((evmChain post).map (frameObjects post)).flatten.Pairwise Disj)
    (hdisj : IvlsDisj ((evmChain post).map (frameObjects post)).flatten (worldOwned s S Nd))
    (hobjects : ∀ ec ∈ (evmChain s).tail, frameObjects post ec = frameObjects s ec)
    (hlogs : ∀ ec ∈ (evmChain s).tail, frameLogs post ec = frameLogs s ec) :
    EvmInvAt post S := by
  obtain ⟨hworld, htries, _, hfixed, hrefs, hfoot, hroles, hjroles, hkind⟩ :=
    log_growth_world_preserved_g09 hAs hAp hWT hheap hscratch hglobals hcell
  obtain ⟨hseparation, havoids⟩ :=
    log_growth_world_separation_g09 hWT hcell htries hfixed hfoot hdisj
  apply evmInvAt_of_head_log_growth_g09 hinv hworld hchain hfields hcont hframes
    hpairwise ?_ havoids hfixed hrefs hfoot hobjects hlogs hroles hjroles hkind
  intro ec hec o ho
  apply hseparation o
  apply List.mem_flatten.2
  refine ⟨frameObjects post ec, ?_, ho⟩
  apply List.mem_map.2
  exact ⟨ec, hchain.symm ▸ hec, rfl⟩

/-- Specialize concrete write preservation to all EVM frame and continuation
records. The copy prefix may have changed the heap pointer and detached buffer. -/
theorem log_growth_chain_records_preserved_g09 {F : Type}
    (s copy : PanSemStateFiniteExact 64 F) (l p n cap log : BitVec 64)
    (hl : l.toNat + 24 ≤ 2 ^ 64)
    (hp : p.toNat + 8 * n.toNat + 8 ≤ 2 ^ 64)
    (hbounds : ∀ ec ∈ evmChain s, ec.1 + 280 ≤ 2 ^ 64 ∧ ec.2 + 104 ≤ 2 ^ 64)
    (hheader : ∀ ec ∈ evmChain s,
      Disj (ec.1, 280) (l.toNat, 24) ∧ Disj (ec.2, 104) (l.toNat, 24))
    (hbuffer : ∀ ec ∈ evmChain s,
      Disj (ec.1, 280) (p.toNat, 8 * n.toNat + 8) ∧
      Disj (ec.2, 104) (p.toNat, 8 * n.toNat + 8))
    (hcopy : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → k % 8 = 0 → memW copy (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → k % 8 = 0 → memW copy (ec.2 + k) = memW s (ec.2 + k))) :
    let post := {copy with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64)
      else if a = l + 16#64 then .word (cap * 2#64)
      else if a = l then .word p else copy.memory a}
    ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → k % 8 = 0 → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → k % 8 = 0 → memW post (ec.2 + k) = memW s (ec.2 + k)) := by
  dsimp only
  intro ec hec
  constructor
  · intro k hk hk8
    exact (log_growth_protected_words_g09 copy l p n cap log (ec.1, 280)
      hl hp (hbounds ec hec).1 (hheader ec hec).1 (hbuffer ec hec).1 k hk).trans
      ((hcopy ec hec).1 k hk hk8)
  · intro k hk hk8
    exact (log_growth_protected_words_g09 copy l p n cap log (ec.2, 104)
      hl hp (hbounds ec hec).2 (hheader ec hec).2 (hbuffer ec hec).2 k hk).trans
      ((hcopy ec hec).2 k hk hk8)

private theorem log_growth_store_effect_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (a w : BitVec 64) (Rl : List Ivl)
    (hma : s.memaddrs = ordinaryDomain) (hd : s.memaddrs a)
    (hin : ∃ i ∈ Rl, i.1 ≤ a.toNat ∧ a.toNat + 8 ≤ i.1 + i.2) :
    ByteRegionEffect s {s with memory := fun b => if b = a then .word w else s.memory b} Rl := by
  have hrun : evaluateHOLFiniteState s (.store (.const a) (.const w)) =
      (none, {s with memory := fun b => if b = a then .word w else s.memory b}) := by
    simp [evaluateHOLFiniteState_store, evalHOLExact, flattenHOL, panMemStoresHOL,
      panMemStoreHOL, hd]
  exact (ByteRegionEffect.of_store_word hma hrun
    (by intro v hv; simp [evalHOLExact] at hv; exact ⟨w, hv.symm⟩)
    (by intro addr ha _; simp [evalHOLExact] at ha; subst addr; exact hin)).1

/-- The concrete growth tail writes only the list header and fresh buffer.
Its byte-accurate effect feeds typed-cell and old-log preservation directly. -/
theorem log_growth_final_effect_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (l p n cap log : BitVec 64)
    (hma : s.memaddrs = ordinaryDomain)
    (hd0 : s.memaddrs l) (hd8 : s.memaddrs (l + 8#64))
    (hd16 : s.memaddrs (l + 16#64)) (hdslot : s.memaddrs (p + n * 8#64))
    (hl : l.toNat + 24 ≤ 2 ^ 64)
    (hp : p.toNat + 8 * n.toNat + 8 ≤ 2 ^ 64) :
    let post := {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64)
      else if a = l + 16#64 then .word (cap * 2#64)
      else if a = l then .word p else s.memory a}
    ByteRegionEffect s post [(l.toNat, 24), (p.toNat, 8 * n.toNat + 8)] := by
  dsimp only
  have hl8 : (l + 8#64).toNat = l.toNat + 8 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hl16 : (l + 16#64).toNat = l.toNat + 16 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hn8 : (n * 8#64).toNat = n.toNat * 8 := by
    rw [BitVec.toNat_mul]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hs : (p + n * 8#64).toNat = p.toNat + 8 * n.toNat := by
    rw [BitVec.toNat_add, hn8, Nat.mod_eq_of_lt (by omega)]; omega
  let Rl : List Ivl := [(l.toNat, 24), (p.toNat, 8 * n.toNat + 8)]
  let s0 := {s with memory := fun a => if a = l then .word p else s.memory a}
  let s16 := {s0 with memory := fun a => if a = l + 16#64 then .word (cap * 2#64) else s0.memory a}
  let s8 := {s16 with memory := fun a => if a = l + 8#64 then .word (n + 1#64) else s16.memory a}
  have h0 : ByteRegionEffect s s0 Rl := log_growth_store_effect_g09 s l p Rl hma hd0
    ⟨(l.toNat, 24), by simp [Rl], by simp⟩
  have h16 : ByteRegionEffect s0 s16 Rl := log_growth_store_effect_g09 s0 _ _ Rl hma hd16
    ⟨(l.toNat, 24), by simp [Rl], by dsimp only; rw [hl16]; omega⟩
  have h8 : ByteRegionEffect s16 s8 Rl := log_growth_store_effect_g09 s16 _ _ Rl hma hd8
    ⟨(l.toNat, 24), by simp [Rl], by dsimp only; rw [hl8]; omega⟩
  have hslot := log_growth_store_effect_g09 s8 (p + n * 8#64) log Rl hma hdslot
    ⟨(p.toNat, 8 * n.toNat + 8), by simp [Rl], by dsimp only; rw [hs]; omega⟩
  exact (h0.trans h16).trans (h8.trans hslot)

/-- Fresh-buffer separation and header/world separation discharge typed-cell
preservation for the concrete four-write growth tail. -/
theorem log_growth_final_typed_cells_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (l p n cap q log : BitVec 64) (S Nd : List Nat)
    (hma : s.memaddrs = ordinaryDomain) (hWT : WorldTypedWith s S Nd)
    (hd0 : s.memaddrs l) (hd8 : s.memaddrs (l + 8#64))
    (hd16 : s.memaddrs (l + 16#64)) (hdslot : s.memaddrs (p + n * 8#64))
    (hl : l.toNat + 24 ≤ 2 ^ 64)
    (hslot : p.toNat + 8 * n.toNat + 8 ≤ q.toNat)
    (hheader : ∀ i ∈ worldTypedIvls s S Nd, Disj (l.toNat, 24) i)
    (hfresh : IvlsDisj [(p.toNat, q.toNat - p.toNat)] (worldTypedIvls s S Nd)) :
    let post := {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64)
      else if a = l + 16#64 then .word (cap * 2#64)
      else if a = l then .word p else s.memory a}
    SameTypedCells s post S Nd := by
  dsimp only
  have hq := q.isLt
  have heff := log_growth_final_effect_g09 s l p n cap log hma hd0 hd8 hd16 hdslot hl (by omega)
  apply ByteRegionEffect.sameTypedCells (Rl := [(l.toNat, 24), (p.toNat, 8 * n.toNat + 8)])
    (extra := []) hma hWT ?_ (by simp) (by simpa using heff)
  intro x hx i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact hheader i hi
  · have hd := hfresh (p.toNat, q.toNat - p.toNat) (by simp) i hi
    rcases hd with hz | hz | hleft | hright
    · dsimp only at hz; omega
    · exact Or.inr (Or.inl hz)
    · exact Or.inr (Or.inr (Or.inl (by dsimp only at hleft ⊢; omega)))
    · exact Or.inr (Or.inr (Or.inr hright))

/-- Frame object disjointness and fresh-copy framing supply every old-record
premise needed by the concrete growth-frame postcondition. -/
theorem log_growth_old_records_g09 {F : Type}
    {s copy : PanSemStateFiniteExact 64 F} {ec : Ivl} {S : List Nat}
    (l p n q : BitVec 64)
    (hA : ArenaReady s) (hFW : FrameWF s S ec)
    (hpw : (frameObjects s ec).Pairwise Disj)
    (hl : memW s (ec.1 + 88) = l.toNat)
    (hn : memW s (l.toNat + 8) = n.toNat)
    (hnonnull : l.toNat ≠ 0)
    (hfresh : IvlsDisj [(p.toNat, q.toNat - p.toNat)] (frameObjects s ec))
    (heff : ByteRegionEffect s copy [(p.toNat, q.toNat - p.toNat)]) :
    ∀ i, i < n.toNat →
      let oldLog := memW s (memW s l.toNat + 8 * i)
      LogEntryOK s oldLog ∧ oldLog + 40 ≤ 2 ^ 64 ∧
      Disj (oldLog, 40) (l.toNat, 24) ∧
      Disj (oldLog, 40) (p.toNat, q.toNat - p.toNat) ∧
      ∀ k ∈ ([0, 8, 16, 24, 32] : List Nat),
        memW copy (oldLog + k) = memW s (oldLog + k) := by
  intro i hi
  have hi' : i < memW s (memW s (ec.1 + 88) + 8) := by rwa [hl, hn]
  have hheap : globN s "heap_ptr" ≤ 2 ^ 64 := by
    have hh := hA.2.2.1
    rw [R11Shards.heapLimit_val] at hh
    omega
  obtain ⟨hok, hbound, hheader⟩ := log_records_of_frame_pairwise_g09 hFW hpw hheap
    (by rwa [hl]) i hi'
  simp only [hl] at hok hbound hheader
  have hmem : (memW s (memW s l.toNat + 8 * i), 40) ∈ frameObjects s ec := by
    simpa only [hl] using logRecord_in_frameObjects_g09 hi'
  have hd := hfresh (p.toNat, q.toNat - p.toNat) (by simp) _ hmem
  refine ⟨hok, hbound, hheader, R11Shards.Disj.symm hd, ?_⟩
  intro k hk
  have hkbound : k + 8 ≤ 40 ∧ k % 8 = 0 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
  exact memW_eq_of_frameDisj_g09 hA.1.memaddrs heff hbound hok.1.1 hkbound.2 hkbound.1
    (by intro x hx; obtain rfl := List.mem_singleton.1 hx; exact hd)

/-- Concrete growth reconstruction: frame invariants supply all old-record
premises, and separation of the finishing writes preserves the typed world. -/
theorem log_growth_concrete_frame_post_g09 {F : Type}
    (s copy : PanSemStateFiniteExact 64 F) (ec : Ivl) (S Nd : List Nat)
    (l p n cap q log : BitVec 64)
    (hA : ArenaReady s) (hFW : FrameWF s S ec)
    (hpw : (frameObjects s ec).Pairwise Disj)
    (hl : memW s (ec.1 + 88) = l.toNat)
    (hn : memW s (l.toNat + 8) = n.toNat) (hnonnull : l.toNat ≠ 0)
    (hfresh : IvlsDisj [(p.toNat, q.toNat - p.toNat)] (frameObjects s ec))
    (hl_bound : l.toNat + 24 ≤ 2 ^ 64)
    (hcap_pos : 1 ≤ cap.toNat) (hcap_bound : cap.toNat ≤ 31457280)
    (hlen : n.toNat ≤ cap.toNat) (hgrow : cap.toNat ≤ n.toNat)
    (hfit : p.toNat + (8#64 * cap * 2#64).toNat ≤ q.toNat)
    (hcopy : ∀ i, i < n.toNat →
      memW copy (p.toNat + 8 * i) = memW s (memW s l.toNat + 8 * i))
    (heff : ByteRegionEffect s copy [(p.toNat, q.toNat - p.toNat)])
    (hheap : globN s "heap_ptr" ≤ globN copy "heap_ptr")
    (hwords : WordsOK copy (p.toNat, q.toNat - p.toNat))
    (hlo : sourceBase ≤ p.toNat) (hq : q.toNat ≤ globN copy "heap_ptr")
    (hWT : WorldTypedWith copy S Nd)
    (hd0 : copy.memaddrs l) (hd8 : copy.memaddrs (l + 8#64))
    (hd16 : copy.memaddrs (l + 16#64)) (hdslot : copy.memaddrs (p + n * 8#64))
    (hheaderWorld : ∀ i ∈ worldTypedIvls copy S Nd, Disj (l.toNat, 24) i)
    (hfreshWorld : IvlsDisj [(p.toNat, q.toNat - p.toNat)]
      (worldTypedIvls copy S Nd)) :
    let post := {copy with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64)
      else if a = l + 16#64 then .word (cap * 2#64)
      else if a = l then .word p else copy.memory a}
    (∀ k ∈ ([8, 16, 24, 32, 40, 88, 112, 136, 144, 168, 176, 216, 232] : List Nat),
      memW post (ec.1 + k) = memW s (ec.1 + k)) →
    WordsOK post (l.toNat, 24) → Allocated post (l.toNat, 24) →
    MsgOwned post S (memW s (ec.1 + 112)) → LogEntryOK post log.toNat →
    SameTypedCells copy post S Nd ∧ FrameWF post S ec ∧
      LogsListOK post (memW post (ec.1 + 88)) ∧
      frameLogObjects post ec = frameLogObjects s ec ++ logOwnedIvls post log.toNat := by
  dsimp only
  intro hfields hheaderWords hallocated hmsg hlog
  have hheader : (l.toNat, 24) ∈ frameObjects s ec := by
    simp [frameObjects, hl]
  have hrecords := log_growth_old_records_g09 l p n q hA hFW hpw hl hn hnonnull hfresh heff
  have hglob := globN_congr heff.globals
  have hma : copy.memaddrs = ordinaryDomain := heff.memaddrs.trans hA.1.memaddrs
  obtain ⟨_, _, _, hmul, _, _, _, _, hslot, _⟩ :=
    log_growth_word_bounds_g09 hcap_pos hcap_bound hlen hgrow hfit
  have htyped := log_growth_final_typed_cells_g09 copy l p n cap q log S Nd
    hma hWT hd0 hd8 hd16 hdslot hl_bound (by rwa [hmul] at hslot)
    hheaderWorld hfreshWorld
  refine ⟨htyped, ?_⟩
  exact log_growth_frame_post_g09 s copy ec S l p n cap q log (frameObjects s ec)
    hFW hl hn hheader hfresh hl_bound hcap_pos hcap_bound hlen hgrow hfit hcopy
    heff.memaddrs hheap (congrFun hglob "vm_system_address")
    (congrFun hglob "scratch_ptr") (congrFun hglob "frame_mem_ptr")
    (congrFun hglob "evm_empty") hwords hlo hq hrecords
    hfields hheaderWords hallocated hmsg hlog

/-- Header allocation/domain and validity of the newly constructed record survive
the concrete growth tail. Only separation of that record from the two write
regions is required; its pointer fields need no post-state assumptions. -/
theorem log_growth_header_and_new_record_g09 {F : Type}
    (s copy : PanSemStateFiniteExact 64 F) (ec : Ivl) (S : List Nat)
    (l p n cap q log : BitVec 64)
    (hA : ArenaReady s) (hFW : FrameWF s S ec)
    (hl : memW s (ec.1 + 88) = l.toNat)
    (hdom : copy.memaddrs = s.memaddrs)
    (hheap : globN s "heap_ptr" ≤ globN copy "heap_ptr")
    (hscratch : globN copy "scratch_ptr" ≤ globN s "scratch_ptr")
    (hl_bound : l.toNat + 24 ≤ 2 ^ 64)
    (hslot : p.toNat + 8 * n.toNat + 8 ≤ q.toNat)
    (hheap_bound : globN copy "heap_ptr" ≤ 2 ^ 64)
    (hlog : LogEntryOK copy log.toNat)
    (hdheader : Disj (log.toNat, 40) (l.toNat, 24))
    (hdbuffer : Disj (log.toNat, 40) (p.toNat, q.toNat - p.toNat)) :
    let post := {copy with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64)
      else if a = l + 16#64 then .word (cap * 2#64)
      else if a = l then .word p else copy.memory a}
    WordsOK post (l.toNat, 24) ∧ Allocated post (l.toNat, 24) ∧
      LogEntryOK post log.toNat ∧ logOwnedIvls post log.toNat = logOwnedIvls copy log.toNat := by
  dsimp only
  have hh := hFW.1 (memW s (ec.1 + 88), 24) (by simp)
  rw [hl] at hh
  have hwords := (wordsOK_congr_of_dom_g09 hdom).2 hh.2
  have hallocated : Allocated copy (l.toNat, 24) :=
    AllocatorGrows.allocated ⟨hheap, hscratch⟩ (Or.inr hh.1)
  have hq := q.isLt
  have hdB : Disj (log.toNat, 40) (p.toNat, 8 * n.toNat + 8) := by
    rcases hdbuffer with hz | hz | hleft | hright
    · exact Or.inl hz
    · dsimp only at hz; omega
    · exact Or.inr (Or.inr (Or.inl hleft))
    · exact Or.inr (Or.inr (Or.inr (by dsimp only at hright ⊢; omega)))
  have hrecord := log_growth_record_preserved_g09 copy copy l p n cap log log.toNat
    hl_bound (by omega) (le_trans hlog.2.1.2 hheap_bound) hdheader hdB rfl
    (le_refl _) rfl (by intros; rfl) hlog
  refine ⟨?_, hallocated, hrecord⟩
  exact (wordsOK_congr_of_dom_g09 (s := copy)
    (post := {copy with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64)
      else if a = l + 16#64 then .word (cap * 2#64)
      else if a = l then .word p else copy.memory a}) rfl).2 hwords

/-- The concrete growth-frame contract with header validity and the new record
derived from pre-tail invariants, rather than assumed in the final state. -/
theorem log_growth_frame_post_from_new_record_g09 {F : Type}
    (s copy : PanSemStateFiniteExact 64 F) (ec : Ivl) (S Nd : List Nat)
    (l p n cap q log : BitVec 64)
    (hA : ArenaReady s) (hFW : FrameWF s S ec)
    (hpw : (frameObjects s ec).Pairwise Disj)
    (hl : memW s (ec.1 + 88) = l.toNat)
    (hn : memW s (l.toNat + 8) = n.toNat) (hnonnull : l.toNat ≠ 0)
    (hfresh : IvlsDisj [(p.toNat, q.toNat - p.toNat)] (frameObjects s ec))
    (hl_bound : l.toNat + 24 ≤ 2 ^ 64)
    (hcap_pos : 1 ≤ cap.toNat) (hcap_bound : cap.toNat ≤ 31457280)
    (hlen : n.toNat ≤ cap.toNat) (hgrow : cap.toNat ≤ n.toNat)
    (hfit : p.toNat + (8#64 * cap * 2#64).toNat ≤ q.toNat)
    (hcopy : ∀ i, i < n.toNat →
      memW copy (p.toNat + 8 * i) = memW s (memW s l.toNat + 8 * i))
    (heff : ByteRegionEffect s copy [(p.toNat, q.toNat - p.toNat)])
    (hheap : globN s "heap_ptr" ≤ globN copy "heap_ptr")
    (hheap_bound : globN copy "heap_ptr" ≤ 2 ^ 64)
    (hwords : WordsOK copy (p.toNat, q.toNat - p.toNat))
    (hlo : sourceBase ≤ p.toNat) (hq : q.toNat ≤ globN copy "heap_ptr")
    (hWT : WorldTypedWith copy S Nd)
    (hd0 : copy.memaddrs l) (hd8 : copy.memaddrs (l + 8#64))
    (hd16 : copy.memaddrs (l + 16#64)) (hdslot : copy.memaddrs (p + n * 8#64))
    (hheaderWorld : ∀ i ∈ worldTypedIvls copy S Nd, Disj (l.toNat, 24) i)
    (hfreshWorld : IvlsDisj [(p.toNat, q.toNat - p.toNat)]
      (worldTypedIvls copy S Nd))
    (hlog : LogEntryOK copy log.toNat)
    (hdheader : Disj (log.toNat, 40) (l.toNat, 24))
    (hdbuffer : Disj (log.toNat, 40) (p.toNat, q.toNat - p.toNat)) :
    let post := {copy with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64)
      else if a = l + 16#64 then .word (cap * 2#64)
      else if a = l then .word p else copy.memory a}
    (∀ k ∈ ([8, 16, 24, 32, 40, 88, 112, 136, 144, 168, 176, 216, 232] : List Nat),
      memW post (ec.1 + k) = memW s (ec.1 + k)) →
    MsgOwned post S (memW s (ec.1 + 112)) →
    SameTypedCells copy post S Nd ∧ FrameWF post S ec ∧
      LogsListOK post (memW post (ec.1 + 88)) ∧
      frameLogObjects post ec = frameLogObjects s ec ++ logOwnedIvls copy log.toNat := by
  dsimp only
  intro hfields hmsg
  obtain ⟨_, _, _, hmul, _, _, _, _, hslot, _⟩ :=
    log_growth_word_bounds_g09 hcap_pos hcap_bound hlen hgrow hfit
  rw [hmul] at hslot
  have hscratch : globN copy "scratch_ptr" ≤ globN s "scratch_ptr" := by
    rw [congrFun (globN_congr heff.globals) "scratch_ptr"]
  obtain ⟨hheaderWords, hallocated, hlogPost, howned⟩ :=
    log_growth_header_and_new_record_g09 s copy ec S l p n cap q log hA hFW hl
      heff.memaddrs hheap hscratch hl_bound hslot hheap_bound hlog hdheader hdbuffer
  obtain ⟨htyped, hframe, hlist, hlogs⟩ :=
    log_growth_concrete_frame_post_g09 s copy ec S Nd l p n cap q log hA hFW hpw
      hl hn hnonnull hfresh hl_bound hcap_pos hcap_bound hlen hgrow hfit hcopy heff
      hheap hwords hlo hq hWT hd0 hd8 hd16 hdslot hheaderWorld hfreshWorld
      hfields hheaderWords hallocated hmsg hlogPost
  exact ⟨htyped, hframe, hlist, by rw [hlogs, howned]⟩

/-- Message ownership is stable under log growth: typed world cells retain all
world exclusions, and only newly introduced frame objects need fresh separation. -/
theorem msgOwned_of_log_growth_cells_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {m : Nat}
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hWT : WorldTypedWith s S Nd)
    (hcell : SameTypedCells s post S Nd)
    (hglobals : ∀ g ∈ coreWorldGlobals, globN post g = globN s g)
    (hdom : post.memaddrs = s.memaddrs)
    (hgrows : AllocatorGrows s post)
    (hfixed : fixedObjects post = fixedObjects s)
    (hfoot : ∀ t ∈ S, htabFootprint post t = htabFootprint s t)
    (hchain : evmChain post = evmChain s)
    (hobjects : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects post ec,
      o ∈ frameObjects s ec ∨ Disj (m, 176) o)
    (hmsg : MsgOwned s S m) : MsgOwned post S m := by
  obtain ⟨hal, hw, hdt, hdf, hdfo, Nd_m, hTr_m, hdj_m⟩ := hmsg
  obtain ⟨hTr_int, hsub_int⟩ := Wave8Contracts.M23.triesTypedWith_inter hWT.2.2.2 hTr_m
  let Ndi := Nd.filter (fun n => decide (n ∈ Nd_m))
  have hsub : ∀ n ∈ Ndi, n ∈ Nd := fun n hn => (List.mem_filter.1 hn).1
  have hcell_i : SameTypedCells s post S Ndi := sameTypedCells_sub_nd_g09 hsub hcell
  have hnodes := nodeExtents_eq hTr_int.1 hcell_i
  have hWT_i : WorldTypedWith s S Ndi := ⟨hWT.1, hWT.2.1, hWT.2.2.1, hTr_int⟩
  have hFT := fixedTyped_of_eq hAp hWT.2.2.1 hgrows.1 hgrows.2 hfixed
  have htries_i : TriesTypedWith post S Ndi := by
    obtain ⟨hpost, _⟩ := worldTypedWith_congr_w1 hAs hAp hgrows.1 hgrows.2
      hglobals hcell_i hWT_i ⟨hFT, fun o ho => Or.inl (by rw [← hfixed]; exact ho)⟩
    exact hpost.2.2.2
  refine ⟨hgrows.allocated hal, (wordsOK_congr_of_dom_g09 hdom).2 hw,
    ?_, ?_, ?_, Ndi, htries_i, ?_⟩
  · intro t ht i hi
    rw [hfoot t ht] at hi
    exact hdt t ht i hi
  · intro j hj
    rw [hfixed] at hj
    exact hdf j hj
  · rw [hchain]
    intro ec hec o ho
    rcases hobjects ec hec o ho with hold | hnew
    · exact hdfo ec hec o hold
    · exact hnew
  · intro o ho j hj
    rw [hnodes] at hj
    exact hdj_m o ho j (hsub_int j hj).2

/-- Protected frame-record readback supplies the finite field list required by
the concrete growth-frame contract. -/
theorem log_growth_frame_fields_g09 {F : Type}
    (s copy : PanSemStateFiniteExact 64 F) (ec : Ivl)
    (l p n cap q log : BitVec 64)
    (hl : l.toNat + 24 ≤ 2 ^ 64)
    (hslot : p.toNat + 8 * n.toNat + 8 ≤ q.toNat)
    (hec : ec.1 + 280 ≤ 2 ^ 64)
    (hdheader : Disj (ec.1, 280) (l.toNat, 24))
    (hdbuffer : Disj (ec.1, 280) (p.toNat, q.toNat - p.toNat))
    (hcopy : ∀ k, k + 8 ≤ 280 → k % 8 = 0 →
      memW copy (ec.1 + k) = memW s (ec.1 + k)) :
    let post := {copy with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64)
      else if a = l + 16#64 then .word (cap * 2#64)
      else if a = l then .word p else copy.memory a}
    ∀ k ∈ ([8, 16, 24, 32, 40, 88, 112, 136, 144, 168, 176, 216, 232] : List Nat),
      memW post (ec.1 + k) = memW s (ec.1 + k) := by
  dsimp only
  intro k hk
  have hkbound : k + 8 ≤ 280 ∧ k % 8 = 0 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hq := q.isLt
  have hdB : Disj (ec.1, 280) (p.toNat, 8 * n.toNat + 8) := by
    rcases hdbuffer with hz | hz | hleft | hright
    · exact Or.inl hz
    · dsimp only at hz; omega
    · exact Or.inr (Or.inr (Or.inl hleft))
    · exact Or.inr (Or.inr (Or.inr (by dsimp only at hright ⊢; omega)))
  exact (log_growth_protected_words_g09 copy l p n cap log (ec.1, 280)
    hl (by omega) hec hdheader hdB k hkbound.1).trans (hcopy k hkbound.1 hkbound.2)

/-- A growing frame introduces precisely its replacement backing array and the
new log-owned regions; every other object was already owned by that frame. -/
theorem log_growth_frame_object_cases_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {ec : Ivl} {log : Nat}
    (hfields : ∀ k ∈ ([8, 24, 40, 88, 232] : List Nat),
      memW post (ec.1 + k) = memW s (ec.1 + k))
    (hret : frameRet post ec = frameRet s ec)
    (hlogs : frameLogObjects post ec = frameLogObjects s ec ++ logOwnedIvls post log) :
    ∀ o ∈ frameObjects post ec,
      o ∈ frameObjects s ec ∨ o = frameLogs post ec ∨ o ∈ logOwnedIvls post log := by
  intro o ho
  rw [frameObjects_of_log_append_g09 hfields hret hlogs] at ho
  rcases List.mem_append.1 ho with ho | ho
  · rcases List.mem_append.1 ho with ho | hold
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (by simp [frameObjects])
      · exact Or.inl (by simp [frameObjects])
      · exact Or.inl (by simp [frameObjects])
      · exact Or.inl (by simp [frameObjects])
      · exact Or.inl (by simp [frameObjects])
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl (by simp [frameObjects])
    · exact Or.inl (by simp only [frameObjects]; exact List.mem_append_right _ hold)
  · exact Or.inr (Or.inr ho)

/-- Head-frame object cases and unchanged suspended frames reduce message
preservation to separation from the replacement array and appended log regions. -/
theorem msgOwned_of_head_log_growth_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {m log : Nat} {head : Ivl}
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hWT : WorldTypedWith s S Nd) (hcell : SameTypedCells s post S Nd)
    (hglobals : ∀ g ∈ coreWorldGlobals, globN post g = globN s g)
    (hdom : post.memaddrs = s.memaddrs) (hgrows : AllocatorGrows s post)
    (hfixed : fixedObjects post = fixedObjects s)
    (hfoot : ∀ t ∈ S, htabFootprint post t = htabFootprint s t)
    (hchain : evmChain post = evmChain s)
    (hhead : ∀ ec ∈ evmChain s, ec = head ∨ ec ∈ (evmChain s).tail)
    (htail : ∀ ec ∈ (evmChain s).tail, frameObjects post ec = frameObjects s ec)
    (hfields : ∀ k ∈ ([8, 24, 40, 88, 232] : List Nat),
      memW post (head.1 + k) = memW s (head.1 + k))
    (hret : frameRet post head = frameRet s head)
    (hlogs : frameLogObjects post head = frameLogObjects s head ++ logOwnedIvls post log)
    (hbuffer : Disj (m, 176) (frameLogs post head))
    (hnew : ∀ o ∈ logOwnedIvls post log, Disj (m, 176) o)
    (hmsg : MsgOwned s S m) : MsgOwned post S m := by
  apply msgOwned_of_log_growth_cells_g09 hAs hAp hWT hcell hglobals hdom hgrows
    hfixed hfoot hchain ?_ hmsg
  intro ec hec o ho
  rcases hhead ec hec with rfl | htail_mem
  · rcases log_growth_frame_object_cases_g09 hfields hret hlogs o ho with hold | rfl | hnew_mem
    · exact Or.inl hold
    · exact Or.inr hbuffer
    · exact Or.inr (hnew o hnew_mem)
  · exact Or.inl (htail ec htail_mem ▸ ho)

/-- Separate the whole post-growth chain from an arbitrary protected region
using only the old chain and the two classes of newly introduced objects. -/
theorem log_growth_chain_disj_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {head : Ivl} {log : Nat} {regions : List Ivl}
    (hchain : evmChain post = evmChain s)
    (hhead : ∀ ec ∈ evmChain s, ec = head ∨ ec ∈ (evmChain s).tail)
    (htail : ∀ ec ∈ (evmChain s).tail, frameObjects post ec = frameObjects s ec)
    (hfields : ∀ k ∈ ([8, 24, 40, 88, 232] : List Nat),
      memW post (head.1 + k) = memW s (head.1 + k))
    (hret : frameRet post head = frameRet s head)
    (hlogs : frameLogObjects post head = frameLogObjects s head ++ logOwnedIvls post log)
    (hold : IvlsDisj ((evmChain s).map (frameObjects s)).flatten regions)
    (hbuffer : ∀ i ∈ regions, Disj (frameLogs post head) i)
    (hnew : IvlsDisj (logOwnedIvls post log) regions) :
    IvlsDisj ((evmChain post).map (frameObjects post)).flatten regions := by
  intro o ho i hi
  obtain ⟨objects, hobjects, ho⟩ := List.mem_flatten.1 ho
  obtain ⟨ec, hec, rfl⟩ := List.mem_map.1 hobjects
  rw [hchain] at hec
  have old_disj : ∀ o ∈ frameObjects s ec, Disj o i := by
    intro old hmem
    exact hold old (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ec, hec, rfl⟩, hmem⟩) i hi
  rcases hhead ec hec with rfl | htail_mem
  · rcases log_growth_frame_object_cases_g09 hfields hret hlogs o ho with hmem | rfl | hmem
    · exact old_disj o hmem
    · exact hbuffer i hi
    · exact hnew o hmem i hi
  · exact old_disj o (htail ec htail_mem ▸ ho)

/-- Fresh allocation separation passes to the entire replacement backing array,
whose extent is exactly the doubled capacity after the concrete finishing writes. -/
theorem log_growth_buffer_disj_g09 {F : Type}
    (copy : PanSemStateFiniteExact 64 F) (ec : Ivl)
    (l p n cap q log : BitVec 64) (objects regions : List Ivl)
    (hheader : (l.toNat, 24) ∈ objects)
    (hfresh : IvlsDisj [(p.toNat, q.toNat - p.toNat)] objects)
    (hl_bound : l.toNat + 24 ≤ 2 ^ 64)
    (hcap_pos : 1 ≤ cap.toNat) (hcap_bound : cap.toNat ≤ 31457280)
    (hlen : n.toNat ≤ cap.toNat) (hgrow : cap.toNat ≤ n.toNat)
    (hfit : p.toNat + (8#64 * cap * 2#64).toNat ≤ q.toNat)
    (hprotected : IvlsDisj [(p.toNat, q.toNat - p.toNat)] regions) :
    let post := {copy with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64)
      else if a = l + 16#64 then .word (cap * 2#64)
      else if a = l then .word p else copy.memory a}
    memW post (ec.1 + 88) = l.toNat →
    ∀ i ∈ regions, Disj (frameLogs post ec) i := by
  dsimp only
  intro hec i hi
  obtain ⟨h0, _, h16, _, _, _⟩ := log_growth_readback_of_fresh_g09
    copy l p n cap q log objects hheader hfresh hl_bound hcap_pos hcap_bound hlen hgrow hfit
  have hl16 : (l + 16#64).toNat = l.toNat + 16 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hl16] at h16
  obtain ⟨_, _, hsize, _, _, _, _, _, _, _⟩ :=
    log_growth_word_bounds_g09 hcap_pos hcap_bound hlen hgrow hfit
  rw [hsize] at hfit
  unfold frameLogs
  rw [hec, h0, h16]
  have hd := hprotected (p.toNat, q.toNat - p.toNat) (by simp) i hi
  rcases hd with hz | hz | hleft | hright
  · dsimp only at hz; omega
  · exact Or.inr (Or.inl hz)
  · exact Or.inr (Or.inr (Or.inl (by dsimp only at hleft ⊢; omega)))
  · exact Or.inr (Or.inr (Or.inr hright))

/-- Assemble the exposed growth invariant from local frame reconstruction and
separation of only the replacement buffer and newly appended log regions. -/
theorem evmInvAt_of_log_growth_new_objects_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {head : Ivl} {log : Nat}
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hinv : EvmInvAt s S) (hWT : WorldTypedWith s S Nd)
    (hheap : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hscratch : globN post "scratch_ptr" ≤ globN s "scratch_ptr")
    (hglobals : ∀ g, ofString g ≠ ofString "heap_ptr" →
      ofString g ≠ ofString "scratch_ptr" → ofString g ≠ ofString "frame_mem_ptr" →
      globN post g = globN s g)
    (hcell : SameTypedCells s post S Nd)
    (hchain : evmChain post = evmChain s)
    (hhead_mem : head ∈ evmChain s)
    (hhead : ∀ ec ∈ evmChain s, ec = head ∨ ec ∈ (evmChain s).tail)
    (hfields : ∀ ec ∈ evmChain s, ∀ k, k + 8 ≤ 280 → k % 8 = 0 →
      memW post (ec.1 + k) = memW s (ec.1 + k))
    (hcont : ∀ ec ∈ evmChain s, ∀ k, k + 8 ≤ 104 → k % 8 = 0 →
      memW post (ec.2 + k) = memW s (ec.2 + k))
    (hframes : ∀ ec ∈ evmChain s, FrameWF post S ec)
    (hpairwise : ((evmChain post).map (frameObjects post)).flatten.Pairwise Disj)
    (hold : IvlsDisj ((evmChain s).map (frameObjects s)).flatten (worldOwned s S Nd))
    (hbuffer : ∀ i ∈ worldOwned s S Nd, Disj (frameLogs post head) i)
    (hnew : IvlsDisj (logOwnedIvls post log) (worldOwned s S Nd))
    (happend : frameLogObjects post head = frameLogObjects s head ++ logOwnedIvls post log)
    (hobjects : ∀ ec ∈ (evmChain s).tail, frameObjects post ec = frameObjects s ec)
    (hlogs : ∀ ec ∈ (evmChain s).tail, frameLogs post ec = frameLogs s ec) :
    EvmInvAt post S := by
  have hhead_fields : ∀ k ∈ ([8, 24, 40, 88, 232] : List Nat),
      memW post (head.1 + k) = memW s (head.1 + k) := by
    intro k hk
    have hb : k + 8 ≤ 280 ∧ k % 8 = 0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
    exact hfields head hhead_mem k hb.1 hb.2
  have hret : frameRet post head = frameRet s head := by
    unfold frameRet
    rw [hfields head hhead_mem 144 (by omega) (by omega),
      hfields head hhead_mem 216 (by omega) (by omega)]
  have hdisj := log_growth_chain_disj_g09 hchain hhead hobjects hhead_fields hret happend
    hold hbuffer hnew
  exact evmInvAt_of_log_growth_cells_g09 hAs hAp hinv hWT hheap hscratch hglobals
    hcell hchain hfields hcont hframes hpairwise hdisj hobjects hlogs

/-- Reconstructed log-growth invariants give the handler-facing invariant,
potential equality and memory alignment directly from unchanged frame records. -/
theorem log_growth_handler_post_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hA : ArenaReady post) (hinv : EvmInvAt post S)
    (hchain : evmChain post = evmChain s)
    (hfields : ∀ ec ∈ evmChain s, ∀ k, k + 8 ≤ 280 → k % 8 = 0 →
      memW post (ec.1 + k) = memW s (ec.1 + k))
    (hev : globN post "ev" = globN s "ev")
    (hframe : globN post "frame_mem_ptr" = globN s "frame_mem_ptr")
    (hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s)
    (hHM : HeadMemAligned s) :
    EvmInv post ∧ evmR post = evmR s ∧ HeadMemAligned post := by
  refine ⟨⟨hA, S, hinv.1, hinv.2⟩, ?_, ?_⟩
  · unfold evmR
    rw [hchain]
    congr 1
    apply List.map_congr_left
    intro ec hec
    rw [hfields ec hec 64 (by omega) (by omega),
      hfields ec hec 192 (by omega) (by omega)]
  · have hm24 := hfields _ hhead 24 (by omega) (by omega)
    have hm32 := hfields _ hhead 32 (by omega) (by omega)
    have hm40 := hfields _ hhead 40 (by omega) (by omega)
    unfold HeadMemAligned at hHM ⊢
    rw [hev, hm24, hm32, hm40, hframe]
    exact hHM

/-- The in-place append writes only the header length and the insertion slot,
with a byte effect suitable for old-record and typed-world framing. -/
theorem log_no_growth_final_effect_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (l p n log : BitVec 64)
    (hma : s.memaddrs = ordinaryDomain)
    (hd8 : s.memaddrs (l + 8#64)) (hdslot : s.memaddrs (p + n * 8#64))
    (hl : l.toNat + 24 ≤ 2 ^ 64)
    (hp : p.toNat + 8 * n.toNat + 8 ≤ 2 ^ 64) :
    ByteRegionEffect s {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64) else s.memory a}
      [(l.toNat + 8, 8), (p.toNat + 8 * n.toNat, 8)] := by
  have hl8 : (l + 8#64).toNat = l.toNat + 8 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hn8 : (n * 8#64).toNat = n.toNat * 8 := by
    rw [BitVec.toNat_mul]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hs : (p + n * 8#64).toNat = p.toNat + 8 * n.toNat := by
    rw [BitVec.toNat_add, hn8, Nat.mod_eq_of_lt (by omega)]; omega
  let Rl : List Ivl := [(l.toNat + 8, 8), (p.toNat + 8 * n.toNat, 8)]
  have hlen := log_growth_store_effect_g09 s (l + 8#64) (n + 1#64) Rl hma hd8
    ⟨(l.toNat + 8, 8), by simp [Rl], by dsimp only; rw [hl8]; omega⟩
  have hstore := log_growth_store_effect_g09
    {s with memory := fun a => if a = l + 8#64 then .word (n + 1#64) else s.memory a}
    (p + n * 8#64) log Rl hma hdslot
    ⟨(p.toNat + 8 * n.toNat, 8), by simp [Rl], by dsimp only; rw [hs]; omega⟩
  exact hlen.trans hstore

/-- In-place append readback preserves the buffer pointer, capacity and every
old slot, while incrementing length and installing the new record pointer. -/
theorem log_no_growth_final_cells_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (l p n cap log : BitVec 64)
    (hl : l.toNat + 24 ≤ 2 ^ 64)
    (hp : p.toNat + 8 * n.toNat + 8 ≤ 2 ^ 64)
    (hdisj : Disj (p.toNat, 8 * n.toNat + 8) (l.toNat, 24))
    (hn : n.toNat + 1 < 2 ^ 64)
    (hm0 : memW s l.toNat = p.toNat)
    (hm16 : memW s (l.toNat + 16) = cap.toNat) :
    let post := {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64) else s.memory a}
    memW post l.toNat = p.toNat ∧
    memW post (l.toNat + 8) = n.toNat + 1 ∧
    memW post (l.toNat + 16) = cap.toNat ∧
    memW post (p.toNat + 8 * n.toNat) = log.toNat ∧
    ∀ i, i < n.toNat → memW post (p.toNat + 8 * i) = memW s (p.toNat + 8 * i) := by
  dsimp only
  obtain ⟨h08, h016, h816, hs0, hs8, hs16, hold⟩ :=
    log_growth_write_disjoint_g09 hl hp hdisj
  have hl8 : (l + 8#64).toNat = l.toNat + 8 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hl16 : (l + 16#64).toNat = l.toNat + 16 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hn8 : (n * 8#64).toNat = n.toNat * 8 := by
    rw [BitVec.toNat_mul]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hs : (p + n * 8#64).toNat = p.toNat + 8 * n.toNat := by
    rw [BitVec.toNat_add, hn8, Nat.mod_eq_of_lt (by omega)]; omega
  have hn1 : (n + 1#64).toNat = n.toNat + 1 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hn
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [memW, Ne.symm hs0, h08] using hm0
  · rw [← hl8]
    simp only [memW, BitVec.ofNat_toNat]
    simp [memW, Ne.symm hs8, hn1]
  · rw [← hl16] at hm16 ⊢
    simp only [memW, BitVec.ofNat_toNat] at hm16 ⊢
    simpa [memW, Ne.symm hs16, Ne.symm h816] using hm16
  · rw [← hs]
    simp only [memW, BitVec.ofNat_toNat]
    simp [memW]
  · intro i hi
    obtain ⟨hns, hn8', _, _⟩ := hold i hi
    simp [memW, hns, hn8']

/-- Concrete in-place readback and byte framing establish the semantic append
contract, including preservation of all pre-existing log-owned intervals. -/
theorem log_no_growth_semantic_post_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (ec : Ivl) (S : List Nat)
    (l p n cap log : BitVec 64)
    (hA : ArenaReady s) (hFW : FrameWF s S ec)
    (hl : memW s (ec.1 + 88) = l.toNat)
    (hn : memW s (l.toNat + 8) = n.toNat)
    (hm0 : memW s l.toNat = p.toNat)
    (hm16 : memW s (l.toNat + 16) = cap.toNat)
    (hlt : n.toNat < cap.toNat) (hn_bound : n.toNat + 1 < 2 ^ 64)
    (hl_bound : l.toNat + 24 ≤ 2 ^ 64)
    (hp_bound : p.toNat + 8 * n.toNat + 8 ≤ 2 ^ 64)
    (hdisj : Disj (p.toNat, 8 * n.toNat + 8) (l.toNat, 24))
    (hd8 : s.memaddrs (l + 8#64)) (hdslot : s.memaddrs (p + n * 8#64))
    (hrecords : ∀ x ∈ ([(l.toNat + 8, 8), (p.toNat + 8 * n.toNat, 8)] : List Ivl),
      ∀ i, i < n.toNat → Disj x (memW s (p.toNat + 8 * i), 40)) :
    let post := {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64) else s.memory a}
    memW post (ec.1 + 88) = l.toNat →
    WordsOK post (l.toNat, 24) → Allocated post (l.toNat, 24) →
    (∀ i, i ≤ n.toNat → WordAt post (p.toNat + 8 * i)) →
    LogEntryOK post log.toNat →
    LogsListOK post (memW post (ec.1 + 88)) ∧
      frameLogObjects post ec = frameLogObjects s ec ++ logOwnedIvls post log.toNat := by
  dsimp only
  intro hframe hwords hallocated hslots hlog
  have heff := log_no_growth_final_effect_g09 s l p n log hA.1.memaddrs
    hd8 hdslot hl_bound hp_bound
  obtain ⟨h0, h8, h16, hstore, hprefix⟩ :=
    log_no_growth_final_cells_g09 s l p n cap log hl_bound hp_bound hdisj hn_bound hm0 hm16
  apply log_append_post_of_frame_effect_g09 hA hFW heff (le_refl _) rfl
  · simpa only [hl, hn, hm0] using hrecords
  · exact hframe.trans hl.symm
  · simpa only [hl] using hwords
  · simpa only [hl] using hallocated
  · simpa only [hl, hn] using h8
  · rw [hl, hn, h16]; omega
  · intro i hi
    rw [hl, hn] at hi
    simp only [hl, h0, hm0]
    exact ⟨hslots i (Nat.le_of_lt hi), hprefix i hi⟩
  · simpa only [hl, hn, h0] using hslots n.toNat (le_refl _)
  · simpa only [hl, hn, h0] using hstore
  · exact hlog

/-- In-place append preserves the backing-array extent and reconstructs the
containing frame from its unchanged structural fields and semantic list result. -/
theorem frameWF_of_log_no_growth_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} {ec : Ivl}
    (hFW : FrameWF s S ec)
    (hdom : post.memaddrs = s.memaddrs)
    (hglobals : post.globals = s.globals)
    (hfields : ∀ k ∈ ([8, 16, 24, 32, 40, 88, 112, 136, 144, 168, 176, 216, 232] : List Nat),
      memW post (ec.1 + k) = memW s (ec.1 + k))
    (hptr : memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)))
    (hcap : memW post (memW s (ec.1 + 88) + 16) = memW s (memW s (ec.1 + 88) + 16))
    (hlen : memW post (memW s (ec.1 + 88) + 8) ≤ memW post (memW s (ec.1 + 88) + 16))
    (hlist : LogsListOK post (memW s (ec.1 + 88)))
    (hmsg : MsgOwned post S (memW s (ec.1 + 112))) :
    FrameWF post S ec ∧ frameLogs post ec = frameLogs s ec := by
  have hg := globN_congr hglobals
  have hbuffer : frameLogs post ec = frameLogs s ec := by
    unfold frameLogs
    rw [hfields 88 (by simp), hptr, hcap]
  have hcap_old := hFW.2.2.2.2.2.2.2.2.2.2.1
  have hinside_old := hFW.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hwords_old := hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨frameWF_of_log_growth_g09 hFW hdom
    (congrFun hg "scratch_ptr") (congrFun hg "frame_mem_ptr")
    (by rw [congrFun hg "heap_ptr"]) (congrFun hg "evm_empty") hfields
    ?_ hlist hlen ?_ ?_ hmsg, hbuffer⟩
  · rw [hcap]
    exact hcap_old
  · rw [hbuffer, congrFun hg "heap_ptr", congrFun hg "scratch_ptr"]
    exact hinside_old
  · rw [hbuffer]
    exact (wordsOK_congr_of_dom_g09 hdom).2 hwords_old

/-- Frame object disjointness separates every existing log record from both
in-place append writes. The insertion cell lies within the unchanged capacity. -/
theorem log_no_growth_old_record_separation_g09 {F : Type}
    {s : PanSemStateFiniteExact 64 F} {ec : Ivl} {S : List Nat}
    (l p n cap : BitVec 64)
    (hA : ArenaReady s) (hFW : FrameWF s S ec)
    (hpw : (frameObjects s ec).Pairwise Disj)
    (hl : memW s (ec.1 + 88) = l.toNat)
    (hn : memW s (l.toNat + 8) = n.toNat)
    (hp : memW s l.toNat = p.toNat)
    (hc : memW s (l.toNat + 16) = cap.toNat)
    (hnonnull : l.toNat ≠ 0) (hlt : n.toNat < cap.toNat) :
    ∀ x ∈ ([(l.toNat + 8, 8), (p.toNat + 8 * n.toNat, 8)] : List Ivl),
      ∀ i, i < n.toNat → Disj x (memW s (p.toNat + 8 * i), 40) := by
  intro x hx i hi
  have hi' : i < memW s (memW s (ec.1 + 88) + 8) := by rwa [hl, hn]
  have hheap : globN s "heap_ptr" ≤ 2 ^ 64 := by
    have hh := hA.2.2.1
    rw [R11Shards.heapLimit_val] at hh
    omega
  obtain ⟨_, _, hdH⟩ := log_records_of_frame_pairwise_g09 hFW hpw hheap
    (by rwa [hl]) i hi'
  simp only [hl, hp] at hdH
  have hdB : Disj (frameLogs s ec) (memW s (p.toNat + 8 * i), 40) := by
    unfold frameObjects at hpw
    have htail := (List.pairwise_cons.1 hpw).2
    have htail := (List.pairwise_cons.1 htail).2
    have htail := (List.pairwise_cons.1 htail).2
    have htail := (List.pairwise_cons.1 htail).2
    have htail := (List.pairwise_cons.1 htail).2
    apply (List.pairwise_cons.1 htail).1
    apply List.mem_cons_of_mem
    simp only [List.append]
    have hm : (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40) ∈ frameLogObjects s ec := by
      unfold frameLogObjects
      apply List.mem_flatMap.2
      refine ⟨i, List.mem_range.2 hi', ?_⟩
      exact List.mem_filter.2 ⟨by simp [logRecordIvls], by simp⟩
    simpa only [hl, hp] using hm
  unfold frameLogs at hdB
  simp only [hl, hp, hc] at hdB
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · have hd := R11Shards.Disj.symm hdH
    rcases hd with hz | hz | hleft | hright
    · cases hz
    · exact Or.inr (Or.inl hz)
    · exact Or.inr (Or.inr (Or.inl (by dsimp only at hleft ⊢; omega)))
    · exact Or.inr (Or.inr (Or.inr (by dsimp only at hright ⊢; omega)))
  · rcases hdB with hz | hz | hleft | hright
    · dsimp only at hz; omega
    · exact Or.inr (Or.inl hz)
    · exact Or.inr (Or.inr (Or.inl (by dsimp only at hleft ⊢; omega)))
    · exact Or.inr (Or.inr (Or.inr (by dsimp only at hright ⊢; omega)))

/-- In-place append reconstructs the frame and its log-object list directly
from pre-state pairwise separation and the concrete two-word update. -/
theorem log_no_growth_concrete_frame_post_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (ec : Ivl) (S : List Nat)
    (l p n cap log : BitVec 64)
    (hA : ArenaReady s) (hFW : FrameWF s S ec)
    (hpw : (frameObjects s ec).Pairwise Disj)
    (hl : memW s (ec.1 + 88) = l.toNat)
    (hn : memW s (l.toNat + 8) = n.toNat)
    (hm0 : memW s l.toNat = p.toNat)
    (hm16 : memW s (l.toNat + 16) = cap.toNat)
    (hnonnull : l.toNat ≠ 0) (hlt : n.toNat < cap.toNat)
    (hn_bound : n.toNat + 1 < 2 ^ 64)
    (hl_bound : l.toNat + 24 ≤ 2 ^ 64)
    (hp_bound : p.toNat + 8 * n.toNat + 8 ≤ 2 ^ 64)
    (hdisj : Disj (p.toNat, 8 * n.toNat + 8) (l.toNat, 24))
    (hd8 : s.memaddrs (l + 8#64)) (hdslot : s.memaddrs (p + n * 8#64)) :
    let post := {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64) else s.memory a}
    (∀ k ∈ ([8, 16, 24, 32, 40, 88, 112, 136, 144, 168, 176, 216, 232] : List Nat),
      memW post (ec.1 + k) = memW s (ec.1 + k)) →
    WordsOK post (l.toNat, 24) → Allocated post (l.toNat, 24) →
    (∀ i, i ≤ n.toNat → WordAt post (p.toNat + 8 * i)) →
    MsgOwned post S (memW s (ec.1 + 112)) → LogEntryOK post log.toNat →
    FrameWF post S ec ∧ frameLogs post ec = frameLogs s ec ∧
      frameLogObjects post ec = frameLogObjects s ec ++ logOwnedIvls post log.toNat := by
  dsimp only
  intro hfields hwords hallocated hslots hmsg hlog
  have hrecords := log_no_growth_old_record_separation_g09 l p n cap
    hA hFW hpw hl hn hm0 hm16 hnonnull hlt
  have hframe := (hfields 88 (by simp)).trans hl
  obtain ⟨hlist, hobjects⟩ := log_no_growth_semantic_post_g09 s ec S l p n cap log
    hA hFW hl hn hm0 hm16 hlt hn_bound hl_bound hp_bound hdisj hd8 hdslot hrecords
    hframe hwords hallocated hslots hlog
  obtain ⟨h0, h8, h16, _, _⟩ := log_no_growth_final_cells_g09 s l p n cap log
    hl_bound hp_bound hdisj hn_bound hm0 hm16
  obtain ⟨hWF, hbuffer⟩ := frameWF_of_log_no_growth_g09
    (post := {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64) else s.memory a})
    hFW rfl rfl hfields
    (by simpa only [hl] using h0.trans hm0.symm)
    (by simpa only [hl] using h16.trans hm16.symm)
    (by rw [hl, h8, h16]; omega)
    (by simpa only [hframe, hl] using hlist) hmsg
  exact ⟨hWF, hbuffer, hobjects⟩

/-- The two in-place append stores preserve typed world cells whenever the
existing log header and backing array are separated from that world. -/
theorem log_no_growth_final_typed_cells_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (l p n cap log : BitVec 64) (S Nd : List Nat)
    (hma : s.memaddrs = ordinaryDomain) (hWT : WorldTypedWith s S Nd)
    (hd8 : s.memaddrs (l + 8#64)) (hdslot : s.memaddrs (p + n * 8#64))
    (hl : l.toNat + 24 ≤ 2 ^ 64)
    (hp : p.toNat + 8 * cap.toNat ≤ 2 ^ 64) (hlt : n.toNat < cap.toNat)
    (hheader : ∀ i ∈ worldTypedIvls s S Nd, Disj (l.toNat, 24) i)
    (hbuffer : ∀ i ∈ worldTypedIvls s S Nd, Disj (p.toNat, 8 * cap.toNat) i) :
    let post := {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64) else s.memory a}
    SameTypedCells s post S Nd := by
  dsimp only
  have heff := log_no_growth_final_effect_g09 s l p n log hma hd8 hdslot hl (by omega)
  apply ByteRegionEffect.sameTypedCells
    (Rl := [(l.toNat + 8, 8), (p.toNat + 8 * n.toNat, 8)])
    (extra := []) hma hWT ?_ (by simp) (by simpa using heff)
  intro x hx i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · rcases hheader i hi with hz | hz | hleft | hright
    · cases hz
    · exact Or.inr (Or.inl hz)
    · exact Or.inr (Or.inr (Or.inl (by dsimp only at hleft ⊢; omega)))
    · exact Or.inr (Or.inr (Or.inr (by dsimp only at hright ⊢; omega)))
  · rcases hbuffer i hi with hz | hz | hleft | hright
    · dsimp only at hz; omega
    · exact Or.inr (Or.inl hz)
    · exact Or.inr (Or.inr (Or.inl (by dsimp only at hleft ⊢; omega)))
    · exact Or.inr (Or.inr (Or.inr (by dsimp only at hright ⊢; omega)))

/-- A newly constructed record separated from the two in-place append writes
retains its validity and owned intervals after installation in the list. -/
theorem log_no_growth_new_record_preserved_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (l p n log : BitVec 64)
    (hl : l.toNat + 24 ≤ 2 ^ 64)
    (hp : p.toNat + 8 * n.toNat + 8 ≤ 2 ^ 64)
    (hbound : log.toNat + 40 ≤ 2 ^ 64)
    (hdheader : Disj (log.toNat, 40) (l.toNat, 24))
    (hdbuffer : Disj (log.toNat, 40) (p.toNat, 8 * n.toNat + 8))
    (hlog : LogEntryOK s log.toNat) :
    let post := {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64) else s.memory a}
    LogEntryOK post log.toNat ∧ logOwnedIvls post log.toNat = logOwnedIvls s log.toNat := by
  dsimp only
  have hl8 : (l + 8#64).toNat = l.toNat + 8 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hn8 : (n * 8#64).toNat = n.toNat * 8 := by
    rw [BitVec.toNat_mul]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hs : (p + n * 8#64).toNat = p.toNat + 8 * n.toNat := by
    rw [BitVec.toNat_add, hn8, Nat.mod_eq_of_lt (by omega)]; omega
  have hrecord : ∀ k ∈ ([0, 8, 16, 24, 32] : List Nat),
      memW {s with memory := fun a =>
        if a = p + n * 8#64 then .word log
        else if a = l + 8#64 then .word (n + 1#64) else s.memory a}
        (log.toNat + k) = memW s (log.toNat + k) := by
    intro k hk
    have hkbound : k + 8 ≤ 40 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
    have hnat : (BitVec.ofNat 64 (log.toNat + k)).toNat = log.toNat + k :=
      Nat.mod_eq_of_lt (by omega)
    have hne1 : BitVec.ofNat 64 (log.toNat + k) ≠ p + n * 8#64 := by
      intro heq
      have heq' := congrArg BitVec.toNat heq
      rw [hnat, hs] at heq'
      rcases hdbuffer with h | h | h | h <;> dsimp only at h <;> omega
    have hne2 : BitVec.ofNat 64 (log.toNat + k) ≠ l + 8#64 := by
      intro heq
      have heq' := congrArg BitVec.toNat heq
      rw [hnat, hl8] at heq'
      rcases hdheader with h | h | h | h <;> dsimp only at h <;> omega
    simp only [memW, hne1, hne2, ↓reduceIte]
  exact ⟨logEntryOK_of_record_agree_g09 (s := s) rfl (le_refl _) hrecord hlog,
    logOwnedIvls_of_record_agree_g09 (s := s) rfl hrecord⟩

/-- Concrete in-place frame reconstruction needs new-record validity only
before the two finishing stores; separation transports it to their result. -/
theorem log_no_growth_frame_post_from_new_record_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (ec : Ivl) (S : List Nat)
    (l p n cap log : BitVec 64)
    (hA : ArenaReady s) (hFW : FrameWF s S ec)
    (hpw : (frameObjects s ec).Pairwise Disj)
    (hl : memW s (ec.1 + 88) = l.toNat)
    (hn : memW s (l.toNat + 8) = n.toNat)
    (hm0 : memW s l.toNat = p.toNat)
    (hm16 : memW s (l.toNat + 16) = cap.toNat)
    (hnonnull : l.toNat ≠ 0) (hlt : n.toNat < cap.toNat)
    (hn_bound : n.toNat + 1 < 2 ^ 64)
    (hl_bound : l.toNat + 24 ≤ 2 ^ 64)
    (hp_bound : p.toNat + 8 * n.toNat + 8 ≤ 2 ^ 64)
    (hdisj : Disj (p.toNat, 8 * n.toNat + 8) (l.toNat, 24))
    (hd8 : s.memaddrs (l + 8#64)) (hdslot : s.memaddrs (p + n * 8#64))
    (hlog : LogEntryOK s log.toNat)
    (hdheader : Disj (log.toNat, 40) (l.toNat, 24))
    (hdbuffer : Disj (log.toNat, 40) (p.toNat, 8 * n.toNat + 8)) :
    let post := {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64) else s.memory a}
    (∀ k ∈ ([8, 16, 24, 32, 40, 88, 112, 136, 144, 168, 176, 216, 232] : List Nat),
      memW post (ec.1 + k) = memW s (ec.1 + k)) →
    WordsOK post (l.toNat, 24) → Allocated post (l.toNat, 24) →
    (∀ i, i ≤ n.toNat → WordAt post (p.toNat + 8 * i)) →
    MsgOwned post S (memW s (ec.1 + 112)) →
    FrameWF post S ec ∧ frameLogs post ec = frameLogs s ec ∧
      frameLogObjects post ec = frameLogObjects s ec ++ logOwnedIvls s log.toNat := by
  dsimp only
  intro hfields hwords hallocated hslots hmsg
  have hheap : globN s "heap_ptr" ≤ 2 ^ 64 := by
    have hh := hA.2.2.1
    rw [R11Shards.heapLimit_val] at hh
    omega
  obtain ⟨hlog_post, howned⟩ := log_no_growth_new_record_preserved_g09 s l p n log
    hl_bound hp_bound (le_trans hlog.2.1.2 hheap) hdheader hdbuffer hlog
  obtain ⟨hWF, hbuffer, hobjects⟩ := log_no_growth_concrete_frame_post_g09 s ec S l p n cap log
    hA hFW hpw hl hn hm0 hm16 hnonnull hlt hn_bound hl_bound hp_bound hdisj
    hd8 hdslot hfields hwords hallocated hslots hmsg hlog_post
  exact ⟨hWF, hbuffer, by rw [hobjects, howned]⟩

/-- Every word contained in an interval separated from the header and used
buffer prefix survives the two in-place append writes. -/
theorem log_no_growth_protected_words_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (l p n log : BitVec 64) (o : Ivl)
    (hl : l.toNat + 24 ≤ 2 ^ 64)
    (hp : p.toNat + 8 * n.toNat + 8 ≤ 2 ^ 64)
    (hb : o.1 + o.2 ≤ 2 ^ 64)
    (hdheader : Disj o (l.toNat, 24))
    (hdbuffer : Disj o (p.toNat, 8 * n.toNat + 8)) :
    let post := {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64) else s.memory a}
    ∀ k, k + 8 ≤ o.2 → memW post (o.1 + k) = memW s (o.1 + k) := by
  dsimp only
  intro k hk
  have hl8 : (l + 8#64).toNat = l.toNat + 8 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hn8 : (n * 8#64).toNat = n.toNat * 8 := by
    rw [BitVec.toNat_mul]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hs : (p + n * 8#64).toNat = p.toNat + 8 * n.toNat := by
    rw [BitVec.toNat_add, hn8, Nat.mod_eq_of_lt (by omega)]; omega
  have hnat : (BitVec.ofNat 64 (o.1 + k)).toNat = o.1 + k :=
    Nat.mod_eq_of_lt (by omega)
  have hne1 : BitVec.ofNat 64 (o.1 + k) ≠ p + n * 8#64 := by
    intro heq
    have heq' := congrArg BitVec.toNat heq
    rw [hnat, hs] at heq'
    rcases hdbuffer with h | h | h | h <;> omega
  have hne2 : BitVec.ofNat 64 (o.1 + k) ≠ l + 8#64 := by
    intro heq
    have heq' := congrArg BitVec.toNat heq
    rw [hnat, hl8] at heq'
    rcases hdheader with h | h | h | h <;> omega
  simp only [memW, hne1, hne2, ↓reduceIte]

/-- Separation of frame and continuation records gives all chain-record
readback facts for the concrete in-place append transition. -/
theorem log_no_growth_chain_records_preserved_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (l p n log : BitVec 64)
    (hl : l.toNat + 24 ≤ 2 ^ 64)
    (hp : p.toNat + 8 * n.toNat + 8 ≤ 2 ^ 64)
    (hbounds : ∀ ec ∈ evmChain s, ec.1 + 280 ≤ 2 ^ 64 ∧ ec.2 + 104 ≤ 2 ^ 64)
    (hheader : ∀ ec ∈ evmChain s,
      Disj (ec.1, 280) (l.toNat, 24) ∧ Disj (ec.2, 104) (l.toNat, 24))
    (hbuffer : ∀ ec ∈ evmChain s,
      Disj (ec.1, 280) (p.toNat, 8 * n.toNat + 8) ∧
      Disj (ec.2, 104) (p.toNat, 8 * n.toNat + 8)) :
    let post := {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64) else s.memory a}
    ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → memW post (ec.2 + k) = memW s (ec.2 + k)) := by
  dsimp only
  intro ec hec
  exact ⟨log_no_growth_protected_words_g09 s l p n log (ec.1, 280)
    hl hp (hbounds ec hec).1 (hheader ec hec).1 (hbuffer ec hec).1,
    log_no_growth_protected_words_g09 s l p n log (ec.2, 104)
    hl hp (hbounds ec hec).2 (hheader ec hec).2 (hbuffer ec hec).2⟩

/-- Typed-cell and chain-record preservation assemble the in-place append
invariant, leaving only the changed object ownership obligations. -/
theorem evmInvAt_of_log_no_growth_cells_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (l p n cap log : BitVec 64) (S Nd : List Nat)
    (hAs : ArenaReady s) (hinv : EvmInvAt s S) (hWT : WorldTypedWith s S Nd)
    (hd8 : s.memaddrs (l + 8#64)) (hdslot : s.memaddrs (p + n * 8#64))
    (hl : l.toNat + 24 ≤ 2 ^ 64)
    (hp : p.toNat + 8 * cap.toNat ≤ 2 ^ 64) (hlt : n.toNat < cap.toNat)
    (hheaderWorld : ∀ i ∈ worldTypedIvls s S Nd, Disj (l.toNat, 24) i)
    (hbufferWorld : ∀ i ∈ worldTypedIvls s S Nd, Disj (p.toNat, 8 * cap.toNat) i)
    (hbounds : ∀ ec ∈ evmChain s, ec.1 + 280 ≤ 2 ^ 64 ∧ ec.2 + 104 ≤ 2 ^ 64)
    (hheader : ∀ ec ∈ evmChain s,
      Disj (ec.1, 280) (l.toNat, 24) ∧ Disj (ec.2, 104) (l.toNat, 24))
    (hbuffer : ∀ ec ∈ evmChain s,
      Disj (ec.1, 280) (p.toNat, 8 * n.toNat + 8) ∧
      Disj (ec.2, 104) (p.toNat, 8 * n.toNat + 8)) :
    let post := {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64) else s.memory a}
    ArenaReady post → evmChain post = evmChain s →
    (∀ ec ∈ evmChain s, FrameWF post S ec) →
    ((evmChain post).map (frameObjects post)).flatten.Pairwise Disj →
    IvlsDisj ((evmChain post).map (frameObjects post)).flatten (worldOwned s S Nd) →
    (∀ ec ∈ (evmChain s).tail, frameObjects post ec = frameObjects s ec) →
    (∀ ec ∈ (evmChain s).tail, frameLogs post ec = frameLogs s ec) →
    EvmInvAt post S := by
  dsimp only
  intro hAp hchain hframes hpairwise hdisj hobjects hlogs
  have hcell := log_no_growth_final_typed_cells_g09 s l p n cap log S Nd
    hAs.1.memaddrs hWT hd8 hdslot hl hp hlt hheaderWorld hbufferWorld
  have hrecords := log_no_growth_chain_records_preserved_g09 s l p n log
    hl (by omega) hbounds hheader hbuffer
  exact evmInvAt_of_log_growth_cells_g09 hAs hAp hinv hWT
    (le_refl _) (le_refl _) (by intros; rfl) hcell hchain
    (fun ec hec k hk _ => (hrecords ec hec).1 k hk)
    (fun ec hec k hk _ => (hrecords ec hec).2 k hk)
    hframes hpairwise hdisj hobjects hlogs

/-- With unchanged buffer extent, the head frame objects grow only by the
new record's owned intervals. -/
theorem frameObjects_of_log_no_growth_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {ec : Ivl} {newObjects : List Ivl}
    (hfields : ∀ k ∈ ([8, 24, 40, 88, 232] : List Nat),
      memW post (ec.1 + k) = memW s (ec.1 + k))
    (hret : frameRet post ec = frameRet s ec)
    (hbuffer : frameLogs post ec = frameLogs s ec)
    (hlogs : frameLogObjects post ec = frameLogObjects s ec ++ newObjects) :
    frameObjects post ec = frameObjects s ec ++ newObjects := by
  unfold frameObjects
  rw [hfields 8 (by simp), hfields 232 (by simp), hfields 24 (by simp),
    hfields 40 (by simp), hfields 88 (by simp), hret, hbuffer, hlogs, List.append_assoc]

/-- The in-place head frame stays pairwise disjoint when the new owned
intervals are internally disjoint and separated from all old frame objects. -/
theorem log_no_growth_frame_objects_pairwise_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {ec : Ivl} {newObjects : List Ivl}
    (hobjects : frameObjects post ec = frameObjects s ec ++ newObjects)
    (hold : (frameObjects s ec).Pairwise Disj)
    (hnew : newObjects.Pairwise Disj)
    (hdisj : IvlsDisj (frameObjects s ec) newObjects) :
    (frameObjects post ec).Pairwise Disj := by
  rw [hobjects]
  exact List.pairwise_append.2 ⟨hold, hnew, hdisj⟩

/-- Replacing the head object list by its append preserves chain-wide
pairwise disjointness if the new objects are separated from the old chain. -/
theorem log_no_growth_chain_objects_pairwise_g09
    (head : List Ivl) (tail : List (List Ivl)) (newObjects : List Ivl)
    (hold : (head ++ tail.flatten).Pairwise Disj)
    (hnew : newObjects.Pairwise Disj)
    (hdisj : IvlsDisj (head ++ tail.flatten) newObjects) :
    ((head ++ newObjects) ++ tail.flatten).Pairwise Disj := by
  obtain ⟨hh, ht, hht⟩ := List.pairwise_append.1 hold
  apply List.pairwise_append.2
  refine ⟨List.pairwise_append.2 ⟨hh, hnew, ?_⟩, ht, ?_⟩
  · intro x hx y hy
    exact hdisj x (List.mem_append_left _ hx) y hy
  · intro x hx y hy
    rcases List.mem_append.1 hx with hx | hx
    · exact hht x hx y hy
    · exact R11Shards.Disj.symm (hdisj y (List.mem_append_right _ hy) x hx)

/-- The concrete chain object list after an in-place head append consists of
the enlarged head followed by the unchanged tail. -/
theorem log_no_growth_chain_objects_eq_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {head : Ivl} {tail : List Ivl}
    {newObjects : List Ivl}
    (hchain : evmChain post = evmChain s)
    (hcons : evmChain s = head :: tail)
    (hhead : frameObjects post head = frameObjects s head ++ newObjects)
    (htail : ∀ ec ∈ tail, frameObjects post ec = frameObjects s ec) :
    ((evmChain post).map (frameObjects post)).flatten =
      (frameObjects s head ++ newObjects) ++ (tail.map (frameObjects s)).flatten := by
  rw [hchain, hcons, List.map_cons, List.flatten_cons, hhead]
  congr 1
  congr 1
  exact List.map_congr_left htail

/-- Head-only object append discharges both chain-wide pairwise separation
and world separation from separation of the new owned intervals. -/
theorem log_no_growth_chain_object_separation_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {head : Ivl} {tail : List Ivl}
    {newObjects world : List Ivl}
    (hchain : evmChain post = evmChain s)
    (hcons : evmChain s = head :: tail)
    (hhead : frameObjects post head = frameObjects s head ++ newObjects)
    (htail : ∀ ec ∈ tail, frameObjects post ec = frameObjects s ec)
    (hold : ((evmChain s).map (frameObjects s)).flatten.Pairwise Disj)
    (hnew : newObjects.Pairwise Disj)
    (hnewOld : IvlsDisj ((evmChain s).map (frameObjects s)).flatten newObjects)
    (holdWorld : IvlsDisj ((evmChain s).map (frameObjects s)).flatten world)
    (hnewWorld : IvlsDisj newObjects world) :
    ((evmChain post).map (frameObjects post)).flatten.Pairwise Disj ∧
      IvlsDisj ((evmChain post).map (frameObjects post)).flatten world := by
  have heq := log_no_growth_chain_objects_eq_g09 hchain hcons hhead htail
  rw [hcons, List.map_cons, List.flatten_cons] at hold hnewOld holdWorld
  rw [heq]
  refine ⟨log_no_growth_chain_objects_pairwise_g09 _ _ _ hold hnew hnewOld, ?_⟩
  intro x hx y hy
  rcases List.mem_append.1 hx with hx | hx
  · rcases List.mem_append.1 hx with hx | hx
    · exact holdWorld x (List.mem_append_left _ hx) y hy
    · exact hnewWorld x hx y hy
  · exact holdWorld x (List.mem_append_right _ hx) y hy

/-- For a head-only in-place append, new-object separation supplies the
pairwise and world-separation premises of invariant reconstruction. -/
theorem evmInvAt_of_log_no_growth_new_objects_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {head : Ivl} {tail : List Ivl} {newObjects : List Ivl}
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hinv : EvmInvAt s S) (hWT : WorldTypedWith s S Nd)
    (hglobals : post.globals = s.globals)
    (hcell : SameTypedCells s post S Nd)
    (hchain : evmChain post = evmChain s)
    (hcons : evmChain s = head :: tail)
    (hfields : ∀ ec ∈ evmChain s, ∀ k, k + 8 ≤ 280 → k % 8 = 0 →
      memW post (ec.1 + k) = memW s (ec.1 + k))
    (hcont : ∀ ec ∈ evmChain s, ∀ k, k + 8 ≤ 104 → k % 8 = 0 →
      memW post (ec.2 + k) = memW s (ec.2 + k))
    (hframes : ∀ ec ∈ evmChain s, FrameWF post S ec)
    (hhead : frameObjects post head = frameObjects s head ++ newObjects)
    (htail : ∀ ec ∈ tail, frameObjects post ec = frameObjects s ec)
    (hlogs : ∀ ec ∈ tail, frameLogs post ec = frameLogs s ec)
    (hold : ((evmChain s).map (frameObjects s)).flatten.Pairwise Disj)
    (hnew : newObjects.Pairwise Disj)
    (hnewOld : IvlsDisj ((evmChain s).map (frameObjects s)).flatten newObjects)
    (holdWorld : IvlsDisj ((evmChain s).map (frameObjects s)).flatten (worldOwned s S Nd))
    (hnewWorld : IvlsDisj newObjects (worldOwned s S Nd)) :
    EvmInvAt post S := by
  obtain ⟨hpw, hdisj⟩ := log_no_growth_chain_object_separation_g09
    hchain hcons hhead htail hold hnew hnewOld holdWorld hnewWorld
  have hg : ∀ g, globN post g = globN s g := by
    intro g
    unfold globN
    rw [hglobals]
  apply evmInvAt_of_log_growth_cells_g09 hAs hAp hinv hWT
    (by rw [hg "heap_ptr"])
    (by rw [hg "scratch_ptr"])
    (by intros; exact hg _) hcell hchain hfields hcont hframes hpw hdisj
  · simpa only [hcons, List.tail_cons] using htail
  · simpa only [hcons, List.tail_cons] using hlogs

/-- In-place append preserves header allocation and word-domain validity,
including the previously unused insertion cell in the backing array. -/
theorem log_no_growth_header_and_slots_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (ec : Ivl) (S : List Nat)
    (l p n cap log : BitVec 64)
    (hFW : FrameWF s S ec)
    (hl : memW s (ec.1 + 88) = l.toNat)
    (hm0 : memW s l.toNat = p.toNat)
    (hm16 : memW s (l.toNat + 16) = cap.toNat)
    (hlt : n.toNat < cap.toNat) :
    let post := {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64) else s.memory a}
    WordsOK post (l.toNat, 24) ∧ Allocated post (l.toNat, 24) ∧
      ∀ i, i ≤ n.toNat → WordAt post (p.toNat + 8 * i) := by
  dsimp only
  have hheader := hFW.1 (memW s (ec.1 + 88), 24) (by simp)
  rw [hl] at hheader
  have hbuffer : WordsOK s (p.toNat, 8 * cap.toNat) := by
    have hw := hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    unfold frameLogs at hw
    simpa only [hl, hm0, hm16] using hw
  have word_post : ∀ a, WordAt s a → WordAt
      {s with memory := fun a =>
        if a = p + n * 8#64 then .word log
        else if a = l + 8#64 then .word (n + 1#64) else s.memory a} a := by
    intro a ha
    obtain ⟨w, hd, hw⟩ := ha
    cases hm : (s.memory (BitVec.ofNat 64 a)) with
    | word w =>
      by_cases h1 : BitVec.ofNat 64 a = p + n * 8#64
      · exact ⟨log, hd, by dsimp only; rw [if_pos h1]⟩
      · by_cases h2 : BitVec.ofNat 64 a = l + 8#64
        · exact ⟨n + 1#64, hd, by dsimp only; rw [if_neg h1, if_pos h2]⟩
        · exact ⟨w, hd, by dsimp only; rw [if_neg h1, if_neg h2, hm]⟩
  refine ⟨⟨hheader.2.1, hheader.2.2.1, fun k hk => word_post _ (hheader.2.2.2 k hk)⟩,
    Or.inr hheader.1, ?_⟩
  intro i hi
  apply word_post
  apply hbuffer.2.2 i
  omega

/-- Frame reconstruction for in-place append derives header, insertion-cell,
and structural-field validity from the original frame and write separation. -/
theorem log_no_growth_frame_post_of_separation_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (ec : Ivl) (S : List Nat)
    (l p n cap log : BitVec 64)
    (hA : ArenaReady s) (hFW : FrameWF s S ec)
    (hpw : (frameObjects s ec).Pairwise Disj)
    (hl : memW s (ec.1 + 88) = l.toNat)
    (hn : memW s (l.toNat + 8) = n.toNat)
    (hm0 : memW s l.toNat = p.toNat)
    (hm16 : memW s (l.toNat + 16) = cap.toNat)
    (hnonnull : l.toNat ≠ 0) (hlt : n.toNat < cap.toNat)
    (hn_bound : n.toNat + 1 < 2 ^ 64)
    (hl_bound : l.toNat + 24 ≤ 2 ^ 64)
    (hp_bound : p.toNat + 8 * n.toNat + 8 ≤ 2 ^ 64)
    (hdisj : Disj (p.toNat, 8 * n.toNat + 8) (l.toNat, 24))
    (hd8 : s.memaddrs (l + 8#64)) (hdslot : s.memaddrs (p + n * 8#64))
    (hec : ec.1 + 280 ≤ 2 ^ 64)
    (hecHeader : Disj (ec.1, 280) (l.toNat, 24))
    (hecBuffer : Disj (ec.1, 280) (p.toNat, 8 * n.toNat + 8))
    (hlog : LogEntryOK s log.toNat)
    (hdheader : Disj (log.toNat, 40) (l.toNat, 24))
    (hdbuffer : Disj (log.toNat, 40) (p.toNat, 8 * n.toNat + 8)) :
    let post := {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64) else s.memory a}
    MsgOwned post S (memW s (ec.1 + 112)) →
    FrameWF post S ec ∧ frameObjects post ec = frameObjects s ec ++ logOwnedIvls s log.toNat := by
  dsimp only
  intro hmsg
  have hfields := log_no_growth_protected_words_g09 s l p n log (ec.1, 280)
    hl_bound hp_bound hec hecHeader hecBuffer
  have hfield_list : ∀ k ∈ ([8, 16, 24, 32, 40, 88, 112, 136, 144, 168, 176, 216, 232] : List Nat),
      k + 8 ≤ 280 := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  obtain ⟨hw, ha, hs⟩ := log_no_growth_header_and_slots_g09 s ec S l p n cap log
    hFW hl hm0 hm16 hlt
  obtain ⟨hWF, hb, ho⟩ := log_no_growth_frame_post_from_new_record_g09 s ec S l p n cap log
    hA hFW hpw hl hn hm0 hm16 hnonnull hlt hn_bound hl_bound hp_bound hdisj
    hd8 hdslot hlog hdheader hdbuffer (fun k hk => hfields k (hfield_list k hk)) hw ha hs hmsg
  refine ⟨hWF, frameObjects_of_log_no_growth_g09 ?_ ?_ hb ho⟩
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> exact hfields _ (by omega)
  · unfold frameRet
    rw [hfields 144 (by omega), hfields 216 (by omega)]

/-- Head-only object append preserves message ownership when the newly
attached intervals are separated from the existing message record. -/
theorem msgOwned_of_log_no_growth_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {head : Ivl} {tail : List Ivl} {newObjects : List Ivl} {m : Nat}
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hWT : WorldTypedWith s S Nd) (hcell : SameTypedCells s post S Nd)
    (hglobals : post.globals = s.globals) (hdom : post.memaddrs = s.memaddrs)
    (hchain : evmChain post = evmChain s)
    (hcons : evmChain s = head :: tail)
    (hhead : frameObjects post head = frameObjects s head ++ newObjects)
    (htail : ∀ ec ∈ tail, frameObjects post ec = frameObjects s ec)
    (hnew : ∀ o ∈ newObjects, Disj (m, 176) o)
    (hmsg : MsgOwned s S m) : MsgOwned post S m := by
  have hg : ∀ g, globN post g = globN s g := by
    intro g
    unfold globN
    rw [hglobals]
  obtain ⟨_, _, _, hfixed, _, hfoot, _, _, _⟩ := log_growth_world_preserved_g09
    hAs hAp hWT (by rw [hg "heap_ptr"]) (by rw [hg "scratch_ptr"])
    (by intros; exact hg _) hcell
  apply msgOwned_of_log_growth_cells_g09 hAs hAp hWT hcell
    (by intros; exact hg _) hdom
    ⟨by rw [hg "heap_ptr"], by rw [hg "scratch_ptr"]⟩ hfixed hfoot hchain ?_ hmsg
  intro ec hec o ho
  rw [hcons] at hec
  rcases List.mem_cons.1 hec with heq | ht
  · subst ec
    rw [hhead] at ho
    rcases List.mem_append.1 ho with ho | ho
    · exact Or.inl ho
    · exact Or.inr (hnew o ho)
  · exact Or.inl (htail ec ht ▸ ho)

/-- Readback of a suspended frame, its log header, slots and records preserves
its complete object list and backing-buffer extent. -/
theorem log_no_growth_tail_objects_congr_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {ec : Ivl}
    (hsys : globN post "vm_system_address" = globN s "vm_system_address")
    (hfields : ∀ k, k + 8 ≤ 280 → memW post (ec.1 + k) = memW s (ec.1 + k))
    (hheader : ∀ k, k + 8 ≤ 24 →
      memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k))
    (hslots : ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      memW post (memW s (memW s (ec.1 + 88)) + 8 * i) =
        memW s (memW s (memW s (ec.1 + 88)) + 8 * i))
    (hrecords : ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      ∀ k ∈ ([0, 8, 16, 24, 32] : List Nat),
        memW post (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + k) =
          memW s (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + k)) :
    frameObjects post ec = frameObjects s ec ∧ frameLogs post ec = frameLogs s ec := by
  have h0 : memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) := by
    simpa only [Nat.add_zero] using hheader 0 (by omega)
  have hlogs : frameLogObjects post ec = frameLogObjects s ec := by
    unfold frameLogObjects
    dsimp only
    rw [hfields 88 (by omega), hheader 8 (by omega)]
    apply List.flatMap_congr
    intro i hi
    have hi' := List.mem_range.1 hi
    rw [h0, hslots i hi']
    exact logOwnedIvls_of_record_agree_g09 hsys (hrecords i hi')
  have hb : frameLogs post ec = frameLogs s ec := by
    unfold frameLogs
    rw [hfields 88 (by omega), h0, hheader 16 (by omega)]
  refine ⟨?_, hb⟩
  unfold frameObjects frameRet
  rw [hfields 8 (by omega), hfields 232 (by omega), hfields 24 (by omega),
    hfields 40 (by omega), hfields 88 (by omega), hfields 144 (by omega),
    hfields 216 (by omega), hb, hlogs]

/-- Separation of suspended-frame records, log headers, buffers and live log
records from the append writes establishes unchanged tail object ownership. -/
theorem log_no_growth_tail_objects_of_separation_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (ec : Ivl) (l p n log : BitVec 64)
    (hl : l.toNat + 24 ≤ 2 ^ 64)
    (hp : p.toNat + 8 * n.toNat + 8 ≤ 2 ^ 64)
    (hprotected : ∀ o ∈ ([(ec.1, 280), (memW s (ec.1 + 88), 24),
        (memW s (memW s (ec.1 + 88)),
          8 * memW s (memW s (ec.1 + 88) + 8))] : List Ivl),
      o.1 + o.2 ≤ 2 ^ 64 ∧ Disj o (l.toNat, 24) ∧
        Disj o (p.toNat, 8 * n.toNat + 8))
    (hrecords : ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      let o := (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40)
      o.1 + o.2 ≤ 2 ^ 64 ∧ Disj o (l.toNat, 24) ∧
        Disj o (p.toNat, 8 * n.toNat + 8)) :
    let post := {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64) else s.memory a}
    frameObjects post ec = frameObjects s ec ∧ frameLogs post ec = frameLogs s ec := by
  dsimp only
  have hf := hprotected (ec.1, 280) (by simp)
  have hh := hprotected (memW s (ec.1 + 88), 24) (by simp)
  have hb := hprotected (memW s (memW s (ec.1 + 88)),
    8 * memW s (memW s (ec.1 + 88) + 8)) (by simp)
  apply log_no_growth_tail_objects_congr_g09 (s := s) (ec := ec)
    (post := {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64) else s.memory a}) rfl
    (log_no_growth_protected_words_g09 s l p n log (ec.1, 280) hl hp hf.1 hf.2.1 hf.2.2)
    (log_no_growth_protected_words_g09 s l p n log (memW s (ec.1 + 88), 24)
      hl hp hh.1 hh.2.1 hh.2.2)
  · intro i hi
    exact log_no_growth_protected_words_g09 s l p n log
      (memW s (memW s (ec.1 + 88)), 8 * memW s (memW s (ec.1 + 88) + 8))
      hl hp hb.1 hb.2.1 hb.2.2 (8 * i) (by omega)
  · intro i hi k hk
    have hr := hrecords i hi
    have hkbound : k + 8 ≤ 40 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
    exact log_no_growth_protected_words_g09 s l p n log
      (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40)
      hl hp hr.1 hr.2.1 hr.2.2 k hkbound

/-- Continuation readback suffices to preserve the active chain. -/
theorem log_chainFrom_of_cont_readback_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (fuel e c : Nat)
    (hread : ∀ ec ∈ evmChainFrom s fuel e c, ∀ k, k + 8 ≤ 104 →
      memW post (ec.2 + k) = memW s (ec.2 + k)) :
    evmChainFrom post fuel e c = evmChainFrom s fuel e c := by
  induction fuel generalizing e c with
  | zero => rfl
  | succ fuel ih =>
    have hc : (e, c) ∈ evmChainFrom s (fuel + 1) e c := by
      simp only [evmChainFrom, List.mem_cons, true_or]
    have h0 := hread (e, c) hc 0 (by omega)
    have h8 := hread (e, c) hc 8 (by omega)
    have h16 := hread (e, c) hc 16 (by omega)
    simp only [Nat.add_zero] at h0 h8 h16
    simp only [evmChainFrom, h16, h0, h8]
    split
    · rfl
    · rename_i hn
      congr 1
      apply ih
      intro ec hec k hk
      apply hread ec _ k hk
      simp only [evmChainFrom, hn, ite_false, List.mem_cons]
      exact Or.inr hec

theorem log_chain_of_cont_readback_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hev : globN post "ev" = globN s "ev")
    (hc : globN post "cur_cont" = globN s "cur_cont")
    (hread : ∀ ec ∈ evmChain s, ∀ k, k + 8 ≤ 104 →
      memW post (ec.2 + k) = memW s (ec.2 + k)) :
    evmChain post = evmChain s := by
  unfold evmChain at *
  rw [hev, hc]
  exact log_chainFrom_of_cont_readback_g09 _ _ _ hread

/-- Concrete in-place stores preserve the invariant, potential and head-memory
alignment once the head append and unchanged tail have been reconstructed. -/
theorem log_no_growth_handler_post_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (l p n cap log : BitVec 64) (S Nd : List Nat)
    (head : Ivl) (tail newObjects : List Ivl)
    (hAs : ArenaReady s) (hinv : EvmInvAt s S) (hWT : WorldTypedWith s S Nd)
    (hd8 : s.memaddrs (l + 8#64)) (hdslot : s.memaddrs (p + n * 8#64))
    (hl : l.toNat + 24 ≤ 2 ^ 64)
    (hp : p.toNat + 8 * cap.toNat ≤ 2 ^ 64) (hlt : n.toNat < cap.toNat)
    (hheaderWorld : ∀ i ∈ worldTypedIvls s S Nd, Disj (l.toNat, 24) i)
    (hbufferWorld : ∀ i ∈ worldTypedIvls s S Nd, Disj (p.toNat, 8 * cap.toNat) i)
    (hbounds : ∀ ec ∈ evmChain s, ec.1 + 280 ≤ 2 ^ 64 ∧ ec.2 + 104 ≤ 2 ^ 64)
    (hheader : ∀ ec ∈ evmChain s,
      Disj (ec.1, 280) (l.toNat, 24) ∧ Disj (ec.2, 104) (l.toNat, 24))
    (hbuffer : ∀ ec ∈ evmChain s,
      Disj (ec.1, 280) (p.toNat, 8 * n.toNat + 8) ∧
      Disj (ec.2, 104) (p.toNat, 8 * n.toNat + 8))
    (hcons : evmChain s = head :: tail)
    (hold : ((evmChain s).map (frameObjects s)).flatten.Pairwise Disj)
    (hnew : newObjects.Pairwise Disj)
    (hnewOld : IvlsDisj ((evmChain s).map (frameObjects s)).flatten newObjects)
    (holdWorld : IvlsDisj ((evmChain s).map (frameObjects s)).flatten (worldOwned s S Nd))
    (hnewWorld : IvlsDisj newObjects (worldOwned s S Nd))
    (hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s)
    (hHM : HeadMemAligned s) :
    let post := {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64) else s.memory a}
    (∀ ec ∈ evmChain s, FrameWF post S ec) →
    frameObjects post head = frameObjects s head ++ newObjects →
    (∀ ec ∈ tail, frameObjects post ec = frameObjects s ec) →
    (∀ ec ∈ tail, frameLogs post ec = frameLogs s ec) →
    EvmInv post ∧ evmR post = evmR s ∧ HeadMemAligned post := by
  dsimp only
  intro hframes hhead htail hlogs
  have hAp : ArenaReady {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64) else s.memory a} :=
    ⟨⟨hAs.1.code, hAs.1.memaddrs, hAs.1.shMemaddrs, hAs.1.baseAddr⟩,
      arenaOK_congr rfl hAs.2⟩
  have hcell := log_no_growth_final_typed_cells_g09 s l p n cap log S Nd
    hAs.1.memaddrs hWT hd8 hdslot hl hp hlt hheaderWorld hbufferWorld
  have hrecords := log_no_growth_chain_records_preserved_g09 s l p n log
    hl (by omega) hbounds hheader hbuffer
  have hchain := log_chain_of_cont_readback_g09 (s := s)
    (post := {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64) else s.memory a}) rfl rfl
    (fun ec hec k hk => (hrecords ec hec).2 k hk)
  have hinv_post := evmInvAt_of_log_no_growth_new_objects_g09 hAs hAp hinv hWT
    rfl hcell hchain hcons
    (fun ec hec k hk _ => (hrecords ec hec).1 k hk)
    (fun ec hec k hk _ => (hrecords ec hec).2 k hk)
    hframes hhead htail hlogs hold hnew hnewOld holdWorld hnewWorld
  exact log_growth_handler_post_g09 hAp hinv_post hchain
    (fun ec hec k hk _ => (hrecords ec hec).1 k hk) rfl rfl hhead_mem hHM

/-- Object-list reconstruction is independent of post-state message ownership. -/
theorem log_no_growth_objects_without_msg_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (ec : Ivl) (S : List Nat)
    (l p n cap log : BitVec 64)
    (hA : ArenaReady s) (hFW : FrameWF s S ec)
    (hpw : (frameObjects s ec).Pairwise Disj)
    (hl : memW s (ec.1 + 88) = l.toNat)
    (hn : memW s (l.toNat + 8) = n.toNat)
    (hm0 : memW s l.toNat = p.toNat)
    (hm16 : memW s (l.toNat + 16) = cap.toNat)
    (hnonnull : l.toNat ≠ 0) (hlt : n.toNat < cap.toNat)
    (hn_bound : n.toNat + 1 < 2 ^ 64)
    (hl_bound : l.toNat + 24 ≤ 2 ^ 64)
    (hp_bound : p.toNat + 8 * n.toNat + 8 ≤ 2 ^ 64)
    (hdisj : Disj (p.toNat, 8 * n.toNat + 8) (l.toNat, 24))
    (hd8 : s.memaddrs (l + 8#64)) (hdslot : s.memaddrs (p + n * 8#64))
    (hec : ec.1 + 280 ≤ 2 ^ 64)
    (hecHeader : Disj (ec.1, 280) (l.toNat, 24))
    (hecBuffer : Disj (ec.1, 280) (p.toNat, 8 * n.toNat + 8))
    (hlogBound : log.toNat + 40 ≤ 2 ^ 64)
    (hlog : LogEntryOK s log.toNat)
    (hdheader : Disj (log.toNat, 40) (l.toNat, 24))
    (hdbuffer : Disj (log.toNat, 40) (p.toNat, 8 * n.toNat + 8)) :
    let post := {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64) else s.memory a}
    frameObjects post ec = frameObjects s ec ++ logOwnedIvls s log.toNat := by
  dsimp only
  have hf := log_no_growth_protected_words_g09 s l p n log (ec.1, 280)
    hl_bound hp_bound hec hecHeader hecBuffer
  have hr := log_no_growth_old_record_separation_g09 l p n cap
    hA hFW hpw hl hn hm0 hm16 hnonnull hlt
  obtain ⟨hw, ha, hs⟩ := log_no_growth_header_and_slots_g09 s ec S l p n cap log
    hFW hl hm0 hm16 hlt
  obtain ⟨hlogPost, howned⟩ := log_no_growth_new_record_preserved_g09 s l p n log
    hl_bound hp_bound hlogBound hdheader hdbuffer hlog
  obtain ⟨_, ho⟩ := log_no_growth_semantic_post_g09 s ec S l p n cap log
    hA hFW hl hn hm0 hm16 hlt hn_bound hl_bound hp_bound hdisj hd8 hdslot hr
    ((hf 88 (by omega)).trans hl) hw ha hs hlogPost
  rw [howned] at ho
  obtain ⟨h0, _, h16, _, _⟩ := log_no_growth_final_cells_g09 s l p n cap log
    hl_bound hp_bound hdisj hn_bound hm0 hm16
  apply frameObjects_of_log_no_growth_g09 _ _ _ ho
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> exact hf _ (by omega)
  · unfold frameRet
    rw [hf 144 (by omega), hf 216 (by omega)]
  · unfold frameLogs
    rw [hf 88 (by omega), hl, h0, h16, hm0, hm16]

/-- Suspended-frame validity transports through readback of its header, slots
and live records, with message ownership established separately. -/
theorem log_tail_frameWF_of_readback_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} {ec : Ivl}
    (hFW : FrameWF s S ec) (hglobals : post.globals = s.globals)
    (hdom : post.memaddrs = s.memaddrs)
    (hfields : ∀ k, k + 8 ≤ 280 → memW post (ec.1 + k) = memW s (ec.1 + k))
    (hheader : ∀ k, k + 8 ≤ 24 →
      memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k))
    (hslots : ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      memW post (memW s (memW s (ec.1 + 88)) + 8 * i) =
        memW s (memW s (memW s (ec.1 + 88)) + 8 * i))
    (hrecords : ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      ∀ k ∈ ([0, 8, 16, 24, 32] : List Nat),
        memW post (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + k) =
          memW s (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + k))
    (hmsg : MsgOwned post S (memW s (ec.1 + 112))) : FrameWF post S ec := by
  have hg : ∀ g, globN post g = globN s g := by
    intro g; unfold globN; rw [hglobals]
  have hwAt : ∀ a, WordAt post a ↔ WordAt s a := by
    intro a
    unfold WordAt
    rw [hdom]
    constructor
    · rintro ⟨_, hd, _⟩
      cases hm : s.memory (BitVec.ofNat 64 a) with
      | word w => exact ⟨w, hd, rfl⟩
    · rintro ⟨_, hd, _⟩
      cases hm : post.memory (BitVec.ofNat 64 a) with
      | word w => exact ⟨w, hd, rfl⟩
  have hw : ∀ o, WordsOK post o ↔ WordsOK s o := by
    intro o; unfold WordsOK
    simp only [hwAt]
  have ha : ∀ o, Allocated post o ↔ Allocated s o := by
    intro o; unfold Allocated; rw [hg "heap_ptr", hg "scratch_ptr"]
  have h0 : memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) := by
    simpa only [Nat.add_zero] using hheader 0 (by omega)
  obtain ⟨_, hb⟩ := log_no_growth_tail_objects_congr_g09 (hg _) hfields hheader hslots hrecords
  have hlist : LogsListOK post (memW s (ec.1 + 88)) := by
    have hs := hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    rcases hs with hn | ⟨hwords, halloc, hn, hcap, hentries⟩
    · exact Or.inl hn
    · right
      refine ⟨(hw _).2 hwords, (ha _).2 halloc, ?_, ?_, ?_⟩
      · rw [hheader 8 (by omega)]; exact hn
      · rw [hheader 8 (by omega), hheader 16 (by omega)]; exact hcap
      · intro i hi
        rw [hheader 8 (by omega)] at hi
        obtain ⟨hword, hentry⟩ := hentries i hi
        rw [h0]
        refine ⟨?_, ?_⟩
        · exact (hwAt _).2 hword
        · rw [hslots i hi]
          exact logEntryOK_of_record_agree_g09 hdom (by rw [hg "heap_ptr"])
            (hrecords i hi) hentry
  apply frameWF_of_log_growth_g09 hFW hdom (hg _) (hg _) (by rw [hg "heap_ptr"]) (hg _)
    _ _ hlist _ _ _ hmsg
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hfields _ (by omega)
  · rw [hheader 16 (by omega)]
    exact hFW.2.2.2.2.2.2.2.2.2.2.1
  · rw [hheader 8 (by omega), hheader 16 (by omega)]
    exact hFW.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [hb, hg "heap_ptr", hg "scratch_ptr"]
    exact hFW.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [hb]; exact (hw _).2 hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Head-frame reconstruction derives its message ownership from pre-state
ownership and the independently reconstructed object append. -/
theorem log_no_growth_head_frame_owned_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (ec : Ivl) (S Nd : List Nat)
    (tail : List Ivl) (l p n cap log : BitVec 64)
    (hA : ArenaReady s) (hFW : FrameWF s S ec)
    (hWT : WorldTypedWith s S Nd)
    (hpw : (frameObjects s ec).Pairwise Disj)
    (hl : memW s (ec.1 + 88) = l.toNat)
    (hn : memW s (l.toNat + 8) = n.toNat)
    (hm0 : memW s l.toNat = p.toNat)
    (hm16 : memW s (l.toNat + 16) = cap.toNat)
    (hnonnull : l.toNat ≠ 0) (hlt : n.toNat < cap.toNat)
    (hn_bound : n.toNat + 1 < 2 ^ 64)
    (hl_bound : l.toNat + 24 ≤ 2 ^ 64)
    (hp_bound : p.toNat + 8 * n.toNat + 8 ≤ 2 ^ 64)
    (hdisj : Disj (p.toNat, 8 * n.toNat + 8) (l.toNat, 24))
    (hd8 : s.memaddrs (l + 8#64)) (hdslot : s.memaddrs (p + n * 8#64))
    (hec : ec.1 + 280 ≤ 2 ^ 64)
    (hecHeader : Disj (ec.1, 280) (l.toNat, 24))
    (hecBuffer : Disj (ec.1, 280) (p.toNat, 8 * n.toNat + 8))
    (hlogBound : log.toNat + 40 ≤ 2 ^ 64)
    (hlog : LogEntryOK s log.toNat)
    (hdheader : Disj (log.toNat, 40) (l.toNat, 24))
    (hdbuffer : Disj (log.toNat, 40) (p.toNat, 8 * n.toNat + 8))
    (hcons : evmChain s = ec :: tail)
    (hnew : ∀ o ∈ logOwnedIvls s log.toNat, Disj (memW s (ec.1 + 112), 176) o) :
    let post := {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64) else s.memory a}
    SameTypedCells s post S Nd → evmChain post = evmChain s →
    (∀ frame ∈ tail, frameObjects post frame = frameObjects s frame) →
    FrameWF post S ec ∧ frameObjects post ec = frameObjects s ec ++ logOwnedIvls s log.toNat := by
  dsimp only
  intro hcell hchain htail
  let post := {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64) else s.memory a}
  have hAp : ArenaReady post :=
    ⟨⟨hA.1.code, hA.1.memaddrs, hA.1.shMemaddrs, hA.1.baseAddr⟩,
      arenaOK_congr rfl hA.2⟩
  have hobjects := log_no_growth_objects_without_msg_g09 s ec S l p n cap log
    hA hFW hpw hl hn hm0 hm16 hnonnull hlt hn_bound hl_bound hp_bound hdisj
    hd8 hdslot hec hecHeader hecBuffer hlogBound hlog hdheader hdbuffer
  have hmsg : MsgOwned post S (memW s (ec.1 + 112)) :=
    msgOwned_of_log_no_growth_g09 hA hAp hWT hcell rfl rfl hchain hcons
      hobjects htail hnew hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact log_no_growth_frame_post_of_separation_g09 s ec S l p n cap log
    hA hFW hpw hl hn hm0 hm16 hnonnull hlt hn_bound hl_bound hp_bound hdisj
    hd8 hdslot hec hecHeader hecBuffer hlog hdheader hdbuffer hmsg

/-- Suspended-frame reconstruction also derives message ownership from the
head-only append, avoiding any post-state frame-validity assumption. -/
theorem log_tail_frame_owned_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {head ec : Ivl} {tail newObjects : List Ivl}
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hWT : WorldTypedWith s S Nd) (hcell : SameTypedCells s post S Nd)
    (hglobals : post.globals = s.globals) (hdom : post.memaddrs = s.memaddrs)
    (hchain : evmChain post = evmChain s) (hcons : evmChain s = head :: tail)
    (hhead : frameObjects post head = frameObjects s head ++ newObjects)
    (htail : ∀ frame ∈ tail, frameObjects post frame = frameObjects s frame)
    (hnew : ∀ o ∈ newObjects, Disj (memW s (ec.1 + 112), 176) o)
    (hFW : FrameWF s S ec)
    (hfields : ∀ k, k + 8 ≤ 280 → memW post (ec.1 + k) = memW s (ec.1 + k))
    (hheader : ∀ k, k + 8 ≤ 24 →
      memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k))
    (hslots : ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      memW post (memW s (memW s (ec.1 + 88)) + 8 * i) =
        memW s (memW s (memW s (ec.1 + 88)) + 8 * i))
    (hrecords : ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      ∀ k ∈ ([0, 8, 16, 24, 32] : List Nat),
        memW post (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + k) =
          memW s (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + k)) :
    FrameWF post S ec := by
  have hmsg := msgOwned_of_log_no_growth_g09 hAs hAp hWT hcell hglobals hdom
    hchain hcons hhead htail hnew hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact log_tail_frameWF_of_readback_g09 hFW hglobals hdom hfields hheader hslots hrecords hmsg

/-- Assemble all frame validity from a reconstructed head and suspended-frame
readback; message ownership for every suspended frame is derived internally. -/
theorem log_all_frames_owned_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {head : Ivl} {tail newObjects : List Ivl}
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hWT : WorldTypedWith s S Nd) (hcell : SameTypedCells s post S Nd)
    (hglobals : post.globals = s.globals) (hdom : post.memaddrs = s.memaddrs)
    (hchain : evmChain post = evmChain s) (hcons : evmChain s = head :: tail)
    (hhead : frameObjects post head = frameObjects s head ++ newObjects)
    (hheadWF : FrameWF post S head)
    (hFW : ∀ ec ∈ evmChain s, FrameWF s S ec)
    (hnew : ∀ ec ∈ tail, ∀ o ∈ newObjects, Disj (memW s (ec.1 + 112), 176) o)
    (hfields : ∀ ec ∈ tail, ∀ k, k + 8 ≤ 280 →
      memW post (ec.1 + k) = memW s (ec.1 + k))
    (hheader : ∀ ec ∈ tail, ∀ k, k + 8 ≤ 24 →
      memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k))
    (hslots : ∀ ec ∈ tail, ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      memW post (memW s (memW s (ec.1 + 88)) + 8 * i) =
        memW s (memW s (memW s (ec.1 + 88)) + 8 * i))
    (hrecords : ∀ ec ∈ tail, ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      ∀ k ∈ ([0, 8, 16, 24, 32] : List Nat),
        memW post (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + k) =
          memW s (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + k)) :
    (∀ ec ∈ evmChain s, FrameWF post S ec) ∧
    (∀ ec ∈ tail, frameObjects post ec = frameObjects s ec) ∧
    (∀ ec ∈ tail, frameLogs post ec = frameLogs s ec) := by
  have hg : globN post "vm_system_address" = globN s "vm_system_address" := by
    unfold globN; rw [hglobals]
  have ht : ∀ ec ∈ tail,
      frameObjects post ec = frameObjects s ec ∧ frameLogs post ec = frameLogs s ec := by
    intro ec hec
    exact log_no_growth_tail_objects_congr_g09 hg (hfields ec hec)
      (hheader ec hec) (hslots ec hec) (hrecords ec hec)
  refine ⟨?_, fun ec hec => (ht ec hec).1, fun ec hec => (ht ec hec).2⟩
  intro ec hec
  rw [hcons] at hec
  rcases List.mem_cons.1 hec with heq | hec
  · subst ec; exact hheadWF
  · apply log_tail_frame_owned_g09 hAs hAp hWT hcell hglobals hdom hchain hcons hhead
      (fun ec hec => (ht ec hec).1) (hnew ec hec)
      (hFW ec (by rw [hcons]; exact List.mem_cons_of_mem _ hec))
      (hfields ec hec) (hheader ec hec) (hslots ec hec) (hrecords ec hec)

/-- Assemble the invariant from head validity and suspended-frame readback,
deriving all tail ownership and separation obligations from the append. -/
theorem evmInvAt_of_log_owned_frames_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {head : Ivl} {tail newObjects : List Ivl}
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hinv : EvmInvAt s S) (hWT : WorldTypedWith s S Nd)
    (hcell : SameTypedCells s post S Nd)
    (hglobals : post.globals = s.globals) (hdom : post.memaddrs = s.memaddrs)
    (hchain : evmChain post = evmChain s) (hcons : evmChain s = head :: tail)
    (hhead : frameObjects post head = frameObjects s head ++ newObjects)
    (hheadWF : FrameWF post S head)
    (hFW : ∀ ec ∈ evmChain s, FrameWF s S ec)
    (hnewMsg : ∀ ec ∈ tail, ∀ o ∈ newObjects, Disj (memW s (ec.1 + 112), 176) o)
    (hfields : ∀ ec ∈ evmChain s, ∀ k, k + 8 ≤ 280 →
      memW post (ec.1 + k) = memW s (ec.1 + k))
    (hcont : ∀ ec ∈ evmChain s, ∀ k, k + 8 ≤ 104 →
      memW post (ec.2 + k) = memW s (ec.2 + k))
    (hheader : ∀ ec ∈ tail, ∀ k, k + 8 ≤ 24 →
      memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k))
    (hslots : ∀ ec ∈ tail, ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      memW post (memW s (memW s (ec.1 + 88)) + 8 * i) =
        memW s (memW s (memW s (ec.1 + 88)) + 8 * i))
    (hrecords : ∀ ec ∈ tail, ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      ∀ k ∈ ([0, 8, 16, 24, 32] : List Nat),
        memW post (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + k) =
          memW s (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + k))
    (hold : ((evmChain s).map (frameObjects s)).flatten.Pairwise Disj)
    (hnew : newObjects.Pairwise Disj)
    (hnewOld : IvlsDisj ((evmChain s).map (frameObjects s)).flatten newObjects)
    (holdWorld : IvlsDisj ((evmChain s).map (frameObjects s)).flatten (worldOwned s S Nd))
    (hnewWorld : IvlsDisj newObjects (worldOwned s S Nd)) :
    EvmInvAt post S := by
  have htailMem : ∀ ec ∈ tail, ec ∈ evmChain s := by
    intro ec hec; rw [hcons]; exact List.mem_cons_of_mem _ hec
  obtain ⟨hframes, hobjects, hlogs⟩ := log_all_frames_owned_g09 hAs hAp hWT hcell
    hglobals hdom hchain hcons hhead hheadWF hFW hnewMsg
    (fun ec hec => hfields ec (htailMem ec hec)) hheader hslots hrecords
  exact evmInvAt_of_log_no_growth_new_objects_g09 hAs hAp hinv hWT hglobals hcell
    hchain hcons (fun ec hec k hk _ => hfields ec hec k hk)
    (fun ec hec k hk _ => hcont ec hec k hk)
    hframes hhead hobjects hlogs hold hnew hnewOld holdWorld hnewWorld

/-- The exact no-growth log_append execution transports a semantic finishing
postcondition through the callee's local-variable cleanup and clock decrement. -/
theorem log_append_no_growth_execution_post_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (e log l n cap p : BitVec 64)
    (hcode : s.code = originalRuntimeCode) (hclock : s.clock ≠ 0)
    (he : s.locals.lookup (ofString "e") = some (.val (.word e)))
    (hlg : s.locals.lookup (ofString "log") = some (.val (.word log)))
    (hde : s.memaddrs (e + 88#64)) (hme : s.memory (e + 88#64) = .word l)
    (hd0 : s.memaddrs l) (hd8 : s.memaddrs (l + 8#64)) (hd16 : s.memaddrs (l + 16#64))
    (hm0 : s.memory l = .word p) (hm8 : s.memory (l + 8#64) = .word n)
    (hm16 : s.memory (l + 16#64) = .word cap)
    (hlt : n.toNat < cap.toNat) (hne : l ≠ l + 8#64)
    (hdslot : s.memaddrs (p + n * 8#64)) :
    let stores := {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64) else s.memory a}
    (EvmInv stores ∧ evmR stores = evmR s ∧ HeadMemAligned stores) →
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_log_append)
    out.1 = some (.returned (.val (.word 0))) ∧
      EvmInv out.2 ∧ evmR out.2 = evmR s ∧ HeadMemAligned out.2 := by
  dsimp only
  intro hpost
  let stores := {s with memory := fun a =>
    if a = p + n * 8#64 then .word log
    else if a = l + 8#64 then .word (n + 1#64) else s.memory a}
  let final := {stores with clock := s.clock - 1, locals := HolFiniteMapExact.empty.resVarEq (ofString "slot", s.locals.lookup (ofString "slot"))}
  rw [log_append_no_growth_exact_g09 s e log l n cap p hcode hclock he hlg
    hde hme hd0 hd8 hd16 hm0 hm8 hm16 hlt hne hdslot]
  dsimp only
  refine ⟨rfl, ?_, ?_, ?_⟩
  · exact localsFree_evmInv
      {s with memory := fun a =>
        if a = p + n * 8#64 then .word log
        else if a = l + 8#64 then .word (n + 1#64) else s.memory a}
      (HolFiniteMapExact.empty.resVarEq (ofString "slot", s.locals.lookup (ofString "slot")))
      (s.clock - 1) hpost.1
  · exact (evm_congr (s := stores) (t := final) rfl rfl).2.1.trans hpost.2.1
  · change HeadMemAligned final
    change EvmInv stores ∧ evmR stores = evmR s ∧ HeadMemAligned stores at hpost
    unfold HeadMemAligned at hpost ⊢
    exact hpost.2.2

/-- Concrete log_append execution closes from the owned-frame invariant
assembly, without assuming an invariant for the result of either store. -/
theorem log_append_no_growth_owned_execution_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (e log l n cap p : BitVec 64)
    (S Nd : List Nat) (head : Ivl) (tail newObjects : List Ivl)
    (hcode : s.code = originalRuntimeCode) (hclock : s.clock ≠ 0)
    (he : s.locals.lookup (ofString "e") = some (.val (.word e)))
    (hlg : s.locals.lookup (ofString "log") = some (.val (.word log)))
    (hde : s.memaddrs (e + 88#64)) (hme : s.memory (e + 88#64) = .word l)
    (hd0 : s.memaddrs l) (hd8 : s.memaddrs (l + 8#64)) (hd16 : s.memaddrs (l + 16#64))
    (hm0 : s.memory l = .word p) (hm8 : s.memory (l + 8#64) = .word n)
    (hm16 : s.memory (l + 16#64) = .word cap)
    (hlt : n.toNat < cap.toNat) (hne : l ≠ l + 8#64)
    (hdslot : s.memaddrs (p + n * 8#64))
    (hAs : ArenaReady s) (hinv : EvmInvAt s S) (hWT : WorldTypedWith s S Nd)
    (hcons : evmChain s = head :: tail)
    (hFW : ∀ ec ∈ evmChain s, FrameWF s S ec)
    (hnewMsg : ∀ ec ∈ tail, ∀ o ∈ newObjects, Disj (memW s (ec.1 + 112), 176) o)
    (hold : ((evmChain s).map (frameObjects s)).flatten.Pairwise Disj)
    (hnew : newObjects.Pairwise Disj)
    (hnewOld : IvlsDisj ((evmChain s).map (frameObjects s)).flatten newObjects)
    (holdWorld : IvlsDisj ((evmChain s).map (frameObjects s)).flatten (worldOwned s S Nd))
    (hnewWorld : IvlsDisj newObjects (worldOwned s S Nd))
    (hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s)
    (hHM : HeadMemAligned s) :
    let post := {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64) else s.memory a}
    SameTypedCells s post S Nd →
    frameObjects post head = frameObjects s head ++ newObjects →
    FrameWF post S head →
    (∀ ec ∈ evmChain s, ∀ k, k + 8 ≤ 280 →
      memW post (ec.1 + k) = memW s (ec.1 + k)) →
    (∀ ec ∈ evmChain s, ∀ k, k + 8 ≤ 104 →
      memW post (ec.2 + k) = memW s (ec.2 + k)) →
    (∀ ec ∈ tail, ∀ k, k + 8 ≤ 24 →
      memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) →
    (∀ ec ∈ tail, ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      memW post (memW s (memW s (ec.1 + 88)) + 8 * i) =
        memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) →
    (∀ ec ∈ tail, ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      ∀ k ∈ ([0, 8, 16, 24, 32] : List Nat),
        memW post (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + k) =
          memW s (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + k)) →
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_log_append)
    out.1 = some (.returned (.val (.word 0))) ∧
      EvmInv out.2 ∧ evmR out.2 = evmR s ∧ HeadMemAligned out.2 := by
  dsimp only
  intro hcell hhead hheadWF hfields hcont hheader hslots hrecords
  let post := {s with memory := fun a =>
    if a = p + n * 8#64 then .word log
    else if a = l + 8#64 then .word (n + 1#64) else s.memory a}
  have hAp : ArenaReady post :=
    ⟨⟨hAs.1.code, hAs.1.memaddrs, hAs.1.shMemaddrs, hAs.1.baseAddr⟩,
      arenaOK_congr rfl hAs.2⟩
  have hchain : evmChain post = evmChain s :=
    log_chain_of_cont_readback_g09 (s := s) (post := post) rfl rfl hcont
  have hi : EvmInvAt post S := evmInvAt_of_log_owned_frames_g09 hAs hAp hinv hWT
    hcell rfl rfl hchain hcons hhead hheadWF hFW hnewMsg hfields hcont
    hheader hslots hrecords hold hnew hnewOld holdWorld hnewWorld
  have hp := log_growth_handler_post_g09 hAp hi hchain
    (fun ec hec k hk _ => hfields ec hec k hk) rfl rfl hhead_mem hHM
  exact log_append_no_growth_execution_post_g09 s e log l n cap p hcode hclock
    he hlg hde hme hd0 hd8 hd16 hm0 hm8 hm16 hlt hne hdslot hp

/-- The growing log_append execution transports the finishing-store
postcondition through the actual callee's local-variable cleanup. -/
theorem log_append_growth_execution_post_g09 {F : Type}
    (s allocPost copyPost : PanSemStateFiniteExact 64 F) (e log l n cap p : BitVec 64)
    (hcode : s.code = originalRuntimeCode) (hclock : s.clock ≠ 0)
    (hpushclock : s.clock - 1 ≠ 0)
    (he : s.locals.lookup (ofString "e") = some (.val (.word e)))
    (hlg : s.locals.lookup (ofString "log") = some (.val (.word log)))
    (hde : s.memaddrs (e + 88#64)) (hme : s.memory (e + 88#64) = .word l)
    (hd8 : s.memaddrs (l + 8#64)) (hd16 : s.memaddrs (l + 16#64))
    (hm8 : s.memory (l + 8#64) = .word n)
    (hm16 : s.memory (l + 16#64) = .word cap)
    (hge : cap.toNat ≤ n.toNat) :
    let cal : HolFiniteMapExact MlS (ValueHOL 64) :=
      (HolFiniteMapExact.empty.update (ofString "l", .val (.word l))).update
        (ofString "esz", .val (.word 8#64))
    let entry := callEntryStateHOLFinite s cal
    let growEntry := setVarHOLFinite (ofString "cap") (.val (.word cap))
      (setVarHOLFinite (ofString "n") (.val (.word n)) entry)
    let copyEntry := setVarHOLFinite (ofString "np") (.val (.word p))
      {allocPost with locals := growEntry.locals}
    evaluateHOLFiniteState
      (callEntryStateHOLFinite growEntry (HolFiniteMapExact.empty.update
        (ofString "n", .val (.word (8#64 * cap * 2#64)))))
      (sourceFnBody Guest.Software.guestFn_alloc) =
        (some (.returned (.val (.word p))), allocPost) →
    evaluateHOLFiniteState copyEntry
      (.call (some (none, none)) (ofString "memcpy")
        [.var .local (ofString "np"), .load .one (.op .add [.var .local (ofString "l"), .const 0]),
          .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]]) =
        (none, copyPost) →
    copyPost.locals = copyEntry.locals →
    copyPost.memaddrs l → copyPost.memaddrs (l + 8#64) → copyPost.memaddrs (l + 16#64) →
    l ≠ l + 8#64 → l ≠ l + 16#64 → copyPost.memaddrs (p + n * 8#64) →
    let stores := {copyPost with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64)
      else if a = l + 16#64 then .word (cap * 2#64)
      else if a = l then HolWordLab.word p else copyPost.memory a}
    (EvmInv stores ∧ evmR stores = evmR s ∧ HeadMemAligned stores) →
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_log_append)
    out.1 = some (.returned (.val (.word 0))) ∧
      EvmInv out.2 ∧ evmR out.2 = evmR s ∧ HeadMemAligned out.2 := by
  dsimp only
  intro halloc hcopy hlocals hd0' hd8' hd16' hne8 hne16 hdslot hpost
  let stores := {copyPost with memory := fun a =>
    if a = p + n * 8#64 then .word log
    else if a = l + 8#64 then .word (n + 1#64)
    else if a = l + 16#64 then .word (cap * 2#64)
    else if a = l then HolWordLab.word p else copyPost.memory a}
  let final := {stores with locals := HolFiniteMapExact.empty.resVarEq (ofString "slot", s.locals.lookup (ofString "slot"))}
  rw [log_append_growth_exact_g09 s allocPost copyPost e log l n cap p
    hcode hclock hpushclock he hlg hde hme hd8 hd16 hm8 hm16 hge
    halloc hcopy hlocals hd0' hd8' hd16' hne8 hne16 hdslot]
  dsimp only
  refine ⟨rfl, ?_, ?_, ?_⟩
  · exact localsFree_evmInv stores final.locals stores.clock hpost.1
  · exact (evm_congr (s := stores) (t := final) rfl rfl).2.1.trans hpost.2.1
  · change HeadMemAligned final
    change EvmInv stores ∧ evmR stores = evmR s ∧ HeadMemAligned stores at hpost
    unfold HeadMemAligned at hpost ⊢
    exact hpost.2.2

/-- Every live entry of a well-formed frame has at most four topics.
Function lookup for op_log only checks the word shape of ntopics, so a
handler proof must obtain this bound from its call-site precondition. -/
theorem frameWF_live_log_topic_bound_g09 {F : Type}
    {post : PanSemStateFiniteExact 64 F} {S : List Nat} {ec : Ivl} {i log : Nat}
    (hf : FrameWF post S ec)
    (hnonnull : memW post (ec.1 + 88) ≠ 0)
    (hi : i < memW post (memW post (ec.1 + 88) + 8))
    (hslot : memW post (memW post (memW post (ec.1 + 88)) + 8 * i) = log) :
    memW post (log + 16) ≤ 4 := by
  have hl : LogsListOK post (memW post (ec.1 + 88)) := by
    unfold FrameWF at hf
    dsimp only at hf
    exact hf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rcases hl with hz | ⟨_, _, _, _, hentries⟩
  · exact False.elim (hnonnull hz)
  · have he := (hentries i hi).2
    rw [hslot] at he
    exact he.2.2.1

/-- The actual two-pop and stack-check prefix of op_log carries its bounded
parameter and head alignment into the cost/allocation continuation. -/
theorem op_log_bounded_prefix_g09 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (nt : BitVec 64) (cont : ProgHOL 64)
    (hcont : HandlerRun s0 (fun t => HeadMemAligned t ∧
      t.locals.lookup (ofString "ntopics") = some (.val (.word nt)) ∧ nt.toNat ≤ 4)
      false cont) :
    HandlerRun s0 (fun t => HeadMemAligned t ∧
      t.locals.lookup (ofString "ntopics") = some (.val (.word nt)) ∧ nt.toNat ≤ 4)
      false
      (.decCall (ofString "start") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
        (.decCall (ofString "size") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
          (.seq (.ite (.cmp .lower
            (.load .one (.op .add [.var .global (ofString "ev"), .const 16]))
            (.var .local (ofString "ntopics")))
            (.raise (ofString "EvmErr") (.const 2)) .skip) cont))) := by
  apply HandlerRun.decCall (Q := fun t => HeadMemAligned t ∧
    t.locals.lookup (ofString "ntopics") = some (.val (.word nt)) ∧ nt.toNat ≤ 4) eps_stack_pop_headMem
  · intros; trivial
  · intro t values body callee ret v post hInv hP hargs hlook hPost hchain hQc
    refine ⟨?_, ?_, hP.2.2⟩
    · exact hQc.2 hP.1
    · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        (by decide : ofString "start" ≠ ofString "ntopics")] using hP.2.1
  · apply HandlerRun.decCall (Q := fun t => HeadMemAligned t ∧
      t.locals.lookup (ofString "ntopics") = some (.val (.word nt)) ∧ nt.toNat ≤ 4) eps_stack_pop_headMem
    · intros; trivial
    · intro t values body callee ret v post hInv hP hargs hlook hPost hchain hQc
      refine ⟨?_, ?_, hP.2.2⟩
      · exact hQc.2 hP.1
      · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          (by decide : ofString "size" ≠ ofString "ntopics")] using hP.2.1
    · exact HandlerRun.seq_ite_raise_skip (fun _ _ _ hP => hP) hcont

/-- Shape-aware log prefix: both popped operands are U256 values when the
cost continuation is reached. -/
theorem op_log_shaped_prefix_g09 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (nt : BitVec 64) (cont : ProgHOL 64)
    (hcont : HandlerRun s0 (fun t => HeadMemAligned t ∧
      t.locals.lookup (ofString "ntopics") = some (.val (.word nt)) ∧ nt.toNat ≤ 4 ∧
      ∃ start size : ValueHOL 64,
        shapeEqHOL (shapeOfHOLExact start) (.comb [.one, .one, .one, .one]) = true ∧
        shapeEqHOL (shapeOfHOLExact size) (.comb [.one, .one, .one, .one]) = true ∧
        t.locals.lookup (ofString "start") = some start ∧
        t.locals.lookup (ofString "size") = some size) false cont) :
    HandlerRun s0 (fun t => HeadMemAligned t ∧
      t.locals.lookup (ofString "ntopics") = some (.val (.word nt)) ∧ nt.toNat ≤ 4)
      false
      (.decCall (ofString "start") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
        (.decCall (ofString "size") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
          (.seq (.ite (.cmp .lower
            (.load .one (.op .add [.var .global (ofString "ev"), .const 16]))
            (.var .local (ofString "ntopics")))
            (.raise (ofString "EvmErr") (.const 2)) .skip) cont))) := by
  apply HandlerRun.decCall_shaped (Q := fun t => HeadMemAligned t ∧
    t.locals.lookup (ofString "ntopics") = some (.val (.word nt)) ∧ nt.toNat ≤ 4 ∧
    ∃ start : ValueHOL 64,
      shapeEqHOL (shapeOfHOLExact start) (.comb [.one, .one, .one, .one]) = true ∧
      t.locals.lookup (ofString "start") = some start) eps_stack_pop_headMem
  · intros; trivial
  · intro t values body callee ret v post hInv hP hsh hargs hlook hPost hchain hQc
    refine ⟨hQc.2 hP.1, ?_, hP.2.2, v, hsh, ?_⟩
    · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        (by decide : ofString "start" ≠ ofString "ntopics")] using hP.2.1
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · apply HandlerRun.decCall_shaped (Q := fun t => HeadMemAligned t ∧
      t.locals.lookup (ofString "ntopics") = some (.val (.word nt)) ∧ nt.toNat ≤ 4 ∧
      ∃ start size : ValueHOL 64,
        shapeEqHOL (shapeOfHOLExact start) (.comb [.one, .one, .one, .one]) = true ∧
        shapeEqHOL (shapeOfHOLExact size) (.comb [.one, .one, .one, .one]) = true ∧
        t.locals.lookup (ofString "start") = some start ∧
        t.locals.lookup (ofString "size") = some size) eps_stack_pop_headMem
    · intros; trivial
    · intro t values body callee ret v post hInv hP hsh hargs hlook hPost hchain hQc
      obtain ⟨hHM, hnt, hnt4, start, hstart, hlstart⟩ := hP
      refine ⟨hQc.2 hHM, ?_, hnt4, start, v, hstart, hsh, ?_, ?_⟩
      · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          (by decide : ofString "size" ≠ ofString "ntopics")] using hnt
      · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          (by decide : ofString "size" ≠ ofString "start")] using hlstart
      · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · exact HandlerRun.seq_ite_raise_skip (fun _ _ _ hP => hP) hcont

/-- Saturating the popped size establishes the exact n operand while
preserving the bounded log parameters and aligned head. -/
theorem op_log_sat_size_step_g09 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (nt : BitVec 64) (start size : ValueHOL 64)
    (hsize : shapeEqHOL (shapeOfHOLExact size) (.comb [.one, .one, .one, .one]) = true)
    (cont : ProgHOL 64)
    (hcont : HandlerRun s0 (fun t => HeadMemAligned t ∧
      t.locals.lookup (ofString "ntopics") = some (.val (.word nt)) ∧ nt.toNat ≤ 4 ∧
      t.locals.lookup (ofString "start") = some start ∧
      t.locals.lookup (ofString "size") = some size ∧
      t.locals.lookup (ofString "n") = some (.val (.word (satWordG09 size)))) false cont) :
    HandlerRun s0 (fun t => HeadMemAligned t ∧
      t.locals.lookup (ofString "ntopics") = some (.val (.word nt)) ∧ nt.toNat ≤ 4 ∧
      t.locals.lookup (ofString "start") = some start ∧
      t.locals.lookup (ofString "size") = some size) false
      (.decCall (ofString "n") .one (ofString "sat_word") [.var .local (ofString "size")] cont) := by
  have hlookup : originalRuntimeCode.lookup (ofString "sat_word") =
      some ([(ofString "v", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_sat_word, .one) :=
    lookup_of_guestAst_getElem 440 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_sat_word) rfl
  apply HandlerRun.decCall (Q := fun t => HeadMemAligned t ∧
      t.locals.lookup (ofString "ntopics") = some (.val (.word nt)) ∧ nt.toNat ≤ 4 ∧
      t.locals.lookup (ofString "start") = some start ∧
      t.locals.lookup (ofString "size") = some size ∧
      t.locals.lookup (ofString "n") = some (.val (.word (satWordG09 size)))) eps_sat_word_exact_g09
  · intro t values body callee ret hc hInv hP hargs hl
    have hev : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        [.var .local (ofString "size")] = some [size] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hP.2.2.2.2]
    rw [hev] at hargs
    injection hargs with hvs
    subst hvs
    have hl' := hl
    rw [hc] at hl'
    have hcal := (one_u256_arg_lookup_g09 hlookup hl').2.2
    obtain ⟨a,b,c,d,rfl⟩ := shapeEq_comb4_iff size hsize
    exact ⟨a,b,c,d,hcal⟩
  · intro t values body callee ret v post hInv hP hargs hl hPost hchain hQc
    have hev : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        [.var .local (ofString "size")] = some [size] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hP.2.2.2.2]
    rw [hev] at hargs
    injection hargs with hvs
    subst hvs
    have hcal := (one_u256_arg_lookup_g09 hlookup hl).2.2
    have hv := hQc.2 size hcal
    subst hv
    have hHM : HeadMemAligned post := by
      rw [hQc.1]
      exact hP.1
    refine ⟨hHM, ?_, hP.2.2.1, ?_, ?_, ?_⟩
    · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        (by decide : ofString "n" ≠ ofString "ntopics")] using hP.2.1
    · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        (by decide : ofString "n" ≠ ofString "start")] using hP.2.2.2.1
    · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        (by decide : ofString "n" ≠ ofString "size")] using hP.2.2.2.2
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · exact hcont

/-- The memory-cost call establishes the aligned expansion operand while
preserving the log parameters needed by the gas and allocation stages. -/
theorem op_log_memory_cost_step_g09 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (nt : BitVec 64) (start size : ValueHOL 64) (n : BitVec 64) (cont : ProgHOL 64)
    (hcont : HandlerRun s0 (fun t => (HeadMemAligned t ∧ XCostAligned t) ∧
      t.locals.lookup (ofString "ntopics") = some (.val (.word nt)) ∧ nt.toNat ≤ 4 ∧
      t.locals.lookup (ofString "start") = some start ∧
      t.locals.lookup (ofString "size") = some size ∧
      t.locals.lookup (ofString "n") = some (.val (.word n))) false cont) :
    HandlerRun s0 (fun t => HeadMemAligned t ∧
      t.locals.lookup (ofString "ntopics") = some (.val (.word nt)) ∧ nt.toNat ≤ 4 ∧
      t.locals.lookup (ofString "start") = some start ∧
      t.locals.lookup (ofString "size") = some size ∧
      t.locals.lookup (ofString "n") = some (.val (.word n))) false
      (.decCall (ofString "x") (.comb [.one, .one]) (ofString "extend_memory_cost1")
        [.var .local (ofString "start"), .var .local (ofString "size")] cont) := by
  apply HandlerRun.decCall (Q := fun t => (HeadMemAligned t ∧ XCostAligned t) ∧
      t.locals.lookup (ofString "ntopics") = some (.val (.word nt)) ∧ nt.toNat ≤ 4 ∧
      t.locals.lookup (ofString "start") = some start ∧
      t.locals.lookup (ofString "size") = some size ∧
      t.locals.lookup (ofString "n") = some (.val (.word n))) eps_extend_memory_cost1_bounds
  · intros; trivial
  · intro t values body callee ret v post hInv hP hargs hl hPost hchain hQc
    obtain ⟨hlf, cw, ebw, rfl, heb⟩ := hQc
    refine ⟨xCostAligned_of_cost1 hP.1 hlf rfl rfl heb, ?_, hP.2.2.1, ?_, ?_, ?_⟩
    · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        (by decide : ofString "x" ≠ ofString "ntopics")] using hP.2.1
    · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        (by decide : ofString "x" ≠ ofString "start")] using hP.2.2.2.1
    · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        (by decide : ofString "x" ≠ ofString "size")] using hP.2.2.2.2.1
    · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        (by decide : ofString "x" ≠ ofString "n")] using hP.2.2.2.2.2
  · exact hcont

/-- Multiplication of data length by eight preserves the aligned expansion
and exposes both result words for the overflow branch. -/
theorem op_log_mul_cost_step_g09 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (nt : BitVec 64) (start size : ValueHOL 64) (n : BitVec 64) (cont : ProgHOL 64)
    (hcont : HandlerRun s0 (fun t => (HeadMemAligned t ∧ XCostAligned t) ∧
      t.locals.lookup (ofString "ntopics") = some (.val (.word nt)) ∧ nt.toNat ≤ 4 ∧
      t.locals.lookup (ofString "start") = some start ∧
      t.locals.lookup (ofString "size") = some size ∧
      t.locals.lookup (ofString "n") = some (.val (.word n)) ∧
      ∃ lo hi : BitVec 64, t.locals.lookup (ofString "dc") =
        some (.rStruct [.val (.word lo), .val (.word hi)])) false cont) :
    HandlerRun s0 (fun t => (HeadMemAligned t ∧ XCostAligned t) ∧
      t.locals.lookup (ofString "ntopics") = some (.val (.word nt)) ∧ nt.toNat ≤ 4 ∧
      t.locals.lookup (ofString "start") = some start ∧
      t.locals.lookup (ofString "size") = some size ∧
      t.locals.lookup (ofString "n") = some (.val (.word n))) false
      (.decCall (ofString "dc") (.comb [.one, .one]) (ofString "mul64x64")
        [.const 8, .var .local (ofString "n")] cont) := by
  apply HandlerRun.decCall_shaped (Q := fun t => (HeadMemAligned t ∧ XCostAligned t) ∧
      t.locals.lookup (ofString "ntopics") = some (.val (.word nt)) ∧ nt.toNat ≤ 4 ∧
      t.locals.lookup (ofString "start") = some start ∧
      t.locals.lookup (ofString "size") = some size ∧
      t.locals.lookup (ofString "n") = some (.val (.word n)) ∧
      ∃ lo hi : BitVec 64, t.locals.lookup (ofString "dc") =
        some (.rStruct [.val (.word lo), .val (.word hi)])) eps_mul64x64
  · intros; trivial
  · intro t values body callee ret v post hInv hP hsh hargs hl hPost hchain hQc
    rw [hQc]
    have hpair : ∃ lo hi : BitVec 64,
        v = .rStruct [.val (.word lo), .val (.word hi)] := by
      cases v with
      | val x => simp [shapeOfHOLExact, shapeEqHOL] at hsh
      | nStruct nm xs => simp [shapeOfHOLExact, shapeEqHOL] at hsh
      | rStruct xs =>
        cases xs with
        | nil => simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh
        | cons a xs =>
          cases xs with
          | nil => simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh
          | cons b xs =>
            cases xs with
            | cons c xs => simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh
            | nil =>
              cases a <;> cases b <;> simp_all [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
              rename_i a b
              cases a <;> cases b <;> simp_all [shapeOfHOLExact, shapeEqHOL]
    obtain ⟨lo, hi, rfl⟩ := hpair
    obtain ⟨⟨hHM,cw,ebw,hx,heb⟩,hnt,hbound,hs,hz,hn⟩ := hP
    refine ⟨⟨hHM, cw, ebw, ?_, heb⟩, ?_, hbound, ?_, ?_, ?_, lo, hi, ?_⟩
    all_goals simp_all [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      (by decide : ofString "dc" ≠ ofString "x"),
      (by decide : ofString "dc" ≠ ofString "ntopics"),
      (by decide : ofString "dc" ≠ ofString "start"),
      (by decide : ofString "dc" ≠ ofString "size"),
      (by decide : ofString "dc" ≠ ofString "n")]
  · exact hcont

/-- The bounded topic charge is positive, and adding memory cost yields a
positive gas operand at least as large as the memory cost. -/
theorem op_log_base_cost_step_g09 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (nt cw ebw : BitVec 64) (P : PanSemStateFiniteExact 64 F → Prop)
    (cont : ProgHOL 64)
    (hpres : ∀ t post cost, LocFrame t post → P t →
      P (setVarHOLFinite (ofString "cost") (.val (.word cost)) {post with locals := t.locals}))
    (hcont : HandlerRun s0 (fun t => P t ∧ ∃ cost : BitVec 64,
      t.locals.lookup (ofString "cost") = some (.val (.word cost)) ∧
      0 < cost.toNat ∧ cw.toNat ≤ cost.toNat) false cont) :
    HandlerRun s0 (fun t => P t ∧
      t.locals.lookup (ofString "ntopics") = some (.val (.word nt)) ∧ nt.toNat ≤ 4 ∧
      t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)])) false
      (.decCall (ofString "cost") .one (ofString "add_sat")
        [.op .add [.const 375, .panop .mul [.const 375, .var .local (ofString "ntopics")]],
         .rfield 0 (.var .local (ofString "x"))] cont) := by
  have hpos (hbound : nt.toNat ≤ 4) : 0 < (375#64 + 375#64 * nt).toNat := by
    have hm : (375#64 * nt).toNat = 375 * nt.toNat := by
      rw [BitVec.toNat_mul]
      change (375 * nt.toNat) % 2^64 = _
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_add, hm]
    change 0 < (375 + 375 * nt.toNat) % 2^64
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hev (t : PanSemStateFiniteExact 64 F)
      (hnt : t.locals.lookup (ofString "ntopics") = some (.val (.word nt)))
      (hx : t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)])) :
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        [.op .add [.const 375, .panop .mul [.const 375, .var .local (ofString "ntopics")]],
         .rfield 0 (.var .local (ofString "x"))] =
        some [.val (.word (375#64 + 375#64 * nt)), .val (.word cw)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact, evalHOLExact, hnt, hx, valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp]
  apply HandlerRun.decCall (Q := fun t => P t ∧ ∃ cost : BitVec 64,
      t.locals.lookup (ofString "cost") = some (.val (.word cost)) ∧
      0 < cost.toNat ∧ cw.toNat ≤ cost.toNat) eps_add_sat_pos_ge_b_g09
  · intro t values body callee ret hc hInv hP hargs hl
    rw [hev t hP.2.1 hP.2.2.2] at hargs
    injection hargs with hvs
    subst hvs
    have hl_orig := hc ▸ hl
    obtain ⟨_, _, a, b, heq, ha, hb⟩ := two_word_arg_lookup (by decide) lookup_add_sat hl_orig
    injection heq with hhd htl
    injection hhd with h1
    injection h1 with h2
    subst h2
    exact ⟨_, b, ha, hb, hpos hP.2.2.1⟩
  · intro t values body callee ret v post hInv hP hargs hl hPost hchain hQc
    obtain ⟨hlf, cost, rfl, hpositive, hge⟩ := hQc
    rw [hev t hP.2.1 hP.2.2.2] at hargs
    injection hargs with hvs
    subst hvs
    obtain ⟨_, _, a, b, heq, ha, hb⟩ := two_word_arg_lookup (by decide) lookup_add_sat hl
    injection heq with hhd htl
    injection htl with hhd2 _
    injection hhd2 with h1
    injection h1 with h2
    subst h2
    refine ⟨hpres t post cost hlf hP.1, cost, ?_, hpositive, hge cw hb⟩
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · exact hcont

/-- Charging a positive log cost preserves the expansion alignment and all
caller-local facts, and rules out a saturated cost on the continuing path. -/
theorem op_log_charge_step_g09 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (cost : BitVec 64) (P : HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (cont : ProgHOL 64)
    (hcont : HandlerRun s0 (fun t => (HeadMemAligned t ∧ XCostAligned t) ∧
      P t.locals ∧ cost.toNat < 2^64 - 1) true cont) :
    HandlerRun s0 (fun t => (HeadMemAligned t ∧ XCostAligned t) ∧ P t.locals ∧
      t.locals.lookup (ofString "cost") = some (.val (.word cost)) ∧ 0 < cost.toNat) false
      (.seq (.call (some (none, none)) (ofString "charge_gas")
        [.var .local (ofString "cost")]) cont) := by
  apply seq_charge_gas_exact_g09 (Q := fun t => (HeadMemAligned t ∧ XCostAligned t) ∧
      P t.locals ∧ cost.toNat < 2^64 - 1)
  · intro t w he hInv hP
    have hw : w = cost := by
      simpa [evalHOLExact, hP.2.2.1] using he.symm
    subst hw
    exact hP.2.2.2
  · intro t post amount he hlt hInv hP hPost hg hchain hmem
    have hw : amount = cost := by
      simpa [evalHOLExact, hP.2.2.1] using he.symm
    subst hw
    have hHM : HeadMemAligned post := headMemAligned_congr_head hg hmem hP.1.1
    have hHMres : HeadMemAligned {post with locals := t.locals} :=
      headMemAligned_congr_head rfl (fun _ _ => rfl) hHM
    obtain ⟨cw,ebw,hx,heb⟩ := hP.1.2
    refine ⟨⟨hHMres, cw, ebw, hx, ?_⟩, hP.2.1, hlt⟩
    rcases heb with hz | ⟨hbound,hmod,hptr⟩
    · exact Or.inl hz
    · right
      have hm32 : memW post (globN post "ev" + 32) = memW t (globN t "ev" + 32) := by
        rw [globN_congr hg]
        exact hmem 32 (by simp)
      change memW post (globN post "ev" + 32) + ebw.toNat < 2^37 ∧
        (memW post (globN post "ev" + 32) + ebw.toNat) % 8 = 0 ∧ _
      rw [hm32]
      exact ⟨hbound,hmod,hHMres.2⟩
  · exact hcont

/-- A saturated log cost cannot continue past charge_gas. -/
theorem op_log_saturated_charge_g09 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (cont : ProgHOL 64) :
    HandlerRun s0 (fun t => t.locals.lookup (ofString "cost") =
      some (.val (.word 18446744073709551615#64))) false
      (.seq (.call (some (none, none)) (ofString "charge_gas")
        [.var .local (ofString "cost")]) cont) := by
  apply seq_charge_gas_exact_g09 (Q := fun _ => False)
  · intro t w he hInv hP
    have hw : w = 18446744073709551615#64 := by
      simpa [evalHOLExact, hP] using he.symm
    subst hw
    decide
  · intro t post amount he hlt hInv hP hPost hg hchain hmem
    have hw : amount = 18446744073709551615#64 := by
      simpa [evalHOLExact, hP] using he.symm
    subst hw
    norm_num at hlt
  · intro t hc hInv hlen hR hFalse hnt
    exact False.elim hFalse

/-- The overflow assignment followed by gas charging closes independently
of the later allocation and append continuation. -/
theorem op_log_overflow_assign_charge_g09 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (cont : ProgHOL 64) :
    HandlerRun s0 (fun _ => True) false
      (.seq (.assign .local (ofString "cost") (.const 18446744073709551615#64))
        (.seq (.call (some (none, none)) (ofString "charge_gas")
          [.var .local (ofString "cost")]) cont)) := by
  apply HandlerRun.seq_assign_local (Q := fun t => t.locals.lookup (ofString "cost") =
    some (.val (.word 18446744073709551615#64)))
  · intro t v he hInv hP
    have hv : v = .val (.word 18446744073709551615#64) := by
      simpa [evalHOLExact] using he.symm
    subst hv
    simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · exact op_log_saturated_charge_g09 s0 cont

/-- The non-overflow data-cost addition preserves caller facts and a
positive gas operand through the actual local-assignment call. -/
theorem op_log_data_cost_step_g09 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (base lo hi : BitVec 64) (P : PanSemStateFiniteExact 64 F → Prop)
    (cont : ProgHOL 64)
    (hpres : ∀ t post cost, LocFrame t post → P t →
      P (setVarHOLFinite (ofString "cost") (.val (.word cost)) {post with locals := t.locals}))
    (hcont : HandlerRun s0 (fun t => P t ∧ ∃ cost : BitVec 64,
      t.locals.lookup (ofString "cost") = some (.val (.word cost)) ∧ 0 < cost.toNat) false cont) :
    HandlerRun s0 (fun t => P t ∧
      t.locals.lookup (ofString "cost") = some (.val (.word base)) ∧ 0 < base.toNat ∧
      t.locals.lookup (ofString "dc") = some (.rStruct [.val (.word lo), .val (.word hi)])) false
      (.seq (.call (some (some (.local, ofString "cost"), none)) (ofString "add_sat")
        [.var .local (ofString "cost"), .rfield 0 (.var .local (ofString "dc"))]) cont) := by
  have hev (t : PanSemStateFiniteExact 64 F)
      (hc : t.locals.lookup (ofString "cost") = some (.val (.word base)))
      (hd : t.locals.lookup (ofString "dc") = some (.rStruct [.val (.word lo), .val (.word hi)])) :
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        [.var .local (ofString "cost"), .rfield 0 (.var .local (ofString "dc"))] =
        some [.val (.word base), .val (.word lo)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hc, hd]
  apply HandlerRun.seq_call_assign_local (Q := fun t => P t ∧ ∃ cost : BitVec 64,
      t.locals.lookup (ofString "cost") = some (.val (.word cost)) ∧ 0 < cost.toNat) eps_add_sat_pos
  · intro t values body callee ret hc hInv hP hargs hl
    rw [hev t hP.2.1 hP.2.2.2] at hargs
    injection hargs with hvs
    subst hvs
    have hl_orig := hc ▸ hl
    obtain ⟨_, _, a, b, heq, ha, hb⟩ := two_word_arg_lookup (by decide) lookup_add_sat hl_orig
    injection heq with hhd htl
    injection hhd with h1
    injection h1 with h2
    subst h2
    exact ⟨_, ha, hP.2.2.1⟩
  · intro t values body callee ret v post hInv hP hargs hl hPost hchain hQc
    obtain ⟨hlf, cost, rfl, hpositive⟩ := hQc
    refine ⟨hpres t post cost hlf hP.1, cost, ?_, hpositive⟩
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · exact hcont

/-- Both concrete data-cost branches compose with gas charging; overflow
closes immediately and the ordinary branch supplies a positive cost. -/
theorem op_log_data_cost_branch_g09 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (base lo hi : BitVec 64) (P : PanSemStateFiniteExact 64 F → Prop)
    (cont : ProgHOL 64)
    (hpres : ∀ t post cost, LocFrame t post → P t →
      P (setVarHOLFinite (ofString "cost") (.val (.word cost)) {post with locals := t.locals}))
    (hcont : HandlerRun s0 (fun t => P t ∧ ∃ cost : BitVec 64,
      t.locals.lookup (ofString "cost") = some (.val (.word cost)) ∧ 0 < cost.toNat) false
      (.seq (.call (some (none, none)) (ofString "charge_gas")
        [.var .local (ofString "cost")]) cont)) :
    HandlerRun s0 (fun t => P t ∧
      t.locals.lookup (ofString "cost") = some (.val (.word base)) ∧ 0 < base.toNat ∧
      t.locals.lookup (ofString "dc") = some (.rStruct [.val (.word lo), .val (.word hi)])) false
      (.seq (.ite (.cmp .notEqual (.rfield 1 (.var .local (ofString "dc"))) (.const 0))
        (.assign .local (ofString "cost") (.const 18446744073709551615#64))
        (.call (some (some (.local, ofString "cost"), none)) (ofString "add_sat")
          [.var .local (ofString "cost"), .rfield 0 (.var .local (ofString "dc"))]))
        (.seq (.call (some (none, none)) (ofString "charge_gas")
          [.var .local (ofString "cost")]) cont)) := by
  apply HandlerRun.seq_ite_unit
  · intro t w he hn s hc hInv hlen hR hP hnt
    exact op_log_overflow_assign_charge_g09 s0 cont s hc hInv hlen hR trivial hnt
  · intro t he
    exact op_log_data_cost_step_g09 s0 base lo hi P _ hpres hcont

/-- Initialize the concrete topic loop at zero, preserving the owned fresh
buffer and exposing unchanged caller locals to the post-loop continuation. -/
theorem op_log_topics_init_step_g09 {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {nt topics qw : BitVec 64} {cont : ProgHOL 64}
    (hcode : s.code = originalRuntimeCode) (hInvW : EvmInvWith s S Nd)
    (hlen : (evmChain s).length = (evmChain s0).length) (hR : evmR s < evmR s0)
    (hnt4 : nt.toNat ≤ 4)
    (hfit : topics.toNat + (32 * nt.toNat + 8) ≤ qw.toNat)
    (hq : qw.toNat ≤ heapLimit) (ha : topics.toNat % 8 = 0) (hlo : sourceBase ≤ topics.toNat)
    (hdj : IvlsDisj [(topics.toNat, qw.toNat - topics.toNat)]
      (worldTypedIvls s S Nd ++ ((evmChain s).map (frameObjects s)).flatten))
    (hntlk : s.locals.lookup (ofString "ntopics") = some (.val (.word nt)))
    (htlk : s.locals.lookup (ofString "topics") = some (.val (.word topics)))
    (hcont : ∀ (last : PanSemStateFiniteExact 64 F),
      last.code = originalRuntimeCode → EvmInvWith last S Nd →
      (evmChain last).length = (evmChain s0).length → evmR last < evmR s0 →
      globN last "heap_ptr" = globN s "heap_ptr" →
      (HeadMemAligned s → HeadMemAligned last) →
      IvlsDisj [(topics.toNat, qw.toNat - topics.toNat)]
        (worldTypedIvls last S Nd ++ ((evmChain last).map (frameObjects last)).flatten) →
      (∀ nm : MlS, nm ≠ ofString "i" → nm ≠ ofString "t" → last.locals.lookup nm = s.locals.lookup nm) →
      (evaluateHOLFiniteState last cont).1 ≠ some .timeOut →
      OpDispatchPost s0 (evaluateHOLFiniteState last cont).1 (evaluateHOLFiniteState last cont).2)
    (hnt : (evaluateHOLFiniteState s (.dec (ofString "i") .one (.const 0)
      (.seq opLogWhileProg cont))).1 ≠ some .timeOut) :
    OpDispatchPost s0
      (evaluateHOLFiniteState s (.dec (ofString "i") .one (.const 0) (.seq opLogWhileProg cont))).1
      (evaluateHOLFiniteState s (.dec (ofString "i") .one (.const 0) (.seq opLogWhileProg cont))).2 := by
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  simp only [evalHOLFinite, evalHOLExact, shapeOfHOLExact, shapeEqHOL, Bool.true_and,
    Bool.and_true, ↓reduceIte] at hnt ⊢
  let si := setVarHOLFinite (ofString "i") (.val (.word 0)) s
  have hiw : EvmInvWith si S Nd := evmInvWith_localsFree (s := s) si.locals s.clock hInvW
  have hi : si.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hntsi : si.locals.lookup (ofString "ntopics") = some (.val (.word nt)) := by
    simpa [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      (by decide : ofString "i" ≠ ofString "ntopics")] using hntlk
  have htpsi : si.locals.lookup (ofString "topics") = some (.val (.word topics)) := by
    simpa [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      (by decide : ofString "i" ≠ ofString "topics")] using htlk
  have hcongr := evm_congr (s := s) (t := si) rfl rfl
  have hch : evmChain si = evmChain s := evmChain_congr (s := s) (t := si) rfl rfl
  have hrsi : evmR si = evmR s := hcongr.2.1
  have hdjsi : IvlsDisj [(topics.toNat, qw.toNat - topics.toNat)]
      (worldTypedIvls si S Nd ++ ((evmChain si).map (frameObjects si)).flatten) := by
    rw [worldTypedIvls_congr_mg_g09 (s := s) (t := si) rfl rfl,
      map_frameObjects_congr_mg_g09 (s := s) (t := si) rfl rfl]
    exact hdj
  have hloop := op_log_topic_while_step_g09 (s0 := s0) (S := S) (Nd := Nd) (nt := nt)
    (topics := topics) (qw := qw) (cont := cont) nt.toNat si 0 (by simp) hnt4
    hcode hiw (by rw [hch]; exact hlen) (by rw [hrsi]; exact hR)
    hfit hq ha hlo hdjsi hi hntsi htpsi
  change OpDispatchPost s0 (evaluateHOLFiniteState si (.seq opLogWhileProg cont)).1
    { (evaluateHOLFiniteState si (.seq opLogWhileProg cont)).2 with
      locals := ((evaluateHOLFiniteState si (.seq opLogWhileProg cont)).2.locals).resVarEq
        (ofString "i", s.locals.lookup (ofString "i")) }
  apply opDispatchPost_congr_lc (s := s0) (s' := s0)
    (post := (evaluateHOLFiniteState si (.seq opLogWhileProg cont)).2) rfl rfl rfl
  apply hloop
  · intro last hc hw hl hr hp hm hdj' hlk hn
    apply hcont last hc hw hl hr hp hm hdj'
    · intro nm hni hnt'
      rw [hlk nm hni hnt']
      simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hni, Ne.symm hni]
    · exact hn
  · exact hnt

/-- Allocate the bounded topic buffer and execute its initialized loop,
delivering separated ownership and unchanged remaining locals downstream. -/
theorem op_log_topics_alloc_loop_g09 {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {nt : BitVec 64} {cont : ProgHOL 64}
    (hcode : s.code = originalRuntimeCode) (hInvW : EvmInvWith s S Nd)
    (hlen : (evmChain s).length = (evmChain s0).length) (hR : evmR s < evmR s0)
    (hnt4 : nt.toNat ≤ 4) (hHM : HeadMemAligned s)
    (hntlk : s.locals.lookup (ofString "ntopics") = some (.val (.word nt)))
    (hcont : ∀ (topics qw : BitVec 64) (last : PanSemStateFiniteExact 64 F),
      last.code = originalRuntimeCode → EvmInvWith last S Nd →
      (evmChain last).length = (evmChain s0).length → evmR last < evmR s0 →
      HeadMemAligned last → globN last "heap_ptr" = qw.toNat →
      topics.toNat + (32 * nt.toNat + 8) ≤ qw.toNat → qw.toNat ≤ heapLimit →
      topics.toNat % 8 = 0 → sourceBase ≤ topics.toNat →
      IvlsDisj [(topics.toNat, qw.toNat - topics.toNat)]
        (worldTypedIvls last S Nd ++ ((evmChain last).map (frameObjects last)).flatten) →
      last.locals.lookup (ofString "topics") = some (.val (.word topics)) →
      (∀ nm : MlS, nm ≠ ofString "i" → nm ≠ ofString "t" → nm ≠ ofString "topics" →
        last.locals.lookup nm = s.locals.lookup nm) →
      (evaluateHOLFiniteState last cont).1 ≠ some .timeOut →
      OpDispatchPost s0 (evaluateHOLFiniteState last cont).1 (evaluateHOLFiniteState last cont).2)
    (hnt : (evaluateHOLFiniteState s (.decCall (ofString "topics") .one (ofString "alloc")
      [.op .add [.panop .mul [.var .local (ofString "ntopics"), .const 32], .const 8]]
      (.dec (ofString "i") .one (.const 0) (.seq opLogWhileProg cont)))).1 ≠ some .timeOut) :
    OpDispatchPost s0
      (evaluateHOLFiniteState s (.decCall (ofString "topics") .one (ofString "alloc")
        [.op .add [.panop .mul [.var .local (ofString "ntopics"), .const 32], .const 8]]
        (.dec (ofString "i") .one (.const 0) (.seq opLogWhileProg cont)))).1
      (evaluateHOLFiniteState s (.decCall (ofString "topics") .one (ofString "alloc")
        [.op .add [.panop .mul [.var .local (ofString "ntopics"), .const 32], .const 8]]
        (.dec (ofString "i") .one (.const 0) (.seq opLogWhileProg cont)))).2 := by
  have hsz : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.panop .mul [.var .local (ofString "ntopics"), .const 32], .const 8]) =
      some (.val (.word (nt * 32#64 + 8#64))) := by
    simp [evalHOLExact, evalListHOLExact, hntlk, valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp]
  have hn : (nt * 32#64 + 8#64).toNat = 32 * nt.toNat + 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_mul]
    change ((nt.toNat * 32) % 2^64 + 8) % 2^64 = _
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  apply decCall_alloc_step_g09 (s0 := s0) (s := s) (charged := true) hcode hInvW hlen hR hsz hnt
  intro topics qw allocated hc hw hworld hframes hchain hpotential hhead hg hm hdom hl hp hq hfit hlim ha hqa hlo hwords hdj hncont
  have hnt_a : allocated.locals.lookup (ofString "ntopics") = some (.val (.word nt)) := by
    rw [hl]
    simpa [HolFiniteMapExact.lookup_update, FUPDATE,
      (by decide : ofString "topics" ≠ ofString "ntopics")] using hntlk
  have htopics_a : allocated.locals.lookup (ofString "topics") = some (.val (.word topics)) := by
    rw [hl]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hfit' : topics.toNat + (32 * nt.toNat + 8) ≤ qw.toNat := by rwa [hn] at hfit
  apply op_log_topics_init_step_g09 hc hw (by rw [hchain]; exact hlen)
    (by rw [hpotential]; exact hR) hnt4 hfit' hlim ha hlo hdj hnt_a htopics_a
  · intro last hcL hwL hlL hrL hpL hmL hdjL hlk hnL
    apply hcont topics qw last hcL hwL hlL hrL (hmL (hhead hHM)) (hpL.trans hq)
      hfit' hlim ha hlo hdjL
    · rw [hlk (ofString "topics") (by decide) (by decide)]
      exact htopics_a
    · intro nm hni hnt' hntop
      rw [hlk nm hni hnt', hl]
      simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hntop]
    · exact hnL
  · exact hncont

/-- Compose the record and address allocations, retaining their separated
ownership and the caller locals needed by record construction. -/
theorem op_log_record_allocations_g09 {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {cont : ProgHOL 64}
    (hcode : s.code = originalRuntimeCode) (hInvW : EvmInvWith s S Nd)
    (hlen : (evmChain s).length = (evmChain s0).length) (hR : evmR s < evmR s0)
    (hHM : HeadMemAligned s)
    (hcont : ∀ (log address finish : BitVec 64) (last : PanSemStateFiniteExact 64 F),
      last.code = originalRuntimeCode → EvmInvWith last S Nd →
      (evmChain last).length = (evmChain s0).length → evmR last < evmR s0 →
      HeadMemAligned last →
      worldTypedIvls last S Nd = worldTypedIvls s S Nd →
      (evmChain last).map (frameObjects last) = (evmChain s).map (frameObjects s) →
      last.memory = s.memory → last.memaddrs = s.memaddrs →
      globN s "heap_ptr" = log.toNat → globN last "heap_ptr" = finish.toNat →
      log.toNat + 40 ≤ address.toNat → address.toNat + 24 ≤ finish.toNat →
      finish.toNat ≤ heapLimit → log.toNat % 8 = 0 → address.toNat % 8 = 0 →
      sourceBase ≤ log.toNat → sourceBase ≤ address.toNat →
      IvlsDisj [(log.toNat, address.toNat - log.toNat),
        (address.toNat, finish.toNat - address.toNat)]
        (worldTypedIvls last S Nd ++ ((evmChain last).map (frameObjects last)).flatten) →
      last.locals.lookup (ofString "log") = some (.val (.word log)) →
      last.locals.lookup (ofString "log_address") = some (.val (.word address)) →
      (∀ nm : MlS, nm ≠ ofString "log" → nm ≠ ofString "log_address" →
        last.locals.lookup nm = s.locals.lookup nm) →
      (evaluateHOLFiniteState last cont).1 ≠ some .timeOut →
      OpDispatchPost s0 (evaluateHOLFiniteState last cont).1 (evaluateHOLFiniteState last cont).2)
    (hnt : (evaluateHOLFiniteState s (.decCall (ofString "log") .one (ofString "alloc") [.const 40]
      (.decCall (ofString "log_address") .one (ofString "alloc") [.const 24] cont))).1 ≠ some .timeOut) :
    OpDispatchPost s0
      (evaluateHOLFiniteState s (.decCall (ofString "log") .one (ofString "alloc") [.const 40]
        (.decCall (ofString "log_address") .one (ofString "alloc") [.const 24] cont))).1
      (evaluateHOLFiniteState s (.decCall (ofString "log") .one (ofString "alloc") [.const 40]
        (.decCall (ofString "log_address") .one (ofString "alloc") [.const 24] cont))).2 := by
  apply decCall_alloc_step_g09 (s0 := s0) (s := s) (charged := true) (nw := 40#64) hcode hInvW hlen hR rfl hnt
  intro log next first hc1 hw1 hwt1 hfo1 hch1 hr1 hhm1 hg1 hm1 hd1 hl1 hp1 hq1 hfit1 hlim1 ha1 hqa1 hlo1 hwords1 hdj1 hn1
  apply decCall_alloc_step_g09 (s0 := s0) (s := first) (charged := true) (nw := 24#64) hc1 hw1
    (by rw [hch1]; exact hlen) (by rw [hr1]; exact hR) rfl hn1
  intro address finish last hc2 hw2 hwt2 hfo2 hch2 hr2 hhm2 hg2 hm2 hd2 hl2 hp2 hq2 hfit2 hlim2 ha2 hqa2 hlo2 hwords2 hdj2 hn2
  have haddr : next.toNat = address.toNat := hq1.symm.trans hp2
  have hdjFirst : IvlsDisj [(log.toNat, address.toNat - log.toNat)]
      (worldTypedIvls last S Nd ++ ((evmChain last).map (frameObjects last)).flatten) := by
    rw [hwt2, hfo2, ← haddr]
    exact hdj1
  apply hcont log address finish last hc2 hw2
    (by rw [hch2,hch1]; exact hlen) (by rw [hr2,hr1]; exact hR)
    (hhm2 (hhm1 hHM)) (hwt2.trans hwt1) (hfo2.trans hfo1)
    (hm2.trans hm1) (hd2.trans hd1) hp1 hq2
    (by simpa only [show (40#64).toNat = 40 from rfl, haddr] using hfit1)
    hfit2 hlim2 ha1 ha2 hlo1 hlo2
  · intro a ha b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact hdjFirst _ (by simp) b hb
    · exact hdj2 _ (by simp) b hb
  · rw [hl2, hl1]
    simp [HolFiniteMapExact.lookup_update, FUPDATE,
      (by decide : ofString "log_address" ≠ ofString "log")]
  · rw [hl2]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  · intro nm hnlog hnaddr
    rw [hl2,hl1]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hnlog, Ne.symm hnaddr]
  · exact hn2

/-- Exact effects of the three header stores in log construction. -/
theorem op_log_header_stores_exact_g09 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (log address topics nt : BitVec 64)
    (hl : s.locals.lookup (ofString "log") = some (.val (.word log)))
    (ha : s.locals.lookup (ofString "log_address") = some (.val (.word address)))
    (ht : s.locals.lookup (ofString "topics") = some (.val (.word topics)))
    (hn : s.locals.lookup (ofString "ntopics") = some (.val (.word nt)))
    (hd0 : s.memaddrs log) (hd8 : s.memaddrs (log + 8#64))
    (hd16 : s.memaddrs (log + 16#64)) :
    evaluateHOLFiniteState s
      (.seq (.store (.op .add [.var .local (ofString "log"), .const 0])
          (.var .local (ofString "log_address")))
        (.seq (.store (.op .add [.var .local (ofString "log"), .const 8])
          (.var .local (ofString "topics")))
          (.store (.op .add [.var .local (ofString "log"), .const 16])
            (.var .local (ofString "ntopics"))))) =
      (none, {s with memory := fun a => if a = log + 16#64 then .word nt else
        if a = log + 8#64 then .word topics else if a = log then .word address else s.memory a}) := by
  simp [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store,
    evalHOLExact, evalListHOLExact, hl, ha, ht, hn, valueIsWord, valueWord,
    wordOpHOL, wordOp, flattenHOL, panMemStoresHOL, panMemStoreHOL, hd0, hd8, hd16]

/-- Exact effects of the final two data-field stores before log_append. -/
theorem op_log_data_stores_exact_g09 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (log data n : BitVec 64)
    (hl : s.locals.lookup (ofString "log") = some (.val (.word log)))
    (hd : s.locals.lookup (ofString "data") = some (.val (.word data)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hd24 : s.memaddrs (log + 24#64)) (hd32 : s.memaddrs (log + 32#64)) :
    evaluateHOLFiniteState s
      (.seq (.store (.op .add [.var .local (ofString "log"), .const 24])
          (.var .local (ofString "data")))
        (.store (.op .add [.var .local (ofString "log"), .const 32])
          (.var .local (ofString "n")))) =
      (none, {s with memory := fun a => if a = log + 32#64 then .word n else
        if a = log + 24#64 then .word data else s.memory a}) := by
  simp [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store,
    evalHOLExact, evalListHOLExact, hl, hd, hn, valueIsWord, valueWord,
    wordOpHOL, wordOp, flattenHOL, panMemStoresHOL, panMemStoreHOL, hd24, hd32]

/-- The log expansion call preserves all caller-local operands. -/
theorem op_log_expand_step_g09 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (cw ebw : BitVec 64) (P : HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (cont : ProgHOL 64)
    (hcont : HandlerRun s0 (fun t => P t.locals) true cont) :
    HandlerRun s0 (fun t => P t.locals ∧
      t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
      (ebw = 0#64 ∨
        (memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
         (memW t (globN t "ev" + 32) + ebw.toNat) % 8 = 0 ∧
         memW t (globN t "ev" + 24) + memW t (globN t "ev" + 40) = globN t "frame_mem_ptr"))) true
      (.seq (.call (some (none, none)) (ofString "extend_memory")
        [.rfield 1 (.var .local (ofString "x"))]) cont) := by
  apply HandlerRun.seq_call (Q := fun t => P t.locals) eps_extend_memory_length_g09
  · intro t values body callee ret hc hInv hP hargs hl
    have hev : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        [.rfield 1 (.var .local (ofString "x"))] = some [.val (.word ebw)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hP.2.1]
    rw [hev] at hargs
    injection hargs with hvs
    subst hvs
    rw [hc] at hl
    obtain ⟨_, _, w, heq, hw⟩ := one_word_arg_lookup lookup_extend_memory hl
    injection heq with h1
    injection h1 with h2
    subst h2
    exact ⟨ebw, hw, hP.2.2⟩
  · intro t values body callee ret v post hInv hP hargs hl hPost hchain hQc
    exact hP.1
  · exact hcont

/-- Allocate the padded log-data buffer, exposing its exact separated extent. -/
theorem op_log_data_allocation_g09 {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {n : BitVec 64} {cont : ProgHOL 64}
    (hcode : s.code = originalRuntimeCode) (hInvW : EvmInvWith s S Nd)
    (hlen : (evmChain s).length = (evmChain s0).length) (hR : evmR s < evmR s0)
    (hHM : HeadMemAligned s) (hnb : n.toNat < 2^37)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hcont : ∀ (data finish : BitVec 64) (last : PanSemStateFiniteExact 64 F),
      last.code = originalRuntimeCode → EvmInvWith last S Nd →
      (evmChain last).length = (evmChain s0).length → evmR last < evmR s0 →
      HeadMemAligned last →
      worldTypedIvls last S Nd = worldTypedIvls s S Nd →
      (evmChain last).map (frameObjects last) = (evmChain s).map (frameObjects s) →
      last.memory = s.memory → last.memaddrs = s.memaddrs →
      globN s "heap_ptr" = data.toNat → globN last "heap_ptr" = finish.toNat →
      data.toNat + n.toNat + 8 ≤ finish.toNat → finish.toNat ≤ heapLimit →
      data.toNat % 8 = 0 → sourceBase ≤ data.toNat →
      WordsOK last (data.toNat, finish.toNat - data.toNat) →
      IvlsDisj [(data.toNat, finish.toNat - data.toNat)]
        (worldTypedIvls last S Nd ++ ((evmChain last).map (frameObjects last)).flatten) →
      last.locals.lookup (ofString "data") = some (.val (.word data)) →
      (∀ nm : MlS, nm ≠ ofString "data" → last.locals.lookup nm = s.locals.lookup nm) →
      (evaluateHOLFiniteState last cont).1 ≠ some .timeOut →
      OpDispatchPost s0 (evaluateHOLFiniteState last cont).1 (evaluateHOLFiniteState last cont).2)
    (hnt : (evaluateHOLFiniteState s (.decCall (ofString "data") .one (ofString "alloc")
      [.op .add [.var .local (ofString "n"), .const 8]] cont)).1 ≠ some .timeOut) :
    OpDispatchPost s0
      (evaluateHOLFiniteState s (.decCall (ofString "data") .one (ofString "alloc")
        [.op .add [.var .local (ofString "n"), .const 8]] cont)).1
      (evaluateHOLFiniteState s (.decCall (ofString "data") .one (ofString "alloc")
        [.op .add [.var .local (ofString "n"), .const 8]] cont)).2 := by
  have he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "n"), .const 8]) = some (.val (.word (n + 8#64))) := by
    simp [evalHOLExact, evalListHOLExact, hn, wordOpHOL, wordOp, valueIsWord, valueWord]
  have hsum : (n + 8#64).toNat = n.toNat + 8 := by
    rw [BitVec.toNat_add]
    change (n.toNat + 8) % 2^64 = _
    exact Nat.mod_eq_of_lt (by omega)
  apply decCall_alloc_step_g09 (s0 := s0) (s := s) (charged := true) hcode hInvW hlen hR he hnt
  intro data finish last hc hw hworld hframes hchain hpotential hhead hg hm hdom hl hp hq hfit hlim ha hqa hlo hwords hdj hncont
  apply hcont data finish last hc hw (by rw [hchain]; exact hlen)
    (by rw [hpotential]; exact hR) (hhead hHM) hworld hframes hm hdom hp hq
    (by rw [hsum] at hfit; omega) hlim ha hlo hwords hdj
  · rw [hl]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  · intro nm hne
    rw [hl]; simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne]
  · exact hncont

/-- Concrete record-field readback and allocation extents establish log validity. -/
theorem op_log_record_valid_g09 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (log address topics data nt n : BitVec 64)
    (hwords : WordsOK s (log.toNat, 40))
    (hl : sourceBase ≤ log.toNat) (hlend : log.toNat + 40 ≤ globN s "heap_ptr")
    (ha : sourceBase ≤ address.toNat) (haend : address.toNat + 20 ≤ globN s "heap_ptr")
    (ht : sourceBase ≤ topics.toNat) (htend : topics.toNat + 32 * nt.toNat ≤ globN s "heap_ptr")
    (hd : sourceBase ≤ data.toNat) (hdend : data.toNat + n.toNat ≤ globN s "heap_ptr")
    (hnt : nt.toNat ≤ 4) (hn : n.toNat < 2^32)
    (h0 : memW s log.toNat = address.toNat)
    (h8 : memW s (log.toNat + 8) = topics.toNat)
    (h16 : memW s (log.toNat + 16) = nt.toNat)
    (h24 : memW s (log.toNat + 24) = data.toNat)
    (h32 : memW s (log.toNat + 32) = n.toNat) :
    LogEntryOK s log.toNat := by
  unfold LogEntryOK
  rw [h0, h8, h16, h24, h32]
  exact ⟨hwords, ⟨hl, hlend⟩, hnt, hn, ⟨ha, haend⟩, ⟨ht, htend⟩, ⟨hd, hdend⟩⟩

/-- The data-field writes have a byte-accurate effect confined to the record. -/
theorem op_log_data_stores_effect_g09 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (log data n : BitVec 64) (hma : s.memaddrs = ordinaryDomain)
    (hb : log.toNat + 40 ≤ 2^64)
    (hd24 : s.memaddrs (log + 24#64)) (hd32 : s.memaddrs (log + 32#64)) :
    ByteRegionEffect s {s with memory := fun a => if a = log + 32#64 then .word n else
      if a = log + 24#64 then .word data else s.memory a} [(log.toNat, 40)] := by
  have h24 : (log + 24#64).toNat = log.toNat + 24 := by
    rw [BitVec.toNat_add]
    change (log.toNat + 24) % 2^64 = _
    exact Nat.mod_eq_of_lt (by omega)
  have h32 : (log + 32#64).toNat = log.toNat + 32 := by
    rw [BitVec.toNat_add]
    change (log.toNat + 32) % 2^64 = _
    exact Nat.mod_eq_of_lt (by omega)
  have he1 := log_growth_store_effect_g09 s (log + 24#64) data [(log.toNat, 40)] hma hd24
    ⟨(log.toNat, 40), by simp, by dsimp only; rw [h24]; omega⟩
  have he2 := log_growth_store_effect_g09
    {s with memory := fun a => if a = log + 24#64 then .word data else s.memory a}
    (log + 32#64) n [(log.toNat, 40)] hma hd32
    ⟨(log.toNat, 40), by simp, by dsimp only; rw [h32]; omega⟩
  exact he1.trans he2

/-- The header writes have a byte-accurate effect confined to the record. -/
theorem op_log_header_stores_effect_g09 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (log address topics nt : BitVec 64) (hma : s.memaddrs = ordinaryDomain)
    (hb : log.toNat + 40 ≤ 2^64)
    (hd0 : s.memaddrs log) (hd8 : s.memaddrs (log + 8#64))
    (hd16 : s.memaddrs (log + 16#64)) :
    ByteRegionEffect s {s with memory := fun a => if a = log + 16#64 then .word nt else
      if a = log + 8#64 then .word topics else if a = log then .word address else s.memory a}
      [(log.toNat, 40)] := by
  have h8 : (log + 8#64).toNat = log.toNat + 8 := by
    rw [BitVec.toNat_add]
    change (log.toNat + 8) % 2^64 = _
    exact Nat.mod_eq_of_lt (by omega)
  have h16 : (log + 16#64).toNat = log.toNat + 16 := by
    rw [BitVec.toNat_add]
    change (log.toNat + 16) % 2^64 = _
    exact Nat.mod_eq_of_lt (by omega)
  have he0 := log_growth_store_effect_g09 s log address [(log.toNat, 40)] hma hd0
    ⟨(log.toNat, 40), by simp, by simp⟩
  let s0 := {s with memory := fun a => if a = log then .word address else s.memory a}
  have he8 := log_growth_store_effect_g09 s0 (log + 8#64) topics [(log.toNat, 40)] hma hd8
    ⟨(log.toNat, 40), by simp, by dsimp only; rw [h8]; omega⟩
  let s8 := {s0 with memory := fun a => if a = log + 8#64 then .word topics else s0.memory a}
  have he16 := log_growth_store_effect_g09 s8 (log + 16#64) nt [(log.toNat, 40)] hma hd16
    ⟨(log.toNat, 40), by simp, by dsimp only; rw [h16]; omega⟩
  exact (he0.trans he8).trans he16

/-- Copy into a detached log-owned buffer, retaining the exposed invariant. -/
theorem op_log_copy_step_g09 {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (dstExp srcExp nExp : ExpHOL 64) (dst src n : BitVec 64) (Rl : List Ivl)
    (cont : ProgHOL 64)
    (hc : s.code = originalRuntimeCode) (hw : EvmInvWith s S Nd)
    (hl : (evmChain s).length = (evmChain s0).length) (hr : evmR s < evmR s0)
    (hd : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp = some (.val (.word dst)))
    (hs : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) srcExp = some (.val (.word src)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp = some (.val (.word n)))
    (hsub : 0 < n.toNat → ∃ i ∈ Rl, i.1 ≤ dst.toNat ∧ dst.toNat + n.toNat ≤ i.1 + i.2)
    (hdj : IvlsDisj Rl (worldTypedIvls s S Nd ++ ((evmChain s).map (frameObjects s)).flatten))
    (hcont : ∀ last : PanSemStateFiniteExact 64 F,
      last.code = originalRuntimeCode → EvmInvWith last S Nd →
      (evmChain last).length = (evmChain s0).length → evmR last < evmR s0 →
      ByteRegionEffect s last Rl → last.locals = s.locals →
      worldTypedIvls last S Nd = worldTypedIvls s S Nd →
      (evmChain last).map (frameObjects last) = (evmChain s).map (frameObjects s) →
      (HeadMemAligned s → HeadMemAligned last) →
      (evaluateHOLFiniteState last cont).1 ≠ some .timeOut →
      OpDispatchPost s0 (evaluateHOLFiniteState last cont).1 (evaluateHOLFiniteState last cont).2)
    (hnt : (evaluateHOLFiniteState s (.seq
      (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp]) cont)).1 ≠ some .timeOut) :
    OpDispatchPost s0
      (evaluateHOLFiniteState s (.seq (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp]) cont)).1
      (evaluateHOLFiniteState s (.seq (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp]) cont)).2 := by
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  let call := ProgHOL.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp]
  have hnc : (evaluateHOLFiniteState s call).1 ≠ some .timeOut := by
    intro h
    change (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp])).1 = some .timeOut at h
    rcases hh : evaluateHOLFiniteState s (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp]) with ⟨r, post⟩
    rw [hh] at h
    dsimp only at h
    subst r
    rw [hh] at hnt
    exact hnt rfl
  have he := Wave8GuestInv.M11.eval_call_memcpy_bre s dstExp srcExp nExp dst src n Rl
    hc hw.1.1.memaddrs hd hs hn hsub hnc
  rcases heval : evaluateHOLFiniteState s call with ⟨r, last⟩
  change evaluateHOLFiniteState s (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp]) = (r, last) at heval
  simp only [heval] at hnt he ⊢
  cases r with
  | none =>
    obtain ⟨heff, hlocals⟩ := he.1 rfl
    have heff' := m11_bre_to_m23 heff
    obtain ⟨hwi,hworld,hframes,hg,hchain,hR,hHM⟩ := evmInvWith_of_bre hw hdj heff'
    exact hcont last (heff'.code.trans hc) hwi (by rw [hchain]; exact hl)
      (by rw [hR]; exact hr) heff' hlocals hworld hframes hHM hnt
  | some res =>
    apply opDispatchPost_other
    · intro v hv
      exact he.2 (by simp) (Or.inl ⟨v, hv⟩)
    · intro hE
      obtain ⟨v,hv⟩ := hE
      exact he.2 (by simp) (Or.inr ⟨ofString "EvmErr", v, hv, by decide⟩)

/-- Execute the two data stores before the append continuation, preserving
the exposed invariant because the new record is still detached. -/
theorem op_log_data_stores_step_g09 {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (log data n : BitVec 64) (cont : ProgHOL 64)
    (hc : s.code = originalRuntimeCode) (hw : EvmInvWith s S Nd)
    (hl : (evmChain s).length = (evmChain s0).length) (hr : evmR s < evmR s0)
    (hlog : s.locals.lookup (ofString "log") = some (.val (.word log)))
    (hdata : s.locals.lookup (ofString "data") = some (.val (.word data)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hb : log.toNat + 40 ≤ 2^64)
    (hd24 : s.memaddrs (log + 24#64)) (hd32 : s.memaddrs (log + 32#64))
    (hdj : IvlsDisj [(log.toNat, 40)]
      (worldTypedIvls s S Nd ++ ((evmChain s).map (frameObjects s)).flatten))
    (hcont : ∀ last : PanSemStateFiniteExact 64 F,
      last.code = originalRuntimeCode → EvmInvWith last S Nd →
      (evmChain last).length = (evmChain s0).length → evmR last < evmR s0 →
      ByteRegionEffect s last [(log.toNat, 40)] → last.locals = s.locals →
      last.memory = (fun a => if a = log + 32#64 then .word n else
        if a = log + 24#64 then .word data else s.memory a) →
      (HeadMemAligned s → HeadMemAligned last) →
      (evaluateHOLFiniteState last cont).1 ≠ some .timeOut →
      OpDispatchPost s0 (evaluateHOLFiniteState last cont).1 (evaluateHOLFiniteState last cont).2)
    (hnt : (evaluateHOLFiniteState s (.seq
      (.seq (.store (.op .add [.var .local (ofString "log"), .const 24]) (.var .local (ofString "data")))
        (.store (.op .add [.var .local (ofString "log"), .const 32]) (.var .local (ofString "n")))) cont)).1 ≠ some .timeOut) :
    OpDispatchPost s0
      (evaluateHOLFiniteState s (.seq
        (.seq (.store (.op .add [.var .local (ofString "log"), .const 24]) (.var .local (ofString "data")))
          (.store (.op .add [.var .local (ofString "log"), .const 32]) (.var .local (ofString "n")))) cont)).1
      (evaluateHOLFiniteState s (.seq
        (.seq (.store (.op .add [.var .local (ofString "log"), .const 24]) (.var .local (ofString "data")))
          (.store (.op .add [.var .local (ofString "log"), .const 32]) (.var .local (ofString "n")))) cont)).2 := by
  rw [evaluateHOLFiniteState_seq_line780,
    op_log_data_stores_exact_g09 s log data n hlog hdata hn hd24 hd32] at hnt ⊢
  dsimp only at hnt ⊢
  have he := op_log_data_stores_effect_g09 s log data n hw.1.1.memaddrs hb hd24 hd32
  obtain ⟨hwi, _, _, _, hchain, hR, hHM⟩ := evmInvWith_of_bre hw hdj he
  exact hcont _ hc hwi (by rw [hchain]; exact hl) (by rw [hR]; exact hr)
    he rfl rfl hHM hnt

/-- Execute the three detached header stores with a preserved invariant. -/
theorem op_log_header_stores_step_g09 {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (log address topics nt : BitVec 64) (cont : ProgHOL 64)
    (hc : s.code = originalRuntimeCode) (hw : EvmInvWith s S Nd)
    (hl : (evmChain s).length = (evmChain s0).length) (hr : evmR s < evmR s0)
    (hlog : s.locals.lookup (ofString "log") = some (.val (.word log)))
    (haddress : s.locals.lookup (ofString "log_address") = some (.val (.word address)))
    (htopics : s.locals.lookup (ofString "topics") = some (.val (.word topics)))
    (hntop : s.locals.lookup (ofString "ntopics") = some (.val (.word nt)))
    (hb : log.toNat + 40 ≤ 2^64)
    (hd0 : s.memaddrs log) (hd8 : s.memaddrs (log + 8#64)) (hd16 : s.memaddrs (log + 16#64))
    (hdj : IvlsDisj [(log.toNat, 40)]
      (worldTypedIvls s S Nd ++ ((evmChain s).map (frameObjects s)).flatten))
    (hcont : ∀ last : PanSemStateFiniteExact 64 F,
      last.code = originalRuntimeCode → EvmInvWith last S Nd →
      (evmChain last).length = (evmChain s0).length → evmR last < evmR s0 →
      ByteRegionEffect s last [(log.toNat, 40)] → last.locals = s.locals →
      last.memory = (fun a => if a = log + 16#64 then .word nt else
        if a = log + 8#64 then .word topics else if a = log then .word address else s.memory a) →
      (HeadMemAligned s → HeadMemAligned last) →
      (evaluateHOLFiniteState last cont).1 ≠ some .timeOut →
      OpDispatchPost s0 (evaluateHOLFiniteState last cont).1 (evaluateHOLFiniteState last cont).2)
    (hnt : (evaluateHOLFiniteState s (.seq
      (.seq (.store (.op .add [.var .local (ofString "log"), .const 0]) (.var .local (ofString "log_address")))
        (.seq (.store (.op .add [.var .local (ofString "log"), .const 8]) (.var .local (ofString "topics")))
          (.store (.op .add [.var .local (ofString "log"), .const 16]) (.var .local (ofString "ntopics"))))) cont)).1 ≠ some .timeOut) :
    OpDispatchPost s0
      (evaluateHOLFiniteState s (.seq
        (.seq (.store (.op .add [.var .local (ofString "log"), .const 0]) (.var .local (ofString "log_address")))
          (.seq (.store (.op .add [.var .local (ofString "log"), .const 8]) (.var .local (ofString "topics")))
            (.store (.op .add [.var .local (ofString "log"), .const 16]) (.var .local (ofString "ntopics"))))) cont)).1
      (evaluateHOLFiniteState s (.seq
        (.seq (.store (.op .add [.var .local (ofString "log"), .const 0]) (.var .local (ofString "log_address")))
          (.seq (.store (.op .add [.var .local (ofString "log"), .const 8]) (.var .local (ofString "topics")))
            (.store (.op .add [.var .local (ofString "log"), .const 16]) (.var .local (ofString "ntopics"))))) cont)).2 := by
  rw [evaluateHOLFiniteState_seq_line780,
    op_log_header_stores_exact_g09 s log address topics nt hlog haddress htopics hntop hd0 hd8 hd16] at hnt ⊢
  dsimp only at hnt ⊢
  have he := op_log_header_stores_effect_g09 s log address topics nt hw.1.1.memaddrs hb hd0 hd8 hd16
  obtain ⟨hwi, _, _, _, hchain, hR, hHM⟩ := evmInvWith_of_bre hw hdj he
  exact hcont _ hc hwi (by rw [hchain]; exact hl) (by rw [hR]; exact hr)
    he rfl rfl hHM hnt

/-- Reassociate concrete sequences without altering finite evaluation. -/
theorem evaluate_seq_assoc_g09 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b c : ProgHOL 64) :
    evaluateHOLFiniteState s (.seq (.seq a b) c) = evaluateHOLFiniteState s (.seq a (.seq b c)) := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_seq_line780]
  rcases h : evaluateHOLFiniteState s a with ⟨r, post⟩
  cases r <;> simp [h, evaluateHOLFiniteState_seq_line780]

/-- The actual right-associated data-store tail inherits the grouped-store contract. -/
theorem op_log_data_tail_step_g09 {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (log data n : BitVec 64) (cont : ProgHOL 64)
    (hc : s.code = originalRuntimeCode) (hw : EvmInvWith s S Nd)
    (hl : (evmChain s).length = (evmChain s0).length) (hr : evmR s < evmR s0)
    (hlog : s.locals.lookup (ofString "log") = some (.val (.word log)))
    (hdata : s.locals.lookup (ofString "data") = some (.val (.word data)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hb : log.toNat + 40 ≤ 2^64)
    (hd24 : s.memaddrs (log + 24#64)) (hd32 : s.memaddrs (log + 32#64))
    (hdj : IvlsDisj [(log.toNat, 40)]
      (worldTypedIvls s S Nd ++ ((evmChain s).map (frameObjects s)).flatten))
    (hcont : ∀ last : PanSemStateFiniteExact 64 F,
      last.code = originalRuntimeCode → EvmInvWith last S Nd →
      (evmChain last).length = (evmChain s0).length → evmR last < evmR s0 →
      ByteRegionEffect s last [(log.toNat, 40)] → last.locals = s.locals →
      last.memory = (fun a => if a = log + 32#64 then .word n else
        if a = log + 24#64 then .word data else s.memory a) →
      (HeadMemAligned s → HeadMemAligned last) →
      (evaluateHOLFiniteState last cont).1 ≠ some .timeOut →
      OpDispatchPost s0 (evaluateHOLFiniteState last cont).1 (evaluateHOLFiniteState last cont).2)
    (hnt : (evaluateHOLFiniteState s (.seq
      (.store (.op .add [.var .local (ofString "log"), .const 24]) (.var .local (ofString "data")))
        (.seq (.store (.op .add [.var .local (ofString "log"), .const 32]) (.var .local (ofString "n"))) cont))).1 ≠ some .timeOut) :
    OpDispatchPost s0
      (evaluateHOLFiniteState s (.seq
        (.store (.op .add [.var .local (ofString "log"), .const 24]) (.var .local (ofString "data")))
          (.seq (.store (.op .add [.var .local (ofString "log"), .const 32]) (.var .local (ofString "n"))) cont))).1
      (evaluateHOLFiniteState s (.seq
        (.store (.op .add [.var .local (ofString "log"), .const 24]) (.var .local (ofString "data")))
          (.seq (.store (.op .add [.var .local (ofString "log"), .const 32]) (.var .local (ofString "n"))) cont))).2 := by
  rw [← evaluate_seq_assoc_g09] at hnt ⊢
  exact op_log_data_stores_step_g09 log data n cont hc hw hl hr hlog hdata hn hb hd24 hd32 hdj hcont hnt

/-- Payload copies preserve a completed detached record and its ownership view. -/
theorem op_log_record_preserved_by_copy_g09 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {log : Nat} {Rl : List Ivl}
    (hma : s.memaddrs = ordinaryDomain) (hb : log + 40 ≤ 2^64)
    (he : ByteRegionEffect s post Rl)
    (hd : ∀ i ∈ Rl, Disj i (log, 40))
    (hok : LogEntryOK s log) :
    LogEntryOK post log ∧ logOwnedIvls post log = logOwnedIvls s log := by
  have hf : ∀ k, k + 8 ≤ 40 → k % 8 = 0 → memW post (log + k) = memW s (log + k) := by
    intro k hk hk8
    exact memW_eq_of_frameDisj_g09 hma he hb hok.1.1 hk8 hk hd
  have h0 := hf 0 (by omega) (by omega)
  simp only [Nat.add_zero] at h0
  have h8 := hf 8 (by omega) (by omega)
  have h16 := hf 16 (by omega) (by omega)
  have h24 := hf 24 (by omega) (by omega)
  have h32 := hf 32 (by omega) (by omega)
  have hg : globN post = globN s := by funext g; simp [globN, he.globals]
  constructor
  · unfold LogEntryOK at hok ⊢
    rw [h0,h8,h16,h24,h32,hg]
    exact ⟨(wordsOK_congr_of_dom_g09 he.memaddrs).2 hok.1, hok.2⟩
  · simp only [logOwnedIvls, logRecordIvls, h0,h8,h16,h24,h32,hg]

/-- The final construction stores establish a valid log record directly. -/
theorem op_log_data_stores_valid_g09 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (log address topics data nt n : BitVec 64)
    (hb : log.toNat + 40 ≤ 2^64) (hwords : WordsOK s (log.toNat, 40))
    (hl : sourceBase ≤ log.toNat) (hlend : log.toNat + 40 ≤ globN s "heap_ptr")
    (ha : sourceBase ≤ address.toNat) (haend : address.toNat + 20 ≤ globN s "heap_ptr")
    (ht : sourceBase ≤ topics.toNat) (htend : topics.toNat + 32 * nt.toNat ≤ globN s "heap_ptr")
    (hd : sourceBase ≤ data.toNat) (hdend : data.toNat + n.toNat ≤ globN s "heap_ptr")
    (hnt : nt.toNat ≤ 4) (hn : n.toNat < 2^32)
    (h0 : memW s log.toNat = address.toNat)
    (h8 : memW s (log.toNat + 8) = topics.toNat)
    (h16 : memW s (log.toNat + 16) = nt.toNat) :
    let post := {s with memory := fun a => if a = log + 32#64 then .word n else
      if a = log + 24#64 then .word data else s.memory a}
    LogEntryOK post log.toNat := by
  dsimp only
  let post := {s with memory := fun a => if a = log + 32#64 then .word n else
    if a = log + 24#64 then .word data else s.memory a}
  have hoff : ∀ k : Nat, k < 40 → (log + BitVec.ofNat 64 k).toNat = log.toNat + k := by
    intro k hk
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hne : ∀ a b : Nat, a < 40 → b < 40 → a ≠ b →
      BitVec.ofNat 64 (log.toNat + a) ≠ log + BitVec.ofNat 64 b := by
    intro a b ha hb' hab he
    have ht := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hoff b hb'] at ht
    omega
  have h24 := hoff 24 (by omega)
  have h32 := hoff 32 (by omega)
  apply op_log_record_valid_g09 post log address topics data nt n
    ((wordsOK_congr_of_dom_g09 (s := s) (post := post) rfl).2 hwords)
    hl hlend ha haend ht htend hd hdend hnt hn
  · have he32 := hne 0 32 (by omega) (by omega) (by omega)
    have he24 := hne 0 24 (by omega) (by omega) (by omega)
    simp only [Nat.add_zero] at he32 he24
    simpa only [post, memW, if_neg he32, if_neg he24] using h0
  · simpa only [post, memW, if_neg (hne 8 32 (by omega) (by omega) (by omega)),
      if_neg (hne 8 24 (by omega) (by omega) (by omega))] using h8
  · simpa only [post, memW, if_neg (hne 16 32 (by omega) (by omega) (by omega)),
      if_neg (hne 16 24 (by omega) (by omega) (by omega))] using h16
  · change memW post (log.toNat + 24) = data.toNat
    rw [← h24]
    simp only [memW, BitVec.ofNat_toNat]
    have hne' : log + 24#64 ≠ log + 32#64 := by
      intro he; have := congrArg BitVec.toNat he; rw [h24,h32] at this; omega
    simp [post, hne']
  · change memW post (log.toNat + 32) = n.toNat
    rw [← h32]
    simp only [memW, BitVec.ofNat_toNat]
    simp [post]

/-- The concrete final stores deliver a valid detached entry to log_append. -/
theorem op_log_valid_data_tail_step_g09 {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (log address topics data nt n : BitVec 64) (cont : ProgHOL 64)
    (hc : s.code = originalRuntimeCode) (hw : EvmInvWith s S Nd)
    (hl : (evmChain s).length = (evmChain s0).length) (hr : evmR s < evmR s0)
    (hlog : s.locals.lookup (ofString "log") = some (.val (.word log)))
    (hdata : s.locals.lookup (ofString "data") = some (.val (.word data)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hb : log.toNat + 40 ≤ 2^64) (hwords : WordsOK s (log.toNat, 40))
    (hlo : sourceBase ≤ log.toNat) (hlend : log.toNat + 40 ≤ globN s "heap_ptr")
    (ha : sourceBase ≤ address.toNat) (haend : address.toNat + 20 ≤ globN s "heap_ptr")
    (ht : sourceBase ≤ topics.toNat) (htend : topics.toNat + 32 * nt.toNat ≤ globN s "heap_ptr")
    (hd : sourceBase ≤ data.toNat) (hdend : data.toNat + n.toNat ≤ globN s "heap_ptr")
    (hnt4 : nt.toNat ≤ 4) (hnb : n.toNat < 2^32)
    (h0 : memW s log.toNat = address.toNat)
    (h8 : memW s (log.toNat + 8) = topics.toNat)
    (h16 : memW s (log.toNat + 16) = nt.toNat)
    (hd24 : s.memaddrs (log + 24#64)) (hd32 : s.memaddrs (log + 32#64))
    (hdj : IvlsDisj [(log.toNat, 40)]
      (worldTypedIvls s S Nd ++ ((evmChain s).map (frameObjects s)).flatten))
    (hcont : ∀ last : PanSemStateFiniteExact 64 F,
      last.code = originalRuntimeCode → EvmInvWith last S Nd →
      (evmChain last).length = (evmChain s0).length → evmR last < evmR s0 →
      ByteRegionEffect s last [(log.toNat, 40)] → last.locals = s.locals →
      LogEntryOK last log.toNat →
      (HeadMemAligned s → HeadMemAligned last) →
      (evaluateHOLFiniteState last cont).1 ≠ some .timeOut →
      OpDispatchPost s0 (evaluateHOLFiniteState last cont).1 (evaluateHOLFiniteState last cont).2)
    (hnt : (evaluateHOLFiniteState s (.seq
      (.store (.op .add [.var .local (ofString "log"), .const 24]) (.var .local (ofString "data")))
        (.seq (.store (.op .add [.var .local (ofString "log"), .const 32]) (.var .local (ofString "n"))) cont))).1 ≠ some .timeOut) :
    OpDispatchPost s0
      (evaluateHOLFiniteState s (.seq
        (.store (.op .add [.var .local (ofString "log"), .const 24]) (.var .local (ofString "data")))
          (.seq (.store (.op .add [.var .local (ofString "log"), .const 32]) (.var .local (ofString "n"))) cont))).1
      (evaluateHOLFiniteState s (.seq
        (.store (.op .add [.var .local (ofString "log"), .const 24]) (.var .local (ofString "data")))
          (.seq (.store (.op .add [.var .local (ofString "log"), .const 32]) (.var .local (ofString "n"))) cont))).2 := by
  apply op_log_data_tail_step_g09 log data n cont hc hw hl hr hlog hdata hn hb hd24 hd32 hdj
  · intro last hcL hwL hlL hrL he hlocals hmemory hHM hnL
    have hv := op_log_data_stores_valid_g09 s log address topics data nt n
      hb hwords hlo hlend ha haend ht htend hd hdend hnt4 hnb h0 h8 h16
    let stores := {s with memory := fun a => if a = log + 32#64 then .word n else
      if a = log + 24#64 then .word data else s.memory a}
    have hvL : LogEntryOK last log.toNat := by
      apply logEntryOK_of_record_agree_g09 (s := stores) (post := last)
        he.memaddrs (by simp only [stores, globN, he.globals]; exact Nat.le_refl _) _ hv
      intro k hk
      simp only [memW, hmemory, stores]
    exact hcont last hcL hwL hlL hrL he hlocals hvL hHM hnL
  · exact hnt

/-- The actual right-associated header stores preserve the detached-record invariant. -/
theorem op_log_header_tail_step_g09 {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (log address topics nt : BitVec 64) (cont : ProgHOL 64)
    (hc : s.code = originalRuntimeCode) (hw : EvmInvWith s S Nd)
    (hl : (evmChain s).length = (evmChain s0).length) (hr : evmR s < evmR s0)
    (hlog : s.locals.lookup (ofString "log") = some (.val (.word log)))
    (haddress : s.locals.lookup (ofString "log_address") = some (.val (.word address)))
    (htopics : s.locals.lookup (ofString "topics") = some (.val (.word topics)))
    (hntop : s.locals.lookup (ofString "ntopics") = some (.val (.word nt)))
    (hb : log.toNat + 40 ≤ 2^64)
    (hd0 : s.memaddrs log) (hd8 : s.memaddrs (log + 8#64)) (hd16 : s.memaddrs (log + 16#64))
    (hdj : IvlsDisj [(log.toNat, 40)]
      (worldTypedIvls s S Nd ++ ((evmChain s).map (frameObjects s)).flatten))
    (hcont : ∀ last : PanSemStateFiniteExact 64 F,
      last.code = originalRuntimeCode → EvmInvWith last S Nd →
      (evmChain last).length = (evmChain s0).length → evmR last < evmR s0 →
      ByteRegionEffect s last [(log.toNat, 40)] → last.locals = s.locals →
      last.memory = (fun a => if a = log + 16#64 then .word nt else
        if a = log + 8#64 then .word topics else if a = log then .word address else s.memory a) →
      (HeadMemAligned s → HeadMemAligned last) →
      (evaluateHOLFiniteState last cont).1 ≠ some .timeOut →
      OpDispatchPost s0 (evaluateHOLFiniteState last cont).1 (evaluateHOLFiniteState last cont).2)
    (hnt : (evaluateHOLFiniteState s (.seq
      (.store (.op .add [.var .local (ofString "log"), .const 0]) (.var .local (ofString "log_address")))
        (.seq (.store (.op .add [.var .local (ofString "log"), .const 8]) (.var .local (ofString "topics")))
          (.seq (.store (.op .add [.var .local (ofString "log"), .const 16]) (.var .local (ofString "ntopics"))) cont)))).1 ≠ some .timeOut) :
    OpDispatchPost s0
      (evaluateHOLFiniteState s (.seq
        (.store (.op .add [.var .local (ofString "log"), .const 0]) (.var .local (ofString "log_address")))
          (.seq (.store (.op .add [.var .local (ofString "log"), .const 8]) (.var .local (ofString "topics")))
            (.seq (.store (.op .add [.var .local (ofString "log"), .const 16]) (.var .local (ofString "ntopics"))) cont)))).1
      (evaluateHOLFiniteState s (.seq
        (.store (.op .add [.var .local (ofString "log"), .const 0]) (.var .local (ofString "log_address")))
          (.seq (.store (.op .add [.var .local (ofString "log"), .const 8]) (.var .local (ofString "topics")))
            (.seq (.store (.op .add [.var .local (ofString "log"), .const 16]) (.var .local (ofString "ntopics"))) cont)))).2 := by
  have hassoc : ∀ (t : PanSemStateFiniteExact 64 F) (a b c d : ProgHOL 64),
      evaluateHOLFiniteState t (.seq (.seq a (.seq b c)) d) =
        evaluateHOLFiniteState t (.seq a (.seq b (.seq c d))) := by
    intro t a b c d
    rw [evaluate_seq_assoc_g09, evaluateHOLFiniteState_seq_line780,
      evaluateHOLFiniteState_seq_line780]
    rcases he : evaluateHOLFiniteState t a with ⟨r, post⟩
    cases r <;> simp [he, evaluate_seq_assoc_g09]
  rw [← hassoc] at hnt ⊢
  exact op_log_header_stores_step_g09 log address topics nt cont hc hw hl hr
    hlog haddress htopics hntop hb hd0 hd8 hd16 hdj hcont hnt

/-- Allocation-order bounds establish both internal and external ownership for a new log. -/
theorem op_log_detached_ownership_g09 {F : Type}
    {s : PanSemStateFiniteExact 64 F} {log address topics data nt n : Nat}
    {objects : List Ivl}
    (h0 : memW s log = address)
    (h8 : memW s (log + 8) = topics)
    (h16 : memW s (log + 16) = nt)
    (h24 : memW s (log + 24) = data)
    (h32 : memW s (log + 32) = n)
    (ht : topics + 32 * nt ≤ log)
    (hl : log + 40 ≤ address)
    (ha : address + 20 ≤ data)
    (hdj : IvlsDisj [(log, 40), (address, 20), (topics, 32 * nt), (data, n)] objects) :
    (logOwnedIvls s log).Pairwise Disj ∧
      IvlsDisj (logOwnedIvls s log) objects := by
  have hpair : ([(log, 40), (address, 20), (topics, 32 * nt), (data, n)] : List Ivl).Pairwise Disj := by
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      List.Pairwise.nil, false_implies, implies_true, and_true]
    constructor
    · intro x hx
      rcases hx with rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inl hl))
      · exact Or.inr (Or.inr (Or.inr ht))
      · exact Or.inr (Or.inr (Or.inl (by omega)))
    · constructor
      · intro x hx
        rcases hx with rfl | rfl
        · exact Or.inr (Or.inr (Or.inr (by omega)))
        · exact Or.inr (Or.inr (Or.inl ha))
      · intro x hx
        have hx' : x = (data, n) := by simpa using hx
        subst x
        exact Or.inr (Or.inr (Or.inl (by omega)))
  have heq : logRecordIvls s log = [(log, 40), (address, 20), (topics, 32 * nt), (data, n)] := by
    simp only [logRecordIvls, h0, h8, h16, h24, h32]
  constructor
  · unfold logOwnedIvls
    rw [heq]
    exact hpair.filter _
  · intro i hi j hj
    have hi' := (List.mem_filter.1 hi).1
    rw [heq] at hi'
    exact hdj i hi' j hj

/-- In-place append keeps the freshly established ownership obligations intact. -/
theorem op_log_no_growth_owned_record_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (l p count log : BitVec 64)
    (address topics data nt size : Nat) (objects : List Ivl)
    (hl : l.toNat + 24 ≤ 2^64)
    (hp : p.toNat + 8 * count.toNat + 8 ≤ 2^64)
    (hb : log.toNat + 40 ≤ 2^64)
    (hheader : Disj (log.toNat, 40) (l.toNat, 24))
    (hbuffer : Disj (log.toNat, 40) (p.toNat, 8 * count.toNat + 8))
    (hvalid : LogEntryOK s log.toNat)
    (h0 : memW s log.toNat = address)
    (h8 : memW s (log.toNat + 8) = topics)
    (h16 : memW s (log.toNat + 16) = nt)
    (h24 : memW s (log.toNat + 24) = data)
    (h32 : memW s (log.toNat + 32) = size)
    (ht : topics + 32 * nt ≤ log.toNat)
    (hlog : log.toNat + 40 ≤ address)
    (ha : address + 20 ≤ data)
    (hdj : IvlsDisj [(log.toNat, 40), (address, 20), (topics, 32 * nt), (data, size)] objects) :
    let post := {s with memory := fun a =>
      if a = p + count * 8#64 then .word log
      else if a = l + 8#64 then .word (count + 1#64) else s.memory a}
    LogEntryOK post log.toNat ∧
      logOwnedIvls post log.toNat = logOwnedIvls s log.toNat ∧
      (logOwnedIvls post log.toNat).Pairwise Disj ∧
      IvlsDisj (logOwnedIvls post log.toNat) objects := by
  dsimp only
  obtain ⟨hv, heq⟩ := log_no_growth_new_record_preserved_g09 s l p count log
    hl hp hb hheader hbuffer hvalid
  obtain ⟨hpair, hsep⟩ := op_log_detached_ownership_g09 h0 h8 h16 h24 h32 ht hlog ha hdj
  exact ⟨hv, heq, heq ▸ hpair, heq ▸ hsep⟩

/-- Growing append preserves the validity and separated ownership of its new entry. -/
theorem op_log_growth_owned_record_g09 {F : Type}
    (s copy : PanSemStateFiniteExact 64 F) (l p count cap log : BitVec 64)
    (address topics data nt size : Nat) (objects : List Ivl)
    (hl : l.toNat + 24 ≤ 2^64)
    (hp : p.toNat + 8 * count.toNat + 8 ≤ 2^64)
    (hb : log.toNat + 40 ≤ 2^64)
    (hheader : Disj (log.toNat, 40) (l.toNat, 24))
    (hbuffer : Disj (log.toNat, 40) (p.toNat, 8 * count.toNat + 8))
    (hdom : copy.memaddrs = s.memaddrs)
    (hheap : globN s "heap_ptr" ≤ globN copy "heap_ptr")
    (hsys : globN copy "vm_system_address" = globN s "vm_system_address")
    (hrecord : ∀ k ∈ ([0, 8, 16, 24, 32] : List Nat),
      memW copy (log.toNat + k) = memW s (log.toNat + k))
    (hvalid : LogEntryOK s log.toNat)
    (h0 : memW s log.toNat = address)
    (h8 : memW s (log.toNat + 8) = topics)
    (h16 : memW s (log.toNat + 16) = nt)
    (h24 : memW s (log.toNat + 24) = data)
    (h32 : memW s (log.toNat + 32) = size)
    (ht : topics + 32 * nt ≤ log.toNat)
    (hlog : log.toNat + 40 ≤ address)
    (ha : address + 20 ≤ data)
    (hdj : IvlsDisj [(log.toNat, 40), (address, 20), (topics, 32 * nt), (data, size)] objects) :
    let post := {copy with memory := fun a =>
      if a = p + count * 8#64 then .word log
      else if a = l + 8#64 then .word (count + 1#64)
      else if a = l + 16#64 then .word (cap * 2#64)
      else if a = l then .word p else copy.memory a}
    LogEntryOK post log.toNat ∧
      logOwnedIvls post log.toNat = logOwnedIvls s log.toNat ∧
      (logOwnedIvls post log.toNat).Pairwise Disj ∧
      IvlsDisj (logOwnedIvls post log.toNat) objects := by
  dsimp only
  obtain ⟨hv, heq⟩ := log_growth_record_preserved_g09 s copy l p count cap log log.toNat
    hl hp hb hheader hbuffer hdom hheap hsys hrecord hvalid
  obtain ⟨hpair, hsep⟩ := op_log_detached_ownership_g09 h0 h8 h16 h24 h32 ht hlog ha hdj
  exact ⟨hv, heq, heq ▸ hpair, heq ▸ hsep⟩

/-- In-place append establishes its semantic list result directly from pre-store validity. -/
theorem op_log_no_growth_list_post_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (ec : Ivl) (S : List Nat)
    (l p n cap log : BitVec 64)
    (hA : ArenaReady s) (hFW : FrameWF s S ec)
    (hpw : (frameObjects s ec).Pairwise Disj)
    (hl : memW s (ec.1 + 88) = l.toNat)
    (hn : memW s (l.toNat + 8) = n.toNat)
    (hm0 : memW s l.toNat = p.toNat)
    (hm16 : memW s (l.toNat + 16) = cap.toNat)
    (hnonnull : l.toNat ≠ 0) (hlt : n.toNat < cap.toNat)
    (hl_bound : l.toNat + 24 ≤ 2^64)
    (hp_bound : p.toNat + 8 * n.toNat + 8 ≤ 2^64)
    (hdisj : Disj (p.toNat, 8 * n.toNat + 8) (l.toNat, 24))
    (hd8 : s.memaddrs (l + 8#64)) (hdslot : s.memaddrs (p + n * 8#64))
    (hec : ec.1 + 280 ≤ 2^64)
    (hecHeader : Disj (ec.1, 280) (l.toNat, 24))
    (hecBuffer : Disj (ec.1, 280) (p.toNat, 8 * n.toNat + 8))
    (hlog : LogEntryOK s log.toNat)
    (hdheader : Disj (log.toNat, 40) (l.toNat, 24))
    (hdbuffer : Disj (log.toNat, 40) (p.toNat, 8 * n.toNat + 8)) :
    let post := {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64) else s.memory a}
    LogsListOK post (memW post (ec.1 + 88)) ∧
      frameLogObjects post ec = frameLogObjects s ec ++ logOwnedIvls s log.toNat := by
  dsimp only
  have hcount : n.toNat + 1 < 2^64 := by
    have hb := (frameWF_logs_cap_bounds hA.2 hFW).2.2.2.1
    rw [hl, hn] at hb
    omega
  have hheap : globN s "heap_ptr" ≤ 2^64 := by
    have hh := hA.2.2.1
    rw [R11Shards.heapLimit_val] at hh
    omega
  obtain ⟨hv, ho⟩ := log_no_growth_new_record_preserved_g09 s l p n log
    hl_bound hp_bound (le_trans hlog.2.1.2 hheap) hdheader hdbuffer hlog
  obtain ⟨hw, ha, hs⟩ := log_no_growth_header_and_slots_g09 s ec S l p n cap log
    hFW hl hm0 hm16 hlt
  have hf := log_no_growth_protected_words_g09 s l p n log (ec.1, 280)
    hl_bound hp_bound hec hecHeader hecBuffer
  have hrecords := log_no_growth_old_record_separation_g09 l p n cap
    hA hFW hpw hl hn hm0 hm16 hnonnull hlt
  obtain ⟨hlist, hobjects⟩ := log_no_growth_semantic_post_g09 s ec S l p n cap log
    hA hFW hl hn hm0 hm16 hlt hcount hl_bound hp_bound hdisj hd8 hdslot
    hrecords ((hf 88 (by omega)).trans hl) hw ha hs hv
  exact ⟨hlist, by rw [hobjects, ho]⟩

/-- Reconstruct the appended head frame without assuming post-store message ownership. -/
theorem op_log_no_growth_head_frame_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (head : Ivl) (tail : List Ivl) (S Nd : List Nat)
    (l p n cap log : BitVec 64)
    (hA : ArenaReady s) (hFW : FrameWF s S head)
    (hWT : WorldTypedWith s S Nd)
    (hpw : (frameObjects s head).Pairwise Disj)
    (hcons : evmChain s = head :: tail)
    (hl : memW s (head.1 + 88) = l.toNat)
    (hn : memW s (l.toNat + 8) = n.toNat)
    (hm0 : memW s l.toNat = p.toNat)
    (hm16 : memW s (l.toNat + 16) = cap.toNat)
    (hnonnull : l.toNat ≠ 0) (hlt : n.toNat < cap.toNat)
    (hl_bound : l.toNat + 24 ≤ 2^64)
    (hp_bound : p.toNat + 8 * n.toNat + 8 ≤ 2^64)
    (hdisj : Disj (p.toNat, 8 * n.toNat + 8) (l.toNat, 24))
    (hd8 : s.memaddrs (l + 8#64)) (hdslot : s.memaddrs (p + n * 8#64))
    (hec : head.1 + 280 ≤ 2^64)
    (hecHeader : Disj (head.1, 280) (l.toNat, 24))
    (hecBuffer : Disj (head.1, 280) (p.toNat, 8 * n.toNat + 8))
    (hlog : LogEntryOK s log.toNat)
    (hdheader : Disj (log.toNat, 40) (l.toNat, 24))
    (hdbuffer : Disj (log.toNat, 40) (p.toNat, 8 * n.toNat + 8))
    (hnewMsg : ∀ o ∈ logOwnedIvls s log.toNat, Disj (memW s (head.1 + 112), 176) o) :
    let post := {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64) else s.memory a}
    SameTypedCells s post S Nd → evmChain post = evmChain s →
    (∀ ec ∈ tail, frameObjects post ec = frameObjects s ec) →
    FrameWF post S head ∧
      frameObjects post head = frameObjects s head ++ logOwnedIvls s log.toNat := by
  dsimp only
  intro hcell hchain htail
  let post := {s with memory := fun a =>
    if a = p + n * 8#64 then .word log
    else if a = l + 8#64 then .word (n + 1#64) else s.memory a}
  have hAp : ArenaReady post :=
    ⟨⟨hA.1.code, hA.1.memaddrs, hA.1.shMemaddrs, hA.1.baseAddr⟩,
      arenaOK_congr rfl hA.2⟩
  have hcount : n.toNat + 1 < 2^64 := by
    have hb := (frameWF_logs_cap_bounds hA.2 hFW).2.2.2.1
    rw [hl, hn] at hb
    omega
  have hheap : globN s "heap_ptr" ≤ 2^64 := by
    have hh := hA.2.2.1
    rw [R11Shards.heapLimit_val] at hh
    omega
  have hobjects : frameObjects post head = frameObjects s head ++ logOwnedIvls s log.toNat :=
    log_no_growth_objects_without_msg_g09 s head S l p n cap log hA hFW hpw
      hl hn hm0 hm16 hnonnull hlt hcount hl_bound hp_bound hdisj hd8 hdslot
      hec hecHeader hecBuffer (le_trans hlog.2.1.2 hheap) hlog hdheader hdbuffer
  have hmsg : MsgOwned post S (memW s (head.1 + 112)) := by
    apply msgOwned_of_log_no_growth_g09 hA hAp hWT hcell rfl rfl hchain hcons
      hobjects htail hnewMsg
    exact hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact log_no_growth_frame_post_of_separation_g09 s head S l p n cap log hA hFW hpw
    hl hn hm0 hm16 hnonnull hlt hcount hl_bound hp_bound hdisj hd8 hdslot
    hec hecHeader hecBuffer hlog hdheader hdbuffer hmsg

/-- Assemble in-place append validity from pre-state frames and suspended-frame readback. -/
theorem op_log_no_growth_invariant_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (head : Ivl) (tail : List Ivl) (S Nd : List Nat)
    (l p n cap log : BitVec 64)
    (hA : ArenaReady s) (hinv : EvmInvAt s S) (hWT : WorldTypedWith s S Nd)
    (hFW : ∀ ec ∈ evmChain s, FrameWF s S ec)
    (hpw : (frameObjects s head).Pairwise Disj)
    (hcons : evmChain s = head :: tail)
    (hl : memW s (head.1 + 88) = l.toNat)
    (hn : memW s (l.toNat + 8) = n.toNat)
    (hm0 : memW s l.toNat = p.toNat)
    (hm16 : memW s (l.toNat + 16) = cap.toNat)
    (hnonnull : l.toNat ≠ 0) (hlt : n.toNat < cap.toNat)
    (hl_bound : l.toNat + 24 ≤ 2^64)
    (hp_bound : p.toNat + 8 * n.toNat + 8 ≤ 2^64)
    (hdisj : Disj (p.toNat, 8 * n.toNat + 8) (l.toNat, 24))
    (hd8 : s.memaddrs (l + 8#64)) (hdslot : s.memaddrs (p + n * 8#64))
    (hec : head.1 + 280 ≤ 2^64)
    (hecHeader : Disj (head.1, 280) (l.toNat, 24))
    (hecBuffer : Disj (head.1, 280) (p.toNat, 8 * n.toNat + 8))
    (hlog : LogEntryOK s log.toNat)
    (hdheader : Disj (log.toNat, 40) (l.toNat, 24))
    (hdbuffer : Disj (log.toNat, 40) (p.toNat, 8 * n.toNat + 8))
    (hnewMsg : ∀ ec ∈ evmChain s, ∀ o ∈ logOwnedIvls s log.toNat,
      Disj (memW s (ec.1 + 112), 176) o)
    (hold : ((evmChain s).map (frameObjects s)).flatten.Pairwise Disj)
    (hnew : (logOwnedIvls s log.toNat).Pairwise Disj)
    (hnewOld : IvlsDisj ((evmChain s).map (frameObjects s)).flatten (logOwnedIvls s log.toNat))
    (holdWorld : IvlsDisj ((evmChain s).map (frameObjects s)).flatten (worldOwned s S Nd))
    (hnewWorld : IvlsDisj (logOwnedIvls s log.toNat) (worldOwned s S Nd)) :
    let post := {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64) else s.memory a}
    SameTypedCells s post S Nd →
    (∀ ec ∈ evmChain s, ∀ k, k + 8 ≤ 280 → memW post (ec.1 + k) = memW s (ec.1 + k)) →
    (∀ ec ∈ evmChain s, ∀ k, k + 8 ≤ 104 → memW post (ec.2 + k) = memW s (ec.2 + k)) →
    (∀ ec ∈ tail, ∀ k, k + 8 ≤ 24 →
      memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) →
    (∀ ec ∈ tail, ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      memW post (memW s (memW s (ec.1 + 88)) + 8 * i) =
        memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) →
    (∀ ec ∈ tail, ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      ∀ k ∈ ([0, 8, 16, 24, 32] : List Nat),
      memW post (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + k) =
        memW s (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + k)) →
    EvmInvAt post S := by
  dsimp only
  intro hcell hfields hcont hheader hslots hrecords
  let post := {s with memory := fun a =>
    if a = p + n * 8#64 then .word log
    else if a = l + 8#64 then .word (n + 1#64) else s.memory a}
  have hAp : ArenaReady post :=
    ⟨⟨hA.1.code, hA.1.memaddrs, hA.1.shMemaddrs, hA.1.baseAddr⟩,
      arenaOK_congr rfl hA.2⟩
  have hchain : evmChain post = evmChain s := log_chain_of_cont_readback_g09 rfl rfl hcont
  have htailMem : ∀ ec ∈ tail, ec ∈ evmChain s := by
    intro ec he; rw [hcons]; exact List.mem_cons_of_mem _ he
  have hheadMem : head ∈ evmChain s := by rw [hcons]; exact List.mem_cons_self
  have htail : ∀ ec ∈ tail, frameObjects post ec = frameObjects s ec := by
    intro ec he
    exact (log_no_growth_tail_objects_congr_g09 (s := s) (post := post) rfl
      (hfields ec (htailMem ec he)) (hheader ec he) (hslots ec he) (hrecords ec he)).1
  obtain ⟨hhwf, hhobj⟩ := op_log_no_growth_head_frame_g09 s head tail S Nd l p n cap log
    hA (hFW head hheadMem) hWT hpw hcons hl hn hm0 hm16 hnonnull hlt
    hl_bound hp_bound hdisj hd8 hdslot hec hecHeader hecBuffer hlog hdheader hdbuffer
    (hnewMsg head hheadMem) hcell hchain htail
  exact evmInvAt_of_log_owned_frames_g09 hA hAp hinv hWT hcell rfl rfl hchain hcons
    hhobj hhwf hFW (fun ec he => hnewMsg ec (htailMem ec he))
    hfields hcont hheader hslots hrecords hold hnew hnewOld holdWorld hnewWorld

/-- Separation supplies all suspended-frame readback needed by append reconstruction. -/
theorem op_log_no_growth_readback_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (tail : List Ivl) (l p n log : BitVec 64)
    (hl : l.toNat + 24 ≤ 2^64)
    (hp : p.toNat + 8 * n.toNat + 8 ≤ 2^64)
    (hprotected : ∀ ec ∈ evmChain s, ∀ o ∈ ([(ec.1, 280), (ec.2, 104)] : List Ivl),
      o.1 + o.2 ≤ 2^64 ∧ Disj o (l.toNat, 24) ∧ Disj o (p.toNat, 8 * n.toNat + 8))
    (htail : ∀ ec ∈ tail, ∀ o ∈ ([(memW s (ec.1 + 88), 24),
        (memW s (memW s (ec.1 + 88)), 8 * memW s (memW s (ec.1 + 88) + 8))] : List Ivl),
      o.1 + o.2 ≤ 2^64 ∧ Disj o (l.toNat, 24) ∧ Disj o (p.toNat, 8 * n.toNat + 8))
    (hrecords : ∀ ec ∈ tail, ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      let o := (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40)
      o.1 + o.2 ≤ 2^64 ∧ Disj o (l.toNat, 24) ∧ Disj o (p.toNat, 8 * n.toNat + 8)) :
    let post := {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64) else s.memory a}
    (∀ ec ∈ evmChain s, ∀ k, k + 8 ≤ 280 → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
    (∀ ec ∈ evmChain s, ∀ k, k + 8 ≤ 104 → memW post (ec.2 + k) = memW s (ec.2 + k)) ∧
    (∀ ec ∈ tail, ∀ k, k + 8 ≤ 24 →
      memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) ∧
    (∀ ec ∈ tail, ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      memW post (memW s (memW s (ec.1 + 88)) + 8 * i) =
        memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) ∧
    (∀ ec ∈ tail, ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      ∀ k ∈ ([0, 8, 16, 24, 32] : List Nat),
      memW post (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + k) =
        memW s (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + k)) := by
  dsimp only
  have read : ∀ o : Ivl, o.1 + o.2 ≤ 2^64 ∧ Disj o (l.toNat, 24) ∧
      Disj o (p.toNat, 8 * n.toNat + 8) → ∀ k, k + 8 ≤ o.2 →
      memW {s with memory := fun a => if a = p + n * 8#64 then .word log
        else if a = l + 8#64 then .word (n + 1#64) else s.memory a} (o.1 + k) = memW s (o.1 + k) := by
    intro o ho
    exact log_no_growth_protected_words_g09 s l p n log o hl hp ho.1 ho.2.1 ho.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ec he k hk
    exact read (ec.1, 280) (hprotected ec he _ (by simp)) k hk
  · intro ec he k hk
    exact read (ec.2, 104) (hprotected ec he _ (by simp)) k hk
  · intro ec he k hk
    exact read (memW s (ec.1 + 88), 24) (htail ec he _ (by simp)) k hk
  · intro ec he i hi
    exact read (memW s (memW s (ec.1 + 88)), 8 * memW s (memW s (ec.1 + 88) + 8))
      (htail ec he _ (by simp)) (8*i) (by omega)
  · intro ec he i hi k hk
    have hkbound : k + 8 ≤ 40 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
    exact read (memW s (memW s (memW s (ec.1 + 88)) + 8*i), 40)
      (hrecords ec he i hi) k hkbound

/-- In-place append reconstructs the invariant solely from pre-state separation. -/
theorem op_log_no_growth_invariant_of_separation_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (head : Ivl) (tail : List Ivl) (S Nd : List Nat)
    (l p n cap log : BitVec 64)
    (hA : ArenaReady s) (hinv : EvmInvAt s S) (hWT : WorldTypedWith s S Nd)
    (hFW : ∀ ec ∈ evmChain s, FrameWF s S ec)
    (hpw : (frameObjects s head).Pairwise Disj)
    (hcons : evmChain s = head :: tail)
    (hl : memW s (head.1 + 88) = l.toNat)
    (hn : memW s (l.toNat + 8) = n.toNat)
    (hm0 : memW s l.toNat = p.toNat)
    (hm16 : memW s (l.toNat + 16) = cap.toNat)
    (hnonnull : l.toNat ≠ 0) (hlt : n.toNat < cap.toNat)
    (hl_bound : l.toNat + 24 ≤ 2^64)
    (hp_bound : p.toNat + 8 * cap.toNat ≤ 2^64)
    (hdisj : Disj (p.toNat, 8 * n.toNat + 8) (l.toNat, 24))
    (hd8 : s.memaddrs (l + 8#64)) (hdslot : s.memaddrs (p + n * 8#64))
    (hlog : LogEntryOK s log.toNat)
    (hdheader : Disj (log.toNat, 40) (l.toNat, 24))
    (hdbuffer : Disj (log.toNat, 40) (p.toNat, 8 * n.toNat + 8))
    (hnewMsg : ∀ ec ∈ evmChain s, ∀ o ∈ logOwnedIvls s log.toNat,
      Disj (memW s (ec.1 + 112), 176) o)
    (hold : ((evmChain s).map (frameObjects s)).flatten.Pairwise Disj)
    (hnew : (logOwnedIvls s log.toNat).Pairwise Disj)
    (hnewOld : IvlsDisj ((evmChain s).map (frameObjects s)).flatten (logOwnedIvls s log.toNat))
    (holdWorld : IvlsDisj ((evmChain s).map (frameObjects s)).flatten (worldOwned s S Nd))
    (hnewWorld : IvlsDisj (logOwnedIvls s log.toNat) (worldOwned s S Nd))
    (hheaderWorld : ∀ i ∈ worldTypedIvls s S Nd, Disj (l.toNat, 24) i)
    (hbufferWorld : ∀ i ∈ worldTypedIvls s S Nd, Disj (p.toNat, 8 * cap.toNat) i)
    (hprotected : ∀ ec ∈ evmChain s, ∀ o ∈ ([(ec.1, 280), (ec.2, 104)] : List Ivl),
      o.1 + o.2 ≤ 2^64 ∧ Disj o (l.toNat, 24) ∧ Disj o (p.toNat, 8 * n.toNat + 8))
    (htail : ∀ ec ∈ tail, ∀ o ∈ ([(memW s (ec.1 + 88), 24),
        (memW s (memW s (ec.1 + 88)), 8 * memW s (memW s (ec.1 + 88) + 8))] : List Ivl),
      o.1 + o.2 ≤ 2^64 ∧ Disj o (l.toNat, 24) ∧ Disj o (p.toNat, 8 * n.toNat + 8))
    (hrecords : ∀ ec ∈ tail, ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      let o := (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40)
      o.1 + o.2 ≤ 2^64 ∧ Disj o (l.toNat, 24) ∧ Disj o (p.toNat, 8 * n.toNat + 8)) :
    let post := {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64) else s.memory a}
    EvmInvAt post S := by
  dsimp only
  have hp : p.toNat + 8 * n.toNat + 8 ≤ 2^64 := by omega
  have hheadMem : head ∈ evmChain s := by rw [hcons]; exact List.mem_cons_self
  have hh := hprotected head hheadMem (head.1, 280) (by simp)
  have hcell := log_no_growth_final_typed_cells_g09 s l p n cap log S Nd
    hA.1.memaddrs hWT hd8 hdslot hl_bound hp_bound hlt hheaderWorld hbufferWorld
  obtain ⟨hfields, hcont, hheaders, hslots, hreads⟩ :=
    op_log_no_growth_readback_g09 s tail l p n log hl_bound hp hprotected htail hrecords
  exact op_log_no_growth_invariant_g09 s head tail S Nd l p n cap log
    hA hinv hWT hFW hpw hcons hl hn hm0 hm16 hnonnull hlt hl_bound hp hdisj hd8 hdslot
    hh.1 hh.2.1 hh.2.2 hlog hdheader hdbuffer hnewMsg hold hnew hnewOld holdWorld hnewWorld
    hcell hfields hcont hheaders hslots hreads

/-- Concrete in-place execution inherits the reconstructed invariant and structural readback. -/
theorem op_log_no_growth_execution_of_invariant_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (e log l n cap p : BitVec 64) (S : List Nat)
    (hA : ArenaReady s) (hcode : s.code = originalRuntimeCode) (hclock : s.clock ≠ 0)
    (he : s.locals.lookup (ofString "e") = some (.val (.word e)))
    (hlg : s.locals.lookup (ofString "log") = some (.val (.word log)))
    (hde : s.memaddrs (e + 88#64)) (hme : s.memory (e + 88#64) = .word l)
    (hd0 : s.memaddrs l) (hd8 : s.memaddrs (l + 8#64)) (hd16 : s.memaddrs (l + 16#64))
    (hm0 : s.memory l = .word p) (hm8 : s.memory (l + 8#64) = .word n)
    (hm16 : s.memory (l + 16#64) = .word cap)
    (hlt : n.toNat < cap.toNat) (hne : l ≠ l + 8#64)
    (hdslot : s.memaddrs (p + n * 8#64)) (hHM : HeadMemAligned s) :
    let stores := {s with memory := fun a =>
      if a = p + n * 8#64 then .word log
      else if a = l + 8#64 then .word (n + 1#64) else s.memory a}
    EvmInvAt stores S →
    (∀ ec ∈ evmChain s, ∀ k, k + 8 ≤ 280 →
      memW stores (ec.1 + k) = memW s (ec.1 + k)) →
    (∀ ec ∈ evmChain s, ∀ k, k + 8 ≤ 104 →
      memW stores (ec.2 + k) = memW s (ec.2 + k)) →
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_log_append)
    out.1 = some (.returned (.val (.word 0))) ∧
      EvmInv out.2 ∧ evmR out.2 = evmR s ∧ HeadMemAligned out.2 := by
  dsimp only
  intro hinv hfields hcont
  let stores := {s with memory := fun a =>
    if a = p + n * 8#64 then .word log
    else if a = l + 8#64 then .word (n + 1#64) else s.memory a}
  have hAp : ArenaReady stores :=
    ⟨⟨hA.1.code, hA.1.memaddrs, hA.1.shMemaddrs, hA.1.baseAddr⟩,
      arenaOK_congr rfl hA.2⟩
  have hchain : evmChain stores = evmChain s := log_chain_of_cont_readback_g09 rfl rfl hcont
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    unfold evmChain
    simp only [evmChainFrom, List.mem_cons, true_or]
  have hp := log_growth_handler_post_g09 hAp hinv hchain
    (fun ec hec k hk _ => hfields ec hec k hk) rfl rfl hhead hHM
  exact log_append_no_growth_execution_post_g09 s e log l n cap p hcode hclock
    he hlg hde hme hd0 hd8 hd16 hm0 hm8 hm16 hlt hne hdslot hp

/-- Concrete in-place log_append closes entirely from pre-state validity and separation. -/
theorem op_log_no_growth_execution_of_separation_g09 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (head : Ivl) (tail : List Ivl) (S Nd : List Nat)
    (e l p n cap log : BitVec 64)
    (hA : ArenaReady s) (hinv : EvmInvAt s S) (hWT : WorldTypedWith s S Nd)
    (hFW : ∀ ec ∈ evmChain s, FrameWF s S ec)
    (hpw : (frameObjects s head).Pairwise Disj)
    (hcons : evmChain s = head :: tail)
    (hl : memW s (head.1 + 88) = l.toNat)
    (hn : memW s (l.toNat + 8) = n.toNat)
    (hm0 : memW s l.toNat = p.toNat)
    (hm16 : memW s (l.toNat + 16) = cap.toNat)
    (hnonnull : l.toNat ≠ 0) (hlt : n.toNat < cap.toNat)
    (hl_bound : l.toNat + 24 ≤ 2^64)
    (hp_bound : p.toNat + 8 * cap.toNat ≤ 2^64)
    (hdisj : Disj (p.toNat, 8 * n.toNat + 8) (l.toNat, 24))
    (hd8 : s.memaddrs (l + 8#64)) (hdslot : s.memaddrs (p + n * 8#64))
    (hlog : LogEntryOK s log.toNat)
    (hdheader : Disj (log.toNat, 40) (l.toNat, 24))
    (hdbuffer : Disj (log.toNat, 40) (p.toNat, 8 * n.toNat + 8))
    (hnewMsg : ∀ ec ∈ evmChain s, ∀ o ∈ logOwnedIvls s log.toNat,
      Disj (memW s (ec.1 + 112), 176) o)
    (hold : ((evmChain s).map (frameObjects s)).flatten.Pairwise Disj)
    (hnew : (logOwnedIvls s log.toNat).Pairwise Disj)
    (hnewOld : IvlsDisj ((evmChain s).map (frameObjects s)).flatten (logOwnedIvls s log.toNat))
    (holdWorld : IvlsDisj ((evmChain s).map (frameObjects s)).flatten (worldOwned s S Nd))
    (hnewWorld : IvlsDisj (logOwnedIvls s log.toNat) (worldOwned s S Nd))
    (hheaderWorld : ∀ i ∈ worldTypedIvls s S Nd, Disj (l.toNat, 24) i)
    (hbufferWorld : ∀ i ∈ worldTypedIvls s S Nd, Disj (p.toNat, 8 * cap.toNat) i)
    (hprotected : ∀ ec ∈ evmChain s, ∀ o ∈ ([(ec.1, 280), (ec.2, 104)] : List Ivl),
      o.1 + o.2 ≤ 2^64 ∧ Disj o (l.toNat, 24) ∧ Disj o (p.toNat, 8 * n.toNat + 8))
    (htail : ∀ ec ∈ tail, ∀ o ∈ ([(memW s (ec.1 + 88), 24),
        (memW s (memW s (ec.1 + 88)), 8 * memW s (memW s (ec.1 + 88) + 8))] : List Ivl),
      o.1 + o.2 ≤ 2^64 ∧ Disj o (l.toNat, 24) ∧ Disj o (p.toNat, 8 * n.toNat + 8))
    (hrecords : ∀ ec ∈ tail, ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      let o := (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40)
      o.1 + o.2 ≤ 2^64 ∧ Disj o (l.toNat, 24) ∧ Disj o (p.toNat, 8 * n.toNat + 8))
    (hclock : s.clock ≠ 0)
    (he : s.locals.lookup (ofString "e") = some (.val (.word e)))
    (hlg : s.locals.lookup (ofString "log") = some (.val (.word log)))
    (hde : s.memaddrs (e + 88#64)) (hme : s.memory (e + 88#64) = .word l)
    (hd0 : s.memaddrs l) (hd16 : s.memaddrs (l + 16#64))
    (hm0w : s.memory l = .word p) (hm8w : s.memory (l + 8#64) = .word n)
    (hm16w : s.memory (l + 16#64) = .word cap)
    (hne : l ≠ l + 8#64) (hHM : HeadMemAligned s) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_log_append)
    out.1 = some (.returned (.val (.word 0))) ∧
      EvmInv out.2 ∧ evmR out.2 = evmR s ∧ HeadMemAligned out.2 := by
  have hi := op_log_no_growth_invariant_of_separation_g09 s head tail S Nd l p n cap log
    hA hinv hWT hFW hpw hcons hl hn hm0 hm16 hnonnull hlt hl_bound hp_bound
    hdisj hd8 hdslot hlog hdheader hdbuffer hnewMsg hold hnew hnewOld holdWorld hnewWorld
    hheaderWorld hbufferWorld hprotected htail hrecords
  obtain ⟨hf, hc, _⟩ := op_log_no_growth_readback_g09 s tail l p n log hl_bound
    (by omega) hprotected htail hrecords
  exact op_log_no_growth_execution_of_invariant_g09 s e log l n cap p S
    hA hA.1.code hclock he hlg hde hme hd0 hd8 hd16 hm0w hm8w hm16w hlt hne hdslot hHM
    hi hf hc

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
