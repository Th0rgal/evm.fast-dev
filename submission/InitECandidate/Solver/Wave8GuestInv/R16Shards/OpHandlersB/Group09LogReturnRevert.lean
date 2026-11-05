import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.Common
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.ReadOnly
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.StoreAllocHelpers
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.Group04
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group06ControlFlow
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.StateGasHelpers
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.UntypedBufHelpers

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

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
