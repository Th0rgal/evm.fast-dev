import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.UntypedBufHelpers
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.AllocJournalStep
import InitECandidate.Solver.Wave8GuestInv.R16Shards.HtabValuesSub
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmHtabStep
import InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01AllocMpt
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_htab_get
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_u256_is_zero

/-! # Journaled transient-storage helpers (`jdel`, `jset` on `ts + 64`, `get_transient_storage`, `set_transient_storage`) -/

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
open InitECandidate.Solver.Wave8GuestInv.R13Shards
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue
open InitECandidate.Solver.Wave8Contracts.M15 (htabGetCallees htabGetCallees_good)
open InitECandidate.Solver.Wave8Contracts.M23

/-! ## 1. Installed lookups -/

theorem lookup_htab_get :
    originalRuntimeCode.lookup (ofString "htab_get") =
      some ([(ofString "t", .one), (ofString "key", .one)],
        sourceFnBody Guest.Software.guestFn_htab_get, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 132 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_get) rfl

def htabGetReadCallees (f : MlS) : Bool :=
  htabGetCallees f || f == ofString "htab_get"

theorem htabGetReadCallees_good :
    ∀ function, htabGetReadCallees function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) →
      Wave8Contracts.M15.readOnlyProg htabGetReadCallees body = true := by
  intro function hfn values body callee rs hfound
  simp only [htabGetReadCallees, Bool.or_eq_true, beq_iff_eq] at hfn
  rcases hfn with hm | rfl
  · obtain ⟨_, _, hinst⟩ := lookupCode_installed hfound
    simp only [htabGetCallees, Bool.or_eq_true, beq_iff_eq] at hm
    rcases hm with rfl | rfl
    · have hl := lookup_of_guestAst_getElem 131 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_htab_find_leaf) rfl
      change originalRuntimeCode.lookup (ofString "htab_find_leaf") = _ at hl
      rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
    · have hl := lookup_of_guestAst_getElem 18 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_memeq) rfl
      change originalRuntimeCode.lookup (ofString "memeq") = _ at hl
      rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
  · obtain ⟨_, _, hinst⟩ := lookupCode_installed hfound
    rw [lookup_htab_get] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide

theorem lookup_jset :
    originalRuntimeCode.lookup (ofString "jset") =
      some ([(ofString "t", .one), (ofString "key", .one), (ofString "value", .one)],
        sourceFnBody Guest.Software.guestFn_jset, .one) :=
  lookup_of_guestAst_getElem 356 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_jset) rfl

theorem lookup_jdel :
    originalRuntimeCode.lookup (ofString "jdel") =
      some ([(ofString "t", .one), (ofString "key", .one)],
        sourceFnBody Guest.Software.guestFn_jdel, .one) :=
  lookup_of_guestAst_getElem 357 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_jdel) rfl

theorem lookup_get_transient_storage :
    originalRuntimeCode.lookup (ofString "get_transient_storage") =
      some ([(ofString "addr", .one), (ofString "key", .one)],
        sourceFnBody Guest.Software.guestFn_get_transient_storage,
        .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 380 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_get_transient_storage) rfl

theorem lookup_set_transient_storage :
    originalRuntimeCode.lookup (ofString "set_transient_storage") =
      some ([(ofString "addr", .one), (ofString "key", .one),
             (ofString "value", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_set_transient_storage, .one) :=
  lookup_of_guestAst_getElem 394 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_set_transient_storage) rfl

/-! ## 2. Closed non-catching callee set for `jset`, `jdel`, `get_transient_storage`, `set_transient_storage` -/

def transientMutCallees (f : MlS) : Bool :=
  htabMutCallees f || f == ofString "htab_get" || f == ofString "sk_make" ||
  f == ofString "u256_is_zero" || f == ofString "jset" || f == ofString "jdel"

private theorem noCatchableRaise_mono {g1 g2 : MlS → Bool} (himp : ∀ f, g1 f = true → g2 f = true) :
    ∀ p : ProgHOL 64, noCatchableRaise g1 p = true → noCatchableRaise g2 p = true
  | .skip, _ | .«break», _ | .«continue», _ | .annot _ _, _ | .«return» _, _
  | .assign _ _ _, _ | .store _ _, _ | .storeByte _ _, _ | .store32 _ _, _
  | .shMemStore _ _ _, _ | .extCall _ _ _ _ _, _ => rfl
  | .raise _ _, hp => hp
  | .dec _ _ _ b, hp => noCatchableRaise_mono himp b hp
  | .seq a b, hp => by
      simp only [noCatchableRaise, Bool.and_eq_true] at hp ⊢
      exact ⟨noCatchableRaise_mono himp a hp.1, noCatchableRaise_mono himp b hp.2⟩
  | .ite _ a b, hp => by
      simp only [noCatchableRaise, Bool.and_eq_true] at hp ⊢
      exact ⟨noCatchableRaise_mono himp a hp.1, noCatchableRaise_mono himp b hp.2⟩
  | .while _ b, hp => noCatchableRaise_mono himp b hp
  | .decCall _ _ fn _ cont, hp => by
      simp only [noCatchableRaise, Bool.and_eq_true] at hp ⊢
      exact ⟨himp fn hp.1, noCatchableRaise_mono himp cont hp.2⟩
  | .call tail fn _, hp => by
      rcases tail with _ | ⟨_, hdl⟩
      · simp [noCatchableRaise] at hp
      · rcases hdl with _ | _
        · exact himp fn hp
        · simp [noCatchableRaise] at hp
  | .shMemLoad _ _ _ _, hp => by simp [noCatchableRaise] at hp

theorem transientMutCallees_good :
    ∀ f, transientMutCallees f = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup f values =
        some (body, callee, rs) →
      noCatchableRaise transientMutCallees body = true := by
  intro f hf values body callee rs hfound
  simp only [transientMutCallees, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with ((((hm | rfl) | rfl) | rfl) | rfl) | rfl
  · exact noCatchableRaise_mono
      (fun g hg => by simp [transientMutCallees, hg])
      body (htabMutCallees_good f hm values body callee rs hfound)
  · obtain ⟨_, _, hinst⟩ := lookupCode_installed hfound
    have hl := lookup_of_guestAst_getElem 132 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_htab_get) rfl
    change originalRuntimeCode.lookup (ofString "htab_get") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
  · obtain ⟨_, _, hinst⟩ := lookupCode_installed hfound
    have hl := lookup_of_guestAst_getElem 360 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_sk_make) rfl
    change originalRuntimeCode.lookup (ofString "sk_make") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
  · obtain ⟨_, _, hinst⟩ := lookupCode_installed hfound
    have hl := lookup_of_guestAst_getElem 42 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_u256_is_zero) rfl
    change originalRuntimeCode.lookup (ofString "u256_is_zero") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
  · obtain ⟨_, _, hinst⟩ := lookupCode_installed hfound
    rw [lookup_jset] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
  · obtain ⟨_, _, hinst⟩ := lookupCode_installed hfound
    rw [lookup_jdel] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide

/-! ## 3. `eps_get_transient_storage` -/

theorem eps_get_transient_storage :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => post.globals = s.globals ∧ evmR post = evmR s)
      (ofString "get_transient_storage") := by
  refine ⟨_, _, _, lookup_get_transient_storage, ?_⟩
  intro F s hcode hInv _ _ hnt
  have hno_evmErr : ¬ IsEvmErr
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_get_transient_storage)).1 := by
    have hnc := evaluate_noCatchableRaise transientMutCallees transientMutCallees_good
      (sourceFnBody Guest.Software.guestFn_get_transient_storage) (by decide) s hcode
    rintro ⟨ev, hev⟩
    exact hnc (ofString "EvmErr") ev (by decide) hev
  dsimp only
  refine ⟨?_, fun he => (hno_evmErr he).elim⟩
  intro v hv
  have hbody : sourceFnBody Guest.Software.guestFn_get_transient_storage =
      .decCall (ofString "k") .one (ofString "sk_make")
        [.var .local (ofString "addr"), .var .local (ofString "key")]
        (.decCall (ofString "v") (.comb [.one, .one]) (ofString "htab_get")
          [.load .one (.op .add [.var .global (ofString "ts"), .const 64]),
           .var .local (ofString "k")]
          (.seq
            (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "v"))) (.const 0))
              (.return (.rstruct [.const 0, .const 0, .const 0, .const 0]))
              .skip)
            (.return (.load (.comb [.one, .one, .one, .one])
              (.rfield 1 (.var .local (ofString "v"))))))) := rfl
  let tailProg : ProgHOL 64 :=
    .decCall (ofString "v") (.comb [.one, .one]) (ofString "htab_get")
      [.load .one (.op .add [.var .global (ofString "ts"), .const 64]),
       .var .local (ofString "k")]
      (.seq
        (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "v"))) (.const 0))
          (.return (.rstruct [.const 0, .const 0, .const 0, .const 0]))
          .skip)
        (.return (.load (.comb [.one, .one, .one, .one])
          (.rfield 1 (.var .local (ofString "v"))))))
  revert hv
  rw [hbody, evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "addr"), .var .local (ofString "key")] with _ | vals
  · simp
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "sk_make") vals with _ | ⟨body_sk, cal_sk, ret_sk⟩
    · simp
    · simp only [hl] at hnt ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        obtain ⟨params_sk, body_sk0, ret_sk0, hlook_sk, hspec_sk⟩ := eps_sk_make
        have hbody_eq : body_sk = body_sk0 :=
          lookupCodeHOLFinite_installed_body s.code.lookup (ofString "sk_make")
            params_sk body_sk0 body_sk ret_sk0 ret_sk vals cal_sk (by rw [hcode]; exact hlook_sk) hl
        subst body_sk
        have hret_eq : ret_sk = ret_sk0 := by
          have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
            s.code.lookup (ofString "sk_make") vals body_sk0 cal_sk ret_sk hl
          rw [hcode] at hx; simp only [Flapjack.lookupCodeHOLExact, hlook_sk] at hx
          split at hx
          · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
          · cases hx
        subst ret_sk
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "sk_make") vals =
            some (body_sk0, cal_sk, ret_sk0) := by rwa [← hcode]
        let ce := callEntryStateHOLFinite s cal_sk
        have hInv_ce : EvmInv ce := localsFree_evmInv s cal_sk (s.clock - 1) hInv
        have hmeta_sk := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s cal_sk) body_sk0).1
        rcases hrun_sk : evaluateHOLFiniteState (callEntryStateHOLFinite s cal_sk) body_sk0 with ⟨res_sk, cpost⟩
        simp only [hrun_sk] at hnt hmeta_sk ⊢
        cases res_sk with
        | none => simp
        | some r0 =>
          cases r0 with
          | timeOut => exact absurd rfl hnt
          | returned kv =>
            dsimp only at hnt ⊢
            split
            · rename_i hsh_kv
              rw [if_pos hsh_kv] at hnt
              intro hv
              have hs_sk := (hspec_sk ce hcode hInv_ce trivial ⟨vals, hl_orig⟩
                (by rw [hrun_sk]; simp)).1 kv (by rw [hrun_sk])
              dsimp only at hs_sk; rw [hrun_sk] at hs_sk
              obtain ⟨hInv_cp, hch_cp, _, hg_cp, hR_cp⟩ := hs_sk
              let s1 := setVarHOLFinite (ofString "k") kv { cpost with locals := s.locals }
              have hs1_code : s1.code = originalRuntimeCode := hmeta_sk.trans hcode
              have hlf_tail : Wave8Contracts.M15.LocFrame s1 (evaluateHOLFiniteState s1 tailProg).2 :=
                Wave8Contracts.M15.evaluate_readOnlyProg htabGetReadCallees htabGetReadCallees_good
                  tailProg (by decide) s1 hs1_code
              let out2 := evaluateHOLFiniteState s1 tailProg
              let post := { out2.2 with locals := out2.2.locals.resVarEq (ofString "k", s.locals.lookup (ofString "k")) }
              have hp_eq : post = { cpost with locals := post.locals, clock := out2.2.clock } := by
                dsimp only [post, out2, s1]
                unfold Wave8Contracts.M15.LocFrame at hlf_tail
                rw [hlf_tail]; rfl
              have hInv_p : EvmInv post := by
                have h := localsFree_evmInv cpost post.locals out2.2.clock hInv_cp
                rwa [← hp_eq] at h
              have hm_p : post.memory = cpost.memory := by rw [hp_eq]
              have hg_p : post.globals = cpost.globals := by rw [hp_eq]
              have hc_p := evm_congr hm_p hg_p
              have hc_ce := evm_congr (s := s) (t := ce) rfl rfl
              have hg_s : post.globals = s.globals := hg_p.trans hg_cp
              have hch_ce : evmChain ce = evmChain s := evmChain_congr rfl rfl
              have hch_s : evmChain post = evmChain s :=
                (evmChain_congr hm_p hg_p).trans (hch_cp.trans hch_ce)
              have hR_s : evmR post = evmR s :=
                hc_p.2.1.trans (hR_cp.trans hc_ce.2.1)
              exact ⟨hInv_p, hch_s, le_of_eq hR_s, hg_s, hR_s⟩
            · simp
          | _ => simp

/-! ## 4. Role and non-aliasing properties of `t0 = memW s (globN s "ts" + 64)` -/

theorem ts64_role_props {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hInv : EvmInvAt s S)
    (hts : globN s "ts" ≠ 0)
    (ht0_nz : memW s (globN s "ts" + 64) ≠ 0) :
    let t0 := memW s (globN s "ts" + 64)
    t0 ∈ S ∧
    t0 ∈ worldTableRefs s S ∧
    (t0, "ts+64") ∈ worldRoleSlots s ∧
    journalRole s t0 = "ts+64" ∧
    (∀ (i : Nat) (_hi : i + 1 < (evmChain s).length), ¬ DelExclusive s S (evmChain s) i t0) ∧
    (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t0) ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
    globN s "bal_accounts" ≠ t0 ∧
    (∀ ad ∈ balRecords s, memW s ad ≠ t0) ∧
    (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) := by
  dsimp only
  set t0 := memW s (globN s "ts" + 64)
  obtain ⟨⟨hT, _, _, _⟩, _, _, _, _, _, _, _, _, _, _, hRoles, _⟩ := hInv
  have ht0_S : t0 ∈ S := by
    have hroot := hT.2.2.2.2.2.1 64 (by decide) hts
    rcases hroot with hz | hmem
    · exact absurd hz ht0_nz
    · exact hmem
  have ht0_wref : t0 ∈ worldTableRefs s S := by
    unfold worldTableRefs
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
    unfold recordSlots
    rw [if_neg hts]
    exact List.mem_map.2 ⟨64, by decide, rfl⟩
  have hts_rec_mem : ∀ (off : Nat) (rname : String),
      (off, rname) ∈ ([(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
        (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] : List (Nat × String)) →
      memW s (globN s "ts" + off) = t0 →
      (t0, rname) ∈ worldRoleSlots s := by
    intro off rname hmem heq
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [ht0_nz]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_right
    unfold recRoles
    rw [if_neg hts]
    exact List.mem_map.2 ⟨(off, rname), hmem, by simp [heq]⟩
  have ht0_wrs : (t0, "ts+64") ∈ worldRoleSlots s :=
    hts_rec_mem 64 "ts+64" (by decide) rfl
  have hpw_all := hRoles.2.1
  have hnot_other_wrs : ∀ rname : String, rname ≠ "ts+64" → (t0, rname) ∉ worldRoleSlots s := by
    intro rname hr_ne hmem
    have hnd : ([(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
        (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] : List (Nat × String)).Nodup := by decide
    -- Use `List.Pairwise` on `worldRoleSlots s`: if two distinct entries have `.1 = t0` and different `.2`,
    -- they cannot be equal as pairs, so `Pairwise` gives `a.2 = b.2`!
    have hpw_wrs : (worldRoleSlots s).Pairwise (fun a b => a.1 = b.1 → a.2 = b.2 ∧ a.2 ∈ sharedRoles) :=
      (List.pairwise_append.1 hpw_all).1
    obtain ⟨i1, hi1, he1⟩ := List.mem_iff_getElem.1 ht0_wrs
    obtain ⟨i2, hi2, he2⟩ := List.mem_iff_getElem.1 hmem
    by_cases hij : i1 = i2
    · subst hij; rw [he1] at he2; exact hr_ne (Prod.mk.inj he2).2.symm
    · rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
      · have hp := List.pairwise_iff_getElem.1 hpw_wrs i1 i2 hi1 hi2 hlt
        rw [he1, he2] at hp
        exact hr_ne (hp rfl).1.symm
      · have hp := List.pairwise_iff_getElem.1 hpw_wrs i2 i1 hi2 hi1 hgt
        rw [he1, he2] at hp
        exact hr_ne (hp rfl).1
  have hts_slot_ne : ∀ (off : Nat) (rname : String),
      (off, rname) ∈ ([(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
        (40, "ts+40"), (48, "ts+48"), (56, "ts+56")] : List (Nat × String)) →
      rname ≠ "ts+64" →
      memW s (globN s "ts" + off) ≠ t0 := by
    intro off rname hmem hr_ne heq
    apply hnot_other_wrs rname hr_ne
    exact hts_rec_mem off rname (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem ⊢
      tauto) heq
  have hjr_eq : journalRole s t0 = "ts+64" := by
    have h16 : memW s (globN s "ts" + 16) ≠ t0 := hts_slot_ne 16 "ts+16" (by decide) (by decide)
    have h32 : memW s (globN s "ts" + 32) ≠ t0 := hts_slot_ne 32 "ts+32" (by decide) (by decide)
    have h48 : memW s (globN s "ts" + 48) ≠ t0 := hts_slot_ne 48 "ts+48" (by decide) (by decide)
    unfold journalRole
    rw [if_neg (fun h => h16 h.2.symm), if_neg (fun h => h32 h.2.symm),
        if_neg (fun h => h48 h.2.symm), if_pos ⟨hts, rfl⟩]
  refine ⟨ht0_S, ht0_wref, ht0_wrs, hjr_eq, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i _ hdel
    exact hdel.1 ht0_wref
  · intro hws heq
    apply hnot_other_wrs "ws+32" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [ht0_nz]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    unfold recRoles; simp [hws, heq]
  · intro hbs heq
    apply hnot_other_wrs "bs+32" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [ht0_nz]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
    unfold recRoles; simp [hbs, heq]
  · intro heq
    apply hnot_other_wrs "bal_accounts" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [ht0_nz]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_right
    simp [heq]
  · intro ad had heq
    apply hnot_other_wrs "bal.stor" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [ht0_nz]⟩
    apply List.mem_append_right
    exact List.mem_flatMap.2 ⟨ad, had, by simp [heq]⟩
  · intro _
    exact hts_slot_ne 32 "ts+32" (by decide) (by decide)

/-! ## 5. Shared journal-append + key-clone + tail helper (`jrecord_push_tail_step`) -/

def jrecordPushTailProg (presExp : ExpHOL 64) (tailProg : ProgHOL 64) : ProgHOL 64 :=
  .dec (ofString "klen") .one
    (.load .one (.op .add [.var .local (ofString "t"), .const 0]))
    (.decCall (ofString "kc") .one (ofString "alloc") [.var .local (ofString "klen")]
      (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "kc"), .var .local (ofString "key"), .var .local (ofString "klen")])
        (.dec (ofString "r") .one
          (.op .add [.var .global (ofString "journal"),
            .panop .mul [.var .global (ofString "journal_n"), .const 32]])
          (.seq
            (.store (.var .local (ofString "r")) (.var .local (ofString "t")))
            (.seq
              (.store (.op .add [.var .local (ofString "r"), .const 8]) (.var .local (ofString "kc")))
              (.seq
                (.store (.op .add [.var .local (ofString "r"), .const 16]) presExp)
                (.seq
                  (.store (.op .add [.var .local (ofString "r"), .const 24])
                    (.rfield 1 (.var .local (ofString "old"))))
                  (.seq
                    (.assign .global (ofString "journal_n")
                      (.op .add [.var .global (ofString "journal_n"), .const 1]))
                    tailProg))))))))

theorem eval_store_word_exact {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {dst val : ExpHOL 64}
    {addr w : BitVec 64}
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst =
      some (.val (.word addr)))
    (hval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val =
      some (.val (.word w)))
    (hrun : evaluateHOLFiniteState s (.store dst val) = (none, post)) :
    s.memaddrs addr ∧ post = { s with memory := Wave8M19.Htab.updW s.memory addr w } := by
  rw [evaluateHOLFiniteState_store] at hrun
  rw [hdst, hval] at hrun
  dsimp only at hrun
  revert hrun
  split
  · rename_i m' hm
    obtain ⟨hdom, rfl⟩ := Wave8M19.Htab.stores_word _ hm
    intro h
    injection h with _ hp
    exact ⟨hdom, hp.symm⟩
  · simp

theorem dec_ret_inv {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {nm : MlS} {sh : ShapeHOL} {init : ExpHOL 64} {bd : ProgHOL 64} {rv : ValueHOL 64}
    (h : evaluateHOLFiniteState s (.dec nm sh init bd) = (some (.returned rv), post)) :
    ∃ val, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init = some val ∧
      ∃ mid, evaluateHOLFiniteState (setVarHOLFinite nm val s) bd = (some (.returned rv), mid) ∧
        post = { mid with locals := HolFiniteMapExact.resVarEq mid.locals (nm, s.locals.lookup nm) } := by
  rw [evaluateHOLFiniteState_dec_total] at h; dsimp only at h
  split at h
  · simp at h
  · rename_i val hev
    split at h
    · rcases hb : evaluateHOLFiniteState (setVarHOLFinite nm val s) bd with ⟨rb, mid⟩
      rw [hb] at h
      cases rb with
      | none => simp at h
      | some r0 =>
        cases r0 with
        | returned u =>
          dsimp only at h
          injection h with hr hso
          injection hr with hr'
          injection hr' with hu
          subst hu
          exact ⟨val, hev, mid, hb, hso.symm⟩
        | _ => simp at h
    · simp at h

theorem seq_store_ret_inv {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {dst val : ExpHOL 64} {b : ProgHOL 64} {rv : ValueHOL 64}
    (h : evaluateHOLFiniteState s (.seq (.store dst val) b) = (some (.returned rv), post)) :
    ∃ mid, evaluateHOLFiniteState s (.store dst val) = (none, mid) ∧
      evaluateHOLFiniteState mid b = (some (.returned rv), post) := by
  rw [evaluateHOLFiniteState_seq_line780] at h
  rcases ha : evaluateHOLFiniteState s (.store dst val) with ⟨ra, mid⟩
  rw [ha] at h
  cases ra with
  | none => exact ⟨mid, rfl, h⟩
  | some r0 =>
    have he := store_some_eq_error' ha; subst he; simp at h

theorem seq_assign_ret_inv {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {vk : VarKind} {nm : MlS} {val : ExpHOL 64} {b : ProgHOL 64} {rv : ValueHOL 64}
    (h : evaluateHOLFiniteState s (.seq (.assign vk nm val) b) = (some (.returned rv), post)) :
    ∃ mid, evaluateHOLFiniteState s (.assign vk nm val) = (none, mid) ∧
      evaluateHOLFiniteState mid b = (some (.returned rv), post) := by
  rw [evaluateHOLFiniteState_seq_line780] at h
  rcases ha : evaluateHOLFiniteState s (.assign vk nm val) with ⟨ra, mid⟩
  rw [ha] at h
  cases ra with
  | none => exact ⟨mid, rfl, h⟩
  | some r0 =>
    exfalso
    rw [evaluateHOLFiniteState_assign] at ha
    split at ha
    · injection ha with hr _; injection hr with hr'; subst hr'; simp at h
    · split at ha
      · simp at ha
      · injection ha with hr _; injection hr with hr'; subst hr'; simp at h

theorem seq_call0_ret_inv {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {fn : MlS} {args : List (ExpHOL 64)} {b : ProgHOL 64} {rv : ValueHOL 64}
    (h : evaluateHOLFiniteState s (.seq (.call (some (none, none)) fn args) b) = (some (.returned rv), post)) :
    ∃ mid, evaluateHOLFiniteState s (.call (some (none, none)) fn args) = (none, mid) ∧
      evaluateHOLFiniteState mid b = (some (.returned rv), post) := by
  rw [evaluateHOLFiniteState_seq_line780] at h
  rcases ha : evaluateHOLFiniteState s (.call (some (none, none)) fn args) with ⟨ra, mid⟩
  rw [ha] at h
  cases ra with
  | none => exact ⟨mid, rfl, h⟩
  | some r0 =>
    exfalso
    rw [evaluateHOLFiniteState_call] at ha
    rcases hev : PanSemStateFiniteExact.evalListHOLFinite s
        (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
    · rw [hev] at ha; dsimp only at ha
      injection ha with hr _; injection hr with hr'; subst hr'; simp at h
    · rw [hev] at ha; dsimp only at ha
      rcases hlk : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fn vals with _ | ⟨body0, cal0, ret0⟩
      · rw [hlk] at ha; dsimp only at ha
        injection ha with hr _; injection hr with hr'; subst hr'; simp at h
      · rw [hlk] at ha; dsimp only at ha
        split at ha
        · injection ha with hr _; injection hr with hr'; subst hr'; simp at h
        · rcases hrb : (s.callEntryStateHOLFinite cal0).evaluateHOLFiniteState body0 with ⟨rb, mb⟩
          rw [hrb] at ha
          cases rb with
          | none =>
            dsimp only at ha
            injection ha with hr _; injection hr with hr'; subst hr'; simp at h
          | some rb0 =>
            cases rb0 <;> simp only at ha
            case returned =>
              split at ha
              · simp at ha
              · injection ha with hr _; injection hr with hr'; subst hr'; simp at h
            all_goals (injection ha with hr _; injection hr with hr'; subst hr'; simp at h)

theorem jrecord_push_tail_step {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    {tw keyw old0 old1 presw : BitVec 64} {presExp : ExpHOL 64}
    {tailProg : ProgHOL 64} {rv : ValueHOL 64}
    (hcode : s.code = originalRuntimeCode)
    (hAs : ArenaReady s)
    (hInv : EvmInvAt s S)
    (ht : s.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hkey : s.locals.lookup (ofString "key") = some (.val (.word keyw)))
    (hold : s.locals.lookup (ofString "old") = some (.rStruct [.val (.word old0), .val (.word old1)]))
    (hpres : ∀ st : PanSemStateFiniteExact 64 F,
      st.locals.lookup (ofString "old") = some (.rStruct [.val (.word old0), .val (.word old1)]) →
      @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) presExp =
        some (.val (.word presw)))
    (hjn_lt : globN s "journal_n" < globN s "journal_cap")
    (hts_nz : globN s "ts" ≠ 0)
    (htw_ts64 : tw.toNat = memW s (globN s "ts" + 64))
    (htw_nz : tw.toNat ≠ 0)
    (hrun : evaluateHOLFiniteState s (jrecordPushTailProg presExp tailProg) = (some (.returned rv), post)) :
    ∃ mid tailPost,
      mid.code = originalRuntimeCode ∧
      ArenaReady mid ∧
      EvmInvAt mid S ∧
      evmChain mid = evmChain s ∧
      evmR mid = evmR s ∧
      globN s "heap_ptr" ≤ globN mid "heap_ptr" ∧
      GlobalsKept ["heap_ptr", "journal_n"] s mid ∧
      (∀ a : BitVec 64,
        ¬ (globN s "heap_ptr" ≤ a.toNat ∧ a.toNat < globN mid "heap_ptr") →
        ¬ (globN s "journal" + 32 * globN s "journal_n" ≤ a.toNat ∧
            a.toNat + 8 ≤ globN s "journal" + 32 * globN s "journal_n" + 32) →
        mid.memory a = s.memory a) ∧
      globN mid "ts" = globN s "ts" ∧
      memW mid (globN s "ts" + 64) = memW s (globN s "ts" + 64) ∧
      (∀ nm : MlS, nm ≠ ofString "klen" → nm ≠ ofString "kc" → nm ≠ ofString "r" →
        mid.locals.lookup nm = s.locals.lookup nm) ∧
      evaluateHOLFiniteState mid tailProg = (some (.returned rv), tailPost) ∧
      post = { tailPost with locals := post.locals } := by
  unfold jrecordPushTailProg at hrun
  -- 1. Unpack `dec "klen"`:
  obtain ⟨vklen, hvklen_ev, m_klen, hrun_klen, hp_klen⟩ := dec_ret_inv hrun
  obtain ⟨_, hvklen_mem⟩ := Wave8M19.Htab.ev_field_load s (ofString "t") tw 0#64 ht vklen hvklen_ev
  rcases hm_tw0 : s.memory (tw + 0#64) with ⟨klenw⟩
  rw [hm_tw0] at hvklen_mem
  subst hvklen_mem
  let s_kl := setVarHOLFinite (ofString "klen") (.val (.word klenw)) s
  have hkl_kl : s_kl.locals.lookup (ofString "klen") = some (.val (.word klenw)) := by
    simp [s_kl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have ht_kl : s_kl.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [s_kl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "klen" ≠ ofString "t" by decide, ht]
  have hkey_kl : s_kl.locals.lookup (ofString "key") = some (.val (.word keyw)) := by
    simp [s_kl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "klen" ≠ ofString "key" by decide, hkey]
  have hold_kl : s_kl.locals.lookup (ofString "old") = some (.rStruct [.val (.word old0), .val (.word old1)]) := by
    simp [s_kl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "klen" ≠ ofString "old" by decide, hold]
  -- 2. Unpack `decCall "kc" .one "alloc" [klen]`:
  change s_kl.evaluateHOLFiniteState _ = (some (.returned rv), m_klen) at hrun_klen
  rw [evaluateHOLFiniteState_decCall_total] at hrun_klen
  have hargs_al : evalListHOLFinite s_kl (h := fun a => Classical.propDecidable (s_kl.memaddrs a))
      [.var .local (ofString "klen")] = some [.val (.word klenw)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hkl_kl]
  have hl_al := pan_one_word_lookup s_kl.code.lookup (ofString "alloc") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_alloc) klenw
    (by change s.code.lookup (ofString "alloc") = _; rw [hcode]; exact lookup_alloc_r13)
  rw [hargs_al] at hrun_klen; dsimp only at hrun_klen
  rw [hl_al] at hrun_klen; dsimp only at hrun_klen
  by_cases hclk_kl : s_kl.clock = 0
  · rw [if_pos hclk_kl] at hrun_klen; simp at hrun_klen
  rw [if_neg hclk_kl, fixClockHOLFinite_evaluateState] at hrun_klen
  let ce_al := callEntryStateHOLFinite s_kl (HolFiniteMapExact.empty.update (ofString "n", .val (.word klenw)))
  have hcode_al : ce_al.code = originalRuntimeCode := hcode
  have hA_al : ArenaReady ce_al := ⟨guestInv_congr (s := s) (t := ce_al) rfl rfl rfl rfl hAs.1, hAs.2⟩
  have hmeta_al := (PanRunBounded.evaluateHOLFiniteState_metadata ce_al (sourceFnBody Guest.Software.guestFn_alloc)).1
  rcases hrun_al : evaluateHOLFiniteState (callEntryStateHOLFinite s_kl (HolFiniteMapExact.empty.update (ofString "n", .val (.word klenw)))) (sourceFnBody Guest.Software.guestFn_alloc) with ⟨res_al, cpost_al⟩
  change evaluateHOLFiniteState ce_al (sourceFnBody Guest.Software.guestFn_alloc) = (res_al, cpost_al) at hrun_al
  rw [show callEntryStateHOLFinite s_kl (HolFiniteMapExact.empty.update (ofString "n", .val (.word klenw))) = ce_al from rfl] at hrun_klen
  rw [hrun_al] at hrun_klen hmeta_al
  dsimp only at hrun_klen hmeta_al
  cases res_al with
  | none => simp at hrun_klen
  | some r_al =>
    cases r_al with
    | returned rv_al =>
      dsimp only at hrun_klen
      have hres_al : Wave8Contracts.M12.Resumes
          (evaluateHOLFiniteState ce_al (sourceFnBody Guest.Software.guestFn_alloc)).1 := by
        rw [hrun_al]; exact Or.inl ⟨rv_al, rfl⟩
      obtain ⟨kcw, qw, hret_al, hkc_nat, hq_nat, hq_lim, hq_8, hkc_le_q, hg_al, hm_al, hbe_al,
        hma_al, hA_cpal, hhp_cpal, _⟩ := alloc_body_resumes_props ce_al hcode_al hA_al hres_al
      rw [hrun_al] at hret_al hg_al hm_al hbe_al hma_al hA_cpal hhp_cpal
      dsimp only at hg_al hm_al hbe_al hma_al hA_cpal hhp_cpal
      injection hret_al with hret_al'; injection hret_al' with hrv_eq
      subst hrv_eq
      have hsh_kc : (shapeEqHOL (shapeOfHOLExact (.val (.word kcw) : ValueHOL 64)) .one &&
          shapeEqHOL (shapeOfHOLExact (.val (.word kcw) : ValueHOL 64)) .one) = true := by
        simp [shapeOfHOLExact, shapeEqHOL]
      rw [if_pos hsh_kc] at hrun_klen
      have hloc_n_al : locN ce_al "n" = klenw.toNat := by
        simp [ce_al, callEntryStateHOLFinite, locN, HolFiniteMapExact.lookup_update, FUPDATE]
      rw [hloc_n_al] at hq_nat
      let s_kc := setVarHOLFinite (ofString "kc") (.val (.word kcw)) { cpost_al with locals := s_kl.locals }
      rcases hrun_kc_body : evaluateHOLFiniteState s_kc
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.var .local (ofString "kc"), .var .local (ofString "key"), .var .local (ofString "klen")])
          (.dec (ofString "r") .one
            (.op .add [.var .global (ofString "journal"),
              .panop .mul [.var .global (ofString "journal_n"), .const 32]])
            (.seq
              (.store (.var .local (ofString "r")) (.var .local (ofString "t")))
              (.seq
                (.store (.op .add [.var .local (ofString "r"), .const 8]) (.var .local (ofString "kc")))
                (.seq
                  (.store (.op .add [.var .local (ofString "r"), .const 16]) presExp)
                  (.seq
                    (.store (.op .add [.var .local (ofString "r"), .const 24])
                      (.rfield 1 (.var .local (ofString "old"))))
                    (.seq
                      (.assign .global (ofString "journal_n")
                        (.op .add [.var .global (ofString "journal_n"), .const 1]))
                      tailProg))))))) with ⟨r_kc, m_kc⟩
      rw [hrun_kc_body] at hrun_klen
      cases r_kc with
      | none => simp at hrun_klen
      | some r_kc0 =>
        cases r_kc0 with
        | returned rv_kc =>
          dsimp only at hrun_klen
          injection hrun_klen with hr_kc hm_klen_eq
          injection hr_kc with hr_kc'
          injection hr_kc' with hrv_kc
          subst hrv_kc
          -- 3. Unpack `seq (call "memcpy" ...) (dec "r" ...)`:
          obtain ⟨s_mc, hcall_mc, hrun_rdec⟩ := seq_call0_ret_inv hrun_kc_body
          have hcode_kc : s_kc.code = originalRuntimeCode := hmeta_al.trans hcode
          have hma_kc : s_kc.memaddrs = ordinaryDomain := hma_al.trans hAs.1.memaddrs
          have hkc_lk : s_kc.locals.lookup (ofString "kc") = some (.val (.word kcw)) := by
            simp [s_kc, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have ht_kc : s_kc.locals.lookup (ofString "t") = some (.val (.word tw)) := by
            simp [s_kc, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "kc" ≠ ofString "t" by decide, ht_kl]
          have hkey_kc : s_kc.locals.lookup (ofString "key") = some (.val (.word keyw)) := by
            simp [s_kc, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "kc" ≠ ofString "key" by decide, hkey_kl]
          have hkl_kc : s_kc.locals.lookup (ofString "klen") = some (.val (.word klenw)) := by
            simp [s_kc, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "kc" ≠ ofString "klen" by decide, hkl_kl]
          have hold_kc : s_kc.locals.lookup (ofString "old") = some (.rStruct [.val (.word old0), .val (.word old1)]) := by
            simp [s_kc, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "kc" ≠ ofString "old" by decide, hold_kl]
          have hhp_ce_s : globN ce_al "heap_ptr" = globN s "heap_ptr" := rfl
          rw [hhp_ce_s] at hkc_nat
          have hbre_mc := (Wave8GuestInv.M11.eval_call_memcpy_bre s_kc
            (.var .local (ofString "kc")) (.var .local (ofString "key")) (.var .local (ofString "klen"))
            kcw keyw klenw [(globN s "heap_ptr", qw.toNat - globN s "heap_ptr")]
            hcode_kc hma_kc
            (by simp [evalHOLExact, hkc_lk])
            (by simp [evalHOLExact, hkey_kc])
            (by simp [evalHOLExact, hkl_kc])
            (fun _ => ⟨(globN s "heap_ptr", qw.toNat - globN s "heap_ptr"), List.mem_singleton.mpr rfl,
              by dsimp only; omega, by dsimp only; omega⟩)
            (by rw [hcall_mc]; simp)).1 (by rw [hcall_mc])
          have hsmc_eq : (evaluateHOLFiniteState s_kc
              (.call (some (none, none)) (ofString "memcpy")
                [.var .local (ofString "kc"), .var .local (ofString "key"), .var .local (ofString "klen")])).2 = s_mc := by
            rw [hcall_mc]
          rw [hsmc_eq] at hbre_mc
          obtain ⟨heff_mc, hloc_mc⟩ := hbre_mc
          -- Apply `evmInvAt_of_fresh_heap_step` from `s` to `s_mc`:
          have hA_mc : ArenaReady s_mc := by
            refine ⟨guestInv_congr (s := cpost_al) (t := s_mc) heff_mc.code heff_mc.memaddrs
              heff_mc.shMemaddrs heff_mc.baseAddr hA_cpal.1, ?_⟩
            exact arenaOK_congr (s := cpost_al) (t := s_mc) heff_mc.globals hA_cpal.2
          have hhp_mc : globN s_mc "heap_ptr" = qw.toNat := by
            rw [show globN s_mc "heap_ptr" = globN s_kc "heap_ptr" by simp [globN, heff_mc.globals]]
            exact hhp_cpal
          have hg_kept_mc : GlobalsKept ["heap_ptr"] s s_mc := by
            intro k hk
            have hk_ne : k ≠ ofString "heap_ptr" := fun h => hk (by simp [h])
            rw [heff_mc.globals]
            change s.globals.lookup k = cpost_al.globals.lookup k
            rw [hg_al, HolFiniteMapExact.lookup_update]
            simp [FUPDATE, hk_ne.symm]; rfl
          obtain ⟨hInv_mc, hch_mc, hR_mc⟩ := evmInvAt_of_fresh_heap_step
            hAs hInv hA_mc (heff_mc.be.trans hbe_al)
            (by rw [hhp_mc]; omega)
            hg_kept_mc
            (fun a hna => by
              have hna_kc : ¬ s_kc.memaddrs a := by
                change ¬ cpost_al.memaddrs a; rw [hma_al]; exact hna
              rw [heff_mc.out_dom a hna_kc]
              change cpost_al.memory a = s.memory a
              rw [hm_al]
              rfl)
            (fun b hb hno => by
              rw [heff_mc.byte_frame b hb (by
                intro i hi hin
                rw [List.mem_singleton] at hi; subst hi
                dsimp [InIvl] at hin
                exact hno ⟨hin.1, by rw [hhp_mc]; omega⟩)]
              unfold memB
              have hm_eq : s_kc.memory = s.memory := hm_al
              have hb_eq : s_kc.be = s.be := hbe_al
              rw [hm_eq, hb_eq])
          have hg_nonHp_mc : ∀ g : String, ofString g ≠ ofString "heap_ptr" → globN s_mc g = globN s g := by
            intro g hg
            exact (globN_eq_of_lookup_eq (hg_kept_mc (ofString g) (by simp [hg]))).symm
          have hts_mc : globN s_mc "ts" = globN s "ts" := hg_nonHp_mc "ts" (by decide)
          have hjn_mc : globN s_mc "journal_n" = globN s "journal_n" := hg_nonHp_mc "journal_n" (by decide)
          have hjc_mc : globN s_mc "journal_cap" = globN s "journal_cap" := hg_nonHp_mc "journal_cap" (by decide)
          have hj_mc : globN s_mc "journal" = globN s "journal" := hg_nonHp_mc "journal" (by decide)
          have hts_rec_unchanged : ∀ off : Nat, off + 8 ≤ 72 → globN s "ts" ≠ 0 →
              memW s_mc (globN s "ts" + off) = memW s (globN s "ts" + off) := by
            intro off hoff hts_nz
            have hts_fix : (globN s "ts", 72) ∈ fixedObjects s := by
              have h := typedRec_in_fixedObjects s (g := "ts") (sz := 72) (by decide)
              simpa [hts_nz] using h
            have hal_ts : Allocated s (globN s "ts", 72) := by
              rcases hInv.1.2.2.1.1 _ hts_fix with h0 | ⟨hal, _⟩
              · simp at h0
              · exact hal
            have hbound_ts := (Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_ts).2
            unfold memW
            have hm_cell : s_mc.memory (BitVec.ofNat 64 (globN s "ts" + off)) =
                s.memory (BitVec.ofNat 64 (globN s "ts" + off)) := by
              rw [heff_mc.cell_frame (BitVec.ofNat 64 (globN s "ts" + off)) (by
                intro i hi hch
                rw [List.mem_singleton] at hi; subst hi
                dsimp [CellHits] at hch
                have htn : (BitVec.ofNat 64 (globN s "ts" + off)).toNat = globN s "ts" + off :=
                  Nat.mod_eq_of_lt (by omega)
                rw [htn] at hch
                have hhp_le_sp : qw.toNat ≤ globN s "scratch_ptr" := by
                  have hlim_le_ss : heapLimit ≤ scratchStart := by decide
                  exact Nat.le_trans hq_lim (Nat.le_trans hlim_le_ss (Nat.le_trans hAs.2.2.2.1 hAs.2.2.2.2.1))
                rcases hal_ts with ⟨_, hhi⟩ | ⟨hlo, _⟩
                · omega
                · omega)]
              change cpost_al.memory _ = s.memory _
              rw [hm_al]; rfl
            rw [hm_cell]
          have hts64_mc : memW s_mc (globN s_mc "ts" + 64) = tw.toNat := by
            rw [hts_mc, hts_rec_unchanged 64 (by omega) hts_nz, htw_ts64]
          obtain ⟨ht0_S_mc, ht0_wref_mc, ht0_wrs_mc, hjr_mc, _⟩ :=
            ts64_role_props hInv_mc (by rwa [hts_mc]) (by rw [hts64_mc]; exact htw_nz)
          rw [hts64_mc] at ht0_S_mc ht0_wref_mc ht0_wrs_mc hjr_mc
          -- 4. Unpack `dec "r"` + 4 word stores + `assign "journal_n"` + `tailProg`:
          obtain ⟨vr, hvr_ev, tailPost, hrun_st0, hm_kc_eq⟩ := dec_ret_inv hrun_rdec
          have hjc_nz : globN s "journal_cap" ≠ 0 := by omega
          rcases hInv_mc.1.2.1.2.2.1 with h0 | ⟨hal_j_mc, _⟩
          · rw [hjc_mc] at h0; exact absurd h0 hjc_nz
          have hj_hi_mc := (Wave8Contracts.M08.ivl_allocated_bound hA_mc.2 hal_j_mc).2
          rw [hj_mc, hjc_mc] at hj_hi_mc
          obtain ⟨jw, hjw_lk⟩ := hA_mc.2.2.2.2.2.2.2.2.2 "journal" (by decide)
          obtain ⟨jnw, hjnw_lk⟩ := hA_mc.2.2.2.2.2.2.2.2.2 "journal_n" (by decide)
          have hjw_nat : jw.toNat = globN s "journal" := by
            rw [← hj_mc]; unfold GlobalWord at hjw_lk; simp [globN, hjw_lk]
          have hjnw_nat : jnw.toNat = globN s "journal_n" := by
            rw [← hjn_mc]; unfold GlobalWord at hjnw_lk; simp [globN, hjnw_lk]
          have hvr_word : vr = .val (.word (jw + jnw * 32#64)) := by
            have hjw_lk' : s_mc.globals.lookup (ofString "journal") = some (.val (.word jw)) := hjw_lk
            have hjnw_lk' : s_mc.globals.lookup (ofString "journal_n") = some (.val (.word jnw)) := hjnw_lk
            simp [evalHOLExact, evalListHOLExact, hjw_lk', hjnw_lk',
              valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL] at hvr_ev
            exact hvr_ev.symm
          subst hvr_word
          set rw := jw + jnw * 32#64
          have hrw_nat : rw.toNat = globN s "journal" + 32 * globN s "journal_n" := by
            have hmul : (jnw * 32#64).toNat = 32 * globN s "journal_n" := by
              rw [BitVec.toNat_mul, hjnw_nat, show (32#64 : BitVec 64).toNat = 32 from rfl]
              rw [Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]
            change (jw + jnw * 32#64).toNat = globN s "journal" + 32 * globN s "journal_n"
            rw [BitVec.toNat_add, hjw_nat, hmul, Nat.mod_eq_of_lt (by omega)]
          let s_r := setVarHOLFinite (ofString "r") (.val (.word rw)) s_mc
          have hr_sr : s_r.locals.lookup (ofString "r") = some (.val (.word rw)) := by
            simp [s_r, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have ht_sr : s_r.locals.lookup (ofString "t") = some (.val (.word tw)) := by
            simp [s_r, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "r" ≠ ofString "t" by decide, hloc_mc, ht_kc]
          have hkc_sr : s_r.locals.lookup (ofString "kc") = some (.val (.word kcw)) := by
            simp [s_r, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "r" ≠ ofString "kc" by decide, hloc_mc, hkc_lk]
          have hold_sr : s_r.locals.lookup (ofString "old") =
              some (.rStruct [.val (.word old0), .val (.word old1)]) := by
            simp [s_r, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "r" ≠ ofString "old" by decide, hloc_mc, hold_kc]
          change s_r.evaluateHOLFiniteState _ = (some (.returned rv_kc), tailPost) at hrun_st0
          obtain ⟨st1, hst1, hrest1⟩ := seq_store_ret_inv hrun_st0
          obtain ⟨st2, hst2, hrest2⟩ := seq_store_ret_inv hrest1
          obtain ⟨st3, hst3, hrest3⟩ := seq_store_ret_inv hrest2
          obtain ⟨st4, hst4, hrest4⟩ := seq_store_ret_inv hrest3
          obtain ⟨mid, hassign_jn, htail_run⟩ := seq_assign_ret_inv hrest4
          obtain ⟨_, hst1_eq⟩ := eval_store_word_exact (addr := rw) (w := tw)
            (by simp [evalHOLExact, hr_sr]) (by simp [evalHOLExact, ht_sr]) hst1
          have hr_st1 : st1.locals.lookup (ofString "r") = some (.val (.word rw)) := by rw [hst1_eq]; exact hr_sr
          have hkc_st1 : st1.locals.lookup (ofString "kc") = some (.val (.word kcw)) := by rw [hst1_eq]; exact hkc_sr
          obtain ⟨_, hst2_eq⟩ := eval_store_word_exact (addr := rw + 8#64) (w := kcw)
            (by simp [evalHOLExact, evalListHOLExact, hr_st1, valueIsWord, valueWord, wordOpHOL, wordOp])
            (by simp [evalHOLExact, hkc_st1]) hst2
          have hr_st2 : st2.locals.lookup (ofString "r") = some (.val (.word rw)) := by rw [hst2_eq]; exact hr_st1
          have hold_st2 : st2.locals.lookup (ofString "old") =
              some (.rStruct [.val (.word old0), .val (.word old1)]) := by
            rw [hst2_eq, hst1_eq]; exact hold_sr
          obtain ⟨_, hst3_eq⟩ := eval_store_word_exact (addr := rw + 16#64) (w := presw)
            (by simp [evalHOLExact, evalListHOLExact, hr_st2, valueIsWord, valueWord, wordOpHOL, wordOp])
            (hpres st2 hold_st2) hst3
          have hr_st3 : st3.locals.lookup (ofString "r") = some (.val (.word rw)) := by rw [hst3_eq]; exact hr_st2
          have hold_st3 : st3.locals.lookup (ofString "old") =
              some (.rStruct [.val (.word old0), .val (.word old1)]) := by
            rw [hst3_eq]; exact hold_st2
          obtain ⟨_, hst4_eq⟩ := eval_store_word_exact (addr := rw + 24#64) (w := old1)
            (by simp [evalHOLExact, evalListHOLExact, hr_st3, valueIsWord, valueWord, wordOpHOL, wordOp])
            (by simp [evalHOLExact, hold_st3]) hst4
          have hjn_st4 : st4.globals.lookup (ofString "journal_n") = some (.val (.word jnw)) := by
            rw [hst4_eq, hst3_eq, hst2_eq, hst1_eq]; exact hjnw_lk
          have hassign_eval : evaluateHOLFiniteState st4
              (.assign .global (ofString "journal_n")
                (.op .add [.var .global (ofString "journal_n"), .const 1])) =
              (none, setGlobalHOLFinite (ofString "journal_n") (.val (.word (jnw + 1#64))) st4) := by
            simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact,
              hjn_st4, wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact,
              isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
          rw [hassign_eval] at hassign_jn
          injection hassign_jn with _ hmr_eq
          subst hst1_eq; subst hst2_eq; subst hst3_eq; subst hst4_eq
          have hmid_eq : mid = setGlobalHOLFinite (ofString "journal_n") (.val (.word (jnw + 1#64)))
              { locals := s_r.locals, globals := s_r.globals, structs := s_r.structs, code := s_r.code,
                eshapes := s_r.eshapes,
                memory := Wave8M19.Htab.updW (Wave8M19.Htab.updW (Wave8M19.Htab.updW
                  (Wave8M19.Htab.updW s_mc.memory rw tw) (rw + 8#64) kcw) (rw + 16#64) presw) (rw + 24#64) old1,
                memaddrs := s_r.memaddrs, shMemaddrs := s_r.shMemaddrs, clock := s_r.clock,
                be := s_r.be, ffi := s_r.ffi, baseAddr := s_r.baseAddr, topAddr := s_r.topAddr } := hmr_eq.symm
          have hmid_mem : mid.memory =
              Wave8M19.Htab.updW (Wave8M19.Htab.updW (Wave8M19.Htab.updW
                (Wave8M19.Htab.updW s_mc.memory rw tw) (rw + 8#64) kcw) (rw + 16#64) presw) (rw + 24#64) old1 := by
            rw [hmid_eq]; rfl
          have hmid_glob : mid.globals = s_mc.globals.update (ofString "journal_n", .val (.word (jnw + 1#64))) := by
            rw [hmid_eq]; rfl
          have hmid_code : mid.code = originalRuntimeCode := by
            rw [hmid_eq]; exact heff_mc.code.trans hcode_kc
          have hmid_be : mid.be = s_mc.be := by
            rw [hmid_eq]; rfl
          have hA_mid : ArenaReady mid := by
            refine ⟨guestInv_congr (s := s_mc) (t := mid)
              (by rw [hmid_eq]; rfl) (by rw [hmid_eq]; rfl) (by rw [hmid_eq]; rfl) (by rw [hmid_eq]; rfl) hA_mc.1, ?_⟩
            unfold ArenaOK
            have hg_eq_ar : ∀ nm : String, ofString nm ≠ ofString "journal_n" →
                globN mid nm = globN s_mc nm := by
              intro nm hne
              unfold globN; rw [hmid_glob, HolFiniteMapExact.lookup_update]
              simp [FUPDATE, hne.symm]
            rw [hg_eq_ar "heap_ptr" (by decide), hg_eq_ar "frame_mem_ptr" (by decide),
                hg_eq_ar "scratch_ptr" (by decide)]
            exact ⟨hA_mc.2.1, hA_mc.2.2.1, hA_mc.2.2.2.1, hA_mc.2.2.2.2.1, hA_mc.2.2.2.2.2.1,
              hA_mc.2.2.2.2.2.2.1, hA_mc.2.2.2.2.2.2.2.1, hA_mc.2.2.2.2.2.2.2.2.1,
              globalsWord_update (s := s_mc) (t := mid)
                (ofString "journal_n") (jnw + 1#64) hmid_glob hA_mc.2.2.2.2.2.2.2.2.2⟩
          have hjn_mid_nat : globN mid "journal_n" = globN s_mc "journal_n" + 1 := by
            have hg_jn : mid.globals.lookup (ofString "journal_n") = some (.val (.word (jnw + 1#64))) := by
              rw [hmid_glob, HolFiniteMapExact.lookup_update]; simp [FUPDATE]
            have hcap_max := hInv.1.2.1.2.1
            have hmax_val : journalCapMax = 2 ^ 19 := rfl
            calc globN mid "journal_n"
              _ = (jnw + 1#64).toNat := by unfold globN; rw [hg_jn]
              _ = globN s "journal_n" + 1 := by
                  rw [BitVec.toNat_add, hjnw_nat, show (1#64 : BitVec 64).toNat = 1 from rfl,
                      Nat.mod_eq_of_lt (by omega)]
              _ = globN s_mc "journal_n" + 1 := by rw [hjn_mc]
          have hrw_off_nat : ∀ k : BitVec 64, k.toNat ≤ 24 →
              (rw + k).toNat = globN s "journal" + 32 * globN s "journal_n" + k.toNat := by
            intro k hk
            rw [BitVec.toNat_add, hrw_nat, Nat.mod_eq_of_lt (by omega)]
          have hcell_out_mid : ∀ a : BitVec 64,
              ¬ (globN s_mc "journal" + 32 * globN s_mc "journal_n" ≤ a.toNat ∧
                  a.toNat + 8 ≤ globN s_mc "journal" + 32 * globN s_mc "journal_n" + 32) →
              mid.memory a = s_mc.memory a := by
            intro a hna
            rw [hj_mc, hjn_mc] at hna
            rw [hmid_mem]
            have hne24 : a ≠ rw + 24#64 := by
              rintro rfl
              have h := hrw_off_nat 24#64 (by decide)
              rw [show (24#64 : BitVec 64).toNat = 24 from rfl] at h
              exact hna ⟨by omega, by omega⟩
            have hne16 : a ≠ rw + 16#64 := by
              rintro rfl
              have h := hrw_off_nat 16#64 (by decide)
              rw [show (16#64 : BitVec 64).toNat = 16 from rfl] at h
              exact hna ⟨by omega, by omega⟩
            have hne8 : a ≠ rw + 8#64 := by
              rintro rfl
              have h := hrw_off_nat 8#64 (by decide)
              rw [show (8#64 : BitVec 64).toNat = 8 from rfl] at h
              exact hna ⟨by omega, by omega⟩
            have hne0 : a ≠ rw := by
              rintro rfl
              exact hna ⟨by omega, by omega⟩
            simp [Wave8M19.Htab.updW, hne24, hne16, hne8, hne0]
          have ht0_mem_mid : memW mid (globN s_mc "journal" + 32 * globN s_mc "journal_n") = tw.toNat := by
            rw [hj_mc, hjn_mc]
            have hbv_rw : BitVec.ofNat 64 (globN s "journal" + 32 * globN s "journal_n") = rw := by
              apply BitVec.eq_of_toNat_eq
              rw [BitVec.toNat_ofNat, hrw_nat, Nat.mod_eq_of_lt (by omega)]
            have hm_rw : mid.memory rw = HolWordLab.word tw := by
              rw [hmid_mem]
              have hne24 : rw ≠ rw + 24#64 := by
                intro heq; have := congrArg BitVec.toNat heq
                rw [hrw_off_nat 24#64 (by decide), show (24#64 : BitVec 64).toNat = 24 from rfl] at this; omega
              have hne16 : rw ≠ rw + 16#64 := by
                intro heq; have := congrArg BitVec.toNat heq
                rw [hrw_off_nat 16#64 (by decide), show (16#64 : BitVec 64).toNat = 16 from rfl] at this; omega
              have hne8 : rw ≠ rw + 8#64 := by
                intro heq; have := congrArg BitVec.toNat heq
                rw [hrw_off_nat 8#64 (by decide), show (8#64 : BitVec 64).toNat = 8 from rfl] at this; omega
              simp [Wave8M19.Htab.updW, hne24, hne16, hne8]
            unfold memW; rw [hbv_rw, hm_rw]
          obtain ⟨hInv_mid, hch_mid, hR_mid⟩ := evmInvAt_of_journal_push
            hA_mc hInv_mc hA_mid hmid_be
            (by rw [hjn_mc, hjc_mc]; exact hjn_lt)
            hjn_mid_nat
            (fun k hk => by
              have hk_ne : k ≠ ofString "journal_n" := fun h => hk (by simp [h])
              rw [hmid_glob, HolFiniteMapExact.lookup_update]
              simp [FUPDATE, hk_ne.symm])
            hcell_out_mid
            ht0_mem_mid
            ht0_S_mc
            ht0_wref_mc
            (by rwa [hjr_mc])
            (by rw [hjr_mc]; decide)
          have hhp_mid : globN mid "heap_ptr" = qw.toNat := by
            have hg_hp : mid.globals.lookup (ofString "heap_ptr") = s_mc.globals.lookup (ofString "heap_ptr") := by
              rw [hmid_glob, HolFiniteMapExact.lookup_update]
              simp [FUPDATE, show ofString "journal_n" ≠ ofString "heap_ptr" by decide]
            exact (globN_eq_of_lookup_eq hg_hp.symm).symm.trans hhp_mc
          have hg_kept_mid : GlobalsKept ["heap_ptr", "journal_n"] s mid := by
            intro k hk
            have hk_hp : k ≠ ofString "heap_ptr" := fun h => hk (by simp [h])
            have hk_jn : k ≠ ofString "journal_n" := fun h => hk (by simp [h])
            have hne_jn : (ofString "journal_n" == k) = false := beq_false_of_ne hk_jn.symm
            rw [hmid_glob, HolFiniteMapExact.lookup_update]
            simp only [FUPDATE, hne_jn]
            exact hg_kept_mc k (by simp [hk_hp])
          have hmem_frame_mid : ∀ a : BitVec 64,
              ¬ (globN s "heap_ptr" ≤ a.toNat ∧ a.toNat < globN mid "heap_ptr") →
              ¬ (globN s "journal" + 32 * globN s "journal_n" ≤ a.toNat ∧
                  a.toNat + 8 ≤ globN s "journal" + 32 * globN s "journal_n" + 32) →
              mid.memory a = s.memory a := by
            intro a hno_hp hno_jr
            rw [hcell_out_mid a (by rwa [hj_mc, hjn_mc])]
            by_cases hda : s_kc.memaddrs a
            · rw [heff_mc.cell_frame a (by
                intro i hi hch
                rw [List.mem_singleton] at hi; subst hi
                dsimp [CellHits] at hch
                rw [hhp_mid] at hno_hp
                have ha8 : a.toNat % 8 = 0 := by
                  rw [hma_kc, ordinaryDomain_iff] at hda; exact hda.2.2
                have hs_hp8 := hAs.2.2.2.2.2.2.1
                exact hno_hp ⟨by omega, by omega⟩)]
              change cpost_al.memory a = s.memory a
              rw [hm_al]; rfl
            · rw [heff_mc.out_dom a hda]
              change cpost_al.memory a = s.memory a
              rw [hm_al]; rfl
          have hts_mid : globN mid "ts" = globN s "ts" := by
            have hg_ts : mid.globals.lookup (ofString "ts") = s_mc.globals.lookup (ofString "ts") := by
              rw [hmid_glob, HolFiniteMapExact.lookup_update]
              simp [FUPDATE, show ofString "journal_n" ≠ ofString "ts" by decide]
            exact (globN_eq_of_lookup_eq hg_ts.symm).symm.trans hts_mc
          have hts64_mid : memW mid (globN s "ts" + 64) = memW s (globN s "ts" + 64) := by
            have hpw_fix : ((globalBuffers.map fun gn => (globN s_mc gn.1, if globN s_mc gn.1 = 0 then 0 else gn.2)) ++
                [(globN s_mc "journal", 32 * globN s_mc "journal_cap")] ++ blockOutObjects s_mc ++ balObjects s_mc).Pairwise Disj := by
              have hp := hInv_mc.1.2.2.1.2
              unfold fixedObjects at hp
              simpa [hjc_mc, hjc_nz] using hp
            obtain ⟨hpw_gb_jr_bo, _, _⟩ := List.pairwise_append.1 hpw_fix
            obtain ⟨hpw_gb_jr, _, _⟩ := List.pairwise_append.1 hpw_gb_jr_bo
            obtain ⟨_, _, hdisj_gb_jr⟩ := List.pairwise_append.1 hpw_gb_jr
            have hdisj_ts_jr : Disj (globN s_mc "ts", 72) (globN s_mc "journal", 32 * globN s_mc "journal_cap") :=
              hdisj_gb_jr _ (List.mem_map.2 ⟨("ts", 72), by simp [globalBuffers], by simp [hts_mc, hts_nz]⟩)
                _ (List.mem_singleton.2 rfl)
            rw [hts_mc, hj_mc, hjc_mc] at hdisj_ts_jr
            have hts_fix_s : (globN s "ts", 72) ∈ fixedObjects s := by
              have h := typedRec_in_fixedObjects s (g := "ts") (sz := 72) (by decide)
              simpa [hts_nz] using h
            have hal_ts_s : Allocated s (globN s "ts", 72) := by
              rcases hInv.1.2.2.1.1 _ hts_fix_s with h0 | ⟨hal, _⟩
              · simp at h0
              · exact hal
            have hbound_ts_s := (Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_ts_s).2
            have hm_cell64 : mid.memory (BitVec.ofNat 64 (globN s "ts" + 64)) =
                s_mc.memory (BitVec.ofNat 64 (globN s "ts" + 64)) := by
              apply hcell_out_mid
              rw [hj_mc, hjn_mc]
              have htn : (BitVec.ofNat 64 (globN s "ts" + 64)).toNat = globN s "ts" + 64 :=
                Nat.mod_eq_of_lt (by omega)
              rw [htn]
              dsimp [Disj] at hdisj_ts_jr
              omega
            have hmc_eq : memW mid (globN s "ts" + 64) = memW s_mc (globN s "ts" + 64) := by
              unfold memW; rw [hm_cell64]
            exact hmc_eq.trans (hts_rec_unchanged 64 (by omega) hts_nz)
          have hloc_other : ∀ nm : MlS, nm ≠ ofString "klen" → nm ≠ ofString "kc" → nm ≠ ofString "r" →
              mid.locals.lookup nm = s.locals.lookup nm := by
            intro nm h1 h2 h3
            have hmid_loc : mid.locals = s_r.locals := by rw [hmid_eq]; rfl
            rw [hmid_loc]
            simp [s_r, s_kc, s_kl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              hloc_mc, h1.symm, h2.symm, h3.symm]
          have hp_tp : post = { tailPost with locals := post.locals } := by
            rw [hp_klen, ← hm_klen_eq, hm_kc_eq]
          exact ⟨mid, tailPost, hmid_code, hA_mid, hInv_mid,
                 hch_mid.trans hch_mc, hR_mid.trans hR_mc,
                 by rw [hhp_mid]; omega,
                 hg_kept_mid, hmem_frame_mid, hts_mid, hts64_mid,
                 hloc_other, htail_run, hp_tp⟩
        | _ => simp at hrun_klen
    | _ => simp at hrun_klen

/-! ## 6. `jdel_ts64_step` and `jset_ts64_step` -/

theorem trap_with_call_not_none {F : Type}
    (t : PanSemStateFiniteExact 64 F) (hcode : t.code = originalRuntimeCode) (c : BitVec 64) :
    (evaluateHOLFiniteState t (.call (some (none, none)) (ofString "trap_with") [.const c])).1 ≠ none := by
  rw [evaluateHOLFiniteState_call]
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) [.const c] with _ | vals
  · simp
  · dsimp only
    rcases hl : lookupCodeHOLFinite t.code.lookup (ofString "trap_with") vals with _ | ⟨body', callee, rs⟩
    · simp
    · dsimp only
      have hbody_tr : body' = sourceFnBody Guest.Software.guestFn_trap_with :=
        lookupCodeHOLFinite_installed_body t.code.lookup (ofString "trap_with") _ _ _ _ _ vals callee
          (by rw [hcode]; exact lookup_trap_with) hl
      subst hbody_tr
      split
      · simp
      · have hout := evaluate_trap_with_body_outcomes (callEntryStateHOLFinite t callee)
        rcases hr : evaluateHOLFiniteState (callEntryStateHOLFinite t callee)
            (sourceFnBody Guest.Software.guestFn_trap_with) with ⟨res, st⟩
        rw [hr] at hout; dsimp only at hout ⊢
        cases res with
        | none => exact absurd rfl hout.1
        | some r0 =>
          cases r0 with
          | returned v => exact absurd rfl (hout.2.1 v)
          | _ => simp

theorem two_word_val_of_shape {v : ValueHOL 64} :
    shapeEqHOL (shapeOfHOLExact v) (.comb [.one, .one]) = true →
    ∃ w0 w1 : BitVec 64, v = .rStruct [.val (.word w0), .val (.word w1)] := by
  rcases v with _ | vs | _
  · simp [shapeOfHOLExact, shapeEqHOL]
  · rcases vs with _ | ⟨v0, _ | ⟨v1, _ | _⟩⟩
    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
    · simp only [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL, List.map, Bool.and_eq_true, Bool.and_true]
      rintro ⟨h0, h1⟩
      rcases v0 with ⟨⟨w0⟩⟩ | _ | _ <;> try simp [shapeOfHOLExact, shapeEqHOL] at h0
      rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> try simp [shapeOfHOLExact, shapeEqHOL] at h1
      exact ⟨w0, w1, rfl⟩
    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
  · simp [shapeOfHOLExact, shapeEqHOL]

theorem htab_get_t_ne_zero {F : Type}
    {s cpost : PanSemStateFiniteExact 64 F}
    {keyw : BitVec 64} {cal : HolFiniteMapExact MlS (ValueHOL 64)} {rv : ValueHOL 64}
    (hcode : s.code = originalRuntimeCode)
    (hAs : ArenaReady s)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "htab_get")
      [.val (.word 0#64), .val (.word keyw)] =
      some (sourceFnBody Guest.Software.guestFn_htab_get, cal, .comb [.one, .one]))
    (hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s cal)
      (sourceFnBody Guest.Software.guestFn_htab_get) = (some (.returned rv), cpost)) : False := by
  obtain ⟨_, hct⟩ := Wave8M19.Htab.lookupCodeHOLFinite_param_at s.code.lookup (ofString "htab_get") []
    (ofString "t") .one [(ofString "key", .one)] _ (.comb [.one, .one])
    (by intro p hp; simp at hp; rw [hp]; decide)
    (by rw [hcode]; exact lookup_htab_get) (vpre := []) (by simp) hl
  let ce := callEntryStateHOLFinite s cal
  change evaluateHOLFiniteState ce _ = _ at hrun
  have hbody_hg : sourceFnBody Guest.Software.guestFn_htab_get =
      .decCall (ofString "leaf") .one (ofString "htab_find_leaf")
        [.var .local (ofString "t"), .var .local (ofString "key")]
        (.seq
          (.ite (.cmp .equal (.var .local (ofString "leaf")) (.const 0))
            (.return (.rstruct [.const 0, .const 0])) .skip)
          (.dec (ofString "klen") .one (.load .one (.op .add [.var .local (ofString "t"), .const 0]))
            (.dec (ofString "stride") .one (.load .one (.op .add [.var .local (ofString "t"), .const 8]))
              (.dec (ofString "keys") .one (.load .one (.op .add [.var .local (ofString "t"), .const 32]))
                (.decCall (ofString "eq") .one (ofString "memeq")
                  [.op .add [.var .local (ofString "keys"),
                    .panop .mul [.var .local (ofString "leaf"), .var .local (ofString "stride")]],
                   .var .local (ofString "key"), .var .local (ofString "klen")]
                  (.seq
                    (.ite (.cmp .equal (.var .local (ofString "eq")) (.const 0))
                      (.return (.rstruct [.const 0, .const 0])) .skip)
                    (.return (.rstruct [.const 1,
                      .load .one (.op .add [.load .one (.op .add [.var .local (ofString "t"), .const 40]),
                        .panop .mul [.var .local (ofString "leaf"), .const 32], .const 8])])))))))) := rfl
  rw [hbody_hg, evaluateHOLFiniteState_decCall_total] at hrun
  rcases hargs_fl : evalListHOLFinite ce (h := fun a => Classical.propDecidable (ce.memaddrs a))
      [.var .local (ofString "t"), .var .local (ofString "key")] with _ | vals_fl
  · rw [hargs_fl] at hrun; simp at hrun
  rw [hargs_fl] at hrun; dsimp only at hrun
  rcases hl_fl : lookupCodeHOLFinite ce.code.lookup (ofString "htab_find_leaf") vals_fl with _ | ⟨body_fl, cal_fl, ret_fl⟩
  · rw [hl_fl] at hrun; simp at hrun
  rw [hl_fl] at hrun; dsimp only at hrun
  by_cases hclk_ce : ce.clock = 0
  · rw [if_pos hclk_ce] at hrun; simp at hrun
  rw [if_neg hclk_ce, fixClockHOLFinite_evaluateState] at hrun
  have hlk_fl : originalRuntimeCode.lookup (ofString "htab_find_leaf") =
      some ([(ofString "t", .one), (ofString "key", .one)],
        sourceFnBody Guest.Software.guestFn_htab_find_leaf, .one) :=
    lookup_of_guestAst_getElem 131 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_htab_find_leaf) rfl
  have hrf_eq : ret_fl = .one := by
    have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
      ce.code.lookup (ofString "htab_find_leaf") vals_fl _ cal_fl ret_fl hl_fl
    change lookupCodeHOLExact s.code.lookup _ _ = _ at hx
    rw [hcode] at hx; simp only [Flapjack.lookupCodeHOLExact, hlk_fl] at hx
    split at hx
    · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
    · cases hx
  subst hrf_eq
  have hbf_eq : body_fl = sourceFnBody Guest.Software.guestFn_htab_find_leaf :=
    lookupCodeHOLFinite_installed_body ce.code.lookup (ofString "htab_find_leaf") _ _ _ _ _ vals_fl cal_fl
      (by change s.code.lookup _ = _; rw [hcode]; exact hlk_fl) hl_fl
  subst hbf_eq
  obtain ⟨tv_fl, _, rfl, htv_fl⟩ := Wave8M19.Htab.evalList_cons_inv ce _ _ hargs_fl
  obtain ⟨_, hct_fl⟩ := Wave8M19.Htab.lookupCodeHOLFinite_param_at ce.code.lookup (ofString "htab_find_leaf") []
    (ofString "t") .one [(ofString "key", .one)] _ .one
    (by intro p hp; simp at hp; rw [hp]; decide)
    (by change s.code.lookup _ = _; rw [hcode]; exact hlk_fl) (vpre := []) (by simp) hl_fl
  have hcal_t_fl : cal_fl.lookup (ofString "t") = some (.val (.word 0#64)) := by
    rw [hct_fl]
    have ht_ce : ce.locals.lookup (ofString "t") = some (.val (.word 0#64)) := hct
    simpa [evalHOLExact, ht_ce] using htv_fl.symm
  let ce_fl := callEntryStateHOLFinite ce cal_fl
  have hndom0 : ¬ ce_fl.memaddrs 0#64 := by
    change ¬ s.memaddrs 0#64
    rw [hAs.1.memaddrs, ordinaryDomain_iff]
    intro ⟨_, hlo, _⟩
    have hsb : sourceBase = 2701131776 := rfl
    have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
    omega
  have hbody_fl : sourceFnBody Guest.Software.guestFn_htab_find_leaf =
      .dec (ofString "keybits") .one
        (.panop .mul [.load .one (.op .add [.var .local (ofString "t"), .const 0]), .const 8])
        (.dec (ofString "nodes") .one (.load .one (.op .add [.var .local (ofString "t"), .const 40]))
          (.dec (ofString "n") .one (.load .one (.op .add [.var .local (ofString "t"), .const 56]))
            (.seq
              (.while (.cmp .notEqual (.var .local (ofString "n")) (.const 0))
                (.dec (ofString "b") .one
                  (.load .one (.op .add [.var .local (ofString "nodes"),
                    .panop .mul [.var .local (ofString "n"), .const 32], .const 24]))
                  (.seq
                    (.ite (.cmp .equal (.var .local (ofString "b")) (.var .local (ofString "keybits")))
                      .break .skip)
                    (.ite (.cmp .equal (.op .and [.shift .lsr (.loadByte (.op .add [.var .local (ofString "key"),
                        .shift .lsr (.var .local (ofString "b")) (.const 3)]))
                      (.op .sub [.const 7, .op .and [.var .local (ofString "b"), .const 7]]), .const 1]) (.const 0))
                      (.assign .local (ofString "n") (.load .one (.op .add [.var .local (ofString "nodes"),
                        .panop .mul [.var .local (ofString "n"), .const 32], .const 8])))
                      (.assign .local (ofString "n") (.load .one (.op .add [.var .local (ofString "nodes"),
                        .panop .mul [.var .local (ofString "n"), .const 32], .const 16])))))))
              (.return (.var .local (ofString "n")))))) := rfl
  rcases hfl_r : evaluateHOLFiniteState ce_fl (sourceFnBody Guest.Software.guestFn_htab_find_leaf) with ⟨rfl0, pfl0⟩
  change evaluateHOLFiniteState ce_fl _ = _ at hfl_r
  rw [show callEntryStateHOLFinite ce cal_fl = ce_fl from rfl] at hrun
  rw [hfl_r] at hrun; dsimp only at hrun
  rw [hbody_fl, evaluateHOLFiniteState_dec_total] at hfl_r; dsimp only at hfl_r
  have hev_kb : @evalHOLExact 64 F _ ce_fl.toExact (fun a => Classical.propDecidable (ce_fl.memaddrs a))
      (.panop .mul [.load .one (.op .add [.var .local (ofString "t"), .const 0]), .const 8]) = none := by
    have ht_fl : ce_fl.locals.lookup (ofString "t") = some (.val (.word 0#64)) := hcal_t_fl
    simp [evalHOLExact, evalListHOLExact, ht_fl, wordOpHOL, wordOp, valueIsWord, valueWord,
      memLoadHOLExact, hndom0]
  rw [hev_kb] at hfl_r; dsimp only at hfl_r
  injection hfl_r with hr_fl _; subst hr_fl; simp at hrun

theorem jdel_ts64_step {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    {tw keyw : BitVec 64} {rv : ValueHOL 64}
    (hcode : s.code = originalRuntimeCode)
    (hAs : ArenaReady s)
    (hInv : EvmInvAt s S)
    (ht : s.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hkey : s.locals.lookup (ofString "key") = some (.val (.word keyw)))
    (hts_nz : globN s "ts" ≠ 0)
    (htw_ts64 : tw.toNat = memW s (globN s "ts" + 64))
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_jdel)).1 =
      some (.returned rv)) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_jdel)).2
    ArenaReady post ∧
    EvmInvAt post S ∧
    evmChain post = evmChain s ∧
    evmR post = evmR s := by
  dsimp only
  have hbody : sourceFnBody Guest.Software.guestFn_jdel =
      .decCall (ofString "old") (.comb [.one, .one]) (ofString "htab_get")
        [.var .local (ofString "t"), .var .local (ofString "key")]
        (.seq
          (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "old"))) (.const 0))
            (.return (.const 0))
            .skip)
          (.seq
            (.ite (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap")))
              (.call (some (none, none)) (ofString "trap_with") [.const 5])
              .skip)
            (jrecordPushTailProg (.const 1)
              (.seq
                (.call (some (none, none)) (ofString "htab_del")
                  [.var .local (ofString "t"), .var .local (ofString "key")])
                (.return (.const 0)))))) := rfl
  rcases hrun : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_jdel) with ⟨res0, post⟩
  rw [hrun] at hret; dsimp only at hret ⊢; subst hret
  rw [hbody, evaluateHOLFiniteState_decCall_total] at hrun
  have hargs_get : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "t"), .var .local (ofString "key")] =
      some [.val (.word tw), .val (.word keyw)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ht, hkey]
  rw [hargs_get] at hrun; dsimp only at hrun
  rcases hl_get : lookupCodeHOLFinite s.code.lookup (ofString "htab_get")
      [.val (.word tw), .val (.word keyw)] with _ | ⟨body_get, cal_get, ret_get⟩
  · rw [hl_get] at hrun; simp at hrun
  rw [hl_get] at hrun; dsimp only at hrun
  by_cases hclk0 : s.clock = 0
  · rw [if_pos hclk0] at hrun; simp at hrun
  rw [if_neg hclk0, fixClockHOLFinite_evaluateState] at hrun
  have hbg_eq : body_get = sourceFnBody Guest.Software.guestFn_htab_get :=
    lookupCodeHOLFinite_installed_body s.code.lookup (ofString "htab_get") _ _ _ _ _
      [.val (.word tw), .val (.word keyw)] cal_get (by rw [hcode]; exact lookup_htab_get) hl_get
  subst hbg_eq
  have hrg_eq : ret_get = .comb [.one, .one] := by
    have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
      s.code.lookup (ofString "htab_get") [.val (.word tw), .val (.word keyw)] _ cal_get ret_get hl_get
    rw [hcode] at hx; simp only [Flapjack.lookupCodeHOLExact, lookup_htab_get] at hx
    split at hx
    · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
    · cases hx
  subst hrg_eq
  let ce_get := callEntryStateHOLFinite s cal_get
  have hlf_get : Wave8Contracts.M15.LocFrame ce_get
      (evaluateHOLFiniteState ce_get (sourceFnBody Guest.Software.guestFn_htab_get)).2 :=
    Wave8Contracts.M15.evaluate_readOnlyProg htabGetCallees htabGetCallees_good
      (sourceFnBody Guest.Software.guestFn_htab_get) (by decide) ce_get hcode
  rcases hrun_get : evaluateHOLFiniteState (callEntryStateHOLFinite s cal_get)
      (sourceFnBody Guest.Software.guestFn_htab_get) with ⟨res_get, cpost_get⟩
  change evaluateHOLFiniteState ce_get _ = _ at hrun_get
  rw [show callEntryStateHOLFinite s cal_get = ce_get from rfl] at hrun
  rw [hrun_get] at hrun hlf_get; dsimp only at hrun hlf_get
  cases res_get with
  | none => simp at hrun
  | some rg0 =>
    cases rg0 with
    | returned oldv =>
      dsimp only at hrun
      split at hrun
      · rename_i hsh_both
        have hsh_old : shapeEqHOL (shapeOfHOLExact oldv) (.comb [.one, .one]) = true := by
          simp only [Bool.and_eq_true] at hsh_both; exact hsh_both.1
        obtain ⟨old0, old1, rfl⟩ := two_word_val_of_shape hsh_old
        have htw_nz : tw.toNat ≠ 0 := by
          intro htz
          have htw0 : tw = 0#64 := BitVec.eq_of_toNat_eq htz
          subst htw0
          exact htab_get_t_ne_zero hcode hAs hl_get hrun_get
        let s1 := setVarHOLFinite (ofString "old") (.rStruct [.val (.word old0), .val (.word old1)])
          { cpost_get with locals := s.locals }
        have hs1_eq : s1 = { s with locals := s1.locals, clock := cpost_get.clock } := by
          dsimp only [s1]
          unfold Wave8Contracts.M15.LocFrame at hlf_get
          rw [hlf_get]; rfl
        have hcode_s1 : s1.code = originalRuntimeCode := by rw [hs1_eq]; exact hcode
        have hA_s1 : ArenaReady s1 := by rw [hs1_eq]; exact (arenaReady_lc s _ _).2 hAs
        have hInv_s1 : EvmInvAt s1 S := by rw [hs1_eq]; exact (evmInvAt_lc s _ _ S).2 hInv
        have hold_s1 : s1.locals.lookup (ofString "old") =
            some (.rStruct [.val (.word old0), .val (.word old1)]) := by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have ht_s1 : s1.locals.lookup (ofString "t") = some (.val (.word tw)) := by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "old" ≠ ofString "t" by decide, ht]
        have hkey_s1 : s1.locals.lookup (ofString "key") = some (.val (.word keyw)) := by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "old" ≠ ofString "key" by decide, hkey]
        have hs1_def : setVarHOLFinite (ofString "old")
            (.rStruct [.val (.word old0), .val (.word old1)])
            { cpost_get with locals := s.locals } = s1 := rfl
        rw [hs1_def] at hrun
        -- First `ite`: `if old.0 == 0 then return 0 else skip`
        rcases hs1_run : s1.evaluateHOLFiniteState
            (.seq
              (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "old"))) (.const 0))
                (.return (.const 0))
                .skip)
              (.seq
                (.ite (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap")))
                  (.call (some (none, none)) (ofString "trap_with") [.const 5])
                  .skip)
                (jrecordPushTailProg (.const 1)
                  (.seq
                    (.call (some (none, none)) (ofString "htab_del")
                      [.var .local (ofString "t"), .var .local (ofString "key")])
                    (.return (.const 0)))))) with ⟨rs1_res, ms1⟩
        rw [hs1_run] at hrun; dsimp only at hrun
        injection hrun with hrs1 hpost_ms1
        subst hrs1
        have hpost_ms1' : post = { ms1 with locals := post.locals } := by rw [← hpost_ms1]
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hs1_run
        by_cases hold0_z : old0 = 0#64
        · subst hold0_z
          have hcmp0 : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
              (.cmp .equal (.rfield 0 (.var .local (ofString "old"))) (.const 0)) =
              some (.val (.word 1#64)) := by
            simp [evalHOLExact, hold_s1, Compiler.Encoders.Asm.wordCmpHOL]
          rw [hcmp0] at hs1_run; dsimp only at hs1_run
          have h1_nz : (1#64 : BitVec 64) ≠ 0 := by decide
          rw [if_neg h1_nz, evaluateHOLFiniteState_return] at hs1_run
          simp [evalHOLExact, shapeOfHOLExact] at hs1_run
          obtain ⟨_, hp_eq⟩ := hs1_run
          have hp_s : post = { s with locals := post.locals, clock := cpost_get.clock } := by
            rw [hpost_ms1', ← hp_eq, hs1_eq]
            cases s; rfl
          rw [hp_s]
          exact ⟨(arenaReady_lc s _ _).2 hAs,
                 (evmInvAt_lc s _ _ S).2 hInv,
                 evmChain_lc s _ _,
                 evmR_lc s _ _⟩
        · have hcmp0 : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
              (.cmp .equal (.rfield 0 (.var .local (ofString "old"))) (.const 0)) =
              some (.val (.word 0#64)) := by
            simp [evalHOLExact, hold_s1, Compiler.Encoders.Asm.wordCmpHOL, hold0_z]
          rw [hcmp0] at hs1_run; dsimp only at hs1_run
          have h0_eq : (0#64 : BitVec 64) = 0 := rfl
          rw [if_pos h0_eq, evaluateHOLFiniteState_skip] at hs1_run; dsimp only at hs1_run
          -- Second `ite`: `if journal_n >=+ journal_cap then trap_with(5) else skip`
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hs1_run
          obtain ⟨jnw, hjn_lk⟩ := hA_s1.2.2.2.2.2.2.2.2.2 "journal_n" (by decide)
          obtain ⟨jcw, hjc_lk⟩ := hA_s1.2.2.2.2.2.2.2.2.2 "journal_cap" (by decide)
          have hjn_nat : jnw.toNat = globN s1 "journal_n" := by
            unfold GlobalWord at hjn_lk; simp [globN, hjn_lk]
          have hjc_nat : jcw.toNat = globN s1 "journal_cap" := by
            unfold GlobalWord at hjc_lk; simp [globN, hjc_lk]
          have hjn_bound : jnw.toNat < 2 ^ 64 := jnw.isLt
          have hjc_bound : jcw.toNat < 2 ^ 64 := jcw.isLt
          have hjn_lk' : s1.globals.lookup (ofString "journal_n") = some (.val (.word jnw)) := hjn_lk
          have hjc_lk' : s1.globals.lookup (ofString "journal_cap") = some (.val (.word jcw)) := hjc_lk
          by_cases hjn_ge : globN s1 "journal_cap" ≤ globN s1 "journal_n"
          · have hnl : Compiler.Encoders.Asm.wordCmpHOL .notLower jnw jcw = true := by
              simp only [Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
              have hnotlt : ¬ (jnw.toNat < jcw.toNat) := by omega
              simp [hnotlt]
            have hcmp_jn : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
                (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap"))) =
                some (.val (.word 1#64)) := by
              simp [evalHOLExact, hjn_lk', hjc_lk', hnl]
            rw [hcmp_jn] at hs1_run; dsimp only at hs1_run
            have h1_nz : (1#64 : BitVec 64) ≠ 0 := by decide
            rw [if_neg h1_nz] at hs1_run
            obtain ⟨_, htr_none, _⟩ := seq_call0_ret_inv (by rw [evaluateHOLFiniteState_seq_line780]; exact hs1_run)
            exact absurd (congrArg Prod.fst htr_none) (trap_with_call_not_none s1 hcode_s1 5)
          · have hjn_lt_s1 : globN s1 "journal_n" < globN s1 "journal_cap" := by omega
            have hnl : Compiler.Encoders.Asm.wordCmpHOL .notLower jnw jcw = false := by
              simp only [Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
              have hlt : jnw.toNat < jcw.toNat := by omega
              simp [hlt]
            have hcmp_jn : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
                (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap"))) =
                some (.val (.word 0#64)) := by
              simp [evalHOLExact, hjn_lk', hjc_lk', hnl]
            rw [hcmp_jn] at hs1_run; dsimp only at hs1_run
            rw [if_pos h0_eq, evaluateHOLFiniteState_skip] at hs1_run; dsimp only at hs1_run
            -- `jrecordPushTailProg (.const 1) (seq (call "htab_del" ...) (return 0))`:
            have hts_s1 : globN s1 "ts" = globN s "ts" := by rw [hs1_eq]; rfl
            have hts64_s1 : memW s1 (globN s1 "ts" + 64) = memW s (globN s "ts" + 64) := by
              rw [hs1_eq]; rfl
            obtain ⟨s_jp, tailPost, hcode_jp, hA_jp, hInv_jp, hch_jp, hR_jp, _, _, _, hts_jp, hts64_jp,
              hloc_jp, htail_run, hmtail_tp⟩ :=
              jrecord_push_tail_step (presw := 1#64) hcode_s1 hA_s1 hInv_s1 ht_s1 hkey_s1 hold_s1
                (fun st _ => rfl) hjn_lt_s1 (by rwa [hts_s1])
                (by rw [hts64_s1]; exact htw_ts64) htw_nz hs1_run
            have hpost_mtail : post = { ms1 with locals := post.locals } := hpost_ms1'
            obtain ⟨s_del, hcall_del, hret_run⟩ := seq_call0_ret_inv htail_run
            obtain ⟨vals_d, body_d, cal_d, ret_d, rvd, cpost_d, hargs_d, hl_d, hrun_d, hsdel_eq⟩ :=
              Wave8M19.Htab.call0_flow s_jp _ _ (Or.inl (congrArg Prod.fst hcall_del))
            have hlk_del : originalRuntimeCode.lookup (ofString "htab_del") =
                some ([(ofString "t", .one), (ofString "key", .one)],
                  sourceFnBody Guest.Software.guestFn_htab_del, .one) :=
              lookup_of_guestAst_getElem 139 (by rw [guestAst_len]; decide)
                (extractFn Guest.Software.guestFn_htab_del) rfl
            have hrd_eq : ret_d = .one := by
              have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
                s_jp.code.lookup (ofString "htab_del") vals_d _ cal_d ret_d hl_d
              rw [hcode_jp] at hx; simp only [Flapjack.lookupCodeHOLExact, hlk_del] at hx
              split at hx
              · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
              · cases hx
            subst hrd_eq
            have hbd_eq : body_d = sourceFnBody Guest.Software.guestFn_htab_del :=
              lookupCodeHOLFinite_installed_body s_jp.code.lookup (ofString "htab_del") _ _ _ _ _ vals_d cal_d
                (by rw [hcode_jp]; exact hlk_del) hl_d
            subst hbd_eq
            have ht_jp : s_jp.locals.lookup (ofString "t") = some (.val (.word tw)) := by
              rw [hloc_jp (ofString "t") (by decide) (by decide) (by decide)]; exact ht_s1
            obtain ⟨tv, _, rfl, htv⟩ := Wave8M19.Htab.evalList_cons_inv s_jp _ _ hargs_d
            obtain ⟨_, hct_d⟩ := Wave8M19.Htab.lookupCodeHOLFinite_param_at s_jp.code.lookup (ofString "htab_del") []
              (ofString "t") .one [(ofString "key", .one)] _ .one
              (by intro p hp; simp at hp; rw [hp]; decide)
              (by rw [hcode_jp]; exact hlk_del) (vpre := []) (by simp) hl_d
            have hcal_t : cal_d.lookup (ofString "t") = some (.val (.word tw)) := by
              rw [hct_d]; simp only [evalHOLExact, ht_jp] at htv; exact htv.symm
            let entry_d := callEntryStateHOLFinite s_jp cal_d
            have hloc_td : locN entry_d "t" = tw.toNat := by
              simp [entry_d, callEntryStateHOLFinite, locN, hcal_t]
            have hts_jp' : globN s_jp "ts" = globN s "ts" := hts_jp.trans hts_s1
            have hts64_jp' : memW s_jp (globN s_jp "ts" + 64) = tw.toNat := by
              rw [hts_jp', ← hts_s1, hts64_jp, hts64_s1, htw_ts64]
            obtain ⟨ht0_S_jp, _, _, _, ht0_ndel_jp, ht0_nws32_jp, ht0_nbs32_jp, ht0_nba_jp, ht0_nad_jp, ht0_nts32_jp⟩ :=
              ts64_role_props hInv_jp (by rwa [hts_jp']) (by rw [hts64_jp']; exact htw_nz)
            rw [hts64_jp'] at ht0_S_jp ht0_ndel_jp ht0_nws32_jp ht0_nbs32_jp ht0_nba_jp ht0_nad_jp ht0_nts32_jp
            have hArg_d : HtabArgWF entry_d := by
              refine ⟨⟨guestInv_congr (s := s_jp) rfl rfl rfl rfl hA_jp.1, hA_jp.2⟩, ?_, ?_⟩
              · rw [hloc_td]
                exact (htabWF_lc s_jp entry_d.locals s_jp.globals entry_d.clock _).mpr
                  (hInv_jp.1.1.2.1 _ ht0_S_jp).1
              · rw [hloc_td]
                intro i hi
                exact ((hInv_jp.1.1.2.1 _ ht0_S_jp).2 i hi).1
            have hdel_sub := htab_del_values_sub entry_d hcode_jp hArg_d rvd (by rw [hrun_d])
            have hcpost_eq : (evaluateHOLFiniteState entry_d (sourceFnBody Guest.Software.guestFn_htab_del)).2 = cpost_d := by
              rw [hrun_d]
            rw [hcpost_eq, hloc_td] at hdel_sub
            obtain ⟨hexit_d, hbe_d, _⟩ := hdel_sub
            unfold HtabExit at hexit_d; dsimp only at hexit_d
            rw [hloc_td] at hexit_d
            obtain ⟨hAp_d, hwf_d, hhdr0_d, _, hhp_d, hfp_d, hfr_d, hg_d⟩ := hexit_d
            obtain ⟨hInv_cd, hch_cd, hR_cd, _⟩ := evmInvAt_of_htab_step
              hA_jp hInv_jp hAp_d hbe_d hwf_d hhdr0_d hhp_d hfp_d hfr_d
              (fun k hk => by
                have hk_hp : k ≠ ofString "heap_ptr" := fun h => hk (by simp [h])
                exact hg_d k (by simp [hk_hp]))
              (by
                have hjn_entry : globN entry_d "journal_n" = globN s_jp "journal_n" := rfl
                have hjn_cd : globN cpost_d "journal_n" = globN s_jp "journal_n" :=
                  (globN_eq_of_lookup_eq (hg_d (ofString "journal_n") (by decide)).symm).trans hjn_entry
                omega)
              ht0_S_jp ht0_ndel_jp ht0_nws32_jp ht0_nbs32_jp ht0_nba_jp ht0_nad_jp
              (Or.inl ht0_nts32_jp)
            -- Finish `return 0` from `s_del`:
            have hsdel_cd : s_del = { cpost_d with locals := s_jp.locals } :=
              (Prod.mk.inj (hcall_del.symm.trans hsdel_eq)).2
            rw [evaluateHOLFiniteState_return] at hret_run
            simp [evalHOLExact, shapeOfHOLExact] at hret_run
            obtain ⟨_, hret_sdel⟩ := hret_run
            have hp_cd : post = { cpost_d with locals := post.locals, clock := cpost_d.clock } := by
              rw [hpost_mtail, hmtail_tp, ← hret_sdel, hsdel_cd]
              cases cpost_d; rfl
            rw [hp_cd]
            have hch_s1 : evmChain s1 = evmChain s := by rw [hs1_eq]; exact evmChain_lc s _ _
            have hR_s1 : evmR s1 = evmR s := by rw [hs1_eq]; exact evmR_lc s _ _
            exact ⟨(arenaReady_lc cpost_d _ _).2 hAp_d,
                   (evmInvAt_lc cpost_d _ _ S).2 hInv_cd,
                   ((evmChain_lc cpost_d _ _).trans hch_cd).trans (hch_jp.trans hch_s1),
                   ((evmR_lc cpost_d _ _).trans hR_cd).trans (hR_jp.trans hR_s1)⟩
      · simp at hrun
    | _ => simp at hrun

theorem jset_ts64_step {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    {tw keyw valw : BitVec 64} {rv : ValueHOL 64}
    (hcode : s.code = originalRuntimeCode)
    (hAs : ArenaReady s) (hInv : EvmInvAt s S)
    (ht : s.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hkey : s.locals.lookup (ofString "key") = some (.val (.word keyw)))
    (hval : s.locals.lookup (ofString "value") = some (.val (.word valw)))
    (hts_nz : globN s "ts" ≠ 0)
    (htw_ts64 : tw.toNat = memW s (globN s "ts" + 64))
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_jset)).1 =
      some (.returned rv)) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_jset)).2
    ArenaReady post ∧ EvmInvAt post S ∧
    evmChain post = evmChain s ∧ evmR post = evmR s := by
  dsimp only
  have hbody : sourceFnBody Guest.Software.guestFn_jset =
      .decCall (ofString "old") (.comb [.one, .one]) (ofString "htab_get")
        [.var .local (ofString "t"), .var .local (ofString "key")]
        (.seq
          (.ite (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap")))
            (.call (some (none, none)) (ofString "trap_with") [.const 4])
            .skip)
          (jrecordPushTailProg (.rfield 0 (.var .local (ofString "old")))
            (.seq
              (.call (some (none, none)) (ofString "htab_set")
                [.var .local (ofString "t"), .var .local (ofString "key"), .var .local (ofString "value")])
              (.return (.const 0))))) := rfl
  rcases hrun : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_jset) with ⟨res, post⟩
  rw [hrun] at hret; dsimp only at hret ⊢
  subst hret
  rw [hbody, evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun
  have hargs_get : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "t"), .var .local (ofString "key")] =
      some [.val (.word tw), .val (.word keyw)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, evalHOLExact, ht, hkey]
  rw [hargs_get] at hrun; dsimp only at hrun
  rcases hl_get : lookupCodeHOLFinite s.code.lookup (ofString "htab_get")
      [.val (.word tw), .val (.word keyw)] with _ | ⟨body_get, cal_get, ret_get⟩
  · rw [hl_get] at hrun; simp at hrun
  rw [hl_get] at hrun; dsimp only at hrun
  by_cases hclk0 : s.clock = 0
  · simp [hclk0] at hrun
  rw [if_neg hclk0] at hrun
  have hbg_eq : body_get = sourceFnBody Guest.Software.guestFn_htab_get :=
    lookupCodeHOLFinite_installed_body s.code.lookup (ofString "htab_get") _ _ _ _ _
      [.val (.word tw), .val (.word keyw)] cal_get (by rw [hcode]; exact lookup_htab_get) hl_get
  subst hbg_eq
  have hrg_eq : ret_get = .comb [.one, .one] := by
    have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
      s.code.lookup (ofString "htab_get") [.val (.word tw), .val (.word keyw)] _ cal_get ret_get hl_get
    rw [hcode] at hx; simp only [Flapjack.lookupCodeHOLExact, lookup_htab_get] at hx
    split at hx
    · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
    · cases hx
  subst hrg_eq
  let ce_get := callEntryStateHOLFinite s cal_get
  have hlf_get : Wave8Contracts.M15.LocFrame ce_get
      (evaluateHOLFiniteState ce_get (sourceFnBody Guest.Software.guestFn_htab_get)).2 :=
    Wave8Contracts.M15.evaluate_readOnlyProg htabGetCallees htabGetCallees_good
      (sourceFnBody Guest.Software.guestFn_htab_get) (by decide) ce_get hcode
  rcases hrun_get : evaluateHOLFiniteState (callEntryStateHOLFinite s cal_get)
      (sourceFnBody Guest.Software.guestFn_htab_get) with ⟨res_get, cpost_get⟩
  change evaluateHOLFiniteState ce_get _ = _ at hrun_get
  rw [show callEntryStateHOLFinite s cal_get = ce_get from rfl] at hrun
  rw [hrun_get] at hrun hlf_get; dsimp only at hrun hlf_get
  cases res_get with
  | none => simp at hrun
  | some rg0 =>
    cases rg0 with
    | returned oldv =>
      dsimp only at hrun
      split at hrun
      · rename_i hsh_both
        have hsh_old : shapeEqHOL (shapeOfHOLExact oldv) (.comb [.one, .one]) = true := by
          simp only [Bool.and_eq_true] at hsh_both; exact hsh_both.1
        obtain ⟨old0, old1, rfl⟩ := two_word_val_of_shape hsh_old
        have htw_nz : tw.toNat ≠ 0 := by
          intro htz
          have htw0 : tw = 0#64 := BitVec.eq_of_toNat_eq htz
          subst htw0
          exact htab_get_t_ne_zero hcode hAs hl_get hrun_get
        let s1 := setVarHOLFinite (ofString "old") (.rStruct [.val (.word old0), .val (.word old1)])
          { cpost_get with locals := s.locals }
        have hs1_eq : s1 = { s with locals := s1.locals, clock := cpost_get.clock } := by
          dsimp only [s1]
          unfold Wave8Contracts.M15.LocFrame at hlf_get
          rw [hlf_get]; rfl
        have hcode_s1 : s1.code = originalRuntimeCode := by rw [hs1_eq]; exact hcode
        have hA_s1 : ArenaReady s1 := by rw [hs1_eq]; exact (arenaReady_lc s _ _).2 hAs
        have hInv_s1 : EvmInvAt s1 S := by rw [hs1_eq]; exact (evmInvAt_lc s _ _ S).2 hInv
        have hold_s1 : s1.locals.lookup (ofString "old") =
            some (.rStruct [.val (.word old0), .val (.word old1)]) := by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have ht_s1 : s1.locals.lookup (ofString "t") = some (.val (.word tw)) := by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "old" ≠ ofString "t" by decide, ht]
        have hkey_s1 : s1.locals.lookup (ofString "key") = some (.val (.word keyw)) := by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "old" ≠ ofString "key" by decide, hkey]
        have hval_s1 : s1.locals.lookup (ofString "value") = some (.val (.word valw)) := by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "old" ≠ ofString "value" by decide, hval]
        have hs1_def : setVarHOLFinite (ofString "old")
            (.rStruct [.val (.word old0), .val (.word old1)])
            { cpost_get with locals := s.locals } = s1 := rfl
        rw [hs1_def] at hrun
        rcases hs1_run : s1.evaluateHOLFiniteState
            (.seq
              (.ite (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap")))
                (.call (some (none, none)) (ofString "trap_with") [.const 4])
                .skip)
              (jrecordPushTailProg (.rfield 0 (.var .local (ofString "old")))
                (.seq
                  (.call (some (none, none)) (ofString "htab_set")
                    [.var .local (ofString "t"), .var .local (ofString "key"), .var .local (ofString "value")])
                  (.return (.const 0))))) with ⟨rs1_res, ms1⟩
        rw [hs1_run] at hrun; dsimp only at hrun
        injection hrun with hrs1 hpost_ms1
        subst hrs1
        have hpost_ms1' : post = { ms1 with locals := post.locals } := by rw [← hpost_ms1]
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hs1_run
        obtain ⟨jnw, hjn_lk⟩ := hA_s1.2.2.2.2.2.2.2.2.2 "journal_n" (by decide)
        obtain ⟨jcw, hjc_lk⟩ := hA_s1.2.2.2.2.2.2.2.2.2 "journal_cap" (by decide)
        have hjn_nat : jnw.toNat = globN s1 "journal_n" := by
          unfold GlobalWord at hjn_lk; simp [globN, hjn_lk]
        have hjc_nat : jcw.toNat = globN s1 "journal_cap" := by
          unfold GlobalWord at hjc_lk; simp [globN, hjc_lk]
        have hjn_lk' : s1.globals.lookup (ofString "journal_n") = some (.val (.word jnw)) := hjn_lk
        have hjc_lk' : s1.globals.lookup (ofString "journal_cap") = some (.val (.word jcw)) := hjc_lk
        by_cases hjn_ge : globN s1 "journal_cap" ≤ globN s1 "journal_n"
        · have hnl : Compiler.Encoders.Asm.wordCmpHOL .notLower jnw jcw = true := by
            simp only [Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
            have hnotlt : ¬ (jnw.toNat < jcw.toNat) := by omega
            simp [hnotlt]
          have hcmp_jn : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
              (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap"))) =
              some (.val (.word 1#64)) := by
            simp [evalHOLExact, hjn_lk', hjc_lk', hnl]
          rw [hcmp_jn] at hs1_run; dsimp only at hs1_run
          have h1_nz : (1#64 : BitVec 64) ≠ 0 := by decide
          rw [if_neg h1_nz] at hs1_run
          obtain ⟨_, htr_none, _⟩ := seq_call0_ret_inv (by rw [evaluateHOLFiniteState_seq_line780]; exact hs1_run)
          exact absurd (congrArg Prod.fst htr_none) (trap_with_call_not_none s1 hcode_s1 4)
        · have hjn_lt_s1 : globN s1 "journal_n" < globN s1 "journal_cap" := by omega
          have hnl : Compiler.Encoders.Asm.wordCmpHOL .notLower jnw jcw = false := by
            simp only [Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
            have hlt : jnw.toNat < jcw.toNat := by omega
            simp [hlt]
          have hcmp_jn : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
              (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap"))) =
              some (.val (.word 0#64)) := by
            simp [evalHOLExact, hjn_lk', hjc_lk', hnl]
          have h0_eq : (0#64 : BitVec 64) = 0 := rfl
          rw [hcmp_jn] at hs1_run; dsimp only at hs1_run
          rw [if_pos h0_eq, evaluateHOLFiniteState_skip] at hs1_run; dsimp only at hs1_run
          have hts_s1 : globN s1 "ts" = globN s "ts" := by rw [hs1_eq]; rfl
          have hts64_s1 : memW s1 (globN s1 "ts" + 64) = memW s (globN s "ts" + 64) := by
            rw [hs1_eq]; rfl
          obtain ⟨s_jp, tailPost, hcode_jp, hA_jp, hInv_jp, hch_jp, hR_jp, _, _, _, hts_jp, hts64_jp,
            hloc_jp, htail_run, hmtail_tp⟩ :=
            jrecord_push_tail_step (presw := old0) hcode_s1 hA_s1 hInv_s1 ht_s1 hkey_s1 hold_s1
              (fun st hst_old => by simp [evalHOLExact, hst_old]) hjn_lt_s1 (by rwa [hts_s1])
              (by rw [hts64_s1]; exact htw_ts64) htw_nz hs1_run
          obtain ⟨s_set, hcall_set, hret_run⟩ := seq_call0_ret_inv htail_run
          obtain ⟨vals_s, body_s, cal_s, ret_s, rvs, cpost_s, hargs_s, hl_s, hrun_s, hsset_eq⟩ :=
            Wave8M19.Htab.call0_flow s_jp _ _ (Or.inl (congrArg Prod.fst hcall_set))
          have hlk_set : originalRuntimeCode.lookup (ofString "htab_set") =
              some ([(ofString "t", .one), (ofString "key", .one), (ofString "value", .one)],
                sourceFnBody Guest.Software.guestFn_htab_set, .one) :=
            lookup_of_guestAst_getElem 138 (by rw [guestAst_len]; decide)
              (extractFn Guest.Software.guestFn_htab_set) rfl
          have hrs_eq : ret_s = .one := by
            have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
              s_jp.code.lookup (ofString "htab_set") vals_s _ cal_s ret_s hl_s
            rw [hcode_jp] at hx; simp only [Flapjack.lookupCodeHOLExact, hlk_set] at hx
            split at hx
            · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
            · cases hx
          subst hrs_eq
          have hbs_eq : body_s = sourceFnBody Guest.Software.guestFn_htab_set :=
            lookupCodeHOLFinite_installed_body s_jp.code.lookup (ofString "htab_set") _ _ _ _ _ vals_s cal_s
              (by rw [hcode_jp]; exact hlk_set) hl_s
          subst hbs_eq
          have ht_jp : s_jp.locals.lookup (ofString "t") = some (.val (.word tw)) := by
            rw [hloc_jp (ofString "t") (by decide) (by decide) (by decide)]; exact ht_s1
          have hkey_jp : s_jp.locals.lookup (ofString "key") = some (.val (.word keyw)) := by
            rw [hloc_jp (ofString "key") (by decide) (by decide) (by decide)]; exact hkey_s1
          have hval_jp : s_jp.locals.lookup (ofString "value") = some (.val (.word valw)) := by
            rw [hloc_jp (ofString "value") (by decide) (by decide) (by decide)]; exact hval_s1
          have hvals_eq : vals_s = [.val (.word tw), .val (.word keyw), .val (.word valw)] := by
            rw [evalListHOLFinite_eq_toExact] at hargs_s
            simp [evalListHOLExact, evalHOLExact, ht_jp, hkey_jp, hval_jp] at hargs_s
            exact hargs_s.symm
          subst hvals_eq
          have hex_lk := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
            s_jp.code.lookup (ofString "htab_set")
            [.val (.word tw), .val (.word keyw), .val (.word valw)] _ cal_s .one hl_s
          unfold lookupCodeHOLExact at hex_lk; rw [hcode_jp, hlk_set] at hex_lk; dsimp only at hex_lk
          split at hex_lk
          · have hmap_eq := congrArg (fun x => x.2.1) (Option.some.inj hex_lk)
            have hcal_t : cal_s.lookup (ofString "t") = some (.val (.word tw)) := by
              have := congrFun hmap_eq.symm (ofString "t")
              simpa [List.map, List.zip, List.foldl,
                show ofString "t" ≠ ofString "value" by decide,
                show ofString "t" ≠ ofString "key" by decide] using this
            have hcal_k : cal_s.lookup (ofString "key") = some (.val (.word keyw)) := by
              have := congrFun hmap_eq.symm (ofString "key")
              simpa [List.map, List.zip, List.foldl,
                show ofString "key" ≠ ofString "value" by decide] using this
            have hcal_v : cal_s.lookup (ofString "value") = some (.val (.word valw)) := by
              have := congrFun hmap_eq.symm (ofString "value")
              simpa [List.map, List.zip, List.foldl] using this
            let entry_s := callEntryStateHOLFinite s_jp cal_s
            have hloc_ts : locN entry_s "t" = tw.toNat := by
              simp [entry_s, callEntryStateHOLFinite, locN, hcal_t]
            have hts_jp' : globN s_jp "ts" = globN s "ts" := hts_jp.trans hts_s1
            have hts64_jp' : memW s_jp (globN s_jp "ts" + 64) = tw.toNat := by
              rw [hts_jp', ← hts_s1, hts64_jp, hts64_s1, htw_ts64]
            obtain ⟨ht0_S_jp, _, _, _, ht0_ndel_jp, ht0_nws32_jp, ht0_nbs32_jp, ht0_nba_jp, ht0_nad_jp, ht0_nts32_jp⟩ :=
              ts64_role_props hInv_jp (by rwa [hts_jp']) (by rw [hts64_jp']; exact htw_nz)
            rw [hts64_jp'] at ht0_S_jp ht0_ndel_jp ht0_nws32_jp ht0_nbs32_jp ht0_nba_jp ht0_nad_jp ht0_nts32_jp
            have hArg_s : HtabArgWF entry_s := by
              refine ⟨⟨guestInv_congr (s := s_jp) rfl rfl rfl rfl hA_jp.1, hA_jp.2⟩, ?_, ?_⟩
              · rw [hloc_ts]
                exact (htabWF_lc s_jp entry_s.locals s_jp.globals entry_s.clock _).mpr
                  (hInv_jp.1.1.2.1 _ ht0_S_jp).1
              · rw [hloc_ts]
                intro i hi
                exact ((hInv_jp.1.1.2.1 _ ht0_S_jp).2 i hi).1
            have hset_sub := htab_set_values_sub entry_s tw keyw valw hcal_t hcal_k hcal_v hArg_s rvs (by rw [hrun_s])
            have hcpost_eq : (evaluateHOLFiniteState entry_s (sourceFnBody Guest.Software.guestFn_htab_set)).2 = cpost_s := by
              rw [hrun_s]
            rw [hcpost_eq, hloc_ts] at hset_sub
            obtain ⟨hexit_s, hbe_s, _⟩ := hset_sub
            unfold HtabExit at hexit_s; dsimp only at hexit_s
            rw [hloc_ts] at hexit_s
            obtain ⟨hAp_s, hwf_s, hhdr0_s, _, hhp_s, hfp_s, hfr_s, hg_s⟩ := hexit_s
            obtain ⟨hInv_cs, hch_cs, hR_cs, _⟩ := evmInvAt_of_htab_step
              hA_jp hInv_jp hAp_s hbe_s hwf_s hhdr0_s hhp_s hfp_s hfr_s
              (fun k hk => by
                have hk_hp : k ≠ ofString "heap_ptr" := fun h => hk (by simp [h])
                exact hg_s k (by simp [hk_hp]))
              (by
                have hjn_entry : globN entry_s "journal_n" = globN s_jp "journal_n" := rfl
                have hjn_cs : globN cpost_s "journal_n" = globN s_jp "journal_n" :=
                  (globN_eq_of_lookup_eq (hg_s (ofString "journal_n") (by decide)).symm).trans hjn_entry
                omega)
              ht0_S_jp ht0_ndel_jp ht0_nws32_jp ht0_nbs32_jp ht0_nba_jp ht0_nad_jp
              (Or.inl ht0_nts32_jp)
            have hsset_cs : s_set = { cpost_s with locals := s_jp.locals } :=
              (Prod.mk.inj (hcall_set.symm.trans hsset_eq)).2
            rw [evaluateHOLFiniteState_return] at hret_run
            simp [evalHOLExact, shapeOfHOLExact] at hret_run
            obtain ⟨_, hret_sset⟩ := hret_run
            have hp_cs : post = { cpost_s with locals := post.locals, clock := cpost_s.clock } := by
              rw [hpost_ms1', hmtail_tp, ← hret_sset, hsset_cs]
              cases cpost_s; rfl
            rw [hp_cs]
            have hch_s1 : evmChain s1 = evmChain s := by rw [hs1_eq]; exact evmChain_lc s _ _
            have hR_s1 : evmR s1 = evmR s := by rw [hs1_eq]; exact evmR_lc s _ _
            exact ⟨(arenaReady_lc cpost_s _ _).2 hAp_s,
                   (evmInvAt_lc cpost_s _ _ S).2 hInv_cs,
                   ((evmChain_lc cpost_s _ _).trans hch_cs).trans (hch_jp.trans hch_s1),
                   ((evmR_lc cpost_s _ _).trans hR_cs).trans (hR_jp.trans hR_s1)⟩
          · cases hex_lk
      · simp at hrun
    | _ => simp at hrun

/-! ## 7. 4-word struct store frame & `eps_set_transient_storage` -/

theorem four_word_val_of_shape {v : ValueHOL 64} :
    shapeEqHOL (shapeOfHOLExact v) (.comb [.one, .one, .one, .one]) = true →
    ∃ w0 w1 w2 w3 : BitVec 64,
      v = .rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)] := by
  rcases v with _ | fs | _
  · simp [shapeOfHOLExact, shapeEqHOL]
  · rcases fs with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, _ | ⟨f3, _ | _⟩⟩⟩⟩
    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
    · simp only [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL, List.map, Bool.and_eq_true, Bool.and_true]
      rintro ⟨h0, h1, h2, h3⟩
      rcases f0 with ⟨⟨w0⟩⟩ | _ | _ <;> try simp [shapeOfHOLExact, shapeEqHOL] at h0
      rcases f1 with ⟨⟨w1⟩⟩ | _ | _ <;> try simp [shapeOfHOLExact, shapeEqHOL] at h1
      rcases f2 with ⟨⟨w2⟩⟩ | _ | _ <;> try simp [shapeOfHOLExact, shapeEqHOL] at h2
      rcases f3 with ⟨⟨w3⟩⟩ | _ | _ <;> try simp [shapeOfHOLExact, shapeEqHOL] at h3
      exact ⟨w0, w1, w2, w3, rfl⟩
    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
  · simp [shapeOfHOLExact, shapeEqHOL]

theorem byteRegionEffect_of_store_struct4 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {dst val : ExpHOL 64}
    {addr w0 w1 w2 w3 : BitVec 64}
    (hma_ord : s.memaddrs = ordinaryDomain)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst =
      some (.val (.word addr)))
    (hval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val =
      some (.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]))
    (hbound : addr.toNat + 32 ≤ 2 ^ 64)
    (hrun : evaluateHOLFiniteState s (.store dst val) = (none, post)) :
    ByteRegionEffect s post [(addr.toNat, 32)] ∧ post.locals = s.locals := by
  rw [evaluateHOLFiniteState_store] at hrun
  rw [hdst, hval] at hrun
  dsimp only at hrun
  revert hrun
  split
  · rename_i m' hst
    have hbw : panBytesInWord 64 = 8#64 := rfl
    have hfl4 : flattenHOL (.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]) =
        [.word w0, .word w1, .word w2, .word w3] := by
      simp [flattenHOL]
    rw [hfl4] at hst
    simp only [panMemStoresHOL, panMemStoreHOL] at hst
    rw [hbw] at hst
    by_cases hd0 : s.memaddrs addr
    · simp only [hd0, ↓reduceIte] at hst
      by_cases hd1 : s.memaddrs (addr + 8#64)
      · simp only [hd1, ↓reduceIte] at hst
        by_cases hd2 : s.memaddrs (addr + 8#64 + 8#64)
        · simp only [hd2, ↓reduceIte] at hst
          by_cases hd3 : s.memaddrs (addr + 8#64 + 8#64 + 8#64)
          · simp only [hd3, ↓reduceIte, Option.some.injEq] at hst
            subst hst
            intro hrun
            injection hrun with _ hpost
            subst hpost
            have ha8 : addr.toNat % 8 = 0 := by
              have hd' := hma_ord ▸ hd0
              rw [ordinaryDomain_iff] at hd'; exact hd'.2.2
            have htn1 : (addr + 8#64).toNat = addr.toNat + 8 := by
              rw [BitVec.toNat_add, show (8#64 : BitVec 64).toNat = 8 from rfl,
                Nat.mod_eq_of_lt (by omega)]
            have htn2 : (addr + 8#64 + 8#64).toNat = addr.toNat + 16 := by
              rw [BitVec.toNat_add, htn1, show (8#64 : BitVec 64).toNat = 8 from rfl,
                Nat.mod_eq_of_lt (by omega)]
            have htn3 : (addr + 8#64 + 8#64 + 8#64).toNat = addr.toNat + 24 := by
              rw [BitVec.toNat_add, htn2, show (8#64 : BitVec 64).toNat = 8 from rfl,
                Nat.mod_eq_of_lt (by omega)]
            refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩, rfl⟩
            · intro a hna
              dsimp only
              have hne3 : a ≠ addr + 8#64 + 8#64 + 8#64 := by rintro rfl; exact hna hd3
              have hne2 : a ≠ addr + 8#64 + 8#64 := by rintro rfl; exact hna hd2
              have hne1 : a ≠ addr + 8#64 := by rintro rfl; exact hna hd1
              have hne0 : a ≠ addr := by rintro rfl; exact hna hd0
              rw [if_neg hne3, if_neg hne2, if_neg hne1, if_neg hne0]
            · intro a hna
              dsimp only
              have hnh : ¬ CellHits a.toNat (addr.toNat, 32) := hna (addr.toNat, 32) (by simp)
              dsimp [CellHits] at hnh
              have hne3 : a ≠ addr + 8#64 + 8#64 + 8#64 := by rintro rfl; omega
              have hne2 : a ≠ addr + 8#64 + 8#64 := by rintro rfl; omega
              have hne1 : a ≠ addr + 8#64 := by rintro rfl; omega
              have hne0 : a ≠ addr := by rintro rfl; omega
              rw [if_neg hne3, if_neg hne2, if_neg hne1, if_neg hne0]
            · intro b hb hno
              unfold memB
              dsimp only
              have hni : ¬ InIvl b (addr.toNat, 32) := hno (addr.toNat, 32) (by simp)
              dsimp [InIvl] at hni
              have hal_b : (panByteAlignHOL (BitVec.ofNat 64 b)).toNat = b / 8 * 8 := by
                rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
              have hne3 : panByteAlignHOL (BitVec.ofNat 64 b) ≠ addr + 8#64 + 8#64 + 8#64 := by
                intro heq; rw [heq] at hal_b; omega
              have hne2 : panByteAlignHOL (BitVec.ofNat 64 b) ≠ addr + 8#64 + 8#64 := by
                intro heq; rw [heq] at hal_b; omega
              have hne1 : panByteAlignHOL (BitVec.ofNat 64 b) ≠ addr + 8#64 := by
                intro heq; rw [heq] at hal_b; omega
              have hne0 : panByteAlignHOL (BitVec.ofNat 64 b) ≠ addr := by
                intro heq; rw [heq] at hal_b; omega
              rw [if_neg hne3, if_neg hne2, if_neg hne1, if_neg hne0]
          · simp [hd3] at hst
        · simp [hd2] at hst
      · simp [hd1] at hst
    · simp [hd0] at hst
  · simp

theorem eps_set_transient_storage :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => evmR post = evmR s)
      (ofString "set_transient_storage") := by
  refine ⟨_, _, _, lookup_set_transient_storage, ?_⟩
  intro F s hcode hInv _ ⟨vals_in, hlk_in⟩ hnt
  have hno_evmErr : ¬ IsEvmErr
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_set_transient_storage)).1 := by
    have hnc := evaluate_noCatchableRaise transientMutCallees transientMutCallees_good
      (sourceFnBody Guest.Software.guestFn_set_transient_storage) (by decide) s hcode
    rintro ⟨ev, hev⟩
    exact hnc (ofString "EvmErr") ev (by decide) hev
  dsimp only
  refine ⟨?_, fun he => (hno_evmErr he).elim⟩
  intro rv hret
  -- Extract `s.locals.lookup "value"` = 4-word struct from `hlk_in`:
  have hval_struct : ∃ vw0 vw1 vw2 vw3 : BitVec 64,
      s.locals.lookup (ofString "value") =
        some (.rStruct [.val (.word vw0), .val (.word vw1), .val (.word vw2), .val (.word vw3)]) := by
    have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
      originalRuntimeCode.lookup (ofString "set_transient_storage") vals_in
      (sourceFnBody Guest.Software.guestFn_set_transient_storage) s.locals .one hlk_in
    simp only [Flapjack.lookupCodeHOLExact, lookup_set_transient_storage] at hx
    rcases vals_in with _ | ⟨va, _ | ⟨vk, _ | ⟨vv, _ | _⟩⟩⟩
    · simp at hx
    · simp at hx
    · simp at hx
    · split at hx
      · rename_i hcond
        have hmap_eq := congrArg (fun x => x.2.1) (Option.some.inj hx)
        have hlv : s.locals.lookup (ofString "value") = some vv := by
          have := congrFun hmap_eq.symm (ofString "value")
          simpa [List.map, List.zip, List.foldl] using this
        have hsh_vv : shapeEqHOL (shapeOfHOLExact vv) (.comb [.one, .one, .one, .one]) = true := by
          have h3 : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact vv) = true := by
            simp [List.zip, List.zipWith, List.all, Bool.and_eq_true] at hcond
            exact hcond.2.2.2
          rcases hsv : shapeOfHOLExact vv with _ | ds | _
          · simp [hsv, shapeEqHOL] at h3
          · rcases ds with _ | ⟨d0, _ | ⟨d1, _ | ⟨d2, _ | ⟨d3, _ | _⟩⟩⟩⟩ <;>
              simp [hsv, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h3 ⊢
            rcases d0 with _ | _ | _ <;> rcases d1 with _ | _ | _ <;>
            rcases d2 with _ | _ | _ <;> rcases d3 with _ | _ | _ <;>
            simp [shapeEqHOL] at h3 ⊢
          · simp [hsv, shapeEqHOL] at h3
        obtain ⟨vw0, vw1, vw2, vw3, rfl⟩ := four_word_val_of_shape hsh_vv
        exact ⟨vw0, vw1, vw2, vw3, hlv⟩
      · cases hx
    · simp at hx
  obtain ⟨vw0, vw1, vw2, vw3, hval_s⟩ := hval_struct
  have hbody : sourceFnBody Guest.Software.guestFn_set_transient_storage =
      .decCall (ofString "k") .one (ofString "sk_make")
        [.var .local (ofString "addr"), .var .local (ofString "key")]
        (.decCall (ofString "z") .one (ofString "u256_is_zero")
          [.var .local (ofString "value")]
          (.seq
            (.ite (.cmp .notEqual (.var .local (ofString "z")) (.const 0))
              (.seq
                (.call (some (none, none)) (ofString "jdel")
                  [.load .one (.op .add [.var .global (ofString "ts"), .const 64]),
                   .var .local (ofString "k")])
                (.return (.const 0)))
              .skip)
            (.decCall (ofString "v") .one (ofString "alloc") [.const 32]
              (.seq
                (.store (.var .local (ofString "v")) (.var .local (ofString "value")))
                (.seq
                  (.call (some (none, none)) (ofString "jset")
                    [.load .one (.op .add [.var .global (ofString "ts"), .const 64]),
                     .var .local (ofString "k"), .var .local (ofString "v")])
                  (.return (.const 0))))))) := rfl
  rcases hrun : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_set_transient_storage) with ⟨res, post⟩
  rw [hrun] at hret hnt; dsimp only at hret ⊢
  subst hret
  -- 1. Unpack `decCall "k" .one "sk_make" [addr, key]`:
  rw [hbody, evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun
  rcases hargs_sk : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "addr"), .var .local (ofString "key")] with _ | vals_sk
  · rw [hargs_sk] at hrun; simp at hrun
  rw [hargs_sk] at hrun; dsimp only at hrun
  rcases hl_sk : lookupCodeHOLFinite s.code.lookup (ofString "sk_make") vals_sk with _ | ⟨body_sk, cal_sk, ret_sk⟩
  · rw [hl_sk] at hrun; simp at hrun
  rw [hl_sk] at hrun; dsimp only at hrun
  by_cases hclk0 : s.clock = 0
  · simp [hclk0] at hrun
  rw [if_neg hclk0] at hrun
  obtain ⟨params_sk, body_sk0, ret_sk0, hlook_sk, hspec_sk⟩ := eps_sk_make
  have hbsk_eq : body_sk = body_sk0 :=
    lookupCodeHOLFinite_installed_body s.code.lookup (ofString "sk_make")
      params_sk body_sk0 body_sk ret_sk0 ret_sk vals_sk cal_sk (by rw [hcode]; exact hlook_sk) hl_sk
  have hrsk_eq : ret_sk = ret_sk0 := by
    have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
      s.code.lookup (ofString "sk_make") vals_sk body_sk cal_sk ret_sk hl_sk
    rw [hcode] at hx; simp only [Flapjack.lookupCodeHOLExact, hlook_sk] at hx
    split at hx
    · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
    · cases hx
  subst body_sk ret_sk
  have hl_sk_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "sk_make") vals_sk =
      some (body_sk0, cal_sk, ret_sk0) := by rwa [← hcode]
  let ce_sk := callEntryStateHOLFinite s cal_sk
  have hInv_cesk : EvmInv ce_sk := localsFree_evmInv s cal_sk (s.clock - 1) hInv
  have hmeta_sk := (PanRunBounded.evaluateHOLFiniteState_metadata ce_sk body_sk0).1
  rcases hrun_sk : evaluateHOLFiniteState (callEntryStateHOLFinite s cal_sk) body_sk0 with ⟨res_sk, cpost_sk⟩
  change evaluateHOLFiniteState ce_sk body_sk0 = _ at hrun_sk
  rw [show callEntryStateHOLFinite s cal_sk = ce_sk from rfl] at hrun
  rw [hrun_sk] at hrun hmeta_sk; dsimp only at hrun hmeta_sk
  cases res_sk with
  | none => simp at hrun
  | some rsk0 =>
    cases rsk0 with
    | returned kv =>
      dsimp only at hrun
      split at hrun
      · rename_i hsh_kv
        have hsh_kv1 : shapeEqHOL (shapeOfHOLExact kv) .one = true := by
          simp only [Bool.and_eq_true] at hsh_kv; exact hsh_kv.1
        have hkv_w : ∃ kw : BitVec 64, kv = .val (.word kw) := by
          rcases kv with ⟨⟨kw⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh_kv1
          exact ⟨kw, rfl⟩
        obtain ⟨kw, rfl⟩ := hkv_w
        have hs_sk := (hspec_sk ce_sk hcode hInv_cesk trivial ⟨vals_sk, hl_sk_orig⟩
          (by rw [hrun_sk]; simp)).1 (.val (.word kw)) (by rw [hrun_sk])
        dsimp only at hs_sk; rw [hrun_sk] at hs_sk
        obtain ⟨hInv_cpsk, hch_cpsk, _, _, hR_cpsk⟩ := hs_sk
        let s1 := setVarHOLFinite (ofString "k") (.val (.word kw)) { cpost_sk with locals := s.locals }
        have hcode_s1 : s1.code = originalRuntimeCode := hmeta_sk.trans hcode
        have hInv_s1 : EvmInv s1 := localsFree_evmInv cpost_sk s1.locals cpost_sk.clock hInv_cpsk
        have hch_s1 : evmChain s1 = evmChain s :=
          (evmChain_lc cpost_sk s1.locals cpost_sk.clock).trans (hch_cpsk.trans (evmChain_lc s cal_sk (s.clock - 1)))
        have hR_s1 : evmR s1 = evmR s :=
          (evmR_lc cpost_sk s1.locals cpost_sk.clock).trans (hR_cpsk.trans (evmR_lc s cal_sk (s.clock - 1)))
        have hk_s1 : s1.locals.lookup (ofString "k") = some (.val (.word kw)) := by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hval_s1 : s1.locals.lookup (ofString "value") =
            some (.rStruct [.val (.word vw0), .val (.word vw1), .val (.word vw2), .val (.word vw3)]) := by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "k" ≠ ofString "value" by decide, hval_s]
        have hs1_def : setVarHOLFinite (ofString "k") (.val (.word kw)) { cpost_sk with locals := s.locals } = s1 := rfl
        rw [hs1_def] at hrun
        -- 2. Unpack `decCall "z" .one "u256_is_zero" [value]`:
        rcases hs1_run : s1.evaluateHOLFiniteState
            (.decCall (ofString "z") .one (ofString "u256_is_zero")
              [.var .local (ofString "value")]
              (.seq
                (.ite (.cmp .notEqual (.var .local (ofString "z")) (.const 0))
                  (.seq
                    (.call (some (none, none)) (ofString "jdel")
                      [.load .one (.op .add [.var .global (ofString "ts"), .const 64]),
                       .var .local (ofString "k")])
                    (.return (.const 0)))
                  .skip)
                (.decCall (ofString "v") .one (ofString "alloc") [.const 32]
                  (.seq
                    (.store (.var .local (ofString "v")) (.var .local (ofString "value")))
                    (.seq
                      (.call (some (none, none)) (ofString "jset")
                        [.load .one (.op .add [.var .global (ofString "ts"), .const 64]),
                         .var .local (ofString "k"), .var .local (ofString "v")])
                      (.return (.const 0))))))) with ⟨rs1_res, ms1⟩
        rw [hs1_run] at hrun
        cases rs1_res with
        | none => simp at hrun
        | some rs1_0 =>
          cases rs1_0 with
          | returned rv1 =>
            dsimp only at hrun
            injection hrun with hr1 hpost_ms1
            injection hr1 with hr1'; injection hr1' with hrv1
            subst hrv1
            have hpost_ms1' : post = { ms1 with locals := post.locals } := by rw [← hpost_ms1]
            rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hs1_run
            have hargs_uz : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
                [.var .local (ofString "value")] =
                some [.rStruct [.val (.word vw0), .val (.word vw1), .val (.word vw2), .val (.word vw3)]] := by
              rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, evalHOLExact, hval_s1]
            rw [hargs_uz] at hs1_run; dsimp only at hs1_run
            rcases hl_uz : lookupCodeHOLFinite s1.code.lookup (ofString "u256_is_zero")
                [.rStruct [.val (.word vw0), .val (.word vw1), .val (.word vw2), .val (.word vw3)]] with
              _ | ⟨body_uz, cal_uz, ret_uz⟩
            · rw [hl_uz] at hs1_run; simp at hs1_run
            rw [hl_uz] at hs1_run; dsimp only at hs1_run
            by_cases hclk1 : s1.clock = 0
            · simp [hclk1] at hs1_run
            rw [if_neg hclk1] at hs1_run
            have hlk_uz : originalRuntimeCode.lookup (ofString "u256_is_zero") =
                some ([(ofString "a", .comb [.one, .one, .one, .one])],
                  sourceFnBody Guest.Software.guestFn_u256_is_zero, .one) :=
              lookup_of_guestAst_getElem 42 (by rw [guestAst_len]; decide)
                (extractFn Guest.Software.guestFn_u256_is_zero) rfl
            have hbuz_eq : body_uz = sourceFnBody Guest.Software.guestFn_u256_is_zero :=
              lookupCodeHOLFinite_installed_body s1.code.lookup (ofString "u256_is_zero") _ _ _ _ _ _ cal_uz
                (by rw [hcode_s1]; exact hlk_uz) hl_uz
            subst hbuz_eq
            have hruz_eq : ret_uz = .one := by
              have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
                s1.code.lookup (ofString "u256_is_zero") _ _ cal_uz ret_uz hl_uz
              rw [hcode_s1] at hx; simp only [Flapjack.lookupCodeHOLExact, hlk_uz] at hx
              split at hx
              · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
              · cases hx
            subst hruz_eq
            let ce_uz := callEntryStateHOLFinite s1 cal_uz
            have hlf_uz : Wave8Contracts.M15.LocFrame ce_uz
                (evaluateHOLFiniteState ce_uz (sourceFnBody Guest.Software.guestFn_u256_is_zero)).2 :=
              Wave8Contracts.M15.evaluate_readOnlyProg (fun _ => false) (fun _ h => by cases h)
                (sourceFnBody Guest.Software.guestFn_u256_is_zero) (by decide) ce_uz hcode_s1
            rcases hrun_uz : evaluateHOLFiniteState (callEntryStateHOLFinite s1 cal_uz)
                (sourceFnBody Guest.Software.guestFn_u256_is_zero) with ⟨res_uz, cpost_uz⟩
            change evaluateHOLFiniteState ce_uz _ = _ at hrun_uz
            rw [show callEntryStateHOLFinite s1 cal_uz = ce_uz from rfl] at hs1_run
            rw [hrun_uz] at hs1_run hlf_uz; dsimp only at hs1_run hlf_uz
            cases res_uz with
            | none => simp at hs1_run
            | some ruz0 =>
              cases ruz0 with
              | returned zv =>
                dsimp only at hs1_run
                split at hs1_run
                · rename_i hsh_zv
                  have hsh_zv1 : shapeEqHOL (shapeOfHOLExact zv) .one = true := by
                    simp only [Bool.and_eq_true] at hsh_zv; exact hsh_zv.1
                  have hzv_w : ∃ zw : BitVec 64, zv = .val (.word zw) := by
                    rcases zv with ⟨⟨zw⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh_zv1
                    exact ⟨zw, rfl⟩
                  obtain ⟨zw, rfl⟩ := hzv_w
                  let s2 := setVarHOLFinite (ofString "z") (.val (.word zw)) { cpost_uz with locals := s1.locals }
                  have hs2_eq : s2 = { s1 with locals := s2.locals, clock := cpost_uz.clock } := by
                    dsimp only [s2]; unfold Wave8Contracts.M15.LocFrame at hlf_uz; rw [hlf_uz]; rfl
                  have hcode_s2 : s2.code = originalRuntimeCode := by rw [hs2_eq]; exact hcode_s1
                  have hInv_s2 : EvmInv s2 := by rw [hs2_eq]; exact localsFree_evmInv s1 _ _ hInv_s1
                  obtain ⟨hA_s2, S_s2, hInvAt_s2⟩ := hInv_s2
                  have hch_s2 : evmChain s2 = evmChain s := by
                    rw [hs2_eq]; exact (evmChain_lc s1 _ _).trans hch_s1
                  have hR_s2 : evmR s2 = evmR s := by
                    rw [hs2_eq]; exact (evmR_lc s1 _ _).trans hR_s1
                  have hz_s2 : s2.locals.lookup (ofString "z") = some (.val (.word zw)) := by
                    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  have hk_s2 : s2.locals.lookup (ofString "k") = some (.val (.word kw)) := by
                    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                      show ofString "z" ≠ ofString "k" by decide, hk_s1]
                  have hval_s2 : s2.locals.lookup (ofString "value") =
                      some (.rStruct [.val (.word vw0), .val (.word vw1), .val (.word vw2), .val (.word vw3)]) := by
                    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                      show ofString "z" ≠ ofString "value" by decide, hval_s1]
                  have hs2_def : setVarHOLFinite (ofString "z") (.val (.word zw)) { cpost_uz with locals := s1.locals } = s2 := rfl
                  rw [hs2_def] at hs1_run
                  rcases hs2_run : s2.evaluateHOLFiniteState
                      (.seq
                        (.ite (.cmp .notEqual (.var .local (ofString "z")) (.const 0))
                          (.seq
                            (.call (some (none, none)) (ofString "jdel")
                              [.load .one (.op .add [.var .global (ofString "ts"), .const 64]),
                               .var .local (ofString "k")])
                            (.return (.const 0)))
                          .skip)
                        (.decCall (ofString "v") .one (ofString "alloc") [.const 32]
                          (.seq
                            (.store (.var .local (ofString "v")) (.var .local (ofString "value")))
                            (.seq
                              (.call (some (none, none)) (ofString "jset")
                                [.load .one (.op .add [.var .global (ofString "ts"), .const 64]),
                                 .var .local (ofString "k"), .var .local (ofString "v")])
                              (.return (.const 0)))))) with ⟨rs2_res, ms2⟩
                  rw [hs2_run] at hs1_run
                  cases rs2_res with
                  | none => simp at hs1_run
                  | some rs2_0 =>
                    cases rs2_0 with
                    | returned rv2 =>
                      dsimp only at hs1_run
                      injection hs1_run with hr2 hms1_ms2
                      injection hr2 with hr2'; injection hr2' with hrv2
                      subst hrv2
                      have hpost_ms2 : post = { ms2 with locals := post.locals } := by
                        rw [hpost_ms1', ← hms1_ms2]
                      -- Helper for evaluating `load .one (ts + 64)` on any `ArenaReady` state `st`:
                      have hload_ts64_inv : ∀ (st : PanSemStateFiniteExact 64 F) (tv : ValueHOL 64),
                          ArenaReady st →
                          @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
                            (.load .one (.op .add [.var .global (ofString "ts"), .const 64])) = some tv →
                          ∃ tw : BitVec 64, tv = .val (.word tw) ∧ globN st "ts" ≠ 0 ∧
                            tw.toNat = memW st (globN st "ts" + 64) := by
                        intro st tv hAst hev
                        obtain ⟨tsw, hts_lk⟩ := hAst.2.2.2.2.2.2.2.2.2 "ts" (by decide)
                        have hts_lk' : st.globals.lookup (ofString "ts") = some (.val (.word tsw)) := hts_lk
                        have hts_nat : tsw.toNat = globN st "ts" := by
                          unfold GlobalWord at hts_lk; simp [globN, hts_lk]
                        have hwf1 : isWfShapeExactHOL st.structs ShapeHOL.one = true := rfl
                        simp [evalHOLExact, evalListHOLExact, hts_lk',
                          valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact, hwf1] at hev
                        obtain ⟨hdom, htv_eq⟩ := hev
                        rcases hm_cell : st.memory (tsw + 64#64) with ⟨tw⟩
                        rw [hm_cell] at htv_eq
                        have hdom_ord : ordinaryDomain (tsw + 64#64) := hAst.1.memaddrs ▸ hdom
                        rw [ordinaryDomain_iff] at hdom_ord
                        have hts_nz : globN st "ts" ≠ 0 := by
                          intro hz
                          have hts0 : tsw = 0#64 := BitVec.eq_of_toNat_eq (hts_nat.trans hz)
                          subst hts0
                          have h64 : (0#64 + 64#64 : BitVec 64).toNat = 64 := rfl
                          omega
                        have haddr_eq : tsw + 64#64 = BitVec.ofNat 64 (globN st "ts" + 64) := by
                          apply BitVec.eq_of_toNat_eq
                          rw [BitVec.toNat_add, hts_nat, show (64#64 : BitVec 64).toNat = 64 from rfl,
                            BitVec.toNat_ofNat]
                        have htw_mem : tw.toNat = memW st (globN st "ts" + 64) := by
                          unfold memW; rw [← haddr_eq, hm_cell]
                        exact ⟨tw, htv_eq.symm, hts_nz, htw_mem⟩
                      -- 3. Branch on `zw != 0`:
                      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hs2_run
                      by_cases hzw0 : zw = 0#64
                      · -- `zw == 0`: skip `jdel`, run `alloc(32); store v value; call jset; return 0`
                        subst hzw0
                        have hcmp_z : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
                            (.cmp .notEqual (.var .local (ofString "z")) (.const 0)) =
                            some (.val (.word 0#64)) := by
                          simp [evalHOLExact, hz_s2, Compiler.Encoders.Asm.wordCmpHOL]
                        have h0_eq : (0#64 : BitVec 64) = 0 := rfl
                        rw [hcmp_z] at hs2_run; dsimp only at hs2_run
                        rw [if_pos h0_eq, evaluateHOLFiniteState_skip] at hs2_run; dsimp only at hs2_run
                        -- Unpack `decCall "v" .one "alloc" [32]`:
                        rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hs2_run
                        have hargs_al : evalListHOLFinite s2 (h := fun a => Classical.propDecidable (s2.memaddrs a))
                            [.const 32] = some [.val (.word 32#64)] := by
                          rw [evalListHOLFinite_eq_toExact]; rfl
                        rw [hargs_al] at hs2_run; dsimp only at hs2_run
                        have hl_al := pan_one_word_lookup s2.code.lookup (ofString "alloc") (ofString "n")
                          (sourceFnBody Guest.Software.guestFn_alloc) 32#64
                          (by rw [hcode_s2]; exact lookup_alloc_r13)
                        rw [hl_al] at hs2_run; dsimp only at hs2_run
                        by_cases hclk2 : s2.clock = 0
                        · simp [hclk2] at hs2_run
                        rw [if_neg hclk2] at hs2_run
                        let ce_al := callEntryStateHOLFinite s2
                          (HolFiniteMapExact.empty.update (ofString "n", .val (.word 32#64)))
                        have hcode_al : ce_al.code = originalRuntimeCode := hcode_s2
                        have hA_al : ArenaReady ce_al :=
                          ⟨guestInv_congr (s := s2) rfl rfl rfl rfl hA_s2.1, hA_s2.2⟩
                        have hmeta_al := (PanRunBounded.evaluateHOLFiniteState_metadata ce_al
                          (sourceFnBody Guest.Software.guestFn_alloc)).1
                        rcases hrun_al : evaluateHOLFiniteState (callEntryStateHOLFinite s2
                            (HolFiniteMapExact.empty.update (ofString "n", .val (.word 32#64))))
                            (sourceFnBody Guest.Software.guestFn_alloc) with ⟨res_al, cpost_al⟩
                        change evaluateHOLFiniteState ce_al _ = _ at hrun_al
                        rw [show callEntryStateHOLFinite s2
                            (HolFiniteMapExact.empty.update (ofString "n", .val (.word 32#64))) = ce_al from rfl] at hs2_run
                        rw [hrun_al] at hs2_run hmeta_al; dsimp only at hs2_run hmeta_al
                        have hres_al : Wave8Contracts.M12.Resumes
                            (evaluateHOLFiniteState ce_al (sourceFnBody Guest.Software.guestFn_alloc)).1 := by
                          rw [hrun_al]
                          cases res_al with
                          | none => simp at hs2_run
                          | some ral0 =>
                            cases ral0 with
                            | returned v => exact Or.inl ⟨v, rfl⟩
                            | _ => simp at hs2_run
                        obtain ⟨vw, qw, hret_al, hv_nat, hq_nat, hq_lim, hq_8, hvw_le_q, hg_al, hm_al, hbe_al,
                          hma_al, hA_cpal, hhp_cpal, _⟩ := alloc_body_resumes_props ce_al hcode_al hA_al hres_al
                        rw [hrun_al] at hret_al hg_al hm_al hbe_al hma_al hA_cpal hhp_cpal
                        dsimp only at hret_al hg_al hm_al hbe_al hma_al hA_cpal hhp_cpal
                        rw [hret_al] at hs2_run
                        dsimp only at hs2_run
                        have hsh_vw : (shapeEqHOL (shapeOfHOLExact (.val (.word vw) : ValueHOL 64)) .one &&
                            shapeEqHOL (shapeOfHOLExact (.val (.word vw) : ValueHOL 64)) .one) = true := by
                          simp [shapeOfHOLExact, shapeEqHOL]
                        rw [if_pos hsh_vw] at hs2_run
                        have hloc_n_al : locN ce_al "n" = 32 := by
                          simp [ce_al, callEntryStateHOLFinite, locN, HolFiniteMapExact.lookup_update, FUPDATE]
                        rw [hloc_n_al] at hq_nat
                        have hhp_ce_s2 : globN ce_al "heap_ptr" = globN s2 "heap_ptr" := rfl
                        rw [hhp_ce_s2] at hv_nat
                        let s3 := setVarHOLFinite (ofString "v") (.val (.word vw)) { cpost_al with locals := s2.locals }
                        have hs3_def : setVarHOLFinite (ofString "v") (.val (.word vw)) { cpost_al with locals := s2.locals } = s3 := rfl
                        rw [hs3_def] at hs2_run
                        rcases hs3_run : s3.evaluateHOLFiniteState
                            (.seq
                              (.store (.var .local (ofString "v")) (.var .local (ofString "value")))
                              (.seq
                                (.call (some (none, none)) (ofString "jset")
                                  [.load .one (.op .add [.var .global (ofString "ts"), .const 64]),
                                   .var .local (ofString "k"), .var .local (ofString "v")])
                                (.return (.const 0)))) with ⟨rs3_res, ms3⟩
                        rw [hs3_run] at hs2_run
                        cases rs3_res with
                        | none => simp at hs2_run
                        | some rs3_0 =>
                          cases rs3_0 with
                          | returned rv3 =>
                            dsimp only at hs2_run
                            injection hs2_run with hr3 hms2_ms3
                            injection hr3 with hr3'; injection hr3' with hrv3
                            subst hrv3
                            have hpost_ms3 : post = { ms3 with locals := post.locals } := by
                              rw [hpost_ms2, ← hms2_ms3]
                            -- Unpack `store v value` -> `s4`:
                            obtain ⟨s4, hst_v, hrest_jset⟩ := seq_store_ret_inv hs3_run
                            have hv_s3 : s3.locals.lookup (ofString "v") = some (.val (.word vw)) := by
                              simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                            have hk_s3 : s3.locals.lookup (ofString "k") = some (.val (.word kw)) := by
                              simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                                show ofString "v" ≠ ofString "k" by decide, hk_s2]
                            have hval_s3 : s3.locals.lookup (ofString "value") =
                                some (.rStruct [.val (.word vw0), .val (.word vw1), .val (.word vw2), .val (.word vw3)]) := by
                              simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                                show ofString "v" ≠ ofString "value" by decide, hval_s2]
                            have hma_s3 : s3.memaddrs = ordinaryDomain := hma_al.trans hA_s2.1.memaddrs
                            have hvw_bound : vw.toNat + 32 ≤ 2 ^ 64 := by
                              have : heapLimit ≤ 2 ^ 64 := by decide
                              omega
                            obtain ⟨heff_st, hloc_s4⟩ := @byteRegionEffect_of_store_struct4 F s3 s4
                              (.var .local (ofString "v")) (.var .local (ofString "value"))
                              vw vw0 vw1 vw2 vw3 hma_s3
                              (by simp [evalHOLExact, hv_s3])
                              (by simp [evalHOLExact, hval_s3])
                              hvw_bound hst_v
                            have hcode_s4 : s4.code = originalRuntimeCode :=
                              heff_st.code.trans (hmeta_al.trans hcode_s2)
                            have hA_s4 : ArenaReady s4 := by
                              have hA_s3 : ArenaReady s3 := (arenaReady_lc cpost_al s3.locals cpost_al.clock).2 hA_cpal
                              exact ⟨guestInv_congr (s := s3) heff_st.code heff_st.memaddrs heff_st.shMemaddrs heff_st.baseAddr hA_s3.1,
                                arenaOK_congr heff_st.globals hA_s3.2⟩
                            have hhp_s4 : globN s4 "heap_ptr" = qw.toNat := by
                              have : s4.globals = cpost_al.globals := heff_st.globals
                              exact (globN_eq_of_lookup_eq (by rw [this])).trans hhp_cpal
                            have hg_kept_s4 : GlobalsKept ["heap_ptr"] s2 s4 := by
                              intro k hk
                              have hs4_g : s4.globals = cpost_al.globals := heff_st.globals
                              have hk_ne : k ≠ ofString "heap_ptr" := fun h => hk (by simp [h])
                              rw [hs4_g]
                              change s2.globals.lookup k = cpost_al.globals.lookup k
                              rw [hg_al, HolFiniteMapExact.lookup_update]
                              simp [FUPDATE, hk_ne.symm]; rfl
                            obtain ⟨hInvAt_s4, hch_s4, hR_s4⟩ := evmInvAt_of_fresh_heap_step
                              hA_s2 hInvAt_s2 hA_s4 (heff_st.be.trans hbe_al)
                              (by rw [hhp_s4]; omega)
                              hg_kept_s4
                              (fun a hna => by
                                have hna3 : ¬ s3.memaddrs a := by rwa [hma_s3, ← hA_s2.1.memaddrs]
                                rw [heff_st.out_dom a hna3]
                                change cpost_al.memory a = s2.memory a
                                rw [hm_al]; rfl)
                              (fun b hb hnot => by
                                rw [heff_st.byte_frame b hb (fun i hi hbi => by
                                  rw [List.mem_singleton] at hi; subst hi
                                  dsimp [InIvl] at hbi
                                  exact hnot ⟨by omega, by rw [hhp_s4]; omega⟩)]
                                unfold memB
                                have hm_s3 : s3.memory = s2.memory := hm_al
                                have hbe_s3 : s3.be = s2.be := hbe_al
                                rw [hm_s3, hbe_s3])
                            -- Unpack `seq (call "jset" ...) (return 0)`:
                            obtain ⟨s_jset, hcall_jset, hret_jset⟩ := seq_call0_ret_inv hrest_jset
                            obtain ⟨vals_j, body_j, cal_j, ret_j, rvj, cpost_j, hargs_j, hl_j, hrun_j, hsjset_eq⟩ :=
                              Wave8M19.Htab.call0_flow s4 _ _ (Or.inl (congrArg Prod.fst hcall_jset))
                            have hbj_eq : body_j = sourceFnBody Guest.Software.guestFn_jset :=
                              lookupCodeHOLFinite_installed_body s4.code.lookup (ofString "jset") _ _ _ _ _ vals_j cal_j
                                (by rw [hcode_s4]; exact lookup_jset) hl_j
                            subst hbj_eq
                            have hrj_eq : ret_j = .one := by
                              have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
                                s4.code.lookup (ofString "jset") vals_j _ cal_j ret_j hl_j
                              rw [hcode_s4] at hx; simp only [Flapjack.lookupCodeHOLExact, lookup_jset] at hx
                              split at hx
                              · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
                              · cases hx
                            subst hrj_eq
                            have hk_s4 : s4.locals.lookup (ofString "k") = some (.val (.word kw)) := by
                              rw [hloc_s4]; exact hk_s3
                            have hv_s4 : s4.locals.lookup (ofString "v") = some (.val (.word vw)) := by
                              rw [hloc_s4]; exact hv_s3
                            obtain ⟨tv_j, vs_j1, rfl, htv_j⟩ := Wave8M19.Htab.evalList_cons_inv s4 _ _ hargs_j
                            obtain ⟨tw, rfl, hts_nz_s4, htw_ts64_s4⟩ := hload_ts64_inv s4 tv_j hA_s4 htv_j
                            have hvs_j1 : vs_j1 = [.val (.word kw), .val (.word vw)] := by
                              rw [evalListHOLFinite_eq_toExact] at hargs_j
                              have hev_k : @evalHOLExact 64 F _ s4.toExact
                                  (fun a => Classical.propDecidable (s4.memaddrs a))
                                  (.var .local (ofString "k")) = some (.val (.word kw)) := by
                                simp [evalHOLExact, hk_s4]
                              have hev_v : @evalHOLExact 64 F _ s4.toExact
                                  (fun a => Classical.propDecidable (s4.memaddrs a))
                                  (.var .local (ofString "v")) = some (.val (.word vw)) := by
                                simp [evalHOLExact, hv_s4]
                              unfold evalListHOLExact at hargs_j
                              rw [htv_j] at hargs_j
                              unfold evalListHOLExact at hargs_j
                              rw [hev_k] at hargs_j
                              unfold evalListHOLExact at hargs_j
                              rw [hev_v] at hargs_j
                              unfold evalListHOLExact at hargs_j
                              dsimp only at hargs_j
                              injection hargs_j with hcons
                              exact (List.cons.inj hcons).2.symm
                            subst hvs_j1
                            have hex_j := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
                              s4.code.lookup (ofString "jset")
                              [.val (.word tw), .val (.word kw), .val (.word vw)] _ cal_j .one hl_j
                            unfold lookupCodeHOLExact at hex_j; rw [hcode_s4, lookup_jset] at hex_j; dsimp only at hex_j
                            split at hex_j
                            · have hmap_j := congrArg (fun x => x.2.1) (Option.some.inj hex_j)
                              have hcal_jt : cal_j.lookup (ofString "t") = some (.val (.word tw)) := by
                                have := congrFun hmap_j.symm (ofString "t")
                                simpa [List.map, List.zip, List.foldl,
                                  show ofString "t" ≠ ofString "value" by decide,
                                  show ofString "t" ≠ ofString "key" by decide] using this
                              have hcal_jk : cal_j.lookup (ofString "key") = some (.val (.word kw)) := by
                                have := congrFun hmap_j.symm (ofString "key")
                                simpa [List.map, List.zip, List.foldl,
                                  show ofString "key" ≠ ofString "value" by decide] using this
                              have hcal_jv : cal_j.lookup (ofString "value") = some (.val (.word vw)) := by
                                have := congrFun hmap_j.symm (ofString "value")
                                simpa [List.map, List.zip, List.foldl] using this
                              let entry_j := callEntryStateHOLFinite s4 cal_j
                              have hcode_ej : entry_j.code = originalRuntimeCode := hcode_s4
                              have hA_ej : ArenaReady entry_j :=
                                ⟨guestInv_congr (s := s4) rfl rfl rfl rfl hA_s4.1, hA_s4.2⟩
                              have hInv_ej : EvmInvAt entry_j S_s2 :=
                                (evmInvAt_lc s4 entry_j.locals entry_j.clock S_s2).2 hInvAt_s4
                              have hjset_res := jset_ts64_step hcode_ej hA_ej hInv_ej
                                hcal_jt hcal_jk hcal_jv hts_nz_s4 htw_ts64_s4
                                (by change (evaluateHOLFiniteState (callEntryStateHOLFinite s4 cal_j) _).1 = _; rw [hrun_j])
                              dsimp only [entry_j] at hjset_res; rw [hrun_j] at hjset_res
                              obtain ⟨hA_cj, hInv_cj, hch_cj, hR_cj⟩ := hjset_res
                              have hsjset_cj : s_jset = { cpost_j with locals := s4.locals } :=
                                (Prod.mk.inj (hcall_jset.symm.trans hsjset_eq)).2
                              rw [evaluateHOLFiniteState_return] at hret_jset
                              simp [evalHOLExact, shapeOfHOLExact] at hret_jset
                              obtain ⟨_, hret_sj⟩ := hret_jset
                              have hp_cj : post = { cpost_j with locals := post.locals, clock := cpost_j.clock } := by
                                rw [hpost_ms3, ← hret_sj, hsjset_cj]
                                cases cpost_j; rfl
                              have hInv_p : EvmInv post := by
                                rw [hp_cj]
                                exact ⟨(arenaReady_lc cpost_j _ _).2 hA_cj, S_s2,
                                       (evmInvAt_lc cpost_j _ _ S_s2).2 hInv_cj⟩
                              have hch_p : evmChain post = evmChain s := by
                                rw [hp_cj]
                                exact ((evmChain_lc cpost_j _ _).trans hch_cj).trans
                                  ((evmChain_lc s4 _ _).trans (hch_s4.trans hch_s2))
                              have hR_p : evmR post = evmR s := by
                                rw [hp_cj]
                                exact ((evmR_lc cpost_j _ _).trans hR_cj).trans
                                  ((evmR_lc s4 _ _).trans (hR_s4.trans hR_s2))
                              exact ⟨hInv_p, hch_p, le_of_eq hR_p, hR_p⟩
                            · cases hex_j
                          | _ => simp at hs2_run
                      · -- `zw ≠ 0`: `call "jdel" [load .one (ts + 64), k]; return 0`
                        have hcmp_z : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
                            (.cmp .notEqual (.var .local (ofString "z")) (.const 0)) =
                            some (.val (.word 1#64)) := by
                          simp [evalHOLExact, hz_s2, Compiler.Encoders.Asm.wordCmpHOL, hzw0]
                        have h1_nz : (1#64 : BitVec 64) ≠ 0 := by decide
                        rw [hcmp_z] at hs2_run; dsimp only at hs2_run
                        rw [if_neg h1_nz] at hs2_run
                        rcases hseq_jd : s2.evaluateHOLFiniteState
                            (.seq
                              (.call (some (none, none)) (ofString "jdel")
                                [.load .one (.op .add [.var .global (ofString "ts"), .const 64]),
                                 .var .local (ofString "k")])
                              (.return (.const 0))) with ⟨r_jd, m_jd⟩
                        rw [hseq_jd] at hs2_run
                        have hrjd_ret : ∃ u, r_jd = some (.returned u) := by
                          rw [evaluateHOLFiniteState_seq_line780] at hseq_jd
                          rcases hc_jd : s2.evaluateHOLFiniteState
                              (.call (some (none, none)) (ofString "jdel")
                                [.load .one (.op .add [.var .global (ofString "ts"), .const 64]),
                                 .var .local (ofString "k")]) with ⟨rc_jd, mc_jd⟩
                          rw [hc_jd] at hseq_jd
                          cases rc_jd with
                          | none =>
                            dsimp only at hseq_jd
                            rw [evaluateHOLFiniteState_return] at hseq_jd
                            simp [evalHOLExact, shapeOfHOLExact] at hseq_jd
                            exact ⟨.val (.word 0#64), hseq_jd.1.symm⟩
                          | some rc0 =>
                            dsimp only at hseq_jd
                            injection hseq_jd with hr_eq hm_eq
                            subst hr_eq hm_eq
                            dsimp only at hs2_run
                            cases rc0 with
                            | returned u => exact ⟨u, rfl⟩
                            | _ => simp at hs2_run
                        obtain ⟨ujd, rfl⟩ := hrjd_ret
                        dsimp only at hs2_run
                        injection hs2_run with _ hms2_mjd
                        have hpost_mjd : post = { m_jd with locals := post.locals } := by
                          rw [hpost_ms2, ← hms2_mjd]
                        obtain ⟨s_jdel, hcall_jdel, hret_jdel⟩ := seq_call0_ret_inv hseq_jd
                        obtain ⟨vals_d, body_d, cal_d, ret_d, rvd, cpost_d, hargs_d, hl_d, hrun_d, hsjdel_eq⟩ :=
                          Wave8M19.Htab.call0_flow s2 _ _ (Or.inl (congrArg Prod.fst hcall_jdel))
                        have hbd_eq : body_d = sourceFnBody Guest.Software.guestFn_jdel :=
                          lookupCodeHOLFinite_installed_body s2.code.lookup (ofString "jdel") _ _ _ _ _ vals_d cal_d
                            (by rw [hcode_s2]; exact lookup_jdel) hl_d
                        subst hbd_eq
                        have hrd_eq : ret_d = .one := by
                          have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
                            s2.code.lookup (ofString "jdel") vals_d _ cal_d ret_d hl_d
                          rw [hcode_s2] at hx; simp only [Flapjack.lookupCodeHOLExact, lookup_jdel] at hx
                          split at hx
                          · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
                          · cases hx
                        subst hrd_eq
                        obtain ⟨tv_d, vs_d1, rfl, htv_d⟩ := Wave8M19.Htab.evalList_cons_inv s2 _ _ hargs_d
                        obtain ⟨tw, rfl, hts_nz_s2, htw_ts64_s2⟩ := hload_ts64_inv s2 tv_d hA_s2 htv_d
                        have hvs_d1 : vs_d1 = [.val (.word kw)] := by
                          rw [evalListHOLFinite_eq_toExact] at hargs_d
                          have hev_k : @evalHOLExact 64 F _ s2.toExact
                              (fun a => Classical.propDecidable (s2.memaddrs a))
                              (.var .local (ofString "k")) = some (.val (.word kw)) := by
                            simp [evalHOLExact, hk_s2]
                          unfold evalListHOLExact at hargs_d
                          rw [htv_d] at hargs_d
                          unfold evalListHOLExact at hargs_d
                          rw [hev_k] at hargs_d
                          unfold evalListHOLExact at hargs_d
                          dsimp only at hargs_d
                          injection hargs_d with hcons
                          exact (List.cons.inj hcons).2.symm
                        subst hvs_d1
                        have hex_d := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
                          s2.code.lookup (ofString "jdel")
                          [.val (.word tw), .val (.word kw)] _ cal_d .one hl_d
                        unfold lookupCodeHOLExact at hex_d; rw [hcode_s2, lookup_jdel] at hex_d; dsimp only at hex_d
                        split at hex_d
                        · have hmap_d := congrArg (fun x => x.2.1) (Option.some.inj hex_d)
                          have hcal_dt : cal_d.lookup (ofString "t") = some (.val (.word tw)) := by
                            have := congrFun hmap_d.symm (ofString "t")
                            simpa [List.map, List.zip, List.foldl,
                              show ofString "t" ≠ ofString "key" by decide] using this
                          have hcal_dk : cal_d.lookup (ofString "key") = some (.val (.word kw)) := by
                            have := congrFun hmap_d.symm (ofString "key")
                            simpa [List.map, List.zip, List.foldl] using this
                          let entry_d := callEntryStateHOLFinite s2 cal_d
                          have hcode_ed : entry_d.code = originalRuntimeCode := hcode_s2
                          have hA_ed : ArenaReady entry_d :=
                            ⟨guestInv_congr (s := s2) rfl rfl rfl rfl hA_s2.1, hA_s2.2⟩
                          have hInv_ed : EvmInvAt entry_d S_s2 :=
                            (evmInvAt_lc s2 entry_d.locals entry_d.clock S_s2).2 hInvAt_s2
                          have hjdel_res := jdel_ts64_step hcode_ed hA_ed hInv_ed
                            hcal_dt hcal_dk hts_nz_s2 htw_ts64_s2
                            (by change (evaluateHOLFiniteState (callEntryStateHOLFinite s2 cal_d) _).1 = _; rw [hrun_d])
                          dsimp only [entry_d] at hjdel_res; rw [hrun_d] at hjdel_res
                          obtain ⟨hA_cd, hInv_cd, hch_cd, hR_cd⟩ := hjdel_res
                          have hsjdel_cd : s_jdel = { cpost_d with locals := s2.locals } :=
                            (Prod.mk.inj (hcall_jdel.symm.trans hsjdel_eq)).2
                          rw [evaluateHOLFiniteState_return] at hret_jdel
                          simp [evalHOLExact, shapeOfHOLExact] at hret_jdel
                          obtain ⟨_, hret_sd⟩ := hret_jdel
                          have hp_cd : post = { cpost_d with locals := post.locals, clock := cpost_d.clock } := by
                            rw [hpost_mjd, ← hret_sd, hsjdel_cd]
                            cases cpost_d; rfl
                          have hInv_p : EvmInv post := by
                            rw [hp_cd]
                            exact ⟨(arenaReady_lc cpost_d _ _).2 hA_cd, S_s2,
                                   (evmInvAt_lc cpost_d _ _ S_s2).2 hInv_cd⟩
                          have hch_p : evmChain post = evmChain s := by
                            rw [hp_cd]
                            exact ((evmChain_lc cpost_d _ _).trans hch_cd).trans
                              ((evmChain_lc s2 _ _).trans hch_s2)
                          have hR_p : evmR post = evmR s := by
                            rw [hp_cd]
                            exact ((evmR_lc cpost_d _ _).trans hR_cd).trans
                              ((evmR_lc s2 _ _).trans hR_s2)
                          exact ⟨hInv_p, hch_p, le_of_eq hR_p, hR_p⟩
                        · cases hex_d
                    | _ => simp at hs1_run
                · simp at hs1_run
              | _ => simp at hs1_run
          | _ => simp at hrun
      · simp at hrun
    | _ => simp at hrun

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
