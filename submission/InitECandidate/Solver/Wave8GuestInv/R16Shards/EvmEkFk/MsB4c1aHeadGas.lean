import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.MsB4bPrimSteps

/-!
# Scratch Rung B4c1: Read-Only Callees, Head Gas Updates, and `warm_address` under `D0PreB`
-/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.EvmStepLemmas
open InitECandidate.Solver.Wave8GuestInv.EvmFrameSpecs
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
open InitECandidate.Solver.Wave8M19.Htab
open InitECandidate.Solver.Wave8GuestInv.HtabC00Ports
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge
open InitECandidate.Solver.Wave8Contracts
open InitECandidate.Solver.Wave8Contracts.M23
open InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue (noCatchableRaise evaluate_noCatchableRaise)

section MsB4c1GasWarmRo
open R10Shards.GbodyProcessMsg
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

/-! ## 1. Read-only `is_warm_address` and generic `D0PreB` read-only `decCall` wrapper -/

theorem ro_is_warm_address : ReadOnlyFn (ofString "is_warm_address") :=
  ⟨_, _, _, lookup_of_guestAst_getElem 471 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_is_warm_address) rfl,
    fun s hcode _ _ _ hr =>
      (evaluate_readOnlyProg opRoCallees opRoCallees_good _ rfl s hcode).to_resumes hr⟩

theorem hoare_d0PreB_decCall_ro
    (gw : List String) (hp : Nat) (G : MlS → Option (ValueHOL 64))
    (ch : List Ivl) (cells : List (Nat × Nat × Nat × Nat))
    (keep : List String)
    (L : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (hL : LocalsOnly keep L)
    {name fname : MlS} (hne : ofString "msg" ≠ name) (hnek : ∀ k ∈ keep, ofString k ≠ name)
    (hro : ReadOnlyFn fname)
    (args : List (ExpHOL 64)) (tail : ProgHOL 64)
    (htail : Hoare (fun s => (D0PreB gw hp G ch cells s ∧ L s) ∧
        ∃ w : BitVec 64, s.locals.lookup name = some (.val (.word w))) tail
      (Fall (fun s => EvmMsgReadyMsgBounded s ∧ StepFromCC gw hp G ch cells s))) :
    Hoare (fun s => D0PreB gw hp G ch cells s ∧ L s)
      (.decCall name .one fname args tail)
      (Fall (fun s => EvmMsgReadyMsgBounded s ∧ StepFromCC gw hp G ch cells s)) := by
  let P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
    fun s => D0PreB gw hp G ch cells s ∧ L s
  have hLO : LocalsOnly ("msg" :: keep) P := by
    intro F s l k hl h
    exact ⟨d0PreB_locals gw hp G ch cells s l k (hl "msg" (by simp)) h.1,
      hL s l k (fun x hx => hl x (List.mem_cons_of_mem _ hx)) h.2⟩
  have hG : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → GuestInv s :=
    fun s h => h.1.1.1.1.1
  have hnot_mem : ∀ n ∈ ("msg" :: keep), ofString n ≠ name := by
    rintro n hn
    rcases List.mem_cons.mp hn with rfl | hn'
    · exact hne
    · exact hnek n hn'
  exact Hoare.decCall_ro_fall hro hG
    (fun s l k h => ⟨localsFree_evmMsgReadyMsgBounded s l k h.1,
      localsFree_stepFromCC gw hp G ch cells s l k h.2⟩)
    (fun _ h => h.1.1)
    (ReadOnlyFn.resumeOn hLO hG hro name hnot_mem args)
    htail

/-! ## 2. Multi-word head-frame gas update preserving `EvmMsgReadyMsgBounded` -/

def headGasUpdateOffs : List Nat := [64, 72, 184, 192, 200]

theorem evmMsgReadyMsgBounded_of_head_gas_mem {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hB : EvmMsgReadyMsgBounded s)
    (hGp : GuestInv post)
    (hglob : post.globals = s.globals)
    (hbe : post.be = s.be)
    (hmem_out : ∀ x : BitVec 64,
      (∀ off ∈ headGasUpdateOffs, x ≠ BitVec.ofNat 64 (globN s "ev" + off)) →
      post.memory x = s.memory x)
    (hgas_le : memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) ≤
      memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192)) :
    EvmMsgReadyMsgBounded post ∧ EvmStepCC [] s post ∧
      memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112) := by
  obtain ⟨hAs, hM, S, hInvAt, hm_nz, hC⟩ := hB
  obtain ⟨hW, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW, hFO_pw, hFO_disj, hAT, hMarks, hRoles, hGas⟩ := hInvAt
  obtain ⟨Nd_at, hTr_at, hAT_at⟩ := hAT
  have hWT : WorldTypedWith s S Nd_at := ⟨hW.1, hW.2.1, hW.2.2.1, hTr_at⟩
  set e0 := globN s "ev"
  set c0 := globN s "cur_cont"
  have hch_cons : ∃ tl, evmChain s = (e0, c0) :: tl := ⟨_, rfl⟩
  obtain ⟨chTail, hch_eq⟩ := hch_cons
  have hhead_mem : (e0, c0) ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_self
  have hhead_FW := hFW_all _ hhead_mem
  obtain ⟨hb1, _, _, _⟩ := EvmStepLemmas.frameWF_bounds hAs.2 hhead_FW
  dsimp only at hb1
  have he0_8 : e0 % 8 = 0 := (hhead_FW.1 (e0, 280) (by simp)).2.1
  have hdom_eq : post.memaddrs = s.memaddrs := hGp.memaddrs.trans hAs.1.memaddrs.symm
  have hoff_props : ∀ off ∈ headGasUpdateOffs,
      off + 8 ≤ 280 ∧ off % 8 = 0 ∧ s.memaddrs (BitVec.ofNat 64 (e0 + off)) := by
    intro off hoff
    have hdiv : off + 8 ≤ 280 ∧ off % 8 = 0 ∧ off / 8 < 280 / 8 ∧ 8 * (off / 8) = off := by
      revert off hoff; decide
    obtain ⟨_, hdom, _⟩ := (hhead_FW.1 (e0, 280) (by simp)).2.2.2 (off / 8) hdiv.2.2.1
    exact ⟨hdiv.1, hdiv.2.1, by simpa [hdiv.2.2.2] using hdom⟩
  have heff : M23.ByteRegionEffect s post [(e0, 280)] := by
    refine ⟨hGp.code.trans hAs.1.code.symm, hdom_eq,
      hGp.shMemaddrs.trans hAs.1.shMemaddrs.symm,
      hGp.baseAddr.trans hAs.1.baseAddr.symm, hbe, hglob, ?_, ?_, ?_⟩
    · intro a hna
      apply hmem_out a
      intro off hoff rfl
      exact hna (hoff_props off hoff).2.2
    · intro a ha
      apply hmem_out a
      intro off hoff rfl
      have hp := hoff_props off hoff
      have htn : (BitVec.ofNat 64 (e0 + off)).toNat = e0 + off := Nat.mod_eq_of_lt (by omega)
      exact ha (e0, 280) (by simp) ⟨by rw [htn]; omega, by rw [htn]; omega⟩
    · intro b hb hno
      unfold memB
      have hal_b : (panByteAlignHOL (BitVec.ofNat 64 b)).toNat = b / 8 * 8 := by
        rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
      rw [hmem_out (panByteAlignHOL (BitVec.ofNat 64 b)), hbe]
      intro off hoff heq
      have hp := hoff_props off hoff
      have htn : (BitVec.ofNat 64 (e0 + off)).toNat = e0 + off := Nat.mod_eq_of_lt (by omega)
      have := congrArg BitVec.toNat heq
      rw [hal_b, htn] at this
      exact hno (e0, 280) (by simp) ⟨by dsimp only; omega, by dsimp only; omega⟩
  have hRl8_e0 : ∀ x ∈ ([(e0, 280)] : List Ivl), x.1 % 8 = 0 := by
    intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact he0_8
  have hglob_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, hglob]
  have hApost : ArenaReady post := ⟨hGp, arenaOK_congr hglob hAs.2⟩
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hglob_eq]
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hglob_eq]
  have hrec_fo : (e0, 280) ∈ frameObjects s (e0, c0) := by simp [frameObjects]
  have hrec_disj_wti : ∀ i ∈ worldTypedIvls s S Nd_at, i.2 = 0 ∨ Disj (e0, 280) i := by
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
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))
      exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _ hfix_j)
    · exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _ (blockOut_in_fixedObjects h4))
    · exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _ (bal_in_fixedObjects h5))
    · exact Or.inr (hAT_at _ (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨_, hhead_mem, rfl⟩, hrec_fo⟩) i h6)
  have hcell : M23.SameTypedCells s post S Nd_at :=
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
    ⟨hWT_post.1, hWT_post.2.1, hWT_post.2.2.1, Nd_at, hWT_post.2.2.2⟩
  have hmemW_ne : ∀ a : Nat, a < 2 ^ 64 →
      (∀ off ∈ headGasUpdateOffs, a ≠ e0 + off) → memW post a = memW s a := by
    intro a ha hne
    unfold memW
    rw [hmem_out (BitVec.ofNat 64 a)]
    intro off hoff heq
    have hp := hoff_props off hoff
    have := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega)] at this
    exact hne off hoff this
  have hpw_head_tail :
      (frameObjects s (e0, c0)).Pairwise Disj ∧
      (∀ o1 ∈ frameObjects s (e0, c0),
        ∀ ec ∈ chTail, ∀ o2 ∈ frameObjects s ec, Disj o1 o2) := by
    have hpw := hFO_pw
    rw [hch_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
    refine ⟨hpw.1, fun o1 ho1 ec hec o2 ho2 => hpw.2.2 o1 ho1 o2 ?_⟩
    exact List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ec, hec, rfl⟩, ho2⟩
  have hhead_disj_rest : ∀ o ∈ ((c0, 104) :: (memW s (e0 + 8), 32 * memW s (e0 + 232)) ::
      (memW s (e0 + 24), memW s (e0 + 40)) :: (memW s (e0 + 88), 24) ::
      frameLogs s (e0, c0) :: frameRet s (e0, c0) :: frameLogObjects s (e0, c0)),
      Disj (e0, 280) o := by
    have hpw0 := hpw_head_tail.1
    unfold frameObjects at hpw0
    exact (List.pairwise_cons.1 hpw0).1
  have hdisj_e0_nonrec : ∀ ec ∈ evmChain s,
      Disj (e0, 280) (ec.2, 104) ∧
      Disj (e0, 280) (memW s (ec.1 + 88), 24) ∧
      Disj (e0, 280) (frameLogs s ec) ∧
      (∀ i < memW s (memW s (ec.1 + 88) + 8),
        Disj (e0, 280) (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40)) := by
    intro ec hec
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with rfl | htail
    · refine ⟨hhead_disj_rest _ (by simp), hhead_disj_rest _ (by simp),
        hhead_disj_rest _ (by simp), fun i hi => hhead_disj_rest _ ?_⟩
      simp only [List.mem_cons]
      right; right; right; right; right; right
      unfold frameLogObjects; dsimp only
      exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
    · refine ⟨hpw_head_tail.2 _ hrec_fo ec htail _ (by simp [frameObjects]),
        hpw_head_tail.2 _ hrec_fo ec htail _ (by simp [frameObjects]),
        hpw_head_tail.2 _ hrec_fo ec htail _ (by simp [frameObjects]),
        fun i hi => hpw_head_tail.2 _ hrec_fo ec htail _ ?_⟩
      unfold frameObjects; apply List.mem_append_right
      unfold frameLogObjects; dsimp only
      exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
  have hrec_eq : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → k ∉ headGasUpdateOffs → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → k % 8 = 0 → memW post (ec.2 + k) = memW s (ec.2 + k)) ∧
      (∀ k, k + 8 ≤ 24 → k % 8 = 0 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨hb_e, hb_c, hb_88, _⟩ := M23.frameWF_bounds hAs.2 hFW
    have hc8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
    have h88_8 : (memW s (ec.1 + 88)) % 8 = 0 := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).2.1
    obtain ⟨hd_c, hd_88, _, _⟩ := hdisj_e0_nonrec ec hec
    refine ⟨?_,
      fun k hk hk8 => memW_eq_of_disj_eff heff hRl8_e0 hb_c hc8 hk8 hk (fun x hx => by simp at hx; subst hx; exact hd_c),
      fun k hk hk8 => memW_eq_of_disj_eff heff hRl8_e0 hb_88 h88_8 hk8 hk (fun x hx => by simp at hx; subst hx; exact hd_88)⟩
    intro k hk hknot
    apply hmemW_ne (ec.1 + k) (by omega)
    intro off hoff heq
    have hp := hoff_props off hoff
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with rfl | htail
    · have : k = off := by dsimp only at heq; omega
      exact hknot (this ▸ hoff)
    · have hd := hpw_head_tail.2 (e0, 280) hrec_fo ec htail (ec.1, 280) (by simp [frameObjects])
      rcases hd with h0 | h0 | h1 | h2 <;> dsimp only at * <;> omega
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
    unfold evmChain; rw [hglob_eq "ev", hglob_eq "cur_cont"]
    exact hchain_aux _ _ _ (fun _ h => h)
  have hframeLogs_eq : ∀ ec ∈ evmChain s, frameLogs post ec = frameLogs s ec := by
    intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    unfold frameLogs
    rw [he_eq 88 (by omega) (by decide),
        show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by simpa using h88_eq 0 (by omega) (by omega),
        h88_eq 16 (by omega) (by omega)]
  have hframeRet_eq : ∀ ec ∈ evmChain s, frameRet post ec = frameRet s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameRet
    rw [he_eq 216 (by omega) (by decide), he_eq 144 (by omega) (by decide)]
  have hlogs_congr : ∀ ec ∈ evmChain s,
      frameLogObjects post ec = frameLogObjects s ec ∧ LogsListOK post (memW post (ec.1 + 88)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨_, _, _, hfob⟩ := M23.frameWF_bounds hAs.2 hFW
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    obtain ⟨_, _, hd_fl, hd_lr⟩ := hdisj_e0_nonrec ec hec
    have hl0 : memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) := by
      simpa using h88_eq 0 (by omega) (by omega)
    have hl8 : memW post (memW s (ec.1 + 88) + 8) = memW s (memW s (ec.1 + 88) + 8) :=
      h88_eq 8 (by omega) (by omega)
    have hl16 : memW post (memW s (ec.1 + 88) + 16) = memW s (memW s (ec.1 + 88) + 16) :=
      h88_eq 16 (by omega) (by omega)
    have harr_eq : ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
        memW post (memW s (memW s (ec.1 + 88)) + 8 * i) = memW s (memW s (memW s (ec.1 + 88)) + 8 * i) := by
      intro i hi
      have hfl_in : frameLogs s ec ∈ frameObjects s ec := by simp [frameObjects]
      have hlen_le : memW s (memW s (ec.1 + 88) + 8) ≤ memW s (memW s (ec.1 + 88) + 16) :=
        hFW.2.2.2.2.2.2.2.2.2.2.2.1
      have hfl_b : (frameLogs s ec).1 + (frameLogs s ec).2 ≤ 2 ^ 64 := by
        rcases hfob _ hfl_in with h0 | hb
        · unfold frameLogs at h0; dsimp only at h0; omega
        · exact hb
      have hfl_8 : (memW s (memW s (ec.1 + 88))) % 8 = 0 := hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
      exact memW_eq_of_disj_eff heff hRl8_e0 hfl_b hfl_8 (by omega)
        (by unfold frameLogs; dsimp only; omega)
        (fun x hx => by simp at hx; subst hx; exact hd_fl)
    have hlr_eq : ∀ i (hi : i < memW s (memW s (ec.1 + 88) + 8)) off, off + 8 ≤ 40 → off % 8 = 0 →
        memW post (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + off) =
          memW s (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + off) := by
      intro i hi off hoff hoff8
      have hlr_in : (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40) ∈ frameObjects s ec := by
        unfold frameObjects; apply List.mem_append_right
        unfold frameLogObjects; dsimp only
        exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
      have hlr_b : memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + 40 ≤ 2 ^ 64 := by
        rcases hfob _ hlr_in with h0 | hb
        · dsimp only at h0; omega
        · exact hb
      have hlr_8 : (memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) % 8 = 0 := by
        rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
        · have he88_in := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1.1
          have h1 := hAs.2.2.2.1; have h2 := hAs.2.2.2.2.1
          rw [R11Shards.scratchStart_val] at h1; dsimp only at he88_in; omega
        · exact (hent i hi).2.1.1
      exact memW_eq_of_disj_eff heff hRl8_e0 hlr_b hlr_8 hoff8 hoff
        (fun x hx => by simp at hx; subst hx; exact hd_lr i hi)
    refine ⟨?_, ?_⟩
    · unfold frameLogObjects; dsimp only
      rw [he_eq 88 (by omega) (by decide), hl8]
      apply List.flatMap_congr; intro i hi; rw [List.mem_range] at hi
      rw [hl0, harr_eq i hi]
      have r0 := hlr_eq i hi 0 (by omega) (by omega)
      have r8 := hlr_eq i hi 8 (by omega) (by omega)
      have r16 := hlr_eq i hi 16 (by omega) (by omega)
      have r24 := hlr_eq i hi 24 (by omega) (by omega)
      have r32 := hlr_eq i hi 32 (by omega) (by omega)
      simp only [Nat.add_zero] at r0
      unfold logOwnedIvls logRecordIvls
      rw [r0, r8, r16, r24, r32, hglob_eq "vm_system_address"]
    · rw [he_eq 88 (by omega) (by decide)]
      rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨hw_l, hal_l, hlt28, hle_cap, hent⟩
      · exact Or.inl hz
      · right
        refine ⟨(wordsOK_congr_dom hdom_eq).2 hw_l, allocated_mono hh hsc hal_l,
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
        rw [r0, r8, r16, r24, r32, hglob_eq "heap_ptr"]
        exact ⟨(wordsOK_congr_dom hdom_eq).2 hle.1, hle.2⟩
  have hframeObjects_eq : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameObjects
    rw [he_eq 8 (by omega) (by decide), he_eq 232 (by omega) (by decide),
        he_eq 24 (by omega) (by decide), he_eq 40 (by omega) (by decide),
        he_eq 88 (by omega) (by decide),
        hframeLogs_eq ec hec, hframeRet_eq ec hec, (hlogs_congr ec hec).1]
  have hframeScratch_eq : ∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameScratch
    rw [he_eq 8 (by omega) (by decide), he_eq 232 (by omega) (by decide),
        he_eq 88 (by omega) (by decide)]
  have hmap_fo_eq : (evmChain s).map (frameObjects post) = (evmChain s).map (frameObjects s) :=
    List.map_congr_left hframeObjects_eq
  have hframeRoleSlots_eq : frameRoleSlots post (evmChain s) = frameRoleSlots s (evmChain s) := by
    unfold frameRoleSlots; apply List.flatMap_congr; intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    rw [he_eq 136 (by omega) (by decide), he_eq 168 (by omega) (by decide),
        he_eq 176 (by omega) (by decide)]
  have hfp_eq_all : ∀ t ∈ S, htabFootprint post t = htabFootprint s t :=
    fun t ht => htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1
  have htail_gas_eq : (chTail.map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)) =
      (chTail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)) := by
    apply List.map_congr_left; intro ec htail
    have hec : ec ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_of_mem _ htail
    obtain ⟨hb_ec, _, _, _⟩ := M23.frameWF_bounds hAs.2 (hFW_all ec hec)
    have hd := hpw_head_tail.2 (e0, 280) hrec_fo ec htail (ec.1, 280) (by simp [frameObjects])
    have hne_ec : ∀ off1, off1 + 8 ≤ 280 → ∀ off2 ∈ headGasUpdateOffs, ec.1 + off1 ≠ e0 + off2 := by
      intro off1 _ off2 hoff2 heq
      have hp2 := hoff_props off2 hoff2
      rcases hd with h0 | h0 | h1 | h2 <;> dsimp only at * <;> omega
    rw [hmemW_ne (ec.1 + 64) (by omega) (hne_ec 64 (by omega)),
        hmemW_ne (ec.1 + 192) (by omega) (hne_ec 192 (by omega))]
  have hR_le : evmR post ≤ evmR s := by
    unfold evmR
    rw [hchain_eq, hch_eq, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, htail_gas_eq]
    exact Nat.add_le_add_right hgas_le _
  have hInvAt_post : EvmInvAt post S := by
    refine ⟨hW_post, by rw [hchain_eq]; exact hch_ne, by rw [hchain_eq]; exact hch_len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hchain_eq]; obtain ⟨ec, hec, hk0⟩ := hch_last
      have hec_mem := List.mem_of_mem_getLast? hec
      exact ⟨ec, hec, by rw [(hrec_eq ec hec_mem).2.1 16 (by omega) (by omega)]; exact hk0⟩
    · rw [hchain_eq]; intro ec hec
      obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
      obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, _, c17⟩ := hFW_all ec hec
      have hlo_ok := (hlogs_congr ec hec).2
      have hmsg_ok : MsgOwned post S (memW post (ec.1 + 112)) := by
        rw [he_eq 112 (by omega) (by decide)]
        obtain ⟨hal_m, hw_m, hdt, hdf, hdfo, Nd_m, hTr_m, hdj_m⟩ := c17
        obtain ⟨hTr_int, hsub_int⟩ := R11Shards.triesTypedWith_inter hTr_at hTr_m
        set Ndi := Nd_at.filter (fun n => decide (n ∈ Nd_m))
        have hcell_i : M23.SameTypedCells s post S Ndi := by
          have hwti_sub : ∀ i ∈ worldTypedIvls s S Ndi, i ∈ worldTypedIvls s S Nd_at := by
            intro i hi; unfold worldTypedIvls at hi ⊢
            rcases List.mem_append.1 hi with hpre | hne
            · exact List.mem_append_left _ hpre
            · apply List.mem_append_right; unfold nodeExtents at hne ⊢
              obtain ⟨n, hn, hnx⟩ := List.mem_flatMap.1 hne
              exact List.mem_flatMap.2 ⟨n, (List.mem_filter.1 hn).1, hnx⟩
          refine ⟨hcell.1, hcell.2.1, hcell.2.2.1, hcell.2.2.2.1,
            fun a ha ha8 ⟨i, hi, h1, h2⟩ => hcell.2.2.2.2.1 a ha ha8 ⟨i, hwti_sub i hi, h1, h2⟩,
            fun b hb ⟨i, hi, h1, h2⟩ => hcell.2.2.2.2.2 b hb ⟨i, hwti_sub i hi, h1, h2⟩⟩
        obtain ⟨hWT_i_post, _⟩ := worldTypedWith_congr_w1 hAs hApost hh hsc
          (fun g _ => hglob_eq g) hcell_i ⟨hWT.1, hWT.2.1, hWT.2.2.1, hTr_int⟩
          ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
        refine ⟨allocated_mono hh hsc hal_m, (wordsOK_congr_dom hdom_eq).2 hw_m,
          fun t ht i hi => by rw [hfp_eq_all t ht] at hi; exact hdt t ht i hi,
          by rw [hfeq]; exact hdf,
          by rw [hchain_eq]; intro ec' hec' o ho; rw [hframeObjects_eq ec' hec'] at ho; exact hdfo ec' hec' o ho,
          Ndi, hWT_i_post.2.2.2, fun o ho j hj => ?_⟩
        rw [nodeExtents_eq hTr_int.1 hcell_i] at hj
        exact hdj_m o ho j (hsub_int j hj).2
      unfold FrameWF; dsimp only
      rw [he_eq 8 (by omega) (by decide), he_eq 232 (by omega) (by decide),
          he_eq 88 (by omega) (by decide), he_eq 24 (by omega) (by decide),
          he_eq 40 (by omega) (by decide), he_eq 16 (by omega) (by decide),
          he_eq 32 (by omega) (by decide), he_eq 136 (by omega) (by decide),
          he_eq 168 (by omega) (by decide), he_eq 176 (by omega) (by decide),
          h88_eq 16 (by omega) (by omega), h88_eq 8 (by omega) (by omega),
          hframeLogs_eq ec hec,
          he_eq 216 (by omega) (by decide), he_eq 144 (by omega) (by decide),
          hframeRet_eq ec hec,
          hglob_eq "scratch_ptr", hglob_eq "frame_mem_ptr", hglob_eq "heap_ptr", hglob_eq "evm_empty"]
      rw [he_eq 88 (by omega) (by decide)] at hlo_ok
      refine ⟨fun i hi => ⟨(c1 i hi).1, (wordsOK_congr_dom hdom_eq).2 (c1 i hi).2⟩,
        c2, (wordsOK_congr_dom hdom_eq).2 c3, c4, c5, c6, c7, c8, c9, c10, c11, c12,
        c13, (wordsOK_congr_dom hdom_eq).2 c14, ?_, hlo_ok, hmsg_ok⟩
      rcases c15 with h0 | ⟨hin, hw⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hin, (wordsOK_congr_dom hdom_eq).2 hw⟩
    · rw [hchain_eq]; intro ec hec
      have hec_mem := List.mem_of_mem_tail hec
      unfold FrameRoom
      rw [(hrec_eq ec hec_mem).1 16 (by omega) (by decide),
          (hrec_eq ec hec_mem).1 232 (by omega) (by decide)]
      exact hFR_all ec hec
    · simp only [hchain_eq]; intro i hi
      have hi0 : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
      have hi1 : (evmChain s)[i + 1] ∈ evmChain s := List.getElem_mem _
      rw [(hrec_eq _ hi0).2.1 80 (by omega) (by omega),
          (hrec_eq _ hi0).2.1 72 (by omega) (by omega),
          (hrec_eq _ hi1).1 40 (by omega) (by decide)]
      exact hRW i hi
    · rw [hchain_eq, hmap_fo_eq]; exact hFO_pw
    · rw [hchain_eq]; intro ec hec o ho
      rw [hframeObjects_eq ec hec] at ho; rw [hfeq]
      exact ⟨fun t ht i hi => by rw [hfp_eq_all t ht] at hi; exact (hFO_disj ec hec o ho).1 t ht i hi,
        (hFO_disj ec hec o ho).2⟩
    · rw [hchain_eq, hmap_fo_eq]
      refine ⟨Nd_at, hWT_post.2.2.2, fun o ho j hj => ?_⟩
      rw [nodeExtents_eq hTr_at.1 hcell] at hj
      exact hAT_at o ho j hj
    · simp only [hchain_eq]
      have hworldRefs_eq : worldTableRefs post S = worldTableRefs s S := by
        unfold worldTableRefs recordSlots
        rw [hglob_eq "ws", hglob_eq "bs", hglob_eq "ts",
            show globalTableRoots.map (globN post) = globalTableRoots.map (globN s) by
              simp only [globalTableRoots, List.map, hglob_eq],
            balRecords_eq hWT.1 hcell (hglob_eq "bal_accounts"),
            hglob_eq "journal_n", hglob_eq "journal"]
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
            have hwti_ad := mem_worldTypedIvls_bal (S := S) (Nd := Nd_at) had_mem
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
            exact memW_eq_of_cellHits hcell (by omega) (mem_worldTypedIvls_journal (S := S) (Nd := Nd_at) hjc_ne)
              ⟨by dsimp only; omega, by dsimp only; omega⟩
        dsimp only
        rw [hglob_eq "bs", hglob_eq "ts", hws_sl, hbs_sl, hts_sl, hnest_bs, hnest_ts, hbal_fl, hjrn_mp]
      have hdelEx_iff : ∀ i t, DelExclusive post S (evmChain s) i t ↔ DelExclusive s S (evmChain s) i t := by
        intro i t; unfold DelExclusive; rw [hworldRefs_eq]
        refine and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun hj =>
          forall_congr' fun k => imp_congr_right fun hk => ?_)
        have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
        have hk_ok : k + 8 ≤ 280 ∧ k ∉ headGasUpdateOffs := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl <;> exact ⟨by omega, by decide⟩
        rw [(hrec_eq _ hj_mem).1 k hk_ok.1 hk_ok.2]
      intro i hi
      have hi_mem : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
      have hm_eq := (hrec_eq _ hi_mem).2.1 48 (by omega) (by omega)
      have hmm_eq := (hrec_eq _ hi_mem).2.1 56 (by omega) (by omega)
      have he24_eq := (hrec_eq _ hi_mem).1 24 (by omega) (by decide)
      have htake_eq : ((evmChain s).take (i + 1)).map (fun ec => memW post (ec.1 + 136)) =
          ((evmChain s).take (i + 1)).map (fun ec => memW s (ec.1 + 136)) := by
        apply List.map_congr_left; intro ec hec
        exact (hrec_eq ec (List.mem_of_mem_take hec)).1 136 (by omega) (by decide)
      have hM0 := hMarks i hi; dsimp only at hM0 ⊢
      rw [hm_eq, hmm_eq, he24_eq, hframeScratch_eq _ hi_mem, hfeq, htake_eq]
      obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM0
      refine ⟨m1, m2, m3, m4, ?_, m6, m7, ?_, m9⟩
      · intro j hj hij
        have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
        rw [hframeScratch_eq _ hj_mem, hframeObjects_eq _ hj_mem, hframeLogs_eq _ hj_mem,
            (hrec_eq _ hj_mem).1 112 (by omega) (by decide)]
        exact m5 j hj hij
      · intro t ht
        rw [hfp_eq_all t ht, hdelEx_iff i t]; exact m8 t ht
    · rw [hchain_eq]
      have hcg : ∀ g ∈ EvmBase.coreWorldGlobals, globN post g = globN s g := fun g _ => hglob_eq g
      rw [worldRoleSlots_eq hAs.2 hWT.1 hWT.2.2.1 hcell hcg,
          hframeRoleSlots_eq,
          journalRoleSlots_eq hAs.2 hWT.2.1 hWT.2.2.1 hcell hcg]
      unfold RolesOK at hRoles ⊢
      refine ⟨fun a ha => ?_, hRoles.2⟩
      obtain ⟨haS, hkl⟩ := hRoles.1 a ha
      have htb := ((hWT.1.2.1 a.1 haS).1.1 (a.1, 88) (by simp [htabFootprint])).1
      rw [htab_hdr_eq hcell haS htb 0 (by omega)]; exact ⟨haS, hkl⟩
    · have hsum_le : ((evmChain post).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)).sum ≤
          ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum := hR_le
      omega
  have h112 : memW post (e0 + 112) = memW s (e0 + 112) :=
    (hrec_eq (e0, c0) hhead_mem).1 112 (by omega) (by decide)
  have hw_code : ∀ g k, (g, k) ∈ ([("ws", 16), ("bs", 48), ("ts", 48)] : List (String × Nat)) →
      globN s g ≠ 0 → memW s (globN s g + k) ≠ 0 →
      ∀ p ∈ htabValues s (memW s (globN s g + k)), memW post (p + 8) = memW s (p + 8) := by
    intro g k hgk hgn hdb p hp
    obtain ⟨hin_p, hp64, _, _⟩ := (hC g k hgk hgn hdb).2 p hp
    have hhp_s := hAs.2.2.1
    apply hmemW_ne (p + 8) (by omega)
    intro off hoff heq
    have hin_e0 := (hhead_FW.1 (e0, 280) (by simp)).1.1
    have h1 := hAs.2.2.2.1; have h2 := hAs.2.2.2.2.1
    have hhs : heapLimit ≤ scratchStart := by decide
    unfold Inside at hin_p hin_e0; dsimp only at hin_p hin_e0; omega
  have hcell_eb : EvmBase.SameTypedCells s post S Nd_at :=
    ⟨hcell.1, hcell.2.1, hcell.2.2.1, hcell.2.2.2.1,
     fun a ha hch => by
       by_cases ha8 : a % 8 = 0
       · exact hcell.2.2.2.2.1 a ha ha8 hch
       · have hnot : ¬ ordinaryDomain (BitVec.ofNat 64 a) := by
           rw [M23.ordinaryDomain_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]; omega
         exact hcell.2.2.2.1 _ hnot,
     hcell.2.2.2.2.2⟩
  obtain ⟨hC_post, hM_post⟩ := msgBounded_side_of_sameTypedCells hAs hApost hWT hC hM hcell_eb
    hh (fun g _ => hglob_eq g) h112 hfeq hw_code
  have hB_post : EvmMsgReadyMsgBounded post := by
    refine ⟨hApost, hM_post, S, hInvAt_post, ?_⟩
    exact ⟨by rw [hglob_eq "ev"]; exact (hInvAt_post.2.2.2.2.1 (e0, c0) (by rw [hchain_eq]; exact hhead_mem)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, hC_post⟩
  have hcc : ChainCellsAgree s post := by
    intro ec hec
    obtain ⟨he_eq, hc_eq, _⟩ := hrec_eq ec hec
    exact ⟨he_eq 24 (by omega) (by decide),
           he_eq 32 (by omega) (by decide),
           he_eq 40 (by omega) (by decide),
           hc_eq 56 (by omega) (by omega)⟩
  have hstep : EvmStep [] s post :=
    ⟨⟨hApost, S, hInvAt_post⟩, hh, fun name _ => (congrArg (fun m => m.lookup name) hglob).symm, hchain_eq⟩
  exact ⟨hB_post, ⟨hstep, hcc⟩, h112⟩

/-! ## 3. `D0PreB` `FunSpec` and `Hoare.call0_fall` specs for `charge_gas`, `charge_state_gas`, and `warm_address` -/

theorem store_some_eq_error_d0 {F : Type} {s post : PanSemStateFiniteExact 64 F}
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

theorem add_sat_body_le_sum_d0 {F : Type} (s : PanSemStateFiniteExact 64 F) (aw bw : BitVec 64)
    (ha : s.locals.lookup (ofString "a") = some (.val (.word aw)))
    (hb : s.locals.lookup (ofString "b") = some (.val (.word bw)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_add_sat)).1 =
      some (.returned v)) :
    ∃ rw : BitVec 64, v = .val (.word rw) ∧ rw.toNat ≤ aw.toNat + bw.toNat := by
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
    have haw := aw.isLt
    have hbw := bw.isLt
    have : (18446744073709551615#64 : BitVec 64).toNat = 18446744073709551615 := rfl
    omega
  · simp only [hlt, ↓reduceIte, evaluateHOLFiniteState_skip] at hret
    rw [evaluateHOLFiniteState_return] at hret
    dsimp only [evalHOLExact] at hret
    rw [hs1_s] at hret; dsimp only at hret
    have hsz : sizeOfShapeWithContextHOL s1.structs
        (shapeOfHOLExact (.val (.word (aw + bw)))) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [if_pos hsz] at hret; dsimp only at hret
    injection hret with h1; injection h1 with hv
    refine ⟨aw + bw, hv.symm, ?_⟩
    rw [BitVec.toNat_add]; exact Nat.mod_le _ _

theorem funSpec_charge_gas_msgBounded :
    FunSpec EvmMsgReadyMsgBounded
      (fun s r post => Resumes r →
        EvmMsgReadyMsgBounded post ∧ EvmStepCC [] s post ∧
          post.globals = s.globals ∧
          memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112))
      (ofString "charge_gas") := by
  refine ⟨_, _, _, EvmFrameSpecs.lookup_charge_gas, ?_⟩
  intro F s hcode hB ⟨vals, hl⟩ hnt hres
  have hInv : EvmInv s := evmInv_of_msgBounded hB
  have hlen1 : ∃ v0, vals = [v0] := by
    have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
      originalRuntimeCode.lookup (ofString "charge_gas") vals _ _ _ hl
    simp only [Flapjack.lookupCodeHOLExact, EvmFrameSpecs.lookup_charge_gas] at hx
    rcases vals with _ | ⟨v0, _ | _⟩ <;> simp at hx
    exact ⟨v0, rfl⟩
  obtain ⟨v0, rfl⟩ := hlen1
  obtain ⟨_, _, amtw, rfl, hamt⟩ := one_word_arg_lookup EvmFrameSpecs.lookup_charge_gas hl
  obtain ⟨hb_ev, evw, hevw, hevw_nat⟩ := ev_word_bounds hInv
  have hev64 : evw + BitVec.ofNat 64 64 = BitVec.ofNat 64 (globN s "ev" + 64) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hevw_nat]
  have hev184 : evw + BitVec.ofNat 64 184 = BitVec.ofNat 64 (globN s "ev" + 184) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hevw_nat]
  have herr_abs : ∀ {post0 : PanSemStateFiniteExact 64 F},
      Resumes (some PanSemResultExact.error) →
      EvmMsgReadyMsgBounded post0 ∧ EvmStepCC [] s post0 ∧
        post0.globals = s.globals ∧
        memW post0 (globN s "ev" + 112) = memW s (globN s "ev" + 112) :=
    fun hr => absurd hr EvmFrameSpecs.not_resumes_error
  have hbody : sourceFnBody Guest.Software.guestFn_charge_gas =
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
  revert hres
  rw [hbody, evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
  rcases hgl : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .global (ofString "ev"), .const 64])) with _ | glv
  · dsimp only; exact herr_abs
  · simp only [hgl] at hnt ⊢
    have hgl_w : ∃ glw : BitVec 64, glv = .val (.word glw) ∧ glw.toNat = memW s (globN s "ev" + 64) := by
      simp [evalHOLExact, evalListHOLExact, hevw, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at hgl
      rcases hm : s.memory (evw + 64#64) with ⟨glw⟩
      rw [hm] at hgl
      exact ⟨glw, hgl.2.symm, by unfold memW; rw [← hev64, hm]⟩
    obtain ⟨glw, rfl, hglw_eq⟩ := hgl_w
    have hsh_gl : shapeEqHOL .one (shapeOfHOLExact (.val (.word glw) : ValueHOL 64)) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    rw [if_pos hsh_gl] at hnt ⊢; dsimp only at hnt ⊢
    set s1 := setVarHOLFinite (ofString "gl") (.val (.word glw)) s with hs1
    have hs1_gl : s1.locals.lookup (ofString "gl") = some (.val (.word glw)) := by
      simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs1_amt : s1.locals.lookup (ofString "amount") = some (.val (.word amtw)) := by
      simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hamt,
        show ofString "gl" ≠ ofString "amount" by decide]
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
    have hcmp : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        (.cmp .lower (.var .local (ofString "gl")) (.var .local (ofString "amount"))) =
        some (.val (.word (if glw < amtw then 1 else 0))) := by
      simp [evalHOLExact, hs1_gl, hs1_amt, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hcmp] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hlt : glw < amtw
    · have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
      simp only [hlt, ↓reduceIte, h10] at hnt ⊢
      rw [evaluateHOLFiniteState_raise] at hnt ⊢; dsimp only [evalHOLExact] at hnt ⊢
      cases hs1_esh : s1.eshapes.lookup (ofString "EvmErr") with
      | none => dsimp only; exact herr_abs
      | some sh =>
        dsimp only
        by_cases hcond : shapeOfHOLExact (.val (.word (4 : BitVec 64))) = sh ∧
            sizeOfShapeWithContextHOL s1.structs (shapeOfHOLExact (.val (.word (4 : BitVec 64)))) ≤ 32
        · rw [if_pos hcond]; dsimp only
          intro _
          let post := { (emptyLocalsHOLFinite s1) with
            locals := (emptyLocalsHOLFinite s1).locals.resVarEq (ofString "gl", s.locals.lookup (ofString "gl")) }
          have hp_eq : post = { s with locals := post.locals, clock := post.clock } := rfl
          have hBp : EvmMsgReadyMsgBounded post := by
            rw [hp_eq]; exact localsFree_evmMsgReadyMsgBounded s _ _ hB
          have hstep : EvmStep [] s post :=
            ⟨evmInv_of_msgBounded hBp, by rw [hp_eq]; exact Nat.le_refl _, fun _ _ => rfl,
             by rw [hp_eq]; exact evmChain_with_locals s _ _⟩
          have hcc : ChainCellsAgree s post := by
            intro ec _; exact ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨hBp, ⟨hstep, hcc⟩, rfl, rfl⟩
        · rw [if_neg hcond]; dsimp only; exact herr_abs
    · have hamt_le : amtw.toNat ≤ glw.toNat := by rw [BitVec.lt_def] at hlt; omega
      simp only [hlt, ↓reduceIte, evaluateHOLFiniteState_skip] at hnt ⊢
      rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
      rcases hst1 : evaluateHOLFiniteState s1
          (.store (.op .add [.var .global (ofString "ev"), .const 64])
            (.op .sub [.var .local (ofString "gl"), .var .local (ofString "amount")])) with ⟨r1, s2⟩
      simp only [hst1] at hnt ⊢
      cases r1 with
      | some res1 =>
        have herr1 := store_some_eq_error_d0 hst1; subst herr1
        dsimp only; exact herr_abs
      | none =>
        dsimp only at hnt ⊢
        obtain ⟨w1, hw1_ev, hs2_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s1) (post := s2)
          (gname := "ev") (gbase := globN s "ev") (off := 64) hevw hevw_nat (by omega)
          (fun v hv => by
            simp [evalHOLExact, evalListHOLExact, hs1_gl, hs1_amt, valueIsWord, valueWord, wordOpHOL, wordOp] at hv
            exact ⟨_, hv.symm⟩) hst1
        have hw1_val : w1 = glw - amtw := by
          simp [evalHOLExact, evalListHOLExact, hs1_gl, hs1_amt, valueIsWord, valueWord, wordOpHOL, wordOp] at hw1_ev
          exact hw1_ev.symm
        subst hw1_val
        rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
        rcases hst2 : evaluateHOLFiniteState s2
            (.store (.op .add [.var .global (ofString "ev"), .const 184])
              (.op .add
                [.load .one (.op .add [.var .global (ofString "ev"), .const 184]),
                 .var .local (ofString "amount")])) with ⟨r2, s3⟩
        simp only [hst2] at hnt ⊢
        cases r2 with
        | some res2 =>
          have herr2 := store_some_eq_error_d0 hst2; subst herr2
          dsimp only; exact herr_abs
        | none =>
          dsimp only at hnt ⊢
          obtain ⟨w2, _, hs3_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s2) (post := s3)
            (gname := "ev") (gbase := globN s "ev") (off := 184)
            (by rw [hs2_eq]; exact hevw) hevw_nat (by omega)
            (fun v hv => by
              simp only [evalHOLExact, wordOpHOL] at hv; revert hv
              rcases @evalListHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a)) _ with _ | vs
              · simp
              · dsimp only; split
                · simp only [Option.map]
                  rcases wordOp .add (vs.map valueWord) with _ | w
                  · simp
                  · intro hv; injection hv with hv'; exact ⟨w, hv'.symm⟩
                · simp) hst2
          rw [evaluateHOLFiniteState_return] at hnt ⊢; dsimp only [evalHOLExact] at hnt ⊢
          have hsz0 : sizeOfShapeWithContextHOL s3.structs
              (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
            simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
          rw [if_pos hsz0] at hnt ⊢; dsimp only at hnt ⊢
          intro _
          let post := { (emptyLocalsHOLFinite s3) with
            locals := (emptyLocalsHOLFinite s3).locals.resVarEq (ofString "gl", s.locals.lookup (ofString "gl")) }
          have hGp : GuestInv post := guestInv_congr (s := s)
            (by simp [post, emptyLocalsHOLFinite, hs3_eq, hs2_eq, hs1, setVarHOLFinite])
            (by simp [post, emptyLocalsHOLFinite, hs3_eq, hs2_eq, hs1, setVarHOLFinite])
            (by simp [post, emptyLocalsHOLFinite, hs3_eq, hs2_eq, hs1, setVarHOLFinite])
            (by simp [post, emptyLocalsHOLFinite, hs3_eq, hs2_eq, hs1, setVarHOLFinite])
            hInv.1.1
          have hglob_p : post.globals = s.globals := by
            simp [post, emptyLocalsHOLFinite, hs3_eq, hs2_eq, hs1, setVarHOLFinite]
          have hbe_p : post.be = s.be := by
            simp [post, emptyLocalsHOLFinite, hs3_eq, hs2_eq, hs1, setVarHOLFinite]
          have hm64 : memW post (globN s "ev" + 64) = memW s (globN s "ev" + 64) - amtw.toNat := by
            change memW s3 (globN s "ev" + 64) = _
            rw [hs3_eq, R14Shards.OpHandlersA.memW_updW_ne s2 _ _ w2 (by omega) (by omega) (by omega),
                hs2_eq, R14Shards.OpHandlersA.memW_updW_same s1 _ (glw - amtw),
                BitVec.toNat_sub_of_le (BitVec.le_def.2 hamt_le), hglw_eq]
          have hm192 : memW post (globN s "ev" + 192) = memW s (globN s "ev" + 192) := by
            change memW s3 (globN s "ev" + 192) = memW s (globN s "ev" + 192)
            rw [hs3_eq, R14Shards.OpHandlersA.memW_updW_ne s2 _ _ w2 (by omega) (by omega) (by omega),
                hs2_eq, R14Shards.OpHandlersA.memW_updW_ne s1 _ _ (glw - amtw) (by omega) (by omega) (by omega)]
            rfl
          have hmem_out : ∀ x : BitVec 64,
              (∀ off ∈ headGasUpdateOffs, x ≠ BitVec.ofNat 64 (globN s "ev" + off)) →
              post.memory x = s.memory x := by
            intro x hx
            change s3.memory x = s.memory x
            rw [hs3_eq, hs2_eq]
            have hn184 : x ≠ BitVec.ofNat 64 (globN s "ev" + 184) := hx 184 (by decide)
            have hn64 : x ≠ BitVec.ofNat 64 (globN s "ev" + 64) := hx 64 (by decide)
            simp [R14Shards.OpHandlersA.updW, hn184, hn64, hs1, setVarHOLFinite]
          obtain ⟨hBp, hstepCC, h112⟩ := evmMsgReadyMsgBounded_of_head_gas_mem hB hGp hglob_p hbe_p hmem_out
            (by rw [hm64, hm192]; omega)
          exact ⟨hBp, hstepCC, hglob_p, h112⟩


end MsB4c1GasWarmRo

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
