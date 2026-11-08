import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.FrameStartFinishChild
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M21.dm_memcpy
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.FrameStartFinishChildStep23

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8Contracts.M23 (EvmStep EvmKeeps EvmAvoids GlobalsKept)
open InitECandidate.Solver.Wave8GuestInv.R11Shards

def srdSetCallees_fc (f : MlS) : Bool :=
  f == ofString "trap_with" || f == ofString "alloc" ||
    f == ofString "memcpy" || f == ofString "set_retdata"

theorem srdSetCallees_fc_good :
    ∀ f, srdSetCallees_fc f = true → ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup f values =
        some (body, callee, rs) →
      StateRestoreEpilogue.noCatchableRaise srdSetCallees_fc body = true := by
  intro f hf values body callee rs hfound
  obtain ⟨params, rs', hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
  simp only [srdSetCallees_fc, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with ((rfl | rfl) | rfl) | rfl
  · have hl := lookup_of_guestAst_getElem 3 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_trap_with) rfl
    change originalRuntimeCode.lookup (ofString "trap_with") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_alloc) rfl
    change originalRuntimeCode.lookup (ofString "alloc") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_memcpy) rfl
    change originalRuntimeCode.lookup (ofString "memcpy") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_set_retdata_fc
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl

theorem call_memcpy_bounds_srd {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dstExp srcExp nExp : ExpHOL 64)
    (dst0 src0 n0 : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (hG : GuestInv s)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) srcExp =
      some (.val (.word src0)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n0)))
    (post : PanSemStateFiniteExact 64 F)
    (hout : evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp]) = (none, post)) :
    post.locals = s.locals ∧
    (0 < n0.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ heapEnd) := by
  have hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp])).1 ≠ some .timeOut := by
    rw [hout]; simp
  have hmc_bre := InitECandidate.Solver.Wave8GuestInv.M11.eval_call_memcpy_bre
    s dstExp srcExp nExp dst0 src0 n0 [(dst0.toNat, n0.toNat)]
    hcode hG.memaddrs hdst hsrc hn
    (fun _ => ⟨(dst0.toNat, n0.toNat), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩) hnt
  have hloc : post.locals = s.locals := by
    have h1 := hmc_bre.1 (by rw [hout])
    rw [hout] at h1; exact h1.2
  refine ⟨hloc, fun hn_pos => ?_⟩
  obtain ⟨params_mc, body_mc, ret_mc, hlk_mc, hspec_mc⟩ :=
    InitECandidate.Solver.Wave8GuestInv.M21.dm_memcpy
  have hout' := hout
  rw [evaluateHOLFiniteState_call] at hout'
  have hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) [dstExp, srcExp, nExp] =
      some [.val (.word dst0), .val (.word src0), .val (.word n0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hsrc, hn]
  rw [hargs] at hout'; dsimp only at hout'
  have hlook := pan_three_word_lookup s.code.lookup (ofString "memcpy")
    (ofString "dst") (ofString "src") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_memcpy) dst0 src0 n0
    (by decide) (by decide) (by decide)
    (by rw [hcode]; exact InitECandidate.Solver.Wave8GuestInv.M11.lookup_memcpy)
  rw [hlook] at hout'; dsimp only at hout'
  have hlk_inst : originalRuntimeCode.lookup (ofString "memcpy") =
      some ([(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memcpy, .one) :=
    InitECandidate.Solver.Wave8GuestInv.M11.lookup_memcpy
  rw [hlk_inst] at hlk_mc
  injection hlk_mc with hlk_tup
  obtain ⟨rfl, hbr_eq⟩ := Prod.mk.inj hlk_tup
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hbr_eq
  by_cases hclk0 : s.clock = 0
  · rw [if_pos hclk0] at hout'; simp at hout'
  · rw [if_neg hclk0] at hout'
    let cmap : HolFiniteMapExact MlS (ValueHOL 64) :=
      (((HolFiniteMapExact.empty.update (ofString "dst", .val (.word dst0))).update
        (ofString "src", .val (.word src0))).update (ofString "n", .val (.word n0)))
    let ent := callEntryStateHOLFinite s cmap
    have hent_code : ent.code = originalRuntimeCode := hcode
    have hent_G : GuestInv ent :=
      ⟨hG.code, hG.memaddrs, hG.shMemaddrs, hG.baseAddr⟩
    have hlook0 := hlook
    rw [hcode] at hlook0
    rcases hrun_mc : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_memcpy) with ⟨rmc, smc_b⟩
    have hrun_mc' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_memcpy) = (rmc, smc_b) := hrun_mc
    rw [hrun_mc'] at hout'
    cases rmc with
    | none => simp at hout'
    | some rr =>
      cases rr with
      | returned rv =>
        have hent_dst : locN ent "dst" = dst0.toNat := by
          unfold locN
          have h1 : ofString "n" ≠ ofString "dst" := by decide
          have h2 : ofString "src" ≠ ofString "dst" := by decide
          simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                h1, h2, Ne.symm h1, Ne.symm h2]
        have hent_n : locN ent "n" = n0.toNat := by
          unfold locN
          simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hins := hspec_mc ent hent_code hent_G
          ⟨[.val (.word dst0), .val (.word src0), .val (.word n0)], hlook0⟩
          (by rw [hrun_mc]; simp)
          (Or.inl ⟨rv, by rw [hrun_mc]⟩)
          (by dsimp only; rw [hent_n]; exact hn_pos)
        dsimp only [Inside] at hins
        rw [hent_dst, hent_n] at hins
        exact hins
      | _ => simp at hout'

private theorem take_succ_cons_srd_fc {α : Type} (a : α) (t : List α) (n : Nat) :
    (a :: t).take (n + 1) = a :: t.take n := rfl

private theorem drop_succ_cons_srd_fc {α : Type} (a : α) (t : List α) (n : Nat) :
    (a :: t).drop (n + 1) = t.drop n := rfl

private theorem mem_of_mem_take_srd_fc {α : Type} {l : List α} {n : Nat} {a : α}
    (h : a ∈ l.take n) : a ∈ l := by
  induction n generalizing l with
  | zero => exact absurd h (by simp)
  | succ n ih =>
    cases l with
    | nil => exact absurd h (by simp)
    | cons b t =>
      rw [take_succ_cons_srd_fc, List.mem_cons] at h
      rcases h with h | h
      · exact List.mem_cons.2 (Or.inl h)
      · exact List.mem_cons.2 (Or.inr (ih h))

private theorem mem_of_mem_drop_srd_fc {α : Type} {l : List α} {n : Nat} {a : α}
    (h : a ∈ l.drop n) : a ∈ l := by
  induction n generalizing l with
  | zero => simpa using h
  | succ n ih =>
    cases l with
    | nil => exact absurd h (by simp)
    | cons b t =>
      rw [drop_succ_cons_srd_fc] at h
      exact List.mem_cons.2 (Or.inr (ih h))

private theorem pairwise_take_srd_fc {α : Type} {R : α → α → Prop} {l : List α}
    (h : l.Pairwise R) (n : Nat) : (l.take n).Pairwise R := by
  induction n generalizing l with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
    cases l with
    | nil => exact List.Pairwise.nil
    | cons a t =>
      obtain ⟨ha, ht⟩ := List.pairwise_cons.1 h
      rw [take_succ_cons_srd_fc]
      exact List.pairwise_cons.2 ⟨fun b hb => ha b (mem_of_mem_take_srd_fc hb), ih ht⟩

private theorem pairwise_drop_srd_fc {α : Type} {R : α → α → Prop} {l : List α}
    (h : l.Pairwise R) (n : Nat) : (l.drop n).Pairwise R := by
  induction n generalizing l with
  | zero => simpa using h
  | succ n ih =>
    cases l with
    | nil => exact h
    | cons a t => exact ih (List.pairwise_cons.1 h).2

theorem evmInvAt_of_head_ret_set_fc {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    {p' cap' : Nat}
    (hAs : ArenaReady s)
    (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S)
    (hGp : GuestInv post)
    (hglob : post.globals = s.globals)
    (hbe : post.be = s.be)
    (hmem_out : ∀ x : BitVec 64,
      (∀ off ∈ headRetZeroOffs, x ≠ BitVec.ofNat 64 (globN s "ev" + off)) →
      post.memory x = s.memory x)
    (hcap_pos : 0 < cap')
    (h216 : memW post (globN s "ev" + 216) = cap')
    (h144 : memW post (globN s "ev" + 144) = p')
    (hret_in : Inside (p', (cap' + 15) / 8 * 8) sourceBase (globN s "heap_ptr"))
    (hret_wok : WordsOK s (p', (cap' + 15) / 8 * 8))
    (hret_disj_fo : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, Disj (p', (cap' + 15) / 8 * 8) o)
    (hret_disj_ht : ∀ t ∈ S, ∀ o ∈ htabFootprint s t, Disj (p', (cap' + 15) / 8 * 8) o)
    (hret_disj_fix : ∀ o ∈ fixedObjects s, Disj (p', (cap' + 15) / 8 * 8) o)
    (hret_avoids : AvoidsTries s S [(p', (cap' + 15) / 8 * 8)])
    (hret_disj_msg : ∀ ec ∈ evmChain s, Disj (memW s (ec.1 + 112), 176) (p', (cap' + 15) / 8 * 8))
    (hsp_le : memW post (globN s "ev" + 16) ≤ memW s (globN s "ev" + 232))
    (hgas_le : memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) +
      (((evmChain s).tail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum) + 1 < 2 ^ 64) :
    ArenaReady post ∧
    InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt post S ∧
    evmChain post = evmChain s ∧
    fixedObjects post = fixedObjects s ∧
    (∀ t ∈ S, htabFootprint post t = htabFootprint s t) ∧
    (∀ ec ∈ evmChain s,
      frameScratch post ec = frameScratch s ec ∧
      frameLogs post ec = frameLogs s ec ∧
      memW post (ec.1 + 24) = memW s (ec.1 + 24) ∧
      memW post (ec.1 + 32) = memW s (ec.1 + 32) ∧
      memW post (ec.1 + 40) = memW s (ec.1 + 40) ∧
      memW post (ec.1 + 112) = memW s (ec.1 + 112) ∧
      memW post (ec.2 + 56) = memW s (ec.2 + 56)) ∧
    (∀ ec ∈ (evmChain s).tail, frameObjects post ec = frameObjects s ec) ∧
    frameRet post (globN s "ev", globN s "cur_cont") = (p', (cap' + 15) / 8 * 8) ∧
    frameObjects post (globN s "ev", globN s "cur_cont") =
      (frameObjects s (globN s "ev", globN s "cur_cont")).take 6 ++
      ([(p', (cap' + 15) / 8 * 8)] ++ (frameObjects s (globN s "ev", globN s "cur_cont")).drop 7) ∧
    OpDispatchSpec.evmR post =
      memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) +
        (((evmChain s).tail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum) := by
  set ret' : Ivl := (p', (cap' + 15) / 8 * 8)
  obtain ⟨hW, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW, hFO_pw, hFO_disj, hAT, hMarks, hRoles, _⟩ := hInv
  obtain ⟨Nd_old, hTr_old, hAT_old⟩ := hAT
  obtain ⟨Nd_r, hTr_r, hd_r⟩ := hret_avoids
  obtain ⟨hTr_at, hsub_at⟩ := R11Shards.triesTypedWith_inter hTr_old hTr_r
  set Nd_at := Nd_old.filter (fun n => decide (n ∈ Nd_r))
  have hAT_at : ∀ o ∈ ((evmChain s).map (frameObjects s)).flatten,
      ∀ j ∈ nodeExtents s Nd_at, Disj o j :=
    fun o ho j hj => hAT_old o ho j (hsub_at j hj).1
  have hret_nodes : ∀ j ∈ nodeExtents s Nd_at, Disj ret' j :=
    fun j hj => hd_r ret' (by simp) j (hsub_at j hj).2
  have hWT : InitECandidate.Solver.Wave8Contracts.M23.WorldTypedWith s S Nd_at :=
    ⟨hW.1, hW.2.1, hW.2.2.1, hTr_at⟩
  set e0 := globN s "ev"
  set c0 := globN s "cur_cont"
  have hch_cons : ∃ tl, evmChain s = (e0, c0) :: tl := ⟨_, rfl⟩
  obtain ⟨chTail, hch_eq⟩ := hch_cons
  have hhead_mem : (e0, c0) ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_self
  have hhead_FW := hFW_all _ hhead_mem
  obtain ⟨hb1, _, _, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hAs.2 hhead_FW
  dsimp only at hb1
  have he0_8 : e0 % 8 = 0 := (hhead_FW.1 (e0, 280) (by simp)).2.1
  have hdom_eq : post.memaddrs = s.memaddrs := hGp.memaddrs.trans hAs.1.memaddrs.symm
  have hoff_props : ∀ off ∈ headRetZeroOffs,
      off + 8 ≤ 280 ∧ off % 8 = 0 ∧ s.memaddrs (BitVec.ofNat 64 (e0 + off)) := by
    intro off hoff
    have hdiv : off + 8 ≤ 280 ∧ off % 8 = 0 ∧ off / 8 < 280 / 8 ∧ 8 * (off / 8) = off := by
      revert off hoff; decide
    obtain ⟨_, hdom, _⟩ := (hhead_FW.1 (e0, 280) (by simp)).2.2.2 (off / 8) hdiv.2.2.1
    exact ⟨hdiv.1, hdiv.2.1, by simpa [hdiv.2.2.2] using hdom⟩
  have heff : InitECandidate.Solver.Wave8Contracts.M23.ByteRegionEffect s post [(e0, 280)] := by
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
        rw [panByteAlign_toNat64,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
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
  have hrec_disj_wti : ∀ i ∈ InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls s S Nd_at,
      i.2 = 0 ∨ Disj (e0, 280) i := by
    intro i hi
    unfold InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls at hi
    simp only [List.mem_append] at hi
    rcases hi with ((((h1 | h2) | h3) | h4) | h5) | h6
    · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
      exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).1 t ht i hfp)
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
      exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _
        (InitECandidate.Solver.Wave8Contracts.M23.typedRec_in_fixedObjects s hr))
    · simp only [List.mem_singleton] at h3; subst h3
      have hfix_j : (if globN s "journal_cap" = 0 then 0 else globN s "journal",
          32 * globN s "journal_cap") ∈ fixedObjects s := by
        unfold fixedObjects
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))
      exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _ hfix_j)
    · exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _
        (InitECandidate.Solver.Wave8Contracts.M23.blockOut_in_fixedObjects h4))
    · exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _
        (InitECandidate.Solver.Wave8Contracts.M23.bal_in_fixedObjects h5))
    · exact Or.inr (hAT_at _ (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨_, hhead_mem, rfl⟩, hrec_fo⟩) i h6)
  have hcell : InitECandidate.Solver.Wave8Contracts.M23.SameTypedCells s post S Nd_at :=
    InitECandidate.Solver.Wave8Contracts.M23.ByteRegionEffect.sameTypedCells
      (Rl := []) (extra := [(e0, 280)]) hAs.1.memaddrs hWT
      (fun _ h => by simp at h)
      (fun x hx => by simp at hx; subst hx; exact hrec_disj_wti)
      (by simpa using heff)
  have hfeq := InitECandidate.Solver.Wave8Contracts.M23.fixedObjects_eq_of_nonHeapGlobalsKept
    hAs.2 hWT.1 hWT.2.2.1 hcell (fun name _ _ _ => by rw [hglob])
  have hFT_post := InitECandidate.Solver.Wave8Contracts.M23.fixedTyped_of_eq hApost hWT.2.2.1 hh hsc hfeq
  obtain ⟨hWT_post, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.worldTypedWith_congr_w1 hAs hApost hh hsc
    (fun g _ => hglob_eq g) hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hW_post : WorldTyped post S :=
    ⟨hWT_post.1, hWT_post.2.1, hWT_post.2.2.1, Nd_at, hWT_post.2.2.2⟩
  have hmemW_ne : ∀ a : Nat, a < 2 ^ 64 →
      (∀ off ∈ headRetZeroOffs, a ≠ e0 + off) → memW post a = memW s a := by
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
      exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by
        unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
    · refine ⟨hpw_head_tail.2 _ hrec_fo ec htail _ (by simp [frameObjects]),
        hpw_head_tail.2 _ hrec_fo ec htail _ (by simp [frameObjects]),
        hpw_head_tail.2 _ hrec_fo ec htail _ (by simp [frameObjects]),
        fun i hi => hpw_head_tail.2 _ hrec_fo ec htail _ ?_⟩
      unfold frameObjects; apply List.mem_append_right
      unfold frameLogObjects; dsimp only
      exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by
        unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
  have htail_rec_eq : ∀ ec ∈ chTail, ∀ k, k + 8 ≤ 280 → memW post (ec.1 + k) = memW s (ec.1 + k) := by
    intro ec htail k hk
    have hFW := hFW_all ec (by rw [hch_eq]; exact List.mem_cons_of_mem _ htail)
    obtain ⟨hb_e, _, _, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hAs.2 hFW
    apply hmemW_ne (ec.1 + k) (by omega)
    intro off hoff heq
    have hp := hoff_props off hoff
    have hd := hpw_head_tail.2 (e0, 280) hrec_fo ec htail (ec.1, 280) (by simp [frameObjects])
    rcases hd with h0 | h0 | h1 | h2 <;> dsimp only at * <;> omega
  have hrec_eq : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → k ∉ headRetZeroOffs → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → k % 8 = 0 → memW post (ec.2 + k) = memW s (ec.2 + k)) ∧
      (∀ k, k + 8 ≤ 24 → k % 8 = 0 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨hb_e, hb_c, hb_88, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hAs.2 hFW
    have hc8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
    have h88_8 : (memW s (ec.1 + 88)) % 8 = 0 := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).2.1
    obtain ⟨hd_c, hd_88, _, _⟩ := hdisj_e0_nonrec ec hec
    refine ⟨?_,
      fun k hk hk8 => R14Shards.OpHandlersA.memW_eq_of_disj_eff heff hRl8_e0 hb_c hc8 hk8 hk
        (fun x hx => by simp at hx; subst hx; exact hd_c),
      fun k hk hk8 => R14Shards.OpHandlersA.memW_eq_of_disj_eff heff hRl8_e0 hb_88 h88_8 hk8 hk
        (fun x hx => by simp at hx; subst hx; exact hd_88)⟩
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
  have hframeRet_head : frameRet post (e0, c0) = ret' := by
    unfold frameRet
    rw [h216, h144, if_neg (by omega)]
  have hhead_ne_tail : (e0, c0) ∉ chTail := by
    intro hmem
    have hd := hpw_head_tail.2 (e0, 280) (by simp [frameObjects]) (e0, c0) hmem
      (e0, 280) (by simp [frameObjects])
    rcases hd with h0 | h0 | h1 | h2 <;> dsimp only at * <;> omega
  have hframeRet_eq : ∀ ec ∈ evmChain s, ec ≠ (e0, c0) → frameRet post ec = frameRet s ec := by
    intro ec hec hne
    have htail : ec ∈ chTail := by
      rw [hch_eq, List.mem_cons] at hec
      rcases hec with rfl | htail
      · exact absurd rfl hne
      · exact htail
    have h216t := htail_rec_eq ec htail 216 (by omega)
    have h144t := htail_rec_eq ec htail 144 (by omega)
    unfold frameRet
    rw [h216t, h144t]
  have hlogs_congr : ∀ ec ∈ evmChain s,
      frameLogObjects post ec = frameLogObjects s ec ∧ LogsListOK post (memW post (ec.1 + 88)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨_, _, _, hfob⟩ := InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hAs.2 hFW
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
      exact R14Shards.OpHandlersA.memW_eq_of_disj_eff heff hRl8_e0 hfl_b hfl_8 (by omega)
        (by unfold frameLogs; dsimp only; omega)
        (fun x hx => by simp at hx; subst hx; exact hd_fl)
    have hlr_eq : ∀ i (hi : i < memW s (memW s (ec.1 + 88) + 8)) off, off + 8 ≤ 40 → off % 8 = 0 →
        memW post (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + off) =
          memW s (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + off) := by
      intro i hi off hoff hoff8
      have hlr_in : (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40) ∈ frameObjects s ec := by
        unfold frameObjects; apply List.mem_append_right
        unfold frameLogObjects; dsimp only
        exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by
          unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
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
      exact R14Shards.OpHandlersA.memW_eq_of_disj_eff heff hRl8_e0 hlr_b hlr_8 hoff8 hoff
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
        refine ⟨(R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 hw_l,
          InitECandidate.Solver.Wave8Contracts.M23.allocated_mono hh hsc hal_l,
          by rw [hl8]; exact hlt28, by rw [hl8, hl16]; exact hle_cap, fun i hi => ?_⟩
        rw [hl8] at hi; rw [hl0]
        obtain ⟨hwa, hle⟩ := hent i hi
        refine ⟨(R14Shards.OpHandlersA.wordAt_congr_dom hdom_eq).2 hwa, ?_⟩
        rw [harr_eq i hi]
        have r0 := hlr_eq i hi 0 (by omega) (by omega)
        have r8 := hlr_eq i hi 8 (by omega) (by omega)
        have r16 := hlr_eq i hi 16 (by omega) (by omega)
        have r24 := hlr_eq i hi 24 (by omega) (by omega)
        have r32 := hlr_eq i hi 32 (by omega) (by omega)
        simp only [Nat.add_zero] at r0
        unfold LogEntryOK at hle ⊢
        rw [r0, r8, r16, r24, r32, hglob_eq "heap_ptr"]
        exact ⟨(R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 hle.1, hle.2⟩
  have hframeObjects_eq : ∀ ec ∈ evmChain s, ec ≠ (e0, c0) →
      frameObjects post ec = frameObjects s ec := by
    intro ec hec hne
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameObjects
    rw [he_eq 8 (by omega) (by decide), he_eq 232 (by omega) (by decide),
        he_eq 24 (by omega) (by decide), he_eq 40 (by omega) (by decide),
        he_eq 88 (by omega) (by decide),
        hframeLogs_eq ec hec, hframeRet_eq ec hec hne, (hlogs_congr ec hec).1]
  have hframeObjects_head : frameObjects post (e0, c0) =
      (frameObjects s (e0, c0)).take 6 ++ ([ret'] ++ (frameObjects s (e0, c0)).drop 7) := by
    have hhead_mem' : (e0, c0) ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_self
    obtain ⟨he_eq, _, _⟩ := hrec_eq (e0, c0) hhead_mem'
    unfold frameObjects
    rw [he_eq 8 (by omega) (by decide), he_eq 232 (by omega) (by decide),
        he_eq 24 (by omega) (by decide), he_eq 40 (by omega) (by decide),
        he_eq 88 (by omega) (by decide),
        hframeLogs_eq (e0, c0) hhead_mem', hframeRet_head,
        (hlogs_congr (e0, c0) hhead_mem').1]
    rfl
  have hframeScratch_eq : ∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameScratch
    rw [he_eq 8 (by omega) (by decide), he_eq 232 (by omega) (by decide),
        he_eq 88 (by omega) (by decide)]
  have hfo_post_sub : ∀ o ∈ ((evmChain s).map (frameObjects post)).flatten,
      o = ret' ∨ o ∈ ((evmChain s).map (frameObjects s)).flatten := by
    intro o ho
    rw [List.mem_flatten] at ho ⊢
    obtain ⟨L, hL, hoL⟩ := ho
    obtain ⟨ec, hec, rfl⟩ := List.mem_map.1 hL
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with hec | htail
    · rw [hec] at hoL
      rw [hframeObjects_head] at hoL
      rcases List.mem_append.1 hoL with hoL | hoL
      · exact Or.inr ⟨frameObjects s (e0, c0),
          List.mem_map.2 ⟨(e0, c0), by rw [hch_eq]; exact List.mem_cons_self, rfl⟩,
          mem_of_mem_take_srd_fc hoL⟩
      · rcases List.mem_append.1 hoL with ho0 | hoL
        · exact Or.inl (List.mem_singleton.1 ho0)
        · exact Or.inr ⟨frameObjects s (e0, c0),
            List.mem_map.2 ⟨(e0, c0), by rw [hch_eq]; exact List.mem_cons_self, rfl⟩,
            mem_of_mem_drop_srd_fc hoL⟩
    · exact Or.inr ⟨frameObjects s ec,
        List.mem_map.2 ⟨ec, by rw [hch_eq]; exact List.mem_cons.2 (Or.inr htail), rfl⟩,
        by rw [← hframeObjects_eq ec (by rw [hch_eq]; exact List.mem_cons.2 (Or.inr htail))
          (fun heq => hhead_ne_tail (heq ▸ htail))]; exact hoL⟩
  have hframeRoleSlots_eq : frameRoleSlots post (evmChain s) = frameRoleSlots s (evmChain s) := by
    unfold frameRoleSlots; apply List.flatMap_congr; intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    rw [he_eq 136 (by omega) (by decide), he_eq 168 (by omega) (by decide),
        he_eq 176 (by omega) (by decide)]
  have hfp_eq_all : ∀ t ∈ S, htabFootprint post t = htabFootprint s t :=
    fun t ht => InitECandidate.Solver.Wave8Contracts.M23.htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1
  have htail_eq_s : (evmChain s).tail = chTail := by rw [hch_eq]; rfl
  have htail_sum_eq :
      (chTail.map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)) =
        (chTail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)) := by
    apply List.map_congr_left; intro ec htail
    rw [htail_rec_eq ec htail 64 (by omega), htail_rec_eq ec htail 192 (by omega)]
  have hR_val : OpDispatchSpec.evmR post =
      memW post (e0 + 64) + memW post (e0 + 192) +
        (((evmChain s).tail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum) := by
    unfold OpDispatchSpec.evmR
    rw [hchain_eq, hch_eq, List.map_cons, List.sum_cons, htail_sum_eq, List.tail_cons]
  refine ⟨hApost, ?_, hchain_eq, hfeq, hfp_eq_all, ?_, ?_, ?_, ?_, hR_val⟩
  · unfold InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt
    refine ⟨hW_post, ?_⟩
    dsimp only; rw [hchain_eq]
    refine ⟨hch_ne, hch_len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨ec, hec, hk0⟩ := hch_last
      have hec_mem := List.mem_of_mem_getLast? hec
      exact ⟨ec, hec, by rw [(hrec_eq ec hec_mem).2.1 16 (by omega) (by omega)]; exact hk0⟩
    · intro ec hec
      obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
      obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, _, c17⟩ := hFW_all ec hec
      have hlo_ok := (hlogs_congr ec hec).2
      have hmsg_ok : MsgOwned post S (memW post (ec.1 + 112)) := by
        rw [he_eq 112 (by omega) (by decide)]
        obtain ⟨hal_m, hw_m, hdt, hdf, hdfo, Nd_m, hTr_m, hdj_m⟩ := c17
        obtain ⟨hTr_int, hsub_int⟩ := R11Shards.triesTypedWith_inter hTr_at hTr_m
        set Ndi := Nd_at.filter (fun n => decide (n ∈ Nd_m))
        have hcell_i : InitECandidate.Solver.Wave8Contracts.M23.SameTypedCells s post S Ndi := by
          have hwti_sub : ∀ i ∈ InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls s S Ndi,
              i ∈ InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls s S Nd_at := by
            intro i hi; unfold InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls at hi ⊢
            rcases List.mem_append.1 hi with hpre | hne
            · exact List.mem_append_left _ hpre
            · apply List.mem_append_right; unfold nodeExtents at hne ⊢
              obtain ⟨n, hn, hnx⟩ := List.mem_flatMap.1 hne
              exact List.mem_flatMap.2 ⟨n, (List.mem_filter.1 hn).1, hnx⟩
          refine ⟨hcell.1, hcell.2.1, hcell.2.2.1, hcell.2.2.2.1,
            fun a ha ha8 ⟨i, hi, h1, h2⟩ => hcell.2.2.2.2.1 a ha ha8 ⟨i, hwti_sub i hi, h1, h2⟩,
            fun b hb ⟨i, hi, h1, h2⟩ => hcell.2.2.2.2.2 b hb ⟨i, hwti_sub i hi, h1, h2⟩⟩
        obtain ⟨hWT_i_post, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.worldTypedWith_congr_w1 hAs hApost hh hsc
          (fun g _ => hglob_eq g) hcell_i ⟨hWT.1, hWT.2.1, hWT.2.2.1, hTr_int⟩
          ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
        have hdisj_post : ∀ ec' ∈ evmChain post, ∀ o ∈ frameObjects post ec',
            Disj (memW s (ec.1 + 112), 176) o := by
          rw [hchain_eq]
          intro ec' hec' o ho
          by_cases hhead' : ec' = (e0, c0)
          · rw [hhead'] at ho
            rw [hframeObjects_head] at ho
            rcases List.mem_append.1 ho with ho | ho
            · exact hdfo (e0, c0) (by rw [hch_eq]; exact List.mem_cons_self) o
                (mem_of_mem_take_srd_fc ho)
            · rcases List.mem_append.1 ho with ho0 | ho
              · rw [List.mem_singleton.1 ho0]
                exact hret_disj_msg ec hec
              · exact hdfo (e0, c0) (by rw [hch_eq]; exact List.mem_cons_self) o
                  (mem_of_mem_drop_srd_fc ho)
          · rw [hframeObjects_eq ec' hec' hhead'] at ho
            exact hdfo ec' hec' o ho
        refine ⟨InitECandidate.Solver.Wave8Contracts.M23.allocated_mono hh hsc hal_m,
          (R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 hw_m,
          fun t ht i hi => by rw [hfp_eq_all t ht] at hi; exact hdt t ht i hi,
          by rw [hfeq]; exact hdf,
          hdisj_post,
          Ndi, hWT_i_post.2.2.2, fun o ho j hj => ?_⟩
        rw [InitECandidate.Solver.Wave8Contracts.M23.nodeExtents_eq hTr_int.1 hcell_i] at hj
        exact hdj_m o ho j (hsub_int j hj).2
      have hc5' : memW post (ec.1 + 16) ≤ memW post (ec.1 + 232) := by
        rw [he_eq 232 (by omega) (by decide)]
        have hec' := hec
        rw [hch_eq, List.mem_cons] at hec'
        rcases hec' with rfl | htail
        · exact hsp_le
        · rw [htail_rec_eq ec htail 16 (by omega)]; exact c5
      unfold FrameWF; dsimp only
      rw [he_eq 8 (by omega) (by decide), he_eq 232 (by omega) (by decide),
          he_eq 88 (by omega) (by decide), he_eq 24 (by omega) (by decide),
          he_eq 40 (by omega) (by decide),
          he_eq 32 (by omega) (by decide), he_eq 136 (by omega) (by decide),
          he_eq 168 (by omega) (by decide), he_eq 176 (by omega) (by decide),
          h88_eq 16 (by omega) (by omega), h88_eq 8 (by omega) (by omega),
          hframeLogs_eq ec hec,
          hglob_eq "scratch_ptr", hglob_eq "frame_mem_ptr", hglob_eq "heap_ptr", hglob_eq "evm_empty"]
      rw [he_eq 88 (by omega) (by decide)] at hlo_ok
      have hc5_rw : memW post (ec.1 + 16) ≤ memW s (ec.1 + 232) := by
        simpa [he_eq 232 (by omega) (by decide)] using hc5'
      refine ⟨fun i hi => ⟨(c1 i hi).1, (R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 (c1 i hi).2⟩,
        c2, (R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 c3, c4, hc5_rw, c6, c7, c8, c9, c10, c11, c12,
        c13, (R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 c14, ?_, hlo_ok, hmsg_ok⟩
      rw [hch_eq, List.mem_cons] at hec
      rcases hec with rfl | htail
      · rw [hframeRet_head]
        exact Or.inr ⟨hret_in, (R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 hret_wok⟩
      · rw [htail_rec_eq ec htail 216 (by omega), htail_rec_eq ec htail 144 (by omega),
          hframeRet_eq ec (by rw [hch_eq]; exact List.mem_cons.2 (Or.inr htail))
            (fun heq => hhead_ne_tail (heq ▸ htail))]
        rcases c15 with h0 | ⟨hin, hw⟩
        · exact Or.inl h0
        · exact Or.inr ⟨hin, (R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 hw⟩
    · intro ec hec
      have hec_tail : ec ∈ chTail := by rwa [htail_eq_s] at hec
      unfold FrameRoom
      rw [htail_rec_eq ec hec_tail 16 (by omega),
          htail_rec_eq ec hec_tail 232 (by omega)]
      exact hFR_all ec hec
    · intro i hi
      have hi0 : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
      have hi1 : (evmChain s)[i + 1] ∈ evmChain s := List.getElem_mem _
      rw [(hrec_eq _ hi0).2.1 80 (by omega) (by omega),
          (hrec_eq _ hi0).2.1 72 (by omega) (by omega),
          (hrec_eq _ hi1).1 40 (by omega) (by decide)]
      exact hRW i hi
    · rw [hch_eq, List.map_cons, List.flatten_cons]
      rw [hframeObjects_head]
      have htail_map_eq : chTail.map (frameObjects post) = chTail.map (frameObjects s) :=
        List.map_congr_left (fun ec htail =>
          hframeObjects_eq ec (by rw [hch_eq]; exact List.mem_cons.2 (Or.inr htail))
            (fun heq => hhead_ne_tail (heq ▸ htail)))
      rw [htail_map_eq]
      have hpw0 := hFO_pw
      rw [hch_eq, List.map_cons, List.flatten_cons] at hpw0
      obtain ⟨hpwL, hpwT, hcross⟩ := List.pairwise_append.1 hpw0
      rw [show [ret'] ++ (frameObjects s (e0, c0)).drop 7 =
          ret' :: (frameObjects s (e0, c0)).drop 7 from rfl]
      rw [List.append_assoc]
      have hdisj_symm : ∀ {a b : Ivl}, Disj a b → Disj b a := by
        intro a b h
        rcases h with h0 | h0 | h1 | h2
        · exact Or.inr (Or.inl h0)
        · exact Or.inl h0
        · exact Or.inr (Or.inr (Or.inr h1))
        · exact Or.inr (Or.inr (Or.inl h2))
      have hcross_td : ∀ {l : List Ivl}, l.Pairwise Disj → ∀ n,
          ∀ x ∈ l.take n, ∀ y ∈ l.drop (n + 1), Disj x y := by
        intro l hl n
        induction n generalizing l with
        | zero => intro x hx; exact absurd hx (by simp)
        | succ n ih =>
          cases l with
          | nil => intro x hx; exact absurd hx (by simp)
          | cons a t =>
            obtain ⟨ha, ht⟩ := List.pairwise_cons.1 hl
            intro x hx
            rw [take_succ_cons_srd_fc] at hx
            rw [drop_succ_cons_srd_fc]
            rcases List.mem_cons.1 hx with h' | hx
            · rw [h']; exact fun y hy => ha y (mem_of_mem_drop_srd_fc hy)
            · exact ih ht x hx
      refine List.pairwise_append.2 ⟨pairwise_take_srd_fc hpwL 6, ?_, ?_⟩
      · refine List.pairwise_append.2 ⟨?_, hpwT, ?_⟩
        · exact List.pairwise_cons.2 ⟨fun y hy => hret_disj_fo (e0, c0) hhead_mem y
            (mem_of_mem_drop_srd_fc hy), pairwise_drop_srd_fc hpwL 7⟩
        · intro x hx y hy
          rcases List.mem_cons.1 hx with hx0 | hx
          · rw [hx0]
            obtain ⟨L, hL, hyL⟩ := List.mem_flatten.1 hy
            obtain ⟨ec, hec, rfl⟩ := List.mem_map.1 hL
            exact hret_disj_fo ec (by rw [hch_eq]; exact List.mem_cons.2 (Or.inr hec)) y hyL
          · exact hcross x (mem_of_mem_drop_srd_fc hx) y hy
      · intro x hx y hy
        rcases List.mem_append.1 hy with hy | hy
        · rcases List.mem_cons.1 hy with hy0 | hy
          · rw [hy0]
            exact hdisj_symm (hret_disj_fo (e0, c0) hhead_mem x (mem_of_mem_take_srd_fc hx))
          · exact hcross_td hpwL 6 x hx y hy
        · exact hcross x (mem_of_mem_take_srd_fc hx) y hy
    · intro ec hec o ho
      rw [hfeq]
      by_cases hhead : ec = (e0, c0)
      · rw [hhead] at ho
        rw [hframeObjects_head] at ho
        rcases List.mem_append.1 ho with ho | ho
        · refine ⟨fun t ht i hi => ?_, ?_⟩
          · rw [hfp_eq_all t ht] at hi
            exact (hFO_disj (e0, c0) hhead_mem o (mem_of_mem_take_srd_fc ho)).1 t ht i hi
          · exact (hFO_disj (e0, c0) hhead_mem o (mem_of_mem_take_srd_fc ho)).2
        · rcases List.mem_append.1 ho with ho0 | ho
          · rw [List.mem_singleton.1 ho0]
            exact ⟨fun t ht i hi => by rw [hfp_eq_all t ht] at hi; exact hret_disj_ht t ht i hi,
              hret_disj_fix⟩
          · refine ⟨fun t ht i hi => ?_, ?_⟩
            · rw [hfp_eq_all t ht] at hi
              exact (hFO_disj (e0, c0) hhead_mem o (mem_of_mem_drop_srd_fc ho)).1 t ht i hi
            · exact (hFO_disj (e0, c0) hhead_mem o (mem_of_mem_drop_srd_fc ho)).2
      · rw [hframeObjects_eq ec hec hhead] at ho
        exact ⟨fun t ht i hi => by rw [hfp_eq_all t ht] at hi; exact (hFO_disj ec hec o ho).1 t ht i hi,
          (hFO_disj ec hec o ho).2⟩
    · refine ⟨Nd_at, hWT_post.2.2.2, fun o ho j hj => ?_⟩
      rw [InitECandidate.Solver.Wave8Contracts.M23.nodeExtents_eq hTr_at.1 hcell] at hj
      rcases hfo_post_sub o ho with ho0 | ho'
      · rw [ho0]; exact hret_nodes j hj
      · exact hAT_at o ho' j hj
    · have hworldRefs_eq : worldTableRefs post S = worldTableRefs s S := by
        unfold worldTableRefs recordSlots
        rw [hglob_eq "ws", hglob_eq "bs", hglob_eq "ts",
            show globalTableRoots.map (globN post) = globalTableRoots.map (globN s) by
              simp only [globalTableRoots, List.map, hglob_eq],
            InitECandidate.Solver.Wave8Contracts.M23.balRecords_eq hWT.1 hcell (hglob_eq "bal_accounts"),
            hglob_eq "journal_n", hglob_eq "journal"]
        have hws_sl : (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW post (globN s "ws" + k)) =
            (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW s (globN s "ws" + k)) := by
          split; · rfl
          rename_i hnz; apply List.map_congr_left; intro k hk
          exact InitECandidate.Solver.Wave8Contracts.M23.memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 40) (by decide) hnz
            (by simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl <;> omega)
        have hbs_sl : (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW post (globN s "bs" + k)) =
            (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW s (globN s "bs" + k)) := by
          split; · rfl
          rename_i hnz; apply List.map_congr_left; intro k hk
          exact InitECandidate.Solver.Wave8Contracts.M23.memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 80) (by decide) hnz
            (by simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
        have hts_sl : (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW post (globN s "ts" + k)) =
            (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW s (globN s "ts" + k)) := by
          split; · rfl
          rename_i hnz; apply List.map_congr_left; intro k hk
          exact InitECandidate.Solver.Wave8Contracts.M23.memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 72) (by decide) hnz
            (by simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
        have hnest_bs : (if globN s "bs" ≠ 0 ∧ memW post (globN s "bs" + 32) ∈ S then htabValues post (memW post (globN s "bs" + 32)) else []) =
            (if globN s "bs" ≠ 0 ∧ memW s (globN s "bs" + 32) ∈ S then htabValues s (memW s (globN s "bs" + 32)) else []) := by
          by_cases hnz : globN s "bs" = 0
          · simp [hnz]
          · rw [InitECandidate.Solver.Wave8Contracts.M23.memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 80) (by decide) hnz (by omega)]
            by_cases hmS : memW s (globN s "bs" + 32) ∈ S
            · simp [hnz, hmS, InitECandidate.Solver.Wave8Contracts.M23.htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1]
            · simp [hnz, hmS]
        have hnest_ts : (if globN s "ts" ≠ 0 ∧ memW post (globN s "ts" + 32) ∈ S then htabValues post (memW post (globN s "ts" + 32)) else []) =
            (if globN s "ts" ≠ 0 ∧ memW s (globN s "ts" + 32) ∈ S then htabValues s (memW s (globN s "ts" + 32)) else []) := by
          by_cases hnz : globN s "ts" = 0
          · simp [hnz]
          · rw [InitECandidate.Solver.Wave8Contracts.M23.memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 72) (by decide) hnz (by omega)]
            by_cases hmS : memW s (globN s "ts" + 32) ∈ S
            · simp [hnz, hmS, InitECandidate.Solver.Wave8Contracts.M23.htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1]
            · simp [hnz, hmS]
        have hbal_fl : (balRecords s).flatMap (fun ad => [memW post ad, memW post (ad + 8)]) =
            (balRecords s).flatMap (fun ad => [memW s ad, memW s (ad + 8)]) := by
          apply List.flatMap_congr; intro ad had
          have had_mem := InitECandidate.Solver.Wave8Contracts.M23.balRecord_ivl_mem had
          rcases InitECandidate.Solver.Wave8Contracts.M23.fixedObject_le_2pow64 hAs.2 hWT.2.2.1
              (InitECandidate.Solver.Wave8Contracts.M23.bal_in_fixedObjects had_mem) with h0 | had_bnd
          · dsimp only at h0; omega
          · dsimp only at had_bnd
            have hwti_ad := InitECandidate.Solver.Wave8Contracts.M23.mem_worldTypedIvls_bal (S := S) (Nd := Nd_at) had_mem
            rw [InitECandidate.Solver.Wave8Contracts.M23.memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩,
                InitECandidate.Solver.Wave8Contracts.M23.memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩]
        have hjrn_mp : (List.range (globN s "journal_n")).map (fun k => memW post (globN s "journal" + 32 * k)) =
            (List.range (globN s "journal_n")).map (fun k => memW s (globN s "journal" + 32 * k)) := by
          apply List.map_congr_left; intro k hk; rw [List.mem_range] at hk
          have hjc_le := hWT.2.1.1
          have hjc_ne : globN s "journal_cap" ≠ 0 := by omega
          rcases hWT.2.1.2.2.1 with h0 | ⟨hal, _⟩
          · exact absurd h0 hjc_ne
          · have hbnd := InitECandidate.Solver.Wave8Contracts.M23.allocated_le_2pow64 hAs.2 hal; dsimp only at hbnd
            have hkle : 32 * k + 8 ≤ 32 * globN s "journal_cap" := by omega
            exact InitECandidate.Solver.Wave8Contracts.M23.memW_eq_of_cellHits hcell (by omega)
              (InitECandidate.Solver.Wave8Contracts.M23.mem_worldTypedIvls_journal (S := S) (Nd := Nd_at) hjc_ne)
              ⟨by dsimp only; omega, by dsimp only; omega⟩
        dsimp only
        rw [hglob_eq "bs", hglob_eq "ts", hws_sl, hbs_sl, hts_sl, hnest_bs, hnest_ts, hbal_fl, hjrn_mp]
      have hdelEx_iff : ∀ i t, DelExclusive post S (evmChain s) i t ↔ DelExclusive s S (evmChain s) i t := by
        intro i t; unfold DelExclusive; rw [hworldRefs_eq]
        refine and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun hj =>
          forall_congr' fun k => imp_congr_right fun hk => ?_)
        have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
        have hk_ok : k + 8 ≤ 280 ∧ k ∉ headRetZeroOffs := by
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
        exact (hrec_eq ec (mem_of_mem_take_srd_fc hec)).1 136 (by omega) (by decide)
      have hM := hMarks i hi; dsimp only at hM ⊢
      rw [hm_eq, hmm_eq, he24_eq, hframeScratch_eq _ hi_mem, hfeq, htake_eq]
      obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM
      refine ⟨m1, m2, m3, m4, ?_, m6, m7, ?_, m9⟩
      · intro j hj hij
        have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
        rw [hframeScratch_eq _ hj_mem, hframeLogs_eq _ hj_mem,
            (hrec_eq _ hj_mem).1 112 (by omega) (by decide)]
        have h3 : (frameObjects post ((evmChain s)[j]))[3]! =
            (frameObjects s ((evmChain s)[j]))[3]! := by
          have h1 : (frameObjects post ((evmChain s)[j]))[3]! =
              (memW post (((evmChain s)[j]).1 + 24), memW post (((evmChain s)[j]).1 + 40)) := by
            simp [frameObjects]
          have h2 : (frameObjects s ((evmChain s)[j]))[3]! =
              (memW s (((evmChain s)[j]).1 + 24), memW s (((evmChain s)[j]).1 + 40)) := by
            simp [frameObjects]
          rw [h1, h2, (hrec_eq _ hj_mem).1 24 (by omega) (by decide),
              (hrec_eq _ hj_mem).1 40 (by omega) (by decide)]
        rw [h3]
        exact m5 j hj hij
      · intro t ht
        rw [hfp_eq_all t ht, hdelEx_iff i t]; exact m8 t ht
    · have hcg : ∀ g ∈ InitECandidate.Solver.Wave8Contracts.M23.coreWorldGlobals,
          globN post g = globN s g := fun g _ => hglob_eq g
      rw [InitECandidate.Solver.Wave8Contracts.M23.worldRoleSlots_eq hAs.2 hWT.1 hWT.2.2.1 hcell hcg,
          hframeRoleSlots_eq,
          InitECandidate.Solver.Wave8Contracts.M23.journalRoleSlots_eq hAs.2 hWT.2.1 hWT.2.2.1 hcell hcg]
      unfold RolesOK at hRoles ⊢
      refine ⟨fun a ha => ?_, hRoles.2⟩
      obtain ⟨haS, hkl⟩ := hRoles.1 a ha
      have htb := ((hWT.1.2.1 a.1 haS).1.1 (a.1, 88) (by simp [htabFootprint])).1
      rw [InitECandidate.Solver.Wave8Contracts.M23.htab_hdr_eq hcell haS htb 0 (by omega)]
      exact ⟨haS, hkl⟩
    · have hsum_eq : ((evmChain s).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)).sum =
          memW post (e0 + 64) + memW post (e0 + 192) +
            (((evmChain s).tail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum) := by
        unfold OpDispatchSpec.evmR at hR_val; rw [hchain_eq] at hR_val; exact hR_val
      rw [hsum_eq]; exact hgas_le
  · intro ec hec
    obtain ⟨he_eq, hc_eq, _⟩ := hrec_eq ec hec
    exact ⟨hframeScratch_eq ec hec, hframeLogs_eq ec hec,
      he_eq 24 (by omega) (by decide), he_eq 32 (by omega) (by decide),
      he_eq 40 (by omega) (by decide), he_eq 112 (by omega) (by decide),
      hc_eq 56 (by omega) (by omega)⟩
  · intro ec htail
    rw [htail_eq_s] at htail
    have hec : ec ∈ evmChain s := by
      rw [hch_eq, List.mem_cons]
      exact Or.inr htail
    exact hframeObjects_eq ec hec (fun heq => hhead_ne_tail (heq ▸ htail))
  · exact hframeRet_head
  · exact hframeObjects_head

theorem fcBranchState_of_head_ret_set_fc {F : Type}
    {s0 s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    {p' cap' : Nat}
    (h : FcBranchState s0 s S)
    (hGp : GuestInv post)
    (hglob : post.globals = s.globals)
    (hbe : post.be = s.be)
    (hloc : post.locals = s.locals)
    (hmem_out : ∀ x : BitVec 64,
      (∀ off ∈ headRetZeroOffs, x ≠ BitVec.ofNat 64 (globN s "ev" + off)) →
      post.memory x = s.memory x)
    (hcap_pos : 0 < cap')
    (h216 : memW post (globN s "ev" + 216) = cap')
    (h144 : memW post (globN s "ev" + 144) = p')
    (hret_in : Inside (p', (cap' + 15) / 8 * 8) sourceBase (globN s "heap_ptr"))
    (hret_wok : WordsOK s (p', (cap' + 15) / 8 * 8))
    (hret_disj_fo : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, Disj (p', (cap' + 15) / 8 * 8) o)
    (hret_disj_ht : ∀ t ∈ S, ∀ o ∈ htabFootprint s t, Disj (p', (cap' + 15) / 8 * 8) o)
    (hret_disj_fix : ∀ o ∈ fixedObjects s, Disj (p', (cap' + 15) / 8 * 8) o)
    (hret_avoids : AvoidsTries s S [(p', (cap' + 15) / 8 * 8)])
    (hret_disj_msg : ∀ ec ∈ evmChain s, Disj (memW s (ec.1 + 112), 176) (p', (cap' + 15) / 8 * 8))
    (hsp_le : memW post (globN s "ev" + 16) ≤ memW s (globN s "ev" + 232))
    (hgas_le : memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) +
      (((evmChain s).tail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum) + 1 < 2 ^ 64)
    (hR : memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) +
      (((evmChain s).tail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum) ≤
        OpDispatchSpec.evmR s0) :
    FcBranchState s0 post S ∧
    evmChain post = evmChain s ∧
    OpDispatchSpec.evmR post =
      memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) +
        (((evmChain s).tail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum) ∧
    frameRet post (globN s "ev", globN s "cur_cont") = (p', (cap' + 15) / 8 * 8) := by
  obtain ⟨hAp, hIp, hch, hfix, htab, hframes, _, hret_eq, _, hRp⟩ :=
    evmInvAt_of_head_ret_set_fc h.arena h.inv hGp hglob hbe hmem_out hcap_pos h216 h144
      hret_in hret_wok hret_disj_fo hret_disj_ht hret_disj_fix hret_avoids hret_disj_msg
      hsp_le hgas_le
  have hhp : globN s "heap_ptr" ≤ globN post "heap_ptr" := by unfold globN; rw [hglob]
  have hRel := releaseReadyAt_transport h.release hhp hch
    (fun ec hec => (hframes ec hec).1)
    (fun ec hec => ⟨(hframes ec hec).2.2.1, (hframes ec hec).2.2.2.2.1⟩)
    (fun ec hec => Or.inl (hframes ec hec).2.1)
    (fun ec hec => (hframes ec hec).2.2.2.2.2.1)
    (fun t ht => Or.inl (htab t ht)) hfix
  refine ⟨⟨hAp, hIp, hRel, fcEntryLocals_congr_locals hloc h.locals_ok,
    hch.trans h.chain_eq, ?_, ?_, ?_, ?_⟩, hch, hRp, hret_eq⟩
  · rw [hch]; exact h.length_eq
  · rw [hRp]; exact hR
  · intro ec hec
    rw [hch] at hec
    obtain ⟨a, b, c, d⟩ := h.cells ec hec
    have hf := (hframes ec hec).2.2
    exact ⟨hf.1.trans a, hf.2.1.trans b, hf.2.2.1.trans c, hf.2.2.2.2.trans d⟩
  · have hev : globN post "ev" = globN s "ev" := by unfold globN; rw [hglob]
    exact hev.trans h.ev_eq


end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
