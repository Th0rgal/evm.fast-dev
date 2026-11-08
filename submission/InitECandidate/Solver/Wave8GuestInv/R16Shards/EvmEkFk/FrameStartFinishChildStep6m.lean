import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.FrameStartFinishChildStep6a
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.StorageCreateFinish
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemAlignedBridge

set_option Elab.async false
set_option autoImplicit false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8Contracts.M23 (GlobalsKept)
open InitECandidate.Solver.Wave8GuestInv.R11Shards

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-! ### Helper transport & signed-less lemmas -/

theorem avoidsTries_of_head_simple_6 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} {ivls : List Ivl}
    (hAs : ArenaReady s)
    (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S)
    (hGp : GuestInv post)
    (hglob : post.globals = s.globals)
    (hbe : post.be = s.be)
    (hmem_out : ∀ x : BitVec 64,
      (∀ off ∈ headSimpleOffs, x ≠ BitVec.ofNat 64 (globN s "ev" + off)) →
      post.memory x = s.memory x)
    (hav : AvoidsTries s S ivls) :
    AvoidsTries post S ivls := by
  obtain ⟨Nd_v, hTr_v, hdj_v⟩ := hav
  obtain ⟨Nd_inv, hTr_inv, hAT_inv⟩ := hInv.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hTr_a, hsub_a⟩ := R11Shards.triesTypedWith_inter hTr_v hTr_inv
  set Nd_a := Nd_v.filter (fun n => decide (n ∈ Nd_inv))
  have hWT : InitECandidate.Solver.Wave8Contracts.M23.WorldTypedWith s S Nd_a :=
    ⟨hInv.1.1, hInv.1.2.1, hInv.1.2.2.1, hTr_a⟩
  set e0 := globN s "ev"
  set c0 := globN s "cur_cont"
  have hhead_mem : (e0, c0) ∈ evmChain s := by
    rw [evmChain_cons]; exact List.mem_cons_self
  have hhead_FW := hInv.2.2.2.2.1 _ hhead_mem
  obtain ⟨hb1, _, _, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hAs.2 hhead_FW
  dsimp only at hb1
  have he0_8 : e0 % 8 = 0 := (hhead_FW.1 (e0, 280) (by simp)).2.1
  have hdom_eq : post.memaddrs = s.memaddrs := hGp.memaddrs.trans hAs.1.memaddrs.symm
  have hoff_props : ∀ off ∈ headSimpleOffs,
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
        rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
      rw [hmem_out (panByteAlignHOL (BitVec.ofNat 64 b)), hbe]
      intro off hoff heq
      have hp := hoff_props off hoff
      have htn : (BitVec.ofNat 64 (e0 + off)).toNat = e0 + off := Nat.mod_eq_of_lt (by omega)
      have := congrArg BitVec.toNat heq
      rw [hal_b, htn] at this
      exact hno (e0, 280) (by simp) ⟨by dsimp only; omega, by dsimp only; omega⟩
  have hglob_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, hglob]
  have hApost : ArenaReady post := ⟨hGp, arenaOK_congr hglob hAs.2⟩
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hglob_eq]
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hglob_eq]
  have hrec_fo : (e0, 280) ∈ frameObjects s (e0, c0) := by simp [frameObjects]
  have hFO_disj := hInv.2.2.2.2.2.2.2.2.1
  have hrec_disj_wti : ∀ i ∈ InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls s S Nd_a,
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
    · exact Or.inr (hAT_inv _ (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨_, hhead_mem, rfl⟩, hrec_fo⟩)
        i (hsub_a i h6).2)
  have hcell : InitECandidate.Solver.Wave8Contracts.M23.SameTypedCells s post S Nd_a :=
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
  refine ⟨Nd_a, hWT_post.2.2.2, fun o ho j hj => ?_⟩
  rw [InitECandidate.Solver.Wave8Contracts.M23.nodeExtents_eq hTr_a.1 hcell] at hj
  exact hdj_v o ho j (hsub_a j hj).1

theorem avoidsTries_lc_6 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (ck : Nat) (S : List Nat) (ivls : List Ivl) :
    AvoidsTries { s with locals := L, clock := ck } S ivls ↔ AvoidsTries s S ivls :=
  Iff.rfl

private theorem holAsmSignedLess_eq_slt_6 (left right : BitVec 64) :
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

theorem globalsKept_trans_6 {F : Type} {l : List String}
    {s1 s2 s3 : PanSemStateFiniteExact 64 F}
    (h12 : GlobalsKept l s1 s2) (h23 : GlobalsKept l s2 s3) :
    GlobalsKept l s1 s3 := by
  intro k hk; exact (h12 k hk).trans (h23 k hk)

theorem call0_congr_locals_6 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (L : HolFiniteMapExact MlS (ValueHOL 64))
    (fname : MlS) (args1 args2 : List (ExpHOL 64)) (vals : List (ValueHOL 64))
    (ha1 : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args1 = some vals)
    (ha2 : evalListHOLFinite { s with locals := L }
      (h := fun a => Classical.propDecidable (s.memaddrs a)) args2 = some vals) :
    let r1 := evaluateHOLFiniteState s (.call (some (none, none)) fname args1)
    let r2 := evaluateHOLFiniteState { s with locals := L } (.call (some (none, none)) fname args2)
    r1.1 = r2.1 ∧ (r1.1 = none → r1.2 = { r2.2 with locals := s.locals }) := by
  dsimp only
  rw [evaluateHOLFiniteState_call, evaluateHOLFiniteState_call, ha1]
  have ha2' : evalListHOLFinite { s with locals := L }
      (h := fun a => Classical.propDecidable (({ s with locals := L } : PanSemStateFiniteExact 64 F).memaddrs a)) args2 =
      some vals := ha2
  rw [ha2']
  dsimp only
  have hce : ∀ cal, callEntryStateHOLFinite { s with locals := L } cal = callEntryStateHOLFinite s cal :=
    fun _ => rfl
  rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body, cal, ret⟩
  · exact ⟨rfl, fun h => by cases h⟩
  · dsimp only
    by_cases hclk : s.clock = 0
    · rw [if_pos hclk, if_pos hclk]
      exact ⟨rfl, fun h => by cases h⟩
    · rw [if_neg hclk, if_neg hclk, hce cal]
      rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s cal) body with ⟨rb, sb⟩
      cases rb with
      | none => exact ⟨rfl, fun h => by cases h⟩
      | some res =>
        cases res with
        | returned rv =>
          dsimp only
          by_cases hsh : shapeEqHOL (shapeOfHOLExact rv) ret = true
          · rw [if_pos hsh, if_pos hsh]; exact ⟨rfl, fun _ => rfl⟩
          · rw [if_neg hsh, if_neg hsh]; exact ⟨rfl, fun h => by cases h⟩
        | timeOut | error | «break» | «continue» | finalFfi _ | exception _ _ =>
          exact ⟨rfl, fun h => by cases h⟩

private theorem call0_not_break_continue_6 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (fname : MlS) (args : List (ExpHOL 64))
    (res : PanSemResultExact 64) (st' : PanSemStateFiniteExact 64 F)
    (h : evaluateHOLFiniteState s (.call (some (none, none)) fname args) = (some res, st')) :
    res ≠ .break ∧ res ≠ .continue := by
  rw [evaluateHOLFiniteState_call] at h
  rcases ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · rw [ha] at h; injection h with h1 _; injection h1 with h2; subst h2; exact ⟨by nofun, by nofun⟩
  · rw [ha] at h; dsimp only at h
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body, cal, ret⟩
    · rw [hl] at h; injection h with h1 _; injection h1 with h2; subst h2; exact ⟨by nofun, by nofun⟩
    · rw [hl] at h; dsimp only at h
      by_cases hc : s.clock = 0
      · rw [if_pos hc] at h
        injection h with h1 _; injection h1 with h2; subst h2; exact ⟨by nofun, by nofun⟩
      · rw [if_neg hc] at h
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s cal) body with ⟨rb, sb⟩
        rw [hrun] at h
        cases rb with
        | none => injection h with h1 _; injection h1 with h2; subst h2; exact ⟨by nofun, by nofun⟩
        | some r0 =>
          cases r0 with
          | «break» | «continue» =>
            injection h with h1 _; injection h1 with h2; subst h2; exact ⟨by nofun, by nofun⟩
          | returned rv =>
            dsimp only at h
            by_cases hs : shapeEqHOL (shapeOfHOLExact rv) ret = true
            · rw [if_pos hs] at h; cases (Prod.mk.inj h).1
            · rw [if_neg hs] at h
              injection h with h1 _; injection h1 with h2; subst h2; exact ⟨by nofun, by nofun⟩
          | timeOut | error | finalFfi _ | exception _ _ =>
            injection h with h1 _; injection h1 with h2; subst h2; exact ⟨by nofun, by nofun⟩

def logAppendWhileBody6 : ProgHOL 64 :=
  .seq
    (.call (some (none, none)) (ofString "log_append")
      [.var .global (ofString "ev"),
       .load .one (.op .add [.var .local (ofString "p"),
         .panop .mul [.var .local (ofString "i"), .const 8#64]])])
    (.assign .local (ofString "i")
      (.op .add [.var .local (ofString "i"), .const 1#64]))

def logAppendWhileProg6 : ProgHOL 64 :=
  .while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n")))
    logAppendWhileBody6

theorem log_append_while_fc_step :
    ∀ (rem : Nat) {F : Type} {s0 st : PanSemStateFiniteExact 64 F} {S : List Nat}
      (L0 : HolFiniteMapExact MlS (ValueHOL 64))
      (p n cap k : Nat),
      k ≤ n → rem = n - k → n < 2 ^ 28 → n ≤ cap →
      FcBranchState s0 { st with locals := L0, clock := st.clock } S →
      st.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 k))) →
      st.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n))) →
      st.locals.lookup (ofString "p") = some (.val (.word (BitVec.ofNat 64 p))) →
      ((p, 8 * cap).2 = 0 ∨ Allocated st (p, 8 * cap)) →
      WordsOK st (p, 8 * cap) →
      (∀ ec ∈ evmChain st, ∀ o ∈ frameObjects st ec, Disj (p, 8 * cap) o) →
      (∀ o ∈ (List.range (n - k)).flatMap
        (fun j => logOwnedIvls st (memW st (p + 8 * (k + j)))),
        Disj (p, 8 * cap) o) →
      (∀ o ∈ (List.range (n - k)).flatMap
        (fun j => logOwnedIvls st (memW st (p + 8 * (k + j)))),
        Disj (globN s0 "ev", 280) o) →
      (∀ j, k ≤ j → j < n →
        WordAt st (p + 8 * j) ∧ LogEntryOK st (memW st (p + 8 * j))) →
      (((List.range (n - k)).flatMap
        (fun j => logOwnedIvls st (memW st (p + 8 * (k + j))))).Pairwise Disj) →
      (∀ o1 ∈ (List.range (n - k)).flatMap
        (fun j => logOwnedIvls st (memW st (p + 8 * (k + j)))),
        ∀ ec ∈ evmChain st, ∀ o2 ∈ frameObjects st ec, Disj o1 o2) →
      (∀ o1 ∈ (List.range (n - k)).flatMap
        (fun j => logOwnedIvls st (memW st (p + 8 * (k + j)))),
        ∀ t ∈ S, ∀ o2 ∈ htabFootprint st t, Disj o1 o2) →
      (∀ o1 ∈ (List.range (n - k)).flatMap
        (fun j => logOwnedIvls st (memW st (p + 8 * (k + j)))),
        ∀ o2 ∈ fixedObjects st, Disj o1 o2) →
      AvoidsTries st S ((List.range (n - k)).flatMap
        (fun j => logOwnedIvls st (memW st (p + 8 * (k + j))))) →
      (∀ o1 ∈ (List.range (n - k)).flatMap
        (fun j => logOwnedIvls st (memW st (p + 8 * (k + j)))),
        ∀ ec ∈ evmChain st, Disj (memW st (ec.1 + 112), 176) o1) →
      WordsOK st (globN s0 "ev", 280) →
      Inside (globN s0 "ev", 280) (globN st "scratch_ptr") scratchEnd →
      (∀ ec ∈ evmChain st, ∀ o ∈ frameObjects st ec, Disj (globN s0 "ev", 280) o) →
      (∀ t ∈ S, ∀ o ∈ htabFootprint st t, Disj (globN s0 "ev", 280) o) →
      ∀ {rv : ValueHOL 64} {cont : ProgHOL 64} {sk : PanSemStateFiniteExact 64 F},
      evaluateHOLFiniteState st (.seq logAppendWhileProg6 cont) = (some (.returned rv), sk) →
      ∃ wm : PanSemStateFiniteExact 64 F,
        evaluateHOLFiniteState st logAppendWhileProg6 = (none, wm) ∧
        evaluateHOLFiniteState wm cont = (some (.returned rv), sk) ∧
        FcBranchState s0 { wm with locals := L0, clock := wm.clock } S ∧
        globN st "heap_ptr" ≤ globN wm "heap_ptr" ∧
        GlobalsKept ["heap_ptr"] st wm ∧
        wm.be = st.be ∧
        evmChain wm = evmChain st ∧
        OpDispatchSpec.evmR wm = OpDispatchSpec.evmR st ∧
        (∀ t ∈ S, htabFootprint wm t = htabFootprint st t) ∧
        memW wm (globN st "ev" + 16) = memW st (globN st "ev" + 16) ∧
        memW wm (globN st "ev" + 40) = memW st (globN st "ev" + 40) ∧
        memW wm (globN st "ev" + 232) = memW st (globN st "ev" + 232) ∧
        WordsOK wm (globN s0 "ev", 280) ∧
        Inside (globN s0 "ev", 280) (globN wm "scratch_ptr") scratchEnd ∧
        (∀ t ∈ S, ∀ o ∈ htabFootprint wm t, Disj (globN s0 "ev", 280) o) ∧
        memW wm (globN s0 "ev" + 96) = memW st (globN s0 "ev" + 96) ∧
        (∀ nm : MlS, nm ≠ ofString "i" → wm.locals.lookup nm = st.locals.lookup nm) := by
  intro rem
  induction rem with
  | zero =>
    intro F s0 st S L0 p n cap k hk hrem hn28 hncap hBS hi_lk hn_lk hp_lk
      hp_alloc hp_wok hp_dfo hp_dlo hc_dlo hlogs hpw hlo_fo hlo_ht hlo_fix hlo_av hlo_msg
      hc_wok hc_ins hc_dfo hc_dht rv cont sk hseq
    have hkn : k = n := by omega
    subst hkn
    rw [evaluateHOLFiniteState_seq_line780] at hseq
    rcases hw : evaluateHOLFiniteState st logAppendWhileProg6 with ⟨rw0, wm⟩
    have hw' := hw
    unfold logAppendWhileProg6 at hw'
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hw'
    have hslt_ff : Compiler.Encoders.Asm.holAsmSignedLess
        (BitVec.ofNat 64 k) (BitVec.ofNat 64 k) = false := by
      rw [holAsmSignedLess_eq_slt_6]; simp [BitVec.slt]
    have hcmp0 : PanSemStateFiniteExact.evalHOLFinite st
        (h := fun a => Classical.propDecidable (st.memaddrs a))
        (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word 0)) := by
      simp [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact, hi_lk, hn_lk,
        Compiler.Encoders.Asm.wordCmpHOL, hslt_ff]
    rw [hcmp0] at hw'
    simp only [ne_eq, not_true_eq_false, ↓reduceIte] at hw'
    injection hw' with hrw hwm
    subst hrw hwm
    rw [hw] at hseq; dsimp only at hseq
    refine ⟨st, rfl, hseq, hBS, le_rfl, fun _ _ => rfl, rfl, rfl, rfl,
      fun _ _ => rfl, rfl, rfl, rfl, hc_wok, hc_ins, hc_dht, rfl, fun _ _ => rfl⟩
  | succ rem ih =>
    intro F s0 st S L0 p n cap k hk hrem hn28 hncap hBS hi_lk hn_lk hp_lk
      hp_alloc hp_wok hp_dfo hp_dlo hc_dlo hlogs hpw hlo_fo hlo_ht hlo_fix hlo_av hlo_msg
      hc_wok hc_ins hc_dfo hc_dht rv cont sk hseq
    have hk_lt : k < n := by omega
    have h263 : k < 2 ^ (64 - 1) ∧ n < 2 ^ (64 - 1) ∧ k < 2 ^ 64 ∧ n < 2 ^ 64 ∧ 8 * k < 2 ^ 64 := by
      have : (2 ^ 28 : Nat) = 268435456 := by norm_num
      have : (2 ^ (64 - 1) : Nat) = 9223372036854775808 := by norm_num
      have : (2 ^ 64 : Nat) = 18446744073709551616 := by norm_num
      omega
    have hslt_tt : Compiler.Encoders.Asm.holAsmSignedLess
        (BitVec.ofNat 64 k) (BitVec.ofNat 64 n) = true := by
      rw [holAsmSignedLess_eq_slt_6, BitVec.slt_eq_decide, BitVec.toInt_eq_msb_cond,
        BitVec.toInt_eq_msb_cond, BitVec.msb_eq_decide, BitVec.msb_eq_decide]
      have hk_tn : (BitVec.ofNat 64 k).toNat = k := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h263.2.2.1]
      have hn_tn : (BitVec.ofNat 64 n).toNat = n := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h263.2.2.2.1]
      have hd1 : decide (2 ^ (64 - 1) ≤ (BitVec.ofNat 64 k).toNat) = false :=
        decide_eq_false (by rw [hk_tn]; exact Nat.not_le.2 h263.1)
      have hd2 : decide (2 ^ (64 - 1) ≤ (BitVec.ofNat 64 n).toNat) = false :=
        decide_eq_false (by rw [hn_tn]; exact Nat.not_le.2 h263.2.1)
      rw [hd1, hd2, hk_tn, hn_tn]
      simp [decide_eq_true_eq]; omega
    rw [evaluateHOLFiniteState_seq_line780] at hseq
    rcases hw : evaluateHOLFiniteState st logAppendWhileProg6 with ⟨rw0, wm⟩
    have hw' := hw
    conv_lhs at hw' => unfold logAppendWhileProg6; rw [evaluateHOLFiniteState_while_fixClockRewrite]
    have hcmp1 : PanSemStateFiniteExact.evalHOLFinite st
        (h := fun a => Classical.propDecidable (st.memaddrs a))
        (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word 1)) := by
      simp [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact, hi_lk, hn_lk,
        Compiler.Encoders.Asm.wordCmpHOL, hslt_tt]
    rw [hcmp1] at hw'
    have h10 : ((1 : BitVec 64) ≠ 0) := by decide
    simp only [ne_eq, h10, not_false_eq_true, ↓reduceIte] at hw'
    by_cases hclk0 : st.clock = 0
    · simp only [hclk0, ↓reduceIte] at hw'
      injection hw' with hrw hwm; subst hrw hwm
      rw [hw] at hseq; cases (Prod.mk.inj hseq).1
    · simp only [hclk0, ↓reduceIte] at hw'
      set s_dc := decClockHOLFinite st
      set s_la : PanSemStateFiniteExact 64 F := { s_dc with locals := L0 }
      have hsla_BS : FcBranchState s0 s_la S := by
        let st0 : PanSemStateFiniteExact 64 F := { st with locals := L0, clock := st.clock }
        have h_eq : s_la = { st0 with locals := L0, clock := s_dc.clock } := rfl
        rw [h_eq]
        exact fcBranchState_congr_locals_clock (st := st0)
          L0 s_dc.clock hBS (fcEntryLocals_congr_locals (s1 := st0) rfl hBS.locals_ok)
      have hAr : ArenaReady st := ⟨guestInv_congr (s := { st with locals := L0, clock := st.clock })
        rfl rfl rfl rfl hBS.arena.1, arenaOK_congr rfl hBS.arena.2⟩
      have hp_pos_alloc : Allocated st (p, 8 * cap) := by
        rcases hp_alloc with h0 | hal
        · dsimp only at h0; omega
        · exact hal
      have hp_bnd : p + 8 * cap ≤ 2 ^ 64 :=
        (InitECandidate.Solver.Wave8Contracts.M08.ivl_allocated_bound hAr.2 hp_pos_alloc).2
      let logExp : ExpHOL 64 :=
        .load .one (.op .add [.var .local (ofString "p"),
          .panop .mul [.var .local (ofString "i"), .const 8#64]])
      have hmul_eq : BitVec.ofNat 64 k * 8#64 = BitVec.ofNat 64 (8 * k) := by
        apply BitVec.eq_of_toNat_eq
        have h8lt : 8 < 2 ^ 64 := by norm_num
        have hk8lt : k * 8 < 2 ^ 64 := by have := h263.2.2.2.2; omega
        rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt h263.2.2.1, Nat.mod_eq_of_lt h8lt,
          Nat.mod_eq_of_lt hk8lt, Nat.mod_eq_of_lt h263.2.2.2.2, Nat.mul_comm]
      have hadd_pk : BitVec.ofNat 64 p + (BitVec.ofNat 64 (8 * k) + (0 : BitVec 64)) =
          BitVec.ofNat 64 (p + 8 * k) := by
        change BitVec.ofNat 64 p + (BitVec.ofNat 64 (8 * k) + 0#64) = _
        rw [BitVec.add_zero]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show p < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (show 8 * k < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (show p + 8 * k < 2 ^ 64 by omega)]
      obtain ⟨wk, hdom_pk, hmem_pk⟩ := hp_wok.2.2 k (by dsimp only; omega)
      set log_k := memW st (p + 8 * k)
      have hlog_ev_dc : @evalHOLExact 64 F _ s_dc.toExact
          (fun a => Classical.propDecidable (s_dc.memaddrs a)) logExp =
          some (.val (.word (BitVec.ofNat 64 log_k))) := by
        have hi_dc : s_dc.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 k))) := hi_lk
        have hp_dc : s_dc.locals.lookup (ofString "p") = some (.val (.word (BitVec.ofNat 64 p))) := hp_lk
        have hdom_dc : s_dc.memaddrs (BitVec.ofNat 64 (p + 8 * k)) := hdom_pk
        have hmem_dc : s_dc.memory (BitVec.ofNat 64 (p + 8 * k)) = .word wk := hmem_pk
        simp only [logExp, log_k, evalHOLExact, evalListHOLExact, hp_dc, hi_dc,
          isWfShapeExactHOL, memLoadHOLExact, ↓reduceIte,
          valueIsWord, valueWord, panOpHOL, hmul_eq, wordOpHOL, wordOp,
          List.all, List.map, Option.map, List.foldr, Bool.and_self]
        rw [hadd_pk]
        simp only [hdom_dc, ↓reduceIte, hmem_dc, Option.some.injEq, ValueHOL.val.injEq,
          HolWordLab.word.injEq]
        unfold memW; rw [hmem_pk]; simp
      obtain ⟨_, _, he_lk_la, _, _⟩ := ev_head_facts_6a hsla_BS.arena hsla_BS.inv
      have hev_dc : @evalHOLExact 64 F _ s_dc.toExact
          (fun a => Classical.propDecidable (s_dc.memaddrs a))
          (.var .global (ofString "ev")) =
          some (.val (.word (BitVec.ofNat 64 (globN s_la "ev")))) := by
        have h1 : s_dc.globals.lookup (ofString "ev") =
            some (.val (.word (BitVec.ofNat 64 (globN s_la "ev")))) := he_lk_la
        simp [evalHOLExact, h1]
      have hargs_dc : evalListHOLFinite s_dc (h := fun a => Classical.propDecidable (s_dc.memaddrs a))
          [.var .global (ofString "ev"), logExp] =
          some [.val (.word (BitVec.ofNat 64 (globN s_la "ev"))),
                .val (.word (BitVec.ofNat 64 log_k))] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, hev_dc, hlog_ev_dc]
      have hargs_la : evalListHOLFinite s_la (h := fun a => Classical.propDecidable (s_la.memaddrs a))
          [.var .global (ofString "ev"), .const (BitVec.ofNat 64 log_k)] =
          some [.val (.word (BitVec.ofNat 64 (globN s_la "ev"))),
                .val (.word (BitVec.ofNat 64 log_k))] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, he_lk_la]
      have hcong_call := call0_congr_locals_6 s_dc L0 (ofString "log_append")
        [.var .global (ofString "ev"), logExp]
        [.var .global (ofString "ev"), .const (BitVec.ofNat 64 log_k)]
        [.val (.word (BitVec.ofNat 64 (globN s_la "ev"))), .val (.word (BitVec.ofNat 64 log_k))]
        hargs_dc hargs_la
      -- Step body: logAppendWhileBody6 = .seq call assign
      rcases hbody : evaluateHOLFiniteState s_dc logAppendWhileBody6 with ⟨rb, sb⟩
      have hbody' := hbody
      unfold logAppendWhileBody6 at hbody'
      rw [evaluateHOLFiniteState_seq_line780] at hbody'
      rcases hcall_dc : evaluateHOLFiniteState s_dc
          (.call (some (none, none)) (ofString "log_append")
            [.var .global (ofString "ev"), logExp]) with ⟨rc_dc, sc_dc⟩
      rw [hcall_dc] at hbody'
      -- Partition range (n - k) = 0 :: map (1 + ·) (range (n - (k + 1)))
      have hrng_eq : (List.range (n - k)).flatMap
          (fun j => logOwnedIvls st (memW st (p + 8 * (k + j)))) =
          logOwnedIvls st log_k ++
            (List.range (n - (k + 1))).flatMap
              (fun j => logOwnedIvls st (memW st (p + 8 * ((k + 1) + j)))) := by
        have hnk : n - k = 1 + (n - (k + 1)) := by omega
        rw [hnk, List.range_add, List.flatMap_append, List.flatMap_map]
        simp only [List.range_one, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          Nat.add_zero, log_k]
        congr 1; apply List.flatMap_congr; intro j _
        rw [show k + (1 + j) = (k + 1) + j by omega]
      rw [hrng_eq, List.pairwise_append] at hpw
      obtain ⟨hpw_k, hpw_tl, hdj_k_tl⟩ := hpw
      obtain ⟨hk_wa_st, hk_ok_st⟩ := hlogs k le_rfl hk_lt
      have hk_wa_la : WordAt s_la log_k := by
        have h0 := hk_ok_st.1.2.2 0 (by dsimp only; omega)
        dsimp only at h0
        rwa [Nat.mul_zero, Nat.add_zero] at h0
      have hk_ev_la : @evalHOLExact 64 F _ s_la.toExact
          (fun a => Classical.propDecidable (s_la.memaddrs a))
          (.const (BitVec.ofNat 64 log_k)) =
          some (.val (.word (BitVec.ofNat 64 log_k))) := rfl
      have hnt_la : (evaluateHOLFiniteState s_la
          (.call (some (none, none)) (ofString "log_append")
            [.var .global (ofString "ev"), .const (BitVec.ofNat 64 log_k)])).1 ≠ some .timeOut := by
        intro hto
        have hrc_to : rc_dc = some .timeOut := by
          have := hcong_call.1; rw [hcall_dc] at this; exact this.trans hto
        subst hrc_to; dsimp only at hbody'
        injection hbody' with hrb _; subst hrb
        rw [hbody] at hw'; dsimp only at hw'
        injection hw' with hrw _; subst hrw
        rw [hw] at hseq; cases (Prod.mk.inj hseq).1
      have hch_la_st : evmChain s_la = evmChain st := evmChain_lc_fc st L0 s_dc.clock
      have hstep_la := log_append_head_fc_step (s0 := s0) (s := s_la) (S := S)
        (logExp := .const (BitVec.ofNat 64 log_k)) (log := log_k)
        hsla_BS hk_ev_la hk_wa_la hk_ok_st hpw_k
        (fun ec hec o1 ho1 o2 ho2 => hlo_fo o1 (by rw [hrng_eq]; exact List.mem_append_left _ ho1)
          ec (hch_la_st ▸ hec) o2 ho2)
        (fun o ho t ht j hj => hlo_ht o (by rw [hrng_eq]; exact List.mem_append_left _ ho) t ht j hj)
        (fun o ho j hj => hlo_fix o (by rw [hrng_eq]; exact List.mem_append_left _ ho) j hj)
        ((avoidsTries_lc_6 st L0 s_dc.clock S _).2
          ⟨hlo_av.choose, hlo_av.choose_spec.1, fun o ho j hj =>
            hlo_av.choose_spec.2 o (by rw [hrng_eq]; exact List.mem_append_left _ ho) j hj⟩)
        (fun o ho ec hec => hlo_msg o (by rw [hrng_eq]; exact List.mem_append_left _ ho)
          ec (hch_la_st ▸ hec))
        hnt_la
      dsimp only at hstep_la
      obtain ⟨hnret_la, hnerr_la, hnone_la⟩ := hstep_la
      cases rc_dc with
      | some r_c =>
        dsimp only at hbody'
        injection hbody' with hrb hsb; subst hrb hsb
        rw [hbody] at hw'; dsimp only at hw'
        cases r_c with
        | timeOut | error =>
          dsimp only at hw'; injection hw' with hrw _; subst hrw
          rw [hw] at hseq; cases (Prod.mk.inj hseq).1
        | «break» =>
          exact absurd rfl (call0_not_break_continue_6 s_dc _ _ _ _ hcall_dc).1
        | «continue» =>
          exact absurd rfl (call0_not_break_continue_6 s_dc _ _ _ _ hcall_dc).2
        | returned u =>
          have hrc_la : (evaluateHOLFiniteState s_la
              (.call (some (none, none)) (ofString "log_append")
                [.var .global (ofString "ev"), .const (BitVec.ofNat 64 log_k)])).1 =
              some (.returned u) := by
            have := hcong_call.1.symm; rwa [hcall_dc] at this
          exact absurd hrc_la (hnret_la u)
        | finalFfi f1 =>
          dsimp only at hw'; injection hw' with hrw _; subst hrw
          rw [hw] at hseq; cases (Prod.mk.inj hseq).1
        | exception eid evx =>
          dsimp only at hw'; injection hw' with hrw _; subst hrw
          rw [hw] at hseq; cases (Prod.mk.inj hseq).1
      | none =>
        dsimp only at hbody'
        have hn_la : (evaluateHOLFiniteState s_la
            (.call (some (none, none)) (ofString "log_append")
              [.var .global (ofString "ev"), .const (BitVec.ofNat 64 log_k)])).1 = none := by
          have := hcong_call.1.symm; rwa [hcall_dc] at this
        set post_la := (evaluateHOLFiniteState s_la
          (.call (some (none, none)) (ofString "log_append")
            [.var .global (ofString "ev"), .const (BitVec.ofNat 64 log_k)])).2
        have hsc_dc_eq : sc_dc = { post_la with locals := st.locals } := by
          have h1 := hcong_call.2 (by rw [hcall_dc])
          rw [hcall_dc] at h1; exact h1
        obtain ⟨hBS_pla, hloc_pla, hhp_pla, hgk_pla, hbe_pla, hch_pla, hR_pla, hfix_pla,
          hht_pla, h112_pla, h16_pla, h40_pla, h232_pla, hfo_tl_pla, hfo_hd_pla,
          hav_pla, hunhit_pla⟩ := hnone_la hn_la
        -- Step assign i := i + 1 on sc_dc
        rw [evaluateHOLFiniteState_assign] at hbody'
        have hsc_i : sc_dc.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 k))) := by
          rw [hsc_dc_eq]; exact hi_lk
        have hadd_i : @evalHOLExact 64 F _ sc_dc.toExact
            (fun a => Classical.propDecidable (sc_dc.memaddrs a))
            (.op .add [.var .local (ofString "i"), .const 1#64]) =
            some (.val (.word (BitVec.ofNat 64 (k + 1)))) := by
          have h1_eq : BitVec.ofNat 64 k + 1#64 = BitVec.ofNat 64 (k + 1) := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          simp [evalHOLExact, evalListHOLExact, hsc_i, valueIsWord, valueWord, wordOpHOL, wordOp, h1_eq]
        have hval_i : sc_dc.isValidValueHOLFinite .local (ofString "i")
            (.val (.word (BitVec.ofNat 64 (k + 1)))) = true := by
          simp [isValidValueHOLFinite, lookupKvarHOLExact, hsc_i, shapeOfHOLExact, shapeEqHOL]
        rw [hadd_i] at hbody'; dsimp only at hbody'
        rw [if_pos hval_i] at hbody'
        injection hbody' with hrb hsb; subst hrb
        rw [hbody] at hw'; dsimp only at hw'
        -- sb = setKvarHOLFinite .local (ofString "i") (.val (.word (BitVec.ofNat 64 (k + 1)))) sc_dc
        have hsb_def : sb = setVarHOLFinite (ofString "i") (.val (.word (BitVec.ofNat 64 (k + 1)))) sc_dc :=
          hsb.symm
        have hsb_la : { sb with locals := L0, clock := sb.clock } = post_la := by
          have haux : ∀ (x : PanSemStateFiniteExact 64 F) (hl : x.locals = L0),
              { x with locals := L0, clock := x.clock } = x := by
            intro x hl; cases x; dsimp only at hl ⊢; subst hl; rfl
          have h1 : { sb with locals := L0, clock := sb.clock } =
              { post_la with locals := L0, clock := post_la.clock } := by
            rw [hsb_def, hsc_dc_eq]; rfl
          exact h1.trans (haux post_la hloc_pla)
        have hBS_sb : FcBranchState s0 { sb with locals := L0, clock := sb.clock } S := by
          rw [hsb_la]; exact hBS_pla
        have hsb_mem : sb.memory = post_la.memory := by rw [hsb_def, hsc_dc_eq]; rfl
        have hsb_glob : sb.globals = post_la.globals := by rw [hsb_def, hsc_dc_eq]; rfl
        have hsb_dom : sb.memaddrs = post_la.memaddrs := by rw [hsb_def, hsc_dc_eq]; rfl
        have hsb_be : sb.be = post_la.be := by rw [hsb_def, hsc_dc_eq]; rfl
        have hsb_dom_st : sb.memaddrs = st.memaddrs :=
          hsb_dom.trans (hBS_pla.arena.1.memaddrs.trans hAr.1.memaddrs.symm)
        have hAr_sb : ArenaReady sb := ⟨guestInv_congr (s := post_la)
          (by rw [hsb_def, hsc_dc_eq]; rfl) hsb_dom
          (by rw [hsb_def, hsc_dc_eq]; rfl) (by rw [hsb_def, hsc_dc_eq]; rfl)
          hBS_pla.arena.1, arenaOK_congr hsb_glob hBS_pla.arena.2⟩
        have hhead_la : (globN s_la "ev", globN s_la "cur_cont") ∈ evmChain s_la := by
          rw [evmChain_cons]; exact List.mem_cons_self
        have hhead_st : (globN st "ev", globN st "cur_cont") ∈ evmChain st := by
          rw [evmChain_cons]; exact List.mem_cons_self
        have hlhdr_fo : (memW s_la (globN s_la "ev" + 88), 24) ∈
            frameObjects s_la (globN s_la "ev", globN s_la "cur_cont") := by
          simp [frameObjects]
        have hfl_fo : frameLogs s_la (globN s_la "ev", globN s_la "cur_cont") ∈
            frameObjects s_la (globN s_la "ev", globN s_la "cur_cont") := by
          simp [frameObjects]
        have hscr_eq_sb : globN sb "scratch_ptr" = globN st "scratch_ptr" :=
          InitECandidate.Solver.Wave8Contracts.M08.globN_eq_of_lookup
            (by rw [hsb_glob]; exact hgk_pla (ofString "scratch_ptr") (by decide))
        have hev_eq_sb : globN sb "ev" = globN st "ev" :=
          InitECandidate.Solver.Wave8Contracts.M08.globN_eq_of_lookup
            (by rw [hsb_glob]; exact hgk_pla (ofString "ev") (by decide))
        have hsys_eq_sb : globN post_la "vm_system_address" = globN s_la "vm_system_address" :=
          InitECandidate.Solver.Wave8Contracts.M08.globN_eq_of_lookup
            (hgk_pla (ofString "vm_system_address") (by decide))
        -- Unhit helper from st to sb
        have hunhit_sb : ∀ iv : Ivl, (iv.2 = 0 ∨ Allocated st iv) →
            Disj iv (memW s_la (globN s_la "ev" + 88), 24) →
            Disj iv (frameLogs s_la (globN s_la "ev", globN s_la "cur_cont")) →
            M08IvlUnhit6a st sb iv := by
          intro iv hal hd1 hd2
          have hu := hunhit_pla iv hal hd1 hd2
          intro x hx
          rw [hsb_mem]
          exact hu x hx
        -- Transport p array
        have hp_unhit : M08IvlUnhit6a st sb (p, 8 * cap) :=
          hunhit_sb (p, 8 * cap) hp_alloc
            (hp_dfo _ hhead_st _ hlhdr_fo) (hp_dfo _ hhead_st _ hfl_fo)
        have hp_alloc_sb : (p, 8 * cap).2 = 0 ∨ Allocated sb (p, 8 * cap) := by
          rcases hp_alloc with h0 | (hheap | hscr)
          · exact Or.inl h0
          · exact Or.inr (Or.inl ⟨hheap.1, le_trans hheap.2 (by unfold globN; rw [hsb_glob]; exact hhp_pla)⟩)
          · exact Or.inr (Or.inr ⟨by rw [hscr_eq_sb]; exact hscr.1, hscr.2⟩)
        have hp_wok_sb : WordsOK sb (p, 8 * cap) :=
          wordsOK_of_unhit_6a hsb_dom_st hp_wok
        have hp_memW_eq : ∀ j, j < cap → memW sb (p + 8 * j) = memW st (p + 8 * j) := by
          intro j hj
          exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hp_unhit
            (by have := hp_wok.1; omega) (by dsimp only; omega) ⟨by dsimp only; omega, by dsimp only; omega⟩
        -- Transport child (globN s0 "ev", 280)
        have hc_unhit : M08IvlUnhit6a st sb (globN s0 "ev", 280) :=
          hunhit_sb (globN s0 "ev", 280) (Or.inr (Or.inr hc_ins))
            (hc_dfo _ hhead_st _ hlhdr_fo) (hc_dfo _ hhead_st _ hfl_fo)
        have hc_wok_sb : WordsOK sb (globN s0 "ev", 280) :=
          wordsOK_of_unhit_6a hsb_dom_st hc_wok
        have hc_ins_sb : Inside (globN s0 "ev", 280) (globN sb "scratch_ptr") scratchEnd := by
          rw [hscr_eq_sb]; exact hc_ins
        have hc_bnd_s0 : globN s0 "ev" + 280 ≤ 2 ^ 64 :=
          (InitECandidate.Solver.Wave8Contracts.M08.ivl_allocated_bound hAr.2 (Or.inr hc_ins)).2
        have hc96_sb : memW sb (globN s0 "ev" + 96) = memW st (globN s0 "ev" + 96) :=
          InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hc_unhit
            (by have := hc_wok.1; omega) (by dsimp only; omega) ⟨by dsimp only; omega, by dsimp only; omega⟩
        -- Transport remaining logs j in [k+1, n)
        have hrem_logs_sb : ∀ j, k + 1 ≤ j → j < n →
            WordAt sb (p + 8 * j) ∧ LogEntryOK sb (memW sb (p + 8 * j)) ∧
              logOwnedIvls sb (memW sb (p + 8 * j)) = logOwnedIvls st (memW st (p + 8 * j)) := by
          intro j hkj hjn
          have hj_cap : j < cap := by omega
          rw [hp_memW_eq j hj_cap]
          obtain ⟨hwa_j, hok_j⟩ := hlogs j (by omega) hjn
          have hwa_sb : WordAt sb (p + 8 * j) := hp_wok_sb.2.2 j (by dsimp only; omega)
          have hmem_j_tl : (memW st (p + 8 * j), 40) ∈
              (List.range (n - (k + 1))).flatMap
                (fun idx => logOwnedIvls st (memW st (p + 8 * ((k + 1) + idx)))) := by
            refine List.mem_flatMap.2 ⟨j - (k + 1), List.mem_range.2 (by omega), ?_⟩
            rw [show (k + 1) + (j - (k + 1)) = j by omega]
            exact List.mem_filter.2 ⟨by simp [logRecordIvls], by simp⟩
          have hmem_j_all : (memW st (p + 8 * j), 40) ∈
              (List.range (n - k)).flatMap
                (fun idx => logOwnedIvls st (memW st (p + 8 * (k + idx)))) := by
            rw [hrng_eq]; exact List.mem_append_right _ hmem_j_tl
          have hu_j : M08IvlUnhit6a s_la post_la (memW st (p + 8 * j), 40) :=
            hunhit_pla _ (Or.inr (Or.inl hok_j.2.1))
              (hlo_fo _ hmem_j_all _ hhead_st _ hlhdr_fo)
              (hlo_fo _ hmem_j_all _ hhead_st _ hfl_fo)
          obtain ⟨hok_pla, hown_pla⟩ := logEntry_unhit_transport_6a
            hsla_BS.arena (hBS_pla.arena.1.memaddrs.trans hsla_BS.arena.1.memaddrs.symm)
            hhp_pla hsys_eq_sb hu_j hok_j
          have hok_sb : LogEntryOK sb (memW st (p + 8 * j)) := by
            have : LogEntryOK { sb with locals := L0, clock := sb.clock } (memW st (p + 8 * j)) := by
              rw [hsb_la]; exact hok_pla
            exact this
          have hown_sb : logOwnedIvls sb (memW st (p + 8 * j)) = logOwnedIvls st (memW st (p + 8 * j)) := by
            have : logOwnedIvls { sb with locals := L0, clock := sb.clock } (memW st (p + 8 * j)) =
                logOwnedIvls post_la (memW st (p + 8 * j)) := by rw [hsb_la]
            exact this.trans hown_pla
          exact ⟨hwa_sb, hok_sb, hown_sb⟩
        have htl_eq : (List.range (n - (k + 1))).flatMap
            (fun j => logOwnedIvls sb (memW sb (p + 8 * ((k + 1) + j)))) =
            (List.range (n - (k + 1))).flatMap
              (fun j => logOwnedIvls st (memW st (p + 8 * ((k + 1) + j)))) := by
          apply List.flatMap_congr
          intro j hj
          have hj_lt := List.mem_range.1 hj
          exact (hrem_logs_sb ((k + 1) + j) (by omega) (by omega)).2.2
        have hch_sb : evmChain sb = evmChain st := by
          have : evmChain { sb with locals := L0, clock := sb.clock } = evmChain post_la := by rw [hsb_la]
          exact (evmChain_lc_fc sb L0 sb.clock).symm.trans (this.trans (hch_pla.trans hch_la_st))
        have hfo_sb_pla : ∀ ec, frameObjects sb ec = frameObjects post_la ec := by
          intro ec
          have : frameObjects { sb with locals := L0, clock := sb.clock } ec = frameObjects post_la ec := by
            rw [hsb_la]
          exact this
        have hht_sb_st : ∀ t ∈ S, htabFootprint sb t = htabFootprint st t := by
          intro t ht
          have : htabFootprint { sb with locals := L0, clock := sb.clock } t = htabFootprint post_la t := by
            rw [hsb_la]
          exact this.trans (hht_pla t ht)
        have hfix_sb_st : fixedObjects sb = fixedObjects st := by
          have : fixedObjects { sb with locals := L0, clock := sb.clock } = fixedObjects post_la := by
            rw [hsb_la]
          exact this.trans hfix_pla
        -- Disjointness of (p, 8*cap) from frameObjects sb
        have hdisj_inside_fresh : ∀ {iv o : Ivl},
            (iv.2 = 0 ∨ Allocated s_la iv) →
            Inside o (globN s_la "heap_ptr") (globN post_la "heap_ptr") →
            Disj iv o := by
          intro iv o hal hins
          rcases hal with h0 | hal'
          · exact Or.inl h0
          · have hd := disj_fresh_of_allocated_6a hsla_BS.arena.2 hBS_pla.arena.2 hhp_pla hal'
            rcases hd with h1 | h2 | h3 | h4
            · exact Or.inl h1
            · dsimp only at h2
              have ho20 : o.2 = 0 := by have := hins.1; have := hins.2; omega
              exact Or.inr (Or.inl ho20)
            · exact Or.inr (Or.inr (Or.inl (by dsimp only at h3 ⊢; exact le_trans h3 hins.1)))
            · exact Or.inr (Or.inr (Or.inr (by dsimp only at h4 ⊢; have := hins.2; omega)))
        have hp_dfo_sb : ∀ ec ∈ evmChain sb, ∀ o ∈ frameObjects sb ec, Disj (p, 8 * cap) o := by
          intro ec hec o ho
          rw [hch_sb] at hec; rw [hfo_sb_pla ec] at ho
          have hec_cons : ec = (globN s_la "ev", globN s_la "cur_cont") ∨ ec ∈ (evmChain s_la).tail := by
            have hcons : evmChain st = (globN s_la "ev", globN s_la "cur_cont") :: (evmChain s_la).tail := by
              rw [hch_la_st]; exact evmChain_cons st
            rw [hcons] at hec; exact List.mem_cons.1 hec
          rcases hec_cons with rfl | htl_ec
          · rcases hfo_hd_pla o ho with ⟨o0, ho0, rfl⟩ | hfresh
            · rcases List.mem_append.1 ho0 with hfo0 | hlo0
              · exact hp_dfo _ hhead_st o hfo0
              · exact hp_dlo o (by rw [hrng_eq]; exact List.mem_append_left _ hlo0)
            · exact hdisj_inside_fresh hp_alloc hfresh
          · rw [hfo_tl_pla ec htl_ec] at ho
            exact hp_dfo ec hec o ho
        -- Disjointness of (globN s0 "ev", 280) from frameObjects sb and htabFootprint sb
        have hc_dfo_sb : ∀ ec ∈ evmChain sb, ∀ o ∈ frameObjects sb ec, Disj (globN s0 "ev", 280) o := by
          intro ec hec o ho
          rw [hch_sb] at hec; rw [hfo_sb_pla ec] at ho
          have hec_cons : ec = (globN s_la "ev", globN s_la "cur_cont") ∨ ec ∈ (evmChain s_la).tail := by
            have hcons : evmChain st = (globN s_la "ev", globN s_la "cur_cont") :: (evmChain s_la).tail := by
              rw [hch_la_st]; exact evmChain_cons st
            rw [hcons] at hec; exact List.mem_cons.1 hec
          rcases hec_cons with rfl | htl_ec
          · rcases hfo_hd_pla o ho with ⟨o0, ho0, rfl⟩ | hfresh
            · rcases List.mem_append.1 ho0 with hfo0 | hlo0
              · exact hc_dfo _ hhead_st o hfo0
              · exact hc_dlo o (by rw [hrng_eq]; exact List.mem_append_left _ hlo0)
            · exact hdisj_inside_fresh (Or.inr (Or.inr hc_ins)) hfresh
          · rw [hfo_tl_pla ec htl_ec] at ho
            exact hc_dfo ec hec o ho
        have hc_dht_sb : ∀ t ∈ S, ∀ o ∈ htabFootprint sb t, Disj (globN s0 "ev", 280) o := by
          intro t ht o ho
          rw [hht_sb_st t ht] at ho
          exact hc_dht t ht o ho
        -- Remaining suffix log intervals disjointness & AvoidsTries on sb
        have hp_dlo_sb : ∀ o ∈ (List.range (n - (k + 1))).flatMap
            (fun j => logOwnedIvls sb (memW sb (p + 8 * ((k + 1) + j)))),
            Disj (p, 8 * cap) o := by
          intro o ho; rw [htl_eq] at ho
          exact hp_dlo o (by rw [hrng_eq]; exact List.mem_append_right _ ho)
        have hc_dlo_sb : ∀ o ∈ (List.range (n - (k + 1))).flatMap
            (fun j => logOwnedIvls sb (memW sb (p + 8 * ((k + 1) + j)))),
            Disj (globN s0 "ev", 280) o := by
          intro o ho; rw [htl_eq] at ho
          exact hc_dlo o (by rw [hrng_eq]; exact List.mem_append_right _ ho)
        have hpw_sb : ((List.range (n - (k + 1))).flatMap
            (fun j => logOwnedIvls sb (memW sb (p + 8 * ((k + 1) + j))))).Pairwise Disj := by
          rw [htl_eq]; exact hpw_tl
        have hlo_fo_sb : ∀ o1 ∈ (List.range (n - (k + 1))).flatMap
            (fun j => logOwnedIvls sb (memW sb (p + 8 * ((k + 1) + j)))),
            ∀ ec ∈ evmChain sb, ∀ o2 ∈ frameObjects sb ec, Disj o1 o2 := by
          intro o1 ho1 ec hec o2 ho2
          rw [htl_eq] at ho1; rw [hch_sb] at hec; rw [hfo_sb_pla ec] at ho2
          have ho1_all : o1 ∈ (List.range (n - k)).flatMap
              (fun j => logOwnedIvls st (memW st (p + 8 * (k + j)))) := by
            rw [hrng_eq]; exact List.mem_append_right _ ho1
          obtain ⟨j0, hj0, ho1_j0⟩ := List.mem_flatMap.1 ho1
          have hj0_lt := List.mem_range.1 hj0
          have ho1_alloc : o1.2 = 0 ∨ Inside o1 sourceBase (globN s_la "heap_ptr") :=
            logOwnedIvls_zero_or_heap_fc (hlogs ((k + 1) + j0) (by omega) (by omega)).2 o1 ho1_j0
          have hec_cons : ec = (globN s_la "ev", globN s_la "cur_cont") ∨ ec ∈ (evmChain s_la).tail := by
            have hcons : evmChain st = (globN s_la "ev", globN s_la "cur_cont") :: (evmChain s_la).tail := by
              rw [hch_la_st]; exact evmChain_cons st
            rw [hcons] at hec; exact List.mem_cons.1 hec
          rcases hec_cons with rfl | htl_ec
          · rcases hfo_hd_pla o2 ho2 with ⟨o0, ho0, rfl⟩ | hfresh
            · rcases List.mem_append.1 ho0 with hfo0 | hlo0
              · exact hlo_fo o1 ho1_all _ hhead_st o2 hfo0
              · exact disj_symm_6a (hdj_k_tl o2 hlo0 o1 ho1)
            · exact hdisj_inside_fresh (ho1_alloc.imp id (fun h => Or.inl h)) hfresh
          · rw [hfo_tl_pla ec htl_ec] at ho2
            exact hlo_fo o1 ho1_all ec hec o2 ho2
        have hlo_ht_sb : ∀ o1 ∈ (List.range (n - (k + 1))).flatMap
            (fun j => logOwnedIvls sb (memW sb (p + 8 * ((k + 1) + j)))),
            ∀ t ∈ S, ∀ o2 ∈ htabFootprint sb t, Disj o1 o2 := by
          intro o1 ho1 t ht o2 ho2
          rw [htl_eq] at ho1; rw [hht_sb_st t ht] at ho2
          exact hlo_ht o1 (by rw [hrng_eq]; exact List.mem_append_right _ ho1) t ht o2 ho2
        have hlo_fix_sb : ∀ o1 ∈ (List.range (n - (k + 1))).flatMap
            (fun j => logOwnedIvls sb (memW sb (p + 8 * ((k + 1) + j)))),
            ∀ o2 ∈ fixedObjects sb, Disj o1 o2 := by
          intro o1 ho1 o2 ho2
          rw [htl_eq] at ho1; rw [hfix_sb_st] at ho2
          exact hlo_fix o1 (by rw [hrng_eq]; exact List.mem_append_right _ ho1) o2 ho2
        have hlo_av_sb : AvoidsTries sb S ((List.range (n - (k + 1))).flatMap
            (fun j => logOwnedIvls sb (memW sb (p + 8 * ((k + 1) + j))))) := by
          let tlIvls := (List.range (n - (k + 1))).flatMap
            (fun j => logOwnedIvls st (memW st (p + 8 * ((k + 1) + j))))
          rw [htl_eq]
          have hav_tl_la : AvoidsTries s_la S tlIvls :=
            (avoidsTries_lc_6 st L0 s_dc.clock S tlIvls).2
              (avoidsTries_sub_6a (fun o ho => by rw [hrng_eq]; exact List.mem_append_right _ ho) hlo_av)
          have hav_tl_pla : AvoidsTries post_la S tlIvls := hav_pla tlIvls hav_tl_la
          have hav_sb_la : AvoidsTries { sb with locals := L0, clock := sb.clock } S tlIvls := by
            rw [hsb_la]; exact hav_tl_pla
          exact (avoidsTries_lc_6 sb L0 sb.clock S tlIvls).1 hav_sb_la
        have hlo_msg_sb : ∀ o1 ∈ (List.range (n - (k + 1))).flatMap
            (fun j => logOwnedIvls sb (memW sb (p + 8 * ((k + 1) + j)))),
            ∀ ec ∈ evmChain sb, Disj (memW sb (ec.1 + 112), 176) o1 := by
          intro o1 ho1 ec hec
          rw [htl_eq] at ho1; rw [hch_sb] at hec
          have hm_sb : memW sb (ec.1 + 112) = memW st (ec.1 + 112) := by
            have h1 : memW sb (ec.1 + 112) = memW post_la (ec.1 + 112) := by
              unfold memW; rw [hsb_mem]
            exact h1.trans (h112_pla ec (hch_la_st.symm ▸ hec))
          rw [hm_sb]
          exact hlo_msg o1 (by rw [hrng_eq]; exact List.mem_append_right _ ho1) ec hec
        -- Locals on sb
        have hi_lk_sb : sb.locals.lookup (ofString "i") =
            some (.val (.word (BitVec.ofNat 64 (k + 1)))) := by
          rw [hsb_def]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hloc_other_sb : ∀ nm : MlS, nm ≠ ofString "i" → sb.locals.lookup nm = st.locals.lookup nm := by
          intro nm hne
          rw [hsb_def, hsc_dc_eq]
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne]
        have hn_lk_sb : sb.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n))) :=
          (hloc_other_sb (ofString "n") (by decide)).trans hn_lk
        have hp_lk_sb : sb.locals.lookup (ofString "p") = some (.val (.word (BitVec.ofNat 64 p))) :=
          (hloc_other_sb (ofString "p") (by decide)).trans hp_lk
        -- Connect hw' to .seq logAppendWhileProg6 cont on sb
        have hw_sb_eq : evaluateHOLFiniteState sb logAppendWhileProg6 = (rw0, wm) := by
          unfold logAppendWhileProg6; exact hw'
        have hseq_sb : evaluateHOLFiniteState sb (.seq logAppendWhileProg6 cont) =
            (some (.returned rv), sk) := by
          rw [evaluateHOLFiniteState_seq_line780, hw_sb_eq]
          rw [hw] at hseq; exact hseq
        obtain ⟨wm1, hwm1_ev, hwm1_cont, hBS_wm1, hhp_wm1, hgk_wm1, hbe_wm1, hch_wm1, hR_wm1,
          hht_wm1, h16_wm1, h40_wm1, h232_wm1, hcwok_wm1, hcins_wm1, hcdht_wm1, hc96_wm1,
          hloc_wm1⟩ :=
          ih L0 p n cap (k + 1) (by omega) (by omega) hn28 hncap hBS_sb
            hi_lk_sb hn_lk_sb hp_lk_sb hp_alloc_sb hp_wok_sb hp_dfo_sb hp_dlo_sb hc_dlo_sb
            (fun j hkj hjn => ⟨(hrem_logs_sb j hkj hjn).1, (hrem_logs_sb j hkj hjn).2.1⟩)
            hpw_sb hlo_fo_sb hlo_ht_sb hlo_fix_sb hlo_av_sb hlo_msg_sb
            hc_wok_sb hc_ins_sb hc_dfo_sb hc_dht_sb hseq_sb
        have hwm_eq : (rw0, wm) = (none, wm1) := hw_sb_eq.symm.trans hwm1_ev
        have hgk_sb : GlobalsKept ["heap_ptr"] st sb := by
          intro g hg; rw [hsb_glob]; exact hgk_pla g hg
        have hhp_sb : globN st "heap_ptr" ≤ globN sb "heap_ptr" := by
          unfold globN; rw [hsb_glob]; exact hhp_pla
        have hR_la_st : OpDispatchSpec.evmR s_la = OpDispatchSpec.evmR st :=
          evmR_lc_fc st L0 s_dc.clock
        have hR_sb : OpDispatchSpec.evmR sb = OpDispatchSpec.evmR st := by
          have h1 : OpDispatchSpec.evmR { sb with locals := L0, clock := sb.clock } =
              OpDispatchSpec.evmR post_la := congrArg OpDispatchSpec.evmR hsb_la
          exact (evmR_lc_fc sb L0 sb.clock).symm.trans (h1.trans (hR_pla.trans hR_la_st))
        have hev_la_st : globN s_la "ev" = globN st "ev" := rfl
        have h16_sb : memW sb (globN st "ev" + 16) = memW st (globN st "ev" + 16) := by
          have h1 : memW sb (globN st "ev" + 16) = memW post_la (globN st "ev" + 16) := by
            unfold memW; rw [hsb_mem]
          have h2 : memW post_la (globN st "ev" + 16) = memW st (globN st "ev" + 16) := h16_pla
          exact h1.trans h2
        have h40_sb : memW sb (globN st "ev" + 40) = memW st (globN st "ev" + 40) := by
          have h1 : memW sb (globN st "ev" + 40) = memW post_la (globN st "ev" + 40) := by
            unfold memW; rw [hsb_mem]
          have h2 : memW post_la (globN st "ev" + 40) = memW st (globN st "ev" + 40) := h40_pla
          exact h1.trans h2
        have h232_sb : memW sb (globN st "ev" + 232) = memW st (globN st "ev" + 232) := by
          have h1 : memW sb (globN st "ev" + 232) = memW post_la (globN st "ev" + 232) := by
            unfold memW; rw [hsb_mem]
          have h2 : memW post_la (globN st "ev" + 232) = memW st (globN st "ev" + 232) := h232_pla
          exact h1.trans h2
        refine ⟨wm1, hwm_eq, hwm1_cont, hBS_wm1, le_trans hhp_sb hhp_wm1,
          globalsKept_trans_6 hgk_sb hgk_wm1, hbe_wm1.trans (hsb_be.trans hbe_pla),
          hch_wm1.trans hch_sb, hR_wm1.trans hR_sb,
          fun t ht => (hht_wm1 t ht).trans (hht_sb_st t ht),
          by rw [hev_eq_sb] at h16_wm1; exact h16_wm1.trans h16_sb,
          by rw [hev_eq_sb] at h40_wm1; exact h40_wm1.trans h40_sb,
          by rw [hev_eq_sb] at h232_wm1; exact h232_wm1.trans h232_sb,
          hcwok_wm1, hcins_wm1, hcdht_wm1, hc96_wm1.trans hc96_sb,
          fun nm hne => (hloc_wm1 nm hne).trans (hloc_other_sb nm hne)⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
