import InitECandidate.Solver.Wave8GuestInv.ContractParts.C18
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21
import InitECandidate.Solver.Wave8GuestInv.R13Shards.GbodyPayloadStateInitShard

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21
open InitECandidate.Solver.Wave8GuestInv.R13PayloadStateInit

/-! ## Helper lemmas for `gbody_payload_header` -/

private theorem clock_storeByte {F : Type} (s : PanSemStateFiniteExact 64 F) (a v : ExpHOL 64) :
    (evaluateHOLFiniteState s (.storeByte a v)).2.clock = s.clock := by
  rw [evaluateHOLFiniteState_storeByte]
  repeat' split
  all_goals (try dsimp only)

private theorem Hoare_store_fall {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {dst src : ExpHOL 64}
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64) (v : ValueHOL 64)
      (mem' : BitVec 64 → HolWordLab 64),
      P s → evalAt s dst = some (.val (.word x)) → evalAt s src = some v →
      @panMemStoresHOL 64 _ x (flattenHOL v) s.memaddrs
        (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem' →
      Q { s with memory := mem' }) :
    Hoare P (.store dst src) (fun r t => r = none → Q t) := by
  refine ⟨fun {F} s _ hP _ hr => ?_⟩
  rw [evaluateHOLFiniteState_store] at hr ⊢
  revert hr
  split
  · rename_i x hx
    split
    · rename_i v hv
      rcases hm : @panMemStoresHOL 64 _ x (flattenHOL v) s.memaddrs
          (fun a => Classical.propDecidable (s.memaddrs a)) s.memory with _ | mem'
      · simp
      · intro _
        exact h s x v mem' hP hx hv hm
    · simp
  · simp

private theorem Hoare_storeByte_fall {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {dst src : ExpHOL 64}
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (x w : BitVec 64)
      (mem' : BitVec 64 → HolWordLab 64),
      P s → evalAt s dst = some (.val (.word x)) → evalAt s src = some (.val (.word w)) →
      s.memaddrs (panByteAlignHOL x) →
      (∃ u : BitVec 64, mem' (panByteAlignHOL x) = .word u) →
      (∀ a : BitVec 64, a ≠ panByteAlignHOL x → mem' a = s.memory a) →
      Q { s with memory := mem' }) :
    Hoare P (.storeByte dst src) (fun r t => r = none → Q t) := by
  refine ⟨fun {F} s _ hP _ hr => ?_⟩
  rw [evaluateHOLFiniteState_storeByte] at hr ⊢
  revert hr
  rcases hx : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst with _ | vx
  · simp
  · rcases vx with ⟨⟨x⟩⟩ | _ | _
    · rcases hw : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) src with _ | vw
      · simp
      · rcases vw with ⟨⟨w⟩⟩ | _ | _
        · dsimp only
          split
          · rename_i m' hst
            unfold panMemStoreByteWord8HOL at hst
            rcases hcell : s.memory (panByteAlignHOL x) with ⟨cell⟩
            have hcell' : (s.6 (panByteAlignHOL x)).1 = cell := by
              rw [show s.6 = s.memory from rfl, hcell]
            dsimp only at hst
            rw [hcell'] at hst
            split at hst
            · rename_i hdom
              injection hst with hm'
              subst hm'
              intro _
              exact h s x w _ hP hx hw hdom ⟨_, if_pos rfl⟩ (fun a hne => if_neg hne)
            · cases hst
          · simp
        · simp
        · simp
    · simp
    · simp

private theorem worldTypedWith_setGlobal_untracked {F : Type} {s : PanSemStateFiniteExact 64 F}
    {gname : MlS} {w : BitVec 64} {S Nd : List Nat}
    (hgb : ∀ gn ∈ globalBuffers, ofString gn.1 ≠ gname)
    (hgtr : ∀ g ∈ globalTableRoots, ofString g ≠ gname)
    (hj : ofString "journal" ≠ gname)
    (hjc : ofString "journal_cap" ≠ gname)
    (hjn : ofString "journal_n" ≠ gname)
    (hhp : ofString "heap_ptr" ≠ gname)
    (hfm : ofString "frame_mem_ptr" ≠ gname)
    (hsc : ofString "scratch_ptr" ≠ gname)
    (hAs : ArenaReady s) (hW : WorldTypedWith s S Nd) :
    let post := setGlobalHOLFinite gname (.val (.word w)) s
    ArenaReady post ∧
    WorldTypedWith post S Nd ∧
    worldOwned post S Nd = worldOwned s S Nd := by
  intro post
  have hlu : ∀ n : String, ofString n ≠ gname → globN post n = globN s n := fun n hne => by
    simp [post, globN, setGlobalHOLFinite, HolFiniteMapExact.update, FUPDATE, Ne.symm hne]
  have hAp : ArenaReady post := by
    refine ⟨guestInv_congr (s := s) rfl rfl rfl rfl hAs.1, ?_⟩
    have hgw : GlobalsWord post := globalsWord_update gname w rfl hAs.2.2.2.2.2.2.2.2.2
    unfold ArenaOK
    rw [hlu "heap_ptr" hhp, hlu "frame_mem_ptr" hfm, hlu "scratch_ptr" hsc]
    exact ⟨hAs.2.1, hAs.2.2.1, hAs.2.2.2.1, hAs.2.2.2.2.1, hAs.2.2.2.2.2.1,
      hAs.2.2.2.2.2.2.1, hAs.2.2.2.2.2.2.2.1, hAs.2.2.2.2.2.2.2.2.1, hgw⟩
  have hag : AllocatorGrows s post := by
    unfold AllocatorGrows
    rw [hlu "heap_ptr" hhp, hlu "scratch_ptr" hsc]
    exact ⟨le_rfl, le_rfl⟩
  have hgs : WorldGlobalsSame s post :=
    ⟨fun gn hgn => hlu gn.1 (hgb gn hgn),
     fun g hg => hlu g (hgtr g hg),
     hlu "journal" hj, hlu "journal_cap" hjc, hlu "journal_n" hjn⟩
  have hunhit : ∀ i : Ivl, IvlUnhit s post i := fun _ _ _ _ => rfl
  have hres := worldTypedWith_congr_bo hAs hAp rfl hag hgs hW
    (fun _ _ i _ => hunhit i)
    (fun _ => hunhit _) (fun _ => hunhit _) (fun _ => hunhit _) (fun _ => hunhit _)
    (fun i _ _ => hunhit i) (fun i _ => hunhit i) (fun o _ => hunhit o)
    (fun _ _ _ => rfl) ⟨rfl, rfl⟩
  exact ⟨hAp, hres.1, hres.2.1⟩

private theorem evalAt_load_one_word {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hg : GuestInv s) {addr : ExpHOL 64} {v : ValueHOL 64}
    (hev : evalAt s (.load .one addr) = some v) :
    ∃ a w : BitVec 64, evalAt s addr = some (.val (.word a)) ∧
      v = .val (.word w) ∧ w.toNat = memW s a.toNat ∧
      a.toNat % 8 = 0 ∧ sourceBase ≤ a.toNat ∧ a.toNat < heapEnd := by
  simp only [evalAt, evalHOLExact] at hev
  rcases ha : @evalHOLExact 64 F _ s.toExact (fun address => Classical.propDecidable (s.memaddrs address)) addr with _ | va
  · rw [ha] at hev; simp at hev
  · rw [ha] at hev
    cases va with
    | val wl =>
      cases wl with
      | word a =>
        simp only [memLoadHOLExact] at hev
        split_ifs at hev with _ hdom
        simp only [Option.some.injEq] at hev
        rw [hg.memaddrs, ordinaryDomain_iff] at hdom
        cases hmem : s.memory a with
        | word w =>
          rw [hmem] at hev
          have hmemW : memW s a.toNat = w.toNat := by
            unfold memW; simp [BitVec.ofNat_toNat, hmem]
          exact ⟨a, w, ha, hev.symm, hmemW.symm, hdom.1, hdom.2.1, hdom.2.2⟩
    | rStruct _ => simp at hev
    | nStruct _ => simp at hev

private theorem len_le_one_of_shape_one {v : ValueHOL 64}
    (hsh : shapeOfHOLExact v = .one) : (flattenHOL v).length ≤ 1 := by
  cases v with
  | val wl => cases wl; simp [flattenHOL]
  | rStruct _ => simp [shapeOfHOLExact] at hsh
  | nStruct _ _ => simp [shapeOfHOLExact] at hsh

private theorem len_le_four_of_shape_comb4 {v : ValueHOL 64}
    (hsh : shapeEqHOL (shapeOfHOLExact v) (.comb [.one, .one, .one, .one]) = true) :
    (flattenHOL v).length ≤ 4 := by
  have heq := (shapeEqHOL_eq_true _ _).1 hsh
  cases v with
  | val _ => simp [shapeOfHOLExact] at heq
  | nStruct _ _ => simp [shapeOfHOLExact] at heq
  | rStruct vs =>
    simp only [shapeOfHOLExact, ShapeHOL.comb.injEq] at heq
    rcases vs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩⟩ <;> simp at heq
    rcases heq with ⟨h0, h1, h2, h3⟩
    have l0 := len_le_one_of_shape_one h0
    have l1 := len_le_one_of_shape_one h1
    have l2 := len_le_one_of_shape_one h2
    have l3 := len_le_one_of_shape_one h3
    simp only [flattenHOL, List.map, List.flatten_cons, List.flatten_nil, List.length_append, List.length_nil]
    omega

private theorem evalAt_src_len_le_one {F : Type} {s : PanSemStateFiniteExact 64 F}
    {src : ExpHOL 64} {v : ValueHOL 64}
    (hshape1 : ∀ {e : ExpHOL 64} {u : ValueHOL 64},
      (e = .const 1#64 ∨
       (∃ a b, e = .op .add [a, b]) ∨
       (∃ addr, e = .load .one addr)) →
      evalAt s e = some u → (flattenHOL u).length ≤ 1)
    (he : src = .const 1#64 ∨ (∃ a b, src = .op .add [a, b]) ∨ (∃ addr, src = .load .one addr))
    (hev : evalAt s src = some v) :
    (flattenHOL v).length ≤ 1 :=
  hshape1 he hev

private theorem evalAt_simple_word_len {F : Type} {s : PanSemStateFiniteExact 64 F} :
    ∀ {e : ExpHOL 64} {u : ValueHOL 64},
      (e = .const 1#64 ∨
       (∃ a b, e = .op .add [a, b]) ∨
       (∃ addr, e = .load .one addr)) →
      evalAt s e = some u → (flattenHOL u).length ≤ 1 := by
  intro e u hkind hev
  rcases hkind with rfl | ⟨a, b, rfl⟩ | ⟨addr, rfl⟩
  · simp only [evalAt, evalHOLExact, Option.some.injEq] at hev
    subst hev; simp [flattenHOL]
  · simp only [evalAt, evalHOLExact] at hev
    rcases hl : @evalListHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) [a, b] with _ | vs
    · rw [hl] at hev; simp at hev
    · rw [hl] at hev; dsimp only at hev
      split_ifs at hev
      simp only [Option.map, Option.some.injEq] at hev
      rcases hw : wordOpHOL .add (vs.map valueWord) with _ | w
      · rw [hw] at hev; simp at hev
      · rw [hw] at hev; simp only [Option.some.injEq] at hev; subst hev; simp [flattenHOL]
  · simp only [evalAt, evalHOLExact] at hev
    rcases ha : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) addr with _ | va
    · rw [ha] at hev; simp at hev
    · rw [ha] at hev
      cases va with
      | val wl =>
        cases wl with
        | word wa =>
          simp only [memLoadHOLExact] at hev
          split_ifs at hev
          simp only [Option.some.injEq] at hev
          subst hev; simp [flattenHOL]
      | rStruct _ => simp at hev
      | nStruct _ => simp at hev

/-! ## Bundle of heap blocks tracked across `payload_header` -/

def AllBlocksGood {F : Type} (s : PanSemStateFiniteExact 64 F) (S Nd : List Nat)
    (bs : List Ivl) : Prop :=
  ∀ b ∈ bs, b.1 % 8 = 0 ∧ b.2 % 8 = 0 ∧ Inside b sourceBase (globN s "heap_ptr") ∧
    WordsOK s b ∧ (∀ o ∈ worldOwned s S Nd, Disj b o)

theorem allBlocksGood_nil {F : Type} (s : PanSemStateFiniteExact 64 F) (S Nd : List Nat) :
    AllBlocksGood s S Nd [] := by
  intro b hb; simp at hb

theorem allBlocksGood_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S Nd : List Nat) (bs : List Ivl) :
    AllBlocksGood { s with locals := locals, clock := k } S Nd bs ↔ AllBlocksGood s S Nd bs := by
  have hmem : ∀ b : Ivl, WordsOK { s with locals := locals, clock := k } b ↔ WordsOK s b :=
    fun _ => Iff.rfl
  have hown : worldOwned { s with locals := locals, clock := k } S Nd = worldOwned s S Nd := rfl
  have hhp : globN { s with locals := locals, clock := k } "heap_ptr" = globN s "heap_ptr" := rfl
  simp only [AllBlocksGood, hmem, hown, hhp]

theorem WorldStep_preserves_inputAndBlocks
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {F : Type} {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {S Nd : List Nat} {si : Nat} {bs : List Ivl}
    (hIA : InputAtWith s S Nd si)
    (hBs : AllBlocksGood s S Nd bs)
    (hws : WorldStep R gw keep Q s r post)
    (hR_z : ∀ j ∈ R s, j.2 = 0 → j.1 % 8 = 0)
    (hR_ti : IvlsDisj (R s) (worldTypedIvls s S Nd))
    (hR_in : IvlsDisj (inputCells s si) (R s))
    (hR_bs : IvlsDisj bs (R s)) :
    ∃ S' Nd', InputAtWith post S' Nd' si ∧
      AllBlocksGood post S' Nd' bs ∧
      (∀ b ∈ bs, IvlUnhit s post b) ∧
      (∀ c ∈ inputCells s si, IvlUnhit s post c) ∧
      Q s r post S' Nd' := by
  obtain ⟨S', Nd', _, hIA', hog, hfr, hQ⟩ :=
    WorldStep.preserves_inputAtWith hIA hws hR_z hR_ti hR_in
  have hold_z := worldOwned_zero_aligned hIA.2.1
  have h_bs_surv : ∀ b ∈ bs,
      Inside b sourceBase (globN post "heap_ptr") ∧
      (∀ o ∈ worldOwned post S' Nd', Disj b o) ∧
      IvlUnhit s post b := by
    intro b hb
    obtain ⟨hb1, hb2, hbin, _, hbow⟩ := hBs b hb
    exact heap_ivl_survives_step hIA.1.2 hws.2.1 hog hfr hold_z hR_z hb1 hb2 hbin
      hbow (fun j hj => hR_bs b hb j hj)
  have h_ic_surv : ∀ c ∈ inputCells s si, IvlUnhit s post c := by
    intro c hc
    obtain ⟨hcin, hcw⟩ := hIA.2.2.1 c hc
    exact (heap_ivl_survives_step hIA.1.2 hws.2.1 hog hfr hold_z hR_z hcw.1 hcw.2.1 hcin
      (fun j hj => hIA.2.2.2.1 c hc j hj) (fun j hj => hR_in c hc j hj)).2.2
  refine ⟨S', Nd', hIA', ?_, (fun b hb => (h_bs_surv b hb).2.2), h_ic_surv, hQ⟩
  intro b hb
  obtain ⟨hb1, hb2, _, hbw, _⟩ := hBs b hb
  exact ⟨hb1, hb2, (h_bs_surv b hb).1,
    wordsOK_transfer hIA.1.1 hws.1.1 hbw,
    (h_bs_surv b hb).2.1⟩

theorem store_in_tracked_block {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si : Nat} {bs : List Ivl}
    {base sz off : Nat} {w_base x : BitVec 64} {v : ValueHOL 64}
    {mem' : BitVec 64 → HolWordLab 64}
    (hIA : InputAtWith s S Nd si)
    (hBs : AllBlocksGood s S Nd bs)
    (hmem_b : (base, sz) ∈ bs)
    (hd_ic : IvlsDisj (inputCells s si) [(base, sz)])
    (hbase_lu : w_base.toNat = base)
    (hoff8 : off % 8 = 0)
    (hx_eq : x = w_base + BitVec.ofNat 64 off)
    (hoff_fit : off + 8 * (flattenHOL v).length ≤ sz)
    (hst : @panMemStoresHOL 64 _ x (flattenHOL v) s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem') :
    InputAtWith { s with memory := mem' } S Nd si ∧
    AllBlocksGood { s with memory := mem' } S Nd bs ∧
    (∀ b : Ivl, (b.2 = 0 → b.1 % 8 = 0) → Disj b (base, sz) → IvlUnhit s { s with memory := mem' } b) := by
  obtain ⟨hb1, hb2, hbin, hbw, hbow⟩ := hBs (base, sz) hmem_b
  have hWT_res := store_in_block_preserves_worldTypedWith hIA.2.1 hIA.1 hbase_lu hb1 hb2 hoff8
    hbin (fun i hi o ho => by simp only [List.mem_singleton] at hi; subst hi; exact hbow o ho)
    hx_eq hoff_fit hst
  have h264 : heapEnd < 2 ^ 64 ∧ heapLimit ≤ heapEnd := ⟨by decide, by decide⟩
  have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hIA.1.2.2.1
  have hbsz_hi : base + sz ≤ heapLimit := Nat.le_trans hbin.2 hhp_lim
  have hx_nat : x.toNat = base + off := by
    rw [hx_eq, BitVec.toNat_add, hbase_lu, BitVec.toNat_ofNat]
    have hoff_lt : off < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hoff_lt]
    exact Nat.mod_eq_of_lt (by omega)
  have hdisj_unhit : ∀ b : Ivl, (b.2 = 0 → b.1 % 8 = 0) → Disj b (base, sz) → IvlUnhit s { s with memory := mem' } b := by
    intro b hbz hdb a ha8 hhit
    apply panMemStoresHOL_frame (flattenHOL v) x s.memory mem' hst a
    intro k hk h_eq
    have ha_nat : a.toNat = base + off + 8 * k := by
      rw [h_eq, BitVec.toNat_add, hx_nat, BitVec.toNat_ofNat]
      have hk_lt : 8 * k < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt hk_lt]
      simpa [Nat.add_assoc] using Nat.mod_eq_of_lt (show base + off + 8 * k < 2 ^ 64 by omega)
    have ha_mod8 : a.toNat % 8 = 0 := ha8
    cases b with
    | mk b1 b2 =>
      dsimp only at hb1 hb2 hbz
      obtain ⟨hhit1, hhit2⟩ := hhit
      rcases hdb with hb0 | hsz0 | hle1 | hle2
      · dsimp only at hb0 hhit1 hhit2; have := hbz hb0; omega
      · dsimp only at hsz0 hhit1 hhit2; omega
      · dsimp only at hle1 hhit1 hhit2; omega
      · dsimp only at hle2 hhit1 hhit2; omega
  set post := { s with memory := mem' }
  have hic_u : ∀ c ∈ inputCells s si, IvlUnhit s post c :=
    fun c hc => hdisj_unhit c (fun _ => (hIA.2.2.1 c hc).2.1) (hd_ic c hc (base, sz) (by simp))
  have hsi_mem : (si, 40) ∈ inputCells s si := by simp [inputCells]
  obtain ⟨hsi_in, hsi_w⟩ := hIA.2.2.1 (si, 40) hsi_mem
  have hsi_u := hic_u (si, 40) hsi_mem
  have hsi0 : memW post si = memW s si :=
    memW_eq_of_ivlUnhit hsi_u hsi_w.1 (by unfold Inside at hsi_in; omega) ⟨le_rfl, by omega⟩
  have hsi32 : memW post (si + 32) = memW s (si + 32) :=
    memW_eq_of_ivlUnhit hsi_u (by have := hsi_w.1; omega) (by unfold Inside at hsi_in; omega) ⟨by omega, by omega⟩
  set pl := memW s si
  set rq := memW s (si + 32)
  have hpl_mem : (pl, 136) ∈ inputCells s si := by simp [inputCells, pl]
  obtain ⟨hpl_in, hpl_w⟩ := hIA.2.2.1 (pl, 136) hpl_mem
  have hpl_u := hic_u (pl, 136) hpl_mem
  have hpl_word : ∀ off', off' % 8 = 0 → off' + 8 ≤ 136 → memW post (pl + off') = memW s (pl + off') :=
    fun off' hoff8' hhi' =>
      memW_eq_of_ivlUnhit hpl_u (by have := hpl_w.1; omega) (by unfold Inside at hpl_in; omega) ⟨by omega, by omega⟩
  have hpl24 := hpl_word 24 (by omega) (by omega)
  have hpl32 := hpl_word 32 (by omega) (by omega)
  have hpl40 := hpl_word 40 (by omega) (by omega)
  have hic_eq : inputCells post si = inputCells s si := by
    simp only [inputCells, hsi0, hsi32]
    change [(si, 40), (pl, 136), (rq, 80), (memW post (pl + 32), 16 * memW post (pl + 40))] =
           [(si, 40), (pl, 136), (rq, 80), (memW s (pl + 32), 16 * memW s (pl + 40))]
    rw [hpl32, hpl40]
  have hrq_mem : (rq, 80) ∈ inputCells s si := by simp [inputCells, rq]
  obtain ⟨hrq_in, hrq_w⟩ := hIA.2.2.1 (rq, 80) hrq_mem
  have hrq_u := hic_u (rq, 80) hrq_mem
  have hptxs_mem : (memW s (pl + 32), 16 * memW s (pl + 40)) ∈ inputCells s si := by simp [inputCells, pl]
  obtain ⟨hptxs_in, hptxs_w⟩ := hIA.2.2.1 _ hptxs_mem
  have hptxs_u := hic_u _ hptxs_mem
  have hIA_post : InputAtWith post S Nd si := by
    refine ⟨hWT_res.1, hWT_res.2.1, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hic_eq]
      exact fun i hi => ⟨(hIA.2.2.1 i hi).1, wordsOK_transfer hIA.1.1 hWT_res.1.1 (hIA.2.2.1 i hi).2⟩
    · rw [hic_eq, hWT_res.2.2.1]; exact hIA.2.2.2.1
    · rw [hsi0]; change memW post (pl + 40) < 2 ^ 63; rw [hpl40]; exact hIA.2.2.2.2.1
    · rw [hsi0]; change PayloadAt post pl
      refine ⟨wordsOK_transfer hIA.1.1 hWT_res.1.1 hIA.2.2.2.2.2.1.1, ?_, ?_, ?_⟩
      · rw [hpl24]; exact hIA.2.2.2.2.2.1.2.1
      · rw [hpl40]; exact hIA.2.2.2.2.2.1.2.2.1
      · rw [hpl32, hpl40]; intro idx hidx
        have hce : memW post (memW s (pl + 32) + 16 * idx + 8) = memW s (memW s (pl + 32) + 16 * idx + 8) :=
          memW_eq_of_ivlUnhit hptxs_u (by have := hptxs_w.1; omega)
            (by unfold Inside at hptxs_in; omega) ⟨by dsimp; omega, by dsimp; omega⟩
        rw [hce]; exact hIA.2.2.2.2.2.1.2.2.2 idx hidx
    · rw [hsi32]; change RequestsAt post rq
      refine ⟨wordsOK_transfer hIA.1.1 hWT_res.1.1 hIA.2.2.2.2.2.2.1, fun idx hidx => ?_⟩
      have hce : memW post (rq + 16 * idx + 8) = memW s (rq + 16 * idx + 8) :=
        memW_eq_of_ivlUnhit hrq_u (by have := hrq_w.1; omega)
          (by unfold Inside at hrq_in; omega) ⟨by omega, by omega⟩
      rw [hce]; exact hIA.2.2.2.2.2.2.2 idx hidx
  have hBs_post : AllBlocksGood post S Nd bs := by
    intro b hb
    obtain ⟨b1, b2, bin, bw, bow⟩ := hBs b hb
    refine ⟨b1, b2, bin, wordsOK_transfer hIA.1.1 hWT_res.1.1 bw, ?_⟩
    rw [hWT_res.2.2.1]; exact bow
  exact ⟨hIA_post, hBs_post, hdisj_unhit⟩

private theorem panMemStoresHOL_word_memW {x w : BitVec 64}
    {dom : BitVec 64 → Prop} {dec : DecidablePred dom}
    {mem mem' : BitVec 64 → HolWordLab 64}
    (hst : @panMemStoresHOL 64 _ x [.word w] dom dec mem = some mem') :
    mem' x = .word w := by
  unfold panMemStoresHOL panMemStoreHOL at hst
  split_ifs at hst with hdom
  unfold panMemStoresHOL at hst
  injection hst with hm'
  subst hm'
  simp [Function.update]

/-! ## Progressive state invariants inside `payload_header` -/

/-- State after binding `pl := *(si+0)` and `raw := *(pl+0)`. -/
def PH_S0 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_si w_pl w_raw : BitVec 64, ∃ S Nd : List Nat,
    InputAtWith s S Nd w_si.toNat ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "raw") = some (.val (.word w_raw)) ∧
    w_pl.toNat = memW s w_si.toNat

/-- State with `h` (248 B) allocated. -/
def PH_H (extra136 : Bool) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_si w_pl w_raw w_h : BitVec 64, ∃ S Nd : List Nat,
    InputAtWith s S Nd w_si.toNat ∧
    AllBlocksGood s S Nd [(w_h.toNat, 248)] ∧
    IvlsDisj (inputCells s w_si.toNat) [(w_h.toNat, 248)] ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "raw") = some (.val (.word w_raw)) ∧
    s.locals.lookup (ofString "h") = some (.val (.word w_h)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    (extra136 = true → memW s (w_h.toNat + 136) ≤ 32)

/-- State with `h` (248 B) and `oh` (32 B). -/
def PH_OH : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_si w_pl w_raw w_h w_oh : BitVec 64, ∃ S Nd : List Nat,
    InputAtWith s S Nd w_si.toNat ∧
    AllBlocksGood s S Nd [(w_h.toNat, 248), (w_oh.toNat, 32)] ∧
    IvlsDisj (inputCells s w_si.toNat) [(w_h.toNat, 248), (w_oh.toNat, 32)] ∧
    Disj (w_h.toNat, 248) (w_oh.toNat, 32) ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "raw") = some (.val (.word w_raw)) ∧
    s.locals.lookup (ofString "h") = some (.val (.word w_h)) ∧
    s.locals.lookup (ofString "oh") = some (.val (.word w_oh)) ∧
    w_pl.toNat = memW s w_si.toNat

/-- State with `h` (248 B), `oh` (32 B), `tmp` (8 B). -/
def PH_TMP : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_si w_pl w_raw w_h w_oh w_tmp : BitVec 64, ∃ S Nd : List Nat,
    InputAtWith s S Nd w_si.toNat ∧
    AllBlocksGood s S Nd [(w_h.toNat, 248), (w_oh.toNat, 32), (w_tmp.toNat, 8)] ∧
    IvlsDisj (inputCells s w_si.toNat) [(w_h.toNat, 248), (w_oh.toNat, 32), (w_tmp.toNat, 8)] ∧
    Disj (w_h.toNat, 248) (w_oh.toNat, 32) ∧
    Disj (w_h.toNat, 248) (w_tmp.toNat, 8) ∧
    Disj (w_oh.toNat, 32) (w_tmp.toNat, 8) ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "raw") = some (.val (.word w_raw)) ∧
    s.locals.lookup (ofString "h") = some (.val (.word w_h)) ∧
    s.locals.lookup (ofString "oh") = some (.val (.word w_oh)) ∧
    s.locals.lookup (ofString "tmp") = some (.val (.word w_tmp)) ∧
    w_pl.toNat = memW s w_si.toNat

/-- State with `h` (248 B) and `txr` (32 B), parameterized by whether `h+136 ≤ 32` is established. -/
def PH_TXR (extra136 : Bool) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_si w_pl w_raw w_h w_txr : BitVec 64, ∃ S Nd : List Nat,
    InputAtWith s S Nd w_si.toNat ∧
    AllBlocksGood s S Nd [(w_h.toNat, 248), (w_txr.toNat, 32)] ∧
    IvlsDisj (inputCells s w_si.toNat) [(w_h.toNat, 248), (w_txr.toNat, 32)] ∧
    Disj (w_h.toNat, 248) (w_txr.toNat, 32) ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "raw") = some (.val (.word w_raw)) ∧
    s.locals.lookup (ofString "h") = some (.val (.word w_h)) ∧
    s.locals.lookup (ofString "txr") = some (.val (.word w_txr)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    (extra136 = true → memW s (w_h.toNat + 136) ≤ 32)

/-- State with `h`, `txr`, and `z8` (8 B), with `h+136 ≤ 32`. -/
def PH_Z8 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_si w_pl w_raw w_h w_txr w_z8 : BitVec 64, ∃ S Nd : List Nat,
    InputAtWith s S Nd w_si.toNat ∧
    AllBlocksGood s S Nd [(w_h.toNat, 248), (w_txr.toNat, 32), (w_z8.toNat, 8)] ∧
    IvlsDisj (inputCells s w_si.toNat) [(w_h.toNat, 248), (w_txr.toNat, 32), (w_z8.toNat, 8)] ∧
    Disj (w_h.toNat, 248) (w_txr.toNat, 32) ∧
    Disj (w_h.toNat, 248) (w_z8.toNat, 8) ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "raw") = some (.val (.word w_raw)) ∧
    s.locals.lookup (ofString "h") = some (.val (.word w_h)) ∧
    s.locals.lookup (ofString "txr") = some (.val (.word w_txr)) ∧
    s.locals.lookup (ofString "z8") = some (.val (.word w_z8)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    memW s (w_h.toNat + 136) ≤ 32

/-- State with `bf` of shape `.comb [.one, .one, .one, .one]` also bound. -/
def PH_BF : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => PH_TXR true s ∧
    ∃ v_bf : ValueHOL 64, s.locals.lookup (ofString "bf") = some v_bf ∧
      shapeEqHOL (shapeOfHOLExact v_bf) (.comb [.one, .one, .one, .one]) = true

/-- State with `h` (248 B), `txr` (32 B), `wr` (32 B), and `h+136 ≤ 32`. -/
def PH_WR : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_si w_pl w_h w_txr w_wr : BitVec 64, ∃ S Nd : List Nat,
    InputAtWith s S Nd w_si.toNat ∧
    AllBlocksGood s S Nd [(w_h.toNat, 248), (w_txr.toNat, 32), (w_wr.toNat, 32)] ∧
    IvlsDisj (inputCells s w_si.toNat) [(w_h.toNat, 248), (w_txr.toNat, 32), (w_wr.toNat, 32)] ∧
    Disj (w_h.toNat, 248) (w_txr.toNat, 32) ∧
    Disj (w_h.toNat, 248) (w_wr.toNat, 32) ∧
    Disj (w_txr.toNat, 32) (w_wr.toNat, 32) ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "h") = some (.val (.word w_h)) ∧
    s.locals.lookup (ofString "txr") = some (.val (.word w_txr)) ∧
    s.locals.lookup (ofString "wr") = some (.val (.word w_wr)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    memW s (w_h.toNat + 136) ≤ 32

/-- State with `rh` (32 B) also allocated. -/
def PH_RH : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_si w_pl w_h w_txr w_wr w_rh : BitVec 64, ∃ S Nd : List Nat,
    InputAtWith s S Nd w_si.toNat ∧
    AllBlocksGood s S Nd [(w_h.toNat, 248), (w_txr.toNat, 32), (w_wr.toNat, 32), (w_rh.toNat, 32)] ∧
    IvlsDisj (inputCells s w_si.toNat) [(w_h.toNat, 248), (w_txr.toNat, 32), (w_wr.toNat, 32), (w_rh.toNat, 32)] ∧
    Disj (w_h.toNat, 248) (w_txr.toNat, 32) ∧
    Disj (w_h.toNat, 248) (w_wr.toNat, 32) ∧
    Disj (w_txr.toNat, 32) (w_wr.toNat, 32) ∧
    Disj (w_h.toNat, 248) (w_rh.toNat, 32) ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "h") = some (.val (.word w_h)) ∧
    s.locals.lookup (ofString "txr") = some (.val (.word w_txr)) ∧
    s.locals.lookup (ofString "wr") = some (.val (.word w_wr)) ∧
    s.locals.lookup (ofString "rh") = some (.val (.word w_rh)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    memW s (w_h.toNat + 136) ≤ 32

/-- State with `bh` (32 B) also allocated. -/
def PH_BH : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_si w_pl w_h w_txr w_wr w_rh w_bh : BitVec 64, ∃ S Nd : List Nat,
    InputAtWith s S Nd w_si.toNat ∧
    AllBlocksGood s S Nd [(w_h.toNat, 248), (w_txr.toNat, 32), (w_wr.toNat, 32), (w_rh.toNat, 32), (w_bh.toNat, 32)] ∧
    IvlsDisj (inputCells s w_si.toNat) [(w_h.toNat, 248), (w_txr.toNat, 32), (w_wr.toNat, 32), (w_rh.toNat, 32), (w_bh.toNat, 32)] ∧
    Disj (w_h.toNat, 248) (w_txr.toNat, 32) ∧
    Disj (w_h.toNat, 248) (w_wr.toNat, 32) ∧
    Disj (w_txr.toNat, 32) (w_wr.toNat, 32) ∧
    Disj (w_h.toNat, 248) (w_rh.toNat, 32) ∧
    Disj (w_h.toNat, 248) (w_bh.toNat, 32) ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "h") = some (.val (.word w_h)) ∧
    s.locals.lookup (ofString "txr") = some (.val (.word w_txr)) ∧
    s.locals.lookup (ofString "wr") = some (.val (.word w_wr)) ∧
    s.locals.lookup (ofString "rh") = some (.val (.word w_rh)) ∧
    s.locals.lookup (ofString "bh") = some (.val (.word w_bh)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    memW s (w_h.toNat + 136) ≤ 32

/-- State after `nwd` is bound, before `wd_rlp_slices := alloc(nwd * 16 + 16)`. -/
def PH_NWD : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_si w_pl w_wr w_nwd : BitVec 64, ∃ S Nd : List Nat,
    InputAtWith s S Nd w_si.toNat ∧
    AllBlocksGood s S Nd [(w_wr.toNat, 32)] ∧
    IvlsDisj (inputCells s w_si.toNat) [(w_wr.toNat, 32)] ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "wr") = some (.val (.word w_wr)) ∧
    s.locals.lookup (ofString "nwd") = some (.val (.word w_nwd)) ∧
    w_pl.toNat = memW s w_si.toNat

/-- State after `wd_rlp_slices := alloc(nwd * 16 + 16)` (before `dec "i"`). -/
def PH_WDS0 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_si w_pl w_wr w_nwd w_wds : BitVec 64, ∃ S Nd : List Nat,
    let alloc_sz := (w_nwd * 16#64 + 16#64).toNat
    InputAtWith s S Nd w_si.toNat ∧
    AllBlocksGood s S Nd [(w_wr.toNat, 32), (w_wds.toNat, alloc_sz)] ∧
    IvlsDisj (inputCells s w_si.toNat) [(w_wr.toNat, 32), (w_wds.toNat, alloc_sz)] ∧
    Disj (w_wr.toNat, 32) (w_wds.toNat, alloc_sz) ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "wr") = some (.val (.word w_wr)) ∧
    s.locals.lookup (ofString "nwd") = some (.val (.word w_nwd)) ∧
    s.globals.lookup (ofString "wd_rlp_slices") = some (.val (.word w_wds)) ∧
    w_pl.toNat = memW s w_si.toNat

/-- Withdrawal loop invariant (`i` from `0` up to `nwd` signed). -/
def PH_LOOP : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_si w_pl w_wr w_nwd w_wds w_i : BitVec 64, ∃ S Nd : List Nat,
    let alloc_sz := (w_nwd * 16#64 + 16#64).toNat
    InputAtWith s S Nd w_si.toNat ∧
    AllBlocksGood s S Nd [(w_wr.toNat, 32), (w_wds.toNat, alloc_sz)] ∧
    IvlsDisj (inputCells s w_si.toNat) [(w_wr.toNat, 32), (w_wds.toNat, alloc_sz)] ∧
    Disj (w_wr.toNat, 32) (w_wds.toNat, alloc_sz) ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "wr") = some (.val (.word w_wr)) ∧
    s.locals.lookup (ofString "nwd") = some (.val (.word w_nwd)) ∧
    s.locals.lookup (ofString "i") = some (.val (.word w_i)) ∧
    s.globals.lookup (ofString "wd_rlp_slices") = some (.val (.word w_wds)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    0 ≤ w_i.toInt ∧
    (0 < w_i.toNat → 44 * (w_i.toNat - 1) < heapEnd)

/-- State inside the loop body right after `e := encode_withdrawal_rlp(wd_i)`. -/
def PH_LOOP_E : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_si w_pl w_wr w_nwd w_wds w_i e0 e1 : BitVec 64, ∃ S Nd : List Nat,
    let alloc_sz := (w_nwd * 16#64 + 16#64).toNat
    InputAtWith s S Nd w_si.toNat ∧
    AllBlocksGood s S Nd [(w_wr.toNat, 32), (w_wds.toNat, alloc_sz)] ∧
    IvlsDisj (inputCells s w_si.toNat) [(w_wr.toNat, 32), (w_wds.toNat, alloc_sz)] ∧
    Disj (w_wr.toNat, 32) (w_wds.toNat, alloc_sz) ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "wr") = some (.val (.word w_wr)) ∧
    s.locals.lookup (ofString "nwd") = some (.val (.word w_nwd)) ∧
    s.locals.lookup (ofString "i") = some (.val (.word w_i)) ∧
    s.locals.lookup (ofString "e") = some (.rStruct [.val (.word e0), .val (.word e1)]) ∧
    s.globals.lookup (ofString "wd_rlp_slices") = some (.val (.word w_wds)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    0 ≤ w_i.toInt ∧
    w_i.toInt < w_nwd.toInt ∧
    44 * w_i.toNat < heapEnd

/-! ## Step lemmas -/

theorem ph_alloc_generic {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (varName : String) (sz : Nat) (hsz8 : sz % 8 = 0) (hsz_lt : sz < 2 ^ 64)
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc"))
    (hExtr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s →
      ∃ w_si : BitVec 64, ∃ S Nd : List Nat, ∃ bs : List Ivl,
        InputAtWith s S Nd w_si.toNat ∧
        AllBlocksGood s S Nd bs ∧
        IvlsDisj (inputCells s w_si.toNat) bs ∧
        (∀ (post : PanSemStateFiniteExact 64 F) (w_new : BitVec 64) (S' Nd' : List Nat),
          let resumed := setVarHOLFinite (ofString varName) (.val (.word w_new))
            { post with locals := s.locals }
          InputAtWith resumed S' Nd' w_si.toNat →
          AllBlocksGood resumed S' Nd' (bs ++ [(w_new.toNat, sz)]) →
          IvlsDisj (inputCells resumed w_si.toNat) (bs ++ [(w_new.toNat, sz)]) →
          (∀ b ∈ bs, Disj b (w_new.toNat, sz)) →
          (∀ b ∈ bs, IvlUnhit s resumed b) →
          (∀ c ∈ inputCells s w_si.toNat, IvlUnhit s resumed c) →
          Q resumed)) :
    DecCallResumeOn P Q (ofString varName) (ofString "alloc") [.const (BitVec.ofNat 64 sz)] := by
  intro F state values body callee ret value post hcode hP hargs hl hrun
  obtain ⟨w_si, S, Nd, bs, hIA, hBs, hd_ic, hBuild⟩ := hExtr state hP
  have hAs := hIA.1
  have hW_state : WorldOK state := ⟨hAs, S, (worldTyped_iff_with state S).2 ⟨Nd, hIA.2.1⟩⟩
  have hpc := callee_param_one_exp state (ofString "alloc") (ofString "n") .one _ _
    (by rw [hcode]; exact R13PayloadStateInit.lookup_alloc_fn) (.const (BitVec.ofNat 64 sz))
    (.val (.word (BitVec.ofNat 64 sz))) values body callee ret rfl hargs hl
  have hn_loc : locN (callEntryStateHOLFinite state callee) "n" = sz := by
    simp only [locN, callEntryStateHOLFinite, hpc.2, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hsz_lt
  have hround : (sz + 7) / 8 * 8 = sz := by omega
  have hstep := FunSpec.at_lookup wal state hcode values body callee ret hl
    (localsFree_worldOK state callee (state.clock - 1) hW_state) (by rw [hrun]; simp)
  rw [hrun] at hstep; dsimp only at hstep
  have hws := hstep (Or.inl ⟨value, rfl⟩)
  have hrt := FunSpec.at_lookup rtal state hcode values body callee ret hl
    (localsFree_arenaReady state callee (state.clock - 1) hAs) (by rw [hrun]; simp)
  rw [hrun] at hrt; dsimp only at hrt
  obtain ⟨w_new, rfl, _, _, hfb⟩ := hrt value rfl
  rw [hn_loc] at hfb
  have hfb_in : Inside (w_new.toNat, sz) (globN state "heap_ptr") (globN post "heap_ptr") := by
    have := hfb.2.1; rwa [hround] at this
  have hfb_w : WordsOK post (w_new.toNat, sz) := by
    have := hfb.2.2; rwa [hround] at this
  have hIA_entry : InputAtWith (callEntryStateHOLFinite state callee) S Nd w_si.toNat :=
    (inputAtWith_with_locals state callee (state.clock - 1) S Nd w_si.toNat).2 hIA
  have hBs_entry : AllBlocksGood (callEntryStateHOLFinite state callee) S Nd bs :=
    (allBlocksGood_with_locals state callee (state.clock - 1) S Nd bs).2 hBs
  obtain ⟨S', Nd', hIA_post, hBs_post, hu_bs, hu_ic, hQ⟩ :=
    WorldStep_preserves_inputAndBlocks hIA_entry hBs_entry hws
      (fun _ hj => by simp at hj) (fun _ hj => by simp at hj)
      (fun _ _ _ hj => by simp at hj) (fun _ _ _ hj => by simp at hj)
  obtain ⟨w_new', hw_eq, hav⟩ := hQ (.val (.word w_new)) rfl
  injection hw_eq with hw_eq'; injection hw_eq' with hw_eq''; subst hw_eq''
  dsimp only at hav; rw [hn_loc, hround] at hav
  set resumed := setVarHOLFinite (ofString varName) (.val (.word w_new)) { post with locals := state.locals }
  have hIA_res : InputAtWith resumed S' Nd' w_si.toNat :=
    (inputAtWith_with_locals post _ post.clock S' Nd' w_si.toNat).2 hIA_post
  have hBs_ext : AllBlocksGood post S' Nd' (bs ++ [(w_new.toNat, sz)]) := by
    intro b hb
    rcases List.mem_append.1 hb with hb_old | hb_new
    · exact hBs_post b hb_old
    · simp only [List.mem_singleton] at hb_new; subst hb_new
      exact ⟨hfb.1, hsz8, ⟨Nat.le_trans hAs.2.1 hfb_in.1, hfb_in.2⟩, hfb_w,
        fun o ho => hav (w_new.toNat, sz) (by simp) o ho⟩
  have hBs_res : AllBlocksGood resumed S' Nd' (bs ++ [(w_new.toNat, sz)]) :=
    (allBlocksGood_with_locals post _ post.clock S' Nd' _).2 hBs_ext
  have hic_eq : inputCells post w_si.toNat = inputCells state w_si.toNat := by
    have hsi_mem : (w_si.toNat, 40) ∈ inputCells state w_si.toNat := by simp [inputCells]
    have hpl_mem : (memW state w_si.toNat, 136) ∈ inputCells state w_si.toNat := by simp [inputCells]
    have h264 : heapLimit ≤ 2 ^ 64 := by decide
    have hhp_lim : globN state "heap_ptr" ≤ heapLimit := hAs.2.2.1
    have hsi_u := hu_ic _ hsi_mem
    have hpl_u := hu_ic _ hpl_mem
    have hsi0_eq : memW post w_si.toNat = memW state w_si.toNat :=
      memW_eq_of_ivlUnhit hsi_u (hIA.2.2.1 _ hsi_mem).2.1
        (by have := (hIA.2.2.1 _ hsi_mem).1.2; omega) ⟨le_rfl, by omega⟩
    have hsi32_eq : memW post (w_si.toNat + 32) = memW state (w_si.toNat + 32) :=
      memW_eq_of_ivlUnhit hsi_u (by have := (hIA.2.2.1 _ hsi_mem).2.1; omega)
        (by have := (hIA.2.2.1 _ hsi_mem).1.2; omega) ⟨by omega, by omega⟩
    have hpl32_eq : memW post (memW state w_si.toNat + 32) = memW state (memW state w_si.toNat + 32) :=
      memW_eq_of_ivlUnhit hpl_u (by have := (hIA.2.2.1 _ hpl_mem).2.1; omega)
        (by have := (hIA.2.2.1 _ hpl_mem).1.2; omega) ⟨by omega, by omega⟩
    have hpl40_eq : memW post (memW state w_si.toNat + 40) = memW state (memW state w_si.toNat + 40) :=
      memW_eq_of_ivlUnhit hpl_u (by have := (hIA.2.2.1 _ hpl_mem).2.1; omega)
        (by have := (hIA.2.2.1 _ hpl_mem).1.2; omega) ⟨by omega, by omega⟩
    simp only [inputCells, hsi0_eq, hsi32_eq, hpl32_eq, hpl40_eq]
  have hd_ic_res : IvlsDisj (inputCells resumed w_si.toNat) (bs ++ [(w_new.toNat, sz)]) := by
    change IvlsDisj (inputCells post w_si.toNat) (bs ++ [(w_new.toNat, sz)])
    rw [hic_eq]
    intro c hc b hb
    rcases List.mem_append.1 hb with hb_old | hb_new
    · exact hd_ic c hc b hb_old
    · simp only [List.mem_singleton] at hb_new; subst hb_new
      exact Or.inr (Or.inr (Or.inl (Nat.le_trans (hIA.2.2.1 c hc).1.2 hfb_in.1)))
  have hd_bs_new : ∀ b ∈ bs, Disj b (w_new.toNat, sz) :=
    fun b hb => Or.inr (Or.inr (Or.inl (Nat.le_trans (hBs b hb).2.2.1.2 hfb_in.1)))
  exact hBuild post w_new S' Nd' hIA_res hBs_res hd_ic_res hd_bs_new hu_bs hu_ic

theorem ph_memzero_generic {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (varName : String) (sz : Nat) (hsz_lt : sz < 2 ^ 64)
    (wmz : WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")]) []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "memzero"))
    (hExtr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s →
      ∃ w_si w_dst : BitVec 64, ∃ S Nd : List Nat, ∃ bs_keep : List Ivl,
        s.locals.lookup (ofString varName) = some (.val (.word w_dst)) ∧
        InputAtWith s S Nd w_si.toNat ∧
        AllBlocksGood s S Nd ((w_dst.toNat, sz) :: bs_keep) ∧
        IvlsDisj (inputCells s w_si.toNat) ((w_dst.toNat, sz) :: bs_keep) ∧
        (∀ b ∈ bs_keep, Disj b (w_dst.toNat, sz)) ∧
        (∀ (post : PanSemStateFiniteExact 64 F) (S' Nd' : List Nat),
          let resumed := { post with locals := s.locals }
          InputAtWith resumed S' Nd' w_si.toNat →
          AllBlocksGood resumed S' Nd' ((w_dst.toNat, sz) :: bs_keep) →
          (∀ b ∈ bs_keep, IvlUnhit s resumed b) →
          (∀ c ∈ inputCells s w_si.toNat, IvlUnhit s resumed c) →
          Q resumed)) :
    Hoare P
      (.call (some (none, none)) (ofString "memzero")
        [.var .local (ofString varName), .const (BitVec.ofNat 64 sz)])
      (fun r t => r = none → Q t) := by
  refine ⟨fun {F} state hcode hP _ hr => ?_⟩
  rcases hcall : evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "memzero")
        [.var .local (ofString varName), .const (BitVec.ofNat 64 sz)]) with ⟨cres, cpost⟩
  have hr' : cres = none := by rw [hcall] at hr; exact hr
  subst hr'
  obtain ⟨w_si, w_dst, S, Nd, bs_keep, hlu_dst, hIA, hBs, hd_ic, hd_keep, hBuild⟩ := hExtr state hP
  rw [evaluateHOLFiniteState_call] at hcall
  have hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString varName), .const (BitVec.ofNat 64 sz)] =
      some [.val (.word w_dst), .val (.word (BitVec.ofNat 64 sz))] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, evalHOLExact, hlu_dst]
  rw [hargs] at hcall; dsimp only at hcall
  rcases hl : lookupCodeHOLFinite state.code.lookup (ofString "memzero")
      [.val (.word w_dst), .val (.word (BitVec.ofNat 64 sz))] with _ | ⟨body, callee, ret⟩
  · rw [hl] at hcall; simp at hcall
  · rw [hl] at hcall; dsimp only at hcall
    split_ifs at hcall with hz
    · simp at hcall
    · rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with ⟨bres, post⟩
      rw [hb] at hcall
      cases bres with
      | none => simp at hcall
      | some br =>
        cases br with
        | returned v =>
          dsimp only at hcall
          split_ifs at hcall with hsh
          · obtain ⟨_, hpost_eq⟩ := Prod.mk.inj hcall
            have hpc := callee_param_two state (ofString "memzero") (ofString "dst") (ofString "n")
              .one .one _ _ (by rw [hcode]; exact R13PayloadStateInit.lookup_memzero_fn)
              (.var .local (ofString varName)) (.const (BitVec.ofNat 64 sz))
              (.val (.word w_dst)) (.val (.word (BitVec.ofNat 64 sz)))
              [.val (.word w_dst), .val (.word (BitVec.ofNat 64 sz))] body callee ret
              (by simpa [evalAt, evalHOLExact] using hlu_dst) rfl hargs hl
            have hdst : locN (callEntryStateHOLFinite state callee) "dst" = w_dst.toNat := by
              simp [locN, callEntryStateHOLFinite, hpc.2.1]
            have hn : locN (callEntryStateHOLFinite state callee) "n" = sz := by
              simp only [locN, callEntryStateHOLFinite, hpc.2.2, BitVec.toNat_ofNat]
              exact Nat.mod_eq_of_lt hsz_lt
            have hW_state : WorldOK state := ⟨hIA.1, S, (worldTyped_iff_with state S).2 ⟨Nd, hIA.2.1⟩⟩
            have hstep := FunSpec.at_lookup wmz state hcode _ body callee ret hl
              (localsFree_worldOK state callee (state.clock - 1) hW_state) (by rw [hb]; simp)
            rw [hb] at hstep; dsimp only at hstep
            have hws := hstep (Or.inl ⟨v, rfl⟩)
            have hIA_entry : InputAtWith (callEntryStateHOLFinite state callee) S Nd w_si.toNat :=
              (inputAtWith_with_locals state callee (state.clock - 1) S Nd w_si.toNat).2 hIA
            have hBs_keep : AllBlocksGood (callEntryStateHOLFinite state callee) S Nd bs_keep :=
              (allBlocksGood_with_locals state callee (state.clock - 1) S Nd bs_keep).2
                (fun b hb => hBs b (List.mem_cons_of_mem _ hb))
            have hdst_good := hBs (w_dst.toNat, sz) (by simp)
            have hhp_same : globN post "heap_ptr" = globN state "heap_ptr" := by
              have hlk := hws.2.2.1 (ofString "heap_ptr") (by simp)
              unfold globN; rw [← hlk]; rfl
            have hRz : ∀ j ∈ [(locN (callEntryStateHOLFinite state callee) "dst",
                locN (callEntryStateHOLFinite state callee) "n")], j.2 = 0 → j.1 % 8 = 0 := by
              intro j hj _; simp only [hdst, hn, List.mem_singleton] at hj; subst hj; exact hdst_good.1
            obtain ⟨S2, Nd2, _, hIA_post2, hog2, hfr2, _⟩ :=
              WorldStep.preserves_inputAtWith hIA_entry hws hRz
                (fun j hj k hk => by
                  simp only [hdst, hn, List.mem_singleton] at hj; subst hj
                  exact hdst_good.2.2.2.2 k (worldTypedIvls_sub_worldOwned _ _ _ k hk))
                (fun i hi j hj => by
                  simp only [hdst, hn, List.mem_singleton] at hj; subst hj
                  exact hd_ic i hi (w_dst.toNat, sz) (by simp))
            have hold_z := worldOwned_zero_aligned hIA_entry.2.1
            have hBs_keep2 : AllBlocksGood post S2 Nd2 bs_keep := by
              intro b hb
              obtain ⟨b1, b2, bin, bw, bow⟩ := hBs_keep b hb
              have hsurv := heap_ivl_survives_step hIA.1.2 hws.2.1 hog2 hfr2 hold_z hRz
                b1 b2 bin bow
                (fun j hj => by
                  simp only [hdst, hn, List.mem_singleton] at hj; subst hj
                  exact hd_keep b hb)
              exact ⟨b1, b2, hsurv.1, wordsOK_transfer hIA.1.1 hws.1.1 bw, hsurv.2.1⟩
            have hu_keep2 : ∀ b ∈ bs_keep, IvlUnhit state { post with locals := state.locals } b := by
              intro b hb
              obtain ⟨b1, b2, bin, _, bow⟩ := hBs_keep b hb
              exact (heap_ivl_survives_step hIA.1.2 hws.2.1 hog2 hfr2 hold_z hRz
                b1 b2 bin bow
                (fun j hj => by
                  simp only [hdst, hn, List.mem_singleton] at hj; subst hj
                  exact hd_keep b hb)).2.2
            have hu_ic2 : ∀ c ∈ inputCells state w_si.toNat, IvlUnhit state { post with locals := state.locals } c := by
              intro c hc
              obtain ⟨cin, cw⟩ := hIA.2.2.1 c hc
              exact (heap_ivl_survives_step hIA.1.2 hws.2.1 hog2 hfr2 hold_z hRz
                cw.1 cw.2.1 cin (fun j hj => hIA.2.2.2.1 c hc j hj)
                (fun j hj => by
                  simp only [hdst, hn, List.mem_singleton] at hj; subst hj
                  exact hd_ic c hc (w_dst.toNat, sz) (by simp))).2.2
            have hdst_post : AllBlocksGood post S2 Nd2 [(w_dst.toNat, sz)] := by
              intro b hb; simp only [List.mem_singleton] at hb; subst hb
              refine ⟨hdst_good.1, hdst_good.2.1,
                ⟨hdst_good.2.2.1.1, Nat.le_trans hdst_good.2.2.1.2 hws.2.1⟩,
                wordsOK_transfer hIA.1.1 hws.1.1 hdst_good.2.2.2.1, ?_⟩
              intro o ho
              rcases hog2 o ho with rfl | ⟨j, hj, hin⟩ | hfresh
              · exact disj_zero_right _
              · exact disj_of_inside_right hin (hdst_good.2.2.2.2 j hj)
              · change Inside o (globN state "heap_ptr") (globN post "heap_ptr") at hfresh
                rw [hhp_same] at hfresh
                exact Or.inr (Or.inl (by unfold Inside at hfresh; omega))
            have hBs_all : AllBlocksGood { post with locals := state.locals } S2 Nd2
                ((w_dst.toNat, sz) :: bs_keep) := by
              apply (allBlocksGood_with_locals post state.locals post.clock S2 Nd2 _).2
              intro b hb
              rcases List.mem_cons.1 hb with rfl | hbk
              · exact hdst_post _ (by simp)
              · exact hBs_keep2 b hbk
            have hQ_res := hBuild post S2 Nd2
              ((inputAtWith_with_locals post state.locals post.clock S2 Nd2 w_si.toNat).2 hIA_post2)
              hBs_all hu_keep2 hu_ic2
            rwa [hpost_eq] at hQ_res
          · simp at hcall
        | _ => simp [emptyLocalsHOLFinite] at hcall

theorem ph_h_store_simple (b : Bool) (off : Nat) (src : ExpHOL 64)
    (hoff8 : off % 8 = 0) (hoff_fit : off + 8 ≤ 248) (hne136 : b = true → off ≠ 136)
    (hsrc_kind : src = .const 1#64 ∨ (∃ x y, src = .op .add [x, y]) ∨ (∃ addr, src = .load .one addr)) :
    Hoare (PH_H b) (.store (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 off)]) src)
      (fun r t => r = none → PH_H b t) := by
  refine Hoare_store_fall (fun s x v mem' hP hx hv hst => ?_)
  obtain ⟨w_si, w_pl, w_raw, w_h, S, Nd, hIA, hBs, hd_ic, hlsi, hlpl, hlraw, hlh, hpl_eq, h136⟩ := hP
  have hx_eq := evalAt_add_local_const hlh hx
  have hlen : (flattenHOL v).length ≤ 1 := evalAt_simple_word_len hsrc_kind hv
  have htr := store_in_tracked_block hIA hBs (by simp) hd_ic rfl hoff8 hx_eq (by omega) hst
  set post := { s with memory := mem' }
  have hsi_mem : (w_si.toNat, 40) ∈ inputCells s w_si.toNat := by simp [inputCells]
  have hsi_u := htr.2.2 _ (fun _ => (hIA.2.2.1 _ hsi_mem).2.1) (hd_ic _ hsi_mem _ (by simp))
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hIA.1.2.2.1
  have hsi0_eq : memW post w_si.toNat = memW s w_si.toNat :=
    memW_eq_of_ivlUnhit hsi_u (hIA.2.2.1 _ hsi_mem).2.1
      (by have := (hIA.2.2.1 _ hsi_mem).1.2; omega) ⟨le_rfl, by omega⟩
  have hpl_mem : (memW s w_si.toNat, 136) ∈ inputCells s w_si.toNat := by simp [inputCells]
  have hpl_u := htr.2.2 _ (fun _ => (hIA.2.2.1 _ hpl_mem).2.1) (hd_ic _ hpl_mem _ (by simp))
  have hsi32_eq : memW post (w_si.toNat + 32) = memW s (w_si.toNat + 32) :=
    memW_eq_of_ivlUnhit hsi_u (by have := (hIA.2.2.1 _ hsi_mem).2.1; omega)
      (by have := (hIA.2.2.1 _ hsi_mem).1.2; omega) ⟨by omega, by omega⟩
  have hpl32_eq : memW post (memW s w_si.toNat + 32) = memW s (memW s w_si.toNat + 32) :=
    memW_eq_of_ivlUnhit hpl_u (by have := (hIA.2.2.1 _ hpl_mem).2.1; omega)
      (by have := (hIA.2.2.1 _ hpl_mem).1.2; omega) ⟨by omega, by omega⟩
  have hpl40_eq : memW post (memW s w_si.toNat + 40) = memW s (memW s w_si.toNat + 40) :=
    memW_eq_of_ivlUnhit hpl_u (by have := (hIA.2.2.1 _ hpl_mem).2.1; omega)
      (by have := (hIA.2.2.1 _ hpl_mem).1.2; omega) ⟨by omega, by omega⟩
  have hic_eq : inputCells post w_si.toNat = inputCells s w_si.toNat := by
    simp only [inputCells, hsi0_eq, hsi32_eq, hpl32_eq, hpl40_eq]
  refine ⟨w_si, w_pl, w_raw, w_h, S, Nd, htr.1, htr.2.1, ?_, hlsi, hlpl, hlraw, hlh, ?_, ?_⟩
  · rw [hic_eq]; exact hd_ic
  · rw [hsi0_eq]; exact hpl_eq
  · intro hb
    have hne := hne136 hb
    have hh_good := hBs (w_h.toNat, 248) (by simp)
    have hh_hi : w_h.toNat + 248 ≤ heapLimit := Nat.le_trans hh_good.2.2.1.2 hhp_lim
    have h264' : heapLimit < 2 ^ 64 := by decide
    have hx_nat : x.toNat = w_h.toNat + off := by
      rw [hx_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
      have hoff_lt : off < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt hoff_lt]
      have hwh_lt : w_h.toNat + off < 2 ^ 64 := by omega
      exact Nat.mod_eq_of_lt hwh_lt
    have hmem_eq : post.memory (BitVec.ofNat 64 (w_h.toNat + 136)) =
        s.memory (BitVec.ofNat 64 (w_h.toNat + 136)) := by
      apply panMemStoresHOL_frame (flattenHOL v) x s.memory mem' hst
      intro k hk h_eq
      have hlhs : (BitVec.ofNat 64 (w_h.toNat + 136)).toNat = w_h.toNat + 136 := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      have hrhs : (x + BitVec.ofNat 64 (8 * k)).toNat = w_h.toNat + off + 8 * k := by
        rw [BitVec.toNat_add, hx_nat, BitVec.toNat_ofNat]
        have hk8_lt : 8 * k < 2 ^ 64 := by omega
        rw [Nat.mod_eq_of_lt hk8_lt]
        have hsum_lt : w_h.toNat + off + 8 * k < 2 ^ 64 := by omega
        simpa [Nat.add_assoc] using Nat.mod_eq_of_lt hsum_lt
      rw [h_eq] at hlhs; omega
    have hw_eq : memW post (w_h.toNat + 136) = memW s (w_h.toNat + 136) := by
      unfold memW; rw [hmem_eq]
    rw [hw_eq]; exact h136 hb

private theorem evalAt_panOp_mul_const {F : Type} {s : PanSemStateFiniteExact 64 F}
    {a : ExpHOL 64} {c : Nat} {v : ValueHOL 64}
    (hev : evalAt s (.panop .mul [a, .const (BitVec.ofNat 64 c)]) = some v) :
    ∃ wa : BitVec 64, evalAt s a = some (.val (.word wa)) ∧
      v = .val (.word (wa * BitVec.ofNat 64 c)) := by
  simp only [evalAt, evalHOLExact, evalListHOLExact] at hev
  rcases ha : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) a with _ | va
  · rw [ha] at hev; simp at hev
  · rw [ha] at hev; dsimp only at hev
    cases va with
    | val wl =>
      cases wl with
      | word wa =>
        simp only [List.all_cons, List.all_nil, Bool.and_true, List.map_cons, List.map_nil,
          valueIsWord, valueWord, panOpHOL, ↓reduceIte, Option.map_some, Option.some.injEq] at hev
        exact ⟨wa, ha, hev.symm⟩
    | rStruct _ => simp [valueIsWord] at hev
    | nStruct _ _ => simp [valueIsWord] at hev

private theorem evalAt_add2_words {F : Type} {s : PanSemStateFiniteExact 64 F}
    {e1 e2 : ExpHOL 64} {x : BitVec 64}
    (hev : evalAt s (.op .add [e1, e2]) = some (.val (.word x))) :
    ∃ w1 w2 : BitVec 64, evalAt s e1 = some (.val (.word w1)) ∧
      evalAt s e2 = some (.val (.word w2)) ∧ x = w1 + w2 := by
  simp only [evalAt, evalHOLExact, evalListHOLExact] at hev
  rcases h1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | v1
  · rw [h1] at hev; simp at hev
  · rw [h1] at hev
    rcases h2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 with _ | v2
    · rw [h2] at hev; simp at hev
    · rw [h2] at hev; dsimp only at hev
      rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> try simp [valueIsWord] at hev
      rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;> try simp [valueIsWord] at hev
      simp only [valueIsWord, Bool.and_self, ↓reduceIte, List.map, valueWord, wordOpHOL, wordOp,
        List.foldr, add_zero, Option.map, Option.some.injEq, ValueHOL.val.injEq,
        HolWordLab.word.injEq] at hev
      exact ⟨w1, w2, h1, h2, hev.symm⟩

private theorem evalAt_add3_words {F : Type} {s : PanSemStateFiniteExact 64 F}
    {e1 e2 e3 : ExpHOL 64} {x : BitVec 64}
    (hev : evalAt s (.op .add [e1, e2, e3]) = some (.val (.word x))) :
    ∃ w1 w2 w3 : BitVec 64, evalAt s e1 = some (.val (.word w1)) ∧
      evalAt s e2 = some (.val (.word w2)) ∧
      evalAt s e3 = some (.val (.word w3)) ∧ x = w1 + (w2 + w3) := by
  simp only [evalAt, evalHOLExact, evalListHOLExact] at hev
  rcases h1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | v1
  · rw [h1] at hev; simp at hev
  · rw [h1] at hev
    rcases h2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 with _ | v2
    · rw [h2] at hev; simp at hev
    · rw [h2] at hev
      rcases h3 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e3 with _ | v3
      · rw [h3] at hev; simp at hev
      · rw [h3] at hev; dsimp only at hev
        rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> try simp [valueIsWord] at hev
        rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;> try simp [valueIsWord] at hev
        rcases v3 with ⟨⟨w3⟩⟩ | _ | _ <;> try simp [valueIsWord] at hev
        simp only [valueIsWord, Bool.and_self, ↓reduceIte, List.map, valueWord, wordOpHOL, wordOp,
          List.foldr, add_zero, Option.map, Option.some.injEq, ValueHOL.val.injEq,
          HolWordLab.word.injEq] at hev
        exact ⟨w1, w2, w3, h1, h2, h3, hev.symm⟩

theorem ph_entry_dec_pl_raw {K : Nat}
    (hbody : TerminatingProgBoundedOn PH_S0
      (match sourceFnBody Guest.Software.guestFn_payload_header with
       | .dec _ _ _ (.dec _ _ _ b) => b
       | p => p) K) :
    TerminatingProgBoundedOn InputReady
      (sourceFnBody Guest.Software.guestFn_payload_header) K := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_payload_header,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil] at hbody ⊢
  set PH_PL : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
    fun s => ∃ w_si w_pl : BitVec 64, ∃ S Nd : List Nat,
      InputAtWith s S Nd w_si.toNat ∧
      s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
      s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
      w_pl.toNat = memW s w_si.toNat
  refine dec_eval_on (P := InputReady) (Q := PH_PL) (ofString "pl") .one
    (.load .one (.op .add [.var .local (ofString "si"), .const 0#64])) ?_
    (dec_eval_on (P := PH_PL) (Q := PH_S0) (ofString "raw") .one
      (.load .one (.op .add [.var .local (ofString "pl"), .const 0#64])) ?_ hbody)
  · intro F s v hIR hev
    obtain ⟨S, Nd, hIA⟩ := (inputAt_iff_with s (locN s "si")).1 hIR
    obtain ⟨a, w_pl, ha, rfl, hpl_mem, _⟩ := evalAt_load_one_word hIA.1.1 hev
    obtain ⟨w_si, w0, hsi_ev, hw0_ev, ha_eq⟩ := evalAt_add2_words ha
    have hlsi : s.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
      simpa [evalAt, evalHOLExact] using hsi_ev
    have hw0 : w0 = 0#64 := by
      simp only [evalAt, evalHOLExact, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hw0_ev
      exact hw0_ev.symm
    subst hw0
    have ha_si : a = w_si := by rw [ha_eq, BitVec.add_zero]
    have hloc_si : locN s "si" = a.toNat := by
      rw [ha_si]; simp [locN, hlsi]
    rw [hloc_si] at hIA
    set s1 := setVarHOLFinite (ofString "pl") (.val (.word w_pl)) s
    exact ⟨a, w_pl, S, Nd,
      (inputAtWith_with_locals s _ s.clock S Nd a.toNat).2 hIA,
      by rw [ha_si]; simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
           show ofString "pl" ≠ ofString "si" by decide, hlsi],
      by simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
      hpl_mem⟩
  · intro F s1 v ⟨w_si, w_pl, S, Nd, hIA, hlsi, hlpl, hpl_eq⟩ hev
    obtain ⟨_, w_raw, _, rfl, _⟩ := evalAt_load_one_word hIA.1.1 hev
    set s2 := setVarHOLFinite (ofString "raw") (.val (.word w_raw)) s1
    exact ⟨w_si, w_pl, w_raw, S, Nd,
      (inputAtWith_with_locals s1 _ s1.clock S Nd w_si.toNat).2 hIA,
      by simp [s2, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
           show ofString "raw" ≠ ofString "si" by decide, hlsi],
      by simp [s2, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
           show ofString "raw" ≠ ofString "pl" by decide, hlpl],
      by simp [s2, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
      hpl_eq⟩

private theorem dec_shape_eval_on
    {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (name : MlS) (sh : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64} {K : Nat}
    (hstep : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      P s → evalAt s init = some v →
      shapeEqHOL sh (shapeOfHOLExact v) = true →
      Q (setVarHOLFinite name v s))
    (hbody : TerminatingProgBoundedOn Q body K) :
    TerminatingProgBoundedOn P (.dec name sh init body) K := by
  intro F state hcode hP
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  revert hnt
  rcases he : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) init with _ | val
  · intro _; exact ⟨Nat.le_add_right state.clock K, Nat.le_refl _⟩
  · dsimp only
    split_ifs with hsh <;> intro hnt
    · have hb := hbody (setVarHOLFinite name val state) hcode (hstep state val hP he hsh)
        (by simpa [setVarHOLFinite] using hnt)
      simpa [setVarHOLFinite] using hb
    · exact ⟨Nat.le_add_right state.clock K, Nat.le_refl _⟩

private theorem ph_s0_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F} (h : PH_S0 s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1

private theorem ph_h_guestInv {b : Bool} {F : Type} {s : PanSemStateFiniteExact 64 F} (h : PH_H b s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1

private theorem ph_oh_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F} (h : PH_OH s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1

private theorem ph_tmp_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F} (h : PH_TMP s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1

private theorem ph_txr_guestInv {b : Bool} {F : Type} {s : PanSemStateFiniteExact 64 F} (h : PH_TXR b s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1

private theorem ph_z8_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F} (h : PH_Z8 s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1

private theorem ph_bf_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F} (h : PH_BF s) : GuestInv s :=
  ph_txr_guestInv h.1

private theorem ph_wr_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F} (h : PH_WR s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1

private theorem ph_rh_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F} (h : PH_RH s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1

private theorem ph_bh_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F} (h : PH_BH s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1

private theorem ph_nwd_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F} (h : PH_NWD s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1

private theorem ph_wds0_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F} (h : PH_WDS0 s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1

private theorem ph_loop_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F} (h : PH_LOOP s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1

private theorem ph_loop_e_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F} (h : PH_LOOP_E s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1

private theorem inputCells_eq_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si : Nat}
    (hIA : InputAtWith s S Nd si)
    (hu : ∀ c ∈ inputCells s si, IvlUnhit s post c) :
    memW post si = memW s si ∧
    memW post (si + 32) = memW s (si + 32) ∧
    inputCells post si = inputCells s si := by
  have hsi_mem : (si, 40) ∈ inputCells s si := by simp [inputCells]
  have hpl_mem : (memW s si, 136) ∈ inputCells s si := by simp [inputCells]
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hIA.1.2.2.1
  have hsi_u := hu _ hsi_mem
  have hpl_u := hu _ hpl_mem
  have hsi0 : memW post si = memW s si :=
    memW_eq_of_ivlUnhit hsi_u (hIA.2.2.1 _ hsi_mem).2.1
      (by have := (hIA.2.2.1 _ hsi_mem).1.2; omega) ⟨le_rfl, by omega⟩
  have hsi32 : memW post (si + 32) = memW s (si + 32) :=
    memW_eq_of_ivlUnhit hsi_u (by have := (hIA.2.2.1 _ hsi_mem).2.1; omega)
      (by have := (hIA.2.2.1 _ hsi_mem).1.2; omega) ⟨by omega, by omega⟩
  have hpl32 : memW post (memW s si + 32) = memW s (memW s si + 32) :=
    memW_eq_of_ivlUnhit hpl_u (by have := (hIA.2.2.1 _ hpl_mem).2.1; omega)
      (by have := (hIA.2.2.1 _ hpl_mem).1.2; omega) ⟨by omega, by omega⟩
  have hpl40 : memW post (memW s si + 40) = memW s (memW s si + 40) :=
    memW_eq_of_ivlUnhit hpl_u (by have := (hIA.2.2.1 _ hpl_mem).2.1; omega)
      (by have := (hIA.2.2.1 _ hpl_mem).1.2; omega) ⟨by omega, by omega⟩
  exact ⟨hsi0, hsi32, by simp only [inputCells, hsi0, hsi32, hpl32, hpl40]⟩

theorem ph_alloc_h
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc")) :
    DecCallResumeOn PH_S0 (PH_H false) (ofString "h") (ofString "alloc") [.const 248#64] := by
  refine ph_alloc_generic "h" 248 (by omega) (by decide) wal rtal ?_
  intro F s ⟨w_si, w_pl, w_raw, S, Nd, hIA, hlsi, hlpl, hlraw, hpl_eq⟩
  refine ⟨w_si, S, Nd, [], hIA, allBlocksGood_nil s S Nd, (fun _ _ _ hb => by simp at hb), ?_⟩
  intro post w_h S' Nd'
  dsimp only
  intro hIA_res hBs_res hd_ic_res _ _ hu_ic
  have hic := inputCells_eq_of_unhit hIA hu_ic
  exact ⟨w_si, w_pl, w_raw, w_h, S', Nd', hIA_res, hBs_res, hd_ic_res,
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "h" ≠ ofString "si" by decide, hlsi],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "h" ≠ ofString "pl" by decide, hlpl],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "h" ≠ ofString "raw" by decide, hlraw],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
    by rw [hic.1]; exact hpl_eq,
    fun h => by cases h⟩

theorem ph_memzero_h
    (wmz : WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")]) []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "memzero")) :
    Hoare (PH_H false)
      (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "h"), .const 248#64])
      (fun r t => r = none → PH_H false t) := by
  refine ph_memzero_generic "h" 248 (by decide) wmz ?_
  intro F s ⟨w_si, w_pl, w_raw, w_h, S, Nd, hIA, hBs, hd_ic, hlsi, hlpl, hlraw, hlh, hpl_eq, _⟩
  refine ⟨w_si, w_h, S, Nd, [], hlh, hIA, hBs, hd_ic, (fun _ hb => by simp at hb), ?_⟩
  intro post S' Nd'
  dsimp only
  intro hIA_res hBs_res _ hu_ic
  have hic := inputCells_eq_of_unhit hIA hu_ic
  refine ⟨w_si, w_pl, w_raw, w_h, S', Nd', hIA_res, hBs_res, ?_, hlsi, hlpl, hlraw, hlh, ?_, fun h => by cases h⟩
  · rw [hic.2.2]; exact hd_ic
  · rw [hic.1]; exact hpl_eq

theorem ph_alloc_oh
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc")) :
    DecCallResumeOn (PH_H false) PH_OH (ofString "oh") (ofString "alloc") [.const 32#64] := by
  refine ph_alloc_generic "oh" 32 (by omega) (by decide) wal rtal ?_
  intro F s ⟨w_si, w_pl, w_raw, w_h, S, Nd, hIA, hBs, hd_ic, hlsi, hlpl, hlraw, hlh, hpl_eq, _⟩
  refine ⟨w_si, S, Nd, [(w_h.toNat, 248)], hIA, hBs, hd_ic, ?_⟩
  intro post w_oh S' Nd'
  dsimp only
  intro hIA_res hBs_res hd_ic_res hd_bs _ hu_ic
  have hic := inputCells_eq_of_unhit hIA hu_ic
  exact ⟨w_si, w_pl, w_raw, w_h, w_oh, S', Nd', hIA_res, hBs_res, hd_ic_res,
    hd_bs _ (by simp),
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "oh" ≠ ofString "si" by decide, hlsi],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "oh" ≠ ofString "pl" by decide, hlpl],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "oh" ≠ ofString "raw" by decide, hlraw],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "oh" ≠ ofString "h" by decide, hlh],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
    by rw [hic.1]; exact hpl_eq⟩

theorem ph_alloc_tmp
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc")) :
    DecCallResumeOn PH_OH PH_TMP (ofString "tmp") (ofString "alloc") [.const 8#64] := by
  refine ph_alloc_generic "tmp" 8 (by omega) (by decide) wal rtal ?_
  intro F s ⟨w_si, w_pl, w_raw, w_h, w_oh, S, Nd, hIA, hBs, hd_ic, hd_ho, hlsi, hlpl, hlraw, hlh, hloh, hpl_eq⟩
  refine ⟨w_si, S, Nd, [(w_h.toNat, 248), (w_oh.toNat, 32)], hIA, hBs, hd_ic, ?_⟩
  intro post w_tmp S' Nd'
  dsimp only
  intro hIA_res hBs_res hd_ic_res hd_bs _ hu_ic
  have hic := inputCells_eq_of_unhit hIA hu_ic
  exact ⟨w_si, w_pl, w_raw, w_h, w_oh, w_tmp, S', Nd', hIA_res, hBs_res, hd_ic_res,
    hd_ho, hd_bs (w_h.toNat, 248) (by simp), hd_bs (w_oh.toNat, 32) (by simp),
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "tmp" ≠ ofString "si" by decide, hlsi],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "tmp" ≠ ofString "pl" by decide, hlpl],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "tmp" ≠ ofString "raw" by decide, hlraw],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "tmp" ≠ ofString "h" by decide, hlh],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "tmp" ≠ ofString "oh" by decide, hloh],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
    by rw [hic.1]; exact hpl_eq⟩

theorem ph_storeByte_tmp :
    Hoare PH_TMP (.storeByte (.var .local (ofString "tmp")) (.const 192#64))
      (fun r t => r = none → PH_TMP t) := by
  refine Hoare_storeByte_fall (fun s x w mem' hP hx _ hdom ⟨u, hu⟩ hframe => ?_)
  obtain ⟨w_si, w_pl, w_raw, w_h, w_oh, w_tmp, S, Nd, hIA, hBs, hd_ic, hd_ho, hd_ht, hd_ot,
    hlsi, hlpl, hlraw, hlh, hloh, hltmp, hpl_eq⟩ := hP
  have hx_eq : w_tmp = x := by
    simp only [evalAt, evalHOLExact, hltmp, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hx
    exact hx
  subst hx_eq
  have htmp_good := hBs (w_tmp.toNat, 8) (by simp)
  have halign : panByteAlignHOL w_tmp = w_tmp := by
    unfold panByteAlignHOL
    have hal8 : (2 ^ (64 / 8).log2 : Nat) = 8 := by decide
    dsimp only; rw [hal8]
    have h1 := htmp_good.1
    have hdiv : w_tmp.toNat / 8 * 8 = w_tmp.toNat := by omega
    rw [hdiv]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt w_tmp.isLt]
  rw [halign] at hdom hu hframe
  set mem1 : BitVec 64 → HolWordLab 64 := fun current => if current = w_tmp then .word u else s.memory current
  have hmem_eq : mem' = mem1 := by
    funext a
    by_cases ha : a = w_tmp
    · subst ha; simp [mem1, hu]
    · simp [mem1, ha, hframe a ha]
  subst hmem_eq
  have hst1 : @panMemStoresHOL 64 _ w_tmp (flattenHOL (.val (.word u) : ValueHOL 64)) s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem1 := by
    simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, if_pos hdom]
    rfl
  have htr := store_in_tracked_block (w_base := w_tmp) (sz := 8) (off := 0) (v := .val (.word u))
    hIA hBs (by simp)
    (fun c hc b hb => by simp only [List.mem_singleton] at hb; subst hb; exact hd_ic c hc _ (by simp))
    rfl (by omega) (by rw [BitVec.add_zero]) (by simp [flattenHOL]) hst1
  have hic := inputCells_eq_of_unhit hIA (fun c hc =>
    htr.2.2 c (fun _ => (hIA.2.2.1 c hc).2.1) (hd_ic c hc (w_tmp.toNat, 8) (by simp)))
  exact ⟨w_si, w_pl, w_raw, w_h, w_oh, w_tmp, S, Nd, htr.1, htr.2.1,
    by rw [hic.2.2]; exact hd_ic,
    hd_ho, hd_ht, hd_ot, hlsi, hlpl, hlraw, hlh, hloh, hltmp,
    by rw [hic.1]; exact hpl_eq⟩

theorem ph_keccak_oh
    (wkec : WorldKeeps WorldOK
      (fun s => [(locN s "out", 32),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "keccak256")) :
    Hoare PH_TMP
      (.call (some (none, none)) (ofString "keccak256")
        [.var .local (ofString "tmp"), .const 1#64, .var .local (ofString "oh")])
      (fun r t => r = none → PH_H false t ∧ ∃ w_oh : BitVec 64, t.locals.lookup (ofString "oh") = some (.val (.word w_oh))) := by
  refine ⟨fun {F} state hcode hP _ hr => ?_⟩
  rcases hcall : evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "keccak256")
        [.var .local (ofString "tmp"), .const 1#64, .var .local (ofString "oh")]) with ⟨cres, cpost⟩
  have hr' : cres = none := by rw [hcall] at hr; exact hr
  subst hr'
  obtain ⟨w_si, w_pl, w_raw, w_h, w_oh, w_tmp, S, Nd, hIA, hBs, hd_ic, hd_ho, _, _,
    hlsi, hlpl, hlraw, hlh, hloh, hltmp, hpl_eq⟩ := hP
  rw [evaluateHOLFiniteState_call] at hcall
  have hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "tmp"), .const 1#64, .var .local (ofString "oh")] =
      some [.val (.word w_tmp), .val (.word 1#64), .val (.word w_oh)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, evalHOLExact, hltmp, hloh]
  rw [hargs] at hcall; dsimp only at hcall
  rcases hl : lookupCodeHOLFinite state.code.lookup (ofString "keccak256")
      [.val (.word w_tmp), .val (.word 1#64), .val (.word w_oh)] with _ | ⟨body, callee, ret⟩
  · rw [hl] at hcall; simp at hcall
  · rw [hl] at hcall; dsimp only at hcall
    split_ifs at hcall with hz
    · simp at hcall
    · rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with ⟨bres, post⟩
      rw [hb] at hcall
      cases bres with
      | none => simp at hcall
      | some br =>
        cases br with
        | returned v =>
          dsimp only at hcall
          split_ifs at hcall with hsh
          · obtain ⟨_, hpost_eq⟩ := Prod.mk.inj hcall
            have hpc := callee_param_three state (ofString "keccak256")
              (ofString "p") (ofString "n") (ofString "out") .one .one .one _ _
              (by rw [hcode]; exact R13PayloadStateInit.lookup_keccak256_fn)
              (.var .local (ofString "tmp")) (.const 1#64) (.var .local (ofString "oh"))
              (.val (.word w_tmp)) (.val (.word 1#64)) (.val (.word w_oh))
              [.val (.word w_tmp), .val (.word 1#64), .val (.word w_oh)] body callee ret
              (by simpa [evalAt, evalHOLExact] using hltmp) rfl
              (by simpa [evalAt, evalHOLExact] using hloh) hargs hl
            set entry := callEntryStateHOLFinite state callee
            have hout : locN entry "out" = w_oh.toNat := by
              simp [entry, locN, callEntryStateHOLFinite, hpc.2.2]
            have hW_state : WorldOK state := ⟨hIA.1, S, (worldTyped_iff_with state S).2 ⟨Nd, hIA.2.1⟩⟩
            have hstep := FunSpec.at_lookup wkec state hcode _ body callee ret hl
              (localsFree_worldOK state callee (state.clock - 1) hW_state) (by rw [hb]; simp)
            rw [hb] at hstep; dsimp only at hstep
            have hws := hstep (Or.inl ⟨v, rfl⟩)
            have hIA_entry : InputAtWith entry S Nd w_si.toNat :=
              (inputAtWith_with_locals state callee (state.clock - 1) S Nd w_si.toNat).2 hIA
            have hBs_h : AllBlocksGood entry S Nd [(w_h.toNat, 248)] :=
              (allBlocksGood_with_locals state callee (state.clock - 1) S Nd [(w_h.toNat, 248)]).2
                (fun b hb => hBs b (by simp only [List.mem_singleton] at hb; subst hb; simp))
            have hoh_good := hBs (w_oh.toNat, 32) (by simp)
            have hh_good := hBs (w_h.toNat, 248) (by simp)
            have hRz : ∀ j ∈ [(locN entry "out", 32),
                bufferRegion entry ("keccak_pad", 136),
                bufferRegion entry ("keccak_st", 200)], j.2 = 0 → j.1 % 8 = 0 := by
              intro j hj
              rcases List.mem_cons.1 hj with rfl | hj1
              · intro _; rw [hout]; exact hoh_good.1
              · rcases List.mem_cons.1 hj1 with rfl | hj2
                · exact bufferRegion_zero_aligned entry "keccak_pad" 136 (by decide)
                · simp only [List.mem_singleton] at hj2; subst hj2
                  exact bufferRegion_zero_aligned entry "keccak_st" 200 (by decide)
            obtain ⟨S2, Nd2, hIA_post2, hBs_h2, _, hu_ic2, _⟩ :=
              WorldStep_preserves_inputAndBlocks hIA_entry hBs_h hws hRz
                (fun j hj k hk => by
                  rcases List.mem_cons.1 hj with rfl | hj1
                  · rw [hout]; exact hoh_good.2.2.2.2 k (worldTypedIvls_sub_worldOwned _ _ _ k hk)
                  · rcases List.mem_cons.1 hj1 with rfl | hj2
                    · exact bufferRegion_disj_le hIA_entry.2.1 ("keccak_pad", 136) (by decide) (by decide) 136 le_rfl k hk
                    · simp only [List.mem_singleton] at hj2; subst hj2
                      exact bufferRegion_disj_le hIA_entry.2.1 ("keccak_st", 200) (by decide) (by decide) 200 le_rfl k hk)
                (fun c hc j hj => by
                  rcases List.mem_cons.1 hj with rfl | hj1
                  · rw [hout]; exact hd_ic c hc (w_oh.toNat, 32) (by simp)
                  · rcases List.mem_cons.1 hj1 with rfl | hj2
                    · exact hIA_entry.2.2.2.1 c hc _ (bufferRegion_mem_worldOwned entry S Nd (gn := ("keccak_pad", 136)) (by decide))
                    · simp only [List.mem_singleton] at hj2; subst hj2
                      exact hIA_entry.2.2.2.1 c hc _ (bufferRegion_mem_worldOwned entry S Nd (gn := ("keccak_st", 200)) (by decide)))
                (fun b hb j hj => by
                  simp only [List.mem_singleton] at hb; subst hb
                  rcases List.mem_cons.1 hj with rfl | hj1
                  · rw [hout]; exact hd_ho
                  · rcases List.mem_cons.1 hj1 with rfl | hj2
                    · exact hh_good.2.2.2.2 _ (bufferRegion_mem_worldOwned entry S Nd (gn := ("keccak_pad", 136)) (by decide))
                    · simp only [List.mem_singleton] at hj2; subst hj2
                      exact hh_good.2.2.2.2 _ (bufferRegion_mem_worldOwned entry S Nd (gn := ("keccak_st", 200)) (by decide)))
            have hic := inputCells_eq_of_unhit hIA hu_ic2
            set resumed := { post with locals := state.locals }
            have hRes : PH_H false resumed ∧ ∃ w_oh' : BitVec 64, resumed.locals.lookup (ofString "oh") = some (.val (.word w_oh')) := by
              refine ⟨⟨w_si, w_pl, w_raw, w_h, S2, Nd2,
                (inputAtWith_with_locals post state.locals post.clock S2 Nd2 w_si.toNat).2 hIA_post2,
                (allBlocksGood_with_locals post state.locals post.clock S2 Nd2 [(w_h.toNat, 248)]).2 hBs_h2,
                ?_, hlsi, hlpl, hlraw, hlh, ?_, fun h => by cases h⟩, w_oh, hloh⟩
              · change IvlsDisj (inputCells post w_si.toNat) [(w_h.toNat, 248)]
                rw [hic.2.2]
                exact fun c hc b hb => by simp only [List.mem_singleton] at hb; subst hb; exact hd_ic c hc _ (by simp)
              · change w_pl.toNat = memW post w_si.toNat; rw [hic.1]; exact hpl_eq
            rwa [hpost_eq] at hRes
          · simp at hcall
        | _ => simp [emptyLocalsHOLFinite] at hcall

theorem ph_store_h16_oh :
    Hoare (fun s => PH_H false s ∧ ∃ w_oh : BitVec 64, s.locals.lookup (ofString "oh") = some (.val (.word w_oh)))
      (.store (.op .add [.var .local (ofString "h"), .const 16#64]) (.var .local (ofString "oh")))
      (fun r t => r = none → PH_H false t) := by
  refine Hoare_store_fall (fun s x v mem' ⟨hH, w_oh, hloh⟩ hx hv hst => ?_)
  obtain ⟨w_si, w_pl, w_raw, w_h, S, Nd, hIA, hBs, hd_ic, hlsi, hlpl, hlraw, hlh, hpl_eq, _⟩ := hH
  have hx_eq := evalAt_add_local_const hlh hx
  have hv_eq : v = .val (.word w_oh) := by
    simp only [evalAt, evalHOLExact, hloh, Option.some.injEq] at hv; exact hv.symm
  subst hv_eq
  have htr := store_in_tracked_block (off := 16) hIA hBs (by simp) hd_ic rfl (by omega) hx_eq (by simp [flattenHOL]) hst
  have hic := inputCells_eq_of_unhit hIA (fun c hc =>
    htr.2.2 c (fun _ => (hIA.2.2.1 c hc).2.1) (hd_ic c hc _ (by simp)))
  exact ⟨w_si, w_pl, w_raw, w_h, S, Nd, htr.1, htr.2.1,
    by rw [hic.2.2]; exact hd_ic,
    hlsi, hlpl, hlraw, hlh, by rw [hic.1]; exact hpl_eq, fun h => by cases h⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
