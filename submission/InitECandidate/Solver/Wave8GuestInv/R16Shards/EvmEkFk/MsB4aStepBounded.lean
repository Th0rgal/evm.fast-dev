import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.MsB1Delta
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.MsB3eExtCodeChainBounded

/-!
# Scratch Rung B4a: `EvmMsgReadyMsgBounded`, `StepFromCC`, `D0PreB`, and `msgBounded_side`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.EvmBase
open InitECandidate.Solver.Wave8GuestInv.EvmStepLemmas
open InitECandidate.Solver.Wave8GuestInv.EvmFrameSpecs
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8M19.Htab
open InitECandidate.Solver.Wave8GuestInv.HtabC00Ports
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge

section StepBounded
open R10Shards.GbodyProcessMsg
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

/-- Combined invariant for `depth0_prepare`, `set_delegation`, and `prepare_dispatch`:
carries both `MsgDisjCodeStrong` (so msg-field stores avoid live code-DB records)
and `CodeDbPayloadBoundedNz` (so `ext_code_of` yields `code_n < 2^40` and `set_code` preserves it). -/
def EvmMsgReadyMsgBounded : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ MsgDisjCodeStrong s ∧ ∃ S, EvmInvAt s S ∧
    MsgOwned s S (memW s (globN s "ev" + 112)) ∧ CodeDbPayloadBoundedNz s S

theorem evmMsgReadyBounded_of_msgBounded {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : EvmMsgReadyMsgBounded s) : EvmMsgReadyBounded s := by
  obtain ⟨hA, _, S, hI, hm, hC⟩ := h
  exact ⟨hA, S, hI, hm, hC⟩

theorem evmMsgReady_of_msgBounded {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : EvmMsgReadyMsgBounded s) : EvmMsgReady s :=
  evmMsgReady_of_bounded (evmMsgReadyBounded_of_msgBounded h)

theorem evmInv_of_msgBounded {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : EvmMsgReadyMsgBounded s) : EvmInv s :=
  evmInv_of_bounded (evmMsgReadyBounded_of_msgBounded h)

theorem evmMsgReadyMsgBounded_of_msgCodeStrong {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : EvmMsgReadyMsgCodeStrong s) : EvmMsgReadyMsgBounded s := by
  obtain ⟨hA, hM, S, hI, hm, hC⟩ := h
  exact ⟨hA, hM, S, hI, hm, codeDbPayloadBoundedNz_of_nonzero hA hC⟩

theorem localsFree_evmMsgReadyMsgBounded : LocalsFree EvmMsgReadyMsgBounded := by
  intro F s locals k ⟨hA, hM, S, hI, hm, hC⟩
  obtain ⟨hAp, S', hIp, hmp, hCp⟩ := localsFree_evmMsgReadyBounded s locals k ⟨hA, S, hI, hm, hC⟩
  exact ⟨hAp, (msgDisjCodeStrong_with_locals_clock s locals k).2 hM, S', hIp, hmp, hCp⟩

/-- `frame_open(msg, 0)` transitions `FrameOpenReadyMsgCodeStrong` to `EvmMsgReadyMsgBounded`. -/
theorem fk_frame_open_msgBounded :
    KeepsOn FrameOpenReadyMsgCodeStrong EvmMsgReadyMsgBounded (ofString "frame_open") := by
  obtain ⟨ps, b, rs, hl, hk⟩ := fk_frame_open_msgCodeStrong
  exact ⟨ps, b, rs, hl, fun s hc hP hex hnt hr =>
    evmMsgReadyMsgBounded_of_msgCodeStrong (hk s hc hP hex hnt hr)⟩

/-- `EvmStep` paired with `ChainCellsAgree` across `evmChain s`. -/
def EvmStepCC (gw : List String) {F : Type} (s post : PanSemStateFiniteExact 64 F) : Prop :=
  EvmStep gw s post ∧ ChainCellsAgree s post

/-- Snapshot of the 4 aligned-chain words `(ec.1+24, ec.1+32, ec.1+40, ec.2+56)` across `ch`. -/
def chainCells {F : Type} (s : PanSemStateFiniteExact 64 F) (ch : List Ivl) :
    List (Nat × Nat × Nat × Nat) :=
  ch.map fun ec => (memW s (ec.1 + 24), memW s (ec.1 + 32), memW s (ec.1 + 40), memW s (ec.2 + 56))

/-- `F`-polymorphic `StepFrom` augmented with `chainCells t ch = cells` (encoding `EvmStepCC`). -/
def StepFromCC (gw : List String) (hp : Nat) (G : MlS → Option (ValueHOL 64))
    (ch : List Ivl) (cells : List (Nat × Nat × Nat × Nat))
    {F : Type} (t : PanSemStateFiniteExact 64 F) : Prop :=
  StepFrom gw hp G ch t ∧ chainCells t ch = cells

theorem stepFromCC_refl {F : Type} (gw : List String) (s : PanSemStateFiniteExact 64 F)
    (h : EvmInv s) :
    StepFromCC gw (globN s "heap_ptr") s.globals.lookup (evmChain s) (chainCells s (evmChain s)) s :=
  ⟨stepFrom_refl gw s h, rfl⟩

theorem chainCells_eq_of_agree {F : Type} {s t : PanSemStateFiniteExact 64 F} {ch : List Ivl}
    (hch : evmChain s = ch) (hag : ChainCellsAgree s t) :
    chainCells t ch = chainCells s ch := by
  subst hch
  unfold chainCells
  apply List.map_congr_left
  intro ec hec
  obtain ⟨h1, h2, h3, h4⟩ := hag ec hec
  rw [h1, h2, h3, h4]

theorem chainCellsAgree_of_chainCells_eq {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (heq : chainCells t (evmChain s) = chainCells s (evmChain s)) :
    ChainCellsAgree s t := by
  intro ec hec
  unfold chainCells at heq
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hec
  have hget := congrArg (fun l => l[i]?) heq
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some, Option.some.injEq,
    Prod.mk.injEq] at hget
  exact ⟨hget.1, hget.2.1, hget.2.2.1, hget.2.2.2⟩

theorem stepFromCC_of_evmStepCC {F : Type} {gw gw' : List String} {hp : Nat}
    {G : MlS → Option (ValueHOL 64)} {ch : List Ivl} {cells : List (Nat × Nat × Nat × Nat)}
    {s t : PanSemStateFiniteExact 64 F}
    (hsub : ∀ g ∈ gw', g ∈ gw)
    (h0 : StepFromCC gw hp G ch cells s) (h : EvmStepCC gw' s t) :
    StepFromCC gw hp G ch cells t :=
  ⟨stepFrom_of_evmStep hsub h0.1 h.1,
   (chainCells_eq_of_agree h0.1.2.2.2 h.2).trans h0.2⟩

theorem evmStepCC_of_stepFromCC {F : Type} {gw : List String} {s t : PanSemStateFiniteExact 64 F}
    (h : StepFromCC gw (globN s "heap_ptr") s.globals.lookup (evmChain s) (chainCells s (evmChain s)) t) :
    EvmStepCC gw s t :=
  ⟨h.1, chainCellsAgree_of_chainCells_eq h.2⟩

theorem localsFree_stepFromCC (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (cells : List (Nat × Nat × Nat × Nat)) :
    LocalsFree (StepFromCC gw hp G ch cells) := by
  intro F s locals k ⟨hS, hc⟩
  exact ⟨localsFree_stepFrom gw hp G ch s locals k hS, hc⟩

/-- Strengthened `D0Pre` carrying `EvmMsgReadyMsgBounded` and `StepFromCC`. -/
def D0PreB (gw : List String) (hp : Nat) (G : MlS → Option (ValueHOL 64))
    (ch : List Ivl) (cells : List (Nat × Nat × Nat × Nat))
    {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  (EvmMsgReadyMsgBounded s ∧ StepFromCC gw hp G ch cells s) ∧
  ∃ m : BitVec 64, s.locals.lookup (ofString "msg") = some (.val (.word m)) ∧
    m.toNat = memW s (globN s "ev" + 112)

theorem d0Pre_of_d0PreB {gw : List String} {hp : Nat} {G : MlS → Option (ValueHOL 64)}
    {ch : List Ivl} {cells : List (Nat × Nat × Nat × Nat)}
    {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : D0PreB gw hp G ch cells s) : D0Pre gw hp G ch s :=
  ⟨⟨evmMsgReady_of_msgBounded h.1.1, h.1.2.1⟩, h.2⟩

theorem d0PreB_locals (gw : List String) (hp : Nat) (G : MlS → Option (ValueHOL 64))
    (ch : List Ivl) (cells : List (Nat × Nat × Nat × Nat))
    {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (hmsg : locals.lookup (ofString "msg") = s.locals.lookup (ofString "msg"))
    (h : D0PreB gw hp G ch cells s) :
    D0PreB gw hp G ch cells {s with locals := locals, clock := k} := by
  obtain ⟨⟨hP, hS⟩, m, hm, hm_eq⟩ := h
  refine ⟨⟨localsFree_evmMsgReadyMsgBounded s locals k hP,
           localsFree_stepFromCC gw hp G ch cells s locals k hS⟩,
          m, ?_, hm_eq⟩
  dsimp only; rwa [hmsg]

theorem d0PreB_of_stepFromCC (gw : List String) (hp : Nat) (G : MlS → Option (ValueHOL 64))
    (ch : List Ivl) (cells : List (Nat × Nat × Nat × Nat))
    {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (hpre : D0PreB gw hp G ch cells s) (hP : EvmMsgReadyMsgBounded t)
    (hS : StepFromCC gw hp G ch cells t) (hloc : t.locals = s.locals)
    (hG : t.globals.lookup (ofString "ev") = s.globals.lookup (ofString "ev"))
    (hmem : memW t (globN s "ev" + 112) = memW s (globN s "ev" + 112)) :
    D0PreB gw hp G ch cells t := by
  obtain ⟨_, m, hm, hm_eq⟩ := hpre
  refine ⟨⟨hP, hS⟩, m, by rw [hloc]; exact hm, ?_⟩
  have hev : globN t "ev" = globN s "ev" := by simp [globN, hG]
  rw [hev, hmem]; exact hm_eq

/-- Master preservation helper for `CodeDbPayloadBoundedNz` + `MsgDisjCodeStrong` across any step
that preserves `SameTypedCells s post S Nd`, `fixedObjects`, non-heap core globals, `ev+112`,
and `memW post (p + 8)` on live code-DB entries. -/
theorem msgBounded_side_of_sameTypedCells {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hWT : WorldTypedWith s S Nd)
    (hC : CodeDbPayloadBoundedNz s S) (hM : MsgDisjCodeStrong s)
    (hcell : EvmBase.SameTypedCells s post S Nd)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hcg : ∀ g ∈ (["ws", "bs", "ts", "ev"] : List String), globN post g = globN s g)
    (h112 : memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112))
    (hfix : fixedObjects post = fixedObjects s)
    (hw : ∀ g k, (g, k) ∈ ([("ws", 16), ("bs", 48), ("ts", 48)] : List (String × Nat)) →
      globN s g ≠ 0 → memW s (globN s g + k) ≠ 0 →
      ∀ p ∈ htabValues s (memW s (globN s g + k)), memW post (p + 8) = memW s (p + 8)) :
    CodeDbPayloadBoundedNz post S ∧ MsgDisjCodeStrong post := by
  have hroot_eq : ∀ g k, (g, k) ∈ ([("ws", 16), ("bs", 48), ("ts", 48)] : List (String × Nat)) →
      globN s g ≠ 0 → memW post (globN s g + k) = memW s (globN s g + k) := by
    intro g k hgk hgn
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk
    rcases hgk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact typed_record_root_preserved hAs hWT hcell "ws" 40 16 (by decide) hgn (by decide)
    · exact typed_record_root_preserved hAs hWT hcell "bs" 80 48 (by decide) hgn (by decide)
    · exact typed_record_root_preserved hAs hWT hcell "ts" 72 48 (by decide) hgn (by decide)
  have hdb_S : ∀ g k, (g, k) ∈ ([("ws", 16), ("bs", 48), ("ts", 48)] : List (String × Nat)) →
      globN s g ≠ 0 → memW s (globN s g + k) ≠ 0 → memW s (globN s g + k) ∈ S := by
    intro g k hgk hgn hdb
    have hroot : RootIn S (memW s (globN s g + k)) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk
      rcases hgk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hWT.1.2.2.2.1 16 (by decide) hgn
      · exact hWT.1.2.2.2.2.1 48 (by decide) hgn
      · exact hWT.1.2.2.2.2.2.1 48 (by decide) hgn
    rcases hroot with h0 | hS
    · exact (hdb h0).elim
    · exact hS
  have hfp : ∀ t ∈ S, htabFootprint post t = htabFootprint s t :=
    fun t ht => EvmBase.htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1
  refine ⟨?_, ?_⟩
  · intro g k hgk hgn_p hdb_p
    have hgg : globN post g = globN s g := hcg g (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk
      rcases hgk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp)
    have hgn : globN s g ≠ 0 := by rwa [hgg] at hgn_p
    have hr := hroot_eq g k hgk hgn
    have hdb : memW s (globN s g + k) ≠ 0 := by rwa [hgg, hr] at hdb_p
    have hmS := hdb_S g k hgk hgn hdb
    rw [hgg, hr]
    exact codeDbPayloadBounded_of_preserved_layout (hC g k hgk hgn hdb) hAs hAp hhp
      (EvmBase.htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1)
      (hw g k hgk hgn hdb) hfp hfix
  · intro g k hgk hgn_p hdb_p p hp
    have hgg : globN post g = globN s g := hcg g (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk
      rcases hgk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp)
    have hgn : globN s g ≠ 0 := by rwa [hgg] at hgn_p
    have hr := hroot_eq g k hgk hgn
    have hdb : memW s (globN s g + k) ≠ 0 := by rwa [hgg, hr] at hdb_p
    have hmS := hdb_S g k hgk hgn hdb
    rw [hgg, hr, EvmBase.htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1] at hp
    rw [hcg "ev" (by simp), h112]
    exact hM g k hgk hgn hdb p hp

/-- Any `ByteRegionEffect` confined to `[(memW s (globN s "ev" + 112), 176)]` preserves
`EvmMsgReadyMsgBounded`, yields `EvmStepCC [] s post`, and leaves `memW _ (globN s "ev" + 112)` intact. -/
theorem evmMsgReadyMsgBounded_of_msg_bre {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hPB : EvmMsgReadyMsgBounded s)
    (heff : EvmStepLemmas.ByteRegionEffect s post [(memW s (globN s "ev" + 112), 176)]) :
    EvmMsgReadyMsgBounded post ∧ EvmStepCC [] s post ∧
    memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112) := by
  obtain ⟨hAs, hMS, S, hInv, hMO, hCB⟩ := hPB
  have hP : EvmMsgReady s := ⟨hAs, S, hInv, hMO⟩
  obtain ⟨hal_m, hw_m, hd_tab, hd_fix, hd_fo, Nd1, hTr1, hdj_nd1⟩ := hMO
  obtain ⟨Nd2, hTr2, hAT2⟩ := hInv.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hTr_int, hsub_int⟩ := triesTypedWith_inter hTr1 hTr2
  let Nd := Nd1.filter (fun n => decide (n ∈ Nd2))
  have hTr : TriesTypedWith s S Nd := hTr_int
  have hWT : WorldTypedWith s S Nd := ⟨hInv.1.1, hInv.1.2.1, hInv.1.2.2.1, hTr⟩
  let Rl : List Ivl := [(memW s (globN s "ev" + 112), 176)]
  have hdj_all : ∀ x ∈ Rl, ∀ o ∈ worldTypedIvls s S Nd ++ ((evmChain s).map (frameObjects s)).flatten,
      Disj x o := by
    intro x hx o ho
    simp only [Rl, List.mem_singleton] at hx
    subst hx
    rcases List.mem_append.1 ho with how | hof
    · have hjo := R13Shards.worldTypedIvls_sub_worldOwned how
      unfold worldOwned at hjo
      rcases List.mem_append.1 hjo with hjo | hjn
      · rcases List.mem_append.1 hjo with hjt | hjx
        · obtain ⟨t, ht, hi⟩ := List.mem_flatMap.1 hjt
          exact hd_tab t ht o hi
        · exact hd_fix o hjx
      · exact hdj_nd1 _ (List.mem_singleton.2 rfl) o (hsub_int o hjn).1
    · obtain ⟨os, hos, hjo⟩ := List.mem_flatten.1 hof
      obtain ⟨ec, hec, rfl⟩ := List.mem_map.1 hos
      exact hd_fo ec hec o hjo
  have hAT_Nd : ∀ o ∈ ((evmChain s).map (frameObjects s)).flatten, ∀ j ∈ nodeExtents s Nd, Disj o j :=
    fun o ho j hj => hAT2 o ho j (hsub_int j hj).2
  have hdj_w : ∀ x ∈ Rl, ∀ i ∈ worldTypedIvls s S Nd, i.2 = 0 ∨ Disj x i :=
    fun x hx i hi => Or.inr (hdj_all x hx i (List.mem_append_left _ hi))
  have hdj_f : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, o.2 ≠ 0 → ∀ x ∈ Rl, Disj x o :=
    fun ec hec o ho _ x hx => hdj_all x hx o (List.mem_append_right _
      (List.mem_flatten.2 ⟨frameObjects s ec, List.mem_map.2 ⟨ec, hec, rfl⟩, ho⟩))
  have hglob_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, heff.globals]
  have hApost : ArenaReady post :=
    ⟨guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hAs.1,
     arenaOK_congr heff.globals hAs.2⟩
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hglob_eq]
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hglob_eq]
  have hG : GlobalsKept [] s post := fun _ _ => by rw [heff.globals]
  have hbfr : EvmBase.ByteFrameOutside s post ([] ++ Rl ++ [freeGap s]) (heapFree s) := by
    refine ⟨heff.be, heff.memaddrs, hAs.1.memaddrs, ?_, ?_, ?_, ?_⟩
    · intro a hna; apply heff.out_dom a; rwa [hAs.1.memaddrs]
    · intro a ha _; exact heff.cell_frame a (fun x hx _ => ha x (List.mem_append_left [freeGap s] hx))
    · intro a ha hdja _
      have hbit : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
      apply heff.cell_frame (BitVec.ofNat 64 a)
      intro x hx hx0; rw [hbit]
      exact EvmBase.not_cellHits_of_disj_aligned hx0 (i := (a, 8)) (by dsimp only; omega) (by dsimp only; omega)
        (hdja x (List.mem_append_left [freeGap s] hx))
    · intro b hb hno _
      exact heff.byte_frame b hb (fun x hx => hno x (List.mem_append_left [freeGap s] hx))
  have hcell : EvmBase.SameTypedCells s post S Nd :=
    EvmBase.sameTypedCells_of_byteFrame hAs hWT (R := []) (extra := Rl) (fun _ h => List.not_mem_nil h |>.elim) hdj_w hbfr
  have hfeq := EvmBase.fixedObjects_eq_of_nonHeapGlobalsKept hAs.2 hWT.1 hWT.2.2.1 hcell
    (fun name _ _ _ => by rw [heff.globals])
  have hFT_post := EvmBase.fixedTyped_of_eq hApost hWT.2.2.1 hh hsc hfeq
  obtain ⟨hWT_post, _⟩ := EvmBase.worldTypedWith_congr_w1 hAs hApost hh hsc
    (fun g _ => hglob_eq g) hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hW_post : WorldTyped post S :=
    ⟨hWT_post.1, hWT_post.2.1, hWT_post.2.2.1, Nd, hWT_post.2.2.2⟩
  obtain ⟨_, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW, hFO_pw, hFO_disj, _, hMarks, hRoles, hGas⟩ := hInv
  have hrec_eq : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → memW post (ec.2 + k) = memW s (ec.2 + k)) ∧
      (∀ k, k + 8 ≤ 24 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) := by
    intro ec hec
    obtain ⟨hb1, hb2, hb88, _⟩ := EvmStepLemmas.frameWF_bounds hAs.2 (hFW_all ec hec)
    refine ⟨fun k hk => memW_eq_of_frameDisj heff hb1 hk (hdj_f ec hec (ec.1, 280) (by simp [frameObjects]) (by simp)),
            fun k hk => memW_eq_of_frameDisj heff hb2 hk (hdj_f ec hec (ec.2, 104) (by simp [frameObjects]) (by simp)),
            fun k hk => memW_eq_of_frameDisj heff hb88 hk (hdj_f ec hec (memW s (ec.1 + 88), 24) (by simp [frameObjects]) (by simp))⟩
  have hchain_aux : ∀ (fuel e c : Nat),
      (∀ ec ∈ evmChainFrom s fuel e c, ec ∈ evmChain s) →
      evmChainFrom post fuel e c = evmChainFrom s fuel e c := by
    intro fuel
    induction fuel with
    | zero => intros; rfl
    | succ fuel ih =>
      intro e c hsub
      have hec : (e, c) ∈ evmChain s := hsub (e, c) (by simp [evmChainFrom])
      obtain ⟨_, hc_eq, _⟩ := hrec_eq (e, c) hec
      have hc16 := hc_eq 16 (by omega)
      have hc0 : memW post c = memW s c := by simpa using hc_eq 0 (by omega)
      have hc8 := hc_eq 8 (by omega)
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
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    unfold frameLogs
    rw [he_eq 88 (by omega), show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by simpa using h88_eq 0 (by omega),
        h88_eq 16 (by omega)]
  have hframeRet_eq : ∀ ec ∈ evmChain s, frameRet post ec = frameRet s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameRet
    rw [he_eq 216 (by omega), he_eq 144 (by omega)]
  have hflo_and_logsOK : ∀ ec ∈ evmChain s,
      frameLogObjects post ec = frameLogObjects s ec ∧ LogsListOK post (memW post (ec.1 + 88)) := by
    intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    refine frameLogObjects_and_logsOK_eq hAs.2 (hFW_all ec hec) heff (he_eq 88 (by omega)) h88_eq ?_ ?_
    · by_cases hfl0 : (frameLogs s ec).2 = 0
      · exact Or.inr (Or.inl hfl0)
      · exact Or.inr (Or.inr (hdj_f ec hec (frameLogs s ec) (by simp [frameObjects]) hfl0))
    · intro o ho honz
      exact hdj_f ec hec o (by unfold frameObjects; exact List.mem_append_right _ ho) honz
  have hframeObjects_eq : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameObjects
    rw [he_eq 8 (by omega), he_eq 232 (by omega), he_eq 24 (by omega), he_eq 40 (by omega),
        he_eq 88 (by omega), hframeLogs_eq ec hec, hframeRet_eq ec hec, (hflo_and_logsOK ec hec).1]
  have hframeScratch_eq : ∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameScratch
    rw [he_eq 8 (by omega), he_eq 232 (by omega), he_eq 88 (by omega)]
  have hmap_fo_eq : (evmChain s).map (frameObjects post) = (evmChain s).map (frameObjects s) :=
    List.map_congr_left hframeObjects_eq
  have hframeRoleSlots_eq : frameRoleSlots post (evmChain s) = frameRoleSlots s (evmChain s) := by
    unfold frameRoleSlots
    apply List.flatMap_congr
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    rw [he_eq 136 (by omega), he_eq 168 (by omega), he_eq 176 (by omega)]
  have hInv_post : EvmInvAt post S := by
    refine ⟨hW_post, ?_⟩
    rw [hchain_eq]
    refine ⟨hch_ne, hch_len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨ec, hec, hk0⟩ := hch_last
      have hec_mem : ec ∈ evmChain s := List.mem_of_getLast? hec
      exact ⟨ec, hec, by rw [(hrec_eq ec hec_mem).2.1 16 (by omega)]; exact hk0⟩
    · intro ec hec
      obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
      obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, _, c17⟩ := hFW_all ec hec
      have hlogOK_post := (hflo_and_logsOK ec hec).2
      have hmsg_post : MsgOwned post S (memW post (ec.1 + 112)) := by
        rw [he_eq 112 (by omega)]
        exact msgOwned_congr hAs.2 hWT.1 hTr hcell hh hsc (hglob_eq "ws") hWT.2.2.1 hFT_post hfeq
          hWT_post.1 hchain_eq hframeObjects_eq c17
      unfold FrameWF
      dsimp only
      rw [he_eq 8 (by omega), he_eq 232 (by omega), he_eq 88 (by omega), he_eq 24 (by omega),
          he_eq 40 (by omega), he_eq 16 (by omega), he_eq 32 (by omega), he_eq 136 (by omega),
          he_eq 168 (by omega), he_eq 176 (by omega),
          h88_eq 16 (by omega), h88_eq 8 (by omega),
          hframeLogs_eq ec hec, he_eq 216 (by omega), he_eq 144 (by omega), hframeRet_eq ec hec,
          hglob_eq "scratch_ptr", hglob_eq "frame_mem_ptr", hglob_eq "heap_ptr", hglob_eq "evm_empty"]
      refine ⟨?_, c2, (EvmBase.wordsOK_congr_of_dom heff.memaddrs).2 c3, c4, c5, c6, c7, c8, c9, c10, c11, c12,
        c13, (EvmBase.wordsOK_congr_of_dom heff.memaddrs).2 c14, ?_, by rwa [he_eq 88 (by omega)] at hlogOK_post,
        hmsg_post⟩
      · intro i hi
        obtain ⟨hin, hw⟩ := c1 i hi
        exact ⟨hin, (EvmBase.wordsOK_congr_of_dom heff.memaddrs).2 hw⟩
      · rcases c15 with h0 | ⟨hin, hw⟩
        · exact Or.inl h0
        · exact Or.inr ⟨hin, (EvmBase.wordsOK_congr_of_dom heff.memaddrs).2 hw⟩
    · intro ec hec
      have hec_mem : ec ∈ evmChain s := List.mem_of_mem_tail hec
      unfold FrameRoom
      rw [(hrec_eq ec hec_mem).1 16 (by omega), (hrec_eq ec hec_mem).1 232 (by omega)]
      exact hFR_all ec hec
    · intro i hi
      have hi0 : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
      have hi1 : (evmChain s)[i + 1] ∈ evmChain s := List.getElem_mem _
      rw [(hrec_eq _ hi0).2.1 80 (by omega), (hrec_eq _ hi0).2.1 72 (by omega),
          (hrec_eq _ hi1).1 40 (by omega)]
      exact hRW i hi
    · rw [hmap_fo_eq]; exact hFO_pw
    · intro ec hec o ho
      rw [hframeObjects_eq ec hec] at ho
      rw [hfeq]
      refine ⟨fun t ht i hi => ?_, (hFO_disj ec hec o ho).2⟩
      rw [EvmBase.htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1] at hi
      exact (hFO_disj ec hec o ho).1 t ht i hi
    · rw [hmap_fo_eq]
      refine ⟨Nd, hWT_post.2.2.2, fun o ho j hj => ?_⟩
      rw [EvmBase.nodeExtents_eq hTr.1 hcell] at hj
      exact hAT_Nd o ho j hj
    · have hworldRefs_eq : worldTableRefs post S = worldTableRefs s S := by
        unfold worldTableRefs recordSlots
        rw [hglob_eq "ws", hglob_eq "bs", hglob_eq "ts",
            show globalTableRoots.map (globN post) = globalTableRoots.map (globN s) by
              simp only [globalTableRoots, List.map, hglob_eq],
            EvmBase.balRecords_eq hWT.1 hcell (hglob_eq "bal_accounts"),
            hglob_eq "journal_n", hglob_eq "journal"]
        have hws_sl : (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW post (globN s "ws" + k)) =
            (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW s (globN s "ws" + k)) := by
          split
          · rfl
          · rename_i hnz
            apply List.map_congr_left; intro k hk
            have hk_le : k + 8 ≤ 40 := by
              simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
              rcases hk with rfl | rfl <;> omega
            exact EvmBase.memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 40) (by decide) hnz hk_le
        have hbs_sl : (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW post (globN s "bs" + k)) =
            (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW s (globN s "bs" + k)) := by
          split
          · rfl
          · rename_i hnz
            apply List.map_congr_left; intro k hk
            have hk_le : k + 8 ≤ 80 := by
              simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
              rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
            exact EvmBase.memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 80) (by decide) hnz hk_le
        have hts_sl : (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW post (globN s "ts" + k)) =
            (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW s (globN s "ts" + k)) := by
          split
          · rfl
          · rename_i hnz
            apply List.map_congr_left; intro k hk
            have hk_le : k + 8 ≤ 72 := by
              simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
              rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
            exact EvmBase.memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 72) (by decide) hnz hk_le
        have hnest_bs : (if globN s "bs" ≠ 0 ∧ memW post (globN s "bs" + 32) ∈ S then htabValues post (memW post (globN s "bs" + 32)) else []) =
            (if globN s "bs" ≠ 0 ∧ memW s (globN s "bs" + 32) ∈ S then htabValues s (memW s (globN s "bs" + 32)) else []) := by
          by_cases hnz : globN s "bs" = 0
          · simp [hnz]
          · rw [EvmBase.memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 80) (by decide) hnz (by omega)]
            by_cases hmS : memW s (globN s "bs" + 32) ∈ S
            · simp [hnz, hmS, EvmBase.htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1]
            · simp [hnz, hmS]
        have hnest_ts : (if globN s "ts" ≠ 0 ∧ memW post (globN s "ts" + 32) ∈ S then htabValues post (memW post (globN s "ts" + 32)) else []) =
            (if globN s "ts" ≠ 0 ∧ memW s (globN s "ts" + 32) ∈ S then htabValues s (memW s (globN s "ts" + 32)) else []) := by
          by_cases hnz : globN s "ts" = 0
          · simp [hnz]
          · rw [EvmBase.memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 72) (by decide) hnz (by omega)]
            by_cases hmS : memW s (globN s "ts" + 32) ∈ S
            · simp [hnz, hmS, EvmBase.htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1]
            · simp [hnz, hmS]
        have hbal_fl : (balRecords s).flatMap (fun ad => [memW post ad, memW post (ad + 8)]) =
            (balRecords s).flatMap (fun ad => [memW s ad, memW s (ad + 8)]) := by
          apply List.flatMap_congr; intro ad had
          have had_mem := EvmBase.balRecord_ivl_mem had
          rcases EvmBase.fixedObject_le_2pow64 hAs.2 hWT.2.2.1 (EvmBase.bal_in_fixedObjects had_mem) with h0 | had_bnd
          · dsimp only at h0; omega
          · dsimp only at had_bnd
            have hwti_ad := EvmBase.mem_worldTypedIvls_bal (S := S) (Nd := Nd) had_mem
            rw [EvmBase.memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩,
                EvmBase.memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩]
        have hjrn_mp : (List.range (globN s "journal_n")).map (fun k => memW post (globN s "journal" + 32 * k)) =
            (List.range (globN s "journal_n")).map (fun k => memW s (globN s "journal" + 32 * k)) := by
          apply List.map_congr_left; intro k hk
          rw [List.mem_range] at hk
          have hjcz : globN s "journal_cap" ≠ 0 := by have := hWT.2.1.1; omega
          rcases hWT.2.1.2.2.1 with h0 | ⟨hal, _⟩
          · exact absurd h0 hjcz
          · have hbnd := EvmBase.allocated_le_2pow64 hAs.2 hal
            dsimp only at hbnd
            have hwti := EvmBase.mem_worldTypedIvls_journal (s := s) (S := S) (Nd := Nd)
            simp only [hjcz, ↓reduceIte] at hwti
            have hlt : 32 * k + 8 ≤ 32 * globN s "journal_cap" := by
              have := hWT.2.1.1; have := hWT.2.1.2.1; omega
            exact EvmBase.memW_eq_of_cellHits hcell (by omega) hwti ⟨by dsimp only; omega, by dsimp only; omega⟩
        dsimp only
        rw [hglob_eq "bs", hglob_eq "ts", hws_sl, hbs_sl, hts_sl, hnest_bs, hnest_ts, hbal_fl, hjrn_mp]
      have hdelEx_iff : ∀ i t, DelExclusive post S (evmChain s) i t ↔ DelExclusive s S (evmChain s) i t := by
        intro i t
        unfold DelExclusive
        rw [hworldRefs_eq]
        refine and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun hj =>
          forall_congr' fun k => imp_congr_right fun hk => ?_)
        have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
        have hk_le : k + 8 ≤ 280 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl <;> omega
        rw [(hrec_eq _ hj_mem).1 k hk_le]
      intro i hi
      have hi_mem : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
      have hm_eq := (hrec_eq _ hi_mem).2.1 48 (by omega)
      have hmm_eq := (hrec_eq _ hi_mem).2.1 56 (by omega)
      have he24_eq := (hrec_eq _ hi_mem).1 24 (by omega)
      have htake_eq : ((evmChain s).take (i + 1)).map (fun ec => memW post (ec.1 + 136)) =
          ((evmChain s).take (i + 1)).map (fun ec => memW s (ec.1 + 136)) := by
        apply List.map_congr_left; intro ec hec
        exact (hrec_eq ec (List.mem_of_mem_take hec)).1 136 (by omega)
      have hM := hMarks i hi
      dsimp only at hM ⊢
      rw [hm_eq, hmm_eq, he24_eq, hframeScratch_eq _ hi_mem, hfeq, htake_eq]
      obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM
      refine ⟨m1, m2, m3, m4, ?_, m6, m7, ?_, m9⟩
      · intro j hj hij
        have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
        rw [hframeScratch_eq _ hj_mem, hframeObjects_eq _ hj_mem, hframeLogs_eq _ hj_mem,
            (hrec_eq _ hj_mem).1 112 (by omega)]
        exact m5 j hj hij
      · intro t ht
        rw [EvmBase.htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1, hdelEx_iff i t]
        exact m8 t ht
    · have hcg : ∀ g ∈ EvmBase.coreWorldGlobals, globN post g = globN s g := fun g _ => hglob_eq g
      rw [EvmBase.worldRoleSlots_eq hAs.2 hWT.1 hWT.2.2.1 hcell hcg,
          hframeRoleSlots_eq,
          EvmBase.journalRoleSlots_eq hAs.2 hWT.2.1 hWT.2.2.1 hcell hcg]
      unfold RolesOK at hRoles ⊢
      refine ⟨fun a ha => ?_, hRoles.2⟩
      obtain ⟨haS, hkl⟩ := hRoles.1 a ha
      have htb := ((hWT.1.2.1 a.1 haS).1.1 (a.1, 88) (by simp [htabFootprint])).1
      rw [EvmBase.htab_hdr_eq hcell haS htb 0 (by omega)]
      exact ⟨haS, hkl⟩
    · have hmap_gas : ((evmChain s).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)) =
          ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)) := by
        apply List.map_congr_left; intro ec hec
        rw [(hrec_eq ec hec).1 64 (by omega), (hrec_eq ec hec).1 192 (by omega)]
      rw [hmap_gas]
      exact hGas
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    unfold evmChain; exact List.mem_cons_self
  have h112 : memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112) :=
    (hrec_eq _ hhead).1 112 (by omega)
  have hMO_post : MsgOwned post S (memW post (globN post "ev" + 112)) := by
    rw [hglob_eq "ev", h112]
    exact msgOwned_congr hAs.2 hWT.1 hTr hcell hh hsc (hglob_eq "ws") hWT.2.2.1 hFT_post hfeq
      hWT_post.1 hchain_eq hframeObjects_eq ⟨hal_m, hw_m, hd_tab, hd_fix, hd_fo, Nd1, hTr1, hdj_nd1⟩
  have hw_code : ∀ g k, (g, k) ∈ ([("ws", 16), ("bs", 48), ("ts", 48)] : List (String × Nat)) →
      globN s g ≠ 0 → memW s (globN s g + k) ≠ 0 →
      ∀ p ∈ htabValues s (memW s (globN s g + k)), memW post (p + 8) = memW s (p + 8) := by
    intro g k hgk hgn hdb p hp
    have hbnd : p + 16 ≤ 2 ^ 64 := ((hCB g k hgk hgn hdb).2 p hp).2.1
    exact memW_eq_of_frameDisj heff hbnd (by omega) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact hMS g k hgk hgn hdb p hp)
  obtain ⟨hCB_post, hMS_post⟩ := msgBounded_side_of_sameTypedCells hAs hApost hWT hCB hMS hcell hh
    (fun g _ => hglob_eq g) h112 hfeq hw_code
  have hcc : ChainCellsAgree s post := fun ec hec =>
    ⟨(hrec_eq ec hec).1 24 (by omega), (hrec_eq ec hec).1 32 (by omega),
     (hrec_eq ec hec).1 40 (by omega), (hrec_eq ec hec).2.1 56 (by omega)⟩
  have hstep : EvmStep [] s post := ⟨⟨hApost, S, hInv_post⟩, hh, hG, hchain_eq⟩
  exact ⟨⟨hApost, hMS_post, S, hInv_post, hMO_post, hCB_post⟩, ⟨hstep, hcc⟩, h112⟩

end StepBounded

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
