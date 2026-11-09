import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.MsB4aStepBounded

/-!
# Scratch Rung B4b: Primitive Steps under `D0PreB` / `EvmMsgReadyMsgBounded`
-/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
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
open InitECandidate.Solver.Wave8GuestInv.EvmBase
open InitECandidate.Solver.Wave8GuestInv.EvmStepLemmas
open InitECandidate.Solver.Wave8GuestInv.EvmFrameSpecs
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8M19.Htab
open InitECandidate.Solver.Wave8GuestInv.HtabC00Ports
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge

section PrimSteps
open R10Shards.GbodyProcessMsg
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

/-! ## 1. Helper: `SameTypedCells` from a disjoint single-word store -/

theorem sameTypedCells_of_store_word_disj {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {x : BitVec 64}
    (hAs : ArenaReady s) (hdom : s.memaddrs x)
    (hpost : post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ post.shMemaddrs = s.shMemaddrs ∧
      post.baseAddr = s.baseAddr ∧ post.be = s.be ∧ post.globals = s.globals ∧
      ∀ a : BitVec 64, a ≠ x → post.memory a = s.memory a)
    (hWT : WorldTypedWith s S Nd)
    (hdisj : ∀ j ∈ worldTypedIvls s S Nd, Disj j (x.toNat, 8)) :
    EvmBase.SameTypedCells s post S Nd := by
  have hunhit : ∀ i ∈ worldTypedIvls s S Nd, R10Shards.GbodyProcessMsg.IvlUnhit s post i := fun i hi =>
    ivlUnhit_of_single_cell_disj hpost.2.2.2.2.2.2 (hdisj i hi)
  refine ⟨hpost.2.2.2.2.1, hpost.2.1, hAs.1.memaddrs, ?_, ?_, ?_⟩
  · intro a hna
    apply hpost.2.2.2.2.2.2
    rintro rfl
    rw [← hAs.1.memaddrs] at hna
    exact hna hdom
  · intro a ha ⟨i, hi, ha1, ha2⟩
    apply hpost.2.2.2.2.2.2
    intro heq
    have hd := hdisj i hi
    have hbit : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
    have hx_a : x.toNat = a := by rw [← heq, hbit]
    unfold Disj at hd
    dsimp only at hd
    omega
  · intro b hb ⟨i, hi, hb1, hb2⟩
    have hal : i.2 = 0 ∨ Allocated s i := worldTypedIvls_allocated hWT hi
    rcases hal with h0 | hal
    · omega
    · exact R10Shards.GbodyProcessMsg.memB_eq_of_ivlUnhit (hunhit i hi) hpost.2.2.2.2.1
        (allocated_le_2pow64 hAs.2 hal) ⟨hb1, hb2⟩

/-! ## 2. Message-field stores (`msg + off`, `off + 8 ≤ 176`) under `D0PreB` -/

theorem hoare_store_msg_word_stepB_with (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (cells : List (Nat × Nat × Nat × Nat))
    (off : Nat) (hoff : off + 8 ≤ 176) (value : ExpHOL 64)
    (L : HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (hword : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      D0PreB gw hp G ch cells s → L s.locals → ev s value = some v →
      ∃ w : BitVec 64, v = .val (.word w)) :
    Hoare (fun s => D0PreB gw hp G ch cells s ∧ L s.locals)
      (.store (.op .add [.var .local (ofString "msg"), .const (BitVec.ofNat 64 off)]) value)
      (Fall (fun s => D0PreB gw hp G ch cells s ∧ L s.locals)) := by
  apply Hoare.store_fall_of_none
  refine ⟨fun {F} s _ ⟨hD, hL⟩ _ hnone => ?_⟩
  obtain ⟨⟨hPB, hS⟩, m, hm, hm_eq⟩ := hD
  have hD : D0PreB gw hp G ch cells s := ⟨⟨hPB, hS⟩, m, hm, hm_eq⟩
  have hP := evmMsgReady_of_msgBounded hPB
  rcases hrun : evaluateHOLFiniteState s
      (.store (.op .add [.var .local (ofString "msg"), .const (BitVec.ofNat 64 off)]) value)
      with ⟨res, post⟩
  rw [hrun] at hnone
  dsimp only at hnone ⊢
  subst res
  have hm_bnd : m.toNat + 176 ≤ 2 ^ 64 := by
    rw [hm_eq]
    exact allocated_le_2pow64 hP.1.2 hP.2.choose_spec.2.1
  obtain ⟨heff, hloc⟩ := M11.ByteRegionEffect.of_store_word
    (Rl := [(m.toNat, 176)]) hP.1.1.memaddrs hrun
    (fun v hv => hword s v hD hL (by simpa only [ev] using hv))
    (fun addr hdst _ => by
      refine ⟨(m.toNat, 176), List.mem_singleton.2 rfl, ?_⟩
      have haddr : addr.toNat = m.toNat + off := by
        simp [evalHOLExact, evalListHOLExact, hm, valueIsWord, valueWord, wordOpHOL, wordOp] at hdst
        subst hdst
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (show off < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
      dsimp only
      omega)
  have heff' : EvmStepLemmas.ByteRegionEffect s post
      [(memW s (globN s "ev" + 112), 176)] := by
    rw [← hm_eq]
    exact m11Bre_to_evmBre (fun i hi => by
      simp only [List.mem_singleton] at hi; subst hi; simp) heff
  obtain ⟨hPB', hstep, h112⟩ := evmMsgReadyMsgBounded_of_msg_bre hPB heff'
  refine ⟨d0PreB_of_stepFromCC gw hp G ch cells hD hPB'
    (stepFromCC_of_evmStepCC (fun g hg => by simp at hg) hS hstep) hloc
    (congrArg (fun gs => gs.lookup (ofString "ev")) heff'.globals) h112, ?_⟩
  rw [hloc]; exact hL

theorem hoare_store_msg_word_stepB (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (cells : List (Nat × Nat × Nat × Nat))
    (off : Nat) (hoff : off + 8 ≤ 176) (value : ExpHOL 64)
    (hword : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      D0PreB gw hp G ch cells s → ev s value = some v → ∃ w : BitVec 64, v = .val (.word w)) :
    Hoare (D0PreB gw hp G ch cells)
      (.store (.op .add [.var .local (ofString "msg"), .const (BitVec.ofNat 64 off)]) value)
      (Fall (D0PreB gw hp G ch cells)) := by
  have h := hoare_store_msg_word_stepB_with gw hp G ch cells off hoff value (fun _ => True)
    (fun s v hD _ hv => hword s v hD hv)
  exact Hoare.mono (Hoare.weaken h (fun _ _ h hr => (h hr).1)) (fun _ hD => ⟨hD, trivial⟩)

theorem hoare_store_msg_local_stepB (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (cells : List (Nat × Nat × Nat × Nat))
    (off : Nat) (hoff : off + 8 ≤ 176) (name : MlS) (w : BitVec 64)
    (L : HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (hL : ∀ locals, L locals → locals.lookup name = some (.val (.word w))) :
    Hoare (fun s => D0PreB gw hp G ch cells s ∧ L s.locals)
      (.store (.op .add [.var .local (ofString "msg"), .const (BitVec.ofNat 64 off)]) (.var .local name))
      (Fall (fun s => D0PreB gw hp G ch cells s ∧ L s.locals)) := by
  apply hoare_store_msg_word_stepB_with gw hp G ch cells off hoff (.var .local name) L
  intro F s v _ hlocals hv
  simp only [ev, evalHOLExact, hL _ hlocals] at hv
  exact ⟨w, (Option.some.inj hv).symm⟩

/-! ## 3. Head-frame dispatch stores (`ev + off`, `off ∈ [48, 56, 80]`) -/

theorem evmMsgReadyMsgBounded_store_dispatch {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (hPB : EvmMsgReadyMsgBounded s)
    {x : BitVec 64} {k : Nat} (hk : k ∈ ([48, 56, 80] : List Nat))
    (hx : x.toNat = globN s "ev" + k) (hdom : s.memaddrs x)
    (hpost : post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ post.shMemaddrs = s.shMemaddrs ∧
      post.baseAddr = s.baseAddr ∧ post.be = s.be ∧ post.globals = s.globals ∧
      ∀ a : BitVec 64, a ≠ x → post.memory a = s.memory a) :
    EvmMsgReadyMsgBounded post ∧ EvmStepCC [] s post := by
  obtain ⟨hAs, hM, S, hI, hmsg, hC⟩ := hPB
  have hInv : EvmInv s := ⟨hAs, S, hI⟩
  have hwords := dispatch_store_chain_words hInv hk hx hpost.2.2.2.2.2.2
  have hg : ∀ name, globN post name = globN s name := fun name => by
    simp [globN, hpost.2.2.2.2.2.1]
  have hch := evmChain_eq_of_cont_words hg hwords.2.1
  have hlogs := dispatch_store_log_objects hInv hg hk hx hpost.2.2.2.2.2.2
  obtain ⟨Nd, ht, hd⟩ := hI.2.2.2.2.2.2.2.2.2.1
  have hklt : k + 8 ≤ 280 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl <;> decide
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    unfold evmChain; exact List.mem_cons_self
  have hheadflat : (globN s "ev", 280) ∈ ((evmChain s).map (frameObjects s)).flatten :=
    List.mem_flatten.2 ⟨frameObjects s (globN s "ev", globN s "cur_cont"),
      List.mem_map.2 ⟨_, hhead, rfl⟩, by simp [frameObjects]⟩
  obtain ⟨hAp, hWTp, hfix, hnd, hwr, hjr, hfp, hrefs⟩ :=
    dispatch_store_world_transport hAs hI ht hklt hx hdom hpost
      (fun j hj => hd _ hheadflat j hj)
  have htries := dispatch_store_all_tries hAs hI hklt hx hdom hpost
  have hfo : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec :=
    fun ec hec => (frameObjects_eq_of_dispatch_slots ec (hwords.1 ec hec)
      (hwords.2.2 ec hec) (hlogs ec hec)).1
  have hm : ∀ m, MsgOwned s S m → MsgOwned post S m := fun m hm =>
    msgOwned_transfer hAs.1 hAp.1 (hg "heap_ptr") (hg "scratch_ptr")
      (fun t ht => (hfp t ht).2) hfix hch hfo htries hm
  have hIpost : EvmInvAt post S := evmInvAt_of_dispatch_transport hI hAs hAp hg hch
    ⟨hWTp.1, hWTp.2.1, hWTp.2.2.1, Nd, hWTp.2.2.2⟩ hwords.1 hwords.2.1 hwords.2.2
    (fun ec hec => ⟨hlogs ec hec,
      dispatch_store_logs_ok hInv hAp hg hklt hx hpost.2.2.2.2.2.2 ec hec⟩)
    hm hfix (fun t ht => (hfp t ht).2) htries hwr hjr hrefs
    (fun t ht => by simpa [hdr] using (hfp t ht).1 0 (by decide))
  have hWTs : WorldTypedWith s S Nd := ⟨hI.1.1, hI.1.2.1, hI.1.2.2.1, ht⟩
  have hcell : EvmBase.SameTypedCells s post S Nd :=
    sameTypedCells_of_store_word_disj hAs hdom hpost hWTs
      (head_store_world_disj hI ht hklt hx (fun j hj => hd _ hheadflat j hj))
  have hheap := head_store_heap_words hInv hx hpost.2.2.2.2.2.2
  have h112 : memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112) :=
    hwords.1 _ hhead 112 (by decide) (by decide)
  obtain ⟨hCp, hMp⟩ := msgBounded_side_of_sameTypedCells hAs hAp hWTs hC hM hcell
    (by rw [hg "heap_ptr"]) (fun g _ => hg g) h112 hfix
    (fun g k hgk hgn hdb p hp => by
      have hin := ((hC g k hgk hgn hdb).2 p hp).1
      have hhl := hAs.2.2.1
      dsimp [Inside] at hin
      exact hheap (p + 8) (by omega))
  have hcc : ChainCellsAgree s post := fun ec hec =>
    ⟨hwords.1 ec hec 24 (by decide) (by decide),
     hwords.1 ec hec 32 (by decide) (by decide),
     hwords.1 ec hec 40 (by decide) (by decide),
     hwords.2.1 ec hec 56 (by decide)⟩
  refine ⟨⟨hAp, hMp, S, hIpost, ?_, hCp⟩,
    ⟨⟨hAp, S, hIpost⟩, by rw [hg "heap_ptr"], fun name _ => by rw [hpost.2.2.2.2.2.1], hch⟩, hcc⟩
  rw [hg "ev", h112]
  exact hm _ hmsg

theorem hoare_store_dispatch_word_stepB_with (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (cells : List (Nat × Nat × Nat × Nat))
    (off : Nat) (hoff : off ∈ ([48, 56, 80] : List Nat)) (value : ExpHOL 64)
    (L : HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (hword : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      D0PreB gw hp G ch cells s → L s.locals → ev s value = some v →
      ∃ w : BitVec 64, v = .val (.word w)) :
    Hoare (fun s => D0PreB gw hp G ch cells s ∧ L s.locals)
      (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]) value)
      (Fall (fun s => D0PreB gw hp G ch cells s ∧ L s.locals)) := by
  apply Hoare.store_fall_of_none
  refine ⟨fun {F} s _ ⟨hD, hL⟩ _ hnone => ?_⟩
  rcases hrun : evaluateHOLFiniteState s
      (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]) value)
      with ⟨res, post⟩
  rw [hrun] at hnone
  dsimp only at hnone ⊢
  subst res
  have hPB := hD.1.1
  have hInv := evmInv_of_msgBounded hPB
  obtain ⟨hb, _, ⟨ew, hew, hen⟩, _⟩ := R11Shards.evm_head_globals hInv
  have hofflt : off + 8 ≤ 280 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl | rfl <;> decide
  let x := BitVec.ofNat 64 (globN s "ev" + off)
  have hx : x.toNat = globN s "ev" + off := Nat.mod_eq_of_lt (by omega)
  have hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]) =
      some (.val (.word x)) := by
    simp only [evalHOLExact, evalListHOLExact, hew, wordOpHOL, wordOp, valueIsWord, valueWord,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr, BitVec.add_zero]
    congr 3
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hen,
      show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero,
      Nat.mod_eq_of_lt (show off < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show globN s "ev" + off < 2 ^ 64 by omega), hx]
  obtain ⟨w, hv, hpst⟩ := R11Shards.store_global_off_word hew hen (by omega)
    (fun v hv => hword s v hD hL hv) hrun
  have hdom : s.memaddrs x := by
    by_contra hn
    rw [evaluateHOLFiniteState_store, hdst, hv] at hrun
    simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hn] at hrun
  have hpost : post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ post.shMemaddrs = s.shMemaddrs ∧
      post.baseAddr = s.baseAddr ∧ post.be = s.be ∧ post.globals = s.globals ∧
      ∀ a : BitVec 64, a ≠ x → post.memory a = s.memory a := by
    rw [hpst]
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro a ha
    simp [R11Shards.updW, show a ≠ BitVec.ofNat 64 (globN s "ev" + off) from ha]
  obtain ⟨hPB', hstep⟩ := evmMsgReadyMsgBounded_store_dispatch hPB hoff hx hdom hpost
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    unfold evmChain; exact List.mem_cons_self
  have hslot := (dispatch_store_chain_words hInv hoff hx hpost.2.2.2.2.2.2).1
    _ hhead 112 (by decide) (by decide)
  have hloc : post.locals = s.locals := by rw [hpst]
  refine ⟨d0PreB_of_stepFromCC gw hp G ch cells hD hPB'
    (stepFromCC_of_evmStepCC (fun g hg => by simp at hg) hD.1.2 hstep) hloc
    (congrArg (fun gs => gs.lookup (ofString "ev")) hpost.2.2.2.2.2.1) hslot, ?_⟩
  rw [hloc]; exact hL

theorem hoare_store_dispatch_local_stepB (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (cells : List (Nat × Nat × Nat × Nat))
    (off : Nat) (hoff : off ∈ ([48, 56, 80] : List Nat)) (name : MlS) (w : BitVec 64)
    (L : HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (hL : ∀ locals, L locals → locals.lookup name = some (.val (.word w))) :
    Hoare (fun s => D0PreB gw hp G ch cells s ∧ L s.locals)
      (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]) (.var .local name))
      (Fall (fun s => D0PreB gw hp G ch cells s ∧ L s.locals)) := by
  apply hoare_store_dispatch_word_stepB_with gw hp G ch cells off hoff (.var .local name) L
  intro F s v _ hlocals hv
  simp only [ev, evalHOLExact, hL _ hlocals] at hv
  exact ⟨w, (Option.some.inj hv).symm⟩

/-! ## 4. Head-frame gas stores (`ev + 192`, `ev + 200`) -/

theorem evmMsgReadyMsgBounded_store_ev_gas {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hPB : EvmMsgReadyMsgBounded s) {x : BitVec 64} {k : Nat} (hk : k = 192 ∨ k = 200)
    (hx_eq : x.toNat = globN s "ev" + k) (hx_dom : s.memaddrs x)
    (hpost : post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ post.shMemaddrs = s.shMemaddrs ∧
      post.baseAddr = s.baseAddr ∧ post.be = s.be ∧ post.globals = s.globals ∧
      ∀ a : BitVec 64, a ≠ x → post.memory a = s.memory a)
    (hgas : memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) ≤
      memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192)) :
    EvmMsgReadyMsgBounded post ∧ EvmStepCC [] s post ∧
      memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112) := by
  obtain ⟨hAs, hM, S, hInvAt, hMO, hC⟩ := hPB
  have hInv : EvmInv s := ⟨hAs, S, hInvAt⟩
  obtain ⟨hAp, hInvAt', hch, hmo, hhead⟩ :=
    evmInvAt_store_ev_gas hAs hInvAt hk hx_eq hx_dom hpost hgas
  have hg : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, hpost.2.2.2.2.2.1]
  have hklt : k + 8 ≤ 280 := by rcases hk with rfl | rfl <;> decide
  obtain ⟨Nd, ht, hd⟩ := hInvAt.2.2.2.2.2.2.2.2.2.1
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    unfold evmChain; exact List.mem_cons_self
  have hheadflat : (globN s "ev", 280) ∈ ((evmChain s).map (frameObjects s)).flatten :=
    List.mem_flatten.2 ⟨frameObjects s (globN s "ev", globN s "cur_cont"),
      List.mem_map.2 ⟨_, hhead_mem, rfl⟩, by simp [frameObjects]⟩
  have hWTs : WorldTypedWith s S Nd := ⟨hInvAt.1.1, hInvAt.1.2.1, hInvAt.1.2.2.1, ht⟩
  obtain ⟨_, _, hfix, _, _, _, _, _⟩ :=
    dispatch_store_world_transport hAs hInvAt ht hklt hx_eq hx_dom hpost
      (fun j hj => hd _ hheadflat j hj)
  have hcell : EvmBase.SameTypedCells s post S Nd :=
    sameTypedCells_of_store_word_disj hAs hx_dom hpost hWTs
      (head_store_world_disj hInvAt ht hklt hx_eq (fun j hj => hd _ hheadflat j hj))
  have hheap := head_store_heap_words hInv hx_eq hpost.2.2.2.2.2.2
  have h112 : memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112) :=
    hhead 112 (by omega) (by omega) (by omega)
  obtain ⟨hCp, hMp⟩ := msgBounded_side_of_sameTypedCells hAs hAp hWTs hC hM hcell
    (by rw [hg "heap_ptr"]) (fun g _ => hg g) h112 hfix
    (fun g k' hgk hgn hdb p hp => by
      have hin := ((hC g k' hgk hgn hdb).2 p hp).1
      have hhl := hAs.2.2.1
      dsimp [Inside] at hin
      exact hheap (p + 8) (by omega))
  have hpoint : ∀ a, a < 2 ^ 64 → a ≠ globN s "ev" + k → memW post a = memW s a := by
    intro a ha hne
    unfold memW
    rw [hpost.2.2.2.2.2.2 (BitVec.ofNat 64 a) ?_]
    intro heq
    have he := congrArg BitVec.toNat heq
    rw [hx_eq, show (BitVec.ofNat 64 a).toNat = a from Nat.mod_eq_of_lt ha] at he
    exact hne he
  have hpw := hInvAt.2.2.2.2.2.2.2.1
  have hfw := hInvAt.2.2.2.2.1
  have hcons : ∃ tl, evmChain s = (globN s "ev", globN s "cur_cont") :: tl := ⟨_, rfl⟩
  obtain ⟨tl, htl⟩ := hcons
  rw [htl, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
  have hhead_disj_cont : Disj (globN s "ev", 280) (globN s "cur_cont", 104) := by
    have h := hpw.1
    unfold frameObjects at h
    simp only [List.cons_append, List.pairwise_cons] at h
    exact h.1 _ (by simp)
  have htail : ∀ ec ∈ tl, ∀ o ∈ frameObjects s ec, Disj (globN s "ev", 280) o :=
    fun ec hec o ho => hpw.2.2 _ (by simp [frameObjects]) o
      (List.mem_flatten.2 ⟨frameObjects s ec, List.mem_map.2 ⟨ec, hec, rfl⟩, ho⟩)
  have hcc : ChainCellsAgree s post := by
    intro ec hec
    obtain ⟨hb1, hb2, _⟩ := frameWF_bounds (hfw ec hec)
    have he1 : ∀ j ∈ ([24, 32, 40] : List Nat), memW post (ec.1 + j) = memW s (ec.1 + j) := by
      intro j hj
      have hjlt : j + 8 ≤ 280 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl <;> decide
      have hjne : j ≠ k := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl <;> rcases hk with rfl | rfl <;> decide
      apply hpoint (ec.1 + j) (by omega)
      rw [htl, List.mem_cons] at hec
      rcases hec with rfl | hec_tl
      · dsimp only; omega
      · have hd_ec := htail ec hec_tl (ec.1, 280) (by simp [frameObjects])
        rcases hd_ec with h | h | h | h <;> dsimp only at h <;> omega
    have he2 : memW post (ec.2 + 56) = memW s (ec.2 + 56) := by
      apply hpoint (ec.2 + 56) (by omega)
      have hd_c : Disj (globN s "ev", 280) (ec.2, 104) := by
        rw [htl, List.mem_cons] at hec
        rcases hec with rfl | hec_tl
        · exact hhead_disj_cont
        · exact htail ec hec_tl (ec.2, 104) (by simp [frameObjects])
      rcases hd_c with h | h | h | h <;> dsimp only at h <;> omega
    exact ⟨he1 24 (by decide), he1 32 (by decide), he1 40 (by decide), he2⟩
  refine ⟨⟨hAp, hMp, S, hInvAt', ?_, hCp⟩,
    ⟨⟨⟨hAp, S, hInvAt'⟩, by rw [hg "heap_ptr"], fun g _ => by rw [hpost.2.2.2.2.2.1], hch⟩, hcc⟩, h112⟩
  rw [hg "ev", h112]
  exact hmo _ hMO

theorem store_ev_gas_runB {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hPB : EvmMsgReadyMsgBounded s) {k : Nat} (hk : k = 192 ∨ k = 200) {src : ExpHOL 64} {w : BitVec 64}
    (hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) src =
      some (.val (.word w)))
    (hgas : k = 200 ∨ w.toNat ≤ memW s (globN s "ev" + 192))
    {post : PanSemStateFiniteExact 64 F}
    (hev : evaluateHOLFiniteState s
      (.store (.op .add [.var .global (ofString "ev"), .const k]) src) = (none, post)) :
    EvmMsgReadyMsgBounded post ∧ EvmStepCC [] s post ∧ post.locals = s.locals ∧
      post.globals = s.globals ∧ memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112) := by
  have hInv := evmInv_of_msgBounded hPB
  have hrun := evaluateHOLFiniteState_store s
    (.op .add [.var .global (ofString "ev"), .const k]) src
  rw [hev] at hrun
  revert hrun
  rcases hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .global (ofString "ev"), .const k]) with _ | dv
  · simp
  · rcases dv with ⟨⟨addr⟩⟩ | _ | _
    · rw [hsrc]
      dsimp only
      split
      · rename_i m' hst
        unfold flattenHOL panMemStoresHOL panMemStoreHOL at hst
        by_cases hdom : s.memaddrs addr
        · simp only [hdom, ↓reduceIte, panMemStoresHOL, Option.some.injEq] at hst
          subst hst
          intro hpair
          injection hpair with _ hpost_eq
          subst hpost_eq
          have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
            unfold evmChain; exact List.mem_cons_self
          obtain ⟨_, S, _, _, _, _, hFW_all, _⟩ := hInv
          have hb_e := (R10Shards.GbodyProcessMsg.frameWF_bounds (hFW_all _ hhead_mem)).1
          dsimp only at hb_e
          have hk_lt : k < 280 := by rcases hk with rfl | rfl <;> omega
          have haddr_nat : addr.toNat = globN s "ev" + k := by
            simp [evalHOLExact, evalListHOLExact] at hdst
            rcases hg : s.globals.lookup (ofString "ev") with _ | gv
            · simp [hg] at hdst
            · rcases gv with ⟨⟨gw⟩⟩ | _ | _
              · simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp] at hdst
                subst hdst
                have hglob : globN s "ev" = gw.toNat := by simp [globN, hg]
                rw [hglob] at hb_e ⊢
                have hkk : (BitVec.ofNat 64 k).toNat = k := Nat.mod_eq_of_lt (by omega)
                rw [BitVec.toNat_add, hkk, Nat.mod_eq_of_lt (by omega)]
              · simp [hg, valueIsWord] at hdst
              · simp [hg, valueIsWord] at hdst
          set post : PanSemStateFiniteExact 64 F :=
            { s with memory := fun current => if current = addr then .word w else s.memory current } with hpost_def
          have hpost : post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ post.shMemaddrs = s.shMemaddrs ∧
              post.baseAddr = s.baseAddr ∧ post.be = s.be ∧ post.globals = s.globals ∧
              ∀ a : BitVec 64, a ≠ addr → post.memory a = s.memory a :=
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun a hne => by simp [post, hne]⟩
          have hne_of : ∀ j, j < 280 → j ≠ k → BitVec.ofNat 64 (globN s "ev" + j) ≠ addr := by
            intro j hj hjne heq
            have h1 : (BitVec.ofNat 64 (globN s "ev" + j)).toNat = globN s "ev" + j :=
              Nat.mod_eq_of_lt (by omega)
            rw [heq, haddr_nat] at h1
            omega
          have hwj : ∀ j, j < 280 → j ≠ k → memW post (globN s "ev" + j) = memW s (globN s "ev" + j) := by
            intro j hj hjne
            unfold memW; simp [post, hne_of j hj hjne]
          have hwk : memW post (globN s "ev" + k) = w.toNat := by
            unfold memW
            have heq : BitVec.ofNat 64 (globN s "ev" + k) = addr := by
              apply BitVec.eq_of_toNat_eq
              rw [haddr_nat]
              exact Nat.mod_eq_of_lt (by omega)
            simp [post, heq]
          have hgas' : memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) ≤
              memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192) := by
            rw [hwj 64 (by omega) (by omega)]
            rcases hk with rfl | rfl
            · rw [hwk]; rcases hgas with h | h <;> omega
            · rw [hwj 192 (by omega) (by omega)]
          obtain ⟨hPB', hstep, h112⟩ := evmMsgReadyMsgBounded_store_ev_gas hPB hk haddr_nat hdom hpost hgas'
          exact ⟨hPB', hstep, rfl, rfl, h112⟩
        · simp [hdom] at hst
      · simp
    · simp
    · simp

theorem hoare_store_ev_192_zero_stepB (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (cells : List (Nat × Nat × Nat × Nat)) :
    Hoare (fun s => EvmMsgReadyMsgBounded s ∧ StepFromCC gw hp G ch cells s)
      (.store (.op .add [.var .global (ofString "ev"), .const 192]) (.const 0))
      (fun r t => r = none → EvmMsgReadyMsgBounded t ∧ StepFromCC gw hp G ch cells t) := by
  refine ⟨fun {F} s _ ⟨hP, hS⟩ _ hr => ?_⟩
  rcases hev : evaluateHOLFiniteState s
    (.store (.op .add [.var .global (ofString "ev"), .const 192]) (.const 0)) with ⟨res, post⟩
  rw [hev] at hr
  dsimp only at hr ⊢
  subst hr
  obtain ⟨hP', hstep, _, _, _⟩ := store_ev_gas_runB s hP (Or.inl rfl) (src := .const 0) (w := 0)
    (by simp [evalHOLExact]) (Or.inr (by simp)) hev
  exact ⟨hP', stepFromCC_of_evmStepCC (fun _ h => by cases h) hS hstep⟩

theorem hoare_store_ev_200_used_stepB (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (cells : List (Nat × Nat × Nat × Nat)) :
    Hoare (fun s => D0PreB gw hp G ch cells s ∧
        ∃ w : BitVec 64, s.locals.lookup (ofString "used") = some (.val (.word w)))
      (.store (.op .add [.var .global (ofString "ev"), .const 200]) (.var .local (ofString "used")))
      (fun r t => r = none → D0PreB gw hp G ch cells t) := by
  refine ⟨fun {F} s _ ⟨hD, w_used, hused⟩ _ hr => ?_⟩
  rcases hev : evaluateHOLFiniteState s
    (.store (.op .add [.var .global (ofString "ev"), .const 200]) (.var .local (ofString "used"))) with ⟨res, post⟩
  rw [hev] at hr
  dsimp only at hr ⊢
  subst hr
  obtain ⟨hP', hstep, hloc, hglob, h112⟩ := store_ev_gas_runB s hD.1.1 (Or.inr rfl)
    (src := .var .local (ofString "used")) (w := w_used) (by simp [evalHOLExact, hused]) (Or.inl rfl) hev
  exact d0PreB_of_stepFromCC gw hp G ch cells hD hP'
    (stepFromCC_of_evmStepCC (fun _ h => by cases h) hD.1.2 hstep) hloc
    (congrArg (fun gs => gs.lookup (ofString "ev")) hglob) h112

/-! ## 5. Fresh-scratch `compute_jumpdests` under `D0PreB` / `EvmMsgReadyMsgBounded` -/

theorem evmMsgReadyMsgBounded_fresh_scratch {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (hPB : EvmMsgReadyMsgBounded s)
    (hAp : ArenaReady post)
    (q n : Nat) (hlo : globN s "frame_mem_ptr" ≤ q)
    (hhi : q + n ≤ globN s "scratch_ptr")
    (hmem : ∀ a : BitVec 64, ¬ CellHits a.toNat (q, n) → post.memory a = s.memory a)
    (hbe : post.be = s.be) (hdom : post.memaddrs = s.memaddrs)
    (hout : ∀ a : BitVec 64, ¬ ordinaryDomain a → post.memory a = s.memory a)
    (hglob : ∀ name : MlS, name ∉ (["scratch_ptr"] : List String).map ofString →
      post.globals.lookup name = s.globals.lookup name)
    (hsp : globN post "scratch_ptr" ≤ globN s "scratch_ptr") :
    EvmMsgReadyMsgBounded post ∧ EvmStepCC ["scratch_ptr"] s post := by
  have hgl : ∀ name, ofString name ≠ ofString "scratch_ptr" →
      s.globals.lookup (ofString name) = post.globals.lookup (ofString name) := by
    intro name hn
    exact (hglob (ofString name) (by simpa using hn)).symm
  have hg : ∀ name, ofString name ≠ ofString "scratch_ptr" → globN post name = globN s name := by
    intro name hn
    exact (globN_eq_of_lookup_eq (hgl name hn)).symm
  obtain ⟨hAs, hM, S, hI, hm, hC⟩ := hPB
  have hInv : EvmInv s := ⟨hAs, S, hI⟩
  have hwords := fresh_scratch_chain_words hInv q n hhi hmem
  have hch := fresh_scratch_chain_eq hInv q n hhi hmem (hg _ (by decide)) (hg _ (by decide))
  have hi := evmInvAt_of_fresh_scratch hAs hAp hI q n hlo hhi hmem hbe hdom hout hg hgl hsp
  obtain ⟨Nd, ht⟩ := hI.1.2.2.2
  have hWT : WorldTypedWith s S Nd := ⟨hI.1.1, hI.1.2.1, hI.1.2.2.1, ht⟩
  have hm' := fresh_scratch_msgOwned hAs hAp hI hWT q n hlo hhi hmem hbe hdom hout hg hgl hsp _ hm
  have hcell := fresh_scratch_sameTypedCells hAs hWT q n hlo hhi hmem hbe hdom hout
  obtain ⟨_, hfix, _, _, _, _⟩ :=
    fresh_scratch_world_transport hAs hAp hWT q n hlo hhi hmem hbe hdom hout hg hgl hsp
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    unfold evmChain; exact List.mem_cons_self
  have h112 := hwords.1 _ hhead 112 (by decide)
  obtain ⟨hCp, hMp⟩ := msgBounded_side_of_sameTypedCells hAs hAp hWT hC hM hcell
    (by rw [hg "heap_ptr" (by decide)])
    (fun g hg_mem => hg g (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg_mem
      rcases hg_mem with rfl | rfl | rfl | rfl <;> decide))
    h112 hfix
    (fun g k hgk hgn hdb p hp => by
      have hin := ((hC g k hgk hgn hdb).2 p hp).1
      have hhl := hAs.2.2.1
      have hsep : heapLimit ≤ scratchStart := by decide
      have hfm := hAs.2.2.2.1
      have hlim : heapLimit ≤ 2 ^ 64 := by decide
      dsimp [Inside] at hin
      unfold memW
      rw [hmem (BitVec.ofNat 64 (p + 8)) ?_]
      rw [show (BitVec.ofNat 64 (p + 8)).toNat = p + 8 from Nat.mod_eq_of_lt (by omega)]
      unfold CellHits; dsimp only; omega)
  have hcc : ChainCellsAgree s post := fun ec hec =>
    ⟨hwords.1 ec hec 24 (by decide),
     hwords.1 ec hec 32 (by decide),
     hwords.1 ec hec 40 (by decide),
     hwords.2.1 ec hec 56 (by decide)⟩
  refine ⟨⟨hAp, hMp, S, hi, ?_, hCp⟩,
    ⟨⟨hAp, S, hi⟩, by rw [hg "heap_ptr" (by decide)], fun name hn => (hglob name hn).symm, hch⟩, hcc⟩
  rw [hg "ev" (by decide), h112]
  exact hm'

theorem compute_jumpdests_evm_runB {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hPB : EvmMsgReadyMsgBounded s) (nw p f : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hp : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word p)))
    (hf : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word f)))
    (hnb : nw.toNat < 2 ^ 40) :
    InitECandidate.Solver.Wave8M19.Htab.Ret s
      (sourceFnBody Guest.Software.guestFn_compute_jumpdests) (fun v post =>
      ∃ q : BitVec 64, v = .val (.word q) ∧
        EvmMsgReadyMsgBounded post ∧ EvmStepCC ["scratch_ptr"] s post) := by
  have hAs := hPB.1
  have hpn : globN s "scratch_ptr" = p.toNat := by simp [globN, hp]
  have hfn : globN s "frame_mem_ptr" = f.toNat := by simp [globN, hf]
  have hfp : f.toNat ≤ p.toNat := by rw [← hpn, ← hfn]; exact hAs.2.2.2.2.1
  intro v hv
  obtain ⟨q, hval, hq, _, hlo, hhi, hg, _, hd, hm⟩ :=
    compute_jumpdests_run s hAs.1.code hAs.1 nw p f hn hp hf hfp hnb v hv
  let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_compute_jumpdests)).2
  have hlow : globN s "frame_mem_ptr" ≤ q.toNat := by rw [hfn]; omega
  have hhigh : q.toNat + (jdLen nw).toNat ≤ globN s "scratch_ptr" := by rwa [hpn]
  have hq8 : q.toNat % 8 = 0 := by rw [hq, and_neg8_toNat]; omega
  have hApost : ArenaReady post := hb_arenaReady_update_scratch_ptr
    (guestInv_evaluate s _ hAs.1) hAs.2 hg hlow
    (by have := hAs.2.2.2.2.2.1; omega) hq8
  have hsp : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by
    have he : globN post "scratch_ptr" = q.toNat := by
      unfold globN; rw [hg]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    omega
  have hglob : ∀ name : MlS, name ∉ (["scratch_ptr"] : List String).map ofString →
      post.globals.lookup name = s.globals.lookup name := by
    intro name hn'
    rw [hg]
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hn'
    simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hn']
  have hout : ∀ a : BitVec 64, ¬ ordinaryDomain a → post.memory a = s.memory a := by
    intro a ha
    apply scratch_evaluate_mem_out_dom
    rwa [hAs.1.memaddrs]
  obtain ⟨hr, hs⟩ := evmMsgReadyMsgBounded_fresh_scratch hPB hApost q.toNat (jdLen nw).toNat
    hlow hhigh hm (InitECandidate.Solver.Wave8GuestInv.R16Shards.evaluate_be_eq s _) hd hout hglob hsp
  exact ⟨q, hval, hr, hs⟩

theorem compute_jumpdests_resumeB (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (cells : List (Nat × Nat × Nat × Nat))
    (code code_n : BitVec 64) (hnb : code_n.toNat < 2 ^ 40) (hsub : "scratch_ptr" ∈ gw) :
    DecCallResumeOn
      (fun s => D0PreB gw hp G ch cells s ∧
        s.locals.lookup (ofString "code") = some (.val (.word code)) ∧
        s.locals.lookup (ofString "code_n") = some (.val (.word code_n)))
      (fun s => D0PreB gw hp G ch cells s ∧ ∃ jd : BitVec 64,
        s.locals.lookup (ofString "jd") = some (.val (.word jd)))
      (ofString "jd") (ofString "compute_jumpdests")
      [.var .local (ofString "code"), .var .local (ofString "code_n")] := by
  intro F s values body callee ret v post hc hD hargs hl hb
  have hvals : values = [.val (.word code), .val (.word code_n)] := by
    simpa [evalListHOLFinite, evalListHOLExact, evalHOLExact, hD.2.1, hD.2.2] using hargs.symm
  subst values
  have hlookup := lookup_compute_jumpdests
  rw [hc] at hl
  have hparams : body = sourceFnBody Guest.Software.guestFn_compute_jumpdests ∧
      callee.lookup (ofString "n") = some (.val (.word code_n)) := by
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
    split at hl
    · cases hl
    · rename_i b l rs raw
      cases hl
      unfold lookupCodeHOLExact at raw
      rw [hlookup] at raw
      simp [shapeOfHOLExact, shapeEqHOL] at raw
      exact ⟨raw.2.1.symm, by dsimp only; rw [← raw.2.2.1]; simp⟩
  rcases hparams with ⟨rfl, hncal⟩
  have hentry : EvmMsgReadyMsgBounded (callEntryStateHOLFinite s callee) :=
    localsFree_evmMsgReadyMsgBounded s _ _ hD.1.1.1
  have hn : (callEntryStateHOLFinite s callee).locals.lookup (ofString "n") =
      some (.val (.word code_n)) := hncal
  obtain ⟨p, hpw⟩ := hentry.1.2.2.2.2.2.2.2.2.2 "scratch_ptr" (by decide)
  obtain ⟨f, hfw⟩ := hentry.1.2.2.2.2.2.2.2.2.2 "frame_mem_ptr" (by decide)
  have hrun := compute_jumpdests_evm_runB (callEntryStateHOLFinite s callee) hentry code_n p f hn hpw hfw hnb v (by rw [hb])
  rw [hb] at hrun
  obtain ⟨jd, rfl, hready, hstep⟩ := hrun
  have hs0 : StepFromCC gw hp G ch cells (callEntryStateHOLFinite s callee) :=
    localsFree_stepFromCC gw hp G ch cells s _ _ hD.1.1.2
  have hs := stepFromCC_of_evmStepCC (fun g hg => by simpa using (List.mem_singleton.1 hg ▸ hsub)) hs0 hstep
  have hpn : globN s "scratch_ptr" = p.toNat := by
    simp [GlobalWord, callEntryStateHOLFinite] at hpw
    simp [globN, hpw]
  have hfn : globN s "frame_mem_ptr" = f.toNat := by
    simp [GlobalWord, callEntryStateHOLFinite] at hfw
    simp [globN, hfw]
  have hfp : f.toNat ≤ p.toNat := by rw [← hpn, ← hfn]; exact hD.1.1.1.1.2.2.2.2.1
  obtain ⟨q, _, _, _, _, hhi, hg, _, _, hm⟩ := compute_jumpdests_run
    (callEntryStateHOLFinite s callee) hentry.1.1.code hentry.1.1 code_n p f hn hpw hfw hfp hnb
    (.val (.word jd)) (by rw [hb])
  rw [hb] at hg hm
  have hmem : ∀ a : BitVec 64, ¬ CellHits a.toNat (q.toNat, (jdLen code_n).toNat) → post.memory a = s.memory a := hm
  have hhigh : q.toNat + (jdLen code_n).toNat ≤ globN s "scratch_ptr" := by rw [hpn]; exact hhi
  have hw := (fresh_scratch_chain_words (evmInv_of_msgBounded hD.1.1.1) _ _ hhigh hmem).1
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    unfold evmChain; exact List.mem_cons_self
  have hev : globN post "ev" = globN s "ev" := by
    unfold globN
    rw [hg]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, callEntryStateHOLFinite,
      show ofString "scratch_ptr" ≠ ofString "ev" by decide]
  obtain ⟨_, m, hm0, hmeq⟩ := hD.1
  refine ⟨⟨⟨localsFree_evmMsgReadyMsgBounded post _ _ hready,
            localsFree_stepFromCC gw hp G ch cells post _ _ hs⟩,
    m, ?_, ?_⟩, jd, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
  · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "jd" ≠ ofString "msg" by decide] using hm0
  · change m.toNat = memW post (globN post "ev" + 112)
    rw [hev, hw _ hhead 112 (by decide)]
    exact hmeq

/-! ## 6. Fresh-heap `alloc` and `alloc` + `memcpy` under `D0PreB` -/

theorem evmMsgReadyMsgBounded_of_fresh_heap_step {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hPB : EvmMsgReadyMsgBounded s) (hAp : ArenaReady post) (hbe : post.be = s.be)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hg_kept : GlobalsKept ["heap_ptr"] s post)
    (hout_dom : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN post "heap_ptr") → memB post b = memB s b) :
    EvmMsgReadyMsgBounded post ∧ EvmStepCC ["heap_ptr"] s post ∧
      memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112) := by
  obtain ⟨hAs, hM, S, hI, hmsg, hC⟩ := hPB
  obtain ⟨hIp, hch, _⟩ := OpHandlersB.evmInvAt_of_fresh_heap_step hAs hI hAp hbe hhp hg_kept hout_dom hbyte
  obtain ⟨Nd_at, hTr_at, _⟩ := hI.2.2.2.2.2.2.2.2.2.1
  have hWT : WorldTypedWith s S Nd_at := ⟨hI.1.1, hI.1.2.1, hI.1.2.2.1, hTr_at⟩
  have hdom_eq : post.memaddrs = s.memaddrs := hAp.1.memaddrs.trans hAs.1.memaddrs.symm
  have hglob_nonHeap : ∀ nm : String, ofString nm ≠ ofString "heap_ptr" → globN post nm = globN s nm := by
    intro nm hne
    exact (globN_eq_of_lookup_eq (hg_kept (ofString nm) (by simp [hne]))).symm
  have hmem_byte_eq : ∀ {a : BitVec 64}, ordinaryDomain a →
      (∀ k : Nat, k < 8 → memB post (a.toNat + k) = memB s (a.toNat + k)) →
      post.memory a = s.memory a := by
    intro a ha_dom hb
    have hdom' := (InitECandidate.Solver.Wave8Contracts.M23.ordinaryDomain_iff a).mp ha_dom
    have ha_ord : a.toNat % 8 = 0 ∧ sourceBase ≤ a.toNat ∧ a.toNat < heapEnd := by
      rw [R11Shards.sourceBase_val, R11Shards.heapEnd_val]; omega
    have hhe_lt : heapEnd ≤ 2 ^ 64 := by rw [R11Shards.heapEnd_val]; decide
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
  have hmemW_out : ∀ {base sz k : Nat},
      base + sz ≤ 2 ^ 64 → base % 8 = 0 → k % 8 = 0 → k + 8 ≤ sz →
      (sz = 0 ∨ globN post "heap_ptr" ≤ base ∨ base + sz ≤ globN s "heap_ptr") →
      memW post (base + k) = memW s (base + k) := by
    intro base sz k hbnd _ _ hk hdj
    have ha : base + k < 2 ^ 64 := by omega
    have hbit : (BitVec.ofNat 64 (base + k)).toNat = base + k := Nat.mod_eq_of_lt ha
    unfold memW
    by_cases hdom : ordinaryDomain (BitVec.ofNat 64 (base + k))
    · rw [hmem_byte_eq hdom]
      intro idx hidx
      rw [hbit]
      apply hbyte (base + k + idx) (by omega)
      intro ⟨h1, h2⟩
      rcases hdj with h0 | h | h <;> omega
    · rw [hout_dom _ (by rwa [hAs.1.memaddrs])]
  have hcell : EvmBase.SameTypedCells s post S Nd_at := by
    have hwti_disj : ∀ i ∈ worldTypedIvls s S Nd_at,
        i.2 = 0 ∨ globN post "heap_ptr" ≤ i.1 ∨ i.1 + i.2 ≤ globN s "heap_ptr" := by
      intro i hi
      rcases worldTypedIvls_allocated hWT hi with h0 | hal
      · exact Or.inl h0
      · rcases hal with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact Or.inr (Or.inr h2)
        · have hp_lim := hAp.2.2.1
          have hs_fr := hAs.2.2.2.1
          have hs_gap := hAs.2.2.2.2.1
          have hsep : heapLimit ≤ scratchStart := by decide
          exact Or.inr (Or.inl (by omega))
    refine ⟨hbe, hdom_eq, hAs.1.memaddrs, ?_, ?_, ?_⟩
    · intro a hna
      apply hout_dom a
      rwa [hAs.1.memaddrs]
    · intro a ha ⟨i, hi, ha1, ha2⟩
      by_cases hdom : ordinaryDomain (BitVec.ofNat 64 a)
      · have hbit : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
        have hdom' := (InitECandidate.Solver.Wave8Contracts.M23.ordinaryDomain_iff (BitVec.ofNat 64 a)).mp hdom
        have ha_ord : a % 8 = 0 ∧ sourceBase ≤ a ∧ a < heapEnd := by
          rw [R11Shards.sourceBase_val, R11Shards.heapEnd_val]; omega
        have hhe_lt : heapEnd ≤ 2 ^ 64 := by rw [R11Shards.heapEnd_val]; decide
        have hhp_s8 : globN s "heap_ptr" % 8 = 0 := hAs.2.2.2.2.2.2.1
        have hhp_p8 : globN post "heap_ptr" % 8 = 0 := hAp.2.2.2.2.2.2.1
        apply hmem_byte_eq hdom
        intro k hk
        rw [hbit]
        apply hbyte (a + k) (by omega)
        intro ⟨hb1, hb2⟩
        rcases hwti_disj i hi with h0 | h | h <;> omega
      · apply hout_dom _ (by rwa [hAs.1.memaddrs])
    · intro b hb ⟨i, hi, hb1, hb2⟩
      apply hbyte b hb
      intro ⟨h1, h2⟩
      rcases hwti_disj i hi with h0 | h | h <;> omega
  have hfeq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [EvmBase.blockOutObjects_eq hAs.2 hWT.2.2.1 hcell (hglob_nonHeap "bo" (by decide)),
        EvmBase.balObjects_eq hAs.2 hWT.1 hWT.2.2.1 hcell (hglob_nonHeap "bal_accounts" (by decide)),
        hglob_nonHeap "journal" (by decide),
        hglob_nonHeap "journal_cap" (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne : ofString gn.1 ≠ ofString "heap_ptr" := by revert gn hgn; decide
    rw [hglob_nonHeap gn.1 hne]
  have hsep : heapLimit ≤ scratchStart := by decide
  have hrec_eq : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → k % 8 = 0 → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → k % 8 = 0 → memW post (ec.2 + k) = memW s (ec.2 + k)) ∧
      (∀ k, k + 8 ≤ 24 → k % 8 = 0 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) := by
    intro ec hec
    have hFW := hI.2.2.2.2.1 ec hec
    obtain ⟨hb1, hb2, hb88, _⟩ := EvmStepLemmas.frameWF_bounds hAs.2 hFW
    have he1_in := (hFW.1 (ec.1, 280) (by simp)).1.1
    have he2_in := (hFW.1 (ec.2, 104) (by simp)).1.1
    have he88_in := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1.1
    have he1_8 : ec.1 % 8 = 0 := (hFW.1 (ec.1, 280) (by simp)).2.1
    have he2_8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
    have he88_8 : (memW s (ec.1 + 88)) % 8 = 0 := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).2.1
    have hfm_ge := hAs.2.2.2.1
    have hsp_ge := hAs.2.2.2.2.1
    have hhp_lim := hAp.2.2.1
    dsimp only at he1_in he2_in he88_in
    refine ⟨fun k hk hk8 => hmemW_out hb1 he1_8 hk8 hk (Or.inr (Or.inl (by omega))),
            fun k hk hk8 => hmemW_out hb2 he2_8 hk8 hk (Or.inr (Or.inl (by omega))),
            fun k hk hk8 => hmemW_out hb88 he88_8 hk8 hk (Or.inr (Or.inl (by omega)))⟩
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    unfold evmChain; exact List.mem_cons_self
  have h112 : memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112) :=
    (hrec_eq _ hhead).1 112 (by decide) (by decide)
  obtain ⟨hCp, hMp⟩ := msgBounded_side_of_sameTypedCells hAs hAp hWT hC hM hcell hhp
    (fun g hg_mem => hglob_nonHeap g (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg_mem
      rcases hg_mem with rfl | rfl | rfl | rfl <;> decide))
    h112 hfeq
    (fun g k hgk hgn hdb p hp => by
      have hin := ((hC g k hgk hgn hdb).2 p hp).1
      have hp_bnd := ((hC g k hgk hgn hdb).2 p hp).2.1
      have hp8 : p % 8 = 0 := ((hC g k hgk hgn hdb).1 p hp).1.1
      dsimp [Inside] at hin
      exact hmemW_out hp_bnd hp8 (by decide) (by decide) (Or.inr (Or.inr hin.2)))
  have hm_post : MsgOwned post S (memW post (globN post "ev" + 112)) :=
    (hIp.2.2.2.2.1 (globN post "ev", globN post "cur_cont")
      (by unfold evmChain; exact List.mem_cons_self)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hcc : ChainCellsAgree s post := fun ec hec =>
    ⟨(hrec_eq ec hec).1 24 (by decide) (by decide),
     (hrec_eq ec hec).1 32 (by decide) (by decide),
     (hrec_eq ec hec).1 40 (by decide) (by decide),
     (hrec_eq ec hec).2.1 56 (by decide) (by decide)⟩
  exact ⟨⟨hAp, hMp, S, hIp, hm_post, hCp⟩, ⟨⟨⟨hAp, S, hIp⟩, hhp, hg_kept, hch⟩, hcc⟩, h112⟩

theorem dispatch_alloc_runB {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (h : EvmMsgReadyMsgBounded s)
    (p n : BitVec 64)
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n))) :
    Ret s (sourceFnBody Guest.Software.guestFn_alloc) (fun v post =>
      v = .val (.word p) ∧ EvmMsgReadyMsgBounded post ∧ EvmStepCC ["heap_ptr"] s post ∧
      p.toNat + n.toNat ≤ globN post "heap_ptr" ∧ post.memory = s.memory ∧
      post.globals = s.globals.update (ofString "heap_ptr",
        .val (.word ((p + (n + 7)) &&& ((0 : BitVec 64) - 8))))) := by
  intro v hv
  obtain ⟨rfl, hready, hstep, hfit, hm, hg⟩ :=
    dispatch_alloc_run s hc (evmMsgReady_of_msgBounded h) p n hp hn v hv
  have hbe : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).2.be = s.be :=
    (M13.evaluateHOLFiniteState_guestInv_be s (sourceFnBody Guest.Software.guestFn_alloc) h.1.1).2
  obtain ⟨hPB', hstepCC, _⟩ := evmMsgReadyMsgBounded_of_fresh_heap_step h hready.1 hbe
    hstep.2.1 hstep.2.2.1 (fun _ _ => by rw [hm]) (fun _ _ _ => by simp [memB, hm, hbe])
  exact ⟨rfl, hPB', hstepCC, hfit, hm, hg⟩

def DispatchCopyReadyB (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (cells : List (Nat × Nat × Nat × Nat))
    {F : Type} (mid : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ (s : PanSemStateFiniteExact 64 F) (dst src : BitVec 64),
    D0PreB gw hp G ch cells s ∧ ArenaReady mid ∧
    globN s "heap_ptr" ≤ globN mid "heap_ptr" ∧ GlobalsKept ["heap_ptr"] s mid ∧
    mid.memory = s.memory ∧ mid.be = s.be ∧ mid.locals = s.locals ∧
    mid.locals.lookup (ofString "daddr") = some (.val (.word dst)) ∧
    mid.locals.lookup (ofString "da") = some (.val (.word src)) ∧
    globN s "heap_ptr" ≤ dst.toNat ∧ dst.toNat + 20 ≤ globN mid "heap_ptr"

theorem d0PreB_of_alloc_copy (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (cells : List (Nat × Nat × Nat × Nat))
    {F : Type} {s mid post : PanSemStateFiniteExact 64 F}
    (hD : D0PreB gw hp G ch cells s) (hmid : ArenaReady mid)
    (hh : "heap_ptr" ∈ gw) (hhp : globN s "heap_ptr" ≤ globN mid "heap_ptr")
    (hG : GlobalsKept ["heap_ptr"] s mid)
    (hm : mid.memory = s.memory) (hbe : mid.be = s.be)
    (hloc : post.locals = s.locals)
    (dst : Nat) (hlo : globN s "heap_ptr" ≤ dst)
    (hhi : dst + 20 ≤ globN mid "heap_ptr")
    (he : ByteRegionEffect mid post [(dst, 20)]) : D0PreB gw hp G ch cells post := by
  have hPB := hD.1.1
  have hAs := hPB.1
  have hgn : ∀ name : String, globN post name = globN mid name := by
    intro name; unfold globN; rw [he.globals]
  have hAp : ArenaReady post := by
    refine ⟨⟨he.code.trans hmid.1.code, he.memaddrs.trans hmid.1.memaddrs,
      he.shMemaddrs.trans hmid.1.shMemaddrs, he.baseAddr.trans hmid.1.baseAddr⟩, ?_⟩
    simpa only [ArenaOK, globN, he.globals, GlobalsWord, GlobalWord] using hmid.2
  have hmem : ∀ a, ¬ s.memaddrs a → post.memory a = s.memory a := by
    intro a ha
    have hd : mid.memaddrs = s.memaddrs := hmid.1.memaddrs.trans hAs.1.memaddrs.symm
    exact (he.out_dom a (by rw [hd]; exact ha)).trans (congrFun hm a)
  have hbyte : ∀ b, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN post "heap_ptr") → memB post b = memB s b := by
    intro b hb hn
    rw [hgn] at hn
    have hmB : memB mid b = memB s b := by simp [memB, hm, hbe]
    refine (he.byte_frame b hb ?_).trans hmB
    intro i hi hin
    simp only [List.mem_singleton] at hi
    subst i
    unfold InIvl at hin
    exact hn ⟨by omega, by omega⟩
  have hG' : GlobalsKept ["heap_ptr"] s post := by
    intro g hg; rw [he.globals]; exact hG g hg
  obtain ⟨hPB', hstepCC, h112⟩ := evmMsgReadyMsgBounded_of_fresh_heap_step hPB hAp
    (he.be.trans hbe) (by rw [hgn]; exact hhp) hG' hmem hbyte
  have hev : post.globals.lookup (ofString "ev") = s.globals.lookup (ofString "ev") := by
    rw [he.globals]; exact (hG (ofString "ev") (by decide)).symm
  exact d0PreB_of_stepFromCC gw hp G ch cells hD hPB'
    (stepFromCC_of_evmStepCC (fun g hg => by simpa using (List.mem_singleton.1 hg ▸ hh))
      hD.1.2 hstepCC) hloc hev h112

theorem dispatch_alloc_copy_resumeB (gw : List String) (hp0 : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (cells : List (Nat × Nat × Nat × Nat)) :
    DecCallResumeOn (fun s => D0PreB gw hp0 G ch cells s ∧ ∃ src : BitVec 64,
      s.locals.lookup (ofString "da") = some (.val (.word src)))
      (DispatchCopyReadyB gw hp0 G ch cells) (ofString "daddr") (ofString "alloc") [.const 24] := by
  intro F s values body callee ret v post hc hP ha hl hb
  obtain ⟨hD, src, hsrc⟩ := hP
  have hv : values = [.val (.word (24 : BitVec 64))] := by
    simpa [evalListHOLFinite, evalListHOLExact, evalHOLExact] using ha.symm
  subst values
  rw [hc] at hl
  have hlookup : originalRuntimeCode.lookup (ofString "alloc") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_alloc, .one) :=
    lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_alloc) rfl
  have hparams : body = sourceFnBody Guest.Software.guestFn_alloc ∧
      callee.lookup (ofString "n") = some (.val (.word (24 : BitVec 64))) := by
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
    split at hl
    · cases hl
    · rename_i b l rs raw
      cases hl
      unfold lookupCodeHOLExact at raw
      rw [hlookup] at raw
      simp [shapeOfHOLExact, shapeEqHOL] at raw
      exact ⟨raw.1.symm, by dsimp only; rw [← raw.2.1]; simp⟩
  rcases hparams with ⟨rfl, hn⟩
  have hE := localsFree_evmMsgReadyMsgBounded s callee (s.clock - 1) hD.1.1
  obtain ⟨p, hp⟩ := hE.1.2.2.2.2.2.2.2.2.2 "heap_ptr" (by decide)
  have hrun := dispatch_alloc_runB (callEntryStateHOLFinite s callee) hc hE p 24 hp hn v
    (by rw [hb])
  rw [hb] at hrun
  obtain ⟨rfl, hready, hstepCC, hfit, hm, hg⟩ := hrun
  dsimp only at hready hstepCC hfit hm hg
  let L := (setVarHOLFinite (ofString "daddr") (.val (.word p)) s).locals
  let s0 := { s with locals := L }
  have hD0 : D0PreB gw hp0 G ch cells s0 := by
    apply d0PreB_locals gw hp0 G ch cells s L s.clock _ hD
    simp (config := {decide := true}) [L, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hready' := localsFree_evmMsgReadyMsgBounded post L post.clock hready
  refine ⟨s0, p, src, hD0, hready'.1, hstepCC.1.2.1, hstepCC.1.2.2.1, hm, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · exact (M13.evaluateHOLFiniteState_guestInv_be
      (callEntryStateHOLFinite s callee) (sourceFnBody Guest.Software.guestFn_alloc)
      (evmInv_guestInv _ (evmInv_of_msgBounded hE))).2 |> fun he => by
        rw [hb] at he; exact he
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · simpa (config := {decide := true}) [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE] using hsrc
  · have hpn : globN s "heap_ptr" = p.toNat := by
      change s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) at hp
      simp [globN, hp]
    exact le_of_eq hpn
  · change p.toNat + 20 ≤ globN post "heap_ptr"
    have hn24 : (24 : BitVec 64).toNat = 24 := rfl
    rw [hn24] at hfit
    omega

theorem hoare_prepare_dispatch_memcpyB (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (cells : List (Nat × Nat × Nat × Nat))
    (hh : "heap_ptr" ∈ gw) :
    Hoare (DispatchCopyReadyB gw hp G ch cells)
      (.call (some (none, none)) (ofString "memcpy")
        [.var .local (ofString "daddr"), .var .local (ofString "da"), .const 20])
      (Fall (fun s => D0PreB gw hp G ch cells s ∧ ∃ dst : BitVec 64,
        s.locals.lookup (ofString "daddr") = some (.val (.word dst)))) := by
  refine ⟨fun {F} mid hc hP hnt hr => ?_⟩
  obtain ⟨s, dst, src, hD, hmid, hhp, hG, hm, hbe, hloc, hdst, hsrc, hlo, hhi⟩ := hP
  have he := dispatch_memcpy_effect mid dst src hc (arenaReady_guestInv mid hmid)
    hdst hsrc hnt hr
  have hnox := StateRestoreEpilogue.evaluate_noCatchableRaise
    StateRestoreEpilogue.htabMutCallees StateRestoreEpilogue.htabMutCallees_good
    (.call (some (none, none)) (ofString "memcpy")
      [.var .local (ofString "daddr"), .var .local (ofString "da"), .const 20])
    (by decide) mid hc
  have hnone : (evaluateHOLFiniteState mid (.call (some (none, none)) (ofString "memcpy")
      [.var .local (ofString "daddr"), .var .local (ofString "da"), .const 20])).1 = none := by
    rcases hr with hr | ⟨v, hv⟩ | ⟨e, v, hev, hne⟩
    · exact hr
    · rw [evaluateHOLFiniteState_call] at hv
      exfalso
      revert hv
      split <;> [simp; (split <;> [simp; (split <;> [simp; skip])])]
      rcases evaluateHOLFiniteState (callEntryStateHOLFinite mid _) _ with ⟨rc, _⟩
      rcases rc with _ | (_ | _ | _ | _ | _ | _ | _) <;> dsimp only <;> (repeat' split) <;> simp
    · exact (hnox e v hne hev).elim
  have hl := dispatch_call_none_locals mid _ _ hnone
  exact ⟨d0PreB_of_alloc_copy gw hp G ch cells hD hmid hh hhp hG hm hbe
    (hl.trans hloc) dst.toNat hlo hhi he, dst, by rw [hl]; exact hdst⟩

theorem hoare_prepare_dispatch_alloc_memcpyB (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (cells : List (Nat × Nat × Nat × Nat))
    (hh : "heap_ptr" ∈ gw) (tail : ProgHOL 64)
    (htail : Hoare (fun s => D0PreB gw hp G ch cells s ∧ ∃ dst : BitVec 64,
      s.locals.lookup (ofString "daddr") = some (.val (.word dst))) tail
      (Fall (fun s => EvmMsgReadyMsgBounded s ∧ StepFromCC gw hp G ch cells s))) :
    Hoare (fun s => D0PreB gw hp G ch cells s ∧ ∃ src : BitVec 64,
      s.locals.lookup (ofString "da") = some (.val (.word src)))
      (.decCall (ofString "daddr") .one (ofString "alloc") [.const 24]
        (.seq (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "daddr"), .var .local (ofString "da"), .const 20]) tail))
      (Fall (fun s => EvmMsgReadyMsgBounded s ∧ StepFromCC gw hp G ch cells s)) := by
  refine Hoare.decCall_returning_fall
    (fun s l k h => ⟨localsFree_evmMsgReadyMsgBounded s l k h.1,
      localsFree_stepFromCC gw hp G ch cells s l k h.2⟩)
    (dispatch_alloc_copy_resumeB gw hp G ch cells) ?_
    (Hoare.seq_fall' (hoare_prepare_dispatch_memcpyB gw hp G ch cells hh) htail (fun _ h => h.1.1))
  intro F s values body callee ret hc _ hl e v he
  rw [hc] at hl
  exact StateRestoreEpilogue.evaluate_noCatchableRaise
    StateRestoreEpilogue.htabMutCallees StateRestoreEpilogue.htabMutCallees_good body
    (StateRestoreEpilogue.htabMutCallees_good _ (by decide) values body callee ret hl)
    (callEntryStateHOLFinite s callee) hc e v he

end PrimSteps

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
