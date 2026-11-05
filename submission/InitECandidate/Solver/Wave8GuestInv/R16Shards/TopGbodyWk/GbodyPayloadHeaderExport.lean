import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.GbodyPayloadHeader
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkBlockRlpLength
import InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover.HeaderHash

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
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
open InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
open InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover

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
        rw [hg.memaddrs, R10Shards.Fast_GbodyC17ToC21.ordinaryDomain_iff] at hdom
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
      · rw [hw] at hev
        simp only [Option.some.injEq] at hev
        subst hev
        simp [flattenHOL]
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

private theorem ph_z8_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F} (h : PH_Z8 s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1

private theorem ph_bh_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F} (h : PH_BH s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1

private theorem ph_loop_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F} (h : PH_LOOP s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1

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

theorem ph_alloc_txr
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc")) :
    DecCallResumeOn (PH_H false) (PH_TXR false) (ofString "txr") (ofString "alloc") [.const 32#64] := by
  refine ph_alloc_generic "txr" 32 (by omega) (by decide) wal rtal ?_
  intro F s ⟨w_si, w_pl, w_raw, w_h, S, Nd, hIA, hBs, hd_ic, hlsi, hlpl, hlraw, hlh, hpl_eq, _⟩
  refine ⟨w_si, S, Nd, [(w_h.toNat, 248)], hIA, hBs, hd_ic, ?_⟩
  intro post w_txr S' Nd'
  dsimp only
  intro hIA_res hBs_res hd_ic_res hd_bs _ hu_ic
  have hic := inputCells_eq_of_unhit hIA hu_ic
  exact ⟨w_si, w_pl, w_raw, w_h, w_txr, S', Nd', hIA_res, hBs_res, hd_ic_res,
    hd_bs _ (by simp),
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "txr" ≠ ofString "si" by decide, hlsi],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "txr" ≠ ofString "pl" by decide, hlpl],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "txr" ≠ ofString "raw" by decide, hlraw],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "txr" ≠ ofString "h" by decide, hlh],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
    by rw [hic.1]; exact hpl_eq,
    fun h => by cases h⟩

theorem ph_txr_store_false (off : Nat) (src : ExpHOL 64)
    (hoff8 : off % 8 = 0) (hoff_fit : off + 32 ≤ 248)
    (hlen : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      PH_TXR false s → evalAt s src = some v → (flattenHOL v).length ≤ 4) :
    Hoare (PH_TXR false)
      (.store (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 off)]) src)
      (fun r t => r = none → PH_TXR false t) := by
  refine Hoare_store_fall (fun s x v mem' hP hx hv hst => ?_)
  have hvlen := hlen s v hP hv
  obtain ⟨w_si, w_pl, w_raw, w_h, w_txr, S, Nd, hIA, hBs, hd_ic, hd_ht,
    hlsi, hlpl, hlraw, hlh, hltxr, hpl_eq, _⟩ := hP
  have hx_eq := evalAt_add_local_const hlh hx
  have htr := store_in_tracked_block (base := w_h.toNat) (sz := 248) (off := off)
    hIA hBs (by simp)
    (fun c hc b hb => by simp only [List.mem_singleton] at hb; subst hb; exact hd_ic c hc _ (by simp))
    rfl hoff8 hx_eq (by omega) hst
  have hic := inputCells_eq_of_unhit hIA (fun c hc =>
    htr.2.2 c (fun _ => (hIA.2.2.1 c hc).2.1) (hd_ic c hc (w_h.toNat, 248) (by simp)))
  exact ⟨w_si, w_pl, w_raw, w_h, w_txr, S, Nd, htr.1, htr.2.1,
    by rw [hic.2.2]; exact hd_ic,
    hd_ht, hlsi, hlpl, hlraw, hlh, hltxr, by rw [hic.1]; exact hpl_eq,
    fun h => by cases h⟩

theorem ph_txr_store_simple (off : Nat) (src : ExpHOL 64)
    (hoff8 : off % 8 = 0) (hoff_fit : off + 32 ≤ 248)
    (hkind : src = .const 1#64 ∨ (∃ a b, src = .op .add [a, b]) ∨ (∃ addr, src = .load .one addr)) :
    Hoare (PH_TXR false)
      (.store (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 off)]) src)
      (fun r t => r = none → PH_TXR false t) := by
  apply ph_txr_store_false off src hoff8 hoff_fit
  intro F s v _ hv
  have := evalAt_simple_word_len hkind hv
  omega

theorem ph_store_h24_raw32 :
    Hoare (PH_H false)
      (.store (.op .add [.var .local (ofString "h"), .const 24#64])
        (.op .add [.var .local (ofString "raw"), .const 32#64]))
      (fun r t => r = none → PH_H false t) :=
  ph_h_store_simple false 24 _ (by omega) (by omega) (by simp) (Or.inr (Or.inl ⟨_, _, rfl⟩))

theorem ph_store_h32_raw52 :
    Hoare (PH_H false)
      (.store (.op .add [.var .local (ofString "h"), .const 32#64])
        (.op .add [.var .local (ofString "raw"), .const 52#64]))
      (fun r t => r = none → PH_H false t) :=
  ph_h_store_simple false 32 _ (by omega) (by omega) (by simp) (Or.inr (Or.inl ⟨_, _, rfl⟩))

theorem ph_store_h48_raw84 :
    Hoare (PH_TXR false)
      (.store (.op .add [.var .local (ofString "h"), .const 48#64])
        (.op .add [.var .local (ofString "raw"), .const 84#64]))
      (fun r t => r = none → PH_TXR false t) :=
  ph_txr_store_simple 48 _ (by omega) (by omega) (Or.inr (Or.inl ⟨_, _, rfl⟩))

theorem ph_store_h56_raw116 :
    Hoare (PH_TXR false)
      (.store (.op .add [.var .local (ofString "h"), .const 56#64])
        (.op .add [.var .local (ofString "raw"), .const 116#64]))
      (fun r t => r = none → PH_TXR false t) :=
  ph_txr_store_simple 56 _ (by omega) (by omega) (Or.inr (Or.inl ⟨_, _, rfl⟩))

theorem ph_store_h_load_pl (off srcOff : Nat) (hoff8 : off % 8 = 0) (hfit : off + 32 ≤ 248) :
    Hoare (PH_TXR false)
      (.store (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 off)])
        (.load .one (.op .add [.var .local (ofString "pl"), .const (BitVec.ofNat 64 srcOff)])))
      (fun r t => r = none → PH_TXR false t) :=
  ph_txr_store_simple off _ hoff8 hfit (Or.inr (Or.inr ⟨_, rfl⟩))

theorem ph_store_h96_pl80 :
    Hoare (PH_TXR false)
      (.store (.op .add [.var .local (ofString "h"), .const 96#64])
        (.load .one (.op .add [.var .local (ofString "pl"), .const 80#64])))
      (fun r t => r = none → PH_TXR false t) :=
  ph_store_h_load_pl 96 80 (by omega) (by omega)

theorem ph_store_h104_pl88 :
    Hoare (PH_TXR false)
      (.store (.op .add [.var .local (ofString "h"), .const 104#64])
        (.load .one (.op .add [.var .local (ofString "pl"), .const 88#64])))
      (fun r t => r = none → PH_TXR false t) :=
  ph_store_h_load_pl 104 88 (by omega) (by omega)

theorem ph_store_h112_pl96 :
    Hoare (PH_TXR false)
      (.store (.op .add [.var .local (ofString "h"), .const 112#64])
        (.load .one (.op .add [.var .local (ofString "pl"), .const 96#64])))
      (fun r t => r = none → PH_TXR false t) :=
  ph_store_h_load_pl 112 96 (by omega) (by omega)

theorem ph_store_h120_pl104 :
    Hoare (PH_TXR false)
      (.store (.op .add [.var .local (ofString "h"), .const 120#64])
        (.load .one (.op .add [.var .local (ofString "pl"), .const 104#64])))
      (fun r t => r = none → PH_TXR false t) :=
  ph_store_h_load_pl 120 104 (by omega) (by omega)

theorem ph_store_h128_pl16 :
    Hoare (PH_TXR false)
      (.store (.op .add [.var .local (ofString "h"), .const 128#64])
        (.load .one (.op .add [.var .local (ofString "pl"), .const 16#64])))
      (fun r t => r = none → PH_TXR false t) :=
  ph_store_h_load_pl 128 16 (by omega) (by omega)

theorem ph_store_h40_txr :
    Hoare (PH_TXR false)
      (.store (.op .add [.var .local (ofString "h"), .const 40#64]) (.var .local (ofString "txr")))
      (fun r t => r = none → PH_TXR false t) := by
  apply ph_txr_store_false 40 _ (by omega) (by omega)
  intro F s v ⟨_, _, _, _, w_txr, _, _, _, _, _, _, _, _, _, _, hl, _⟩ hv
  simp only [evalAt, evalHOLExact, hl, Option.some.injEq] at hv
  subst v
  simp [flattenHOL]

theorem ph_store_h64_zero :
    Hoare (PH_TXR false)
      (.store (.op .add [.var .local (ofString "h"), .const 64#64])
        (.rstruct [.const 0#64, .const 0#64, .const 0#64, .const 0#64]))
      (fun r t => r = none → PH_TXR false t) := by
  apply ph_txr_store_false 64 _ (by omega) (by omega)
  intro F s v _ hv
  simp [evalAt, evalHOLExact, evalListHOLExact] at hv
  subst v
  simp [flattenHOL]

theorem ph_store_h136_pl24 :
    Hoare (PH_TXR false)
      (.store (.op .add [.var .local (ofString "h"), .const 136#64])
        (.load .one (.op .add [.var .local (ofString "pl"), .const 24#64])))
      (fun r t => r = none → PH_TXR true t) := by
  refine Hoare_store_fall (fun s x v mem' hP hx hv hst => ?_)
  obtain ⟨w_si, w_pl, w_raw, w_h, w_txr, S, Nd, hIA, hBs, hd_ic, hd_ht,
    hlsi, hlpl, hlraw, hlh, hltxr, hpl_eq, _⟩ := hP
  obtain ⟨a, w, ha, rfl, hw, _⟩ := evalAt_load_one_word hIA.1.1 hv
  have ha_eq := evalAt_add_local_const hlpl ha
  have hx_eq := evalAt_add_local_const hlh hx
  have htr := store_in_tracked_block (base := w_h.toNat) (sz := 248) (off := 136)
    hIA hBs (by simp)
    (fun c hc b hb => by simp only [List.mem_singleton] at hb; subst hb; exact hd_ic c hc _ (by simp))
    rfl (by omega) hx_eq (by simp [flattenHOL]) hst
  have hic := inputCells_eq_of_unhit hIA (fun c hc =>
    htr.2.2 c (fun _ => (hIA.2.2.1 c hc).2.1) (hd_ic c hc (w_h.toNat, 248) (by simp)))
  have hlim : heapLimit < 2 ^ 64 := by decide
  have hh := (hBs (w_h.toNat, 248) (by simp)).2.2.1.2
  have hp := (hIA.2.2.1 (memW s w_si.toNat, 136) (by simp [inputCells])).1.2
  have hhp := hIA.1.2.2.1
  have hxnat : x.toNat = w_h.toNat + 136 := by
    rw [hx_eq, BitVec.toNat_add]
    change (w_h.toNat + 136) % 2 ^ 64 = _
    omega
  have hanat : a.toNat = w_pl.toNat + 24 := by
    rw [ha_eq, BitVec.toNat_add]
    change (w_pl.toNat + 24) % 2 ^ 64 = _
    omega
  have hcell := panMemStoresHOL_word_memW (by simpa [flattenHOL] using hst)
  have hbound : memW { s with memory := mem' } (w_h.toNat + 136) ≤ 32 := by
    have hmw : memW { s with memory := mem' } x.toNat = w.toNat := by
      unfold memW; simp [BitVec.ofNat_toNat, hcell]
    rw [← hxnat, hmw, hw, hanat, hpl_eq]
    exact hIA.2.2.2.2.2.1.2.1
  exact ⟨w_si, w_pl, w_raw, w_h, w_txr, S, Nd, htr.1, htr.2.1,
    by rw [hic.2.2]; exact hd_ic,
    hd_ht, hlsi, hlpl, hlraw, hlh, hltxr, by rw [hic.1]; exact hpl_eq,
    fun _ => hbound⟩

private theorem ph_tracked_word_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {bs : List Ivl} {base sz off : Nat}
    (hIA : InputAtWith s S Nd (locN s "si"))
    (hBs : AllBlocksGood s S Nd bs) (hb : (base, sz) ∈ bs)
    (hu : IvlUnhit s post (base, sz)) (hoff8 : off % 8 = 0) (hoff : off + 8 ≤ sz) :
    memW post (base + off) = memW s (base + off) := by
  have hg := hBs (base, sz) hb
  have hlim : heapLimit < 2 ^ 64 := by decide
  have hhp := hIA.1.2.2.1
  exact memW_eq_of_ivlUnhit hu (by have := hg.1; omega)
    (by have := hg.2.2.1.2; omega) ⟨by omega, by omega⟩

theorem ph_txr_store_after136 (off : Nat) (src : ExpHOL 64)
    (hoff8 : off % 8 = 0) (hoff_fit : off + 8 ≤ 248) (hne : off ≠ 136)
    (hkind : src = .const 1#64 ∨ (∃ a b, src = .op .add [a, b]) ∨ (∃ addr, src = .load .one addr)) :
    Hoare (PH_TXR true)
      (.store (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 off)]) src)
      (fun r t => r = none → PH_TXR true t) := by
  refine Hoare_store_fall (fun s x v mem' hP hx hv hst => ?_)
  obtain ⟨w_si, w_pl, w_raw, w_h, w_txr, S, Nd, hIA, hBs, hd_ic, hd_ht,
    hlsi, hlpl, hlraw, hlh, hltxr, hpl_eq, h136⟩ := hP
  have hx_eq := evalAt_add_local_const hlh hx
  have hlen := evalAt_simple_word_len hkind hv
  have htr := store_in_tracked_block (base := w_h.toNat) (sz := 248) (off := off)
    hIA hBs (by simp)
    (fun c hc b hb => by simp only [List.mem_singleton] at hb; subst hb; exact hd_ic c hc _ (by simp))
    rfl hoff8 hx_eq (by omega) hst
  have hic := inputCells_eq_of_unhit hIA (fun c hc =>
    htr.2.2 c (fun _ => (hIA.2.2.1 c hc).2.1) (hd_ic c hc (w_h.toNat, 248) (by simp)))
  have hh := hBs (w_h.toNat, 248) (by simp)
  have hhp := hIA.1.2.2.1
  have hlim : heapLimit < 2 ^ 64 := by decide
  have hxnat : x.toNat = w_h.toNat + off := by
    rw [hx_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
    have hofflt : off < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hofflt]
    exact Nat.mod_eq_of_lt (by have := hh.2.2.1.2; omega)
  have hm : mem' (BitVec.ofNat 64 (w_h.toNat + 136)) = s.memory (BitVec.ofNat 64 (w_h.toNat + 136)) := by
    apply panMemStoresHOL_frame (flattenHOL v) x s.memory mem' hst
    intro k hk heq
    have hlhs : (BitVec.ofNat 64 (w_h.toNat + 136)).toNat = w_h.toNat + 136 := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := hh.2.2.1.2; omega)
    have hrhs : (x + BitVec.ofNat 64 (8 * k)).toNat = w_h.toNat + off + 8 * k := by
      rw [BitVec.toNat_add, hxnat, BitVec.toNat_ofNat]
      have hklt : 8 * k < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt hklt]
      simpa [Nat.add_assoc] using Nat.mod_eq_of_lt (show w_h.toNat + off + 8 * k < 2 ^ 64 by have := hh.2.2.1.2; omega)
    rw [heq] at hlhs
    omega
  have hbnd : memW { s with memory := mem' } (w_h.toNat + 136) ≤ 32 := by
    change (match mem' (BitVec.ofNat 64 (w_h.toNat + 136)) with | .word w => w.toNat) ≤ 32
    rw [hm]
    exact h136 rfl
  exact ⟨w_si, w_pl, w_raw, w_h, w_txr, S, Nd, htr.1, htr.2.1,
    by rw [hic.2.2]; exact hd_ic,
    hd_ht, hlsi, hlpl, hlraw, hlh, hltxr, by rw [hic.1]; exact hpl_eq,
    fun _ => hbnd⟩

theorem ph_store_h144_raw372 :
    Hoare (PH_TXR true)
      (.store (.op .add [.var .local (ofString "h"), .const 144#64])
        (.op .add [.var .local (ofString "raw"), .const 372#64]))
      (fun r t => r = none → PH_TXR true t) :=
  ph_txr_store_after136 144 _ (by omega) (by omega) (by omega) (Or.inr (Or.inl ⟨_, _, rfl⟩))

def PH_Z8D : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => PH_Z8 s ∧ Disj (locN s "txr", 32) (locN s "z8", 8)

theorem ph_z8d_z8 {F : Type} {s : PanSemStateFiniteExact 64 F} (h : PH_Z8D s) : PH_Z8 s := h.1

theorem ph_z8d_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F} (h : PH_Z8D s) : GuestInv s :=
  ph_z8_guestInv h.1

theorem ph_alloc_z8d
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc")) :
    DecCallResumeOn (PH_TXR true) PH_Z8D (ofString "z8") (ofString "alloc") [.const 8#64] := by
  refine ph_alloc_generic "z8" 8 (by omega) (by decide) wal rtal ?_
  intro F s ⟨w_si, w_pl, w_raw, w_h, w_txr, S, Nd, hIA, hBs, hd_ic, hd_ht,
    hlsi, hlpl, hlraw, hlh, hltxr, hpl_eq, h136⟩
  refine ⟨w_si, S, Nd, [(w_h.toNat, 248), (w_txr.toNat, 32)], hIA, hBs, hd_ic, ?_⟩
  intro post w_z8 S' Nd'
  dsimp only
  intro hIA_res hBs_res hd_ic_res hd_bs hu_bs hu_ic
  have hic := inputCells_eq_of_unhit hIA hu_ic
  have hloc : locN s "si" = w_si.toNat := by simp [locN, hlsi]
  have hword := ph_tracked_word_unhit (off := 136) (by rwa [hloc]) hBs (by simp)
    (hu_bs (w_h.toNat, 248) (by simp)) (by omega) (by omega)
  have hltxr_res : (setVarHOLFinite (ofString "z8") (.val (.word w_z8)) { post with locals := s.locals }).locals.lookup
      (ofString "txr") = some (.val (.word w_txr)) := by
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "z8" ≠ ofString "txr" by decide, hltxr]
  have hlz8_res : (setVarHOLFinite (ofString "z8") (.val (.word w_z8)) { post with locals := s.locals }).locals.lookup
      (ofString "z8") = some (.val (.word w_z8)) := by
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  refine ⟨⟨w_si, w_pl, w_raw, w_h, w_txr, w_z8, S', Nd', hIA_res, hBs_res, hd_ic_res,
    hd_ht, hd_bs (w_h.toNat, 248) (by simp),
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "z8" ≠ ofString "si" by decide, hlsi],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "z8" ≠ ofString "pl" by decide, hlpl],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "z8" ≠ ofString "raw" by decide, hlraw],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "z8" ≠ ofString "h" by decide, hlh],
    hltxr_res, hlz8_res,
    by rw [hic.1]; exact hpl_eq,
    by rw [hword]; exact h136 rfl⟩, ?_⟩
  simp only [locN, hltxr_res, hlz8_res]
  exact hd_bs (w_txr.toNat, 32) (by simp)

theorem ph_memzero_z8d
    (wmz : WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")]) []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "memzero")) :
    Hoare PH_Z8D
      (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "z8"), .const 8#64])
      (fun r t => r = none → PH_TXR true t ∧ ∃ w_z8 : BitVec 64, t.locals.lookup (ofString "z8") = some (.val (.word w_z8))) := by
  refine ph_memzero_generic "z8" 8 (by decide) wmz ?_
  intro F s ⟨⟨w_si, w_pl, w_raw, w_h, w_txr, w_z8, S, Nd, hIA, hBs, hd_ic, hd_ht, hd_hz,
    hlsi, hlpl, hlraw, hlh, hltxr, hlz8, hpl_eq, h136⟩, hd_tz⟩
  simp only [locN, hltxr, hlz8] at hd_tz
  refine ⟨w_si, w_z8, S, Nd, [(w_h.toNat, 248), (w_txr.toNat, 32)], hlz8, hIA,
    (fun b hb => by
      rcases List.mem_cons.1 hb with rfl | hb1
      · exact hBs _ (by simp)
      · rcases List.mem_cons.1 hb1 with rfl | hb2
        · exact hBs _ (by simp)
        · simp only [List.mem_singleton] at hb2; subst hb2; exact hBs _ (by simp)),
    (fun c hc b hb => by
      rcases List.mem_cons.1 hb with rfl | hb1
      · exact hd_ic c hc _ (by simp)
      · rcases List.mem_cons.1 hb1 with rfl | hb2
        · exact hd_ic c hc _ (by simp)
        · simp only [List.mem_singleton] at hb2; subst hb2; exact hd_ic c hc _ (by simp)),
    (fun b hb => by
      rcases List.mem_cons.1 hb with rfl | hb1
      · exact hd_hz
      · simp only [List.mem_singleton] at hb1; subst hb1; exact hd_tz), ?_⟩
  intro post S' Nd'
  dsimp only
  intro hIA_res hBs_res hu_keep hu_ic
  have hic := inputCells_eq_of_unhit hIA hu_ic
  have hloc : locN s "si" = w_si.toNat := by simp [locN, hlsi]
  have hword := ph_tracked_word_unhit (off := 136) (by rwa [hloc]) hBs (by simp)
    (hu_keep (w_h.toNat, 248) (by simp)) (by omega) (by omega)
  refine ⟨⟨w_si, w_pl, w_raw, w_h, w_txr, S', Nd', hIA_res,
    (fun b hb => hBs_res b (List.mem_cons_of_mem _ hb)),
    ?_, hd_ht, hlsi, hlpl, hlraw, hlh, hltxr,
    by rw [hic.1]; exact hpl_eq,
    fun _ => by rw [hword]; exact h136⟩, w_z8, hlz8⟩
  rw [hic.2.2]
  intro c hc b hb
  rcases List.mem_cons.1 hb with rfl | hb1
  · exact hd_ic c hc _ (by simp)
  · simp only [List.mem_singleton] at hb1; subst hb1; exact hd_ic c hc _ (by simp)

theorem ph_store_h152_z8 :
    Hoare (fun s => PH_TXR true s ∧ ∃ w_z8 : BitVec 64, s.locals.lookup (ofString "z8") = some (.val (.word w_z8)))
      (.store (.op .add [.var .local (ofString "h"), .const 152#64]) (.var .local (ofString "z8")))
      (fun r t => r = none → PH_TXR true t) := by
  refine Hoare_store_fall (fun s x v mem' ⟨hP, w_z8, hlz8⟩ hx hv hst => ?_)
  obtain ⟨w_si, w_pl, w_raw, w_h, w_txr, S, Nd, hIA, hBs, hd_ic, hd_ht,
    hlsi, hlpl, hlraw, hlh, hltxr, hpl_eq, h136⟩ := hP
  have hx_eq := evalAt_add_local_const hlh hx
  have hv_eq : v = .val (.word w_z8) := by
    simp only [evalAt, evalHOLExact, hlz8, Option.some.injEq] at hv; exact hv.symm
  subst hv_eq
  have htr := store_in_tracked_block (base := w_h.toNat) (sz := 248) (off := 152)
    hIA hBs (by simp)
    (fun c hc b hb => by simp only [List.mem_singleton] at hb; subst hb; exact hd_ic c hc _ (by simp))
    rfl (by omega) hx_eq (by simp [flattenHOL]) hst
  have hic := inputCells_eq_of_unhit hIA (fun c hc =>
    htr.2.2 c (fun _ => (hIA.2.2.1 c hc).2.1) (hd_ic c hc (w_h.toNat, 248) (by simp)))
  have hh := hBs (w_h.toNat, 248) (by simp)
  have hhp := hIA.1.2.2.1
  have hlim : heapLimit < 2 ^ 64 := by decide
  have hxnat : x.toNat = w_h.toNat + 152 := by
    rw [hx_eq, BitVec.toNat_add]
    change (w_h.toNat + 152) % 2 ^ 64 = _
    have := hh.2.2.1.2; omega
  have hm : mem' (BitVec.ofNat 64 (w_h.toNat + 136)) = s.memory (BitVec.ofNat 64 (w_h.toNat + 136)) := by
    apply panMemStoresHOL_frame (flattenHOL (.val (.word w_z8) : ValueHOL 64)) x s.memory mem' hst
    intro k hk heq
    have hlhs : (BitVec.ofNat 64 (w_h.toNat + 136)).toNat = w_h.toNat + 136 := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := hh.2.2.1.2; omega)
    have hrhs : (x + BitVec.ofNat 64 (8 * k)).toNat = w_h.toNat + 152 + 8 * k := by
      rw [BitVec.toNat_add, hxnat, BitVec.toNat_ofNat]
      have hklt : 8 * k < 2 ^ 64 := by simp [flattenHOL] at hk; omega
      rw [Nat.mod_eq_of_lt hklt]
      simp [flattenHOL] at hk
      simpa [Nat.add_assoc] using Nat.mod_eq_of_lt (show w_h.toNat + 152 + 8 * k < 2 ^ 64 by have := hh.2.2.1.2; omega)
    rw [heq] at hlhs; simp [flattenHOL] at hk; omega
  have hbnd : memW { s with memory := mem' } (w_h.toNat + 136) ≤ 32 := by
    change (match mem' (BitVec.ofNat 64 (w_h.toNat + 136)) with | .word w => w.toNat) ≤ 32
    rw [hm]; exact h136 rfl
  exact ⟨w_si, w_pl, w_raw, w_h, w_txr, S, Nd, htr.1, htr.2.1,
    by rw [hic.2.2]; exact hd_ic,
    hd_ht, hlsi, hlpl, hlraw, hlh, hltxr, by rw [hic.1]; exact hpl_eq,
    fun _ => hbnd⟩

theorem ph_dec_bf {body : ProgHOL 64} {K : Nat} (init : ExpHOL 64)
    (hbody : TerminatingProgBoundedOn PH_BF body K) :
    TerminatingProgBoundedOn (PH_TXR true) (.dec (ofString "bf") (.comb [.one, .one, .one, .one]) init body) K := by
  refine dec_shape_eval_on (ofString "bf") (.comb [.one, .one, .one, .one]) init ?_ hbody
  intro F s v hP _ hsh
  obtain ⟨w_si, w_pl, w_raw, w_h, w_txr, S, Nd, hIA, hBs, hd_ic, hd_ht,
    hlsi, hlpl, hlraw, hlh, hltxr, hpl_eq, h136⟩ := hP
  have hsh' : shapeEqHOL (shapeOfHOLExact v) (.comb [.one, .one, .one, .one]) = true := by
    have heq := (shapeEqHOL_eq_true _ _).1 hsh
    exact (shapeEqHOL_eq_true _ _).2 heq.symm
  refine ⟨⟨w_si, w_pl, w_raw, w_h, w_txr, S, Nd,
    (inputAtWith_with_locals s _ s.clock S Nd w_si.toNat).2 hIA,
    (allBlocksGood_with_locals s _ s.clock S Nd _).2 hBs,
    hd_ic, hd_ht,
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "bf" ≠ ofString "si" by decide, hlsi],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "bf" ≠ ofString "pl" by decide, hlpl],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "bf" ≠ ofString "raw" by decide, hlraw],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "bf" ≠ ofString "h" by decide, hlh],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "bf" ≠ ofString "txr" by decide, hltxr],
    hpl_eq, h136⟩,
    v, by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE], hsh'⟩

theorem ph_store_h160_bf :
    Hoare PH_BF
      (.store (.op .add [.var .local (ofString "h"), .const 160#64]) (.var .local (ofString "bf")))
      (fun r t => r = none → PH_TXR true t) := by
  refine Hoare_store_fall (fun s x v mem' ⟨hP, v_bf, hlbf, hsh⟩ hx hv hst => ?_)
  obtain ⟨w_si, w_pl, w_raw, w_h, w_txr, S, Nd, hIA, hBs, hd_ic, hd_ht,
    hlsi, hlpl, hlraw, hlh, hltxr, hpl_eq, h136⟩ := hP
  have hx_eq := evalAt_add_local_const hlh hx
  have hv_eq : v = v_bf := by
    simp only [evalAt, evalHOLExact, hlbf, Option.some.injEq] at hv; exact hv.symm
  subst hv_eq
  have hlen := len_le_four_of_shape_comb4 hsh
  have htr := store_in_tracked_block (base := w_h.toNat) (sz := 248) (off := 160)
    hIA hBs (by simp)
    (fun c hc b hb => by simp only [List.mem_singleton] at hb; subst hb; exact hd_ic c hc _ (by simp))
    rfl (by omega) hx_eq (by omega) hst
  have hic := inputCells_eq_of_unhit hIA (fun c hc =>
    htr.2.2 c (fun _ => (hIA.2.2.1 c hc).2.1) (hd_ic c hc (w_h.toNat, 248) (by simp)))
  have hh := hBs (w_h.toNat, 248) (by simp)
  have hhp := hIA.1.2.2.1
  have hlim : heapLimit < 2 ^ 64 := by decide
  have hxnat : x.toNat = w_h.toNat + 160 := by
    rw [hx_eq, BitVec.toNat_add]
    change (w_h.toNat + 160) % 2 ^ 64 = _
    have := hh.2.2.1.2; omega
  have hm : mem' (BitVec.ofNat 64 (w_h.toNat + 136)) = s.memory (BitVec.ofNat 64 (w_h.toNat + 136)) := by
    apply panMemStoresHOL_frame (flattenHOL v) x s.memory mem' hst
    intro k hk heq
    have hlhs : (BitVec.ofNat 64 (w_h.toNat + 136)).toNat = w_h.toNat + 136 := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := hh.2.2.1.2; omega)
    have hrhs : (x + BitVec.ofNat 64 (8 * k)).toNat = w_h.toNat + 160 + 8 * k := by
      rw [BitVec.toNat_add, hxnat, BitVec.toNat_ofNat]
      have hklt : 8 * k < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt hklt]
      simpa [Nat.add_assoc] using Nat.mod_eq_of_lt (show w_h.toNat + 160 + 8 * k < 2 ^ 64 by have := hh.2.2.1.2; omega)
    rw [heq] at hlhs; omega
  have hbnd : memW { s with memory := mem' } (w_h.toNat + 136) ≤ 32 := by
    change (match mem' (BitVec.ofNat 64 (w_h.toNat + 136)) with | .word w => w.toNat) ≤ 32
    rw [hm]; exact h136 rfl
  exact ⟨w_si, w_pl, w_raw, w_h, w_txr, S, Nd, htr.1, htr.2.1,
    by rw [hic.2.2]; exact hd_ic,
    hd_ht, hlsi, hlpl, hlraw, hlh, hltxr, by rw [hic.1]; exact hpl_eq,
    fun _ => hbnd⟩

theorem ph_alloc_z8
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc")) :
    DecCallResumeOn (PH_TXR true) PH_Z8 (ofString "z8") (ofString "alloc") [.const 8#64] := by
  refine ph_alloc_generic "z8" 8 (by omega) (by decide) wal rtal ?_
  intro F s ⟨w_si, w_pl, w_raw, w_h, w_txr, S, Nd, hIA, hBs, hd_ic, hd_ht,
    hlsi, hlpl, hlraw, hlh, hltxr, hpl_eq, h136⟩
  refine ⟨w_si, S, Nd, [(w_h.toNat, 248), (w_txr.toNat, 32)], hIA, hBs, hd_ic, ?_⟩
  intro post w_z8 S' Nd'
  dsimp only
  intro hIA_res hBs_res hd_ic_res hd_bs hu_bs hu_ic
  have hic := inputCells_eq_of_unhit hIA hu_ic
  have hloc : locN s "si" = w_si.toNat := by simp [locN, hlsi]
  have hword := ph_tracked_word_unhit (off := 136) (by rwa [hloc]) hBs (by simp)
    (hu_bs (w_h.toNat, 248) (by simp)) (by omega) (by omega)
  exact ⟨w_si, w_pl, w_raw, w_h, w_txr, w_z8, S', Nd', hIA_res, hBs_res, hd_ic_res,
    hd_ht, hd_bs _ (by simp),
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "z8" ≠ ofString "si" by decide, hlsi],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "z8" ≠ ofString "pl" by decide, hlpl],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "z8" ≠ ofString "raw" by decide, hlraw],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "z8" ≠ ofString "h" by decide, hlh],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "z8" ≠ ofString "txr" by decide, hltxr],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
    by rw [hic.1]; exact hpl_eq,
    by rw [hword]; exact h136 rfl⟩

theorem ph_alloc_wr
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc")) :
    DecCallResumeOn (PH_TXR true) PH_WR (ofString "wr") (ofString "alloc") [.const 32#64] := by
  refine ph_alloc_generic "wr" 32 (by omega) (by decide) wal rtal ?_
  intro F s ⟨w_si, w_pl, w_raw, w_h, w_txr, S, Nd, hIA, hBs, hd_ic, hd_ht,
    hlsi, hlpl, hlraw, hlh, hltxr, hpl_eq, h136⟩
  refine ⟨w_si, S, Nd, [(w_h.toNat, 248), (w_txr.toNat, 32)], hIA, hBs, hd_ic, ?_⟩
  intro post w_wr S' Nd'
  dsimp only
  intro hIA_res hBs_res hd_ic_res hd_bs hu_bs hu_ic
  have hic := inputCells_eq_of_unhit hIA hu_ic
  have hloc : locN s "si" = w_si.toNat := by simp [locN, hlsi]
  have hword := ph_tracked_word_unhit (off := 136) (by rwa [hloc]) hBs (by simp)
    (hu_bs (w_h.toNat, 248) (by simp)) (by omega) (by omega)
  exact ⟨w_si, w_pl, w_h, w_txr, w_wr, S', Nd', hIA_res, hBs_res, hd_ic_res,
    hd_ht, hd_bs (w_h.toNat, 248) (by simp), hd_bs (w_txr.toNat, 32) (by simp),
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "wr" ≠ ofString "si" by decide, hlsi],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "wr" ≠ ofString "pl" by decide, hlpl],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "wr" ≠ ofString "h" by decide, hlh],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "wr" ≠ ofString "txr" by decide, hltxr],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
    by rw [hic.1]; exact hpl_eq,
    by rw [hword]; exact h136 rfl⟩

theorem ph_alloc_rh
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc")) :
    DecCallResumeOn PH_WR PH_RH (ofString "rh") (ofString "alloc") [.const 32#64] := by
  refine ph_alloc_generic "rh" 32 (by omega) (by decide) wal rtal ?_
  intro F s ⟨w_si, w_pl, w_h, w_txr, w_wr, S, Nd, hIA, hBs, hd_ic, hd_ht, hd_hw, hd_tw,
    hlsi, hlpl, hlh, hltxr, hlwr, hpl_eq, h136⟩
  refine ⟨w_si, S, Nd, [(w_h.toNat, 248), (w_txr.toNat, 32), (w_wr.toNat, 32)], hIA, hBs, hd_ic, ?_⟩
  intro post w_rh S' Nd'
  dsimp only
  intro hIA_res hBs_res hd_ic_res hd_bs hu_bs hu_ic
  have hic := inputCells_eq_of_unhit hIA hu_ic
  have hloc : locN s "si" = w_si.toNat := by simp [locN, hlsi]
  have hword := ph_tracked_word_unhit (off := 136) (by rwa [hloc]) hBs (by simp)
    (hu_bs (w_h.toNat, 248) (by simp)) (by omega) (by omega)
  exact ⟨w_si, w_pl, w_h, w_txr, w_wr, w_rh, S', Nd', hIA_res, hBs_res, hd_ic_res,
    hd_ht, hd_hw, hd_tw, hd_bs (w_h.toNat, 248) (by simp),
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "rh" ≠ ofString "si" by decide, hlsi],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "rh" ≠ ofString "pl" by decide, hlpl],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "rh" ≠ ofString "h" by decide, hlh],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "rh" ≠ ofString "txr" by decide, hltxr],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "rh" ≠ ofString "wr" by decide, hlwr],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
    by rw [hic.1]; exact hpl_eq,
    by rw [hword]; exact h136⟩

theorem ph_alloc_bh
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc")) :
    DecCallResumeOn PH_RH PH_BH (ofString "bh") (ofString "alloc") [.const 32#64] := by
  refine ph_alloc_generic "bh" 32 (by omega) (by decide) wal rtal ?_
  intro F s ⟨w_si, w_pl, w_h, w_txr, w_wr, w_rh, S, Nd, hIA, hBs, hd_ic, hd_ht, hd_hw, hd_tw, hd_hr,
    hlsi, hlpl, hlh, hltxr, hlwr, hlrh, hpl_eq, h136⟩
  refine ⟨w_si, S, Nd, [(w_h.toNat, 248), (w_txr.toNat, 32), (w_wr.toNat, 32), (w_rh.toNat, 32)], hIA, hBs, hd_ic, ?_⟩
  intro post w_bh S' Nd'
  dsimp only
  intro hIA_res hBs_res hd_ic_res hd_bs hu_bs hu_ic
  have hic := inputCells_eq_of_unhit hIA hu_ic
  have hloc : locN s "si" = w_si.toNat := by simp [locN, hlsi]
  have hword := ph_tracked_word_unhit (off := 136) (by rwa [hloc]) hBs (by simp)
    (hu_bs (w_h.toNat, 248) (by simp)) (by omega) (by omega)
  exact ⟨w_si, w_pl, w_h, w_txr, w_wr, w_rh, w_bh, S', Nd', hIA_res, hBs_res, hd_ic_res,
    hd_ht, hd_hw, hd_tw, hd_hr, hd_bs (w_h.toNat, 248) (by simp),
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "bh" ≠ ofString "si" by decide, hlsi],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "bh" ≠ ofString "pl" by decide, hlpl],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "bh" ≠ ofString "h" by decide, hlh],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "bh" ≠ ofString "txr" by decide, hltxr],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "bh" ≠ ofString "wr" by decide, hlwr],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "bh" ≠ ofString "rh" by decide, hlrh],
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
    by rw [hic.1]; exact hpl_eq,
    by rw [hword]; exact h136⟩

private theorem ph_h136_frame_after {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {bs : List Ivl} {w_h x : BitVec 64} {off : Nat} {v : ValueHOL 64}
    {mem' : BitVec 64 → HolWordLab 64}
    (hIA : InputAtWith s S Nd (locN s "si"))
    (hBs : AllBlocksGood s S Nd bs) (hb : (w_h.toNat, 248) ∈ bs)
    (hx_eq : x = w_h + BitVec.ofNat 64 off)
    (hoff_fit : off + 8 * (flattenHOL v).length ≤ 248) (hne : off > 136)
    (hst : @panMemStoresHOL 64 _ x (flattenHOL v) s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem')
    (h136 : memW s (w_h.toNat + 136) ≤ 32) :
    memW { s with memory := mem' } (w_h.toNat + 136) ≤ 32 := by
  have hh := hBs (w_h.toNat, 248) hb
  have hhp := hIA.1.2.2.1
  have hlim : heapLimit < 2 ^ 64 := by decide
  have hxnat : x.toNat = w_h.toNat + off := by
    rw [hx_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
    have hofflt : off < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hofflt]
    exact Nat.mod_eq_of_lt (by have := hh.2.2.1.2; omega)
  have hm : mem' (BitVec.ofNat 64 (w_h.toNat + 136)) = s.memory (BitVec.ofNat 64 (w_h.toNat + 136)) := by
    apply panMemStoresHOL_frame (flattenHOL v) x s.memory mem' hst
    intro k hk heq
    have hlhs : (BitVec.ofNat 64 (w_h.toNat + 136)).toNat = w_h.toNat + 136 := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := hh.2.2.1.2; omega)
    have hrhs : (x + BitVec.ofNat 64 (8 * k)).toNat = w_h.toNat + off + 8 * k := by
      rw [BitVec.toNat_add, hxnat, BitVec.toNat_ofNat]
      have hklt : 8 * k < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt hklt]
      simpa [Nat.add_assoc] using Nat.mod_eq_of_lt (show w_h.toNat + off + 8 * k < 2 ^ 64 by have := hh.2.2.1.2; omega)
    rw [heq] at hlhs; omega
  change (match mem' (BitVec.ofNat 64 (w_h.toNat + 136)) with | .word w => w.toNat) ≤ 32
  rw [hm]; exact h136

theorem ph_wr_store (off : Nat) (src : ExpHOL 64)
    (hoff8 : off % 8 = 0) (hoff_fit : off + 8 ≤ 248) (hgt : off > 136)
    (hlen1 : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      PH_WR s → evalAt s src = some v → (flattenHOL v).length ≤ 1) :
    Hoare PH_WR
      (.store (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 off)]) src)
      (fun r t => r = none → PH_WR t) := by
  refine Hoare_store_fall (fun s x v mem' hP hx hv hst => ?_)
  have hlen := hlen1 s v hP hv
  obtain ⟨w_si, w_pl, w_h, w_txr, w_wr, S, Nd, hIA, hBs, hd_ic, hd_ht, hd_hw, hd_tw,
    hlsi, hlpl, hlh, hltxr, hlwr, hpl_eq, h136⟩ := hP
  have hx_eq := evalAt_add_local_const hlh hx
  have htr := store_in_tracked_block (base := w_h.toNat) (sz := 248) (off := off)
    hIA hBs (by simp)
    (fun c hc b hb => by simp only [List.mem_singleton] at hb; subst hb; exact hd_ic c hc _ (by simp))
    rfl hoff8 hx_eq (by omega) hst
  have hic := inputCells_eq_of_unhit hIA (fun c hc =>
    htr.2.2 c (fun _ => (hIA.2.2.1 c hc).2.1) (hd_ic c hc (w_h.toNat, 248) (by simp)))
  have hloc : locN s "si" = w_si.toNat := by simp [locN, hlsi]
  exact ⟨w_si, w_pl, w_h, w_txr, w_wr, S, Nd, htr.1, htr.2.1,
    by rw [hic.2.2]; exact hd_ic,
    hd_ht, hd_hw, hd_tw, hlsi, hlpl, hlh, hltxr, hlwr,
    by rw [hic.1]; exact hpl_eq,
    ph_h136_frame_after (by rwa [hloc]) hBs (by simp) hx_eq (by omega) hgt hst h136⟩

theorem ph_store_h192_wr :
    Hoare PH_WR
      (.store (.op .add [.var .local (ofString "h"), .const 192#64]) (.var .local (ofString "wr")))
      (fun r t => r = none → PH_WR t) := by
  apply ph_wr_store 192 _ (by omega) (by omega) (by omega)
  intro F s v ⟨_, _, _, _, w_wr, _, _, _, _, _, _, _, _, _, _, _, _, hl, _⟩ hv
  simp only [evalAt, evalHOLExact, hl, Option.some.injEq] at hv; subst v; simp [flattenHOL]

theorem ph_store_h200_pl112 :
    Hoare PH_WR
      (.store (.op .add [.var .local (ofString "h"), .const 200#64])
        (.load .one (.op .add [.var .local (ofString "pl"), .const 112#64])))
      (fun r t => r = none → PH_WR t) := by
  apply ph_wr_store 200 _ (by omega) (by omega) (by omega)
  intro F s v _ hv; exact evalAt_simple_word_len (Or.inr (Or.inr ⟨_, rfl⟩)) hv

theorem ph_store_h208_pl120 :
    Hoare PH_WR
      (.store (.op .add [.var .local (ofString "h"), .const 208#64])
        (.load .one (.op .add [.var .local (ofString "pl"), .const 120#64])))
      (fun r t => r = none → PH_WR t) := by
  apply ph_wr_store 208 _ (by omega) (by omega) (by omega)
  intro F s v _ hv; exact evalAt_simple_word_len (Or.inr (Or.inr ⟨_, rfl⟩)) hv

theorem ph_store_h216_si24 :
    Hoare PH_WR
      (.store (.op .add [.var .local (ofString "h"), .const 216#64])
        (.load .one (.op .add [.var .local (ofString "si"), .const 24#64])))
      (fun r t => r = none → PH_WR t) := by
  apply ph_wr_store 216 _ (by omega) (by omega) (by omega)
  intro F s v _ hv; exact evalAt_simple_word_len (Or.inr (Or.inr ⟨_, rfl⟩)) hv

theorem ph_store_h224_rh :
    Hoare PH_RH
      (.store (.op .add [.var .local (ofString "h"), .const 224#64]) (.var .local (ofString "rh")))
      (fun r t => r = none → PH_RH t) := by
  refine Hoare_store_fall (fun s x v mem' hP hx hv hst => ?_)
  obtain ⟨w_si, w_pl, w_h, w_txr, w_wr, w_rh, S, Nd, hIA, hBs, hd_ic, hd_ht, hd_hw, hd_tw, hd_hr,
    hlsi, hlpl, hlh, hltxr, hlwr, hlrh, hpl_eq, h136⟩ := hP
  have hx_eq := evalAt_add_local_const hlh hx
  have hv_eq : v = .val (.word w_rh) := by
    simp only [evalAt, evalHOLExact, hlrh, Option.some.injEq] at hv; exact hv.symm
  subst hv_eq
  have htr := store_in_tracked_block (base := w_h.toNat) (sz := 248) (off := 224)
    hIA hBs (by simp)
    (fun c hc b hb => by simp only [List.mem_singleton] at hb; subst hb; exact hd_ic c hc _ (by simp))
    rfl (by omega) hx_eq (by simp [flattenHOL]) hst
  have hic := inputCells_eq_of_unhit hIA (fun c hc =>
    htr.2.2 c (fun _ => (hIA.2.2.1 c hc).2.1) (hd_ic c hc (w_h.toNat, 248) (by simp)))
  have hloc : locN s "si" = w_si.toNat := by simp [locN, hlsi]
  exact ⟨w_si, w_pl, w_h, w_txr, w_wr, w_rh, S, Nd, htr.1, htr.2.1,
    by rw [hic.2.2]; exact hd_ic,
    hd_ht, hd_hw, hd_tw, hd_hr, hlsi, hlpl, hlh, hltxr, hlwr, hlrh,
    by rw [hic.1]; exact hpl_eq,
    ph_h136_frame_after (by rwa [hloc]) hBs (by simp) hx_eq (by simp [flattenHOL]) (by omega) hst h136⟩

theorem ph_bh_store (off : Nat) (src : ExpHOL 64)
    (hoff8 : off % 8 = 0) (hoff_fit : off + 8 ≤ 248) (hgt : off > 136)
    (hlen1 : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      PH_BH s → evalAt s src = some v → (flattenHOL v).length ≤ 1) :
    Hoare PH_BH
      (.store (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 off)]) src)
      (fun r t => r = none → PH_BH t) := by
  refine Hoare_store_fall (fun s x v mem' hP hx hv hst => ?_)
  have hlen := hlen1 s v hP hv
  obtain ⟨w_si, w_pl, w_h, w_txr, w_wr, w_rh, w_bh, S, Nd, hIA, hBs, hd_ic, hd_ht, hd_hw, hd_tw, hd_hr, hd_hb,
    hlsi, hlpl, hlh, hltxr, hlwr, hlrh, hlbh, hpl_eq, h136⟩ := hP
  have hx_eq := evalAt_add_local_const hlh hx
  have htr := store_in_tracked_block (base := w_h.toNat) (sz := 248) (off := off)
    hIA hBs (by simp)
    (fun c hc b hb => by simp only [List.mem_singleton] at hb; subst hb; exact hd_ic c hc _ (by simp))
    rfl hoff8 hx_eq (by omega) hst
  have hic := inputCells_eq_of_unhit hIA (fun c hc =>
    htr.2.2 c (fun _ => (hIA.2.2.1 c hc).2.1) (hd_ic c hc (w_h.toNat, 248) (by simp)))
  have hloc : locN s "si" = w_si.toNat := by simp [locN, hlsi]
  exact ⟨w_si, w_pl, w_h, w_txr, w_wr, w_rh, w_bh, S, Nd, htr.1, htr.2.1,
    by rw [hic.2.2]; exact hd_ic,
    hd_ht, hd_hw, hd_tw, hd_hr, hd_hb, hlsi, hlpl, hlh, hltxr, hlwr, hlrh, hlbh,
    by rw [hic.1]; exact hpl_eq,
    ph_h136_frame_after (by rwa [hloc]) hBs (by simp) hx_eq (by omega) hgt hst h136⟩

theorem ph_store_h232_bh :
    Hoare PH_BH
      (.store (.op .add [.var .local (ofString "h"), .const 232#64]) (.var .local (ofString "bh")))
      (fun r t => r = none → PH_BH t) := by
  apply ph_bh_store 232 _ (by omega) (by omega) (by omega)
  intro F s v ⟨_, _, _, _, _, _, w_bh, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hl, _⟩ hv
  simp only [evalAt, evalHOLExact, hl, Option.some.injEq] at hv; subst v; simp [flattenHOL]

theorem ph_store_h240_pl128 :
    Hoare PH_BH
      (.store (.op .add [.var .local (ofString "h"), .const 240#64])
        (.load .one (.op .add [.var .local (ofString "pl"), .const 128#64])))
      (fun r t => r = none → PH_BH t) := by
  apply ph_bh_store 240 _ (by omega) (by omega) (by omega)
  intro F s v _ hv; exact evalAt_simple_word_len (Or.inr (Or.inr ⟨_, rfl⟩)) hv

theorem ph_dec_nwd {body : ProgHOL 64} {K : Nat}
    (hbody : TerminatingProgBoundedOn PH_NWD body K) :
    TerminatingProgBoundedOn PH_BH
      (.dec (ofString "nwd") .one
        (.load .one (.op .add [.var .local (ofString "pl"), .const 56#64])) body) K := by
  refine dec_eval_on (P := PH_BH) (Q := PH_NWD) _ _ _ ?_ hbody
  intro F s v hP hev
  obtain ⟨w_si, w_pl, w_h, w_txr, w_wr, w_rh, w_bh, S, Nd, hIA, hBs, hd_ic,
    _, _, _, _, _, hlsi, hlpl, _, _, hlwr, _, _, hpl_eq, _⟩ := hP
  obtain ⟨_, w_nwd, _, rfl, _⟩ := evalAt_load_one_word hIA.1.1 hev
  refine ⟨w_si, w_pl, w_wr, w_nwd, S, Nd,
    (inputAtWith_with_locals s _ s.clock S Nd w_si.toNat).2 hIA,
    (allBlocksGood_with_locals s _ s.clock S Nd [(w_wr.toNat, 32)]).2 ?_,
    ?_, ?_, ?_, ?_, ?_, hpl_eq⟩
  · intro b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact hBs _ (by simp)
  · intro c hc b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact hd_ic c hc _ (by simp)
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "nwd" ≠ ofString "si" by decide, hlsi]
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "nwd" ≠ ofString "pl" by decide, hlpl]
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "nwd" ≠ ofString "wr" by decide, hlwr]
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

theorem ph_dec_i {body : ProgHOL 64} {K : Nat}
    (hbody : TerminatingProgBoundedOn PH_LOOP body K) :
    TerminatingProgBoundedOn PH_WDS0
      (.dec (ofString "i") .one (.const 0#64) body) K := by
  refine dec_eval_on (P := PH_WDS0) (Q := PH_LOOP) _ _ _ ?_ hbody
  intro F s v hP hev
  have hv : v = .val (.word 0#64) := by
    simpa only [evalAt, evalHOLExact, Option.some.injEq] using hev.symm
  subst v
  obtain ⟨w_si, w_pl, w_wr, w_nwd, w_wds, S, Nd, hIA, hBs, hd_ic, hd,
    hlsi, hlpl, hlwr, hlnwd, hgwds, hpl_eq⟩ := hP
  refine ⟨w_si, w_pl, w_wr, w_nwd, w_wds, 0#64, S, Nd,
    (inputAtWith_with_locals s _ s.clock S Nd w_si.toNat).2 hIA,
    (allBlocksGood_with_locals s _ s.clock S Nd _).2 hBs,
    hd_ic, hd, ?_, ?_, ?_, ?_, ?_, hgwds, hpl_eq, ?_, ?_⟩
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "si" by decide, hlsi]
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "pl" by decide, hlpl]
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "wr" by decide, hlwr]
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "nwd" by decide, hlnwd]
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · decide
  · simp

theorem ph_bl_check :
    Hoare PH_BH
      (.ite (.cmp .lower (.const 8388608#64) (.var .local (ofString "bl")))
        (.raise (ofString "BlockErr") (.const 7#64)) .skip)
      (fun r t => r = none → PH_BH t) :=
  Hoare.ite_raise_skip _ _ _

theorem ph_guestInv_tail
    (hreq : TerminatingFunBoundedOn GuestInv (ofString "encode_execution_requests") K.«encode_execution_requests»)
    (hhash : TerminatingFunBoundedOn GuestInv (ofString "compute_requests_hash") K.«compute_requests_hash»)
    (hkec : TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256»)
    (args : List (ExpHOL 64)) (hashArgs kecArgs : List (ExpHOL 64)) (ret : ExpHOL 64) :
    TerminatingProgBoundedOn GuestInv
      (.decCall (ofString "reqs") (.comb [.one, .one]) (ofString "encode_execution_requests") args
        (.seq (.call (some (none, none)) (ofString "compute_requests_hash") hashArgs)
          (.seq (.call (some (none, none)) (ofString "keccak256") kecArgs) (.return ret))))
      (K.«encode_execution_requests» + ((K.«compute_requests_hash» + 1) + (K.«keccak256» + 1 + 0)) + 1) := by
  exact TerminatingProgBoundedOn.decCall_guestInv hreq _ _ _
    (TerminatingProgBoundedOn.seq_guestInv
      (TerminatingProgBoundedOn.call_guestInv hhash _ _)
      (TerminatingProgBoundedOn.seq_guestInv
        (TerminatingProgBoundedOn.call_guestInv hkec _ _)
        (TerminatingProgBoundedOn.of_clock (fun s => clock_return s ret))))

def PH_WR_POST : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_si w_pl w_wr : BitVec 64, ∃ S Nd : List Nat,
    InputAtWith s S Nd w_si.toNat ∧
    AllBlocksGood s S Nd [(w_wr.toNat, 32)] ∧
    IvlsDisj (inputCells s w_si.toNat) [(w_wr.toNat, 32)] ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "wr") = some (.val (.word w_wr)) ∧
    w_pl.toNat = memW s w_si.toNat

theorem ph_build_mpt_txr
    (wmpt : WorldKeeps WorldOK
      (fun s => [(locN s "out", 32),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
                 (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "build_mpt_indexed")) :
    Hoare PH_BH
      (.call (some (none, none)) (ofString "build_mpt_indexed")
        [.load .one (.op .add [.var .local (ofString "pl"), .const 32#64]),
         .load .one (.op .add [.var .local (ofString "pl"), .const 40#64]),
         .var .local (ofString "txr")])
      (fun r t => r = none → PH_WR_POST t) := by
  classical
  refine ⟨fun {F} state hcode hP _ hr => ?_⟩
  set e1 : ExpHOL 64 := .load .one (.op .add [.var .local (ofString "pl"), .const 32#64])
  set e2 : ExpHOL 64 := .load .one (.op .add [.var .local (ofString "pl"), .const 40#64])
  set e3 : ExpHOL 64 := .var .local (ofString "txr")
  rcases hcall : evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "build_mpt_indexed") [e1, e2, e3]) with ⟨cres, cpost⟩
  have hr' : cres = none := by rw [hcall] at hr; exact hr
  subst hr'
  obtain ⟨w_si, w_pl, w_h, w_txr, w_wr, w_rh, w_bh, S, Nd, hIA, hBs, hd_ic,
    hd_ht, hd_hw, hd_tw, hd_hr, hd_hb,
    hlsi, hlpl, hlh, hltxr, hlwr, hlrh, hlbh, hpl_eq, h136⟩ := hP
  rw [evaluateHOLFiniteState_call] at hcall
  rcases hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) [e1, e2, e3] with _ | values
  · rw [hargs] at hcall; simp at hcall
  · rw [hargs] at hcall; dsimp only at hcall
    have hargs' : evalListHOLExact state.toExact [e1, e2, e3] = some values := by
      rwa [evalListHOLFinite_eq_toExact] at hargs
    rcases he1 : evalAt state e1 with _ | v1
    · simp [evalAt, evalListHOLExact, he1] at hargs'
    · rcases he2 : evalAt state e2 with _ | v2
      · simp [evalAt, evalListHOLExact, he1, he2] at hargs'
      · have he3 : evalAt state e3 = some (.val (.word w_txr)) := by
          simpa [e3, evalAt, evalHOLExact] using hltxr
        rcases hl : lookupCodeHOLFinite state.code.lookup (ofString "build_mpt_indexed") values with _ | ⟨body, callee, ret⟩
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
                  have hpc := callee_param_three state (ofString "build_mpt_indexed")
                    (ofString "slice_arr") (ofString "n") (ofString "out") .one .one .one _ _
                    (by rw [hcode]; exact R13PayloadStateInit.lookup_build_mpt_indexed_fn)
                    e1 e2 e3 v1 v2 (.val (.word w_txr)) values body callee ret he1 he2 he3 hargs hl
                  set entry := callEntryStateHOLFinite state callee
                  have hout : locN entry "out" = w_txr.toNat := by
                    simp [entry, locN, callEntryStateHOLFinite, hpc.2.2]
                  have hW_state : WorldOK state := ⟨hIA.1, S, (worldTyped_iff_with state S).2 ⟨Nd, hIA.2.1⟩⟩
                  have hstep := FunSpec.at_lookup wmpt state hcode values body callee ret hl
                    (localsFree_worldOK state callee (state.clock - 1) hW_state) (by rw [hb]; simp)
                  rw [hb] at hstep; dsimp only at hstep
                  have hws := hstep (Or.inl ⟨v, rfl⟩)
                  have hIA_entry : InputAtWith entry S Nd w_si.toNat :=
                    (inputAtWith_with_locals state callee (state.clock - 1) S Nd w_si.toNat).2 hIA
                  set bs_keep : List Ivl := [(w_wr.toNat, 32)]
                  have hBs_keep : AllBlocksGood entry S Nd bs_keep :=
                    (allBlocksGood_with_locals state callee (state.clock - 1) S Nd bs_keep).2
                      (fun b hb => by simp only [bs_keep, List.mem_singleton] at hb; subst hb; exact hBs _ (by simp))
                  have htxr_good := hBs (w_txr.toNat, 32) (by simp)
                  have hwr_good := hBs (w_wr.toNat, 32) (by simp)
                  have hRz : ∀ j ∈ [(locN entry "out", 32),
                      bufferRegion entry ("keccak_pad", 136),
                      bufferRegion entry ("keccak_st", 200),
                      bufferRegion entry ("mpt_hash_scratch", 40),
                      bufferRegion entry ("mpt_key_scratch", 16)], j.2 = 0 → j.1 % 8 = 0 := by
                    intro j hj
                    rcases List.mem_cons.1 hj with rfl | hj1
                    · intro _; rw [hout]; exact htxr_good.1
                    · rcases List.mem_cons.1 hj1 with rfl | hj2
                      · exact bufferRegion_zero_aligned entry "keccak_pad" 136 (by decide)
                      · rcases List.mem_cons.1 hj2 with rfl | hj3
                        · exact bufferRegion_zero_aligned entry "keccak_st" 200 (by decide)
                        · rcases List.mem_cons.1 hj3 with rfl | hj4
                          · exact bufferRegion_zero_aligned entry "mpt_hash_scratch" 40 (by decide)
                          · simp only [List.mem_singleton] at hj4; subst hj4
                            exact bufferRegion_zero_aligned entry "mpt_key_scratch" 16 (by decide)
                  obtain ⟨S2, Nd2, hIA_post2, hBs_keep2, _, hu_ic2, _⟩ :=
                    WorldStep_preserves_inputAndBlocks hIA_entry hBs_keep hws hRz
                      (fun j hj k hk => by
                        rcases List.mem_cons.1 hj with rfl | hj1
                        · rw [hout]; exact htxr_good.2.2.2.2 k (worldTypedIvls_sub_worldOwned _ _ _ k hk)
                        · rcases List.mem_cons.1 hj1 with rfl | hj2
                          · exact bufferRegion_disj_le hIA_entry.2.1 ("keccak_pad", 136) (by decide) (by decide) 136 le_rfl k hk
                          · rcases List.mem_cons.1 hj2 with rfl | hj3
                            · exact bufferRegion_disj_le hIA_entry.2.1 ("keccak_st", 200) (by decide) (by decide) 200 le_rfl k hk
                            · rcases List.mem_cons.1 hj3 with rfl | hj4
                              · exact bufferRegion_disj_le hIA_entry.2.1 ("mpt_hash_scratch", 40) (by decide) (by decide) 40 le_rfl k hk
                              · simp only [List.mem_singleton] at hj4; subst hj4
                                exact bufferRegion_disj_le hIA_entry.2.1 ("mpt_key_scratch", 16) (by decide) (by decide) 16 le_rfl k hk)
                      (fun c hc j hj => by
                        rcases List.mem_cons.1 hj with rfl | hj1
                        · rw [hout]; exact hd_ic c hc (w_txr.toNat, 32) (by simp)
                        · rcases List.mem_cons.1 hj1 with rfl | hj2
                          · exact hIA_entry.2.2.2.1 c hc _
                              (bufferRegion_mem_worldOwned entry S Nd (gn := ("keccak_pad", 136)) (by decide))
                          · rcases List.mem_cons.1 hj2 with rfl | hj3
                            · exact hIA_entry.2.2.2.1 c hc _
                                (bufferRegion_mem_worldOwned entry S Nd (gn := ("keccak_st", 200)) (by decide))
                            · rcases List.mem_cons.1 hj3 with rfl | hj4
                              · exact hIA_entry.2.2.2.1 c hc _
                                  (bufferRegion_mem_worldOwned entry S Nd (gn := ("mpt_hash_scratch", 40)) (by decide))
                              · simp only [List.mem_singleton] at hj4
                                subst hj4
                                exact hIA_entry.2.2.2.1 c hc _
                                  (bufferRegion_mem_worldOwned entry S Nd (gn := ("mpt_key_scratch", 16)) (by decide)))
                      (fun b hb j hj => by
                        simp only [bs_keep, List.mem_singleton] at hb; subst hb
                        rcases List.mem_cons.1 hj with rfl | hj1
                        · rw [hout]
                          rcases hd_tw with h0 | h0 | hle | hle
                          · exact Or.inr (Or.inl h0)
                          · exact Or.inl h0
                          · exact Or.inr (Or.inr (Or.inr hle))
                          · exact Or.inr (Or.inr (Or.inl hle))
                        · rcases List.mem_cons.1 hj1 with rfl | hj2
                          · exact hwr_good.2.2.2.2 _
                              (bufferRegion_mem_worldOwned entry S Nd (gn := ("keccak_pad", 136)) (by decide))
                          · rcases List.mem_cons.1 hj2 with rfl | hj3
                            · exact hwr_good.2.2.2.2 _
                                (bufferRegion_mem_worldOwned entry S Nd (gn := ("keccak_st", 200)) (by decide))
                            · rcases List.mem_cons.1 hj3 with rfl | hj4
                              · exact hwr_good.2.2.2.2 _
                                  (bufferRegion_mem_worldOwned entry S Nd (gn := ("mpt_hash_scratch", 40)) (by decide))
                              · simp only [List.mem_singleton] at hj4
                                subst hj4
                                exact hwr_good.2.2.2.2 _
                                  (bufferRegion_mem_worldOwned entry S Nd (gn := ("mpt_key_scratch", 16)) (by decide)))
                  have hic := inputCells_eq_of_unhit hIA hu_ic2
                  set resumed := { post with locals := state.locals }
                  have hRes : PH_WR_POST resumed := by
                    refine ⟨w_si, w_pl, w_wr, S2, Nd2,
                      (inputAtWith_with_locals post state.locals post.clock S2 Nd2 w_si.toNat).2 hIA_post2,
                      (allBlocksGood_with_locals post state.locals post.clock S2 Nd2 [(w_wr.toNat, 32)]).2 hBs_keep2,
                      ?_, hlsi, hlpl, hlwr,
                      by change w_pl.toNat = memW post w_si.toNat; rw [hic.1]; exact hpl_eq⟩
                    change IvlsDisj (inputCells post w_si.toNat) [(w_wr.toNat, 32)]
                    rw [hic.2.2]
                    intro c hc b hb
                    simp only [List.mem_singleton] at hb; subst hb
                    exact hd_ic c hc _ (by simp)
                  rwa [hpost_eq] at hRes
                · simp at hcall
              | _ => simp [emptyLocalsHOLFinite] at hcall

theorem ph_dec_nwd_post {body : ProgHOL 64} {K : Nat}
    (hbody : TerminatingProgBoundedOn PH_NWD body K) :
    TerminatingProgBoundedOn PH_WR_POST
      (.dec (ofString "nwd") .one
        (.load .one (.op .add [.var .local (ofString "pl"), .const 56#64])) body) K := by
  refine dec_eval_on (P := PH_WR_POST) (Q := PH_NWD) _ _ _ ?_ hbody
  intro F s v hP hev
  obtain ⟨w_si, w_pl, w_wr, S, Nd, hIA, hBs, hd_ic, hlsi, hlpl, hlwr, hpl_eq⟩ := hP
  obtain ⟨_, w_nwd, _, rfl, _⟩ := evalAt_load_one_word hIA.1.1 hev
  refine ⟨w_si, w_pl, w_wr, w_nwd, S, Nd,
    (inputAtWith_with_locals s _ s.clock S Nd w_si.toNat).2 hIA,
    (allBlocksGood_with_locals s _ s.clock S Nd [(w_wr.toNat, 32)]).2 hBs,
    hd_ic, ?_, ?_, ?_, ?_, hpl_eq⟩
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "nwd" ≠ ofString "si" by decide, hlsi]
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "nwd" ≠ ofString "pl" by decide, hlpl]
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "nwd" ≠ ofString "wr" by decide, hlwr]
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

theorem ph_loop_worldOK {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hP : PH_LOOP s) : WorldOK s := by
  obtain ⟨_, _, _, _, _, _, S, Nd, hIA, _⟩ := hP
  exact ⟨hIA.1, S, (worldTyped_iff_with s S).2 ⟨Nd, hIA.2.1⟩⟩

theorem ph_second_mpt_tail
    (hmpt : TerminatingFunBoundedOn WorldOK (ofString "build_mpt_indexed") K.«build_mpt_indexed»)
    {tail : ProgHOL 64} {B : Nat}
    (htail : TerminatingProgBoundedOn GuestInv tail B) :
    TerminatingProgBoundedOn PH_LOOP
      (.seq (.call (some (none, none)) (ofString "build_mpt_indexed")
        [.var .global (ofString "wd_rlp_slices"), .var .local (ofString "nwd"),
         .var .local (ofString "wr")]) tail)
      (K.«build_mpt_indexed» + 1 + B) := by
  exact TerminatingProgBoundedOn.seq_guestInv_after
    (TerminatingProgBoundedOn.call_on hmpt _ _
      (callEntryOn_of_imp localsFree_worldOK ph_loop_worldOK _ _))
    (fun s hP => (ph_loop_worldOK s hP).1.1) htail

theorem ph_alloc_wd_rlp_slices
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc")) :
    Hoare PH_NWD
      (.call (some (some (.global, ofString "wd_rlp_slices"), none)) (ofString "alloc")
        [.op .add [.panop .mul [.var .local (ofString "nwd"), .const 16#64], .const 16#64]])
      (fun r t => r = none → PH_WDS0 t) := by
  classical
  refine ⟨fun {F} state hcode hP _ hr => ?_⟩
  set e_sz : ExpHOL 64 :=
    .op .add [.panop .mul [.var .local (ofString "nwd"), .const 16#64], .const 16#64]
  rcases hcall : evaluateHOLFiniteState state
      (.call (some (some (.global, ofString "wd_rlp_slices"), none)) (ofString "alloc") [e_sz])
    with ⟨cres, cpost⟩
  have hr' : cres = none := by rw [hcall] at hr; exact hr
  subst hr'
  obtain ⟨w_si, w_pl, w_wr, w_nwd, S, Nd, hIA, hBs, hd_ic, hlsi, hlpl, hlwr, hlnwd, hpl_eq⟩ := hP
  have hAs := hIA.1
  have hW_state : WorldOK state := ⟨hAs, S, (worldTyped_iff_with state S).2 ⟨Nd, hIA.2.1⟩⟩
  set w_sz : BitVec 64 := w_nwd * 16#64 + 16#64
  have he_sz : evalAt state e_sz = some (.val (.word w_sz)) := by
    simp [e_sz, w_sz, evalAt, evalHOLExact, evalListHOLExact, hlnwd, valueIsWord, valueWord,
      panOpHOL, wordOpHOL, wordOp]
  have hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) [e_sz] =
      some [.val (.word w_sz)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp only [evalListHOLExact]
    have he := he_sz
    unfold evalAt at he
    rw [he]
  rw [evaluateHOLFiniteState_call, hargs] at hcall
  dsimp only at hcall
  rcases hl : lookupCodeHOLFinite state.code.lookup (ofString "alloc") [.val (.word w_sz)]
    with _ | ⟨body, callee, ret⟩
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
        | returned value =>
          dsimp only at hcall
          split_ifs at hcall with hsh hv
          · obtain ⟨_, hpost_eq⟩ := Prod.mk.inj hcall
            have hpc := callee_param_one_exp state (ofString "alloc") (ofString "n") .one _ _
              (by rw [hcode]; exact R13PayloadStateInit.lookup_alloc_fn) e_sz
              (.val (.word w_sz)) [.val (.word w_sz)] body callee ret he_sz hargs hl
            have hn_loc : locN (callEntryStateHOLFinite state callee) "n" = w_sz.toNat := by
              simp [locN, callEntryStateHOLFinite, hpc.2]
            have hsz8 : w_sz.toNat % 8 = 0 := by
              have h16 : (16#64 : BitVec 64).toNat = 16 := by decide
              have h264 : (2 ^ 64) % 8 = 0 := by decide
              rw [show w_sz = w_nwd * 16#64 + 16#64 from rfl, BitVec.toNat_add, BitVec.toNat_mul, h16]
              omega
            have hround : (w_sz.toNat + 7) / 8 * 8 = w_sz.toNat := by omega
            have hstep := FunSpec.at_lookup wal state hcode [.val (.word w_sz)] body callee ret hl
              (localsFree_worldOK state callee (state.clock - 1) hW_state) (by rw [hb]; simp)
            rw [hb] at hstep; dsimp only at hstep
            have hws := hstep (Or.inl ⟨value, rfl⟩)
            have hrt := FunSpec.at_lookup rtal state hcode [.val (.word w_sz)] body callee ret hl
              (localsFree_arenaReady state callee (state.clock - 1) hAs) (by rw [hb]; simp)
            rw [hb] at hrt; dsimp only at hrt
            obtain ⟨w_wds, rfl, _, _, hfb⟩ := hrt value rfl
            rw [hn_loc] at hfb
            have hfb_in : Inside (w_wds.toNat, w_sz.toNat) (globN state "heap_ptr") (globN post "heap_ptr") := by
              have := hfb.2.1; rwa [hround] at this
            have hfb_w : WordsOK post (w_wds.toNat, w_sz.toNat) := by
              have := hfb.2.2; rwa [hround] at this
            have hIA_entry : InputAtWith (callEntryStateHOLFinite state callee) S Nd w_si.toNat :=
              (inputAtWith_with_locals state callee (state.clock - 1) S Nd w_si.toNat).2 hIA
            have hBs_entry : AllBlocksGood (callEntryStateHOLFinite state callee) S Nd [(w_wr.toNat, 32)] :=
              (allBlocksGood_with_locals state callee (state.clock - 1) S Nd [(w_wr.toNat, 32)]).2 hBs
            obtain ⟨S', Nd', hIA_post, hBs_post, _, hu_ic, hQ⟩ :=
              WorldStep_preserves_inputAndBlocks hIA_entry hBs_entry hws
                (fun _ hj => by simp at hj) (fun _ hj => by simp at hj)
                (fun _ _ _ hj => by simp at hj) (fun _ _ _ hj => by simp at hj)
            obtain ⟨w_wds', hw_eq, hav⟩ := hQ (.val (.word w_wds)) rfl
            injection hw_eq with hw_eq'; injection hw_eq' with hw_eq''; subst hw_eq''
            dsimp only at hav; rw [hn_loc, hround] at hav
            have hic := inputCells_eq_of_unhit hIA hu_ic
            set mid := { post with locals := state.locals }
            have hIA_mid : InputAtWith mid S' Nd' w_si.toNat :=
              (inputAtWith_with_locals post state.locals post.clock S' Nd' w_si.toNat).2 hIA_post
            have hug := worldTypedWith_setGlobal_untracked (s := mid)
              (gname := ofString "wd_rlp_slices") (w := w_wds) (S := S') (Nd := Nd')
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              hIA_mid.1 hIA_mid.2.1
            set resumed := setGlobalHOLFinite (ofString "wd_rlp_slices") (.val (.word w_wds)) mid
            have hhp_eq : globN resumed "heap_ptr" = globN post "heap_ptr" := by
              simp [resumed, mid, globN, setGlobalHOLFinite, HolFiniteMapExact.update, FUPDATE,
                show ofString "wd_rlp_slices" ≠ ofString "heap_ptr" by decide]
            have hIA_res : InputAtWith resumed S' Nd' w_si.toNat := by
              refine ⟨hug.1, hug.2.1, hIA_mid.2.2.1, ?_, hIA_mid.2.2.2.2⟩
              change IvlsDisj (inputCells post w_si.toNat) (worldOwned resumed S' Nd')
              rw [hug.2.2]; exact hIA_post.2.2.2.1
            have hBs_res : AllBlocksGood resumed S' Nd' [(w_wr.toNat, 32), (w_wds.toNat, w_sz.toNat)] := by
              intro b hb
              rcases List.mem_cons.1 hb with rfl | hb1
              · have hbg := hBs_post (w_wr.toNat, 32) (by simp)
                refine ⟨hbg.1, hbg.2.1, ?_, hbg.2.2.2.1, ?_⟩
                · rw [hhp_eq]; exact hbg.2.2.1
                · rw [hug.2.2]; exact hbg.2.2.2.2
              · simp only [List.mem_singleton] at hb1; subst hb1
                refine ⟨hfb.1, hsz8, ?_, hfb_w, ?_⟩
                · rw [hhp_eq]; exact ⟨Nat.le_trans hAs.2.1 hfb_in.1, hfb_in.2⟩
                · rw [hug.2.2]; exact fun o ho => hav (w_wds.toNat, w_sz.toNat) (by simp) o ho
            have hd_ic_res : IvlsDisj (inputCells resumed w_si.toNat) [(w_wr.toNat, 32), (w_wds.toNat, w_sz.toNat)] := by
              change IvlsDisj (inputCells post w_si.toNat) [(w_wr.toNat, 32), (w_wds.toNat, w_sz.toNat)]
              rw [hic.2.2]
              intro c hc b hb
              rcases List.mem_cons.1 hb with rfl | hb1
              · exact hd_ic c hc _ (by simp)
              · simp only [List.mem_singleton] at hb1; subst hb1
                exact Or.inr (Or.inr (Or.inl (Nat.le_trans (hIA.2.2.1 c hc).1.2 hfb_in.1)))
            have hd_wr_wds : Disj (w_wr.toNat, 32) (w_wds.toNat, w_sz.toNat) :=
              Or.inr (Or.inr (Or.inl (Nat.le_trans (hBs (w_wr.toNat, 32) (by simp)).2.2.1.2 hfb_in.1)))
            have hRes : PH_WDS0 resumed := by
              refine ⟨w_si, w_pl, w_wr, w_nwd, w_wds, S', Nd', hIA_res, hBs_res, hd_ic_res, hd_wr_wds,
                hlsi, hlpl, hlwr, hlnwd, ?_,
                by change w_pl.toNat = memW post w_si.toNat; rw [hic.1]; exact hpl_eq⟩
              simp [resumed, setGlobalHOLFinite, HolFiniteMapExact.update, FUPDATE]
            show PH_WDS0 cpost
            rw [← hpost_eq]
            exact hRes
          · simp at hcall
          · simp at hcall
        | _ => simp [emptyLocalsHOLFinite] at hcall

def ph_withdrawal_store (idx : Nat) : ProgHOL 64 :=
  .store
    (.op .add
      (if idx = 0 then
        [.var .global (ofString "wd_rlp_slices"),
         .panop .mul [.var .local (ofString "i"), .const 16#64]]
      else
        [.var .global (ofString "wd_rlp_slices"),
         .panop .mul [.var .local (ofString "i"), .const 16#64], .const 8#64]))
    (.rfield idx (.var .local (ofString "e")))

def ph_withdrawal_increment : ProgHOL 64 :=
  .assign .local (ofString "i")
    (.op .add [.var .local (ofString "i"), .const 1#64])

def ph_withdrawal_args : List (ExpHOL 64) :=
  [.op .add
    [.load .one (.op .add [.var .local (ofString "pl"), .const 48#64]),
     .panop .mul [.var .local (ofString "i"), .const 44#64]]]

def ph_withdrawal_body : ProgHOL 64 :=
  .decCall (ofString "e") (.comb [.one, .one]) (ofString "encode_withdrawal_rlp")
    ph_withdrawal_args
    (.seq (ph_withdrawal_store 0)
      (.seq (ph_withdrawal_store 1) ph_withdrawal_increment))

def ph_withdrawal_loop : ProgHOL 64 :=
  .while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nwd")))
    ph_withdrawal_body

theorem ph_withdrawal_body_bound
    (henc : TerminatingFunBoundedOn GuestInv (ofString "encode_withdrawal_rlp") K.«encode_withdrawal_rlp») :
    TerminatingProgBoundedOn GuestInv ph_withdrawal_body (K.«encode_withdrawal_rlp» + 1) := by
  unfold ph_withdrawal_body ph_withdrawal_store ph_withdrawal_increment
  exact TerminatingProgBoundedOn.decCall_guestInv henc _ _ _
    (TerminatingProgBoundedOn.seq_guestInv
      (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
      (TerminatingProgBoundedOn.seq_guestInv
        (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
        (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))))

theorem ph_withdrawal_body_counter : StepsCounter (ofString "i") ph_withdrawal_body := by
  unfold ph_withdrawal_body ph_withdrawal_store ph_withdrawal_increment
  exact StepsCounter.decCall_ne (by decide) _ _
    (StepsCounter.seq_keep (PreservesCounter.store _ _ _)
      (StepsCounter.seq_keep (PreservesCounter.store _ _ _) (StepsCounter.assign_inc _)))

theorem ph_withdrawal_loop_bound
    (henc : TerminatingFunBoundedOn GuestInv (ofString "encode_withdrawal_rlp") K.«encode_withdrawal_rlp») :
    TerminatingProgBoundedOn GuestInv ph_withdrawal_loop
      ((2 ^ 64 + 1) * ((K.«encode_withdrawal_rlp» + 1) + 1)) := by
  unfold ph_withdrawal_loop
  apply while_signed_up_on
  · intro F s hG
    exact localsFree_guestInv s s.locals (s.clock - 1) hG
  · exact ph_withdrawal_body_bound henc
  · exact ⟨fun s _ hP _ _ => guestInv_evaluate s ph_withdrawal_body hP.1⟩
  · rfl
  · exact ph_withdrawal_body_counter

theorem ph_loop_decClock {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hP : PH_LOOP s) : PH_LOOP (decClockHOLFinite s) := by
  obtain ⟨w_si, w_pl, w_wr, w_nwd, w_wds, w_i, S, Nd, hIA, hBs, hd_ic, hd,
    hlsi, hlpl, hlwr, hlnwd, hli, hgwds, hpl_eq, hi0, hib⟩ := hP
  exact ⟨w_si, w_pl, w_wr, w_nwd, w_wds, w_i, S, Nd,
    (inputAtWith_with_locals s s.locals (s.clock - 1) S Nd w_si.toNat).2 hIA,
    (allBlocksGood_with_locals s s.locals (s.clock - 1) S Nd _).2 hBs,
    hd_ic, hd, hlsi, hlpl, hlwr, hlnwd, hli, hgwds, hpl_eq, hi0, hib⟩

theorem ph_withdrawal_loop_frame :
    Hoare
      (fun s => PH_LOOP s ∧ CondTrue
        (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nwd"))) s)
      ph_withdrawal_body (fun r t => r = none → PH_LOOP t) →
    Hoare PH_LOOP ph_withdrawal_loop (fun r t => r = none → PH_LOOP t) := by
  intro hbody
  exact Hoare.while_preserve_ncb ph_loop_decClock rfl hbody

theorem ph_withdrawal_loop_tail
    (henc : TerminatingFunBoundedOn GuestInv (ofString "encode_withdrawal_rlp") K.«encode_withdrawal_rlp»)
    (hmpt : TerminatingFunBoundedOn WorldOK (ofString "build_mpt_indexed") K.«build_mpt_indexed»)
    {tail : ProgHOL 64} {B : Nat}
    (htail : TerminatingProgBoundedOn GuestInv tail B) :
    Hoare PH_LOOP ph_withdrawal_loop (fun r t => r = none → PH_LOOP t) →
    TerminatingProgBoundedOn PH_LOOP
      (.seq ph_withdrawal_loop
        (.seq (.call (some (none, none)) (ofString "build_mpt_indexed")
          [.var .global (ofString "wd_rlp_slices"), .var .local (ofString "nwd"),
           .var .local (ofString "wr")]) tail))
      ((2 ^ 64 + 1) * ((K.«encode_withdrawal_rlp» + 1) + 1) +
        (K.«build_mpt_indexed» + 1 + B)) := by
  intro hframe
  have hbound : TerminatingProgBoundedOn PH_LOOP ph_withdrawal_loop
      ((2 ^ 64 + 1) * ((K.«encode_withdrawal_rlp» + 1) + 1)) := by
    intro F s hc hP hnt
    exact ph_withdrawal_loop_bound henc s hc (ph_loop_guestInv hP) hnt
  intro F s hc hP hnt
  exact TerminatingProgBoundedOn.seq_hoare_trans hbound hframe
    (ph_second_mpt_tail hmpt htail) s hc hP hnt

theorem ph_withdrawal_address_nowrap (base i : BitVec 64)
    (hprev : 0 < i.toNat → base.toNat < heapEnd ∧ 44 * (i.toNat - 1) < heapEnd) :
    (base + i * 44#64).toNat = base.toNat + 44 * i.toNat := by
  have hsum : base.toNat + 44 * i.toNat < 2 ^ 64 := by
    by_cases hz : i.toNat = 0
    · simpa [hz] using base.isLt
    · obtain ⟨hb, hi⟩ := hprev (by omega)
      have he : 2 * heapEnd + 44 < 2 ^ 64 := by decide
      omega
  have hmul : i.toNat * 44 < 2 ^ 64 := by omega
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hmul, Nat.mul_comm i.toNat 44, Nat.mod_eq_of_lt hsum]

theorem ph_withdrawal_domain_progress (base i : BitVec 64)
    (hprev : 0 < i.toNat → base.toNat < heapEnd ∧ 44 * (i.toNat - 1) < heapEnd)
    (hdom : Inside ((base + i * 44#64).toNat, 1) sourceBase heapEnd) :
    base.toNat < heapEnd ∧ 44 * i.toNat < heapEnd := by
  have haddr := ph_withdrawal_address_nowrap base i hprev
  obtain ⟨_, hend⟩ := hdom
  dsimp only at hend
  rw [haddr] at hend
  omega

theorem ph_slice_offset_bounds (nwd i : BitVec 64)
    (hi0 : 0 ≤ i.toInt) (hilt : i.toInt < nwd.toInt)
    (hnwd : 44 * nwd.toNat ≤ heapEnd + 44) :
    (i * 16#64).toNat = 16 * i.toNat ∧
    (i * 16#64 + 8#64).toNat = 16 * i.toNat + 8 ∧
    16 * i.toNat + 16 ≤ (nwd * 16#64 + 16#64).toNat := by
  have he : heapEnd < 2 ^ 40 := by decide
  have hbi := i.isLt
  have hbn := nwd.isLt
  have hlt_nat : i.toNat < nwd.toNat := by
    have hn0 : 0 ≤ nwd.toInt := by omega
    have hi_int := BitVec.toInt_eq_msb_cond i
    have hn_int := BitVec.toInt_eq_msb_cond nwd
    rw [BitVec.msb_eq_decide] at hi_int hn_int
    split_ifs at hi_int hn_int <;> omega
  have hn_small : nwd.toNat * 16 + 16 < 2 ^ 64 := by omega
  have hi_small : i.toNat * 16 + 8 < 2 ^ 64 := by omega
  have hi_mul : i.toNat * 16 < 2 ^ 64 := by omega
  have hn_mul : nwd.toNat * 16 < 2 ^ 64 := by omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt hi_mul, Nat.mul_comm]
  · simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt hi_mul, Nat.mod_eq_of_lt hi_small, Nat.mul_comm]
  · simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt hn_mul, Nat.mod_eq_of_lt hn_small]
    omega

theorem ph_withdrawal_count_at_exit (nwd i : BitVec 64)
    (hi0 : 0 ≤ i.toInt) (hn0 : 0 ≤ nwd.toInt)
    (hexit : nwd.toInt ≤ i.toInt)
    (hprev : 0 < i.toNat → 44 * (i.toNat - 1) < heapEnd) :
    44 * nwd.toNat ≤ heapEnd + 44 := by
  have hi_int := BitVec.toInt_eq_msb_cond i
  have hn_int := BitVec.toInt_eq_msb_cond nwd
  rw [BitVec.msb_eq_decide] at hi_int hn_int
  have hle : nwd.toNat ≤ i.toNat := by
    split_ifs at hi_int hn_int <;> omega
  by_cases hz : i.toNat = 0
  · have hnz : nwd.toNat = 0 := by omega
    simp [hnz]
  · have hp := hprev (by omega)
    omega

theorem ph_lookup_rlp_word_encoded_len :
    originalRuntimeCode.lookup (ofString "rlp_word_encoded_len") =
      some ([(ofString "w", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_word_encoded_len, .one) :=
  lookup_of_guestAst_getElem 127 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_word_encoded_len) rfl

theorem ph_lookup_withdrawal_rlp_len :
    originalRuntimeCode.lookup (ofString "withdrawal_rlp_len") =
      some ([(ofString "wd", .one)],
        sourceFnBody Guest.Software.guestFn_withdrawal_rlp_len, .one) :=
  lookup_of_guestAst_getElem 837 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_withdrawal_rlp_len) rfl

theorem ph_frame_rlp_be_len : M13.FunLocFrame (ofString "rlp_be_len") :=
  M13.funLocFrame_of_locOnlyW 118 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_be_len rfl rfl

theorem ph_frame_rlp_header_len : M13.FunLocFrame (ofString "rlp_header_len") := by
  refine ⟨_, _, _, WkBlockTxEnc.lookup_rlp_header_len, fun s hcode => ?_⟩
  have hb : sourceFnBody Guest.Software.guestFn_rlp_header_len =
      .seq (.ite (.cmp .notLower (.const 55) (.var .local (ofString "n")))
        (.return (.const 1)) .skip)
        (.decCall (ofString "ll") .one (ofString "rlp_be_len")
          [.var .local (ofString "n")]
          (.return (.op .add [.const 1, .var .local (ofString "ll")]))) := rfl
  rw [hb]
  apply M13.locFrame_seq
  · exact M13.locFrameW_eval _ rfl s
  · intro m hm
    exact M13.locFrame_decCall (hm.code.trans hcode) ph_frame_rlp_be_len _ _ _
      (fun t _ => M13.locFrameW_eval _ rfl t)

theorem ph_frame_rlp_list_header_len : M13.FunLocFrame (ofString "rlp_list_header_len") := by
  refine ⟨_, _, _, WkBlockTxEnc.lookup_rlp_list_header_len, fun s hcode => ?_⟩
  have hb : sourceFnBody Guest.Software.guestFn_rlp_list_header_len =
      .call none (ofString "rlp_header_len") [.var .local (ofString "payload_len")] := rfl
  rw [hb]
  exact M13.locFrame_tailCall hcode ph_frame_rlp_header_len _

theorem ph_frame_rlp_word_encoded_len : M13.FunLocFrame (ofString "rlp_word_encoded_len") := by
  refine ⟨_, _, _, ph_lookup_rlp_word_encoded_len, fun s hcode => ?_⟩
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_word_encoded_len,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply M13.locFrame_seq
  · exact M13.locFrameW_eval _ rfl s
  · intro m hm
    exact M13.locFrame_decCall (hm.code.trans hcode) ph_frame_rlp_be_len _ _ _
      (fun t _ => M13.locFrameW_eval _ rfl t)

theorem ph_frame_withdrawal_rlp_len : M13.FunLocFrame (ofString "withdrawal_rlp_len") := by
  refine ⟨_, _, _, ph_lookup_withdrawal_rlp_len, fun s hcode => ?_⟩
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_withdrawal_rlp_len,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply M13.locFrame_decCall hcode ph_frame_rlp_word_encoded_len _ _ _
  intro t1 hc1
  apply M13.locFrame_decCall hc1 ph_frame_rlp_word_encoded_len _ _ _
  intro t2 hc2
  apply M13.locFrame_decCall hc2 ph_frame_rlp_word_encoded_len _ _ _
  intro t3 hc3
  apply M13.locFrame_dec
  intro _
  apply M13.locFrame_decCall (by exact hc3) ph_frame_rlp_list_header_len _ _ _
  intro t4 _
  exact M13.locFrameW_eval _ rfl t4

theorem ph_lookup_rlp_bytes_encoded_len :
    originalRuntimeCode.lookup (ofString "rlp_bytes_encoded_len") =
      some ([(ofString "first_byte", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len, .one) :=
  lookup_of_guestAst_getElem 125 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_bytes_encoded_len) rfl

theorem ph_frame_rlp_bytes_encoded_len : M13.FunLocFrame (ofString "rlp_bytes_encoded_len") := by
  refine ⟨_, _, _, ph_lookup_rlp_bytes_encoded_len, fun s hcode => ?_⟩
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_bytes_encoded_len,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply M13.locFrame_seq
  · exact M13.locFrameW_eval _ rfl s
  · intro m hm
    exact M13.locFrame_decCall (hm.code.trans hcode) ph_frame_rlp_header_len _ _ _
      (fun t _ => M13.locFrameW_eval _ rfl t)

def ph_blockRlpTail : ProgHOL 64 :=
  match (sourceFunctionEntry Guest.Software.guestFn_block_rlp_length).2.2.1 with
  | .decCall _ _ _ _ (.decCall _ _ _ _ (.seq _ tail)) => tail
  | p => p

theorem ph_frame_blockRlpTail {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) :
    M13.LocFrame s (evaluateHOLFiniteState s ph_blockRlpTail).2 := by
  dsimp only [ph_blockRlpTail, sourceFunctionEntry, Guest.Software.guestFn_block_rlp_length,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply M13.locFrame_dec; intro _
  apply M13.locFrame_dec; intro _
  apply M13.locFrame_dec; intro _
  apply M13.locFrame_dec; intro _
  apply M13.locFrame_dec; intro _
  apply M13.locFrame_seq
  · refine M13.locFrame_while _ ?_ _ (by exact hcode)
    intro t htc
    apply M13.locFrame_dec; intro _
    apply M13.locFrame_dec; intro _
    apply M13.locFrame_seq
    · exact M13.locFrameW_eval _ rfl _
    · intro m1 hm1
      have hc1 : m1.code = originalRuntimeCode := hm1.code.trans htc
      apply M13.locFrame_dec; intro _
      apply M13.locFrame_seq
      · apply M13.locFrame_ite
        · exact M13.locFrame_call_local (by exact hc1) ph_frame_rlp_bytes_encoded_len (some (.local, ofString "el"))
            (fun _ _ h => by cases h; rfl) _
        · exact M13.locFrameW_eval _ rfl _
      · intro m2 _
        exact M13.locFrameW_eval _ rfl m2
  · intro m3 hm3
    have hc3 : m3.code = originalRuntimeCode := hm3.code.trans (by exact hcode)
    apply M13.locFrame_decCall hc3 ph_frame_rlp_list_header_len _ _ _
    intro t4 hc4
    apply M13.locFrame_seq
    · exact M13.locFrameW_eval _ rfl t4
    · intro m4 hm4
      have hc4' : m4.code = originalRuntimeCode := hm4.code.trans hc4
      apply M13.locFrame_seq
      · exact M13.locFrameW_eval _ rfl m4
      · intro m5 hm5
        have hc5 : m5.code = originalRuntimeCode := hm5.code.trans hc4'
        apply M13.locFrame_dec; intro _
        apply M13.locFrame_dec; intro _
        apply M13.locFrame_seq
        · exact M13.locFrameW_eval _ rfl _
        · intro m6 hm6
          have hc6 : m6.code = originalRuntimeCode := hm6.code.trans (by exact hc5)
          apply M13.locFrame_seq
          · refine M13.locFrame_while _ ?_ m6 hc6
            intro tw htw
            apply M13.locFrame_decCall htw ph_frame_withdrawal_rlp_len _ _ _
            intro tw2 _
            exact M13.locFrameW_eval _ rfl tw2
          · intro m7 hm7
            have hc7 := hm7.code.trans hc6
            apply M13.locFrame_seq
            · exact M13.locFrame_call_local hc7 ph_frame_rlp_list_header_len (some (.local, ofString "hl"))
                (fun _ _ h => by cases h; rfl) _
            · intro m8 hm8
              have hc8 := hm8.code.trans hc7
              apply M13.locFrame_seq
              · exact M13.locFrameW_eval _ rfl m8
              · intro m9 hm9
                have hc9 := hm9.code.trans hc8
                apply M13.locFrame_seq
                · exact M13.locFrame_call_local hc9 ph_frame_rlp_list_header_len (some (.local, ofString "hl"))
                    (fun _ _ h => by cases h; rfl) _
                · intro m10 _
                  exact M13.locFrameW_eval _ rfl m10

theorem ph_eval_withdrawal_head_domain {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hG : GuestInv s) (es : List (ExpHOL 64)) (v : ValueHOL 64)
    (he : evalAt s (.op .or (.loadByte (.var .local (ofString "wd")) :: es)) = some v) :
    sourceBase ≤ locN s "wd" ∧ locN s "wd" < heapEnd := by
  have hhead : ∃ v1, evalAt s (.loadByte (.var .local (ofString "wd"))) = some v1 := by
    rcases h1 : evalAt s (.loadByte (.var .local (ofString "wd"))) with _ | v1
    · simp only [evalAt, evalHOLExact, evalListHOLExact] at h1 he
      rw [h1] at he
      cases he
    · exact ⟨v1, rfl⟩
  obtain ⟨v1, hv1⟩ := hhead
  simp only [evalAt, evalHOLExact] at hv1
  rcases hl : s.locals.lookup (ofString "wd") with _ | lv
  · simp [hl] at hv1
  · simp only [hl] at hv1
    rcases lv with x | _ | _
    · cases x with
      | word w =>
        simp only [panMemLoadByteHOL] at hv1
        have hdom : s.memaddrs (panByteAlignHOL w) := by
          by_contra hc
          simp [hc] at hv1
        rw [hG.memaddrs, WkBlockTxEnc.ordinaryDomain_iff] at hdom
        have ha : (panByteAlignHOL (width := 64) w).toNat = w.toNat / 8 * 8 := by
          have h8 : 2 ^ Nat.log2 (64 / 8) = 8 := by decide
          simp only [panByteAlignHOL, h8, BitVec.toNat_ofNat]
          have hw := w.isLt
          exact Nat.mod_eq_of_lt (by omega)
        have hloc : locN s "wd" = w.toNat := by simp [locN, hl]
        have hhe : heapEnd = 33806089704 := by decide
        have hsb : sourceBase = 2701131776 := by decide
        rw [hloc]
        omega
    · simp at hv1
    · simp at hv1

theorem ph_withdrawal_rlp_len_resumes_domain {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (hG : GuestInv s)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_withdrawal_rlp_len)).1) :
    sourceBase ≤ locN s "wd" ∧ locN s "wd" < heapEnd := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_withdrawal_rlp_len,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hres
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hres
  rcases ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) _ with _ | vs
  · rw [ha] at hres; exact False.elim (WkBlockTxEnc.not_resumes_error hres)
  · unfold evalListHOLFinite at ha
    dsimp only [evalListHOLExact] at ha
    rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) _ with _ | v
    · rw [hev] at ha; cases ha
    · exact ph_eval_withdrawal_head_domain s hG _ v hev

def ph_noReturnProg : ProgHOL 64 → Bool
  | .seq a b | .ite _ a b => ph_noReturnProg a && ph_noReturnProg b
  | .while _ a => ph_noReturnProg a
  | .dec _ _ _ a => ph_noReturnProg a
  | .decCall _ _ _ _ a => ph_noReturnProg a
  | .call (some (_, none)) _ _ => true
  | .assign _ _ _ | .store _ _ | .storeByte _ _ | .skip => true
  | _ => false

theorem ph_eval_noReturnProg {F : Type} (p : ProgHOL 64) (hp : ph_noReturnProg p = true)
    (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s p).1 ≠ some (.returned v) := by
  cases shape : p with
  | skip => simp [evaluateHOLFiniteState_skip]
  | assign _ _ _ =>
    rw [evaluateHOLFiniteState_assign]
    split
    · simp
    · split <;> simp
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | dec vname _ _ a =>
    have ha : ph_noReturnProg a = true := by simpa [shape, ph_noReturnProg] using hp
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · rename_i val _
      split
      · have mclk : (setVarHOLFinite vname val s).clock ≤ s.clock := le_rfl
        exact ph_eval_noReturnProg a ha (setVarHOLFinite vname val s) v
      · simp
  | decCall vname _ _ _ a =>
    have ha : ph_noReturnProg a = true := by simpa [shape, ph_noReturnProg] using hp
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    split
    · simp
    · split
      · simp
      · rename_i body callee _ _
        split
        · simp
        · dsimp only
          have rem := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
          rcases hcal : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rc, sc⟩
          rw [hcal] at rem
          dsimp only
          cases rc with
          | none => simp
          | some rc' =>
            cases rc' with
            | returned rv =>
              dsimp only
              split
              · have smaller : (setVarHOLFinite vname rv { sc with locals := s.locals }).clock < s.clock := by
                  change sc.clock < s.clock
                  change sc.clock ≤ s.clock - 1 at rem
                  omega
                exact ph_eval_noReturnProg a ha (setVarHOLFinite vname rv { sc with locals := s.locals }) v
              · simp
            | _ => simp
  | call ret _ _ =>
    cases ret with
    | none => simp [shape, ph_noReturnProg] at hp
    | some rt =>
      rcases rt with ⟨lhs, hopt⟩
      cases hopt with
      | some _ => simp [shape, ph_noReturnProg] at hp
      | none =>
        rw [evaluateHOLFiniteState_call]
        split
        · simp
        · split
          · simp
          · rename_i body callee _ _
            split
            · simp
            · dsimp only
              rcases hcal : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rc, sc⟩
              cases rc with
              | none => simp
              | some rc' =>
                cases rc' with
                | returned rv =>
                  simp only []
                  split
                  · cases lhs with
                    | none => simp
                    | some kv =>
                      rcases kv with ⟨vk, vn⟩
                      simp only []
                      split <;> simp
                  · simp
                | _ => simp
  | seq a b =>
    have hab : ph_noReturnProg a = true ∧ ph_noReturnProg b = true := by
      simpa [shape, ph_noReturnProg, Bool.and_eq_true] using hp
    have rem := evaluateHOLFiniteState_clock_le s a
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := ph_eval_noReturnProg a hab.1 s v
    rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
    rw [hr] at ha rem
    cases r with
    | none =>
      have mclk : m.clock ≤ s.clock := rem
      exact ph_eval_noReturnProg b hab.2 m v
    | some _ => exact ha
  | ite _ a b =>
    have hab : ph_noReturnProg a = true ∧ ph_noReturnProg b = true := by
      simpa [shape, ph_noReturnProg, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact ph_eval_noReturnProg b hab.2 s v
      · exact ph_eval_noReturnProg a hab.1 s v
    · simp
  | «while» cond body =>
    have hb : ph_noReturnProg body = true := by simpa [shape, ph_noReturnProg] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp
        · have dec_lt : (decClockHOLFinite s).clock < s.clock := by simp only [decClockHOLFinite]; omega
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := ph_eval_noReturnProg body hb (decClockHOLFinite s) v
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at ih1 rem
          have smaller : mid.clock < s.clock := by change mid.clock ≤ s.clock - 1 at rem; omega
          cases r1 with
          | none => exact ph_eval_noReturnProg (.while cond body) (by simpa [shape] using hp) mid v
          | some r1 =>
            cases r1 with
            | «continue» => exact ph_eval_noReturnProg (.while cond body) (by simpa [shape] using hp) mid v
            | «returned» _ => exact ih1
            | _ => simp
      · simp
    · simp
  | _ => simp [shape, ph_noReturnProg] at hp
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals
    subst shape
    simp_wf
    first
      | exact Prod.Lex.left _ _ dec_lt
      | exact Prod.Lex.left _ _ smaller
      | exact Prod.Lex.right _ (by omega)
      | (rcases Nat.lt_or_eq_of_le mclk with h | h
         · exact Prod.Lex.left _ _ h
         · rw [h]; exact Prod.Lex.right _ (by omega))

def ph_wdLenBody : ProgHOL 64 :=
  .decCall (ofString "wlen") .one (ofString "withdrawal_rlp_len")
    [.op .add
      [.load .one (.op .add [.var .local (ofString "pl"), .const 48#64]),
       .panop .mul [.var .local (ofString "i"), .const 44#64]]]
    (.seq
      (.assign .local (ofString "wl")
        (.op .add [.var .local (ofString "wl"), .var .local (ofString "wlen")]))
      (.assign .local (ofString "i")
        (.op .add [.var .local (ofString "i"), .const 1#64])))

def ph_wdLenLoop : ProgHOL 64 :=
  .while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nwd")))
    ph_wdLenBody

theorem ph_signed_less_eq_slt (left right : BitVec 64) :
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

theorem ph_callee_param_value {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname pk : MlS) (sk : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : s.code.lookup fname = some ([(pk, sk)], body, ret))
    (v : ValueHOL 64) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hlook : lookupCodeHOLFinite s.code.lookup fname [v] = some (body', callee, ret')) :
    callee.lookup pk = some v := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hlook
  split at hlook
  · cases hlook
  · rename_i exactBody exactLocals exactShape raw
    have heq := Option.some.inj hlook
    rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨rfl, _⟩
    unfold lookupCodeHOLExact at raw
    rw [hl] at raw
    dsimp only at raw
    split at raw
    · have heq := Option.some.inj raw
      rcases Prod.mk.inj heq with ⟨-, hrest⟩
      rcases Prod.mk.inj hrest with ⟨hloc, -⟩
      subst hloc
      simp
    · cases raw

theorem ph_wdLenLoop_exit_bound {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (w_pl w_nwd w_i : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (hG : GuestInv s)
    (hpl : s.locals.lookup (ofString "pl") = some (.val (.word w_pl)))
    (hnwd : s.locals.lookup (ofString "nwd") = some (.val (.word w_nwd)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word w_i)))
    (hn0 : 0 ≤ w_nwd.toInt)
    (hi0 : 0 ≤ w_i.toInt)
    (hprev : 0 < w_i.toNat → memW s (w_pl + 48#64).toNat < heapEnd ∧ 44 * (w_i.toNat - 1) < heapEnd) :
    (evaluateHOLFiniteState s ph_wdLenLoop).1 = none →
    44 * w_nwd.toNat ≤ heapEnd + 44 ∧
      (0 < w_nwd.toNat → memW s (w_pl + 48#64).toNat < heapEnd) := by
  intro hnone
  have hrec : ∀ (clk : Nat) (st : PanSemStateFiniteExact 64 F) (wi : BitVec 64),
      st.clock = clk →
      st.code = originalRuntimeCode →
      GuestInv st →
      st.locals.lookup (ofString "pl") = some (.val (.word w_pl)) →
      st.locals.lookup (ofString "nwd") = some (.val (.word w_nwd)) →
      st.locals.lookup (ofString "i") = some (.val (.word wi)) →
      0 ≤ wi.toInt →
      (0 < wi.toNat → memW st (w_pl + 48#64).toNat < heapEnd ∧ 44 * (wi.toNat - 1) < heapEnd) →
      (evaluateHOLFiniteState st ph_wdLenLoop).1 = none →
      44 * w_nwd.toNat ≤ heapEnd + 44 ∧
        (0 < w_nwd.toNat → memW st (w_pl + 48#64).toNat < heapEnd) := by
    intro clk
    induction clk using Nat.strongRecOn with
    | ind clk ih =>
      intro st wi hclk hsc hGs hst_pl hst_nwd hst_i hwi0 hwi_prev hst_none
      dsimp only [ph_wdLenLoop] at hst_none
      rw [evaluateHOLFiniteState_while_total, evalHOLFinite_eq_toExact] at hst_none
      have hevc : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
          (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nwd"))) =
          some (.val (.word (if wi.toInt < w_nwd.toInt then 1 else 0))) := by
        simp only [evalHOLExact, evalListHOLExact, hst_i, hst_nwd, Compiler.Encoders.Asm.wordCmpHOL,
          ph_signed_less_eq_slt, BitVec.slt_eq_decide, decide_eq_true_eq]
      rw [hevc] at hst_none
      dsimp only at hst_none
      by_cases hlt : wi.toInt < w_nwd.toInt
      · rw [if_pos hlt] at hst_none
        have h1 : (1 : BitVec 64) ≠ 0 := by decide
        rw [if_pos h1] at hst_none
        by_cases hcz : st.clock = 0
        · rw [if_pos hcz] at hst_none; simp at hst_none
        · rw [if_neg hcz, fixClockHOLFinite_evaluateState] at hst_none
          set st1 := decClockHOLFinite st
          have hG1 : GuestInv st1 := localsFree_guestInv st st.locals (st.clock - 1) hGs
          have hcle := evaluateHOLFiniteState_clock_le st1 ph_wdLenBody
          have hsc1 : st1.code = originalRuntimeCode := hsc
          have hlf : M13.LocFrame st1 (evaluateHOLFiniteState st1 ph_wdLenBody).2 := by
            dsimp only [ph_wdLenBody]
            apply M13.locFrame_decCall hsc1 ph_frame_withdrawal_rlp_len _ _ _
            intro tw _
            exact M13.locFrameW_eval _ rfl tw
          rcases hbr : evaluateHOLFiniteState st1 ph_wdLenBody with ⟨rb, mid⟩
          rw [hbr] at hst_none hcle hlf
          dsimp only at hlf
          have hclk_lt : mid.clock < clk := by
            change mid.clock ≤ st.clock - 1 at hcle; omega
          have hmemW_mid : memW mid (w_pl + 48#64).toNat = memW st (w_pl + 48#64).toNat := by
            simp only [memW, hlf.memory]
            rfl
          have hbr_step : rb ≠ some .continue ∧ rb ≠ some .break ∧
              (rb = none →
                memW st (w_pl + 48#64).toNat < heapEnd ∧
                44 * wi.toNat < heapEnd ∧
                mid.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
                mid.locals.lookup (ofString "nwd") = some (.val (.word w_nwd)) ∧
                mid.locals.lookup (ofString "i") = some (.val (.word (wi + 1#64)))) := by
            have hbr' := hbr
            dsimp only [ph_wdLenBody] at hbr'
            rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hbr'
            rcases ha : evalListHOLFinite st1 (h := fun a => Classical.propDecidable (st1.memaddrs a)) _
              with _ | vs
            · rw [ha] at hbr'
              injection hbr' with hrb _
              subst hrb
              simp
            · rw [ha] at hbr'
              dsimp only at hbr'
              rcases hl : lookupCodeHOLFinite st1.code.lookup (ofString "withdrawal_rlp_len") vs
                with _ | ⟨body', callee, rs⟩
              · rw [hl] at hbr'
                injection hbr' with hrb _
                subst hrb
                simp
              · rw [hl] at hbr'
                dsimp only at hbr'
                by_cases hc1 : st1.clock = 0
                · rw [if_pos hc1] at hbr'
                  injection hbr' with hrb _
                  subst hrb
                  simp
                · rw [if_neg hc1] at hbr'
                  have hb_eq := lookupCodeHOLFinite_installed_body st1.code.lookup
                    (ofString "withdrawal_rlp_len") _ _ _ _ _ vs callee
                    (by change st.code.lookup _ = _; rw [hsc]; exact ph_lookup_withdrawal_rlp_len) hl
                  subst hb_eq
                  have ha_ex : ∃ w_base : BitVec 64,
                      w_base.toNat = memW st (w_pl + 48#64).toNat ∧
                      vs = [.val (.word (w_base + wi * 44#64))] := by
                    rw [evalListHOLFinite_eq_toExact] at ha
                    dsimp only [evalListHOLExact] at ha
                    rcases he1 : @evalHOLExact 64 F _ st1.toExact
                      (fun a => Classical.propDecidable (st1.memaddrs a)) _ with _ | v_arg
                    · rw [he1] at ha; cases ha
                    · rw [he1] at ha; injection ha with hvs
                      have he1' : evalAt st1 (.op .add
                          [.load .one (.op .add [.var .local (ofString "pl"), .const 48#64]),
                           .panop .mul [.var .local (ofString "i"), .const 44#64]]) = some v_arg := he1
                      have hv_word : ∃ w_arg : BitVec 64, v_arg = .val (.word w_arg) := by
                        simp only [evalHOLExact] at he1
                        rcases hl_arg : @evalListHOLExact 64 F _ st1.toExact
                            (fun x => Classical.propDecidable (st1.memaddrs x))
                            [.load .one (.op .add [.var .local (ofString "pl"), .const 48#64]),
                             .panop .mul [.var .local (ofString "i"), .const 44#64]] with _ | vs_arg
                        · rw [hl_arg] at he1; simp at he1
                        · rw [hl_arg] at he1; dsimp only at he1
                          split_ifs at he1
                          rcases hw_arg : @wordOpHOL 64 _ .add (vs_arg.map valueWord) with _ | w_arg
                          · rw [hw_arg] at he1; simp at he1
                          · rw [hw_arg] at he1; simp only [Option.map, Option.some.injEq] at he1
                            exact ⟨w_arg, he1.symm⟩
                      obtain ⟨w_arg, rfl⟩ := hv_word
                      obtain ⟨w_base, w_mul, hld, hmul, hw_eq⟩ := evalAt_add2_words he1'
                      obtain ⟨a_ld, w_base', ha_ld, hwb, hw_mem, _, _, _⟩ := evalAt_load_one_word hG1 hld
                      cases hwb
                      have ha_pl := evalAt_add_local_const (s := st1) (off := 48) hst_pl ha_ld
                      subst ha_pl
                      obtain ⟨wi', hwi', hmul_eq⟩ := evalAt_panOp_mul_const (c := 44) hmul
                      have hwi_eq : wi' = wi := by
                        change st1.locals.lookup (ofString "i") = some (.val (.word wi')) at hwi'
                        rw [show st1.locals.lookup (ofString "i") = some (.val (.word wi)) from hst_i] at hwi'
                        cases hwi'
                        rfl
                      subst hwi_eq
                      cases hmul_eq
                      subst hw_eq
                      exact ⟨w_base, hw_mem, hvs.symm⟩
                  obtain ⟨w_base, hw_base, rfl⟩ := ha_ex
                  have hparam := ph_callee_param_value st1 (ofString "withdrawal_rlp_len") (ofString "wd") .one _ _
                    (by change st.code.lookup _ = _; rw [hsc]; exact ph_lookup_withdrawal_rlp_len)
                    (.val (.word (w_base + wi * 44#64))) _ callee rs hl
                  set entry := callEntryStateHOLFinite st1 callee
                  have hG_ent : GuestInv entry := localsFree_guestInv st1 callee (st1.clock - 1) hG1
                  rcases hcal : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_withdrawal_rlp_len)
                    with ⟨rc, sc⟩
                  rw [hcal] at hbr'
                  dsimp only at hbr'
                  cases rc with
                  | none => injection hbr' with hrb _; subst hrb; simp
                  | some rc' =>
                    cases rc' with
                    | returned rv =>
                      dsimp only at hbr'
                      split at hbr'
                      · have hdom_wd := ph_withdrawal_rlp_len_resumes_domain entry hG_ent
                          (by rw [hcal]; exact Or.inl ⟨rv, rfl⟩)
                        have hloc_wd : locN entry "wd" = (w_base + wi * 44#64).toNat := by
                          simp [entry, locN, callEntryStateHOLFinite, hparam]
                        rw [hloc_wd] at hdom_wd
                        have hprog := ph_withdrawal_domain_progress w_base wi
                          (by intro hp; rw [hw_base]; exact hwi_prev hp)
                          ⟨hdom_wd.1, by omega⟩
                        set s_cont := setVarHOLFinite (ofString "wlen") rv { sc with locals := st1.locals }
                        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign] at hbr'
                        rcases he_wl : @evalHOLExact 64 F _ s_cont.toExact
                            (fun a => Classical.propDecidable (s_cont.memaddrs a))
                            (.op .add [.var .local (ofString "wl"), .var .local (ofString "wlen")]) with _ | v_wl
                        · rw [he_wl] at hbr'
                          injection hbr' with hrb _
                          subst hrb
                          simp
                        · rw [he_wl] at hbr'
                          dsimp only at hbr'
                          by_cases hval_wl : s_cont.isValidValueHOLFinite .local (ofString "wl") v_wl = true
                          · rw [if_pos hval_wl] at hbr'
                            dsimp only at hbr'
                            set s_cont2 := setKvarHOLFinite .local (ofString "wl") v_wl s_cont
                            rw [evaluateHOLFiniteState_assign] at hbr'
                            have h_i_c2 : s_cont2.locals.lookup (ofString "i") = some (.val (.word wi)) := by
                              simp [s_cont2, s_cont, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                                show ofString "wl" ≠ ofString "i" by decide,
                                show ofString "wlen" ≠ ofString "i" by decide,
                                show st1.locals.lookup (ofString "i") = some (.val (.word wi)) from hst_i]
                            have he_i : @evalHOLExact 64 F _ s_cont2.toExact
                                (fun a => Classical.propDecidable (s_cont2.memaddrs a))
                                (.op .add [.var .local (ofString "i"), .const 1#64]) =
                                some (.val (.word (wi + 1#64))) := by
                              simp [evalHOLExact, evalListHOLExact, h_i_c2, valueIsWord, valueWord, wordOpHOL, wordOp]
                            have hval_i : s_cont2.isValidValueHOLFinite .local (ofString "i") (.val (.word (wi + 1#64))) = true := by
                              simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, h_i_c2,
                                shapeOfHOLExact, shapeEqHOL]
                            rw [he_i] at hbr'
                            dsimp only at hbr'
                            rw [if_pos hval_i] at hbr'
                            injection hbr' with hrb hmid
                            subst hrb
                            refine ⟨by simp, by simp, fun _ => ⟨by rw [← hw_base]; exact hprog.1, hprog.2, ?_, ?_, ?_⟩⟩
                            · rw [← hmid]
                              simp [PanRunBounded.resVarEq_lookup, s_cont2, s_cont, setKvarHOLFinite, setVarHOLFinite,
                                HolFiniteMapExact.lookup_update, FUPDATE,
                                show ofString "pl" ≠ ofString "wlen" by decide,
                                show ofString "i" ≠ ofString "pl" by decide,
                                show ofString "wl" ≠ ofString "pl" by decide,
                                show ofString "wlen" ≠ ofString "pl" by decide,
                                show st1.locals.lookup (ofString "pl") = some (.val (.word w_pl)) from hst_pl]
                            · rw [← hmid]
                              simp [PanRunBounded.resVarEq_lookup, s_cont2, s_cont, setKvarHOLFinite, setVarHOLFinite,
                                HolFiniteMapExact.lookup_update, FUPDATE,
                                show ofString "nwd" ≠ ofString "wlen" by decide,
                                show ofString "i" ≠ ofString "nwd" by decide,
                                show ofString "wl" ≠ ofString "nwd" by decide,
                                show ofString "wlen" ≠ ofString "nwd" by decide,
                                show st1.locals.lookup (ofString "nwd") = some (.val (.word w_nwd)) from hst_nwd]
                            · rw [← hmid]
                              simp [PanRunBounded.resVarEq_lookup, s_cont2, s_cont, setKvarHOLFinite, setVarHOLFinite,
                                HolFiniteMapExact.lookup_update, FUPDATE,
                                show ofString "i" ≠ ofString "wlen" by decide]
                          · rw [if_neg hval_wl] at hbr'
                            injection hbr' with hrb _
                            subst hrb
                            simp
                      · injection hbr' with hrb _
                        subst hrb
                        simp
                    | «continue» =>
                      injection hbr' with hrb _
                      subst hrb
                      simp
                    | «break» =>
                      injection hbr' with hrb _
                      subst hrb
                      simp
                    | exception _ _ =>
                      injection hbr' with hrb _
                      subst hrb
                      simp
                    | timeOut =>
                      injection hbr' with hrb _
                      subst hrb
                      simp
                    | error =>
                      injection hbr' with hrb _
                      subst hrb
                      simp
                    | finalFfi _ =>
                      injection hbr' with hrb _
                      subst hrb
                      simp
          cases rb with
          | none =>
            obtain ⟨hbase_lt, hwi_lt, hm_pl, hm_nwd, hm_i⟩ := hbr_step.2.2 rfl
            have hwi1_int : 0 ≤ (wi + 1#64).toInt := by
              have hhe : heapEnd < 2 ^ 62 := by decide
              have h1_lt : wi.toNat + 1 < 2 ^ 64 := by omega
              have hw1_nat : (wi + 1#64).toNat = wi.toNat + 1 := by
                rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1_lt]
              have hw1_int := BitVec.toInt_eq_msb_cond (wi + 1#64)
              rw [BitVec.msb_eq_decide] at hw1_int
              split_ifs at hw1_int with hmsb
              · rw [decide_eq_true_eq] at hmsb; omega
              · omega
            have hwi1_prev : 0 < (wi + 1#64).toNat →
                memW mid (w_pl + 48#64).toNat < heapEnd ∧ 44 * ((wi + 1#64).toNat - 1) < heapEnd := by
              intro _
              have hhe : heapEnd < 2 ^ 62 := by decide
              have h1_lt : wi.toNat + 1 < 2 ^ 64 := by omega
              have hw1_nat : (wi + 1#64).toNat = wi.toNat + 1 := by
                rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1_lt]
              rw [hmemW_mid, hw1_nat]
              exact ⟨hbase_lt, by simpa using hwi_lt⟩
            have hG_mid : GuestInv mid := by
              have hg := guestInv_evaluate st1 ph_wdLenBody hG1
              rwa [hbr] at hg
            have hih := ih mid.clock hclk_lt mid (wi + 1#64) rfl (hlf.code.trans hsc) hG_mid
              hm_pl hm_nwd hm_i hwi1_int hwi1_prev hst_none
            rw [hmemW_mid] at hih
            exact hih
          | some rb' =>
            cases rb' with
            | «continue» => exact absurd rfl hbr_step.1
            | «break» => exact absurd rfl hbr_step.2.1
            | _ => simp at hst_none
      · rw [if_neg hlt] at hst_none
        have h0 : ¬ ((0 : BitVec 64) ≠ 0) := not_not.mpr rfl
        rw [if_neg h0] at hst_none
        refine ⟨ph_withdrawal_count_at_exit w_nwd wi hwi0 hn0 (by omega) (fun hp => (hwi_prev hp).2), ?_⟩
        intro hn_pos
        have hi_pos : 0 < wi.toNat := by
          have hw1 := wi.isLt
          have hw2 := w_nwd.isLt
          have hi_int := BitVec.toInt_eq_msb_cond wi
          have hn_int := BitVec.toInt_eq_msb_cond w_nwd
          rw [BitVec.msb_eq_decide] at hi_int hn_int
          split_ifs at hi_int hn_int <;> omega
        exact (hwi_prev hi_pos).1
  exact hrec s.clock s w_i rfl hcode hG hpl hnwd hi hi0 hprev hnone

def ph_writesNoPl : ProgHOL 64 → Bool
  | .skip => true
  | .assign .local vn _ => vn != ofString "pl"
  | .assign .global _ _ => true
  | .store _ _ | .storeByte _ _ => true
  | .dec vn _ _ body => (vn != ofString "pl") && ph_writesNoPl body
  | .decCall vn _ _ _ cont => (vn != ofString "pl") && ph_writesNoPl cont
  | .call (some (some (.local, vn), none)) _ _ => vn != ofString "pl"
  | .call (some (none, none)) _ _ => true
  | .seq a b | .ite _ a b => ph_writesNoPl a && ph_writesNoPl b
  | .while _ body => ph_writesNoPl body
  | _ => false

theorem ph_eval_preserves_pl_nb {F : Type} (p : ProgHOL 64) (hp : ph_writesNoPl p = true)
    (s : PanSemStateFiniteExact 64 F) :
    ((evaluateHOLFiniteState s p).1 = none ∨
     (evaluateHOLFiniteState s p).1 = some .break ∨
     (evaluateHOLFiniteState s p).1 = some .continue) →
    (evaluateHOLFiniteState s p).2.locals.lookup (ofString "pl") =
      s.locals.lookup (ofString "pl") := by
  cases shape : p with
  | skip => intro _; simp [evaluateHOLFiniteState_skip]
  | assign vk vn _ =>
    intro _
    rw [evaluateHOLFiniteState_assign]
    split
    · rfl
    · split
      · cases vk with
        | «global» => simp [setKvarHOLFinite, setGlobalHOLFinite]
        | «local» =>
          have hne : vn ≠ ofString "pl" := by
            simpa [shape, ph_writesNoPl, bne_iff_ne] using hp
          simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
      · rfl
  | store _ _ =>
    intro _
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split <;> rfl
      · rfl
    · rfl
  | storeByte _ _ =>
    intro _
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split <;> rfl
      · rfl
    · rfl
  | dec vn _ _ body =>
    have h12 : vn ≠ ofString "pl" ∧ ph_writesNoPl body = true := by
      simpa [shape, ph_writesNoPl, Bool.and_eq_true, bne_iff_ne] using hp
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · intro hnb; simp at hnb
    · rename_i val _
      split
      · intro hnb
        have mclk : (setVarHOLFinite vn val s).clock ≤ s.clock := le_rfl
        have ih := ph_eval_preserves_pl_nb body h12.2 (setVarHOLFinite vn val s) hnb
        dsimp only
        rw [PanRunBounded.resVarEq_lookup, if_neg (Ne.symm h12.1), ih]
        simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h12.1]
      · intro hnb; simp at hnb
  | decCall vn _ _ _ cont =>
    have h12 : vn ≠ ofString "pl" ∧ ph_writesNoPl cont = true := by
      simpa [shape, ph_writesNoPl, Bool.and_eq_true, bne_iff_ne] using hp
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    split
    · intro hnb; simp at hnb
    · split
      · intro hnb; simp at hnb
      · rename_i body callee _ _
        split
        · intro hnb; simp at hnb
        · dsimp only
          have rem := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
          rcases hcal : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rc, sc⟩
          rw [hcal] at rem
          dsimp only
          cases rc with
          | none => intro hnb; simp at hnb
          | some rc' =>
            cases rc' with
            | returned crv =>
              dsimp only
              split
              · intro hnb
                have smaller : (setVarHOLFinite vn crv { sc with locals := s.locals }).clock < s.clock := by
                  change sc.clock < s.clock; change sc.clock ≤ s.clock - 1 at rem; omega
                have ih := ph_eval_preserves_pl_nb cont h12.2 (setVarHOLFinite vn crv { sc with locals := s.locals }) hnb
                dsimp only
                rw [PanRunBounded.resVarEq_lookup, if_neg (Ne.symm h12.1), ih]
                simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h12.1]
              · intro hnb; simp at hnb
            | _ => intro hnb; simp at hnb
  | call ret _ _ =>
    cases ret with
    | none => simp [shape, ph_writesNoPl] at hp
    | some rt =>
      rcases rt with ⟨lhs, hopt⟩
      cases hopt with
      | some _ => simp [shape, ph_writesNoPl] at hp
      | none =>
        rw [evaluateHOLFiniteState_call]
        split
        · intro hnb; simp at hnb
        · split
          · intro hnb; simp at hnb
          · rename_i body callee _ _
            split
            · intro hnb; simp at hnb
            · dsimp only
              rcases hcal : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rc, sc⟩
              cases rc with
              | none => intro hnb; simp at hnb
              | some rc' =>
                cases rc' with
                | returned rv =>
                  dsimp only
                  split
                  · cases lhs with
                    | none => intro _; rfl
                    | some kv =>
                      rcases kv with ⟨vk, vn⟩
                      cases vk with
                      | «global» => simp [shape, ph_writesNoPl] at hp
                      | «local» =>
                        have hne : vn ≠ ofString "pl" := by
                          simpa [shape, ph_writesNoPl, bne_iff_ne] using hp
                        dsimp only
                        split
                        · intro _
                          simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
                        · intro hnb; simp at hnb
                  · intro hnb; simp at hnb
                | _ => intro hnb; simp at hnb
  | seq a b =>
    have h12 : ph_writesNoPl a = true ∧ ph_writesNoPl b = true := by
      simpa [shape, ph_writesNoPl, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_seq_line780]
    have rem := evaluateHOLFiniteState_clock_le s a
    have ih1_fn := ph_eval_preserves_pl_nb a h12.1 s
    rcases hr1 : evaluateHOLFiniteState s a with ⟨r1, mid⟩
    rw [hr1] at rem ih1_fn
    dsimp only at rem ih1_fn ⊢
    cases r1 with
    | none =>
      intro hnb
      have mclk : mid.clock ≤ s.clock := rem
      exact (ph_eval_preserves_pl_nb b h12.2 mid hnb).trans (ih1_fn (Or.inl rfl))
    | some r1' =>
      cases r1' with
      | «break» => intro _; exact ih1_fn (Or.inr (Or.inl rfl))
      | «continue» => intro _; exact ih1_fn (Or.inr (Or.inr rfl))
      | _ => intro hnb; simp at hnb
  | ite _ a b =>
    have h12 : ph_writesNoPl a = true ∧ ph_writesNoPl b = true := by
      simpa [shape, ph_writesNoPl, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · intro hnb
        have mclk : s.clock ≤ s.clock := le_rfl
        exact ph_eval_preserves_pl_nb b h12.2 s hnb
      · intro hnb
        have mclk : s.clock ≤ s.clock := le_rfl
        exact ph_eval_preserves_pl_nb a h12.1 s hnb
    · intro hnb; simp at hnb
  | «while» cond body =>
    have hb : ph_writesNoPl body = true := by simpa [shape, ph_writesNoPl] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · intro hnb; simp at hnb
        · have dec_lt : (decClockHOLFinite s).clock < s.clock := by simp only [decClockHOLFinite]; omega
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          have ih1_fn := ph_eval_preserves_pl_nb body hb (decClockHOLFinite s)
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at rem ih1_fn
          dsimp only at rem ih1_fn
          have smaller : mid.clock < s.clock := by change mid.clock ≤ s.clock - 1 at rem; omega
          cases r1 with
          | none =>
            intro hnb
            exact (ph_eval_preserves_pl_nb (.while cond body) (by simpa [shape] using hp) mid hnb).trans
              (ih1_fn (Or.inl rfl))
          | some r1' =>
            cases r1' with
            | «continue» =>
              intro hnb
              exact (ph_eval_preserves_pl_nb (.while cond body) (by simpa [shape] using hp) mid hnb).trans
                (ih1_fn (Or.inr (Or.inr rfl)))
            | «break» =>
              intro _
              exact ih1_fn (Or.inr (Or.inl rfl))
            | _ => intro hnb; simp at hnb
      · intro _; rfl
    · intro hnb; simp at hnb
  | _ => simp [shape, ph_writesNoPl] at hp
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals
    subst shape
    simp_wf
    first
      | exact Prod.Lex.left _ _ dec_lt
      | exact Prod.Lex.left _ _ smaller
      | exact Prod.Lex.right _ (by omega)
      | (rcases Nat.lt_or_eq_of_le mclk with h | h
         · exact Prod.Lex.left _ _ h
         · rw [h]; exact Prod.Lex.right _ (by omega))

theorem ph_eval_preserves_pl_none {F : Type} (p : ProgHOL 64) (hp : ph_writesNoPl p = true)
    (s : PanSemStateFiniteExact 64 F)
    (hnone : (evaluateHOLFiniteState s p).1 = none) :
    (evaluateHOLFiniteState s p).2.locals.lookup (ofString "pl") =
      s.locals.lookup (ofString "pl") :=
  ph_eval_preserves_pl_nb p hp s (Or.inl hnone)

private theorem ph_ret_of_dec {F : Type} {s : PanSemStateFiniteExact 64 F}
    {vn : MlS} {sh : ShapeHOL} {e : ExpHOL 64} {body : ProgHOL 64} {rv : ValueHOL 64}
    (hv : vn ≠ ofString "pl")
    (hr : (evaluateHOLFiniteState s (.dec vn sh e body)).1 = some (.returned rv)) :
    ∃ s1 : PanSemStateFiniteExact 64 F,
      (∃ val, evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) e = some val ∧
        s1 = setVarHOLFinite vn val s) ∧
      s1.code = s.code ∧
      (GuestInv s → GuestInv s1) ∧
      s1.memory = s.memory ∧
      s1.locals.lookup (ofString "pl") = s.locals.lookup (ofString "pl") ∧
      (evaluateHOLFiniteState s1 body).1 = some (.returned rv) := by
  rw [evaluateHOLFiniteState_dec_total] at hr
  dsimp only at hr
  rcases he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | val
  · rw [he] at hr; simp at hr
  · rw [he] at hr; dsimp only at hr
    split_ifs at hr with hsh
    · refine ⟨setVarHOLFinite vn val s, ⟨val, ?_, rfl⟩, rfl, fun hG => localsFree_guestInv s _ s.clock hG, rfl, ?_, hr⟩
      · rw [evalHOLFinite_eq_toExact]; exact he
      · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hv]
    · simp at hr

private theorem ph_ret_of_seq {F : Type} {s : PanSemStateFiniteExact 64 F}
    {a b : ProgHOL 64} {rv : ValueHOL 64}
    (hna : ph_noReturnProg a = true)
    (hnpl : ph_writesNoPl a = true)
    (hcode : s.code = originalRuntimeCode)
    (hlf_a : M13.LocFrame s (evaluateHOLFiniteState s a).2)
    (hr : (evaluateHOLFiniteState s (.seq a b)).1 = some (.returned rv)) :
    ∃ s1 : PanSemStateFiniteExact 64 F,
      s1 = (evaluateHOLFiniteState s a).2 ∧
      (evaluateHOLFiniteState s a).1 = none ∧
      s1.code = originalRuntimeCode ∧
      (GuestInv s → GuestInv s1) ∧
      s1.memory = s.memory ∧
      s1.locals.lookup (ofString "pl") = s.locals.lookup (ofString "pl") ∧
      (evaluateHOLFiniteState s1 b).1 = some (.returned rv) := by
  have hneq := ph_eval_noReturnProg a hna s rv
  rw [evaluateHOLFiniteState_seq_line780] at hr
  rcases ha : evaluateHOLFiniteState s a with ⟨ra, sa⟩
  rw [ha] at hr hneq hlf_a
  dsimp only at hlf_a
  cases ra with
  | none =>
    have ha_none : (evaluateHOLFiniteState s a).1 = none := by rw [ha]
    have hpl_eq := ph_eval_preserves_pl_none a hnpl s ha_none
    rw [ha] at hpl_eq; dsimp only at hpl_eq
    refine ⟨sa, by simp [ha], rfl, hlf_a.code.trans hcode, fun hG => ?_, hlf_a.memory, hpl_eq, hr⟩
    have hg := guestInv_evaluate s a hG
    rwa [ha] at hg
  | some ra' =>
    cases ra' with
    | returned v' =>
      dsimp only at hr
      injection hr with h1; injection h1 with h2; subst h2
      exact absurd rfl hneq
    | _ => simp at hr

private theorem ph_ret_of_decCall {F : Type} {s : PanSemStateFiniteExact 64 F}
    {vn : MlS} {sh : ShapeHOL} {fn : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64} {rv : ValueHOL 64}
    (hcode : s.code = originalRuntimeCode)
    (hfn : M13.FunLocFrame fn)
    (hv : vn ≠ ofString "pl")
    (hr : (evaluateHOLFiniteState s (.decCall vn sh fn args cont)).1 = some (.returned rv)) :
    ∃ s1 : PanSemStateFiniteExact 64 F,
      s1.code = originalRuntimeCode ∧
      (GuestInv s → GuestInv s1) ∧
      s1.memory = s.memory ∧
      s1.locals.lookup (ofString "pl") = s.locals.lookup (ofString "pl") ∧
      (evaluateHOLFiniteState s1 cont).1 = some (.returned rv) := by
  obtain ⟨params, fbody, fret, hlook, hbody⟩ := hfn
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hr
  rcases ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · rw [ha] at hr; simp at hr
  · rw [ha] at hr; dsimp only at hr
    rcases hl : lookupCodeHOLFinite s.code.lookup fn vs with _ | ⟨body, callee, rs⟩
    · rw [hl] at hr; simp at hr
    · rw [hl] at hr; dsimp only at hr
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fn params fbody body
        fret rs vs callee (by rw [hcode]; exact hlook) hl
      subst hsame
      split_ifs at hr with hcz
      · simp at hr
      · have hlf : M13.LocFrame (callEntryStateHOLFinite s callee)
            (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).2 :=
          hbody (callEntryStateHOLFinite s callee) hcode
        rcases hcal : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rc, sc⟩
        rw [hcal] at hr hlf
        dsimp only at hr hlf
        cases rc with
        | none => simp at hr
        | some rc' =>
          cases rc' with
          | returned crv =>
            dsimp only at hr
            split_ifs at hr with hsh
            · set s1 := setVarHOLFinite vn crv { sc with locals := s.locals }
              refine ⟨s1, hlf.code.trans hcode, fun hG => ?_, hlf.memory, ?_, hr⟩
              · have hG_ent : GuestInv (callEntryStateHOLFinite s callee) :=
                  localsFree_guestInv s callee (s.clock - 1) hG
                have hG_sc : GuestInv sc := by
                  have hg := guestInv_evaluate (callEntryStateHOLFinite s callee) body hG_ent
                  rwa [hcal] at hg
                exact localsFree_guestInv sc _ sc.clock hG_sc
              · simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hv]
            · simp at hr
          | _ => simp at hr

theorem ph_blockRlpTail_returned_bound {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (w_pl : BitVec 64) (rv : ValueHOL 64)
    (hcode : s.code = originalRuntimeCode)
    (hG : GuestInv s)
    (hpl : s.locals.lookup (ofString "pl") = some (.val (.word w_pl))) :
    (evaluateHOLFiniteState s ph_blockRlpTail).1 = some (.returned rv) →
    0 < (BitVec.ofNat 64 (memW s (w_pl + 56#64).toNat)).toInt →
      memW s (w_pl + 48#64).toNat < heapEnd ∧
      44 * memW s (w_pl + 56#64).toNat ≤ heapEnd + 44 := by
  intro hret hn_pos
  dsimp only [ph_blockRlpTail, sourceFunctionEntry, Guest.Software.guestFn_block_rlp_length,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hret
  obtain ⟨s1, _, hc1, hG1_fn, hm1, hpl1, hr1⟩ := ph_ret_of_dec (by decide) hret
  obtain ⟨s2, _, hc2, hG2_fn, hm2, hpl2, hr2⟩ := ph_ret_of_dec (by decide) hr1
  obtain ⟨s3, _, hc3, hG3_fn, hm3, hpl3, hr3⟩ := ph_ret_of_dec (by decide) hr2
  obtain ⟨s4, _, hc4, hG4_fn, hm4, hpl4, hr4⟩ := ph_ret_of_dec (by decide) hr3
  obtain ⟨s5, _, hc5_eq, hG5_fn, hm5, hpl5, hr5⟩ := ph_ret_of_dec (by decide) hr4
  have hG5 : GuestInv s5 := hG5_fn (hG4_fn (hG3_fn (hG2_fn (hG1_fn hG))))
  have hc5 : s5.code = originalRuntimeCode := by rw [hc5_eq, hc4, hc3, hc2, hc1, hcode]
  obtain ⟨s6, _, _, hc6, hG6_fn, hm6_eq, hpl6_eq, hr6⟩ :=
    ph_ret_of_seq (by decide) rfl hc5
      (by
        refine M13.locFrame_while _ ?_ s5 hc5
        intro t htc
        apply M13.locFrame_dec; intro _
        apply M13.locFrame_dec; intro _
        apply M13.locFrame_seq
        · exact M13.locFrameW_eval _ rfl _
        · intro m1 hm1
          have hc1 : m1.code = originalRuntimeCode := hm1.code.trans htc
          apply M13.locFrame_dec; intro _
          apply M13.locFrame_seq
          · apply M13.locFrame_ite
            · exact M13.locFrame_call_local (by exact hc1) ph_frame_rlp_bytes_encoded_len (some (.local, ofString "el"))
                (fun _ _ h => by cases h; rfl) _
            · exact M13.locFrameW_eval _ rfl _
          · intro m2 _
            exact M13.locFrameW_eval _ rfl m2)
      hr5
  have hG6 : GuestInv s6 := hG6_fn hG5
  have hm6 : s6.memory = s.memory := by rw [hm6_eq, hm5, hm4, hm3, hm2, hm1]
  have hpl6 : s6.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by
    rw [hpl6_eq, hpl5, hpl4, hpl3, hpl2, hpl1, hpl]
  obtain ⟨s7, hc7, hG7_fn, hm7_eq, hpl7_eq, hr7⟩ :=
    ph_ret_of_decCall hc6 ph_frame_rlp_list_header_len (by decide) hr6
  have hG7 : GuestInv s7 := hG7_fn hG6
  obtain ⟨s8, _, _, hc8, hG8_fn, hm8_eq, hpl8_eq, hr8⟩ :=
    ph_ret_of_seq (by decide) rfl hc7 (M13.locFrameW_eval _ rfl s7) hr7
  have hG8 : GuestInv s8 := hG8_fn hG7
  obtain ⟨s9, _, _, hc9, hG9_fn, hm9_eq, hpl9_eq, hr9⟩ :=
    ph_ret_of_seq (by decide) rfl hc8 (M13.locFrameW_eval _ rfl s8) hr8
  have hG9 : GuestInv s9 := hG9_fn hG8
  have hm9 : s9.memory = s.memory := by rw [hm9_eq, hm8_eq, hm7_eq, hm6]
  have hpl9 : s9.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by
    rw [hpl9_eq, hpl8_eq, hpl7_eq, hpl6]
  obtain ⟨s10, ⟨val_nwd, he_nwd, hs10_eq⟩, hc10, hG10_fn, hm10, hpl10, hr10⟩ := ph_ret_of_dec (by decide) hr9
  have hG10 : GuestInv s10 := hG10_fn hG9
  rw [evalHOLFinite_eq_toExact] at he_nwd
  obtain ⟨a_nwd, w_nwd, ha_nwd, hval_nwd, hw_nwd_mem, _, _, _⟩ := evalAt_load_one_word hG9 he_nwd
  subst hval_nwd
  have ha_pl := evalAt_add_local_const (s := s9) (off := 56) hpl9 ha_nwd
  subst ha_pl
  have hw_nwd_s : w_nwd.toNat = memW s (w_pl + 56#64).toNat := by
    rw [hw_nwd_mem]; simp only [memW, hm9]
  have hw_nwd_bv : w_nwd = BitVec.ofNat 64 (memW s (w_pl + 56#64).toNat) := by
    rw [← hw_nwd_s, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain ⟨s11, ⟨val_wl, he_wl, hs11_eq⟩, hc11, hG11_fn, hm11, hpl11, hr11⟩ := ph_ret_of_dec (by decide) hr10
  have hG11 : GuestInv s11 := hG11_fn hG10
  have hc11' : s11.code = originalRuntimeCode := by rw [hc11, hc10, hc9]
  obtain ⟨s12, hs12_eq, ha_i0, hc12, hG12_fn, hm12_eq, hpl12_eq, hr12⟩ :=
    ph_ret_of_seq (by decide) rfl hc11' (M13.locFrameW_eval _ rfl s11) hr11
  have hG12 : GuestInv s12 := hG12_fn hG11
  have hm12 : s12.memory = s.memory := by rw [hm12_eq, hm11, hm10, hm9]
  have hpl12 : s12.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by
    rw [hpl12_eq, hpl11, hpl10, hpl9]
  have hnwd10 : s10.locals.lookup (ofString "nwd") = some (.val (.word w_nwd)) := by
    simp [hs10_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hnwd11 : s11.locals.lookup (ofString "nwd") = some (.val (.word w_nwd)) := by
    simp [hs11_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "wl" ≠ ofString "nwd" by decide, hnwd10]
  have hi12_and_nwd : s12.locals.lookup (ofString "i") = some (.val (.word 0#64)) ∧
      s12.locals.lookup (ofString "nwd") = some (.val (.word w_nwd)) := by
    have ha_i0' := ha_i0
    rw [evaluateHOLFiniteState_assign] at ha_i0'
    have he0 : @evalHOLExact 64 F _ s11.toExact (fun a => Classical.propDecidable (s11.memaddrs a)) (.const 0#64) =
        some (.val (.word 0#64)) := rfl
    rw [he0] at ha_i0'
    dsimp only at ha_i0'
    by_cases hvi : s11.isValidValueHOLFinite .local (ofString "i") (.val (.word 0#64)) = true
    · have hs12_def : s12 = setKvarHOLFinite .local (ofString "i") (.val (.word 0#64)) s11 := by
        rw [hs12_eq, evaluateHOLFiniteState_assign, he0]
        dsimp only
        rw [if_pos hvi]
      rw [hs12_def]
      exact ⟨by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
        by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "nwd" by decide, hnwd11]⟩
    · rw [if_neg hvi] at ha_i0'
      simp at ha_i0'
  obtain ⟨_, _, hw_wd, _, _, _, _, _⟩ :=
    ph_ret_of_seq (by decide) rfl hc12
      (by
        refine M13.locFrame_while _ ?_ s12 hc12
        intro tw htw
        apply M13.locFrame_decCall htw ph_frame_withdrawal_rlp_len _ _ _
        intro tw2 _
        exact M13.locFrameW_eval _ rfl tw2)
      hr12
  have hn0 : 0 ≤ w_nwd.toInt := by
    rw [hw_nwd_bv]
    exact le_of_lt hn_pos
  have hexit := ph_wdLenLoop_exit_bound s12 w_pl w_nwd 0#64 hc12 hG12 hpl12 hi12_and_nwd.2 hi12_and_nwd.1 hn0
    (by decide) (fun h => by simp at h) hw_wd
  have hn_nat_pos : 0 < w_nwd.toNat := by
    rw [hw_nwd_bv]
    by_cases hz : (BitVec.ofNat 64 (memW s (w_pl + 56#64).toNat)).toNat = 0
    · have hbv0 : BitVec.ofNat 64 (memW s (w_pl + 56#64).toNat) = 0#64 := BitVec.eq_of_toNat_eq hz
      rw [hbv0] at hn_pos
      exact absurd hn_pos (by decide)
    · omega
  have hbase_s12 := hexit.2 hn_nat_pos
  have hbase_s : memW s (w_pl + 48#64).toNat < heapEnd := by
    simpa only [memW, hm12] using hbase_s12
  exact ⟨hbase_s, by rw [← hw_nwd_s]; exact hexit.1⟩

private theorem heapByteEff_of_seq_none {F : Type}
    {s0 s m : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64} {Rl : List Ivl} {gw : List String}
    (ha : evaluateHOLFiniteState s a = (none, m))
    (hb : HeapByteEff s0 (evaluateHOLFiniteState m b).2 Rl gw) :
    HeapByteEff s0 (evaluateHOLFiniteState s (.seq a b)).2 Rl gw := by
  rw [evaluateHOLFiniteState_seq_line780, ha]
  exact hb

private theorem heapByteEff_of_eq_resVar {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {p : ProgHOL 64}
    {r' : Option (PanSemResultExact 64)} {q : PanSemStateFiniteExact 64 F}
    {L : HolFiniteMapExact MlS (ValueHOL 64)} {Rl : List Ivl} {gw : List String}
    (heq : evaluateHOLFiniteState s p = (r', { q with locals := L }))
    (hq : HeapByteEff s0 q Rl gw) :
    HeapByteEff s0 (evaluateHOLFiniteState s p).2 Rl gw := by
  rw [heq]
  exact hq.locals_clock L q.clock

private theorem ivlUnhit_of_heapByteEff_below_hp {F : Type}
    {s0 st : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    (hAR0 : ArenaReady s0)
    (heff : HeapByteEff s0 st Rl gw)
    {h len : Nat} (hh_ins : Inside (h, len) sourceBase (globN s0 "heap_ptr"))
    (hRl_ge : ∀ i ∈ Rl, 0 < i.2 → globN s0 "heap_ptr" ≤ i.1) :
    IvlUnhit s0 st (h, len) := by
  intro a ha8 hhit
  obtain ⟨ha_lo, ha_hi⟩ := hhit
  dsimp only at ha_lo ha_hi
  obtain ⟨hh_lo, hh_hi⟩ := hh_ins
  dsimp only at hh_lo hh_hi
  by_contra hne
  have hsep : heapLimit = scratchStart := rfl
  have hhp8 : globN s0 "heap_ptr" % 8 = 0 := hAR0.2.2.2.2.2.2.1
  have hfp8 : globN s0 "frame_mem_ptr" % 8 = 0 := hAR0.2.2.2.2.2.2.2.1
  have hhp_hi : globN s0 "heap_ptr" ≤ heapLimit := hAR0.2.2.1
  have hfp_lo : scratchStart ≤ globN s0 "frame_mem_ptr" := hAR0.2.2.2.1
  rcases heff.cell_frame a hne with ⟨i, hi, hipos, hc1, hc2⟩ | ⟨_, g1, _⟩ | ⟨_, f1, _⟩
  · have := hRl_ge i hi hipos
    omega
  · unfold freeGap at g1
    dsimp only at g1
    omega
  · unfold heapFree at f1
    dsimp only at f1
    omega

theorem wk_block_rlp_length_hdr :
    WorldKeeps (fun s => WorldOK s ∧ HeaderAtStrong s (locN s "hdr")) (fun _ => [])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "block_rlp_length") := by
  refine ⟨_, _, _, lookup_block_rlp_length, fun {F} s hcode ⟨hW, hHdr⟩ hparams hnt hres => ?_⟩
  have hAR : ArenaReady s := hW.1
  have hhl264 : heapLimit < 2 ^ 64 := by rw [heapLimit_val]; decide
  obtain ⟨vals, hl_args⟩ := hparams
  obtain ⟨hw, w_pl, _, hhdr_lk, _⟩ :=
    R13Shards.Keccak256.lookupCode_two_words (by decide) lookup_block_rlp_length hl_args
  have hhdr_locN : locN s "hdr" = hw.toNat := by simp [locN, hhdr_lk]
  have hH : HeaderAtStrong s hw.toNat := by rwa [hhdr_locN] at hHdr
  suffices hmain : HeapByteEff s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_block_rlp_length)).2
      (([] : List Ivl) ++ ([] : List (String × Nat)).map (bufferRegion s)) ["heap_ptr"] by
    exact hmain.to_worldStep (R := fun _ => []) (B := [])
      (by intro _ h; cases h)
      (by intro g hg; simp at hg; exact Or.inl hg)
      hW (fun _ _ _ _ _ => trivial)
  have hb : sourceFnBody Guest.Software.guestFn_block_rlp_length =
      .decCall (ofString "mark") .one (ofString "heap_mark") []
        (.decCall (ofString "he") (.comb [.one, .one]) (ofString "encode_header")
          [.var .local (ofString "hdr")]
          (.seq
            (.call (some (none, none)) (ofString "heap_release")
              [.var .local (ofString "mark")])
            ph_blockRlpTail)) := rfl
  rw [hb] at hnt hres ⊢
  set Rall : List Ivl := ([] : List Ivl) ++ ([] : List (String × Nat)).map (bufferRegion s)
  obtain ⟨mark, s1, _, hmark_nat, _, _, hs1_loc, heff01_nil, hnt1, heq1⟩ :=
    eval_decCall_heap_mark s "mark" _ ([] : List Ivl) ["heap_ptr"] hcode hAR hnt
  have heff01 : HeapByteEff s s1 Rall ["heap_ptr"] :=
    heff01_nil.mono (fun _ h => by cases h) (fun _ h => h)
  rw [heq1] at hres
  dsimp only at hres
  refine heapByteEff_of_eq_resVar heq1 ?_
  have hs1_mark : s1.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_hdr : s1.locals.lookup (ofString "hdr") = some (.val (.word hw)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hhdr_lk,
      show ofString "mark" ≠ ofString "hdr" by decide]
  have hH_s1 : HeaderAtStrong s1 hw.toNat := by
    have hu : IvlUnhit s s1 (hw.toNat, 248) :=
      ivlUnhit_of_heapByteEff_below_hp hAR heff01_nil hH.2 (fun _ h => by cases h)
    exact headerAtStrong_of_ivlUnhit hAR.1 heff01.arena.1 heff01.hp_le
      (by have := hH.2.2; have := hAR.2.2.1; omega) hu hH
  obtain ⟨startw, totalw, s2, hs2_loc, heff12, hnt2, hres2, heq2⟩ :=
    eval_decCall_encode_header s1 "he" (.var .local (ofString "hdr")) hw _ Rall ["heap_ptr"]
      heff01.arena.1.code heff01.arena (by simp) hs1_hdr hH_s1 hnt1 hres
  refine heapByteEff_of_eq_resVar heq2 ?_
  have heff02 : HeapByteEff s s2 Rall ["heap_ptr"] := heff01.trans heff12
  have hs2_mark : s2.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
    rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_mark,
      show ofString "he" ≠ ofString "mark" by decide]
  rw [evaluateHOLFiniteState_seq_line780] at hnt2 hres2
  rcases hc3 : evaluateHOLFiniteState s2
    (.call (some (none, none)) (ofString "heap_release")
      [.var .local (ofString "mark")]) with ⟨r3, s3⟩
  have hnt_c3 : r3 ≠ some .timeOut := by
    rintro rfl; rw [hc3] at hnt2; exact hnt2 rfl
  have h3 := eval_call_heap_release s2 (.var .local (ofString "mark")) mark
    Rall ["heap_ptr"] heff02.arena.1.code heff02 (by simp) hs2_mark
    (by rw [hmark_nat]) (by rw [hmark_nat]; exact hAR.2.1)
    (by rw [hmark_nat]; exact hAR.2.2.1)
    (by rw [hmark_nat]; exact hAR.2.2.2.2.2.2.1) (by rw [hc3]; exact hnt_c3)
  dsimp only at h3
  rw [hc3] at h3
  obtain ⟨rfl, _, _, _, heff03⟩ := h3
  refine heapByteEff_of_seq_none hc3 ?_
  have hlf4 := ph_frame_blockRlpTail s3 heff03.arena.1.code
  exact heff03.trans (HeapByteEff.of_locFrame heff03.arena hlf4 Rall ["heap_ptr"])

def PH_BL_POST : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => PH_BH s ∧
    ∀ w_pl : BitVec 64, s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) →
      0 < (BitVec.ofNat 64 (memW s (w_pl + 56#64).toNat)).toInt →
      memW s (w_pl + 48#64).toNat < heapEnd ∧
      44 * memW s (w_pl + 56#64).toNat ≤ heapEnd + 44

theorem ph_bl_post_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F} :
    PH_BL_POST s → GuestInv s := by
  intro h; exact ph_bh_guestInv h.1

theorem ph_block_rlp_length_returned_bound {F : Type}
    (s : PanSemStateFiniteExact 64 F) (w_hdr w_pl : BitVec 64) (rv : ValueHOL 64)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hhdr : s.locals.lookup (ofString "hdr") = some (.val (.word w_hdr)))
    (hpl : s.locals.lookup (ofString "pl") = some (.val (.word w_pl)))
    (hH : HeaderAtStrong s w_hdr.toNat)
    (hpl_in : Inside (w_pl.toNat, 136) sourceBase (globN s "heap_ptr"))
    (hpl8 : w_pl.toNat % 8 = 0)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_block_rlp_length)).1 =
      some (.returned rv)) :
    0 < (BitVec.ofNat 64 (memW s (w_pl + 56#64).toNat)).toInt →
      memW s (w_pl + 48#64).toNat < heapEnd ∧
      44 * memW s (w_pl + 56#64).toNat ≤ heapEnd + 44 := by
  have hb : sourceFnBody Guest.Software.guestFn_block_rlp_length =
      .decCall (ofString "mark") .one (ofString "heap_mark") []
        (.decCall (ofString "he") (.comb [.one, .one]) (ofString "encode_header")
          [.var .local (ofString "hdr")]
          (.seq
            (.call (some (none, none)) (ofString "heap_release")
              [.var .local (ofString "mark")])
            ph_blockRlpTail)) := rfl
  have hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_block_rlp_length)).1 ≠
      some .timeOut := by rw [hret]; simp
  have hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_block_rlp_length)).1 :=
    Or.inl ⟨rv, hret⟩
  rw [hb] at hret hnt hres
  set Rall : List Ivl := ([] : List Ivl) ++ ([] : List (String × Nat)).map (bufferRegion s)
  obtain ⟨mark, s1, _, hmark_nat, _, _, hs1_loc, heff01_nil, hnt1, heq1⟩ :=
    eval_decCall_heap_mark s "mark" _ ([] : List Ivl) ["heap_ptr"] hcode hAR hnt
  have heff01 : HeapByteEff s s1 Rall ["heap_ptr"] :=
    heff01_nil.mono (fun _ h => by cases h) (fun _ h => h)
  rw [heq1] at hret hres
  dsimp only at hret hres
  have hs1_mark : s1.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_hdr : s1.locals.lookup (ofString "hdr") = some (.val (.word w_hdr)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hhdr,
      show ofString "mark" ≠ ofString "hdr" by decide]
  have hs1_pl : s1.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hpl,
      show ofString "mark" ≠ ofString "pl" by decide]
  have hhl264 : heapLimit < 2 ^ 64 := by rw [heapLimit_val]; decide
  have hH_s1 : HeaderAtStrong s1 w_hdr.toNat := by
    have hu : IvlUnhit s s1 (w_hdr.toNat, 248) :=
      ivlUnhit_of_heapByteEff_below_hp hAR heff01_nil hH.2 (fun _ h => by cases h)
    exact headerAtStrong_of_ivlUnhit hAR.1 heff01.arena.1 heff01.hp_le
      (by have := hH.2.2; have := hAR.2.2.1; omega) hu hH
  obtain ⟨startw, totalw, s2, hs2_loc, heff12, hnt2, hres2, heq2⟩ :=
    eval_decCall_encode_header s1 "he" (.var .local (ofString "hdr")) w_hdr _ Rall ["heap_ptr"]
      heff01.arena.1.code heff01.arena (by simp) hs1_hdr hH_s1 hnt1 hres
  rw [heq2] at hret
  dsimp only at hret
  have heff02 : HeapByteEff s s2 Rall ["heap_ptr"] := heff01.trans heff12
  have hs2_mark : s2.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
    rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_mark,
      show ofString "he" ≠ ofString "mark" by decide]
  have hs2_pl : s2.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by
    rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_pl,
      show ofString "he" ≠ ofString "pl" by decide]
  rw [evaluateHOLFiniteState_seq_line780] at hret hnt2 hres2
  rcases hc3 : evaluateHOLFiniteState s2
    (.call (some (none, none)) (ofString "heap_release")
      [.var .local (ofString "mark")]) with ⟨r3, s3⟩
  have hnt_c3 : r3 ≠ some .timeOut := by
    rintro rfl; rw [hc3] at hnt2; exact hnt2 rfl
  have h3 := eval_call_heap_release s2 (.var .local (ofString "mark")) mark
    Rall ["heap_ptr"] heff02.arena.1.code heff02 (by simp) hs2_mark
    (by rw [hmark_nat]) (by rw [hmark_nat]; exact hAR.2.1)
    (by rw [hmark_nat]; exact hAR.2.2.1)
    (by rw [hmark_nat]; exact hAR.2.2.2.2.2.2.1) (by rw [hc3]; exact hnt_c3)
  dsimp only at h3
  rw [hc3] at h3 hret
  obtain ⟨rfl, hs3_loc, _, _, heff03⟩ := h3
  dsimp only at hret hs3_loc heff03
  have hs3_pl : s3.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by
    rw [hs3_loc]; exact hs2_pl
  intro hn_pos
  have hu_pl : IvlUnhit s s3 (w_pl.toNat, 136) :=
    ivlUnhit_of_heapByteEff_below_hp hAR heff03 hpl_in (by intro _ h; simp [Rall] at h)
  have hpl_hi : w_pl.toNat + 136 ≤ heapLimit := Nat.le_trans hpl_in.2 hAR.2.2.1
  have hmem_eq : ∀ off : Nat, off % 8 = 0 → off + 8 ≤ 136 →
      memW s3 (w_pl + BitVec.ofNat 64 off).toNat = memW s (w_pl + BitVec.ofNat 64 off).toNat := by
    intro off hoff8 hoff_hi
    have hnat : (w_pl + BitVec.ofNat 64 off).toNat = w_pl.toNat + off := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    rw [hnat]
    exact memW_eq_of_ivlUnhit hu_pl (by omega) (by omega) ⟨by omega, by omega⟩
  have hm48 := hmem_eq 48 (by omega) (by omega)
  have hm56 := hmem_eq 56 (by omega) (by omega)
  have htail := ph_blockRlpTail_returned_bound s3 w_pl rv heff03.arena.1.code heff03.arena.1 hs3_pl hret
    (by simpa only [hm56] using hn_pos)
  simpa only [hm48, hm56] using htail

theorem ph_block_rlp_length_resume :
    DecCallResumeOn PH_BH PH_BL_POST (ofString "bl") (ofString "block_rlp_length")
      [.var .local (ofString "h"), .var .local (ofString "pl")] := by
  intro F s values body callee ret rv post hcode hP hargs hl hret
  obtain ⟨w_si, w_pl, w_h, w_txr, w_wr, w_rh, w_bh, S, Nd, hIA, hBs, hd_ic,
    hd_ht, hd_hw, hd_tw, hd_hr, hd_hb, hlsi, hlpl, hlh, hltxr, hlwr, hlrh, hlbh,
    hpl_eq, h136⟩ := hP
  have heh : evalAt s (.var .local (ofString "h")) = some (.val (.word w_h)) := by
    simpa [evalAt, evalHOLExact] using hlh
  have hep : evalAt s (.var .local (ofString "pl")) = some (.val (.word w_pl)) := by
    simpa [evalAt, evalHOLExact] using hlpl
  have hpc := callee_param_two s (ofString "block_rlp_length") (ofString "hdr")
    (ofString "pl") .one .one _ _ (by rw [hcode]; exact lookup_block_rlp_length)
    _ _ _ _ values body callee ret heh hep hargs hl
  have hl0 : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "block_rlp_length") values =
      some (body, callee, ret) := by rwa [hcode] at hl
  have hbody : body = sourceFnBody Guest.Software.guestFn_block_rlp_length := by
    obtain ⟨p', r', hc⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hl0
    rw [lookup_block_rlp_length] at hc
    injection hc with hc1
    injection hc1 with _ hc2
    injection hc2 with hb _
    exact hb.symm
  subst body
  let entry := callEntryStateHOLFinite s callee
  have hIAe : InputAtWith entry S Nd w_si.toNat :=
    (inputAtWith_with_locals s callee (s.clock - 1) S Nd w_si.toNat).2 hIA
  have hBse : AllBlocksGood entry S Nd
      [(w_h.toNat, 248), (w_txr.toNat, 32), (w_wr.toNat, 32), (w_rh.toNat, 32), (w_bh.toNat, 32)] :=
    (allBlocksGood_with_locals s callee (s.clock - 1) S Nd _).2 hBs
  have hH : HeaderAtStrong entry w_h.toNat :=
    ⟨⟨(hBse _ (by simp)).2.2.2.1, h136⟩, (hBse _ (by simp)).2.2.1⟩
  have hWe : WorldOK entry := ⟨hIAe.1, S, (worldTyped_iff_with entry S).2 ⟨Nd, hIAe.2.1⟩⟩
  have hguard : WorldOK entry ∧ HeaderAtStrong entry (locN entry "hdr") := by
    refine ⟨hWe, ?_⟩
    simpa [entry, locN, callEntryStateHOLFinite, hpc.2.1] using hH
  have hws := FunSpec.at_lookup wk_block_rlp_length_hdr s hcode values _ callee ret hl hguard
    (by rw [hret]; simp)
  rw [hret] at hws
  dsimp only at hws
  have hstep := hws (Or.inl ⟨rv, rfl⟩)
  obtain ⟨S', Nd', hIAp, hBsp, hu_bs, hu_ic, _⟩ :=
    WorldStep_preserves_inputAndBlocks hIAe hBse hstep
      (by intro j hj; cases hj) (by intro j hj; cases hj)
      (by intro c hc j hj; cases hj) (by intro b hb j hj; cases hj)
  have hic := inputCells_eq_of_unhit hIAe hu_ic
  have hplmem : (w_pl.toNat, 136) ∈ inputCells entry w_si.toNat := by
    change (w_pl.toNat, 136) ∈ inputCells s w_si.toNat
    rw [hpl_eq]; simp [inputCells]
  have hplgood := hIAe.2.2.1 _ hplmem
  have hbound := ph_block_rlp_length_returned_bound entry w_h w_pl rv hIAe.1.1.code hIAe.1
    hpc.2.1 hpc.2.2 hH hplgood.1 hplgood.2.1 (by rw [hret])
  have hlim : heapLimit < 2 ^ 64 := by decide
  have hpl_hi : w_pl.toNat + 136 ≤ heapLimit := Nat.le_trans hplgood.1.2 hIAe.1.2.2.1
  have hpl8 : w_pl.toNat % 8 = 0 := hplgood.2.1
  have hm : ∀ off : Nat, off % 8 = 0 → off + 8 ≤ 136 →
      memW post (w_pl + BitVec.ofNat 64 off).toNat =
        memW entry (w_pl + BitVec.ofNat 64 off).toNat := by
    intro off ho hf
    have hn : (w_pl + BitVec.ofNat 64 off).toNat = w_pl.toNat + off := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    rw [hn]
    exact memW_eq_of_ivlUnhit (hu_ic _ hplmem) (by omega) (by omega) ⟨by omega, by omega⟩
  have hh := hBse (w_h.toNat, 248) (by simp)
  have h136eq : memW post (w_h.toNat + 136) = memW entry (w_h.toNat + 136) :=
    memW_eq_of_ivlUnhit (hu_bs (w_h.toNat, 248) (by simp)) (by have := hh.1; omega)
      (by have := hh.2.2.1.2; have := hIAe.1.2.2.1; omega) ⟨by omega, by omega⟩
  constructor
  · refine ⟨w_si, w_pl, w_h, w_txr, w_wr, w_rh, w_bh, S', Nd',
      (inputAtWith_with_locals post _ post.clock S' Nd' w_si.toNat).2 hIAp,
      (allBlocksGood_with_locals post _ post.clock S' Nd' _).2 hBsp,
      ?_, hd_ht, hd_hw, hd_tw, hd_hr, hd_hb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change IvlsDisj (inputCells post w_si.toNat) _
      rw [hic.2.2]; exact hd_ic
    · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "bl" ≠ ofString "si" by decide, hlsi]
    · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "bl" ≠ ofString "pl" by decide, hlpl]
    · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "bl" ≠ ofString "h" by decide, hlh]
    · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "bl" ≠ ofString "txr" by decide, hltxr]
    · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "bl" ≠ ofString "wr" by decide, hlwr]
    · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "bl" ≠ ofString "rh" by decide, hlrh]
    · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "bl" ≠ ofString "bh" by decide, hlbh]
    · exact hpl_eq.trans hic.1.symm
    · change memW post (w_h.toNat + 136) ≤ 32
      rw [h136eq]; exact h136
  · intro wp hwp hn
    have hwp' : wp = w_pl := by
      simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "bl" ≠ ofString "pl" by decide, hlpl] using hwp.symm
    subst wp
    change 0 < (BitVec.ofNat 64 (memW post (w_pl + 56#64).toNat)).toInt at hn
    change memW post (w_pl + 48#64).toNat < heapEnd ∧
      44 * memW post (w_pl + 56#64).toNat ≤ heapEnd + 44
    rw [hm 48 (by omega) (by omega), hm 56 (by omega) (by omega)]
    exact hbound (by simpa only [hm 56 (by omega) (by omega)] using hn)

theorem ph_block_rlp_length_entry :
    CallEntryOn PH_BH GuestInv (ofString "block_rlp_length")
      [.var .local (ofString "h"), .var .local (ofString "pl")] :=
  callEntryOn_of_imp localsFree_guestInv (fun _ h => ph_bh_guestInv h) _ _

theorem ph_bl_check_post :
    Hoare PH_BL_POST
      (.ite (.cmp .lower (.const 8388608#64) (.var .local (ofString "bl")))
        (.raise (ofString "BlockErr") (.const 7#64)) .skip)
      (fun r t => r = none → PH_BL_POST t) :=
  Hoare.ite_raise_skip _ _ _

theorem ph_payload_word_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {w_si w_pl : BitVec 64}
    (hIA : InputAtWith s S Nd w_si.toNat)
    (hpl : w_pl.toNat = memW s w_si.toNat)
    (hu : ∀ c ∈ inputCells s w_si.toNat, IvlUnhit s post c)
    (off : Nat) (ho : off % 8 = 0) (hf : off + 8 ≤ 136) :
    memW post (w_pl + BitVec.ofNat 64 off).toNat =
      memW s (w_pl + BitVec.ofNat 64 off).toNat := by
  have hc : (w_pl.toNat, 136) ∈ inputCells s w_si.toNat := by
    rw [hpl]; simp [inputCells]
  have hg := hIA.2.2.1 _ hc
  have hhi : w_pl.toNat + 136 ≤ heapLimit := Nat.le_trans hg.1.2 hIA.1.2.2.1
  have hlim : heapLimit < 2 ^ 64 := by decide
  have hn : (w_pl + BitVec.ofNat 64 off).toNat = w_pl.toNat + off := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  rw [hn]
  exact memW_eq_of_ivlUnhit (hu _ hc) (by have := hg.2.1; omega)
    (by omega) ⟨by omega, by omega⟩

theorem ph_withdrawal_bounds_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {w_si w_pl : BitVec 64}
    (hIA : InputAtWith s S Nd w_si.toNat)
    (hpl : w_pl.toNat = memW s w_si.toNat)
    (hu : ∀ c ∈ inputCells s w_si.toNat, IvlUnhit s post c)
    (hb : 0 < (BitVec.ofNat 64 (memW s (w_pl + 56#64).toNat)).toInt →
      memW s (w_pl + 48#64).toNat < heapEnd ∧
        44 * memW s (w_pl + 56#64).toNat ≤ heapEnd + 44) :
    0 < (BitVec.ofNat 64 (memW post (w_pl + 56#64).toNat)).toInt →
      memW post (w_pl + 48#64).toNat < heapEnd ∧
        44 * memW post (w_pl + 56#64).toNat ≤ heapEnd + 44 := by
  rw [ph_payload_word_unhit hIA hpl hu 48 (by omega) (by omega),
    ph_payload_word_unhit hIA hpl hu 56 (by omega) (by omega)]
  exact hb

theorem ph_withdrawal_active_lt {F : Type} {s : PanSemStateFiniteExact 64 F}
    {w_i w_nwd : BitVec 64}
    (hi : s.locals.lookup (ofString "i") = some (.val (.word w_i)))
    (hn : s.locals.lookup (ofString "nwd") = some (.val (.word w_nwd)))
    (hc : CondTrue (.cmp .less (.var .local (ofString "i"))
      (.var .local (ofString "nwd"))) s) :
    w_i.toInt < w_nwd.toInt := by
  obtain ⟨w, he, hw⟩ := hc
  have ha : LoopActive (.cmp .less (.var .local (ofString "i"))
      (.var .local (ofString "nwd"))) s :=
    ⟨w, by rwa [evalHOLFinite_eq_toExact], hw⟩
  obtain ⟨wi, wn, hli, hln, hlt⟩ := loopActive_cmp_less_locals ha
  rw [hi] at hli
  rw [hn] at hln
  cases hli
  cases hln
  exact hlt

def PH_WR_POST_B : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => PH_WR_POST s ∧
    ∀ w_pl : BitVec 64, s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) →
      0 < (BitVec.ofNat 64 (memW s (w_pl + 56#64).toNat)).toInt →
      memW s (w_pl + 48#64).toNat < heapEnd ∧
      44 * memW s (w_pl + 56#64).toNat ≤ heapEnd + 44

def PH_NWD_B : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_si w_pl w_wr w_nwd : BitVec 64, ∃ S Nd : List Nat,
    InputAtWith s S Nd w_si.toNat ∧
    AllBlocksGood s S Nd [(w_wr.toNat, 32)] ∧
    IvlsDisj (inputCells s w_si.toNat) [(w_wr.toNat, 32)] ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "wr") = some (.val (.word w_wr)) ∧
    s.locals.lookup (ofString "nwd") = some (.val (.word w_nwd)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    (0 < w_nwd.toInt →
      memW s (w_pl + 48#64).toNat < heapEnd ∧ 44 * w_nwd.toNat ≤ heapEnd + 44)

def PH_WDS0_B : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
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
    w_pl.toNat = memW s w_si.toNat ∧
    (0 < w_nwd.toInt →
      memW s (w_pl + 48#64).toNat < heapEnd ∧ 44 * w_nwd.toNat ≤ heapEnd + 44)

def PH_LOOP_B : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
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
    (0 < w_i.toNat → 44 * (w_i.toNat - 1) < heapEnd) ∧
    (0 < w_nwd.toInt →
      memW s (w_pl + 48#64).toNat < heapEnd ∧ 44 * w_nwd.toNat ≤ heapEnd + 44)

def PH_LOOP_EB : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
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
    44 * w_i.toNat < heapEnd ∧
    (0 < w_nwd.toInt →
      memW s (w_pl + 48#64).toNat < heapEnd ∧ 44 * w_nwd.toNat ≤ heapEnd + 44)

theorem ph_loop_b_loop {F : Type} {s : PanSemStateFiniteExact 64 F} :
    PH_LOOP_B s → PH_LOOP s := by
  rintro ⟨w_si, w_pl, w_wr, w_nwd, w_wds, w_i, S, Nd, hIA, hBs, hd_ic, hd,
    hlsi, hlpl, hlwr, hlnwd, hli, hgwds, hpl_eq, hi0, hib, _⟩
  exact ⟨w_si, w_pl, w_wr, w_nwd, w_wds, w_i, S, Nd, hIA, hBs, hd_ic, hd,
    hlsi, hlpl, hlwr, hlnwd, hli, hgwds, hpl_eq, hi0, hib⟩

theorem ph_loop_b_decClock {F : Type} (s : PanSemStateFiniteExact 64 F) :
    PH_LOOP_B s → PH_LOOP_B (decClockHOLFinite s) := by
  rintro ⟨w_si, w_pl, w_wr, w_nwd, w_wds, w_i, S, Nd, hIA, hBs, hd_ic, hd,
    hlsi, hlpl, hlwr, hlnwd, hli, hgwds, hpl_eq, hi0, hib, hnwd⟩
  exact ⟨w_si, w_pl, w_wr, w_nwd, w_wds, w_i, S, Nd,
    (inputAtWith_with_locals s s.locals (s.clock - 1) S Nd w_si.toNat).2 hIA,
    (allBlocksGood_with_locals s s.locals (s.clock - 1) S Nd _).2 hBs,
    hd_ic, hd, hlsi, hlpl, hlwr, hlnwd, hli, hgwds, hpl_eq, hi0, hib, hnwd⟩

theorem ph_loop_b_localsOnly :
    LocalsOnly ["si", "pl", "wr", "nwd", "i"] PH_LOOP_B := by
  intro F s locals k hl
  rintro ⟨w_si, w_pl, w_wr, w_nwd, w_wds, w_i, S, Nd, hIA, hBs, hd_ic, hd,
    hlsi, hlpl, hlwr, hlnwd, hli, hgwds, hpl_eq, hi0, hib, hnwd⟩
  refine ⟨w_si, w_pl, w_wr, w_nwd, w_wds, w_i, S, Nd,
    (inputAtWith_with_locals s locals k S Nd w_si.toNat).2 hIA,
    (allBlocksGood_with_locals s locals k S Nd _).2 hBs,
    hd_ic, hd, ?_, ?_, ?_, ?_, ?_, hgwds, hpl_eq, hi0, hib, hnwd⟩
  · simpa [hl "si" (by simp)] using hlsi
  · simpa [hl "pl" (by simp)] using hlpl
  · simpa [hl "wr" (by simp)] using hlwr
  · simpa [hl "nwd" (by simp)] using hlnwd
  · simpa [hl "i" (by simp)] using hli

theorem ph_build_mpt_txr_b
    (wmpt : WorldKeeps WorldOK
      (fun s => [(locN s "out", 32),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
                 (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "build_mpt_indexed")) :
    Hoare PH_BL_POST
      (.call (some (none, none)) (ofString "build_mpt_indexed")
        [.load .one (.op .add [.var .local (ofString "pl"), .const 32#64]),
         .load .one (.op .add [.var .local (ofString "pl"), .const 40#64]),
         .var .local (ofString "txr")])
      (fun r t => r = none → PH_WR_POST_B t) := by
  classical
  refine ⟨fun {F} state hcode hP _ hr => ?_⟩
  refine ⟨(ph_build_mpt_txr wmpt).run state hcode hP.1 (by rw [hr]; simp) hr, ?_⟩
  set e1 : ExpHOL 64 := .load .one (.op .add [.var .local (ofString "pl"), .const 32#64])
  set e2 : ExpHOL 64 := .load .one (.op .add [.var .local (ofString "pl"), .const 40#64])
  set e3 : ExpHOL 64 := .var .local (ofString "txr")
  rcases hcall : evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "build_mpt_indexed") [e1, e2, e3]) with ⟨cres, cpost⟩
  have hr' : cres = none := by rw [hcall] at hr; exact hr
  subst hr'
  obtain ⟨⟨w_si, w_pl, w_h, w_txr, w_wr, w_rh, w_bh, S, Nd, hIA, hBs, hd_ic,
    _, _, _, _, _, _, hlpl, _, hltxr, _, _, _, hpl_eq, _⟩, hbound0⟩ := hP
  have hb0 := hbound0 w_pl hlpl
  rw [evaluateHOLFiniteState_call] at hcall
  rcases hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) [e1, e2, e3] with _ | values
  · rw [hargs] at hcall; simp at hcall
  · rw [hargs] at hcall; dsimp only at hcall
    have hargs' : evalListHOLExact state.toExact [e1, e2, e3] = some values := by
      rwa [evalListHOLFinite_eq_toExact] at hargs
    rcases he1 : evalAt state e1 with _ | v1
    · simp [evalListHOLExact, he1] at hargs'
    · rcases he2 : evalAt state e2 with _ | v2
      · simp [evalListHOLExact, he1, he2] at hargs'
      · have he3 : evalAt state e3 = some (.val (.word w_txr)) := by
          simpa [e3, evalAt, evalHOLExact] using hltxr
        rcases hl : lookupCodeHOLFinite state.code.lookup (ofString "build_mpt_indexed") values
          with _ | ⟨body, callee, ret⟩
        · rw [hl] at hcall; simp at hcall
        · rw [hl] at hcall; dsimp only at hcall
          split_ifs at hcall with hz
          · simp at hcall
          · rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body
              with ⟨bres, post⟩
            rw [hb] at hcall
            cases bres with
            | none => simp at hcall
            | some br =>
              cases br with
              | returned v =>
                dsimp only at hcall
                split_ifs at hcall with hsh
                · obtain ⟨_, hpost_eq⟩ := Prod.mk.inj hcall
                  have hpc := callee_param_three state (ofString "build_mpt_indexed")
                    (ofString "slice_arr") (ofString "n") (ofString "out") .one .one .one _ _
                    (by rw [hcode]; exact lookup_build_mpt_indexed_fn)
                    e1 e2 e3 v1 v2 (.val (.word w_txr)) values body callee ret he1 he2 he3 hargs hl
                  set entry := callEntryStateHOLFinite state callee
                  have hout : locN entry "out" = w_txr.toNat := by
                    simp [entry, locN, callEntryStateHOLFinite, hpc.2.2]
                  have hW_state : WorldOK state := ⟨hIA.1, S, (worldTyped_iff_with state S).2 ⟨Nd, hIA.2.1⟩⟩
                  have hstep := FunSpec.at_lookup wmpt state hcode values body callee ret hl
                    (localsFree_worldOK state callee (state.clock - 1) hW_state) (by rw [hb]; simp)
                  rw [hb] at hstep; dsimp only at hstep
                  have hws := hstep (Or.inl ⟨v, rfl⟩)
                  have hIA_entry : InputAtWith entry S Nd w_si.toNat :=
                    (inputAtWith_with_locals state callee (state.clock - 1) S Nd w_si.toNat).2 hIA
                  have htxr_good := hBs (w_txr.toNat, 32) (by simp)
                  have hRz : ∀ j ∈ [(locN entry "out", 32),
                      bufferRegion entry ("keccak_pad", 136),
                      bufferRegion entry ("keccak_st", 200),
                      bufferRegion entry ("mpt_hash_scratch", 40),
                      bufferRegion entry ("mpt_key_scratch", 16)], j.2 = 0 → j.1 % 8 = 0 := by
                    intro j hj
                    rcases List.mem_cons.1 hj with rfl | hj1
                    · intro _; rw [hout]; exact htxr_good.1
                    · rcases List.mem_cons.1 hj1 with rfl | hj2
                      · exact bufferRegion_zero_aligned entry "keccak_pad" 136 (by decide)
                      · rcases List.mem_cons.1 hj2 with rfl | hj3
                        · exact bufferRegion_zero_aligned entry "keccak_st" 200 (by decide)
                        · rcases List.mem_cons.1 hj3 with rfl | hj4
                          · exact bufferRegion_zero_aligned entry "mpt_hash_scratch" 40 (by decide)
                          · simp only [List.mem_singleton] at hj4; subst hj4
                            exact bufferRegion_zero_aligned entry "mpt_key_scratch" 16 (by decide)
                  obtain ⟨_, _, _, _, _, hu_ic2, _⟩ :=
                    WorldStep_preserves_inputAndBlocks hIA_entry (allBlocksGood_nil entry S Nd) hws hRz
                      (fun j hj k hk => by
                        rcases List.mem_cons.1 hj with rfl | hj1
                        · rw [hout]; exact htxr_good.2.2.2.2 k (worldTypedIvls_sub_worldOwned _ _ _ k hk)
                        · rcases List.mem_cons.1 hj1 with rfl | hj2
                          · exact bufferRegion_disj_le hIA_entry.2.1 ("keccak_pad", 136) (by decide) (by decide) 136 le_rfl k hk
                          · rcases List.mem_cons.1 hj2 with rfl | hj3
                            · exact bufferRegion_disj_le hIA_entry.2.1 ("keccak_st", 200) (by decide) (by decide) 200 le_rfl k hk
                            · rcases List.mem_cons.1 hj3 with rfl | hj4
                              · exact bufferRegion_disj_le hIA_entry.2.1 ("mpt_hash_scratch", 40) (by decide) (by decide) 40 le_rfl k hk
                              · simp only [List.mem_singleton] at hj4; subst hj4
                                exact bufferRegion_disj_le hIA_entry.2.1 ("mpt_key_scratch", 16) (by decide) (by decide) 16 le_rfl k hk)
                      (fun c hc j hj => by
                        rcases List.mem_cons.1 hj with rfl | hj1
                        · rw [hout]; exact hd_ic c hc (w_txr.toNat, 32) (by simp)
                        · rcases List.mem_cons.1 hj1 with rfl | hj2
                          · exact hIA_entry.2.2.2.1 c hc _
                              (bufferRegion_mem_worldOwned entry S Nd (gn := ("keccak_pad", 136)) (by decide))
                          · rcases List.mem_cons.1 hj2 with rfl | hj3
                            · exact hIA_entry.2.2.2.1 c hc _
                                (bufferRegion_mem_worldOwned entry S Nd (gn := ("keccak_st", 200)) (by decide))
                            · rcases List.mem_cons.1 hj3 with rfl | hj4
                              · exact hIA_entry.2.2.2.1 c hc _
                                  (bufferRegion_mem_worldOwned entry S Nd (gn := ("mpt_hash_scratch", 40)) (by decide))
                              · simp only [List.mem_singleton] at hj4; subst hj4
                                exact hIA_entry.2.2.2.1 c hc _
                                  (bufferRegion_mem_worldOwned entry S Nd (gn := ("mpt_key_scratch", 16)) (by decide)))
                      (fun _ hb _ _ => by cases hb)
                  intro wp hwp
                  dsimp only
                  rw [← hpost_eq] at hwp ⊢
                  have hwp' : wp = w_pl := by simpa [hlpl] using hwp.symm
                  subst wp
                  exact ph_withdrawal_bounds_unhit hIA hpl_eq hu_ic2 hb0
                · simp at hcall
              | _ => simp [emptyLocalsHOLFinite] at hcall

theorem ph_dec_nwd_post_b {body : ProgHOL 64} {K : Nat}
    (hbody : TerminatingProgBoundedOn PH_NWD_B body K) :
    TerminatingProgBoundedOn PH_WR_POST_B
      (.dec (ofString "nwd") .one
        (.load .one (.op .add [.var .local (ofString "pl"), .const 56#64])) body) K := by
  refine dec_eval_on (P := PH_WR_POST_B) (Q := PH_NWD_B) _ _ _ ?_ hbody
  intro F s v ⟨⟨w_si, w_pl, w_wr, S, Nd, hIA, hBs, hd_ic, hlsi, hlpl, hlwr, hpl_eq⟩, hbound⟩ hev
  obtain ⟨a, w_nwd, ha, rfl, hmem, _⟩ := evalAt_load_one_word hIA.1.1 hev
  have ha_eq := evalAt_add_local_const (off := 56) hlpl ha
  subst ha_eq
  have hbv : BitVec.ofNat 64 (memW s (w_pl + 56#64).toNat) = w_nwd := by
    rw [← hmem, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨w_si, w_pl, w_wr, w_nwd, S, Nd,
    (inputAtWith_with_locals s _ s.clock S Nd w_si.toNat).2 hIA,
    (allBlocksGood_with_locals s _ s.clock S Nd [(w_wr.toNat, 32)]).2 hBs,
    hd_ic, ?_, ?_, ?_, ?_, hpl_eq, ?_⟩
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "nwd" ≠ ofString "si" by decide, hlsi]
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "nwd" ≠ ofString "pl" by decide, hlpl]
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "nwd" ≠ ofString "wr" by decide, hlwr]
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · intro hn
    have hb := hbound w_pl hlpl (by rwa [hbv])
    rwa [← hmem] at hb

theorem ph_alloc_wd_rlp_slices_b
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc")) :
    Hoare PH_NWD_B
      (.call (some (some (.global, ofString "wd_rlp_slices"), none)) (ofString "alloc")
        [.op .add [.panop .mul [.var .local (ofString "nwd"), .const 16#64], .const 16#64]])
      (fun r t => r = none → PH_WDS0_B t) := by
  classical
  refine ⟨fun {F} state hcode hP _ hr => ?_⟩
  obtain ⟨w_si, w_pl, w_wr, w_nwd, S, Nd, hIA, hBs, hd_ic, hlsi, hlpl, hlwr, hlnwd, hpl_eq, hnwdb⟩ := hP
  have hbase := (ph_alloc_wd_rlp_slices wal rtal).run state hcode
    ⟨w_si, w_pl, w_wr, w_nwd, S, Nd, hIA, hBs, hd_ic, hlsi, hlpl, hlwr, hlnwd, hpl_eq⟩
    (by rw [hr]; simp) hr
  set e_sz : ExpHOL 64 :=
    .op .add [.panop .mul [.var .local (ofString "nwd"), .const 16#64], .const 16#64]
  rcases hcall : evaluateHOLFiniteState state
      (.call (some (some (.global, ofString "wd_rlp_slices"), none)) (ofString "alloc") [e_sz])
    with ⟨cres, cpost⟩
  have hbase0 : PH_WDS0 cpost := by rw [hcall] at hbase; exact hbase
  have hr' : cres = none := by rw [hcall] at hr; exact hr
  subst hr'
  have hW_state : WorldOK state := ⟨hIA.1, S, (worldTyped_iff_with state S).2 ⟨Nd, hIA.2.1⟩⟩
  set w_sz : BitVec 64 := w_nwd * 16#64 + 16#64
  have he_sz : evalAt state e_sz = some (.val (.word w_sz)) := by
    simp [e_sz, w_sz, evalAt, evalHOLExact, evalListHOLExact, hlnwd, valueIsWord, valueWord,
      panOpHOL, wordOpHOL, wordOp]
  have hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) [e_sz] =
      some [.val (.word w_sz)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp only [evalListHOLExact]
    unfold evalAt at he_sz
    rw [he_sz]
  rw [evaluateHOLFiniteState_call, hargs] at hcall
  dsimp only at hcall
  rcases hl : lookupCodeHOLFinite state.code.lookup (ofString "alloc") [.val (.word w_sz)]
    with _ | ⟨body, callee, ret⟩
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
        | returned value =>
          dsimp only at hcall
          split_ifs at hcall with hsh hv
          · obtain ⟨_, hpost_eq⟩ := Prod.mk.inj hcall
            have hstep := FunSpec.at_lookup wal state hcode [.val (.word w_sz)] body callee ret hl
              (localsFree_worldOK state callee (state.clock - 1) hW_state) (by rw [hb]; simp)
            rw [hb] at hstep; dsimp only at hstep
            have hws := hstep (Or.inl ⟨value, rfl⟩)
            have hIA_entry : InputAtWith (callEntryStateHOLFinite state callee) S Nd w_si.toNat :=
              (inputAtWith_with_locals state callee (state.clock - 1) S Nd w_si.toNat).2 hIA
            obtain ⟨_, _, _, _, _, hu_ic, _⟩ :=
              WorldStep_preserves_inputAndBlocks hIA_entry (allBlocksGood_nil _ S Nd) hws
                (fun _ hj => by simp at hj) (fun _ hj => by simp at hj)
                (fun _ _ _ hj => by simp at hj) (fun _ hb' _ _ => by cases hb')
            have hm48 := ph_payload_word_unhit hIA hpl_eq hu_ic 48 (by omega) (by omega)
            obtain ⟨w_si', w_pl', w_wr', w_nwd', w_wds, S', Nd',
              hIA', hBs', hd_ic', hd', hlsi', hlpl', hlwr', hlnwd', hgwds', hpl_eq'⟩ := hbase0
            have hpl_same : w_pl' = w_pl := by
              rw [← hpost_eq] at hlpl'
              simpa [setKvarHOLFinite, setGlobalHOLFinite, hlpl] using hlpl'.symm
            have hnwd_same : w_nwd' = w_nwd := by
              rw [← hpost_eq] at hlnwd'
              simpa [setKvarHOLFinite, setGlobalHOLFinite, hlnwd] using hlnwd'.symm
            subst w_pl' w_nwd'
            dsimp only
            refine ⟨w_si', w_pl, w_wr', w_nwd, w_wds, S', Nd',
              hIA', hBs', hd_ic', hd', hlsi', hlpl', hlwr', hlnwd', hgwds', hpl_eq', ?_⟩
            intro hn
            rw [← hpost_eq]
            change memW post (w_pl + 48#64).toNat < heapEnd ∧ 44 * w_nwd.toNat ≤ heapEnd + 44
            rw [hm48]
            exact hnwdb hn
          · simp at hcall
          · simp at hcall
        | _ => simp [emptyLocalsHOLFinite] at hcall

theorem ph_dec_i_b {body : ProgHOL 64} {K : Nat}
    (hbody : TerminatingProgBoundedOn PH_LOOP_B body K) :
    TerminatingProgBoundedOn PH_WDS0_B
      (.dec (ofString "i") .one (.const 0#64) body) K := by
  refine dec_eval_on (P := PH_WDS0_B) (Q := PH_LOOP_B) _ _ _ ?_ hbody
  intro F s v hP hev
  have hv : v = .val (.word 0#64) := by
    simp only [evalAt, evalHOLExact, Option.some.injEq] at hev
    exact hev.symm
  subst hv
  obtain ⟨w_si, w_pl, w_wr, w_nwd, w_wds, S, Nd, hIA, hBs, hd_ic, hd,
    hlsi, hlpl, hlwr, hlnwd, hgwds, hpl_eq, hnwdb⟩ := hP
  refine ⟨w_si, w_pl, w_wr, w_nwd, w_wds, 0#64, S, Nd,
    (inputAtWith_with_locals s _ s.clock S Nd w_si.toNat).2 hIA,
    (allBlocksGood_with_locals s _ s.clock S Nd _).2 hBs,
    hd_ic, hd, ?_, ?_, ?_, ?_, ?_, hgwds, hpl_eq, by decide, fun hp => absurd hp (by decide), hnwdb⟩
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "si" by decide, hlsi]
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "pl" by decide, hlpl]
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "wr" by decide, hlwr]
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "nwd" by decide, hlnwd]
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

theorem ph_withdrawal_store0_b :
    Hoare PH_LOOP_EB (ph_withdrawal_store 0) (fun r t => r = none → PH_LOOP_EB t) := by
  unfold ph_withdrawal_store
  simp only [↓reduceIte]
  refine Hoare_store_fall (fun s x v mem' hP hx hv hst => ?_)
  obtain ⟨w_si, w_pl, w_wr, w_nwd, w_wds, w_i, e0, e1, S, Nd, hIA, hBs, hd_ic, hd,
    hlsi, hlpl, hlwr, hlnwd, hli, hle, hgwds, hpl_eq, hi0, hilt, hi44, hnwdb⟩ := hP
  have hn0 : 0 < w_nwd.toInt := by omega
  have hbounds := ph_slice_offset_bounds w_nwd w_i hi0 hilt (hnwdb hn0).2
  have hfit0 : 16 * w_i.toNat + 8 ≤ (w_nwd * 16#64 + 16#64).toNat :=
    Nat.le_trans (by omega) hbounds.2.2
  obtain ⟨w1, w2, hw1, hw2, hx_eq⟩ := evalAt_add2_words hx
  have hw1_eq : w1 = w_wds := by
    simpa [evalAt, evalHOLExact, hgwds] using hw1.symm
  subst w1
  obtain ⟨wi', hwi', hmul_eq⟩ := evalAt_panOp_mul_const (c := 16) hw2
  have hwi_eq : wi' = w_i := by
    simpa [evalAt, evalHOLExact, hli] using hwi'.symm
  subst wi'
  cases hmul_eq
  have hv_eq : v = .val (.word e0) := by
    simpa [evalAt, evalHOLExact, hle] using hv.symm
  subst v
  have hx_off : x = w_wds + BitVec.ofNat 64 (16 * w_i.toNat) := by
    rw [hx_eq, ← hbounds.1, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have htr := store_in_tracked_block
    (base := w_wds.toNat) (sz := (w_nwd * 16#64 + 16#64).toNat) (off := 16 * w_i.toNat)
    hIA hBs (by simp)
    (fun c hc b hb => by simp only [List.mem_singleton] at hb; subst hb; exact hd_ic c hc _ (by simp))
    rfl (by omega) hx_off (by simpa [flattenHOL] using hfit0) hst
  have hu_ic : ∀ c ∈ inputCells s w_si.toNat, IvlUnhit s { s with memory := mem' } c :=
    fun c hc => htr.2.2 c (fun _ => (hIA.2.2.1 c hc).2.1) (hd_ic c hc _ (by simp))
  have hic := inputCells_eq_of_unhit hIA hu_ic
  have hm48 := ph_payload_word_unhit hIA hpl_eq hu_ic 48 (by omega) (by omega)
  refine ⟨w_si, w_pl, w_wr, w_nwd, w_wds, w_i, e0, e1, S, Nd,
    htr.1, htr.2.1, ?_, hd, hlsi, hlpl, hlwr, hlnwd, hli, hle, hgwds,
    by rw [hic.1]; exact hpl_eq, hi0, hilt, hi44, ?_⟩
  · rw [hic.2.2]; exact hd_ic
  · intro hp
    rw [hm48]; exact hnwdb hp

theorem ph_withdrawal_store1_b :
    Hoare PH_LOOP_EB (ph_withdrawal_store 1) (fun r t => r = none → PH_LOOP_EB t) := by
  unfold ph_withdrawal_store
  simp only [show (1 : Nat) ≠ 0 by decide, ↓reduceIte]
  refine Hoare_store_fall (fun s x v mem' hP hx hv hst => ?_)
  obtain ⟨w_si, w_pl, w_wr, w_nwd, w_wds, w_i, e0, e1, S, Nd, hIA, hBs, hd_ic, hd,
    hlsi, hlpl, hlwr, hlnwd, hli, hle, hgwds, hpl_eq, hi0, hilt, hi44, hnwdb⟩ := hP
  have hn0 : 0 < w_nwd.toInt := by omega
  have hbounds := ph_slice_offset_bounds w_nwd w_i hi0 hilt (hnwdb hn0).2
  obtain ⟨w1, w2, w3, hw1, hw2, hw3, hx_eq⟩ := evalAt_add3_words hx
  have hw1_eq : w1 = w_wds := by
    simpa [evalAt, evalHOLExact, hgwds] using hw1.symm
  subst w1
  obtain ⟨wi', hwi', hmul_eq⟩ := evalAt_panOp_mul_const (c := 16) hw2
  have hwi_eq : wi' = w_i := by
    simpa [evalAt, evalHOLExact, hli] using hwi'.symm
  subst wi'
  cases hmul_eq
  have hw3_eq : w3 = 8#64 := by
    simpa [evalAt, evalHOLExact] using hw3.symm
  subst w3
  have hv_eq : v = .val (.word e1) := by
    simpa [evalAt, evalHOLExact, hle] using hv.symm
  subst v
  have hx_off : x = w_wds + BitVec.ofNat 64 (16 * w_i.toNat + 8) := by
    rw [hx_eq, ← hbounds.2.1, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have htr := store_in_tracked_block
    (base := w_wds.toNat) (sz := (w_nwd * 16#64 + 16#64).toNat) (off := 16 * w_i.toNat + 8)
    hIA hBs (by simp)
    (fun c hc b hb => by simp only [List.mem_singleton] at hb; subst hb; exact hd_ic c hc _ (by simp))
    rfl (by omega) hx_off (by simpa [flattenHOL] using hbounds.2.2) hst
  have hu_ic : ∀ c ∈ inputCells s w_si.toNat, IvlUnhit s { s with memory := mem' } c :=
    fun c hc => htr.2.2 c (fun _ => (hIA.2.2.1 c hc).2.1) (hd_ic c hc _ (by simp))
  have hic := inputCells_eq_of_unhit hIA hu_ic
  have hm48 := ph_payload_word_unhit hIA hpl_eq hu_ic 48 (by omega) (by omega)
  refine ⟨w_si, w_pl, w_wr, w_nwd, w_wds, w_i, e0, e1, S, Nd,
    htr.1, htr.2.1, ?_, hd, hlsi, hlpl, hlwr, hlnwd, hli, hle, hgwds,
    by rw [hic.1]; exact hpl_eq, hi0, hilt, hi44, ?_⟩
  · rw [hic.2.2]; exact hd_ic
  · intro hp
    rw [hm48]; exact hnwdb hp

theorem ph_withdrawal_inc_b :
    Hoare PH_LOOP_EB ph_withdrawal_increment (fun r t => r = none → PH_LOOP_B t) := by
  unfold ph_withdrawal_increment
  refine Hoare.assign_fall (fun s v hP hv => ?_)
  obtain ⟨w_si, w_pl, w_wr, w_nwd, w_wds, w_i, _, _, S, Nd, hIA, hBs, hd_ic, hd,
    hlsi, hlpl, hlwr, hlnwd, hli, _, hgwds, hpl_eq, hi0, _, hi44, hnwdb⟩ := hP
  have hv_eq : v = .val (.word (w_i + 1#64)) := by
    simpa [evalAt, evalHOLExact, evalListHOLExact, hli, valueIsWord, valueWord,
      wordOpHOL, wordOp] using hv.symm
  subst v
  have he : heapEnd < 2 ^ 40 := by decide
  have hi_lt63 : w_i.toNat + 1 < 2 ^ 63 := by omega
  have hnext_nat : (w_i + 1#64).toNat = w_i.toNat + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have h1 : (1 : Nat) % 2 ^ 64 = 1 := by decide
    rw [h1, Nat.mod_eq_of_lt (by omega)]
  have hnext_int : 0 ≤ (w_i + 1#64).toInt := by
    rw [BitVec.toInt_eq_msb_cond, BitVec.msb_eq_decide]
    have hnot : ¬ decide ((w_i + 1#64).toNat ≥ 2 ^ 63) = true := by
      rw [decide_eq_true_eq, hnext_nat]; omega
    rw [if_neg hnot]
    exact Int.natCast_nonneg _
  refine ⟨w_si, w_pl, w_wr, w_nwd, w_wds, w_i + 1#64, S, Nd,
    (inputAtWith_with_locals s _ s.clock S Nd w_si.toNat).2 hIA,
    (allBlocksGood_with_locals s _ s.clock S Nd _).2 hBs,
    hd_ic, hd, ?_, ?_, ?_, ?_, ?_, hgwds, hpl_eq, hnext_int, ?_, hnwdb⟩
  · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "si" by decide, hlsi]
  · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "pl" by decide, hlpl]
  · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "wr" by decide, hlwr]
  · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "nwd" by decide, hlnwd]
  · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · intro _
    rw [hnext_nat]
    simpa using hi44

theorem hoare_decCall_fall_shaped {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {names : List String} {name fname : MlS} {shape : ShapeHOL}
    {arguments : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hname : ∀ n ∈ names, ofString n ≠ name)
    (hQ : LocalsOnly names Q)
    (hres : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (values : List (ValueHOL 64))
      (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
      (value : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode → P state →
      evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        arguments = some values →
      lookupCodeHOLFinite state.code.lookup fname values = some (body, callee, returnShape) →
      evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
        (some (.returned value), post) →
      shapeEqHOL (shapeOfHOLExact value) shape = true →
      R (setVarHOLFinite name value { post with locals := state.locals }))
    (hcont : Hoare R cont (fun r t => r = none → Q t)) :
    Hoare P (.decCall name shape fname arguments cont) (fun r t => r = none → Q t) := by
  refine ⟨fun {F} s hcode hP _ hr => ?_⟩
  rcases hrun : evaluateHOLFiniteState s (.decCall name shape fname arguments cont) with ⟨r, post⟩
  rw [hrun] at hr
  dsimp only at hr
  subst hr
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun
  rcases hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments with _ | values
  · rw [hargs] at hrun; simp at hrun
  · rw [hargs] at hrun; dsimp only at hrun
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · rw [hl] at hrun; simp at hrun
    · rw [hl] at hrun; dsimp only at hrun
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hrun; simp at hrun
      · rw [if_neg hz] at hrun
        have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body').1
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨bres, bpost⟩
        rw [hb] at hrun hmeta
        dsimp only at hmeta
        cases bres with
        | none => simp at hrun
        | some br =>
          cases br with
          | returned v =>
            dsimp only at hrun
            split at hrun
            · rename_i hcond
              set resumed := setVarHOLFinite name v { bpost with locals := s.locals }
              have hresR : R resumed :=
                hres s values body' callee ret' v bpost hcode hP hargs hl hb
                  ((Bool.and_eq_true _ _).mp hcond).1
              have hresCode : resumed.code = originalRuntimeCode := hmeta.trans hcode
              rcases hc : evaluateHOLFiniteState resumed cont with ⟨cres, cpost⟩
              rw [hc] at hrun
              dsimp only at hrun
              obtain ⟨rfl, hpost_eq⟩ := Prod.mk.inj hrun
              have hQc0 := hcont.run resumed hresCode hresR (by rw [hc]; simp)
              rw [hc] at hQc0
              have hQc : Q cpost := hQc0 rfl
              dsimp only
              rw [← hpost_eq]
              exact hQ cpost _ cpost.clock
                (fun n hn => resVarEq_lookup_ne _ _ _ _ (hname n hn)) hQc
            · simp at hrun
          | _ => simp [emptyLocalsHOLFinite] at hrun

theorem ph_encode_withdrawal_resume_b
    (wenc : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "encode_withdrawal_rlp"))
    (denc : ResumesInDomain (fun s => (locN s "wd", 1)) (ofString "encode_withdrawal_rlp")) :
    ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (values : List (ValueHOL 64))
      (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
      (value : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode →
      (PH_LOOP_B state ∧
        CondTrue (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nwd"))) state) →
      evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        ph_withdrawal_args = some values →
      lookupCodeHOLFinite state.code.lookup (ofString "encode_withdrawal_rlp") values =
        some (body, callee, returnShape) →
      evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
        (some (.returned value), post) →
      shapeEqHOL (shapeOfHOLExact value) (.comb [.one, .one]) = true →
      PH_LOOP_EB (setVarHOLFinite (ofString "e") value { post with locals := state.locals }) := by
  intro F state values body callee returnShape value post hcode ⟨hP, hcond⟩ hargs hl hb hsh
  obtain ⟨w_si, w_pl, w_wr, w_nwd, w_wds, w_i, S, Nd, hIA, hBs, hd_ic, hd,
    hlsi, hlpl, hlwr, hlnwd, hli, hgwds, hpl_eq, hi0, hprev, hnwdb⟩ := hP
  have hilt := ph_withdrawal_active_lt hli hlnwd hcond
  have hn0 : 0 < w_nwd.toInt := by omega
  have hbase_lt : memW state (w_pl + 48#64).toNat < heapEnd := (hnwdb hn0).1
  unfold ph_withdrawal_args at hargs
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact] at hargs
  set e_arg : ExpHOL 64 :=
    .op .add
      [.load .one (.op .add [.var .local (ofString "pl"), .const 48#64]),
       .panop .mul [.var .local (ofString "i"), .const 44#64]]
  rcases he_arg : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) e_arg with _ | v_arg
  · rw [he_arg] at hargs; simp at hargs
  · rw [he_arg] at hargs
    have hv_list : values = [v_arg] := by simpa using hargs.symm
    subst values
    have hl_fn : state.code.lookup (ofString "encode_withdrawal_rlp") =
        some ([(ofString "wd", .one)],
          sourceFnBody Guest.Software.guestFn_encode_withdrawal_rlp, .comb [.one, .one]) := by
      rw [hcode]
      exact lookup_encode_withdrawal_rlp_fn
    have hargs_fin : evalListHOLFinite state
        (h := fun a => Classical.propDecidable (state.memaddrs a)) [e_arg] = some [v_arg] := by
      rw [evalListHOLFinite_eq_toExact]
      simp [evalListHOLExact, he_arg]
    obtain ⟨hsh_arg, hcallee_wd⟩ := callee_param_one_exp state (ofString "encode_withdrawal_rlp")
      (ofString "wd") .one _ (.comb [.one, .one]) hl_fn e_arg v_arg [v_arg]
      body callee returnShape he_arg hargs_fin hl
    have hsh_arg_eq := (shapeEqHOL_eq_true _ _).1 hsh_arg
    rcases v_arg with ⟨⟨w_arg⟩⟩ | _ | _ <;> try simp [shapeOfHOLExact] at hsh_arg_eq
    obtain ⟨w_base, w_mul, hw_base, hw_mul, harg_eq⟩ := evalAt_add2_words (s := state) he_arg
    obtain ⟨a48, w_base', ha48, hw_base_val, hmem48, _⟩ := evalAt_load_one_word hIA.1.1 hw_base
    have ha48_eq := evalAt_add_local_const (off := 48) hlpl ha48
    subst a48
    have hw_base_eq : w_base' = w_base := by simpa using hw_base_val.symm
    subst w_base'
    obtain ⟨wi', hwi', hmul_eq⟩ := evalAt_panOp_mul_const (c := 44) hw_mul
    have hwi_eq : wi' = w_i := by simpa [evalAt, evalHOLExact, hli] using hwi'.symm
    subst wi'
    cases hmul_eq
    have hW_state : WorldOK state := ⟨hIA.1, S, (worldTyped_iff_with state S).2 ⟨Nd, hIA.2.1⟩⟩
    have hstep := FunSpec.at_lookup wenc state hcode [.val (.word w_arg)] body callee returnShape hl
      (localsFree_worldOK state callee (state.clock - 1) hW_state) (by rw [hb]; simp)
    rw [hb] at hstep; dsimp only at hstep
    have hws := hstep (Or.inl ⟨value, rfl⟩)
    have hdom0 := FunSpec.at_lookup denc state hcode [.val (.word w_arg)] body callee returnShape hl
      (localsFree_guestInv state callee (state.clock - 1) hIA.1.1) (by rw [hb]; simp)
    rw [hb] at hdom0; dsimp only at hdom0
    have hloc_wd : locN (callEntryStateHOLFinite state callee) "wd" = w_arg.toNat := by
      simp [callEntryStateHOLFinite, locN, hcallee_wd]
    have hinside : Inside (w_arg.toNat, 1) sourceBase heapEnd := by
      have hd1 := hdom0 (Or.inl ⟨value, rfl⟩) (by decide)
      simpa [hloc_wd] using hd1
    have hprog := ph_withdrawal_domain_progress w_base w_i
      (fun hp => ⟨by rw [hmem48]; exact hbase_lt, hprev hp⟩)
      (by rwa [← harg_eq])
    have hIA_entry : InputAtWith (callEntryStateHOLFinite state callee) S Nd w_si.toNat :=
      (inputAtWith_with_locals state callee (state.clock - 1) S Nd w_si.toNat).2 hIA
    have hBs_entry : AllBlocksGood (callEntryStateHOLFinite state callee) S Nd
        [(w_wr.toNat, 32), (w_wds.toNat, (w_nwd * 16#64 + 16#64).toNat)] :=
      (allBlocksGood_with_locals state callee (state.clock - 1) S Nd _).2 hBs
    obtain ⟨S', Nd', hIA_post, hBs_post, _, hu_ic, _⟩ :=
      WorldStep_preserves_inputAndBlocks hIA_entry hBs_entry hws
        (fun _ hj => by simp at hj) (fun _ hj => by simp at hj)
        (fun _ _ _ hj => by simp at hj) (fun _ _ _ hj => by simp at hj)
    have hic := inputCells_eq_of_unhit hIA_entry hu_ic
    have hm48 := ph_payload_word_unhit hIA hpl_eq hu_ic 48 (by omega) (by omega)
    have hgwds_post : post.globals.lookup (ofString "wd_rlp_slices") = some (.val (.word w_wds)) := by
      have hg_eq := hws.2.2.1 (ofString "wd_rlp_slices")
        (by simp [show ofString "wd_rlp_slices" ≠ ofString "heap_ptr" by decide])
      simpa [callEntryStateHOLFinite, hgwds] using hg_eq.symm
    have hsh_eq := (shapeEqHOL_eq_true _ _).1 hsh
    cases value with
    | val _ => simp [shapeOfHOLExact] at hsh_eq
    | nStruct _ _ => simp [shapeOfHOLExact] at hsh_eq
    | rStruct vs =>
      simp only [shapeOfHOLExact, ShapeHOL.comb.injEq] at hsh_eq
      rcases vs with _ | ⟨v0, _ | ⟨v1, _ | _⟩⟩ <;> simp at hsh_eq
      rcases hsh_eq with ⟨hv0, hv1⟩
      cases v0 with
      | rStruct _ => simp [shapeOfHOLExact] at hv0
      | nStruct _ _ => simp [shapeOfHOLExact] at hv0
      | val wl0 =>
        cases wl0 with
        | word e0 =>
          cases v1 with
          | rStruct _ => simp [shapeOfHOLExact] at hv1
          | nStruct _ _ => simp [shapeOfHOLExact] at hv1
          | val wl1 =>
            cases wl1 with
            | word e1 =>
              refine ⟨w_si, w_pl, w_wr, w_nwd, w_wds, w_i, e0, e1, S', Nd',
                (inputAtWith_with_locals post _ post.clock S' Nd' w_si.toNat).2 hIA_post,
                (allBlocksGood_with_locals post _ post.clock S' Nd' _).2 hBs_post,
                ?_, hd, ?_, ?_, ?_, ?_, ?_, ?_, hgwds_post, ?_, hi0, hilt, hprog.2, ?_⟩
              · change IvlsDisj (inputCells post w_si.toNat) _
                rw [hic.2.2]; exact hd_ic
              · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
                  show ofString "e" ≠ ofString "si" by decide, hlsi]
              · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
                  show ofString "e" ≠ ofString "pl" by decide, hlpl]
              · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
                  show ofString "e" ≠ ofString "wr" by decide, hlwr]
              · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
                  show ofString "e" ≠ ofString "nwd" by decide, hlnwd]
              · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
                  show ofString "e" ≠ ofString "i" by decide, hli]
              · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
              · change w_pl.toNat = memW post w_si.toNat
                rw [hic.1]; exact hpl_eq
              · intro hp
                change memW post (w_pl + 48#64).toNat < heapEnd ∧ _
                rw [hm48]; exact hnwdb hp

theorem ph_withdrawal_body_hoare_b
    (wenc : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "encode_withdrawal_rlp"))
    (denc : ResumesInDomain (fun s => (locN s "wd", 1)) (ofString "encode_withdrawal_rlp")) :
    Hoare
      (fun s => PH_LOOP_B s ∧
        CondTrue (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nwd"))) s)
      ph_withdrawal_body
      (fun r t => r = none → PH_LOOP_B t) := by
  unfold ph_withdrawal_body
  exact hoare_decCall_fall_shaped
    (fun n hn => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn; rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide)
    ph_loop_b_localsOnly
    (ph_encode_withdrawal_resume_b wenc denc)
    (Hoare.seq_fall ph_withdrawal_store0_b
      (Hoare.seq_fall ph_withdrawal_store1_b ph_withdrawal_inc_b))

theorem ph_withdrawal_loop_hoare_b
    (wenc : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "encode_withdrawal_rlp"))
    (denc : ResumesInDomain (fun s => (locN s "wd", 1)) (ofString "encode_withdrawal_rlp")) :
    Hoare PH_LOOP_B ph_withdrawal_loop (fun r t => r = none → PH_LOOP_B t) :=
  Hoare.while_preserve_ncb ph_loop_b_decClock rfl (ph_withdrawal_body_hoare_b wenc denc)

private theorem ph_h_false_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : PH_H false s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1

private theorem ph_oh_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : PH_OH s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1

private theorem ph_tmp_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : PH_TMP s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1

private theorem ph_txr_guestInv (b : Bool) {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : PH_TXR b s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1

private theorem ph_wr_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : PH_WR s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1

private theorem ph_rh_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : PH_RH s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1

private theorem ph_s0_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : PH_S0 s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1

private theorem ph_nwd_b_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : PH_NWD_B s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1

private theorem ph_bl_post_worldOK {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : PH_BL_POST s) : WorldOK s := by
  obtain ⟨⟨_, _, _, _, _, _, _, S, Nd, hIA, _⟩, _⟩ := h
  exact ⟨hIA.1, S, (worldTyped_iff_with s S).2 ⟨Nd, hIA.2.1⟩⟩

private theorem ph_store_h0_one :
    Hoare (PH_H false)
      (.store (.op .add [.var .local (ofString "h"), .const 0#64]) (.const 1#64))
      (fun r t => r = none → PH_H false t) :=
  ph_h_store_simple false 0 _ (by omega) (by omega) (by simp) (Or.inl rfl)

private theorem ph_store_h8_raw0 :
    Hoare (PH_H false)
      (.store (.op .add [.var .local (ofString "h"), .const 8#64])
        (.op .add [.var .local (ofString "raw"), .const 0#64]))
      (fun r t => r = none → PH_H false t) :=
  ph_h_store_simple false 8 _ (by omega) (by omega) (by simp) (Or.inr (Or.inl ⟨_, _, rfl⟩))

private theorem ph_withdrawal_loop_bound_b
    (henc : TerminatingFunBoundedOn GuestInv (ofString "encode_withdrawal_rlp") K.«encode_withdrawal_rlp») :
    TerminatingProgBoundedOn PH_LOOP_B ph_withdrawal_loop
      ((2 ^ 64 + 1) * ((K.«encode_withdrawal_rlp» + 1) + 1)) := by
  intro F s hc hP hnt
  exact ph_withdrawal_loop_bound henc s hc (ph_loop_guestInv (ph_loop_b_loop hP)) hnt

private theorem ph_withdrawal_loop_hoare_loop
    (wenc : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "encode_withdrawal_rlp"))
    (denc : ResumesInDomain (fun s => (locN s "wd", 1)) (ofString "encode_withdrawal_rlp")) :
    Hoare PH_LOOP_B ph_withdrawal_loop (fun r t => r = none → PH_LOOP t) :=
  ⟨fun s hc hP hnt hr =>
    ph_loop_b_loop ((ph_withdrawal_loop_hoare_b wenc denc).run s hc hP hnt hr)⟩

private def PH_H_OH : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => PH_H false t ∧ ∃ w_oh : BitVec 64, t.locals.lookup (ofString "oh") = some (.val (.word w_oh))

private def PH_TXR_Z8 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => PH_TXR true t ∧ ∃ w_z8 : BitVec 64, t.locals.lookup (ofString "z8") = some (.val (.word w_z8))

private theorem ph_keccak_oh'
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
      (fun r t => r = none → PH_H_OH t) :=
  ph_keccak_oh wkec

private theorem ph_store_h16_oh' :
    Hoare PH_H_OH
      (.store (.op .add [.var .local (ofString "h"), .const 16#64]) (.var .local (ofString "oh")))
      (fun r t => r = none → PH_H false t) :=
  ph_store_h16_oh

private theorem ph_memzero_z8d'
    (wmz : WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")]) []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "memzero")) :
    Hoare PH_Z8D
      (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "z8"), .const 8#64])
      (fun r t => r = none → PH_TXR_Z8 t) :=
  ph_memzero_z8d wmz

private theorem ph_store_h152_z8' :
    Hoare PH_TXR_Z8
      (.store (.op .add [.var .local (ofString "h"), .const 152#64]) (.var .local (ofString "z8")))
      (fun r t => r = none → PH_TXR true t) :=
  ph_store_h152_z8

theorem «gbody_payload_header» : GBody.«payload_header» := by
  intro hal hbl hmpt hcrh heer henc hkec hmz wal rtal _wbl wmpt wenc denc wkec wmz _zvmz
  refine ⟨_, _, _, R13PayloadStateInit.lookup_payload_header, ?_⟩
  apply ph_entry_dec_pl_raw
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_payload_header,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil, List.map]
  apply TerminatingProgBoundedOn.mono_bound (a := _)
  · apply TerminatingProgBoundedOn.decCall_on hal _ _ _
      (callEntryOn_of_imp localsFree_guestInv ph_s0_guestInv _ _)
      (ph_alloc_h wal rtal)
    apply TerminatingProgBoundedOn.seq_hoare
      (TerminatingProgBoundedOn.call_on hmz _ _
        (callEntryOn_of_imp localsFree_guestInv ph_h_false_guestInv _ _))
      (ph_memzero_h wmz)
    apply TerminatingProgBoundedOn.seq_hoare
      (TerminatingProgBoundedOn.of_clock (fun {F} s => clock_store s _ _))
      ph_store_h0_one
    apply TerminatingProgBoundedOn.seq_hoare
      (TerminatingProgBoundedOn.of_clock (fun {F} s => clock_store s _ _))
      ph_store_h8_raw0
    apply TerminatingProgBoundedOn.decCall_on hal _ _ _
      (callEntryOn_of_imp localsFree_guestInv ph_h_false_guestInv _ _)
      (ph_alloc_oh wal rtal)
    apply TerminatingProgBoundedOn.decCall_on hal _ _ _
      (callEntryOn_of_imp localsFree_guestInv ph_oh_guestInv _ _)
      (ph_alloc_tmp wal rtal)
    apply TerminatingProgBoundedOn.seq_hoare
      (TerminatingProgBoundedOn.of_clock (fun {F} s => clock_storeByte s _ _))
      ph_storeByte_tmp
    apply TerminatingProgBoundedOn.seq_hoare_trans
      (TerminatingProgBoundedOn.call_on hkec _ _
        (callEntryOn_of_imp localsFree_guestInv ph_tmp_guestInv _ _))
      (ph_keccak_oh' wkec)
    apply TerminatingProgBoundedOn.seq_hoare_trans
      (TerminatingProgBoundedOn.of_clock (fun {F} s => clock_store s _ _))
      ph_store_h16_oh'
    apply TerminatingProgBoundedOn.seq_hoare
      (TerminatingProgBoundedOn.of_clock (fun {F} s => clock_store s _ _))
      ph_store_h24_raw32
    apply TerminatingProgBoundedOn.seq_hoare
      (TerminatingProgBoundedOn.of_clock (fun {F} s => clock_store s _ _))
      ph_store_h32_raw52
    apply TerminatingProgBoundedOn.decCall_on hal _ _ _
      (callEntryOn_of_imp localsFree_guestInv ph_h_false_guestInv _ _)
      (ph_alloc_txr wal rtal)
    apply TerminatingProgBoundedOn.seq_hoare
      (TerminatingProgBoundedOn.of_clock (fun {F} s => clock_store s _ _))
      ph_store_h40_txr
    apply TerminatingProgBoundedOn.seq_hoare
      (TerminatingProgBoundedOn.of_clock (fun {F} s => clock_store s _ _))
      ph_store_h48_raw84
    apply TerminatingProgBoundedOn.seq_hoare
      (TerminatingProgBoundedOn.of_clock (fun {F} s => clock_store s _ _))
      ph_store_h56_raw116
    apply TerminatingProgBoundedOn.seq_hoare
      (TerminatingProgBoundedOn.of_clock (fun {F} s => clock_store s _ _))
      ph_store_h64_zero
    apply TerminatingProgBoundedOn.seq_hoare
      (TerminatingProgBoundedOn.of_clock (fun {F} s => clock_store s _ _))
      ph_store_h96_pl80
    apply TerminatingProgBoundedOn.seq_hoare
      (TerminatingProgBoundedOn.of_clock (fun {F} s => clock_store s _ _))
      ph_store_h104_pl88
    apply TerminatingProgBoundedOn.seq_hoare
      (TerminatingProgBoundedOn.of_clock (fun {F} s => clock_store s _ _))
      ph_store_h112_pl96
    apply TerminatingProgBoundedOn.seq_hoare
      (TerminatingProgBoundedOn.of_clock (fun {F} s => clock_store s _ _))
      ph_store_h120_pl104
    apply TerminatingProgBoundedOn.seq_hoare
      (TerminatingProgBoundedOn.of_clock (fun {F} s => clock_store s _ _))
      ph_store_h128_pl16
    apply TerminatingProgBoundedOn.seq_hoare_trans
      (TerminatingProgBoundedOn.of_clock (fun {F} s => clock_store s _ _))
      ph_store_h136_pl24
    apply TerminatingProgBoundedOn.seq_hoare
      (TerminatingProgBoundedOn.of_clock (fun {F} s => clock_store s _ _))
      ph_store_h144_raw372
    apply TerminatingProgBoundedOn.decCall_on hal _ _ _
      (callEntryOn_of_imp localsFree_guestInv (ph_txr_guestInv true) _ _)
      (ph_alloc_z8d wal rtal)
    apply TerminatingProgBoundedOn.seq_hoare_trans
      (TerminatingProgBoundedOn.call_on hmz _ _
        (callEntryOn_of_imp localsFree_guestInv (fun _ h => ph_z8d_guestInv h) _ _))
      (ph_memzero_z8d' wmz)
    apply TerminatingProgBoundedOn.seq_hoare_trans
      (TerminatingProgBoundedOn.of_clock (fun {F} s => clock_store s _ _))
      ph_store_h152_z8'
    apply ph_dec_bf _
    apply TerminatingProgBoundedOn.seq_hoare_trans
      (TerminatingProgBoundedOn.of_clock (fun {F} s => clock_store s _ _))
      ph_store_h160_bf
    apply TerminatingProgBoundedOn.decCall_on hal _ _ _
      (callEntryOn_of_imp localsFree_guestInv (ph_txr_guestInv true) _ _)
      (ph_alloc_wr wal rtal)
    apply TerminatingProgBoundedOn.seq_hoare
      (TerminatingProgBoundedOn.of_clock (fun {F} s => clock_store s _ _))
      ph_store_h192_wr
    apply TerminatingProgBoundedOn.seq_hoare
      (TerminatingProgBoundedOn.of_clock (fun {F} s => clock_store s _ _))
      ph_store_h200_pl112
    apply TerminatingProgBoundedOn.seq_hoare
      (TerminatingProgBoundedOn.of_clock (fun {F} s => clock_store s _ _))
      ph_store_h208_pl120
    apply TerminatingProgBoundedOn.seq_hoare
      (TerminatingProgBoundedOn.of_clock (fun {F} s => clock_store s _ _))
      ph_store_h216_si24
    apply TerminatingProgBoundedOn.decCall_on hal _ _ _
      (callEntryOn_of_imp localsFree_guestInv ph_wr_guestInv _ _)
      (ph_alloc_rh wal rtal)
    apply TerminatingProgBoundedOn.seq_hoare
      (TerminatingProgBoundedOn.of_clock (fun {F} s => clock_store s _ _))
      ph_store_h224_rh
    apply TerminatingProgBoundedOn.decCall_on hal _ _ _
      (callEntryOn_of_imp localsFree_guestInv ph_rh_guestInv _ _)
      (ph_alloc_bh wal rtal)
    apply TerminatingProgBoundedOn.seq_hoare
      (TerminatingProgBoundedOn.of_clock (fun {F} s => clock_store s _ _))
      ph_store_h232_bh
    apply TerminatingProgBoundedOn.seq_hoare
      (TerminatingProgBoundedOn.of_clock (fun {F} s => clock_store s _ _))
      ph_store_h240_pl128
    apply TerminatingProgBoundedOn.decCall_on hbl _ _ _
      ph_block_rlp_length_entry
      ph_block_rlp_length_resume
    apply TerminatingProgBoundedOn.seq_hoare
      (TerminatingProgBoundedOn.ite_on
        (TerminatingProgBoundedOn.of_clock (fun {F} s => clock_raise s _ _))
        (TerminatingProgBoundedOn.of_clock (fun {F} s => clock_skip s)))
      ph_bl_check_post
    apply TerminatingProgBoundedOn.seq_hoare_trans
      (TerminatingProgBoundedOn.call_on hmpt _ _
        (callEntryOn_of_imp localsFree_worldOK ph_bl_post_worldOK _ _))
      (ph_build_mpt_txr_b wmpt)
    apply ph_dec_nwd_post_b
    apply TerminatingProgBoundedOn.seq_hoare_trans
      (TerminatingProgBoundedOn.call_on hal _ _
        (callEntryOn_of_imp localsFree_guestInv ph_nwd_b_guestInv _ _))
      (ph_alloc_wd_rlp_slices_b wal rtal)
    apply ph_dec_i_b
    apply TerminatingProgBoundedOn.seq_hoare_trans
      (ph_withdrawal_loop_bound_b henc)
      (ph_withdrawal_loop_hoare_loop wenc denc)
    exact ph_second_mpt_tail hmpt (ph_guestInv_tail heer hcrh hkec _ _ _ _)
  · unfold K.«payload_header»
    try simp only [show ∀ a b : Nat, Nat.max a b = max a b from fun _ _ => rfl]
    omega

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
