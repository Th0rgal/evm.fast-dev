import InitECandidate.Solver.Wave8GuestInv.Deliveries.M26.Common

/-! Return-typing contract `rt_node_new_ext` for micro-shard `m26` (`wave8/contracts-m26`),
checked against frozen revision 9 (`8a79d9f28`, tag `wave8-spec-frozen-r9`).

`node_new_ext` (AST line 10021, index 257): returns a fresh 56-byte heap node, separated from the
decoder scratch stack.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8Contracts.M26

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

private theorem lookup_node_new_ext :
    originalRuntimeCode.lookup (ofString "node_new_ext") =
      some ([(ofString "nib", .one), (ofString "nlen", .one), (ofString "child", .one)],
        sourceFnBody Guest.Software.guestFn_node_new_ext, .one) :=
  lookup_of_guestAst_getElem 257 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_new_ext) rfl

private theorem Ret.seq_store_any {F : Type} {s : PanSemStateFiniteExact 64 F} {d e : ExpHOL 64}
    {b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hb : ∀ m : BitVec 64 → HolWordLab 64, Ret { s with memory := m } b Φ) :
    Ret s (.seq (.store d e) b) Φ :=
  Ret.seq_store (fun _ _ m _ _ _ => hb m)

private theorem Ret.ns_store_any {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C}
    {d e : ExpHOL 64} {b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hb : ∀ M' : BitVec 64 → HolWordLab 64, Ret (NS s L G M' C) b Φ) :
    Ret (NS s L G M C) (.seq (.store d e) b) Φ :=
  Ret.seq_store_any hb

/-- `node_new_ext` (AST line 10021): returns a fresh 56-byte heap node, separated from the decoder
scratch stack. -/
theorem rt_node_new_ext :
    Returns ArenaReady (fun s post p => FreshBlock s post p 56)
    (ofString "node_new_ext") := by
  refine ⟨_, _, _, lookup_node_new_ext, ?_⟩
  intro F s hcode hAR _ _hnt v hret
  obtain ⟨hG, hA⟩ := hAR
  obtain ⟨hp, fp, sp, hhp, hhp_eq, hfp, hfp_eq, hsp, hsp_eq⟩ := arenaOK_globals s hA
  have hbody : sourceFnBody Guest.Software.guestFn_node_new_ext =
      .decCall (ofString "nd") .one (ofString "alloc") [.const 56]
        (.seq (.store (.op .add [.var .local (ofString "nd"), .const 0]) (.const 2))
          (.seq (.store (.op .add [.var .local (ofString "nd"), .const 8]) (.const 0))
            (.seq (.store (.op .add [.var .local (ofString "nd"), .const 16]) (.const 0))
              (.seq (.store (.op .add [.var .local (ofString "nd"), .const 24]) (.const 0))
                (.seq (.store (.op .add [.var .local (ofString "nd"), .const 32]) (.var .local (ofString "nib")))
                  (.seq (.store (.op .add [.var .local (ofString "nd"), .const 40]) (.var .local (ofString "nlen")))
                    (.seq (.store (.op .add [.var .local (ofString "nd"), .const 48]) (.var .local (ofString "child")))
                      (.return (.var .local (ofString "nd")))))))))) := rfl
  have hrun : Ret s (sourceFnBody Guest.Software.guestFn_node_new_ext)
      (fun rv post => ∃ w : BitVec 64, rv = .val (.word w) ∧
        ArenaReady post ∧ AllocatorGrows s post ∧ FreshBlock s post w.toNat 56) := by
    rw [hbody]
    apply Ret.of_NS
    refine Ret.ns_alloc hcode 56 rfl hp hhp ?_
    intro hcmp1 hcmp2
    apply Ret.ns_store_any; intro M1
    apply Ret.ns_store_any; intro M2
    apply Ret.ns_store_any; intro M3
    apply Ret.ns_store_any; intro M4
    apply Ret.ns_store_any; intro M5
    apply Ret.ns_store_any; intro M6
    apply Ret.ns_store_any; intro M7
    apply Ret.ns_ret
    intro val hval
    have hval_eq : val = .val (.word hp) := by
      simp [ev, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE] at hval
      exact hval.symm
    subst hval_eq
    set q : BitVec 64 := (hp + (56 + 7)) &&& ((0 : BitVec 64) - 8)
    set post : PanSemStateFiniteExact 64 F :=
      { (NS s (emptyLocalsHOLFinite (NS s (s.locals.update (ofString "nd", .val (.word hp)))
            (s.globals.update (ofString "heap_ptr", .val (.word q))) M7 (s.clock - 1))).locals
          (s.globals.update (ofString "heap_ptr", .val (.word q))) M7 (s.clock - 1)) with
        locals := HolFiniteMapExact.resVarEq
          (emptyLocalsHOLFinite (NS s (s.locals.update (ofString "nd", .val (.word hp)))
            (s.globals.update (ofString "heap_ptr", .val (.word q))) M7 (s.clock - 1))).locals
          (ofString "nd", s.locals.lookup (ofString "nd")) }
    refine ⟨hp, rfl, ?_⟩
    have hhp_hi : hp.toNat ≤ heapLimit := by rw [hhp_eq]; exact hA.2.1
    have hhp_al : hp.toNat % 8 = 0 := by rw [hhp_eq]; exact hA.2.2.2.2.2.1
    obtain ⟨hq_eq, hq_hi, hq_al, hp_le_q⟩ := alloc_arith hp 56 hhp_hi hhp_al hcmp1 hcmp2
    change q.toNat = _ at hq_eq
    change q.toNat ≤ heapLimit at hq_hi
    change q.toNat % 8 = 0 at hq_al
    change hp.toNat ≤ q.toNat at hp_le_q
    have h56 : ((56 : BitVec 64).toNat + 7) / 8 * 8 = 56 := by decide
    rw [h56] at hq_eq
    have hpost_hp : globN post "heap_ptr" = q.toNat := by
      simp [post, globN, HolFiniteMapExact.lookup_update, FUPDATE]
    have hpost_fp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by
      simp [post, globN, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
    have hpost_sp : globN post "scratch_ptr" = globN s "scratch_ptr" := by
      simp [post, globN, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
    have hG_post : GuestInv post := ⟨hG.code, hG.memaddrs, hG.shMemaddrs, hG.baseAddr⟩
    have hA_post : ArenaOK post := by
      unfold ArenaOK
      rw [hpost_hp, hpost_fp, hpost_sp]
      refine ⟨?_, hq_hi, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1, hq_al, hA.2.2.2.2.2.2.1,
        hA.2.2.2.2.2.2.2.1,
        globalsWord_update (s := s) (t := post) (ofString "heap_ptr") q rfl hA.2.2.2.2.2.2.2.2⟩
      have hsb_le : sourceBase ≤ hp.toNat := by rw [hhp_eq]; exact hA.1
      omega
    have hAG : AllocatorGrows s post := by
      refine ⟨?_, by rw [hpost_sp]⟩
      rw [hpost_hp, ← hhp_eq]
      exact hp_le_q
    have hlim_le_he : heapLimit ≤ heapEnd := by decide
    have hWOK : WordsOK post (hp.toNat, (56 + 7) / 8 * 8) := by
      change WordsOK post (hp.toNat, 56)
      apply wordsOK_of_guestInv post hG_post hp.toNat 56 hhp_al (by decide)
      · rw [hhp_eq]; exact hA.1
      · omega
    refine ⟨⟨hG_post, hA_post⟩, hAG, hhp_al, ?_, hWOK⟩
    change Inside (hp.toNat, 56) (globN s "heap_ptr") (globN post "heap_ptr")
    rw [← hhp_eq, hpost_hp]
    exact ⟨le_rfl, le_of_eq hq_eq.symm⟩
  exact hrun v hret

end InitECandidate.Solver.Wave8Contracts.M26
