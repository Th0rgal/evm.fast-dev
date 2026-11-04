import InitECandidate.Solver.Wave8GuestInv.R10Shards.EvmFrameSpecs
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmHtabStep
import InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M11.RlpMemcpyLemmas

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
open InitECandidate.Solver.Wave8GuestInv.EvmBase
open InitECandidate.Solver.Wave8GuestInv.EvmStepLemmas
open InitECandidate.Solver.Wave8GuestInv.EvmFrameSpecs
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue (noCatchableRaise
  evaluate_noCatchableRaise htabMutCallees htabMutCallees_good)

theorem lookup_sk_make :
    originalRuntimeCode.lookup (ofString "sk_make") =
      some ([(ofString "addr", .one), (ofString "key", .one)],
        sourceFnBody Guest.Software.guestFn_sk_make, .one) :=
  lookup_of_guestAst_getElem 360 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_sk_make) rfl

theorem m11Bre_to_evmBre {F : Type} {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hnz : ∀ i ∈ Rl, i.2 ≠ 0)
    (h : M11.ByteRegionEffect s post Rl) :
    EvmStepLemmas.ByteRegionEffect s post Rl :=
  ⟨h.code, h.memaddrs, h.shMemaddrs, h.baseAddr, h.be, h.globals,
   h.out_dom, fun a ha => h.cell_frame a (fun i hi hch => ha i hi (hnz i hi) hch),
   h.byte_frame⟩

private theorem sk_make_zero_err {F : Type}
    (s : PanSemStateFiniteExact 64 F) (src0 : BitVec 64)
    (hma : s.memaddrs = ordinaryDomain)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word 0)))
    (hsrc : s.locals.lookup (ofString "src") = some (.val (.word src0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word 20)))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memcpy)).1 ≠ some .timeOut) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memcpy)).1 = some .error := by
  have hnot_dom0 : ¬ ordinaryDomain (0 : BitVec 64) := by
    rw [ordinaryDomain_iff]; simp
  have hnot_dom_al0 : ¬ ordinaryDomain (panByteAlignHOL (0 : BitVec 64)) := by
    have hal0 : panByteAlignHOL (0 : BitVec 64) = 0 := BitVec.eq_of_toNat_eq (by rw [panByteAlign_toNat64]; rfl)
    rw [hal0]; exact hnot_dom0
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memcpy,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt ⊢
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  have hev0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.const (BitVec.ofNat 64 0)) = some (.val (.word 0)) := rfl
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [hev0] at hnt ⊢; dsimp only at hnt ⊢; rw [if_pos hsh0] at hnt ⊢
  set s1 := setVarHOLFinite (ofString "i") (.val (.word 0)) s
  have hs1_dst : s1.locals.lookup (ofString "dst") = some (.val (.word 0)) := by
    have hne : ofString "i" ≠ ofString "dst" := by decide
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hdst]
  have hs1_src : s1.locals.lookup (ofString "src") = some (.val (.word src0)) := by
    have hne : ofString "i" ≠ ofString "src" := by decide
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hsrc]
  have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word 20)) := by
    have hne : ofString "i" ≠ ofString "n" := by decide
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hn]
  have hs1_i : s1.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  change (evaluateHOLFiniteState s1 _).1 = some .error
  have hnt' : (evaluateHOLFiniteState s1 _).1 ≠ some .timeOut := hnt
  clear hnt
  rw [evaluateHOLFiniteState_seq_line780] at hnt' ⊢
  rw [evaluateHOLFiniteState_ite] at hnt' ⊢
  rcases hcond : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
      (.cmp .equal (.op .and [.op .or [.var .local (ofString "dst"), .var .local (ofString "src")], .const (BitVec.ofNat 64 7)]) (.const (BitVec.ofNat 64 0))) with _ | cv
  · simp [hcond]
  · have hcv_w : ∃ cw : BitVec 64, cv = .val (.word cw) := by
      simp [evalHOLExact, evalListHOLExact, hs1_dst, hs1_src, wordOpHOL, wordOp, valueIsWord, valueWord,
        Compiler.Encoders.Asm.wordCmpHOL] at hcond
      exact ⟨_, hcond.symm⟩
    obtain ⟨cw, rfl⟩ := hcv_w
    simp only [hcond] at hnt' ⊢
    by_cases hcw0 : cw = 0
    · rw [if_pos hcw0, evaluateHOLFiniteState_skip] at hnt' ⊢
      dsimp only at hnt' ⊢
      rw [evaluateHOLFiniteState_seq_line780] at hnt' ⊢
      rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt' ⊢
      have hc3 : @evalHOLFinite 64 F _ s1 (fun a => Classical.propDecidable (s1.memaddrs a))
          (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)])) =
          some (.val (.word 1)) := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, evalListHOLExact, hs1_n, hs1_i, wordOpHOL, wordOp, valueIsWord, valueWord,
          Compiler.Encoders.Asm.wordCmpHOL]
      simp only [hc3] at hnt' ⊢
      have h10 : (1 : BitVec 64) ≠ 0 := by decide
      rw [if_pos h10] at hnt' ⊢
      by_cases hk0 : s1.clock = 0
      · simp [hk0] at hnt'
      · rw [if_neg hk0]
        have hsb0 : (evaluateHOLFiniteState (decClockHOLFinite s1)
            (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
              (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))).1 =
            some .error := by
          rw [evaluateHOLFiniteState_storeByte]
          have hd' : (decClockHOLFinite s1).locals.lookup (ofString "dst") = some (.val (.word 0)) := hs1_dst
          have hi' : (decClockHOLFinite s1).locals.lookup (ofString "i") = some (.val (.word 0)) := hs1_i
          have ha0 : @evalHOLExact 64 F _ (decClockHOLFinite s1).toExact
              (fun a => Classical.propDecidable ((decClockHOLFinite s1).memaddrs a))
              (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) =
              some (.val (.word 0)) := by
            simp [evalHOLExact, evalListHOLExact, hd', hi', wordOpHOL, wordOp, valueIsWord, valueWord]
          rw [ha0]; dsimp only
          split
          · unfold panMemStoreByteWord8HOL; dsimp only
            have hnd : ¬ (decClockHOLFinite s1).memaddrs (panByteAlignHOL (0 : BitVec 64)) := by
              change ¬ s.memaddrs (panByteAlignHOL (0 : BitVec 64)); rw [hma]; exact hnot_dom_al0
            rw [if_neg hnd]
          · rfl
        rw [evaluateHOLFiniteState_seq_line780]
        rcases hr0 : evaluateHOLFiniteState (decClockHOLFinite s1)
            (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
              (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")]))) with ⟨r0, m0⟩
        rw [hr0] at hsb0; dsimp only at hsb0; subst hsb0
        rfl
    · rw [if_neg hcw0] at hnt' ⊢
      rw [evaluateHOLFiniteState_seq_line780] at hnt' ⊢
      have hlp1 : evaluateHOLFiniteState s1
          (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 32)]))
            (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
                    (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
              (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 8)])
                      (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 8)])))
                (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 16)])
                        (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 16)])))
                  (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 24)])
                          (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 24)])))
                    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 32)]))))))) =
          (none, s1) := by
        rw [evaluateHOLFiniteState_while_fixClockRewrite]
        have hc1 : @evalHOLFinite 64 F _ s1 (fun a => Classical.propDecidable (s1.memaddrs a))
            (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 32)])) =
            some (.val (.word 0)) := by
          rw [evalHOLFinite_eq_toExact]
          simp [evalHOLExact, evalListHOLExact, hs1_n, hs1_i, wordOpHOL, wordOp, valueIsWord, valueWord,
            Compiler.Encoders.Asm.wordCmpHOL]
        simp only [hc1]
        have h00 : ¬ ((0 : BitVec 64) ≠ 0) := by decide
        rw [if_neg h00]
      simp only [hlp1] at hnt' ⊢
      rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt' ⊢
      have hc2 : @evalHOLFinite 64 F _ s1 (fun a => Classical.propDecidable (s1.memaddrs a))
          (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)])) =
          some (.val (.word 1)) := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, evalListHOLExact, hs1_n, hs1_i, wordOpHOL, wordOp, valueIsWord, valueWord,
          Compiler.Encoders.Asm.wordCmpHOL]
      simp only [hc2] at hnt' ⊢
      have h10 : (1 : BitVec 64) ≠ 0 := by decide
      rw [if_pos h10] at hnt' ⊢
      by_cases hk0 : s1.clock = 0
      · simp [hk0] at hnt'
      · rw [if_neg hk0]
        have hst0 : (evaluateHOLFiniteState (decClockHOLFinite s1)
            (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
              (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))).1 =
            some .error := by
          rw [evaluateHOLFiniteState_store]
          have hd' : (decClockHOLFinite s1).locals.lookup (ofString "dst") = some (.val (.word 0)) := hs1_dst
          have hi' : (decClockHOLFinite s1).locals.lookup (ofString "i") = some (.val (.word 0)) := hs1_i
          have ha0 : @evalHOLExact 64 F _ (decClockHOLFinite s1).toExact
              (fun a => Classical.propDecidable ((decClockHOLFinite s1).memaddrs a))
              (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) =
              some (.val (.word 0)) := by
            simp [evalHOLExact, evalListHOLExact, hd', hi', wordOpHOL, wordOp, valueIsWord, valueWord]
          rw [ha0]; dsimp only
          rcases hv : @evalHOLExact 64 F _ (decClockHOLFinite s1).toExact
              (fun a => Classical.propDecidable ((decClockHOLFinite s1).memaddrs a))
              (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])) with _ | v
          · rfl
          · obtain ⟨w, rfl⟩ := M11.eval_load_one_word (decClockHOLFinite s1) _ v hv
            dsimp only
            have hnd : ¬ (decClockHOLFinite s1).memaddrs (0 : BitVec 64) := by
              change ¬ s.memaddrs (0 : BitVec 64); rw [hma]; exact hnot_dom0
            have hps : @panMemStoresHOL 64 _ 0 (flattenHOL (.val (.word w)))
                (decClockHOLFinite s1).memaddrs
                (fun a => Classical.propDecidable ((decClockHOLFinite s1).memaddrs a))
                (decClockHOLFinite s1).memory = none := by
              unfold flattenHOL panMemStoresHOL panMemStoreHOL
              rw [if_neg hnd]
            rw [hps]
        rw [evaluateHOLFiniteState_seq_line780]
        rcases hr0 : evaluateHOLFiniteState (decClockHOLFinite s1)
            (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
              (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")]))) with ⟨r0, m0⟩
        rw [hr0] at hst0; dsimp only at hst0; subst hst0
        rfl

private theorem three_one_word_call_args_local {F : Type}
    (s : PanSemStateFiniteExact 64 F) (fn : MlS) (e1 e2 e3 : ExpHOL 64)
    (body : ProgHOL 64) (retShape : ShapeHOL)
    (p1 p2 p3 : MlS)
    (hcode : s.code.lookup fn = some ([(p1, .one), (p2, .one), (p3, .one)], body, retShape))
    (hok : (evaluateHOLFiniteState s (.call (some (none, none)) fn [e1, e2, e3])).1 ≠ some .error) :
    ∃ w1 w2 w3 : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 = some (.val (.word w1)) ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 = some (.val (.word w2)) ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e3 = some (.val (.word w3)) := by
  rw [evaluateHOLFiniteState_call] at hok
  rcases hv1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | v1
  · simp [evalListHOLFinite, evalListHOLExact, hv1] at hok
  · rcases hv2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 with _ | v2
    · simp [evalListHOLFinite, evalListHOLExact, hv1, hv2] at hok
    · rcases hv3 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e3 with _ | v3
      · simp [evalListHOLFinite, evalListHOLExact, hv1, hv2, hv3] at hok
      · have hevl : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1, e2, e3] =
            some [v1, v2, v3] := by
          simp [evalListHOLFinite, evalListHOLExact, hv1, hv2, hv3]
        rw [hevl] at hok; dsimp only at hok
        rcases hl : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fn [v1, v2, v3] with _ | ⟨b, c, rs⟩
        · rw [hl] at hok; exact absurd rfl hok
        · have hraw : lookupCodeHOLExact s.code.lookup fn [v1, v2, v3] ≠ none := by
            intro hn
            unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
            split at hl
            · simp at hl
            · rename_i hsome; rw [hn] at hsome; simp at hsome
          simp only [lookupCodeHOLExact, hcode, List.length_cons, List.length_nil, ↓reduceIte,
            List.zip, List.zipWith, List.all, Bool.and_true, Bool.and_eq_true] at hraw
          have hshapes : shapeEqHOL .one (shapeOfHOLExact v1) = true ∧
              shapeEqHOL .one (shapeOfHOLExact v2) = true ∧
              shapeEqHOL .one (shapeOfHOLExact v3) = true := by
            by_contra hns; simp [hns] at hraw
          have hw : ∀ v : ValueHOL 64, shapeEqHOL .one (shapeOfHOLExact v) = true → ∃ w, v = .val (.word w) := by
            intro v hsv
            rcases v with ⟨⟨w⟩⟩ | _ | _
            · exact ⟨w, rfl⟩
            · simp [shapeOfHOLExact, shapeEqHOL] at hsv
            · simp [shapeOfHOLExact, shapeEqHOL] at hsv
          obtain ⟨w1, rfl⟩ := hw v1 hshapes.1
          obtain ⟨w2, rfl⟩ := hw v2 hshapes.2.1
          obtain ⟨w3, rfl⟩ := hw v3 hshapes.2.2
          exact ⟨w1, w2, w3, rfl, rfl, rfl⟩

theorem eval_sk_make_body_evm {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hsk_fit : ∀ (h : globN s "sk_buf" ≠ 0), globN s "sk_buf" + 52 ≤ 2 ^ 64)
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make)).1) :
    ∃ skw : BitVec 64,
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make)).1 =
        some (.returned (.val (.word skw))) ∧
      skw.toNat = globN s "sk_buf" ∧
      globN s "sk_buf" ≠ 0 ∧
      EvmStepLemmas.ByteRegionEffect s
        (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make)).2
        [(globN s "sk_buf", 52)] := by
  have hb : sourceFnBody Guest.Software.guestFn_sk_make =
      .seq
        (.call (some (none, none)) (ofString "memcpy")
          [.var .global (ofString "sk_buf"), .var .local (ofString "addr"), .const 20])
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.op .add [.var .global (ofString "sk_buf"), .const 20],
             .var .local (ofString "key"), .const 32])
          (.return (.var .global (ofString "sk_buf")))) := rfl
  rw [hb] at hnt hres ⊢
  by_cases hsk0 : globN s "sk_buf" = 0
  · exfalso
    rw [evaluateHOLFiniteState_seq_line780] at hnt hres
    rcases hc1 : evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "memcpy")
          [.var .global (ofString "sk_buf"), .var .local (ofString "addr"), .const 20]) with ⟨r1, s1⟩
    have hc1_ne_err : r1 ≠ some .error := by
      rintro rfl; simp only [hc1] at hres; exact EvmFrameSpecs.not_resumes_error hres
    obtain ⟨skw, adw, _, hsk_ev, had_ev, _⟩ :=
      three_one_word_call_args_local s (ofString "memcpy")
        (.var .global (ofString "sk_buf")) (.var .local (ofString "addr")) (.const 20)
        _ _ (ofString "dst") (ofString "src") (ofString "n")
        (by rw [hcode]; exact M11.lookup_memcpy)
        (by rw [hc1]; exact hc1_ne_err)
    simp only [evalHOLExact] at hsk_ev had_ev
    have hskw0 : skw = 0 := by
      unfold globN at hsk0; rw [hsk_ev] at hsk0; exact BitVec.eq_of_toNat_eq hsk0
    subst hskw0
    simp only [hc1] at hnt hres
    rw [evaluateHOLFiniteState_call] at hc1
    have hargs : evalListHOLFinite s
        (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.var .global (ofString "sk_buf"), .var .local (ofString "addr"), .const 20] =
        some [.val (.word 0), .val (.word adw), .val (.word 20)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hsk_ev, had_ev]
    have hlook := pan_three_word_lookup s.code.lookup (ofString "memcpy")
      (ofString "dst") (ofString "src") (ofString "n")
      (sourceFnBody Guest.Software.guestFn_memcpy) 0 adw 20
      (by decide) (by decide) (by decide)
      (by rw [hcode]; exact M11.lookup_memcpy)
    rw [hargs] at hc1; dsimp only at hc1
    rw [hlook] at hc1; dsimp only at hc1
    by_cases hclk0 : s.clock = 0
    · rw [if_pos hclk0] at hc1; rcases hc1 with ⟨rfl, _⟩; exact hnt rfl
    · rw [if_neg hclk0] at hc1
      let cmap : HolFiniteMapExact MlS (ValueHOL 64) :=
        ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word 0))).update
          (ofString "src", ValueHOL.val (.word adw))).update (ofString "n", ValueHOL.val (.word 20))
      let entry := callEntryStateHOLFinite s cmap
      have hent_dst : entry.locals.lookup (ofString "dst") = some (.val (.word 0)) := by
        have h1 : ofString "n" ≠ ofString "dst" := by decide
        have h2 : ofString "src" ≠ ofString "dst" := by decide
        simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h1, h2, Ne.symm h1, Ne.symm h2]
      have hent_src : entry.locals.lookup (ofString "src") = some (.val (.word adw)) := by
        have h1 : ofString "n" ≠ ofString "src" := by decide
        simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h1, Ne.symm h1]
      have hent_n : entry.locals.lookup (ofString "n") = some (.val (.word 20)) := by
        simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      rcases hb_m : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_memcpy) with ⟨br, bs⟩
      have hb_m' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
          (sourceFnBody Guest.Software.guestFn_memcpy) = (br, bs) := hb_m
      rw [hb_m'] at hc1
      have hnt_b : br ≠ some .timeOut := by
        rintro rfl; dsimp only at hc1; rcases hc1 with ⟨rfl, _⟩; exact hnt rfl
      have herr := sk_make_zero_err entry adw hma hent_dst hent_src hent_n (by rw [hb_m]; exact hnt_b)
      rw [hb_m] at herr; dsimp only at herr; subst herr
      dsimp only at hc1; rcases hc1 with ⟨rfl, _⟩
      exact EvmFrameSpecs.not_resumes_error hres
  · have hbnd_sk := hsk_fit hsk0
    obtain ⟨skw, hsk_lk, hsk_nat⟩ := global_word_of_pos s "sk_buf" (by omega)
    have hsk20_nat : (skw + 20).toNat = globN s "sk_buf" + 20 := by
      rw [BitVec.toNat_add, hsk_nat]
      change (globN s "sk_buf" + 20) % 2 ^ 64 = _
      exact Nat.mod_eq_of_lt (by omega)
    rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
    rcases hc1 : evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "memcpy")
          [.var .global (ofString "sk_buf"), .var .local (ofString "addr"), .const 20]) with ⟨r1, s1⟩
    have hc1_ne_err : r1 ≠ some .error := by
      rintro rfl; simp only [hc1] at hres; exact EvmFrameSpecs.not_resumes_error hres
    obtain ⟨_, adw, _, _, had_lk, _⟩ :=
      three_one_word_call_args_local s (ofString "memcpy")
        (.var .global (ofString "sk_buf")) (.var .local (ofString "addr")) (.const 20)
        _ _ (ofString "dst") (ofString "src") (ofString "n")
        (by rw [hcode]; exact M11.lookup_memcpy)
        (by rw [hc1]; exact hc1_ne_err)
    simp only [evalHOLExact] at had_lk
    simp only [hc1] at hnt hres ⊢
    have hnt1 : r1 ≠ some .timeOut := by rintro rfl; exact hnt rfl
    have hm1 := M11.eval_call_memcpy_bre s
      (.var .global (ofString "sk_buf")) (.var .local (ofString "addr")) (.const 20)
      skw adw 20 [(globN s "sk_buf", 52)] hcode hma
      (by simp [evalHOLExact, hsk_lk])
      (by simp [evalHOLExact, had_lk])
      rfl
      (fun _ => ⟨(globN s "sk_buf", 52), List.mem_singleton.2 rfl,
        by dsimp only; rw [hsk_nat],
        by dsimp only; rw [hsk_nat]; change globN s "sk_buf" + 20 ≤ _; omega⟩)
      (by rw [hc1]; exact hnt1)
    dsimp only at hm1; rw [hc1] at hm1
    cases r1 with
    | some r =>
      dsimp only at hres
      exact False.elim (hm1.2 (by simp) hres)
    | none =>
      dsimp only at hnt hres ⊢
      obtain ⟨heff1, _⟩ := hm1.1 rfl
      have hs1_code : s1.code = originalRuntimeCode := heff1.code.trans hcode
      have hs1_ma : s1.memaddrs = ordinaryDomain := heff1.memaddrs.trans hma
      have hs1_sk : s1.globals.lookup (ofString "sk_buf") = some (.val (.word skw)) := by
        rw [heff1.globals]; exact hsk_lk
      rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
      rcases hc2 : evaluateHOLFiniteState s1
          (.call (some (none, none)) (ofString "memcpy")
            [.op .add [.var .global (ofString "sk_buf"), .const 20],
             .var .local (ofString "key"), .const 32]) with ⟨r2, s2⟩
      have hc2_ne_err : r2 ≠ some .error := by
        rintro rfl; simp only [hc2] at hres; exact EvmFrameSpecs.not_resumes_error hres
      obtain ⟨_, kyw, _, _, hky_lk, _⟩ :=
        three_one_word_call_args_local s1 (ofString "memcpy")
          (.op .add [.var .global (ofString "sk_buf"), .const 20]) (.var .local (ofString "key")) (.const 32)
          _ _ (ofString "dst") (ofString "src") (ofString "n")
          (by rw [hs1_code]; exact M11.lookup_memcpy)
          (by rw [hc2]; exact hc2_ne_err)
      simp only [evalHOLExact] at hky_lk
      simp only [hc2] at hnt hres ⊢
      have hnt2 : r2 ≠ some .timeOut := by rintro rfl; exact hnt rfl
      have hm2 := M11.eval_call_memcpy_bre s1
        (.op .add [.var .global (ofString "sk_buf"), .const 20]) (.var .local (ofString "key")) (.const 32)
        (skw + 20) kyw 32 [(globN s "sk_buf", 52)] hs1_code hs1_ma
        (by simp [evalHOLExact, evalListHOLExact, hs1_sk, wordOpHOL, wordOp, valueIsWord, valueWord])
        (by simp [evalHOLExact, hky_lk])
        rfl
        (fun _ => ⟨(globN s "sk_buf", 52), List.mem_singleton.2 rfl,
          by dsimp only; rw [hsk20_nat]; omega,
          by dsimp only; rw [hsk20_nat]; change globN s "sk_buf" + 20 + 32 ≤ _; omega⟩)
        (by rw [hc2]; exact hnt2)
      dsimp only at hm2; rw [hc2] at hm2
      cases r2 with
      | some r =>
        dsimp only at hres
        exact False.elim (hm2.2 (by simp) hres)
      | none =>
        dsimp only at hnt hres ⊢
        obtain ⟨heff2, _⟩ := hm2.1 rfl
        have hs2_sk : s2.globals.lookup (ofString "sk_buf") = some (.val (.word skw)) := by
          rw [heff2.globals]; exact hs1_sk
        rw [evaluateHOLFiniteState_return]
        have hev_ret : @evalHOLExact 64 F _ s2.toExact
            (fun a => Classical.propDecidable (s2.memaddrs a)) (.var .global (ofString "sk_buf")) =
            some (.val (.word skw)) := by simp [evalHOLExact, hs2_sk]
        rw [hev_ret]; dsimp only
        have hsz : sizeOfShapeWithContextHOL s2.structs (shapeOfHOLExact (.val (.word skw) : ValueHOL 64)) ≤ 32 := by
          simp [shapeOfHOLExact]
        rw [if_pos hsz]; dsimp only
        exact ⟨skw, rfl, hsk_nat, hsk0,
          m11Bre_to_evmBre (fun i hi => by rcases List.mem_singleton.1 hi with rfl; dsimp only; omega)
            ((heff1.trans heff2).with_locals_clock _ _)⟩

theorem lookup_warm_storage_key :
    originalRuntimeCode.lookup (ofString "warm_storage_key") =
      some ([(ofString "addr", .one), (ofString "key", .one)],
        sourceFnBody Guest.Software.guestFn_warm_storage_key, .one) :=
  lookup_of_guestAst_getElem 526 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_warm_storage_key) rfl

private theorem head_frame_key_role_props {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hInv : EvmInvAt s S) :
    let t0 := memW s (globN s "ev" + 176)
    t0 ∈ S ∧
    (∀ (i : Nat) (hi : i + 1 < (evmChain s).length), ¬ DelExclusive s S (evmChain s) i t0) ∧
    (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t0) ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
    globN s "bal_accounts" ≠ t0 ∧
    (∀ ad ∈ balRecords s, memW s ad ≠ t0) ∧
    (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) := by
  dsimp only
  set t0 := memW s (globN s "ev" + 176)
  obtain ⟨⟨hT, _, _, _⟩, hch_ne, _, _, hFW_all, _, _, _, _, _, _, hRoles, _⟩ := hInv
  have hch_cons : ∃ tail, evmChain s = (globN s "ev", globN s "cur_cont") :: tail := by
    unfold evmChain
    have hpos : ∃ m, Wave8GuestInv.maxChain + 1 = m + 1 := ⟨Wave8GuestInv.maxChain, rfl⟩
    obtain ⟨m, hm⟩ := hpos; rw [hm, evmChainFrom]; exact ⟨_, rfl⟩
  obtain ⟨chTail, hch⟩ := hch_cons
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by rw [hch]; exact List.mem_cons_self
  have ht0_S : t0 ∈ S := (hFW_all _ hhead).2.2.2.2.2.2.2.2.2.1
  have ht0_pos : 0 < t0 := by
    have := ((hT.2.1 t0 ht0_S).1.1 (t0, 88) (by simp [htabFootprint])).1.1
    have hsb : 0 < sourceBase := by decide
    dsimp at this; omega
  have hnot_world_role : ∀ rname : String, rname ≠ "frame.key" → (t0, rname) ∉ worldRoleSlots s := by
    intro rname hr_ne hmem
    have hpw : (worldRoleSlots s ++ frameRoleSlots s (evmChain s)).Pairwise
        (fun a b => a.1 = b.1 → a.2 = b.2 ∧ a.2 ∈ sharedRoles) := hRoles.2.1
    have hcross := (List.pairwise_append.1 hpw).2.2 (t0, rname) hmem (t0, "frame.key")
      (by
        unfold frameRoleSlots
        exact List.mem_flatMap.2 ⟨(globN s "ev", globN s "cur_cont"), hhead, by simp [t0]⟩)
      rfl
    exact hr_ne hcross.1
  refine ⟨ht0_S, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi hdel
    have h0_lt : 0 < (evmChain s).length := by omega
    have hch0 : (evmChain s)[0].1 = globN s "ev" := by simp [hch]
    have h176 := hdel.2 0 h0_lt 176 (by decide) (by rw [hch0])
    omega
  · intro hws heq
    apply hnot_world_role "ws+32" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    unfold recRoles; simp [hws, heq]
  · intro hbs heq
    apply hnot_world_role "bs+32" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
    unfold recRoles; simp [hbs, heq]
  · intro heq
    apply hnot_world_role "bal_accounts" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_right; simp [heq]
  · intro ad had heq
    apply hnot_world_role "bal.stor" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_right
    exact List.mem_flatMap.2 ⟨ad, had, by simp [heq]⟩
  · intro hts heq
    apply hnot_world_role "ts+32" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_right
    unfold recRoles; simp [hts, heq]

/-- `warm_storage_key` (AST line 16571): EVM step keeping `EvmInv`, globals outside `["heap_ptr"]`, and `evmChain`. -/
theorem «ek_warm_storage_key» :
    EvmKeeps (EvmAvoids (fun s => [(globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)]))
    ["heap_ptr"] (ofString "warm_storage_key") := by
  refine ⟨_, _, _, lookup_warm_storage_key, ?_⟩
  intro F s hcode hAv _hlookup hnt hres
  have hsk_fit : ∀ (hz : globN s "sk_buf" ≠ 0), globN s "sk_buf" + 52 ≤ 2 ^ 64 := by
    intro hz
    obtain ⟨hAs, S, hInvAt, _⟩ := hAv
    have hmem_fix : (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 64) ∈ fixedObjects s := by
      unfold fixedObjects
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_map.2 ⟨("sk_buf", 64), by decide, rfl⟩
    rw [if_neg hz] at hmem_fix
    rcases fixedObject_le_2pow64 hAs.2 hInvAt.1.2.2.1 hmem_fix with h0 | hbnd
    · dsimp only at h0; omega
    · dsimp only at hbnd; omega
  revert hnt hres
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_warm_storage_key,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "addr"), .var .local (ofString "key")] with _ | vals
  · intro _ hres; exact absurd hres EvmFrameSpecs.not_resumes_error
  · dsimp only
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "sk_make") vals with _ | ⟨body_sk, callee_sk, rs_sk⟩
    · intro _ hres; exact absurd hres EvmFrameSpecs.not_resumes_error
    · dsimp only
      by_cases hclk_sk : s.clock = 0
      · simp [hclk_sk]
      · rw [if_neg hclk_sk]
        have hsame_sk := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "sk_make")
          _ _ _ _ _ vals callee_sk (by rw [hcode]; exact lookup_sk_make) hl
        subst hsame_sk
        let ent_sk := callEntryStateHOLFinite s callee_sk
        rcases hrun_sk : evaluateHOLFiniteState (callEntryStateHOLFinite s callee_sk)
            (sourceFnBody Guest.Software.guestFn_sk_make) with ⟨res_sk, st_sk⟩
        have hrun_sk_ent : evaluateHOLFiniteState ent_sk (sourceFnBody Guest.Software.guestFn_sk_make) =
            (res_sk, st_sk) := hrun_sk
        have hma : s.memaddrs = ordinaryDomain := hAv.1.1.memaddrs
        cases res_sk with
        | none => intro _ hres; exact absurd hres EvmFrameSpecs.not_resumes_error
        | some r_sk =>
          cases r_sk with
          | timeOut => intro hnt _; exact absurd rfl hnt
          | «break» | «continue» | error =>
            intro _ hres; exact absurd hres EvmFrameSpecs.not_resumes_error
          | finalFfi _ =>
            intro _ hres; rcases hres with ⟨_, hc⟩ | ⟨_, _, hc, _⟩ <;> simp at hc
          | exception e_sk v_sk =>
            intro _ hres
            obtain ⟨_, hret_eq, _, _, _⟩ := eval_sk_make_body_evm ent_sk hcode hma hsk_fit
              (by rw [hrun_sk_ent]; simp)
              (by rw [hrun_sk_ent]; rcases hres with ⟨_, hc⟩ | ⟨e', v', hc, hnt_e⟩
                  · simp at hc
                  · injection hc with hc; injection hc with he _; subst he; exact Or.inr ⟨_, _, rfl, hnt_e⟩)
            rw [hrun_sk_ent] at hret_eq; simp at hret_eq
          | returned rv_sk =>
            dsimp only
            obtain ⟨skw, hret_eq, hsk_nat, hsk_nz_ent, heff_sk0⟩ :=
              eval_sk_make_body_evm ent_sk hcode hma hsk_fit
                (by rw [hrun_sk_ent]; simp)
                (by rw [hrun_sk_ent]; exact Or.inl ⟨rv_sk, rfl⟩)
            have hsk_nz : globN s "sk_buf" ≠ 0 := hsk_nz_ent
            rw [hrun_sk_ent] at hret_eq heff_sk0
            dsimp only at hret_eq heff_sk0
            injection hret_eq with hret_eq; injection hret_eq with hret_eq
            subst hret_eq
            split
            · intro hnt hres
              set s1 := setVarHOLFinite (ofString "k") (.val (.word skw)) { st_sk with locals := s.locals }
              have heff_s1 : EvmStepLemmas.ByteRegionEffect s s1
                  [(globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)] := by
                rw [if_neg hsk_nz]
                exact (((EvmStepLemmas.ByteRegionEffect.refl s _).with_locals_clock _ _).trans heff_sk0).with_locals_clock _ _
              have hStep1 : EvmStep [] s s1 :=
                EvmStepLemmas.ByteRegionEffect.to_evmStep_avoids hAv heff_s1
              obtain ⟨hInv_s1, hhp_s1, hg_s1, hch_s1⟩ := hStep1
              obtain ⟨hAs1, S1, hInvAt1⟩ := hInv_s1
              have hs1_code : s1.code = originalRuntimeCode := heff_s1.code.trans hcode
              set contProg : ProgHOL 64 :=
                .seq
                  (.call (some (none, none)) (ofString "htab_set")
                    [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 176)]),
                     .var .local (ofString "k"), .const (BitVec.ofNat 64 1)])
                  (.return (.const (BitVec.ofNat 64 0)))
              have hncr : noCatchableRaise htabMutCallees contProg = true := rfl
              rcases hrun_c : evaluateHOLFiniteState s1 contProg with ⟨res_c, post_c⟩
              have hnt_c : res_c ≠ some .timeOut := by
                change (evaluateHOLFiniteState s1 contProg).1 ≠ some .timeOut at hnt
                rw [hrun_c] at hnt; exact hnt
              have hres_c : Resumes res_c := by
                change Resumes (evaluateHOLFiniteState s1 contProg).1 at hres
                rw [hrun_c] at hres; exact hres
              have hno_catch := evaluate_noCatchableRaise htabMutCallees htabMutCallees_good
                contProg hncr s1 hs1_code
              have hret_c : ∃ v_c, res_c = some (.returned v_c) := by
                rcases hres_c with ⟨v_c, hc⟩ | ⟨eid, ev, hc, hnot_trap⟩
                · exact ⟨v_c, hc⟩
                · exfalso
                  have hnc := hno_catch eid ev hnot_trap
                  rw [hrun_c] at hnc; exact hnc hc
              obtain ⟨v_c, rfl⟩ := hret_c
              have hp_eq : (evaluateHOLFiniteState s1 contProg).2 = post_c := by rw [hrun_c]
              dsimp only [contProg] at hrun_c
              rw [evaluateHOLFiniteState_seq_line780] at hrun_c
              rcases hc_set : evaluateHOLFiniteState s1
                  (.call (some (none, none)) (ofString "htab_set")
                    [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 176)]),
                     .var .local (ofString "k"), .const (BitVec.ofNat 64 1)]) with ⟨r_set, s2⟩
              rw [hc_set] at hrun_c
              cases r_set with
              | some rs =>
                dsimp only at hrun_c
                exfalso
                have hrs_ret : rs = .returned v_c := Option.some.inj (Prod.mk.inj hrun_c).1
                rw [evaluateHOLFiniteState_call] at hc_set
                split at hc_set
                · have h1 := Option.some.inj (Prod.mk.inj hc_set).1
                  rw [hrs_ret] at h1; cases h1
                · split at hc_set
                  · have h1 := Option.some.inj (Prod.mk.inj hc_set).1
                    rw [hrs_ret] at h1; cases h1
                  · split at hc_set
                    · have h1 := Option.some.inj (Prod.mk.inj hc_set).1
                      rw [hrs_ret] at h1; cases h1
                    · split at hc_set
                      · have h1 := Option.some.inj (Prod.mk.inj hc_set).1
                        rw [hrs_ret] at h1; cases h1
                      · have h1 := Option.some.inj (Prod.mk.inj hc_set).1
                        rw [hrs_ret] at h1; cases h1
                      · have h1 := Option.some.inj (Prod.mk.inj hc_set).1
                        rw [hrs_ret] at h1; cases h1
                      · split at hc_set
                        · simp at hc_set
                        · have h1 := Option.some.inj (Prod.mk.inj hc_set).1
                          rw [hrs_ret] at h1; cases h1
                      · have h1 := Option.some.inj (Prod.mk.inj hc_set).1
                        rw [hrs_ret] at h1; cases h1
                      · rename_i other _ _ heq_other _ _
                        have h1 := Option.some.inj (Prod.mk.inj hc_set).1
                        rw [hrs_ret] at h1
                        subst h1
                        exact heq_other v_c rfl
              | none =>
                dsimp only at hrun_c
                rw [evaluateHOLFiniteState_return] at hrun_c
                have hev0_s2 : @evalHOLExact 64 F _ s2.toExact
                    (fun a => Classical.propDecidable (s2.memaddrs a)) (.const (BitVec.ofNat 64 0)) =
                    some (.val (.word 0)) := rfl
                have hsz0_s2 : sizeOfShapeWithContextHOL s2.structs
                    (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) ≤ 32 := by
                  simp [shapeOfHOLExact]
                rw [hev0_s2] at hrun_c; dsimp only at hrun_c; rw [if_pos hsz0_s2] at hrun_c
                injection hrun_c with _ hpost_c
                obtain ⟨tw, kw, vw, htw_ev, hkw_ev, hvw_ev⟩ :=
                  three_one_word_call_args_local s1 (ofString "htab_set")
                    (.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 176)]))
                    (.var .local (ofString "k")) (.const (BitVec.ofNat 64 1))
                    _ _ (ofString "t") (ofString "key") (ofString "value")
                    (by rw [hs1_code]; exact lookup_htab_set)
                    (by rw [hc_set]; simp)
                obtain ⟨_, hev1_pos, hb_ev1, _, _, _⟩ := evmInv_head_info ⟨hAs1, S1, hInvAt1⟩
                obtain ⟨evw1, hevw1_lk, hevw1_nat⟩ := global_word_of_pos s1 "ev" hev1_pos
                have htw_nat : tw.toNat = memW s1 (globN s1 "ev" + 176) := by
                  have had_eq : @evalHOLExact 64 F _ s1.toExact
                      (fun a => Classical.propDecidable (s1.memaddrs a))
                      (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 176)]) =
                      some (.val (.word (BitVec.ofNat 64 (globN s1 "ev" + 176)))) := by
                    simp only [evalHOLExact, evalListHOLExact, hevw1_lk, wordOpHOL, wordOp, valueIsWord, valueWord,
                      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr, BitVec.add_zero]
                    congr 3
                    apply BitVec.eq_of_toNat_eq
                    have hz0 : (0 : BitVec 64).toNat = 0 := rfl
                    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hevw1_nat, hz0, Nat.add_zero,
                      Nat.mod_eq_of_lt (show 176 < 2 ^ 64 by omega),
                      Nat.mod_eq_of_lt (show globN s1 "ev" + 176 < 2 ^ 64 by omega)]
                  unfold evalHOLExact at htw_ev
                  rw [had_eq] at htw_ev; dsimp only at htw_ev
                  unfold memLoadHOLExact at htw_ev
                  split at htw_ev
                  · split at htw_ev
                    · injection htw_ev with htw_m
                      unfold memW
                      cases hm_cell : s1.memory (BitVec.ofNat 64 (globN s1 "ev" + 176)) with
                      | word cw =>
                        change ValueHOL.val (s1.memory (BitVec.ofNat 64 (globN s1 "ev" + 176))) = .val (.word tw) at htw_m
                        rw [hm_cell] at htw_m
                        injection htw_m with htw_m; injection htw_m with htw_m; subst htw_m; rfl
                    · cases htw_ev
                  · cases htw_ev
                rw [evaluateHOLFiniteState_call] at hc_set
                have hargs_set : evalListHOLFinite s1
                    (h := fun a => Classical.propDecidable (s1.memaddrs a))
                    [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 176)]),
                     .var .local (ofString "k"), .const (BitVec.ofNat 64 1)] =
                    some [.val (.word tw), .val (.word kw), .val (.word vw)] := by
                  simp [evalListHOLFinite, evalListHOLExact, htw_ev, hkw_ev, hvw_ev]
                have hlook_set := pan_three_word_lookup s1.code.lookup (ofString "htab_set")
                  (ofString "t") (ofString "key") (ofString "value")
                  (sourceFnBody Guest.Software.guestFn_htab_set) tw kw vw
                  (by decide) (by decide) (by decide)
                  (by rw [hs1_code]; exact lookup_htab_set)
                rw [hargs_set] at hc_set; dsimp only at hc_set
                rw [hlook_set] at hc_set; dsimp only at hc_set
                by_cases hclk_s1 : s1.clock = 0
                · rw [if_pos hclk_s1] at hc_set; simp at hc_set
                · rw [if_neg hclk_s1] at hc_set
                  let cmap_s : HolFiniteMapExact MlS (ValueHOL 64) :=
                    ((HolFiniteMapExact.empty.update (ofString "t", ValueHOL.val (.word tw))).update
                      (ofString "key", ValueHOL.val (.word kw))).update (ofString "value", ValueHOL.val (.word vw))
                  let entry_s := callEntryStateHOLFinite s1 cmap_s
                  rcases hb_set : evaluateHOLFiniteState entry_s (sourceFnBody Guest.Software.guestFn_htab_set) with
                    ⟨r_bs, cpost_s⟩
                  have hb_set' : evaluateHOLFiniteState (callEntryStateHOLFinite s1 cmap_s)
                      (sourceFnBody Guest.Software.guestFn_htab_set) = (r_bs, cpost_s) := hb_set
                  rw [hb_set'] at hc_set
                  have hr_bs_ret : ∃ rv_bs, r_bs = some (.returned rv_bs) ∧ s2 = { cpost_s with locals := s1.locals } := by
                    cases r_bs with
                    | none => simp at hc_set
                    | some rbi =>
                      cases rbi with
                      | returned rv_bs =>
                        dsimp only at hc_set
                        split at hc_set
                        · exact ⟨rv_bs, rfl, (Prod.mk.inj hc_set).2.symm⟩
                        · simp at hc_set
                      | _ => simp at hc_set
                  obtain ⟨rv_bs, rfl, hs2_eq⟩ := hr_bs_ret
                  obtain ⟨ht0_S1, ht0_ndel, ht0_nws32, ht0_nbs32, ht0_nba, ht0_nad, ht0_nts32⟩ :=
                    head_frame_key_role_props hInvAt1
                  have hcal_t : entry_s.locals.lookup (ofString "t") = some (.val (.word tw)) := by
                    have h1 : ofString "value" ≠ ofString "t" := by decide
                    have h2 : ofString "key" ≠ ofString "t" := by decide
                    simp [entry_s, cmap_s, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h1, h2, Ne.symm h1, Ne.symm h2]
                  have hloc_ts : locN entry_s "t" = memW s1 (globN s1 "ev" + 176) := by
                    simp [locN, hcal_t, htw_nat]
                  have hArg_s : HtabArgWF entry_s := by
                    refine ⟨⟨guestInv_congr (s := s1) rfl rfl rfl rfl hAs1.1, hAs1.2⟩, ?_, ?_⟩
                    · rw [hloc_ts]
                      exact (htabWF_with_locals s1 entry_s.locals entry_s.clock _).mpr
                        (hInvAt1.1.1.2.1 _ ht0_S1).1
                    · rw [hloc_ts]
                      intro i hi
                      exact ((hInvAt1.1.1.2.1 _ ht0_S1).2 i hi).1
                  have hhl_entry : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "htab_set")
                      [.val (.word tw), .val (.word kw), .val (.word vw)] =
                      some (sourceFnBody Guest.Software.guestFn_htab_set, entry_s.locals, .one) := by
                    rw [← hs1_code]; exact hlook_set
                  obtain ⟨params_sp, body_sp, rs_sp, hlk_spec, hfn_spec⟩ := SoloHtabSet.htab_set_spec_proof
                  have hbody_eq : ([(ofString "t", ShapeHOL.one), (ofString "key", ShapeHOL.one), (ofString "value", ShapeHOL.one)],
                      sourceFnBody Guest.Software.guestFn_htab_set, ShapeHOL.one) = (params_sp, body_sp, rs_sp) :=
                    Option.some.inj (lookup_htab_set.symm.trans hlk_spec)
                  rcases Prod.mk.inj hbody_eq with ⟨_, hbr⟩
                  rcases Prod.mk.inj hbr with ⟨hb_eq, hrs_eq⟩
                  subst hb_eq hrs_eq
                  have hexit_s := hfn_spec entry_s hs1_code hArg_s ⟨_, hhl_entry⟩
                    (by rw [hb_set]; simp) rv_bs (by rw [hb_set])
                  have hbe_s : cpost_s.be = s1.be := by
                    have hbe0 := evaluate_be_eq entry_s (sourceFnBody Guest.Software.guestFn_htab_set)
                    rw [hb_set] at hbe0; exact hbe0
                  have hcpost_eq : (evaluateHOLFiniteState entry_s (sourceFnBody Guest.Software.guestFn_htab_set)).2 = cpost_s := by
                    rw [hb_set]
                  rw [hcpost_eq] at hexit_s
                  unfold HtabExit at hexit_s; dsimp only at hexit_s
                  rw [hloc_ts] at hexit_s
                  obtain ⟨hAp_s, hwf_s, hhdr0_s, _, hhp_s, hfp_s, hfr_s, hg_s⟩ := hexit_s
                  obtain ⟨hInv_cs, hch_cs, _, _⟩ := evmInvAt_of_htab_step
                    hAs1 hInvAt1 hAp_s hbe_s hwf_s hhdr0_s hhp_s hfp_s hfr_s
                    (fun k hk => hg_s k (fun h => hk (by simp at h; simp [h])))
                    (by
                      have hjn : globN cpost_s "journal_n" = globN entry_s "journal_n" :=
                        globN_eq_of_lookup_eq (hg_s (ofString "journal_n") (by decide)).symm
                      have hjn_ent : globN entry_s "journal_n" = globN s1 "journal_n" := rfl
                      omega)
                    ht0_S1 ht0_ndel ht0_nws32 ht0_nbs32 ht0_nba ht0_nad (Or.inl ht0_nts32)
                  have hcpost_inv : EvmInv cpost_s := ⟨hAp_s, S1, hInv_cs⟩
                  let finalLocals := HolFiniteMapExact.resVarEq post_c.locals
                    (ofString "k", s.locals.lookup (ofString "k"))
                  dsimp only
                  have hfinal_eq : ({ post_c with locals := finalLocals } : PanSemStateFiniteExact 64 F) =
                      { cpost_s with locals := finalLocals, clock := cpost_s.clock } := by
                    rw [← hpost_c, hs2_eq]; rfl
                  rw [hfinal_eq]
                  refine ⟨localsFree_evmInv cpost_s _ _ hcpost_inv, ?_, ?_, ?_⟩
                  · change globN s "heap_ptr" ≤ globN cpost_s "heap_ptr"
                    exact le_trans hhp_s1 hhp_s
                  · intro k hk
                    change s.globals.lookup k = cpost_s.globals.lookup k
                    exact (hg_s1 k (by simp)).trans (hg_s k hk)
                  · exact ((evmChain_with_locals cpost_s _ _).trans hch_cs).trans hch_s1
            · intro _ hres; exact absurd hres EvmFrameSpecs.not_resumes_error

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
