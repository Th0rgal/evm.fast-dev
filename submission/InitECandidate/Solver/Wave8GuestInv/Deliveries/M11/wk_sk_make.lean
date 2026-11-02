import InitECandidate.Solver.Wave8GuestInv.Deliveries.M11.RlpMemcpyLemmas

/-! `wk_sk_make`: relational world step for `sk_make` (`Guest/SoftwareAst.lean:12923`, `guestAst[360]`).

Checked against frozen spec revision 9 (`8a79d9f28`, tag `wave8-spec-frozen-r9`).

`sk_make(addr, key)` executes:
1. `memcpy(sk_buf, addr, 20)`
2. `memcpy(sk_buf + 20, key, 32)`
3. `return sk_buf`

If `globN s "sk_buf" = 0`:
- Either `sk_buf` is not a word (so `memcpy` call errors), or `sk_buf = 0#64`, in which case the
  first `memcpy(0, addr, 20)` attempts to store at address `0 ∉ ordinaryDomain` and errors, so
  `sk_make` cannot resume.
If `globN s "sk_buf" ≠ 0`:
- `("sk_buf", 64) ∈ globalBuffers` is an untyped global scratch buffer in `fixedObjects s`, so
  `Allocated s (globN s "sk_buf", 64)` gives `globN s "sk_buf" + 64 ≤ heapEnd < 2^64` (no wraparound
  for `sk_buf + 20`), `[sk_buf, sk_buf + 20)` and `[sk_buf + 20, sk_buf + 52)` both lie inside
  `(globN s "sk_buf", 64)`, and `untypedGlobalBuf_disj_worldTypedIvls` + `ByteRegionEffect.to_worldStep`
  discharges `WorldStep (fun _ => []) [] stdKeep NoExtra` directly.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false

namespace InitECandidate.Solver.Wave8GuestInv.M11

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

theorem lookup_sk_make :
    originalRuntimeCode.lookup (ofString "sk_make") =
      some ([(ofString "addr", .one), (ofString "key", .one)],
        sourceFnBody Guest.Software.guestFn_sk_make, .one) :=
  lookup_of_guestAst_getElem 360 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_sk_make) rfl

/-- When `dst = 0` and `n = 20`, `memcpy(0, src, 20)` on an `ordinaryDomain` state always errors
(if non-timeout): in the aligned branch, `32 ≤ 20` is false so `lp1` skips and `lp2` (`8 ≤ 20`)
executes `store (0 + 0) ...` which fails `ordinaryDomain 0`; in the unaligned branch, `ite` skips
and `lp3` (`8 ≤ 20`) executes `storeByte (0 + 0) ...` which fails `ordinaryDomain (panByteAlignHOL 0)`. -/
private theorem memcpy_zero_20_err {F : Type}
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
    · -- Unaligned branch: `ite` skips, then `lp3` (`notLower 20 (0 + 8)`) runs 1st `storeByte (0 + 0)` and errors!
      rw [if_pos hcw0, evaluateHOLFiniteState_skip] at hnt' ⊢
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
        -- First `storeByte (dst + i) ...` on `decClockHOLFinite s1`:
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
    · -- Aligned branch: `lp1` (`notLower 20 (0 + 32)`) is false so exits `(none, s1)`, then `lp2` (`notLower 20 (0 + 8)`) runs `store (0 + 0)` and errors!
      rw [if_neg hcw0] at hnt' ⊢
      rw [evaluateHOLFiniteState_seq_line780] at hnt' ⊢
      -- `lp1` exits immediately with `(none, s1)`:
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
      -- Now `lp2` on `s1`:
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
          · obtain ⟨w, rfl⟩ := eval_load_one_word (decClockHOLFinite s1) _ v hv
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

private theorem three_one_word_call_args {F : Type}
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
            · rename_i hsome
              rw [hn] at hsome; simp at hsome
          simp only [lookupCodeHOLExact, hcode, List.length_cons, List.length_nil, ↓reduceIte,
            List.zip, List.zipWith, List.all, Bool.and_true, Bool.and_eq_true] at hraw
          have hshapes : shapeEqHOL .one (shapeOfHOLExact v1) = true ∧
              shapeEqHOL .one (shapeOfHOLExact v2) = true ∧
              shapeEqHOL .one (shapeOfHOLExact v3) = true := by
            by_contra hns
            simp [hns] at hraw
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

/-- `sk_make` (AST line 12923): relational world step. -/
theorem «wk_sk_make» :
    WorldKeeps WorldOK (fun _ => [])
    []
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "sk_make") := by
  refine ⟨_, _, _, lookup_sk_make, ?_⟩
  intro F s hcode hW hnt hres
  let extra : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl :=
    fun t => [(globN t "sk_buf", if globN t "sk_buf" = 0 then 0 else 64)]
  have hextra_fix : ∀ x ∈ extra s, x ∈ fixedObjects s ∧
      ∀ S Nd, WorldTypedWith s S Nd → ∀ i ∈ worldTypedIvls s S Nd, i.2 = 0 ∨ Disj x i := by
    intro x hx
    simp only [extra, List.mem_singleton] at hx
    subst hx
    refine ⟨?_, fun S Nd hWT => untypedGlobalBuf_disj_worldTypedIvls hWT (by decide) (by decide)⟩
    unfold fixedObjects
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    exact List.mem_map.2 ⟨("sk_buf", 64), by decide, rfl⟩
  suffices heff : ByteRegionEffect s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make)).2
      (([] : List Ivl) ++ extra s) by
    exact ByteRegionEffect.to_worldStep (R := fun _ => []) (extra := extra) hW hextra_fix heff
  simp only [List.nil_append]
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
  -- First, if `globN s "sk_buf" = 0`, the first `memcpy` call cannot return `(none, _)`, nor can it `Resumes`!
  by_cases hsk0 : globN s "sk_buf" = 0
  · exfalso
    rw [evaluateHOLFiniteState_seq_line780] at hnt hres
    rcases hc1 : evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "memcpy")
          [.var .global (ofString "sk_buf"), .var .local (ofString "addr"), .const 20]) with ⟨r1, s1⟩
    have hc1_ne_err : r1 ≠ some .error := by
      rintro rfl; simp only [hc1] at hres; exact not_resumes_error hres
    obtain ⟨skw, adw, _, hsk_ev, had_ev, _⟩ :=
      three_one_word_call_args s (ofString "memcpy")
        (.var .global (ofString "sk_buf")) (.var .local (ofString "addr")) (.const 20)
        _ _ (ofString "dst") (ofString "src") (ofString "n")
        (by rw [hcode]; exact lookup_memcpy)
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
      (by rw [hcode]; exact lookup_memcpy)
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
      have herr := memcpy_zero_20_err entry adw hW.1.1.memaddrs hent_dst hent_src hent_n
        (by rw [hb_m]; exact hnt_b)
      rw [hb_m] at herr; dsimp only at herr; subst herr
      dsimp only at hc1; rcases hc1 with ⟨rfl, _⟩
      exact not_resumes_error hres
  · -- `globN s "sk_buf" ≠ 0`:
    obtain ⟨skw, hsk_lk, hsk_nat⟩ := global_word_of_pos s "sk_buf" (by omega)
    obtain ⟨S0, hWT0⟩ := hW.2
    have hfo_sk : (globN s "sk_buf", 64) ∈ fixedObjects s := by
      have hm := (hextra_fix _ (List.mem_singleton.2 rfl)).1
      rwa [if_neg hsk0] at hm
    have hal_sk : Allocated s (globN s "sk_buf", 64) := by
      rcases hWT0.2.2.1.1 _ hfo_sk with h0 | ⟨hal, _⟩
      · dsimp only at h0; omega
      · exact hal
    have hbnd_sk := allocated_le_2pow64 hW.1.2 hal_sk
    dsimp only at hbnd_sk
    have hsk20_nat : (skw + 20).toNat = globN s "sk_buf" + 20 := by
      rw [BitVec.toNat_add, hsk_nat]
      change (globN s "sk_buf" + 20) % 2 ^ 64 = _
      exact Nat.mod_eq_of_lt (by omega)
    -- Step 1: `memcpy(sk_buf, addr, 20)`
    rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
    rcases hc1 : evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "memcpy")
          [.var .global (ofString "sk_buf"), .var .local (ofString "addr"), .const 20]) with ⟨r1, s1⟩
    have hc1_ne_err : r1 ≠ some .error := by
      rintro rfl; simp only [hc1] at hres; exact not_resumes_error hres
    obtain ⟨_, adw, _, _, had_lk, _⟩ :=
      three_one_word_call_args s (ofString "memcpy")
        (.var .global (ofString "sk_buf")) (.var .local (ofString "addr")) (.const 20)
        _ _ (ofString "dst") (ofString "src") (ofString "n")
        (by rw [hcode]; exact lookup_memcpy)
        (by rw [hc1]; exact hc1_ne_err)
    simp only [evalHOLExact] at had_lk
    simp only [hc1] at hnt hres ⊢
    have hnt1 : r1 ≠ some .timeOut := by rintro rfl; exact hnt rfl
    have hm1 := eval_call_memcpy_bre s
      (.var .global (ofString "sk_buf")) (.var .local (ofString "addr")) (.const 20)
      skw adw 20 (extra s) hcode hW.1.1.memaddrs
      (by simp [evalHOLExact, hsk_lk])
      (by simp [evalHOLExact, had_lk])
      rfl
      (fun _ => ⟨(globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 64),
        List.mem_singleton.2 rfl,
        by dsimp only; rw [hsk_nat],
        by dsimp only; rw [if_neg hsk0, hsk_nat]; change globN s "sk_buf" + 20 ≤ _; omega⟩)
      (by rw [hc1]; exact hnt1)
    dsimp only at hm1; rw [hc1] at hm1
    cases r1 with
    | some r =>
      dsimp only at hres
      exact False.elim (hm1.2 (by simp) hres)
    | none =>
      dsimp only at hnt hres ⊢
      obtain ⟨heff1, hs1_loc⟩ := hm1.1 rfl
      have hs1_code : s1.code = originalRuntimeCode := heff1.code.trans hcode
      have hs1_ma : s1.memaddrs = ordinaryDomain := heff1.memaddrs.trans hW.1.1.memaddrs
      have hs1_sk : s1.globals.lookup (ofString "sk_buf") = some (.val (.word skw)) := by
        rw [heff1.globals]; exact hsk_lk
      -- Step 2: `memcpy(sk_buf + 20, key, 32)`
      rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
      rcases hc2 : evaluateHOLFiniteState s1
          (.call (some (none, none)) (ofString "memcpy")
            [.op .add [.var .global (ofString "sk_buf"), .const 20],
             .var .local (ofString "key"), .const 32]) with ⟨r2, s2⟩
      have hc2_ne_err : r2 ≠ some .error := by
        rintro rfl; simp only [hc2] at hres; exact not_resumes_error hres
      obtain ⟨_, kyw, _, _, hky_lk, _⟩ :=
        three_one_word_call_args s1 (ofString "memcpy")
          (.op .add [.var .global (ofString "sk_buf"), .const 20]) (.var .local (ofString "key")) (.const 32)
          _ _ (ofString "dst") (ofString "src") (ofString "n")
          (by rw [hs1_code]; exact lookup_memcpy)
          (by rw [hc2]; exact hc2_ne_err)
      simp only [evalHOLExact] at hky_lk
      simp only [hc2] at hnt hres ⊢
      have hnt2 : r2 ≠ some .timeOut := by rintro rfl; exact hnt rfl
      have hm2 := eval_call_memcpy_bre s1
        (.op .add [.var .global (ofString "sk_buf"), .const 20]) (.var .local (ofString "key")) (.const 32)
        (skw + 20) kyw 32 (extra s) hs1_code hs1_ma
        (by simp [evalHOLExact, evalListHOLExact, hs1_sk, wordOpHOL, wordOp, valueIsWord, valueWord])
        (by simp [evalHOLExact, hky_lk])
        rfl
        (fun _ => ⟨(globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 64),
          List.mem_singleton.2 rfl,
          by dsimp only; rw [hsk20_nat]; omega,
          by dsimp only; rw [if_neg hsk0, hsk20_nat]; change globN s "sk_buf" + 20 + 32 ≤ _; omega⟩)
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
        exact (heff1.trans heff2).with_locals_clock _ _

end InitECandidate.Solver.Wave8GuestInv.M11
