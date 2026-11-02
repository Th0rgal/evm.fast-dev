import InitECandidate.Solver.Wave8GuestInv.Deliveries.M11.RlpMemcpyLemmas

/-! `wk_rlp_encode_bytes`: relational world step with output region `(locN s "dst", locN s "n" + 9)`
for `rlp_encode_bytes` (`Guest/SoftwareAst.lean:4768`, `guestAst[122]`).

Checked against frozen spec revision 9 (`8a79d9f28`, tag `wave8-spec-frozen-r9`).

Proof outline:
1. Branch 1 (`n == 1 && loadByte(src) < 128`): `storeByte dst b; return 1` writes 1 byte at `dst`,
   which lies inside `(locN s "dst", locN s "n" + 9)`.
2. Branch 2: `decCall "h" .one "rlp_write_header" [dst, 128, n] (seq (call "memcpy" [dst + h, src, n]) (return (h + n)))`.
   - `rlp_write_header(dst, 128, n)` executes `storeByte dst ...` first on every resuming path,
     which establishes `dst0.toNat < heapEnd = 33806089704`, writes at most `1 + ll` bytes (`ll ≤ 8`)
     in `[dst0, dst0 + h) ⊆ [dst0, dst0 + 9)`, and returns `h` with `1 ≤ h.toNat ≤ 9` (never raising
     any exception).
   - Since `dst0.toNat < heapEnd` and `h.toNat ≤ 9`, `(dst0 + h).toNat = dst0.toNat + h.toNat`
     without `2^64` wraparound.
   - `eval_call_memcpy_bre_gen` then discharges `memcpy(dst0 + h, src0, n0)` into
     `Rl = [(locN s "dst", locN s "n" + 9)]` without any `2^64` assumption on `dst0 + n0`,
     because `(dst0.toNat + h.toNat) + off < dst0.toNat + (n0.toNat + 9)` in `Nat` for all `off < n0.toNat`.
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

theorem lookup_rlp_encode_bytes :
    originalRuntimeCode.lookup (ofString "rlp_encode_bytes") =
      some ([(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_encode_bytes, .one) :=
  lookup_of_guestAst_getElem 122 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_encode_bytes) rfl

private theorem storeByte_local_dst_inv {F : Type}
    (t : PanSemStateFiniteExact 64 F) (val : ExpHOL 64)
    (hma : t.memaddrs = ordinaryDomain)
    (hnone : (evaluateHOLFiniteState t (.storeByte (.var .local (ofString "dst")) val)).1 = none) :
    ∃ dst0 : BitVec 64,
      t.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
      dst0.toNat < heapEnd := by
  rw [evaluateHOLFiniteState_storeByte] at hnone
  rcases hd : t.locals.lookup (ofString "dst") with _ | dv
  · simp [evalHOLExact, hd] at hnone
  · rcases dv with ⟨⟨dst0⟩⟩ | _ | _
    · simp only [evalHOLExact, hd] at hnone
      split at hnone
      · split at hnone
        · rename_i m' hst
          unfold panMemStoreByteWord8HOL at hst
          dsimp only at hst
          cases hm : t.memory (panByteAlignHOL dst0) with
          | word cell =>
            by_cases hdom : t.memaddrs (panByteAlignHOL dst0)
            · exact ⟨dst0, rfl, (byteAlign_lt_heapEnd hma dst0 hdom).2⟩
            · simp [hm, hdom] at hst
        · simp at hnone
      · simp at hnone
    · simp [evalHOLExact, hd] at hnone
    · simp [evalHOLExact, hd] at hnone

private theorem storeByte_only_none_or_error {F : Type}
    (t : PanSemStateFiniteExact 64 F) (dst val : ExpHOL 64) :
    (evaluateHOLFiniteState t (.storeByte dst val)).1 = none ∨
      (evaluateHOLFiniteState t (.storeByte dst val)).1 = some .error := by
  rw [evaluateHOLFiniteState_storeByte]
  split
  · split
    · split
      · exact Or.inl rfl
      · exact Or.inr rfl
    · exact Or.inr rfl
  · exact Or.inr rfl

private theorem eval_call_rlp_put_be_no_exn {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dstExp vExp nExp : ExpHOL 64)
    (dst0 v0 n0 : BitVec 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) vExp =
      some (.val (.word v0)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n0)))
    (hfit : dst0.toNat + n0.toNat ≤ 2 ^ 64)
    (hin_ivl : 0 < n0.toNat → ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "rlp_put_be") [dstExp, vExp, nExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "rlp_put_be") [dstExp, vExp, nExp])
    (out.1 = none → ByteRegionEffect s out.2 Rl ∧ out.2.locals = s.locals) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  exact eval_call_rlp_put_be s dstExp vExp nExp dst0 v0 n0 Rl hcode hdst hv hn hfit hin_ivl hnt

/-- Exact body evaluation of `rlp_write_header(dst, base, n)` (`guestAst[120]`, AST line 4732):
if it `Resumes`, it returns `rv = .val (.word h)` with `1 ≤ h.toNat ≤ 9`, `dst0.toNat < heapEnd`,
and `ByteRegionEffect s out.2 Rl` whenever `[dst0.toNat, dst0.toNat + 9) ⊆ ivl ∈ Rl`. -/
private theorem eval_rlp_write_header_body {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dst0 base0 n0 : BitVec 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (_hbase : s.locals.lookup (ofString "base") = some (.val (.word base0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + 9 ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_write_header)).1 ≠
      some .timeOut) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_write_header)
    (∀ rv, out.1 = some (.returned rv) →
      ∃ h : BitVec 64, rv = .val (.word h) ∧ 1 ≤ h.toNat ∧ h.toNat ≤ 9 ∧
        dst0.toNat < heapEnd ∧ ByteRegionEffect s out.2 Rl) ∧
    (∀ r, out.1 = some r → (∀ rv, r ≠ .returned rv) → ¬ Resumes (some r)) := by
  have hb : sourceFnBody Guest.Software.guestFn_rlp_write_header =
      .seq
        (.ite (.cmp .notLower (.const 55) (.var .local (ofString "n")))
          (.seq
            (.storeByte (.var .local (ofString "dst"))
              (.op .add [.var .local (ofString "base"), .var .local (ofString "n")]))
            (.return (.const 1)))
          .skip)
        (.decCall (ofString "ll") .one (ofString "rlp_be_len") [.var .local (ofString "n")]
          (.seq
            (.storeByte (.var .local (ofString "dst"))
              (.op .add [.var .local (ofString "base"), .const 55, .var .local (ofString "ll")]))
            (.seq
              (.call (some (none, none)) (ofString "rlp_put_be")
                [.op .add [.var .local (ofString "dst"), .const 1],
                 .var .local (ofString "n"),
                 .var .local (ofString "ll")])
              (.return (.op .add [.const 1, .var .local (ofString "ll")]))))) := rfl
  dsimp only
  rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
  have hev_c : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.const 55) (.var .local (ofString "n"))) =
      some (.val (.word (if n0.toNat ≤ 55 then 1 else 0))) := by
    simp [evalHOLExact, hn, Compiler.Encoders.Asm.wordCmpHOL, BitVec.le_def]
  rw [hev_c] at hnt ⊢
  dsimp only at hnt ⊢
  by_cases hn55 : n0.toNat ≤ 55
  · -- Short header (`n0 ≤ 55`): `storeByte dst (base + n); return 1`
    rw [if_pos hn55] at hnt ⊢
    have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    rw [if_neg h10] at hnt ⊢
    rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
    rcases hsb : evaluateHOLFiniteState s
        (.storeByte (.var .local (ofString "dst"))
          (.op .add [.var .local (ofString "base"), .var .local (ofString "n")])) with ⟨rsb, s1⟩
    simp only [hsb] at hnt ⊢
    rcases storeByte_only_none_or_error s (.var .local (ofString "dst"))
        (.op .add [.var .local (ofString "base"), .var .local (ofString "n")]) with hsn | hse
    · rw [hsb] at hsn; dsimp only at hsn; subst hsn
      dsimp only at hnt ⊢
      obtain ⟨dst0', hdst0', hdst_lt_he⟩ := storeByte_local_dst_inv s _ hma (by rw [hsb])
      have hdst_eq : dst0' = dst0 := by
        rw [hdst] at hdst0'
        injection hdst0' with h1; injection h1 with h2; injection h2 with h3
        exact h3.symm
      subst dst0'
      obtain ⟨heff1, _⟩ := ByteRegionEffect.of_storeByte (Rl := Rl) hsb (fun addr hdst_ev _ => by
        simp only [evalHOLExact, hdst, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst_ev
        subst hdst_ev
        obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
        exact ⟨ivl, hivl, h1, by omega⟩)
      rw [evaluateHOLFiniteState_return]
      simp only [evalHOLExact]
      have hsz : sizeOfShapeWithContextHOL s1.structs (shapeOfHOLExact (.val (.word 1) : ValueHOL 64)) ≤ 32 := by
        simp [shapeOfHOLExact]
      rw [if_pos hsz]; dsimp only
      refine ⟨fun rv hrv => ?_, fun r hr hnr => ?_⟩
      · injection hrv with hrv'; injection hrv' with hrv''
        exact ⟨1, hrv''.symm, by decide, by decide, hdst_lt_he, heff1.with_locals_clock _ _⟩
      · injection hr with hr'; subst hr'
        exact absurd rfl (hnr _)
    · rw [hsb] at hse; dsimp only at hse; subst hse
      refine ⟨fun _ h => by simp at h, fun r hr _ => ?_⟩
      injection hr with hr'; subst hr'; exact not_resumes_error
  · -- Long header (`n0 > 55`): `decCall "ll" rlp_be_len [n] ...`
    rw [if_neg hn55, if_pos rfl, evaluateHOLFiniteState_skip] at hnt ⊢
    dsimp only at hnt ⊢
    obtain ⟨ll, mid, hll8, _, hmid_loc, hmid_eq, hnt_m, hr_eq, hs_eq⟩ :=
      eval_decCall_rlp_be_len s "ll" (.var .local (ofString "n")) n0 _ hcode
        (by simp [evalHOLExact, hn]) hnt
    rw [hr_eq, hs_eq]
    have hmid_code : mid.code = originalRuntimeCode := by rw [hmid_eq]; exact hcode
    have hmid_ma : mid.memaddrs = ordinaryDomain := by rw [hmid_eq]; exact hma
    have hmid_ll : mid.locals.lookup (ofString "ll") = some (.val (.word ll)) := by
      rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hmid_dst : mid.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      have hne : ofString "ll" ≠ ofString "dst" := by decide
      rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hdst]
    have hmid_n : mid.locals.lookup (ofString "n") = some (.val (.word n0)) := by
      have hne : ofString "ll" ≠ ofString "n" := by decide
      rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hn]
    have heff_s_mid : ByteRegionEffect s mid Rl := by
      rw [hmid_eq]; exact ByteRegionEffect.refl s Rl |>.with_locals_clock mid.locals mid.clock
    -- Step 2a: `storeByte dst (base + 55 + ll)`
    rw [evaluateHOLFiniteState_seq_line780] at hnt_m ⊢
    rcases hsb : evaluateHOLFiniteState mid
        (.storeByte (.var .local (ofString "dst"))
          (.op .add [.var .local (ofString "base"), .const 55, .var .local (ofString "ll")])) with ⟨rsb, s2⟩
    simp only [hsb] at hnt_m ⊢
    rcases storeByte_only_none_or_error mid (.var .local (ofString "dst"))
        (.op .add [.var .local (ofString "base"), .const 55, .var .local (ofString "ll")]) with hsn | hse
    · rw [hsb] at hsn; dsimp only at hsn; subst hsn
      dsimp only at hnt_m ⊢
      obtain ⟨dst0', hdst0', hdst_lt_he⟩ := storeByte_local_dst_inv mid _ hmid_ma (by rw [hsb])
      have hdst_eq : dst0' = dst0 := by
        rw [hmid_dst] at hdst0'
        injection hdst0' with h1; injection h1 with h2; injection h2 with h3
        exact h3.symm
      subst dst0'
      obtain ⟨heff_hdr, hs2_loc⟩ := ByteRegionEffect.of_storeByte (Rl := Rl) hsb (fun addr hdst_ev _ => by
        simp only [evalHOLExact, hmid_dst, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst_ev
        subst hdst_ev
        obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
        exact ⟨ivl, hivl, h1, by omega⟩)
      -- Step 2b: `call rlp_put_be [dst + 1, n, ll]`
      have hs2_code : s2.code = originalRuntimeCode := heff_hdr.code.trans hmid_code
      have hs2_dst : s2.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        rw [hs2_loc]; exact hmid_dst
      have hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word n0)) := by
        rw [hs2_loc]; exact hmid_n
      have hs2_ll : s2.locals.lookup (ofString "ll") = some (.val (.word ll)) := by
        rw [hs2_loc]; exact hmid_ll
      have hdst1_nat : (dst0 + 1).toNat = dst0.toNat + 1 := by
        have hhe := hdst_lt_he; rw [heapEnd_val] at hhe
        rw [BitVec.toNat_add]
        change (dst0.toNat + 1) % 2 ^ 64 = _
        exact Nat.mod_eq_of_lt (by omega)
      have hfit : (dst0 + 1).toNat + ll.toNat ≤ 2 ^ 64 := by
        have hhe := hdst_lt_he; rw [heapEnd_val] at hhe; omega
      rw [evaluateHOLFiniteState_seq_line780] at hnt_m ⊢
      rcases hc_put : evaluateHOLFiniteState s2
        (.call (some (none, none)) (ofString "rlp_put_be")
          [.op .add [.var .local (ofString "dst"), .const 1],
           .var .local (ofString "n"),
           .var .local (ofString "ll")]) with ⟨rc, s3⟩
      have hnt_put : rc ≠ some .timeOut := by
        rintro rfl; rw [hc_put] at hnt_m; exact hnt_m rfl
      have hput := eval_call_rlp_put_be_no_exn s2
        (.op .add [.var .local (ofString "dst"), .const 1])
        (.var .local (ofString "n"))
        (.var .local (ofString "ll"))
        (dst0 + 1) n0 ll Rl hs2_code
        (by simp [evalHOLExact, evalListHOLExact, hs2_dst, wordOpHOL, wordOp, valueIsWord, valueWord])
        (by simp [evalHOLExact, hs2_n])
        (by simp [evalHOLExact, hs2_ll])
        hfit
        (fun _ => by
          obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
          exact ⟨ivl, hivl, by rw [hdst1_nat]; omega, by rw [hdst1_nat]; omega⟩)
        (by rw [hc_put]; exact hnt_put)
      dsimp only at hput
      rw [hc_put] at hput
      simp only [hc_put] at hnt_m ⊢
      cases rc with
      | some r =>
        dsimp only
        have hnr := hput.2 (by simp)
        refine ⟨fun rv hrv => False.elim (hnr (Or.inl ⟨rv, hrv⟩)), fun r' hr' _ => ?_⟩
        injection hr' with hr''; subst hr''; exact hnr
      | none =>
        dsimp only at hnt_m ⊢
        obtain ⟨heff_put, hs3_loc⟩ := hput.1 rfl
        have hs3_ll : s3.locals.lookup (ofString "ll") = some (.val (.word ll)) := by
          rw [hs3_loc]; exact hs2_ll
        rw [evaluateHOLFiniteState_return]
        have hev_ret : @evalHOLExact 64 F _ s3.toExact
            (fun a => Classical.propDecidable (s3.memaddrs a))
            (.op .add [.const 1, .var .local (ofString "ll")]) =
            some (.val (.word (1 + ll))) := by
          simp [evalHOLExact, evalListHOLExact, hs3_ll, wordOpHOL, wordOp, valueIsWord, valueWord]
        rw [hev_ret]; dsimp only
        have hsz : sizeOfShapeWithContextHOL s3.structs (shapeOfHOLExact (.val (.word (1 + ll)) : ValueHOL 64)) ≤ 32 := by
          simp [shapeOfHOLExact]
        rw [if_pos hsz]; dsimp only
        have h1ll_nat : (1 + ll).toNat = 1 + ll.toNat := by
          rw [BitVec.toNat_add]
          change (1 + ll.toNat) % 2 ^ 64 = _
          exact Nat.mod_eq_of_lt (by omega)
        refine ⟨fun rv hrv => ?_, fun r hr hnr => ?_⟩
        · injection hrv with hrv'; injection hrv' with hrv''
          exact ⟨1 + ll, hrv''.symm, by omega, by omega, hdst_lt_he,
            (((heff_s_mid.trans heff_hdr).trans heff_put).with_locals_clock _ _).with_locals_clock _ _⟩
        · injection hr with hr'; subst hr'
          exact absurd rfl (hnr _)
    · rw [hsb] at hse; dsimp only at hse; subst hse
      refine ⟨fun _ h => by simp at h, fun r hr _ => ?_⟩
      injection hr with hr'; subst hr'; exact not_resumes_error

/-- `decCall` wrapper for `rlp_write_header` when argument words are already known. -/
private theorem eval_decCall_rlp_write_header_words {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (dstExp baseExp nExp : ExpHOL 64)
    (dst0 base0 n0 : BitVec 64) (cont : ProgHOL 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hv1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hv2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) baseExp =
      some (.val (.word base0)))
    (hv3 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n0)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + 9 ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_write_header") [dstExp, baseExp, nExp] cont)).1 ≠
      some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_write_header") [dstExp, baseExp, nExp] cont)).1) :
    ∃ (h : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      1 ≤ h.toNat ∧ h.toNat ≤ 9 ∧ dst0.toNat < heapEnd ∧
      ByteRegionEffect s mid Rl ∧
      mid.locals = s.locals.update (ofString lname, .val (.word h)) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "rlp_write_header") [dstExp, baseExp, nExp] cont)).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
            (ofString lname, s.locals.lookup (ofString lname)) } := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres ⊢
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, baseExp, nExp] =
      some [.val (.word dst0), .val (.word base0), .val (.word n0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hv1, hv2, hv3]
  have hlook := pan_three_word_lookup s.code.lookup (ofString "rlp_write_header")
    (ofString "dst") (ofString "base") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_rlp_write_header) dst0 base0 n0
    (by decide) (by decide) (by decide)
    (by rw [hcode]; exact lookup_rlp_write_header)
  simp only [hargs, hlook] at hnt hres ⊢
  by_cases hclk0 : s.clock = 0
  · simp [hclk0] at hnt
  · simp only [hclk0, ↓reduceIte] at hnt hres ⊢
    set cmap : HolFiniteMapExact MlS (ValueHOL 64) :=
      ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
        (ofString "base", ValueHOL.val (.word base0))).update (ofString "n", ValueHOL.val (.word n0))
    set entry := callEntryStateHOLFinite s cmap
    have hent_dst : entry.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      have h1 : ofString "n" ≠ ofString "dst" := by decide
      have h2 : ofString "base" ≠ ofString "dst" := by decide
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h1, h2, Ne.symm h1, Ne.symm h2]
    have hent_base : entry.locals.lookup (ofString "base") = some (.val (.word base0)) := by
      have h1 : ofString "n" ≠ ofString "base" := by decide
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h1, Ne.symm h1]
    have hent_n : entry.locals.lookup (ofString "n") = some (.val (.word n0)) := by
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hb : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_rlp_write_header) with ⟨br, bs⟩
    have hnt_b : br ≠ some .timeOut := by
      rintro rfl
      rw [hb] at hnt; exact hnt rfl
    obtain ⟨hret, hnonret⟩ := eval_rlp_write_header_body entry dst0 base0 n0 Rl
      hcode hma hent_dst hent_base hent_n hin_ivl (by rw [hb]; exact hnt_b)
    rw [hb] at hret hnonret
    dsimp only at hret hnonret
    simp only [hb] at hnt hres ⊢
    cases br with
    | none =>
      exact False.elim (not_resumes_error hres)
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt_b
      | exception eid ev =>
        exact False.elim (hnonret (.exception eid ev) rfl (fun _ h => by cases h) hres)
      | returned rv =>
        obtain ⟨h, rfl, hh1, hh9, hdst_lt_he, heff_b⟩ := hret rv rfl
        dsimp only at hnt hres ⊢
        have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word h) : ValueHOL 64)) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word h) : ValueHOL 64)) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        rw [if_pos hsh] at hnt hres ⊢
        let mid := setVarHOLFinite (ofString lname) (.val (.word h)) { bs with locals := s.locals }
        have heff_s_ent : ByteRegionEffect s entry Rl :=
          ByteRegionEffect.refl s Rl |>.with_locals_clock entry.locals entry.clock
        exact ⟨h, mid, hh1, hh9, hdst_lt_he,
          (heff_s_ent.trans heff_b).with_locals_clock mid.locals mid.clock, rfl, hnt, hres, rfl⟩
      | «break» =>
        exact False.elim (not_resumes_error hres)
      | «continue» =>
        exact False.elim (not_resumes_error hres)
      | error =>
        exact False.elim (not_resumes_error hres)
      | finalFfi f =>
        rcases hres with ⟨_, hr⟩ | ⟨_, _, hr, _⟩ <;> simp at hr

private theorem eval_decCall_rlp_write_header_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (dstExp baseExp nExp : ExpHOL 64)
    (cont : ProgHOL 64)
    (Rfn : BitVec 64 → BitVec 64 → List Ivl)
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hin_ivl : ∀ dst0 n0 : BitVec 64,
      ∃ ivl ∈ Rfn dst0 n0, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + 9 ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_write_header") [dstExp, baseExp, nExp] cont)).1 ≠
      some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_write_header") [dstExp, baseExp, nExp] cont)).1) :
    ∃ (dst0 base0 n0 h : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
        some (.val (.word dst0)) ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) baseExp =
        some (.val (.word base0)) ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
        some (.val (.word n0)) ∧
      1 ≤ h.toNat ∧ h.toNat ≤ 9 ∧ dst0.toNat < heapEnd ∧
      ByteRegionEffect s mid (Rfn dst0 n0) ∧
      mid.locals = s.locals.update (ofString lname, .val (.word h)) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "rlp_write_header") [dstExp, baseExp, nExp] cont)).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
            (ofString lname, s.locals.lookup (ofString lname)) } := by
  have hwords : ∃ dst0 base0 n0 : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
        some (.val (.word dst0)) ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) baseExp =
        some (.val (.word base0)) ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
        some (.val (.word n0)) := by
    have hres' := hres
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hres'
    rcases hv1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp with _ | v1
    · simp [evalListHOLFinite, evalListHOLExact, hv1] at hres'
      exact False.elim (not_resumes_error hres')
    · rcases hv2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) baseExp with _ | v2
      · simp [evalListHOLFinite, evalListHOLExact, hv1, hv2] at hres'
        exact False.elim (not_resumes_error hres')
      · rcases hv3 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp with _ | v3
        · simp [evalListHOLFinite, evalListHOLExact, hv1, hv2, hv3] at hres'
          exact False.elim (not_resumes_error hres')
        · have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
              [dstExp, baseExp, nExp] = some [v1, v2, v3] := by
            simp [evalListHOLFinite, evalListHOLExact, hv1, hv2, hv3]
          rw [hargs] at hres'; dsimp only at hres'
          rcases hl : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup (ofString "rlp_write_header") [v1, v2, v3] with _ | ⟨b, c, rs⟩
          · rw [hl] at hres'; exact False.elim (not_resumes_error hres')
          · have hraw : lookupCodeHOLExact s.code.lookup (ofString "rlp_write_header") [v1, v2, v3] ≠ none := by
              intro hn
              unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
              split at hl
              · simp at hl
              · rename_i hsome; rw [hn] at hsome; simp at hsome
            have hcl := lookup_rlp_write_header
            rw [← hcode] at hcl
            simp only [lookupCodeHOLExact, hcl, List.length_cons, List.length_nil, ↓reduceIte,
              List.zip, List.zipWith, List.all, Bool.and_true, Bool.and_eq_true] at hraw
            have hsh : shapeEqHOL .one (shapeOfHOLExact v1) = true ∧
                shapeEqHOL .one (shapeOfHOLExact v2) = true ∧
                shapeEqHOL .one (shapeOfHOLExact v3) = true := by
              by_contra hns; simp [hns] at hraw
            have hw : ∀ v : ValueHOL 64, shapeEqHOL .one (shapeOfHOLExact v) = true → ∃ w, v = .val (.word w) := by
              intro v hsv; rcases v with ⟨⟨w⟩⟩ | _ | _
              · exact ⟨w, rfl⟩
              · simp [shapeOfHOLExact, shapeEqHOL] at hsv
              · simp [shapeOfHOLExact, shapeEqHOL] at hsv
            obtain ⟨dst0, rfl⟩ := hw v1 hsh.1
            obtain ⟨base0, rfl⟩ := hw v2 hsh.2.1
            obtain ⟨n0, rfl⟩ := hw v3 hsh.2.2
            exact ⟨dst0, base0, n0, rfl, rfl, rfl⟩
  obtain ⟨dst0, base0, n0, h1, h2, h3⟩ := hwords
  obtain ⟨h, mid, hh1, hh9, hdst_lt_he, heff, hmloc, hnt_m, hres_m, hseq⟩ :=
    eval_decCall_rlp_write_header_words s lname dstExp baseExp nExp dst0 base0 n0 cont
      (Rfn dst0 n0) hcode hma h1 h2 h3 (hin_ivl dst0 n0) hnt hres
  exact ⟨dst0, base0, n0, h, mid, h1, h2, h3, hh1, hh9, hdst_lt_he, heff, hmloc, hnt_m, hres_m, hseq⟩

/-- `rlp_encode_bytes` (AST line 4768): relational world step with output region. -/
theorem «wk_rlp_encode_bytes» :
    WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n" + 9)])
    []
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "rlp_encode_bytes") := by
  refine ⟨_, _, _, lookup_rlp_encode_bytes, ?_⟩
  intro F s hcode hW _ hnt hres
  suffices heff : ByteRegionEffect s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)).2
      ([(locN s "dst", locN s "n" + 9)] ++ ([] : List Ivl)) by
    exact ByteRegionEffect.to_worldStep (extra := fun _ => []) hW (fun _ h => by simp at h) heff
  simp only [List.append_nil]
  let Rl : List Ivl := [(locN s "dst", locN s "n" + 9)]
  change ByteRegionEffect s
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)).2 Rl
  have hb : sourceFnBody Guest.Software.guestFn_rlp_encode_bytes =
      .seq
        (.ite (.cmp .equal (.var .local (ofString "n")) (.const 1))
          (.dec (ofString "b") .one (.loadByte (.var .local (ofString "src")))
            (.ite (.cmp .lower (.var .local (ofString "b")) (.const 128))
              (.seq
                (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "b")))
                (.return (.const 1)))
              .skip))
          .skip)
        (.decCall (ofString "h") .one (ofString "rlp_write_header")
          [.var .local (ofString "dst"), .const 128, .var .local (ofString "n")]
          (.seq
            (.call (some (none, none)) (ofString "memcpy")
              [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
               .var .local (ofString "src"),
               .var .local (ofString "n")])
            (.return (.op .add [.var .local (ofString "h"), .var .local (ofString "n")])))) := rfl
  rw [hb] at hnt hres ⊢
  have hma : s.memaddrs = ordinaryDomain := hW.1.1.memaddrs
  -- Extract `n` as a word:
  have hn_ex : ∃ n0 : BitVec 64, s.locals.lookup (ofString "n") = some (.val (.word n0)) := by
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres
    rcases hn : s.locals.lookup (ofString "n") with _ | nv
    · simp [evalHOLExact, hn] at hres; exact False.elim (not_resumes_error hres)
    · rcases nv with ⟨⟨n0⟩⟩ | _ | _
      · exact ⟨n0, rfl⟩
      · simp [evalHOLExact, hn] at hres; exact False.elim (not_resumes_error hres)
      · simp [evalHOLExact, hn] at hres; exact False.elim (not_resumes_error hres)
  obtain ⟨n0, hn0⟩ := hn_ex
  -- Step 1: Analyze the `ite (n == 1)` prefix: either it returns `(some (.returned 1), post)` with
  -- `ByteRegionEffect s post Rl`, or it falls through with `(none, s')` where `s'` differs from `s`
  -- only in `locals` and `clock` and `s'.locals = s.locals`!
  let tailP : ProgHOL 64 :=
    .decCall (ofString "h") .one (ofString "rlp_write_header")
      [.var .local (ofString "dst"), .const 128, .var .local (ofString "n")]
      (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
           .var .local (ofString "src"),
           .var .local (ofString "n")])
        (.return (.op .add [.var .local (ofString "h"), .var .local (ofString "n")])))
  -- Prove `tailP` on any state `t` that agrees with `s` on `code, memaddrs, locals`:
  have htail : ∀ (t : PanSemStateFiniteExact 64 F),
      ByteRegionEffect s t Rl →
      t.locals = s.locals →
      (evaluateHOLFiniteState t tailP).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState t tailP).1 →
      ByteRegionEffect s (evaluateHOLFiniteState t tailP).2 Rl := by
    intro t heff_t ht_loc hnt_t hres_t
    have ht_code : t.code = originalRuntimeCode := heff_t.code.trans hcode
    have ht_ma : t.memaddrs = ordinaryDomain := heff_t.memaddrs.trans hma
    obtain ⟨dst0, base0, n0', h, mid, hdst_ev, _, hn_ev, hh1, hh9, hdst_lt_he,
      heff_hdr, hmid_loc, hnt_m, hres_m, hs_eq⟩ :=
      eval_decCall_rlp_write_header_resumes t "h"
        (.var .local (ofString "dst")) (.const 128) (.var .local (ofString "n")) _
        (fun d nn => [(d.toNat, nn.toNat + 9)])
        ht_code ht_ma
        (fun d nn => ⟨(d.toNat, nn.toNat + 9), List.mem_singleton.2 rfl, le_refl _, by omega⟩)
        hnt_t hres_t
    have ht_dst : t.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      rcases hd : t.locals.lookup (ofString "dst") with _ | dv
      · simp [evalHOLExact, hd] at hdst_ev
      · simpa [evalHOLExact, hd] using hdst_ev
    have hs_dst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      rw [← ht_loc]; exact ht_dst
    have ht_n : t.locals.lookup (ofString "n") = some (.val (.word n0')) := by
      rcases hn' : t.locals.lookup (ofString "n") with _ | nv
      · simp [evalHOLExact, hn'] at hn_ev
      · simpa [evalHOLExact, hn'] using hn_ev
    have hn_eq : n0' = n0 := by
      rw [ht_loc, hn0] at ht_n
      injection ht_n with h1; injection h1 with h2; injection h2 with h3
      exact h3.symm
    subst n0'
    have hdst_nat : locN s "dst" = dst0.toNat := by simp [locN, hs_dst]
    have hn_nat : locN s "n" = n0.toNat := by simp [locN, hn0]
    have hRl_eq : ([(dst0.toNat, n0.toNat + 9)] : List Ivl) = Rl := by
      dsimp only [Rl]; rw [hdst_nat, hn_nat]
    rw [hRl_eq] at heff_hdr
    rw [hs_eq]
    -- Now in `mid`: `seq (call "memcpy" [dst + h, src, n]) (return (h + n))`
    have hmid_code : mid.code = originalRuntimeCode := heff_hdr.code.trans ht_code
    have hmid_ma : mid.memaddrs = ordinaryDomain := heff_hdr.memaddrs.trans ht_ma
    have hmid_h : mid.locals.lookup (ofString "h") = some (.val (.word h)) := by
      rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hmid_dst : mid.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      have hne : ofString "h" ≠ ofString "dst" := by decide
      rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, ht_dst]
    have hmid_n : mid.locals.lookup (ofString "n") = some (.val (.word n0)) := by
      have hne : ofString "h" ≠ ofString "n" := by decide
      rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, ht_n]
    have hmid_src_lk : mid.locals.lookup (ofString "src") = s.locals.lookup (ofString "src") := by
      have hne : ofString "h" ≠ ofString "src" := by decide
      rw [hmid_loc, ht_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne]
    rw [evaluateHOLFiniteState_seq_line780] at hnt_m hres_m ⊢
    rcases hc_mc : evaluateHOLFiniteState mid
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
         .var .local (ofString "src"),
         .var .local (ofString "n")]) with ⟨rmc, smc⟩
    have hnt_mc : rmc ≠ some .timeOut := by
      rintro rfl; rw [hc_mc] at hnt_m; exact hnt_m rfl
    -- Extract `src0` from `memcpy` not erroring (since `hres_m` holds):
    have hmc_nerr : rmc ≠ some .error := by
      rintro rfl; rw [hc_mc] at hres_m; exact not_resumes_error hres_m
    have hsrc_ex : ∃ src0 : BitVec 64, mid.locals.lookup (ofString "src") = some (.val (.word src0)) := by
      rw [evaluateHOLFiniteState_call] at hc_mc
      rcases hsrc : mid.locals.lookup (ofString "src") with _ | sv
      · simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hmid_dst, hmid_h, hsrc,
          wordOpHOL, wordOp, valueIsWord, valueWord] at hc_mc
        exact absurd hc_mc.1.symm hmc_nerr
      · rcases sv with ⟨⟨src0⟩⟩ | fields | ⟨nm, fields⟩
        · exact ⟨src0, rfl⟩
        · have hevl : evalListHOLFinite mid (h := fun a => Classical.propDecidable (mid.memaddrs a))
              [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
               .var .local (ofString "src"), .var .local (ofString "n")] =
              some [.val (.word (dst0 + h)), .rStruct fields, .val (.word n0)] := by
            simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hmid_dst, hmid_h, hmid_n, hsrc,
              wordOpHOL, wordOp, valueIsWord, valueWord]
          rw [hevl] at hc_mc; dsimp only at hc_mc
          have hlk_none : PanSemStateFiniteExact.lookupCodeHOLFinite mid.code.lookup (ofString "memcpy")
              [.val (.word (dst0 + h)), .rStruct fields, .val (.word n0)] = none := by
            have hraw : lookupCodeHOLExact mid.code.lookup (ofString "memcpy")
                [.val (.word (dst0 + h)), .rStruct fields, .val (.word n0)] = none := by
              unfold lookupCodeHOLExact
              rw [hmid_code, lookup_memcpy]
              simp [shapeOfHOLExact, shapeEqHOL]
            unfold PanSemStateFiniteExact.lookupCodeHOLFinite
            split
            · rfl
            · rename_i hsome; rw [hraw] at hsome; simp at hsome
          rw [hlk_none] at hc_mc; dsimp only at hc_mc
          injection hc_mc with hr_eq _; exact absurd hr_eq.symm hmc_nerr
        · have hevl : evalListHOLFinite mid (h := fun a => Classical.propDecidable (mid.memaddrs a))
              [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
               .var .local (ofString "src"), .var .local (ofString "n")] =
              some [.val (.word (dst0 + h)), .nStruct nm fields, .val (.word n0)] := by
            simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hmid_dst, hmid_h, hmid_n, hsrc,
              wordOpHOL, wordOp, valueIsWord, valueWord]
          rw [hevl] at hc_mc; dsimp only at hc_mc
          have hlk_none : PanSemStateFiniteExact.lookupCodeHOLFinite mid.code.lookup (ofString "memcpy")
              [.val (.word (dst0 + h)), .nStruct nm fields, .val (.word n0)] = none := by
            have hraw : lookupCodeHOLExact mid.code.lookup (ofString "memcpy")
                [.val (.word (dst0 + h)), .nStruct nm fields, .val (.word n0)] = none := by
              unfold lookupCodeHOLExact
              rw [hmid_code, lookup_memcpy]
              simp [shapeOfHOLExact, shapeEqHOL]
            unfold PanSemStateFiniteExact.lookupCodeHOLFinite
            split
            · rfl
            · rename_i hsome; rw [hraw] at hsome; simp at hsome
          rw [hlk_none] at hc_mc; dsimp only at hc_mc
          injection hc_mc with hr_eq _; exact absurd hr_eq.symm hmc_nerr
    obtain ⟨src0, hmid_src⟩ := hsrc_ex
    have hdsth_nat : (dst0 + h).toNat = dst0.toNat + h.toNat := by
      have hhe := hdst_lt_he; rw [heapEnd_val] at hhe
      rw [BitVec.toNat_add]
      exact Nat.mod_eq_of_lt (by omega)
    have hmc := eval_call_memcpy_bre_gen mid
      (.op .add [.var .local (ofString "dst"), .var .local (ofString "h")])
      (.var .local (ofString "src"))
      (.var .local (ofString "n"))
      (dst0 + h) src0 n0 Rl hmid_code hmid_ma
      (by simp [evalHOLExact, evalListHOLExact, hmid_dst, hmid_h, wordOpHOL, wordOp, valueIsWord, valueWord])
      (by simp [evalHOLExact, hmid_src])
      (by simp [evalHOLExact, hmid_n])
      (fun off hoff _ => ⟨(locN s "dst", locN s "n" + 9), List.mem_singleton.2 rfl,
        by dsimp only; rw [hdst_nat, hdsth_nat]; omega,
        by dsimp only; rw [hdst_nat, hn_nat, hdsth_nat]; omega⟩)
      (fun off hoff _ => ⟨(locN s "dst", locN s "n" + 9), List.mem_singleton.2 rfl,
        by dsimp only; rw [hdst_nat, hdsth_nat]; omega,
        by dsimp only; rw [hdst_nat, hn_nat, hdsth_nat]; omega⟩)
      (by rw [hc_mc]; exact hnt_mc)
    dsimp only at hmc
    rw [hc_mc] at hmc
    simp only [hc_mc] at hres_m ⊢
    cases rmc with
    | some r =>
      dsimp only at hres_m
      exact False.elim (hmc.2 (by simp) hres_m)
    | none =>
      dsimp only at hres_m ⊢
      obtain ⟨heff_mc, hsmc_loc⟩ := hmc.1 rfl
      have hsmc_h : smc.locals.lookup (ofString "h") = some (.val (.word h)) := by
        rw [hsmc_loc]; exact hmid_h
      have hsmc_n : smc.locals.lookup (ofString "n") = some (.val (.word n0)) := by
        rw [hsmc_loc]; exact hmid_n
      rw [evaluateHOLFiniteState_return]
      have hev_ret : @evalHOLExact 64 F _ smc.toExact
          (fun a => Classical.propDecidable (smc.memaddrs a))
          (.op .add [.var .local (ofString "h"), .var .local (ofString "n")]) =
          some (.val (.word (h + n0))) := by
        simp [evalHOLExact, evalListHOLExact, hsmc_h, hsmc_n, wordOpHOL, wordOp, valueIsWord, valueWord]
      rw [hev_ret]; dsimp only
      have hsz : sizeOfShapeWithContextHOL smc.structs (shapeOfHOLExact (.val (.word (h + n0)) : ValueHOL 64)) ≤ 32 := by
        simp [shapeOfHOLExact]
      rw [if_pos hsz]; dsimp only
      exact ((((heff_t.trans heff_hdr).trans heff_mc).with_locals_clock _ _).with_locals_clock _ _)
  -- Now discharge the outer `seq (ite (n == 1) ... skip) tailP`:
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt hres ⊢
  have hev_n1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.var .local (ofString "n")) (.const 1)) =
      some (.val (.word (if n0 = 1 then 1 else 0))) := by
    simp [evalHOLExact, hn0, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hev_n1] at hnt hres ⊢
  dsimp only at hnt hres ⊢
  by_cases hn1 : n0 = 1
  · rw [if_pos hn1] at hnt hres ⊢
    have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    rw [if_neg h10] at hnt hres ⊢
    rw [evaluateHOLFiniteState_dec_total] at hnt hres ⊢
    dsimp only at hnt hres ⊢
    rcases hlb : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.loadByte (.var .local (ofString "src"))) with _ | bv
    · simp [hlb] at hres; exact False.elim (not_resumes_error hres)
    · have hbv_w : ∃ b0 : BitVec 64, bv = .val (.word b0) := by
        rcases hsrc : s.locals.lookup (ofString "src") with _ | sv
        · simp [evalHOLExact, hsrc] at hlb
        · rcases sv with ⟨⟨src0⟩⟩ | _ | _
          · simp only [evalHOLExact, hsrc] at hlb
            unfold panMemLoadByteHOL at hlb
            dsimp only at hlb
            cases hm : s.memory (panByteAlignHOL src0) with
            | word cell =>
              simp only [hm] at hlb
              split at hlb
              · simp only [Option.map, Option.some.injEq] at hlb
                exact ⟨_, hlb.symm⟩
              · simp at hlb
          · simp [evalHOLExact, hsrc] at hlb
          · simp [evalHOLExact, hsrc] at hlb
      obtain ⟨b0, rfl⟩ := hbv_w
      simp only [hlb] at hnt hres ⊢
      have hsh_b : shapeEqHOL .one (shapeOfHOLExact (.val (.word b0) : ValueHOL 64)) = true := by
        simp [shapeEqHOL, shapeOfHOLExact]
      rw [if_pos hsh_b] at hnt hres ⊢
      set sb := setVarHOLFinite (ofString "b") (.val (.word b0)) s
      have hsb_b : sb.locals.lookup (ofString "b") = some (.val (.word b0)) := by
        simp [sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hsb_dst_lk : sb.locals.lookup (ofString "dst") = s.locals.lookup (ofString "dst") := by
        have hne : ofString "b" ≠ ofString "dst" := by decide
        simp [sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne]
      rw [evaluateHOLFiniteState_ite] at hnt hres ⊢
      have hev_blt : @evalHOLExact 64 F _ sb.toExact (fun a => Classical.propDecidable (sb.memaddrs a))
          (.cmp .lower (.var .local (ofString "b")) (.const 128)) =
          some (.val (.word (if b0 < 128 then 1 else 0))) := by
        simp [evalHOLExact, hsb_b, Compiler.Encoders.Asm.wordCmpHOL]
      rw [hev_blt] at hnt hres ⊢
      dsimp only at hnt hres ⊢
      by_cases hblt : b0 < 128
      · -- Fast 1-byte path (`n == 1 && b < 128`): `storeByte dst b; return 1`
        rw [if_pos hblt, if_neg h10] at hnt hres ⊢
        rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
        rcases hst : evaluateHOLFiniteState sb
            (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "b"))) with ⟨rst, s1⟩
        simp only [hst] at hres ⊢
        rcases storeByte_only_none_or_error sb (.var .local (ofString "dst")) (.var .local (ofString "b")) with hsn | hse
        · rw [hst] at hsn; dsimp only at hsn; subst hsn
          dsimp only at hres ⊢
          obtain ⟨dst0, hsb_dst, _⟩ := storeByte_local_dst_inv sb (.var .local (ofString "b")) hma (by rw [hst])
          have hs_dst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
            rw [← hsb_dst_lk]; exact hsb_dst
          have hdst_nat : locN s "dst" = dst0.toNat := by simp [locN, hs_dst]
          obtain ⟨heff1, _⟩ := ByteRegionEffect.of_storeByte (Rl := Rl) hst (fun addr hdst_ev _ => by
            simp only [evalHOLExact, hsb_dst, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst_ev
            subst hdst_ev
            exact ⟨(locN s "dst", locN s "n" + 9), List.mem_singleton.2 rfl,
              by rw [hdst_nat], by dsimp only; rw [hdst_nat]; omega⟩)
          rw [evaluateHOLFiniteState_return]
          simp only [evalHOLExact]
          have hsz : sizeOfShapeWithContextHOL s1.structs (shapeOfHOLExact (.val (.word 1) : ValueHOL 64)) ≤ 32 := by
            simp [shapeOfHOLExact]
          rw [if_pos hsz]; dsimp only
          have heff_s_sb : ByteRegionEffect s sb Rl :=
            ByteRegionEffect.refl s Rl |>.with_locals_clock sb.locals sb.clock
          exact (((heff_s_sb.trans heff1).with_locals_clock _ _).with_locals_clock _ _)
        · rw [hst] at hse; dsimp only at hse; subst hse
          exact False.elim (not_resumes_error hres)
      · -- `b0 ≥ 128`: inner `ite` skips, `dec "b"` restores `b`, falls through to `tailP`!
        rw [if_neg hblt, if_pos rfl, evaluateHOLFiniteState_skip] at hnt hres ⊢
        dsimp only at hnt hres ⊢
        let s' : PanSemStateFiniteExact 64 F :=
          { sb with locals := HolFiniteMapExact.resVarEq sb.locals (ofString "b", s.locals.lookup (ofString "b")) }
        have hs'_loc : s'.locals = s.locals := by
          dsimp only [s']
          apply HolFiniteMapExact.ext
          funext k
          change (HolFiniteMapExact.resVarEq sb.locals (ofString "b", s.locals.lookup (ofString "b"))).lookup k = s.locals.lookup k
          rw [PanRunBounded.resVarEq_lookup]
          by_cases hk : k = ofString "b"
          · subst hk; simp
          · simp [hk, sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
        exact htail s' (ByteRegionEffect.refl s Rl |>.with_locals_clock s'.locals s'.clock) hs'_loc hnt hres
  · -- `n0 ≠ 1`: outer `ite` skips immediately, falls through to `tailP` on `s`!
    rw [if_neg hn1, if_pos rfl, evaluateHOLFiniteState_skip] at hnt hres ⊢
    dsimp only at hnt hres ⊢
    exact htail s (ByteRegionEffect.refl s Rl) rfl hnt hres

end InitECandidate.Solver.Wave8GuestInv.M11
