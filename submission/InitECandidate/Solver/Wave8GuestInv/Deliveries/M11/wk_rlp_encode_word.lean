import InitECandidate.Solver.Wave8GuestInv.Deliveries.M11.RlpMemcpyLemmas

/-! `wk_rlp_encode_word`: relational world step with output region `(locN s "dst", 9)` for
`rlp_encode_word` (`Guest/SoftwareAst.lean:4790`, `guestAst[123]`).

Checked against frozen spec revision 9 (`8a79d9f28`, tag `wave8-spec-frozen-r9`).
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

theorem lookup_rlp_encode_word :
    originalRuntimeCode.lookup (ofString "rlp_encode_word") =
      some ([(ofString "dst", .one), (ofString "w", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_encode_word, .one) :=
  lookup_of_guestAst_getElem 123 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_encode_word) rfl

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

/-- `rlp_encode_word` (AST line 4790): relational world step with output region. -/
theorem «wk_rlp_encode_word» :
    WorldKeeps WorldOK (fun s => [(locN s "dst", 9)])
    []
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "rlp_encode_word") := by
  refine ⟨_, _, _, lookup_rlp_encode_word, ?_⟩
  intro F s hcode hW _ hnt hres
  suffices heff : ByteRegionEffect s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_encode_word)).2
      ([(locN s "dst", 9)] ++ ([] : List Ivl)) by
    exact ByteRegionEffect.to_worldStep (extra := fun _ => []) hW (fun _ h => by simp at h) heff
  simp only [List.append_nil]
  let Rl : List Ivl := [(locN s "dst", 9)]
  change ByteRegionEffect s
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_encode_word)).2 Rl
  have hb : sourceFnBody Guest.Software.guestFn_rlp_encode_word =
      .seq
        (.ite (.cmp .equal (.var .local (ofString "w")) (.const 0))
          (.seq
            (.storeByte (.var .local (ofString "dst")) (.const 128))
            (.return (.const 1)))
          .skip)
        (.seq
          (.ite (.cmp .lower (.var .local (ofString "w")) (.const 128))
            (.seq
              (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "w")))
              (.return (.const 1)))
            .skip)
          (.decCall (ofString "ll") .one (ofString "rlp_be_len") [.var .local (ofString "w")]
            (.seq
              (.storeByte (.var .local (ofString "dst"))
                (.op .add [.const 128, .var .local (ofString "ll")]))
              (.seq
                (.call (some (none, none)) (ofString "rlp_put_be")
                  [.op .add [.var .local (ofString "dst"), .const 1],
                   .var .local (ofString "w"),
                   .var .local (ofString "ll")])
                (.return (.op .add [.const 1, .var .local (ofString "ll")])))))) := rfl
  rw [hb] at hnt hres ⊢
  -- Extract `w` as a word:
  have hw_ex : ∃ w0 : BitVec 64, s.locals.lookup (ofString "w") = some (.val (.word w0)) := by
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres
    rcases hw : s.locals.lookup (ofString "w") with _ | wv
    · simp [evalHOLExact, hw] at hres; exact False.elim (not_resumes_error hres)
    · rcases wv with ⟨⟨w0⟩⟩ | _ | _
      · exact ⟨w0, rfl⟩
      · simp [evalHOLExact, hw] at hres; exact False.elim (not_resumes_error hres)
      · simp [evalHOLExact, hw] at hres; exact False.elim (not_resumes_error hres)
  obtain ⟨w0, hw0⟩ := hw_ex
  -- Branch 1: `w0 = 0` vs `w0 ≠ 0`
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt hres ⊢
  have hev_c1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.var .local (ofString "w")) (.const 0)) =
      some (.val (.word (if w0 = 0 then 1 else 0))) := by
    simp [evalHOLExact, hw0, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hev_c1] at hnt hres ⊢
  dsimp only at hnt hres ⊢
  by_cases hwz : w0 = 0
  · -- Branch 1 (`w0 = 0`): `storeByte dst 128; return 1`
    rw [if_pos hwz] at hnt hres ⊢
    have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    rw [if_neg h10] at hnt hres ⊢
    rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
    rcases hsb : evaluateHOLFiniteState s (.storeByte (.var .local (ofString "dst")) (.const 128)) with ⟨rsb, s1⟩
    simp only [hsb] at hres ⊢
    rcases storeByte_only_none_or_error s (.var .local (ofString "dst")) (.const 128) with hsn | hse
    · rw [hsb] at hsn; dsimp only at hsn; subst hsn
      dsimp only at hres ⊢
      obtain ⟨dst0, hdst0, _⟩ := storeByte_local_dst_inv s (.const 128) hW.1.1.memaddrs (by rw [hsb])
      have hdst_nat : locN s "dst" = dst0.toNat := by simp [locN, hdst0]
      obtain ⟨heff1, _⟩ := ByteRegionEffect.of_storeByte hsb (Rl := Rl) (fun addr hdst_ev _ => by
        simp only [evalHOLExact, hdst0, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst_ev
        subst hdst_ev
        exact ⟨(locN s "dst", 9), List.mem_singleton.2 rfl, by rw [hdst_nat], by rw [hdst_nat]; omega⟩)
      rw [evaluateHOLFiniteState_return]
      simp only [evalHOLExact]
      have hsz : sizeOfShapeWithContextHOL s1.structs (shapeOfHOLExact (.val (.word 1) : ValueHOL 64)) ≤ 32 := by
        simp [shapeOfHOLExact]
      rw [if_pos hsz]
      exact heff1.with_locals_clock _ _
    · rw [hsb] at hse; dsimp only at hse; subst hse
      exact False.elim (not_resumes_error hres)
  · -- `w0 ≠ 0`: skip first `ite`
    rw [if_neg hwz, if_pos rfl, evaluateHOLFiniteState_skip] at hnt hres ⊢
    dsimp only at hnt hres ⊢
    -- Branch 2: `w0 < 128` vs `¬ (w0 < 128)`
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt hres ⊢
    have hev_c2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .lower (.var .local (ofString "w")) (.const 128)) =
        some (.val (.word (if w0 < 128 then 1 else 0))) := by
      simp [evalHOLExact, hw0, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hev_c2] at hnt hres ⊢
    dsimp only at hnt hres ⊢
    by_cases hw128 : w0 < 128
    · rw [if_pos hw128] at hnt hres ⊢
      have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
      rw [if_neg h10] at hnt hres ⊢
      rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
      rcases hsb : evaluateHOLFiniteState s
          (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "w"))) with ⟨rsb, s1⟩
      simp only [hsb] at hres ⊢
      rcases storeByte_only_none_or_error s (.var .local (ofString "dst")) (.var .local (ofString "w")) with hsn | hse
      · rw [hsb] at hsn; dsimp only at hsn; subst hsn
        dsimp only at hres ⊢
        obtain ⟨dst0, hdst0, _⟩ := storeByte_local_dst_inv s (.var .local (ofString "w")) hW.1.1.memaddrs (by rw [hsb])
        have hdst_nat : locN s "dst" = dst0.toNat := by simp [locN, hdst0]
        obtain ⟨heff1, _⟩ := ByteRegionEffect.of_storeByte hsb (Rl := Rl) (fun addr hdst_ev _ => by
          simp only [evalHOLExact, hdst0, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst_ev
          subst hdst_ev
          exact ⟨(locN s "dst", 9), List.mem_singleton.2 rfl, by rw [hdst_nat], by rw [hdst_nat]; omega⟩)
        rw [evaluateHOLFiniteState_return]
        simp only [evalHOLExact]
        have hsz : sizeOfShapeWithContextHOL s1.structs (shapeOfHOLExact (.val (.word 1) : ValueHOL 64)) ≤ 32 := by
          simp [shapeOfHOLExact]
        rw [if_pos hsz]
        exact heff1.with_locals_clock _ _
      · rw [hsb] at hse; dsimp only at hse; subst hse
        exact False.elim (not_resumes_error hres)
    · -- Branch 3: `w0 ≥ 128`: `decCall "ll" rlp_be_len [w] ...`
      rw [if_neg hw128, if_pos rfl, evaluateHOLFiniteState_skip] at hnt hres ⊢
      dsimp only at hnt hres ⊢
      obtain ⟨ll, mid, hll8, _, hmid_loc, hmid_eq, hnt_m, hr_eq, hs_eq⟩ :=
        eval_decCall_rlp_be_len s "ll" (.var .local (ofString "w")) w0 _ hcode
          (by simp [evalHOLExact, hw0]) hnt
      rw [hr_eq] at hres
      rw [hs_eq]
      have hmid_code : mid.code = originalRuntimeCode := by rw [hmid_eq]; exact hcode
      have hmid_ma : mid.memaddrs = ordinaryDomain := by rw [hmid_eq]; exact hW.1.1.memaddrs
      have hmid_ll : mid.locals.lookup (ofString "ll") = some (.val (.word ll)) := by
        rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
      have hmid_w : mid.locals.lookup (ofString "w") = some (.val (.word w0)) := by
        have hne : ofString "ll" ≠ ofString "w" := by decide
        rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hw0]
      have hmid_dst_lk : mid.locals.lookup (ofString "dst") = s.locals.lookup (ofString "dst") := by
        have hne : ofString "ll" ≠ ofString "dst" := by decide
        rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne]
      have heff_s_mid : ByteRegionEffect s mid Rl := by
        rw [hmid_eq]; exact ByteRegionEffect.refl s Rl |>.with_locals_clock mid.locals mid.clock
      -- Step 3a: `storeByte dst (128 + ll)`
      rw [evaluateHOLFiniteState_seq_line780] at hnt_m hres ⊢
      rcases hsb : evaluateHOLFiniteState mid
          (.storeByte (.var .local (ofString "dst"))
            (.op .add [.const 128, .var .local (ofString "ll")])) with ⟨rsb, s2⟩
      simp only [hsb] at hnt_m hres ⊢
      rcases storeByte_only_none_or_error mid (.var .local (ofString "dst"))
          (.op .add [.const 128, .var .local (ofString "ll")]) with hsn | hse
      · rw [hsb] at hsn; dsimp only at hsn; subst hsn
        dsimp only at hnt_m hres ⊢
        obtain ⟨dst0, hmid_dst, hdst_lt_he⟩ :=
          storeByte_local_dst_inv mid (.op .add [.const 128, .var .local (ofString "ll")])
            hmid_ma (by rw [hsb])
        have hs_dst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
          rw [← hmid_dst_lk]; exact hmid_dst
        have hdst_nat : locN s "dst" = dst0.toNat := by simp [locN, hs_dst]
        obtain ⟨heff_hdr, hs2_loc⟩ := ByteRegionEffect.of_storeByte (Rl := Rl) hsb (fun addr hdst_ev _ => by
          simp only [evalHOLExact, hmid_dst, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst_ev
          subst hdst_ev
          exact ⟨(locN s "dst", 9), List.mem_singleton.2 rfl, by rw [hdst_nat], by rw [hdst_nat]; omega⟩)
        -- Step 3b: `call rlp_put_be [dst + 1, w, ll]`
        have hs2_code : s2.code = originalRuntimeCode := heff_hdr.code.trans hmid_code
        have hs2_dst : s2.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
          rw [hs2_loc]; exact hmid_dst
        have hs2_w : s2.locals.lookup (ofString "w") = some (.val (.word w0)) := by
          rw [hs2_loc]; exact hmid_w
        have hs2_ll : s2.locals.lookup (ofString "ll") = some (.val (.word ll)) := by
          rw [hs2_loc]; exact hmid_ll
        have hdst1_nat : (dst0 + 1).toNat = dst0.toNat + 1 := by
          rw [heapEnd_val] at hdst_lt_he
          rw [BitVec.toNat_add]
          change (dst0.toNat + 1) % 2 ^ 64 = _
          exact Nat.mod_eq_of_lt (by omega)
        have hfit : (dst0 + 1).toNat + ll.toNat ≤ 2 ^ 64 := by
          rw [heapEnd_val] at hdst_lt_he
          omega
        rw [evaluateHOLFiniteState_seq_line780] at hnt_m hres ⊢
        rcases hc_put : evaluateHOLFiniteState s2
          (.call (some (none, none)) (ofString "rlp_put_be")
            [.op .add [.var .local (ofString "dst"), .const 1],
             .var .local (ofString "w"),
             .var .local (ofString "ll")]) with ⟨rc, s3⟩
        have hnt_put : rc ≠ some .timeOut := by
          rintro rfl
          rw [hc_put] at hnt_m
          exact hnt_m rfl
        have hput := eval_call_rlp_put_be s2
          (.op .add [.var .local (ofString "dst"), .const 1])
          (.var .local (ofString "w"))
          (.var .local (ofString "ll"))
          (dst0 + 1) w0 ll Rl hs2_code
          (by simp [evalHOLExact, evalListHOLExact, hs2_dst, wordOpHOL, wordOp, valueIsWord, valueWord])
          (by simp [evalHOLExact, hs2_w])
          (by simp [evalHOLExact, hs2_ll])
          hfit
          (fun _ => ⟨(locN s "dst", 9), List.mem_singleton.2 rfl,
            by dsimp only; rw [hdst_nat, hdst1_nat]; omega,
            by dsimp only; rw [hdst_nat, hdst1_nat]; omega⟩)
          (by rw [hc_put]; exact hnt_put)
        dsimp only at hput
        rw [hc_put] at hput
        simp only [hc_put] at hres ⊢
        cases rc with
        | some r =>
          dsimp only at hres
          exact False.elim (hput.2 (by simp) hres)
        | none =>
          dsimp only at hres ⊢
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
          exact (((heff_s_mid.trans heff_hdr).trans heff_put).with_locals_clock _ _).with_locals_clock _ _
      · rw [hsb] at hse; dsimp only at hse; subst hse
        exact False.elim (not_resumes_error hres)

end InitECandidate.Solver.Wave8GuestInv.M11
