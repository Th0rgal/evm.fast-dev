import InitECandidate.Solver.Wave8GuestInv.Deliveries.M12.StepLemmas

/-! `wk_st_le64`: relational world step with output region `(locN s "p", 8)` for
`st_le64` (`Guest/SoftwareAst.lean:571`, `guestAst[26]`).

Checked against frozen spec revision 9 (`8a79d9f28`, tag `wave8-spec-frozen-r9`).
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false

namespace InitECandidate.Solver.Wave8Contracts.M12

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

theorem lookup_st_le32 :
    originalRuntimeCode.lookup (ofString "st_le32") =
      some ([(ofString "p", .one), (ofString "v", .one)],
        sourceFnBody Guest.Software.guestFn_st_le32, .one) :=
  lookup_of_guestAst_getElem 25 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_st_le32) rfl

theorem lookup_st_le64 :
    originalRuntimeCode.lookup (ofString "st_le64") =
      some ([(ofString "p", .one), (ofString "v", .one)],
        sourceFnBody Guest.Software.guestFn_st_le64, .one) :=
  lookup_of_guestAst_getElem 26 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_st_le64) rfl

private theorem not_resumes_error : ¬ Resumes (some (.error : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

private theorem byteAlign_lt_heapEnd {s_ma : BitVec 64 → Prop} (hma : s_ma = ordinaryDomain)
    (addr : BitVec 64) (hdom : s_ma (panByteAlignHOL addr)) :
    sourceBase ≤ (panByteAlignHOL addr).toNat ∧ addr.toNat < heapEnd := by
  rw [hma, ordinaryDomain_iff] at hdom
  have hal := panByteAlign_toNat64 addr
  rw [sourceBase_val, heapEnd_val]
  omega

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

private theorem storeByte_addr_lt_heapEnd {F : Type}
    (t : PanSemStateFiniteExact 64 F) (dst val : ExpHOL 64) (addr : BitVec 64)
    (hma : t.memaddrs = ordinaryDomain)
    (hdst : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) dst =
      some (.val (.word addr)))
    (hnone : (evaluateHOLFiniteState t (.storeByte dst val)).1 = none) :
    addr.toNat < heapEnd := by
  rw [evaluateHOLFiniteState_storeByte] at hnone
  rw [hdst] at hnone
  dsimp only at hnone
  split at hnone
  · split at hnone
    · rename_i m' hst
      unfold panMemStoreByteWord8HOL at hst
      dsimp only at hst
      cases hm : t.memory (panByteAlignHOL addr) with
      | word cell =>
        by_cases hdom : t.memaddrs (panByteAlignHOL addr)
        · exact (byteAlign_lt_heapEnd hma addr hdom).2
        · simp [hm, hdom] at hst
    · simp at hnone
  · simp at hnone

private theorem eval_st_le32_body {F : Type}
    (s : PanSemStateFiniteExact 64 F) (p0 v0 : BitVec 64) (Rl : List Ivl)
    (hma : s.memaddrs = ordinaryDomain)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word p0)))
    (_hv : s.locals.lookup (ofString "v") = some (.val (.word v0)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ p0.toNat ∧ p0.toNat + 4 ≤ ivl.1 + ivl.2) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_st_le32)
    (∃ post0, out = (some (.returned (.val (.word 0))), post0) ∧
        ByteRegionEffect s post0 Rl ∧ p0.toNat < heapEnd) ∨
      out = (some .error, out.2) := by
  dsimp only
  have hb : sourceFnBody Guest.Software.guestFn_st_le32 =
      .seq (.storeByte (.var .local (ofString "p")) (.var .local (ofString "v")))
        (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 1])
                (.shift .lsr (.var .local (ofString "v")) (.const 8)))
          (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 2])
                  (.shift .lsr (.var .local (ofString "v")) (.const 16)))
            (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 3])
                    (.shift .lsr (.var .local (ofString "v")) (.const 24)))
              (.return (.const 0))))) := rfl
  rw [hb]
  obtain ⟨ivl, hivl, hlo, hhi⟩ := hin_ivl
  -- Byte 0
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hsb0 : evaluateHOLFiniteState s
      (.storeByte (.var .local (ofString "p")) (.var .local (ofString "v"))) with ⟨r0, s1⟩
  rcases storeByte_only_none_or_error s (.var .local (ofString "p")) (.var .local (ofString "v")) with hn0 | he0
  · rw [hsb0] at hn0; dsimp only at hn0; subst hn0
    dsimp only
    have hp_lt_he : p0.toNat < heapEnd :=
      storeByte_addr_lt_heapEnd s (.var .local (ofString "p")) (.var .local (ofString "v"))
        p0 hma hp (by rw [hsb0])
    have hp_lt_64 : p0.toNat + 4 < 2 ^ 64 := by
      have hhe := heapEnd_val; omega
    obtain ⟨heff0, hl1⟩ := ByteRegionEffect.of_storeByte hsb0 (Rl := Rl) (fun addr hdst _ => by
      simp only [evalHOLExact, hp, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst
      subst hdst
      exact ⟨ivl, hivl, hlo, by omega⟩)
    have hs1_p : s1.locals.lookup (ofString "p") = some (.val (.word p0)) := by rw [hl1]; exact hp
    -- Byte 1
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hsb1 : evaluateHOLFiniteState s1
        (.storeByte (.op .add [.var .local (ofString "p"), .const 1])
          (.shift .lsr (.var .local (ofString "v")) (.const 8))) with ⟨r1, s2⟩
    rcases storeByte_only_none_or_error s1
        (.op .add [.var .local (ofString "p"), .const 1])
        (.shift .lsr (.var .local (ofString "v")) (.const 8)) with hn1 | he1
    · rw [hsb1] at hn1; dsimp only at hn1; subst hn1
      dsimp only
      obtain ⟨heff1, hl2⟩ := ByteRegionEffect.of_storeByte hsb1 (Rl := Rl) (fun addr hdst _ => by
        have haddr : addr = p0 + 1 := by
          simp only [evalHOLExact, evalListHOLExact, hs1_p, wordOpHOL, wordOp, valueIsWord, valueWord,
            List.all, List.map, Bool.and_self, ↓reduceIte, List.foldr, BitVec.add_zero, Option.map,
            Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst
          simpa [BitVec.add_zero] using hdst.symm
        subst haddr
        have hnat : (p0 + 1).toNat = p0.toNat + 1 := by
          rw [BitVec.toNat_add]; change (p0.toNat + 1) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
        exact ⟨ivl, hivl, by omega, by omega⟩)
      have hs2_p : s2.locals.lookup (ofString "p") = some (.val (.word p0)) := by rw [hl2]; exact hs1_p
      -- Byte 2
      rw [evaluateHOLFiniteState_seq_line780]
      rcases hsb2 : evaluateHOLFiniteState s2
          (.storeByte (.op .add [.var .local (ofString "p"), .const 2])
            (.shift .lsr (.var .local (ofString "v")) (.const 16))) with ⟨r2, s3⟩
      rcases storeByte_only_none_or_error s2
          (.op .add [.var .local (ofString "p"), .const 2])
          (.shift .lsr (.var .local (ofString "v")) (.const 16)) with hn2 | he2
      · rw [hsb2] at hn2; dsimp only at hn2; subst hn2
        dsimp only
        obtain ⟨heff2, hl3⟩ := ByteRegionEffect.of_storeByte hsb2 (Rl := Rl) (fun addr hdst _ => by
          have haddr : addr = p0 + 2 := by
            simp only [evalHOLExact, evalListHOLExact, hs2_p, wordOpHOL, wordOp, valueIsWord, valueWord,
              List.all, List.map, Bool.and_self, ↓reduceIte, List.foldr, BitVec.add_zero, Option.map,
              Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst
            simpa [BitVec.add_zero] using hdst.symm
          subst haddr
          have hnat : (p0 + 2).toNat = p0.toNat + 2 := by
            rw [BitVec.toNat_add]; change (p0.toNat + 2) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
          exact ⟨ivl, hivl, by omega, by omega⟩)
        have hs3_p : s3.locals.lookup (ofString "p") = some (.val (.word p0)) := by rw [hl3]; exact hs2_p
        -- Byte 3
        rw [evaluateHOLFiniteState_seq_line780]
        rcases hsb3 : evaluateHOLFiniteState s3
            (.storeByte (.op .add [.var .local (ofString "p"), .const 3])
              (.shift .lsr (.var .local (ofString "v")) (.const 24))) with ⟨r3, s4⟩
        rcases storeByte_only_none_or_error s3
            (.op .add [.var .local (ofString "p"), .const 3])
            (.shift .lsr (.var .local (ofString "v")) (.const 24)) with hn3 | he3
        · rw [hsb3] at hn3; dsimp only at hn3; subst hn3
          dsimp only
          obtain ⟨heff3, _⟩ := ByteRegionEffect.of_storeByte hsb3 (Rl := Rl) (fun addr hdst _ => by
            have haddr : addr = p0 + 3 := by
              simp only [evalHOLExact, evalListHOLExact, hs3_p, wordOpHOL, wordOp, valueIsWord, valueWord,
                List.all, List.map, Bool.and_self, ↓reduceIte, List.foldr, BitVec.add_zero, Option.map,
                Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst
              simpa [BitVec.add_zero] using hdst.symm
            subst haddr
            have hnat : (p0 + 3).toNat = p0.toNat + 3 := by
              rw [BitVec.toNat_add]; change (p0.toNat + 3) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
            exact ⟨ivl, hivl, by omega, by omega⟩)
          rw [evaluateHOLFiniteState_return]
          have hev0 : @evalHOLExact 64 F _ s4.toExact
              (fun a => Classical.propDecidable (s4.memaddrs a)) (.const 0) = some (.val (.word 0)) := rfl
          have hsz : sizeOfShapeWithContextHOL s4.structs (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) ≤ 32 := by
            simp [shapeOfHOLExact]
          rw [hev0]; dsimp only; rw [if_pos hsz]; dsimp only
          exact Or.inl ⟨_, rfl, (((heff0.trans heff1).trans heff2).trans heff3).with_locals_clock _ _, hp_lt_he⟩
        · rw [hsb3] at he3; dsimp only at he3; subst he3
          exact Or.inr rfl
      · rw [hsb2] at he2; dsimp only at he2; subst he2
        exact Or.inr rfl
    · rw [hsb1] at he1; dsimp only at he1; subst he1
      exact Or.inr rfl
  · rw [hsb0] at he0; dsimp only at he0; subst he0
    exact Or.inr rfl

private theorem eval_call_st_le32 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pExp vExp : ExpHOL 64)
    (p0 v0 : BitVec 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hp : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) pExp =
      some (.val (.word p0)))
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) vExp =
      some (.val (.word v0)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ p0.toNat ∧ p0.toNat + 4 ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "st_le32") [pExp, vExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "st_le32") [pExp, vExp])
    (out.1 = none ∧ ByteRegionEffect s out.2 Rl ∧ out.2.locals = s.locals ∧ p0.toNat < heapEnd) ∨
      out.1 = some .error := by
  dsimp only
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) [pExp, vExp] =
      some [.val (.word p0), .val (.word v0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hp, hv]
  have hlook := pan_two_word_lookup s.code.lookup (ofString "st_le32")
    (ofString "p") (ofString "v")
    (sourceFnBody Guest.Software.guestFn_st_le32) p0 v0
    (by decide)
    (by rw [hcode]; exact lookup_st_le32)
  rw [hargs] at hnt ⊢; dsimp only at hnt ⊢
  rw [hlook] at hnt ⊢; dsimp only at hnt ⊢
  by_cases hclk0 : s.clock = 0
  · rw [if_pos hclk0] at hnt; exact absurd rfl hnt
  · rw [if_neg hclk0] at hnt ⊢
    let cmap : HolFiniteMapExact MlS (ValueHOL 64) :=
      (HolFiniteMapExact.empty.update (ofString "p", ValueHOL.val (.word p0))).update
        (ofString "v", ValueHOL.val (.word v0))
    let entry := callEntryStateHOLFinite s cmap
    have hent_p : entry.locals.lookup (ofString "p") = some (.val (.word p0)) := by
      have hne : ofString "v" ≠ ofString "p" := by decide
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne]
    have hent_v : entry.locals.lookup (ofString "v") = some (.val (.word v0)) := by
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hent_ma : entry.memaddrs = ordinaryDomain := hma
    rcases eval_st_le32_body entry p0 v0 Rl hent_ma hent_p hent_v hin_ivl with
      ⟨post0, hb, heff0, hp_lt⟩ | herr
    · change evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
          (sourceFnBody Guest.Software.guestFn_st_le32) = _ at hb
      rw [hb]
      dsimp only
      have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) .one = true := by
        simp [shapeOfHOLExact, shapeEqHOL]
      rw [if_pos hsh]
      have heff_ent : ByteRegionEffect s entry Rl :=
        ByteRegionEffect.refl s Rl |>.with_locals_clock entry.locals entry.clock
      exact Or.inl ⟨rfl, (heff_ent.trans heff0).with_locals_clock s.locals post0.clock, rfl, hp_lt⟩
    · change evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
          (sourceFnBody Guest.Software.guestFn_st_le32) = _ at herr
      rw [herr]
      exact Or.inr rfl

/-- `st_le64` (AST line 571): relational world step with output region. -/
theorem «wk_st_le64» :
    WorldKeeps WorldOK (fun s => [(locN s "p", 8)])
    []
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "st_le64") := by
  refine ⟨_, _, _, lookup_st_le64, ?_⟩
  intro F s hcode hW _ hnt hres
  suffices heff : ByteRegionEffect s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_st_le64)).2
      ([(locN s "p", 8)] ++ ([] : List Ivl)) by
    exact ByteRegionEffect.to_worldStep (extra := fun _ => []) hW (fun _ h => by simp at h) heff
  simp only [List.append_nil]
  let Rl : List Ivl := [(locN s "p", 8)]
  change ByteRegionEffect s
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_st_le64)).2 Rl
  have hb : sourceFnBody Guest.Software.guestFn_st_le64 =
      .seq
        (.call (some (none, none)) (ofString "st_le32")
          [.var .local (ofString "p"), .var .local (ofString "v")])
        (.seq
          (.call (some (none, none)) (ofString "st_le32")
            [.op .add [.var .local (ofString "p"), .const 4],
             .shift .lsr (.var .local (ofString "v")) (.const 32)])
          (.return (.const 0))) := rfl
  rw [hb] at hnt hres ⊢
  -- Extract `p` and `v` as words (otherwise first `call` evaluates to `some .error`):
  have hpv_ex : ∃ p0 v0 : BitVec 64,
      s.locals.lookup (ofString "p") = some (.val (.word p0)) ∧
      s.locals.lookup (ofString "v") = some (.val (.word v0)) := by
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hres
    have hcl : s.code.lookup (ofString "st_le32") =
        some ([(ofString "p", .one), (ofString "v", .one)],
          sourceFnBody Guest.Software.guestFn_st_le32, .one) := by
      rw [hcode]; exact lookup_st_le32
    have hbad : ∀ (vp vv : ValueHOL 64),
        (shapeEqHOL .one (shapeOfHOLExact vp) = false ∨
         shapeEqHOL .one (shapeOfHOLExact vv) = false) →
        PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup (ofString "st_le32") [vp, vv] = none := by
      intro vp vv hsh
      have hraw : lookupCodeHOLExact s.code.lookup (ofString "st_le32") [vp, vv] = none := by
        rcases hsh with h1 | h2
        · simp [lookupCodeHOLExact, hcl, h1]
        · simp [lookupCodeHOLExact, hcl, h2]
      unfold PanSemStateFiniteExact.lookupCodeHOLFinite
      split
      · rfl
      · rename_i fb fl fs hfound
        rw [hraw] at hfound; cases hfound
    rcases hp : s.locals.lookup (ofString "p") with _ | pv
    · simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp] at hres
      exact False.elim (not_resumes_error hres)
    · rcases pv with ⟨⟨p0⟩⟩ | _ | _
      · rcases hv : s.locals.lookup (ofString "v") with _ | vv
        · simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp, hv] at hres
          exact False.elim (not_resumes_error hres)
        · rcases vv with ⟨⟨v0⟩⟩ | fs | ⟨nm, fs⟩
          · exact ⟨p0, v0, rfl, rfl⟩
          · have hn := hbad (.val (.word p0)) (.rStruct fs) (Or.inr (by simp [shapeOfHOLExact, shapeEqHOL]))
            simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp, hv, hn] at hres
            exact False.elim (not_resumes_error hres)
          · have hn := hbad (.val (.word p0)) (.nStruct nm fs) (Or.inr (by simp [shapeOfHOLExact, shapeEqHOL]))
            simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp, hv, hn] at hres
            exact False.elim (not_resumes_error hres)
      · rename_i fs
        rcases hv : s.locals.lookup (ofString "v") with _ | vv
        · simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp, hv] at hres
          exact False.elim (not_resumes_error hres)
        · have hn := hbad (.rStruct fs) vv (Or.inl (by simp [shapeOfHOLExact, shapeEqHOL]))
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp, hv, hn] at hres
          exact False.elim (not_resumes_error hres)
      · rename_i nm fs
        rcases hv : s.locals.lookup (ofString "v") with _ | vv
        · simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp, hv] at hres
          exact False.elim (not_resumes_error hres)
        · have hn := hbad (.nStruct nm fs) vv (Or.inl (by simp [shapeOfHOLExact, shapeEqHOL]))
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp, hv, hn] at hres
          exact False.elim (not_resumes_error hres)
  obtain ⟨p0, v0, hp0, hv0⟩ := hpv_ex
  have hp_nat : locN s "p" = p0.toNat := by simp [locN, hp0]
  -- First call: `st_le32(p, v)`
  rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
  rcases hc1 : evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "st_le32")
        [.var .local (ofString "p"), .var .local (ofString "v")]) with ⟨r1, s1⟩
  have hnt1 : r1 ≠ some .timeOut := by
    rintro rfl; rw [hc1] at hnt; exact hnt rfl
  have hcall1 := eval_call_st_le32 s
    (.var .local (ofString "p")) (.var .local (ofString "v"))
    p0 v0 Rl hcode hW.1.1.memaddrs
    (by simp [evalHOLExact, hp0])
    (by simp [evalHOLExact, hv0])
    ⟨(locN s "p", 8), List.mem_singleton.2 rfl, by rw [hp_nat], by rw [hp_nat]; omega⟩
    (by rw [hc1]; exact hnt1)
  dsimp only at hcall1
  rw [hc1] at hcall1
  simp only [hc1] at hnt hres ⊢
  rcases hcall1 with ⟨rfl, heff1, hs1_loc, hp_lt_he⟩ | rfl
  · dsimp only at hnt hres ⊢
    -- Second call: `st_le32(p + 4, v >>> 32)`
    have hs1_code : s1.code = originalRuntimeCode := heff1.code.trans hcode
    have hs1_ma : s1.memaddrs = ordinaryDomain := heff1.memaddrs.trans hW.1.1.memaddrs
    have hs1_p : s1.locals.lookup (ofString "p") = some (.val (.word p0)) := by rw [hs1_loc]; exact hp0
    have hs1_v : s1.locals.lookup (ofString "v") = some (.val (.word v0)) := by rw [hs1_loc]; exact hv0
    have hp4_nat : (p0 + 4).toNat = p0.toNat + 4 := by
      have hhe := heapEnd_val
      rw [BitVec.toNat_add]
      change (p0.toNat + 4) % 2 ^ 64 = _
      exact Nat.mod_eq_of_lt (by omega)
    rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
    rcases hc2 : evaluateHOLFiniteState s1
        (.call (some (none, none)) (ofString "st_le32")
          [.op .add [.var .local (ofString "p"), .const 4],
           .shift .lsr (.var .local (ofString "v")) (.const 32)]) with ⟨r2, s2⟩
    have hnt2 : r2 ≠ some .timeOut := by
      rintro rfl; rw [hc2] at hnt; exact hnt rfl
    have hcall2 := eval_call_st_le32 s1
      (.op .add [.var .local (ofString "p"), .const 4])
      (.shift .lsr (.var .local (ofString "v")) (.const 32))
      (p0 + 4) (v0 >>> (32 : BitVec 64).toNat) Rl hs1_code hs1_ma
      (by simp [evalHOLExact, evalListHOLExact, hs1_p, wordOpHOL, wordOp, valueIsWord, valueWord])
      (by simp [evalHOLExact, hs1_v, wordShiftHOL])
      ⟨(locN s "p", 8), List.mem_singleton.2 rfl,
        by dsimp only; rw [hp_nat, hp4_nat]; omega,
        by dsimp only; rw [hp_nat, hp4_nat]⟩
      (by rw [hc2]; exact hnt2)
    dsimp only at hcall2
    rw [hc2] at hcall2
    simp only [hc2] at hres ⊢
    rcases hcall2 with ⟨rfl, heff2, _, _⟩ | rfl
    · dsimp only at hres ⊢
      rw [evaluateHOLFiniteState_return]
      have hev0 : @evalHOLExact 64 F _ s2.toExact
          (fun a => Classical.propDecidable (s2.memaddrs a)) (.const 0) = some (.val (.word 0)) := rfl
      have hsz : sizeOfShapeWithContextHOL s2.structs (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) ≤ 32 := by
        simp [shapeOfHOLExact]
      rw [hev0]; dsimp only; rw [if_pos hsz]; dsimp only
      exact (heff1.trans heff2).with_locals_clock _ _
    · exact False.elim (not_resumes_error hres)
  · exact False.elim (not_resumes_error hres)

end InitECandidate.Solver.Wave8Contracts.M12
