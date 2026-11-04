import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.Batch1

/-!
# R16h LogsBloom: `wk_logs_bloom`

Zero-sorry proof of `wk_logs_bloom`, matching the frozen statement in
`ContractParts/C08.lean` verbatim.
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## Section 1: Lookups and bit-index arithmetic for `add_to_bloom` -/

theorem lookup_add_to_bloom :
    originalRuntimeCode.lookup (ofString "add_to_bloom") =
      some ([(ofString "bloom", .one), (ofString "entry", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_add_to_bloom, .one) :=
  lookup_of_guestAst_getElem 831 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_add_to_bloom) rfl

theorem lookup_logs_bloom :
    originalRuntimeCode.lookup (ofString "logs_bloom") =
      some ([(ofString "logs", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_logs_bloom, .one) :=
  lookup_of_guestAst_getElem 832 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_logs_bloom) rfl

private theorem bloom_byte_index_lt_256 (x : BitVec 64) :
    ((2047#64 - (x &&& 2047#64)) >>> 3).toNat < 256 := by
  have hx : (x &&& 2047#64).toNat ≤ 2047 := by
    rw [BitVec.toNat_and]
    exact Nat.and_le_right
  have hsub : (2047#64 - (x &&& 2047#64)).toNat = 2047 - (x &&& 2047#64).toNat := by
    apply BitVec.toNat_sub_of_le
    rw [BitVec.le_def]
    exact hx
  have hr : ((2047#64 - (x &&& 2047#64)) >>> (3 : Nat)).toNat =
      (2047#64 - (x &&& 2047#64)).toNat >>> 3 := BitVec.toNat_ushiftRight _ 3
  change ((2047#64 - (x &&& 2047#64)) >>> (3 : Nat)).toNat < 256
  rw [hr, hsub]
  omega

private theorem bloom_add_byte_index_in_ivl
    (bloom0 byteIdx : BitVec 64)
    (hlo : sourceBase ≤ bloom0.toNat)
    (hhi : bloom0.toNat + 256 ≤ heapEnd)
    (hidx : byteIdx.toNat < 256) :
    InIvl (bloom0 + byteIdx).toNat (bloom0.toNat, 256) := by
  have hhe : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  have hadd : (bloom0 + byteIdx).toNat = bloom0.toNat + byteIdx.toNat :=
    BitVec.toNat_add_of_lt (by omega)
  exact ⟨by omega, by omega⟩

private def addToBloomLoopBody : ProgHOL 64 :=
  .dec (ofString "bit") .one
    (.op .and
      [.op .or
          [.shift .lsl
              (.loadByte (.op .add [ExpHOL.var VarKind.local (ofString "h"),
                ExpHOL.var VarKind.local (ofString "idx")]))
              (.const 8),
            .loadByte (.op .add [ExpHOL.var VarKind.local (ofString "h"),
              ExpHOL.var VarKind.local (ofString "idx"), .const 1])],
        .const 2047])
    (.dec (ofString "bit_index") .one
      (.op .sub [.const 2047, ExpHOL.var VarKind.local (ofString "bit")])
      (.dec (ofString "byte_index") .one
        (.shift .lsr (ExpHOL.var VarKind.local (ofString "bit_index")) (.const 3))
        (.dec (ofString "bv") .one
          (.shift .lsl (.const 1)
            (.op .sub [.const 7,
              .op .and [ExpHOL.var VarKind.local (ofString "bit_index"), .const 7]]))
          (.seq
            (.storeByte
              (.op .add [ExpHOL.var VarKind.local (ofString "bloom"),
                ExpHOL.var VarKind.local (ofString "byte_index")])
              (.op .or
                [.loadByte (.op .add [ExpHOL.var VarKind.local (ofString "bloom"),
                    ExpHOL.var VarKind.local (ofString "byte_index")]),
                  ExpHOL.var VarKind.local (ofString "bv")]))
            (.assign VarKind.local (ofString "idx")
              (.op .add [ExpHOL.var VarKind.local (ofString "idx"), .const 2]))))))

private def addToBloomWhile : ProgHOL 64 :=
  .while (.cmp .less (ExpHOL.var VarKind.local (ofString "idx")) (.const 6)) addToBloomLoopBody

private theorem addToBloomLoopBody_step {F : Type}
    (s : PanSemStateFiniteExact 64 F) (bloom0 : BitVec 64) (Rl : List Ivl) (gw : List String)
    (hAR : ArenaReady s)
    (hbloom : s.locals.lookup (ofString "bloom") = some (.val (.word bloom0)))
    (hdom : sourceBase ≤ bloom0.toNat ∧ bloom0.toNat + 256 ≤ heapEnd)
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ bloom0.toNat ∧ bloom0.toNat + 256 ≤ ivl.1 + ivl.2) :
    let out := evaluateHOLFiniteState s addToBloomLoopBody
    HeapByteEff s out.2 Rl gw ∧
    out.1 ≠ some .continue ∧
    out.1 ≠ some .break ∧
    (∀ r, out.1 = some r → ¬ Resumes (some r)) ∧
    (out.1 = none →
      out.2.locals.lookup (ofString "bloom") = some (.val (.word bloom0)) ∧
      out.2.locals.lookup (ofString "mark") = s.locals.lookup (ofString "mark")) := by
  intro out; dsimp only [out, addToBloomLoopBody]
  rw [evaluateHOLFiniteState_dec_total]; dsimp only
  let orExp : ExpHOL 64 :=
    .op .or
      [.shift .lsl
          (.loadByte (.op .add [ExpHOL.var VarKind.local (ofString "h"),
            ExpHOL.var VarKind.local (ofString "idx")]))
          (.const 8),
        .loadByte (.op .add [ExpHOL.var VarKind.local (ofString "h"),
          ExpHOL.var VarKind.local (ofString "idx"), .const 1])]
  rcases hv_bit : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .and [orExp, .const 2047]) with _ | vbit
  · exact ⟨HeapByteEff.refl hAR Rl gw, by simp, by simp,
      fun r hr => by injection hr with e; subst e; exact not_resumes_error, by simp⟩
  · have hbit_word : ∃ rawW : BitVec 64, vbit = .val (.word (rawW &&& 2047#64)) := by
      rcases ho : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) orExp with _ | vo
      · simp [evalHOLExact, evalListHOLExact, ho] at hv_bit
      · rcases vo with ⟨⟨ow⟩⟩ | _ | _ <;>
          simp [evalHOLExact, evalListHOLExact, ho, valueIsWord, valueWord, wordOpHOL, wordOp] at hv_bit
        exact ⟨ow, hv_bit.symm⟩
    obtain ⟨rawW, rfl⟩ := hbit_word
    dsimp only
    let bitW : BitVec 64 := rawW &&& 2047#64
    have hsh1 : shapeEqHOL .one (shapeOfHOLExact (.val (.word bitW) : ValueHOL 64)) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hsh1]; dsimp only
    set s1 := setVarHOLFinite (ofString "bit") (.val (.word bitW)) s
    have hs1_AR : ArenaReady s1 := localsFree_arenaReady s s1.locals s1.clock hAR
    have hs1_bit : s1.locals.lookup (ofString "bit") = some (.val (.word bitW)) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs1_bloom : s1.locals.lookup (ofString "bloom") = some (.val (.word bloom0)) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hbloom,
        show ofString "bit" ≠ ofString "bloom" by decide]
    -- Second `.dec`: `bit_index := 2047 - bit`
    let bitIdxW : BitVec 64 := 2047#64 - bitW
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    have hev_bi : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        (.op .sub [.const 2047, ExpHOL.var VarKind.local (ofString "bit")]) =
        some (.val (.word bitIdxW)) := by
      simp [evalHOLExact, evalListHOLExact, hs1_bit, wordOpHOL, wordOp, valueIsWord, valueWord, bitIdxW]
    rw [hev_bi]; dsimp only
    have hsh2 : shapeEqHOL .one (shapeOfHOLExact (.val (.word bitIdxW) : ValueHOL 64)) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hsh2]; dsimp only
    set s2 := setVarHOLFinite (ofString "bit_index") (.val (.word bitIdxW)) s1
    have hs2_bi : s2.locals.lookup (ofString "bit_index") = some (.val (.word bitIdxW)) := by
      simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs2_bloom : s2.locals.lookup (ofString "bloom") = some (.val (.word bloom0)) := by
      simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_bloom,
        show ofString "bit_index" ≠ ofString "bloom" by decide]
    -- Third `.dec`: `byte_index := bit_index >>> 3`
    let byteIdxW : BitVec 64 := bitIdxW >>> 3
    have hbyte_lt : byteIdxW.toNat < 256 := bloom_byte_index_lt_256 rawW
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    have hev_byi : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
        (.shift .lsr (ExpHOL.var VarKind.local (ofString "bit_index")) (.const 3)) =
        some (.val (.word byteIdxW)) := by
      simp [evalHOLExact, hs2_bi, wordShiftHOL, byteIdxW]
    rw [hev_byi]; dsimp only
    have hsh3 : shapeEqHOL .one (shapeOfHOLExact (.val (.word byteIdxW) : ValueHOL 64)) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hsh3]; dsimp only
    set s3 := setVarHOLFinite (ofString "byte_index") (.val (.word byteIdxW)) s2
    have hs3_bi : s3.locals.lookup (ofString "bit_index") = some (.val (.word bitIdxW)) := by
      simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_bi,
        show ofString "byte_index" ≠ ofString "bit_index" by decide]
    have hs3_byi : s3.locals.lookup (ofString "byte_index") = some (.val (.word byteIdxW)) := by
      simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs3_bloom : s3.locals.lookup (ofString "bloom") = some (.val (.word bloom0)) := by
      simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_bloom,
        show ofString "byte_index" ≠ ofString "bloom" by decide]
    -- Fourth `.dec`: `bv := 1 <<< (7 - (bit_index &&& 7))`
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    rcases hev_bv : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
        (.shift .lsl (.const 1)
          (.op .sub [.const 7,
            .op .and [ExpHOL.var VarKind.local (ofString "bit_index"), .const 7]])) with _ | vbv
    · exact ⟨HeapByteEff.refl hAR Rl gw |>.locals_clock _ s.clock,
        by simp, by simp, fun r hr => by injection hr with e; subst e; exact not_resumes_error, by simp⟩
    · dsimp only
      split
      · set s4 := setVarHOLFinite (ofString "bv") vbv s3
        have hs4_AR : ArenaReady s4 := localsFree_arenaReady s s4.locals s4.clock hAR
        have hs4_G : GuestInv s4 := hs4_AR.1
        have hs4_byi : s4.locals.lookup (ofString "byte_index") = some (.val (.word byteIdxW)) := by
          simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_byi,
            show ofString "bv" ≠ ofString "byte_index" by decide]
        have hs4_bloom : s4.locals.lookup (ofString "bloom") = some (.val (.word bloom0)) := by
          simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_bloom,
            show ofString "bv" ≠ ofString "bloom" by decide]
        have hs4_mark : s4.locals.lookup (ofString "mark") = s.locals.lookup (ofString "mark") := by
          simp [s4, s3, s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "bv" ≠ ofString "mark" by decide,
            show ofString "byte_index" ≠ ofString "mark" by decide,
            show ofString "bit_index" ≠ ofString "mark" by decide,
            show ofString "bit" ≠ ofString "mark" by decide]
        -- `.seq (.storeByte ...) (.assign "idx" ...)`
        rw [evaluateHOLFiniteState_seq_line780]
        have hsb := (R13Shards.Keccak256.byteEff_storeByte (Rl := Rl) hs4_G
          (.op .add [ExpHOL.var VarKind.local (ofString "bloom"),
            ExpHOL.var VarKind.local (ofString "byte_index")])
          (.op .or
            [.loadByte (.op .add [ExpHOL.var VarKind.local (ofString "bloom"),
                ExpHOL.var VarKind.local (ofString "byte_index")]),
              ExpHOL.var VarKind.local (ofString "bv")])
          (fun x hx _ => by
            simp [evalHOLExact, evalListHOLExact, hs4_bloom, hs4_byi, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
            subst hx
            obtain ⟨ivl, hivl, hi1, hi2⟩ := hin_ivl
            obtain ⟨hb1, hb2⟩ := bloom_add_byte_index_in_ivl bloom0 byteIdxW hdom.1 hdom.2 hbyte_lt
            exact ⟨ivl, hivl, by omega, by omega⟩)).1
        rcases hr_sb : evaluateHOLFiniteState s4
          (.storeByte
            (.op .add [ExpHOL.var VarKind.local (ofString "bloom"),
              ExpHOL.var VarKind.local (ofString "byte_index")])
            (.op .or
              [.loadByte (.op .add [ExpHOL.var VarKind.local (ofString "bloom"),
                  ExpHOL.var VarKind.local (ofString "byte_index")]),
                ExpHOL.var VarKind.local (ofString "bv")])) with ⟨rsb, s5⟩
        rw [hr_sb] at hsb
        have heff_s_s5 : HeapByteEff s s5 Rl gw :=
          (HeapByteEff.refl hAR Rl gw |>.locals_clock s4.locals s4.clock).trans
            (HeapByteEff.of_byteEff hs4_AR hsb)
        have hsb_ctrl : (rsb = none ∧ s5.locals = s4.locals) ∨ rsb = some .error := by
          rw [evaluateHOLFiniteState_storeByte] at hr_sb
          split at hr_sb
          · split at hr_sb
            · split at hr_sb
              · injection hr_sb with e1 e2; exact Or.inl ⟨e1.symm, by rw [← e2]⟩
              · injection hr_sb with e1 _; exact Or.inr e1.symm
            · injection hr_sb with e1 _; exact Or.inr e1.symm
          · injection hr_sb with e1 _; exact Or.inr e1.symm
        rcases hsb_ctrl with ⟨rfl, hs5_loc⟩ | rfl
        · dsimp only
          rw [evaluateHOLFiniteState_assign]
          split
          · exact ⟨heff_s_s5.locals_clock _ s5.clock,
              by simp, by simp, fun r hr => by injection hr with e; subst e; exact not_resumes_error, by simp⟩
          · split
            · dsimp only [setKvarHOLFinite, setVarHOLFinite]
              refine ⟨heff_s_s5.locals_clock _ s5.clock,
                by simp, by simp, fun _ hr => by simp at hr, fun _ => ⟨?_, ?_⟩⟩
              · rw [resVarEq_lookup_ne _ _ _ _ (by decide),
                    resVarEq_lookup_ne _ _ _ _ (by decide),
                    resVarEq_lookup_ne _ _ _ _ (by decide),
                    resVarEq_lookup_ne _ _ _ _ (by decide), hs5_loc]
                simp [HolFiniteMapExact.lookup_update, FUPDATE, hs4_bloom,
                  show ofString "idx" ≠ ofString "bloom" by decide]
              · rw [resVarEq_lookup_ne _ _ _ _ (by decide),
                    resVarEq_lookup_ne _ _ _ _ (by decide),
                    resVarEq_lookup_ne _ _ _ _ (by decide),
                    resVarEq_lookup_ne _ _ _ _ (by decide), hs5_loc]
                simp [HolFiniteMapExact.lookup_update, FUPDATE, hs4_mark,
                  show ofString "idx" ≠ ofString "mark" by decide]
            · exact ⟨heff_s_s5.locals_clock _ s5.clock,
                by simp, by simp, fun r hr => by injection hr with e; subst e; exact not_resumes_error, by simp⟩
        · dsimp only
          exact ⟨heff_s_s5.locals_clock _ s5.clock,
            by simp, by simp, fun r hr => by injection hr with e; subst e; exact not_resumes_error, by simp⟩
      · exact ⟨HeapByteEff.refl hAR Rl gw |>.locals_clock _ s.clock,
          by simp, by simp, fun r hr => by injection hr with e; subst e; exact not_resumes_error, by simp⟩

private theorem addToBloomWhile_eff {F : Type}
    (clk : Nat) (s : PanSemStateFiniteExact 64 F) (bloom0 : BitVec 64)
    (Rl : List Ivl) (gw : List String)
    (hclk : s.clock ≤ clk)
    (hAR : ArenaReady s)
    (hbloom : s.locals.lookup (ofString "bloom") = some (.val (.word bloom0)))
    (hdom : sourceBase ≤ bloom0.toNat ∧ bloom0.toNat + 256 ≤ heapEnd)
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ bloom0.toNat ∧ bloom0.toNat + 256 ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s addToBloomWhile).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s addToBloomWhile
    HeapByteEff s out.2 Rl gw ∧
    (out.1 ≠ none → ¬ Resumes out.1) ∧
    (out.1 = none → out.2.locals.lookup (ofString "mark") = s.locals.lookup (ofString "mark")) := by
  induction clk generalizing s with
  | zero =>
    dsimp only [addToBloomWhile] at hnt ⊢
    rw [evaluateHOLFiniteState_while_total] at hnt ⊢
    rcases hevc : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .less (ExpHOL.var VarKind.local (ofString "idx")) (.const 6)) with _ | cv
    · simp only [hevc]
      exact ⟨HeapByteEff.refl hAR Rl gw, fun _ => not_resumes_error, by simp⟩
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;>
        try (simp only [hevc]; exact ⟨HeapByteEff.refl hAR Rl gw, fun _ => not_resumes_error, by simp⟩)
      simp only [hevc] at hnt ⊢
      by_cases hnz : cw ≠ 0
      · have hz : s.clock = 0 := by omega
        rw [if_pos hnz, if_pos hz] at hnt
        exact absurd rfl hnt
      · rw [if_neg hnz]
        exact ⟨HeapByteEff.refl hAR Rl gw, fun h => False.elim (h rfl), fun _ => rfl⟩
  | succ k ih =>
    dsimp only [addToBloomWhile] at hnt ⊢
    rw [evaluateHOLFiniteState_while_total] at hnt ⊢
    rcases hevc : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .less (ExpHOL.var VarKind.local (ofString "idx")) (.const 6)) with _ | cv
    · simp only [hevc]
      exact ⟨HeapByteEff.refl hAR Rl gw, fun _ => not_resumes_error, by simp⟩
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;>
        try (simp only [hevc]; exact ⟨HeapByteEff.refl hAR Rl gw, fun _ => not_resumes_error, by simp⟩)
      simp only [hevc] at hnt ⊢
      by_cases hnz : cw ≠ 0
      · rw [if_pos hnz] at hnt ⊢
        by_cases hz : s.clock = 0
        · rw [if_pos hz] at hnt; exact absurd rfl hnt
        · rw [if_neg hz] at hnt ⊢
          rw [fixClockHOLFinite_evaluateState] at hnt ⊢
          let sd := decClockHOLFinite s
          have hsd_AR : ArenaReady sd := localsFree_arenaReady s s.locals (s.clock - 1) hAR
          have hstep := addToBloomLoopBody_step sd bloom0 Rl gw hsd_AR hbloom hdom hin_ivl
          have hcle := evaluateHOLFiniteState_clock_le sd addToBloomLoopBody
          rcases hbr : evaluateHOLFiniteState sd addToBloomLoopBody with ⟨rb, mid⟩
          rw [hbr] at hstep hcle hnt
          dsimp only at hstep hcle hnt ⊢
          have heff1 : HeapByteEff s mid Rl gw :=
            (HeapByteEff.refl hAR Rl gw |>.locals_clock sd.locals sd.clock).trans hstep.1
          cases rb with
          | none =>
            obtain ⟨hm_bloom, hm_mark⟩ := hstep.2.2.2.2 rfl
            have hm_clk : mid.clock ≤ k := by change mid.clock ≤ s.clock - 1 at hcle; omega
            have ih_res := ih mid hm_clk heff1.arena hm_bloom hnt
            exact ⟨heff1.trans ih_res.1, ih_res.2.1, fun hn => (ih_res.2.2 hn).trans hm_mark⟩
          | some r' =>
            cases r' with
            | «continue» => exact absurd rfl hstep.2.1
            | «break» => exact absurd rfl hstep.2.2.1
            | timeOut => exact absurd rfl hnt
            | returned rv => exact ⟨heff1, fun _ => hstep.2.2.2.1 _ rfl, by simp⟩
            | exception e v => exact ⟨heff1, fun _ => hstep.2.2.2.1 _ rfl, by simp⟩
            | error => exact ⟨heff1.locals_clock _ _, fun _ => not_resumes_error, by simp⟩
            | finalFfi f =>
              exact ⟨heff1.locals_clock _ _, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h, by simp⟩
      · rw [if_neg hnz]
        exact ⟨HeapByteEff.refl hAR Rl gw, fun h => False.elim (h rfl), fun _ => rfl⟩

/-! ## Section 2: `eval_call_add_to_bloom` -/

private theorem heapByteEff_of_seq_none {F : Type}
    {s0 s m : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64} {Rl : List Ivl} {gw : List String}
    (ha : evaluateHOLFiniteState s a = (none, m))
    (hb : HeapByteEff s0 (evaluateHOLFiniteState m b).2 Rl gw) :
    HeapByteEff s0 (evaluateHOLFiniteState s (.seq a b)).2 Rl gw := by
  rw [evaluateHOLFiniteState_seq_line780, ha]
  exact hb

private theorem heapByteEff_of_seq_some {F : Type}
    {s0 s m : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64} {r : PanSemResultExact 64}
    {Rl : List Ivl} {gw : List String}
    (ha : evaluateHOLFiniteState s a = (some r, m))
    (hm : HeapByteEff s0 m Rl gw) :
    HeapByteEff s0 (evaluateHOLFiniteState s (.seq a b)).2 Rl gw := by
  rw [evaluateHOLFiniteState_seq_line780, ha]
  exact hm

private theorem heapByteEff_of_eq_resVar {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {p : ProgHOL 64}
    {r' : Option (PanSemResultExact 64)} {q : PanSemStateFiniteExact 64 F}
    {L : HolFiniteMapExact MlS (ValueHOL 64)} {Rl : List Ivl} {gw : List String}
    (heq : evaluateHOLFiniteState s p = (r', { q with locals := L }))
    (hq : HeapByteEff s0 q Rl gw) :
    HeapByteEff s0 (evaluateHOLFiniteState s p).2 Rl gw := by
  rw [heq]
  exact hq.locals_clock L q.clock

private theorem call0_ne_break_continue {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname : MlS) (args : List (ExpHOL 64)) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 ≠ some .break ∧
    (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 ≠ some .continue := by
  rw [evaluateHOLFiniteState_call]
  rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · simp
  · dsimp only
    rcases lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨b, c, r⟩
    · simp
    · dsimp only
      by_cases hclk : s.clock = 0
      · simp [hclk]
      · rw [if_neg hclk]
        rcases evaluateHOLFiniteState (callEntryStateHOLFinite s c) b with ⟨rb, pb⟩
        cases rb with
        | none => simp
        | some rb' =>
          cases rb' <;> dsimp only
          all_goals try (split <;> simp)
          all_goals simp

private theorem call0_any_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname : MlS) (args : List (ExpHOL 64))
    (hnone : (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 = none) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).2.locals = s.locals := by
  rw [evaluateHOLFiniteState_call]
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · rfl
  · dsimp only
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨b, c, r⟩
    · rfl
    · dsimp only
      by_cases hclk : s.clock = 0
      · exfalso
        rw [evaluateHOLFiniteState_call, hargs] at hnone
        simp [hl, hclk] at hnone
      · rw [if_neg hclk]
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s c) b with ⟨rb, pb⟩
        cases rb with
        | none =>
          exfalso; rw [evaluateHOLFiniteState_call, hargs] at hnone
          simp [hl, hclk, hb] at hnone
        | some rb' =>
          cases rb' with
          | returned rv =>
            dsimp only
            split
            · rfl
            · rename_i hbad
              exfalso; rw [evaluateHOLFiniteState_call, hargs] at hnone
              simp [hl, hclk, hb, hbad] at hnone
          | _ =>
            exfalso; rw [evaluateHOLFiniteState_call, hargs] at hnone
            simp [hl, hclk, hb] at hnone

theorem eval_call_add_to_bloom {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (bloomExp entryExp nExp : ExpHOL 64)
    (bloom0 : BitVec 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hgw : "heap_ptr" ∈ gw)
    (hbloom_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) bloomExp =
      some (.val (.word bloom0)))
    (hdom : sourceBase ≤ bloom0.toNat ∧ bloom0.toNat + 256 ≤ heapEnd)
    (hbloom_in : ∃ ivl ∈ Rl, ivl.1 ≤ bloom0.toNat ∧ bloom0.toNat + 256 ≤ ivl.1 + ivl.2)
    (hpad_in : globN s "keccak_pad" ≠ 0 →
      ∃ ivl ∈ Rl, ivl.1 ≤ globN s "keccak_pad" ∧ globN s "keccak_pad" + 136 ≤ ivl.1 + ivl.2)
    (hst_in : globN s "keccak_st" ≠ 0 →
      ∃ ivl ∈ Rl, ivl.1 ≤ globN s "keccak_st" ∧ globN s "keccak_st" + 200 ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "add_to_bloom") [bloomExp, entryExp, nExp])).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "add_to_bloom") [bloomExp, entryExp, nExp])).1 = none ∨
      Resumes (evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "add_to_bloom") [bloomExp, entryExp, nExp])).1) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "add_to_bloom") [bloomExp, entryExp, nExp])
    HeapByteEff s out.2 Rl gw ∧
    (out.1 = none → out.2.locals = s.locals) := by
  intro out; dsimp only [out]
  have hnone_loc : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "add_to_bloom") [bloomExp, entryExp, nExp])).1 = none →
      (evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "add_to_bloom") [bloomExp, entryExp, nExp])).2.locals = s.locals :=
    call0_any_locals s (ofString "add_to_bloom") [bloomExp, entryExp, nExp]
  refine ⟨?_, hnone_loc⟩
  rw [evaluateHOLFiniteState_call] at hnt hor ⊢
  rcases ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [bloomExp, entryExp, nExp] with _ | vs
  · exact HeapByteEff.refl hAR Rl gw
  · simp only [ha] at hnt hor ⊢
    rcases hlk : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup (ofString "add_to_bloom") vs with _ | ⟨b, cmap, rs⟩
    · exact HeapByteEff.refl hAR Rl gw
    · simp only [hlk] at hnt hor ⊢
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "add_to_bloom")
        [(ofString "bloom", .one), (ofString "entry", .one), (ofString "n", .one)]
        (sourceFnBody Guest.Software.guestFn_add_to_bloom) b .one rs vs cmap
        (by rw [hcode]; exact lookup_add_to_bloom) hlk
      have hrs := lookupCodeHOLFinite_installed_return s (ofString "add_to_bloom")
        [(ofString "bloom", .one), (ofString "entry", .one), (ofString "n", .one)]
        (sourceFnBody Guest.Software.guestFn_add_to_bloom) b .one rs vs cmap
        (by rw [hcode]; exact lookup_add_to_bloom) hlk
      subst hsame; subst hrs
      have hthree := R13Shards.Keccak256.lookupCode_three_words (by decide) (by decide) (by decide)
        lookup_add_to_bloom (by rw [← hcode]; exact hlk)
      obtain ⟨bw, entry0, n0, rfl, hcmap_b, hcmap_e, hcmap_n⟩ := hthree
      have hbw_eq : bw = bloom0 := by
        simp only [evalListHOLFinite, evalListHOLExact, hbloom_ev] at ha
        rcases hev_e : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) entryExp with _ | ve <;>
          simp [hev_e] at ha
        rcases hev_n : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp with _ | vn <;>
          simp [hev_n] at ha
        exact ha.left.symm
      subst bw
      by_cases hcz : s.clock = 0
      · simp [hcz] at hnt
      · simp only [hcz, ↓reduceIte] at hnt hor ⊢
        set ent := callEntryStateHOLFinite s cmap
        have hent_AR : ArenaReady ent := ⟨guestInv_callEntry s cmap hAR.1, hAR.2⟩
        have hent_code : ent.code = originalRuntimeCode := hcode
        -- Show `HeapByteEff ent (evaluateHOLFiniteState ent body).2 Rl gw`, then lift to `s`:
        suffices hbody : HeapByteEff ent
            (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_add_to_bloom)).2 Rl gw by
          have heff0 : HeapByteEff s ent Rl gw :=
            (HeapByteEff.refl hAR Rl gw).locals_clock ent.locals ent.clock
          have heff_post : HeapByteEff s
              (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_add_to_bloom)).2 Rl gw :=
            heff0.trans hbody
          rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_add_to_bloom) with ⟨rb, sb⟩
          rw [hrun] at heff_post
          dsimp only at heff_post ⊢
          cases rb with
          | none => exact heff_post.locals_clock _ _
          | some rb' =>
            cases rb' with
            | returned rv =>
              dsimp only
              split
              · exact heff_post.locals_clock _ _
              · exact heff_post.locals_clock _ _
            | _ => exact heff_post.locals_clock _ _
        -- Extract `hnt_ent` and `hres_ent`:
        have hnt_ent : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_add_to_bloom)).1 ≠ some .timeOut := by
          rcases hrun_ent : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_add_to_bloom) with ⟨rb_e, sb_e⟩
          rintro rfl; rw [hrun_ent] at hnt; exact hnt rfl
        have hres_ent : Resumes (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_add_to_bloom)).1 := by
          rcases hrun_ent : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_add_to_bloom) with ⟨rb_e, sb_e⟩
          rw [hrun_ent] at hor; dsimp only
          cases rb_e with
          | none => exfalso; rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
          | some rb' =>
            cases rb' with
            | returned rv => exact Or.inl ⟨rv, rfl⟩
            | exception eid ev =>
              rcases hor with h | ⟨_, h⟩ | ⟨e', v', h, hne_t⟩
              · simp at h
              · simp at h
              · simp at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨eid, ev, rfl, hne_t⟩
            | «break» | «continue» | error | timeOut | finalFfi _ =>
              exfalso; rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
        -- Unfold `sourceFnBody Guest.Software.guestFn_add_to_bloom`:
        have hb_atb : sourceFnBody Guest.Software.guestFn_add_to_bloom =
            .decCall (ofString "mark") .one (ofString "heap_mark") []
              (.decCall (ofString "h") .one (ofString "alloc") [.const 32]
                (.seq (.call (some (none, none)) (ofString "keccak256")
                    [ExpHOL.var VarKind.local (ofString "entry"),
                     ExpHOL.var VarKind.local (ofString "n"),
                     ExpHOL.var VarKind.local (ofString "h")])
                  (.dec (ofString "idx") .one (.const 0)
                    (.seq addToBloomWhile
                      (.seq (.call (some (none, none)) (ofString "heap_release")
                          [ExpHOL.var VarKind.local (ofString "mark")])
                        (.return (.const 0))))))) := rfl
        rw [hb_atb] at hnt_ent hres_ent ⊢
        -- Step 1: `mark := heap_mark()`
        obtain ⟨mark, s1, _, hmark_nat, hs1_g, _, hs1_loc, heff01, hnt1, heq1⟩ :=
          eval_decCall_heap_mark ent "mark" _ Rl gw hent_code hent_AR hnt_ent
        rw [heq1] at hres_ent; dsimp only at hres_ent
        refine heapByteEff_of_eq_resVar heq1 ?_
        have hs1_mark : s1.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
          rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        have hs1_bloom : s1.locals.lookup (ofString "bloom") = some (.val (.word bloom0)) := by
          rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "mark" ≠ ofString "bloom" by decide]
          exact hcmap_b
        have hs1_entry : s1.locals.lookup (ofString "entry") = some (.val (.word entry0)) := by
          rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "mark" ≠ ofString "entry" by decide]
          exact hcmap_e
        have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word n0)) := by
          rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "mark" ≠ ofString "n" by decide]
          exact hcmap_n
        -- Step 2: `h := alloc(32)`
        obtain ⟨hw, n32, q, s2, h32_ev, hhw_hp, _, hq_nat, hpq, hq_hi, _, hs2_hp, hs2_g, _, hs2_loc,
            heff12, hnt2, hres2, heq2⟩ :=
          eval_decCall_alloc_resumes s1 "h" (.const 32) _ Rl gw
            heff01.arena.1.code heff01.arena hgw hnt1 hres_ent
        have hn32 : n32 = 32 := by simp [evalHOLExact] at h32_ev; exact h32_ev.symm
        subst hn32
        have h32_val : (32 : BitVec 64).toNat = 32 := rfl
        rw [h32_val] at hpq hq_nat
        have hs1_hp_eq : globN s1 "heap_ptr" = globN ent "heap_ptr" := by simp [globN, hs1_g]
        have hhw_ge : globN ent "heap_ptr" ≤ hw.toNat := by omega
        have hhw_hi : hw.toNat + 32 ≤ heapLimit := by omega
        refine heapByteEff_of_eq_resVar heq2 ?_
        let Rall : List Ivl := (hw.toNat, 32) :: Rl
        have hs2_h : s2.locals.lookup (ofString "h") = some (.val (.word hw)) := by
          rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        have hs2_mark : s2.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
          rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_mark,
            show ofString "h" ≠ ofString "mark" by decide]
        have hs2_bloom : s2.locals.lookup (ofString "bloom") = some (.val (.word bloom0)) := by
          rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_bloom,
            show ofString "h" ≠ ofString "bloom" by decide]
        have hs2_entry : s2.locals.lookup (ofString "entry") = some (.val (.word entry0)) := by
          rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_entry,
            show ofString "h" ≠ ofString "entry" by decide]
        have hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word n0)) := by
          rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_n,
            show ofString "h" ≠ ofString "n" by decide]
        have heff_ent_s2 : HeapByteEff ent s2 Rall gw :=
          (heff01.mono (fun i hi _ => Or.inl ⟨i, List.mem_cons_of_mem _ hi, le_rfl, le_rfl⟩) (fun _ hg => hg)).trans
            (heff12.mono (fun i hi _ => Or.inl ⟨i, List.mem_cons_of_mem _ hi, le_rfl, le_rfl⟩) (fun _ hg => hg))
        have hmono_Rall : ∀ {post : PanSemStateFiniteExact 64 F},
            HeapByteEff ent post Rall gw → HeapByteEff ent post Rl gw := fun h =>
          h.mono
            (fun i hi _ => by
              simp only [Rall, List.mem_cons] at hi
              rcases hi with rfl | hi_rl
              · exact Or.inr (Or.inr ⟨hhw_ge, hhw_hi⟩)
              · exact Or.inl ⟨i, hi_rl, le_rfl, le_rfl⟩)
            (fun _ hg => hg)
        -- Step 3: `keccak256(entry, n, h)`
        have hkpad_eq : globN s2 "keccak_pad" = globN s "keccak_pad" := by
          change globN s2 "keccak_pad" = globN ent "keccak_pad"
          unfold globN; rw [hs2_g, hs1_g]
          simp [HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "heap_ptr" ≠ ofString "keccak_pad" by decide]
        have hkst_eq : globN s2 "keccak_st" = globN s "keccak_st" := by
          change globN s2 "keccak_st" = globN ent "keccak_st"
          unfold globN; rw [hs2_g, hs1_g]
          simp [HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "heap_ptr" ≠ ofString "keccak_st" by decide]
        rw [evaluateHOLFiniteState_seq_line780] at hnt2 hres2
        rcases hc3 : evaluateHOLFiniteState s2
            (.call (some (none, none)) (ofString "keccak256")
              [ExpHOL.var VarKind.local (ofString "entry"),
               ExpHOL.var VarKind.local (ofString "n"),
               ExpHOL.var VarKind.local (ofString "h")]) with ⟨r3, s3⟩
        have hnt_c3 : r3 ≠ some .timeOut := by rintro rfl; rw [hc3] at hnt2; exact hnt2 rfl
        have hor_c3 : r3 = none ∨ Resumes r3 := by
          cases r3 with
          | none => exact Or.inl rfl
          | some rk =>
            right; rw [hc3] at hres2; exact hres2
        have h3 := eval_call_keccak256_heap s2
          (ExpHOL.var VarKind.local (ofString "entry"))
          (ExpHOL.var VarKind.local (ofString "n"))
          (ExpHOL.var VarKind.local (ofString "h"))
          entry0 n0 hw Rall gw heff12.arena.1.code heff12.arena
          hs2_entry hs2_n hs2_h
          ⟨(hw.toNat, 32), List.mem_cons_self, le_rfl, le_rfl⟩
          (fun hnz => by
            rw [hkpad_eq] at hnz ⊢
            obtain ⟨ivl, hivl, h1, h2⟩ := hpad_in hnz
            exact ⟨ivl, List.mem_cons_of_mem _ hivl, h1, h2⟩)
          (fun hnz => by
            rw [hkst_eq] at hnz ⊢
            obtain ⟨ivl, hivl, h1, h2⟩ := hst_in hnz
            exact ⟨ivl, List.mem_cons_of_mem _ hivl, h1, h2⟩)
          (by rw [hc3]; exact hnt_c3)
          (by rw [hc3]; exact hor_c3)
        rw [hc3] at h3 hnt2 hres2
        cases r3 with
        | some _ =>
          refine heapByteEff_of_seq_some hc3 ?_
          exact hmono_Rall (heff_ent_s2.trans h3.1)
        | none =>
          dsimp only at hnt2 hres2
          refine heapByteEff_of_seq_none hc3 ?_
          obtain ⟨hs3_loc, _⟩ := h3.2 rfl
          have hs3_mark : s3.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
            rw [hs3_loc]; exact hs2_mark
          have hs3_bloom : s3.locals.lookup (ofString "bloom") = some (.val (.word bloom0)) := by
            rw [hs3_loc]; exact hs2_bloom
          have heff_ent_s3 : HeapByteEff ent s3 Rall gw := heff_ent_s2.trans h3.1
          -- Step 4: `.dec "idx" .one (.const 0)`
          rw [evaluateHOLFiniteState_dec_total] at hnt2 hres2 ⊢
          dsimp only at hnt2 hres2 ⊢
          have hc0_ev : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
              (.const 0) = some (.val (.word 0)) := rfl
          rw [hc0_ev] at hnt2 hres2 ⊢; dsimp only at hnt2 hres2 ⊢
          have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) = true := by
            simp [shapeOfHOLExact, shapeEqHOL]
          rw [if_pos hsh0] at hnt2 hres2 ⊢; dsimp only at hnt2 hres2 ⊢
          set s4 := setVarHOLFinite (ofString "idx") (.val (.word 0)) s3
          have hs4_AR : ArenaReady s4 := localsFree_arenaReady s3 s4.locals s4.clock heff_ent_s3.arena
          have hs4_bloom : s4.locals.lookup (ofString "bloom") = some (.val (.word bloom0)) := by
            simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_bloom,
              show ofString "idx" ≠ ofString "bloom" by decide]
          have hs4_mark : s4.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
            simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_mark,
              show ofString "idx" ≠ ofString "mark" by decide]
          have heff_ent_s4 : HeapByteEff ent s4 Rall gw := heff_ent_s3.locals_clock s4.locals s4.clock
          -- Step 5: `addToBloomWhile`
          suffices hs4_tail : HeapByteEff ent
              (evaluateHOLFiniteState s4
                (.seq addToBloomWhile
                  (.seq (.call (some (none, none)) (ofString "heap_release")
                      [ExpHOL.var VarKind.local (ofString "mark")])
                    (.return (.const 0))))).2 Rl gw by
            exact hs4_tail.locals_clock _ _
          rw [evaluateHOLFiniteState_seq_line780] at hnt2 hres2
          rcases hw4 : evaluateHOLFiniteState s4 addToBloomWhile with ⟨rw4_res, s5⟩
          have hnt_w4 : rw4_res ≠ some .timeOut := by rintro rfl; rw [hw4] at hnt2; exact hnt2 rfl
          have hw_eff := addToBloomWhile_eff s4.clock s4 bloom0 Rall gw le_rfl hs4_AR hs4_bloom hdom
            (by obtain ⟨ivl, hivl, h1, h2⟩ := hbloom_in; exact ⟨ivl, List.mem_cons_of_mem _ hivl, h1, h2⟩)
            (by rw [hw4]; exact hnt_w4)
          rw [hw4] at hw_eff hnt2 hres2
          cases rw4_res with
          | some rw' =>
            dsimp only at hres2
            exact False.elim (hw_eff.2.1 (by simp) hres2)
          | none =>
            dsimp only at hnt2 hres2
            refine heapByteEff_of_seq_none hw4 ?_
            have hs5_mark : s5.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
              rw [hw_eff.2.2 rfl]; exact hs4_mark
            have heff_ent_s5 : HeapByteEff ent s5 Rall gw := heff_ent_s4.trans hw_eff.1
            -- Step 6: `heap_release(mark)` followed by `return 0`
            rw [evaluateHOLFiniteState_seq_line780] at hnt2 hres2
            rcases hc6 : evaluateHOLFiniteState s5
                (.call (some (none, none)) (ofString "heap_release")
                  [ExpHOL.var VarKind.local (ofString "mark")]) with ⟨r6, s6⟩
            have hnt_c6 : r6 ≠ some .timeOut := by rintro rfl; rw [hc6] at hnt2; exact hnt2 rfl
            have h6 := eval_call_heap_release s5 (ExpHOL.var VarKind.local (ofString "mark")) mark
              Rall gw heff_ent_s5.arena.1.code heff_ent_s5 hgw hs5_mark
              (by rw [hmark_nat])
              (by rw [hmark_nat]; exact hent_AR.2.1)
              (by rw [hmark_nat]; exact hent_AR.2.2.1)
              (by rw [hmark_nat]; exact hent_AR.2.2.2.2.2.2.1)
              (by rw [hc6]; exact hnt_c6)
            dsimp only at h6; rw [hc6] at h6
            obtain ⟨rfl, _, _, _, heff_ent_s6⟩ := h6
            refine heapByteEff_of_seq_none hc6 ?_
            have heff_ret : HeapByteEff s6 (evaluateHOLFiniteState s6 (.return (.const 0))).2 Rall gw :=
              HeapByteEff.of_byteEff heff_ent_s6.arena
                (R13Shards.Keccak256.byteEff_return s6 (.const 0) Rall)
            exact hmono_Rall (heff_ent_s6.trans heff_ret)

/-! ## Section 3: Inner and outer loops of `logs_bloom` and `wk_logs_bloom` -/

private def logsBloomInnerBody : ProgHOL 64 :=
  .seq
    (.call (some (none, none)) (ofString "add_to_bloom")
      [ExpHOL.var VarKind.local (ofString "out"),
       .op .add
         [.load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 8]),
          .panop .mul [ExpHOL.var VarKind.local (ofString "j"), .const 32]],
       .const 32])
    (.assign VarKind.local (ofString "j")
      (.op .add [ExpHOL.var VarKind.local (ofString "j"), .const 1]))

private def logsBloomInnerWhile : ProgHOL 64 :=
  .while (.cmp .less (ExpHOL.var VarKind.local (ofString "j"))
    (ExpHOL.var VarKind.local (ofString "nt"))) logsBloomInnerBody

private theorem logsBloomInnerWhile_eff {F : Type}
    (clk : Nat) (s0 s : PanSemStateFiniteExact 64 F) (out0 : BitVec 64)
    (Rl : List Ivl) (gw : List String)
    (hclk : s.clock ≤ clk)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hgw : "heap_ptr" ∈ gw)
    (hkpad_not_gw : ofString "keccak_pad" ∉ gw.map ofString)
    (hkst_not_gw : ofString "keccak_st" ∉ gw.map ofString)
    (hout : s.locals.lookup (ofString "out") = some (.val (.word out0)))
    (hdom : sourceBase ≤ out0.toNat ∧ out0.toNat + 256 ≤ heapEnd)
    (hout_in : ∃ ivl ∈ Rl, ivl.1 ≤ out0.toNat ∧ out0.toNat + 256 ≤ ivl.1 + ivl.2)
    (hpad_in : globN s0 "keccak_pad" ≠ 0 →
      ∃ ivl ∈ Rl, ivl.1 ≤ globN s0 "keccak_pad" ∧ globN s0 "keccak_pad" + 136 ≤ ivl.1 + ivl.2)
    (hst_in : globN s0 "keccak_st" ≠ 0 →
      ∃ ivl ∈ Rl, ivl.1 ≤ globN s0 "keccak_st" ∧ globN s0 "keccak_st" + 200 ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s logsBloomInnerWhile).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState s logsBloomInnerWhile).1 = none ∨
      Resumes (evaluateHOLFiniteState s logsBloomInnerWhile).1) :
    let out := evaluateHOLFiniteState s logsBloomInnerWhile
    HeapByteEff s out.2 Rl gw ∧
    (out.1 = none →
      out.2.locals.lookup (ofString "out") = some (.val (.word out0)) ∧
      out.2.locals.lookup (ofString "i") = s.locals.lookup (ofString "i") ∧
      out.2.locals.lookup (ofString "n") = s.locals.lookup (ofString "n") ∧
      out.2.locals.lookup (ofString "p") = s.locals.lookup (ofString "p")) := by
  induction clk generalizing s with
  | zero =>
    dsimp only [logsBloomInnerWhile] at hnt hor ⊢
    rw [evaluateHOLFiniteState_while_total] at hnt hor ⊢
    rcases hevc : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .less (ExpHOL.var VarKind.local (ofString "j"))
          (ExpHOL.var VarKind.local (ofString "nt"))) with _ | cv
    · simp only [hevc]; exact ⟨HeapByteEff.refl heff0.arena Rl gw, by simp⟩
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;>
        try (simp only [hevc]; exact ⟨HeapByteEff.refl heff0.arena Rl gw, by simp⟩)
      simp only [hevc] at hnt ⊢
      by_cases hnz : cw ≠ 0
      · have hz : s.clock = 0 := by omega
        rw [if_pos hnz, if_pos hz] at hnt; exact absurd rfl hnt
      · rw [if_neg hnz]
        exact ⟨HeapByteEff.refl heff0.arena Rl gw, fun _ => ⟨hout, rfl, rfl, rfl⟩⟩
  | succ k ih =>
    dsimp only [logsBloomInnerWhile] at hnt hor ⊢
    rw [evaluateHOLFiniteState_while_total] at hnt hor ⊢
    rcases hevc : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .less (ExpHOL.var VarKind.local (ofString "j"))
          (ExpHOL.var VarKind.local (ofString "nt"))) with _ | cv
    · simp only [hevc]; exact ⟨HeapByteEff.refl heff0.arena Rl gw, by simp⟩
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;>
        try (simp only [hevc]; exact ⟨HeapByteEff.refl heff0.arena Rl gw, by simp⟩)
      simp only [hevc] at hnt hor ⊢
      by_cases hnz : cw ≠ 0
      · rw [if_pos hnz] at hnt hor ⊢
        by_cases hz : s.clock = 0
        · rw [if_pos hz] at hnt; exact absurd rfl hnt
        · rw [if_neg hz] at hnt hor ⊢
          rw [fixClockHOLFinite_evaluateState] at hnt hor ⊢
          let sd := decClockHOLFinite s
          have hsd_AR : ArenaReady sd := localsFree_arenaReady s s.locals (s.clock - 1) heff0.arena
          dsimp only [logsBloomInnerBody] at hnt hor ⊢
          rw [evaluateHOLFiniteState_seq_line780] at hnt hor ⊢
          rcases hcall : evaluateHOLFiniteState sd
              (.call (some (none, none)) (ofString "add_to_bloom")
                [ExpHOL.var VarKind.local (ofString "out"),
                 .op .add
                   [.load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 8]),
                    .panop .mul [ExpHOL.var VarKind.local (ofString "j"), .const 32]],
                 .const 32]) with ⟨rc, m1⟩
          have hnt_c : rc ≠ some .timeOut := by
            rintro rfl; rw [hcall] at hnt; exact hnt rfl
          have hnbc := call0_ne_break_continue sd (ofString "add_to_bloom")
            [ExpHOL.var VarKind.local (ofString "out"),
             .op .add
               [.load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 8]),
                .panop .mul [ExpHOL.var VarKind.local (ofString "j"), .const 32]],
             .const 32]
          rw [hcall] at hnbc
          have hor_c : rc = none ∨ Resumes rc := by
            cases rc with
            | none => exact Or.inl rfl
            | some rc' =>
              cases rc' with
              | returned v => exact Or.inr (Or.inl ⟨v, rfl⟩)
              | exception e v =>
                rw [hcall] at hor; dsimp only at hor
                rcases hor with h | ⟨_, h⟩ | ⟨e', v', h, hne_t⟩
                · simp at h
                · simp at h
                · simp at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr (Or.inr ⟨e, v, rfl, hne_t⟩)
              | «break» => exact absurd rfl hnbc.1
              | «continue» => exact absurd rfl hnbc.2
              | error | timeOut | finalFfi _ =>
                rw [hcall] at hor; dsimp only at hor
                exfalso; rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
          have hkpad_sd : globN sd "keccak_pad" = globN s0 "keccak_pad" := by
            change globN s "keccak_pad" = globN s0 "keccak_pad"
            unfold globN
            rw [← heff0.globals (ofString "keccak_pad") hkpad_not_gw]
          have hkst_sd : globN sd "keccak_st" = globN s0 "keccak_st" := by
            change globN s "keccak_st" = globN s0 "keccak_st"
            unfold globN
            rw [← heff0.globals (ofString "keccak_st") hkst_not_gw]
          have hc_eff := eval_call_add_to_bloom sd
            (ExpHOL.var VarKind.local (ofString "out"))
            (.op .add
              [.load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 8]),
               .panop .mul [ExpHOL.var VarKind.local (ofString "j"), .const 32]])
            (.const 32)
            out0 Rl gw hsd_AR.1.code hsd_AR hgw hout hdom hout_in
            (fun hnz_p => by rw [hkpad_sd] at hnz_p ⊢; exact hpad_in hnz_p)
            (fun hnz_s => by rw [hkst_sd] at hnz_s ⊢; exact hst_in hnz_s)
            (by rw [hcall]; exact hnt_c)
            (by rw [hcall]; exact hor_c)
          have hclk_c := evaluateHOLFiniteState_clock_le sd
            (.call (some (none, none)) (ofString "add_to_bloom")
              [ExpHOL.var VarKind.local (ofString "out"),
               .op .add
                 [.load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 8]),
                  .panop .mul [ExpHOL.var VarKind.local (ofString "j"), .const 32]],
               .const 32])
          rw [hcall] at hc_eff hclk_c hnt hor
          have heff_s_m1 : HeapByteEff s m1 Rl gw :=
            (HeapByteEff.refl heff0.arena Rl gw |>.locals_clock sd.locals sd.clock).trans hc_eff.1
          cases rc with
          | some rc' =>
            cases rc' with
            | «break» => exact absurd rfl hnbc.1
            | «continue» => exact absurd rfl hnbc.2
            | returned _ | exception _ _ => exact ⟨heff_s_m1, by simp⟩
            | error | timeOut | finalFfi _ => exact ⟨heff_s_m1.locals_clock _ _, by simp⟩
          | none =>
            have hm1_loc : m1.locals = s.locals := hc_eff.2 rfl
            rcases hass : evaluateHOLFiniteState m1
                (.assign VarKind.local (ofString "j")
                  (.op .add [ExpHOL.var VarKind.local (ofString "j"), .const 1])) with ⟨ra, m2⟩
            simp only [hcall, hass] at hnt hor ⊢
            have hass_cases : (ra = none ∧ ∃ jv, m2 = setVarHOLFinite (ofString "j") jv m1) ∨
                (ra = some .error ∧ m2 = m1) := by
              rw [evaluateHOLFiniteState_assign] at hass
              split at hass
              · injection hass with hr hm; exact Or.inr ⟨hr.symm, hm.symm⟩
              · split at hass
                · rename_i jv _ _
                  injection hass with hr hm
                  exact Or.inl ⟨hr.symm, jv, hm.symm⟩
                · injection hass with hr hm; exact Or.inr ⟨hr.symm, hm.symm⟩
            rcases hass_cases with ⟨rfl, jv, rfl⟩ | ⟨rfl, rfl⟩
            · dsimp only at hnt hor ⊢
              set m2 := setVarHOLFinite (ofString "j") jv m1
              have heff_s_m2 : HeapByteEff s m2 Rl gw := heff_s_m1.locals_clock m2.locals m2.clock
              have hm2_clk : m2.clock ≤ k := by change m1.clock ≤ k; change m1.clock ≤ s.clock - 1 at hclk_c; omega
              have hm2_out : m2.locals.lookup (ofString "out") = some (.val (.word out0)) := by
                simp [m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_loc, hout,
                  show ofString "j" ≠ ofString "out" by decide]
              have ih_res := ih m2 hm2_clk (heff0.trans heff_s_m2) hm2_out hnt hor
              dsimp only [logsBloomInnerWhile, logsBloomInnerBody] at ih_res
              refine ⟨heff_s_m2.trans ih_res.1, fun hn => ?_⟩
              obtain ⟨ho1, ho2, ho3, ho4⟩ := ih_res.2 hn
              refine ⟨ho1, ?_, ?_, ?_⟩
              · rw [ho2]; simp [m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_loc,
                  show ofString "j" ≠ ofString "i" by decide]
              · rw [ho3]; simp [m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_loc,
                  show ofString "j" ≠ ofString "n" by decide]
              · rw [ho4]; simp [m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_loc,
                  show ofString "j" ≠ ofString "p" by decide]
            · exact ⟨heff_s_m1, by simp⟩
      · rw [if_neg hnz]
        exact ⟨HeapByteEff.refl heff0.arena Rl gw, fun _ => ⟨hout, rfl, rfl, rfl⟩⟩

private def logsBloomOuterBody : ProgHOL 64 :=
  .dec (ofString "log") .one
    (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "p"),
      .panop .mul [ExpHOL.var VarKind.local (ofString "i"), .const 8]]))
    (.seq
      (.call (some (none, none)) (ofString "add_to_bloom")
        [ExpHOL.var VarKind.local (ofString "out"),
         .load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 0]),
         .const 20])
      (.dec (ofString "nt") .one
        (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 16]))
        (.dec (ofString "j") .one (.const 0)
          (.seq logsBloomInnerWhile
            (.assign VarKind.local (ofString "i")
              (.op .add [ExpHOL.var VarKind.local (ofString "i"), .const 1]))))))

private def logsBloomOuterWhile : ProgHOL 64 :=
  .while (.cmp .less (ExpHOL.var VarKind.local (ofString "i"))
    (ExpHOL.var VarKind.local (ofString "n"))) logsBloomOuterBody

private theorem logsBloomOuterBody_step {F : Type}
    (s0 s : PanSemStateFiniteExact 64 F) (out0 : BitVec 64)
    (Rl : List Ivl) (gw : List String)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hgw : "heap_ptr" ∈ gw)
    (hkpad_not_gw : ofString "keccak_pad" ∉ gw.map ofString)
    (hkst_not_gw : ofString "keccak_st" ∉ gw.map ofString)
    (hout : s.locals.lookup (ofString "out") = some (.val (.word out0)))
    (hdom : sourceBase ≤ out0.toNat ∧ out0.toNat + 256 ≤ heapEnd)
    (hout_in : ∃ ivl ∈ Rl, ivl.1 ≤ out0.toNat ∧ out0.toNat + 256 ≤ ivl.1 + ivl.2)
    (hpad_in : globN s0 "keccak_pad" ≠ 0 →
      ∃ ivl ∈ Rl, ivl.1 ≤ globN s0 "keccak_pad" ∧ globN s0 "keccak_pad" + 136 ≤ ivl.1 + ivl.2)
    (hst_in : globN s0 "keccak_st" ≠ 0 →
      ∃ ivl ∈ Rl, ivl.1 ≤ globN s0 "keccak_st" ∧ globN s0 "keccak_st" + 200 ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s logsBloomOuterBody).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState s logsBloomOuterBody).1 = none ∨
      Resumes (evaluateHOLFiniteState s logsBloomOuterBody).1) :
    let out := evaluateHOLFiniteState s logsBloomOuterBody
    HeapByteEff s out.2 Rl gw ∧
    out.1 ≠ some .continue ∧
    out.1 ≠ some .break ∧
    (out.1 = none → out.2.locals.lookup (ofString "out") = some (.val (.word out0))) := by
  intro out; dsimp only [out]; dsimp only [logsBloomOuterBody] at hnt hor ⊢
  rw [evaluateHOLFiniteState_dec_total] at hnt hor ⊢
  dsimp only at hnt hor ⊢
  revert hor; revert hnt
  split
  · intro _ _; exact ⟨HeapByteEff.refl heff0.arena Rl gw, by simp, by simp, by simp⟩
  · rename_i vlog hlog_ev
    split
    · rename_i hsh_log
      intro hnt hor
      dsimp only at hnt hor ⊢
      set s1 := setVarHOLFinite (ofString "log") vlog s
      have heff_s_s1 : HeapByteEff s s1 Rl gw :=
        (HeapByteEff.refl heff0.arena Rl gw).locals_clock s1.locals s1.clock
      have hs1_out : s1.locals.lookup (ofString "out") = some (.val (.word out0)) := by
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hout,
          show ofString "log" ≠ ofString "out" by decide]
      -- `.seq (call add_to_bloom ...) ...`
      rw [evaluateHOLFiniteState_seq_line780] at hnt hor ⊢
      rcases hc1 : evaluateHOLFiniteState s1
          (.call (some (none, none)) (ofString "add_to_bloom")
            [ExpHOL.var VarKind.local (ofString "out"),
             .load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 0]),
             .const 20]) with ⟨rc1, s2⟩
      have hnt_c1 : rc1 ≠ some .timeOut := by rintro rfl; rw [hc1] at hnt; exact hnt rfl
      have hnbc1 := call0_ne_break_continue s1 (ofString "add_to_bloom")
        [ExpHOL.var VarKind.local (ofString "out"),
         .load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 0]),
         .const 20]
      rw [hc1] at hnbc1
      have hor_c1 : rc1 = none ∨ Resumes rc1 := by
        cases rc1 with
        | none => exact Or.inl rfl
        | some rc' =>
          rw [hc1] at hor; dsimp only at hor
          exact Or.inr (hor.resolve_left (by simp))
      have hkpad_s1 : globN s1 "keccak_pad" = globN s0 "keccak_pad" := by
        change globN s "keccak_pad" = globN s0 "keccak_pad"
        unfold globN
        rw [← heff0.globals (ofString "keccak_pad") hkpad_not_gw]
      have hkst_s1 : globN s1 "keccak_st" = globN s0 "keccak_st" := by
        change globN s "keccak_st" = globN s0 "keccak_st"
        unfold globN
        rw [← heff0.globals (ofString "keccak_st") hkst_not_gw]
      have h1_eff := eval_call_add_to_bloom s1
        (ExpHOL.var VarKind.local (ofString "out"))
        (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 0]))
        (.const 20)
        out0 Rl gw heff_s_s1.arena.1.code heff_s_s1.arena hgw hs1_out hdom hout_in
        (fun hnz_p => by rw [hkpad_s1] at hnz_p ⊢; exact hpad_in hnz_p)
        (fun hnz_s => by rw [hkst_s1] at hnz_s ⊢; exact hst_in hnz_s)
        (by rw [hc1]; exact hnt_c1)
        (by rw [hc1]; exact hor_c1)
      rw [hc1] at h1_eff hnt hor
      have heff_s_s2 : HeapByteEff s s2 Rl gw := heff_s_s1.trans h1_eff.1
      cases rc1 with
      | some rc' =>
        dsimp only
        exact ⟨heff_s_s2.locals_clock _ _, hnbc1.2, hnbc1.1, by simp⟩
      | none =>
        dsimp only at hnt hor ⊢
        have hs2_loc : s2.locals = s1.locals := h1_eff.2 rfl
        have hs2_out : s2.locals.lookup (ofString "out") = some (.val (.word out0)) := by
          rw [hs2_loc]; exact hs1_out
        -- `.dec "nt"`
        rw [evaluateHOLFiniteState_dec_total] at hnt hor ⊢
        dsimp only at hnt hor ⊢
        revert hor; revert hnt
        split
        · intro _ _; exact ⟨heff_s_s2.locals_clock _ _, by simp, by simp, by simp⟩
        · rename_i vnt hnt_ev
          split
          · rename_i hsh_nt
            intro hnt hor
            dsimp only at hnt hor ⊢
            set s3 := setVarHOLFinite (ofString "nt") vnt s2
            -- `.dec "j" := 0`
            rw [evaluateHOLFiniteState_dec_total] at hnt hor ⊢
            simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt hor ⊢
            set s4 := setVarHOLFinite (ofString "j") (.val (.word 0)) s3
            have heff_s_s4 : HeapByteEff s s4 Rl gw := heff_s_s2.locals_clock s4.locals s4.clock
            have hs4_out : s4.locals.lookup (ofString "out") = some (.val (.word out0)) := by
              simp [s4, s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_out,
                show ofString "j" ≠ ofString "out" by decide,
                show ofString "nt" ≠ ofString "out" by decide]
            -- `.seq logsBloomInnerWhile (.assign "i" ...)`
            rw [evaluateHOLFiniteState_seq_line780] at hnt hor ⊢
            rcases hwi : evaluateHOLFiniteState s4 logsBloomInnerWhile with ⟨rwi, s5⟩
            have hnt_wi : rwi ≠ some .timeOut := by rintro rfl; rw [hwi] at hnt; exact hnt rfl
            have hwi_nbc : rwi ≠ some .break ∧ rwi ≠ some .continue := by
              have hwnbc : ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock ≤ k →
                  (evaluateHOLFiniteState st logsBloomInnerWhile).1 ≠ some .break ∧
                  (evaluateHOLFiniteState st logsBloomInnerWhile).1 ≠ some .continue := by
                intro k
                induction k with
                | zero =>
                  intro st hst_k; dsimp only [logsBloomInnerWhile]; rw [evaluateHOLFiniteState_while_total]
                  split
                  · split
                    · split
                      · simp
                      · omega
                    · simp
                  · simp
                | succ k ih_k =>
                  intro st hst_k; dsimp only [logsBloomInnerWhile]; rw [evaluateHOLFiniteState_while_total]
                  split
                  · split
                    · split
                      · simp
                      · dsimp only; rw [fixClockHOLFinite_evaluateState]
                        have hrem_k := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) logsBloomInnerBody
                        rcases hbk : evaluateHOLFiniteState (decClockHOLFinite st) logsBloomInnerBody with ⟨rbk, mbk⟩
                        rw [hbk] at hrem_k
                        cases rbk with
                        | none => exact ih_k mbk (by change mbk.clock ≤ st.clock - 1 at hrem_k; omega)
                        | some rbk' =>
                          cases rbk' <;> try simp
                          exact ih_k mbk (by change mbk.clock ≤ st.clock - 1 at hrem_k; omega)
                    · simp
                  · simp
              have hw := hwnbc s4.clock s4 le_rfl
              rw [hwi] at hw
              exact hw
            have hor_wi : rwi = none ∨ Resumes rwi := by
              cases rwi with
              | none => exact Or.inl rfl
              | some rw' =>
                rw [hwi] at hor; dsimp only at hor
                exact Or.inr (hor.resolve_left (by simp))
            have hwi_eff := logsBloomInnerWhile_eff s4.clock s0 s4 out0 Rl gw le_rfl
              (heff0.trans heff_s_s4) hgw hkpad_not_gw hkst_not_gw hs4_out hdom hout_in hpad_in hst_in
              (by rw [hwi]; exact hnt_wi) (by rw [hwi]; exact hor_wi)
            rw [hwi] at hwi_eff hnt hor
            have heff_s_s5 : HeapByteEff s s5 Rl gw := heff_s_s4.trans hwi_eff.1
            cases rwi with
            | some rw' =>
              dsimp only
              exact ⟨((heff_s_s5.locals_clock _ _).locals_clock _ _).locals_clock _ _, hwi_nbc.2, hwi_nbc.1, by simp⟩
            | none =>
              dsimp only at hnt hor ⊢
              obtain ⟨hs5_out, _, _, _⟩ := hwi_eff.2 rfl
              rw [evaluateHOLFiniteState_assign]
              split
              · exact ⟨((heff_s_s5.locals_clock _ _).locals_clock _ _).locals_clock _ _, by simp, by simp, by simp⟩
              · split
                · dsimp only [setKvarHOLFinite, setVarHOLFinite]
                  refine ⟨(((heff_s_s5.locals_clock _ _).locals_clock _ _).locals_clock _ _).locals_clock _ _,
                    by simp, by simp, fun _ => ?_⟩
                  have hlr : ∀ (m : HolFiniteMapExact MlS (ValueHOL 64)) (v : MlS) (old : Option (ValueHOL 64)) (k : MlS),
                      k ≠ v → (m.resVarEq (v, old)).lookup k = m.lookup k := by
                    intro m v old k hne
                    simp only [HolFiniteMapExact.resVarEq]
                    cases old <;> simp [FDOMSUB_HOL, FUPDATE_HOL, hne, Ne.symm hne]
                  simp only [hlr _ _ _ _ (show ofString "out" ≠ ofString "log" by decide),
                    hlr _ _ _ _ (show ofString "out" ≠ ofString "nt" by decide),
                    hlr _ _ _ _ (show ofString "out" ≠ ofString "j" by decide),
                    HolFiniteMapExact.lookup_update, FUPDATE,
                    if_neg (show ofString "out" ≠ ofString "i" by decide)]
                  exact hs5_out
                · exact ⟨((heff_s_s5.locals_clock _ _).locals_clock _ _).locals_clock _ _, by simp, by simp, by simp⟩
          · intro _ _; exact ⟨heff_s_s2.locals_clock _ _, by simp, by simp, by simp⟩
    · intro _ _; exact ⟨HeapByteEff.refl heff0.arena Rl gw, by simp, by simp, by simp⟩

private theorem logsBloomOuterWhile_eff {F : Type}
    (clk : Nat) (s0 s : PanSemStateFiniteExact 64 F) (out0 : BitVec 64)
    (Rl : List Ivl) (gw : List String)
    (hclk : s.clock ≤ clk)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hgw : "heap_ptr" ∈ gw)
    (hkpad_not_gw : ofString "keccak_pad" ∉ gw.map ofString)
    (hkst_not_gw : ofString "keccak_st" ∉ gw.map ofString)
    (hout : s.locals.lookup (ofString "out") = some (.val (.word out0)))
    (hdom : sourceBase ≤ out0.toNat ∧ out0.toNat + 256 ≤ heapEnd)
    (hout_in : ∃ ivl ∈ Rl, ivl.1 ≤ out0.toNat ∧ out0.toNat + 256 ≤ ivl.1 + ivl.2)
    (hpad_in : globN s0 "keccak_pad" ≠ 0 →
      ∃ ivl ∈ Rl, ivl.1 ≤ globN s0 "keccak_pad" ∧ globN s0 "keccak_pad" + 136 ≤ ivl.1 + ivl.2)
    (hst_in : globN s0 "keccak_st" ≠ 0 →
      ∃ ivl ∈ Rl, ivl.1 ≤ globN s0 "keccak_st" ∧ globN s0 "keccak_st" + 200 ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s logsBloomOuterWhile).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState s logsBloomOuterWhile).1 = none ∨
      Resumes (evaluateHOLFiniteState s logsBloomOuterWhile).1) :
    HeapByteEff s (evaluateHOLFiniteState s logsBloomOuterWhile).2 Rl gw := by
  induction clk generalizing s with
  | zero =>
    dsimp only [logsBloomOuterWhile] at hnt ⊢
    rw [evaluateHOLFiniteState_while_total] at hnt ⊢
    rcases hevc : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .less (ExpHOL.var VarKind.local (ofString "i"))
          (ExpHOL.var VarKind.local (ofString "n"))) with _ | cv
    · simp only [hevc]; exact HeapByteEff.refl heff0.arena Rl gw
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;>
        try (simp only [hevc]; exact HeapByteEff.refl heff0.arena Rl gw)
      simp only [hevc] at hnt ⊢
      by_cases hnz : cw ≠ 0
      · have hz : s.clock = 0 := by omega
        rw [if_pos hnz, if_pos hz] at hnt; exact absurd rfl hnt
      · rw [if_neg hnz]; exact HeapByteEff.refl heff0.arena Rl gw
  | succ k ih =>
    dsimp only [logsBloomOuterWhile] at hnt hor ⊢
    rw [evaluateHOLFiniteState_while_total] at hnt hor ⊢
    rcases hevc : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .less (ExpHOL.var VarKind.local (ofString "i"))
          (ExpHOL.var VarKind.local (ofString "n"))) with _ | cv
    · simp only [hevc]; exact HeapByteEff.refl heff0.arena Rl gw
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;>
        try (simp only [hevc]; exact HeapByteEff.refl heff0.arena Rl gw)
      simp only [hevc] at hnt hor ⊢
      by_cases hnz : cw ≠ 0
      · rw [if_pos hnz] at hnt hor ⊢
        by_cases hz : s.clock = 0
        · rw [if_pos hz] at hnt; exact absurd rfl hnt
        · rw [if_neg hz] at hnt hor ⊢
          rw [fixClockHOLFinite_evaluateState] at hnt hor ⊢
          let sd := decClockHOLFinite s
          have heff_s_sd : HeapByteEff s sd Rl gw :=
            (HeapByteEff.refl heff0.arena Rl gw).locals_clock sd.locals sd.clock
          have hcle := evaluateHOLFiniteState_clock_le sd logsBloomOuterBody
          rcases hbr : evaluateHOLFiniteState sd logsBloomOuterBody with ⟨rb, mid⟩
          have hnt_b : rb ≠ some .timeOut := by
            rintro rfl; rw [hbr] at hnt; exact hnt rfl
          have hnbc_b : rb ≠ some .break ∧ rb ≠ some .continue := by
            dsimp only [logsBloomOuterBody] at hbr
            rw [evaluateHOLFiniteState_dec_total] at hbr; dsimp only at hbr
            split at hbr
            · injection hbr with e _; subst e; simp
            · rename_i vlog_t _
              split at hbr
              · rw [evaluateHOLFiniteState_seq_line780] at hbr
                let args1 : List (ExpHOL 64) :=
                  [ExpHOL.var VarKind.local (ofString "out"),
                   .load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 0]),
                   .const 20]
                rcases hc_tmp : evaluateHOLFiniteState (setVarHOLFinite (ofString "log") vlog_t sd)
                    (.call (some (none, none)) (ofString "add_to_bloom") args1) with ⟨rc_t, mc_t⟩
                have hnbc_t := call0_ne_break_continue (setVarHOLFinite (ofString "log") vlog_t sd) (ofString "add_to_bloom") args1
                rw [hc_tmp] at hbr hnbc_t
                cases rc_t with
                | some rc_t' =>
                  dsimp only at hbr; injection hbr with e _; subst e
                  exact ⟨hnbc_t.1, hnbc_t.2⟩
                | none =>
                  dsimp only at hbr
                  rw [evaluateHOLFiniteState_dec_total] at hbr; dsimp only at hbr
                  split at hbr
                  · injection hbr with e _; subst e; simp
                  · split at hbr
                    · rename_i vnt_t _ _
                      rw [evaluateHOLFiniteState_dec_total] at hbr; dsimp only at hbr
                      split at hbr
                      · injection hbr with e _; subst e; simp
                      · rename_i vj_t _
                        split at hbr
                        · let st_wi := setVarHOLFinite (ofString "j") vj_t (setVarHOLFinite (ofString "nt") vnt_t mc_t)
                          rw [evaluateHOLFiniteState_seq_line780] at hbr
                          rcases hwi_t : evaluateHOLFiniteState st_wi logsBloomInnerWhile with ⟨rwi_t, mwi_t⟩
                          have hwnbc : ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock ≤ k →
                              (evaluateHOLFiniteState st logsBloomInnerWhile).1 ≠ some .break ∧
                              (evaluateHOLFiniteState st logsBloomInnerWhile).1 ≠ some .continue := by
                            intro k0
                            induction k0 with
                            | zero =>
                              intro st hst_k; dsimp only [logsBloomInnerWhile]; rw [evaluateHOLFiniteState_while_total]
                              split
                              · split
                                · split
                                  · simp
                                  · omega
                                · simp
                              · simp
                            | succ k0 ih_k =>
                              intro st _; dsimp only [logsBloomInnerWhile]; rw [evaluateHOLFiniteState_while_total]
                              split
                              · split
                                · split
                                  · simp
                                  · dsimp only; rw [fixClockHOLFinite_evaluateState]
                                    have hrem_k := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) logsBloomInnerBody
                                    rcases hbk : evaluateHOLFiniteState (decClockHOLFinite st) logsBloomInnerBody with ⟨rbk, mbk⟩
                                    rw [hbk] at hrem_k
                                    cases rbk with
                                    | none => exact ih_k mbk (by change mbk.clock ≤ st.clock - 1 at hrem_k; omega)
                                    | some rbk' =>
                                      cases rbk' <;> try simp
                                      exact ih_k mbk (by change mbk.clock ≤ st.clock - 1 at hrem_k; omega)
                                · simp
                              · simp
                          have hw_t := hwnbc st_wi.clock st_wi le_rfl
                          rw [hwi_t] at hbr hw_t
                          cases rwi_t with
                          | some rwi_t' =>
                            dsimp only at hbr; injection hbr with e _; subst e
                            exact hw_t
                          | none =>
                            dsimp only at hbr
                            rw [evaluateHOLFiniteState_assign] at hbr
                            split at hbr
                            · injection hbr with e _; subst e; simp
                            · split at hbr
                              · injection hbr with e _; subst e; simp
                              · injection hbr with e _; subst e; simp
                        · injection hbr with e _; subst e; simp
                    · injection hbr with e _; subst e; simp
              · injection hbr with e _; subst e; simp
          have hor_b : rb = none ∨ Resumes rb := by
            cases rb with
            | none => exact Or.inl rfl
            | some rb' =>
              cases rb' with
              | returned v => exact Or.inr (Or.inl ⟨v, rfl⟩)
              | exception e v =>
                rw [hbr] at hor; dsimp only at hor
                rcases hor with h | ⟨_, h⟩ | ⟨e', v', h, hne_t⟩
                · simp at h
                · simp at h
                · simp at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr (Or.inr ⟨e, v, rfl, hne_t⟩)
              | «break» => exact False.elim (hnbc_b.1 rfl)
              | «continue» => exact False.elim (hnbc_b.2 rfl)
              | error | timeOut | finalFfi _ =>
                exfalso
                rw [hbr] at hor; dsimp only at hor
                rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
          have hstep := logsBloomOuterBody_step s0 sd out0 Rl gw
            (heff0.trans heff_s_sd) hgw hkpad_not_gw hkst_not_gw hout hdom hout_in hpad_in hst_in
            (by rw [hbr]; exact hnt_b) (by rw [hbr]; exact hor_b)
          rw [hbr] at hstep hcle hnt hor
          have heff_s_mid : HeapByteEff s mid Rl gw := heff_s_sd.trans hstep.1
          cases rb with
          | none =>
            dsimp only at hnt hor ⊢
            have hm_clk : mid.clock ≤ k := by change mid.clock ≤ s.clock - 1 at hcle; omega
            have hm_out := hstep.2.2.2 rfl
            exact heff_s_mid.trans (ih mid hm_clk (heff0.trans heff_s_mid) hm_out hnt hor)
          | some rb' =>
            cases rb' with
            | «continue» => exact absurd rfl hstep.2.1
            | «break» => exact absurd rfl hstep.2.2.1
            | returned _ | exception _ _ => exact heff_s_mid
            | error | timeOut | finalFfi _ => exact heff_s_mid.locals_clock _ _
      · rw [if_neg hnz]; exact HeapByteEff.refl heff0.arena Rl gw

theorem «wk_logs_bloom» :
    WorldKeeps WorldOK
      (fun s => [(locN s "out", 256),
        (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "logs_bloom") := by
  refine ⟨_, _, _, lookup_logs_bloom, fun {F} s hcode hW hparams hnt hres => ?_⟩
  have hAR : ArenaReady s := hW.1
  obtain ⟨vals, hl_args⟩ := hparams
  obtain ⟨logs0, out0, _, hlogs, hout⟩ :=
    R13Shards.Keccak256.lookupCode_two_words (by decide) lookup_logs_bloom hl_args
  have hout_locN : locN s "out" = out0.toNat := by simp [locN, hout]
  let Rs : List Ivl :=
    [(locN s "out", 256),
     (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
     (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)]
  suffices hmain : HeapByteEff s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_logs_bloom)).2
      (Rs ++ ([] : List (String × Nat)).map (bufferRegion s)) ["heap_ptr"] by
    exact hmain.to_worldStep (R := fun t =>
        [(locN t "out", 256),
         (globN t "keccak_pad", if globN t "keccak_pad" = 0 then 0 else 136),
         (globN t "keccak_st", if globN t "keccak_st" = 0 then 0 else 200)])
      (B := [])
      (by intro _ h; cases h)
      (by intro g hg; simp at hg; exact Or.inl hg)
      hW (fun _ _ _ _ _ => trivial)
  simp only [List.map_nil, List.append_nil]
  have hb : sourceFnBody Guest.Software.guestFn_logs_bloom =
      .seq (.call (some (none, none)) (ofString "memzero")
          [ExpHOL.var VarKind.local (ofString "out"), .const 256])
        (.dec (ofString "n") .one
          (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "logs"), .const 8]))
          (.dec (ofString "p") .one
            (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "logs"), .const 0]))
            (.dec (ofString "i") .one (.const 0)
              (.seq logsBloomOuterWhile
                (.return (.const 0)))))) := rfl
  rw [hb] at hnt hres ⊢
  rw [evaluateHOLFiniteState_seq_line780] at hnt hres
  rcases hmz : evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memzero")
        [ExpHOL.var VarKind.local (ofString "out"), .const 256]) with ⟨rmz, s1⟩
  have hnt_mz : rmz ≠ some .timeOut := by rintro rfl; rw [hmz] at hnt; exact hnt rfl
  have h1 := eval_call_memzero_heap s
    (ExpHOL.var VarKind.local (ofString "out")) (.const 256)
    out0 256 Rs ["heap_ptr"] hcode hAR hout rfl
    (fun _ => ⟨(locN s "out", 256), List.mem_cons_self,
      by rw [hout_locN], by rw [hout_locN]; change out0.toNat + 256 ≤ out0.toNat + 256; omega⟩)
    (by rw [hmz]; exact hnt_mz)
  dsimp only at h1; rw [hmz] at h1 hnt hres
  cases rmz with
  | some _ => exfalso; exact h1.2 (by simp) hres
  | none =>
    dsimp only at hnt hres h1
    refine heapByteEff_of_seq_none hmz ?_
    obtain ⟨hdom_fn, heff01, hs1_loc, _⟩ := h1.1 rfl
    have hdom : sourceBase ≤ out0.toNat ∧ out0.toNat + 256 ≤ heapEnd := hdom_fn (by decide)
    -- Step 2: `.dec "n"`
    rw [evaluateHOLFiniteState_dec_total] at hnt hres ⊢
    rcases hn_ev : evalHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
        (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "logs"), .const 8])) with _ | vn
    · simp only [evalHOLFinite] at hn_ev
      simp only [hn_ev]
      exact heff01
    · simp only [evalHOLFinite] at hn_ev
      simp only [hn_ev] at hnt hres ⊢
      by_cases hsh_n : shapeEqHOL .one (shapeOfHOLExact vn) = true
      · rw [if_pos hsh_n] at hnt hres ⊢
        dsimp only at hnt hres ⊢
        set s2 := setVarHOLFinite (ofString "n") vn s1
        suffices hs2_tail : HeapByteEff s
            (evaluateHOLFiniteState s2
              (.dec (ofString "p") .one
                (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "logs"), .const 0]))
                (.dec (ofString "i") .one (.const 0)
                  (.seq logsBloomOuterWhile (.return (.const 0)))))).2 Rs ["heap_ptr"] by
          exact hs2_tail.locals_clock _ _
        -- Step 3: `.dec "p"`
        rw [evaluateHOLFiniteState_dec_total] at hnt hres ⊢
        rcases hp_ev : evalHOLFinite s2 (h := fun a => Classical.propDecidable (s2.memaddrs a))
            (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "logs"), .const 0])) with _ | vp
        · simp only [evalHOLFinite] at hp_ev
          simp only [hp_ev]
          exact heff01.locals_clock s2.locals s2.clock
        · simp only [evalHOLFinite] at hp_ev
          simp only [hp_ev] at hnt hres ⊢
          by_cases hsh_p : shapeEqHOL .one (shapeOfHOLExact vp) = true
          · rw [if_pos hsh_p] at hnt hres ⊢
            dsimp only at hnt hres ⊢
            set s3 := setVarHOLFinite (ofString "p") vp s2
            suffices hs3_tail : HeapByteEff s
                (evaluateHOLFiniteState s3
                  (.dec (ofString "i") .one (.const 0)
                    (.seq logsBloomOuterWhile (.return (.const 0))))).2 Rs ["heap_ptr"] by
              exact hs3_tail.locals_clock _ _
            -- Step 4: `.dec "i" := 0`
            rw [evaluateHOLFiniteState_dec_total] at hnt hres ⊢
            simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt hres ⊢
            set s4 := setVarHOLFinite (ofString "i") (.val (.word 0)) s3
            have heff_s_s4 : HeapByteEff s s4 Rs ["heap_ptr"] := heff01.locals_clock s4.locals s4.clock
            have hs4_out : s4.locals.lookup (ofString "out") = some (.val (.word out0)) := by
              simp [s4, s3, s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_loc, hout,
                show ofString "i" ≠ ofString "out" by decide,
                show ofString "p" ≠ ofString "out" by decide,
                show ofString "n" ≠ ofString "out" by decide]
            -- Step 5: `.seq logsBloomOuterWhile (.return (.const 0))`
            suffices hs4_tail : HeapByteEff s
                (evaluateHOLFiniteState s4 (.seq logsBloomOuterWhile (.return (.const 0)))).2 Rs ["heap_ptr"] by
              exact hs4_tail.locals_clock _ _
            rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
            rcases hwo : evaluateHOLFiniteState s4 logsBloomOuterWhile with ⟨rwo, s5⟩
            have hnt_wo : rwo ≠ some .timeOut := by rintro rfl; rw [hwo] at hnt; exact hnt rfl
            have hor_wo : rwo = none ∨ Resumes rwo := by
              cases rwo with
              | none => exact Or.inl rfl
              | some _ => rw [hwo] at hres; right; exact hres
            have hwo_eff := logsBloomOuterWhile_eff s4.clock s s4 out0 Rs ["heap_ptr"] le_rfl
              heff_s_s4 (by simp) (by decide) (by decide) hs4_out hdom
              ⟨(locN s "out", 256), List.mem_cons_self, by rw [hout_locN], by rw [hout_locN]⟩
              (fun hnz => ⟨(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                List.mem_cons_of_mem _ List.mem_cons_self, le_rfl, by simp [hnz]⟩)
              (fun hnz => ⟨(globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), le_rfl, by simp [hnz]⟩)
              (by rw [hwo]; exact hnt_wo) (by rw [hwo]; exact hor_wo)
            rw [hwo] at hwo_eff
            have heff_s_s5 : HeapByteEff s s5 Rs ["heap_ptr"] := heff_s_s4.trans hwo_eff
            cases rwo with
            | some _ => exact heff_s_s5
            | none =>
              dsimp only
              exact heff_s_s5.trans
                (HeapByteEff.of_byteEff heff_s_s5.arena (R13Shards.Keccak256.byteEff_return s5 (.const 0) Rs))
          · rw [if_neg hsh_p]
            exact heff01.locals_clock s2.locals s2.clock
      · rw [if_neg hsh_n]
        exact heff01

end InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
