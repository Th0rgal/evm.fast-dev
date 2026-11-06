import InitECandidate.Solver.Wave8GuestInv.ContractParts.C12
import InitECandidate.Solver.Wave8GuestInv.R14Shards.P3C10C12.P3_CsrLoops
import InitECandidate.Solver.Wave8GuestInv.R14Shards.P3C10C12.P3_MptSet_Memory
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkEncodeAccount
import InitECandidate.Solver.Wave8GuestInv.R16Shards.GbodyC17ToC21Common
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkCacheGetRootTop
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01AllocMpt
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.wk_u256_to_be_min

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.P3Csr
open InitECandidate.Solver.Wave8GuestInv.P3MptSet
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28
open InitECandidate.Solver.Wave8GuestInv.R16Shards.GbodyC17ToC21Common
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R16Rlp

/-! ## Section 1: Callee lookups and `rv_encode_account` (`RetLe` ≤ 110) -/

theorem lookup_htab_copy_csr :
    originalRuntimeCode.lookup (ofString "htab_copy") =
      some ((sourceFunctionEntry Guest.Software.guestFn_htab_copy).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 145 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_copy) rfl

theorem lookup_mpt_from_witness_csr :
    originalRuntimeCode.lookup (ofString "mpt_from_witness") =
      some ((sourceFunctionEntry Guest.Software.guestFn_mpt_from_witness).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 269 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mpt_from_witness) rfl

theorem lookup_mpt_root_csr :
    originalRuntimeCode.lookup (ofString "mpt_root") =
      some ((sourceFunctionEntry Guest.Software.guestFn_mpt_root).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 291 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mpt_root) rfl

theorem lookup_u256_to_be_min_csr :
    originalRuntimeCode.lookup (ofString "u256_to_be_min") =
      some ((sourceFunctionEntry Guest.Software.guestFn_u256_to_be_min).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 88 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_to_be_min) rfl

theorem lookup_compute_state_root_csr :
    originalRuntimeCode.lookup (ofString "compute_state_root") =
      some ((sourceFunctionEntry Guest.Software.guestFn_compute_state_root).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 843 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_compute_state_root) rfl

private theorem not_resumes_err_csr : ¬ Resumes (some (.error : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h

private def encodeAcctZeroLoopCsr : ProgHOL 64 :=
  .while (.cmp .lower (.var .local (ofString "z")) (.const (32#64)))
    (.seq
      (.ite (.cmp .notEqual
          (.loadByte (.op .add [.var .global (ofString "mpt_hash_scratch"), .var .local (ofString "z")]))
          (.const (0#64)))
        .break .skip)
      (.assign .local (ofString "z") (.op .add [.var .local (ofString "z"), .const (1#64)])))

private theorem eval_encodeAcctZeroLoopCsr {F : Type} :
    ∀ (k : Nat) (s : PanSemStateFiniteExact 64 F) (zw : BitVec 64),
      s.clock = k →
      s.locals.lookup (ofString "z") = some (.val (.word zw)) →
      zw.toNat ≤ 32 →
      (evaluateHOLFiniteState s encodeAcctZeroLoopCsr).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState s encodeAcctZeroLoopCsr).1 = none →
        ∃ zw' : BitVec 64,
          zw'.toNat ≤ 32 ∧
          (evaluateHOLFiniteState s encodeAcctZeroLoopCsr).2.locals =
            s.locals.update (ofString "z", .val (.word zw')) ∧
          (evaluateHOLFiniteState s encodeAcctZeroLoopCsr).2 =
            { s with locals := (evaluateHOLFiniteState s encodeAcctZeroLoopCsr).2.locals,
                     clock := (evaluateHOLFiniteState s encodeAcctZeroLoopCsr).2.clock }) ∧
      ((evaluateHOLFiniteState s encodeAcctZeroLoopCsr).1 ≠ none →
        ¬ Resumes (evaluateHOLFiniteState s encodeAcctZeroLoopCsr).1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro s zw hclk hz hzw_le hnt
    unfold encodeAcctZeroLoopCsr at hnt ⊢
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    have hcond : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .lower (.var .local (ofString "z")) (.const (32#64))) =
        some (.val (.word (if zw.toNat < 32 then 1 else 0))) := by
      simp [evalHOLFinite, evalHOLExact, hz, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hlt : zw.toNat < 32
    · rw [if_pos hlt, if_pos (by decide : (1 : BitVec 64) ≠ 0)] at hnt ⊢
      by_cases hk0 : s.clock = 0
      · simp [hk0] at hnt
      · rw [if_neg hk0] at hnt ⊢
        let sd := decClockHOLFinite s
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
        rcases hev_lb : @evalHOLExact 64 F _ sd.toExact (fun a => Classical.propDecidable (sd.memaddrs a))
            (.cmp .notEqual
              (.loadByte (.op .add [.var .global (ofString "mpt_hash_scratch"), .var .local (ofString "z")]))
              (.const (0#64))) with _ | cv
        · simp [sd, hev_lb] at hnt ⊢; exact not_resumes_err_csr
        · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try (simp [sd, hev_lb] at hnt ⊢; exact not_resumes_err_csr)
          simp only [sd, hev_lb] at hnt ⊢
          by_cases hcw0 : cw = 0
          · rw [if_pos hcw0, evaluateHOLFiniteState_skip] at hnt ⊢; dsimp only at hnt ⊢
            have hsd_z : (decClockHOLFinite s).locals.lookup (ofString "z") = some (.val (.word zw)) := hz
            have hasg : evaluateHOLFiniteState (decClockHOLFinite s)
                (.assign .local (ofString "z") (.op .add [.var .local (ofString "z"), .const (1#64)])) =
                (none, setVarHOLFinite (ofString "z") (.val (.word (zw + 1#64))) (decClockHOLFinite s)) := by
              simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hsd_z,
                wordOpHOL, wordOp, valueIsWord, valueWord, isValidValueHOLExact, lookupKvarHOLExact,
                shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]
            rw [hasg] at hnt ⊢; dsimp only at hnt ⊢
            let s1 := setVarHOLFinite (ofString "z") (.val (.word (zw + 1#64))) (decClockHOLFinite s)
            have hs1_clk : s1.clock < k := by simp [s1, setVarHOLFinite, decClockHOLFinite, hclk]; omega
            have hs1_z : s1.locals.lookup (ofString "z") = some (.val (.word (zw + 1#64))) := by
              simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have hzw1 : (zw + 1#64).toNat = zw.toNat + 1 :=
              BitVec.toNat_add_of_lt (by change zw.toNat + 1 < 2 ^ 64; omega)
            obtain ⟨ih1, ih2⟩ := ih s1.clock hs1_clk s1 (zw + 1#64) rfl hs1_z (by omega) hnt
            refine ⟨fun hn => ?_, ih2⟩
            obtain ⟨zw', hle', hloc', heq'⟩ := ih1 hn
            refine ⟨zw', hle', ?_, ?_⟩
            · change (evaluateHOLFiniteState s1 encodeAcctZeroLoopCsr).2.locals = _
              rw [hloc']
              apply HolFiniteMapExact.ext_lookup; intro m
              by_cases hm : m = ofString "z"
              · subst hm; simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              · simp [s1, setVarHOLFinite, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  hm, Ne.symm hm]
            · change (evaluateHOLFiniteState s1 encodeAcctZeroLoopCsr).2 =
                { s with locals := (evaluateHOLFiniteState s1 encodeAcctZeroLoopCsr).2.locals,
                         clock := (evaluateHOLFiniteState s1 encodeAcctZeroLoopCsr).2.clock }
              rw [heq']; simp [s1, encodeAcctZeroLoopCsr, setVarHOLFinite, decClockHOLFinite]
          · rw [if_neg hcw0, evaluateHOLFiniteState_break]
            dsimp only
            refine ⟨fun _ => ⟨zw, hzw_le, ?_, by cases s; rfl⟩, fun h => False.elim (h rfl)⟩
            apply HolFiniteMapExact.ext_lookup; intro m
            by_cases hm : m = ofString "z"
            · subst hm; simp [decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hz]
            · simp [decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm, Ne.symm hm]
    · rw [if_neg hlt, if_neg (by decide : ¬ ((0 : BitVec 64) ≠ 0))]
      refine ⟨fun _ => ⟨zw, hzw_le, ?_, by cases s; rfl⟩, fun h => False.elim (h rfl)⟩
      apply HolFiniteMapExact.ext_lookup; intro m
      by_cases hm : m = ofString "z"
      · subst hm; simp [HolFiniteMapExact.lookup_update, FUPDATE, hz]
      · simp [HolFiniteMapExact.lookup_update, FUPDATE, hm, Ne.symm hm]

private theorem eval_decCall_rlp_encode_word_returned_csr {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (dstExp wExp : ExpHOL 64)
    (cont : ProgHOL 64) (v : ValueHOL 64)
    (hcode : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_encode_word") [dstExp, wExp] cont)).1 ≠ some .timeOut)
    (hret : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_encode_word") [dstExp, wExp] cont)).1 = some (.returned v)) :
    ∃ (dst0 r : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
        some (.val (.word dst0)) ∧
      1 ≤ r.toNat ∧ r.toNat ≤ 9 ∧
      ByteEff s mid [(dst0.toNat, 9)] ∧
      mid.locals = s.locals.update (ofString lname, .val (.word r)) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState mid cont).1 = some (.returned v) := by
  have hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_encode_word") [dstExp, wExp] cont)).1 :=
    Or.inl ⟨v, hret⟩
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hret hres
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, wExp] with _ | vals
  · simp [evalListHOLFinite, hargs] at hret
  · simp only [evalListHOLFinite, hargs] at hnt hret hres
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "rlp_encode_word") vals with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hret
    · simp only [hl] at hnt hret hres
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "rlp_encode_word")
        _ _ body' _ ret' vals callee (by rw [hcode]; exact lookup_rlp_encode_word) hl
      have hrspec := lookupCodeHOLFinite_installed_return s (ofString "rlp_encode_word")
        _ _ body' _ ret' vals callee (by rw [hcode]; exact lookup_rlp_encode_word) hl
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_encode_word") vals =
          some (body', callee, ret') := by rw [← hcode]; exact hl
      subst hsame; subst hrspec
      obtain ⟨dst0, w0, rfl, hc_dst, hc_w⟩ := lookupCode_two_words (by decide)
        lookup_rlp_encode_word hl_orig
      simp only [evalListHOLExact, Option.some.injEq, List.cons.injEq] at hargs
      rcases hv1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp with _ | v1
      · simp [hv1] at hargs
      · rcases hv2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) wExp with _ | v2
        · simp [hv1, hv2] at hargs
        · simp only [hv1, hv2, Option.some.injEq, List.cons.injEq, and_true] at hargs
          obtain ⟨rfl, rfl⟩ := hargs
          by_cases hz : s.clock = 0
          · simp [hz] at hnt
          · rw [if_neg hz] at hnt hret
            set ent := callEntryStateHOLFinite s callee
            rcases hrun : evaluateHOLFiniteState ent
                (sourceFnBody Guest.Software.guestFn_rlp_encode_word) with ⟨rb, pb⟩
            have hnt_b : rb ≠ some .timeOut := by rintro rfl; simp [hrun] at hnt
            have hres_b : Resumes rb := by
              cases rb with
              | none => simp [hrun] at hret
              | some cr =>
                cases cr with
                | returned rv => exact Or.inl ⟨rv, rfl⟩
                | exception _ _ => simp [hrun] at hret
                | _ => simp [hrun] at hret
            obtain ⟨r, hrb, hr1, hr9, _, heff_b⟩ := eval_rlp_encode_word_body ent dst0 w0 [(dst0.toNat, 9)]
              hcode (guestInv_callEntry s callee hG) hc_dst hc_w
              ⟨(dst0.toNat, 9), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩
              (by rw [hrun]; exact hnt_b) (by rw [hrun]; exact hres_b)
            rw [hrun] at hrb heff_b; dsimp only at hrb heff_b; subst hrb
            have hsh_r : (shapeEqHOL (shapeOfHOLExact (.val (.word r) : ValueHOL 64)) .one &&
                shapeEqHOL (shapeOfHOLExact (.val (.word r) : ValueHOL 64)) .one) = true := by
              simp [shapeOfHOLExact, shapeEqHOL]
            rw [hrun] at hnt hret; dsimp only at hnt hret; rw [if_pos hsh_r] at hnt hret
            let mid := setVarHOLFinite (ofString lname) (.val (.word r)) { pb with locals := s.locals }
            exact ⟨dst0, r, mid, rfl, hr1, hr9,
              (((ByteEff.refl s _).locals_clock _ _).trans heff_b).locals_clock _ _,
              rfl, hnt, hret⟩

private theorem eval_decCall_rlp_encode_bytes_returned_csr {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (dstExp srcExp nExp : ExpHOL 64)
    (dst0 n0 : BitVec 64) (cont : ProgHOL 64) (v : ValueHOL 64)
    (hcode : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hdst_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hn_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n0)))
    (hn_le : n0.toNat ≤ 55)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_encode_bytes") [dstExp, srcExp, nExp] cont)).1 ≠ some .timeOut)
    (hret : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_encode_bytes") [dstExp, srcExp, nExp] cont)).1 = some (.returned v)) :
    ∃ (r : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      1 ≤ r.toNat ∧ r.toNat ≤ n0.toNat + 1 ∧
      ByteEff s mid [(dst0.toNat, n0.toNat + 1)] ∧
      mid.locals = s.locals.update (ofString lname, .val (.word r)) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState mid cont).1 = some (.returned v) := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hret
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, srcExp, nExp] with _ | vals
  · simp [evalListHOLFinite, hargs] at hret
  · simp only [evalListHOLFinite, hargs] at hnt hret
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "rlp_encode_bytes") vals with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hret
    · simp only [hl] at hnt hret
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "rlp_encode_bytes")
        _ _ body' _ ret' vals callee (by rw [hcode]; exact lookup_rlp_encode_bytes) hl
      have hrspec := lookupCodeHOLFinite_installed_return s (ofString "rlp_encode_bytes")
        _ _ body' _ ret' vals callee (by rw [hcode]; exact lookup_rlp_encode_bytes) hl
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_encode_bytes") vals =
          some (body', callee, ret') := by rw [← hcode]; exact hl
      subst hsame; subst hrspec
      obtain ⟨d', src0, n', hvals_eq, hc_dst, hc_src, hc_n⟩ := lookupCode_three_words
        (by decide) (by decide) (by decide) lookup_rlp_encode_bytes hl_orig
      subst hvals_eq
      rcases hv2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) srcExp with _ | v2
      · simp [evalListHOLExact, hdst_ev, hv2] at hargs
      · simp only [evalListHOLExact, hdst_ev, hv2, hn_ev, Option.some.injEq, List.cons.injEq, and_true,
          ValueHOL.val.injEq, HolWordLab.word.injEq] at hargs
        obtain ⟨rfl, rfl, rfl⟩ := hargs
        by_cases hz : s.clock = 0
        · simp [hz] at hnt
        · rw [if_neg hz] at hnt hret
          set ent := callEntryStateHOLFinite s callee
          rcases hrun : evaluateHOLFiniteState ent
              (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes) with ⟨rb, pb⟩
          have hnt_b : rb ≠ some .timeOut := by rintro rfl; simp [hrun] at hnt
          have hres_b : Resumes rb := by
            cases rb with
            | none => simp [hrun] at hret
            | some cr =>
              cases cr with
              | returned rv => exact Or.inl ⟨rv, rfl⟩
              | exception _ _ => simp [hrun] at hret
              | _ => simp [hrun] at hret
          obtain ⟨r, hrb, hr1, hrhi, _, heff_b⟩ := eval_rlp_encode_bytes_bounded ent dst0 src0 n0
            [(dst0.toNat, n0.toNat + 1)] hcode (guestInv_callEntry s callee hG) hc_dst hc_src hc_n hn_le
            ⟨(dst0.toNat, n0.toNat + 1), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩
            (by rw [hrun]; exact hnt_b) (by rw [hrun]; exact hres_b)
          rw [hrun] at hrb heff_b; dsimp only at hrb heff_b; subst hrb
          have hsh_r : (shapeEqHOL (shapeOfHOLExact (.val (.word r) : ValueHOL 64)) .one &&
              shapeEqHOL (shapeOfHOLExact (.val (.word r) : ValueHOL 64)) .one) = true := by
            simp [shapeOfHOLExact, shapeEqHOL]
          rw [hrun] at hnt hret; dsimp only at hnt hret; rw [if_pos hsh_r] at hnt hret
          let mid := setVarHOLFinite (ofString lname) (.val (.word r)) { pb with locals := s.locals }
          exact ⟨r, mid, hr1, hrhi,
            (((ByteEff.refl s _).locals_clock _ _).trans heff_b).locals_clock _ _,
            rfl, hnt, hret⟩

private theorem call0_be64_meta {F : Type}
    (cur : PanSemStateFiniteExact 64 F) (pExp vExp : ExpHOL 64) :
    ((evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "st_be64") [pExp, vExp])).1 ≠ none →
      ∀ v, (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "st_be64") [pExp, vExp])).1 ≠
        some (.returned v)) ∧
    ((evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "st_be64") [pExp, vExp])).1 = none →
      (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "st_be64") [pExp, vExp])).2.locals = cur.locals ∧
      (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "st_be64") [pExp, vExp])).2.code = cur.code ∧
      (GuestInv cur → GuestInv (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "st_be64") [pExp, vExp])).2)) := by
  have hmeta := evaluateHOLFiniteState_metadata cur (.call (some (none, none)) (ofString "st_be64") [pExp, vExp])
  refine ⟨fun hne v hrv => ?_, fun hnone => ?_⟩
  · rw [evaluateHOLFiniteState_call] at hne hrv
    rcases ha : @evalListHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
        [pExp, vExp] with _ | vals
    · simp [evalListHOLFinite, ha] at hrv
    · simp only [evalListHOLFinite, ha] at hne hrv
      rcases hl : lookupCodeHOLFinite cur.code.lookup (ofString "st_be64") vals with _ | ⟨b, c, rs⟩
      · simp [hl] at hrv
      · simp only [hl] at hne hrv
        by_cases hclk : cur.clock = 0
        · simp [hclk] at hrv
        · rw [if_neg hclk] at hne hrv
          rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite cur c) b with ⟨rb, pb⟩
          rw [hrun] at hne hrv
          cases rb with
          | none => simp at hrv
          | some rb' =>
            cases rb' with
            | returned rv =>
              dsimp only at hne hrv
              split at hrv
              · rename_i hsh; rw [if_pos hsh] at hne; exact hne rfl
              · simp at hrv
            | exception _ _ => simp at hrv
            | _ => simp at hrv
  · exact ⟨call0_locals_r16 cur (ofString "st_be64") [pExp, vExp] hnone,
      hmeta.1, fun hG => guestInv_evaluate cur (.call (some (none, none)) (ofString "st_be64") [pExp, vExp]) hG⟩

theorem rv_encode_account_csr : RetLe (fun _ => 110) (ofString "encode_account") := by
  refine ⟨_, _, _, lookup_encode_account, fun {F} s hcode hGI _ hnt v hret => ?_⟩
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_encode_account,
    FrontendCodecComputation.declToHOLStructural, FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural, FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil, List.map] at hnt hret
  rw [evaluateHOLFiniteState_dec_total] at hnt hret
  simp only [evalHOLExact, shapeEqHOL, shapeOfHOLExact, ↓reduceIte] at hnt hret
  let s0 := setVarHOLFinite (ofString "off") (.val (.word (2#64))) s
  have hs0_code : s0.code = originalRuntimeCode := hcode
  have hGs0 : GuestInv s0 := guestInv_setVar _ _ s hGI
  have hs0_off : s0.locals.lookup (ofString "off") = some (.val (.word (2#64))) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs0_other : ∀ m, m ≠ ofString "off" → s0.locals.lookup m = s.locals.lookup m := fun m hm => by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm, Ne.symm hm]
  obtain ⟨dst1, w1, s1, hdst1_ev, hw1_lo, hw1_hi, heff1, hs1_loc, hnt1, hret1⟩ :=
    eval_decCall_rlp_encode_word_returned_csr s0 "w"
      (.op .add [.var .local (ofString "out"), .var .local (ofString "off")])
      (.var .local (ofString "nonce")) _ v hs0_code hGs0 hnt hret
  have hout_ex : ∃ out0 : BitVec 64, s.locals.lookup (ofString "out") = some (.val (.word out0)) := by
    have hout_s0 := hs0_other (ofString "out") (by decide)
    rcases hout_lk : s.locals.lookup (ofString "out") with _ | ov
    · simp [evalHOLExact, evalListHOLExact, hout_s0, hout_lk, hs0_off] at hdst1_ev
    · rcases ov with ⟨⟨out0⟩⟩ | _ | _
      · exact ⟨out0, rfl⟩
      · simp [evalHOLExact, evalListHOLExact, hout_s0, hout_lk, hs0_off, valueIsWord] at hdst1_ev
      · simp [evalHOLExact, evalListHOLExact, hout_s0, hout_lk, hs0_off, valueIsWord] at hdst1_ev
  obtain ⟨out0, hs_out⟩ := hout_ex
  have hs1_code : s1.code = originalRuntimeCode := heff1.code.trans hs0_code
  have hGs1 : GuestInv s1 := guestInv_congr heff1.code heff1.memaddrs heff1.shMemaddrs heff1.baseAddr hGs0
  have hs1_off : s1.locals.lookup (ofString "off") = some (.val (.word (2#64))) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs0_off, show ofString "w" ≠ ofString "off" by decide]
  have hs1_w : s1.locals.lookup (ofString "w") = some (.val (.word w1)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  -- `off = off + w1`
  rw [evaluateHOLFiniteState_seq_line780] at hnt1 hret1
  have hasg1 : evaluateHOLFiniteState s1
      (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "w")])) =
      (none, setVarHOLFinite (ofString "off") (.val (.word ((2#64) + w1))) s1) := by
    simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hs1_off, hs1_w,
      wordOpHOL, wordOp, valueIsWord, valueWord, isValidValueHOLExact, lookupKvarHOLExact,
      shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]
  rw [hasg1] at hnt1 hret1; dsimp only at hnt1 hret1
  set off2 := (2#64) + w1
  have hoff2_nat : off2.toNat = 2 + w1.toNat := BitVec.toNat_add_of_lt (by change 2 + w1.toNat < 2 ^ 64; omega)
  set s2 := setVarHOLFinite (ofString "off") (.val (.word off2)) s1
  have hs2_code : s2.code = originalRuntimeCode := hs1_code
  have hGs2 : GuestInv s2 := guestInv_setVar _ _ s1 hGs1
  -- 4x `st_be64` calls:
  rw [evaluateHOLFiniteState_seq_line780] at hnt1 hret1
  have hm_be0 := call0_be64_meta s2 (.var .global (ofString "mpt_hash_scratch")) (.rfield 3 (.var .local (ofString "balance")))
  rcases hbe0 : evaluateHOLFiniteState s2 (.call (some (none, none)) (ofString "st_be64")
      [.var .global (ofString "mpt_hash_scratch"), .rfield 3 (.var .local (ofString "balance"))]) with ⟨rbe0, s3⟩
  rw [hbe0] at hnt1 hret1 hm_be0
  cases rbe0 with
  | some _ => dsimp only at hret1; exact False.elim (hm_be0.1 (by simp) v hret1)
  | none =>
    dsimp only at hnt1 hret1 hm_be0
    obtain ⟨hs3_loc, hs3_code', hs3_G⟩ := hm_be0.2 rfl
    have hs3_code : s3.code = originalRuntimeCode := hs3_code'.trans hs2_code
    have hGs3 : GuestInv s3 := hs3_G hGs2
    rw [evaluateHOLFiniteState_seq_line780] at hnt1 hret1
    have hm_be1 := call0_be64_meta s3 (.op .add [.var .global (ofString "mpt_hash_scratch"), .const (8#64)])
        (.rfield 2 (.var .local (ofString "balance")))
    rcases hbe1 : evaluateHOLFiniteState s3 (.call (some (none, none)) (ofString "st_be64")
        [.op .add [.var .global (ofString "mpt_hash_scratch"), .const (8#64)],
         .rfield 2 (.var .local (ofString "balance"))]) with ⟨rbe1, s4⟩
    rw [hbe1] at hnt1 hret1 hm_be1
    cases rbe1 with
    | some _ => dsimp only at hret1; exact False.elim (hm_be1.1 (by simp) v hret1)
    | none =>
      dsimp only at hnt1 hret1 hm_be1
      obtain ⟨hs4_loc', hs4_code', hs4_G⟩ := hm_be1.2 rfl
      have hs4_loc : s4.locals = s2.locals := hs4_loc'.trans hs3_loc
      have hs4_code : s4.code = originalRuntimeCode := hs4_code'.trans hs3_code
      have hGs4 : GuestInv s4 := hs4_G hGs3
      rw [evaluateHOLFiniteState_seq_line780] at hnt1 hret1
      have hm_be2 := call0_be64_meta s4 (.op .add [.var .global (ofString "mpt_hash_scratch"), .const (16#64)])
          (.rfield 1 (.var .local (ofString "balance")))
      rcases hbe2 : evaluateHOLFiniteState s4 (.call (some (none, none)) (ofString "st_be64")
          [.op .add [.var .global (ofString "mpt_hash_scratch"), .const (16#64)],
           .rfield 1 (.var .local (ofString "balance"))]) with ⟨rbe2, s5⟩
      rw [hbe2] at hnt1 hret1 hm_be2
      cases rbe2 with
      | some _ => dsimp only at hret1; exact False.elim (hm_be2.1 (by simp) v hret1)
      | none =>
        dsimp only at hnt1 hret1 hm_be2
        obtain ⟨hs5_loc', hs5_code', hs5_G⟩ := hm_be2.2 rfl
        have hs5_loc : s5.locals = s2.locals := hs5_loc'.trans hs4_loc
        have hs5_code : s5.code = originalRuntimeCode := hs5_code'.trans hs4_code
        have hGs5 : GuestInv s5 := hs5_G hGs4
        rw [evaluateHOLFiniteState_seq_line780] at hnt1 hret1
        have hm_be3 := call0_be64_meta s5 (.op .add [.var .global (ofString "mpt_hash_scratch"), .const (24#64)])
            (.rfield 0 (.var .local (ofString "balance")))
        rcases hbe3 : evaluateHOLFiniteState s5 (.call (some (none, none)) (ofString "st_be64")
            [.op .add [.var .global (ofString "mpt_hash_scratch"), .const (24#64)],
             .rfield 0 (.var .local (ofString "balance"))]) with ⟨rbe3, s6⟩
        rw [hbe3] at hnt1 hret1 hm_be3
        cases rbe3 with
        | some _ => dsimp only at hret1; exact False.elim (hm_be3.1 (by simp) v hret1)
        | none =>
          dsimp only at hnt1 hret1 hm_be3
          obtain ⟨hs6_loc', hs6_code', hs6_G⟩ := hm_be3.2 rfl
          have hs6_loc : s6.locals = s2.locals := hs6_loc'.trans hs5_loc
          have hs6_code : s6.code = originalRuntimeCode := hs6_code'.trans hs5_code
          have hGs6 : GuestInv s6 := hs6_G hGs5
          -- `dec "z" 0` + `encodeAcctZeroLoopCsr`
          rw [evaluateHOLFiniteState_dec_total] at hnt1 hret1
          simp only [evalHOLExact, shapeEqHOL, shapeOfHOLExact, ↓reduceIte] at hnt1 hret1
          set s7 := setVarHOLFinite (ofString "z") (.val (.word (0#64))) s6
          have hs7_z : s7.locals.lookup (ofString "z") = some (.val (.word (0#64))) := by
            simp [s7, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          rw [evaluateHOLFiniteState_seq_line780] at hnt1 hret1
          rcases hzl : evaluateHOLFiniteState s7 encodeAcctZeroLoopCsr with ⟨rzl, s8⟩
          have hzl' : evaluateHOLFiniteState s7
              (.while (.cmp .lower (.var .local (ofString "z")) (.const (32#64)))
                (.seq
                  (.ite (.cmp .notEqual
                      (.loadByte (.op .add [.var .global (ofString "mpt_hash_scratch"), .var .local (ofString "z")]))
                      (.const (0#64)))
                    .break .skip)
                  (.assign .local (ofString "z") (.op .add [.var .local (ofString "z"), .const (1#64)])))) =
              (rzl, s8) := hzl
          rw [hzl'] at hnt1 hret1
          have hnt_zl : rzl ≠ some .timeOut := by rintro rfl; simp at hnt1
          have hzl_spec := eval_encodeAcctZeroLoopCsr s7.clock s7 (0#64) rfl hs7_z (by decide) (by rw [hzl]; exact hnt_zl)
          rw [hzl] at hzl_spec
          cases rzl with
          | some rzl' =>
            dsimp only at hret1
            exfalso
            apply hzl_spec.2 (by simp)
            exact Or.inl ⟨v, by simpa using hret1⟩
          | none =>
            dsimp only at hnt1 hret1 hzl_spec
            obtain ⟨zw, hzw_le, hs8_loc, hs8_eq⟩ := hzl_spec.1 rfl
            have hs8_code : s8.code = originalRuntimeCode := by rw [hs8_eq]; exact hs6_code
            have hGs8 : GuestInv s8 := by
              rw [hs8_eq]; exact guestInv_with_locals_clock s7 _ _ (guestInv_setVar _ _ s6 hGs6)
            have hs8_z : s8.locals.lookup (ofString "z") = some (.val (.word zw)) := by
              rw [hs8_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
            have hs8_other : ∀ m, m ≠ ofString "z" → s8.locals.lookup m = s2.locals.lookup m := by
              intro m hm
              rw [hs8_loc]; simp [s7, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm, Ne.symm hm, hs6_loc]
            have hs8_out : s8.locals.lookup (ofString "out") = some (.val (.word out0)) := by
              rw [hs8_other _ (by decide)]
              simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "off" ≠ ofString "out" by decide, hs1_loc,
                show ofString "w" ≠ ofString "out" by decide,
                hs0_other (ofString "out") (by decide), hs_out]
            have hs8_off : s8.locals.lookup (ofString "off") = some (.val (.word off2)) := by
              rw [hs8_other _ (by decide)]
              simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have h32z_nat : ((32#64) - zw).toNat = 32 - zw.toNat := by
              rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hzw_le)]; rfl
            -- `wb = rlp_encode_bytes(...)`
            obtain ⟨wb, s9, hwb_lo, hwb_hi, heff_wb, hs9_loc, hnt9, hret9⟩ :=
              eval_decCall_rlp_encode_bytes_returned_csr s8 "wb"
                (.op .add [.var .local (ofString "out"), .var .local (ofString "off")])
                (.op .add [.var .global (ofString "mpt_hash_scratch"), .var .local (ofString "z")])
                (.op .sub [.const (32#64), .var .local (ofString "z")])
                (out0 + off2) ((32#64) - zw) _ v hs8_code hGs8
                (by simp [evalHOLExact, evalListHOLExact, hs8_out, hs8_off, wordOpHOL, wordOp, valueIsWord, valueWord])
                (by simp [evalHOLExact, evalListHOLExact, hs8_z, wordOpHOL, wordOp, valueIsWord, valueWord])
                (by omega) hnt1 hret1
            have hwb_33 : wb.toNat ≤ 33 := by rw [h32z_nat] at hwb_hi; omega
            have hs9_code : s9.code = originalRuntimeCode := heff_wb.code.trans hs8_code
            have hGs9 : GuestInv s9 := guestInv_congr heff_wb.code heff_wb.memaddrs heff_wb.shMemaddrs heff_wb.baseAddr hGs8
            have hs9_off : s9.locals.lookup (ofString "off") = some (.val (.word off2)) := by
              rw [hs9_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs8_off, show ofString "wb" ≠ ofString "off" by decide]
            have hs9_wb : s9.locals.lookup (ofString "wb") = some (.val (.word wb)) := by
              rw [hs9_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
            rw [evaluateHOLFiniteState_seq_line780] at hnt9 hret9
            have hasg_off2 : evaluateHOLFiniteState s9
                (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "wb")])) =
                (none, setVarHOLFinite (ofString "off") (.val (.word (off2 + wb))) s9) := by
              simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hs9_off, hs9_wb,
                wordOpHOL, wordOp, valueIsWord, valueWord, isValidValueHOLExact, lookupKvarHOLExact,
                shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]
            rw [hasg_off2] at hnt9 hret9; dsimp only at hnt9 hret9
            set off3 := off2 + wb
            have hoff3_nat : off3.toNat = off2.toNat + wb.toNat :=
              BitVec.toNat_add_of_lt (by change off2.toNat + wb.toNat < 2 ^ 64; omega)
            set s10 := setVarHOLFinite (ofString "off") (.val (.word off3)) s9
            have hs10_code : s10.code = originalRuntimeCode := hs9_code
            have hGs10 : GuestInv s10 := guestInv_setVar _ _ s9 hGs9
            have hs10_out : s10.locals.lookup (ofString "out") = some (.val (.word out0)) := by
              simp [s10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "off" ≠ ofString "out" by decide, hs9_loc,
                show ofString "wb" ≠ ofString "out" by decide, hs8_out]
            have hs10_off : s10.locals.lookup (ofString "off") = some (.val (.word off3)) := by
              simp [s10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            -- `wsl = rlp_encode_bytes(...)`
            have h32_lit : (32#64).toNat = 32 := rfl
            obtain ⟨wsl, s11, hwsl_lo, hwsl_hi, heff_wsl, hs11_loc, hnt11, hret11⟩ :=
              eval_decCall_rlp_encode_bytes_returned_csr s10 "wsl"
                (.op .add [.var .local (ofString "out"), .var .local (ofString "off")])
                (.var .local (ofString "storage_root")) (.const (32#64))
                (out0 + off3) (32#64) _ v hs10_code hGs10
                (by simp [evalHOLExact, evalListHOLExact, hs10_out, hs10_off, wordOpHOL, wordOp, valueIsWord, valueWord])
                rfl (by decide) hnt9 hret9
            have hwsl_33 : wsl.toNat ≤ 33 := by rw [h32_lit] at hwsl_hi; omega
            have hs11_code : s11.code = originalRuntimeCode := heff_wsl.code.trans hs10_code
            have hGs11 : GuestInv s11 := guestInv_congr heff_wsl.code heff_wsl.memaddrs heff_wsl.shMemaddrs heff_wsl.baseAddr hGs10
            have hs11_off : s11.locals.lookup (ofString "off") = some (.val (.word off3)) := by
              rw [hs11_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs10_off, show ofString "wsl" ≠ ofString "off" by decide]
            have hs11_wsl : s11.locals.lookup (ofString "wsl") = some (.val (.word wsl)) := by
              rw [hs11_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
            rw [evaluateHOLFiniteState_seq_line780] at hnt11 hret11
            have hasg_off3 : evaluateHOLFiniteState s11
                (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "wsl")])) =
                (none, setVarHOLFinite (ofString "off") (.val (.word (off3 + wsl))) s11) := by
              simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hs11_off, hs11_wsl,
                wordOpHOL, wordOp, valueIsWord, valueWord, isValidValueHOLExact, lookupKvarHOLExact,
                shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]
            rw [hasg_off3] at hnt11 hret11; dsimp only at hnt11 hret11
            set off4 := off3 + wsl
            have hoff4_nat : off4.toNat = off3.toNat + wsl.toNat :=
              BitVec.toNat_add_of_lt (by change off3.toNat + wsl.toNat < 2 ^ 64; omega)
            set s12 := setVarHOLFinite (ofString "off") (.val (.word off4)) s11
            have hs12_code : s12.code = originalRuntimeCode := hs11_code
            have hGs12 : GuestInv s12 := guestInv_setVar _ _ s11 hGs11
            have hs12_out : s12.locals.lookup (ofString "out") = some (.val (.word out0)) := by
              simp [s12, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "off" ≠ ofString "out" by decide, hs11_loc,
                show ofString "wsl" ≠ ofString "out" by decide, hs10_out]
            have hs12_off : s12.locals.lookup (ofString "off") = some (.val (.word off4)) := by
              simp [s12, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            -- `wc = rlp_encode_bytes(...)`
            obtain ⟨wc, s13, hwc_lo, hwc_hi, heff_wc, hs13_loc, hnt13, hret13⟩ :=
              eval_decCall_rlp_encode_bytes_returned_csr s12 "wc"
                (.op .add [.var .local (ofString "out"), .var .local (ofString "off")])
                (.var .local (ofString "code_hash")) (.const (32#64))
                (out0 + off4) (32#64) _ v hs12_code hGs12
                (by simp [evalHOLExact, evalListHOLExact, hs12_out, hs12_off, wordOpHOL, wordOp, valueIsWord, valueWord])
                rfl (by decide) hnt11 hret11
            have hwc_33 : wc.toNat ≤ 33 := by rw [h32_lit] at hwc_hi; omega
            have hs13_off : s13.locals.lookup (ofString "off") = some (.val (.word off4)) := by
              rw [hs13_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs12_off, show ofString "wc" ≠ ofString "off" by decide]
            have hs13_wc : s13.locals.lookup (ofString "wc") = some (.val (.word wc)) := by
              rw [hs13_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
            rw [evaluateHOLFiniteState_seq_line780] at hnt13 hret13
            have hasg_off4 : evaluateHOLFiniteState s13
                (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "wc")])) =
                (none, setVarHOLFinite (ofString "off") (.val (.word (off4 + wc))) s13) := by
              simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hs13_off, hs13_wc,
                wordOpHOL, wordOp, valueIsWord, valueWord, isValidValueHOLExact, lookupKvarHOLExact,
                shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]
            rw [hasg_off4] at hnt13 hret13; dsimp only at hnt13 hret13
            set off5 := off4 + wc
            have hoff5_nat : off5.toNat = off4.toNat + wc.toNat :=
              BitVec.toNat_add_of_lt (by change off4.toNat + wc.toNat < 2 ^ 64; omega)
            set s14 := setVarHOLFinite (ofString "off") (.val (.word off5)) s13
            have hs14_off : s14.locals.lookup (ofString "off") = some (.val (.word off5)) := by
              simp [s14, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            -- `st8 out, 248; st8 (out + 1), (off - 2); return off`
            rw [evaluateHOLFiniteState_seq_line780] at hret13
            have hcf1 := evaluate_storeByte_control_frame s14 (.var .local (ofString "out")) (.const (248#64))
            rcases hst1 : evaluateHOLFiniteState s14 (.storeByte (.var .local (ofString "out")) (.const (248#64))) with ⟨r248, s15⟩
            rw [hst1] at hcf1 hret13
            rcases hcf1.1 with rfl | rfl
            · dsimp only at hcf1 hret13
              have hs15_off : s15.locals.lookup (ofString "off") = some (.val (.word off5)) := by
                rw [hcf1.2.2.1]; exact hs14_off
              rw [evaluateHOLFiniteState_seq_line780] at hret13
              have hcf2 := evaluate_storeByte_control_frame s15
                (.op .add [.var .local (ofString "out"), .const (1#64)])
                (.op .sub [.var .local (ofString "off"), .const (2#64)])
              rcases hst2 : evaluateHOLFiniteState s15
                (.storeByte (.op .add [.var .local (ofString "out"), .const (1#64)])
                            (.op .sub [.var .local (ofString "off"), .const (2#64)])) with ⟨rlen, s16⟩
              rw [hst2] at hcf2 hret13
              rcases hcf2.1 with rfl | rfl
              · dsimp only at hcf2 hret13
                have hs16_off : s16.locals.lookup (ofString "off") = some (.val (.word off5)) := by
                  rw [hcf2.2.2.1]; exact hs15_off
                simp only [evaluateHOLFiniteState_return, evalHOLFinite, evalHOLExact,
                  PanSemStateFiniteExact.toExact, hs16_off, shapeOfHOLExact,
                  sizeOfShapeWithContextHOL] at hret13
                rw [if_pos (by decide : (1 : Nat) ≤ 32)] at hret13
                simp only [Option.some.injEq, PanSemResultExact.returned.injEq] at hret13
                subst hret13
                exact ⟨off5, rfl, by dsimp only; omega⟩
              · simp at hret13
            · simp at hret13

theorem mptObjInWith_with_locals_csr {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S Nm : List Nat) (m : Nat) :
    MptObjInWith {s with locals := locals, clock := k} S Nm m ↔
      MptObjInWith s S Nm m := Iff.rfl

theorem mptObjReady_of_parts_csr {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s) {S Nd Nm : List Nat}
    (hW : WorldTypedWith s S Nd)
    (hm : MptObjInWith s S Nm (locN s "m"))
    (hd : IvlsDisj (mptObjIvls s Nm (locN s "m")) (nodeExtents s Nd)) :
    MptObjReady s := by
  have hobj : (locN s "m", 16) ∈ mptObjIvls s Nm (locN s "m") := by
    simp [mptObjIvls]
  refine ⟨hA, S, (worldTyped_iff_with s S).2 ⟨Nd, hW⟩,
    ⟨Nm, hm⟩, by simp, ⟨Nd, hW.2.2.2, ?_⟩, Nm, Nd, hm, hW.2.2.2, ?_⟩
  · intro o ho j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    subst o
    exact hd _ hobj j hj
  · intro o ho j hj
    apply hd o ?_ j hj
    simpa [mptObjIvls] using ho

theorem mptSetReady_of_parts_csr {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s) {S Nd Nm : List Nat}
    (hW : WorldTypedWith s S Nd)
    (hm : MptObjInWith s S Nm (locN s "m"))
    (hd : IvlsDisj (mptObjIvls s Nm (locN s "m")) (nodeExtents s Nd))
    (hk : locN s "klen" ≤ 32) (hv : locN s "vlen" ≤ 110) :
    MptSetReady s := by
  exact ⟨mptObjReady_of_parts_csr hA hW hm hd, hk, by omega⟩

theorem mptObjInWith_of_parts_csr {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd Nm : List Nat} {m : Nat}
    (ha : Allocated s (m, 16)) (hw : WordsOK s (m, 16))
    (hn : NodeHeap s Nm) (hr : RootIn Nm (memW s m))
    (hd : IvlsDisj (mptObjIvls s Nm m) (worldOwned s S Nd))
    (hm : ∀ o ∈ nodeExtents s Nm, Disj o (m, 16)) :
    MptObjInWith s S Nm m := by
  have hobj : (m, 16) ∈ mptObjIvls s Nm m := by simp [mptObjIvls]
  have htab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, i ∈ worldOwned s S Nd := by
    intro t ht i hi
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
      (Or.inl (List.mem_flatMap.mpr ⟨t, ht, hi⟩))))
  have hfixed : ∀ i ∈ fixedObjects s, i ∈ worldOwned s S Nd := by
    intro i hi
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hi)))
  refine ⟨ha, hw, ?_, ?_, hn, hr, ?_⟩
  · intro t ht i hi
    exact hd _ hobj i (htab t ht i hi)
  · intro i hi
    exact hd _ hobj i (hfixed i hi)
  · intro o ho
    have hom : o ∈ mptObjIvls s Nm m := List.mem_cons_of_mem _ ho
    exact ⟨hm o ho, fun t ht i hi => hd o hom i (htab t ht i hi),
      fun i hi => hd o hom i (hfixed i hi)⟩

theorem mptObjInWith_mono_world_csr {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S T Nm : List Nat} {m : Nat} (hm : MptObjInWith s S Nm m)
    (hsub : ∀ t ∈ T, t ∈ S) : MptObjInWith s T Nm m := by
  obtain ⟨ha, hw, ht, hf, hn, hr, hd⟩ := hm
  exact ⟨ha, hw, fun t h => ht t (hsub t h), hf, hn, hr,
    fun o ho => ⟨(hd o ho).1,
      fun t h => (hd o ho).2.1 t (hsub t h), (hd o ho).2.2⟩⟩

theorem mptObjInWith_disj_world_csr {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd Nm : List Nat} {m : Nat} (hm : MptObjInWith s S Nm m)
    (hd : IvlsDisj (mptObjIvls s Nm m) (nodeExtents s Nd)) :
    IvlsDisj (mptObjIvls s Nm m) (worldOwned s S Nd) := by
  intro o ho j hj
  have ho_parts : Disj o j := by
    rcases List.mem_append.mp hj with hj | hj
    · rcases List.mem_append.mp hj with hj | hj
      · obtain ⟨t, ht, hj⟩ := List.mem_flatMap.mp hj
        rcases List.mem_cons.mp ho with rfl | ho
        · exact hm.2.2.1 t ht j hj
        · exact (hm.2.2.2.2.2.2 o ho).2.1 t ht j hj
      · rcases List.mem_cons.mp ho with rfl | ho
        · exact hm.2.2.2.1 j hj
        · exact (hm.2.2.2.2.2.2 o ho).2.2 j hj
    · exact hd o ho j hj
  exact ho_parts

theorem mptObjInWith_disj_buffer_csr {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nm : List Nat} {m : Nat} (hm : MptObjInWith s S Nm m)
    {gn : String × Nat} (hg : gn ∈ globalBuffers) :
    IvlsDisj [bufferRegion s gn] (mptObjIvls s Nm m) := by
  intro i hi o ho
  obtain rfl := List.mem_singleton.mp hi
  have hb : bufferRegion s gn ∈ fixedObjects s := by
    unfold fixedObjects
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
      (Or.inl (List.mem_append.mpr
        (Or.inl (List.mem_map.mpr ⟨gn, hg, rfl⟩))))))
  apply Disj.flip
  rcases List.mem_cons.mp ho with rfl | ho
  · exact hm.2.2.2.1 _ hb
  · exact (hm.2.2.2.2.2.2 o ho).2.2 _ hb

theorem mptObjStep_parts_csr {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    (hstep : MptObjStep R gw keep s post) {S Nd Nm : List Nat}
    (hW : WorldTypedWith s S Nd)
    (hm : MptObjInWith s S Nm (locN s "m"))
    (hd : IvlsDisj (mptObjIvls s Nm (locN s "m")) (nodeExtents s Nd))
    (hR : IvlsDisj (R s) (worldTypedIvls s S Nd ++ mptObjIvls s Nm (locN s "m")))
    (hRN : IvlsDisj (R s) (nodeExtents s Nd)) :
    ∃ S' Nd' Nm', (∀ t ∈ S, t ∈ S') ∧ WorldTypedWith post S' Nd' ∧
      MptObjInWith post S' Nm' (locN s "m") ∧
      IvlsDisj (mptObjIvls post Nm' (locN s "m")) (nodeExtents post Nd') ∧
      OwnedGrows s post (worldOwned s S Nd ++ mptObjIvls s Nm (locN s "m"))
        (worldOwned post S' Nd' ++ mptObjIvls post Nm' (locN s "m")) ∧
      FrameOutside s post
        (worldOwned s S Nd ++ mptObjIvls s Nm (locN s "m") ++ R s ++ [freeGap s])
        (heapFree s) := by
  apply hstep.2.2.2.2 S Nd Nm hW hm ?_ hR
  intro i hi j hj
  rcases List.mem_cons.mp hi with hi | hi
  · subst i
    exact hd _ (by simp [mptObjIvls]) j hj
  · rcases List.mem_append.mp hi with hi | hi
    · exact hRN i hi j hj
    · exact hd i (List.mem_cons_of_mem _ hi) j hj

theorem mptObjInWith_allocated_csr {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nm : List Nat} {m : Nat} (hm : MptObjInWith s S Nm m) :
    ∀ o ∈ mptObjIvls s Nm m, o.2 ≠ 0 → Allocated s o := by
  intro o ho hnz
  rcases List.mem_cons.mp ho with rfl | ho
  · exact hm.1
  · obtain ⟨n, hn, ho⟩ := List.mem_flatMap.mp ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact (hm.2.2.2.2.1.1 n hn).2.1
    · by_cases hp : (memW s n = 1 ∨ memW s n = 2) ∧ memW s (n + 40) ≠ 0
      · rw [show nodePath s n = (memW s (n + 32), memW s (n + 40)) from if_pos hp]
        rcases (hm.2.2.2.2.1.1 n hn).2.2.2.2.2.2.1 hp.1 with hz | hk
        · exact False.elim (hp.2 hz)
        · exact hk.2.1
      · rw [show nodePath s n = (0, 0) from if_neg hp] at hnz
        exact False.elim (hnz rfl)

theorem worldTypedWith_with_locals_csr {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S Nd : List Nat) :
    WorldTypedWith {s with locals := locals, clock := k} S Nd ↔
      WorldTypedWith s S Nd := by
  simp only [WorldTypedWith, tablesTyped_with_locals]
  exact Iff.rfl

theorem retMptObj_ready_csr {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {S Nd : List Nat}
    (hA : ArenaReady post) (hW : WorldTypedWith post S Nd)
    (hret : RetMptObj s r post S Nd) {v : ValueHOL 64}
    (hr : r = some (.returned v)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧
      ∀ (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat),
        locN {post with locals := locals, clock := k} "m" = w.toNat →
        MptObjReady {post with locals := locals, clock := k} := by
  obtain ⟨w, hv, _, Nm, hm, hd, _⟩ := hret v hr
  refine ⟨w, hv, fun locals k hl => ?_⟩
  apply mptObjReady_of_parts_csr
    ((arenaReady_with_locals post locals k).2 hA)
    (S := S) (Nd := Nd) (Nm := Nm)
  · exact (worldTypedWith_with_locals_csr post locals k S Nd).2 hW
  · rw [hl]
    exact hm
  · rw [hl]
    exact hd

theorem mptObjStep_ready_csr {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    (hstep : MptObjStep R gw keep s post) {S Nd Nm : List Nat}
    (hW : WorldTypedWith s S Nd)
    (hm : MptObjInWith s S Nm (locN s "m"))
    (hd : IvlsDisj (mptObjIvls s Nm (locN s "m")) (nodeExtents s Nd))
    (hR : IvlsDisj (R s) (worldTypedIvls s S Nd ++ mptObjIvls s Nm (locN s "m")))
    (hRN : IvlsDisj (R s) (nodeExtents s Nd))
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (hl : locN {post with locals := locals, clock := k} "m" = locN s "m") :
    MptObjReady {post with locals := locals, clock := k} := by
  obtain ⟨S', Nd', Nm', _, hW', hm', hd', _, _⟩ :=
    mptObjStep_parts_csr hstep hW hm hd hR hRN
  apply mptObjReady_of_parts_csr
    ((arenaReady_with_locals post locals k).2 hstep.1)
    (S := S') (Nd := Nd') (Nm := Nm')
  · exact (worldTypedWith_with_locals_csr post locals k S' Nd').2 hW'
  · rw [hl]
    exact hm'
  · rw [hl]
    exact hd'

theorem ivlsDisj_ownedGrows_csr {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hs : ArenaOK s) (hp : ArenaOK post) {old new objects : List Ivl}
    (hg : OwnedGrows s post old new)
    (ha : ∀ o ∈ objects, o.2 ≠ 0 → Allocated s o)
    (hd : IvlsDisj objects old) : IvlsDisj objects new := by
  intro o ho j hj
  by_cases hz : o.2 = 0
  · exact Or.inl hz
  · rcases hg j hj with rfl | ⟨i, hi, hin⟩ | hin
    · exact Or.inr (Or.inl rfl)
    · exact R10Shards.P26_P28.disj_of_inside_right hin (hd o ho i hi)
    · exact (disj_allocated_fresh_heap hs hp (ha o ho hz) hin).flip

theorem nodeHeap_extents_congr_unhit_csr {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hs : ArenaReady s) (hp : ArenaReady post) (hbe : post.be = s.be)
    (hag : AllocatorGrows s post) {Nm : List Nat} (hn : NodeHeap s Nm)
    (hu : ∀ o ∈ nodeExtents s Nm, o.2 ≠ 0 → P3MptSet.IvlUnhit s post o) :
    NodeHeap post Nm ∧ nodeExtents post Nm = nodeExtents s Nm := by
  apply nodeHeap_congr_bytes hs.1 hp.1 hag hn
  · intro n hnm
    apply hu _ (List.mem_flatMap.mpr ⟨n, hnm, by simp⟩)
    have hsz : 32 ≤ nodeSize (memW s n) := by unfold nodeSize; split_ifs <;> omega
    change nodeSize (memW s n) ≠ 0
    omega
  · intro n hnm hk hl k hkl
    have hpath : nodePath s n = (memW s (n + 32), memW s (n + 40)) :=
      if_pos ⟨hk, hl⟩
    have hmem : nodePath s n ∈ nodeExtents s Nm :=
      List.mem_flatMap.mpr ⟨n, hnm, by simp⟩
    rw [hpath] at hmem
    have hal : Allocated s (memW s (n + 32), memW s (n + 40)) := by
      rcases (hn.1 n hnm).2.2.2.2.2.2.1 hk with hz | ha
      · exact (hl hz).elim
      · exact ha.2.1
    exact P3MptSet.memB_eq_of_ivlUnhit (hu _ hmem hl) hbe
      (P3MptSet.ivl_allocated_bound hs.2 hal) ⟨by omega, by omega⟩

theorem mptObjInWith_transfer_csr {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hs : ArenaReady s) (hp : ArenaReady post) (hbe : post.be = s.be)
    (hag : AllocatorGrows s post) {S S' Nd Nd' Nm : List Nat} {m : Nat}
    (hm : MptObjInWith s S Nm m)
    (hd : IvlsDisj (mptObjIvls s Nm m) (nodeExtents s Nd))
    (hg : OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd'))
    (hu : ∀ o ∈ mptObjIvls s Nm m, o.2 ≠ 0 → P3MptSet.IvlUnhit s post o) :
    MptObjInWith post S' Nm m ∧
      IvlsDisj (mptObjIvls post Nm m) (nodeExtents post Nd') ∧
      mptObjIvls post Nm m = mptObjIvls s Nm m := by
  obtain ⟨hn, hext⟩ := nodeHeap_extents_congr_unhit_csr hs hp hbe hag
    hm.2.2.2.2.1 (fun o ho => hu o (List.mem_cons_of_mem _ ho))
  have hivl : mptObjIvls post Nm m = mptObjIvls s Nm m := by
    simp only [mptObjIvls, hext]
  have hdis : IvlsDisj (mptObjIvls post Nm m) (worldOwned post S' Nd') := by
    rw [hivl]
    exact ivlsDisj_ownedGrows_csr hs.2 hp.2 hg (mptObjInWith_allocated_csr hm)
      (mptObjInWith_disj_world_csr hm hd)
  have hroot : memW post m = memW s m :=
    P3MptSet.memW_eq_of_ivlUnhit (hu _ (by simp [mptObjIvls]) (by dsimp; omega))
      hm.2.1.1 (P3MptSet.ivl_allocated_bound hs.2 hm.1) ⟨le_rfl, by omega⟩
  refine ⟨mptObjInWith_of_parts_csr (hag.allocated hm.1)
    (P3MptSet.wordsOK_transfer hs.1 hp.1 hm.2.1) hn ?_ hdis ?_, ?_, hivl⟩
  · rw [hroot]
    exact hm.2.2.2.2.2.1
  · intro o ho
    rw [hext] at ho
    exact (hm.2.2.2.2.2.2 o ho).1
  · intro o ho j hj
    exact hdis o ho j (List.mem_append.mpr (Or.inr hj))

theorem worldStep_liveMpt_csr {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    (hs : ArenaReady s) (hstep : WorldStep R gw keep Q s r post)
    (hbe : post.be = s.be) (hag : AllocatorGrows s post)
    {S Nd Nm : List Nat} {m : Nat}
    (hW : WorldTypedWith s S Nd) (hm : MptObjInWith s S Nm m)
    (hd : IvlsDisj (mptObjIvls s Nm m) (nodeExtents s Nd))
    (hR : IvlsDisj (R s) (worldTypedIvls s S Nd))
    (hcells : ∀ o ∈ mptObjIvls s Nm m, o.2 ≠ 0 →
      ∀ a : BitVec 64, a.toNat % 8 = 0 → CellHits a.toNat o →
        (∀ j ∈ worldOwned s S Nd ++ R s ++ [freeGap s], ¬ CellHits a.toNat j) ∧
        ¬ CellHits a.toNat (heapFree s)) :
    ∃ S' Nd', (∀ t ∈ S, t ∈ S') ∧ WorldTypedWith post S' Nd' ∧
      MptObjInWith post S' Nm m ∧
      IvlsDisj (mptObjIvls post Nm m) (nodeExtents post Nd') ∧
      mptObjIvls post Nm m = mptObjIvls s Nm m ∧ Q s r post S' Nd' := by
  obtain ⟨S', Nd', hsub, hW', hg, hf, hQ⟩ := hstep.2.2.2.2 S Nd hW hR
  have hu : ∀ o ∈ mptObjIvls s Nm m, o.2 ≠ 0 → P3MptSet.IvlUnhit s post o := by
    intro o ho hnz a ha hh
    obtain ⟨hkeep, hfresh⟩ := hcells o ho hnz a ha hh
    exact hf a hkeep hfresh
  obtain ⟨hm', hd', heq⟩ := mptObjInWith_transfer_csr hs hstep.1 hbe hag hm hd hg hu
  exact ⟨S', Nd', hsub, hW', hm', hd', heq, hQ⟩

theorem mptObjInWith_transfer_frame_csr {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hs : ArenaReady s) (hp : ArenaReady post) (hbe : post.be = s.be)
    (hag : AllocatorGrows s post) {S S' Nd Nd' Nm : List Nat} {m : Nat}
    {keep : List Ivl} {fresh : Ivl}
    (hm : MptObjInWith s S Nm m)
    (hd : IvlsDisj (mptObjIvls s Nm m) (nodeExtents s Nd))
    (hg : OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd'))
    (hfr : FrameOutside s post keep fresh)
    (hk : ∀ o ∈ mptObjIvls s Nm m, o.2 ≠ 0 → ∀ j ∈ keep,
      (j.1 % 8 = 0 ∧ j.2 % 8 = 0 ∧ Disj o j) ∨ j.1 + j.2 + 8 ≤ o.1)
    (hfa : fresh.1 % 8 = 0 ∧ fresh.2 % 8 = 0)
    (hf : IvlsDisj (mptObjIvls s Nm m) [fresh]) :
    MptObjInWith post S' Nm m ∧
      IvlsDisj (mptObjIvls post Nm m) (nodeExtents post Nd') ∧
      mptObjIvls post Nm m = mptObjIvls s Nm m := by
  apply mptObjInWith_transfer_csr hs hp hbe hag hm hd hg
  intro o ho hnz
  exact P3MptSet.ivlUnhit_of_frameOutside hfr (hk o ho hnz) hfa
    (hf o ho fresh (by simp)) hnz

theorem worldStep_liveMpt_of_separated_csr {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    (hs : ArenaReady s) (hstep : WorldStep R gw keep Q s r post)
    (hbe : post.be = s.be) (hag : AllocatorGrows s post)
    {S Nd Nm : List Nat} {m : Nat}
    (hW : WorldTypedWith s S Nd) (hm : MptObjInWith s S Nm m)
    (hd : IvlsDisj (mptObjIvls s Nm m) (nodeExtents s Nd))
    (hR : IvlsDisj (R s) (worldTypedIvls s S Nd))
    (hsep : ∀ o ∈ mptObjIvls s Nm m, o.2 ≠ 0 →
      ∀ j ∈ worldOwned s S Nd ++ R s ++ [freeGap s],
        (j.1 % 8 = 0 ∧ j.2 % 8 = 0 ∧ Disj o j) ∨ j.1 + j.2 + 8 ≤ o.1) :
    ∃ S' Nd', (∀ t ∈ S, t ∈ S') ∧ WorldTypedWith post S' Nd' ∧
      MptObjInWith post S' Nm m ∧
      IvlsDisj (mptObjIvls post Nm m) (nodeExtents post Nd') ∧
      mptObjIvls post Nm m = mptObjIvls s Nm m ∧ Q s r post S' Nd' := by
  obtain ⟨S', Nd', hsub, hW', hg, hfr, hQ⟩ := hstep.2.2.2.2 S Nd hW hR
  have hfa : (heapFree s).1 % 8 = 0 ∧ (heapFree s).2 % 8 = 0 := by
    have hal := hs.2.2.2.2.2.2.1
    have hlim : heapLimit % 8 = 0 := by decide
    dsimp [heapFree]
    exact ⟨hal, by omega⟩
  have hf : IvlsDisj (mptObjIvls s Nm m) [heapFree s] := by
    intro o ho j hj
    have heq : j = heapFree s := List.mem_singleton.mp hj
    subst j
    by_cases hz : o.2 = 0
    · exact Or.inl hz
    · exact P3MptSet.disj_allocated_heapFree hs.2 (mptObjInWith_allocated_csr hm o ho hz)
  obtain ⟨hm', hd', heq⟩ := mptObjInWith_transfer_frame_csr hs hstep.1 hbe hag
    hm hd hg hfr hsep hfa hf
  exact ⟨S', Nd', hsub, hW', hm', hd', heq, hQ⟩

theorem htab_frame_liveMpt_csr {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hs : ArenaReady s) {S S' Nd Nd' Nm : List Nat} {t m : Nat}
    (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (hp : ArenaReady post) (hW' : WorldTypedWith post S' Nd')
    (hog : OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd'))
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hfr : FrameOutside s post (htabFootprint s t)
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr"))
    (hbe : post.be = s.be)
    (hg : ∀ name : MlS, name ∉ (["heap_ptr"] : List String).map ofString →
      s.globals.lookup name = post.globals.lookup name)
    (hm : MptObjInWith s S Nm m)
    (hd : IvlsDisj (mptObjIvls s Nm m) (nodeExtents s Nd)) :
    WorldTypedWith post S' Nd' ∧
      MptObjInWith post S' Nm m ∧
      IvlsDisj (mptObjIvls post Nm m) (nodeExtents post Nd') ∧
      mptObjIvls post Nm m = mptObjIvls s Nm m := by
  have hag : AllocatorGrows s post := by
    refine ⟨hhp, ?_⟩
    rw [R10Shards.P26_P28.globN_eq_of_lookup (hg (ofString "scratch_ptr") (by decide))]
  have hfa : (globN s "heap_ptr") % 8 = 0 ∧
      (globN post "heap_ptr" - globN s "heap_ptr") % 8 = 0 := by
    have hs8 := hs.2.2.2.2.2.2.1
    have hp8 := hp.2.2.2.2.2.2.1
    exact ⟨hs8, by omega⟩
  have hdis : IvlsDisj (mptObjIvls s Nm m)
      [(globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")] := by
    intro o ho j hj
    obtain rfl := List.mem_singleton.mp hj
    by_cases hz : o.2 = 0
    · exact Or.inl hz
    · exact (disj_allocated_fresh_heap hs.2 hp.2
        (mptObjInWith_allocated_csr hm o ho hz) ⟨le_rfl, by dsimp; omega⟩).flip
  obtain ⟨hm', hd', heq⟩ := mptObjInWith_transfer_frame_csr hs hp hbe hag hm hd hog hfr
    (fun o ho hnz j hj => Or.inl
      ⟨((hW.1.2.1 t ht).1.1 j hj).2.1,
       ((hW.1.2.1 t ht).1.1 j hj).2.2.1,
       mptObjInWith_disj_world_csr hm hd o ho j
         (List.mem_append.mpr (Or.inl (List.mem_append.mpr
           (Or.inl (List.mem_flatMap.mpr ⟨t, ht, hj⟩)))))⟩)
    hfa hdis
  exact ⟨hW', hm', hd', heq⟩

theorem htabNewExit_local_table_csr {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {v : ValueHOL 64}
    (hs : ArenaReady s) {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    (hbe : post.be = s.be)
    (hexit : HtabNewExit s (some (.returned v)) post) :
    ∃ w : BitVec 64, v = .val (.word w) ∧
      ArenaReady post ∧ AllocatorGrows s post ∧
      w.toNat ∉ S ∧ w.toNat ≠ 0 ∧
      hdr post w.toNat 0 = locN s "key_len" ∧
      hdr post w.toNat 3 = 0 ∧
      (∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ w.toNat) ∧
      WorldTypedWith post (S ++ [w.toNat]) Nd ∧
      worldRoleSlots post = worldRoleSlots s ∧
      journalRoleSlots post = journalRoleSlots s ∧
      (∀ u ∈ S, hdr post u 0 = hdr s u 0) ∧
      GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧
      FrameOutside s post
        [(globN post "scratch_ptr", globN s "scratch_ptr" - globN post "scratch_ptr")]
        (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
  obtain ⟨w, hv, hp, hag, hwf, hc3, hc0, hfp, hfr, hg⟩ := hexit v rfl
  obtain ⟨hnotS, hnz, hlocal, hW', hwrs, hjr, hhdr, _⟩ :=
    worldTypedWith_htab_new hs hW hp hag hwf hfp hfr hbe hg
  exact ⟨w, hv, hp, hag, hnotS, hnz, hc0, hc3, hlocal, hW', hwrs, hjr, hhdr, hg, hfr⟩

theorem htabCopy_local_table_csr {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {v : ValueHOL 64}
    {S Nd : List Nat} {keep : List (String × List Nat)}
    (hs : ArenaReady s) (hW : WorldTypedWith s S Nd)
    (harg : HtabWF s (locN s "t") ∧
      ∀ i ∈ htabFootprint s (locN s "t"), Allocated s i)
    (hstep : WorldStep (fun _ => []) ["heap_ptr"] keep
      (RetAvoidsIf (fun s => HtabWF s (locN s "t") ∧
        ∀ i ∈ htabFootprint s (locN s "t"), Allocated s i)
        (fun _ post w => htabFootprint post w)) s (some (.returned v)) post)
    (hret : RetWord (fun s post n => ArenaReady post ∧ AllocatorGrows s post ∧
      locN s "t" ≠ 0 ∧
      (HtabWF s (locN s "t") →
        (∀ i ∈ htabFootprint s (locN s "t"), Allocated s i) →
        HtabWF post n ∧ hdr post n 3 = hdr s (locN s "t") 3 ∧
        ∀ i ∈ htabFootprint post n,
          Inside i (globN s "heap_ptr") (globN post "heap_ptr")))
      s (some (.returned v)) post) :
    ∃ (w : BitVec 64) (S' Nd' : List Nat), v = .val (.word w) ∧
      (∀ t ∈ S, t ∈ S') ∧ WorldTypedWith post (S' ++ [w.toNat]) Nd' ∧
      w.toNat ∉ S' ∧ w.toNat ≠ 0 ∧
      (∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ w.toNat) ∧
      hdr post w.toNat 3 = hdr s (locN s "t") 3 := by
  obtain ⟨S', Nd', hsub, hW', _, _, havoid⟩ :=
    hstep.2.2.2.2 S Nd hW (by intro i hi; simp at hi)
  obtain ⟨w, hv, hp, _, _, hcopy⟩ := hret v rfl
  obtain ⟨hwf, hc3, hfp⟩ := hcopy harg.1 harg.2
  obtain ⟨wa, hva, hdis⟩ := havoid harg v rfl
  have heq : wa = w := by simpa using hva.symm.trans hv
  subst wa
  have halloc : ∀ i ∈ htabFootprint post w.toNat, Allocated post i := by
    intro i hi
    have hin := hfp i hi
    exact Or.inl ⟨Nat.le_trans hs.2.1 hin.1, hin.2⟩
  obtain ⟨hnot, hnz, hlocal, hjoin⟩ := adjoin_local_table hW' hwf
    (fun i hi => ⟨halloc i hi, hdis i hi⟩) (klen := hdr post w.toNat 0) rfl
  exact ⟨w, S', Nd', hv, hsub, hjoin, hnot, hnz, hlocal, hc3⟩

theorem htabExit_preserves_other_table_csr {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {u : Nat}
    (hs : ArenaReady s) (hW : WorldTypedWith s S Nd)
    (ht : locN s "t" ∈ S) (hu : u ∈ S) (hne : u ≠ locN s "t")
    (hexit : HtabExit s post) :
    HtabWF post u ∧ htabFootprint post u = htabFootprint s u ∧
      (∀ k, k < 11 → hdr post u k = hdr s u k) ∧
      (∀ i ∈ htabFootprint s u, GbodyC17ToC21Common.IvlUnhit s post i) := by
  obtain ⟨hp, _, _, _, hhp, _, hfr, hg⟩ := hexit
  have hag : AllocatorGrows s post := by
    refine ⟨hhp, ?_⟩
    rw [R10Shards.P26_P28.globN_eq_of_lookup
      (hg (ofString "scratch_ptr") (by decide))]
  have hfa : (globN s "heap_ptr") % 8 = 0 ∧
      (globN post "heap_ptr" - globN s "heap_ptr") % 8 = 0 := by
    have hs8 := hs.2.2.2.2.2.2.1
    have hp8 := hp.2.2.2.2.2.2.1
    exact ⟨hs8, by omega⟩
  have hunhit : ∀ i ∈ htabFootprint s u, GbodyC17ToC21Common.IvlUnhit s post i := by
    intro i hi
    have hiw := ((hW.1.2.1 u hu).1.1 i hi).2
    have hal := ((hW.1.2.1 u hu).2 i hi).1
    have hipos := htabFootprint_len_pos (hW.1.2.1 u hu).1 hi
    have hfree := (ivl_disj_free_of_zero_or_allocated hs.2 hp.2 hag
      (Or.inr ⟨hipos, hal⟩)).1
    exact GbodyC17ToC21Common.ivlUnhit_of_frameOutside_aligned hfr
      (fun _ => hiw.1)
      (fun j hj => ⟨((hW.1.2.1 _ ht).1.1 j hj).2.1,
        ((hW.1.2.1 _ ht).1.1 j hj).2.2.1⟩)
      hfa (fun j hj => hW.1.2.2.1 u hu _ ht hne i hi j hj) hfree
  have hheader : (u, 88) ∈ htabFootprint s u := by simp [htabFootprint]
  have hu8 := ((hW.1.2.1 u hu).1.1 _ hheader).2.1
  have hhi : u + 88 ≤ 2 ^ 64 := by
    have hb := ((hW.1.2.1 u hu).1.1 _ hheader).1.2
    have hbound : heapEnd ≤ 2 ^ 64 := by decide
    dsimp at hb
    omega
  obtain ⟨hhdr, hfp⟩ := GbodyC17ToC21Common.htabFootprint_eq_of_hdr_unhit hu8 hhi (hunhit _ hheader)
  exact ⟨GbodyC17ToC21Common.htabWF_congr_unhit hs.1 hp.1 (hW.1.2.1 u hu).1 hunhit,
    hfp, hhdr, hunhit⟩

theorem worldTypedWith_perm_csr {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S S' Nd : List Nat} (hp : S.Perm S') (hW : WorldTypedWith s S Nd) :
    WorldTypedWith s S' Nd := by
  obtain ⟨hT, hJ, hF, hTr⟩ := hW
  have hmem : ∀ x, x ∈ S' ↔ x ∈ S := fun x => hp.symm.mem_iff
  have hroot : ∀ {v}, RootIn S v → RootIn S' v := by
    rintro v (rfl | hv)
    · exact Or.inl rfl
    · exact Or.inr ((hmem v).2 hv)
  have hval : ∀ {u}, HtabValuesIn s u S → HtabValuesIn s u S' :=
    fun hv i hi => (hmem _).2 (hv i hi)
  obtain ⟨hnd, hTt, hTp, hws, hbs, hts, hg, hbsN, htsN, hbal, hbo, hroles⟩ := hT
  refine ⟨⟨hp.nodup_iff.1 hnd,
    fun u hu => hTt u ((hmem u).1 hu),
    fun u hu v hv => hTp u ((hmem u).1 hu) v ((hmem v).1 hv),
    fun k hk hnz => hroot (hws k hk hnz),
    fun k hk hnz => hroot (hbs k hk hnz),
    fun k hk hnz => hroot (hts k hk hnz),
    fun g hgm => hroot (hg g hgm),
    fun hnz hm => hval (hbsN hnz ((hmem _).1 hm)),
    fun hnz hm => hval (htsN hnz ((hmem _).1 hm)),
    fun ad had => ⟨(hmem _).2 (hbal ad had).1, (hmem _).2 (hbal ad had).2.1, (hbal ad had).2.2⟩,
    hbo,
    ⟨fun a ha => ⟨(hmem _).2 (hroles.1 a ha).1, (hroles.1 a ha).2⟩, hroles.2⟩⟩,
    ⟨hJ.1, hJ.2.1, hJ.2.2.1, fun i hi => (hmem _).2 (hJ.2.2.2 i hi)⟩,
    hF,
    ⟨hTr.1, fun o ho => ⟨fun u hu => (hTr.2.1 o ho).1 u ((hmem u).1 hu), (hTr.2.1 o ho).2⟩,
      fun hnz => ⟨(hTr.2.2 hnz).1, fun hm => (hTr.2.2 hnz).2 ((hmem _).1 hm)⟩⟩⟩

theorem htabExit_rejoin_local_csr {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hs : ArenaReady s) (hW : WorldTypedWith s S Nd)
    (ht : locN s "t" ∈ S) (hexit : HtabExit s post)
    (hbase : WorldTypedWith post (S.erase (locN s "t")) Nd)
    (howned : worldOwned post (S.erase (locN s "t")) Nd =
      worldOwned s (S.erase (locN s "t")) Nd) :
    WorldTypedWith post S Nd ∧
      (∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ locN s "t") := by
  obtain ⟨hp, hwf, _, _, hhp, hfp, _, hg⟩ := hexit
  have hag : AllocatorGrows s post := by
    refine ⟨hhp, ?_⟩
    rw [R10Shards.P26_P28.globN_eq_of_lookup
      (hg (ofString "scratch_ptr") (by decide))]
  have hdisj : ∀ i ∈ htabFootprint post (locN s "t"),
      ∀ o ∈ worldOwned post (S.erase (locN s "t")) Nd, Disj i o := by
    intro i hi o ho
    rw [howned] at ho
    rcases (hfp i hi).2 with ⟨j, hj, hin⟩ | hin
    · apply GbodyC17ToC21Common.disj_of_inside_left hin
      unfold worldOwned at ho
      rcases List.mem_append.1 ho with h1 | hnd
      · rcases List.mem_append.1 h1 with htab | hfix
        · obtain ⟨u, hu, hofp⟩ := List.mem_flatMap.1 htab
          obtain ⟨hne, huS⟩ := (List.Nodup.mem_erase_iff hW.1.1).1 hu
          exact hW.1.2.2.1 _ ht u huS hne.symm j hj o hofp
        · exact ((hW.1.2.1 _ ht).2 j hj).2 o hfix
      · exact ((hW.2.2.2.2.1 o hnd).1 _ ht j hj).flip
    · have hoS : o ∈ worldOwned s S Nd := by
        unfold worldOwned at ho ⊢
        rcases List.mem_append.1 ho with h1 | hnd
        · apply List.mem_append.2; left
          rcases List.mem_append.1 h1 with htab | hfix
          · apply List.mem_append.2; left
            obtain ⟨u, hu, hofp⟩ := List.mem_flatMap.1 htab
            exact List.mem_flatMap.2 ⟨u, List.mem_of_mem_erase hu, hofp⟩
          · exact List.mem_append.2 (Or.inr hfix)
        · exact List.mem_append.2 (Or.inr hnd)
      have hd := (ivl_disj_free_of_zero_or_allocated hs.2 hp.2 hag
        (worldOwned_zero_or_allocated hW o hoS)).1
      exact (GbodyC17ToC21Common.disj_of_inside_right hin hd).flip
  obtain ⟨_, _, hlocal, hadd⟩ := adjoin_local_table hbase hwf
    (fun i hi => ⟨(hfp i hi).1, hdisj i hi⟩) rfl
  have hperm : (S.erase (locN s "t") ++ [locN s "t"]).Perm S :=
    (List.perm_append_singleton _ _).trans (List.perm_cons_erase ht).symm
  exact ⟨worldTypedWith_perm_csr hperm hadd, hlocal⟩

theorem worldTypedWith_htab_set_local_csr {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hs : ArenaReady s) (hW : WorldTypedWith s S Nd)
    (ht : locN s "t" ∈ S)
    (hlocal : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ locN s "t")
    (hexit : HtabExit s post) (hbe : post.be = s.be) :
    WorldTypedWith post S Nd ∧
      worldRoleSlots post = worldRoleSlots s ∧
      journalRoleSlots post = journalRoleSlots s ∧
      (∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ locN s "t") ∧
      (∀ u ∈ S, hdr post u 0 = hdr s u 0) ∧
      OwnedGrows s post (worldOwned s S Nd) (worldOwned post S Nd) ∧
      (∀ b : Ivl, (b.2 = 0 → b.1 % 8 = 0) → Inside b sourceBase (globN s "heap_ptr") →
        (∀ j ∈ worldOwned s S Nd, Disj b j) →
        Inside b sourceBase (globN post "heap_ptr") ∧
          (∀ o ∈ worldOwned post S Nd, Disj b o) ∧
          GbodyC17ToC21Common.IvlUnhit s post b) := by
  have hWer := worldTypedWith_erase_local hW hlocal
  have hexit_saved := hexit
  obtain ⟨hp, _, hhdr0, _, hhp, hfp, hfr, hg⟩ := hexit
  have hag : AllocatorGrows s post := by
    refine ⟨hhp, ?_⟩
    rw [R10Shards.P26_P28.globN_eq_of_lookup
      (hg (ofString "scratch_ptr") (by decide))]
  have hgs : GbodyC17ToC21Common.WorldGlobalsSame s post :=
    ⟨fun gn hgn => R10Shards.P26_P28.globN_eq_of_lookup (hg (ofString gn.1)
        ((by decide : ∀ gn ∈ globalBuffers,
          ofString gn.1 ∉ (["heap_ptr"] : List String).map ofString) gn hgn)),
     fun g hgm => R10Shards.P26_P28.globN_eq_of_lookup (hg (ofString g)
        ((by decide : ∀ g ∈ globalTableRoots,
          ofString g ∉ (["heap_ptr"] : List String).map ofString) g hgm)),
     R10Shards.P26_P28.globN_eq_of_lookup (hg (ofString "journal") (by decide)),
     R10Shards.P26_P28.globN_eq_of_lookup (hg (ofString "journal_cap") (by decide)),
     R10Shards.P26_P28.globN_eq_of_lookup (hg (ofString "journal_n") (by decide))⟩
  have hfa : (globN s "heap_ptr") % 8 = 0 ∧
      (globN post "heap_ptr" - globN s "heap_ptr") % 8 = 0 := by
    have hs8 := hs.2.2.2.2.2.2.1
    have hp8 := hp.2.2.2.2.2.2.1
    exact ⟨hs8, by omega⟩
  have htal : ∀ j ∈ htabFootprint s (locN s "t"), j.1 % 8 = 0 ∧ j.2 % 8 = 0 :=
    fun j hj => ⟨((hW.1.2.1 _ ht).1.1 j hj).2.1, ((hW.1.2.1 _ ht).1.1 j hj).2.2.1⟩
  have hmlow : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 := by
    have hlow : ∀ a : Nat, a + 8 ≤ sourceBase → memW post a = memW s a := fun a ha => by
      have hsb264 : sourceBase < 2 ^ 64 := by decide
      have ha_lt : a < 2 ^ 64 := by omega
      have hm := hfr (BitVec.ofNat 64 a)
        (fun j hj hcj => by
          obtain ⟨h1, _⟩ := hcj
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
          have hlo := ((hW.1.2.1 _ ht).1.1 j hj).1.1
          omega)
        (fun hcf => by
          obtain ⟨h1, _⟩ := hcf
          dsimp at h1
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
          have hsl := hs.2.1
          omega)
      unfold memW; rw [hm]
    exact ⟨hlow 8 (by decide), hlow 16 (by decide)⟩
  have hunhit_er_ow : ∀ o ∈ worldOwned s (S.erase (locN s "t")) Nd,
      GbodyC17ToC21Common.IvlUnhit s post o := by
    intro o ho
    have hal := worldOwned_zero_or_allocated hWer o ho
    have hfree := (ivl_disj_free_of_zero_or_allocated hs.2 hp.2 hag hal).1
    apply GbodyC17ToC21Common.ivlUnhit_of_frameOutside_aligned hfr
      (worldOwned_zero_aligned hWer o ho) htal hfa ?_ hfree
    unfold worldOwned at ho
    rcases List.mem_append.1 ho with h1 | hnd
    · rcases List.mem_append.1 h1 with htab | hfix
      · obtain ⟨u, huer, hofp⟩ := List.mem_flatMap.1 htab
        obtain ⟨hne, huS⟩ := (List.Nodup.mem_erase_iff hW.1.1).1 huer
        exact fun j hj => hW.1.2.2.1 u huS _ ht hne o hofp j hj
      · exact fun j hj => (((hW.1.2.1 _ ht).2 j hj).2 o hfix).flip
    · exact fun j hj => (hW.2.2.2.2.1 o hnd).1 _ ht j hj
  have hunhit_er : ∀ i ∈ worldTypedIvls s (S.erase (locN s "t")) Nd,
      GbodyC17ToC21Common.IvlUnhit s post i := fun i hi =>
    hunhit_er_ow i (worldTypedIvls_sub_worldOwned s _ Nd i hi)
  have hbo_u : globN s "bo" ≠ 0 → GbodyC17ToC21Common.IvlUnhit s post (globN s "bo", 88) :=
    fun hnz => hunhit_er _ (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; right
      exact List.mem_map.2 ⟨("bo", 88), by simp [typedRecords], by simp [hnz]⟩)
  obtain ⟨hbase, howned_er, hwrs_eq, hjr_eq, hhdr_er⟩ :=
    worldTypedWith_congr_bo hs hp hbe hag hgs hWer
      (fun u hu i hi => hunhit_er i (by
        unfold worldTypedIvls
        apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
        apply List.mem_append.2; left; apply List.mem_append.2; left
        exact List.mem_flatMap.2 ⟨u, hu, hi⟩))
      (fun hnz => hunhit_er _ (by
        unfold worldTypedIvls
        apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
        apply List.mem_append.2; left; apply List.mem_append.2; right
        exact List.mem_map.2 ⟨("ws", 40), by simp [typedRecords], by simp [hnz]⟩))
      (fun hnz => hunhit_er _ (by
        unfold worldTypedIvls
        apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
        apply List.mem_append.2; left; apply List.mem_append.2; right
        exact List.mem_map.2 ⟨("bs", 80), by simp [typedRecords], by simp [hnz]⟩))
      (fun hnz => hunhit_er _ (by
        unfold worldTypedIvls
        apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
        apply List.mem_append.2; left; apply List.mem_append.2; right
        exact List.mem_map.2 ⟨("ts", 72), by simp [typedRecords], by simp [hnz]⟩))
      (fun hnz => hunhit_er _ (by
        unfold worldTypedIvls
        apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
        apply List.mem_append.2; right; simp [hnz]))
      (fun i hi _ => hunhit_er i (by
        unfold worldTypedIvls
        apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
        exact hi))
      (fun i hi => hunhit_er i (by
        unfold worldTypedIvls
        apply List.mem_append.2; left; apply List.mem_append.2; right
        exact hi))
      (fun o ho => hunhit_er o (by
        unfold worldTypedIvls
        exact List.mem_append.2 (Or.inr ho)))
      (fun hnz k hk => by
        have hk_in : k % 8 = 0 ∧ k + 8 ≤ 88 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
        have hbo_g : globN post "bo" = globN s "bo" := hgs.1 ("bo", 88) (by simp [globalBuffers])
        simpa [hbo_g] using
          GbodyC17ToC21Common.rec_word_eq_of_unhit hs.2 hWer.2.2.1 "bo" 88
            (by simp [typedRecords]) hbo_g hnz (hbo_u hnz) hk_in.1 hk_in.2)
      hmlow
  obtain ⟨hW_post, hlocal_post⟩ := htabExit_rejoin_local_csr hs hW ht hexit_saved hbase howned_er
  have hhdr_all : ∀ u ∈ S, hdr post u 0 = hdr s u 0 := by
    intro u hu
    by_cases hut : u = locN s "t"
    · subst hut; exact hhdr0
    · exact hhdr_er u ((List.Nodup.mem_erase_iff hW.1.1).2 ⟨hut, hu⟩)
  have hog : OwnedGrows s post (worldOwned s S Nd) (worldOwned post S Nd) := by
    intro o ho
    have hsub_ow : ∀ x ∈ worldOwned s (S.erase (locN s "t")) Nd, x ∈ worldOwned s S Nd := by
      intro x hx; unfold worldOwned at hx ⊢
      rcases List.mem_append.1 hx with h1 | hnd
      · apply List.mem_append.2; left
        rcases List.mem_append.1 h1 with htab | hfix
        · apply List.mem_append.2; left
          obtain ⟨u, huer, hxfp⟩ := List.mem_flatMap.1 htab
          exact List.mem_flatMap.2 ⟨u, List.mem_of_mem_erase huer, hxfp⟩
        · exact List.mem_append.2 (Or.inr hfix)
      · exact List.mem_append.2 (Or.inr hnd)
    unfold worldOwned at ho
    rcases List.mem_append.1 ho with h1 | hnd
    · rcases List.mem_append.1 h1 with htab | hfix
      · obtain ⟨u, huS, hofp⟩ := List.mem_flatMap.1 htab
        by_cases hut : u = locN s "t"
        · rw [hut] at huS hofp
          rcases (hfp o hofp).2 with ⟨j, hj, hin_j⟩ | hin_hp
          · refine Or.inr (Or.inl ⟨j, ?_, hin_j⟩)
            unfold worldOwned
            exact List.mem_append.2 (Or.inl (List.mem_append.2
              (Or.inl (List.mem_flatMap.2 ⟨_, huS, hj⟩))))
          · right; right
            unfold Inside at hin_hp ⊢; omega
        · have huer : u ∈ S.erase (locN s "t") :=
            (List.Nodup.mem_erase_iff hW.1.1).2 ⟨hut, huS⟩
          have ho_er : o ∈ worldOwned post (S.erase (locN s "t")) Nd := by
            unfold worldOwned
            exact List.mem_append.2 (Or.inl (List.mem_append.2
              (Or.inl (List.mem_flatMap.2 ⟨u, huer, hofp⟩))))
          rw [howned_er] at ho_er
          exact Or.inr (Or.inl ⟨o, hsub_ow o ho_er, ⟨le_rfl, le_rfl⟩⟩)
      · have ho_er : o ∈ worldOwned post (S.erase (locN s "t")) Nd := by
          unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))
        rw [howned_er] at ho_er
        exact Or.inr (Or.inl ⟨o, hsub_ow o ho_er, ⟨le_rfl, le_rfl⟩⟩)
    · have ho_er : o ∈ worldOwned post (S.erase (locN s "t")) Nd := by
        unfold worldOwned; exact List.mem_append.2 (Or.inr hnd)
      rw [howned_er] at ho_er
      exact Or.inr (Or.inl ⟨o, hsub_ow o ho_er, ⟨le_rfl, le_rfl⟩⟩)
  refine ⟨hW_post, hwrs_eq, hjr_eq, hlocal_post, hhdr_all, hog, ?_⟩
  intro b hb0 hb_in hb_disj
  have hd_hp : Disj b (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") :=
    Or.inr (Or.inr (Or.inl hb_in.2))
  refine ⟨⟨hb_in.1, Nat.le_trans hb_in.2 hhp⟩, ?_, ?_⟩
  · intro o ho
    rcases hog o ho with rfl | ⟨j, hj, hin_j⟩ | hin_hp
    · exact GbodyC17ToC21Common.disj_zero_right b
    · exact GbodyC17ToC21Common.disj_of_inside_right hin_j (hb_disj j hj)
    · exact Or.inr (Or.inr (Or.inl (Nat.le_trans hb_in.2 hin_hp.1)))
  · exact GbodyC17ToC21Common.ivlUnhit_of_frameOutside_aligned hfr hb0 htal hfa
      (fun j hj => hb_disj j (by
        unfold worldOwned
        exact List.mem_append.2 (Or.inl (List.mem_append.2
          (Or.inl (List.mem_flatMap.2 ⟨_, ht, hj⟩))))))
      hd_hp

theorem htabExit_local_liveMpt_csr {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd Nm : List Nat} {m : Nat}
    (hs : ArenaReady s) (hW : WorldTypedWith s S Nd)
    (ht : locN s "t" ∈ S)
    (hlocal : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ locN s "t")
    (hexit : HtabExit s post) (hbe : post.be = s.be)
    (hm : MptObjInWith s S Nm m)
    (hd : IvlsDisj (mptObjIvls s Nm m) (nodeExtents s Nd)) :
    WorldTypedWith post S Nd ∧
      MptObjInWith post S Nm m ∧
      IvlsDisj (mptObjIvls post Nm m) (nodeExtents post Nd) ∧
      mptObjIvls post Nm m = mptObjIvls s Nm m ∧
      worldRoleSlots post = worldRoleSlots s ∧
      journalRoleSlots post = journalRoleSlots s ∧
      (∀ u ∈ S, hdr post u 0 = hdr s u 0) ∧
      OwnedGrows s post (worldOwned s S Nd) (worldOwned post S Nd) := by
  obtain ⟨hWp, hwrs, hjrs, _, hhdr, hog, _⟩ :=
    worldTypedWith_htab_set_local_csr hs hW ht hlocal hexit hbe
  obtain ⟨hp, _, _, _, hhp, _, hfr, hg⟩ := hexit
  obtain ⟨_, hmp, hdp, heq⟩ := htab_frame_liveMpt_csr hs hW ht hp hWp hog hhp hfr hbe hg hm hd
  exact ⟨hWp, hmp, hdp, heq, hwrs, hjrs, hhdr, hog⟩

private theorem worldTypedIvls_erase_sub_csr {F : Type}
    (s : PanSemStateFiniteExact 64 F) (S Nd : List Nat) (t : Nat) :
    ∀ i ∈ worldTypedIvls s (S.erase t) Nd, i ∈ worldTypedIvls s S Nd := by
  intro i hi
  unfold worldTypedIvls at hi ⊢
  rcases List.mem_append.1 hi with h1 | hnd
  · apply List.mem_append.2; left
    rcases List.mem_append.1 h1 with h2 | hbal
    · apply List.mem_append.2; left
      rcases List.mem_append.1 h2 with h3 | hbo
      · apply List.mem_append.2; left
        rcases List.mem_append.1 h3 with h4 | hjr
        · apply List.mem_append.2; left
          rcases List.mem_append.1 h4 with htab | hrec
          · apply List.mem_append.2; left
            obtain ⟨u, hu0, hi_fp⟩ := List.mem_flatMap.1 htab
            exact List.mem_flatMap.2 ⟨u, List.mem_of_mem_erase hu0, hi_fp⟩
          · exact List.mem_append.2 (Or.inr hrec)
        · exact List.mem_append.2 (Or.inr hjr)
      · exact List.mem_append.2 (Or.inr hbo)
    · exact List.mem_append.2 (Or.inr hbal)
  · exact List.mem_append.2 (Or.inr hnd)

private theorem worldOwned_erase_sub_csr {F : Type}
    (s : PanSemStateFiniteExact 64 F) (S Nd : List Nat) (t : Nat) :
    ∀ j ∈ worldOwned s (S.erase t) Nd, j ∈ worldOwned s S Nd := by
  intro j hj
  unfold worldOwned at hj ⊢
  rcases List.mem_append.1 hj with h1 | hnd
  · apply List.mem_append.2; left
    rcases List.mem_append.1 h1 with htab | hfix
    · apply List.mem_append.2; left
      obtain ⟨u, hu0, hj_fp⟩ := List.mem_flatMap.1 htab
      exact List.mem_flatMap.2 ⟨u, List.mem_of_mem_erase hu0, hj_fp⟩
    · exact List.mem_append.2 (Or.inr hfix)
  · exact List.mem_append.2 (Or.inr hnd)

theorem worldStep_preserves_two_local_tables_csr {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)} {S Nd : List Nat} {t1 t2 : Nat}
    (hAs : ArenaReady s) (hW : WorldTypedWith s S Nd)
    (ht1_S : t1 ∈ S) (ht2_S : t2 ∈ S) (hne : t1 ≠ t2)
    (ht1_loc : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ t1)
    (ht2_loc : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ t2)
    (hstep : WorldStep R gw keep Q s r post)
    (hR_z : ∀ j ∈ R s, j.2 = 0 → j.1 % 8 = 0)
    (hR_ti : IvlsDisj (R s) (worldTypedIvls s S Nd)) :
    ∃ S0' Nd',
      WorldTypedWith post (S0' ++ [t1, t2]) Nd' ∧
      t1 ∈ S0' ++ [t1, t2] ∧ t2 ∈ S0' ++ [t1, t2] ∧
      (∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ t1) ∧
      (∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ t2) ∧
      htabFootprint post t1 = htabFootprint s t1 ∧
      htabFootprint post t2 = htabFootprint s t2 ∧
      hdr post t1 0 = hdr s t1 0 ∧ hdr post t2 0 = hdr s t2 0 ∧
      Q s r post S0' Nd' ∧
      OwnedGrows s post (worldOwned s S Nd)
        (worldOwned post (S0' ++ [t1, t2]) Nd') ∧
      FrameOutside s post (worldOwned s S Nd ++ R s ++ [freeGap s]) (heapFree s) := by
  obtain ⟨hAp, hhp, _, _, hWS⟩ := hstep
  obtain ⟨S1', _, hsub1, hW1', _, _, _⟩ := hWS S Nd hW hR_ti
  have ht1_S1' : t1 ∈ S1' := hsub1 t1 ht1_S
  have ht2_S1' : t2 ∈ S1' := hsub1 t2 ht2_S
  let S_1 := S.erase t1
  let S0 := S_1.erase t2
  have hW_1 : WorldTypedWith s S_1 Nd := worldTypedWith_erase_local hW ht1_loc
  have hW0 : WorldTypedWith s S0 Nd := worldTypedWith_erase_local hW_1 ht2_loc
  have hsub0 : ∀ u ∈ S0, u ∈ S :=
    fun u hu => List.mem_of_mem_erase (List.mem_of_mem_erase hu)
  have hsub_ti0 : ∀ i ∈ worldTypedIvls s S0 Nd, i ∈ worldTypedIvls s S Nd :=
    fun i hi => worldTypedIvls_erase_sub_csr s S Nd t1 i
      (worldTypedIvls_erase_sub_csr s S_1 Nd t2 i hi)
  obtain ⟨S0', Nd0', _, hW0', hog0, hfr0, hQ0⟩ :=
    hWS S0 Nd hW0 (fun x hx i hi => hR_ti x hx i (hsub_ti0 i hi))
  obtain ⟨hT, _, _, hTr⟩ := hW
  have ht1_not_S0 : t1 ∉ S0 := fun hm =>
    ((List.Nodup.mem_erase_iff hT.1).1 (List.mem_of_mem_erase hm)).1 rfl
  have ht2_not_S0 : t2 ∉ S0 := fun hm =>
    ((List.Nodup.mem_erase_iff (hT.1.erase t1)).1 hm).1 rfl
  have hsep : heapLimit ≤ scratchStart := by decide
  obtain ⟨_, hs_hp, hs_fm, hs_sc, _⟩ := hAs.2
  obtain ⟨_, hp_hp, _, _, _⟩ := hAp.2
  have htab_surv : ∀ {t : Nat} (htS : t ∈ S) (htS1' : t ∈ S1') (ht0 : t ∉ S0),
      HtabWF post t ∧ htabFootprint post t = htabFootprint s t ∧ hdr post t 0 = hdr s t 0 ∧
      (∀ i ∈ htabFootprint post t, Allocated post i ∧
        ∀ o ∈ worldOwned post S0' Nd0', Disj i o) := by
    intro t htS htS1' ht0
    have hwf_s := (hT.2.1 t htS).1
    have hdisj_ow0 : ∀ i ∈ htabFootprint s t, ∀ j ∈ worldOwned s S0 Nd, Disj i j := by
      intro i hi j hj
      unfold worldOwned at hj
      rcases List.mem_append.1 hj with h1 | hnd
      · rcases List.mem_append.1 h1 with htab | hfix
        · obtain ⟨u, hu0, hj_fp⟩ := List.mem_flatMap.1 htab
          exact hT.2.2.1 t htS u (hsub0 u hu0) (fun heq => ht0 (heq ▸ hu0)) i hi j hj_fp
        · exact ((hT.2.1 t htS).2 i hi).2 j hfix
      · exact ((hTr.2.1 j hnd).1 t htS i hi).flip
    have hunhit_t : ∀ i ∈ htabFootprint s t, GbodyC17ToC21Common.IvlUnhit s post i := by
      intro i hi
      have hw := (hwf_s.1 i hi).2
      have hal_i := ((hT.2.1 t htS).2 i hi).1
      intro a ha8 hhit
      apply hfr0 a
      · intro j hj hcj
        rcases List.mem_append.1 hj with hj12 | hfg
        · rcases List.mem_append.1 hj12 with hj_ow | hj_R
          · exact GbodyC17ToC21Common.not_cellHits_of_disj hw.1 hw.2.1 ha8
              (worldOwned_zero_aligned hW0 j hj_ow) hhit (hdisj_ow0 i hi j hj_ow) hcj
          · have hi_ti : i ∈ worldTypedIvls s S Nd := by
              unfold worldTypedIvls
              apply List.mem_append.2; left; apply List.mem_append.2; left
              apply List.mem_append.2; left; apply List.mem_append.2; left
              apply List.mem_append.2; left
              exact List.mem_flatMap.2 ⟨t, htS, hi⟩
            exact GbodyC17ToC21Common.not_cellHits_of_disj hw.1 hw.2.1 ha8
              (hR_z j hj_R) hhit (hR_ti j hj_R i hi_ti).flip hcj
        · simp only [List.mem_singleton] at hfg; subst hfg
          obtain ⟨hc1, hc2⟩ := hhit
          obtain ⟨hj1, hj2⟩ := hcj
          unfold freeGap at hj1 hj2; dsimp at hj1 hj2
          rcases hal_i with ⟨_, hhi_i⟩ | ⟨hlo_i, _⟩ <;> omega
      · intro ⟨hf1, hf2⟩
        obtain ⟨hc1, hc2⟩ := hhit
        unfold heapFree at hf1 hf2; dsimp at hf1 hf2
        rcases hal_i with ⟨_, hhi_i⟩ | ⟨hlo_i, _⟩ <;> omega
    have hwf_post : HtabWF post t :=
      GbodyC17ToC21Common.htabWF_congr_unhit hAs.1 hAp.1 hwf_s hunhit_t
    have ht_fp : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
    have ht8 : t % 8 = 0 := (hwf_s.1 _ ht_fp).2.1
    have h264 : heapEnd ≤ 2 ^ 64 := by decide
    have hhi : t + 88 ≤ 2 ^ 64 := by have := (hwf_s.1 _ ht_fp).1.2; omega
    obtain ⟨hhdr_eq, hfp_eq⟩ :=
      GbodyC17ToC21Common.htabFootprint_eq_of_hdr_unhit ht8 hhi (hunhit_t _ ht_fp)
    refine ⟨hwf_post, hfp_eq, hhdr_eq 0 (by omega), fun i hi => ?_⟩
    have hal_post_i : Allocated post i := ((hW1'.1.2.1 t htS1').2 i hi).1
    rw [hfp_eq] at hi
    have hal_s_i : Allocated s i := ((hT.2.1 t htS).2 i hi).1
    refine ⟨hal_post_i, fun o ho => ?_⟩
    rcases hog0 o ho with rfl | ⟨j, hj0, hin_j⟩ | hfresh
    · exact GbodyC17ToC21Common.disj_zero_right i
    · exact GbodyC17ToC21Common.disj_of_inside_right hin_j (hdisj_ow0 i hi j hj0)
    · rcases hal_s_i with ⟨_, hhi_i⟩ | ⟨hlo_i, _⟩
      · exact Or.inr (Or.inr (Or.inl (Nat.le_trans hhi_i hfresh.1)))
      · exact Or.inr (Or.inr (Or.inr (by unfold Inside at hfresh; omega)))
  obtain ⟨hwf_t1, hfp_t1, hhdr_t1, hsurv_t1⟩ := htab_surv ht1_S ht1_S1' ht1_not_S0
  obtain ⟨hwf_t2, hfp_t2, hhdr_t2, hsurv_t2⟩ := htab_surv ht2_S ht2_S1' ht2_not_S0
  obtain ⟨_, _, ht1_unass, hW_t1⟩ :=
    adjoin_local_table hW0' hwf_t1 hsurv_t1 (klen := hdr s t1 0) hhdr_t1
  have hsurv_t2' : ∀ i ∈ htabFootprint post t2,
      Allocated post i ∧ ∀ o ∈ worldOwned post (S0' ++ [t1]) Nd0', Disj i o := by
    intro i hi
    refine ⟨(hsurv_t2 i hi).1, fun o ho => ?_⟩
    unfold worldOwned at ho
    rcases List.mem_append.1 ho with h1 | hnd
    · rcases List.mem_append.1 h1 with htab | hfix
      · rw [List.flatMap_append] at htab
        rcases List.mem_append.1 htab with htab' | htab_t1
        · apply (hsurv_t2 i hi).2 o
          unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl htab')))
        · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at htab_t1
          rw [hfp_t2] at hi; rw [hfp_t1] at htab_t1
          exact hT.2.2.1 t2 ht2_S t1 ht1_S hne.symm i hi o htab_t1
      · apply (hsurv_t2 i hi).2 o
        unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))
    · apply (hsurv_t2 i hi).2 o
      unfold worldOwned; exact List.mem_append.2 (Or.inr hnd)
  obtain ⟨_, _, ht2_unass, hW_both⟩ :=
    adjoin_local_table hW_t1 hwf_t2 hsurv_t2' (klen := hdr s t2 0) hhdr_t2
  have hassoc : (S0' ++ [t1]) ++ [t2] = S0' ++ [t1, t2] := by simp
  rw [hassoc] at hW_both
  have hsub_ow0 : ∀ j ∈ worldOwned s S0 Nd, j ∈ worldOwned s S Nd :=
    fun j hj => worldOwned_erase_sub_csr s S Nd t1 j
      (worldOwned_erase_sub_csr s S_1 Nd t2 j hj)
  have hog_both : OwnedGrows s post (worldOwned s S Nd)
      (worldOwned post (S0' ++ [t1, t2]) Nd0') := by
    intro o ho
    unfold worldOwned at ho
    rcases List.mem_append.1 ho with h1 | hnd
    · rcases List.mem_append.1 h1 with htab | hfix
      · rw [List.flatMap_append] at htab
        rcases List.mem_append.1 htab with htab' | htab_loc
        · have ho0 : o ∈ worldOwned post S0' Nd0' :=
            List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl htab')))
          rcases hog0 o ho0 with rfl | ⟨j, hj0, hin_j⟩ | hfresh
          · exact Or.inl rfl
          · exact Or.inr (Or.inl ⟨j, hsub_ow0 j hj0, hin_j⟩)
          · exact Or.inr (Or.inr hfresh)
        · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at htab_loc
          rcases htab_loc with ho_t1 | ho_t2
          · rw [hfp_t1] at ho_t1
            exact Or.inr (Or.inl ⟨o, List.mem_append.2 (Or.inl (List.mem_append.2
              (Or.inl (List.mem_flatMap.2 ⟨t1, ht1_S, ho_t1⟩)))), ⟨le_rfl, le_rfl⟩⟩)
          · rw [hfp_t2] at ho_t2
            exact Or.inr (Or.inl ⟨o, List.mem_append.2 (Or.inl (List.mem_append.2
              (Or.inl (List.mem_flatMap.2 ⟨t2, ht2_S, ho_t2⟩)))), ⟨le_rfl, le_rfl⟩⟩)
      · have ho0 : o ∈ worldOwned post S0' Nd0' :=
          List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))
        rcases hog0 o ho0 with rfl | ⟨j, hj0, hin_j⟩ | hfresh
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨j, hsub_ow0 j hj0, hin_j⟩)
        · exact Or.inr (Or.inr hfresh)
    · have ho0 : o ∈ worldOwned post S0' Nd0' := List.mem_append.2 (Or.inr hnd)
      rcases hog0 o ho0 with rfl | ⟨j, hj0, hin_j⟩ | hfresh
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨j, hsub_ow0 j hj0, hin_j⟩)
      · exact Or.inr (Or.inr hfresh)
  have hfr_both : FrameOutside s post (worldOwned s S Nd ++ R s ++ [freeGap s]) (heapFree s) := by
    intro a hkeep hfresh
    refine hfr0 a (fun j hj hcj => hkeep j ?_ hcj) hfresh
    rcases List.mem_append.1 hj with hj12 | hfg
    · apply List.mem_append.2; left
      rcases List.mem_append.1 hj12 with hj0 | hjR
      · exact List.mem_append.2 (Or.inl (hsub_ow0 j hj0))
      · exact List.mem_append.2 (Or.inr hjR)
    · exact List.mem_append.2 (Or.inr hfg)
  exact ⟨S0', Nd0', hW_both, by simp, by simp, ht1_unass, ht2_unass,
    hfp_t1, hfp_t2, hhdr_t1, hhdr_t2, hQ0, hog_both, hfr_both⟩

theorem mptObjInWith_erase_sub_csr {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nm : List Nat} {m t : Nat}
    (hm : MptObjInWith s S Nm m) :
    MptObjInWith s (S.erase t) Nm m :=
  ⟨hm.1, hm.2.1,
    fun u hu => hm.2.2.1 u (List.mem_of_mem_erase hu),
    hm.2.2.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2.1,
    fun o ho => ⟨(hm.2.2.2.2.2.2 o ho).1,
      fun u hu => (hm.2.2.2.2.2.2 o ho).2.1 u (List.mem_of_mem_erase hu),
      (hm.2.2.2.2.2.2 o ho).2.2⟩⟩

theorem mptObjInWith_adjoin_local_csr {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nm : List Nat} {m t : Nat}
    (hm : MptObjInWith s S Nm m)
    (hdisj : ∀ o ∈ mptObjIvls s Nm m, ∀ i ∈ htabFootprint s t, Disj o i) :
    MptObjInWith s (S ++ [t]) Nm m := by
  refine ⟨hm.1, hm.2.1, ?_, hm.2.2.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2.1, ?_⟩
  · intro u hu i hi
    rcases List.mem_append.1 hu with huS | hut
    · exact hm.2.2.1 u huS i hi
    · simp only [List.mem_singleton] at hut; subst hut
      exact hdisj (m, 16) (by simp [mptObjIvls]) i hi
  · intro o ho
    refine ⟨(hm.2.2.2.2.2.2 o ho).1, ?_, (hm.2.2.2.2.2.2 o ho).2.2⟩
    intro u hu i hi
    rcases List.mem_append.1 hu with huS | hut
    · exact (hm.2.2.2.2.2.2 o ho).2.1 u huS i hi
    · simp only [List.mem_singleton] at hut; subst hut
      exact hdisj o (List.mem_cons_of_mem _ ho) i hi

theorem worldStep_two_local_liveMpt_csr {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)} {S Nd Nm : List Nat} {t1 t2 m : Nat}
    (hs : ArenaReady s) (hW : WorldTypedWith s S Nd)
    (ht1_S : t1 ∈ S) (ht2_S : t2 ∈ S) (hne : t1 ≠ t2)
    (ht1_loc : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ t1)
    (ht2_loc : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ t2)
    (hstep : WorldStep R gw keep Q s r post)
    (hbe : post.be = s.be) (hag : AllocatorGrows s post)
    (hm : MptObjInWith s S Nm m)
    (hd : IvlsDisj (mptObjIvls s Nm m) (nodeExtents s Nd))
    (hR_z : ∀ j ∈ R s, j.2 = 0 → j.1 % 8 = 0)
    (hR_ti : IvlsDisj (R s) (worldTypedIvls s S Nd))
    (hsep : ∀ o ∈ mptObjIvls s Nm m, o.2 ≠ 0 →
      ∀ j ∈ worldOwned s S Nd ++ R s ++ [freeGap s],
        (j.1 % 8 = 0 ∧ j.2 % 8 = 0 ∧ Disj o j) ∨ j.1 + j.2 + 8 ≤ o.1) :
    ∃ S0' Nd',
      WorldTypedWith post (S0' ++ [t1, t2]) Nd' ∧
      t1 ∈ S0' ++ [t1, t2] ∧ t2 ∈ S0' ++ [t1, t2] ∧
      (∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ t1) ∧
      (∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ t2) ∧
      htabFootprint post t1 = htabFootprint s t1 ∧
      htabFootprint post t2 = htabFootprint s t2 ∧
      hdr post t1 0 = hdr s t1 0 ∧ hdr post t2 0 = hdr s t2 0 ∧
      MptObjInWith post (S0' ++ [t1, t2]) Nm m ∧
      IvlsDisj (mptObjIvls post Nm m) (nodeExtents post Nd') ∧
      mptObjIvls post Nm m = mptObjIvls s Nm m ∧
      Q s r post S0' Nd' ∧
      OwnedGrows s post (worldOwned s S Nd)
        (worldOwned post (S0' ++ [t1, t2]) Nd') := by
  obtain ⟨S0', Nd', hW_both, ht1', ht2', ht1_unass, ht2_unass,
    hfp_t1, hfp_t2, hhdr_t1, hhdr_t2, hQ0, hog_both, hfr_both⟩ :=
    worldStep_preserves_two_local_tables_csr hs hW ht1_S ht2_S hne ht1_loc ht2_loc
      hstep hR_z hR_ti
  have hfa : (heapFree s).1 % 8 = 0 ∧ (heapFree s).2 % 8 = 0 := by
    have hal := hs.2.2.2.2.2.2.1
    have hlim : heapLimit % 8 = 0 := by decide
    dsimp [heapFree]
    exact ⟨hal, by omega⟩
  have hf : IvlsDisj (mptObjIvls s Nm m) [heapFree s] := by
    intro o ho j hj
    obtain rfl := List.mem_singleton.mp hj
    by_cases hz : o.2 = 0
    · exact Or.inl hz
    · exact P3MptSet.disj_allocated_heapFree hs.2 (mptObjInWith_allocated_csr hm o ho hz)
  obtain ⟨hm', hd', heq⟩ := mptObjInWith_transfer_frame_csr hs hstep.1 hbe hag
    hm hd hog_both hfr_both hsep hfa hf
  exact ⟨S0', Nd', hW_both, ht1', ht2', ht1_unass, ht2_unass,
    hfp_t1, hfp_t2, hhdr_t1, hhdr_t2, hm', hd', heq, hQ0, hog_both⟩

theorem mptObjStep_preserves_two_local_tables_csr {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {S Nd Nm : List Nat} {t1 t2 : Nat}
    (hAs : ArenaReady s) (hW : WorldTypedWith s S Nd)
    (ht1_S : t1 ∈ S) (ht2_S : t2 ∈ S) (hne : t1 ≠ t2)
    (ht1_loc : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ t1)
    (ht2_loc : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ t2)
    (hm : MptObjInWith s S Nm (locN s "m"))
    (hd : IvlsDisj (mptObjIvls s Nm (locN s "m")) (nodeExtents s Nd))
    (hstep : MptObjStep R gw keep s post)
    (hR_z : ∀ j ∈ R s, j.2 = 0 → j.1 % 8 = 0)
    (hR_ti : IvlsDisj (R s) (worldTypedIvls s S Nd ++ mptObjIvls s Nm (locN s "m")))
    (hRN : IvlsDisj (R s) (nodeExtents s Nd)) :
    ∃ S0' Nd' Nm',
      WorldTypedWith post (S0' ++ [t1, t2]) Nd' ∧
      t1 ∈ S0' ++ [t1, t2] ∧ t2 ∈ S0' ++ [t1, t2] ∧
      (∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ t1) ∧
      (∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ t2) ∧
      htabFootprint post t1 = htabFootprint s t1 ∧
      htabFootprint post t2 = htabFootprint s t2 ∧
      hdr post t1 0 = hdr s t1 0 ∧ hdr post t2 0 = hdr s t2 0 ∧
      MptObjInWith post (S0' ++ [t1, t2]) Nm' (locN s "m") ∧
      IvlsDisj (mptObjIvls post Nm' (locN s "m")) (nodeExtents post Nd') ∧
      OwnedGrows s post (worldOwned s S Nd ++ mptObjIvls s Nm (locN s "m"))
        (worldOwned post (S0' ++ [t1, t2]) Nd' ++ mptObjIvls post Nm' (locN s "m")) ∧
      FrameOutside s post
        (worldOwned s S Nd ++ mptObjIvls s Nm (locN s "m") ++ R s ++ [freeGap s])
        (heapFree s) := by
  have hAp := hstep.1
  obtain ⟨S1', _, _, hsub1, hW1', _, _, _, _⟩ :=
    mptObjStep_parts_csr hstep hW hm hd hR_ti hRN
  have ht1_S1' : t1 ∈ S1' := hsub1 t1 ht1_S
  have ht2_S1' : t2 ∈ S1' := hsub1 t2 ht2_S
  let S_1 := S.erase t1
  let S0 := S_1.erase t2
  have hW_1 : WorldTypedWith s S_1 Nd := worldTypedWith_erase_local hW ht1_loc
  have hW0 : WorldTypedWith s S0 Nd := worldTypedWith_erase_local hW_1 ht2_loc
  have hm0 : MptObjInWith s S0 Nm (locN s "m") :=
    mptObjInWith_erase_sub_csr (mptObjInWith_erase_sub_csr hm)
  have hsub0 : ∀ u ∈ S0, u ∈ S :=
    fun u hu => List.mem_of_mem_erase (List.mem_of_mem_erase hu)
  have hsub_ti0 : ∀ i ∈ worldTypedIvls s S0 Nd, i ∈ worldTypedIvls s S Nd :=
    fun i hi => worldTypedIvls_erase_sub_csr s S Nd t1 i
      (worldTypedIvls_erase_sub_csr s S_1 Nd t2 i hi)
  have hsub_ow0 : ∀ j ∈ worldOwned s S0 Nd, j ∈ worldOwned s S Nd :=
    fun j hj => worldOwned_erase_sub_csr s S Nd t1 j
      (worldOwned_erase_sub_csr s S_1 Nd t2 j hj)
  have hR_ti0 : IvlsDisj (R s) (worldTypedIvls s S0 Nd ++ mptObjIvls s Nm (locN s "m")) := by
    intro x hx i hi
    rcases List.mem_append.1 hi with hi_w | hi_m
    · exact hR_ti x hx i (List.mem_append.2 (Or.inl (hsub_ti0 i hi_w)))
    · exact hR_ti x hx i (List.mem_append.2 (Or.inr hi_m))
  obtain ⟨S0', Nd0', Nm0', _, hW0', hm0', hd0', hog0, hfr0⟩ :=
    mptObjStep_parts_csr hstep hW0 hm0 hd hR_ti0 hRN
  obtain ⟨hT, _, _, hTr⟩ := hW
  have ht1_not_S0 : t1 ∉ S0 := fun hm_in =>
    ((List.Nodup.mem_erase_iff hT.1).1 (List.mem_of_mem_erase hm_in)).1 rfl
  have ht2_not_S0 : t2 ∉ S0 := fun hm_in =>
    ((List.Nodup.mem_erase_iff (hT.1.erase t1)).1 hm_in).1 rfl
  have hsep : heapLimit ≤ scratchStart := by decide
  obtain ⟨_, hs_hp, hs_fm, hs_sc, _⟩ := hAs.2
  obtain ⟨_, hp_hp, _, _, _⟩ := hAp.2
  have hm_z_al : ∀ j ∈ mptObjIvls s Nm (locN s "m"), j.2 = 0 → j.1 % 8 = 0 := by
    intro j hj hj0
    rcases List.mem_cons.1 hj with rfl | hj_ext
    · dsimp at hj0; omega
    · obtain ⟨n, hn, hj_np⟩ := List.mem_flatMap.1 hj_ext
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj_np
      rcases hj_np with rfl | rfl
      · have hsz : 32 ≤ nodeSize (memW s n) := by unfold nodeSize; split_ifs <;> omega
        dsimp [nodeIvl] at hj0; omega
      · by_cases hp : (memW s n = 1 ∨ memW s n = 2) ∧ memW s (n + 40) ≠ 0
        · rw [show nodePath s n = (memW s (n + 32), memW s (n + 40)) from if_pos hp] at hj0
          exact absurd hj0 hp.2
        · rw [show nodePath s n = (0, 0) from if_neg hp]; simp
  have htab_surv : ∀ {t : Nat} (htS : t ∈ S) (htS1' : t ∈ S1') (ht0 : t ∉ S0),
      HtabWF post t ∧ htabFootprint post t = htabFootprint s t ∧ hdr post t 0 = hdr s t 0 ∧
      (∀ i ∈ htabFootprint post t, Allocated post i ∧
        (∀ o ∈ worldOwned post S0' Nd0', Disj i o) ∧
        (∀ o ∈ mptObjIvls post Nm0' (locN s "m"), Disj o i)) := by
    intro t htS htS1' ht0
    have hwf_s := (hT.2.1 t htS).1
    have hdisj_ow0 : ∀ i ∈ htabFootprint s t,
        ∀ j ∈ worldOwned s S0 Nd ++ mptObjIvls s Nm (locN s "m"), Disj i j := by
      intro i hi j hj
      rcases List.mem_append.1 hj with hj_ow | hj_m
      · unfold worldOwned at hj_ow
        rcases List.mem_append.1 hj_ow with h1 | hnd
        · rcases List.mem_append.1 h1 with htab | hfix
          · obtain ⟨u, hu0, hj_fp⟩ := List.mem_flatMap.1 htab
            exact hT.2.2.1 t htS u (hsub0 u hu0) (fun heq => ht0 (heq ▸ hu0)) i hi j hj_fp
          · exact ((hT.2.1 t htS).2 i hi).2 j hfix
        · exact ((hTr.2.1 j hnd).1 t htS i hi).flip
      · rcases List.mem_cons.1 hj_m with rfl | hj_ext
        · exact (hm.2.2.1 t htS i hi).flip
        · exact ((hm.2.2.2.2.2.2 j hj_ext).2.1 t htS i hi).flip
    have hunhit_t : ∀ i ∈ htabFootprint s t, GbodyC17ToC21Common.IvlUnhit s post i := by
      intro i hi
      have hw := (hwf_s.1 i hi).2
      have hal_i := ((hT.2.1 t htS).2 i hi).1
      intro a ha8 hhit
      apply hfr0 a
      · intro j hj hcj
        rcases List.mem_append.1 hj with hj12 | hfg
        · rcases List.mem_append.1 hj12 with hj_owm | hj_R
          · have hza : j.2 = 0 → j.1 % 8 = 0 := by
              rcases List.mem_append.1 hj_owm with hj_ow | hj_m
              · exact worldOwned_zero_aligned hW0 j hj_ow
              · exact hm_z_al j hj_m
            exact GbodyC17ToC21Common.not_cellHits_of_disj hw.1 hw.2.1 ha8 hza hhit
              (hdisj_ow0 i hi j hj_owm) hcj
          · have hi_ti : i ∈ worldTypedIvls s S Nd ++ mptObjIvls s Nm (locN s "m") := by
              apply List.mem_append.2; left
              unfold worldTypedIvls
              apply List.mem_append.2; left; apply List.mem_append.2; left
              apply List.mem_append.2; left; apply List.mem_append.2; left
              apply List.mem_append.2; left
              exact List.mem_flatMap.2 ⟨t, htS, hi⟩
            exact GbodyC17ToC21Common.not_cellHits_of_disj hw.1 hw.2.1 ha8
              (hR_z j hj_R) hhit (hR_ti j hj_R i hi_ti).flip hcj
        · simp only [List.mem_singleton] at hfg; subst hfg
          obtain ⟨hc1, hc2⟩ := hhit
          obtain ⟨hj1, hj2⟩ := hcj
          unfold freeGap at hj1 hj2; dsimp at hj1 hj2
          rcases hal_i with ⟨_, hhi_i⟩ | ⟨hlo_i, _⟩ <;> omega
      · intro ⟨hf1, hf2⟩
        obtain ⟨hc1, hc2⟩ := hhit
        unfold heapFree at hf1 hf2; dsimp at hf1 hf2
        rcases hal_i with ⟨_, hhi_i⟩ | ⟨hlo_i, _⟩ <;> omega
    have hwf_post : HtabWF post t :=
      GbodyC17ToC21Common.htabWF_congr_unhit hAs.1 hAp.1 hwf_s hunhit_t
    have ht_fp : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
    have ht8 : t % 8 = 0 := (hwf_s.1 _ ht_fp).2.1
    have h264 : heapEnd ≤ 2 ^ 64 := by decide
    have hhi : t + 88 ≤ 2 ^ 64 := by have := (hwf_s.1 _ ht_fp).1.2; omega
    obtain ⟨hhdr_eq, hfp_eq⟩ :=
      GbodyC17ToC21Common.htabFootprint_eq_of_hdr_unhit ht8 hhi (hunhit_t _ ht_fp)
    refine ⟨hwf_post, hfp_eq, hhdr_eq 0 (by omega), fun i hi => ?_⟩
    have hal_post_i : Allocated post i := ((hW1'.1.2.1 t htS1').2 i hi).1
    rw [hfp_eq] at hi
    have hal_s_i : Allocated s i := ((hT.2.1 t htS).2 i hi).1
    have hdisj_comb : ∀ o ∈ worldOwned post S0' Nd0' ++ mptObjIvls post Nm0' (locN s "m"),
        Disj i o := by
      intro o ho
      rcases hog0 o ho with rfl | ⟨j, hj0, hin_j⟩ | hfresh
      · exact GbodyC17ToC21Common.disj_zero_right i
      · exact GbodyC17ToC21Common.disj_of_inside_right hin_j (hdisj_ow0 i hi j hj0)
      · rcases hal_s_i with ⟨_, hhi_i⟩ | ⟨hlo_i, _⟩
        · exact Or.inr (Or.inr (Or.inl (Nat.le_trans hhi_i hfresh.1)))
        · exact Or.inr (Or.inr (Or.inr (by unfold Inside at hfresh; omega)))
    refine ⟨hal_post_i,
      fun o ho => hdisj_comb o (List.mem_append.2 (Or.inl ho)),
      fun o ho => (hdisj_comb o (List.mem_append.2 (Or.inr ho))).flip⟩
  obtain ⟨hwf_t1, hfp_t1, hhdr_t1, hsurv_t1⟩ := htab_surv ht1_S ht1_S1' ht1_not_S0
  obtain ⟨hwf_t2, hfp_t2, hhdr_t2, hsurv_t2⟩ := htab_surv ht2_S ht2_S1' ht2_not_S0
  obtain ⟨_, _, ht1_unass, hW_t1⟩ := adjoin_local_table hW0' hwf_t1
    (fun i hi => ⟨(hsurv_t1 i hi).1, (hsurv_t1 i hi).2.1⟩) (klen := hdr s t1 0) hhdr_t1
  have hsurv_t2' : ∀ i ∈ htabFootprint post t2,
      Allocated post i ∧ ∀ o ∈ worldOwned post (S0' ++ [t1]) Nd0', Disj i o := by
    intro i hi
    refine ⟨(hsurv_t2 i hi).1, fun o ho => ?_⟩
    unfold worldOwned at ho
    rcases List.mem_append.1 ho with h1 | hnd
    · rcases List.mem_append.1 h1 with htab | hfix
      · rw [List.flatMap_append] at htab
        rcases List.mem_append.1 htab with htab' | htab_t1
        · apply (hsurv_t2 i hi).2.1 o
          unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl htab')))
        · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at htab_t1
          rw [hfp_t2] at hi; rw [hfp_t1] at htab_t1
          exact hT.2.2.1 t2 ht2_S t1 ht1_S hne.symm i hi o htab_t1
      · apply (hsurv_t2 i hi).2.1 o
        unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))
    · apply (hsurv_t2 i hi).2.1 o
      unfold worldOwned; exact List.mem_append.2 (Or.inr hnd)
  obtain ⟨_, _, ht2_unass, hW_both⟩ :=
    adjoin_local_table hW_t1 hwf_t2 hsurv_t2' (klen := hdr s t2 0) hhdr_t2
  have hm_t1 : MptObjInWith post (S0' ++ [t1]) Nm0' (locN s "m") :=
    mptObjInWith_adjoin_local_csr hm0' (fun o ho i hi => (hsurv_t1 i hi).2.2 o ho)
  have hm_both : MptObjInWith post ((S0' ++ [t1]) ++ [t2]) Nm0' (locN s "m") :=
    mptObjInWith_adjoin_local_csr hm_t1 (fun o ho i hi => (hsurv_t2 i hi).2.2 o ho)
  have hassoc : (S0' ++ [t1]) ++ [t2] = S0' ++ [t1, t2] := by simp
  rw [hassoc] at hW_both hm_both
  have hog_both : OwnedGrows s post (worldOwned s S Nd ++ mptObjIvls s Nm (locN s "m"))
      (worldOwned post (S0' ++ [t1, t2]) Nd0' ++ mptObjIvls post Nm0' (locN s "m")) := by
    have hsub_owm : ∀ j ∈ worldOwned s S0 Nd ++ mptObjIvls s Nm (locN s "m"),
        j ∈ worldOwned s S Nd ++ mptObjIvls s Nm (locN s "m") := by
      intro j hj
      rcases List.mem_append.1 hj with hj0 | hjm
      · exact List.mem_append.2 (Or.inl (hsub_ow0 j hj0))
      · exact List.mem_append.2 (Or.inr hjm)
    intro o ho
    rcases List.mem_append.1 ho with ho_ow | ho_m
    · unfold worldOwned at ho_ow
      rcases List.mem_append.1 ho_ow with h1 | hnd
      · rcases List.mem_append.1 h1 with htab | hfix
        · rw [List.flatMap_append] at htab
          rcases List.mem_append.1 htab with htab' | htab_loc
          · have ho0 : o ∈ worldOwned post S0' Nd0' ++ mptObjIvls post Nm0' (locN s "m") :=
              List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl htab')))))
            rcases hog0 o ho0 with rfl | ⟨j, hj0, hin_j⟩ | hfresh
            · exact Or.inl rfl
            · exact Or.inr (Or.inl ⟨j, hsub_owm j hj0, hin_j⟩)
            · exact Or.inr (Or.inr hfresh)
          · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at htab_loc
            rcases htab_loc with ho_t1 | ho_t2
            · rw [hfp_t1] at ho_t1
              exact Or.inr (Or.inl ⟨o, List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl
                (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨t1, ht1_S, ho_t1⟩)))))),
                ⟨le_rfl, le_rfl⟩⟩)
            · rw [hfp_t2] at ho_t2
              exact Or.inr (Or.inl ⟨o, List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl
                (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨t2, ht2_S, ho_t2⟩)))))),
                ⟨le_rfl, le_rfl⟩⟩)
        · have ho0 : o ∈ worldOwned post S0' Nd0' ++ mptObjIvls post Nm0' (locN s "m") :=
            List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))))
          rcases hog0 o ho0 with rfl | ⟨j, hj0, hin_j⟩ | hfresh
          · exact Or.inl rfl
          · exact Or.inr (Or.inl ⟨j, hsub_owm j hj0, hin_j⟩)
          · exact Or.inr (Or.inr hfresh)
      · have ho0 : o ∈ worldOwned post S0' Nd0' ++ mptObjIvls post Nm0' (locN s "m") :=
          List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hnd)))
        rcases hog0 o ho0 with rfl | ⟨j, hj0, hin_j⟩ | hfresh
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨j, hsub_owm j hj0, hin_j⟩)
        · exact Or.inr (Or.inr hfresh)
    · have ho0 : o ∈ worldOwned post S0' Nd0' ++ mptObjIvls post Nm0' (locN s "m") :=
        List.mem_append.2 (Or.inr ho_m)
      rcases hog0 o ho0 with rfl | ⟨j, hj0, hin_j⟩ | hfresh
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨j, hsub_owm j hj0, hin_j⟩)
      · exact Or.inr (Or.inr hfresh)
  have hfr_both : FrameOutside s post
      (worldOwned s S Nd ++ mptObjIvls s Nm (locN s "m") ++ R s ++ [freeGap s])
      (heapFree s) := by
    intro a hkeep hfresh
    refine hfr0 a (fun j hj hcj => hkeep j ?_ hcj) hfresh
    rcases List.mem_append.1 hj with hj12 | hfg
    · apply List.mem_append.2; left
      rcases List.mem_append.1 hj12 with hj0m | hjR
      · apply List.mem_append.2; left
        rcases List.mem_append.1 hj0m with hj0 | hjm
        · exact List.mem_append.2 (Or.inl (hsub_ow0 j hj0))
        · exact List.mem_append.2 (Or.inr hjm)
      · exact List.mem_append.2 (Or.inr hjR)
    · exact List.mem_append.2 (Or.inr hfg)
  exact ⟨S0', Nd0', Nm0', hW_both, by simp, by simp, ht1_unass, ht2_unass,
    hfp_t1, hfp_t2, hhdr_t1, hhdr_t2, hm_both, hd0', hog_both, hfr_both⟩

theorem pBounded_return_csr {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (e : ExpHOL 64) : PBounded P (.return e) 0 :=
  ⟨TerminatingProgBoundedOn.of_clock (fun s => by
      rw [evaluateHOLFiniteState_return]
      split
      · rfl
      · split <;> rfl),
   ⟨fun s _ _ _ hr => absurd hr (return_ne_none s e)⟩⟩

theorem pBounded_call0_csr
    {P Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop}
    {fname : MlS} {args : List (ExpHOL 64)} {B : Nat}
    (hfb : TerminatingFunBoundedOn Pc fname B)
    (hspec : FunSpec Pc Qc fname)
    (hentry : CallEntryOn P Pc fname args)
    (hret : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (post : PanSemStateFiniteExact 64 F)
      (v : ValueHOL 64), s.code = originalRuntimeCode → P s →
      Qc (callEntryStateHOLFinite s callee) (some (.returned v)) post →
      P { post with locals := s.locals }) :
    PBounded P (.call (some (none, none)) fname args) (B + 1) :=
  ⟨TerminatingProgBoundedOn.call_on hfb none args hentry,
   Hoare.call0 hspec hentry (fun s callee post v hc hP hQc _ => hret s callee post v hc hP hQc)
     (fun _ _ hr _ h => absurd h hr)⟩

theorem pBounded_callLocal_csr
    {P Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {name fname : MlS} {args : List (ExpHOL 64)} {B : Nat}
    (hfb : TerminatingFunBoundedOn Pc fname B)
    (hentry : CallEntryOn P Pc fname args)
    (hres : DecCallResumeOn P P name fname args) :
    PBounded P (.call (some (some (.local, name), none)) fname args) (B + 1) := by
  refine ⟨TerminatingProgBoundedOn.call_on hfb (some (.local, name)) args hentry, ?_⟩
  refine ⟨fun {F} s hc hP _ hr => ?_⟩
  rw [evaluateHOLFiniteState_call] at hr ⊢
  rcases ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · rw [ha] at hr; simp at hr
  · simp only [ha] at hr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body, callee, ret⟩
    · simp [hl] at hr
    · simp only [hl] at hr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hr
      · simp only [hz, ↓reduceIte] at hr ⊢
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, post⟩
        simp only [hb] at hr ⊢
        cases res with
        | none => simp at hr
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hr ⊢
            split at hr
            · rename_i hsh
              rw [if_pos hsh]
              split at hr
              · rename_i hv
                rw [if_pos hv]
                exact hres s vs body callee ret v post hc hP ha hl hb
              · simp at hr
            · simp at hr
          | _ => simp at hr

def CsrTablesAt {F : Type} (s : PanSemStateFiniteExact 64 F) (cache roots : Nat) : Prop :=
  ArenaReady s ∧ cache ≠ roots ∧ ∃ S Nd,
    WorldTypedWith s S Nd ∧ cache ∈ S ∧ roots ∈ S ∧
    (∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ cache) ∧
    (∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ roots)

theorem localsFree_csrTablesAt (cache roots : Nat) :
    LocalsFree (fun s => CsrTablesAt s cache roots) := by
  intro F s locals k h
  obtain ⟨hA, hne, S, Nd, hW, hc, hr, hcl, hrl⟩ := h
  exact ⟨localsFree_arenaReady s locals k hA, hne, S, Nd,
    (worldTypedWith_with_locals_csr s locals k S Nd).2 hW,
    hc, hr, hcl, hrl⟩

theorem nodeHeap_append_disj_csr {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd1 Nd2 : List Nat}
    (h1 : NodeHeap s Nd1) (h2 : NodeHeap s Nd2)
    (hd : IvlsDisj (nodeExtents s Nd1) (nodeExtents s Nd2)) :
    NodeHeap s (Nd1 ++ Nd2) := by
  have hroot1 : ∀ {v}, RootIn Nd1 v → RootIn (Nd1 ++ Nd2) v := by
    rintro v (rfl | hv)
    · exact Or.inl rfl
    · exact Or.inr (List.mem_append_left _ hv)
  have hroot2 : ∀ {v}, RootIn Nd2 v → RootIn (Nd1 ++ Nd2) v := by
    rintro v (rfl | hv)
    · exact Or.inl rfl
    · exact Or.inr (List.mem_append_right _ hv)
  have hnivl1 : ∀ n ∈ Nd1, nodeIvl s n ∈ nodeExtents s Nd1 := fun n hn =>
    List.mem_flatMap.2 ⟨n, hn, by simp⟩
  have hnivl2 : ∀ n ∈ Nd2, nodeIvl s n ∈ nodeExtents s Nd2 := fun n hn =>
    List.mem_flatMap.2 ⟨n, hn, by simp⟩
  refine ⟨fun n hn => ?_, fun n hn m hm hne => ?_⟩
  · rcases List.mem_append.1 hn with hn1 | hn2
    · obtain ⟨hk3, hal, hin, hw, hext, hbr, hkey, hb16, hb56, hb168⟩ := h1.1 n hn1
      refine ⟨hk3, hal, hin, hw,
        fun h2k => hroot1 (hext h2k),
        fun h3k i hi => hroot1 (hbr h3k i hi),
        fun h12 => ?_, hb16, hb56, hb168⟩
      rcases hkey h12 with hz | ⟨hnib, halp, hinp, hdjp⟩
      · exact Or.inl hz
      · right
        refine ⟨hnib, halp, hinp, fun m hm => ?_⟩
        rcases List.mem_append.1 hm with hm1 | hm2
        · exact hdjp m hm1
        · by_cases hlen0 : memW s (n + 40) = 0
          · exact Or.inl hlen0
          · have hp1 : (memW s (n + 32), memW s (n + 40)) ∈ nodeExtents s Nd1 := by
              unfold nodeExtents
              exact List.mem_flatMap.2 ⟨n, hn1, by simp [nodePath, h12, hlen0]⟩
            exact hd _ hp1 _ (hnivl2 m hm2)
    · obtain ⟨hk3, hal, hin, hw, hext, hbr, hkey, hb16, hb56, hb168⟩ := h2.1 n hn2
      refine ⟨hk3, hal, hin, hw,
        fun h2k => hroot2 (hext h2k),
        fun h3k i hi => hroot2 (hbr h3k i hi),
        fun h12 => ?_, hb16, hb56, hb168⟩
      rcases hkey h12 with hz | ⟨hnib, halp, hinp, hdjp⟩
      · exact Or.inl hz
      · right
        refine ⟨hnib, halp, hinp, fun m hm => ?_⟩
        rcases List.mem_append.1 hm with hm1 | hm2
        · by_cases hlen0 : memW s (n + 40) = 0
          · exact Or.inl hlen0
          · have hp2 : (memW s (n + 32), memW s (n + 40)) ∈ nodeExtents s Nd2 := by
              unfold nodeExtents
              exact List.mem_flatMap.2 ⟨n, hn2, by simp [nodePath, h12, hlen0]⟩
            exact (hd _ (hnivl1 m hm1) _ hp2).flip
        · exact hdjp m hm2
  · rcases List.mem_append.1 hn with hn1 | hn2 <;>
    rcases List.mem_append.1 hm with hm1 | hm2
    · exact h1.2 n hn1 m hm1 hne
    · exact hd _ (hnivl1 n hn1) _ (hnivl2 m hm2)
    · exact (hd _ (hnivl1 m hm1) _ (hnivl2 n hn2)).flip
    · exact h2.2 n hn2 m hm2 hne

theorem worldTypedWith_append_mptNodes_csr {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd Nm : List Nat} {m : Nat}
    (hW : WorldTypedWith s S Nd) (hm : MptObjInWith s S Nm m)
    (hd : IvlsDisj (mptObjIvls s Nm m) (nodeExtents s Nd)) :
    WorldTypedWith s S (Nd ++ Nm) := by
  obtain ⟨hT, hJ, hF, hTr⟩ := hW
  have hd_nodes : IvlsDisj (nodeExtents s Nd) (nodeExtents s Nm) :=
    fun o1 ho1 o2 ho2 => (hd o2 (List.mem_cons_of_mem _ ho2) o1 ho1).flip
  have hNH : NodeHeap s (Nd ++ Nm) :=
    nodeHeap_append_disj_csr hTr.1 hm.2.2.2.2.1 hd_nodes
  have hroot1 : ∀ {v}, RootIn Nd v → RootIn (Nd ++ Nm) v := by
    rintro v (rfl | hv)
    · exact Or.inl rfl
    · exact Or.inr (List.mem_append_left _ hv)
  refine ⟨hT, hJ, hF, ⟨hNH, ?_, ?_⟩⟩
  · intro o ho
    unfold nodeExtents at ho
    rw [List.flatMap_append] at ho
    rcases List.mem_append.1 ho with ho_nd | ho_nm
    · exact hTr.2.1 o ho_nd
    · exact (hm.2.2.2.2.2.2 o ho_nm).2
  · intro hnz
    obtain ⟨hr24, hr32⟩ := hTr.2.2 hnz
    exact ⟨hroot1 hr24, fun hm32 i hi => hroot1 (hr32 hm32 i hi)⟩

theorem mptObjInWith_transfer_bytes_csr {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hs : ArenaReady s) (hp : ArenaReady post)
    (hag : AllocatorGrows s post) {S S' Nd Nd' Nm : List Nat} {m : Nat}
    (hm : MptObjInWith s S Nm m)
    (hd : IvlsDisj (mptObjIvls s Nm m) (nodeExtents s Nd))
    (hg : OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd'))
    (hu_m : R10Shards.P26_P28.IvlUnhit s post (m, 16))
    (hu_rec : ∀ n ∈ Nm, R10Shards.P26_P28.IvlUnhit s post (nodeIvl s n))
    (hu_byte : ∀ n ∈ Nm, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
      ∀ k, k < memW s (n + 40) → memB post (memW s (n + 32) + k) = memB s (memW s (n + 32) + k)) :
    MptObjInWith post S' Nm m ∧
      IvlsDisj (mptObjIvls post Nm m) (nodeExtents post Nd') ∧
      mptObjIvls post Nm m = mptObjIvls s Nm m := by
  obtain ⟨hn, hext⟩ := R10Shards.P26_P28.nodeHeap_congr_bytes hs.1 hp.1 hag
    hm.2.2.2.2.1 hu_rec hu_byte
  have hivl : mptObjIvls post Nm m = mptObjIvls s Nm m := by
    simp only [mptObjIvls, hext]
  have hdis : IvlsDisj (mptObjIvls post Nm m) (worldOwned post S' Nd') := by
    rw [hivl]
    exact ivlsDisj_ownedGrows_csr hs.2 hp.2 hg (mptObjInWith_allocated_csr hm)
      (mptObjInWith_disj_world_csr hm hd)
  have hroot : memW post m = memW s m :=
    R10Shards.P26_P28.memW_eq_of_ivlUnhit hu_m hm.2.1.1
      (P3MptSet.ivl_allocated_bound hs.2 hm.1) ⟨le_rfl, by omega⟩
  refine ⟨mptObjInWith_of_parts_csr (hag.allocated hm.1)
    (P3MptSet.wordsOK_transfer hs.1 hp.1 hm.2.1) hn ?_ hdis ?_, ?_, hivl⟩
  · rw [hroot]
    exact hm.2.2.2.2.2.1
  · intro o ho
    rw [hext] at ho
    exact (hm.2.2.2.2.2.2 o ho).1
  · intro o ho j hj
    exact hdis o ho j (List.mem_append.mpr (Or.inr hj))

theorem worldEff_liveMpt_csr {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    {S Nd Nm : List Nat} {m : Nat}
    (hs : ArenaReady s)
    (hB_ok : ∀ gs ∈ B, gs ∈ globalBuffers ∧ gs.1 ∉ typedRecords.map Prod.fst)
    (hcore_out : ∀ g ∈ coreWorldGlobals, ofString g ∉ gw.map ofString)
    (heff : R16Shards.WorldEff s post Rl B gw)
    (hW : WorldTypedWith s S Nd)
    (hm : MptObjInWith s S Nm m)
    (hd : IvlsDisj (mptObjIvls s Nm m) (nodeExtents s Nd))
    (hR : IvlsDisj Rl (worldTypedIvls s S Nd ++ mptObjIvls s Nm m)) :
    WorldTypedWith post S Nd ∧
      MptObjInWith post S Nm m ∧
      IvlsDisj (mptObjIvls post Nm m) (nodeExtents post Nd) ∧
      mptObjIvls post Nm m = mptObjIvls s Nm m ∧
      nodeExtents post Nd = nodeExtents s Nd ∧
      (∀ t ∈ S, htabFootprint post t = htabFootprint s t) ∧
      (∀ t ∈ S, ∀ k, k < 11 → hdr post t k = hdr s t k) ∧
      (∀ a ∈ worldRoleSlots post ++ journalRoleSlots post,
        a ∈ worldRoleSlots s ++ journalRoleSlots s) ∧
      OwnedGrows s post (worldOwned s S Nd) (worldOwned post S Nd) := by
  have hAp : ArenaReady post := heff.arena
  have hag : AllocatorGrows s post := ⟨heff.hp_lo, heff.sp_hi⟩
  have hcore : ∀ g ∈ coreWorldGlobals, globN post g = globN s g :=
    fun g hg => R10Shards.P26_P28.globN_eq_of_lookup (heff.gw_kept (ofString g) (hcore_out g hg))
  have hlow : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 :=
    ⟨R10Shards.P26_P28.mem_low_eq_of_domain_writes heff.out_dom hs.1 (by rw [sourceBase_val]; omega),
     R10Shards.P26_P28.mem_low_eq_of_domain_writes heff.out_dom hs.1 (by rw [sourceBase_val]; omega)⟩
  obtain ⟨hT, hJ, hF, hTr⟩ := hW
  have hR_wti : IvlsDisj Rl (worldTypedIvls s S Nd) :=
    fun r hr i hi => hR r hr i (List.mem_append_left _ hi)
  have hR_mpt : IvlsDisj Rl (mptObjIvls s Nm m) :=
    fun r hr o ho => hR r hr o (List.mem_append_right _ ho)
  let keep0 : List Ivl := Rl ++ B.map (bufferRegion s) ++ [freeGap s]
  have hfr_pos : ∀ a : BitVec 64, post.memory a ≠ s.memory a →
      (∃ j ∈ keep0, CellHitsPos a.toNat j) ∨ CellHitsPos a.toNat (heapFree s) := by
    intro a hne
    rcases heff.cell_frame a hne with ⟨ivl, hivl, hhit⟩ | ⟨gs, hgs, hhit⟩ | hfg | hhf
    · left; refine ⟨ivl, ?_, hhit⟩
      simp only [keep0, List.mem_append]; exact Or.inl (Or.inl hivl)
    · left; refine ⟨bufferRegion s gs, ?_, hhit⟩
      simp only [keep0, List.mem_append]; exact Or.inl (Or.inr (List.mem_map.2 ⟨gs, hgs, rfl⟩))
    · left; refine ⟨freeGap s, ?_, hfg⟩
      simp only [keep0, List.mem_append, List.mem_singleton]; exact Or.inr trivial
    · exact Or.inr hhf
  have hu_wti_aligned : ∀ i ∈ worldTypedIvls s S Nd, Allocated s i → i.1 % 8 = 0 → i.2 % 8 = 0 →
      R10Shards.P26_P28.IvlUnhit s post i := by
    intro i hi hal hi1 hi2
    refine R10Shards.P26_P28.ivlUnhit_of_cellHitsPos hi1 hi2 hfr_pos (fun j hj => ?_)
      (R10Shards.P26_P28.disj_allocated_heapFree hs.2 hal)
    simp only [keep0, List.mem_append, List.mem_singleton] at hj
    rcases hj with (hjR | hjB) | rfl
    · exact Disj.flip (hR_wti j hjR i hi)
    · obtain ⟨gs, hgs, rfl⟩ := List.mem_map.1 hjB
      obtain ⟨hgs_gb, hgs_nt⟩ := hB_ok gs hgs
      exact Disj.flip (R10Shards.P26_P28.untypedBuf_disj_worldTypedIvls ⟨hT, hJ, hF, hTr⟩ gs hgs_gb hgs_nt i hi)
    · exact R10Shards.P26_P28.disj_allocated_freeGap hs.2 hal
  have hu_mpt_aligned : ∀ o ∈ mptObjIvls s Nm m, Allocated s o → o.1 % 8 = 0 → o.2 % 8 = 0 →
      R10Shards.P26_P28.IvlUnhit s post o := by
    intro o ho hal ho1 ho2
    refine R10Shards.P26_P28.ivlUnhit_of_cellHitsPos ho1 ho2 hfr_pos (fun j hj => ?_)
      (R10Shards.P26_P28.disj_allocated_heapFree hs.2 hal)
    simp only [keep0, List.mem_append, List.mem_singleton] at hj
    rcases hj with (hjR | hjB) | rfl
    · exact Disj.flip (hR_mpt j hjR o ho)
    · obtain ⟨gs, hgs, rfl⟩ := List.mem_map.1 hjB
      exact Disj.flip (mptObjInWith_disj_buffer_csr hm (hB_ok gs hgs).1 _ List.mem_cons_self o ho)
    · exact R10Shards.P26_P28.disj_allocated_freeGap hs.2 hal
  have hu_fix_wti : ∀ i ∈ worldTypedIvls s S Nd, i ∈ fixedObjects s → i.2 ≠ 0 →
      R10Shards.P26_P28.IvlUnhit s post i := by
    intro i hwti hfi hpos
    rcases hF.1 i hfi with h0 | ⟨hal, hw⟩
    · exact absurd h0 hpos
    · exact hu_wti_aligned i hwti hal hw.1 hw.2.1
  have hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, R10Shards.P26_P28.IvlUnhit s post i := by
    intro t ht i hi
    have hal := ((hT.2.1 t ht).2 i hi).1
    have hw := ((hT.2.1 t ht).1.1 i hi).2
    refine hu_wti_aligned i ?_ hal hw.1 hw.2.1
    unfold worldTypedIvls
    apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
    apply List.mem_append.2; left; apply List.mem_append.2; left
    exact List.mem_flatMap.2 ⟨t, ht, hi⟩
  have hu_ws : globN s "ws" ≠ 0 → R10Shards.P26_P28.IvlUnhit s post (globN s "ws", 40) := fun hnz =>
    hu_fix_wti _
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
          exact List.mem_map.2 ⟨("ws", 40), by simp [typedRecords], by simp [hnz]⟩)
      (by simpa [hnz] using R10Shards.P26_P28.typedRecord_mem_fixedObjects s (r := ("ws", 40)) (by simp [typedRecords]))
      (by simp)
  have hu_bs : globN s "bs" ≠ 0 → R10Shards.P26_P28.IvlUnhit s post (globN s "bs", 80) := fun hnz =>
    hu_fix_wti _
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
          exact List.mem_map.2 ⟨("bs", 80), by simp [typedRecords], by simp [hnz]⟩)
      (by simpa [hnz] using R10Shards.P26_P28.typedRecord_mem_fixedObjects s (r := ("bs", 80)) (by simp [typedRecords]))
      (by simp)
  have hu_ts : globN s "ts" ≠ 0 → R10Shards.P26_P28.IvlUnhit s post (globN s "ts", 72) := fun hnz =>
    hu_fix_wti _
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
          exact List.mem_map.2 ⟨("ts", 72), by simp [typedRecords], by simp [hnz]⟩)
      (by simpa [hnz] using R10Shards.P26_P28.typedRecord_mem_fixedObjects s (r := ("ts", 72)) (by simp [typedRecords]))
      (by simp)
  have hu_bo : globN s "bo" ≠ 0 → R10Shards.P26_P28.IvlUnhit s post (globN s "bo", 88) := fun hnz =>
    hu_fix_wti _
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
          exact List.mem_map.2 ⟨("bo", 88), by simp [typedRecords], by simp [hnz]⟩)
      (by simpa [hnz] using R10Shards.P26_P28.typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by simp [typedRecords]))
      (by simp)
  have hu_jr : globN s "journal_cap" ≠ 0 →
      R10Shards.P26_P28.IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap") := fun hcnz =>
    hu_fix_wti _
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; right; simp [hcnz])
      (by unfold fixedObjects; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; right; simp [hcnz])
      (by dsimp only; omega)
  have hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 → R10Shards.P26_P28.IvlUnhit s post i := fun i hi h24 =>
    hu_fix_wti i
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; right; exact hi)
      (by unfold fixedObjects; apply List.mem_append.2; left; apply List.mem_append.2; right; exact hi)
      (by omega)
  have hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → R10Shards.P26_P28.IvlUnhit s post i := fun i hi hpos =>
    hu_fix_wti i
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; right; exact hi)
      (by unfold fixedObjects; exact List.mem_append.2 (Or.inr hi))
      hpos
  have hu_nd_rec : ∀ n ∈ Nd, R10Shards.P26_P28.IvlUnhit s post (nodeIvl s n) := fun n hn => by
    have hal := (hTr.1.1 n hn).2.1
    have hw := (hTr.1.1 n hn).2.2.2.1
    refine hu_wti_aligned _ ?_ hal hw.1 hw.2.1
    unfold worldTypedIvls; refine List.mem_append.2 (Or.inr ?_)
    unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodeIvl]⟩
  have hu_nd_byte : ∀ n ∈ Nd, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
      ∀ k, k < memW s (n + 40) → memB post (memW s (n + 32) + k) = memB s (memW s (n + 32) + k) := by
    intro n hn h12 hlen0 k hk
    have h264 : heapLimit ≤ 2 ^ 64 := by decide
    rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, hal_p, hin_p, _⟩
    · exact absurd h0 hlen0
    · have hp_wti : (memW s (n + 32), memW s (n + 40)) ∈ worldTypedIvls s S Nd := by
        unfold worldTypedIvls; refine List.mem_append.2 (Or.inr ?_)
        unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodePath, h12, hlen0]⟩
      by_contra hne_b
      have ha_lt : memW s (n + 32) + k < 2 ^ 64 := by have := hin_p.2; dsimp at this; omega
      rcases heff.byte_frame _ ha_lt hne_b with ⟨ivl, hivl, hin_ivl⟩ | ⟨gs, hgs, hin_gs⟩ | hfg | hhf
      · have hdj := hR_wti ivl hivl _ hp_wti
        unfold InIvl at hin_ivl; rcases hdj with h0 | h0 | h1 | h2 <;> (dsimp at *; omega)
      · obtain ⟨hgs_gb, hgs_nt⟩ := hB_ok gs hgs
        have hdj := R10Shards.P26_P28.untypedBuf_disj_worldTypedIvls ⟨hT, hJ, hF, hTr⟩ gs hgs_gb hgs_nt _ hp_wti
        unfold InIvl at hin_gs; rcases hdj with h0 | h0 | h1 | h2 <;> (dsimp at *; omega)
      · have hdj := R10Shards.P26_P28.disj_allocated_freeGap hs.2 hal_p
        unfold InIvl at hfg; rcases hdj with h0 | h0 | h1 | h2 <;> (dsimp at *; omega)
      · have hdj := R10Shards.P26_P28.disj_allocated_heapFree hs.2 hal_p
        unfold InIvl at hhf; rcases hdj with h0 | h0 | h1 | h2 <;> (dsimp at *; omega)
  have hbo_eq := (R10Shards.P26_P28.blockOutObjects_eq_of_bo_unhit hs.2 hF (hcore "bo" (by decide))
    hT.2.2.2.2.2.2.2.2.2.2.1 hu_bo hu_bo_lst).1
  have hbal_eq := (R10Shards.P26_P28.balObjects_eq_of_unhit hs.2 hT hF (hcore "bal_accounts" (by decide))
    hu_tab hu_bal hlow).1
  have hwrs_eq := R10Shards.P26_P28.worldRoleSlots_eq_of_unhit hs.2 hT hF hcore hu_tab hu_ws hu_bs hu_ts hu_bal hlow
  have hjrs_eq := (R10Shards.P26_P28.journalRoleSlots_eq_of_unhit hs.1 hAp.1 hs.2 hag
    (fun _ hx => hx) hJ hF hcore hu_ts hu_jr).1
  obtain ⟨hF_post, hfix_new⟩ := R10Shards.P26_P28.fixedTyped_of_freshBufsOK hs hAp hag hF
    (hcore "journal" (by decide)) (hcore "journal_cap" (by decide)) hbo_eq hbal_eq heff.fresh_bufs
  obtain ⟨hWT_post, hOG, hne_eq, hfp_eq⟩ := R10Shards.P26_P28.worldTypedWith_congr_w1 hs hAp hag hcore
    ⟨hT, hJ, hF, hTr⟩ hu_tab hu_ws hu_bs hu_ts hu_bo hu_jr hu_bo_lst hu_bal hu_nd_rec hu_nd_byte
    hlow hF_post hfix_new
  have hhdr_eq : ∀ t ∈ S, ∀ k, k < 11 → hdr post t k = hdr s t k := by
    have h264_he : heapEnd ≤ 2 ^ 64 := by decide
    intro t ht
    have hwf := (hT.2.1 t ht).1
    have ht_fp : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
    have ht8 : t % 8 = 0 := (hwf.1 _ ht_fp).2.1
    have hhi : t + 88 ≤ 2 ^ 64 := by have := (hwf.1 _ ht_fp).1.2; dsimp at this; omega
    exact (R10Shards.P26_P28.htabFootprint_eq_of_hdr_unhit ht8 hhi (hu_tab t ht _ ht_fp)).1
  have hu_m : R10Shards.P26_P28.IvlUnhit s post (m, 16) :=
    hu_mpt_aligned _ List.mem_cons_self hm.1 hm.2.1.1 hm.2.1.2.1
  have hu_nm_rec : ∀ n ∈ Nm, R10Shards.P26_P28.IvlUnhit s post (nodeIvl s n) := fun n hn => by
    have hal := (hm.2.2.2.2.1.1 n hn).2.1
    have hw := (hm.2.2.2.2.1.1 n hn).2.2.2.1
    refine hu_mpt_aligned _ (List.mem_cons_of_mem _ ?_) hal hw.1 hw.2.1
    unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodeIvl]⟩
  have hu_nm_byte : ∀ n ∈ Nm, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
      ∀ k, k < memW s (n + 40) → memB post (memW s (n + 32) + k) = memB s (memW s (n + 32) + k) := by
    intro n hn h12 hlen0 k hk
    have h264 : heapLimit ≤ 2 ^ 64 := by decide
    rcases (hm.2.2.2.2.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, hal_p, hin_p, _⟩
    · exact absurd h0 hlen0
    · have hp_mpt : (memW s (n + 32), memW s (n + 40)) ∈ mptObjIvls s Nm m := by
        refine List.mem_cons_of_mem _ ?_
        unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodePath, h12, hlen0]⟩
      by_contra hne_b
      have ha_lt : memW s (n + 32) + k < 2 ^ 64 := by have := hin_p.2; dsimp at this; omega
      rcases heff.byte_frame _ ha_lt hne_b with ⟨ivl, hivl, hin_ivl⟩ | ⟨gs, hgs, hin_gs⟩ | hfg | hhf
      · have hdj := hR_mpt ivl hivl _ hp_mpt
        unfold InIvl at hin_ivl; rcases hdj with h0 | h0 | h1 | h2 <;> (dsimp at *; omega)
      · have hdj := mptObjInWith_disj_buffer_csr hm (hB_ok gs hgs).1 _ List.mem_cons_self _ hp_mpt
        unfold InIvl at hin_gs; rcases hdj with h0 | h0 | h1 | h2 <;> (dsimp at *; omega)
      · have hdj := R10Shards.P26_P28.disj_allocated_freeGap hs.2 hal_p
        unfold InIvl at hfg; rcases hdj with h0 | h0 | h1 | h2 <;> (dsimp at *; omega)
      · have hdj := R10Shards.P26_P28.disj_allocated_heapFree hs.2 hal_p
        unfold InIvl at hhf; rcases hdj with h0 | h0 | h1 | h2 <;> (dsimp at *; omega)
  obtain ⟨hm_post, hd_post, hm_ivl_eq⟩ :=
    mptObjInWith_transfer_bytes_csr hs hAp hag hm hd hOG hu_m hu_nm_rec hu_nm_byte
  refine ⟨hWT_post, hm_post, hd_post, hm_ivl_eq, hne_eq, hfp_eq, hhdr_eq, ?_, hOG⟩
  intro a ha
  rwa [hwrs_eq, hjrs_eq] at ha

def CsrLiveAt {F : Type} (s : PanSemStateFiniteExact 64 F)
    (cache roots m : Nat) : Prop :=
  ArenaReady s ∧ cache ≠ roots ∧ ∃ S Nd Nm,
    WorldTypedWith s S Nd ∧ cache ∈ S ∧ roots ∈ S ∧
    (∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ cache) ∧
    (∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ roots) ∧
    MptObjInWith s S Nm m ∧
    IvlsDisj (mptObjIvls s Nm m) (nodeExtents s Nd)

theorem localsFree_csrLiveAt (cache roots m : Nat) :
    LocalsFree (fun s => CsrLiveAt s cache roots m) := by
  intro F s locals k h
  obtain ⟨hA, hne, S, Nd, Nm, hW, hc, hr, hcl, hrl, hm, hd⟩ := h
  exact ⟨localsFree_arenaReady s locals k hA, hne, S, Nd, Nm,
    (worldTypedWith_with_locals_csr s locals k S Nd).2 hW,
    hc, hr, hcl, hrl, (mptObjInWith_with_locals_csr s locals k S Nm m).2 hm, hd⟩

theorem csrLiveAt_tables {F : Type} {s : PanSemStateFiniteExact 64 F}
    {cache roots m : Nat} (h : CsrLiveAt s cache roots m) :
    CsrTablesAt s cache roots := by
  obtain ⟨hA, hne, S, Nd, Nm, hW, hc, hr, hcl, hrl, hm, hd⟩ := h
  exact ⟨hA, hne, S, Nd, hW, hc, hr, hcl, hrl⟩

theorem worldEff_csrLiveAt {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    {cache roots m : Nat}
    (hs : CsrLiveAt s cache roots m)
    (hB_ok : ∀ gs ∈ B, gs ∈ globalBuffers ∧ gs.1 ∉ typedRecords.map Prod.fst)
    (hcore_out : ∀ g ∈ coreWorldGlobals, ofString g ∉ gw.map ofString)
    (heff : R16Shards.WorldEff s post Rl B gw)
    (hR : ∀ S Nd Nm, WorldTypedWith s S Nd →
      MptObjInWith s S Nm m →
      IvlsDisj (mptObjIvls s Nm m) (nodeExtents s Nd) →
      IvlsDisj Rl (worldTypedIvls s S Nd ++ mptObjIvls s Nm m)) :
    CsrLiveAt post cache roots m := by
  obtain ⟨hA, hne, S, Nd, Nm, hW, hc, hr, hcl, hrl, hm, hd⟩ := hs
  obtain ⟨hWp, hmp, hdp, _, _, _, _, hroles, _⟩ :=
    worldEff_liveMpt_csr hA hB_ok hcore_out heff hW hm hd (hR S Nd Nm hW hm hd)
  exact ⟨heff.arena, hne, S, Nd, Nm, hWp, hc, hr,
    fun a ha => hcl a (hroles a ha), fun a ha => hrl a (hroles a ha), hmp, hdp⟩

theorem mptObjStep_csrLiveAt {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {cache roots : Nat}
    (hs : CsrLiveAt s cache roots (locN s "m"))
    (hstep : MptObjStep R gw keep s post)
    (hR_z : ∀ j ∈ R s, j.2 = 0 → j.1 % 8 = 0)
    (hR_ti : ∀ S Nd Nm, WorldTypedWith s S Nd →
      MptObjInWith s S Nm (locN s "m") →
      IvlsDisj (mptObjIvls s Nm (locN s "m")) (nodeExtents s Nd) →
      IvlsDisj (R s) (worldTypedIvls s S Nd ++ mptObjIvls s Nm (locN s "m"))) :
    CsrLiveAt post cache roots (locN s "m") := by
  obtain ⟨hA, hne, S, Nd, Nm, hW, hc, hr, hcl, hrl, hm, hd⟩ := hs
  have hR := hR_ti S Nd Nm hW hm hd
  have hRN : IvlsDisj (R s) (nodeExtents s Nd) := by
    intro r hr i hi
    exact hR r hr i (List.mem_append_left _ (by
      unfold worldTypedIvls
      exact List.mem_append_right _ hi))
  obtain ⟨S', Nd', Nm', hWp, hc', hr', hcl', hrl', _, _, _, _, hmp, hdp, _, _⟩ :=
    mptObjStep_preserves_two_local_tables_csr hA hW hc hr hne hcl hrl hm hd
      hstep hR_z hR hRN
  exact ⟨hstep.1, hne, S' ++ [cache, roots], Nd', Nm', hWp,
    hc', hr', hcl', hrl', hmp, hdp⟩

theorem csrTablesAt_worldOK {F : Type} {s : PanSemStateFiniteExact 64 F}
    {cache roots : Nat} (h : CsrTablesAt s cache roots) : WorldOK s := by
  obtain ⟨hA, _, S, Nd, hW, _⟩ := h
  exact ⟨hA, S, (worldTyped_iff_with s S).2 ⟨Nd, hW⟩⟩

theorem csrLiveAt_mptObjReady {F : Type} {s : PanSemStateFiniteExact 64 F}
    {cache roots : Nat} (h : CsrLiveAt s cache roots (locN s "m")) :
    MptObjReady s := by
  obtain ⟨hA, _, S, Nd, Nm, hW, _, _, _, _, hm, hd⟩ := h
  exact mptObjReady_of_parts_csr hA hW hm hd

theorem htabExit_csrTablesAt {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {cache roots : Nat}
    (hs : CsrTablesAt s cache roots)
    (ht : locN s "t" = cache ∨ locN s "t" = roots)
    (hexit : HtabExit s post) (hbe : post.be = s.be) :
    CsrTablesAt post cache roots := by
  obtain ⟨hA, hne, S, Nd, hW, hc, hr, hcl, hrl⟩ := hs
  have htS : locN s "t" ∈ S := ht.elim (fun h => h ▸ hc) (fun h => h ▸ hr)
  have htl : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ locN s "t" := by
    rcases ht with ht | ht
    · simpa only [ht] using hcl
    · simpa only [ht] using hrl
  obtain ⟨hWp, hwrs, hjrs, _⟩ :=
    worldTypedWith_htab_set_local_csr hA hW htS htl hexit hbe
  exact ⟨hexit.1, hne, S, Nd, hWp, hc, hr,
    by simpa only [hwrs, hjrs] using hcl,
    by simpa only [hwrs, hjrs] using hrl⟩

theorem htabExit_csrLiveAt {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {cache roots m : Nat}
    (hs : CsrLiveAt s cache roots m)
    (ht : locN s "t" = cache ∨ locN s "t" = roots)
    (hexit : HtabExit s post) (hbe : post.be = s.be) :
    CsrLiveAt post cache roots m := by
  obtain ⟨hA, hne, S, Nd, Nm, hW, hc, hr, hcl, hrl, hm, hd⟩ := hs
  have htS : locN s "t" ∈ S := ht.elim (fun h => h ▸ hc) (fun h => h ▸ hr)
  have htl : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ locN s "t" := by
    rcases ht with ht | ht
    · simpa only [ht] using hcl
    · simpa only [ht] using hrl
  obtain ⟨hWp, hmp, hdp, _, hwrs, hjrs, _⟩ :=
    htabExit_local_liveMpt_csr hA hW htS htl hexit hbe hm hd
  exact ⟨hexit.1, hne, S, Nd, Nm, hWp, hc, hr,
    by simpa only [hwrs, hjrs] using hcl,
    by simpa only [hwrs, hjrs] using hrl, hmp, hdp⟩

theorem worldStep_csrTablesAt {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)} {cache roots : Nat}
    (hs : CsrTablesAt s cache roots)
    (hstep : WorldStep R gw keep Q s r post)
    (hR_z : ∀ j ∈ R s, j.2 = 0 → j.1 % 8 = 0)
    (hR : ∀ S Nd, WorldTypedWith s S Nd →
      IvlsDisj (R s) (worldTypedIvls s S Nd)) :
    CsrTablesAt post cache roots := by
  obtain ⟨hA, hne, S, Nd, hW, hc, hr, hcl, hrl⟩ := hs
  obtain ⟨S', Nd', hWp, hc', hr', hcl', hrl', _⟩ :=
    worldStep_preserves_two_local_tables_csr hA hW hc hr hne hcl hrl
      hstep hR_z (hR S Nd hW)
  exact ⟨hstep.1, hne, S' ++ [cache, roots], Nd', hWp, hc', hr', hcl', hrl'⟩

theorem worldStep_csrLiveAt {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)} {cache roots m : Nat}
    (hs : CsrLiveAt s cache roots m)
    (hstep : WorldStep R gw keep Q s r post)
    (hbe : post.be = s.be) (hag : AllocatorGrows s post)
    (hR_z : ∀ j ∈ R s, j.2 = 0 → j.1 % 8 = 0)
    (hR : ∀ S Nd Nm, WorldTypedWith s S Nd → MptObjInWith s S Nm m →
      IvlsDisj (mptObjIvls s Nm m) (nodeExtents s Nd) →
      IvlsDisj (R s) (worldTypedIvls s S Nd ++ mptObjIvls s Nm m))
    (hcells : ∀ S Nd Nm, WorldTypedWith s S Nd → MptObjInWith s S Nm m →
      IvlsDisj (mptObjIvls s Nm m) (nodeExtents s Nd) →
      ∀ o ∈ mptObjIvls s Nm m, o.2 ≠ 0 →
      ∀ a : BitVec 64, a.toNat % 8 = 0 → CellHits a.toNat o →
        (∀ j ∈ worldOwned s S Nd ++ R s ++ [freeGap s], ¬ CellHits a.toNat j) ∧
        ¬ CellHits a.toNat (heapFree s)) :
    CsrLiveAt post cache roots m := by
  obtain ⟨hA, hne, S, Nd, Nm, hW, hc, hr, hcl, hrl, hm, hd⟩ := hs
  have hR_all := hR S Nd Nm hW hm hd
  have hR_wti : IvlsDisj (R s) (worldTypedIvls s S Nd) :=
    fun r' hr' i hi => hR_all r' hr' i (List.mem_append_left _ hi)
  obtain ⟨S', Nd', hWp, hc', hr', hcl', hrl', _, _, _, _, _, hog, hfr⟩ :=
    worldStep_preserves_two_local_tables_csr hA hW hc hr hne hcl hrl
      hstep hR_z hR_wti
  have hu : ∀ o ∈ mptObjIvls s Nm m, o.2 ≠ 0 → P3MptSet.IvlUnhit s post o := by
    intro o ho hnz a ha hh
    obtain ⟨hkeep, hfresh⟩ := hcells S Nd Nm hW hm hd o ho hnz a ha hh
    exact hfr a hkeep hfresh
  obtain ⟨hm', hd', _⟩ :=
    mptObjInWith_transfer_csr hA hstep.1 hbe hag hm hd hog hu
  exact ⟨hstep.1, hne, S' ++ [cache, roots], Nd', Nm, hWp,
    hc', hr', hcl', hrl', hm', hd'⟩

def CsrTabs : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => CsrTablesAt s (locN s "cache") (locN s "new_roots")

def CsrMpt (name : String) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => CsrLiveAt s (locN s "cache") (locN s "new_roots") (locN s name)

theorem localsOnly_csrTabs : LocalsOnly ["cache", "new_roots"] CsrTabs := by
  intro F s locals k hl hs
  unfold CsrTabs
  rw [locN_congr s locals k "cache" (hl "cache" (by simp)),
    locN_congr s locals k "new_roots" (hl "new_roots" (by simp))]
  exact localsFree_csrTablesAt _ _ s locals k hs

theorem localsOnly_csrMpt (name : String) :
    LocalsOnly ["cache", "new_roots", name] (CsrMpt name) := by
  intro F s locals k hl hs
  unfold CsrMpt
  rw [locN_congr s locals k "cache" (hl "cache" (by simp)),
    locN_congr s locals k "new_roots" (hl "new_roots" (by simp)),
    locN_congr s locals k name (hl name (by simp))]
  exact localsFree_csrLiveAt _ _ _ s locals k hs

theorem csrTabs_worldOK {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hs : CsrTabs s) : WorldOK s := csrTablesAt_worldOK hs

theorem csrMpt_tabs (name : String) {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hs : CsrMpt name s) : CsrTabs s := csrLiveAt_tables hs

def CsrBound (name : String) (bound : Nat)
    (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => P s ∧ locN s name ≤ bound

theorem localsOnly_csrBound {names : List String}
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : LocalsOnly names P) (name : String) (bound : Nat) :
    LocalsOnly (name :: names) (CsrBound name bound P) := by
  intro F s locals k hl hs
  refine ⟨hP s locals k (fun n hn => hl n (by simp [hn])) hs.1, ?_⟩
  change locN { s with locals := locals, clock := k } name ≤ bound
  rw [locN_congr s locals k name (hl name (by simp))]
  exact hs.2

theorem callEntryOn_guestInv_csr
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → GuestInv s)
    (fname : MlS) (args : List (ExpHOL 64)) :
    CallEntryOn P GuestInv fname args := by
  intro F s values body callee ret hc hs ha hl
  exact guestInv_callEntry s callee (hP s hs)

theorem pBounded_readOnlyLocal_csr
    {names : List String} {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {fname name : MlS} {args : List (ExpHOL 64)} {B : Nat}
    (hP : LocalsOnly names P)
    (hG : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → GuestInv s)
    (hfb : TerminatingFunBoundedOn GuestInv fname B)
    (hro : ReadOnlyFn fname) (hne : ∀ n ∈ names, ofString n ≠ name) :
    PBounded P (.call (some (some (.local, name), none)) fname args) (B + 1) :=
  pBounded_callLocal_csr hfb (callEntryOn_guestInv_csr hG fname args)
    (hro.resumeOn hP hG name hne args)

theorem funSpec_resumeOn_csr
    {P Pc R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop}
    {fname name : MlS} {args : List (ExpHOL 64)}
    (hspec : FunSpec Pc Qc fname)
    (hentry : CallEntryOn P Pc fname args)
    (hret : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F)
      (values : List (ValueHOL 64)) (body : ProgHOL 64)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
      (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      s.code = originalRuntimeCode → P s →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values →
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      Qc (callEntryStateHOLFinite s callee) (some (.returned v)) post →
      R (setVarHOLFinite name v { post with locals := s.locals })) :
    DecCallResumeOn P R name fname args := by
  intro F s values body callee ret v post hc hs ha hl hb
  have hq := FunSpec.at_lookup hspec s hc values body callee ret hl
    (hentry s values body callee ret hc hs ha hl) (by rw [hb]; simp)
  rw [hb] at hq
  exact hret s values body callee ret v post hc hs ha hl hb hq

theorem pBounded_specLocal_csr
    {P Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop}
    {fname name : MlS} {args : List (ExpHOL 64)} {B : Nat}
    (hfb : TerminatingFunBoundedOn Pc fname B)
    (hspec : FunSpec Pc Qc fname)
    (hentry : CallEntryOn P Pc fname args)
    (hret : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F)
      (values : List (ValueHOL 64)) (body : ProgHOL 64)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
      (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      s.code = originalRuntimeCode → P s →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values →
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      Qc (callEntryStateHOLFinite s callee) (some (.returned v)) post →
      P (setVarHOLFinite name v { post with locals := s.locals })) :
    PBounded P (.call (some (some (.local, name), none)) fname args) (B + 1) :=
  pBounded_callLocal_csr hfb hentry (funSpec_resumeOn_csr hspec hentry hret)

theorem pBounded_readOnlyDecCall_csr
    {names : List String} {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {fname name : MlS} {args : List (ExpHOL 64)} {B Bc : Nat}
    {shape : ShapeHOL} {cont : ProgHOL 64}
    (hP : LocalsOnly names P)
    (hG : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → GuestInv s)
    (hfb : TerminatingFunBoundedOn GuestInv fname B)
    (hro : ReadOnlyFn fname) (hne : ∀ n ∈ names, ofString n ≠ name)
    (hb : PBounded P cont Bc) :
    PBounded P (.decCall name shape fname args cont) (B + Bc + 1) :=
  PBounded.decCallTrans hfb hP name hne shape args
    (callEntryOn_guestInv_csr hG fname args) (hro.resumeOn hP hG name hne args)
    hb.bounded hb.hoare

theorem callee_param_five_exp_csr {F : Type} (state : PanSemStateFiniteExact 64 F)
    (fname p1 p2 p3 p4 p5 : MlS) (s1 s2 s3 s4 s5 : ShapeHOL)
    (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname =
      some ([(p1, s1), (p2, s2), (p3, s3), (p4, s4), (p5, s5)], body, ret))
    (e1 e2 e3 e4 e5 : ExpHOL 64) (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [e1, e2, e3, e4, e5] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    ∃ v1 v2 v3 v4 v5,
      evalAt state e1 = some v1 ∧ evalAt state e2 = some v2 ∧
      evalAt state e3 = some v3 ∧ evalAt state e4 = some v4 ∧
      evalAt state e5 = some v5 ∧
      callee.lookup p1 = some v1 ∧ callee.lookup p2 = some v2 ∧
      callee.lookup p3 = some v3 ∧ callee.lookup p4 = some v4 ∧
      callee.lookup p5 = some v5 := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact] at hargs
  rcases he1 : evalAt state e1 with _ | v1 <;>
  rcases he2 : evalAt state e2 with _ | v2 <;>
  rcases he3 : evalAt state e3 with _ | v3 <;>
  rcases he4 : evalAt state e4 with _ | v4 <;>
  rcases he5 : evalAt state e5 with _ | v5 <;>
    simp only [evalAt] at he1 he2 he3 he4 he5 <;>
    simp only [he1, he2, he3, he4, he5, Option.some.injEq] at hargs <;>
    cases hargs
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
    · rename_i hcond
      have rawEq := Option.some.inj raw
      rcases Prod.mk.inj rawEq with ⟨-, hrest2⟩
      rcases Prod.mk.inj hrest2 with ⟨hloc, -⟩
      subst hloc
      obtain ⟨hnd, -, -⟩ := hcond
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
        not_or, List.not_mem_nil, or_false] at hnd
      refine ⟨v1, v2, v3, v4, v5, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · simp [List.zip, List.foldl, hnd.1.1, hnd.1.2.1, hnd.1.2.2.1, hnd.1.2.2.2]
      · simp [List.zip, List.foldl, hnd.2.1.1, hnd.2.1.2.1, hnd.2.1.2.2]
      · simp [List.zip, List.foldl, hnd.2.2.1.1, hnd.2.2.1.2]
      · simp [List.zip, List.foldl, hnd.2.2.2]
      · simp [List.zip, List.foldl]
    · cases raw

theorem csrLiveAt_htabArgWF {F : Type} {s : PanSemStateFiniteExact 64 F}
    {cache roots m : Nat} (hs : CsrLiveAt s cache roots m)
    (ht : locN s "t" = cache ∨ locN s "t" = roots) : HtabArgWF s := by
  obtain ⟨hA, _, S, Nd, Nm, hW, hc, hr, _⟩ := hs
  have htS : locN s "t" ∈ S := ht.elim (fun h => h ▸ hc) (fun h => h ▸ hr)
  exact ⟨hA, (hW.1.2.1 _ htS).1, fun i hi => (hW.1.2.1 _ htS).2 i hi |>.1⟩

theorem csrTablesAt_htabArgWF {F : Type} {s : PanSemStateFiniteExact 64 F}
    {cache roots : Nat} (hs : CsrTablesAt s cache roots)
    (ht : locN s "t" = cache ∨ locN s "t" = roots) : HtabArgWF s := by
  obtain ⟨hA, _, S, Nd, hW, hc, hr, _⟩ := hs
  have htS : locN s "t" ∈ S := ht.elim (fun h => h ▸ hc) (fun h => h ▸ hr)
  exact ⟨hA, (hW.1.2.1 _ htS).1, fun i hi => (hW.1.2.1 _ htS).2 i hi |>.1⟩

theorem csrLiveAt_mptSetReady {F : Type} {s : PanSemStateFiniteExact 64 F}
    {cache roots : Nat} (hs : CsrLiveAt s cache roots (locN s "m"))
    (hk : locN s "klen" ≤ 32) (hv : locN s "vlen" ≤ 110) : MptSetReady s := by
  obtain ⟨hA, _, S, Nd, Nm, hW, _, _, _, _, hm, hd⟩ := hs
  exact mptSetReady_of_parts_csr hA hW hm hd hk hv

theorem pBounded_specDecCall_csr
    {names : List String}
    {P Pc R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop}
    {fname name : MlS} {args : List (ExpHOL 64)} {B Bc : Nat}
    {shape : ShapeHOL} {cont : ProgHOL 64}
    (hP : LocalsOnly names P)
    (hfb : TerminatingFunBoundedOn Pc fname B)
    (hspec : FunSpec Pc Qc fname)
    (hentry : CallEntryOn P Pc fname args)
    (hne : ∀ n ∈ names, ofString n ≠ name)
    (hret : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F)
      (values : List (ValueHOL 64)) (body : ProgHOL 64)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
      (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      s.code = originalRuntimeCode → P s →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values →
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      Qc (callEntryStateHOLFinite s callee) (some (.returned v)) post →
      R (setVarHOLFinite name v { post with locals := s.locals }))
    (hb : TerminatingProgBoundedOn R cont Bc)
    (hh : Hoare R cont (fun r t => r = none → P t)) :
    PBounded P (.decCall name shape fname args cont) (B + Bc + 1) :=
  PBounded.decCallTrans hfb hP name hne shape args hentry
    (funSpec_resumeOn_csr hspec hentry hret) hb hh

 theorem callEntryOn_worldOK_csr
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → WorldOK s)
    (fname : MlS) (args : List (ExpHOL 64)) :
    CallEntryOn P WorldOK fname args := by
  intro F s values body callee ret hc hs ha hl
  exact localsFree_worldOK s _ _ (hP s hs)

 theorem callEntryOn_arenaReady_csr
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → ArenaReady s)
    (fname : MlS) (args : List (ExpHOL 64)) :
    CallEntryOn P ArenaReady fname args := by
  intro F s values body callee ret hc hs ha hl
  exact localsFree_arenaReady s _ _ (hP s hs)

 theorem csrMpt_worldOK (name : String) {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hs : CsrMpt name s) : WorldOK s := csrTabs_worldOK (csrMpt_tabs name hs)

theorem csrBuffers_disj_worldTyped_csr {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {buffers : List (String × Nat)} (hW : WorldTypedWith s S Nd)
    (hb : ∀ b ∈ buffers, b ∈ globalBuffers ∧ b.1 ∉ typedRecords.map Prod.fst) :
    IvlsDisj (buffers.map (bufferRegion s)) (worldTypedIvls s S Nd) := by
  intro i hi j hj
  obtain ⟨b, hmem, rfl⟩ := List.mem_map.mp hi
  exact bufferRegion_disj hW b (hb b hmem).1 (hb b hmem).2 j hj

theorem worldStep_buffers_csrTablesAt {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {cache roots : Nat}
    {buffers : List (String × Nat)} {gw : List String}
    {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (hs : CsrTablesAt s cache roots)
    (hb : ∀ b ∈ buffers, b ∈ globalBuffers ∧ b.1 ∉ typedRecords.map Prod.fst)
    (hstep : WorldStep (fun t => buffers.map (bufferRegion t)) gw keep Q s r post) :
    CsrTablesAt post cache roots := by
  apply worldStep_csrTablesAt hs hstep
  · intro j hj hz
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hj
    dsimp only [bufferRegion] at hz ⊢
    by_cases hzero : globN s b.1 = 0
    · simp [hzero]
    · simp only [hzero, ↓reduceIte] at hz
      have hbuf := (hb b (by assumption)).1
      have hpos : b.2 ≠ 0 := by
        revert hbuf
        have : ∀ b ∈ globalBuffers, b.2 ≠ 0 := by decide
        exact this b
      exact False.elim (hpos hz)
  · intro S Nd hW
    exact csrBuffers_disj_worldTyped_csr hW hb

def CsrHeapBufAt {F : Type} (s : PanSemStateFiniteExact 64 F)
    (b : Ivl) (owned : List Ivl) : Prop :=
  Inside b sourceBase (globN s "heap_ptr") ∧ WordsOK s b ∧ IvlsDisj [b] owned

theorem csrHeapBufAt_fresh {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {p n : Nat} {owned : List Ivl}
    (hs : ArenaOK s) (hf : FreshBlock s post p n)
    (hd : IvlsDisj [(p, (n + 7) / 8 * 8)] owned) :
    CsrHeapBufAt post (p, (n + 7) / 8 * 8) owned := by
  exact ⟨⟨Nat.le_trans hs.1 hf.2.1.1, hf.2.1.2⟩, hf.2.2, hd⟩

theorem csrHeapBufAt_transfer {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {b : Ivl} {old new : List Ivl}
    (hs : ArenaReady s) (hp : ArenaReady post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hb : CsrHeapBufAt s b old) (hg : OwnedGrows s post old new) :
    CsrHeapBufAt post b new := by
  refine ⟨⟨hb.1.1, Nat.le_trans hb.1.2 hhp⟩,
    P3MptSet.wordsOK_transfer hs.1 hp.1 hb.2.1, ?_⟩
  exact ivlsDisj_ownedGrows_csr hs.2 hp.2 hg
    (by intro o ho _; obtain rfl := List.mem_singleton.mp ho; exact Or.inl hb.1) hb.2.2

theorem csrHeapBufAt_subregion_disj {F : Type} {s : PanSemStateFiniteExact 64 F}
    {b i : Ivl} {owned : List Ivl} (hb : CsrHeapBufAt s b owned)
    (hi : Inside i b.1 (b.1 + b.2)) : IvlsDisj [i] owned := by
  intro o ho j hj
  obtain rfl := List.mem_singleton.mp ho
  exact (GbodyC17ToC21Common.disj_of_inside_right hi
    (hb.2.2 b (by simp) j hj).flip).flip

theorem localsFree_csrHeapBufAt (b : Ivl) :
    LocalsFree (fun s => CsrHeapBufAt s b []) := by
  intro F s locals k hb
  exact hb

theorem csrHeapBufAt_worldTyped_disj {F : Type}
    {s : PanSemStateFiniteExact 64 F} {b : Ivl} {S Nd : List Nat}
    (hb : CsrHeapBufAt s b (worldOwned s S Nd)) :
    IvlsDisj [b] (worldTypedIvls s S Nd) := by
  intro o ho j hj
  exact hb.2.2 o ho j (worldTypedIvls_sub_worldOwned s S Nd j hj)

theorem mptObjStep_csrHeapBufAt {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {S Nd Nm : List Nat} {cache roots : Nat} {b : Ivl}
    (hs : ArenaReady s) (hW : WorldTypedWith s S Nd)
    (hc : cache ∈ S) (hr : roots ∈ S) (hne : cache ≠ roots)
    (hcl : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ cache)
    (hrl : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ roots)
    (hm : MptObjInWith s S Nm (locN s "m"))
    (hd : IvlsDisj (mptObjIvls s Nm (locN s "m")) (nodeExtents s Nd))
    (hb : CsrHeapBufAt s b (worldOwned s S Nd ++ mptObjIvls s Nm (locN s "m")))
    (hstep : MptObjStep R gw keep s post)
    (hR_z : ∀ j ∈ R s, j.2 = 0 → j.1 % 8 = 0)
    (hR : IvlsDisj (R s) (worldTypedIvls s S Nd ++ mptObjIvls s Nm (locN s "m")))
    (hRN : IvlsDisj (R s) (nodeExtents s Nd)) :
    ∃ S' Nd' Nm',
      WorldTypedWith post S' Nd' ∧ cache ∈ S' ∧ roots ∈ S' ∧
      (∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ cache) ∧
      (∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ roots) ∧
      MptObjInWith post S' Nm' (locN s "m") ∧
      IvlsDisj (mptObjIvls post Nm' (locN s "m")) (nodeExtents post Nd') ∧
      CsrHeapBufAt post b (worldOwned post S' Nd' ++ mptObjIvls post Nm' (locN s "m")) := by
  obtain ⟨S', Nd', Nm', hWp, hc', hr', hcl', hrl', _, _, _, _, hmp, hdp, hog, _⟩ :=
    mptObjStep_preserves_two_local_tables_csr hs hW hc hr hne hcl hrl hm hd
      hstep hR_z hR hRN
  exact ⟨S' ++ [cache, roots], Nd', Nm', hWp, hc', hr', hcl', hrl', hmp, hdp,
    csrHeapBufAt_transfer hs hstep.1 hstep.2.1 hb hog⟩

def CsrLiveBufAt {F : Type} (s : PanSemStateFiniteExact 64 F)
    (cache roots m : Nat) (b : Ivl) : Prop :=
  ArenaReady s ∧ cache ≠ roots ∧ ∃ S Nd Nm,
    WorldTypedWith s S Nd ∧ cache ∈ S ∧ roots ∈ S ∧
    (∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ cache) ∧
    (∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ roots) ∧
    MptObjInWith s S Nm m ∧
    IvlsDisj (mptObjIvls s Nm m) (nodeExtents s Nd) ∧
    CsrHeapBufAt s b (worldOwned s S Nd ++ mptObjIvls s Nm m)

theorem localsFree_csrLiveBufAt (cache roots m : Nat) (b : Ivl) :
    LocalsFree (fun s => CsrLiveBufAt s cache roots m b) := by
  intro F s locals k h
  obtain ⟨hA, hne, S, Nd, Nm, hW, hc, hr, hcl, hrl, hm, hd, hb⟩ := h
  refine ⟨localsFree_arenaReady s locals k hA, hne, S, Nd, Nm,
    (worldTypedWith_with_locals_csr s locals k S Nd).2 hW,
    hc, hr, hcl, hrl, (mptObjInWith_with_locals_csr s locals k S Nm m).2 hm, hd, ?_⟩
  exact ⟨hb.1, hb.2.1, hb.2.2⟩

theorem csrLiveBufAt_liveAt {F : Type} {s : PanSemStateFiniteExact 64 F}
    {cache roots m : Nat} {b : Ivl}
    (hs : CsrLiveBufAt s cache roots m b) : CsrLiveAt s cache roots m := by
  obtain ⟨hA, hne, S, Nd, Nm, hW, hc, hr, hcl, hrl, hm, hd, _⟩ := hs
  exact ⟨hA, hne, S, Nd, Nm, hW, hc, hr, hcl, hrl, hm, hd⟩

theorem csrLiveBufAt_mptObjReady {F : Type} {s : PanSemStateFiniteExact 64 F}
    {cache roots : Nat} {b : Ivl}
    (hs : CsrLiveBufAt s cache roots (locN s "m") b) : MptObjReady s :=
  csrLiveAt_mptObjReady (csrLiveBufAt_liveAt hs)

theorem csrLiveBufAt_mptSetReady {F : Type} {s : PanSemStateFiniteExact 64 F}
    {cache roots : Nat} {b : Ivl}
    (hs : CsrLiveBufAt s cache roots (locN s "m") b)
    (hk : locN s "klen" ≤ 32) (hv : locN s "vlen" ≤ 110) : MptSetReady s :=
  csrLiveAt_mptSetReady (csrLiveBufAt_liveAt hs) hk hv

theorem csrLiveBufAt_htabArgWF {F : Type} {s : PanSemStateFiniteExact 64 F}
    {cache roots m : Nat} {b : Ivl}
    (hs : CsrLiveBufAt s cache roots m b)
    (ht : locN s "t" = cache ∨ locN s "t" = roots) : HtabArgWF s :=
  csrLiveAt_htabArgWF (csrLiveBufAt_liveAt hs) ht

theorem htabExit_csrLiveBufAt {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {cache roots m : Nat} {b : Ivl}
    (hs : CsrLiveBufAt s cache roots m b)
    (ht : locN s "t" = cache ∨ locN s "t" = roots)
    (hexit : HtabExit s post) (hbe : post.be = s.be) :
    CsrLiveBufAt post cache roots m b := by
  obtain ⟨hA, hne, S, Nd, Nm, hW, hc, hr, hcl, hrl, hm, hd, hb⟩ := hs
  have htS : locN s "t" ∈ S := ht.elim (fun h => h ▸ hc) (fun h => h ▸ hr)
  have htl : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ locN s "t" := by
    rcases ht with ht | ht
    · simpa only [ht] using hcl
    · simpa only [ht] using hrl
  obtain ⟨hWp, hmp, hdp, heq, hwrs, hjrs, _, hog⟩ :=
    htabExit_local_liveMpt_csr hA hW htS htl hexit hbe hm hd
  have hog_all : OwnedGrows s post
      (worldOwned s S Nd ++ mptObjIvls s Nm m)
      (worldOwned post S Nd ++ mptObjIvls post Nm m) := by
    intro o ho
    rcases List.mem_append.mp ho with how | hom
    · rcases hog o how with rfl | ⟨j, hj, hin⟩ | hf
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨j, List.mem_append_left _ hj, hin⟩)
      · exact Or.inr (Or.inr hf)
    · rw [heq] at hom
      exact Or.inr (Or.inl ⟨o, List.mem_append_right _ hom, ⟨le_rfl, le_rfl⟩⟩)
  exact ⟨hexit.1, hne, S, Nd, Nm, hWp, hc, hr,
    by simpa only [hwrs, hjrs] using hcl,
    by simpa only [hwrs, hjrs] using hrl,
    hmp, hdp, csrHeapBufAt_transfer hA hexit.1 hexit.2.2.2.2.1 hb hog_all⟩

def CsrLiveBufsAt {F : Type} (s : PanSemStateFiniteExact 64 F)
    (cache roots m : Nat) (bs : List Ivl) : Prop :=
  ArenaReady s ∧ cache ≠ roots ∧ ∃ S Nd Nm,
    WorldTypedWith s S Nd ∧ cache ∈ S ∧ roots ∈ S ∧
    (∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ cache) ∧
    (∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ roots) ∧
    MptObjInWith s S Nm m ∧
    IvlsDisj (mptObjIvls s Nm m) (nodeExtents s Nd) ∧
    (∀ b ∈ bs, CsrHeapBufAt s b (worldOwned s S Nd ++ mptObjIvls s Nm m)) ∧
    bs.Pairwise Disj

theorem localsFree_csrLiveBufsAt (cache roots m : Nat) (bs : List Ivl) :
    LocalsFree (fun s => CsrLiveBufsAt s cache roots m bs) := by
  intro F s locals k h
  obtain ⟨hA, hne, S, Nd, Nm, hW, hc, hr, hcl, hrl, hm, hd, hbs, hpw⟩ := h
  refine ⟨localsFree_arenaReady s locals k hA, hne, S, Nd, Nm,
    (worldTypedWith_with_locals_csr s locals k S Nd).2 hW,
    hc, hr, hcl, hrl, (mptObjInWith_with_locals_csr s locals k S Nm m).2 hm, hd,
    fun b hb => ⟨(hbs b hb).1, (hbs b hb).2.1, (hbs b hb).2.2⟩, hpw⟩

theorem csrLiveBufsAt_of_liveAt {F : Type} {s : PanSemStateFiniteExact 64 F}
    {cache roots m : Nat} (hs : CsrLiveAt s cache roots m) :
    CsrLiveBufsAt s cache roots m [] := by
  obtain ⟨hA, hne, S, Nd, Nm, hW, hc, hr, hcl, hrl, hm, hd⟩ := hs
  exact ⟨hA, hne, S, Nd, Nm, hW, hc, hr, hcl, hrl, hm, hd,
    fun _ h => False.elim (List.not_mem_nil h), List.Pairwise.nil⟩

theorem csrLiveBufsAt_liveAt {F : Type} {s : PanSemStateFiniteExact 64 F}
    {cache roots m : Nat} {bs : List Ivl}
    (hs : CsrLiveBufsAt s cache roots m bs) : CsrLiveAt s cache roots m := by
  obtain ⟨hA, hne, S, Nd, Nm, hW, hc, hr, hcl, hrl, hm, hd, _, _⟩ := hs
  exact ⟨hA, hne, S, Nd, Nm, hW, hc, hr, hcl, hrl, hm, hd⟩

theorem csrLiveBufsAt_singleton_iff {F : Type} {s : PanSemStateFiniteExact 64 F}
    {cache roots m : Nat} {b : Ivl} :
    CsrLiveBufsAt s cache roots m [b] ↔ CsrLiveBufAt s cache roots m b := by
  constructor
  · intro ⟨hA, hne, S, Nd, Nm, hW, hc, hr, hcl, hrl, hm, hd, hbs, _⟩
    exact ⟨hA, hne, S, Nd, Nm, hW, hc, hr, hcl, hrl, hm, hd, hbs b (by simp)⟩
  · intro ⟨hA, hne, S, Nd, Nm, hW, hc, hr, hcl, hrl, hm, hd, hb⟩
    refine ⟨hA, hne, S, Nd, Nm, hW, hc, hr, hcl, hrl, hm, hd, ?_, List.pairwise_singleton _ _⟩
    intro x hx; obtain rfl := List.mem_singleton.mp hx; exact hb

theorem csrLiveBufsAt_sub {F : Type} {s : PanSemStateFiniteExact 64 F}
    {cache roots m : Nat} {bs1 bs2 : List Ivl}
    (hs : CsrLiveBufsAt s cache roots m bs1)
    (hsub : ∀ b ∈ bs2, b ∈ bs1) (hpw2 : bs2.Pairwise Disj) :
    CsrLiveBufsAt s cache roots m bs2 := by
  obtain ⟨hA, hne, S, Nd, Nm, hW, hc, hr, hcl, hrl, hm, hd, hbs, _⟩ := hs
  exact ⟨hA, hne, S, Nd, Nm, hW, hc, hr, hcl, hrl, hm, hd, fun b hb => hbs b (hsub b hb), hpw2⟩

theorem worldEff_csrLiveBufsAt {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    {cache roots m : Nat} {bs : List Ivl}
    (hs : CsrLiveBufsAt s cache roots m bs)
    (hB_ok : ∀ gs ∈ B, gs ∈ globalBuffers ∧ gs.1 ∉ typedRecords.map Prod.fst)
    (hcore_out : ∀ g ∈ coreWorldGlobals, ofString g ∉ gw.map ofString)
    (heff : R16Shards.WorldEff s post Rl B gw)
    (hR : ∀ iv ∈ Rl, iv.2 ≠ 0 → ∃ b ∈ bs, Inside iv b.1 (b.1 + b.2)) :
    CsrLiveBufsAt post cache roots m bs := by
  obtain ⟨hA, hne, S, Nd, Nm, hW, hc, hr, hcl, hrl, hm, hd, hbs, hpw⟩ := hs
  have hR_disj : IvlsDisj Rl (worldTypedIvls s S Nd ++ mptObjIvls s Nm m) := by
    intro iv hiv j hj
    by_cases hz : iv.2 = 0
    · exact Or.inl hz
    · obtain ⟨b, hb_mem, hin⟩ := hR iv hiv hz
      have hsub : j ∈ worldOwned s S Nd ++ mptObjIvls s Nm m := by
        rcases List.mem_append.mp hj with hjw | hjm
        · exact List.mem_append_left _ (worldTypedIvls_sub_worldOwned s S Nd j hjw)
        · exact List.mem_append_right _ hjm
      exact csrHeapBufAt_subregion_disj (hbs b hb_mem) hin iv (by simp) j hsub
  obtain ⟨hWp, hmp, hdp, hm_ivl_eq, _, _, _, hroles, hog⟩ :=
    worldEff_liveMpt_csr hA hB_ok hcore_out heff hW hm hd hR_disj
  have hog_all : OwnedGrows s post
      (worldOwned s S Nd ++ mptObjIvls s Nm m)
      (worldOwned post S Nd ++ mptObjIvls post Nm m) := by
    intro o ho
    rcases List.mem_append.mp ho with how | hom
    · rcases hog o how with rfl | ⟨j, hj, hin⟩ | hf
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨j, List.mem_append_left _ hj, hin⟩)
      · exact Or.inr (Or.inr hf)
    · rw [hm_ivl_eq] at hom
      exact Or.inr (Or.inl ⟨o, List.mem_append_right _ hom, ⟨le_rfl, le_rfl⟩⟩)
  exact ⟨heff.arena, hne, S, Nd, Nm, hWp, hc, hr,
    fun a ha => hcl a (hroles a ha), fun a ha => hrl a (hroles a ha),
    hmp, hdp, fun b hb => csrHeapBufAt_transfer hA heff.arena heff.hp_lo (hbs b hb) hog_all, hpw⟩

theorem worldEff_csrLiveBufAt {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    {cache roots m : Nat} {b : Ivl}
    (hs : CsrLiveBufAt s cache roots m b)
    (hB_ok : ∀ gs ∈ B, gs ∈ globalBuffers ∧ gs.1 ∉ typedRecords.map Prod.fst)
    (hcore_out : ∀ g ∈ coreWorldGlobals, ofString g ∉ gw.map ofString)
    (heff : R16Shards.WorldEff s post Rl B gw)
    (hR : ∀ iv ∈ Rl, iv.2 ≠ 0 → Inside iv b.1 (b.1 + b.2)) :
    CsrLiveBufAt post cache roots m b := by
  rw [← csrLiveBufsAt_singleton_iff] at hs ⊢
  exact worldEff_csrLiveBufsAt hs hB_ok hcore_out heff
    (fun iv hiv hz => ⟨b, List.mem_singleton_self b, hR iv hiv hz⟩)

theorem mptObjStep_csrLiveBufsAt {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {cache roots : Nat} {bs : List Ivl}
    (hs : CsrLiveBufsAt s cache roots (locN s "m") bs)
    (hstep : MptObjStep R gw keep s post)
    (hR_z : ∀ j ∈ R s, j.2 = 0 → j.1 % 8 = 0)
    (hR_ti : ∀ S Nd Nm, WorldTypedWith s S Nd →
      MptObjInWith s S Nm (locN s "m") →
      IvlsDisj (mptObjIvls s Nm (locN s "m")) (nodeExtents s Nd) →
      (∀ b ∈ bs, CsrHeapBufAt s b (worldOwned s S Nd ++ mptObjIvls s Nm (locN s "m"))) →
      IvlsDisj (R s) (worldTypedIvls s S Nd ++ mptObjIvls s Nm (locN s "m"))) :
    CsrLiveBufsAt post cache roots (locN s "m") bs := by
  obtain ⟨hA, hne, S, Nd, Nm, hW, hc, hr, hcl, hrl, hm, hd, hbs, hpw⟩ := hs
  have hR := hR_ti S Nd Nm hW hm hd hbs
  have hRN : IvlsDisj (R s) (nodeExtents s Nd) := by
    intro r hr_mem i hi
    exact hR r hr_mem i (List.mem_append_left _ (by
      unfold worldTypedIvls
      exact List.mem_append_right _ hi))
  obtain ⟨S', Nd', Nm', hWp, hc', hr', hcl', hrl', _, _, _, _, hmp, hdp, hog, _⟩ :=
    mptObjStep_preserves_two_local_tables_csr hA hW hc hr hne hcl hrl hm hd
      hstep hR_z hR hRN
  exact ⟨hstep.1, hne, S' ++ [cache, roots], Nd', Nm', hWp, hc', hr', hcl', hrl', hmp, hdp,
    fun b hb => csrHeapBufAt_transfer hA hstep.1 hstep.2.1 (hbs b hb) hog, hpw⟩

theorem htabExit_csrLiveBufsAt {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {cache roots m : Nat} {bs : List Ivl}
    (hs : CsrLiveBufsAt s cache roots m bs)
    (ht : locN s "t" = cache ∨ locN s "t" = roots)
    (hexit : HtabExit s post) (hbe : post.be = s.be) :
    CsrLiveBufsAt post cache roots m bs := by
  obtain ⟨hA, hne, S, Nd, Nm, hW, hc, hr, hcl, hrl, hm, hd, hbs, hpw⟩ := hs
  have htS : locN s "t" ∈ S := ht.elim (fun h => h ▸ hc) (fun h => h ▸ hr)
  have htl : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ locN s "t" := by
    rcases ht with ht | ht
    · simpa only [ht] using hcl
    · simpa only [ht] using hrl
  obtain ⟨hWp, hmp, hdp, heq, hwrs, hjrs, _, hog⟩ :=
    htabExit_local_liveMpt_csr hA hW htS htl hexit hbe hm hd
  have hog_all : OwnedGrows s post
      (worldOwned s S Nd ++ mptObjIvls s Nm m)
      (worldOwned post S Nd ++ mptObjIvls post Nm m) := by
    intro o ho
    rcases List.mem_append.mp ho with how | hom
    · rcases hog o how with rfl | ⟨j, hj, hin⟩ | hf
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨j, List.mem_append_left _ hj, hin⟩)
      · exact Or.inr (Or.inr hf)
    · rw [heq] at hom
      exact Or.inr (Or.inl ⟨o, List.mem_append_right _ hom, ⟨le_rfl, le_rfl⟩⟩)
  exact ⟨hexit.1, hne, S, Nd, Nm, hWp, hc, hr,
    by simpa only [hwrs, hjrs] using hcl,
    by simpa only [hwrs, hjrs] using hrl,
    hmp, hdp,
    fun b hb => csrHeapBufAt_transfer hA hexit.1 hexit.2.2.2.2.1 (hbs b hb) hog_all, hpw⟩

theorem worldEff_alloc_body_csr {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (hA : ArenaReady s)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).1) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)
    ∃ p : BitVec 64,
      out.1 = some (.returned (.val (.word p))) ∧
      p.toNat = globN s "heap_ptr" ∧
      FreshBlock s out.2 p.toNat (locN s "n") ∧
      out.2.memory = s.memory ∧
      out.2.be = s.be ∧
      R16Shards.WorldEff s out.2 [] [] ["heap_ptr"] := by
  dsimp only
  obtain ⟨p, q, hrv, hp_eq, hq_eq, hq_hi, _, hp_le_q, hpost_g, hpost_m, hpost_be,
    hpost_ma, hA_post, hpost_hp, hpost_sp⟩ :=
    R13Shards.alloc_body_resumes_props s hcode hA hres
  set post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).2
  have hhp_al : p.toNat % 8 = 0 := by rw [hp_eq]; exact hA.2.2.2.2.2.2.1
  have hsb_le : sourceBase ≤ p.toNat := by rw [hp_eq]; exact hA.2.1
  have hlim_le_he : heapLimit ≤ heapEnd := by decide
  have hf : FreshBlock s post p.toNat (locN s "n") := by
    refine ⟨hhp_al, ?_, ?_⟩
    · rw [← hp_eq, hpost_hp]
      exact ⟨le_rfl, le_of_eq hq_eq.symm⟩
    · exact R13.wordsOK_of_guestInv post hA_post.1 p.toNat ((locN s "n" + 7) / 8 * 8)
        hhp_al (by omega) hsb_le (by omega)
  have hgw : GlobalsKept ["heap_ptr"] s post := by
    intro k hk
    have hne : ofString "heap_ptr" ≠ k := fun h => hk (by simp [h])
    rw [hpost_g]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne]
  have hfb : R10Shards.P26_P28.FreshBufsOK s post :=
    R16Shards.freshBufsOK_of_no_globalBuf_writes hgw
      (by intro gs hgs; revert gs hgs; decide)
  have hpost_fmp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" :=
    (R10Shards.P26_P28.globN_eq_of_lookup (hgw (ofString "frame_mem_ptr") (by decide)))
  have heff : R16Shards.WorldEff s post [] [] ["heap_ptr"] :=
    ⟨hA_post, hA_post.1.code, hpost_ma, hpost_be,
     (evaluateHOLFiniteState_metadata s (sourceFnBody Guest.Software.guestFn_alloc)).2.2.2.2,
     by rw [← hp_eq, hpost_hp]; exact hp_le_q,
     hpost_fmp,
     by rw [hpost_sp],
     hgw, hfb,
     fun a hne => absurd (hpost_m ▸ rfl) hne,
     fun a hne => absurd (hpost_m ▸ rfl) hne,
     fun b _ hne => absurd (by unfold memB; rw [hpost_m, hpost_be]) hne⟩
  exact ⟨p, hrv, hp_eq, hf, hpost_m, hpost_be, heff⟩

theorem fixedObjects_eq_of_mem_globals_csr {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hm : post.memory = s.memory)
    (hgw : GlobalsKept ["heap_ptr"] s post) :
    fixedObjects post = fixedObjects s := by
  have hg : ∀ name : String, ofString name ≠ ofString "heap_ptr" → globN post name = globN s name :=
    fun name hne => R10Shards.P26_P28.globN_eq_of_lookup
      (hgw (ofString name) (fun h => hne (by simp only [List.map, List.mem_cons, List.not_mem_nil, or_false] at h; exact h)))
  have hmw : ∀ a : Nat, memW post a = memW s a := fun a => by simp [memW, hm]
  have hbo : blockOutObjects post = blockOutObjects s := by
    simp only [blockOutObjects, hg "bo" (by decide), hmw]
  have hbal_rec : balRecords post = balRecords s := by
    simp only [balRecords, hg "bal_accounts" (by decide), hdr, nodeF, hmw]
  have hbal : balObjects post = balObjects s := by
    simp only [balObjects, hbal_rec, lstObjects, htabValues, hdr, nodeF, hmw]
  have hgb : globalBuffers.map (fun gn => (globN post gn.1, if globN post gn.1 = 0 then 0 else gn.2)) =
      globalBuffers.map (fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) := by
    apply List.map_congr_left
    intro gn hgn
    have hne : ofString gn.1 ≠ ofString "heap_ptr" := by revert gn hgn; decide
    rw [hg gn.1 hne]
  unfold fixedObjects
  rw [hgb, hbo, hbal, hg "journal" (by decide), hg "journal_cap" (by decide)]

theorem alloc_csrLiveBufsAt {F : Type}
    {s : PanSemStateFiniteExact 64 F}
    {cache roots m : Nat} {bs : List Ivl}
    (hs : CsrLiveBufsAt s cache roots m bs)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).1) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)
    ∃ p : BitVec 64,
      out.1 = some (.returned (.val (.word p))) ∧
      CsrLiveBufsAt out.2 cache roots m
        ((p.toNat, (locN s "n" + 7) / 8 * 8) :: bs) := by
  dsimp only
  obtain ⟨hA, hne, S, Nd, Nm, hW, hc, hr, hcl, hrl, hm, hd, hbs, hpw⟩ := hs
  obtain ⟨p, hrv, hp_eq, hf, hpost_m, _, heff⟩ :=
    worldEff_alloc_body_csr s hA.1.code hA hres
  set post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).2
  obtain ⟨hWp, hmp, hdp, hm_ivl_eq, hne_eq, hfp_eq, _, hroles, hog⟩ :=
    worldEff_liveMpt_csr hA (fun _ h => False.elim (List.not_mem_nil h))
      (by intro g hg; revert g hg; decide) heff hW hm hd
      (fun _ h => False.elim (List.not_mem_nil h))
  have hwo_eq : worldOwned post S Nd = worldOwned s S Nd := by
    unfold worldOwned
    rw [fixedObjects_eq_of_mem_globals_csr hpost_m heff.gw_kept, hne_eq]
    congr 2
    exact List.flatMap_congr fun t ht => hfp_eq t ht
  have hog_all : OwnedGrows s post
      (worldOwned s S Nd ++ mptObjIvls s Nm m)
      (worldOwned post S Nd ++ mptObjIvls post Nm m) := by
    intro o ho
    rw [hwo_eq, hm_ivl_eq] at ho
    exact Or.inr (Or.inl ⟨o, ho, ⟨le_rfl, le_rfl⟩⟩)
  let nb : Ivl := (p.toNat, (locN s "n" + 7) / 8 * 8)
  have hd_nb : IvlsDisj [nb] (worldOwned post S Nd ++ mptObjIvls post Nm m) := by
    rw [hwo_eq, hm_ivl_eq]
    intro x hx o ho
    obtain rfl := List.mem_singleton.mp hx
    rcases List.mem_append.mp ho with how | hom
    · rcases worldOwned_zero_or_allocated hW o how with rfl | ⟨_, hal_o⟩
      · exact Or.inr (Or.inl rfl)
      · exact disj_allocated_fresh_heap hA.2 heff.arena.2 hal_o (f := nb) hf.2.1
    · by_cases hoz : o.2 = 0
      · exact Or.inr (Or.inl hoz)
      · exact disj_allocated_fresh_heap hA.2 heff.arena.2
          (mptObjInWith_allocated_csr hm o hom hoz) (f := nb) hf.2.1
  have hnb : CsrHeapBufAt post nb (worldOwned post S Nd ++ mptObjIvls post Nm m) :=
    csrHeapBufAt_fresh hA.2 hf hd_nb
  have hpw_cons : (nb :: bs).Pairwise Disj := by
    refine List.Pairwise.cons (fun b hb => ?_) hpw
    have hb_in := (hbs b hb).1
    exact Or.inr (Or.inr (Or.inr (by dsimp [nb]; unfold Inside at hb_in; omega)))
  refine ⟨p, hrv, heff.arena, hne, S, Nd, Nm, hWp, hc, hr,
    fun a ha => hcl a (hroles a ha), fun a ha => hrl a (hroles a ha),
    hmp, hdp, ?_, hpw_cons⟩
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb_tl
  · exact hnb
  · exact csrHeapBufAt_transfer hA heff.arena heff.hp_lo (hbs b hb_tl) hog_all

def CsrMptBufs (name : String) (buffers : List (String × Nat)) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => CsrLiveBufsAt s (locN s "cache") (locN s "new_roots") (locN s name)
    (buffers.map fun b => (locN s b.1, b.2))

theorem localsOnly_csrMptBufs (name : String) (buffers : List (String × Nat)) :
    LocalsOnly (["cache", "new_roots", name] ++ buffers.map Prod.fst)
      (CsrMptBufs name buffers) := by
  intro F s locals k hl hs
  have hbuf : buffers.map (fun b => (locN { s with locals := locals, clock := k } b.1, b.2)) =
      buffers.map (fun b => (locN s b.1, b.2)) := by
    apply List.map_congr_left
    intro b hb
    rw [locN_congr s locals k b.1 (hl b.1 (List.mem_append_right _
      (List.mem_map.mpr ⟨b, hb, rfl⟩)))]
  unfold CsrMptBufs
  rw [locN_congr s locals k "cache" (hl "cache" (by simp)),
    locN_congr s locals k "new_roots" (hl "new_roots" (by simp)),
    locN_congr s locals k name (hl name (by simp)), hbuf]
  exact localsFree_csrLiveBufsAt _ _ _ _ s locals k hs

theorem csrMptBufs_mpt (name : String) (buffers : List (String × Nat))
    {F : Type} {s : PanSemStateFiniteExact 64 F} (hs : CsrMptBufs name buffers s) :
    CsrMpt name s := csrLiveBufsAt_liveAt hs

theorem csrMptBufs_worldOK (name : String) (buffers : List (String × Nat))
    {F : Type} {s : PanSemStateFiniteExact 64 F} (hs : CsrMptBufs name buffers s) :
    WorldOK s := csrMpt_worldOK name (csrMptBufs_mpt name buffers hs)

theorem csrMptBufs_nil_iff (name : String) {F : Type}
    {s : PanSemStateFiniteExact 64 F} : CsrMptBufs name [] s ↔ CsrMpt name s :=
  ⟨csrLiveBufsAt_liveAt, csrLiveBufsAt_of_liveAt⟩

theorem csrLiveBufsAt_mptObjReady {F : Type} {s : PanSemStateFiniteExact 64 F}
    {cache roots : Nat} {bs : List Ivl}
    (hs : CsrLiveBufsAt s cache roots (locN s "m") bs) : MptObjReady s :=
  csrLiveAt_mptObjReady (csrLiveBufsAt_liveAt hs)

theorem csrLiveBufsAt_mptSetReady {F : Type} {s : PanSemStateFiniteExact 64 F}
    {cache roots : Nat} {bs : List Ivl}
    (hs : CsrLiveBufsAt s cache roots (locN s "m") bs)
    (hk : locN s "klen" ≤ 32) (hv : locN s "vlen" ≤ 110) : MptSetReady s :=
  csrLiveAt_mptSetReady (csrLiveBufsAt_liveAt hs) hk hv

theorem csrLiveBufsAt_htabArgWF {F : Type} {s : PanSemStateFiniteExact 64 F}
    {cache roots m : Nat} {bs : List Ivl}
    (hs : CsrLiveBufsAt s cache roots m bs)
    (ht : locN s "t" = cache ∨ locN s "t" = roots) : HtabArgWF s :=
  csrLiveAt_htabArgWF (csrLiveBufsAt_liveAt hs) ht

theorem csrLiveBufsAt_buffer {F : Type} {s : PanSemStateFiniteExact 64 F}
    {cache roots m : Nat} {bs : List Ivl} {b : Ivl}
    (hs : CsrLiveBufsAt s cache roots m bs) (hb : b ∈ bs) :
    CsrLiveBufAt s cache roots m b := by
  apply csrLiveBufsAt_singleton_iff.mp
  exact csrLiveBufsAt_sub hs (fun x hx => (List.mem_singleton.mp hx) ▸ hb)
    (List.pairwise_singleton _ _)



theorem pass_loop_slack_csr {B_j : Nat} (h : K.«htab_set» ≤ (2 ^ 64 - 2) * B_j) :
    3 * ((2 ^ 64 + 1) * (B_j + 1) + 1) + (K.«htab_set» + 1) ≤
      (2 ^ 64 + 1) * ((2 ^ 64 + 1) * (B_j + 1) + 1) := by
  have h1 : (2 ^ 64 - 2) * B_j + 1 ≤ (2 ^ 64 - 2) * ((2 ^ 64 + 1) * (B_j + 1) + 1) := by
    have hle : B_j + 1 ≤ (2 ^ 64 + 1) * (B_j + 1) + 1 := by
      have : 1 * (B_j + 1) ≤ (2 ^ 64 + 1) * (B_j + 1) := Nat.mul_le_mul_right _ (by decide)
      omega
    have hmul := Nat.mul_le_mul_left (2 ^ 64 - 2) hle
    omega
  omega

theorem pBounded_mono_bound_csr {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {prog : ProgHOL 64} {a b : Nat} (h : PBounded P prog a) (hle : a ≤ b) :
    PBounded P prog b :=
  ⟨TerminatingProgBoundedOn.mono_bound h.bounded hle, h.hoare⟩

theorem pBounded_congr_csr {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {prog : ProgHOL 64} {K : Nat}
    (hiff : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s ↔ Q s)
    (h : PBounded Q prog K) : PBounded P prog K :=
  ⟨fun s hc hP => h.bounded s hc ((hiff s).1 hP),
   ⟨fun s hc hP hnt hr => (hiff _).2 (h.hoare.run s hc ((hiff s).1 hP) hnt hr)⟩⟩

theorem signed_less_eq_csr (left right : BitVec 64) :
    holAsmSignedLess left right = left.slt right := by
  have bl := left.isLt
  have br := right.isLt
  simp only [holAsmSignedLess, BitVec.slt_eq_decide, BitVec.toInt_eq_msb_cond,
    BitVec.msb_eq_decide]
  repeat (any_goals first | split)
  all_goals simp_all only [decide_eq_true_eq]
  all_goals apply Bool.eq_iff_iff.mpr
  all_goals simp_all [decide_eq_true_eq]
  all_goals omega

def passRank_csr (counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup counter with
  | some (.val (.word w)) => (2 - w.toInt).toNat
  | _ => 0

def CsrNonNeg (name : String)
    (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => P s ∧ ∃ w : BitVec 64, s.locals.lookup (ofString name) = some (.val (.word w)) ∧ 0 ≤ w.toInt

theorem localsOnly_csrNonNeg {names : List String}
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : LocalsOnly names P) (name : String) :
    LocalsOnly (name :: names) (CsrNonNeg name P) := by
  intro F s locals k hl hs
  refine ⟨hP s locals k (fun n hn => hl n (by simp [hn])) hs.1, ?_⟩
  obtain ⟨w, hw, h0⟩ := hs.2
  exact ⟨w, (hl name (by simp)).trans hw, h0⟩

theorem while_pass_lt2_csr {names : List String}
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : LocalsOnly names P)
    {body : ProgHOL 64} {B : Nat}
    (hb : PBounded (CsrNonNeg "pass" P) body B)
    (hinc : IncrBody (ofString "pass") body)
    (hnb : noTopBreak body = true) :
    PBounded (CsrNonNeg "pass" P)
      (.while (.cmp .less (.var .local (ofString "pass")) (.const (2#64))) body)
      (3 * (B + 1)) := by
  have hLP : LocalsOnly ("pass" :: names) (CsrNonNeg "pass" P) := localsOnly_csrNonNeg hP "pass"
  refine ⟨TerminatingProgBoundedOn.while_rank (N := 2) (passRank_csr (ofString "pass"))
      (fun s hs => hLP.decClock s hs) hb.bounded ?_ ?_,
    hoare_while_less_preserve hLP (ofString "pass") (.const (2#64)) hb.hoare hinc hnb⟩
  · intro F s _ hs _
    obtain ⟨w, hw, h0⟩ := hs.2
    simp only [passRank_csr, hw]
    omega
  · intro F s hcode hs ⟨result, hcond, hnz⟩ hflow
    change evalAt s _ = _ at hcond
    obtain ⟨w, v, hw, hv, hword⟩ := evalAt_cmp s .less _ _ result hcond
    simp only [evalAt, evalHOLExact] at hw hv
    have hwl : s.locals.lookup (ofString "pass") = some (.val (.word w)) := by simpa using hw
    have hveq : v = 2#64 := by simpa using hv.symm
    subst v
    obtain ⟨w', hw', h0⟩ := hs.2
    have hww : w = w' := by simpa [hwl] using hw'
    subst w'
    obtain ⟨hnc_w, hinc_w⟩ := hinc.run (decClockHOLFinite s) w hwl
    have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none :=
      hflow.elim id (fun h => absurd h hnc_w)
    have hP_post : CsrNonNeg "pass" P (evaluateHOLFiniteState (decClockHOLFinite s) body).2 :=
      hb.hoare.run (decClockHOLFinite s) hcode (hLP.decClock s hs) (by rw [hnone]; simp) hnone
    have hcmp : wordCmpHOL .less w (2#64) = true := by
      by_contra h; simp [h] at hword; exact hnz hword
    have hlt : w.toInt < (2#64).toInt := by
      simpa only [wordCmpHOL, signed_less_eq_csr, BitVec.slt_iff_toInt_lt] using hcmp
    have h2int : (2#64).toInt = 2 := by decide
    have hone : (1 : BitVec 64).toInt = 1 := by decide
    have hnext : (w + 1).toInt = w.toInt + 1 := by
      rw [BitVec.toInt_add, hone]; apply Int.bmod_eq_of_le <;> omega
    refine ⟨hP_post, ?_⟩
    simp only [passRank_csr, hinc_w hnone, hwl, hnext]
    omega

theorem pBounded_decZero_csrNonNeg {names : List String}
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : LocalsOnly names P)
    (name : String) (hne : ∀ n ∈ names, ofString n ≠ ofString name)
    {body : ProgHOL 64} {K : Nat}
    (hb : PBounded (CsrNonNeg name P) body K) :
    PBounded P (.dec (ofString name) .one (.const (0#64)) body) K := by
  refine ⟨?_, Hoare.dec (names := names) (P' := CsrNonNeg name P) hne
      (fun s v hs hv => ?_)
      ⟨fun s hc hPs hnt hr => (hb.hoare.run s hc hPs hnt hr).1⟩
      (fun _ t locals hlk h hr => hP t locals t.clock hlk (h hr))
      (fun _ _ hr => absurd hr (by simp))⟩
  · intro F state hcode hPst hnt
    rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
    dsimp only at hnt ⊢
    have hev : @evalHOLExact 64 F _ state.toExact
        (fun a => Classical.propDecidable (state.memaddrs a))
        (.const (0#64)) = some (ValueHOL.val (.word (0#64))) := rfl
    rw [hev] at hnt ⊢
    dsimp only at hnt ⊢
    have hvalid : shapeEqHOL ShapeHOL.one
        (shapeOfHOLExact (ValueHOL.val (HolWordLab.word 0#64))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    simp only [hvalid, ↓reduceIte] at hnt ⊢
    have hinit : CsrNonNeg name P (setVarHOLFinite (ofString name) (.val (.word (0#64))) state) := by
      refine ⟨hP.setVar hne _ state hPst, 0#64, ?_, by decide⟩
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hrun := hb.bounded (setVarHOLFinite (ofString name) (.val (.word (0#64))) state) hcode hinit
    unfold TerminatingRunBounded at hrun
    rcases hb_ev : evaluateHOLFiniteState (setVarHOLFinite (ofString name) (.val (.word (0#64))) state) body with ⟨rb, tb⟩
    simp only [hb_ev] at hnt hrun ⊢
    exact hrun hnt
  · have hv0 : v = .val (.word (0#64)) := by
      simp only [evalHOLExact, Option.some.injEq] at hv; exact hv.symm
    subst v
    refine ⟨hP.setVar hne _ s hs, 0#64, ?_, by decide⟩
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

theorem pBounded_call0_entry_csr
    {P Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop}
    {fname : MlS} {args : List (ExpHOL 64)} {B : Nat}
    (hfb : TerminatingFunBoundedOn GuestInv fname B)
    (hG : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → GuestInv s)
    (hspec : FunSpec Pc Qc fname)
    (hentry : CallEntryOn P Pc fname args)
    (hret : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F)
      (values : List (ValueHOL 64)) (body : ProgHOL 64)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
      (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      s.code = originalRuntimeCode → P s →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values →
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      Qc (callEntryStateHOLFinite s callee) (some (.returned v)) post →
      P { post with locals := s.locals }) :
    PBounded P (.call (some (none, none)) fname args) (B + 1) := by
  refine ⟨TerminatingProgBoundedOn.call_on hfb none args (callEntryOn_guestInv_csr hG fname args), ?_⟩
  refine ⟨fun {F} s hc hs _ hr => ?_⟩
  rw [evaluateHOLFiniteState_call] at hr ⊢
  rcases ha : @evalListHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [PanSemStateFiniteExact.evalListHOLFinite, ha] at hr
  · simp only [PanSemStateFiniteExact.evalListHOLFinite, ha] at hr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body, callee, ret⟩
    · simp [hl] at hr
    · simp only [hl] at hr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hr
      · simp only [hz, ↓reduceIte] at hr ⊢
        have harg := hentry s vs body callee ret hc hs ha hl
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, post⟩
        simp only [hb] at hr ⊢
        cases res with
        | none => simp at hr
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hr ⊢
            split at hr
            · rename_i hsh
              rw [if_pos hsh]
              have hq := FunSpec.at_lookup hspec s hc vs body callee ret hl harg (by rw [hb]; simp)
              rw [hb] at hq
              exact hret s vs body callee ret v post hc hs ha hl hb hq
            · simp at hr
          | _ => simp at hr

theorem pBounded_decCall_guestInv_csr
    {names : List String}
    {P Pc R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop}
    {fname name : MlS} {args : List (ExpHOL 64)} {B Bc : Nat}
    {shape : ShapeHOL} {cont : ProgHOL 64}
    (hP : LocalsOnly names P)
    (hG : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → GuestInv s)
    (hfb : TerminatingFunBoundedOn GuestInv fname B)
    (hspec : FunSpec Pc Qc fname)
    (hentry : CallEntryOn P Pc fname args)
    (hne : ∀ n ∈ names, ofString n ≠ name)
    (hret : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F)
      (values : List (ValueHOL 64)) (body : ProgHOL 64)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
      (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      s.code = originalRuntimeCode → P s →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values →
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      Qc (callEntryStateHOLFinite s callee) (some (.returned v)) post →
      R (setVarHOLFinite name v { post with locals := s.locals }))
    (hb : TerminatingProgBoundedOn R cont Bc)
    (hh : Hoare R cont (fun r t => r = none → P t)) :
    PBounded P (.decCall name shape fname args cont) (B + Bc + 1) :=
  PBounded.decCallTrans hfb hP name hne shape args
    (callEntryOn_guestInv_csr hG fname args)
    (funSpec_resumeOn_csr hspec hentry hret) hb hh

-- Call-site wrappers:
-- 1. htab_set on CsrTabs
theorem pBounded_htab_set_csrTabs
    (tf_htab_set : TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set»)
    (h_htab_set : type_of% @htab_set_spec)
    (tname : String) (ht_mem : tname = "cache" ∨ tname = "new_roots")
    (ekey eval_e : ExpHOL 64) :
    PBounded CsrTabs
      (.call (some (none, none)) (ofString "htab_set")
        [.var .local (ofString tname), ekey, eval_e])
      (K.«htab_set» + 1) := by
  refine pBounded_call0_entry_csr tf_htab_set (fun s hs => (csrTabs_worldOK hs).1.1) h_htab_set ?_ ?_
  · intro F s values body callee ret hc hs ha hl
    obtain ⟨v1, _, _, he1, _, _, hc1, _, _⟩ :=
      P3MptSet.callee_param_three_exp s (ofString "htab_set")
        (ofString "t") (ofString "key") (ofString "value") .one .one .one
        (sourceFnBody Guest.Software.guestFn_htab_set) .one
        (hc ▸ SoloHtabSet.lookup_htab_set)
        (.var .local (ofString tname)) ekey eval_e values body callee ret ha hl
    have ht_eq : locN (callEntryStateHOLFinite s callee) "t" = locN s tname := by
      unfold locN callEntryStateHOLFinite; dsimp only; rw [hc1]
      simp only [evalAt, evalHOLExact] at he1; rw [← he1]
    apply csrTablesAt_htabArgWF (localsFree_csrTablesAt _ _ s callee _ hs)
    exact ht_mem.elim (fun h => Or.inl (ht_eq.trans (by subst h; rfl)))
      (fun h => Or.inr (ht_eq.trans (by subst h; rfl)))
  · intro F s vs body callee ret v post hc hs ha hl hb hq
    obtain ⟨v1, _, _, he1, _, _, hc1, _, _⟩ :=
      P3MptSet.callee_param_three_exp s (ofString "htab_set")
        (ofString "t") (ofString "key") (ofString "value") .one .one .one
        (sourceFnBody Guest.Software.guestFn_htab_set) .one
        (hc ▸ SoloHtabSet.lookup_htab_set)
        (.var .local (ofString tname)) ekey eval_e vs body callee ret ha hl
    have ht_eq : locN (callEntryStateHOLFinite s callee) "t" = locN s tname := by
      unfold locN callEntryStateHOLFinite; dsimp only; rw [hc1]
      simp only [evalAt, evalHOLExact] at he1; rw [← he1]
    have hexit : HtabExit (callEntryStateHOLFinite s callee) post := hq v rfl
    have hmeta := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body
    rw [hb] at hmeta
    have hpost : CsrTablesAt post (locN s "cache") (locN s "new_roots") :=
      htabExit_csrTablesAt (localsFree_csrTablesAt _ _ s callee _ hs)
        (ht_mem.elim (fun h => Or.inl (ht_eq.trans (by subst h; rfl)))
          (fun h => Or.inr (ht_eq.trans (by subst h; rfl))))
        hexit hmeta.2.2.1
    exact localsFree_csrTablesAt _ _ post s.locals post.clock hpost

-- 2. htab_set on CsrMptBufs
theorem pBounded_htab_set_csrMptBufs
    (tf_htab_set : TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set»)
    (h_htab_set : type_of% @htab_set_spec)
    (mname : String) (buffers : List (String × Nat))
    (tname : String) (ht_mem : tname = "cache" ∨ tname = "new_roots")
    (ekey eval_e : ExpHOL 64) :
    PBounded (CsrMptBufs mname buffers)
      (.call (some (none, none)) (ofString "htab_set")
        [.var .local (ofString tname), ekey, eval_e])
      (K.«htab_set» + 1) := by
  refine pBounded_call0_entry_csr tf_htab_set (fun s hs => (csrMptBufs_worldOK mname buffers hs).1.1)
      h_htab_set ?_ ?_
  · intro F s values body callee ret hc hs ha hl
    obtain ⟨v1, _, _, he1, _, _, hc1, _, _⟩ :=
      P3MptSet.callee_param_three_exp s (ofString "htab_set")
        (ofString "t") (ofString "key") (ofString "value") .one .one .one
        (sourceFnBody Guest.Software.guestFn_htab_set) .one
        (hc ▸ SoloHtabSet.lookup_htab_set)
        (.var .local (ofString tname)) ekey eval_e values body callee ret ha hl
    have ht_eq : locN (callEntryStateHOLFinite s callee) "t" = locN s tname := by
      unfold locN callEntryStateHOLFinite; dsimp only; rw [hc1]
      simp only [evalAt, evalHOLExact] at he1; rw [← he1]
    exact csrLiveBufsAt_htabArgWF (localsFree_csrLiveBufsAt _ _ _ _ s callee _ hs)
      (ht_mem.elim (fun h => Or.inl (ht_eq.trans (by subst h; rfl)))
        (fun h => Or.inr (ht_eq.trans (by subst h; rfl))))
  · intro F s vs body callee ret v post hc hs ha hl hb hq
    obtain ⟨v1, _, _, he1, _, _, hc1, _, _⟩ :=
      P3MptSet.callee_param_three_exp s (ofString "htab_set")
        (ofString "t") (ofString "key") (ofString "value") .one .one .one
        (sourceFnBody Guest.Software.guestFn_htab_set) .one
        (hc ▸ SoloHtabSet.lookup_htab_set)
        (.var .local (ofString tname)) ekey eval_e vs body callee ret ha hl
    have ht_eq : locN (callEntryStateHOLFinite s callee) "t" = locN s tname := by
      unfold locN callEntryStateHOLFinite; dsimp only; rw [hc1]
      simp only [evalAt, evalHOLExact] at he1; rw [← he1]
    have hexit : HtabExit (callEntryStateHOLFinite s callee) post := hq v rfl
    have hmeta := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body
    rw [hb] at hmeta
    have hpost := htabExit_csrLiveBufsAt (localsFree_csrLiveBufsAt _ _ _ _ s callee _ hs)
      (ht_mem.elim (fun h => Or.inl (ht_eq.trans (by subst h; rfl)))
        (fun h => Or.inr (ht_eq.trans (by subst h; rfl))))
      hexit hmeta.2.2.1
    exact localsFree_csrLiveBufsAt _ _ _ _ post s.locals post.clock hpost

-- 3. callee_param_one_exp_csr and callee_param_two_exp_csr
theorem callee_param_one_exp_csr {F : Type} (state : PanSemStateFiniteExact 64 F)
    (fname p1 : MlS) (s1 : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname = some ([(p1, s1)], body, ret))
    (e1 : ExpHOL 64) (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [e1] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    ∃ v1, evalAt state e1 = some v1 ∧ callee.lookup p1 = some v1 ∧ body' = body := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact] at hargs
  rcases he1 : evalAt state e1 with _ | v1 <;>
    simp only [evalAt] at he1 <;>
    simp only [he1, Option.some.injEq] at hargs <;>
    cases hargs
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hlook
  split at hlook
  · cases hlook
  · rename_i exactBody exactLocals exactShape raw
    have heq := Option.some.inj hlook
    rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨rfl, _⟩
    unfold lookupCodeHOLExact at raw
    rw [hl] at raw; dsimp only at raw
    split at raw
    · have rawEq := Option.some.inj raw
      rcases Prod.mk.inj rawEq with ⟨hb, hrest2⟩
      rcases Prod.mk.inj hrest2 with ⟨hloc, -⟩
      subst hb; subst hloc
      refine ⟨v1, rfl, ?_, rfl⟩
      simp [List.zip, List.foldl]
    · cases raw

theorem callee_param_two_exp_csr {F : Type} (state : PanSemStateFiniteExact 64 F)
    (fname p1 p2 : MlS) (s1 s2 : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname = some ([(p1, s1), (p2, s2)], body, ret))
    (e1 e2 : ExpHOL 64) (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [e1, e2] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    ∃ v1 v2, evalAt state e1 = some v1 ∧ evalAt state e2 = some v2 ∧
      callee.lookup p1 = some v1 ∧ callee.lookup p2 = some v2 ∧ body' = body := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact] at hargs
  rcases he1 : evalAt state e1 with _ | v1 <;>
  rcases he2 : evalAt state e2 with _ | v2 <;>
    simp only [evalAt] at he1 he2 <;>
    simp only [he1, he2, Option.some.injEq] at hargs <;>
    cases hargs
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hlook
  split at hlook
  · cases hlook
  · rename_i exactBody exactLocals exactShape raw
    have heq := Option.some.inj hlook
    rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨rfl, _⟩
    unfold lookupCodeHOLExact at raw
    rw [hl] at raw; dsimp only at raw
    split at raw
    · rename_i hcond
      have rawEq := Option.some.inj raw
      rcases Prod.mk.inj rawEq with ⟨hb, hrest2⟩
      rcases Prod.mk.inj hrest2 with ⟨hloc, -⟩
      subst hb; subst hloc
      obtain ⟨hnd, -, -⟩ := hcond
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false] at hnd
      refine ⟨v1, v2, rfl, rfl, ?_, ?_, rfl⟩
      · simp [List.zip, List.foldl, hnd.1]
      · simp [List.zip, List.foldl]
    · cases raw

-- 4. Callee lookups and WorldEff / ByteFrame / ByteEff bridges on CsrLiveBufsAt
theorem lookup_ws_get_account_optional_csr :
    originalRuntimeCode.lookup (ofString "ws_get_account_optional") =
      some ([(ofString "addr", .one)],
        sourceFnBody Guest.Software.guestFn_ws_get_account_optional, .one) :=
  lookup_of_guestAst_getElem 366 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ws_get_account_optional) rfl

theorem lookup_cache_get_root_csr :
    originalRuntimeCode.lookup (ofString "cache_get_root") =
      some ([(ofString "cache", .one), (ofString "addr", .one)],
        sourceFnBody Guest.Software.guestFn_cache_get_root, .one) :=
  lookup_of_guestAst_getElem 842 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_cache_get_root) rfl

theorem callee_param_five_exp_body_csr {F : Type} (state : PanSemStateFiniteExact 64 F)
    (fname p1 p2 p3 p4 p5 : MlS) (s1 s2 s3 s4 s5 : ShapeHOL)
    (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname =
      some ([(p1, s1), (p2, s2), (p3, s3), (p4, s4), (p5, s5)], body, ret))
    (e1 e2 e3 e4 e5 : ExpHOL 64) (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [e1, e2, e3, e4, e5] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    ∃ v1 v2 v3 v4 v5,
      evalAt state e1 = some v1 ∧ evalAt state e2 = some v2 ∧
      evalAt state e3 = some v3 ∧ evalAt state e4 = some v4 ∧
      evalAt state e5 = some v5 ∧
      callee.lookup p1 = some v1 ∧ callee.lookup p2 = some v2 ∧
      callee.lookup p3 = some v3 ∧ callee.lookup p4 = some v4 ∧
      callee.lookup p5 = some v5 ∧ body' = body := by
  obtain ⟨v1, v2, v3, v4, v5, he1, he2, he3, he4, he5, hc1, hc2, hc3, hc4, hc5⟩ :=
    callee_param_five_exp_csr state fname p1 p2 p3 p4 p5 s1 s2 s3 s4 s5 body ret hl
      e1 e2 e3 e4 e5 values body' callee ret' hargs hlook
  have hb := lookupCodeHOLFinite_installed_body state.code.lookup fname
    [(p1, s1), (p2, s2), (p3, s3), (p4, s4), (p5, s5)] body body' ret ret' values callee hl hlook
  exact ⟨v1, v2, v3, v4, v5, he1, he2, he3, he4, he5, hc1, hc2, hc3, hc4, hc5, hb⟩

theorem worldEff_of_byteFrame_csr {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hA : ArenaReady s) (hc : s.code = originalRuntimeCode)
    (hpos : ∀ r ∈ Rl, 0 < r.2)
    (hbf : M13.ByteFrame Rl s post) :
    R16Shards.WorldEff s post Rl [] [] := by
  have hcode : post.code = s.code := by rw [hbf.1]
  have hmemaddrs : post.memaddrs = s.memaddrs := by rw [hbf.1]
  have hsh : post.shMemaddrs = s.shMemaddrs := by rw [hbf.1]
  have hbase : post.baseAddr = s.baseAddr := by rw [hbf.1]
  have hbe : post.be = s.be := by rw [hbf.1]
  have hesh : post.eshapes = s.eshapes := by rw [hbf.1]
  have hglob : post.globals = s.globals := by rw [hbf.1]
  have hGp : GuestInv post := guestInv_congr hcode hmemaddrs hsh hbase hA.1
  have hAp : ArenaReady post := ⟨hGp, arenaOK_congr hglob hA.2⟩
  refine ⟨hAp, hcode.trans hc, hmemaddrs, hbe, hesh,
    by simp [globN, hglob], by simp [globN, hglob], by simp [globN, hglob],
    fun _ _ => by rw [hglob], ?_, fun a hne => (hbf.2.1 a hne).1, ?_, ?_⟩
  · refine ⟨fun k _ => Or.inl (by simp [globN, hglob]), ?_⟩
    rw [List.pairwise_iff_getElem]
    intro i j _ _ _ h1 _; exact absurd (by simp [globN, hglob]) h1.1
  · intro a hne
    obtain ⟨_, r, hr, hh1, hh2⟩ := hbf.2.1 a hne
    exact Or.inl ⟨r, hr, hpos r hr, hh1, hh2⟩
  · intro b hb64 hne
    obtain ⟨r, hr, hin⟩ := hbf.2.2 b hb64 hne
    exact Or.inl ⟨r, hr, hin⟩

private theorem lookup_resVarEq_ne_csr (m : HolFiniteMapExact MlS (ValueHOL 64))
    (k q : MlS) (old : Option (ValueHOL 64)) (hne : k ≠ q) :
    (m.resVarEq (k, old)).lookup q = m.lookup q := by
  unfold HolFiniteMapExact.resVarEq
  cases old with
  | none => simp [HolFiniteMapExact.eraseEq, FDOMSUB_HOL, hne.symm]
  | some v => simp [HolFiniteMapExact.updateEq, FUPDATE_HOL, hne.symm]

private theorem not_resumes_err_csr1 : ¬ Resumes (some (.error : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h

private def encodeAcctZeroLoopCsr1 : ProgHOL 64 :=
  .while (.cmp .lower (.var .local (ofString "z")) (.const (32#64)))
    (.seq
      (.ite (.cmp .notEqual
          (.loadByte (.op .add [.var .global (ofString "mpt_hash_scratch"), .var .local (ofString "z")]))
          (.const (0#64)))
        .break .skip)
      (.assign .local (ofString "z") (.op .add [.var .local (ofString "z"), .const (1#64)])))

private theorem eval_encodeAcctZeroLoopCsr1 {F : Type} :
    ∀ (k : Nat) (s : PanSemStateFiniteExact 64 F) (zw : BitVec 64),
      s.clock = k →
      s.locals.lookup (ofString "z") = some (.val (.word zw)) →
      zw.toNat ≤ 32 →
      (evaluateHOLFiniteState s encodeAcctZeroLoopCsr1).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState s encodeAcctZeroLoopCsr1).1 = none →
        ∃ zw' : BitVec 64,
          zw'.toNat ≤ 32 ∧
          (evaluateHOLFiniteState s encodeAcctZeroLoopCsr1).2.locals =
            s.locals.update (ofString "z", .val (.word zw')) ∧
          (evaluateHOLFiniteState s encodeAcctZeroLoopCsr1).2 =
            { s with locals := (evaluateHOLFiniteState s encodeAcctZeroLoopCsr1).2.locals,
                     clock := (evaluateHOLFiniteState s encodeAcctZeroLoopCsr1).2.clock }) ∧
      ((evaluateHOLFiniteState s encodeAcctZeroLoopCsr1).1 ≠ none →
        ¬ Resumes (evaluateHOLFiniteState s encodeAcctZeroLoopCsr1).1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro s zw hclk hz hzw_le hnt
    unfold encodeAcctZeroLoopCsr1 at hnt ⊢
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    have hcond : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .lower (.var .local (ofString "z")) (.const (32#64))) =
        some (.val (.word (if zw.toNat < 32 then 1 else 0))) := by
      simp [evalHOLFinite, evalHOLExact, hz, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hlt : zw.toNat < 32
    · rw [if_pos hlt, if_pos (by decide : (1 : BitVec 64) ≠ 0)] at hnt ⊢
      by_cases hk0 : s.clock = 0
      · simp [hk0] at hnt
      · rw [if_neg hk0] at hnt ⊢
        let sd := decClockHOLFinite s
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
        rcases hev_lb : @evalHOLExact 64 F _ sd.toExact (fun a => Classical.propDecidable (sd.memaddrs a))
            (.cmp .notEqual
              (.loadByte (.op .add [.var .global (ofString "mpt_hash_scratch"), .var .local (ofString "z")]))
              (.const (0#64))) with _ | cv
        · simp [sd, hev_lb] at hnt ⊢; exact not_resumes_err_csr1
        · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try (simp [sd, hev_lb] at hnt ⊢; exact not_resumes_err_csr1)
          simp only [sd, hev_lb] at hnt ⊢
          by_cases hcw0 : cw = 0
          · rw [if_pos hcw0, evaluateHOLFiniteState_skip] at hnt ⊢; dsimp only at hnt ⊢
            have hsd_z : (decClockHOLFinite s).locals.lookup (ofString "z") = some (.val (.word zw)) := hz
            have hasg : evaluateHOLFiniteState (decClockHOLFinite s)
                (.assign .local (ofString "z") (.op .add [.var .local (ofString "z"), .const (1#64)])) =
                (none, setVarHOLFinite (ofString "z") (.val (.word (zw + 1#64))) (decClockHOLFinite s)) := by
              simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hsd_z,
                wordOpHOL, wordOp, valueIsWord, valueWord, isValidValueHOLExact, lookupKvarHOLExact,
                shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]
            rw [hasg] at hnt ⊢; dsimp only at hnt ⊢
            let s1 := setVarHOLFinite (ofString "z") (.val (.word (zw + 1#64))) (decClockHOLFinite s)
            have hs1_clk : s1.clock < k := by simp [s1, setVarHOLFinite, decClockHOLFinite, hclk]; omega
            have hs1_z : s1.locals.lookup (ofString "z") = some (.val (.word (zw + 1#64))) := by
              simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have hzw1 : (zw + 1#64).toNat = zw.toNat + 1 :=
              BitVec.toNat_add_of_lt (by change zw.toNat + 1 < 2 ^ 64; omega)
            obtain ⟨ih1, ih2⟩ := ih s1.clock hs1_clk s1 (zw + 1#64) rfl hs1_z (by omega) hnt
            refine ⟨fun hn => ?_, ih2⟩
            obtain ⟨zw', hle', hloc', heq'⟩ := ih1 hn
            refine ⟨zw', hle', ?_, ?_⟩
            · change (evaluateHOLFiniteState s1 encodeAcctZeroLoopCsr1).2.locals = _
              rw [hloc']
              apply HolFiniteMapExact.ext_lookup; intro m
              by_cases hm : m = ofString "z"
              · subst hm; simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              · simp [s1, setVarHOLFinite, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  hm, Ne.symm hm]
            · change (evaluateHOLFiniteState s1 encodeAcctZeroLoopCsr1).2 =
                { s with locals := (evaluateHOLFiniteState s1 encodeAcctZeroLoopCsr1).2.locals,
                         clock := (evaluateHOLFiniteState s1 encodeAcctZeroLoopCsr1).2.clock }
              rw [heq']; simp [s1, encodeAcctZeroLoopCsr1, setVarHOLFinite, decClockHOLFinite]
          · rw [if_neg hcw0, evaluateHOLFiniteState_break]
            dsimp only
            refine ⟨fun _ => ⟨zw, hzw_le, ?_, by cases s; rfl⟩, fun h => False.elim (h rfl)⟩
            apply HolFiniteMapExact.ext_lookup; intro m
            by_cases hm : m = ofString "z"
            · subst hm; simp [decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hz]
            · simp [decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm, Ne.symm hm]
    · rw [if_neg hlt, if_neg (by decide : ¬ ((0 : BitVec 64) ≠ 0))]
      refine ⟨fun _ => ⟨zw, hzw_le, ?_, by cases s; rfl⟩, fun h => False.elim (h rfl)⟩
      apply HolFiniteMapExact.ext_lookup; intro m
      by_cases hm : m = ofString "z"
      · subst hm; simp [HolFiniteMapExact.lookup_update, FUPDATE, hz]
      · simp [HolFiniteMapExact.lookup_update, FUPDATE, hm, Ne.symm hm]

private def toBeMinLoopBodyCsr : ProgHOL 64 :=
  .dec (ofString "pos") .one
    (.op .sub [.op .sub [.var .local (ofString "len"), .const 1#64], .var .local (ofString "i")])
    (.decCall (ofString "l") .one (ofString "u256_limb")
      [.var .local (ofString "a"), .shift .lsr (.var .local (ofString "pos")) (.const 3#64)]
      (.seq
        (.storeByte (.op .add [.var .local (ofString "out"), .var .local (ofString "i")])
          (.op .and
            [.shift .lsr (.var .local (ofString "l"))
              (.panop .mul [.op .and [.var .local (ofString "pos"), .const 7#64], .const 8#64]),
             .const 255#64]))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))))

private def toBeMinWhileCsr : ProgHOL 64 :=
  .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len"))) toBeMinLoopBodyCsr

private theorem toBeMinLoopBody_step_csr {F : Type}
    (s : PanSemStateFiniteExact 64 F) (R : List Ivl) (len iv : BitVec 64)
    (outOpt : Option (ValueHOL 64))
    (hcode : s.code = originalRuntimeCode)
    (hdom_eq : s.memaddrs = ordinaryDomain)
    (hiv_lt : iv.toNat < len.toNat)
    (hlen_le : len.toNat ≤ 32)
    (hlen : s.locals.lookup (ofString "len") = some (.val (.word len)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iv)))
    (hout : s.locals.lookup (ofString "out") = outOpt)
    (hR : ∀ outW : BitVec 64, outOpt = some (.val (.word outW)) → (outW.toNat, 32) ∈ R) :
    let res := evaluateHOLFiniteState s toBeMinLoopBodyCsr
    M13.ByteFrame R s res.2 ∧
    res.1 ≠ some .continue ∧
    (res.1 = none →
      res.2.code = originalRuntimeCode ∧
      res.2.memaddrs = ordinaryDomain ∧
      res.2.locals.lookup (ofString "len") = some (.val (.word len)) ∧
      res.2.locals.lookup (ofString "out") = outOpt ∧
      ∃ iv' : BitVec 64, res.2.locals.lookup (ofString "i") = some (.val (.word iv'))) := by
  dsimp only [toBeMinLoopBodyCsr]
  rw [evaluateHOLFiniteState_dec_total]; dsimp only
  let posv := (len - 1#64) - iv
  have hev_pos : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .sub [.op .sub [.var .local (ofString "len"), .const 1#64], .var .local (ofString "i")]) =
      some (.val (.word posv)) := by
    simp [evalHOLExact, evalListHOLExact, hlen, hi, wordOpHOL, wordOp, valueIsWord, valueWord, posv]
  rw [hev_pos]; dsimp only
  have hsh1 : shapeEqHOL .one (shapeOfHOLExact (.val (.word posv))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh1]; dsimp only
  set s1 := setVarHOLFinite (ofString "pos") (.val (.word posv)) s
  have hs1_len : s1.locals.lookup (ofString "len") = some (.val (.word len)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlen,
      show ofString "pos" ≠ ofString "len" by decide]
  have hs1_i : s1.locals.lookup (ofString "i") = some (.val (.word iv)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hi,
      show ofString "pos" ≠ ofString "i" by decide]
  have hs1_out : s1.locals.lookup (ofString "out") = outOpt := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hout,
      show ofString "pos" ≠ ofString "out" by decide]
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  split
  · exact ⟨(M13.ByteFrame.refl R s).setVar _ _ |>.locals _, by simp, fun h => by simp at h⟩
  · rename_i values _
    split
    · exact ⟨(M13.ByteFrame.refl R s).setVar _ _ |>.locals _, by simp, fun h => by simp at h⟩
    · rename_i body' callee ret' hl
      have hsame := lookupCodeHOLFinite_installed_body s1.code.lookup (ofString "u256_limb")
        [(ofString "a", .comb [.one, .one, .one, .one]), (ofString "i", .one)]
        (sourceFnBody Guest.Software.guestFn_u256_limb) body' .one ret' values callee
        (by rw [show s1.code = originalRuntimeCode from hcode]; exact M13.lookup_u256_limb) hl
      subst hsame
      split
      · exact ⟨(M13.ByteFrame.refl R s).setVar _ _ |>.emptyLocals.locals _, by simp, fun h => by simp at h⟩
      · dsimp only
        have hlf_b : M13.LocFrame (callEntryStateHOLFinite s1 callee)
            (evaluateHOLFiniteState (callEntryStateHOLFinite s1 callee)
              (sourceFnBody Guest.Software.guestFn_u256_limb)).2 :=
          M13.locFrameW_eval _ rfl _
        rcases hrun_l : evaluateHOLFiniteState (callEntryStateHOLFinite s1 callee)
            (sourceFnBody Guest.Software.guestFn_u256_limb) with ⟨rl, post_l⟩
        rw [hrun_l] at hlf_b
        have hbf_l : M13.ByteFrame R s post_l :=
          M13.ByteFrame.of_locFrame R (by unfold M13.LocFrame at hlf_b ⊢; dsimp only at hlf_b; rw [hlf_b]; rfl)
        rcases rl with _ | rl
        · exact ⟨hbf_l.locals _, by simp, fun h => by simp at h⟩
        · cases rl with
          | returned vl =>
            dsimp only
            split
            · dsimp only
              set s2 := setVarHOLFinite (ofString "l") vl { post_l with locals := s1.locals }
              have hs2_bf : M13.ByteFrame R s s2 := (hbf_l.locals _).setVar _ _
              have hs2_code : s2.code = originalRuntimeCode := by rw [hs2_bf.1]; exact hcode
              have hs2_dom : s2.memaddrs = ordinaryDomain := by rw [hs2_bf.1]; exact hdom_eq
              have hs2_len : s2.locals.lookup (ofString "len") = some (.val (.word len)) := by
                simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_len,
                  show ofString "l" ≠ ofString "len" by decide]
              have hs2_i : s2.locals.lookup (ofString "i") = some (.val (.word iv)) := by
                simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_i,
                  show ofString "l" ≠ ofString "i" by decide]
              have hs2_out : s2.locals.lookup (ofString "out") = outOpt := by
                simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_out,
                  show ofString "l" ≠ ofString "out" by decide]
              let sbProg : ProgHOL 64 := .storeByte (.op .add [.var .local (ofString "out"), .var .local (ofString "i")])
                (.op .and
                  [.shift .lsr (.var .local (ofString "l"))
                    (.panop .mul [.op .and [.var .local (ofString "pos"), .const 7#64], .const 8#64]),
                   .const 255#64])
              have hbf_sb : M13.ByteFrame R s2 (evaluateHOLFiniteState s2 sbProg).2 := by
                refine M13.byteFrame_storeByte s2 _ _ (fun addr hdst hdom => ?_)
                rcases hout_case : outOpt with _ | outVal
                · simp [evalHOLExact, evalListHOLExact, hs2_out, hout_case] at hdst
                · cases outVal with
                  | rStruct _ =>
                    simp [evalHOLExact, evalListHOLExact, hs2_out, hs2_i, hout_case, List.all, wordOpHOL, wordOp, valueIsWord] at hdst
                  | nStruct _ _ =>
                    simp [evalHOLExact, evalListHOLExact, hs2_out, hs2_i, hout_case, List.all, wordOpHOL, wordOp, valueIsWord] at hdst
                  | val wl =>
                    cases wl with
                    | word outW =>
                      have haddr_eq : addr = outW + iv := by
                        simp [evalHOLExact, evalListHOLExact, hs2_out, hs2_i, hout_case,
                          wordOpHOL, wordOp, valueIsWord, valueWord] at hdst
                        exact hdst.symm
                      subst haddr_eq
                      rw [hs2_dom] at hdom
                      have hsb_val : sourceBase = 2701131776 := rfl
                      have hnw := M13.add_no_wrap_of_memaddrs outW iv (by omega) hdom
                      exact ⟨(outW.toNat, 32), hR outW hout_case, by rw [hnw.2.1]; omega, by rw [hnw.2.1]; omega⟩
              rw [evaluateHOLFiniteState_seq_line780]
              rcases hsb_run : evaluateHOLFiniteState s2 sbProg with ⟨rsb, s3⟩
              rw [hsb_run] at hbf_sb
              have hsb_ctrl := evaluate_storeByte_control_frame s2
                (.op .add [.var .local (ofString "out"), .var .local (ofString "i")])
                (.op .and
                  [.shift .lsr (.var .local (ofString "l"))
                    (.panop .mul [.op .and [.var .local (ofString "pos"), .const 7#64], .const 8#64]),
                   .const 255#64])
              have hsb_r : rsb = none ∨ rsb = some .error := by
                have h1 := hsb_ctrl.1; change (evaluateHOLFiniteState s2 sbProg).1 = _ ∨ (evaluateHOLFiniteState s2 sbProg).1 = _ at h1
                rw [hsb_run] at h1; exact h1
              have hs3_loc : s3.locals = s2.locals := by
                have h2 := hsb_ctrl.2.2.1; change (evaluateHOLFiniteState s2 sbProg).2.locals = s2.locals at h2
                rw [hsb_run] at h2; exact h2
              rcases hsb_r with rfl | rfl
              · dsimp only
                rw [evaluateHOLFiniteState_assign]
                have hs3_i : s3.locals.lookup (ofString "i") = some (.val (.word iv)) := by
                  rw [hs3_loc]; exact hs2_i
                have hs3_len : s3.locals.lookup (ofString "len") = some (.val (.word len)) := by
                  rw [hs3_loc]; exact hs2_len
                have hs3_out : s3.locals.lookup (ofString "out") = outOpt := by
                  rw [hs3_loc]; exact hs2_out
                have hev_inc : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
                    (.op .add [.var .local (ofString "i"), .const 1#64]) = some (.val (.word (iv + 1#64))) := by
                  simp [evalHOLExact, evalListHOLExact, hs3_i, wordOpHOL, wordOp, valueIsWord, valueWord]
                rw [hev_inc]; dsimp only
                have hval_i : isValidValueHOLFinite s3 .local (ofString "i") (.val (.word (iv + 1#64))) = true := by
                  simp [isValidValueHOLFinite, lookupKvarHOLFinite, hs3_i, shapeOfHOLExact, shapeEqHOL]
                rw [if_pos hval_i]; dsimp only
                have hbf_all : M13.ByteFrame R s (setKvarHOLFinite .local (ofString "i") (.val (.word (iv + 1#64))) s3) :=
                  (hs2_bf.trans hbf_sb).setVar _ _
                let finalSt :=
                  let __src2 := setKvarHOLFinite .local (ofString "i") (.val (.word (iv + 1#64))) s3
                  let __src1 : PanSemStateFiniteExact 64 F := { __src2 with locals := __src2.locals.resVarEq (ofString "l", s1.locals.lookup (ofString "l")) }
                  ({ __src1 with locals := __src1.locals.resVarEq (ofString "pos", s.locals.lookup (ofString "pos")) } : PanSemStateFiniteExact 64 F)
                have hbf_final : M13.ByteFrame R s finalSt := hbf_all.locals _ |>.locals _
                have hf_code : finalSt.code = originalRuntimeCode := by
                  have h1 := hbf_all.1; dsimp only [finalSt]; rw [h1]; exact hcode
                have hf_dom : finalSt.memaddrs = ordinaryDomain := by
                  have h1 := hbf_all.1; dsimp only [finalSt]; rw [h1]; exact hdom_eq
                refine ⟨hbf_final, by simp, fun _ => ⟨hf_code, hf_dom, ?_, ?_, iv + 1#64, ?_⟩⟩
                · change ((setKvarHOLFinite .local (ofString "i") (.val (.word (iv + 1#64))) s3).locals.resVarEq
                      (ofString "l", s1.locals.lookup (ofString "l")) |>.resVarEq
                      (ofString "pos", s.locals.lookup (ofString "pos"))).lookup (ofString "len") = _
                  rw [lookup_resVarEq_ne_csr _ _ _ _ (by decide), lookup_resVarEq_ne_csr _ _ _ _ (by decide)]
                  simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_len,
                    show ofString "i" ≠ ofString "len" by decide]
                · change ((setKvarHOLFinite .local (ofString "i") (.val (.word (iv + 1#64))) s3).locals.resVarEq
                      (ofString "l", s1.locals.lookup (ofString "l")) |>.resVarEq
                      (ofString "pos", s.locals.lookup (ofString "pos"))).lookup (ofString "out") = _
                  rw [lookup_resVarEq_ne_csr _ _ _ _ (by decide), lookup_resVarEq_ne_csr _ _ _ _ (by decide)]
                  simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_out,
                    show ofString "i" ≠ ofString "out" by decide]
                · change ((setKvarHOLFinite .local (ofString "i") (.val (.word (iv + 1#64))) s3).locals.resVarEq
                      (ofString "l", s1.locals.lookup (ofString "l")) |>.resVarEq
                      (ofString "pos", s.locals.lookup (ofString "pos"))).lookup (ofString "i") = _
                  rw [lookup_resVarEq_ne_csr _ _ _ _ (by decide), lookup_resVarEq_ne_csr _ _ _ _ (by decide)]
                  simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              · exact ⟨(hs2_bf.trans hbf_sb).locals _ |>.locals _, by simp, fun h => by simp at h⟩
            · exact ⟨hbf_l.locals _, by simp, fun h => by simp at h⟩
          | «break» => exact ⟨hbf_l.locals _, by simp, fun h => by simp at h⟩
          | «continue» => exact ⟨hbf_l.locals _, by simp, fun h => by simp at h⟩
          | _ => exact ⟨hbf_l.emptyLocals.locals _, by simp, fun h => by simp at h⟩

private theorem toBeMinWhile_byteFrame_csr {F : Type}
    (s : PanSemStateFiniteExact 64 F) (R : List Ivl) (len iv : BitVec 64)
    (outOpt : Option (ValueHOL 64))
    (hcode : s.code = originalRuntimeCode)
    (hdom_eq : s.memaddrs = ordinaryDomain)
    (hlen_le : len.toNat ≤ 32)
    (hlen : s.locals.lookup (ofString "len") = some (.val (.word len)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iv)))
    (hout : s.locals.lookup (ofString "out") = outOpt)
    (hR : ∀ outW : BitVec 64, outOpt = some (.val (.word outW)) → (outW.toNat, 32) ∈ R) :
    M13.ByteFrame R s (evaluateHOLFiniteState s toBeMinWhileCsr).2 := by
  suffices hrec : ∀ (clk : Nat) (st : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      st.clock = clk →
      st.code = originalRuntimeCode →
      st.memaddrs = ordinaryDomain →
      st.locals.lookup (ofString "len") = some (.val (.word len)) →
      st.locals.lookup (ofString "i") = some (.val (.word w)) →
      st.locals.lookup (ofString "out") = outOpt →
      M13.ByteFrame R st (evaluateHOLFiniteState st toBeMinWhileCsr).2 by
    exact hrec s.clock s iv rfl hcode hdom_eq hlen hi hout
  intro clk
  induction clk using Nat.strongRecOn with
  | ind clk ih =>
    intro st w hclk hst_code hst_dom hst_len hst_i hst_out
    dsimp only [toBeMinWhileCsr]
    rw [evaluateHOLFiniteState_while_total, evalHOLFinite_eq_toExact]
    have hevc : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len"))) =
        some (.val (.word (if w.toNat < len.toNat then 1 else 0))) := by
      simp only [evalHOLExact, hst_i, hst_len, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        BitVec.lt_def, decide_eq_true_eq]
    rw [hevc]; dsimp only
    by_cases hlt_w : w.toNat < len.toNat
    · rw [if_pos hlt_w]
      have h1 : (1 : BitVec 64) ≠ 0 := by intro h; cases h
      rw [if_pos h1]
      by_cases hcz : st.clock = 0
      · rw [if_pos hcz]; exact (M13.ByteFrame.refl R st).emptyLocals
      · rw [if_neg hcz]
        rw [fixClockHOLFinite_evaluateState]
        have hstep := toBeMinLoopBody_step_csr (decClockHOLFinite st) R len w outOpt
          hst_code hst_dom hlt_w hlen_le hst_len hst_i hst_out hR
        have hcle := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) toBeMinLoopBodyCsr
        rcases hbr : evaluateHOLFiniteState (decClockHOLFinite st) toBeMinLoopBodyCsr with ⟨rb, mid⟩
        rw [hbr] at hstep hcle; dsimp only at hstep hcle
        have hclk_lt : mid.clock < clk := by change mid.clock ≤ st.clock - 1 at hcle; omega
        have hbf1 : M13.ByteFrame R st mid :=
          (M13.ByteFrame.of_locFrame R (s := st) (t := decClockHOLFinite st) rfl).trans hstep.1
        cases rb with
        | none =>
          obtain ⟨hm_code, hm_dom, hm_len, hm_out, w', hm_i⟩ := hstep.2.2 rfl
          exact hbf1.trans (ih mid.clock hclk_lt mid w' rfl hm_code hm_dom hm_len hm_i hm_out)
        | some r' =>
          cases r' with
          | «continue» => exact absurd rfl hstep.2.1
          | _ => exact hbf1
    · rw [if_neg hlt_w]
      have h0 : ¬ ((0 : BitVec 64) ≠ 0) := not_not.mpr rfl
      rw [if_neg h0]; exact M13.ByteFrame.refl R st

theorem byteFrame_u256_to_be_min_body_csr {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (hdom_eq : s.memaddrs = ordinaryDomain) :
    M13.ByteFrame [(locN s "out", 32)] s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_to_be_min)).2 := by
  let R := [(locN s "out", 32)]
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_u256_to_be_min,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  split
  · exact M13.ByteFrame.refl R s
  · rename_i values _
    split
    · exact M13.ByteFrame.refl R s
    · rename_i body' callee ret' hl
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "u256_byte_length")
        [(ofString "a", .comb [.one, .one, .one, .one])]
        (sourceFnBody Guest.Software.guestFn_u256_byte_length) body' .one ret' values callee
        (by rw [hcode]; exact M13.lookup_u256_byte_length) hl
      subst hsame
      split
      · exact (M13.ByteFrame.refl R s).emptyLocals
      · dsimp only
        have hlf_bl := M13.locFrame_u256_byte_length_body (callEntryStateHOLFinite s callee) hcode
        rcases hrun_bl : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
            (sourceFnBody Guest.Software.guestFn_u256_byte_length) with ⟨rbl, post_bl⟩
        rw [hrun_bl] at hlf_bl
        have hbf_bl : M13.ByteFrame R s post_bl :=
          M13.ByteFrame.of_locFrame R (by unfold M13.LocFrame at hlf_bl ⊢; dsimp only at hlf_bl; rw [hlf_bl]; rfl)
        rcases rbl with _ | rbl
        · exact hbf_bl
        · cases rbl with
          | returned vbl =>
            obtain ⟨len, rfl, hlen_le⟩ := M13.u256_byte_length_body_le_32
              (callEntryStateHOLFinite s callee) hcode vbl (by rw [hrun_bl])
            dsimp only
            split
            · dsimp only
              set s1 := setVarHOLFinite (ofString "len") (.val (.word len)) { post_bl with locals := s.locals }
              have hs1_bf : M13.ByteFrame R s s1 := (hbf_bl.locals _).setVar _ _
              rw [evaluateHOLFiniteState_dec_total]; dsimp only
              have h0_ev : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
                  (.const 0#64) = some (.val (.word 0#64)) := rfl
              rw [h0_ev]; dsimp only
              have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0#64))) = true := by
                simp [shapeEqHOL, shapeOfHOLExact]
              rw [if_pos hsh0]; dsimp only
              set s2 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s1
              have hs2_bf : M13.ByteFrame R s s2 := hs1_bf.setVar _ _
              have hs2_code : s2.code = originalRuntimeCode := by rw [hs2_bf.1]; exact hcode
              have hs2_dom : s2.memaddrs = ordinaryDomain := by rw [hs2_bf.1]; exact hdom_eq
              have hs2_len : s2.locals.lookup (ofString "len") = some (.val (.word len)) := by
                simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "i" ≠ ofString "len" by decide]
              have hs2_i : s2.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
                simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              have hs2_out : s2.locals.lookup (ofString "out") = s.locals.lookup (ofString "out") := by
                simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "i" ≠ ofString "out" by decide,
                  show ofString "len" ≠ ofString "out" by decide]
              have hR_mem : ∀ outW : BitVec 64,
                  s.locals.lookup (ofString "out") = some (.val (.word outW)) →
                  (outW.toNat, 32) ∈ R := by
                intro outW houtW
                have hlocN : locN s "out" = outW.toNat := by simp [locN, houtW]
                simp [R, hlocN]
              have hseq_bf : M13.ByteFrame R s2
                  (evaluateHOLFiniteState s2
                    (.seq toBeMinWhileCsr (.return (.var .local (ofString "len"))))).2 := by
                rw [evaluateHOLFiniteState_seq_line780]
                have hw_bf := toBeMinWhile_byteFrame_csr s2 R len 0#64 (s.locals.lookup (ofString "out"))
                  hs2_code hs2_dom hlen_le hs2_len hs2_i hs2_out hR_mem
                rcases hw_run : evaluateHOLFiniteState s2 toBeMinWhileCsr with ⟨rw_res, s3⟩
                rw [hw_run] at hw_bf
                cases rw_res with
                | some _ => exact hw_bf
                | none =>
                  dsimp only
                  exact hw_bf.trans (M13.ByteFrame.of_locFrame R (M13.locFrameW_eval _ rfl s3))
              exact (hs2_bf.trans hseq_bf).locals _ |>.locals _
            · exact hbf_bl
          | «break» => exact hbf_bl
          | «continue» => exact hbf_bl
          | _ => exact hbf_bl.emptyLocals

theorem byteEff_encode_account_body_csr {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (hWOK : WorldOK s)
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_encode_account)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_encode_account)).1) :
    ByteEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_encode_account)).2
      [(locN s "out", 110),
       (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)] := by
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  have hsb_pos : 0 < sourceBase := by rw [sourceBase_val]; decide
  let Rl : List Ivl :=
    [(locN s "out", 110), (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)]
  change ByteEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_encode_account)).2 Rl
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_encode_account,
    FrontendCodecComputation.declToHOLStructural, FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural, FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil, List.map] at hnt hres ⊢
  rw [evaluateHOLFiniteState_dec_total] at hnt hres ⊢
  simp only [evalHOLExact, shapeEqHOL, shapeOfHOLExact, ↓reduceIte] at hnt hres ⊢
  let s0 := setVarHOLFinite (ofString "off") (.val (.word (2#64))) s
  have hGs0 : GuestInv s0 := guestInv_setVar _ _ s hWOK.1.1
  have hs0_off : s0.locals.lookup (ofString "off") = some (.val (.word (2#64))) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs0_other : ∀ m, m ≠ ofString "off" → s0.locals.lookup m = s.locals.lookup m := fun m hm => by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm, Ne.symm hm]
  obtain ⟨dst1, nonce0, w1, s1, hdst1_ev, _, hw1_lo, hw1_hi, hdst1_lt_he, heff1, hs1_loc, hnt1, hres1, hpost1⟩ :=
    eval_decCall_rlp_encode_word_resumes s0 "w"
      (.op .add [.var .local (ofString "out"), .var .local (ofString "off")])
      (.var .local (ofString "nonce")) _
      (fun d => [(d.toNat, 9)]) hcode hGs0
      (fun d => ⟨(d.toNat, 9), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
      hnt hres
  have hout_ex : ∃ out0 : BitVec 64, s.locals.lookup (ofString "out") = some (.val (.word out0)) ∧
      dst1 = out0 + 2 := by
    have hout_s0 := hs0_other (ofString "out") (by decide)
    rcases hout_lk : s.locals.lookup (ofString "out") with _ | ov
    · simp [evalHOLExact, evalListHOLExact, hout_s0, hout_lk, hs0_off] at hdst1_ev
    · rcases ov with ⟨⟨out0⟩⟩ | _ | _
      · simp [evalHOLExact, evalListHOLExact, hout_s0, hout_lk, hs0_off, wordOpHOL, wordOp,
          valueIsWord, valueWord] at hdst1_ev
        exact ⟨out0, rfl, hdst1_ev.symm⟩
      · simp [evalHOLExact, evalListHOLExact, hout_s0, hout_lk, hs0_off, valueIsWord] at hdst1_ev
      · simp [evalHOLExact, evalListHOLExact, hout_s0, hout_lk, hs0_off, valueIsWord] at hdst1_ev
  obtain ⟨out0, hs_out, rfl⟩ := hout_ex
  have hout_nat : locN s "out" = out0.toNat := by simp [locN, hs_out]
  dsimp only [s0] at hpost1
  rw [hpost1]
  have hncr_be : ∀ f, (f == ofString "st_be64" || f == ofString "st_be32" || f == ofString "bswap64") = true →
      ∀ values body callee rs, lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body, callee, rs) →
        noCatchableRaise (fun g => g == ofString "st_be64" || g == ofString "st_be32" || g == ofString "bswap64") body = true := by
    intro f hf values body callee rs hfound
    obtain ⟨params, rs', hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
    simp only [Bool.or_eq_true, beq_iff_eq] at hf
    rcases hf with (rfl | rfl) | rfl
    · have hl := lookup_of_guestAst_getElem 28 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_st_be64) rfl
      change originalRuntimeCode.lookup (ofString "st_be64") = _ at hl
      rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
    · have hl := lookup_of_guestAst_getElem 27 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_st_be32) rfl
      change originalRuntimeCode.lookup (ofString "st_be32") = _ at hl
      rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
    · have hl := lookup_of_guestAst_getElem 23 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_bswap64) rfl
      change originalRuntimeCode.lookup (ofString "bswap64") = _ at hl
      rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
  have call0_be64_not_resumes : ∀ (cur : PanSemStateFiniteExact 64 F) (pExp vExp : ExpHOL 64),
      cur.code = originalRuntimeCode →
      ¬ Resumes (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "st_be64") [pExp, vExp])).1 := by
    intro cur pExp vExp hcc
    rw [evaluateHOLFiniteState_call]
    rcases evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) [pExp, vExp] with _ | vals
    · exact not_resumes_err_csr1
    · dsimp only
      rcases hl : lookupCodeHOLFinite cur.code.lookup (ofString "st_be64") vals with _ | ⟨b, c, rs⟩
      · exact not_resumes_err_csr1
      · dsimp only
        split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · have hbok := hncr_be (ofString "st_be64") (by decide) vals b c rs (by rwa [← hcc])
          have hncr := evaluate_noCatchableRaise _ hncr_be b hbok (callEntryStateHOLFinite cur c) hcc
          rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite cur c) b with ⟨rb, pb⟩
          rw [hrun] at hncr
          cases rb with
          | none => exact not_resumes_err_csr1
          | some rb' =>
            cases rb' with
            | returned _ => dsimp only; split <;> [ (rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h); exact not_resumes_err_csr1 ]
            | exception eid ev =>
              rintro (⟨_, h⟩ | ⟨e', v', h, hne⟩)
              · simp at h
              · injection h with h'; injection h' with h1 h2; subst h1 h2; exact hncr eid ev hne rfl
            | _ => rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
  obtain ⟨phs, hphs_g⟩ := hWOK.1.2.2.2.2.2.2.2.2.2 "mpt_hash_scratch" (by decide)
  have hphs_nat : globN s "mpt_hash_scratch" = phs.toNat := by
    unfold GlobalWord at hphs_g; simp [globN, hphs_g]
  have st_be64_dom_of_none : ∀ (cur : PanSemStateFiniteExact 64 F) (pExp vExp : ExpHOL 64) (pw : BitVec 64),
      cur.code = originalRuntimeCode → GuestInv cur →
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) pExp =
        some (.val (.word pw)) →
      (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "st_be64") [pExp, vExp])).1 = none →
      sourceBase ≤ pw.toNat ∧ ByteEff cur
        (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "st_be64") [pExp, vExp])).2
        [(pw.toNat, 8)] := by
    intro cur pExp vExp pw hcc hGc hp_ev hnone
    have hlook64 : originalRuntimeCode.lookup (ofString "st_be64") =
        some ([(ofString "p", .one), (ofString "v", .one)],
          sourceFnBody Guest.Software.guestFn_st_be64, .one) :=
      lookup_of_guestAst_getElem 28 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_st_be64) rfl
    have hv_ex : ∃ vw : BitVec 64,
        @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) vExp =
          some (.val (.word vw)) := by
      have hnone' := hnone
      rw [evaluateHOLFiniteState_call] at hnone'
      rcases hv_ev : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) vExp with _ | vv
      · simp [evalListHOLFinite, evalListHOLExact, hp_ev, hv_ev] at hnone'
      · rcases vv with ⟨⟨vw⟩⟩ | flds | ⟨nm, flds⟩
        · exact ⟨vw, rfl⟩
        · have ha : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) [pExp, vExp] =
              some [.val (.word pw), .rStruct flds] := by simp [evalListHOLFinite, evalListHOLExact, hp_ev, hv_ev]
          rw [ha] at hnone'; dsimp only at hnone'
          have hl0 : lookupCodeHOLFinite cur.code.lookup (ofString "st_be64") [.val (.word pw), .rStruct flds] = none := by
            apply Option.eq_none_iff_forall_not_mem.2; intro ⟨b, c, r⟩ hm
            have hx := lookupCodeHOLFinite_eq_some cur.code.lookup _ _ b c r hm
            rw [hcc] at hx; simp [lookupCodeHOLExact, hlook64, shapeOfHOLExact, shapeEqHOL] at hx
          rw [hl0] at hnone'; simp at hnone'
        · have ha : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) [pExp, vExp] =
              some [.val (.word pw), .nStruct nm flds] := by simp [evalListHOLFinite, evalListHOLExact, hp_ev, hv_ev]
          rw [ha] at hnone'; dsimp only at hnone'
          have hl0 : lookupCodeHOLFinite cur.code.lookup (ofString "st_be64") [.val (.word pw), .nStruct nm flds] = none := by
            apply Option.eq_none_iff_forall_not_mem.2; intro ⟨b, c, r⟩ hm
            have hx := lookupCodeHOLFinite_eq_some cur.code.lookup _ _ b c r hm
            rw [hcc] at hx; simp [lookupCodeHOLExact, hlook64, shapeOfHOLExact, shapeEqHOL] at hx
          rw [hl0] at hnone'; simp at hnone'
    obtain ⟨vw, hv_ev⟩ := hv_ex
    have hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) [pExp, vExp] =
        some [.val (.word pw), .val (.word vw)] := by
      simp [evalListHOLFinite, evalListHOLExact, hp_ev, hv_ev]
    have heff := call0_byteEff funByteEff_st_be64 cur [pExp, vExp] [(pw.toNat, 8)] hcc hGc
      (fun vs hvs iv hiv _ => by
        rw [hargs] at hvs; injection hvs with hvs; subst hvs
        simp [valWordNat] at hiv; subst hiv
        exact ⟨(pw.toNat, 8), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
      (by rw [hnone]; simp) (Or.inl hnone)
    have hlo : sourceBase ≤ pw.toNat := by
      obtain ⟨_, rv, hrv⟩ := call0_two_word_success cur _ _ _ _ _ _ pw vw (by decide) hcc hlook64 hargs hnone
      let ent := callEntryStateHOLFinite cur
        ((HolFiniteMapExact.empty.update (ofString "p", .val (.word pw))).update (ofString "v", .val (.word vw)))
      have hp_ent : ent.locals.lookup (ofString "p") = some (.val (.word pw)) := by
        simp [ent, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "v" ≠ ofString "p" by decide]
      have hv_ent : ent.locals.lookup (ofString "v") = some (.val (.word vw)) := by
        simp [ent, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hGent : GuestInv ent := guestInv_callEntry cur _ hGc
      have hbody64 : sourceFnBody Guest.Software.guestFn_st_be64 =
          .seq (.ite (.cmp .equal (.op .and [.var .local (ofString "p"), .const 7]) (.const 0))
              (.decCall (ofString "w") .one (ofString "bswap64") [.var .local (ofString "v")]
                (.seq (.store (.var .local (ofString "p")) (.var .local (ofString "w")))
                  (.return (.const 0))))
              .skip)
            (.seq (.call (some (none, none)) (ofString "st_be32")
                [.var .local (ofString "p"), .shift .lsr (.var .local (ofString "v")) (.const 32)])
              (.seq (.call (some (none, none)) (ofString "st_be32")
                  [.op .add [.var .local (ofString "p"), .const 4], .var .local (ofString "v")])
                (.return (.const 0)))) := rfl
      change (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_st_be64)).1 = some (.returned rv) at hrv
      rw [hbody64, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hrv
      have hc7 : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
          (.cmp .equal (.op .and [.var .local (ofString "p"), .const 7]) (.const 0)) =
          some (.val (.word (if pw &&& 7 = 0 then 1 else 0))) := by
        simp [evalHOLExact, evalListHOLExact, hp_ent, wordOpHOL, wordOp, valueIsWord, valueWord,
          Compiler.Encoders.Asm.wordCmpHOL]
      rw [hc7] at hrv; dsimp only at hrv
      by_cases hp7 : pw &&& 7 = 0
      · rw [if_pos hp7, if_neg (by decide : ¬ ((1 : BitVec 64) = 0))] at hrv
        rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrv
        have hvbs : evalListHOLFinite ent (h := fun a => Classical.propDecidable (ent.memaddrs a))
            [.var .local (ofString "v")] = some [.val (.word vw)] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hv_ent]
        rw [hvbs] at hrv; dsimp only at hrv
        rcases hlbs : lookupCodeHOLFinite ent.code.lookup (ofString "bswap64") [.val (.word vw)] with _ | ⟨bbs, cbs, rsbs⟩
        · simp [hlbs] at hrv
        · simp only [hlbs] at hrv
          by_cases hclk_ent : ent.clock = 0
          · simp [hclk_ent] at hrv
          · rw [if_neg hclk_ent] at hrv
            set ent_bs := callEntryStateHOLFinite ent cbs
            have hG_pbs_raw := guestInv_evaluate ent_bs bbs (guestInv_callEntry ent cbs hGent)
            rcases hrun_bs : evaluateHOLFiniteState ent_bs bbs with ⟨_ | rbs, pbs⟩
            · simp [hrun_bs] at hrv
            · rw [hrun_bs] at hG_pbs_raw hrv
              dsimp only at hrv
              cases rbs with
              | returned rv_bs =>
                dsimp only at hrv
                by_cases hsh_bs : (shapeEqHOL (shapeOfHOLExact rv_bs) .one && shapeEqHOL (shapeOfHOLExact rv_bs) rsbs) = true
                · rw [if_pos hsh_bs] at hrv
                  rcases rv_bs with ⟨⟨wv⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hsh_bs)
                  set st_w := setVarHOLFinite (ofString "w") (.val (.word wv)) { pbs with locals := ent.locals }
                  have hGw : GuestInv st_w := guestInv_setVar _ _ _
                    (guestInv_with_locals_clock pbs ent.locals pbs.clock hG_pbs_raw)
                  have hp_w : st_w.locals.lookup (ofString "p") = some (.val (.word pw)) := by
                    simp [st_w, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_ent,
                      show ofString "w" ≠ ofString "p" by decide]
                  have hw_w : st_w.locals.lookup (ofString "w") = some (.val (.word wv)) := by
                    simp [st_w, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  rw [evaluateHOLFiniteState_seq_line780] at hrv
                  have hcf_st := evaluate_store_control_frame st_w (.var .local (ofString "p")) (.var .local (ofString "w"))
                  rcases hst : evaluateHOLFiniteState st_w
                      (.store (.var .local (ofString "p")) (.var .local (ofString "w"))) with ⟨rst, mst⟩
                  rw [hst] at hcf_st
                  rcases hcf_st.1 with hrst | hrst
                  · subst hrst
                    obtain ⟨x, hx, hdlo, _, _⟩ := store_one_domain hGw (.var .local (ofString "p")) (.var .local (ofString "w"))
                      (fun v hv => by simp [evalHOLExact, hw_w] at hv; exact ⟨wv, hv.symm⟩)
                      (by rw [hst])
                    simp [evalHOLExact, hp_w] at hx; subst hx; exact hdlo
                  · subst hrst; simp [hst] at hrv
                · rw [if_neg hsh_bs] at hrv; simp at hrv
              | _ => simp at hrv
      · rw [if_neg hp7, if_pos rfl, evaluateHOLFiniteState_skip] at hrv; dsimp only at hrv
        rw [evaluateHOLFiniteState_seq_line780] at hrv
        have hlook32 : originalRuntimeCode.lookup (ofString "st_be32") =
            some ([(ofString "p", .one), (ofString "v", .one)],
              sourceFnBody Guest.Software.guestFn_st_be32, .one) :=
          lookup_of_guestAst_getElem 27 (by rw [guestAst_len]; decide)
            (extractFn Guest.Software.guestFn_st_be32) rfl
        have ha1 : evalListHOLFinite ent (h := fun a => Classical.propDecidable (ent.memaddrs a))
            [.var .local (ofString "p"), .shift .lsr (.var .local (ofString "v")) (.const 32)] =
            some [.val (.word pw), .val (.word (vw >>> 32))] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp_ent, hv_ent, wordShiftHOL]
        rcases hc1 : evaluateHOLFiniteState ent
            (.call (some (none, none)) (ofString "st_be32")
              [.var .local (ofString "p"), .shift .lsr (.var .local (ofString "v")) (.const 32)]) with ⟨rc1, m1⟩
        rw [hc1] at hrv
        have hor1 : rc1 = none ∨ Resumes rc1 := by
          cases rc1 with
          | none => exact Or.inl rfl
          | some _ => exact Or.inr (Or.inl ⟨rv, hrv⟩)
        have hres1_b := call0_two_word_resumes ent _ _ _ _ _ _ pw (vw >>> 32) (by decide) hcc hlook32 ha1 (by rw [hc1]; exact hor1)
        exact (st_be32_body_eff _ pw (guestInv_callEntry ent _ hGent)
          (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "v" ≠ ofString "p" by decide])
          hres1_b).2.1
    exact ⟨hlo, heff⟩
  have hphs_bound_if_nz : phs.toNat ≠ 0 → phs.toNat + 40 ≤ heapEnd := by
    intro hnz
    obtain ⟨hGI0, S0, hWT0⟩ := hWOK
    have hF0 := hWT0.2.2.1
    have hmf : (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40) ∈ fixedObjects s := by
      unfold fixedObjects
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_map.2 ⟨("mpt_hash_scratch", 40), by decide, rfl⟩
    rw [hphs_nat, if_neg hnz] at hmf
    rcases hF0.1 _ hmf with h0 | ⟨hal, _⟩
    · simp at h0
    · rcases hal with ⟨_, hi⟩ | ⟨_, hi⟩
      · dsimp only at hi
        have h1 : globN s "heap_ptr" ≤ heapLimit := hGI0.2.2.1
        have h2 : heapLimit ≤ heapEnd := by decide
        omega
      · dsimp only at hi
        have h2 : scratchEnd ≤ heapEnd := by decide
        omega
  have hs1_code : s1.code = originalRuntimeCode := heff1.code.trans hcode
  have hGs1 : GuestInv s1 := guestInv_congr heff1.code heff1.memaddrs heff1.shMemaddrs heff1.baseAddr hGs0
  have hs1_off : s1.locals.lookup (ofString "off") = some (.val (.word (2#64))) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs0_off, show ofString "w" ≠ ofString "off" by decide]
  have hs1_w : s1.locals.lookup (ofString "w") = some (.val (.word w1)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  rw [evaluateHOLFiniteState_seq_line780] at hnt1 hres1 ⊢
  have hasg_off1 : evaluateHOLFiniteState s1
      (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "w")])) =
      (none, setVarHOLFinite (ofString "off") (.val (.word ((2#64) + w1))) s1) := by
    simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hs1_off, hs1_w,
      wordOpHOL, wordOp, valueIsWord, valueWord, isValidValueHOLExact, lookupKvarHOLExact,
      shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]
  rw [hasg_off1] at hnt1 hres1 ⊢; dsimp only at hnt1 hres1 ⊢
  set off2 := (2#64) + w1
  have hoff2_nat : off2.toNat = 2 + w1.toNat := BitVec.toNat_add_of_lt (by change 2 + w1.toNat < 2 ^ 64; omega)
  set s2 := setVarHOLFinite (ofString "off") (.val (.word off2)) s1
  have hs2_code : s2.code = originalRuntimeCode := hs1_code
  have hGs2 : GuestInv s2 := guestInv_setVar _ _ s1 hGs1
  have hs2_glob : s2.globals = s.globals := heff1.globals
  rw [evaluateHOLFiniteState_seq_line780] at hnt1 hres1 ⊢
  rcases hbe0 : evaluateHOLFiniteState s2
      (.call (some (none, none)) (ofString "st_be64")
        [.var .global (ofString "mpt_hash_scratch"), .rfield 3 (.var .local (ofString "balance"))]) with ⟨rbe0, s3⟩
  rw [hbe0] at hnt1 hres1
  cases rbe0 with
  | some _ => dsimp only at hres1; exact False.elim (call0_be64_not_resumes s2 _ _ hs2_code (by rw [hbe0]; exact hres1))
  | none =>
    dsimp only at hnt1 hres1 ⊢
    have hphs_s2 : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
        (.var .global (ofString "mpt_hash_scratch")) = some (.val (.word phs)) := by
      change s2.globals.lookup _ = _; rw [hs2_glob]; exact hphs_g
    obtain ⟨hphs_lo, heff_be0⟩ := st_be64_dom_of_none s2
      (.var .global (ofString "mpt_hash_scratch")) (.rfield 3 (.var .local (ofString "balance")))
      phs hs2_code hGs2 hphs_s2 (by rw [hbe0])
    rw [hbe0] at heff_be0; dsimp only at heff_be0
    have hphs_nz : phs.toNat ≠ 0 := by omega
    have hphs_hi : phs.toNat + 40 ≤ heapEnd := hphs_bound_if_nz hphs_nz
    have hs3_loc : s3.locals = s2.locals := by
      have := call0_locals_r16 s2 (ofString "st_be64")
        [.var .global (ofString "mpt_hash_scratch"), .rfield 3 (.var .local (ofString "balance"))]
        (by rw [hbe0])
      rwa [hbe0] at this
    have hs3_code : s3.code = originalRuntimeCode := heff_be0.code.trans hs2_code
    have hGs3 : GuestInv s3 := guestInv_congr heff_be0.code heff_be0.memaddrs heff_be0.shMemaddrs heff_be0.baseAddr hGs2
    have hs3_glob : s3.globals = s.globals := heff_be0.globals.trans hs2_glob
    rw [evaluateHOLFiniteState_seq_line780] at hnt1 hres1 ⊢
    rcases hbe1 : evaluateHOLFiniteState s3
        (.call (some (none, none)) (ofString "st_be64")
          [.op .add [.var .global (ofString "mpt_hash_scratch"), .const (8#64)],
           .rfield 2 (.var .local (ofString "balance"))]) with ⟨rbe1, s4⟩
    rw [hbe1] at hnt1 hres1
    cases rbe1 with
    | some _ => dsimp only at hres1; exact False.elim (call0_be64_not_resumes s3 _ _ hs3_code (by rw [hbe1]; exact hres1))
    | none =>
      dsimp only at hnt1 hres1 ⊢
      have hphs_s3 : s3.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word phs)) := by
        rw [hs3_glob]; exact hphs_g
      obtain ⟨_, heff_be1⟩ := st_be64_dom_of_none s3
        (.op .add [.var .global (ofString "mpt_hash_scratch"), .const (8#64)])
        (.rfield 2 (.var .local (ofString "balance")))
        (phs + 8#64) hs3_code hGs3
        (by simp [evalHOLExact, evalListHOLExact, PanSemStateFiniteExact.toExact, hphs_s3, wordOpHOL, wordOp, valueIsWord, valueWord])
        (by rw [hbe1])
      rw [hbe1] at heff_be1; dsimp only at heff_be1
      have hs4_loc : s4.locals = s2.locals := by
        have := call0_locals_r16 s3 (ofString "st_be64")
          [.op .add [.var .global (ofString "mpt_hash_scratch"), .const (8#64)],
           .rfield 2 (.var .local (ofString "balance"))] (by rw [hbe1])
        rw [hbe1] at this; exact this.trans hs3_loc
      have hs4_code : s4.code = originalRuntimeCode := heff_be1.code.trans hs3_code
      have hGs4 : GuestInv s4 := guestInv_congr heff_be1.code heff_be1.memaddrs heff_be1.shMemaddrs heff_be1.baseAddr hGs3
      have hs4_glob : s4.globals = s.globals := heff_be1.globals.trans hs3_glob
      rw [evaluateHOLFiniteState_seq_line780] at hnt1 hres1 ⊢
      rcases hbe2 : evaluateHOLFiniteState s4
          (.call (some (none, none)) (ofString "st_be64")
            [.op .add [.var .global (ofString "mpt_hash_scratch"), .const (16#64)],
             .rfield 1 (.var .local (ofString "balance"))]) with ⟨rbe2, s5⟩
      rw [hbe2] at hnt1 hres1
      cases rbe2 with
      | some _ => dsimp only at hres1; exact False.elim (call0_be64_not_resumes s4 _ _ hs4_code (by rw [hbe2]; exact hres1))
      | none =>
        dsimp only at hnt1 hres1 ⊢
        have hphs_s4 : s4.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word phs)) := by
          rw [hs4_glob]; exact hphs_g
        obtain ⟨_, heff_be2⟩ := st_be64_dom_of_none s4
          (.op .add [.var .global (ofString "mpt_hash_scratch"), .const (16#64)])
          (.rfield 1 (.var .local (ofString "balance")))
          (phs + 16#64) hs4_code hGs4
          (by simp [evalHOLExact, evalListHOLExact, PanSemStateFiniteExact.toExact, hphs_s4, wordOpHOL, wordOp, valueIsWord, valueWord])
          (by rw [hbe2])
        rw [hbe2] at heff_be2; dsimp only at heff_be2
        have hs5_loc : s5.locals = s2.locals := by
          have := call0_locals_r16 s4 (ofString "st_be64")
            [.op .add [.var .global (ofString "mpt_hash_scratch"), .const (16#64)],
             .rfield 1 (.var .local (ofString "balance"))] (by rw [hbe2])
          rw [hbe2] at this; exact this.trans hs4_loc
        have hs5_code : s5.code = originalRuntimeCode := heff_be2.code.trans hs4_code
        have hGs5 : GuestInv s5 := guestInv_congr heff_be2.code heff_be2.memaddrs heff_be2.shMemaddrs heff_be2.baseAddr hGs4
        have hs5_glob : s5.globals = s.globals := heff_be2.globals.trans hs4_glob
        rw [evaluateHOLFiniteState_seq_line780] at hnt1 hres1 ⊢
        rcases hbe3 : evaluateHOLFiniteState s5
            (.call (some (none, none)) (ofString "st_be64")
              [.op .add [.var .global (ofString "mpt_hash_scratch"), .const (24#64)],
               .rfield 0 (.var .local (ofString "balance"))]) with ⟨rbe3, s6⟩
        rw [hbe3] at hnt1 hres1
        cases rbe3 with
        | some _ => dsimp only at hres1; exact False.elim (call0_be64_not_resumes s5 _ _ hs5_code (by rw [hbe3]; exact hres1))
        | none =>
          dsimp only at hnt1 hres1 ⊢
          have hphs_s5 : s5.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word phs)) := by
            rw [hs5_glob]; exact hphs_g
          obtain ⟨_, heff_be3⟩ := st_be64_dom_of_none s5
            (.op .add [.var .global (ofString "mpt_hash_scratch"), .const (24#64)])
            (.rfield 0 (.var .local (ofString "balance")))
            (phs + 24#64) hs5_code hGs5
            (by simp [evalHOLExact, evalListHOLExact, PanSemStateFiniteExact.toExact, hphs_s5, wordOpHOL, wordOp, valueIsWord, valueWord])
            (by rw [hbe3])
          rw [hbe3] at heff_be3; dsimp only at heff_be3
          have hs6_loc : s6.locals = s2.locals := by
            have := call0_locals_r16 s5 (ofString "st_be64")
              [.op .add [.var .global (ofString "mpt_hash_scratch"), .const (24#64)],
               .rfield 0 (.var .local (ofString "balance"))] (by rw [hbe3])
            rw [hbe3] at this; exact this.trans hs5_loc
          have hs6_code : s6.code = originalRuntimeCode := heff_be3.code.trans hs5_code
          have hGs6 : GuestInv s6 := guestInv_congr heff_be3.code heff_be3.memaddrs heff_be3.shMemaddrs heff_be3.baseAddr hGs5
          have hphs8 : (phs + 8#64).toNat = phs.toNat + 8 := BitVec.toNat_add_of_lt (by change phs.toNat + 8 < 2 ^ 64; omega)
          have hphs16 : (phs + 16#64).toNat = phs.toNat + 16 := BitVec.toNat_add_of_lt (by change phs.toNat + 16 < 2 ^ 64; omega)
          have hphs24 : (phs + 24#64).toNat = phs.toNat + 24 := BitVec.toNat_add_of_lt (by change phs.toNat + 24 < 2 ^ 64; omega)
          have heff_be_all : ByteEff s2 s6 [(globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)] := by
            have h0 : ByteEff s2 s3 [(globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)] :=
              heff_be0.mono (fun iv hiv _ => by
                simp at hiv; subst hiv
                exact ⟨_, List.mem_singleton.2 rfl, by simp [hphs_nat, hphs_nz], by simp [hphs_nat, hphs_nz]⟩)
            have h1 : ByteEff s3 s4 [(globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)] :=
              heff_be1.mono (fun iv hiv _ => by
                simp [hphs8] at hiv; subst hiv
                exact ⟨_, List.mem_singleton.2 rfl, by simp [hphs_nat, hphs_nz], by simp [hphs_nat, hphs_nz]⟩)
            have h2 : ByteEff s4 s5 [(globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)] :=
              heff_be2.mono (fun iv hiv _ => by
                simp [hphs16] at hiv; subst hiv
                exact ⟨_, List.mem_singleton.2 rfl, by simp [hphs_nat, hphs_nz], by simp [hphs_nat, hphs_nz]⟩)
            have h3 : ByteEff s5 s6 [(globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)] :=
              heff_be3.mono (fun iv hiv _ => by
                simp [hphs24] at hiv; subst hiv
                exact ⟨_, List.mem_singleton.2 rfl, by simp [hphs_nat, hphs_nz], by simp [hphs_nat, hphs_nz]⟩)
            exact ((h0.trans h1).trans h2).trans h3
          rw [evaluateHOLFiniteState_dec_total] at hnt1 hres1 ⊢
          simp only [evalHOLExact, shapeEqHOL, shapeOfHOLExact, ↓reduceIte] at hnt1 hres1 ⊢
          set s7 := setVarHOLFinite (ofString "z") (.val (.word (0#64))) s6
          have hs7_z : s7.locals.lookup (ofString "z") = some (.val (.word (0#64))) := by
            simp [s7, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          rw [evaluateHOLFiniteState_seq_line780] at hnt1 hres1 ⊢
          dsimp only at hnt1 hres1 ⊢
          rcases hzl : evaluateHOLFiniteState s7 encodeAcctZeroLoopCsr1 with ⟨rzl, s8⟩
          have hzl' : evaluateHOLFiniteState s7
              (.while (.cmp .lower (.var .local (ofString "z")) (.const (32#64)))
                (.seq
                  (.ite (.cmp .notEqual
                      (.loadByte (.op .add [.var .global (ofString "mpt_hash_scratch"), .var .local (ofString "z")]))
                      (.const (0#64)))
                    .break .skip)
                  (.assign .local (ofString "z") (.op .add [.var .local (ofString "z"), .const (1#64)])))) =
              (rzl, s8) := hzl
          rw [hzl'] at hnt1 hres1 ⊢
          have hnt_zl : rzl ≠ some .timeOut := by rintro rfl; simp at hnt1
          have hzl_spec := eval_encodeAcctZeroLoopCsr1 s7.clock s7 (0#64) rfl hs7_z (by decide) (by rw [hzl]; exact hnt_zl)
          rw [hzl] at hzl_spec
          cases rzl with
          | some _ => dsimp only at hres1; exact False.elim (hzl_spec.2 (by simp) hres1)
          | none =>
            dsimp only at hnt1 hres1 hzl_spec ⊢
            obtain ⟨zw, hzw_le, hs8_loc, hs8_eq⟩ := hzl_spec.1 rfl
            have hs8_code : s8.code = originalRuntimeCode := by rw [hs8_eq]; exact hs6_code
            have hGs8 : GuestInv s8 := by
              rw [hs8_eq]; exact guestInv_with_locals_clock s7 _ _ (guestInv_setVar _ _ s6 hGs6)
            have hs8_z : s8.locals.lookup (ofString "z") = some (.val (.word zw)) := by
              rw [hs8_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
            have hs8_other : ∀ m, m ≠ ofString "z" → s8.locals.lookup m = s2.locals.lookup m := by
              intro m hm
              rw [hs8_loc]; simp [s7, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm, Ne.symm hm, hs6_loc]
            have hs8_out : s8.locals.lookup (ofString "out") = some (.val (.word out0)) := by
              rw [hs8_other _ (by decide)]
              simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "off" ≠ ofString "out" by decide, hs1_loc,
                show ofString "w" ≠ ofString "out" by decide,
                hs0_other (ofString "out") (by decide), hs_out]
            have hs8_off : s8.locals.lookup (ofString "off") = some (.val (.word off2)) := by
              rw [hs8_other _ (by decide)]
              simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have h32z_nat : ((32#64) - zw).toNat = 32 - zw.toNat := by
              rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hzw_le)]; rfl
            obtain ⟨wb, s9, hwb_lo, hwb_hi, _, heff_wb, hs9_loc, hnt9, hres9, hpost9⟩ :=
              eval_decCall_rlp_encode_bytes_bounded s8 "wb"
                (.op .add [.var .local (ofString "out"), .var .local (ofString "off")])
                (.op .add [.var .global (ofString "mpt_hash_scratch"), .var .local (ofString "z")])
                (.op .sub [.const (32#64), .var .local (ofString "z")])
                (out0 + off2) ((32#64) - zw) _
                [((out0 + off2).toNat, 33)] hs8_code hGs8
                (by simp [evalHOLExact, evalListHOLExact, hs8_out, hs8_off, wordOpHOL, wordOp, valueIsWord, valueWord])
                (by simp [evalHOLExact, evalListHOLExact, hs8_z, wordOpHOL, wordOp, valueIsWord, valueWord])
                (by omega)
                ⟨((out0 + off2).toNat, 33), List.mem_singleton.2 rfl, le_rfl, by rw [h32z_nat]; omega⟩
                hnt1 hres1
            have hwb_33 : wb.toNat ≤ 33 := by rw [h32z_nat] at hwb_hi; omega
            rw [hpost9]
            have hs9_code : s9.code = originalRuntimeCode := heff_wb.code.trans hs8_code
            have hGs9 : GuestInv s9 := guestInv_congr heff_wb.code heff_wb.memaddrs heff_wb.shMemaddrs heff_wb.baseAddr hGs8
            have hs9_off : s9.locals.lookup (ofString "off") = some (.val (.word off2)) := by
              rw [hs9_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs8_off, show ofString "wb" ≠ ofString "off" by decide]
            have hs9_wb : s9.locals.lookup (ofString "wb") = some (.val (.word wb)) := by
              rw [hs9_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
            rw [evaluateHOLFiniteState_seq_line780] at hnt9 hres9 ⊢
            have hasg_off2 : evaluateHOLFiniteState s9
                (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "wb")])) =
                (none, setVarHOLFinite (ofString "off") (.val (.word (off2 + wb))) s9) := by
              simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hs9_off, hs9_wb,
                wordOpHOL, wordOp, valueIsWord, valueWord, isValidValueHOLExact, lookupKvarHOLExact,
                shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]
            rw [hasg_off2] at hnt9 hres9 ⊢; dsimp only at hnt9 hres9 ⊢
            set off3 := off2 + wb
            have hoff3_nat : off3.toNat = off2.toNat + wb.toNat :=
              BitVec.toNat_add_of_lt (by change off2.toNat + wb.toNat < 2 ^ 64; omega)
            set s10 := setVarHOLFinite (ofString "off") (.val (.word off3)) s9
            have hs10_code : s10.code = originalRuntimeCode := hs9_code
            have hGs10 : GuestInv s10 := guestInv_setVar _ _ s9 hGs9
            have hs10_out : s10.locals.lookup (ofString "out") = some (.val (.word out0)) := by
              simp [s10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "off" ≠ ofString "out" by decide, hs9_loc,
                show ofString "wb" ≠ ofString "out" by decide, hs8_out]
            have hs10_off : s10.locals.lookup (ofString "off") = some (.val (.word off3)) := by
              simp [s10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have h32_lit : (32#64).toNat = 32 := rfl
            obtain ⟨wsl, s11, hwsl_lo, hwsl_hi, _, heff_wsl, hs11_loc, hnt11, hres11, hpost11⟩ :=
              eval_decCall_rlp_encode_bytes_bounded s10 "wsl"
                (.op .add [.var .local (ofString "out"), .var .local (ofString "off")])
                (.var .local (ofString "storage_root")) (.const (32#64))
                (out0 + off3) (32#64) _ [((out0 + off3).toNat, 33)] hs10_code hGs10
                (by simp [evalHOLExact, evalListHOLExact, hs10_out, hs10_off, wordOpHOL, wordOp, valueIsWord, valueWord])
                rfl (by decide)
                ⟨((out0 + off3).toNat, 33), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩
                hnt9 hres9
            have hwsl_33 : wsl.toNat ≤ 33 := by rw [h32_lit] at hwsl_hi; omega
            rw [hpost11]
            have hs11_code : s11.code = originalRuntimeCode := heff_wsl.code.trans hs10_code
            have hGs11 : GuestInv s11 := guestInv_congr heff_wsl.code heff_wsl.memaddrs heff_wsl.shMemaddrs heff_wsl.baseAddr hGs10
            have hs11_off : s11.locals.lookup (ofString "off") = some (.val (.word off3)) := by
              rw [hs11_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs10_off, show ofString "wsl" ≠ ofString "off" by decide]
            have hs11_wsl : s11.locals.lookup (ofString "wsl") = some (.val (.word wsl)) := by
              rw [hs11_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
            rw [evaluateHOLFiniteState_seq_line780] at hnt11 hres11 ⊢
            have hasg_off3 : evaluateHOLFiniteState s11
                (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "wsl")])) =
                (none, setVarHOLFinite (ofString "off") (.val (.word (off3 + wsl))) s11) := by
              simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hs11_off, hs11_wsl,
                wordOpHOL, wordOp, valueIsWord, valueWord, isValidValueHOLExact, lookupKvarHOLExact,
                shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]
            rw [hasg_off3] at hnt11 hres11 ⊢; dsimp only at hnt11 hres11 ⊢
            set off4 := off3 + wsl
            have hoff4_nat : off4.toNat = off3.toNat + wsl.toNat :=
              BitVec.toNat_add_of_lt (by change off3.toNat + wsl.toNat < 2 ^ 64; omega)
            set s12 := setVarHOLFinite (ofString "off") (.val (.word off4)) s11
            have hs12_code : s12.code = originalRuntimeCode := hs11_code
            have hGs12 : GuestInv s12 := guestInv_setVar _ _ s11 hGs11
            have hs12_out : s12.locals.lookup (ofString "out") = some (.val (.word out0)) := by
              simp [s12, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "off" ≠ ofString "out" by decide, hs11_loc,
                show ofString "wsl" ≠ ofString "out" by decide, hs10_out]
            have hs12_off : s12.locals.lookup (ofString "off") = some (.val (.word off4)) := by
              simp [s12, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            obtain ⟨wc, s13, hwc_lo, hwc_hi, _, heff_wc, hs13_loc, hnt13, hres13, hpost13⟩ :=
              eval_decCall_rlp_encode_bytes_bounded s12 "wc"
                (.op .add [.var .local (ofString "out"), .var .local (ofString "off")])
                (.var .local (ofString "code_hash")) (.const (32#64))
                (out0 + off4) (32#64) _ [((out0 + off4).toNat, 33)] hs12_code hGs12
                (by simp [evalHOLExact, evalListHOLExact, hs12_out, hs12_off, wordOpHOL, wordOp, valueIsWord, valueWord])
                rfl (by decide)
                ⟨((out0 + off4).toNat, 33), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩
                hnt11 hres11
            have hwc_33 : wc.toNat ≤ 33 := by rw [h32_lit] at hwc_hi; omega
            rw [hpost13]
            have hGs13 : GuestInv s13 := guestInv_congr heff_wc.code heff_wc.memaddrs heff_wc.shMemaddrs heff_wc.baseAddr hGs12
            have hs13_off : s13.locals.lookup (ofString "off") = some (.val (.word off4)) := by
              rw [hs13_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs12_off, show ofString "wc" ≠ ofString "off" by decide]
            have hs13_wc : s13.locals.lookup (ofString "wc") = some (.val (.word wc)) := by
              rw [hs13_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
            rw [evaluateHOLFiniteState_seq_line780] at hnt13 hres13 ⊢
            have hasg_off4 : evaluateHOLFiniteState s13
                (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "wc")])) =
                (none, setVarHOLFinite (ofString "off") (.val (.word (off4 + wc))) s13) := by
              simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hs13_off, hs13_wc,
                wordOpHOL, wordOp, valueIsWord, valueWord, isValidValueHOLExact, lookupKvarHOLExact,
                shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]
            rw [hasg_off4] at hnt13 hres13 ⊢; dsimp only at hnt13 hres13 ⊢
            set off5 := off4 + wc
            set s14 := setVarHOLFinite (ofString "off") (.val (.word off5)) s13
            have hGs14 : GuestInv s14 := guestInv_setVar _ _ s13 hGs13
            have hs14_out : s14.locals.lookup (ofString "out") = some (.val (.word out0)) := by
              simp [s14, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "off" ≠ ofString "out" by decide, hs13_loc,
                show ofString "wc" ≠ ofString "out" by decide, hs12_out]
            rw [evaluateHOLFiniteState_seq_line780] at hnt13 hres13 ⊢
            have hsb_248 := byteEff_storeByte hGs14 (.var .local (ofString "out")) (.const (248#64))
              (fun x hx _ => by
                simp [evalHOLExact, hs14_out] at hx; subst hx
                exact ⟨(out0.toNat, 2), List.mem_singleton.2 rfl, le_rfl, by omega⟩)
            have hcf_248 := evaluate_storeByte_control_frame s14 (.var .local (ofString "out")) (.const (248#64))
            rcases hst248 : evaluateHOLFiniteState s14 (.storeByte (.var .local (ofString "out")) (.const (248#64))) with ⟨r248, s15⟩
            rw [hst248] at hsb_248 hcf_248 hres13
            dsimp only at hsb_248 hcf_248 hres13 ⊢
            rcases hcf_248.1 with hr248 | hr248
            · subst hr248
              dsimp only at hres13 ⊢
              obtain ⟨x, hx, _, hout_hi⟩ := hsb_248.2 rfl
              simp [evalHOLExact, hs14_out] at hx; subst hx
              have hhe_val : heapEnd = 33806089704 := heapEnd_val
              have ho2 : (out0 + 2#64).toNat = out0.toNat + 2 :=
                BitVec.toNat_add_of_lt (by change out0.toNat + 2 < 2 ^ 64; omega)
              have ho_off2 : (out0 + off2).toNat = out0.toNat + off2.toNat :=
                BitVec.toNat_add_of_lt (by change out0.toNat + off2.toNat < 2 ^ 64; omega)
              have ho_off3 : (out0 + off3).toNat = out0.toNat + off3.toNat :=
                BitVec.toNat_add_of_lt (by change out0.toNat + off3.toNat < 2 ^ 64; omega)
              have ho_off4 : (out0 + off4).toNat = out0.toNat + off4.toNat :=
                BitVec.toNat_add_of_lt (by change out0.toNat + off4.toNat < 2 ^ 64; omega)
              have ho1 : (out0 + 1#64).toNat = out0.toNat + 1 :=
                BitVec.toNat_add_of_lt (by change out0.toNat + 1 < 2 ^ 64; omega)
              have hGs15 : GuestInv s15 := guestInv_congr hsb_248.1.code hsb_248.1.memaddrs hsb_248.1.shMemaddrs hsb_248.1.baseAddr hGs14
              have hs15_out : s15.locals.lookup (ofString "out") = some (.val (.word out0)) := by
                rw [hcf_248.2.2.1]; exact hs14_out
              rw [evaluateHOLFiniteState_seq_line780]
              have hsb_len := (byteEff_storeByte (Rl := Rl) hGs15
                (.op .add [.var .local (ofString "out"), .const (1#64)])
                (.op .sub [.var .local (ofString "off"), .const (2#64)])
                (fun x hx _ => by
                  simp [evalHOLExact, evalListHOLExact, hs15_out, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
                  subst hx
                  exact ⟨(locN s "out", 110), List.mem_cons_self,
                    by dsimp only; rw [hout_nat, ho1]; omega,
                    by dsimp only; rw [hout_nat, ho1]; omega⟩)).1
              rcases hst_len : evaluateHOLFiniteState s15
                  (.storeByte (.op .add [.var .local (ofString "out"), .const (1#64)])
                              (.op .sub [.var .local (ofString "off"), .const (2#64)])) with ⟨rlen, s16⟩
              rw [hst_len] at hsb_len; dsimp only at hsb_len ⊢
              have he1 : ByteEff s s1 Rl :=
                ((ByteEff.refl s Rl).locals_clock _ _).trans (heff1.mono (fun iv hiv _ => by
                  have ho2' : (out0 + (2 : BitVec 64)).toNat = out0.toNat + 2 := ho2
                  simp [ho2, ho2'] at hiv; subst hiv
                  exact ⟨(locN s "out", 110), List.mem_cons_self,
                    by dsimp only; rw [hout_nat]; omega,
                    by dsimp only; rw [hout_nat]; omega⟩))
              have he2 : ByteEff s1 s6 Rl :=
                ((ByteEff.refl s1 Rl).locals_clock _ _).trans (heff_be_all.mono (fun iv hiv _ => by
                  simp at hiv; subst hiv
                  exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, le_rfl, le_rfl⟩))
              have he3 : ByteEff s6 s8 Rl := by
                rw [hs8_eq]; exact (ByteEff.refl s6 Rl).locals_clock _ _
              have he4 : ByteEff s8 s10 Rl :=
                (heff_wb.mono (fun iv hiv _ => by
                  simp [ho_off2] at hiv; subst hiv
                  exact ⟨(locN s "out", 110), List.mem_cons_self,
                    by dsimp only; rw [hout_nat]; omega,
                    by dsimp only; rw [hout_nat]; omega⟩)).locals_clock _ _
              have he5 : ByteEff s10 s12 Rl :=
                (heff_wsl.mono (fun iv hiv _ => by
                  simp [ho_off3] at hiv; subst hiv
                  exact ⟨(locN s "out", 110), List.mem_cons_self,
                    by dsimp only; rw [hout_nat]; omega,
                    by dsimp only; rw [hout_nat]; omega⟩)).locals_clock _ _
              have he6 : ByteEff s12 s14 Rl :=
                (heff_wc.mono (fun iv hiv _ => by
                  simp [ho_off4] at hiv; subst hiv
                  exact ⟨(locN s "out", 110), List.mem_cons_self,
                    by dsimp only; rw [hout_nat]; omega,
                    by dsimp only; rw [hout_nat]; omega⟩)).locals_clock _ _
              have he7 : ByteEff s14 s15 Rl :=
                hsb_248.1.mono (fun iv hiv _ => by
                  simp at hiv; subst hiv
                  exact ⟨(locN s "out", 110), List.mem_cons_self,
                    by dsimp only; rw [hout_nat],
                    by dsimp only; rw [hout_nat]; omega⟩)
              have he_s_16 : ByteEff s s16 Rl :=
                ((((((he1.trans he2).trans he3).trans he4).trans he5).trans he6).trans he7).trans hsb_len
              cases rlen with
              | some _ =>
                exact (((((he_s_16.locals_clock _ _).locals_clock _ _).locals_clock _ _).locals_clock _ _).locals_clock _ _).locals_clock _ _
              | none =>
                dsimp only
                exact ((((((he_s_16.trans (byteEff_return s16 _ Rl)).locals_clock _ _).locals_clock _ _).locals_clock _ _).locals_clock _ _).locals_clock _ _).locals_clock _ _
            · subst hr248; exact False.elim (not_resumes_err_csr1 hres13)

-- 5. ws_storage_root_of on CsrTabs
theorem pBounded_ws_storage_root_of_csrTabs
    (tf_ws_sr : TerminatingFunBoundedOn GuestInv (ofString "ws_storage_root_of") K.«ws_storage_root_of»)
    (wk_ws_sr : WorldKeeps WorldOK
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "ws_storage_root_of"))
    {name : MlS} {args : List (ExpHOL 64)} {Bc : Nat} {cont : ProgHOL 64}
    (hne : ∀ n ∈ ["cache", "new_roots"], ofString n ≠ name)
    (hcont : PBounded CsrTabs cont Bc) :
    PBounded CsrTabs (.decCall name .one (ofString "ws_storage_root_of") args cont)
      (K.«ws_storage_root_of» + Bc + 1) := by
  refine pBounded_decCall_guestInv_csr localsOnly_csrTabs
    (fun s hs => (csrTabs_worldOK hs).1.1) tf_ws_sr wk_ws_sr
    (callEntryOn_worldOK_csr (fun _ hs => csrTabs_worldOK hs) _ args) hne ?_ hcont.1 hcont.2
  intro F s values body callee ret v post hc hs ha hl hb hq
  have hstep := hq (Or.inl ⟨v, rfl⟩)
  let bufs : List (String × Nat) := [("keccak_pad", 136), ("keccak_st", 200), ("mpt_nib_scratch", 64)]
  have hpost : CsrTablesAt post (locN s "cache") (locN s "new_roots") :=
    worldStep_buffers_csrTablesAt (buffers := bufs)
      (localsFree_csrTablesAt _ _ s callee _ hs) (by decide) hstep
  exact localsOnly_csrTabs { post with locals := s.locals } _ _
    (fun n hn => by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne n hn, Ne.symm (hne n hn)])
    (localsFree_csrTablesAt _ _ post s.locals post.clock hpost)

-- 6. mpt_from_witness: CsrTabs -> CsrMptBufs mname []
theorem pBounded_mpt_from_witness_csr
    (tf_mfw : TerminatingFunBoundedOn ArenaReady (ofString "mpt_from_witness") K.«mpt_from_witness»)
    (wk_mfw : WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetMptObj (ofString "mpt_from_witness"))
    (mname : String) {args : List (ExpHOL 64)} {Bc : Nat} {cont : ProgHOL 64}
    (hne : ∀ n ∈ ["cache", "new_roots"], ofString n ≠ ofString mname)
    (hcont : PBounded (CsrMptBufs mname []) cont Bc) :
    PBounded CsrTabs (.decCall (ofString mname) .one (ofString "mpt_from_witness") args cont)
      (K.«mpt_from_witness» + Bc + 1) := by
  have hentry_wok : CallEntryOn CsrTabs WorldOK (ofString "mpt_from_witness") args :=
    callEntryOn_worldOK_csr (fun _ hs => csrTabs_worldOK hs) _ args
  have hentry_ar : CallEntryOn CsrTabs ArenaReady (ofString "mpt_from_witness") args :=
    fun s _ _ _ _ _ hs _ _ => localsFree_arenaReady s _ _ (csrTabs_worldOK hs).1
  refine PBounded.decCallTrans tf_mfw localsOnly_csrTabs (ofString mname) hne .one args
    hentry_ar (funSpec_resumeOn_csr wk_mfw hentry_wok ?_) hcont.1
    ⟨fun s hc hR hnt hr => csrMpt_tabs mname (csrMptBufs_mpt mname [] (hcont.2.run s hc hR hnt hr))⟩
  intro F s values body callee ret v post hc hs ha hl hb hq
  have hstep := hq (Or.inl ⟨v, rfl⟩)
  obtain ⟨hA, hne_cr, S, Nd, hW, hcache_S, hroots_S, hcl, hrl⟩ :=
    localsFree_csrTablesAt _ _ s callee _ hs
  obtain ⟨S0', Nd', hW_both, hc', hr', hcl', hrl', hfp_c, hfp_r, _, _, hQ0, _, _⟩ :=
    worldStep_preserves_two_local_tables_csr hA hW hcache_S hroots_S hne_cr hcl hrl hstep
      (fun _ hj => False.elim (List.not_mem_nil hj))
      (fun _ hj => False.elim (List.not_mem_nil hj))
  obtain ⟨w, rfl, _, Nm, hm0, hd0, hfresh⟩ := hQ0 v rfl
  have hsep : heapLimit ≤ scratchStart := by decide
  have hm_c : MptObjInWith post (S0' ++ [locN s "cache"]) Nm w.toNat := by
    refine mptObjInWith_adjoin_local_csr hm0 (fun o ho i hi => ?_)
    rw [hfp_c] at hi
    have hal_i : Allocated (callEntryStateHOLFinite s callee) i :=
      ((hW.1.2.1 _ hcache_S).2 i hi).1
    rcases hfresh o ho with rfl | hin_o
    · exact Or.inl rfl
    · exact disj_allocated_fresh_heap hA.2 hstep.1.2 hal_i hin_o
  have hm_both : MptObjInWith post (S0' ++ [locN s "cache", locN s "new_roots"]) Nm w.toNat := by
    have hassoc : (S0' ++ [locN s "cache"]) ++ [locN s "new_roots"] =
        S0' ++ [locN s "cache", locN s "new_roots"] := by simp
    rw [← hassoc]
    refine mptObjInWith_adjoin_local_csr hm_c (fun o ho i hi => ?_)
    rw [hfp_r] at hi
    have hal_i : Allocated (callEntryStateHOLFinite s callee) i :=
      ((hW.1.2.1 _ hroots_S).2 i hi).1
    rcases hfresh o ho with rfl | hin_o
    · exact Or.inl rfl
    · exact disj_allocated_fresh_heap hA.2 hstep.1.2 hal_i hin_o
  have hlive_post : CsrLiveAt post (locN s "cache") (locN s "new_roots") w.toNat :=
    ⟨hstep.1, hne_cr, S0' ++ [locN s "cache", locN s "new_roots"], Nd', Nm,
     hW_both, hc', hr', hcl', hrl', hm_both, hd0⟩
  let mid := setVarHOLFinite (ofString mname) (.val (.word w)) { post with locals := s.locals }
  have hc_mid : locN mid "cache" = locN s "cache" := by
    simp [mid, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      hne "cache" (by simp), Ne.symm (hne "cache" (by simp))]
  have hr_mid : locN mid "new_roots" = locN s "new_roots" := by
    simp [mid, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      hne "new_roots" (by simp), Ne.symm (hne "new_roots" (by simp))]
  have hm_mid : locN mid mname = w.toNat := by
    simp [mid, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  show CsrMptBufs mname [] mid
  rw [csrMptBufs_nil_iff]
  unfold CsrMpt
  rw [hc_mid, hr_mid, hm_mid]
  exact localsFree_csrLiveAt _ _ _ post mid.locals mid.clock hlive_post

-- 7. alloc on CsrMptBufs (and CsrBound + CsrMptBufs)
theorem pBounded_alloc_csrMptBufs
    (tf_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (mname bname : String) (buffers : List (String × Nat)) (sz : BitVec 64)
    {Bc : Nat} {cont : ProgHOL 64}
    (hne : ∀ n ∈ ["cache", "new_roots", mname] ++ buffers.map Prod.fst,
      ofString n ≠ ofString bname)
    (hcont : PBounded (CsrMptBufs mname ((bname, (sz.toNat + 7) / 8 * 8) :: buffers)) cont Bc) :
    PBounded (CsrMptBufs mname buffers)
      (.decCall (ofString bname) .one (ofString "alloc") [.const sz] cont)
      (K.«alloc» + Bc + 1) := by
  refine PBounded.decCallTrans tf_alloc (localsOnly_csrMptBufs mname buffers)
    (ofString bname) hne .one [.const sz]
    (callEntryOn_guestInv_csr (fun s hs => (csrMptBufs_worldOK mname buffers hs).1.1) _ _)
    ?_ hcont.1
    ⟨fun s hc hR hnt hr => by
      have ht := hcont.2.run s hc hR hnt hr
      have hpw : ((locN (evaluateHOLFiniteState s cont).2 bname, (sz.toNat + 7) / 8 * 8) ::
          buffers.map fun b => (locN (evaluateHOLFiniteState s cont).2 b.1, b.2)).Pairwise Disj := by
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hpw0⟩ := ht
        exact hpw0
      exact csrLiveBufsAt_sub ht (fun b hb => List.mem_cons_of_mem _ hb) (List.Pairwise.tail hpw)⟩
  intro F s values body callee ret v post hc hs ha hl hb
  obtain ⟨v1, he1, hc1, hbody_eq⟩ := callee_param_one_exp_csr s (ofString "alloc")
    (ofString "n") .one (sourceFnBody Guest.Software.guestFn_alloc) .one
    (hc ▸ R13Shards.lookup_alloc_r13) (.const sz) values body callee ret ha hl
  subst hbody_eq
  have hv1 : v1 = .val (.word sz) := by
    simp [evalAt, evalHOLExact] at he1; exact he1.symm
  subst hv1
  let ent := callEntryStateHOLFinite s callee
  have hn_ent : locN ent "n" = sz.toNat := by
    unfold locN ent callEntryStateHOLFinite; dsimp only; rw [hc1]
  have hs_ent : CsrLiveBufsAt ent (locN s "cache") (locN s "new_roots") (locN s mname)
      (buffers.map fun b => (locN s b.1, b.2)) :=
    localsFree_csrLiveBufsAt _ _ _ _ s callee _ hs
  obtain ⟨p, hrv, hpost_live⟩ := alloc_csrLiveBufsAt hs_ent (by rw [hb]; exact Or.inl ⟨v, rfl⟩)
  rw [hb] at hrv hpost_live; rw [hn_ent] at hpost_live; dsimp only at hrv hpost_live
  have hv_eq : v = .val (.word p) := by injection hrv with hr'; injection hr'
  subst hv_eq
  let mid := setVarHOLFinite (ofString bname) (.val (.word p)) { post with locals := s.locals }
  have hc_mid : locN mid "cache" = locN s "cache" := by
    simp [mid, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      hne "cache" (by simp), Ne.symm (hne "cache" (by simp))]
  have hr_mid : locN mid "new_roots" = locN s "new_roots" := by
    simp [mid, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      hne "new_roots" (by simp), Ne.symm (hne "new_roots" (by simp))]
  have hm_mid : locN mid mname = locN s mname := by
    simp [mid, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      hne mname (by simp), Ne.symm (hne mname (by simp))]
  have hb_mid : locN mid bname = p.toNat := by
    simp [mid, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hbufs_mid : buffers.map (fun b => (locN mid b.1, b.2)) =
      buffers.map (fun b => (locN s b.1, b.2)) := by
    apply List.map_congr_left
    intro b hb_mem
    have hbn : ofString b.1 ≠ ofString bname :=
      hne b.1 (List.mem_append_right _ (List.mem_map.mpr ⟨b, hb_mem, rfl⟩))
    simp [mid, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hbn, Ne.symm hbn]
  show CsrMptBufs mname ((bname, (sz.toNat + 7) / 8 * 8) :: buffers) mid
  unfold CsrMptBufs
  simp only [List.map_cons, hc_mid, hr_mid, hm_mid, hb_mid, hbufs_mid]
  exact localsFree_csrLiveBufsAt _ _ _ _ post mid.locals mid.clock hpost_live

theorem pBounded_alloc_csrBound_csrMptBufs
    (tf_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (wname : String) (wbound : Nat)
    (mname bname : String) (buffers : List (String × Nat)) (sz : BitVec 64)
    {Bc : Nat} {cont : ProgHOL 64}
    (hne_w : ofString wname ≠ ofString bname)
    (hne : ∀ n ∈ ["cache", "new_roots", mname] ++ buffers.map Prod.fst,
      ofString n ≠ ofString bname)
    (hcont : PBounded (CsrBound wname wbound
      (CsrMptBufs mname ((bname, (sz.toNat + 7) / 8 * 8) :: buffers))) cont Bc) :
    PBounded (CsrBound wname wbound (CsrMptBufs mname buffers))
      (.decCall (ofString bname) .one (ofString "alloc") [.const sz] cont)
      (K.«alloc» + Bc + 1) := by
  have hne_all : ∀ n ∈ wname :: (["cache", "new_roots", mname] ++ buffers.map Prod.fst),
      ofString n ≠ ofString bname := by
    intro n hn
    rcases List.mem_cons.mp hn with rfl | hn'
    · exact hne_w
    · exact hne n hn'
  refine PBounded.decCallTrans tf_alloc
    (localsOnly_csrBound (localsOnly_csrMptBufs mname buffers) wname wbound)
    (ofString bname) hne_all .one [.const sz]
    (callEntryOn_guestInv_csr (fun s hs => (csrMptBufs_worldOK mname buffers hs.1).1.1) _ _)
    ?_ hcont.1
    ⟨fun s hc hR hnt hr => by
      obtain ⟨ht, hw⟩ := hcont.2.run s hc hR hnt hr
      have hpw : ((locN (evaluateHOLFiniteState s cont).2 bname, (sz.toNat + 7) / 8 * 8) ::
          buffers.map fun b => (locN (evaluateHOLFiniteState s cont).2 b.1, b.2)).Pairwise Disj := by
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hpw0⟩ := ht
        exact hpw0
      exact ⟨csrLiveBufsAt_sub ht (fun b hb => List.mem_cons_of_mem _ hb) (List.Pairwise.tail hpw), hw⟩⟩
  intro F s values body callee ret v post hc hs ha hl hb
  obtain ⟨v1, he1, hc1, hbody_eq⟩ := callee_param_one_exp_csr s (ofString "alloc")
    (ofString "n") .one (sourceFnBody Guest.Software.guestFn_alloc) .one
    (hc ▸ R13Shards.lookup_alloc_r13) (.const sz) values body callee ret ha hl
  subst hbody_eq
  have hv1 : v1 = .val (.word sz) := by
    simp [evalAt, evalHOLExact] at he1; exact he1.symm
  subst hv1
  let ent := callEntryStateHOLFinite s callee
  have hn_ent : locN ent "n" = sz.toNat := by
    unfold locN ent callEntryStateHOLFinite; dsimp only; rw [hc1]
  have hs_ent : CsrLiveBufsAt ent (locN s "cache") (locN s "new_roots") (locN s mname)
      (buffers.map fun b => (locN s b.1, b.2)) :=
    localsFree_csrLiveBufsAt _ _ _ _ s callee _ hs.1
  obtain ⟨p, hrv, hpost_live⟩ := alloc_csrLiveBufsAt hs_ent (by rw [hb]; exact Or.inl ⟨v, rfl⟩)
  rw [hb] at hrv hpost_live; rw [hn_ent] at hpost_live; dsimp only at hrv hpost_live
  have hv_eq : v = .val (.word p) := by injection hrv with hr'; injection hr'
  subst hv_eq
  let mid := setVarHOLFinite (ofString bname) (.val (.word p)) { post with locals := s.locals }
  show CsrBound wname wbound (CsrMptBufs mname ((bname, (sz.toNat + 7) / 8 * 8) :: buffers)) mid
  refine ⟨?_, ?_⟩
  · have hc_mid : locN mid "cache" = locN s "cache" := by
      simp [mid, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        hne "cache" (by simp), Ne.symm (hne "cache" (by simp))]
    have hr_mid : locN mid "new_roots" = locN s "new_roots" := by
      simp [mid, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        hne "new_roots" (by simp), Ne.symm (hne "new_roots" (by simp))]
    have hm_mid : locN mid mname = locN s mname := by
      simp [mid, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        hne mname (by simp), Ne.symm (hne mname (by simp))]
    have hb_mid : locN mid bname = p.toNat := by
      simp [mid, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hbufs_mid : buffers.map (fun b => (locN mid b.1, b.2)) =
        buffers.map (fun b => (locN s b.1, b.2)) := by
      apply List.map_congr_left
      intro b hb_mem
      have hbn : ofString b.1 ≠ ofString bname :=
        hne b.1 (List.mem_append_right _ (List.mem_map.mpr ⟨b, hb_mem, rfl⟩))
      simp [mid, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hbn, Ne.symm hbn]
    show CsrMptBufs mname ((bname, (sz.toNat + 7) / 8 * 8) :: buffers) mid
    unfold CsrMptBufs
    simp only [List.map_cons, hc_mid, hr_mid, hm_mid, hb_mid, hbufs_mid]
    exact localsFree_csrLiveBufsAt _ _ _ _ post mid.locals mid.clock hpost_live
  · show locN mid wname ≤ wbound
    have hw_mid : locN mid wname = locN s wname := by
      simp [mid, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne_w, Ne.symm hne_w]
    rw [hw_mid]; exact hs.2

theorem worldEff_of_p26ByteEff_csr {F : Type} {s cur next : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String} {Sub : List Ivl}
    (h : R16Shards.WorldEff s cur Rl B gw) (hb : ByteEff cur next Sub)
    (hsub : ∀ iv ∈ Sub, 0 < iv.2 →
      (∃ j ∈ Rl, j.1 ≤ iv.1 ∧ iv.1 + iv.2 ≤ j.1 + j.2) ∨
      (∃ gs ∈ B, (bufferRegion s gs).1 ≤ iv.1 ∧
        iv.1 + iv.2 ≤ (bufferRegion s gs).1 + (bufferRegion s gs).2) ∨
      (globN s "frame_mem_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ globN s "scratch_ptr") ∨
      (globN s "heap_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ heapLimit)) :
    R16Shards.WorldEff s next Rl B gw :=
  h.of_byteEff ⟨hb.code, hb.memaddrs, hb.shMemaddrs, hb.baseAddr, hb.be, hb.globals, hb.eshapes,
    hb.out_dom, hb.cell_frame, hb.byte_frame⟩ hsub

theorem callee_param_three_exp_body_csr {F : Type} (state : PanSemStateFiniteExact 64 F)
    (fname p1 p2 p3 : MlS) (s1 s2 s3 : ShapeHOL)
    (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname =
      some ([(p1, s1), (p2, s2), (p3, s3)], body, ret))
    (e1 e2 e3 : ExpHOL 64) (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [e1, e2, e3] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    ∃ v1 v2 v3,
      evalAt state e1 = some v1 ∧ evalAt state e2 = some v2 ∧ evalAt state e3 = some v3 ∧
      callee.lookup p1 = some v1 ∧ callee.lookup p2 = some v2 ∧ callee.lookup p3 = some v3 ∧
      body' = body := by
  obtain ⟨v1, v2, v3, he1, he2, he3, hc1, hc2, hc3⟩ :=
    P3MptSet.callee_param_three_exp state fname p1 p2 p3 s1 s2 s3 body ret hl
      e1 e2 e3 values body' callee ret' hargs hlook
  have hb := lookupCodeHOLFinite_installed_body state.code.lookup fname
    [(p1, s1), (p2, s2), (p3, s3)] body body' ret ret' values callee hl hlook
  exact ⟨v1, v2, v3, he1, he2, he3, hc1, hc2, hc3, hb⟩

theorem pBounded_call0_on_csr
    {P Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop}
    {fname : MlS} {args : List (ExpHOL 64)} {B : Nat}
    (hfb : TerminatingFunBoundedOn Pc fname B)
    (hspec : FunSpec Pc Qc fname)
    (hentry : CallEntryOn P Pc fname args)
    (hret : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F)
      (values : List (ValueHOL 64)) (body : ProgHOL 64)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
      (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      s.code = originalRuntimeCode → P s →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values →
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      Qc (callEntryStateHOLFinite s callee) (some (.returned v)) post →
      P { post with locals := s.locals }) :
    PBounded P (.call (some (none, none)) fname args) (B + 1) := by
  refine ⟨TerminatingProgBoundedOn.call_on hfb none args hentry, ?_⟩
  refine ⟨fun {F} s hc hs _ hr => ?_⟩
  rw [evaluateHOLFiniteState_call] at hr ⊢
  rcases ha : @evalListHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [PanSemStateFiniteExact.evalListHOLFinite, ha] at hr
  · simp only [PanSemStateFiniteExact.evalListHOLFinite, ha] at hr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body, callee, ret⟩
    · simp [hl] at hr
    · simp only [hl] at hr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hr
      · simp only [hz, ↓reduceIte] at hr ⊢
        have harg := hentry s vs body callee ret hc hs ha hl
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, post⟩
        simp only [hb] at hr ⊢
        cases res with
        | none => simp at hr
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hr ⊢
            split at hr
            · rename_i hsh
              rw [if_pos hsh]
              have hq := FunSpec.at_lookup hspec s hc vs body callee ret hl harg (by rw [hb]; simp)
              rw [hb] at hq
              exact hret s vs body callee ret v post hc hs ha hl hb hq
            · simp at hr
          | _ => simp at hr

private theorem csr_wsBufs_ok :
    ∀ gs ∈ R16Shards.wsBufs, gs ∈ globalBuffers ∧ gs.1 ∉ typedRecords.map Prod.fst := by
  decide

private theorem csr_ws_core_out :
    ∀ g ∈ coreWorldGlobals, ofString g ∉ R16Shards.wsGw.map ofString := by
  decide

private theorem csr_eaBufs_ok :
    ∀ gs ∈ ([("mpt_hash_scratch", 40)] : List (String × Nat)),
      gs ∈ globalBuffers ∧ gs.1 ∉ typedRecords.map Prod.fst := by
  decide

private theorem csr_empty_core_out :
    ∀ g ∈ coreWorldGlobals, ofString g ∉ ([] : List String).map ofString := by
  decide

private theorem csr_mptRootBufs_ok :
    ∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
      gs ∈ globalBuffers ∧ gs.1 ∉ typedRecords.map Prod.fst := by
  decide

private theorem csr_mptSetBufs_ok :
    ∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200), ("mpt_hash_scratch", 40)] : List (String × Nat)),
      gs ∈ globalBuffers ∧ gs.1 ∉ typedRecords.map Prod.fst := by
  decide

theorem pBounded_alloc_csrBound_csrNonNeg_csrMptBufs
    (tf_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (wname : String) (wbound : Nat) (pname : String)
    (mname bname : String) (buffers : List (String × Nat)) (sz : BitVec 64)
    {Bc : Nat} {cont : ProgHOL 64}
    (hne_w : ofString wname ≠ ofString bname)
    (hne_p : ofString pname ≠ ofString bname)
    (hne : ∀ n ∈ ["cache", "new_roots", mname] ++ buffers.map Prod.fst,
      ofString n ≠ ofString bname)
    (hcont : PBounded (CsrBound wname wbound (CsrNonNeg pname
      (CsrMptBufs mname ((bname, (sz.toNat + 7) / 8 * 8) :: buffers)))) cont Bc) :
    PBounded (CsrBound wname wbound (CsrNonNeg pname (CsrMptBufs mname buffers)))
      (.decCall (ofString bname) .one (ofString "alloc") [.const sz] cont)
      (K.«alloc» + Bc + 1) := by
  have hne_all : ∀ n ∈ wname :: pname :: (["cache", "new_roots", mname] ++ buffers.map Prod.fst),
      ofString n ≠ ofString bname := by
    intro n hn
    rcases List.mem_cons.mp hn with rfl | hn1
    · exact hne_w
    · rcases List.mem_cons.mp hn1 with rfl | hn2
      · exact hne_p
      · exact hne n hn2
  refine PBounded.decCallTrans tf_alloc
    (localsOnly_csrBound (localsOnly_csrNonNeg (localsOnly_csrMptBufs mname buffers) pname) wname wbound)
    (ofString bname) hne_all .one [.const sz]
    (callEntryOn_guestInv_csr (fun s hs => (csrMptBufs_worldOK mname buffers hs.1.1).1.1) _ _)
    ?_ hcont.1
    ⟨fun s hc hR hnt hr => by
      obtain ⟨⟨ht, hp_nn⟩, hw⟩ := hcont.2.run s hc hR hnt hr
      have hpw : ((locN (evaluateHOLFiniteState s cont).2 bname, (sz.toNat + 7) / 8 * 8) ::
          buffers.map fun b => (locN (evaluateHOLFiniteState s cont).2 b.1, b.2)).Pairwise Disj := by
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hpw0⟩ := ht
        exact hpw0
      exact ⟨⟨csrLiveBufsAt_sub ht (fun b hb => List.mem_cons_of_mem _ hb) (List.Pairwise.tail hpw), hp_nn⟩, hw⟩⟩
  intro F s values body callee ret v post hc hs ha hl hb
  obtain ⟨v1, he1, hc1, hbody_eq⟩ := callee_param_one_exp_csr s (ofString "alloc")
    (ofString "n") .one (sourceFnBody Guest.Software.guestFn_alloc) .one
    (hc ▸ R13Shards.lookup_alloc_r13) (.const sz) values body callee ret ha hl
  subst hbody_eq
  have hv1 : v1 = .val (.word sz) := by
    simp [evalAt, evalHOLExact] at he1; exact he1.symm
  subst hv1
  let ent := callEntryStateHOLFinite s callee
  have hn_ent : locN ent "n" = sz.toNat := by
    unfold locN ent callEntryStateHOLFinite; dsimp only; rw [hc1]
  have hs_ent : CsrLiveBufsAt ent (locN s "cache") (locN s "new_roots") (locN s mname)
      (buffers.map fun b => (locN s b.1, b.2)) :=
    localsFree_csrLiveBufsAt _ _ _ _ s callee _ hs.1.1
  obtain ⟨p, hrv, hpost_live⟩ := alloc_csrLiveBufsAt hs_ent (by rw [hb]; exact Or.inl ⟨v, rfl⟩)
  rw [hb] at hrv hpost_live; rw [hn_ent] at hpost_live; dsimp only at hrv hpost_live
  have hv_eq : v = .val (.word p) := by injection hrv with hr'; injection hr'
  subst hv_eq
  let mid := setVarHOLFinite (ofString bname) (.val (.word p)) { post with locals := s.locals }
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hc_mid : locN mid "cache" = locN s "cache" := by
      simp [mid, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        hne "cache" (by simp), Ne.symm (hne "cache" (by simp))]
    have hr_mid : locN mid "new_roots" = locN s "new_roots" := by
      simp [mid, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        hne "new_roots" (by simp), Ne.symm (hne "new_roots" (by simp))]
    have hm_mid : locN mid mname = locN s mname := by
      simp [mid, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        hne mname (by simp), Ne.symm (hne mname (by simp))]
    have hb_mid : locN mid bname = p.toNat := by
      simp [mid, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hbufs_mid : buffers.map (fun b => (locN mid b.1, b.2)) =
        buffers.map (fun b => (locN s b.1, b.2)) := by
      apply List.map_congr_left
      intro b hb_mem
      have hbn : ofString b.1 ≠ ofString bname :=
        hne b.1 (List.mem_append_right _ (List.mem_map.mpr ⟨b, hb_mem, rfl⟩))
      simp [mid, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hbn, Ne.symm hbn]
    show CsrMptBufs mname ((bname, (sz.toNat + 7) / 8 * 8) :: buffers) mid
    unfold CsrMptBufs
    simp only [List.map_cons, hc_mid, hr_mid, hm_mid, hb_mid, hbufs_mid]
    exact localsFree_csrLiveBufsAt _ _ _ _ post mid.locals mid.clock hpost_live
  · obtain ⟨wp, hwp, hwp0⟩ := hs.1.2
    refine ⟨wp, ?_, hwp0⟩
    simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne_p, Ne.symm hne_p, hwp]
  · have hw_mid : locN mid wname = locN s wname := by
      simp [mid, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne_w, Ne.symm hne_w]
    rw [hw_mid]; exact hs.2

theorem pBounded_u256_to_be_min_csr
    (tf_utbm : TerminatingFunBoundedOn GuestInv (ofString "u256_to_be_min") K.«u256_to_be_min»)
    (rv_utbm : RetLe (fun _ => 32) (ofString "u256_to_be_min"))
    (ev : ExpHOL 64) {Bc : Nat} {cont : ProgHOL 64}
    (hcont : PBounded (CsrBound "n" 32 (CsrNonNeg "pass" (CsrMptBufs "mpt" [("vbuf", 96)]))) cont Bc) :
    PBounded (CsrNonNeg "pass" (CsrMptBufs "mpt" [("vbuf", 96)]))
      (.decCall (ofString "n") .one (ofString "u256_to_be_min")
        [ev, .op .add [.var .local (ofString "vbuf"), .const (8#64)]] cont)
      (K.«u256_to_be_min» + Bc + 1) := by
  have hne : ∀ n ∈ "pass" :: (["cache", "new_roots", "mpt"] ++ ([("vbuf", 96)] : List (String × Nat)).map Prod.fst),
      ofString n ≠ ofString "n" := by decide
  refine pBounded_specDecCall_csr
    (localsOnly_csrNonNeg (localsOnly_csrMptBufs "mpt" [("vbuf", 96)]) "pass")
    tf_utbm rv_utbm
    (callEntryOn_guestInv_csr (fun s hs => (csrMptBufs_worldOK "mpt" [("vbuf", 96)] hs.1).1.1) _ _)
    hne ?_ hcont.1 ⟨fun s hc hR hnt hr => (hcont.2.run s hc hR hnt hr).1⟩
  intro F s values body callee ret v post hc hs ha hl hb hq
  obtain ⟨w, rfl, hw_le⟩ := hq v rfl
  obtain ⟨_, v2, _, he2, _, hc2, hbody_eq⟩ := callee_param_two_exp_csr s (ofString "u256_to_be_min")
    (ofString "a") (ofString "out") (.comb [.one, .one, .one, .one]) .one
    (sourceFnBody Guest.Software.guestFn_u256_to_be_min) .one
    (hc ▸ lookup_u256_to_be_min_csr)
    ev (.op .add [.var .local (ofString "vbuf"), .const (8#64)]) values body callee ret ha hl
  subst hbody_eq
  have hvbuf_ex : ∃ vb : BitVec 64, s.locals.lookup (ofString "vbuf") = some (.val (.word vb)) ∧
      v2 = .val (.word (vb + 8#64)) := by
    simp only [evalAt, evalHOLExact, evalListHOLExact] at he2
    rcases hlk : s.locals.lookup (ofString "vbuf") with _ | vv
    · simp [hlk] at he2
    · rcases vv with ⟨⟨vb⟩⟩ | _ | _
      · simp [hlk, valueIsWord, valueWord, wordOpHOL, wordOp] at he2
        exact ⟨vb, rfl, he2.symm⟩
      · simp [hlk, valueIsWord] at he2
      · simp [hlk, valueIsWord] at he2
  obtain ⟨vb, hvb_lk, rfl⟩ := hvbuf_ex
  let ent := callEntryStateHOLFinite s callee
  have hout_ent : locN ent "out" = (vb + 8#64).toNat := by
    unfold locN ent callEntryStateHOLFinite; dsimp only; rw [hc2]
  have hs_live : CsrLiveBufsAt s (locN s "cache") (locN s "new_roots") (locN s "mpt") [(locN s "vbuf", 96)] := hs.1
  have hvb_nat : locN s "vbuf" = vb.toNat := by simp [locN, hvb_lk]
  have hvb_hi : vb.toNat + 96 ≤ heapLimit := by
    obtain ⟨hA, _, _, _, _, _, _, _, _, _, _, _, hbs, _⟩ := hs_live
    have hb_in := (hbs (locN s "vbuf", 96) (by simp)).1
    have hhp_hi := hA.2.2.1
    rw [hvb_nat] at hb_in
    exact Nat.le_trans hb_in.2 hhp_hi
  have h264 : heapLimit < 2 ^ 64 := by rw [heapLimit_val]; decide
  have hout_add : (vb + 8#64).toNat = vb.toNat + 8 := by
    apply BitVec.toNat_add_of_lt
    change vb.toNat + 8 < 2 ^ 64
    omega
  have hs_ent : CsrLiveBufsAt ent (locN s "cache") (locN s "new_roots") (locN s "mpt") [(locN s "vbuf", 96)] :=
    localsFree_csrLiveBufsAt _ _ _ _ s callee _ hs_live
  have hbf := byteFrame_u256_to_be_min_body_csr ent hc hs_ent.1.1.memaddrs
  rw [hb] at hbf
  have heff := worldEff_of_byteFrame_csr hs_ent.1 hc
    (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact Nat.zero_lt_succ 31) hbf
  have hpost_live : CsrLiveBufsAt post (locN s "cache") (locN s "new_roots") (locN s "mpt") [(locN s "vbuf", 96)] :=
    worldEff_csrLiveBufsAt hs_ent (by decide) csr_empty_core_out heff (fun iv hiv _ => by
      obtain rfl := List.mem_singleton.mp hiv
      refine ⟨(locN s "vbuf", 96), by simp, ?_⟩
      unfold Inside; dsimp only
      rw [hout_ent, hout_add, hvb_nat]
      omega)
  let mid := setVarHOLFinite (ofString "n") (.val (.word w)) { post with locals := s.locals }
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hc_mid : locN mid "cache" = locN s "cache" := locN_setVar_ne _ "cache" (ofString "n") _ (by decide)
    have hr_mid : locN mid "new_roots" = locN s "new_roots" := locN_setVar_ne _ "new_roots" (ofString "n") _ (by decide)
    have hm_mid : locN mid "mpt" = locN s "mpt" := locN_setVar_ne _ "mpt" (ofString "n") _ (by decide)
    have hv_mid : locN mid "vbuf" = locN s "vbuf" := locN_setVar_ne _ "vbuf" (ofString "n") _ (by decide)
    show CsrMptBufs "mpt" [("vbuf", 96)] mid
    unfold CsrMptBufs
    simp only [List.map_cons, List.map_nil, hc_mid, hr_mid, hm_mid, hv_mid]
    exact localsFree_csrLiveBufsAt _ _ _ _ post mid.locals mid.clock hpost_live
  · obtain ⟨wp, hwp, hwp0⟩ := hs.2
    refine ⟨wp, ?_, hwp0⟩
    simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hwp,
      show ofString "pass" ≠ ofString "n" by decide, show ofString "n" ≠ ofString "pass" by decide]
  · show locN mid "n" ≤ 32
    rw [locN_setVar_same]
    exact hw_le

theorem pBounded_rlp_encode_bytes_csr
    (tf_reb : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_bytes") K.«rlp_encode_bytes»)
    {Bc : Nat} {cont : ProgHOL 64}
    (hcont : PBounded (CsrBound "w" 33 (CsrNonNeg "pass" (CsrMptBufs "mpt" [("vbuf", 96)]))) cont Bc)
    (hpres_n : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s cont).1 = none →
      (evaluateHOLFiniteState s cont).2.locals.lookup (ofString "n") = s.locals.lookup (ofString "n")) :
    PBounded (CsrBound "n" 32 (CsrNonNeg "pass" (CsrMptBufs "mpt" [("vbuf", 96)])))
      (.decCall (ofString "w") .one (ofString "rlp_encode_bytes")
        [.op .add [.op .add [.var .local (ofString "vbuf"), .const (8#64)], .const (32#64)],
         .op .add [.var .local (ofString "vbuf"), .const (8#64)],
         .var .local (ofString "n")] cont)
      (K.«rlp_encode_bytes» + Bc + 1) := by
  have hne : ∀ nm ∈ "n" :: "pass" :: (["cache", "new_roots", "mpt"] ++ ([("vbuf", 96)] : List (String × Nat)).map Prod.fst),
      ofString nm ≠ ofString "w" := by decide
  refine PBounded.decCallTrans (R := CsrBound "n" 32 (CsrBound "w" 33 (CsrNonNeg "pass" (CsrMptBufs "mpt" [("vbuf", 96)]))))
    tf_reb
    (localsOnly_csrBound (localsOnly_csrNonNeg (localsOnly_csrMptBufs "mpt" [("vbuf", 96)]) "pass") "n" 32)
    (ofString "w") hne .one _
    (callEntryOn_guestInv_csr (fun s hs => (csrMptBufs_worldOK "mpt" [("vbuf", 96)] hs.1.1).1.1) _ _)
    ?_ (fun s hc hR => hcont.1 s hc hR.1)
    ⟨fun s hc hR hnt hr => by
      have hpost := (hcont.2.run s hc hR.1 hnt hr).1
      have hn_eq : locN (evaluateHOLFiniteState s cont).2 "n" = locN s "n" := by
        unfold locN; rw [hpres_n s hr]
      exact ⟨hpost, hn_eq ▸ hR.2⟩⟩
  intro F s values body callee ret v post hc hs ha hl hb
  obtain ⟨v1, v2, v3, he1, he2, he3, hc1, hc2, hc3, hbody_eq⟩ :=
    callee_param_three_exp_body_csr s (ofString "rlp_encode_bytes")
      (ofString "dst") (ofString "src") (ofString "n") .one .one .one
      (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes) .one
      (hc ▸ R16Rlp.lookup_rlp_encode_bytes)
      (.op .add [.op .add [.var .local (ofString "vbuf"), .const (8#64)], .const (32#64)])
      (.op .add [.var .local (ofString "vbuf"), .const (8#64)])
      (.var .local (ofString "n")) values body callee ret ha hl
  subst hbody_eq
  have hvbuf_ex : ∃ vb : BitVec 64, s.locals.lookup (ofString "vbuf") = some (.val (.word vb)) ∧
      v1 = .val (.word ((vb + 8#64) + 32#64)) ∧ v2 = .val (.word (vb + 8#64)) := by
    simp only [evalAt, evalHOLExact, evalListHOLExact] at he1 he2
    rcases hlk : s.locals.lookup (ofString "vbuf") with _ | vv
    · simp [hlk] at he2
    · rcases vv with ⟨⟨vb⟩⟩ | _ | _
      · simp [hlk, valueIsWord, valueWord, wordOpHOL, wordOp] at he1 he2
        exact ⟨vb, rfl, he1.symm, he2.symm⟩
      · simp [hlk, valueIsWord] at he2
      · simp [hlk, valueIsWord] at he2
  obtain ⟨vb, hvb_lk, rfl, rfl⟩ := hvbuf_ex
  have hn_ex : ∃ n0 : BitVec 64, s.locals.lookup (ofString "n") = some (.val (.word n0)) ∧
      v3 = .val (.word n0) := by
    have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_encode_bytes") values =
        some (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes, callee, ret) := hc ▸ hl
    have hret_eq : ret = .one :=
      lookupCodeHOLFinite_installed_return s (ofString "rlp_encode_bytes")
        _ _ _ _ ret values callee (hc ▸ R16Rlp.lookup_rlp_encode_bytes) hl
    subst hret_eq
    obtain ⟨_, _, n0, hvs, _, _, _⟩ := lookupCode_three_words
      (by decide) (by decide) (by decide) R16Rlp.lookup_rlp_encode_bytes hl_orig
    have hv3_eq : v3 = .val (.word n0) := by
      rw [evalListHOLFinite_eq_toExact] at ha
      simp only [evalListHOLExact] at ha
      simp only [evalAt] at he1 he2 he3
      rw [he1, he2, he3] at ha
      injection ha with hvs'
      rw [← hvs'] at hvs
      injection hvs with _ htl1; injection htl1 with _ htl2; injection htl2 with hv3 _
    subst hv3_eq
    simp only [evalAt, evalHOLExact] at he3
    exact ⟨n0, he3, rfl⟩
  obtain ⟨n0, hn_lk, rfl⟩ := hn_ex
  have hn0_le : n0.toNat ≤ 32 := by
    have hln : locN s "n" = n0.toNat := by simp [locN, hn_lk]
    have := hs.2; omega
  let ent := callEntryStateHOLFinite s callee
  have hs_live : CsrLiveBufsAt s (locN s "cache") (locN s "new_roots") (locN s "mpt") [(locN s "vbuf", 96)] := hs.1.1
  have hvb_nat : locN s "vbuf" = vb.toNat := by simp [locN, hvb_lk]
  have hvb_hi : vb.toNat + 96 ≤ heapLimit := by
    obtain ⟨hA, _, _, _, _, _, _, _, _, _, _, _, hbs, _⟩ := hs_live
    have hb_in := (hbs (locN s "vbuf", 96) (by simp)).1
    rw [hvb_nat] at hb_in
    exact Nat.le_trans hb_in.2 hA.2.2.1
  have h264 : heapLimit < 2 ^ 64 := by rw [heapLimit_val]; decide
  have hdst_nat : ((vb + 8#64) + 32#64).toNat = vb.toNat + 40 := by
    have h1 : (vb + 8#64).toNat = vb.toNat + 8 :=
      BitVec.toNat_add_of_lt (by change vb.toNat + 8 < 2 ^ 64; omega)
    have h2 : ((vb + 8#64) + 32#64).toNat = (vb + 8#64).toNat + 32 :=
      BitVec.toNat_add_of_lt (by rw [h1]; change (vb.toNat + 8) + 32 < 2 ^ 64; omega)
    omega
  have hs_ent : CsrLiveBufsAt ent (locN s "cache") (locN s "new_roots") (locN s "mpt") [(locN s "vbuf", 96)] :=
    localsFree_csrLiveBufsAt _ _ _ _ s callee _ hs_live
  obtain ⟨r, hrb, _, hr_hi, _, heff_b⟩ := R16Rlp.eval_rlp_encode_bytes_bounded ent
    ((vb + 8#64) + 32#64) (vb + 8#64) n0 [(locN s "vbuf", 96)]
    hc hs_ent.1.1
    (by unfold ent callEntryStateHOLFinite; dsimp only; exact hc1)
    (by unfold ent callEntryStateHOLFinite; dsimp only; exact hc2)
    (by unfold ent callEntryStateHOLFinite; dsimp only; exact hc3)
    (by omega)
    ⟨(locN s "vbuf", 96), by simp, by rw [hdst_nat, hvb_nat]; omega, by rw [hdst_nat, hvb_nat]; omega⟩
    (by rw [hb]; simp)
    (by rw [hb]; exact Or.inl ⟨v, rfl⟩)
  rw [hb] at hrb heff_b; dsimp only at hrb heff_b
  have hv_eq : v = .val (.word r) := by injection hrb with hr'; injection hr'
  subst hv_eq
  have heff_w : R16Shards.WorldEff ent post [(locN s "vbuf", 96)] [] [] :=
    worldEff_of_p26ByteEff_csr (R16Shards.WorldEff.refl ent [(locN s "vbuf", 96)] [] [] hs_ent.1 hc) heff_b
      (fun iv hiv _ => Or.inl ⟨iv, hiv, le_rfl, le_rfl⟩)
  have hpost_live : CsrLiveBufsAt post (locN s "cache") (locN s "new_roots") (locN s "mpt") [(locN s "vbuf", 96)] :=
    worldEff_csrLiveBufsAt hs_ent (by decide) csr_empty_core_out heff_w
      (fun iv hiv _ => ⟨iv, hiv, le_rfl, le_rfl⟩)
  let mid := setVarHOLFinite (ofString "w") (.val (.word r)) { post with locals := s.locals }
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · have hc_mid : locN mid "cache" = locN s "cache" := locN_setVar_ne _ "cache" (ofString "w") _ (by decide)
    have hr_mid : locN mid "new_roots" = locN s "new_roots" := locN_setVar_ne _ "new_roots" (ofString "w") _ (by decide)
    have hm_mid : locN mid "mpt" = locN s "mpt" := locN_setVar_ne _ "mpt" (ofString "w") _ (by decide)
    have hv_mid : locN mid "vbuf" = locN s "vbuf" := locN_setVar_ne _ "vbuf" (ofString "w") _ (by decide)
    show CsrMptBufs "mpt" [("vbuf", 96)] mid
    unfold CsrMptBufs
    simp only [List.map_cons, List.map_nil, hc_mid, hr_mid, hm_mid, hv_mid]
    exact localsFree_csrLiveBufsAt _ _ _ _ post mid.locals mid.clock hpost_live
  · obtain ⟨wp, hwp, hwp0⟩ := hs.1.2
    refine ⟨wp, ?_, hwp0⟩
    simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hwp,
      show ofString "pass" ≠ ofString "w" by decide, show ofString "w" ≠ ofString "pass" by decide]
  · show locN mid "w" ≤ 33
    rw [locN_setVar_same]; omega
  · show locN mid "n" ≤ 32
    rw [locN_setVar_ne _ "n" (ofString "w") _ (by decide)]; exact hs.2

theorem pBounded_memcpy_csr
    (tf_mc : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»)
    (esrc : ExpHOL 64) :
    PBounded (CsrBound "w" 33 (CsrNonNeg "pass" (CsrMptBufs "mpt" [("enc", 40), ("vbuf", 96)])))
      (.call (some (none, none)) (ofString "memcpy")
        [.var .local (ofString "enc"), esrc, .var .local (ofString "w")])
      (K.«memcpy» + 1) := by
  let P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
    CsrBound "w" 33 (CsrNonNeg "pass" (CsrMptBufs "mpt" [("enc", 40), ("vbuf", 96)]))
  refine ⟨TerminatingProgBoundedOn.call_on tf_mc none _
    (callEntryOn_guestInv_csr (fun s (hs : P s) => (csrMptBufs_worldOK "mpt" [("enc", 40), ("vbuf", 96)] hs.1.1).1.1) _ _), ?_⟩
  refine ⟨fun {F} s hc hs _ hr => ?_⟩
  have hbe_call := call0_byteEff funByteEff_memcpy s
    [.var .local (ofString "enc"), esrc, .var .local (ofString "w")]
    [(locN s "enc", 40)]
    hc (csrMptBufs_worldOK "mpt" [("enc", 40), ("vbuf", 96)] hs.1.1).1.1
    (by
      intro vals hvals i hi hpos
      rw [evalListHOLFinite_eq_toExact] at hvals
      simp only [evalListHOLExact] at hvals
      rcases he1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.var .local (ofString "enc")) with _ | v1 <;>
      rcases he2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          esrc with _ | v2 <;>
      rcases he3 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.var .local (ofString "w")) with _ | v3 <;>
        simp only [he1, he2, he3, Option.some.injEq] at hvals <;>
        cases hvals
      obtain rfl := List.mem_singleton.mp hi
      dsimp only at hpos ⊢
      have henc_val : valWordNat v1 = locN s "enc" := by
        simp only [evalHOLExact] at he1
        unfold locN
        rcases hlk : s.locals.lookup (ofString "enc") with _ | vv
        · simp [hlk] at he1
        · simp only [hlk, Option.some.injEq] at he1; subst he1
          rcases vv with ⟨⟨w⟩⟩ | _ | _ <;> rfl
      have hw_val : valWordNat v3 = locN s "w" := by
        simp only [evalHOLExact] at he3
        unfold locN
        rcases hlk : s.locals.lookup (ofString "w") with _ | vv
        · simp [hlk] at he3
        · simp only [hlk, Option.some.injEq] at he3; subst he3
          rcases vv with ⟨⟨w⟩⟩ | _ | _ <;> rfl
      refine ⟨(locN s "enc", 40), by simp, ?_, ?_⟩
      · simp only [List.getElem?_cons_zero, Option.getD_some]; rw [henc_val]
      · simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
        rw [henc_val, hw_val]; have := hs.2; omega)
    (by rw [hr]; simp) (Or.inl hr)
  have hloc_eq : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy")
        [.var .local (ofString "enc"), esrc, .var .local (ofString "w")])).2.locals = s.locals := by
    rw [evaluateHOLFiniteState_call] at hr ⊢
    rcases ha : @evalListHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a))
        [.var .local (ofString "enc"), esrc, .var .local (ofString "w")] with _ | vs
    · simp [PanSemStateFiniteExact.evalListHOLFinite, ha] at hr
    · simp only [PanSemStateFiniteExact.evalListHOLFinite, ha] at hr ⊢
      rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs with _ | ⟨body, callee, ret⟩
      · simp [hl] at hr
      · simp only [hl] at hr ⊢
        by_cases hz : s.clock = 0
        · simp [hz] at hr
        · simp only [hz, ↓reduceIte] at hr ⊢
          rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, post⟩
          simp only [hb] at hr ⊢
          cases res with
          | none => simp at hr
          | some r =>
            cases r with
            | returned v =>
              dsimp only at hr ⊢
              split at hr
              · rename_i hsh; rw [if_pos hsh]
              · simp at hr
            | _ => simp at hr
  have hloc_lk : ∀ k : MlS, (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy")
        [.var .local (ofString "enc"), esrc, .var .local (ofString "w")])).2.locals.lookup k =
      s.locals.lookup k := by
    intro k; rw [hloc_eq]
  have hs_live : CsrLiveBufsAt s (locN s "cache") (locN s "new_roots") (locN s "mpt")
      [(locN s "enc", 40), (locN s "vbuf", 96)] := hs.1.1
  have heff_w : R16Shards.WorldEff s
      (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "memcpy")
        [.var .local (ofString "enc"), esrc, .var .local (ofString "w")])).2
      [(locN s "enc", 40)] [] [] :=
    worldEff_of_p26ByteEff_csr (R16Shards.WorldEff.refl s [(locN s "enc", 40)] [] [] hs_live.1 hc) hbe_call
      (fun iv hiv _ => Or.inl ⟨iv, hiv, le_rfl, le_rfl⟩)
  have hpost_live : CsrLiveBufsAt
      (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "memcpy")
        [.var .local (ofString "enc"), esrc, .var .local (ofString "w")])).2
      (locN s "cache") (locN s "new_roots") (locN s "mpt")
      [(locN s "enc", 40), (locN s "vbuf", 96)] :=
    worldEff_csrLiveBufsAt hs_live (by decide) csr_empty_core_out heff_w
      (fun iv hiv _ => by
        obtain rfl := List.mem_singleton.mp hiv
        exact ⟨(locN s "enc", 40), by simp, le_rfl, le_rfl⟩)
  have hln : ∀ nm : String, locN (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy")
        [.var .local (ofString "enc"), esrc, .var .local (ofString "w")])).2 nm = locN s nm := by
    intro nm; unfold locN; rw [hloc_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold CsrMptBufs
    simp only [List.map_cons, List.map_nil, hln "cache", hln "new_roots", hln "mpt", hln "enc", hln "vbuf"]
    exact hpost_live
  · obtain ⟨wp, hwp, hwp0⟩ := hs.1.2
    exact ⟨wp, (hloc_lk (ofString "pass")).trans hwp, hwp0⟩
  · rw [hln "w"]; exact hs.2

private theorem mptSet_R_z_csr {F : Type} (ent : PanSemStateFiniteExact 64 F) :
    ∀ j ∈ [(globN ent "keccak_pad", if globN ent "keccak_pad" = 0 then 0 else 136),
           (globN ent "keccak_st", if globN ent "keccak_st" = 0 then 0 else 200),
           (globN ent "mpt_hash_scratch", if globN ent "mpt_hash_scratch" = 0 then 0 else 40)],
      j.2 = 0 → j.1 % 8 = 0 := by
  intro j hj hz
  rcases List.mem_cons.mp hj with rfl | hj1
  · dsimp only at hz ⊢; split at hz <;> omega
  · rcases List.mem_cons.mp hj1 with rfl | hj2
    · dsimp only at hz ⊢; split at hz <;> omega
    · obtain rfl := List.mem_singleton.mp hj2
      dsimp only at hz ⊢; split at hz <;> omega

private theorem mptSet_R_ti_csr {F : Type} (ent : PanSemStateFiniteExact 64 F)
    {S Nd Nm : List Nat}
    (hW : WorldTypedWith ent S Nd)
    (hm : MptObjInWith ent S Nm (locN ent "m")) :
    IvlsDisj
      [(globN ent "keccak_pad", if globN ent "keccak_pad" = 0 then 0 else 136),
       (globN ent "keccak_st", if globN ent "keccak_st" = 0 then 0 else 200),
       (globN ent "mpt_hash_scratch", if globN ent "mpt_hash_scratch" = 0 then 0 else 40)]
      (worldTypedIvls ent S Nd ++ mptObjIvls ent Nm (locN ent "m")) := by
  let bufs : List (String × Nat) := [("keccak_pad", 136), ("keccak_st", 200), ("mpt_hash_scratch", 40)]
  change IvlsDisj (bufs.map (bufferRegion ent)) (worldTypedIvls ent S Nd ++ mptObjIvls ent Nm (locN ent "m"))
  intro i hi j hj
  obtain ⟨b, hb_mem, rfl⟩ := List.mem_map.mp hi
  rcases List.mem_append.mp hj with hjw | hjm
  · exact bufferRegion_disj hW b (csr_mptSetBufs_ok b hb_mem).1 (csr_mptSetBufs_ok b hb_mem).2 j hjw
  · exact mptObjInWith_disj_buffer_csr hm (csr_mptSetBufs_ok b hb_mem).1 _ (List.mem_singleton_self _) j hjm

theorem pBounded_mpt_set_const_csrMptBufs
    (g_ms : TerminatingFunBoundedOn MptSetReady (ofString "mpt_set") K.«mpt_set»)
    (mk_ms : MptKeeps MptSetReady
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (ofString "mpt_set"))
    (mname : String) (buffers : List (String × Nat))
    (ekey evptr : ExpHOL 64) (klen vlen : BitVec 64)
    (hk : klen.toNat ≤ 32) (hv : vlen.toNat ≤ 110) :
    PBounded (CsrMptBufs mname buffers)
      (.call (some (none, none)) (ofString "mpt_set")
        [.var .local (ofString mname), ekey, .const klen, evptr, .const vlen])
      (K.«mpt_set» + 1) := by
  refine pBounded_call0_on_csr g_ms mk_ms ?_ ?_
  · intro F s values body callee ret hc hs ha hl
    obtain ⟨v1, _, v3, _, v5, he1, _, he3, _, he5, hc1, _, hc3, _, hc5⟩ :=
      callee_param_five_exp_csr s (ofString "mpt_set")
        (ofString "m") (ofString "key") (ofString "klen") (ofString "vptr") (ofString "vlen")
        .one .one .one .one .one (sourceFnBody Guest.Software.guestFn_mpt_set) .one
        (hc ▸ P3MptSet.lookup_mpt_set)
        (.var .local (ofString mname)) ekey (.const klen) evptr (.const vlen)
        values body callee ret ha hl
    let ent := callEntryStateHOLFinite s callee
    have hm_eq : locN ent "m" = locN s mname := by
      unfold locN ent callEntryStateHOLFinite; dsimp only; rw [hc1]
      simp only [evalAt, evalHOLExact] at he1; rw [← he1]
    have hk_eq : locN ent "klen" = klen.toNat := by
      simp only [evalAt, evalHOLExact, Option.some.injEq] at he3; subst v3
      unfold locN ent callEntryStateHOLFinite; dsimp only; rw [hc3]
    have hv_eq : locN ent "vlen" = vlen.toNat := by
      simp only [evalAt, evalHOLExact, Option.some.injEq] at he5; subst v5
      unfold locN ent callEntryStateHOLFinite; dsimp only; rw [hc5]
    have hs_ent : CsrLiveBufsAt ent (locN s "cache") (locN s "new_roots") (locN ent "m")
        (buffers.map fun b => (locN s b.1, b.2)) := by
      rw [hm_eq]; exact localsFree_csrLiveBufsAt _ _ _ _ s callee _ hs
    exact csrLiveBufsAt_mptSetReady hs_ent (hk_eq ▸ hk) (hv_eq ▸ hv)
  · intro F s values body callee ret v post hc hs ha hl _ hq
    obtain ⟨v1, _, _, _, _, he1, _, _, _, _, hc1, _, _, _, _⟩ :=
      callee_param_five_exp_csr s (ofString "mpt_set")
        (ofString "m") (ofString "key") (ofString "klen") (ofString "vptr") (ofString "vlen")
        .one .one .one .one .one (sourceFnBody Guest.Software.guestFn_mpt_set) .one
        (hc ▸ P3MptSet.lookup_mpt_set)
        (.var .local (ofString mname)) ekey (.const klen) evptr (.const vlen)
        values body callee ret ha hl
    let ent := callEntryStateHOLFinite s callee
    have hm_eq : locN ent "m" = locN s mname := by
      unfold locN ent callEntryStateHOLFinite; dsimp only; rw [hc1]
      simp only [evalAt, evalHOLExact] at he1; rw [← he1]
    have hs_ent : CsrLiveBufsAt ent (locN s "cache") (locN s "new_roots") (locN ent "m")
        (buffers.map fun b => (locN s b.1, b.2)) := by
      rw [hm_eq]; exact localsFree_csrLiveBufsAt _ _ _ _ s callee _ hs
    have hpost := mptObjStep_csrLiveBufsAt hs_ent (hq (Or.inl ⟨v, rfl⟩))
      (mptSet_R_z_csr ent) (fun S Nd Nm hW hm _ _ => mptSet_R_ti_csr ent hW hm)
    rw [hm_eq] at hpost
    exact localsFree_csrLiveBufsAt _ _ _ _ post s.locals post.clock hpost

theorem pBounded_mpt_set_const_csrNonNeg
    (g_ms : TerminatingFunBoundedOn MptSetReady (ofString "mpt_set") K.«mpt_set»)
    (mk_ms : MptKeeps MptSetReady
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (ofString "mpt_set"))
    (pname mname : String) (buffers : List (String × Nat))
    (ekey evptr : ExpHOL 64) (klen vlen : BitVec 64)
    (hk : klen.toNat ≤ 32) (hv : vlen.toNat ≤ 110) :
    PBounded (CsrNonNeg pname (CsrMptBufs mname buffers))
      (.call (some (none, none)) (ofString "mpt_set")
        [.var .local (ofString mname), ekey, .const klen, evptr, .const vlen])
      (K.«mpt_set» + 1) := by
  have hb0 := pBounded_mpt_set_const_csrMptBufs g_ms mk_ms mname buffers ekey evptr klen vlen hk hv
  refine pBounded_call0_on_csr g_ms mk_ms
    (fun s vs body callee ret hc hs ha hl => by
      obtain ⟨v1, _, v3, _, v5, he1, _, he3, _, he5, hc1, _, hc3, _, hc5⟩ :=
        callee_param_five_exp_csr s (ofString "mpt_set")
          (ofString "m") (ofString "key") (ofString "klen") (ofString "vptr") (ofString "vlen")
          .one .one .one .one .one (sourceFnBody Guest.Software.guestFn_mpt_set) .one
          (hc ▸ P3MptSet.lookup_mpt_set)
          (.var .local (ofString mname)) ekey (.const klen) evptr (.const vlen)
          vs body callee ret ha hl
      let ent := callEntryStateHOLFinite s callee
      have hm_eq : locN ent "m" = locN s mname := by
        unfold locN ent callEntryStateHOLFinite; dsimp only; rw [hc1]
        simp only [evalAt, evalHOLExact] at he1; rw [← he1]
      have hk_eq : locN ent "klen" = klen.toNat := by
        simp only [evalAt, evalHOLExact, Option.some.injEq] at he3; subst v3
        unfold locN ent callEntryStateHOLFinite; dsimp only; rw [hc3]
      have hv_eq : locN ent "vlen" = vlen.toNat := by
        simp only [evalAt, evalHOLExact, Option.some.injEq] at he5; subst v5
        unfold locN ent callEntryStateHOLFinite; dsimp only; rw [hc5]
      have hs_ent : CsrLiveBufsAt ent (locN s "cache") (locN s "new_roots") (locN ent "m")
          (buffers.map fun b => (locN s b.1, b.2)) := by
        rw [hm_eq]; exact localsFree_csrLiveBufsAt _ _ _ _ s callee _ hs.1
      exact csrLiveBufsAt_mptSetReady hs_ent (hk_eq ▸ hk) (hv_eq ▸ hv))
    (fun s vs body callee ret v post hc hs ha hl _ hq => by
      obtain ⟨v1, _, _, _, _, he1, _, _, _, _, hc1, _, _, _, _⟩ :=
        callee_param_five_exp_csr s (ofString "mpt_set")
          (ofString "m") (ofString "key") (ofString "klen") (ofString "vptr") (ofString "vlen")
          .one .one .one .one .one (sourceFnBody Guest.Software.guestFn_mpt_set) .one
          (hc ▸ P3MptSet.lookup_mpt_set)
          (.var .local (ofString mname)) ekey (.const klen) evptr (.const vlen)
          vs body callee ret ha hl
      let ent := callEntryStateHOLFinite s callee
      have hm_eq : locN ent "m" = locN s mname := by
        unfold locN ent callEntryStateHOLFinite; dsimp only; rw [hc1]
        simp only [evalAt, evalHOLExact] at he1; rw [← he1]
      have hs_ent : CsrLiveBufsAt ent (locN s "cache") (locN s "new_roots") (locN ent "m")
          (buffers.map fun b => (locN s b.1, b.2)) := by
        rw [hm_eq]; exact localsFree_csrLiveBufsAt _ _ _ _ s callee _ hs.1
      have hpost := mptObjStep_csrLiveBufsAt hs_ent (hq (Or.inl ⟨v, rfl⟩))
        (mptSet_R_z_csr ent) (fun S Nd Nm hW hm _ _ => mptSet_R_ti_csr ent hW hm)
      rw [hm_eq] at hpost
      exact ⟨localsFree_csrLiveBufsAt _ _ _ _ post s.locals post.clock hpost, hs.2⟩)

theorem pBounded_mpt_set_bound_csrMptBufs
    (g_ms : TerminatingFunBoundedOn MptSetReady (ofString "mpt_set") K.«mpt_set»)
    (mk_ms : MptKeeps MptSetReady
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (ofString "mpt_set"))
    (wname : String) (wbound : Nat) (mname : String) (buffers : List (String × Nat))
    (ekey evptr : ExpHOL 64) (klen : BitVec 64)
    (hk : klen.toNat ≤ 32) (hv : wbound ≤ 110) :
    PBounded (CsrBound wname wbound (CsrMptBufs mname buffers))
      (.call (some (none, none)) (ofString "mpt_set")
        [.var .local (ofString mname), ekey, .const klen, evptr, .var .local (ofString wname)])
      (K.«mpt_set» + 1) := by
  refine pBounded_call0_on_csr g_ms mk_ms ?_ ?_
  · intro F s values body callee ret hc hs ha hl
    obtain ⟨v1, _, v3, _, v5, he1, _, he3, _, he5, hc1, _, hc3, _, hc5⟩ :=
      callee_param_five_exp_csr s (ofString "mpt_set")
        (ofString "m") (ofString "key") (ofString "klen") (ofString "vptr") (ofString "vlen")
        .one .one .one .one .one (sourceFnBody Guest.Software.guestFn_mpt_set) .one
        (hc ▸ P3MptSet.lookup_mpt_set)
        (.var .local (ofString mname)) ekey (.const klen) evptr (.var .local (ofString wname))
        values body callee ret ha hl
    let ent := callEntryStateHOLFinite s callee
    have hm_eq : locN ent "m" = locN s mname := by
      unfold locN ent callEntryStateHOLFinite; dsimp only; rw [hc1]
      simp only [evalAt, evalHOLExact] at he1; rw [← he1]
    have hk_eq : locN ent "klen" = klen.toNat := by
      simp only [evalAt, evalHOLExact, Option.some.injEq] at he3; subst v3
      unfold locN ent callEntryStateHOLFinite; dsimp only; rw [hc3]
    have hv_eq : locN ent "vlen" = locN s wname := by
      unfold locN ent callEntryStateHOLFinite; dsimp only; rw [hc5]
      simp only [evalAt, evalHOLExact] at he5; rw [← he5]
    have hs_ent : CsrLiveBufsAt ent (locN s "cache") (locN s "new_roots") (locN ent "m")
        (buffers.map fun b => (locN s b.1, b.2)) := by
      rw [hm_eq]; exact localsFree_csrLiveBufsAt _ _ _ _ s callee _ hs.1
    exact csrLiveBufsAt_mptSetReady hs_ent (hk_eq ▸ hk) (hv_eq ▸ Nat.le_trans hs.2 hv)
  · intro F s values body callee ret v post hc hs ha hl _ hq
    obtain ⟨v1, _, _, _, _, he1, _, _, _, _, hc1, _, _, _, _⟩ :=
      callee_param_five_exp_csr s (ofString "mpt_set")
        (ofString "m") (ofString "key") (ofString "klen") (ofString "vptr") (ofString "vlen")
        .one .one .one .one .one (sourceFnBody Guest.Software.guestFn_mpt_set) .one
        (hc ▸ P3MptSet.lookup_mpt_set)
        (.var .local (ofString mname)) ekey (.const klen) evptr (.var .local (ofString wname))
        values body callee ret ha hl
    let ent := callEntryStateHOLFinite s callee
    have hm_eq : locN ent "m" = locN s mname := by
      unfold locN ent callEntryStateHOLFinite; dsimp only; rw [hc1]
      simp only [evalAt, evalHOLExact] at he1; rw [← he1]
    have hs_ent : CsrLiveBufsAt ent (locN s "cache") (locN s "new_roots") (locN ent "m")
        (buffers.map fun b => (locN s b.1, b.2)) := by
      rw [hm_eq]; exact localsFree_csrLiveBufsAt _ _ _ _ s callee _ hs.1
    have hpost := mptObjStep_csrLiveBufsAt hs_ent (hq (Or.inl ⟨v, rfl⟩))
      (mptSet_R_z_csr ent) (fun S Nd Nm hW hm _ _ => mptSet_R_ti_csr ent hW hm)
    rw [hm_eq] at hpost
    exact ⟨localsFree_csrLiveBufsAt _ _ _ _ post s.locals post.clock hpost, hs.2⟩

theorem pBounded_mpt_set_bound_csrNonNeg_csrMptBufs
    (g_ms : TerminatingFunBoundedOn MptSetReady (ofString "mpt_set") K.«mpt_set»)
    (mk_ms : MptKeeps MptSetReady
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (ofString "mpt_set"))
    (wname : String) (wbound : Nat) (pname mname : String) (buffers : List (String × Nat))
    (ekey evptr : ExpHOL 64) (klen : BitVec 64)
    (hk : klen.toNat ≤ 32) (hv : wbound ≤ 110) :
    PBounded (CsrBound wname wbound (CsrNonNeg pname (CsrMptBufs mname buffers)))
      (.call (some (none, none)) (ofString "mpt_set")
        [.var .local (ofString mname), ekey, .const klen, evptr, .var .local (ofString wname)])
      (K.«mpt_set» + 1) := by
  refine pBounded_call0_on_csr g_ms mk_ms ?_ ?_
  · intro F s values body callee ret hc hs ha hl
    obtain ⟨v1, _, v3, _, v5, he1, _, he3, _, he5, hc1, _, hc3, _, hc5⟩ :=
      callee_param_five_exp_csr s (ofString "mpt_set")
        (ofString "m") (ofString "key") (ofString "klen") (ofString "vptr") (ofString "vlen")
        .one .one .one .one .one (sourceFnBody Guest.Software.guestFn_mpt_set) .one
        (hc ▸ P3MptSet.lookup_mpt_set)
        (.var .local (ofString mname)) ekey (.const klen) evptr (.var .local (ofString wname))
        values body callee ret ha hl
    let ent := callEntryStateHOLFinite s callee
    have hm_eq : locN ent "m" = locN s mname := by
      unfold locN ent callEntryStateHOLFinite; dsimp only; rw [hc1]
      simp only [evalAt, evalHOLExact] at he1; rw [← he1]
    have hk_eq : locN ent "klen" = klen.toNat := by
      simp only [evalAt, evalHOLExact, Option.some.injEq] at he3; subst v3
      unfold locN ent callEntryStateHOLFinite; dsimp only; rw [hc3]
    have hv_eq : locN ent "vlen" = locN s wname := by
      unfold locN ent callEntryStateHOLFinite; dsimp only; rw [hc5]
      simp only [evalAt, evalHOLExact] at he5; rw [← he5]
    have hs_ent : CsrLiveBufsAt ent (locN s "cache") (locN s "new_roots") (locN ent "m")
        (buffers.map fun b => (locN s b.1, b.2)) := by
      rw [hm_eq]; exact localsFree_csrLiveBufsAt _ _ _ _ s callee _ hs.1.1
    exact csrLiveBufsAt_mptSetReady hs_ent (hk_eq ▸ hk) (hv_eq ▸ Nat.le_trans hs.2 hv)
  · intro F s values body callee ret v post hc hs ha hl _ hq
    obtain ⟨v1, _, _, _, _, he1, _, _, _, _, hc1, _, _, _, _⟩ :=
      callee_param_five_exp_csr s (ofString "mpt_set")
        (ofString "m") (ofString "key") (ofString "klen") (ofString "vptr") (ofString "vlen")
        .one .one .one .one .one (sourceFnBody Guest.Software.guestFn_mpt_set) .one
        (hc ▸ P3MptSet.lookup_mpt_set)
        (.var .local (ofString mname)) ekey (.const klen) evptr (.var .local (ofString wname))
        values body callee ret ha hl
    let ent := callEntryStateHOLFinite s callee
    have hm_eq : locN ent "m" = locN s mname := by
      unfold locN ent callEntryStateHOLFinite; dsimp only; rw [hc1]
      simp only [evalAt, evalHOLExact] at he1; rw [← he1]
    have hs_ent : CsrLiveBufsAt ent (locN s "cache") (locN s "new_roots") (locN ent "m")
        (buffers.map fun b => (locN s b.1, b.2)) := by
      rw [hm_eq]; exact localsFree_csrLiveBufsAt _ _ _ _ s callee _ hs.1.1
    have hpost := mptObjStep_csrLiveBufsAt hs_ent (hq (Or.inl ⟨v, rfl⟩))
      (mptSet_R_z_csr ent) (fun S Nd Nm hW hm _ _ => mptSet_R_ti_csr ent hW hm)
    rw [hm_eq] at hpost
    exact ⟨⟨localsFree_csrLiveBufsAt _ _ _ _ post s.locals post.clock hpost, hs.1.2⟩, hs.2⟩

theorem pBounded_mpt_root_buf_csr
    (g_mr : TerminatingFunBoundedOn MptObjReady (ofString "mpt_root") K.«mpt_root»)
    (mk_mr : MptKeeps MptObjReady
      (fun s => [(locN s "out", 32),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (ofString "mpt_root"))
    (mname rname : String) (buffers : List (String × Nat)) :
    PBounded (CsrMptBufs mname ((rname, 32) :: buffers))
      (.call (some (none, none)) (ofString "mpt_root")
        [.var .local (ofString mname), .var .local (ofString rname)])
      (K.«mpt_root» + 1) := by
  refine pBounded_call0_on_csr g_mr mk_mr ?_ ?_
  · intro F s values body callee ret hc hs ha hl
    obtain ⟨v1, _, he1, _, hc1, _, _⟩ := callee_param_two_exp_csr s (ofString "mpt_root")
      (ofString "m") (ofString "out") .one .one
      (sourceFnBody Guest.Software.guestFn_mpt_root) .one
      (hc ▸ lookup_mpt_root_csr)
      (.var .local (ofString mname)) (.var .local (ofString rname)) values body callee ret ha hl
    let ent := callEntryStateHOLFinite s callee
    have hm_eq : locN ent "m" = locN s mname := by
      unfold locN ent callEntryStateHOLFinite; dsimp only; rw [hc1]
      simp only [evalAt, evalHOLExact] at he1; rw [← he1]
    have hs_ent : CsrLiveBufsAt ent (locN s "cache") (locN s "new_roots") (locN ent "m")
        (((rname, 32) :: buffers).map fun b => (locN s b.1, b.2)) := by
      rw [hm_eq]; exact localsFree_csrLiveBufsAt _ _ _ _ s callee _ hs
    exact csrLiveBufsAt_mptObjReady hs_ent
  · intro F s values body callee ret v post hc hs ha hl _ hq
    obtain ⟨v1, v2, he1, he2, hc1, hc2, _⟩ := callee_param_two_exp_csr s (ofString "mpt_root")
      (ofString "m") (ofString "out") .one .one
      (sourceFnBody Guest.Software.guestFn_mpt_root) .one
      (hc ▸ lookup_mpt_root_csr)
      (.var .local (ofString mname)) (.var .local (ofString rname)) values body callee ret ha hl
    let ent := callEntryStateHOLFinite s callee
    have hm_eq : locN ent "m" = locN s mname := by
      unfold locN ent callEntryStateHOLFinite; dsimp only; rw [hc1]
      simp only [evalAt, evalHOLExact] at he1; rw [← he1]
    have hout_eq : locN ent "out" = locN s rname := by
      unfold locN ent callEntryStateHOLFinite; dsimp only; rw [hc2]
      simp only [evalAt, evalHOLExact] at he2; rw [← he2]
    have hs_ent : CsrLiveBufsAt ent (locN s "cache") (locN s "new_roots") (locN ent "m")
        (((rname, 32) :: buffers).map fun b => (locN s b.1, b.2)) := by
      rw [hm_eq]; exact localsFree_csrLiveBufsAt _ _ _ _ s callee _ hs
    have hpost := mptObjStep_csrLiveBufsAt hs_ent (hq (Or.inl ⟨v, rfl⟩))
      (fun j hj hz => by
        rcases List.mem_cons.mp hj with rfl | hj1
        · dsimp only at hz; omega
        · rcases List.mem_cons.mp hj1 with rfl | hj2
          · dsimp only at hz ⊢; split at hz <;> omega
          · obtain rfl := List.mem_singleton.mp hj2
            dsimp only at hz ⊢; split at hz <;> omega)
      (fun S Nd Nm hW hm _ hbs => by
        intro r hr_mem j hj
        rcases List.mem_cons.mp hr_mem with rfl | hr1
        · have hb_root : CsrHeapBufAt ent (locN s rname, 32)
              (worldOwned ent S Nd ++ mptObjIvls ent Nm (locN ent "m")) :=
            hbs (locN s rname, 32) (by simp)
          have hj_sub : j ∈ worldOwned ent S Nd ++ mptObjIvls ent Nm (locN ent "m") := by
            rcases List.mem_append.mp hj with hjw | hjm
            · exact List.mem_append_left _ (worldTypedIvls_sub_worldOwned ent S Nd j hjw)
            · exact List.mem_append_right _ hjm
          rw [hout_eq]
          exact hb_root.2.2 _ (List.mem_singleton_self _) j hj_sub
        · let bufs : List (String × Nat) := [("keccak_pad", 136), ("keccak_st", 200)]
          have hr_buf : r ∈ bufs.map (bufferRegion ent) := hr1
          obtain ⟨b, hb_mem, rfl⟩ := List.mem_map.mp hr_buf
          rcases List.mem_append.mp hj with hjw | hjm
          · exact bufferRegion_disj hW b (csr_mptRootBufs_ok b hb_mem).1
              (csr_mptRootBufs_ok b hb_mem).2 j hjw
          · exact mptObjInWith_disj_buffer_csr hm (csr_mptRootBufs_ok b hb_mem).1
              _ (List.mem_singleton_self _) j hjm)
    rw [hm_eq] at hpost
    exact localsFree_csrLiveBufsAt _ _ _ _ post s.locals post.clock hpost

theorem pBounded_encode_account_csr
    (tf_ea : TerminatingFunBoundedOn GuestInv (ofString "encode_account") K.«encode_account»)
    (mname ename nname : String)
    (e1 e2 e3 e4 : ExpHOL 64) {Bc : Nat} {cont : ProgHOL 64}
    (hne : ∀ n ∈ ["cache", "new_roots", mname, ename], ofString n ≠ ofString nname)
    (hcont : PBounded (CsrBound nname 110 (CsrMptBufs mname [(ename, 128)])) cont Bc) :
    PBounded (CsrMptBufs mname [(ename, 128)])
      (.decCall (ofString nname) .one (ofString "encode_account")
        [e1, e2, e3, e4, .var .local (ofString ename)] cont)
      (K.«encode_account» + Bc + 1) := by
  have hne' : ∀ n ∈ ["cache", "new_roots", mname] ++ ([(ename, 128)] : List (String × Nat)).map Prod.fst,
      ofString n ≠ ofString nname := by
    intro n hn
    simp only [List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append] at hn
    exact hne n hn
  refine pBounded_specDecCall_csr (localsOnly_csrMptBufs mname [(ename, 128)]) tf_ea rv_encode_account_csr
    (callEntryOn_guestInv_csr (fun s hs => (csrMptBufs_worldOK mname [(ename, 128)] hs).1.1) _ _)
    hne' ?_ hcont.1 ⟨fun s hc hR hnt hr => (hcont.2.run s hc hR hnt hr).1⟩
  intro F s values body callee ret v post hc hs ha hl hb hq
  obtain ⟨w, rfl, hw_le⟩ := hq v rfl
  obtain ⟨_, _, _, _, v5, _, _, _, _, he5, _, _, _, _, hc5, hbody_eq⟩ :=
    callee_param_five_exp_body_csr s (ofString "encode_account")
      (ofString "nonce") (ofString "balance") (ofString "storage_root") (ofString "code_hash") (ofString "out")
      .one (.comb [.one, .one, .one, .one]) .one .one .one
      (sourceFnBody Guest.Software.guestFn_encode_account) .one
      (hc ▸ R16Rlp.lookup_encode_account)
      e1 e2 e3 e4 (.var .local (ofString ename)) values body callee ret ha hl
  subst hbody_eq
  let ent := callEntryStateHOLFinite s callee
  have hout_eq : locN ent "out" = locN s ename := by
    unfold locN ent callEntryStateHOLFinite; dsimp only; rw [hc5]
    simp only [evalAt, evalHOLExact] at he5; rw [← he5]
  have hs_ent : CsrLiveBufsAt ent (locN s "cache") (locN s "new_roots") (locN s mname)
      [(locN s ename, 128)] :=
    localsFree_csrLiveBufsAt _ _ _ _ s callee _ hs
  have hwok_ent : WorldOK ent := localsFree_worldOK s callee _ (csrMptBufs_worldOK mname [(ename, 128)] hs)
  have hbe_ea := byteEff_encode_account_body_csr ent hc hwok_ent
    (by rw [hb]; simp) (by rw [hb]; exact Or.inl ⟨.val (.word w), rfl⟩)
  rw [hb] at hbe_ea; dsimp only at hbe_ea
  have heff_w : R16Shards.WorldEff ent post [(locN s ename, 128)] [("mpt_hash_scratch", 40)] [] :=
    worldEff_of_p26ByteEff_csr
      (R16Shards.WorldEff.refl ent [(locN s ename, 128)] [("mpt_hash_scratch", 40)] [] hs_ent.1 hc)
      hbe_ea
      (fun iv hiv hpos => by
        rcases List.mem_cons.mp hiv with rfl | hiv1
        · left; refine ⟨(locN s ename, 128), by simp, ?_, ?_⟩
          · dsimp only; rw [hout_eq]
          · dsimp only; rw [hout_eq]; omega
        · obtain rfl := List.mem_singleton.mp hiv1
          right; left
          refine ⟨("mpt_hash_scratch", 40), by simp, le_rfl, le_rfl⟩)
  have hpost_live : CsrLiveBufsAt post (locN s "cache") (locN s "new_roots") (locN s mname)
      [(locN s ename, 128)] :=
    worldEff_csrLiveBufsAt hs_ent csr_eaBufs_ok csr_empty_core_out heff_w
      (fun iv hiv _ => ⟨iv, hiv, le_rfl, le_rfl⟩)
  let mid := setVarHOLFinite (ofString nname) (.val (.word w)) { post with locals := s.locals }
  refine ⟨?_, ?_⟩
  · have hc_mid : locN mid "cache" = locN s "cache" := locN_setVar_ne _ "cache" (ofString nname) _ (hne "cache" (by simp))
    have hr_mid : locN mid "new_roots" = locN s "new_roots" := locN_setVar_ne _ "new_roots" (ofString nname) _ (hne "new_roots" (by simp))
    have hm_mid : locN mid mname = locN s mname := locN_setVar_ne _ mname (ofString nname) _ (hne mname (by simp))
    have he_mid : locN mid ename = locN s ename := locN_setVar_ne _ ename (ofString nname) _ (hne ename (by simp))
    show CsrMptBufs mname [(ename, 128)] mid
    unfold CsrMptBufs
    simp only [List.map_cons, List.map_nil, hc_mid, hr_mid, hm_mid, he_mid]
    exact localsFree_csrLiveBufsAt _ _ _ _ post mid.locals mid.clock hpost_live
  · show locN mid nname ≤ 110
    rw [locN_setVar_same]; exact hw_le

theorem pBounded_ws_get_account_optional_csrMptBufs
    (tf_wgao : TerminatingFunBoundedOn GuestInv (ofString "ws_get_account_optional") K.«ws_get_account_optional»)
    (mname aname : String) (eaddr : ExpHOL 64) {Bc : Nat} {cont : ProgHOL 64}
    (hne : ∀ n ∈ ["cache", "new_roots", mname], ofString n ≠ ofString aname)
    (hcont : PBounded (CsrMptBufs mname []) cont Bc) :
    PBounded (CsrMptBufs mname [])
      (.decCall (ofString aname) .one (ofString "ws_get_account_optional") [eaddr] cont)
      (K.«ws_get_account_optional» + Bc + 1) := by
  have hne' : ∀ n ∈ ["cache", "new_roots", mname] ++ ([] : List (String × Nat)).map Prod.fst,
      ofString n ≠ ofString aname := by
    intro n hn; simp at hn; exact hne n (by simpa using hn)
  refine PBounded.decCallTrans tf_wgao (localsOnly_csrMptBufs mname []) (ofString aname) hne' .one [eaddr]
    (callEntryOn_guestInv_csr (fun s hs => (csrMptBufs_worldOK mname [] hs).1.1) _ _)
    ?_ hcont.1 hcont.2
  intro F s values body callee ret v post hc hs ha hl hb
  obtain ⟨_, _, _, hbody_eq⟩ := callee_param_one_exp_csr s (ofString "ws_get_account_optional")
    (ofString "addr") .one (sourceFnBody Guest.Software.guestFn_ws_get_account_optional) .one
    (hc ▸ lookup_ws_get_account_optional_csr) eaddr values body callee ret ha hl
  subst hbody_eq
  let ent := callEntryStateHOLFinite s callee
  have hs_ent : CsrLiveBufsAt ent (locN s "cache") (locN s "new_roots") (locN s mname) [] :=
    localsFree_csrLiveBufsAt _ _ _ _ s callee _ hs
  have heff := R16Shards.worldEff_ws_get_account_optional ent ent hs_ent.1.2
    (R16Shards.WorldEff.refl ent [] R16Shards.wsBufs R16Shards.wsGw hs_ent.1 hc)
    (by rw [hb]; simp) (by rw [hb]; exact Or.inl ⟨v, rfl⟩)
  rw [hb] at heff; dsimp only at heff
  have hpost_live : CsrLiveBufsAt post (locN s "cache") (locN s "new_roots") (locN s mname) [] :=
    worldEff_csrLiveBufsAt hs_ent csr_wsBufs_ok csr_ws_core_out heff (fun _ h => by cases h)
  let mid := setVarHOLFinite (ofString aname) v { post with locals := s.locals }
  have hc_mid : locN mid "cache" = locN s "cache" := locN_setVar_ne _ "cache" (ofString aname) _ (hne "cache" (by simp))
  have hr_mid : locN mid "new_roots" = locN s "new_roots" := locN_setVar_ne _ "new_roots" (ofString aname) _ (hne "new_roots" (by simp))
  have hm_mid : locN mid mname = locN s mname := locN_setVar_ne _ mname (ofString aname) _ (hne mname (by simp))
  show CsrMptBufs mname [] mid
  unfold CsrMptBufs
  simp only [List.map_nil, hc_mid, hr_mid, hm_mid]
  exact localsFree_csrLiveBufsAt _ _ _ _ post mid.locals mid.clock hpost_live

theorem pBounded_cache_get_root_csrMptBufs
    (tf_cgr : TerminatingFunBoundedOn GuestInv (ofString "cache_get_root") K.«cache_get_root»)
    (mname sname : String) (ecache eaddr : ExpHOL 64)
    (hne : ∀ n ∈ ["cache", "new_roots", mname], ofString n ≠ ofString sname) :
    PBounded (CsrMptBufs mname [])
      (.call (some (some (.local, ofString sname), none)) (ofString "cache_get_root") [ecache, eaddr])
      (K.«cache_get_root» + 1) := by
  refine pBounded_callLocal_csr tf_cgr
    (callEntryOn_guestInv_csr (fun s hs => (csrMptBufs_worldOK mname [] hs).1.1) _ _)
    ?_
  intro F s values body callee ret v post hc hs ha hl hb
  obtain ⟨_, _, _, _, _, _, hbody_eq⟩ := callee_param_two_exp_csr s (ofString "cache_get_root")
    (ofString "cache") (ofString "addr") .one .one
    (sourceFnBody Guest.Software.guestFn_cache_get_root) .one
    (hc ▸ lookup_cache_get_root_csr) ecache eaddr values body callee ret ha hl
  subst hbody_eq
  let ent := callEntryStateHOLFinite s callee
  have hs_ent : CsrLiveBufsAt ent (locN s "cache") (locN s "new_roots") (locN s mname) [] :=
    localsFree_csrLiveBufsAt _ _ _ _ s callee _ hs
  have heff := R16Shards.worldEff_cache_get_root ent ent hs_ent.1.2
    (R16Shards.WorldEff.refl ent [] R16Shards.wsBufs R16Shards.wsGw hs_ent.1 hc)
    (by rw [hb]; simp) (by rw [hb]; exact Or.inl ⟨v, rfl⟩)
  rw [hb] at heff; dsimp only at heff
  have hpost_live : CsrLiveBufsAt post (locN s "cache") (locN s "new_roots") (locN s mname) [] :=
    worldEff_csrLiveBufsAt hs_ent csr_wsBufs_ok csr_ws_core_out heff (fun _ h => by cases h)
  let mid := setVarHOLFinite (ofString sname) v { post with locals := s.locals }
  have hc_mid : locN mid "cache" = locN s "cache" := locN_setVar_ne _ "cache" (ofString sname) _ (hne "cache" (by simp))
  have hr_mid : locN mid "new_roots" = locN s "new_roots" := locN_setVar_ne _ "new_roots" (ofString sname) _ (hne "new_roots" (by simp))
  have hm_mid : locN mid mname = locN s mname := locN_setVar_ne _ mname (ofString sname) _ (hne mname (by simp))
  show CsrMptBufs mname [] mid
  unfold CsrMptBufs
  simp only [List.map_nil, hc_mid, hr_mid, hm_mid]
  exact localsFree_csrLiveBufsAt _ _ _ _ post mid.locals mid.clock hpost_live

theorem pBounded_roDecCall_csr {names : List String}
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {fname : MlS} {B Bc : Nat}
    (hf : TerminatingFunBoundedOn GuestInv fname B)
    (hro : ReadOnlyFn fname)
    (hP : LocalsOnly names P)
    (hPG : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → GuestInv s)
    (name : MlS) (hne : ∀ n ∈ names, ofString n ≠ name)
    (shape : ShapeHOL) (args : List (ExpHOL 64)) {cont : ProgHOL 64}
    (hcont : PBounded P cont Bc) :
    PBounded P (.decCall name shape fname args cont) (B + Bc + 1) :=
  PBounded.decCallTrans hf hP name hne shape args
    (callEntryOn_guestInv_csr hPG fname args)
    (ReadOnlyFn.resumeOn hP hPG hro name hne args)
    hcont.bounded hcont.hoare

theorem pBounded_ite_yes_csr
    {P Y : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (cond : ExpHOL 64) {yes no : ProgHOL 64} {a b : Nat}
    (himp : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → CondTrue cond s → Y s)
    (hout : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F), Y t → P t)
    (hy : PBounded Y yes a) (hn : PBounded P no b) :
    PBounded P (.ite cond yes no) (max a b) := by
  refine ⟨?_, Hoare.ite
    ⟨fun s hc hPs hnt hr => hout _ (hy.hoare.run s hc (himp s hPs.1 hPs.2) hnt hr)⟩
    ⟨fun s hc hPs hnt hr => hn.hoare.run s hc hPs.1 hnt hr⟩
    (fun _ _ hr => absurd hr (by simp))⟩
  intro F state hcode hP hnt
  rw [evaluateHOLFiniteState_ite] at hnt ⊢
  revert hnt
  split <;> intro hnt
  · rename_i w hw
    revert hnt
    split <;> intro hnt
    · exact TerminatingRunBounded.weaken (hn.bounded state hcode hP) (Nat.le_max_right a b) hnt
    · rename_i hz
      exact TerminatingRunBounded.weaken
        (hy.bounded state hcode (himp state hP ⟨w, hw, hz⟩)) (Nat.le_max_left a b) hnt
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

theorem pass0_cond_nonNeg_csr {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : CondTrue
      (.op .and
        [.cmp .notEqual (.const (0#64))
          (.cmp .equal (.var .local (ofString "pass")) (.const (0#64))),
         .cmp .notEqual (.const (0#64))
          (.cmp .equal (.var .local (ofString "z")) (.const (0#64)))]) s) :
    ∃ wp : BitVec 64, s.locals.lookup (ofString "pass") = some (.val (.word wp)) ∧ 0 ≤ wp.toInt := by
  obtain ⟨w, hw, hz⟩ := hc
  change @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) _ = some (.val (.word w)) at hw
  simp only [evalHOLExact, evalListHOLExact] at hw
  rcases hlp : s.locals.lookup (ofString "pass") with _ | vp
  · simp [hlp, valueIsWord] at hw
  · rcases vp with ⟨⟨wp⟩⟩ | _ | _
    · rcases hlz : s.locals.lookup (ofString "z") with _ | vz
      · simp [hlp, hlz, valueIsWord] at hw
      · rcases vz with ⟨⟨wz⟩⟩ | _ | _
        · by_cases hp0 : wp = 0#64
          · subst hp0
            exact ⟨0#64, rfl, by decide⟩
          · simp [hlp, hlz, hp0, wordCmpHOL, valueIsWord, valueWord, wordOpHOL, wordOp,
              List.all, List.map, Option.map, List.foldr] at hw
            subst hw
            exact absurd rfl hz
        · simp [hlp, hlz, valueIsWord] at hw
        · simp [hlp, hlz, valueIsWord] at hw
    · simp [hlp, valueIsWord] at hw
    · simp [hlp, valueIsWord] at hw

theorem pBounded_rlp_encode_bytes_flat_csr
    (tf_reb : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_bytes") K.«rlp_encode_bytes»)
    {Bc : Nat} {cont : ProgHOL 64}
    (hcont : PBounded (CsrBound "w" 33 (CsrNonNeg "pass" (CsrMptBufs "mpt" [("vbuf", 96)]))) cont Bc)
    (hpres_n : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s cont).1 = none →
      (evaluateHOLFiniteState s cont).2.locals.lookup (ofString "n") = s.locals.lookup (ofString "n")) :
    PBounded (CsrBound "n" 32 (CsrNonNeg "pass" (CsrMptBufs "mpt" [("vbuf", 96)])))
      (.decCall (ofString "w") .one (ofString "rlp_encode_bytes")
        [.op .add [.var .local (ofString "vbuf"), .const (8#64), .const (32#64)],
         .op .add [.var .local (ofString "vbuf"), .const (8#64)],
         .var .local (ofString "n")] cont)
      (K.«rlp_encode_bytes» + Bc + 1) := by
  have hne : ∀ nm ∈ "n" :: "pass" :: (["cache", "new_roots", "mpt"] ++ ([("vbuf", 96)] : List (String × Nat)).map Prod.fst),
      ofString nm ≠ ofString "w" := by decide
  refine PBounded.decCallTrans (R := CsrBound "n" 32 (CsrBound "w" 33 (CsrNonNeg "pass" (CsrMptBufs "mpt" [("vbuf", 96)]))))
    tf_reb
    (localsOnly_csrBound (localsOnly_csrNonNeg (localsOnly_csrMptBufs "mpt" [("vbuf", 96)]) "pass") "n" 32)
    (ofString "w") hne .one _
    (callEntryOn_guestInv_csr (fun s hs => (csrMptBufs_worldOK "mpt" [("vbuf", 96)] hs.1.1).1.1) _ _)
    ?_ (fun s hc hR => hcont.1 s hc hR.1)
    ⟨fun s hc hR hnt hr => by
      have hpost := (hcont.2.run s hc hR.1 hnt hr).1
      have hn_eq : locN (evaluateHOLFiniteState s cont).2 "n" = locN s "n" := by
        unfold locN; rw [hpres_n s hr]
      exact ⟨hpost, hn_eq ▸ hR.2⟩⟩
  intro F s values body callee ret v post hc hs ha hl hb
  obtain ⟨v1, v2, v3, he1, he2, he3, hc1, hc2, hc3, hbody_eq⟩ :=
    callee_param_three_exp_body_csr s (ofString "rlp_encode_bytes")
      (ofString "dst") (ofString "src") (ofString "n") .one .one .one
      (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes) .one
      (hc ▸ R16Rlp.lookup_rlp_encode_bytes)
      (.op .add [.var .local (ofString "vbuf"), .const (8#64), .const (32#64)])
      (.op .add [.var .local (ofString "vbuf"), .const (8#64)])
      (.var .local (ofString "n")) values body callee ret ha hl
  subst hbody_eq
  have hvbuf_ex : ∃ vb : BitVec 64, s.locals.lookup (ofString "vbuf") = some (.val (.word vb)) ∧
      v1 = .val (.word (vb + 40#64)) ∧ v2 = .val (.word (vb + 8#64)) := by
    simp only [evalAt, evalHOLExact, evalListHOLExact] at he1 he2
    rcases hlk : s.locals.lookup (ofString "vbuf") with _ | vv
    · simp [hlk] at he2
    · rcases vv with ⟨⟨vb⟩⟩ | _ | _
      · simp [hlk, valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map,
          Option.map, List.foldr, BitVec.add_assoc] at he1 he2
        exact ⟨vb, rfl, he1.symm, he2.symm⟩
      · simp [hlk, valueIsWord] at he2
      · simp [hlk, valueIsWord] at he2
  obtain ⟨vb, hvb_lk, rfl, rfl⟩ := hvbuf_ex
  have hn_ex : ∃ n0 : BitVec 64, s.locals.lookup (ofString "n") = some (.val (.word n0)) ∧
      v3 = .val (.word n0) := by
    have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_encode_bytes") values =
        some (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes, callee, ret) := hc ▸ hl
    have hret_eq : ret = .one :=
      lookupCodeHOLFinite_installed_return s (ofString "rlp_encode_bytes")
        _ _ _ _ ret values callee (hc ▸ R16Rlp.lookup_rlp_encode_bytes) hl
    subst hret_eq
    obtain ⟨_, _, n0, hvs, _, _, _⟩ := lookupCode_three_words
      (by decide) (by decide) (by decide) R16Rlp.lookup_rlp_encode_bytes hl_orig
    have hv3_eq : v3 = .val (.word n0) := by
      rw [evalListHOLFinite_eq_toExact] at ha
      simp only [evalListHOLExact] at ha
      simp only [evalAt] at he1 he2 he3
      rw [he1, he2, he3] at ha
      injection ha with hvs'
      rw [← hvs'] at hvs
      injection hvs with _ htl1; injection htl1 with _ htl2; injection htl2 with hv3 _
    subst hv3_eq
    simp only [evalAt, evalHOLExact] at he3
    exact ⟨n0, he3, rfl⟩
  obtain ⟨n0, hn_lk, rfl⟩ := hn_ex
  have hn0_le : n0.toNat ≤ 32 := by
    have hln : locN s "n" = n0.toNat := by simp [locN, hn_lk]
    have := hs.2; omega
  let ent := callEntryStateHOLFinite s callee
  have hs_live : CsrLiveBufsAt s (locN s "cache") (locN s "new_roots") (locN s "mpt") [(locN s "vbuf", 96)] := hs.1.1
  have hvb_nat : locN s "vbuf" = vb.toNat := by simp [locN, hvb_lk]
  have hvb_hi : vb.toNat + 96 ≤ heapLimit := by
    obtain ⟨hA, _, _, _, _, _, _, _, _, _, _, _, hbs, _⟩ := hs_live
    have hb_in := (hbs (locN s "vbuf", 96) (by simp)).1
    rw [hvb_nat] at hb_in
    exact Nat.le_trans hb_in.2 hA.2.2.1
  have h264 : heapLimit < 2 ^ 64 := by rw [heapLimit_val]; decide
  have hdst_nat : (vb + 40#64).toNat = vb.toNat + 40 :=
    BitVec.toNat_add_of_lt (by change vb.toNat + 40 < 2 ^ 64; omega)
  have hs_ent : CsrLiveBufsAt ent (locN s "cache") (locN s "new_roots") (locN s "mpt") [(locN s "vbuf", 96)] :=
    localsFree_csrLiveBufsAt _ _ _ _ s callee _ hs_live
  obtain ⟨r, hrb, _, hr_hi, _, heff_b⟩ := R16Rlp.eval_rlp_encode_bytes_bounded ent
    (vb + 40#64) (vb + 8#64) n0 [(locN s "vbuf", 96)]
    hc hs_ent.1.1
    (by unfold ent callEntryStateHOLFinite; dsimp only; exact hc1)
    (by unfold ent callEntryStateHOLFinite; dsimp only; exact hc2)
    (by unfold ent callEntryStateHOLFinite; dsimp only; exact hc3)
    (Nat.le_trans hn0_le (by decide))
    ⟨(locN s "vbuf", 96), by simp, by rw [hdst_nat, hvb_nat]; omega, by rw [hdst_nat, hvb_nat]; omega⟩
    (by rw [hb]; simp)
    (by rw [hb]; exact Or.inl ⟨v, rfl⟩)
  rw [hb] at hrb heff_b; dsimp only at hrb heff_b
  have hv_eq : v = .val (.word r) := by injection hrb with hr'; injection hr'
  subst hv_eq
  have heff_w : R16Shards.WorldEff ent post [(locN s "vbuf", 96)] [] [] :=
    worldEff_of_p26ByteEff_csr (R16Shards.WorldEff.refl ent [(locN s "vbuf", 96)] [] [] hs_ent.1 hc) heff_b
      (fun iv hiv _ => Or.inl ⟨iv, hiv, le_rfl, le_rfl⟩)
  have hpost_live : CsrLiveBufsAt post (locN s "cache") (locN s "new_roots") (locN s "mpt") [(locN s "vbuf", 96)] :=
    worldEff_csrLiveBufsAt hs_ent (by decide) (by decide) heff_w
      (fun iv hiv _ => ⟨iv, hiv, le_rfl, le_rfl⟩)
  let mid := setVarHOLFinite (ofString "w") (.val (.word r)) { post with locals := s.locals }
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · have hc_mid : locN mid "cache" = locN s "cache" := locN_setVar_ne _ "cache" (ofString "w") _ (by decide)
    have hr_mid : locN mid "new_roots" = locN s "new_roots" := locN_setVar_ne _ "new_roots" (ofString "w") _ (by decide)
    have hm_mid : locN mid "mpt" = locN s "mpt" := locN_setVar_ne _ "mpt" (ofString "w") _ (by decide)
    have hv_mid : locN mid "vbuf" = locN s "vbuf" := locN_setVar_ne _ "vbuf" (ofString "w") _ (by decide)
    show CsrMptBufs "mpt" [("vbuf", 96)] mid
    unfold CsrMptBufs
    simp only [List.map_cons, List.map_nil, hc_mid, hr_mid, hm_mid, hv_mid]
    exact localsFree_csrLiveBufsAt _ _ _ _ post mid.locals mid.clock hpost_live
  · obtain ⟨wp, hwp, hwp0⟩ := hs.1.2
    refine ⟨wp, ?_, hwp0⟩
    simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hwp,
      show ofString "pass" ≠ ofString "w" by decide, show ofString "w" ≠ ofString "pass" by decide]
  · show locN mid "w" ≤ 33
    rw [locN_setVar_same]; omega
  · show locN mid "n" ≤ 32
    rw [locN_setVar_ne _ "n" (ofString "w") _ (by decide)]; exact hs.2

def CsrCacheAt {F : Type} (s : PanSemStateFiniteExact 64 F) (cache : Nat) : Prop :=
  ArenaReady s ∧ ∃ S Nd,
    WorldTypedWith s S Nd ∧ cache ∈ S ∧
    ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ cache

def CsrCache : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => CsrCacheAt s (locN s "cache")

theorem localsFree_csrCacheAt (cache : Nat) :
    LocalsFree (fun s => CsrCacheAt s cache) := by
  intro F s locals k h
  obtain ⟨hA, S, Nd, hW, hc, hcl⟩ := h
  exact ⟨localsFree_arenaReady s locals k hA, S, Nd,
    (worldTypedWith_with_locals_csr s locals k S Nd).2 hW, hc, hcl⟩

theorem decCall_htab_copy_entry_csr
    (fb_hc : TerminatingFunBoundedOn GuestInv (ofString "htab_copy") K.«htab_copy»)
    (wk_hc : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoidsIf (fun s => HtabWF s (locN s "t") ∧
          ∀ i ∈ htabFootprint s (locN s "t"), Allocated s i)
        (fun _ post w => htabFootprint post w)) (ofString "htab_copy"))
    (rt_hc : Returns ArenaReady (fun s post n => locN s "t" ≠ 0 ∧
        (HtabWF s (locN s "t") → (∀ i ∈ htabFootprint s (locN s "t"), Allocated s i) →
          HtabWF post n ∧ hdr post n 3 = hdr s (locN s "t") 3 ∧
          ∀ i ∈ htabFootprint post n, Inside i (globN s "heap_ptr") (globN post "heap_ptr")))
      (ofString "htab_copy"))
    {Bc : Nat} {cont : ProgHOL 64}
    (hcont : TerminatingProgBoundedOn CsrCache cont Bc) :
    TerminatingProgBoundedOn WorldOK
      (.decCall (ofString "cache") .one (ofString "htab_copy")
        [.load .one (.op .add [.var .global (ofString "bs"), .const (72#64)])] cont)
      (K.«htab_copy» + Bc + 1) := by
  refine TerminatingProgBoundedOn.decCall_on fb_hc (ofString "cache") .one _
    (callEntryOn_guestInv_csr (fun _ hs => hs.1.1) _ _) ?_ hcont
  intro F s vs body callee ret v post hc hs ha hl hb
  obtain ⟨v1, he1, hc1, _⟩ := callee_param_one_exp_csr s (ofString "htab_copy")
    (ofString "t") .one (sourceFnBody Guest.Software.guestFn_htab_copy) .one
    (hc ▸ lookup_htab_copy_csr)
    (.load .one (.op .add [.var .global (ofString "bs"), .const (72#64)]))
    vs body callee ret ha hl
  obtain ⟨tw, rfl, htw_nat, hbs_nz⟩ :=
    evalAt_loadG_nz s hs.1.1 "bs" 72#64 (by rw [sourceBase_val]; decide) v1 he1
  let ent := callEntryStateHOLFinite s callee
  have ht_ent : locN ent "t" = memW s (globN s "bs" + 72) := by
    unfold locN ent callEntryStateHOLFinite; dsimp only; rw [hc1]; exact htw_nat
  have hA_ent : ArenaReady ent := localsFree_arenaReady s callee _ hs.1
  have hWOK_ent : WorldOK ent := localsFree_worldOK s callee _ hs
  have hret := FunSpec.at_lookup rt_hc s hc vs body callee ret hl hA_ent (by rw [hb]; simp)
  rw [hb] at hret
  have hstep0 := FunSpec.at_lookup wk_hc s hc vs body callee ret hl hWOK_ent (by rw [hb]; simp)
  rw [hb] at hstep0
  have hstep := hstep0 (Or.inl ⟨v, rfl⟩)
  obtain ⟨_, _, _, _, ht_nz, _⟩ := hret v rfl
  obtain ⟨S, hWT⟩ := hs.2
  obtain ⟨Nd, hW0⟩ := (worldTyped_iff_with s S).1 hWT
  have hW_ent : WorldTypedWith ent S Nd := (worldTypedWith_with_locals_csr s callee _ S Nd).2 hW0
  have hslot : memW ent (globN ent "bs" + 72) = 0 ∨ memW ent (globN ent "bs" + 72) ∈ S :=
    hW_ent.1.2.2.2.2.1 72 (by simp [bsTableSlots]) hbs_nz
  have ht_in_S : locN ent "t" ∈ S := by
    change memW s (globN s "bs" + 72) = 0 ∨ memW s (globN s "bs" + 72) ∈ S at hslot
    rw [← ht_ent] at hslot
    exact hslot.resolve_left ht_nz
  have hwf_t := hW_ent.1.2.1 (locN ent "t") ht_in_S
  have harg : HtabWF ent (locN ent "t") ∧ ∀ i ∈ htabFootprint ent (locN ent "t"), Allocated ent i :=
    ⟨hwf_t.1, fun i hi => (hwf_t.2 i hi).1⟩
  obtain ⟨w, S', Nd', rfl, _, hW_post, _, _, hlocal, _⟩ :=
    htabCopy_local_table_csr hA_ent hW_ent harg hstep hret
  let mid := setVarHOLFinite (ofString "cache") (.val (.word w)) { post with locals := s.locals }
  have hc_mid : locN mid "cache" = w.toNat := locN_setVar_same _ "cache" w
  show CsrCache mid
  unfold CsrCache; rw [hc_mid]
  exact localsFree_csrCacheAt w.toNat post mid.locals mid.clock
    ⟨hstep.1, S' ++ [w.toNat], Nd', hW_post, by simp, hlocal⟩

theorem decCall_htab_new_entry_csr
    (fb_hn : TerminatingFunBoundedOn GuestInv (ofString "htab_new") K.«htab_new»)
    (hn_spec : type_of% @htab_new_spec)
    {Bc : Nat} {cont : ProgHOL 64}
    (hcont : TerminatingProgBoundedOn CsrTabs cont Bc) :
    TerminatingProgBoundedOn CsrCache
      (.decCall (ofString "new_roots") .one (ofString "htab_new")
        [.const (20#64), .const (64#64)] cont)
      (K.«htab_new» + Bc + 1) := by
  refine TerminatingProgBoundedOn.decCall_on fb_hn (ofString "new_roots") .one _
    (callEntryOn_guestInv_csr (fun _ hs => hs.1.1) _ _) ?_ hcont
  intro F s vs body callee ret v post hc hs ha hl hb
  obtain ⟨v1, v2, he1, he2, hc1, hc2, _⟩ := callee_param_two_exp_csr s (ofString "htab_new")
    (ofString "key_len") (ofString "cap") .one .one
    (sourceFnBody Guest.Software.guestFn_htab_new) .one
    (hc ▸ lookup_htab_new_fn) (.const (20#64)) (.const (64#64)) vs body callee ret ha hl
  have hv1 : v1 = .val (.word (20#64)) := by simp [evalAt, evalHOLExact] at he1; exact he1.symm
  have hv2 : v2 = .val (.word (64#64)) := by simp [evalAt, evalHOLExact] at he2; exact he2.symm
  subst hv1; subst hv2
  let ent := callEntryStateHOLFinite s callee
  have hkl_ent : locN ent "key_len" = 20 := by
    unfold locN ent callEntryStateHOLFinite; dsimp only; rw [hc1]; decide
  have hcap_ent : locN ent "cap" = 64 := by
    unfold locN ent callEntryStateHOLFinite; dsimp only; rw [hc2]; decide
  obtain ⟨hA0, S, Nd, hW0, hc_S, hcl⟩ := hs
  have hA_ent : ArenaReady ent := localsFree_arenaReady s callee _ hA0
  have hready : HtabNewReady ent :=
    ⟨hA_ent, by rw [hkl_ent]; decide, by rw [hcap_ent]; decide⟩
  have hexit := FunSpec.at_lookup hn_spec s hc vs body callee ret hl hready (by rw [hb]; simp)
  rw [hb] at hexit
  have hW_ent : WorldTypedWith ent S Nd := (worldTypedWith_with_locals_csr s callee _ S Nd).2 hW0
  have hmeta := (evaluateHOLFiniteState_metadata ent body).2.2.1
  rw [hb] at hmeta
  obtain ⟨w, rfl, hAp, _, hnotS, _, _, _, hrl, hW_post, hwrs, hjrs, _, _, _⟩ :=
    htabNewExit_local_table_csr hA_ent hW_ent hmeta hexit
  have hne_cr : locN s "cache" ≠ w.toNat := fun heq => hnotS (heq ▸ hc_S)
  have hcl_post : ∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ locN s "cache" := by
    rw [hwrs, hjrs]; exact hcl
  have htabs_post : CsrTablesAt post (locN s "cache") w.toNat :=
    ⟨hAp, hne_cr, S ++ [w.toNat], Nd, hW_post, List.mem_append_left _ hc_S,
     by simp, hcl_post, hrl⟩
  let mid := setVarHOLFinite (ofString "new_roots") (.val (.word w)) { post with locals := s.locals }
  have hc_mid : locN mid "cache" = locN s "cache" :=
    locN_setVar_ne _ "cache" (ofString "new_roots") _ (by decide)
  have hr_mid : locN mid "new_roots" = w.toNat :=
    locN_setVar_same _ "new_roots" w
  show CsrTabs mid
  unfold CsrTabs; rw [hc_mid, hr_mid]
  exact localsFree_csrTablesAt _ _ post mid.locals mid.clock htabs_post

private theorem seq_return_ne_none_csr {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p : ProgHOL 64) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.seq p (.return e))).1 ≠ none := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hr : evaluateHOLFiniteState s p with ⟨r, mid⟩
  dsimp only
  cases r with
  | none => exact return_ne_none mid e
  | some _ => simp

theorem pBounded_csr_final_mpt_root
    (g_mr : TerminatingFunBoundedOn MptObjReady (ofString "mpt_root") K.«mpt_root») :
    PBounded (CsrMptBufs "state_mpt" [])
      (.seq
        (.call (some (none, none)) (ofString "mpt_root")
          [.var .local (ofString "state_mpt"), .var .local (ofString "out")])
        (.return (.const (0#64))))
      (K.«mpt_root» + 1) := by
  have hentry : CallEntryOn (CsrMptBufs "state_mpt" []) MptObjReady (ofString "mpt_root")
      [.var .local (ofString "state_mpt"), .var .local (ofString "out")] := by
    intro F s vs body callee ret hc hs ha hl
    obtain ⟨v1, _, he1, _, hc1, _, _⟩ := callee_param_two_exp_csr s (ofString "mpt_root")
      (ofString "m") (ofString "out") .one .one
      (sourceFnBody Guest.Software.guestFn_mpt_root) .one
      (hc ▸ lookup_mpt_root_csr)
      (.var .local (ofString "state_mpt")) (.var .local (ofString "out"))
      vs body callee ret ha hl
    let ent := callEntryStateHOLFinite s callee
    have hm_eq : locN ent "m" = locN s "state_mpt" := by
      unfold locN ent callEntryStateHOLFinite; dsimp only; rw [hc1]
      simp only [evalAt, evalHOLExact] at he1; rw [← he1]
    have hs_ent : CsrLiveBufsAt ent (locN s "cache") (locN s "new_roots") (locN ent "m") [] := by
      rw [hm_eq]; exact localsFree_csrLiveBufsAt _ _ _ _ s callee _ hs
    exact csrLiveBufsAt_mptObjReady hs_ent
  refine ⟨TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.seq_guestInv_after
      (TerminatingProgBoundedOn.call_on g_mr none
        [.var .local (ofString "state_mpt"), .var .local (ofString "out")] hentry)
      (fun _ hs => (csrMptBufs_worldOK "state_mpt" [] hs).1.1)
      (TerminatingProgBoundedOn.of_clock (fun s => clock_return s (.const (0#64)))))
    (by omega),
    ⟨fun s _ _ _ hr => absurd hr (seq_return_ne_none_csr s _ _)⟩⟩

theorem pBounded_csr_j_loop
    (fb_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (fb_htab_item : TerminatingFunBoundedOn GuestInv (ofString "htab_item") K.«htab_item»)
    (fb_memcpy : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»)
    (g_mpt_set : TerminatingFunBoundedOn MptSetReady (ofString "mpt_set") K.«mpt_set»)
    (fb_rlp_encode_bytes : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_bytes") K.«rlp_encode_bytes»)
    (fb_u256_is_zero : TerminatingFunBoundedOn GuestInv (ofString "u256_is_zero") K.«u256_is_zero»)
    (fb_u256_to_be_min : TerminatingFunBoundedOn GuestInv (ofString "u256_to_be_min") K.«u256_to_be_min»)
    (ro_htab_item : ReadOnlyFn (ofString "htab_item"))
    (mk_mpt_set : MptKeeps MptSetReady
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (ofString "mpt_set"))
    (ro_u256_is_zero : ReadOnlyFn (ofString "u256_is_zero"))
    (rv_u256_to_be_min : RetLe (fun _ => 32) (ofString "u256_to_be_min")) :
    PBounded (CsrMptBufs "mpt" [("vbuf", 96)])
      (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "icount")))
        (.decCall (ofString "e") (.comb [.one, .one, .one]) (ofString "htab_item")
          [.var .local (ofString "inner"), .var .local (ofString "j")]
          (.seq
            (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "e"))) (.const (0#64)))
              (.dec (ofString "v") (.comb [.one, .one, .one, .one])
                (.load (.comb [.one, .one, .one, .one]) (.rfield 2 (.var .local (ofString "e"))))
                (.decCall (ofString "z") .one (ofString "u256_is_zero")
                  [.var .local (ofString "v")]
                  (.seq
                    (.ite (.op .and
                      [.cmp .notEqual (.const (0#64))
                        (.cmp .equal (.var .local (ofString "pass")) (.const (0#64))),
                       .cmp .notEqual (.const (0#64))
                        (.cmp .equal (.var .local (ofString "z")) (.const (0#64)))])
                      (.decCall (ofString "n") .one (ofString "u256_to_be_min")
                        [.var .local (ofString "v"),
                         .op .add [.var .local (ofString "vbuf"), .const (8#64)]]
                        (.decCall (ofString "w") .one (ofString "rlp_encode_bytes")
                          [.op .add [.var .local (ofString "vbuf"), .const (8#64), .const (32#64)],
                           .op .add [.var .local (ofString "vbuf"), .const (8#64)],
                           .var .local (ofString "n")]
                          (.decCall (ofString "enc") .one (ofString "alloc") [.const (40#64)]
                            (.seq
                              (.call (some (none, none)) (ofString "memcpy")
                                [.var .local (ofString "enc"),
                                 .op .add [.var .local (ofString "vbuf"), .const (40#64)],
                                 .var .local (ofString "w")])
                              (.call (some (none, none)) (ofString "mpt_set")
                                [.var .local (ofString "mpt"),
                                 .rfield 1 (.var .local (ofString "e")),
                                 .const (32#64),
                                 .var .local (ofString "enc"),
                                 .var .local (ofString "w")])))))
                      .skip)
                    (.ite (.op .and
                      [.cmp .notEqual (.const (0#64))
                        (.cmp .equal (.var .local (ofString "pass")) (.const (1#64))),
                       .cmp .notEqual (.const (0#64))
                        (.cmp .notEqual (.var .local (ofString "z")) (.const (0#64)))])
                      (.call (some (none, none)) (ofString "mpt_set")
                        [.var .local (ofString "mpt"),
                         .rfield 1 (.var .local (ofString "e")),
                         .const (32#64), .const (0#64), .const (0#64)])
                      .skip))))
              .skip)
            (.assign .local (ofString "j")
              (.op .add [.var .local (ofString "j"), .const (1#64)])))))
      ((2 ^ 64 + 1) *
        ((K.«htab_item» + 1) +
          Nat.max
            ((K.«u256_is_zero» + 1) +
              Nat.max
                ((K.«u256_to_be_min» + 1) + (K.«rlp_encode_bytes» + 1) +
                  (K.«alloc» + 1) + (K.«memcpy» + 1) + (K.«mpt_set» + 1))
                0 +
              Nat.max (K.«mpt_set» + 1) 0)
            0 + 1)) := by
  have hp0_yes : PBounded (CsrNonNeg "pass" (CsrMptBufs "mpt" [("vbuf", 96)]))
      (.decCall (ofString "n") .one (ofString "u256_to_be_min")
        [.var .local (ofString "v"),
         .op .add [.var .local (ofString "vbuf"), .const (8#64)]]
        (.decCall (ofString "w") .one (ofString "rlp_encode_bytes")
          [.op .add [.var .local (ofString "vbuf"), .const (8#64), .const (32#64)],
           .op .add [.var .local (ofString "vbuf"), .const (8#64)],
           .var .local (ofString "n")]
          (.decCall (ofString "enc") .one (ofString "alloc") [.const (40#64)]
            (.seq
              (.call (some (none, none)) (ofString "memcpy")
                [.var .local (ofString "enc"),
                 .op .add [.var .local (ofString "vbuf"), .const (40#64)],
                 .var .local (ofString "w")])
              (.call (some (none, none)) (ofString "mpt_set")
                [.var .local (ofString "mpt"),
                 .rfield 1 (.var .local (ofString "e")),
                 .const (32#64),
                 .var .local (ofString "enc"),
                 .var .local (ofString "w")])))))
      ((K.«u256_to_be_min» + 1) + (K.«rlp_encode_bytes» + 1) +
        (K.«alloc» + 1) + (K.«memcpy» + 1) + (K.«mpt_set» + 1)) :=
    pBounded_mono_bound_csr
      (pBounded_u256_to_be_min_csr fb_u256_to_be_min rv_u256_to_be_min
        (.var .local (ofString "v"))
        (pBounded_rlp_encode_bytes_flat_csr fb_rlp_encode_bytes
          (pBounded_alloc_csrBound_csrNonNeg_csrMptBufs fb_alloc "w" 33 "pass" "mpt" "enc"
            [("vbuf", 96)] (40#64) (by decide) (by decide) (by decide)
            (PBounded.seq
              (pBounded_memcpy_csr fb_memcpy
                (.op .add [.var .local (ofString "vbuf"), .const (40#64)]))
              (pBounded_mpt_set_bound_csrNonNeg_csrMptBufs g_mpt_set mk_mpt_set
                "w" 33 "pass" "mpt" [("enc", 40), ("vbuf", 96)]
                (.rfield 1 (.var .local (ofString "e")))
                (.var .local (ofString "enc")) (32#64)
                (by decide) (by decide))))
          (fun s hr => evaluate_avoidsLocal_flowing (ofString "n") _ (by decide) s (Or.inl hr))))
      (by omega)
  have hp0_ite :=
    pBounded_ite_yes_csr
      (.op .and
        [.cmp .notEqual (.const (0#64))
          (.cmp .equal (.var .local (ofString "pass")) (.const (0#64))),
         .cmp .notEqual (.const (0#64))
          (.cmp .equal (.var .local (ofString "z")) (.const (0#64)))])
      (fun s hs hc => ⟨hs, pass0_cond_nonNeg_csr s hc⟩)
      (fun _ ht => ht.1)
      hp0_yes PBounded.skip
  have hp1_ite :=
    PBounded.ite
      (.op .and
        [.cmp .notEqual (.const (0#64))
          (.cmp .equal (.var .local (ofString "pass")) (.const (1#64))),
         .cmp .notEqual (.const (0#64))
          (.cmp .notEqual (.var .local (ofString "z")) (.const (0#64)))])
      (pBounded_mpt_set_const_csrMptBufs g_mpt_set mk_mpt_set "mpt" [("vbuf", 96)]
        (.rfield 1 (.var .local (ofString "e"))) (.const (0#64))
        (32#64) (0#64) (by decide) (by decide))
      PBounded.skip
  have hj_yes : PBounded (CsrMptBufs "mpt" [("vbuf", 96)]) _
      ((K.«u256_is_zero» + 1) +
        Nat.max
          ((K.«u256_to_be_min» + 1) + (K.«rlp_encode_bytes» + 1) +
            (K.«alloc» + 1) + (K.«memcpy» + 1) + (K.«mpt_set» + 1))
          0 +
        Nat.max (K.«mpt_set» + 1) 0) :=
    pBounded_mono_bound_csr
      (PBounded.dec (localsOnly_csrMptBufs "mpt" [("vbuf", 96)]) (ofString "v") (by decide)
        (.comb [.one, .one, .one, .one])
        (.load (.comb [.one, .one, .one, .one]) (.rfield 2 (.var .local (ofString "e"))))
        (pBounded_roDecCall_csr fb_u256_is_zero ro_u256_is_zero
          (localsOnly_csrMptBufs "mpt" [("vbuf", 96)])
          (fun _ hs => (csrMptBufs_worldOK "mpt" [("vbuf", 96)] hs).1.1)
          (ofString "z") (by decide) .one [.var .local (ofString "v")]
          (PBounded.seq hp0_ite hp1_ite)))
      (by simp only [Nat.max_def]; repeat (first | split | omega))
  have hj_body : PBounded (CsrMptBufs "mpt" [("vbuf", 96)]) _
      ((K.«htab_item» + 1) +
        Nat.max
          ((K.«u256_is_zero» + 1) +
            Nat.max
              ((K.«u256_to_be_min» + 1) + (K.«rlp_encode_bytes» + 1) +
                (K.«alloc» + 1) + (K.«memcpy» + 1) + (K.«mpt_set» + 1))
              0 +
            Nat.max (K.«mpt_set» + 1) 0)
          0) :=
    pBounded_mono_bound_csr
      (pBounded_roDecCall_csr fb_htab_item ro_htab_item
        (localsOnly_csrMptBufs "mpt" [("vbuf", 96)])
        (fun _ hs => (csrMptBufs_worldOK "mpt" [("vbuf", 96)] hs).1.1)
        (ofString "e") (by decide) (.comb [.one, .one, .one])
        [.var .local (ofString "inner"), .var .local (ofString "j")]
        (PBounded.seq
          (PBounded.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "e"))) (.const (0#64)))
            hj_yes PBounded.skip)
          (PBounded.assignLocal (localsOnly_csrMptBufs "mpt" [("vbuf", 96)])
            (ofString "j") (by decide) (.op .add [.var .local (ofString "j"), .const (1#64)]))))
      (by simp only [Nat.max_def]; repeat (first | split | omega))
  exact PBounded.whileLess (localsOnly_csrMptBufs "mpt" [("vbuf", 96)])
    (ofString "j") (.var .local (ofString "icount")) hj_body
    (IncrBody.decCall _ _ _ _ (by decide) (IncrBody.seq _ (by decide) (by decide) IncrBody.incr))
    (by decide)

theorem pBounded_csr_loop1
    (fb_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (fb_htab_has : TerminatingFunBoundedOn GuestInv (ofString "htab_has") K.«htab_has»)
    (fb_htab_item : TerminatingFunBoundedOn GuestInv (ofString "htab_item") K.«htab_item»)
    (fb_htab_set : TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set»)
    (fb_memcpy : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»)
    (g_mpt_from_witness : TerminatingFunBoundedOn ArenaReady (ofString "mpt_from_witness") K.«mpt_from_witness»)
    (g_mpt_root : TerminatingFunBoundedOn MptObjReady (ofString "mpt_root") K.«mpt_root»)
    (g_mpt_set : TerminatingFunBoundedOn MptSetReady (ofString "mpt_set") K.«mpt_set»)
    (fb_rlp_encode_bytes : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_bytes") K.«rlp_encode_bytes»)
    (fb_u256_is_zero : TerminatingFunBoundedOn GuestInv (ofString "u256_is_zero") K.«u256_is_zero»)
    (fb_u256_to_be_min : TerminatingFunBoundedOn GuestInv (ofString "u256_to_be_min") K.«u256_to_be_min»)
    (fb_ws_storage_root_of : TerminatingFunBoundedOn GuestInv (ofString "ws_storage_root_of") K.«ws_storage_root_of»)
    (ro_htab_has : ReadOnlyFn (ofString "htab_has"))
    (ro_htab_item : ReadOnlyFn (ofString "htab_item"))
    (h_htab_set : type_of% @htab_set_spec)
    (wk_mpt_from_witness : WorldKeeps WorldOK (fun _ => []) ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetMptObj (ofString "mpt_from_witness"))
    (mk_mpt_root : MptKeeps MptObjReady
      (fun s => [(locN s "out", 32),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (ofString "mpt_root"))
    (mk_mpt_set : MptKeeps MptSetReady
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (ofString "mpt_set"))
    (ro_u256_is_zero : ReadOnlyFn (ofString "u256_is_zero"))
    (rv_u256_to_be_min : RetLe (fun _ => 32) (ofString "u256_to_be_min"))
    (wk_ws_storage_root_of : WorldKeeps WorldOK
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "ws_storage_root_of")) :
    PBounded CsrTabs
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "cap")))
        (.decCall (ofString "s") (.comb [.one, .one, .one]) (ofString "htab_item")
          [.var .local (ofString "sw"), .var .local (ofString "i")]
          (.seq
            (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s"))) (.const (0#64)))
              (.dec (ofString "addr") .one (.rfield 1 (.var .local (ofString "s")))
                (.dec (ofString "inner") .one (.rfield 2 (.var .local (ofString "s")))
                  (.decCall (ofString "has") .one (ofString "htab_has")
                    [.var .local (ofString "cache"), .var .local (ofString "addr")]
                    (.seq
                      (.ite (.cmp .equal (.var .local (ofString "has")) (.const (0#64)))
                        (.call (some (none, none)) (ofString "htab_set")
                          [.var .local (ofString "cache"), .var .local (ofString "addr"), .const (1#64)])
                        .skip)
                      (.decCall (ofString "old_root") .one (ofString "ws_storage_root_of")
                        [.var .local (ofString "addr")]
                        (.decCall (ofString "mpt") .one (ofString "mpt_from_witness")
                          [.var .local (ofString "nodedb"), .var .local (ofString "old_root"), .const (1#64)]
                          (.decCall (ofString "vbuf") .one (ofString "alloc") [.const (96#64)]
                            (.dec (ofString "pass") .one (.const (0#64))
                              (.seq
                                (.while (.cmp .less (.var .local (ofString "pass")) (.const (2#64)))
                                  (.dec (ofString "j") .one (.const (0#64))
                                    (.dec (ofString "icount") .one
                                      (.load .one (.op .add [.var .local (ofString "inner"), .const (24#64)]))
                                      (.seq
                                        (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "icount")))
                                          (.decCall (ofString "e") (.comb [.one, .one, .one]) (ofString "htab_item")
                                            [.var .local (ofString "inner"), .var .local (ofString "j")]
                                            (.seq
                                              (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "e"))) (.const (0#64)))
                                                (.dec (ofString "v") (.comb [.one, .one, .one, .one])
                                                  (.load (.comb [.one, .one, .one, .one]) (.rfield 2 (.var .local (ofString "e"))))
                                                  (.decCall (ofString "z") .one (ofString "u256_is_zero")
                                                    [.var .local (ofString "v")]
                                                    (.seq
                                                      (.ite (.op .and
                                                        [.cmp .notEqual (.const (0#64))
                                                          (.cmp .equal (.var .local (ofString "pass")) (.const (0#64))),
                                                         .cmp .notEqual (.const (0#64))
                                                          (.cmp .equal (.var .local (ofString "z")) (.const (0#64)))])
                                                        (.decCall (ofString "n") .one (ofString "u256_to_be_min")
                                                          [.var .local (ofString "v"),
                                                           .op .add [.var .local (ofString "vbuf"), .const (8#64)]]
                                                          (.decCall (ofString "w") .one (ofString "rlp_encode_bytes")
                                                            [.op .add [.var .local (ofString "vbuf"), .const (8#64), .const (32#64)],
                                                             .op .add [.var .local (ofString "vbuf"), .const (8#64)],
                                                             .var .local (ofString "n")]
                                                            (.decCall (ofString "enc") .one (ofString "alloc") [.const (40#64)]
                                                              (.seq
                                                                (.call (some (none, none)) (ofString "memcpy")
                                                                  [.var .local (ofString "enc"),
                                                                   .op .add [.var .local (ofString "vbuf"), .const (40#64)],
                                                                   .var .local (ofString "w")])
                                                                (.call (some (none, none)) (ofString "mpt_set")
                                                                  [.var .local (ofString "mpt"),
                                                                   .rfield 1 (.var .local (ofString "e")),
                                                                   .const (32#64),
                                                                   .var .local (ofString "enc"),
                                                                   .var .local (ofString "w")])))))
                                                        .skip)
                                                      (.ite (.op .and
                                                        [.cmp .notEqual (.const (0#64))
                                                          (.cmp .equal (.var .local (ofString "pass")) (.const (1#64))),
                                                         .cmp .notEqual (.const (0#64))
                                                          (.cmp .notEqual (.var .local (ofString "z")) (.const (0#64)))])
                                                        (.call (some (none, none)) (ofString "mpt_set")
                                                          [.var .local (ofString "mpt"),
                                                           .rfield 1 (.var .local (ofString "e")),
                                                           .const (32#64), .const (0#64), .const (0#64)])
                                                        .skip))))
                                                .skip)
                                              (.assign .local (ofString "j")
                                                (.op .add [.var .local (ofString "j"), .const (1#64)])))))
                                        (.assign .local (ofString "pass")
                                          (.op .add [.var .local (ofString "pass"), .const (1#64)]))))))
                                (.decCall (ofString "root") .one (ofString "alloc") [.const (32#64)]
                                  (.seq
                                    (.call (some (none, none)) (ofString "mpt_root")
                                      [.var .local (ofString "mpt"), .var .local (ofString "root")])
                                    (.call (some (none, none)) (ofString "htab_set")
                                      [.var .local (ofString "new_roots"), .var .local (ofString "addr"),
                                       .var .local (ofString "root")]))))))))))))
              .skip)
            (.assign .local (ofString "i")
              (.op .add [.var .local (ofString "i"), .const (1#64)])))))
      ((2 ^ 64 + 1) *
        ((K.«htab_item» + 1) +
          Nat.max
            ((K.«htab_has» + 1) + Nat.max (K.«htab_set» + 1) 0 +
              (K.«ws_storage_root_of» + 1) + (K.«mpt_from_witness» + 1) + (K.«alloc» + 1) +
              (2 ^ 64 + 1) *
                ((2 ^ 64 + 1) *
                  ((K.«htab_item» + 1) +
                    Nat.max
                      ((K.«u256_is_zero» + 1) +
                        Nat.max
                          ((K.«u256_to_be_min» + 1) + (K.«rlp_encode_bytes» + 1) +
                            (K.«alloc» + 1) + (K.«memcpy» + 1) + (K.«mpt_set» + 1))
                          0 +
                        Nat.max (K.«mpt_set» + 1) 0)
                      0 + 1) + 1) +
              (K.«alloc» + 1) + (K.«mpt_root» + 1) + (K.«htab_set» + 1))
            0 + 1)) := by
  have hj := pBounded_csr_j_loop fb_alloc fb_htab_item fb_memcpy g_mpt_set
    fb_rlp_encode_bytes fb_u256_is_zero fb_u256_to_be_min
    ro_htab_item mk_mpt_set ro_u256_is_zero rv_u256_to_be_min
  have hpass_body :=
    PBounded.dec (localsOnly_csrMptBufs "mpt" [("vbuf", 96)]) (ofString "j") (by decide)
      .one (.const (0#64))
      (PBounded.dec (localsOnly_csrMptBufs "mpt" [("vbuf", 96)]) (ofString "icount") (by decide)
        .one (.load .one (.op .add [.var .local (ofString "inner"), .const (24#64)]))
        (PBounded.seq hj
          (PBounded.assignLocal (localsOnly_csrMptBufs "mpt" [("vbuf", 96)])
            (ofString "pass") (by decide) (.op .add [.var .local (ofString "pass"), .const (1#64)]))))
  have hpass_loop :=
    PBounded.whileLess (localsOnly_csrMptBufs "mpt" [("vbuf", 96)])
      (ofString "pass") (.const (2#64)) hpass_body
      (IncrBody.dec _ _ _ (by decide)
        (IncrBody.dec _ _ _ (by decide)
          (IncrBody.seq _ (by decide) (by decide) IncrBody.incr)))
      (by decide)
  have hroot_tail :=
    pBounded_alloc_csrMptBufs fb_alloc "mpt" "root" [("vbuf", 96)] (32#64) (by decide)
      (PBounded.seq
        (pBounded_mpt_root_buf_csr g_mpt_root mk_mpt_root "mpt" "root" [("vbuf", 96)])
        (pBounded_htab_set_csrMptBufs fb_htab_set h_htab_set
          "mpt" [("root", 32), ("vbuf", 96)] "new_roots" (Or.inr rfl)
          (.var .local (ofString "addr")) (.var .local (ofString "root"))))
  have hi_yes : PBounded CsrTabs _
      ((K.«htab_has» + 1) + Nat.max (K.«htab_set» + 1) 0 +
        (K.«ws_storage_root_of» + 1) + (K.«mpt_from_witness» + 1) + (K.«alloc» + 1) +
        (2 ^ 64 + 1) *
          ((2 ^ 64 + 1) *
            ((K.«htab_item» + 1) +
              Nat.max
                ((K.«u256_is_zero» + 1) +
                  Nat.max
                    ((K.«u256_to_be_min» + 1) + (K.«rlp_encode_bytes» + 1) +
                      (K.«alloc» + 1) + (K.«memcpy» + 1) + (K.«mpt_set» + 1))
                    0 +
                  Nat.max (K.«mpt_set» + 1) 0)
                0 + 1) + 1) +
        (K.«alloc» + 1) + (K.«mpt_root» + 1) + (K.«htab_set» + 1)) :=
    pBounded_mono_bound_csr
      (PBounded.dec localsOnly_csrTabs (ofString "addr") (by decide)
        .one (.rfield 1 (.var .local (ofString "s")))
        (PBounded.dec localsOnly_csrTabs (ofString "inner") (by decide)
          .one (.rfield 2 (.var .local (ofString "s")))
          (pBounded_roDecCall_csr fb_htab_has ro_htab_has localsOnly_csrTabs
            (fun _ hs => (csrTabs_worldOK hs).1.1) (ofString "has") (by decide) .one
            [.var .local (ofString "cache"), .var .local (ofString "addr")]
            (PBounded.seq
              (PBounded.ite (.cmp .equal (.var .local (ofString "has")) (.const (0#64)))
                (pBounded_htab_set_csrTabs fb_htab_set h_htab_set "cache" (Or.inl rfl)
                  (.var .local (ofString "addr")) (.const (1#64)))
                PBounded.skip)
              (pBounded_ws_storage_root_of_csrTabs fb_ws_storage_root_of wk_ws_storage_root_of
                (name := ofString "old_root") (args := [.var .local (ofString "addr")]) (by decide)
                (pBounded_mpt_from_witness_csr g_mpt_from_witness wk_mpt_from_witness
                  "mpt" (args := [.var .local (ofString "nodedb"), .var .local (ofString "old_root"), .const (1#64)])
                  (by decide)
                  (pBounded_alloc_csrMptBufs fb_alloc "mpt" "vbuf" [] (96#64) (by decide)
                    (PBounded.dec (localsOnly_csrMptBufs "mpt" [("vbuf", 96)])
                      (ofString "pass") (by decide) .one (.const (0#64))
                      (PBounded.seq hpass_loop hroot_tail)))))))))
      (by
        simp only [show ∀ a b : Nat, Nat.max a b = max a b from fun _ _ => rfl,
          Nat.max_zero, Nat.zero_max]
        omega)
  have hi_body : PBounded CsrTabs _
      ((K.«htab_item» + 1) +
        Nat.max
          ((K.«htab_has» + 1) + Nat.max (K.«htab_set» + 1) 0 +
            (K.«ws_storage_root_of» + 1) + (K.«mpt_from_witness» + 1) + (K.«alloc» + 1) +
            (2 ^ 64 + 1) *
              ((2 ^ 64 + 1) *
                ((K.«htab_item» + 1) +
                  Nat.max
                    ((K.«u256_is_zero» + 1) +
                      Nat.max
                        ((K.«u256_to_be_min» + 1) + (K.«rlp_encode_bytes» + 1) +
                          (K.«alloc» + 1) + (K.«memcpy» + 1) + (K.«mpt_set» + 1))
                        0 +
                      Nat.max (K.«mpt_set» + 1) 0)
                    0 + 1) + 1) +
            (K.«alloc» + 1) + (K.«mpt_root» + 1) + (K.«htab_set» + 1))
          0) :=
    pBounded_mono_bound_csr
      (pBounded_roDecCall_csr fb_htab_item ro_htab_item localsOnly_csrTabs
        (fun _ hs => (csrTabs_worldOK hs).1.1) (ofString "s") (by decide) (.comb [.one, .one, .one])
        [.var .local (ofString "sw"), .var .local (ofString "i")]
        (PBounded.seq
          (PBounded.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s"))) (.const (0#64)))
            hi_yes PBounded.skip)
          (PBounded.assignLocal localsOnly_csrTabs (ofString "i") (by decide)
            (.op .add [.var .local (ofString "i"), .const (1#64)]))))
      (by
        simp only [show ∀ a b : Nat, Nat.max a b = max a b from fun _ _ => rfl,
          Nat.max_zero, Nat.zero_max]
        omega)
  exact PBounded.whileLess localsOnly_csrTabs (ofString "i") (.var .local (ofString "cap"))
    hi_body
    (IncrBody.decCall _ _ _ _ (by decide) (IncrBody.seq _ (by decide) (by decide) IncrBody.incr))
    (by decide)

theorem pBounded_csr_loop2
    (fb_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (fb_encode_account : TerminatingFunBoundedOn GuestInv (ofString "encode_account") K.«encode_account»)
    (fb_htab_get : TerminatingFunBoundedOn GuestInv (ofString "htab_get") K.«htab_get»)
    (fb_htab_has : TerminatingFunBoundedOn GuestInv (ofString "htab_has") K.«htab_has»)
    (fb_htab_item : TerminatingFunBoundedOn GuestInv (ofString "htab_item") K.«htab_item»)
    (fb_htab_set : TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set»)
    (g_mpt_set : TerminatingFunBoundedOn MptSetReady (ofString "mpt_set") K.«mpt_set»)
    (fb_ws_get_account_optional : TerminatingFunBoundedOn GuestInv (ofString "ws_get_account_optional") K.«ws_get_account_optional»)
    (ro_htab_get : ReadOnlyFn (ofString "htab_get"))
    (ro_htab_has : ReadOnlyFn (ofString "htab_has"))
    (ro_htab_item : ReadOnlyFn (ofString "htab_item"))
    (h_htab_set : type_of% @htab_set_spec)
    (mk_mpt_set : MptKeeps MptSetReady
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (ofString "mpt_set")) :
    PBounded (CsrMptBufs "state_mpt" [])
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "cap")))
        (.decCall (ofString "s2") (.comb [.one, .one, .one]) (ofString "htab_item")
          [.var .local (ofString "sw"), .var .local (ofString "i")]
          (.seq
            (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s2"))) (.const (0#64)))
              (.decCall (ofString "inaw") .one (ofString "htab_has")
                [.var .local (ofString "aw"), .rfield 1 (.var .local (ofString "s2"))]
                (.ite (.cmp .equal (.var .local (ofString "inaw")) (.const (0#64)))
                  (.decCall (ofString "a") .one (ofString "ws_get_account_optional")
                    [.rfield 1 (.var .local (ofString "s2"))]
                    (.seq
                      (.call (some (none, none)) (ofString "htab_set")
                        [.var .local (ofString "cache"), .rfield 1 (.var .local (ofString "s2")), .const (1#64)])
                      (.ite (.cmp .notEqual (.var .local (ofString "a")) (.const (1#64)))
                        (.decCall (ofString "nr") (.comb [.one, .one]) (ofString "htab_get")
                          [.var .local (ofString "new_roots"), .rfield 1 (.var .local (ofString "s2"))]
                          (.dec (ofString "sr") .one (.var .global (ofString "empty_trie_root"))
                            (.seq
                              (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "nr"))) (.const (0#64)))
                                (.assign .local (ofString "sr") (.rfield 1 (.var .local (ofString "nr"))))
                                .skip)
                              (.decCall (ofString "enc") .one (ofString "alloc") [.const (128#64)]
                                (.decCall (ofString "n") .one (ofString "encode_account")
                                  [.load .one (.op .add [.var .local (ofString "a"), .const (0#64)]),
                                   .load (.comb [.one, .one, .one, .one])
                                     (.op .add [.var .local (ofString "a"), .const (8#64)]),
                                   .var .local (ofString "sr"),
                                   .load .one (.op .add [.var .local (ofString "a"), .const (48#64)]),
                                   .var .local (ofString "enc")]
                                  (.call (some (none, none)) (ofString "mpt_set")
                                    [.var .local (ofString "state_mpt"),
                                     .rfield 1 (.var .local (ofString "s2")),
                                     .const (20#64),
                                     .var .local (ofString "enc"),
                                     .var .local (ofString "n")]))))))
                        .skip)))
                  .skip))
              .skip)
            (.assign .local (ofString "i")
              (.op .add [.var .local (ofString "i"), .const (1#64)])))))
      ((2 ^ 64 + 1) *
        ((K.«htab_item» + 1) +
          Nat.max
            ((K.«htab_has» + 1) +
              Nat.max
                ((K.«ws_get_account_optional» + 1) + (K.«htab_set» + 1) +
                  Nat.max
                    ((K.«htab_get» + 1) + (K.«alloc» + 1) +
                      (K.«encode_account» + 1) + (K.«mpt_set» + 1))
                    0)
                0)
            0 + 1)) := by
  have ha_yes : PBounded (CsrMptBufs "state_mpt" [])
      (.decCall (ofString "nr") (.comb [.one, .one]) (ofString "htab_get")
        [.var .local (ofString "new_roots"), .rfield 1 (.var .local (ofString "s2"))]
        (.dec (ofString "sr") .one (.var .global (ofString "empty_trie_root"))
          (.seq
            (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "nr"))) (.const (0#64)))
              (.assign .local (ofString "sr") (.rfield 1 (.var .local (ofString "nr"))))
              .skip)
            (.decCall (ofString "enc") .one (ofString "alloc") [.const (128#64)]
              (.decCall (ofString "n") .one (ofString "encode_account")
                [.load .one (.op .add [.var .local (ofString "a"), .const (0#64)]),
                 .load (.comb [.one, .one, .one, .one])
                   (.op .add [.var .local (ofString "a"), .const (8#64)]),
                 .var .local (ofString "sr"),
                 .load .one (.op .add [.var .local (ofString "a"), .const (48#64)]),
                 .var .local (ofString "enc")]
                (.call (some (none, none)) (ofString "mpt_set")
                  [.var .local (ofString "state_mpt"),
                   .rfield 1 (.var .local (ofString "s2")),
                   .const (20#64),
                   .var .local (ofString "enc"),
                   .var .local (ofString "n")]))))))
      ((K.«htab_get» + 1) + (K.«alloc» + 1) +
        (K.«encode_account» + 1) + (K.«mpt_set» + 1)) :=
    pBounded_mono_bound_csr
      (pBounded_roDecCall_csr fb_htab_get ro_htab_get
        (localsOnly_csrMptBufs "state_mpt" [])
        (fun _ hs => (csrMptBufs_worldOK "state_mpt" [] hs).1.1)
        (ofString "nr") (by decide) (.comb [.one, .one])
        [.var .local (ofString "new_roots"), .rfield 1 (.var .local (ofString "s2"))]
        (PBounded.dec (localsOnly_csrMptBufs "state_mpt" []) (ofString "sr") (by decide) .one
          (.var .global (ofString "empty_trie_root"))
          (PBounded.seq
            (PBounded.ite
              (.cmp .notEqual (.rfield 0 (.var .local (ofString "nr"))) (.const (0#64)))
              (PBounded.assignLocal (localsOnly_csrMptBufs "state_mpt" [])
                (ofString "sr") (by decide) (.rfield 1 (.var .local (ofString "nr"))))
              PBounded.skip)
            (pBounded_alloc_csrMptBufs fb_alloc "state_mpt" "enc" [] (128#64) (by decide)
              (pBounded_encode_account_csr fb_encode_account "state_mpt" "enc" "n"
                (.load .one (.op .add [.var .local (ofString "a"), .const (0#64)]))
                (.load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "a"), .const (8#64)]))
                (.var .local (ofString "sr"))
                (.load .one (.op .add [.var .local (ofString "a"), .const (48#64)]))
                (by decide)
                (pBounded_mpt_set_bound_csrMptBufs g_mpt_set mk_mpt_set
                  "n" 110 "state_mpt" [("enc", 128)]
                  (.rfield 1 (.var .local (ofString "s2")))
                  (.var .local (ofString "enc"))
                  (20#64)
                  (by decide) (by decide)))))))
      (by simp only [Nat.max_def]; repeat (first | split | omega))
  have hinaw_yes : PBounded (CsrMptBufs "state_mpt" []) _
      ((K.«ws_get_account_optional» + 1) + (K.«htab_set» + 1) +
        Nat.max
          ((K.«htab_get» + 1) + (K.«alloc» + 1) +
            (K.«encode_account» + 1) + (K.«mpt_set» + 1))
          0) :=
    pBounded_mono_bound_csr
      (pBounded_ws_get_account_optional_csrMptBufs fb_ws_get_account_optional
        "state_mpt" "a" (.rfield 1 (.var .local (ofString "s2"))) (by decide)
        (PBounded.seq
          (pBounded_htab_set_csrMptBufs fb_htab_set h_htab_set
            "state_mpt" [] "cache" (Or.inl rfl)
            (.rfield 1 (.var .local (ofString "s2"))) (.const (1#64)))
          (PBounded.ite (.cmp .notEqual (.var .local (ofString "a")) (.const (1#64)))
            ha_yes PBounded.skip)))
      (by simp only [Nat.max_def]; repeat (first | split | omega))
  have hs2_yes : PBounded (CsrMptBufs "state_mpt" []) _
      ((K.«htab_has» + 1) +
        Nat.max
          ((K.«ws_get_account_optional» + 1) + (K.«htab_set» + 1) +
            Nat.max
              ((K.«htab_get» + 1) + (K.«alloc» + 1) +
                (K.«encode_account» + 1) + (K.«mpt_set» + 1))
              0)
          0) :=
    pBounded_mono_bound_csr
      (pBounded_roDecCall_csr fb_htab_has ro_htab_has
        (localsOnly_csrMptBufs "state_mpt" [])
        (fun _ hs => (csrMptBufs_worldOK "state_mpt" [] hs).1.1)
        (ofString "inaw") (by decide) .one
        [.var .local (ofString "aw"), .rfield 1 (.var .local (ofString "s2"))]
        (PBounded.ite (.cmp .equal (.var .local (ofString "inaw")) (.const (0#64)))
          hinaw_yes PBounded.skip))
      (by simp only [Nat.max_def]; repeat (first | split | omega))
  have hbody : PBounded (CsrMptBufs "state_mpt" []) _
      ((K.«htab_item» + 1) +
        Nat.max
          ((K.«htab_has» + 1) +
            Nat.max
              ((K.«ws_get_account_optional» + 1) + (K.«htab_set» + 1) +
                Nat.max
                  ((K.«htab_get» + 1) + (K.«alloc» + 1) +
                    (K.«encode_account» + 1) + (K.«mpt_set» + 1))
                  0)
              0)
          0) :=
    pBounded_mono_bound_csr
      (pBounded_roDecCall_csr fb_htab_item ro_htab_item
        (localsOnly_csrMptBufs "state_mpt" [])
        (fun _ hs => (csrMptBufs_worldOK "state_mpt" [] hs).1.1)
        (ofString "s2") (by decide) (.comb [.one, .one, .one])
        [.var .local (ofString "sw"), .var .local (ofString "i")]
        (PBounded.seq
          (PBounded.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s2"))) (.const (0#64)))
            hs2_yes PBounded.skip)
          (PBounded.assignLocal (localsOnly_csrMptBufs "state_mpt" [])
            (ofString "i") (by decide) (.op .add [.var .local (ofString "i"), .const (1#64)]))))
      (by simp only [Nat.max_def]; repeat (first | split | omega))
  exact PBounded.whileLess (localsOnly_csrMptBufs "state_mpt" [])
    (ofString "i") (.var .local (ofString "cap")) hbody
    (IncrBody.decCall _ _ _ _ (by decide) (IncrBody.seq _ (by decide) (by decide) IncrBody.incr))
    (by decide)

theorem pBounded_csr_loop3
    (fb_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (fb_cache_get_root : TerminatingFunBoundedOn GuestInv (ofString "cache_get_root") K.«cache_get_root»)
    (fb_encode_account : TerminatingFunBoundedOn GuestInv (ofString "encode_account") K.«encode_account»)
    (fb_htab_get : TerminatingFunBoundedOn GuestInv (ofString "htab_get") K.«htab_get»)
    (fb_htab_item : TerminatingFunBoundedOn GuestInv (ofString "htab_item") K.«htab_item»)
    (g_mpt_set : TerminatingFunBoundedOn MptSetReady (ofString "mpt_set") K.«mpt_set»)
    (ro_htab_get : ReadOnlyFn (ofString "htab_get"))
    (ro_htab_item : ReadOnlyFn (ofString "htab_item"))
    (mk_mpt_set : MptKeeps MptSetReady
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (ofString "mpt_set")) :
    PBounded (CsrMptBufs "state_mpt" [])
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "acap")))
        (.decCall (ofString "s3") (.comb [.one, .one, .one]) (ofString "htab_item")
          [.var .local (ofString "aw"), .var .local (ofString "i")]
          (.seq
            (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s3"))) (.const (0#64)))
              (.dec (ofString "addr3") .one (.rfield 1 (.var .local (ofString "s3")))
                (.dec (ofString "acct") .one (.rfield 2 (.var .local (ofString "s3")))
                  (.ite (.cmp .equal (.var .local (ofString "acct")) (.const (1#64)))
                    (.call (some (none, none)) (ofString "mpt_set")
                      [.var .local (ofString "state_mpt"),
                       .var .local (ofString "addr3"),
                       .const (20#64), .const (0#64), .const (0#64)])
                    (.decCall (ofString "nr2") (.comb [.one, .one]) (ofString "htab_get")
                      [.var .local (ofString "new_roots"), .var .local (ofString "addr3")]
                      (.dec (ofString "sr2") .one (.const (0#64))
                        (.seq
                          (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "nr2"))) (.const (0#64)))
                            (.assign .local (ofString "sr2") (.rfield 1 (.var .local (ofString "nr2"))))
                            (.call (some (some (.local, ofString "sr2"), none)) (ofString "cache_get_root")
                              [.var .local (ofString "cache"), .var .local (ofString "addr3")]))
                          (.decCall (ofString "enc2") .one (ofString "alloc") [.const (128#64)]
                            (.decCall (ofString "n2") .one (ofString "encode_account")
                              [.load .one (.op .add [.var .local (ofString "acct"), .const (0#64)]),
                               .load (.comb [.one, .one, .one, .one])
                                 (.op .add [.var .local (ofString "acct"), .const (8#64)]),
                               .var .local (ofString "sr2"),
                               .load .one (.op .add [.var .local (ofString "acct"), .const (48#64)]),
                               .var .local (ofString "enc2")]
                              (.call (some (none, none)) (ofString "mpt_set")
                                [.var .local (ofString "state_mpt"),
                                 .var .local (ofString "addr3"),
                                 .const (20#64),
                                 .var .local (ofString "enc2"),
                                 .var .local (ofString "n2")])))))))))
              .skip)
            (.assign .local (ofString "i")
              (.op .add [.var .local (ofString "i"), .const (1#64)])))))
      ((2 ^ 64 + 1) *
        ((K.«htab_item» + 1) +
          Nat.max
            (Nat.max (K.«mpt_set» + 1)
              ((K.«htab_get» + 1) + Nat.max 0 (K.«cache_get_root» + 1) +
                (K.«alloc» + 1) + (K.«encode_account» + 1) + (K.«mpt_set» + 1)))
            0 + 1)) := by
  have hacct_no : PBounded (CsrMptBufs "state_mpt" []) _
      ((K.«htab_get» + 1) + Nat.max 0 (K.«cache_get_root» + 1) +
        (K.«alloc» + 1) + (K.«encode_account» + 1) + (K.«mpt_set» + 1)) :=
    pBounded_mono_bound_csr
      (pBounded_roDecCall_csr fb_htab_get ro_htab_get
        (localsOnly_csrMptBufs "state_mpt" [])
        (fun _ hs => (csrMptBufs_worldOK "state_mpt" [] hs).1.1)
        (ofString "nr2") (by decide) (.comb [.one, .one])
        [.var .local (ofString "new_roots"), .var .local (ofString "addr3")]
        (PBounded.dec (localsOnly_csrMptBufs "state_mpt" []) (ofString "sr2") (by decide) .one (.const (0#64))
          (PBounded.seq
            (PBounded.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "nr2"))) (.const (0#64)))
              (PBounded.assignLocal (localsOnly_csrMptBufs "state_mpt" [])
                (ofString "sr2") (by decide) (.rfield 1 (.var .local (ofString "nr2"))))
              (pBounded_cache_get_root_csrMptBufs fb_cache_get_root
                "state_mpt" "sr2" (.var .local (ofString "cache")) (.var .local (ofString "addr3")) (by decide)))
            (pBounded_alloc_csrMptBufs fb_alloc "state_mpt" "enc2" [] (128#64) (by decide)
              (pBounded_encode_account_csr fb_encode_account "state_mpt" "enc2" "n2"
                (.load .one (.op .add [.var .local (ofString "acct"), .const (0#64)]))
                (.load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "acct"), .const (8#64)]))
                (.var .local (ofString "sr2"))
                (.load .one (.op .add [.var .local (ofString "acct"), .const (48#64)]))
                (by decide)
                (pBounded_mpt_set_bound_csrMptBufs g_mpt_set mk_mpt_set
                  "n2" 110 "state_mpt" [("enc2", 128)]
                  (.var .local (ofString "addr3"))
                  (.var .local (ofString "enc2"))
                  (20#64)
                  (by decide) (by decide)))))))
      (by simp only [Nat.max_def]; repeat (first | split | omega))
  have hs3_yes :=
    PBounded.dec (localsOnly_csrMptBufs "state_mpt" []) (ofString "addr3") (by decide)
      .one (.rfield 1 (.var .local (ofString "s3")))
      (PBounded.dec (localsOnly_csrMptBufs "state_mpt" []) (ofString "acct") (by decide)
        .one (.rfield 2 (.var .local (ofString "s3")))
        (PBounded.ite (.cmp .equal (.var .local (ofString "acct")) (.const (1#64)))
          (pBounded_mpt_set_const_csrMptBufs g_mpt_set mk_mpt_set
            "state_mpt" [] (.var .local (ofString "addr3")) (.const (0#64)) (20#64) (0#64) (by decide) (by decide))
          hacct_no))
  have hbody : PBounded (CsrMptBufs "state_mpt" []) _
      ((K.«htab_item» + 1) +
        Nat.max
          (Nat.max (K.«mpt_set» + 1)
            ((K.«htab_get» + 1) + Nat.max 0 (K.«cache_get_root» + 1) +
              (K.«alloc» + 1) + (K.«encode_account» + 1) + (K.«mpt_set» + 1)))
          0) :=
    pBounded_mono_bound_csr
      (pBounded_roDecCall_csr fb_htab_item ro_htab_item
        (localsOnly_csrMptBufs "state_mpt" [])
        (fun _ hs => (csrMptBufs_worldOK "state_mpt" [] hs).1.1)
        (ofString "s3") (by decide) (.comb [.one, .one, .one])
        [.var .local (ofString "aw"), .var .local (ofString "i")]
        (PBounded.seq
          (PBounded.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s3"))) (.const (0#64)))
            hs3_yes PBounded.skip)
          (PBounded.assignLocal (localsOnly_csrMptBufs "state_mpt" [])
            (ofString "i") (by decide) (.op .add [.var .local (ofString "i"), .const (1#64)]))))
      (by simp only [Nat.max_def]; repeat (first | split | omega))
  exact PBounded.whileLess (localsOnly_csrMptBufs "state_mpt" [])
    (ofString "i") (.var .local (ofString "acap")) hbody
    (IncrBody.decCall _ _ _ _ (by decide) (IncrBody.seq _ (by decide) (by decide) IncrBody.incr))
    (by decide)

theorem «gbody_compute_state_root» : GBody.«compute_state_root» := by
  intro fb_alloc fb_cache_get_root fb_encode_account fb_htab_copy fb_htab_get
    fb_htab_has fb_htab_item fb_htab_new fb_htab_set fb_memcpy
    g_mpt_from_witness g_mpt_root g_mpt_set fb_rlp_encode_bytes
    fb_u256_is_zero fb_u256_to_be_min fb_ws_get_account_optional fb_ws_storage_root_of
    _wk_alloc _rt_alloc _wk_cache_get_root _wk_encode_account
    wk_htab_copy rt_htab_copy ro_htab_get ro_htab_has ro_htab_item
    h_htab_new h_htab_set _wk_memcpy wk_mpt_from_witness mk_mpt_root mk_mpt_set
    _wk_rlp_encode_bytes _rv_rlp_encode_bytes ro_u256_is_zero
    _wk_u256_to_be_min rv_u256_to_be_min _wk_ws_get_account_optional wk_ws_storage_root_of
  refine ⟨_, _, _, lookup_compute_state_root_csr, ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_compute_state_root,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  have hloop1 := pBounded_csr_loop1 fb_alloc fb_htab_has fb_htab_item fb_htab_set
    fb_memcpy g_mpt_from_witness g_mpt_root g_mpt_set fb_rlp_encode_bytes
    fb_u256_is_zero fb_u256_to_be_min fb_ws_storage_root_of
    ro_htab_has ro_htab_item h_htab_set wk_mpt_from_witness
    mk_mpt_root mk_mpt_set ro_u256_is_zero rv_u256_to_be_min wk_ws_storage_root_of
  have hloop2 := pBounded_csr_loop2 fb_alloc fb_encode_account fb_htab_get
    fb_htab_has fb_htab_item fb_htab_set g_mpt_set fb_ws_get_account_optional
    ro_htab_get ro_htab_has ro_htab_item h_htab_set mk_mpt_set
  have hloop3 := pBounded_csr_loop3 fb_alloc fb_cache_get_root fb_encode_account
    fb_htab_get fb_htab_item g_mpt_set ro_htab_get ro_htab_item mk_mpt_set
  have hfinal := pBounded_csr_final_mpt_root g_mpt_root
  have hstate_tail :=
    pBounded_mpt_from_witness_csr g_mpt_from_witness wk_mpt_from_witness
      "state_mpt"
      (args := [.var .local (ofString "nodedb"),
                .load .one (.op .add [.var .global (ofString "ws"), .const (8#64)]),
                .const (1#64)])
      (by decide)
      (PBounded.seq
        (PBounded.assignLocal (localsOnly_csrMptBufs "state_mpt" [])
          (ofString "i") (by decide) (.const (0#64)))
        (PBounded.seq hloop2
          (PBounded.dec (localsOnly_csrMptBufs "state_mpt" [])
            (ofString "acap") (by decide) .one
            (.load .one (.op .add [.var .local (ofString "aw"), .const (24#64)]))
            (PBounded.seq
              (PBounded.assignLocal (localsOnly_csrMptBufs "state_mpt" [])
                (ofString "i") (by decide) (.const (0#64)))
              (PBounded.seq hloop3 hfinal)))))
  have htabs_body :=
    PBounded.dec localsOnly_csrTabs (ofString "sw") (by decide) .one
      (.load .one (.op .add [.var .global (ofString "bs"), .const (32#64)]))
      (PBounded.dec localsOnly_csrTabs (ofString "aw") (by decide) .one
        (.load .one (.op .add [.var .global (ofString "bs"), .const (16#64)]))
        (PBounded.dec localsOnly_csrTabs (ofString "nodedb") (by decide) .one
          (.load .one (.op .add [.var .global (ofString "ws"), .const (0#64)]))
          (PBounded.dec localsOnly_csrTabs (ofString "cap") (by decide) .one
            (.load .one (.op .add [.var .local (ofString "sw"), .const (24#64)]))
            (PBounded.dec localsOnly_csrTabs (ofString "i") (by decide) .one (.const (0#64))
              (PBounded.seq hloop1 hstate_tail)))))
  refine @TerminatingProgBoundedOn.mono_bound WorldOK _ _ K.«compute_state_root»
    (decCall_htab_copy_entry_csr fb_htab_copy wk_htab_copy rt_htab_copy
      (decCall_htab_new_entry_csr fb_htab_new h_htab_new htabs_body.bounded)) ?_
  unfold K.«compute_state_root»
  simp only [show ∀ a b : Nat, Nat.max a b = max a b from fun _ _ => rfl,
    Nat.max_zero, Nat.zero_max]
  omega

end InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12
