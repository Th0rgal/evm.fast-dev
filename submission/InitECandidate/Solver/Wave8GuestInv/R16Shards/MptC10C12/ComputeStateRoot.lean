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

end InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12
