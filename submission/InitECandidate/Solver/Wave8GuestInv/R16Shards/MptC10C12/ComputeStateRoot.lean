import InitECandidate.Solver.Wave8GuestInv.ContractParts.C12
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2Core
import InitECandidate.Solver.Wave8GuestInv.R14Shards.P3C10C12.P3_MptSet_Memory
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkEncodeAccount

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
open InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase1
open InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase2
open InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.FastPhase5
open InitECandidate.Solver.Wave8GuestInv.P3MptSet
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28
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
  apply disj_symm
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
    · exact disj_symm (disj_allocated_fresh_heap hs hp (ha o ho hz) hin)

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

end InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12
