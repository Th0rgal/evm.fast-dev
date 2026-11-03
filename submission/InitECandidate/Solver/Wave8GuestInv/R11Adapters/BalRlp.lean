import InitECandidate.Solver.Wave8GuestInv.R11Adapters.FbAuto2
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P12_P15Callees
import InitECandidate.Solver.Wave8GuestInv.R11Adapters.FbClosure2
import InitECandidate.Solver.Wave8GuestInv.Shards.S01.Leaves
import InitECandidate.Solver.Wave8GuestInv.Deliveries.HTAB_LEAVES.Loops
import InitECandidate.Solver.Wave8GuestInv.Deliveries.RLP.RlpEnc
import InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.FbHtab

/-! Clean `fb_*` bounds for the EIP-7928 block access list RLP cone:
`bal_sort_gt`, `htab_keys`, `sort_elems`, `sorted_keys32`, `bal_encode_account`,
and `build_block_access_list_rlp`. -/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R11Adapters.BalRlp

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.P12_P15.Common
open InitECandidate.Solver.Wave8GuestInv.R11Adapters

private instance : InitECandidate.Solver.Wave8GuestInv.S01.IsGuestInv
    (@InitECandidate.Solver.Wave8GuestInv.GuestInv) where
  eval s prog h := InitECandidate.Solver.Wave8GuestInv.guestInv_evaluate s prog h
  congr hcode hmem hsh hbase h :=
    InitECandidate.Solver.Wave8GuestInv.guestInv_congr hcode hmem hsh hbase h

theorem fb_bal_sort_gt :
    TerminatingFunBoundedOn GuestInv (ofString "bal_sort_gt") K.«bal_sort_gt» := by
  fb_prove2 429 Guest.Software.guestFn_bal_sort_gt K.«bal_sort_gt»

theorem fb_htab_keys :
    TerminatingFunBoundedOn GuestInv (ofString "htab_keys") K.«htab_keys» :=
  InitECandidate.Solver.Wave8GuestInv.Htab.fb_htab_keys_of P12_P15.Callees.fb_memcpy

theorem fb_bal_ensure_account :
    TerminatingFunBoundedOn GuestInv (ofString "bal_ensure_account") K.«bal_ensure_account» :=
  InitECandidate.Solver.Wave8GuestInv.S01.fb_bal_ensure_account_of
    (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv)
    PrimShardP10P30.fb_htab_get PrimShardP10P30.fb_htab_set

theorem fb_add_storage_read :
    TerminatingFunBoundedOn GuestInv (ofString "add_storage_read") K.«add_storage_read» :=
  InitECandidate.Solver.Wave8GuestInv.S01.fb_add_storage_read_of
    (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv)
    fb_bal_ensure_account PrimShardP10P30.fb_htab_set

theorem fb_add_touched_account :
    TerminatingFunBoundedOn GuestInv (ofString "add_touched_account") K.«add_touched_account» :=
  InitECandidate.Solver.Wave8GuestInv.S01.fb_add_touched_account_of
    (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv)
    fb_bal_ensure_account

/-! ### `sort_elems`: bottom-up merge sort -/

private theorem signed_less_iff_toInt (a b : BitVec 64) :
    wordCmpHOL .less a b = true ↔ a.toInt < b.toInt := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [wordCmpHOL, holAsmSignedLess, BitVec.toInt_eq_msb_cond, BitVec.msb_eq_decide]
  split_ifs <;> simp_all <;> omega

/-- Rank for the dual-finger merge loop `while (0 != (i < mid)) & (0 != (j < right))`. -/
def mergeGap {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  (match s.locals.lookup (ofString "i"), s.locals.lookup (ofString "mid") with
   | some (.val (.word i)), some (.val (.word m)) => cmpRank .less m - cmpRank .less i
   | _, _ => 0) +
  (match s.locals.lookup (ofString "j"), s.locals.lookup (ofString "right") with
   | some (.val (.word j)), some (.val (.word r)) => cmpRank .less r - cmpRank .less j
   | _, _ => 0)

private theorem evalAt_binop_and {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e1 e2 : ExpHOL 64) (word : BitVec 64)
    (hw : evalAt s (.op .and [e1, e2]) = some (.val (.word word)))
    (hnz : word ≠ 0) :
    ∃ w1 w2 : BitVec 64, evalAt s e1 = some (.val (.word w1)) ∧
      evalAt s e2 = some (.val (.word w2)) ∧ w1 ≠ 0 ∧ w2 ≠ 0 := by
  simp only [evalAt, evalHOLExact, evalListHOLExact] at hw ⊢
  cases h1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 with
  | none => simp [h1] at hw
  | some v1 =>
    cases h2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 with
    | none => simp [h1, h2] at hw
    | some v2 =>
      simp only [h1, h2] at hw
      cases v1 with
      | rStruct _ => simp [List.all, valueIsWord] at hw
      | nStruct _ _ => simp [List.all, valueIsWord] at hw
      | val wl1 =>
        cases wl1 with
        | word w1 =>
          cases v2 with
          | rStruct _ => simp [List.all, valueIsWord] at hw
          | nStruct _ _ => simp [List.all, valueIsWord] at hw
          | val wl2 =>
            cases wl2 with
            | word w2 =>
              simp only [List.all, valueIsWord, Bool.true_and, ↓reduceIte, List.map,
                valueWord, wordOpHOL, wordOp] at hw
              have hweq : word = w1 &&& (w2 &&& 18446744073709551615#64) := by simpa using hw.symm
              subst hweq
              refine ⟨w1, w2, rfl, rfl, ?_, ?_⟩
              · rintro rfl; simp at hnz
              · rintro rfl; simp at hnz

private theorem while_counter_step_guestInv (op : Cmp) (hop : op = .less ∨ op = .lower) (i X : MlS)
    {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B)
    (hstep : CounterStep i 1 body)
    (hnc : noTopContinue body = true)
    (hX : avoidsLocal X body = true) :
    TerminatingProgBoundedOn GuestInv (.while (.cmp op (.var .local i) (.var .local X)) body)
      ((2 ^ 64 + 1) * (B + 1)) := by
  refine @TerminatingProgBoundedOn.while_rank GuestInv
    (.cmp op (.var .local i) (.var .local X)) body B (2 ^ 64)
    (counterGap op i X)
    (fun s hs => guestInv_decClock s hs) hbody ?_ ?_
  · intro F s _ _ _
    simp only [counterGap]
    split
    · rename_i a b _ _
      have := cmpRank_le op b
      omega
    · omega
  · intro F s _ hs hact hflow
    refine ⟨guestInv_evaluate _ _ (guestInv_decClock s hs), ?_⟩
    obtain ⟨word, hw, hnz⟩ := hact
    change evalAt s _ = _ at hw
    obtain ⟨a, b, ha, hb, hword⟩ := evalAt_cmp s op _ _ word hw
    simp only [evalAt, evalHOLExact] at ha hb
    have hia : s.locals.lookup i = some (.val (.word a)) := by simpa using ha
    have hXb : s.locals.lookup X = some (.val (.word b)) := by simpa using hb
    have hcmp : wordCmpHOL op a b = true := by
      by_contra hc
      simp [hc] at hword
      exact hnz hword
    have hlt := cmpRank_lt op hop a b hcmp
    have hnc' := evaluate_noTopContinue body hnc (decClockHOLFinite s)
    have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none := by
      rcases hflow with h | h
      · exact h
      · exact absurd h hnc'
    have hi' := hstep (decClockHOLFinite s) a hia (Or.inl hnone)
    have hX' := evaluate_avoidsLocal_flowing X body hX (decClockHOLFinite s) (Or.inl hnone)
    have hX'' : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup X =
        some (.val (.word b)) := hX'.trans hXb
    have hsucc := cmpRank_succ op a b hlt
    simp only [counterGap, hi', hX'', hia, hXb]
    omega

private theorem evalAt_nonzero_cmp_less {F : Type} (s : PanSemStateFiniteExact 64 F)
    (vL vR : MlS) (w : BitVec 64)
    (hw : evalAt s (.cmp .notEqual (.const 0) (.cmp .less (.var .local vL) (.var .local vR))) =
      some (.val (.word w)))
    (hnz : w ≠ 0) :
    ∃ a b : BitVec 64,
      s.locals.lookup vL = some (.val (.word a)) ∧
      s.locals.lookup vR = some (.val (.word b)) ∧
      cmpRank .less a < cmpRank .less b := by
  obtain ⟨z, c, hz, hc, hwz⟩ := evalAt_cmp s .notEqual _ _ w hw
  have hz0 : z = 0 := by simpa [evalAt, evalHOLExact] using hz.symm
  subst hz0
  obtain ⟨a, b, ha, hb, hwc⟩ := evalAt_cmp s .less _ _ c hc
  have ha' : s.locals.lookup vL = some (.val (.word a)) := by simpa [evalAt, evalHOLExact] using ha
  have hb' : s.locals.lookup vR = some (.val (.word b)) := by simpa [evalAt, evalHOLExact] using hb
  refine ⟨a, b, ha', hb', cmpRank_lt .less (Or.inl rfl) a b ?_⟩
  by_contra hfalse
  have hc0 : c = 0 := by simp [hfalse] at hwc; exact hwc
  subst hc0
  have hw0 : w = 0 := by
    simp [wordCmpHOL] at hwz
    exact hwz
  exact hnz hw0

private theorem while_merge_guestInv
    {aInit bInit : ExpHOL 64} {gtArgs m1Args m2Args : List (ExpHOL 64)} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv
      (.dec (ofString "a") .one aInit
        (.dec (ofString "b") .one bInit
          (.decCall (ofString "gt") .one (ofString "bal_sort_gt") gtArgs
            (.seq
              (.ite (.cmp .equal (.var .local (ofString "gt")) (.const 0))
                (.seq (.call (some (none, none)) (ofString "memcpy") m1Args)
                  (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
                (.seq (.call (some (none, none)) (ofString "memcpy") m2Args)
                  (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1]))))
              (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))))))
      B) :
    TerminatingProgBoundedOn GuestInv
      (.while
        (.op .and
          [.cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))),
           .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))])
        (.dec (ofString "a") .one aInit
          (.dec (ofString "b") .one bInit
            (.decCall (ofString "gt") .one (ofString "bal_sort_gt") gtArgs
              (.seq
                (.ite (.cmp .equal (.var .local (ofString "gt")) (.const 0))
                  (.seq (.call (some (none, none)) (ofString "memcpy") m1Args)
                    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
                  (.seq (.call (some (none, none)) (ofString "memcpy") m2Args)
                    (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1]))))
                (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1])))))))
      ((2 ^ 65 + 1) * (B + 1)) := by
  refine @TerminatingProgBoundedOn.while_rank GuestInv _ _ B (2 ^ 65) mergeGap
    (fun s hs => guestInv_decClock s hs) hbody ?_ ?_
  · intro F s _ _ _
    simp only [mergeGap]
    have h1 : (match s.locals.lookup (ofString "i"), s.locals.lookup (ofString "mid") with
        | some (.val (.word i)), some (.val (.word m)) => cmpRank .less m - cmpRank .less i
        | _, _ => 0) < 2 ^ 64 := by
      split
      · rename_i i m _ _; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (cmpRank_le .less m)
      · omega
    have h2 : (match s.locals.lookup (ofString "j"), s.locals.lookup (ofString "right") with
        | some (.val (.word j)), some (.val (.word r)) => cmpRank .less r - cmpRank .less j
        | _, _ => 0) < 2 ^ 64 := by
      split
      · rename_i j r _ _; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (cmpRank_le .less r)
      · omega
    omega
  · intro F s _ hs hact hflow
    refine ⟨guestInv_evaluate _ _ (guestInv_decClock s hs), ?_⟩
    obtain ⟨word, hw, hnz⟩ := hact
    change evalAt s _ = _ at hw
    obtain ⟨w1, w2, hw1, hw2, hnz1, hnz2⟩ := evalAt_binop_and s _ _ word hw hnz
    obtain ⟨vi, vm, hvi, hvm, hlt_i⟩ := evalAt_nonzero_cmp_less s (ofString "i") (ofString "mid") w1 hw1 hnz1
    obtain ⟨vj, vr, hvj, hvr, hlt_j⟩ := evalAt_nonzero_cmp_less s (ofString "j") (ofString "right") w2 hw2 hnz2
    set body :=
      ProgHOL.dec (ofString "a") .one aInit
        (.dec (ofString "b") .one bInit
          (.decCall (ofString "gt") .one (ofString "bal_sort_gt") gtArgs
            (.seq
              (.ite (.cmp .equal (.var .local (ofString "gt")) (.const 0))
                (.seq (.call (some (none, none)) (ofString "memcpy") m1Args)
                  (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
                (.seq (.call (some (none, none)) (ofString "memcpy") m2Args)
                  (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1]))))
              (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1])))))
    have hnc : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 ≠ some .continue :=
      evaluate_noTopContinue body rfl (decClockHOLFinite s)
    have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none := by
      rcases hflow with h | h
      · exact h
      · exact absurd h hnc
    have hflow0 : Flowing (evaluateHOLFiniteState (decClockHOLFinite s) body).1 := Or.inl hnone
    have hmid_keep := evaluate_avoidsLocal_flowing (ofString "mid") body rfl (decClockHOLFinite s) hflow0
    have hright_keep := evaluate_avoidsLocal_flowing (ofString "right") body rfl (decClockHOLFinite s) hflow0
    have hvm' : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup (ofString "mid") =
        some (.val (.word vm)) := hmid_keep.trans hvm
    have hvr' : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup (ofString "right") =
        some (.val (.word vr)) := hright_keep.trans hvr
    rcases hrun : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨res, post⟩
    have hres : res = none := by simpa [hrun] using hnone
    subst hres
    rw [hrun] at hvm' hvr'
    dsimp only at hvm' hvr' ⊢
    obtain ⟨va, inner1, hrun1, hloc1⟩ := dec_flowing (Or.inl rfl) hrun
    obtain ⟨vb, inner2, hrun2, hloc2⟩ := dec_flowing (Or.inl rfl) hrun1
    obtain ⟨vgt, resumed, inner3, hresLoc, _, hrun3, hloc3⟩ := decCall_flowing (Or.inl rfl) hrun2
    have lookup_s1 : ∀ x, x ≠ ofString "a" →
        (setVarHOLFinite (ofString "a") va (decClockHOLFinite s)).locals.lookup x = s.locals.lookup x := by
      intro x hx
      simp [setVarHOLFinite, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hx]
    have lookup_s2 : ∀ x, x ≠ ofString "a" → x ≠ ofString "b" →
        (setVarHOLFinite (ofString "b") vb (setVarHOLFinite (ofString "a") va (decClockHOLFinite s))).locals.lookup x =
          s.locals.lookup x := by
      intro x hxa hxb
      have h1 : (setVarHOLFinite (ofString "b") vb (setVarHOLFinite (ofString "a") va (decClockHOLFinite s))).locals.lookup x =
          (setVarHOLFinite (ofString "a") va (decClockHOLFinite s)).locals.lookup x := by
        simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hxb]
      exact h1.trans (lookup_s1 x hxa)
    have hvi_res : resumed.locals.lookup (ofString "i") = some (.val (.word vi)) :=
      (hresLoc _ (by decide)).trans ((lookup_s2 _ (by decide) (by decide)).trans hvi)
    have hvj_res : resumed.locals.lookup (ofString "j") = some (.val (.word vj)) :=
      (hresLoc _ (by decide)).trans ((lookup_s2 _ (by decide) (by decide)).trans hvj)
    have post_lookup : ∀ x, x ≠ ofString "a" → x ≠ ofString "b" → x ≠ ofString "gt" →
        post.locals.lookup x = inner3.locals.lookup x := by
      intro x hxa hxb hxgt
      have p1 : post.locals.lookup x = inner1.locals.lookup x := by
        rw [hloc1, @PanRunBounded.resVarEq_lookup 64 _, if_neg hxa]
      have p2 : inner1.locals.lookup x = inner2.locals.lookup x := by
        rw [hloc2, @PanRunBounded.resVarEq_lookup 64 _, if_neg hxb]
      have p3 : inner2.locals.lookup x = inner3.locals.lookup x := by
        rw [hloc3, @PanRunBounded.resVarEq_lookup 64 _, if_neg hxgt]
      exact p1.trans (p2.trans p3)
    rw [evaluateHOLFiniteState_seq_line780] at hrun3
    set iteProg :=
      ProgHOL.ite (.cmp .equal (.var .local (ofString "gt")) (.const 0))
        (.seq (.call (some (none, none)) (ofString "memcpy") m1Args)
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
        (.seq (.call (some (none, none)) (ofString "memcpy") m2Args)
          (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1])))
    set kInc : ProgHOL 64 := ProgHOL.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1])
    rcases hite : evaluateHOLFiniteState resumed iteProg with ⟨rite, mid⟩
    rw [hite] at hrun3
    have hrite : rite = none := by
      cases rite with
      | none => rfl
      | some r => simp at hrun3
    subst hrite
    dsimp only at hrun3
    have hk_avoid_i : (evaluateHOLFiniteState mid kInc).2.locals.lookup (ofString "i") = mid.locals.lookup (ofString "i") :=
      evaluate_avoidsLocal_flowing (ofString "i") kInc rfl mid (by rw [hrun3]; exact Or.inl rfl)
    have hk_avoid_j : (evaluateHOLFiniteState mid kInc).2.locals.lookup (ofString "j") = mid.locals.lookup (ofString "j") :=
      evaluate_avoidsLocal_flowing (ofString "j") kInc rfl mid (by rw [hrun3]; exact Or.inl rfl)
    rw [hrun3] at hk_avoid_i hk_avoid_j
    dsimp only at hk_avoid_i hk_avoid_j
    have hbranch :
        (mid.locals.lookup (ofString "i") = some (.val (.word (vi + 1))) ∧
          mid.locals.lookup (ofString "j") = some (.val (.word vj))) ∨
        (mid.locals.lookup (ofString "i") = some (.val (.word vi)) ∧
          mid.locals.lookup (ofString "j") = some (.val (.word (vj + 1)))) := by
      rw [evaluateHOLFiniteState_ite] at hite
      split at hite
      · split at hite
        · right
          have hij_keep := evaluate_avoidsLocal_flowing (ofString "i")
            (.seq (.call (some (none, none)) (ofString "memcpy") m2Args)
              (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1])))
            rfl resumed (by rw [hite]; exact Or.inl rfl)
          rw [hite] at hij_keep
          have hinc_j : IncrBody (ofString "j")
              (.seq (.call (some (none, none)) (ofString "memcpy") m2Args)
                (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1]))) :=
            IncrBody.seq _ rfl rfl IncrBody.incr
          have hj_step := (hinc_j.run resumed vj hvj_res).2 (by rw [hite])
          rw [hite] at hj_step
          exact ⟨hij_keep.trans hvi_res, hj_step⟩
        · left
          have hij_keep := evaluate_avoidsLocal_flowing (ofString "j")
            (.seq (.call (some (none, none)) (ofString "memcpy") m1Args)
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
            rfl resumed (by rw [hite]; exact Or.inl rfl)
          rw [hite] at hij_keep
          have hinc_i : IncrBody (ofString "i")
              (.seq (.call (some (none, none)) (ofString "memcpy") m1Args)
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))) :=
            IncrBody.seq _ rfl rfl IncrBody.incr
          have hi_step := (hinc_i.run resumed vi hvi_res).2 (by rw [hite])
          rw [hite] at hi_step
          exact ⟨hi_step, hij_keep.trans hvj_res⟩
      · simp at hite
    have hpi := (post_lookup (ofString "i") (by decide) (by decide) (by decide)).trans hk_avoid_i
    have hpj := (post_lookup (ofString "j") (by decide) (by decide) (by decide)).trans hk_avoid_j
    rcases hbranch with ⟨hmi, hmj⟩ | ⟨hmi, hmj⟩
    · have hpi' := hpi.trans hmi
      have hpj' := hpj.trans hmj
      have hsucc := cmpRank_succ .less vi vm hlt_i
      simp only [mergeGap, hpi', hpj', hvm', hvr', hvi, hvj, hvm, hvr, hsucc]
      have hsub : cmpRank .less vm - (cmpRank .less vi + 1) < cmpRank .less vm - cmpRank .less vi :=
        Nat.sub_lt_sub_left hlt_i (Nat.lt_succ_self _)
      exact Nat.add_lt_add_right hsub _
    · have hpi' := hpi.trans hmi
      have hpj' := hpj.trans hmj
      have hsucc := cmpRank_succ .less vj vr hlt_j
      simp only [mergeGap, hpi', hpj', hvm', hvr', hvi, hvj, hvm, hvr, hsucc]
      have hsub : cmpRank .less vr - (cmpRank .less vj + 1) < cmpRank .less vr - cmpRank .less vj :=
        Nat.sub_lt_sub_left hlt_j (Nat.lt_succ_self _)
      exact Nat.add_lt_add_left hsub _

/-- Guard for `sort_elems`'s outer loop: `GuestInv` plus `width = 0` or `∃ m ≤ 63, width.toNat = 2^m`. -/
def OuterSortInv {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  GuestInv s ∧
  ∃ w : BitVec 64, s.locals.lookup (ofString "width") = some (.val (.word w)) ∧
    (w = 0 ∨ ∃ m : Nat, m ≤ 63 ∧ w.toNat = 2 ^ m)

/-- Guard for `sort_elems`'s middle loop: `GuestInv`, plus either `(0 < width ≤ 2^63 ∧ left < 2^63)` or `(width = 0 ∧ left = 0)`. -/
def MergePassInv {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  GuestInv s ∧
  ((∃ w l : BitVec 64,
      s.locals.lookup (ofString "width") = some (.val (.word w)) ∧
      s.locals.lookup (ofString "left") = some (.val (.word l)) ∧
      0 < w.toNat ∧ w.toNat ≤ 2 ^ 63 ∧ l.toNat < 2 ^ 63) ∨
   (s.locals.lookup (ofString "width") = some (.val (.word 0)) ∧
    s.locals.lookup (ofString "left") = some (.val (.word 0))))

private theorem outerSortInv_decClock {F : Type} (s : PanSemStateFiniteExact 64 F) (h : OuterSortInv s) :
    OuterSortInv (decClockHOLFinite s) :=
  ⟨guestInv_decClock s h.1, h.2⟩

private theorem mergePassInv_decClock {F : Type} (s : PanSemStateFiniteExact 64 F) (h : MergePassInv s) :
    MergePassInv (decClockHOLFinite s) :=
  ⟨guestInv_decClock s h.1, h.2⟩

private theorem signed_less_nonneg_left (a b : BitVec 64)
    (ha_nonneg : a.toNat < 2 ^ 63) (hlt : wordCmpHOL .less a b = true) :
    a.toNat < b.toNat ∧ b.toNat < 2 ^ 63 := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [wordCmpHOL, holAsmSignedLess] at hlt
  split_ifs at hlt <;> simp_all <;> omega

private theorem merge_pass_advance (left width n : BitVec 64)
    (hwpos : 0 < width.toNat) (hw_nonneg : width.toNat ≤ 2 ^ 63)
    (hl_nonneg : left.toNat < 2 ^ 63)
    (hlt : wordCmpHOL .less left n = true) :
    let m0 := left + width
    let m1 := if wordCmpHOL .lower n m0 then n else m0
    let r0 := m1 + width
    let right := if wordCmpHOL .lower n r0 then n else r0
    cmpRank .less left < cmpRank .less right ∧ right.toNat < 2 ^ 63 := by
  obtain ⟨hln, hn_nonneg⟩ := signed_less_nonneg_left left n hl_nonneg hlt
  have hsum1 : left.toNat + width.toNat < 2 ^ 64 := by omega
  have hm0 : (left + width).toNat = left.toNat + width.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hsum1]
  dsimp only
  cases hc1 : wordCmpHOL .lower n (left + width)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hle1 : (left + width).toNat ≤ n.toNat := by
      simp only [wordCmpHOL, BitVec.lt_def, decide_eq_false_iff_not] at hc1
      omega
    have hm0_nonneg : (left + width).toNat < 2 ^ 63 := by omega
    have hsum2 : (left + width).toNat + width.toNat < 2 ^ 64 := by omega
    have hr0 : (left + width + width).toNat = (left + width).toNat + width.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt hsum2]
    cases hc2 : wordCmpHOL .lower n (left + width + width)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hle2 : (left + width + width).toNat ≤ n.toNat := by
        simp only [wordCmpHOL, BitVec.lt_def, decide_eq_false_iff_not] at hc2
        omega
      refine ⟨?_, by omega⟩
      simp only [cmpRank]
      omega
    · simp only [↓reduceIte]
      exact ⟨cmpRank_lt .less (Or.inl rfl) left n hlt, hn_nonneg⟩
  · simp only [↓reduceIte]
    have hsum2 : n.toNat + width.toNat < 2 ^ 64 := by omega
    have hr0 : (n + width).toNat = n.toNat + width.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt hsum2]
    have hc2 : wordCmpHOL .lower n (n + width) = true := by
      simp only [wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
      omega
    simp only [hc2, ↓reduceIte]
    exact ⟨cmpRank_lt .less (Or.inl rfl) left n hlt, hn_nonneg⟩

private theorem eval_clamp_ite {F : Type} (s : PanSemStateFiniteExact 64 F)
    (vN vX : MlS) (vn vx : BitVec 64)
    (hn : s.locals.lookup vN = some (.val (.word vn)))
    (hx : s.locals.lookup vX = some (.val (.word vx)))
    (hne : vN ≠ vX) :
    let clamp : BitVec 64 := if wordCmpHOL .lower vn vx then vn else vx
    ∃ s', evaluateHOLFiniteState s
        (.ite (.cmp .lower (.var .local vN) (.var .local vX))
          (.assign .local vX (.var .local vN)) .skip) = (none, s') ∧
      s'.locals.lookup vX = some (.val (.word clamp)) ∧
      s'.locals.lookup vN = some (.val (.word vn)) ∧
      (∀ k, k ≠ vX → s'.locals.lookup k = s.locals.lookup k) := by
  dsimp only
  rw [evaluateHOLFiniteState_ite]
  have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .lower (.var .local vN) (.var .local vX)) =
      some (.val (.word (if wordCmpHOL .lower vn vx then 1 else 0))) := by
    simp [evalHOLExact, hn, hx]
  rw [hcond]
  dsimp only
  cases hcmp : wordCmpHOL .lower vn vx
  · simp only [Bool.false_eq_true, ↓reduceIte, evaluateHOLFiniteState_skip]
    exact ⟨s, rfl, hx, hn, fun _ _ => rfl⟩
  · simp only [↓reduceIte]
    have hne0 : (1 : BitVec 64) ≠ 0 := by decide
    simp only [hne0, ↓reduceIte]
    have hass : evaluateHOLFiniteState s (.assign .local vX (.var .local vN)) =
        (none, setVarHOLFinite vX (.val (.word vn)) s) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, hn, hx, lookupKvarHOLExact,
        isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
    rw [hass]
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hn]
    · intro k hk
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]

private theorem run_merge_pass_body_inner
    {w1Body w2Body w3Body : ProgHOL 64}
    (h1r : avoidsLocal (ofString "right") w1Body = true)
    (h1l : avoidsLocal (ofString "left") w1Body = true)
    (h2r : avoidsLocal (ofString "right") w2Body = true)
    (h2l : avoidsLocal (ofString "left") w2Body = true)
    (h3r : avoidsLocal (ofString "right") w3Body = true)
    (h3l : avoidsLocal (ofString "left") w3Body = true)
    {F : Type} (s4 : PanSemStateFiniteExact 64 F) (vl rightVal : BitVec 64)
    (hs4_l : s4.locals.lookup (ofString "left") = some (.val (.word vl)))
    (hs4_r : s4.locals.lookup (ofString "right") = some (.val (.word rightVal)))
    (hnone : (evaluateHOLFiniteState s4
      (.dec (ofString "i") .one (.var .local (ofString "left"))
        (.dec (ofString "j") .one (.var .local (ofString "mid"))
          (.dec (ofString "k") .one (.var .local (ofString "left"))
            (.seq
              (.while (.op .and [
                .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))),
                .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))]) w1Body)
              (.seq
                (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))) w2Body)
                (.seq
                  (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right"))) w3Body)
                  (.assign .local (ofString "left") (.var .local (ofString "right")))))))))).1 = none) :
    (evaluateHOLFiniteState s4
      (.dec (ofString "i") .one (.var .local (ofString "left"))
        (.dec (ofString "j") .one (.var .local (ofString "mid"))
          (.dec (ofString "k") .one (.var .local (ofString "left"))
            (.seq
              (.while (.op .and [
                .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))),
                .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))]) w1Body)
              (.seq
                (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))) w2Body)
                (.seq
                  (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right"))) w3Body)
                  (.assign .local (ofString "left") (.var .local (ofString "right")))))))))).2.locals.lookup (ofString "left") =
      some (.val (.word rightVal)) := by
  rw [evaluateHOLFiniteState_dec_total] at hnone ⊢
  have hi_ev : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
      (.var .local (ofString "left")) = some (.val (.word vl)) := by simp [evalHOLExact, hs4_l]
  dsimp only at hnone ⊢
  rw [hi_ev] at hnone ⊢
  dsimp only at hnone ⊢
  rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])] at hnone ⊢
  set si := setVarHOLFinite (ofString "i") (.val (.word vl)) s4
  have hsi_l : si.locals.lookup (ofString "left") = some (.val (.word vl)) := by
    simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "i" ≠ ofString "left" by decide, hs4_l]
  have hsi_r : si.locals.lookup (ofString "right") = some (.val (.word rightVal)) := by
    simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "i" ≠ ofString "right" by decide, hs4_r]
  rw [evaluateHOLFiniteState_dec_total] at hnone ⊢
  dsimp only at hnone ⊢
  cases hj_ev : @evalHOLExact 64 F _ si.toExact (fun a => Classical.propDecidable (si.memaddrs a))
      (.var .local (ofString "mid")) with
  | none => rw [hj_ev] at hnone; simp at hnone
  | some vj =>
    rw [hj_ev] at hnone
    dsimp only at hnone ⊢
    by_cases hshj : shapeEqHOL .one (shapeOfHOLExact vj) = true
    · rw [if_pos hshj] at hnone ⊢
      set sj := setVarHOLFinite (ofString "j") vj si
      have hsj_l : sj.locals.lookup (ofString "left") = some (.val (.word vl)) := by
        simp [sj, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "j" ≠ ofString "left" by decide, hsi_l]
      have hsj_r : sj.locals.lookup (ofString "right") = some (.val (.word rightVal)) := by
        simp [sj, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "j" ≠ ofString "right" by decide, hsi_r]
      rw [evaluateHOLFiniteState_dec_total] at hnone ⊢
      have hk_ev : @evalHOLExact 64 F _ sj.toExact (fun a => Classical.propDecidable (sj.memaddrs a))
          (.var .local (ofString "left")) = some (.val (.word vl)) := by simp [evalHOLExact, hsj_l]
      dsimp only at hnone ⊢
      rw [hk_ev] at hnone ⊢
      dsimp only at hnone ⊢
      rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])] at hnone ⊢
      set sk := setVarHOLFinite (ofString "k") (.val (.word vl)) sj
      have hsk_l : sk.locals.lookup (ofString "left") = some (.val (.word vl)) := by
        simp [sk, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "k" ≠ ofString "left" by decide, hsj_l]
      have hsk_r : sk.locals.lookup (ofString "right") = some (.val (.word rightVal)) := by
        simp [sk, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "k" ≠ ofString "right" by decide, hsj_r]
      set loops3 : ProgHOL 64 :=
        .seq
          (.while (.op .and [
            .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))),
            .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))]) w1Body)
          (.seq
            (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))) w2Body)
            (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right"))) w3Body))
      have hseq_assoc :
          evaluateHOLFiniteState sk
            (.seq
              (.while (.op .and [
                .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))),
                .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))]) w1Body)
              (.seq
                (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))) w2Body)
                (.seq
                  (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right"))) w3Body)
                  (.assign .local (ofString "left") (.var .local (ofString "right")))))) =
          evaluateHOLFiniteState sk (.seq loops3 (.assign .local (ofString "left") (.var .local (ofString "right")))) := by
        simp only [loops3, evaluateHOLFiniteState_seq_line780]
        rcases evaluateHOLFiniteState sk _ with ⟨rA, sA⟩
        cases rA <;> dsimp only
        rcases evaluateHOLFiniteState sA _ with ⟨rB, sB⟩
        cases rB <;> dsimp only <;> rfl
      rw [hseq_assoc, evaluateHOLFiniteState_seq_line780] at hnone ⊢
      have hav_r : avoidsLocal (ofString "right") loops3 = true := by
        simp [loops3, avoidsLocal, h1r, h2r, h3r]
      have hav_l : avoidsLocal (ofString "left") loops3 = true := by
        simp [loops3, avoidsLocal, h1l, h2l, h3l]
      rcases hloops : evaluateHOLFiniteState sk loops3 with ⟨rL, s5⟩
      cases rL with
      | some r => simp [hloops] at hnone
      | none =>
        dsimp only at hnone ⊢
        have hs5_r : s5.locals.lookup (ofString "right") = some (.val (.word rightVal)) := by
          have hk := evaluate_avoidsLocal_flowing (ofString "right") loops3 hav_r sk (by rw [hloops]; exact Or.inl rfl)
          rw [hloops] at hk; exact hk.trans hsk_r
        have hs5_l : s5.locals.lookup (ofString "left") = some (.val (.word vl)) := by
          have hk := evaluate_avoidsLocal_flowing (ofString "left") loops3 hav_l sk (by rw [hloops]; exact Or.inl rfl)
          rw [hloops] at hk; exact hk.trans hsk_l
        have hass_left : evaluateHOLFiniteState s5
            (.assign .local (ofString "left") (.var .local (ofString "right"))) =
            (none, setVarHOLFinite (ofString "left") (.val (.word rightVal)) s5) := by
          simp [evaluateHOLFiniteState_assign, evalHOLExact, hs5_r, hs5_l, lookupKvarHOLExact,
            isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
        rw [hass_left]
        dsimp only
        rw [PanRunBounded.resVarEq_lookup, if_neg (by decide)]
        rw [PanRunBounded.resVarEq_lookup, if_neg (by decide)]
        rw [PanRunBounded.resVarEq_lookup, if_neg (by decide)]
        simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · rw [if_neg hshj] at hnone; dsimp only at hnone; simp at hnone

private theorem run_merge_pass_body
    {w1Body w2Body w3Body : ProgHOL 64}
    (h1r : avoidsLocal (ofString "right") w1Body = true)
    (h1l : avoidsLocal (ofString "left") w1Body = true)
    (h2r : avoidsLocal (ofString "right") w2Body = true)
    (h2l : avoidsLocal (ofString "left") w2Body = true)
    (h3r : avoidsLocal (ofString "right") w3Body = true)
    (h3l : avoidsLocal (ofString "left") w3Body = true)
    {F : Type} (st : PanSemStateFiniteExact 64 F) (vl vw bn : BitVec 64)
    (hvl : st.locals.lookup (ofString "left") = some (.val (.word vl)))
    (hvw : st.locals.lookup (ofString "width") = some (.val (.word vw)))
    (hbn : st.locals.lookup (ofString "n") = some (.val (.word bn))) :
    let m1 : BitVec 64 := if wordCmpHOL .lower bn (vl + vw) then bn else vl + vw
    let rightVal : BitVec 64 := if wordCmpHOL .lower bn (m1 + vw) then bn else m1 + vw
    let fullBody : ProgHOL 64 :=
      .dec (ofString "mid") .one (.op .add [.var .local (ofString "left"), .var .local (ofString "width")])
        (.seq
          (.ite (.cmp .lower (.var .local (ofString "n")) (.var .local (ofString "mid")))
            (.assign .local (ofString "mid") (.var .local (ofString "n"))) .skip)
          (.dec (ofString "right") .one (.op .add [.var .local (ofString "mid"), .var .local (ofString "width")])
            (.seq
              (.ite (.cmp .lower (.var .local (ofString "n")) (.var .local (ofString "right")))
                (.assign .local (ofString "right") (.var .local (ofString "n"))) .skip)
              (.dec (ofString "i") .one (.var .local (ofString "left"))
                (.dec (ofString "j") .one (.var .local (ofString "mid"))
                  (.dec (ofString "k") .one (.var .local (ofString "left"))
                    (.seq
                      (.while (.op .and [
                        .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))),
                        .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))]) w1Body)
                      (.seq
                        (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))) w2Body)
                        (.seq
                          (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right"))) w3Body)
                          (.assign .local (ofString "left") (.var .local (ofString "right"))))))))))))
    (evaluateHOLFiniteState st fullBody).1 ≠ some .continue ∧
    ((evaluateHOLFiniteState st fullBody).1 = none →
      (evaluateHOLFiniteState st fullBody).2.locals.lookup (ofString "left") =
        some (.val (.word rightVal))) := by
  intro m1 rightVal fullBody
  have hnc_full : noTopContinue fullBody = true := by
    simp [fullBody, noTopContinue]
  refine ⟨evaluate_noTopContinue fullBody hnc_full st, fun hnone => ?_⟩
  change (evaluateHOLFiniteState st
    (.dec (ofString "mid") .one (.op .add [.var .local (ofString "left"), .var .local (ofString "width")]) _)).1 = none at hnone
  change (evaluateHOLFiniteState st
    (.dec (ofString "mid") .one (.op .add [.var .local (ofString "left"), .var .local (ofString "width")]) _)).2.locals.lookup (ofString "left") = _
  rw [evaluateHOLFiniteState_dec_total] at hnone ⊢
  have hm0_eval : @evalHOLExact 64 F _ st.toExact
      (fun a => Classical.propDecidable (st.memaddrs a))
      (.op .add [.var .local (ofString "left"), .var .local (ofString "width")]) =
      some (.val (.word (vl + vw))) := by
    simp [evalHOLExact, evalListHOLExact, hvl, hvw, valueIsWord, valueWord, wordOpHOL, wordOp]
  dsimp only at hnone ⊢
  rw [hm0_eval] at hnone ⊢
  simp only [shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnone ⊢
  set s1 := setVarHOLFinite (ofString "mid") (.val (.word (vl + vw))) st
  have hs1_mid : s1.locals.lookup (ofString "mid") = some (.val (.word (vl + vw))) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word bn)) := by
    have hne : ofString "mid" ≠ ofString "n" := by decide
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hbn]
  have hs1_w : s1.locals.lookup (ofString "width") = some (.val (.word vw)) := by
    have hne : ofString "mid" ≠ ofString "width" := by decide
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hvw]
  have hs1_l : s1.locals.lookup (ofString "left") = some (.val (.word vl)) := by
    have hne : ofString "mid" ≠ ofString "left" := by decide
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hvl]
  obtain ⟨s2, hs2_run, hs2_mid, hs2_n, hs2_keep⟩ :=
    eval_clamp_ite s1 (ofString "n") (ofString "mid") bn (vl + vw) hs1_n hs1_mid (by decide)
  have hs2_w : s2.locals.lookup (ofString "width") = some (.val (.word vw)) :=
    (hs2_keep _ (by decide)).trans hs1_w
  have hs2_l : s2.locals.lookup (ofString "left") = some (.val (.word vl)) :=
    (hs2_keep _ (by decide)).trans hs1_l
  rw [evaluateHOLFiniteState_seq_line780, hs2_run] at hnone ⊢
  dsimp only at hnone ⊢
  rw [evaluateHOLFiniteState_dec_total] at hnone ⊢
  have hr0_eval : @evalHOLExact 64 F _ s2.toExact
      (fun a => Classical.propDecidable (s2.memaddrs a))
      (.op .add [.var .local (ofString "mid"), .var .local (ofString "width")]) =
      some (.val (.word (m1 + vw))) := by
    simp [evalHOLExact, evalListHOLExact, hs2_mid, hs2_w, valueIsWord, valueWord, wordOpHOL, wordOp, m1]
  dsimp only at hnone ⊢
  rw [hr0_eval] at hnone ⊢
  simp only [shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnone ⊢
  set s3 := setVarHOLFinite (ofString "right") (.val (.word (m1 + vw))) s2
  have hs3_r : s3.locals.lookup (ofString "right") = some (.val (.word (m1 + vw))) := by
    simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs3_n : s3.locals.lookup (ofString "n") = some (.val (.word bn)) := by
    have hne : ofString "right" ≠ ofString "n" := by decide
    simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs2_n]
  have hs3_l : s3.locals.lookup (ofString "left") = some (.val (.word vl)) := by
    have hne : ofString "right" ≠ ofString "left" := by decide
    simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs2_l]
  obtain ⟨s4, hs4_run, hs4_r, _, hs4_keep⟩ :=
    eval_clamp_ite s3 (ofString "n") (ofString "right") bn (m1 + vw) hs3_n hs3_r (by decide)
  have hs4_l : s4.locals.lookup (ofString "left") = some (.val (.word vl)) :=
    (hs4_keep _ (by decide)).trans hs3_l
  rw [evaluateHOLFiniteState_seq_line780, hs4_run] at hnone ⊢
  dsimp only at hnone ⊢
  have hinner_post := run_merge_pass_body_inner h1r h1l h2r h2l h3r h3l s4 vl rightVal hs4_l hs4_r hnone
  rcases hinner_eq : evaluateHOLFiniteState s4 _ with ⟨r_in, s_in⟩
  rw [hinner_eq] at hinner_post hnone
  cases r_in with
  | some r => simp at hnone
  | none =>
    dsimp only at hinner_post ⊢
    rw [PanRunBounded.resVarEq_lookup, if_neg (by decide)]
    rw [PanRunBounded.resVarEq_lookup, if_neg (by decide)]
    exact hinner_post

private theorem eval_dec_resVarEq_self {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (e : ExpHOL 64) (v : ValueHOL 64) (body : ProgHOL 64)
    (heval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some v)
    (hshape : shapeEqHOL .one (shapeOfHOLExact v) = true)
    (hbody : evaluateHOLFiniteState (setVarHOLFinite name v s) body = (none, setVarHOLFinite name v s)) :
    evaluateHOLFiniteState s (.dec name .one e body) = (none, s) := by
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [heval]
  dsimp only
  rw [if_pos hshape, hbody]
  dsimp only
  have hloc : (setVarHOLFinite name v s).locals.resVarEq (name, s.locals.lookup name) = s.locals := by
    apply HolFiniteMapExact.ext_lookup
    intro k
    rw [PanRunBounded.resVarEq_lookup]
    by_cases hk : k = name
    · subst hk; simp
    · simp [hk, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
  have hs_res : ({ setVarHOLFinite name v s with locals := (setVarHOLFinite name v s).locals.resVarEq (name, s.locals.lookup name) } : PanSemStateFiniteExact 64 F) = s := by
    rw [hloc]; rfl
  rw [hs_res]

private theorem run_merge_inner_zero
    {w1Body w2Body w3Body : ProgHOL 64}
    {F : Type} (s4 : PanSemStateFiniteExact 64 F)
    (hl : s4.locals.lookup (ofString "left") = some (.val (.word 0)))
    (hm : s4.locals.lookup (ofString "mid") = some (.val (.word 0)))
    (hr : s4.locals.lookup (ofString "right") = some (.val (.word 0))) :
    let innerProg : ProgHOL 64 :=
      .dec (ofString "i") .one (.var .local (ofString "left"))
        (.dec (ofString "j") .one (.var .local (ofString "mid"))
          (.dec (ofString "k") .one (.var .local (ofString "left"))
            (.seq
              (.while (.op .and [
                .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))),
                .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))]) w1Body)
              (.seq
                (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))) w2Body)
                (.seq
                  (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right"))) w3Body)
                  (.assign .local (ofString "left") (.var .local (ofString "right"))))))))
    evaluateHOLFiniteState s4 innerProg = (none, s4) := by
  intro innerProg
  set si := setVarHOLFinite (ofString "i") (.val (.word 0)) s4
  set sj := setVarHOLFinite (ofString "j") (.val (.word 0)) si
  set sk := setVarHOLFinite (ofString "k") (.val (.word 0)) sj
  have hsi_m : si.locals.lookup (ofString "mid") = some (.val (.word 0)) := by
    simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "i" ≠ ofString "mid" by decide, hm]
  have hsi_l : si.locals.lookup (ofString "left") = some (.val (.word 0)) := by
    simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "i" ≠ ofString "left" by decide, hl]
  have hsi_r : si.locals.lookup (ofString "right") = some (.val (.word 0)) := by
    simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "i" ≠ ofString "right" by decide, hr]
  have hsi_i : si.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hsj_l : sj.locals.lookup (ofString "left") = some (.val (.word 0)) := by
    simp [sj, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "j" ≠ ofString "left" by decide, hsi_l]
  have hsj_m : sj.locals.lookup (ofString "mid") = some (.val (.word 0)) := by
    simp [sj, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "j" ≠ ofString "mid" by decide, hsi_m]
  have hsj_r : sj.locals.lookup (ofString "right") = some (.val (.word 0)) := by
    simp [sj, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "j" ≠ ofString "right" by decide, hsi_r]
  have hsj_i : sj.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [sj, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "j" ≠ ofString "i" by decide, hsi_i]
  have hsj_j : sj.locals.lookup (ofString "j") = some (.val (.word 0)) := by
    simp [sj, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hsk_l : sk.locals.lookup (ofString "left") = some (.val (.word 0)) := by
    simp [sk, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "k" ≠ ofString "left" by decide, hsj_l]
  have hsk_m : sk.locals.lookup (ofString "mid") = some (.val (.word 0)) := by
    simp [sk, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "k" ≠ ofString "mid" by decide, hsj_m]
  have hsk_r : sk.locals.lookup (ofString "right") = some (.val (.word 0)) := by
    simp [sk, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "k" ≠ ofString "right" by decide, hsj_r]
  have hsk_i : sk.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [sk, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "k" ≠ ofString "i" by decide, hsj_i]
  have hsk_j : sk.locals.lookup (ofString "j") = some (.val (.word 0)) := by
    simp [sk, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "k" ≠ ofString "j" by decide, hsj_j]
  have hw1 : evaluateHOLFiniteState sk
      (.while (.op .and [
        .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))),
        .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))]) w1Body) =
      (none, sk) := by
    rw [evaluateHOLFiniteState_while_total]
    have hc1 : evalHOLFinite sk (h := fun a => Classical.propDecidable (sk.memaddrs a))
        (.op .and [
          .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))),
          .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))]) =
        some (.val (.word 0)) := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, evalListHOLExact, hsk_i, hsk_m, hsk_j, hsk_r,
        wordCmpHOL, holAsmSignedLess, valueIsWord, valueWord, wordOpHOL, wordOp]
    rw [hc1]; simp
  have hw2 : evaluateHOLFiniteState sk
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))) w2Body) =
      (none, sk) := by
    rw [evaluateHOLFiniteState_while_total]
    have hc2 : evalHOLFinite sk (h := fun a => Classical.propDecidable (sk.memaddrs a))
        (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))) =
        some (.val (.word 0)) := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, hsk_i, hsk_m, wordCmpHOL, holAsmSignedLess]
    rw [hc2]; simp
  have hw3 : evaluateHOLFiniteState sk
      (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right"))) w3Body) =
      (none, sk) := by
    rw [evaluateHOLFiniteState_while_total]
    have hc3 : evalHOLFinite sk (h := fun a => Classical.propDecidable (sk.memaddrs a))
        (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right"))) =
        some (.val (.word 0)) := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, hsk_j, hsk_r, wordCmpHOL, holAsmSignedLess]
    rw [hc3]; simp
  have hass_l : evaluateHOLFiniteState sk
      (.assign .local (ofString "left") (.var .local (ofString "right"))) = (none, sk) := by
    have hrw : evaluateHOLFiniteState sk
        (.assign .local (ofString "left") (.var .local (ofString "right"))) =
        (none, setVarHOLFinite (ofString "left") (.val (.word 0)) sk) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, hsk_r, hsk_l, lookupKvarHOLExact,
        isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
    rw [hrw]
    have hloc0 : sk.locals.update (ofString "left", .val (.word 0)) = sk.locals := by
      apply HolFiniteMapExact.ext_lookup
      intro k
      by_cases hk : k = ofString "left"
      · subst hk; simp [HolFiniteMapExact.lookup_update, FUPDATE, hsk_l]
      · simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
    have hsk_eq : setVarHOLFinite (ofString "left") (.val (.word 0)) sk = sk := by
      rcases sk with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩
      simp only [setVarHOLFinite] at hloc0 ⊢
      congr
    rw [hsk_eq]
  have hseq_k : evaluateHOLFiniteState sk
      (.seq
        (.while (.op .and [
          .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))),
          .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))]) w1Body)
        (.seq
          (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))) w2Body)
          (.seq
            (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right"))) w3Body)
            (.assign .local (ofString "left") (.var .local (ofString "right")))))) =
      (none, sk) := by
    rw [evaluateHOLFiniteState_seq_line780, hw1]; dsimp only
    rw [evaluateHOLFiniteState_seq_line780, hw2]; dsimp only
    rw [evaluateHOLFiniteState_seq_line780, hw3]; dsimp only
    exact hass_l
  have hdec_k : evaluateHOLFiniteState sj
      (.dec (ofString "k") .one (.var .local (ofString "left"))
        (.seq
          (.while (.op .and [
            .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))),
            .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))]) w1Body)
          (.seq
            (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))) w2Body)
            (.seq
              (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right"))) w3Body)
              (.assign .local (ofString "left") (.var .local (ofString "right"))))))) =
      (none, sj) :=
    eval_dec_resVarEq_self sj (ofString "k") (.var .local (ofString "left")) (.val (.word 0)) _
      (by simp [evalHOLExact, hsj_l]) (by simp [shapeOfHOLExact, shapeEqHOL]) hseq_k
  have hdec_j : evaluateHOLFiniteState si
      (.dec (ofString "j") .one (.var .local (ofString "mid"))
        (.dec (ofString "k") .one (.var .local (ofString "left"))
          (.seq
            (.while (.op .and [
              .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))),
              .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))]) w1Body)
            (.seq
              (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))) w2Body)
              (.seq
                (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right"))) w3Body)
                (.assign .local (ofString "left") (.var .local (ofString "right")))))))) =
      (none, si) :=
    eval_dec_resVarEq_self si (ofString "j") (.var .local (ofString "mid")) (.val (.word 0)) _
      (by simp [evalHOLExact, hsi_m]) (by simp [shapeOfHOLExact, shapeEqHOL]) hdec_k
  exact eval_dec_resVarEq_self s4 (ofString "i") (.var .local (ofString "left")) (.val (.word 0)) _
    (by simp [evalHOLExact, hl]) (by simp [shapeOfHOLExact, shapeEqHOL]) hdec_j

private theorem run_merge_pass_zero
    {w1Body w2Body w3Body : ProgHOL 64}
    {F : Type} (st : PanSemStateFiniteExact 64 F) (bn : BitVec 64)
    (hvl : st.locals.lookup (ofString "left") = some (.val (.word 0)))
    (hvw : st.locals.lookup (ofString "width") = some (.val (.word 0)))
    (hbn : st.locals.lookup (ofString "n") = some (.val (.word bn))) :
    let fullBody : ProgHOL 64 :=
      .dec (ofString "mid") .one (.op .add [.var .local (ofString "left"), .var .local (ofString "width")])
        (.seq
          (.ite (.cmp .lower (.var .local (ofString "n")) (.var .local (ofString "mid")))
            (.assign .local (ofString "mid") (.var .local (ofString "n"))) .skip)
          (.dec (ofString "right") .one (.op .add [.var .local (ofString "mid"), .var .local (ofString "width")])
            (.seq
              (.ite (.cmp .lower (.var .local (ofString "n")) (.var .local (ofString "right")))
                (.assign .local (ofString "right") (.var .local (ofString "n"))) .skip)
              (.dec (ofString "i") .one (.var .local (ofString "left"))
                (.dec (ofString "j") .one (.var .local (ofString "mid"))
                  (.dec (ofString "k") .one (.var .local (ofString "left"))
                    (.seq
                      (.while (.op .and [
                        .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))),
                        .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))]) w1Body)
                      (.seq
                        (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))) w2Body)
                        (.seq
                          (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right"))) w3Body)
                          (.assign .local (ofString "left") (.var .local (ofString "right"))))))))))))
    evaluateHOLFiniteState st fullBody = (none, st) := by
  intro fullBody
  have hcmp0 : wordCmpHOL .lower bn (0#64) = false := by
    simp [wordCmpHOL]
  change evaluateHOLFiniteState st (.dec (ofString "mid") .one _ _) = (none, st)
  rw [evaluateHOLFiniteState_dec_total]
  have hm0_eval : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
      (.op .add [.var .local (ofString "left"), .var .local (ofString "width")]) =
      some (.val (.word 0)) := by
    simp [evalHOLExact, evalListHOLExact, hvl, hvw, valueIsWord, valueWord, wordOpHOL, wordOp]
  dsimp only
  rw [hm0_eval]
  dsimp only
  rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])]
  set s1 := setVarHOLFinite (ofString "mid") (.val (.word 0)) st
  have hs1_mid : s1.locals.lookup (ofString "mid") = some (.val (.word 0)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word bn)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "mid" ≠ ofString "n" by decide, hbn]
  have hs1_w : s1.locals.lookup (ofString "width") = some (.val (.word 0)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "mid" ≠ ofString "width" by decide, hvw]
  have hs1_l : s1.locals.lookup (ofString "left") = some (.val (.word 0)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "mid" ≠ ofString "left" by decide, hvl]
  have hite1 : evaluateHOLFiniteState s1
      (.ite (.cmp .lower (.var .local (ofString "n")) (.var .local (ofString "mid")))
        (.assign .local (ofString "mid") (.var .local (ofString "n"))) .skip) = (none, s1) := by
    rw [evaluateHOLFiniteState_ite]
    have hc : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        (.cmp .lower (.var .local (ofString "n")) (.var .local (ofString "mid"))) =
        some (.val (.word 0)) := by
      simp [evalHOLExact, hs1_n, hs1_mid, hcmp0]
    rw [hc]; simp [evaluateHOLFiniteState_skip]
  rw [evaluateHOLFiniteState_seq_line780, hite1]
  dsimp only
  rw [evaluateHOLFiniteState_dec_total]
  have hr0_eval : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
      (.op .add [.var .local (ofString "mid"), .var .local (ofString "width")]) =
      some (.val (.word 0)) := by
    simp [evalHOLExact, evalListHOLExact, hs1_mid, hs1_w, valueIsWord, valueWord, wordOpHOL, wordOp]
  dsimp only
  rw [hr0_eval]
  dsimp only
  rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])]
  set s3 := setVarHOLFinite (ofString "right") (.val (.word 0)) s1
  have hs3_r : s3.locals.lookup (ofString "right") = some (.val (.word 0)) := by
    simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs3_mid : s3.locals.lookup (ofString "mid") = some (.val (.word 0)) := by
    simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "right" ≠ ofString "mid" by decide, hs1_mid]
  have hs3_n : s3.locals.lookup (ofString "n") = some (.val (.word bn)) := by
    simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "right" ≠ ofString "n" by decide, hs1_n]
  have hs3_l : s3.locals.lookup (ofString "left") = some (.val (.word 0)) := by
    simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "right" ≠ ofString "left" by decide, hs1_l]
  have hite2 : evaluateHOLFiniteState s3
      (.ite (.cmp .lower (.var .local (ofString "n")) (.var .local (ofString "right")))
        (.assign .local (ofString "right") (.var .local (ofString "n"))) .skip) = (none, s3) := by
    rw [evaluateHOLFiniteState_ite]
    have hc : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
        (.cmp .lower (.var .local (ofString "n")) (.var .local (ofString "right"))) =
        some (.val (.word 0)) := by
      simp [evalHOLExact, hs3_n, hs3_r, hcmp0]
    rw [hc]; simp [evaluateHOLFiniteState_skip]
  rw [evaluateHOLFiniteState_seq_line780, hite2]
  dsimp only
  rw [run_merge_inner_zero s3 hs3_l hs3_mid hs3_r]
  dsimp only
  have hloc_r : s3.locals.resVarEq (ofString "right", s1.locals.lookup (ofString "right")) = s1.locals := by
    apply HolFiniteMapExact.ext_lookup
    intro k
    rw [PanRunBounded.resVarEq_lookup]
    by_cases hk : k = ofString "right"
    · subst hk; simp
    · simp [hk, s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
  have hloc_m : s1.locals.resVarEq (ofString "mid", st.locals.lookup (ofString "mid")) = st.locals := by
    apply HolFiniteMapExact.ext_lookup
    intro k
    rw [PanRunBounded.resVarEq_lookup]
    by_cases hk : k = ofString "mid"
    · subst hk; simp
    · simp [hk, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
  have hst_res : ({ s3 with locals := (s3.locals.resVarEq (ofString "right", s1.locals.lookup (ofString "right"))).resVarEq (ofString "mid", st.locals.lookup (ofString "mid")) } : PanSemStateFiniteExact 64 F) = st := by
    rw [hloc_r, hloc_m]; rfl
  rw [hst_res]

private theorem while_stationary_timeout (condition : ExpHOL 64) (body : ProgHOL 64)
    (hstep : ∀ {F : Type} (st : PanSemStateFiniteExact 64 F),
      st.locals.lookup (ofString "left") = some (.val (.word 0)) →
      st.locals.lookup (ofString "width") = some (.val (.word 0)) →
      (∃ bn : BitVec 64, st.locals.lookup (ofString "n") = some (.val (.word bn))) →
      evaluateHOLFiniteState st body = (none, st)) :
    ∀ (clk : Nat) {F : Type} (s : PanSemStateFiniteExact 64 F),
      s.clock = clk →
      s.locals.lookup (ofString "left") = some (.val (.word 0)) →
      s.locals.lookup (ofString "width") = some (.val (.word 0)) →
      (∃ bn : BitVec 64, s.locals.lookup (ofString "n") = some (.val (.word bn))) →
      LoopActive condition s →
      (evaluateHOLFiniteState s (.while condition body)).1 = some .timeOut := by
  intro clk
  induction clk with
  | zero =>
    intro F s hclk _ _ _ ⟨word, hw, hnz⟩
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    rw [evalHOLFinite_eq_toExact] at hw
    have hnz' : word ≠ 0#64 := hnz
    simp [hw, hnz', hclk]
  | succ clk ih =>
    intro F s hclk hl hw0 hn hact
    have hact_dec := loopActive_decClock hact
    obtain ⟨word, hw, hnz⟩ := hact
    have hclk_ne : s.clock ≠ 0 := by omega
    have hrun := hstep (decClockHOLFinite s) hl hw0 hn
    rw [while_unfold_continue condition body s word hw hnz hclk_ne (by rw [hrun]; exact Or.inl rfl)]
    rw [hrun]
    dsimp only
    exact ih (decClockHOLFinite s) (by change s.clock - 1 = clk; omega) hl hw0 hn hact_dec

private theorem while_merge_pass
    {w1Body w2Body w3Body : ProgHOL 64} {Bi : Nat}
    (hinner : TerminatingProgBoundedOn GuestInv
      (.dec (ofString "i") .one (.var .local (ofString "left"))
        (.dec (ofString "j") .one (.var .local (ofString "mid"))
          (.dec (ofString "k") .one (.var .local (ofString "left"))
            (.seq
              (.while (.op .and [
                .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))),
                .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))]) w1Body)
              (.seq
                (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))) w2Body)
                (.seq
                  (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right"))) w3Body)
                  (.assign .local (ofString "left") (.var .local (ofString "right"))))))))) Bi)
    (h1n : avoidsLocal (ofString "n") w1Body = true)
    (h1w : avoidsLocal (ofString "width") w1Body = true)
    (h1r : avoidsLocal (ofString "right") w1Body = true)
    (h1l : avoidsLocal (ofString "left") w1Body = true)
    (h2n : avoidsLocal (ofString "n") w2Body = true)
    (h2w : avoidsLocal (ofString "width") w2Body = true)
    (h2r : avoidsLocal (ofString "right") w2Body = true)
    (h2l : avoidsLocal (ofString "left") w2Body = true)
    (h3n : avoidsLocal (ofString "n") w3Body = true)
    (h3w : avoidsLocal (ofString "width") w3Body = true)
    (h3r : avoidsLocal (ofString "right") w3Body = true)
    (h3l : avoidsLocal (ofString "left") w3Body = true) :
    TerminatingProgBoundedOn MergePassInv
      (.while (.cmp .less (.var .local (ofString "left")) (.var .local (ofString "n")))
        (.dec (ofString "mid") .one (.op .add [.var .local (ofString "left"), .var .local (ofString "width")])
          (.seq
            (.ite (.cmp .lower (.var .local (ofString "n")) (.var .local (ofString "mid")))
              (.assign .local (ofString "mid") (.var .local (ofString "n"))) .skip)
            (.dec (ofString "right") .one (.op .add [.var .local (ofString "mid"), .var .local (ofString "width")])
              (.seq
                (.ite (.cmp .lower (.var .local (ofString "n")) (.var .local (ofString "right")))
                  (.assign .local (ofString "right") (.var .local (ofString "n"))) .skip)
                (.dec (ofString "i") .one (.var .local (ofString "left"))
                  (.dec (ofString "j") .one (.var .local (ofString "mid"))
                    (.dec (ofString "k") .one (.var .local (ofString "left"))
                      (.seq
                        (.while (.op .and [
                          .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))),
                          .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))]) w1Body)
                        (.seq
                          (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))) w2Body)
                          (.seq
                            (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right"))) w3Body)
                            (.assign .local (ofString "left") (.var .local (ofString "right"))))))))))))))
      ((2 ^ 64 + 1) * (Bi + 1)) := by
  have hbodyG : TerminatingProgBoundedOn GuestInv
      (.dec (ofString "mid") .one (.op .add [.var .local (ofString "left"), .var .local (ofString "width")])
        (.seq
          (.ite (.cmp .lower (.var .local (ofString "n")) (.var .local (ofString "mid")))
            (.assign .local (ofString "mid") (.var .local (ofString "n"))) .skip)
          (.dec (ofString "right") .one (.op .add [.var .local (ofString "mid"), .var .local (ofString "width")])
            (.seq
              (.ite (.cmp .lower (.var .local (ofString "n")) (.var .local (ofString "right")))
                (.assign .local (ofString "right") (.var .local (ofString "n"))) .skip)
              (.dec (ofString "i") .one (.var .local (ofString "left"))
                (.dec (ofString "j") .one (.var .local (ofString "mid"))
                  (.dec (ofString "k") .one (.var .local (ofString "left"))
                    (.seq
                      (.while (.op .and [
                        .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))),
                        .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))]) w1Body)
                      (.seq
                        (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))) w2Body)
                        (.seq
                          (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right"))) w3Body)
                          (.assign .local (ofString "left") (.var .local (ofString "right"))))))))))))) Bi := by
    apply dec_guestInv
    apply TerminatingProgBoundedOn.weaken' (K := 0 + (0 + Bi))
    · apply TerminatingProgBoundedOn.seq_guestInv (straightOn _ rfl)
      apply dec_guestInv
      exact TerminatingProgBoundedOn.seq_guestInv (straightOn _ rfl) hinner
    · omega
  refine @TerminatingProgBoundedOn.while_rank_stationary MergePassInv _ _ Bi (2 ^ 64)
    (counterGap .less (ofString "left") (ofString "n"))
    mergePassInv_decClock (fun s hc hp => hbodyG s hc hp.1) ?_ ?_
  · intro F s _ _ _
    simp only [counterGap]
    split
    · rename_i a b _ _
      exact Nat.le_trans (Nat.sub_le _ _) (Nat.le_of_lt (cmpRank_le .less b))
    · exact Nat.zero_le _
  · intro F s _ ⟨hg, hcases⟩ hact hflow
    obtain ⟨word, hw, hnz⟩ := hact
    change evalAt s _ = _ at hw
    obtain ⟨al, bn, hal, hbn, hword⟩ := evalAt_cmp s .less _ _ word hw
    have hal' : s.locals.lookup (ofString "left") = some (.val (.word al)) := by
      simpa [evalAt, evalHOLExact] using hal
    have hbn' : s.locals.lookup (ofString "n") = some (.val (.word bn)) := by
      simpa [evalAt, evalHOLExact] using hbn
    rcases hcases with ⟨vw, vl, hvw, hvl, hwpos, hwnonneg, hlnonneg⟩ | ⟨hvw0, hvl0⟩
    · have hal_eq : vl = al := by
        rw [hvl] at hal'
        injection hal' with h1; injection h1 with h2; injection h2 with h3
      subst hal_eq
      have hcmp : wordCmpHOL .less vl bn = true := by
        cases hc : wordCmpHOL .less vl bn
        · exfalso; rw [hc] at hword; simp at hword; exact hnz hword
        · rfl
      obtain ⟨hnoc, hpost_l_fn⟩ := run_merge_pass_body h1r h1l h2r h2l h3r h3l
        (decClockHOLFinite s) vl vw bn hvl hvw hbn'
      have hnone := hflow.resolve_right hnoc
      have hpost_l := hpost_l_fn hnone
      have havoid_full_w : avoidsLocal (ofString "width")
          (.dec (ofString "mid") .one (.op .add [.var .local (ofString "left"), .var .local (ofString "width")])
            (.seq
              (.ite (.cmp .lower (.var .local (ofString "n")) (.var .local (ofString "mid")))
                (.assign .local (ofString "mid") (.var .local (ofString "n"))) .skip)
              (.dec (ofString "right") .one (.op .add [.var .local (ofString "mid"), .var .local (ofString "width")])
                (.seq
                  (.ite (.cmp .lower (.var .local (ofString "n")) (.var .local (ofString "right")))
                    (.assign .local (ofString "right") (.var .local (ofString "n"))) .skip)
                  (.dec (ofString "i") .one (.var .local (ofString "left"))
                    (.dec (ofString "j") .one (.var .local (ofString "mid"))
                      (.dec (ofString "k") .one (.var .local (ofString "left"))
                        (.seq
                          (.while (.op .and [
                            .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))),
                            .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))]) w1Body)
                          (.seq
                            (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))) w2Body)
                            (.seq
                              (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right"))) w3Body)
                              (.assign .local (ofString "left") (.var .local (ofString "right"))))))))))))) = true := by
        simp [avoidsLocal, h1w, h2w, h3w]; decide
      have havoid_full_n : avoidsLocal (ofString "n")
          (.dec (ofString "mid") .one (.op .add [.var .local (ofString "left"), .var .local (ofString "width")])
            (.seq
              (.ite (.cmp .lower (.var .local (ofString "n")) (.var .local (ofString "mid")))
                (.assign .local (ofString "mid") (.var .local (ofString "n"))) .skip)
              (.dec (ofString "right") .one (.op .add [.var .local (ofString "mid"), .var .local (ofString "width")])
                (.seq
                  (.ite (.cmp .lower (.var .local (ofString "n")) (.var .local (ofString "right")))
                    (.assign .local (ofString "right") (.var .local (ofString "n"))) .skip)
                  (.dec (ofString "i") .one (.var .local (ofString "left"))
                    (.dec (ofString "j") .one (.var .local (ofString "mid"))
                      (.dec (ofString "k") .one (.var .local (ofString "left"))
                        (.seq
                          (.while (.op .and [
                            .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))),
                            .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))]) w1Body)
                          (.seq
                            (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))) w2Body)
                            (.seq
                              (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right"))) w3Body)
                              (.assign .local (ofString "left") (.var .local (ofString "right"))))))))))))) = true := by
        simp [avoidsLocal, h1n, h2n, h3n]; decide
      have hvw_post := (evaluate_avoidsLocal_flowing (ofString "width") _ havoid_full_w
        (decClockHOLFinite s) (Or.inl hnone)).trans hvw
      have hbn_post := (evaluate_avoidsLocal_flowing (ofString "n") _ havoid_full_n
        (decClockHOLFinite s) (Or.inl hnone)).trans hbn'
      obtain ⟨hlt_adv, hr_nonneg⟩ := merge_pass_advance vl vw bn hwpos hwnonneg hlnonneg hcmp
      refine ⟨⟨guestInv_evaluate (decClockHOLFinite s) _ (guestInv_decClock s hg),
        Or.inl ⟨vw, _, hvw_post, hpost_l, hwpos, hwnonneg, hr_nonneg⟩⟩, Or.inl ?_⟩
      simp only [counterGap, hpost_l, hbn_post, hvl, hbn']
      have hlt_bn : cmpRank .less vl < cmpRank .less bn := cmpRank_lt .less (Or.inl rfl) vl bn hcmp
      exact Nat.sub_lt_sub_left hlt_bn hlt_adv
    · have hrun0 := @run_merge_pass_zero w1Body w2Body w3Body _ (decClockHOLFinite s) bn hvl0 hvw0 hbn'
      refine ⟨?_, Or.inr (Or.inl ?_)⟩
      · rw [hrun0]
        exact ⟨guestInv_decClock s hg, Or.inr ⟨hvw0, hvl0⟩⟩
      · rw [hrun0]
        rfl

private noncomputable def outerSortRank {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup (ofString "width") with
  | some (.val (.word w)) =>
      if h : ∃ m : Nat, m ≤ 63 ∧ w.toNat = 2 ^ m then
        65 - Classical.choose h
      else
        0
  | _ => 0

private theorem outerSortRank_eq_of_pow {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w : BitVec 64) (m : Nat)
    (hw : s.locals.lookup (ofString "width") = some (.val (.word w)))
    (hm_le : m ≤ 63) (hm_pow : w.toNat = 2 ^ m) :
    outerSortRank s = 65 - m := by
  simp only [outerSortRank, hw]
  have hex : ∃ k : Nat, k ≤ 63 ∧ w.toNat = 2 ^ k := ⟨m, hm_le, hm_pow⟩
  rw [dif_pos hex]
  have hspec := Classical.choose_spec hex
  have heq : Classical.choose hex = m := by
    have hpow_eq : 2 ^ Classical.choose hex = 2 ^ m := hspec.2.symm.trans hm_pow
    exact (Nat.pow_right_injective (by decide : 1 < 2)) hpow_eq
  rw [heq]

private theorem outerSortRank_eq_zero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hw : s.locals.lookup (ofString "width") = some (.val (.word 0))) :
    outerSortRank s = 0 := by
  simp only [outerSortRank, hw]
  rw [dif_neg]
  rintro ⟨m, _, hm⟩
  have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
  simp at hm
  omega

private theorem pow2_mul2_step (w : BitVec 64) (m : Nat) (hm_le : m ≤ 63) (hm_pow : w.toNat = 2 ^ m) :
    (m < 63 ∧ (w * 2).toNat = 2 ^ (m + 1)) ∨ (m = 63 ∧ w * 2 = 0) := by
  by_cases hlt : m < 63
  · left
    refine ⟨hlt, ?_⟩
    have hm1 : m + 1 ≤ 63 := by omega
    have hpow_lt : 2 ^ (m + 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
    rw [BitVec.toNat_mul]
    have h2 : (2 : BitVec 64).toNat = 2 := by decide
    rw [h2, hm_pow, ← Nat.pow_succ, Nat.mod_eq_of_lt hpow_lt]
  · right
    have hm63 : m = 63 := by omega
    subst hm63
    refine ⟨rfl, ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_mul]
    have h2 : (2 : BitVec 64).toNat = 2 := by decide
    rw [h2, hm_pow]
    decide

private theorem run_swap_tail {F : Type} (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hw : s.locals.lookup (ofString "width") = some (.val (.word w))) :
    let tailProg : ProgHOL 64 :=
      .dec (ofString "swap") .one (.var .local (ofString "src"))
        (.seq (.assign .local (ofString "src") (.var .local (ofString "dst")))
          (.seq (.assign .local (ofString "dst") (.var .local (ofString "swap")))
            (.assign .local (ofString "width")
              (.panop .mul [.var .local (ofString "width"), .const 2#64]))))
    (evaluateHOLFiniteState s tailProg).1 ≠ some .continue ∧
    ((evaluateHOLFiniteState s tailProg).1 = none →
      (evaluateHOLFiniteState s tailProg).2.locals.lookup (ofString "width") =
        some (.val (.word (w * 2)))) := by
  intro tailProg
  change (evaluateHOLFiniteState s (.dec (ofString "swap") .one _ _)).1 ≠ some .continue ∧ _
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  cases hev_src : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString "src")) with
  | none => exact ⟨by simp, by simp⟩
  | some vsrc =>
    dsimp only
    by_cases hsh : shapeEqHOL .one (shapeOfHOLExact vsrc) = true
    · rw [if_pos hsh]
      set s1 := setVarHOLFinite (ofString "swap") vsrc s
      have hs1_w : s1.locals.lookup (ofString "width") = some (.val (.word w)) := by
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "swap" ≠ ofString "width" by decide, hw]
      set a1 : ProgHOL 64 := .assign .local (ofString "src") (.var .local (ofString "dst"))
      set a2 : ProgHOL 64 := .assign .local (ofString "dst") (.var .local (ofString "swap"))
      set a3 : ProgHOL 64 := .assign .local (ofString "width")
        (.panop .mul [.var .local (ofString "width"), .const 2#64])
      have hav1 : avoidsLocal (ofString "width") a1 = true := by decide
      have hav2 : avoidsLocal (ofString "width") a2 = true := by decide
      have hnc1 := evaluate_noTopContinue a1 (by decide) s1
      rw [evaluateHOLFiniteState_seq_line780]
      cases hr1 : evaluateHOLFiniteState s1 a1 with
      | mk r1 s2 =>
        cases r1 with
        | some r =>
          rw [hr1] at hnc1
          exact ⟨by simpa using hnc1, by simp⟩
        | none =>
          have hs2_w : s2.locals.lookup (ofString "width") = some (.val (.word w)) := by
            have hf1 := evaluate_avoidsLocal_flowing (ofString "width") a1 hav1 s1
            rw [hr1] at hf1
            exact (hf1 (Or.inl rfl)).trans hs1_w
          dsimp only
          have hnc2 := evaluate_noTopContinue a2 (by decide) s2
          rw [evaluateHOLFiniteState_seq_line780]
          cases hr2 : evaluateHOLFiniteState s2 a2 with
          | mk r2 s3 =>
            cases r2 with
            | some r =>
              rw [hr2] at hnc2
              exact ⟨by simpa using hnc2, by simp⟩
            | none =>
              have hs3_w : s3.locals.lookup (ofString "width") = some (.val (.word w)) := by
                have hf2 := evaluate_avoidsLocal_flowing (ofString "width") a2 hav2 s2
                rw [hr2] at hf2
                exact (hf2 (Or.inl rfl)).trans hs2_w
              dsimp only
              have hr3 : evaluateHOLFiniteState s3 a3 =
                  (none, setVarHOLFinite (ofString "width") (.val (.word (w * 2))) s3) := by
                simp [a3, evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hs3_w,
                  panOpHOL, valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact,
                  setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
              rw [hr3]
              refine ⟨by simp, fun _ => ?_⟩
              dsimp only
              rw [PanRunBounded.resVarEq_lookup, if_neg (by decide)]
              simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · rw [if_neg hsh]
      exact ⟨by simp, by simp⟩

private theorem dec_width1_outerSortInv {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn OuterSortInv body B) :
    TerminatingProgBoundedOn GuestInv
      (.dec (ofString "width") .one (.const 1) body) B := by
  intro F state hcode hg
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  have hev : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) (.const 1) =
      some (.val (.word 1)) := by
    simp [evalHOLExact]
  dsimp only at hnt ⊢
  rw [hev] at hnt ⊢
  dsimp only at hnt ⊢
  rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])] at hnt ⊢
  have hP : OuterSortInv (setVarHOLFinite (ofString "width") (.val (.word 1)) state) := by
    refine ⟨guestInv_with_locals_clock state _ state.clock hg, 1, ?_, Or.inr ⟨0, by decide, by decide⟩⟩
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hb := hbody (setVarHOLFinite (ofString "width") (.val (.word 1)) state) hcode hP hnt
  simpa [setVarHOLFinite] using hb

private theorem dec_left0_mergePassInv {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn MergePassInv body B) :
    TerminatingProgBoundedOn OuterSortInv
      (.dec (ofString "left") .one (.const 0) body) B := by
  intro F state hcode ⟨hg, w, hw, hw_cases⟩
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  have hev : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) (.const 0) =
      some (.val (.word 0)) := by
    simp [evalHOLExact]
  dsimp only at hnt ⊢
  rw [hev] at hnt ⊢
  dsimp only at hnt ⊢
  rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])] at hnt ⊢
  set s1 := setVarHOLFinite (ofString "left") (.val (.word 0)) state
  have hs1_w : s1.locals.lookup (ofString "width") = some (.val (.word w)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "left" ≠ ofString "width" by decide, hw]
  have hs1_l : s1.locals.lookup (ofString "left") = some (.val (.word 0)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hP : MergePassInv s1 := by
    refine ⟨guestInv_with_locals_clock state _ state.clock hg, ?_⟩
    rcases hw_cases with rfl | ⟨m, hm_le, hm_pow⟩
    · exact Or.inr ⟨hs1_w, hs1_l⟩
    · refine Or.inl ⟨w, 0, hs1_w, hs1_l, ?_, ?_, by decide⟩
      · rw [hm_pow]; exact Nat.two_pow_pos m
      · rw [hm_pow]; exact Nat.pow_le_pow_right (by decide) hm_le
  have hb := hbody s1 hcode hP hnt
  simpa [s1, setVarHOLFinite] using hb

private theorem seq_of_guestInv_tail {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {first second : ProgHOL 64} {a b : Nat}
    (hPG : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → GuestInv s)
    (h1 : TerminatingProgBoundedOn P first a)
    (h2 : TerminatingProgBoundedOn GuestInv second b) :
    TerminatingProgBoundedOn P (.seq first second) (a + b) := by
  intro F state hcode hP
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata state first
  have hmid := guestInv_evaluate state first (hPG state hP)
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr1 : evaluateHOLFiniteState state first with ⟨r1, mid⟩
  simp only [hr1] at hmeta hnt hmid ⊢
  cases r1 with
  | none =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simp [hr1]
    obtain ⟨s1, k1⟩ := h1 state hcode hP hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    obtain ⟨s2, k2⟩ := h2 mid (hmeta.1.trans hcode) hmid hnt
    exact ⟨by omega, by omega⟩
  | some r =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simpa [hr1] using hnt
    obtain ⟨s1, k1⟩ := h1 state hcode hP hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    exact ⟨by omega, k1⟩

theorem fb_sort_elems :
    TerminatingFunBoundedOn GuestInv (ofString "sort_elems") K.«sort_elems» := by
  have h0 := P12_P15.Callees.fb_heap_mark
  have h1 := P12_P15.Callees.fb_alloc
  have h2 := fb_bal_sort_gt
  have h3 := P12_P15.Callees.fb_memcpy
  have h4 := P12_P15.Callees.fb_heap_release
  fb_unfold 430 Guest.Software.guestFn_sort_elems
  apply TerminatingProgBoundedOn.weaken'
  · apply TerminatingProgBoundedOn.seq_guestInv
    · fb_auto2
    · apply decCall_guestInv' h0
      apply decCall_guestInv' h1
      apply dec_guestInv
      apply dec_guestInv
      apply dec_width1_outerSortInv
      apply seq_of_guestInv_tail (fun s hp => hp.1)
      · refine @TerminatingProgBoundedOn.while_rank OuterSortInv
          (.cmp .less (.var .local (ofString "width")) (.var .local (ofString "n"))) _
          ((2 ^ 64 + 1) * (((2 ^ 65 + 1) * ((K.«bal_sort_gt» + 1) + (K.«memcpy» + 1) + 1) +
            (2 ^ 64 + 1) * ((K.«memcpy» + 1) + 1) +
            (2 ^ 64 + 1) * ((K.«memcpy» + 1) + 1)) + 1) + 0)
          65 outerSortRank outerSortInv_decClock ?_ ?_ ?_
        · apply dec_left0_mergePassInv
          apply seq_of_guestInv_tail (fun s hp => hp.1)
          · apply while_merge_pass
            · apply dec_guestInv
              apply dec_guestInv
              apply dec_guestInv
              apply TerminatingProgBoundedOn.weaken'
                (K' := (2 ^ 65 + 1) * ((K.«bal_sort_gt» + 1) + (K.«memcpy» + 1) + 1) +
                  (2 ^ 64 + 1) * ((K.«memcpy» + 1) + 1) +
                  (2 ^ 64 + 1) * ((K.«memcpy» + 1) + 1))
              · apply TerminatingProgBoundedOn.seq_guestInv
                · apply while_merge_guestInv
                  fb_auto2
                · apply TerminatingProgBoundedOn.seq_guestInv
                  · apply while_counter_step_guestInv .less (Or.inl rfl)
                    · fb_auto2
                    · apply CounterStep.seq _ _ _ rfl rfl
                      exact CounterStep.suffix _ _ _ (CounterStep.assign _ _) rfl
                    · rfl
                    · rfl
                  · apply TerminatingProgBoundedOn.seq_guestInv
                    · apply while_counter_step_guestInv .less (Or.inl rfl)
                      · fb_auto2
                      · apply CounterStep.seq _ _ _ rfl rfl
                        exact CounterStep.suffix _ _ _ (CounterStep.assign _ _) rfl
                      · rfl
                      · rfl
                    · exact straightOn _ rfl
              · generalize_K; try simp only [nat_max_eq]
                omega
            · decide
            · decide
            · decide
            · decide
            · decide
            · decide
            · decide
            · decide
            · decide
            · decide
            · decide
            · decide
          · exact straightOn _ rfl
        · intro F s _ _ _
          simp only [outerSortRank]
          split
          · split <;> omega
          · omega
        · intro F s _ ⟨hg, w, hw, hw_cases⟩ hact hflow
          obtain ⟨word, hw_ev, hnz⟩ := hact
          change evalAt s _ = _ at hw_ev
          obtain ⟨aw, bn, haw, hbn, hword⟩ := evalAt_cmp s .less _ _ word hw_ev
          have haw' : s.locals.lookup (ofString "width") = some (.val (.word aw)) := by
            simpa [evalAt, evalHOLExact] using haw
          have hbn' : s.locals.lookup (ofString "n") = some (.val (.word bn)) := by
            simpa [evalAt, evalHOLExact] using hbn
          have haw_eq : w = aw := by
            rw [hw] at haw'
            injection haw' with e1; injection e1 with e2; injection e2 with e3
          subst haw_eq
          have hcmp_wn : wordCmpHOL .less w bn = true := by
            cases hc : wordCmpHOL .less w bn
            · exfalso; rw [hc] at hword; simp at hword; exact hnz hword
            · rfl
          set sd := decClockHOLFinite s
          set s1 := setVarHOLFinite (ofString "left") (.val (.word 0#64)) sd
          have hsd_w : sd.locals.lookup (ofString "width") = some (.val (.word w)) := hw
          have hsd_n : sd.locals.lookup (ofString "n") = some (.val (.word bn)) := hbn'
          have hs1_l : s1.locals.lookup (ofString "left") = some (.val (.word 0#64)) := by
            simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hs1_w : s1.locals.lookup (ofString "width") = some (.val (.word w)) := by
            simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "left" ≠ ofString "width" by decide, hsd_w]
          have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word bn)) := by
            simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "left" ≠ ofString "n" by decide, hsd_n]
          let midLoop : ProgHOL 64 :=
            .while (.cmp .less (.var .local (ofString "left")) (.var .local (ofString "n")))
              (.dec (ofString "mid") .one (.op .add [.var .local (ofString "left"), .var .local (ofString "width")])
                (.seq
                  (.ite (.cmp .lower (.var .local (ofString "n")) (.var .local (ofString "mid")))
                    (.assign .local (ofString "mid") (.var .local (ofString "n"))) .skip)
                  (.dec (ofString "right") .one (.op .add [.var .local (ofString "mid"), .var .local (ofString "width")])
                    (.seq
                      (.ite (.cmp .lower (.var .local (ofString "n")) (.var .local (ofString "right")))
                        (.assign .local (ofString "right") (.var .local (ofString "n"))) .skip)
                      (.dec (ofString "i") .one (.var .local (ofString "left"))
                        (.dec (ofString "j") .one (.var .local (ofString "mid"))
                          (.dec (ofString "k") .one (.var .local (ofString "left"))
                            (.seq
                              (.while (.op .and [
                                .cmp .notEqual (.const 0#64) (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))),
                                .cmp .notEqual (.const 0#64) (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))])
                                (.dec (ofString "a") .one (.op .add [.var .local (ofString "src"), .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]])
                                  (.dec (ofString "b") .one (.op .add [.var .local (ofString "src"), .panop .mul [.var .local (ofString "j"), .var .local (ofString "esz")]])
                                    (.decCall (ofString "gt") .one (ofString "bal_sort_gt") [.var .local (ofString "a"), .var .local (ofString "b"), .var .local (ofString "kind")]
                                      (.seq
                                        (.ite (.cmp .equal (.var .local (ofString "gt")) (.const 0#64))
                                          (.seq (.call (some (none, none)) (ofString "memcpy") [.op .add [.var .local (ofString "dst"), .panop .mul [.var .local (ofString "k"), .var .local (ofString "esz")]], .var .local (ofString "a"), .var .local (ofString "esz")])
                                            (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])))
                                          (.seq (.call (some (none, none)) (ofString "memcpy") [.op .add [.var .local (ofString "dst"), .panop .mul [.var .local (ofString "k"), .var .local (ofString "esz")]], .var .local (ofString "b"), .var .local (ofString "esz")])
                                            (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1#64]))))
                                        (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1#64])))))))
                              (.seq
                                (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid")))
                                  (.seq (.call (some (none, none)) (ofString "memcpy") [.op .add [.var .local (ofString "dst"), .panop .mul [.var .local (ofString "k"), .var .local (ofString "esz")]], .op .add [.var .local (ofString "src"), .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]], .var .local (ofString "esz")])
                                    (.seq (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))
                                      (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1#64])))))
                                (.seq
                                  (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))
                                    (.seq (.call (some (none, none)) (ofString "memcpy") [.op .add [.var .local (ofString "dst"), .panop .mul [.var .local (ofString "k"), .var .local (ofString "esz")]], .op .add [.var .local (ofString "src"), .panop .mul [.var .local (ofString "j"), .var .local (ofString "esz")]], .var .local (ofString "esz")])
                                      (.seq (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1#64]))
                                        (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1#64])))))
                                  (.assign .local (ofString "left") (.var .local (ofString "right")))))))))))))
          rcases hw_cases with rfl | ⟨m, hm_le, hm_pow⟩
          · exfalso
            rw [evaluateHOLFiniteState_dec_total] at hflow
            have hev0 : @evalHOLExact 64 F _ sd.toExact
                (fun a => Classical.propDecidable (sd.memaddrs a)) (.const 0#64) =
                some (.val (.word 0#64)) := by simp [evalHOLExact]
            dsimp only at hflow
            rw [hev0] at hflow
            dsimp only at hflow
            rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])] at hflow
            rw [evaluateHOLFiniteState_seq_line780] at hflow
            have hact_mid : LoopActive (.cmp .less (.var .local (ofString "left")) (.var .local (ofString "n"))) s1 := by
              refine ⟨1#64, ?_, by decide⟩
              rw [evalHOLFinite_eq_toExact]
              simp only [evalHOLExact, hs1_l, hs1_n]
              change some (ValueHOL.val (HolWordLab.word (if wordCmpHOL .less 0#64 bn then 1#64 else 0#64))) = _
              rw [show (0#64 : BitVec 64) = 0 from rfl, hcmp_wn]
              rfl
            have hto : (evaluateHOLFiniteState s1 midLoop).1 = some .timeOut :=
              while_stationary_timeout _ _
                (fun st hst_l hst_w ⟨bn0, hst_n⟩ => run_merge_pass_zero st bn0 hst_l hst_w hst_n)
                s1.clock s1 rfl hs1_l hs1_w ⟨bn, hs1_n⟩ hact_mid
            rcases hmid_eq : evaluateHOLFiniteState s1 _ with ⟨rmid, smid⟩
            have hmid_eq_def : evaluateHOLFiniteState s1 midLoop = (rmid, smid) := hmid_eq
            rw [hmid_eq] at hflow
            rw [hmid_eq_def] at hto
            dsimp only at hto
            subst hto
            simp at hflow
          · rw [evaluateHOLFiniteState_dec_total] at hflow ⊢
            have hev0 : @evalHOLExact 64 F _ sd.toExact
                (fun a => Classical.propDecidable (sd.memaddrs a)) (.const 0#64) =
                some (.val (.word 0#64)) := by simp [evalHOLExact]
            dsimp only at hflow ⊢
            rw [hev0] at hflow ⊢
            dsimp only at hflow ⊢
            rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])] at hflow ⊢
            rw [evaluateHOLFiniteState_seq_line780] at hflow ⊢
            have havoid_mid_w : avoidsLocal (ofString "width") midLoop = true := by
              decide
            have hnc_mid := evaluate_noTopContinue midLoop (by decide) s1
            rcases hmid_run : evaluateHOLFiniteState s1 _ with ⟨rmid, smid⟩
            have hmid_run_def : evaluateHOLFiniteState s1 midLoop = (rmid, smid) := hmid_run
            rw [hmid_run] at hflow
            rw [hmid_run_def] at hnc_mid
            cases rmid with
            | some r =>
              exfalso
              dsimp only at hflow hnc_mid
              rcases hflow with h | h
              · simp at h
              · exact hnc_mid h
            | none =>
              dsimp only at hflow ⊢
              have hsmid_w : smid.locals.lookup (ofString "width") = some (.val (.word w)) := by
                have hf := evaluate_avoidsLocal_flowing (ofString "width") midLoop havoid_mid_w s1
                rw [hmid_run_def] at hf
                exact (hf (Or.inl rfl)).trans hs1_w
              obtain ⟨hnc_tail, htail_w⟩ := run_swap_tail smid w hsmid_w
              rcases htail_run : evaluateHOLFiniteState smid _ with ⟨rtail, stail⟩
              rw [htail_run] at hflow hnc_tail htail_w
              dsimp only at hflow hnc_tail htail_w ⊢
              have hrtail_none : rtail = none := by
                rcases hflow with h | h
                · exact h
                · exact absurd h hnc_tail
              subst hrtail_none
              have hstail_w := htail_w rfl
              set sp := ({ stail with locals := stail.locals.resVarEq (ofString "left", sd.locals.lookup (ofString "left")) } : PanSemStateFiniteExact 64 F)
              have hpost_w : sp.locals.lookup (ofString "width") =
                  some (.val (.word (w * 2))) := by
                change (stail.locals.resVarEq (ofString "left", sd.locals.lookup (ofString "left"))).lookup (ofString "width") = _
                rw [PanRunBounded.resVarEq_lookup, if_neg (by decide)]
                exact hstail_w
              have hguest_post : GuestInv sp := by
                have hg_s1 : GuestInv s1 := guestInv_with_locals_clock sd _ sd.clock (guestInv_decClock s hg)
                have hg_smid : GuestInv smid := by
                  have hge := guestInv_evaluate s1 midLoop hg_s1
                  rw [hmid_run_def] at hge; exact hge
                have hg_stail : GuestInv stail := by
                  have hge := guestInv_evaluate smid
                    (.dec (ofString "swap") .one (.var .local (ofString "src"))
                      (.seq (.assign .local (ofString "src") (.var .local (ofString "dst")))
                        (.seq (.assign .local (ofString "dst") (.var .local (ofString "swap")))
                          (.assign .local (ofString "width")
                            (.panop .mul [.var .local (ofString "width"), .const 2#64]))))) hg_smid
                  rw [htail_run] at hge; exact hge
                exact guestInv_with_locals_clock stail _ stail.clock hg_stail
              have hstep_pow := pow2_mul2_step w m hm_le hm_pow
              have hr_before := outerSortRank_eq_of_pow s w m hw hm_le hm_pow
              rcases hstep_pow with ⟨hlt63, hm1_pow⟩ | ⟨rfl, hw2_zero⟩
              · refine ⟨⟨hguest_post, w * 2, hpost_w, Or.inr ⟨m + 1, by omega, hm1_pow⟩⟩, ?_⟩
                have hr_after := outerSortRank_eq_of_pow sp (w * 2) (m + 1) hpost_w (by omega) hm1_pow
                omega
              · have hpost_w0 : sp.locals.lookup (ofString "width") =
                    some (.val (.word 0)) := by
                  rw [← hw2_zero]
                  exact hpost_w
                refine ⟨⟨hguest_post, 0, hpost_w0, Or.inl rfl⟩, ?_⟩
                have hr_after := outerSortRank_eq_zero sp hpost_w0
                omega
      · fb_auto2
  · fb_arith K.«sort_elems»

theorem fb_sorted_keys32 :
    TerminatingFunBoundedOn GuestInv (ofString "sorted_keys32") K.«sorted_keys32» := by
  have h0 := fb_htab_keys
  have h1 := fb_sort_elems
  fb_prove2 431 Guest.Software.guestFn_sorted_keys32 K.«sorted_keys32»

theorem fb_bal_encode_account :
    TerminatingFunBoundedOn GuestInv (ofString "bal_encode_account") K.«bal_encode_account» := by
  have h0 := InitECandidate.Solver.Wave8Leaves.Rlp.fb_rlp_encode_bytes
  have h1 := P12_P15.Callees.fb_heap_mark
  have h2 := fb_sorted_keys32
  have h3 := PrimShardP10P30.fb_htab_get
  have h4 := fb_sort_elems
  have h5 := P12_P15.Callees.fb_u256_from_be
  have h6 := R11Adapters.«fb_rlp_put_u256»
  have h7 := InitECandidate.Solver.Wave8Leaves.Rlp.fb_rlp_encode_word
  have h8 := InitECandidate.Solver.Wave8Leaves.Rlp.fb_rlp_list_header_len
  have h9 := P12_P15.Callees.fb_memcpy
  have h10 := InitECandidate.Solver.Wave8Leaves.Rlp.fb_rlp_encode_list_header
  have h11 := fb_htab_keys
  have h12 := PrimShardP10P30.fb_htab_has
  have h13 := P12_P15.Callees.fb_heap_release
  fb_prove2 432 Guest.Software.guestFn_bal_encode_account K.«bal_encode_account»

theorem fb_build_block_access_list_rlp :
    TerminatingFunBoundedOn GuestInv (ofString "build_block_access_list_rlp") K.«build_block_access_list_rlp» := by
  have h0 := PrimShardP10P30.fb_htab_item
  have h1 := fb_add_storage_read
  have h2 := fb_add_touched_account
  have h3 := P12_P15.Callees.fb_alloc
  have h4 := fb_htab_keys
  have h5 := fb_sort_elems
  have h6 := PrimShardP10P30.fb_htab_get
  have h7 := fb_bal_encode_account
  have h8 := InitECandidate.Solver.Wave8Leaves.Rlp.fb_rlp_list_header_len
  have h9 := InitECandidate.Solver.Wave8Leaves.Rlp.fb_rlp_encode_list_header
  fb_prove2 433 Guest.Software.guestFn_build_block_access_list_rlp K.«build_block_access_list_rlp»

end InitECandidate.Solver.Wave8GuestInv.R11Adapters.BalRlp
