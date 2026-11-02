import InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.FbRlp

/-!
# PrimShardP10P30.FbSetStorage

Proves `TerminatingFunBoundedOn GuestInv` for `fb_set_storage` (Target #3) and its remaining
RLP / MPT / world-state callees on `wave8/spec-r11`:
- `fb_rlp_list_count` (`((domainBytes + 1) + 1) * ...`)
- `fb_rlp_item`
- `fb_rlp_decode_fully`
- `fb_rlp_list_to_slices`
- `fb_decode_account_from_leaf`
- `fb_trie_walk` (`(71723149827058354885847154688 + 1) * ...`)
- `fb_trie_lookup`
- `fb_ws_account_leaf`
- `fb_ws_get_account_optional`
- `fb_get_pre_state_account_optional`
- `fb_get_account_optional`
- `fb_set_storage`
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestUniformClockBound

/-! ### `fb_rlp_list_count` (`((domainBytes + 1) + 1) * ((K.rlp_item_total + 1) + 1)`) -/

section RlpListCount

theorem R_decCall' {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {n : MlS}
    {sh : ShapeHOL} {f : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (h : ∀ (values : List (ValueHOL 64)) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
      (rs : ShapeHOL) (v : ValueHOL 64),
      evalListHOLFinite s (h := fun address => Classical.propDecidable (s.memaddrs address)) args =
        some values →
      lookupCodeHOLFinite s.code.lookup f values = some (body, callee, rs) →
      (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1 = some (.returned v) →
      shapeEqHOL (shapeOfHOLExact v) sh = true →
      ∀ (u : PanSemStateFiniteExact 64 F), u.code = s.code →
        (∀ k, k ≠ n → u.locals.lookup k = s.locals.lookup k) → u.locals.lookup n = some v →
        RetOK Q u cont) :
    RetOK Q s (.decCall n sh f args cont) := by
  intro v hv
  rw [evaluateHOLFiniteState_decCall_total] at hv
  split at hv
  · simp at hv
  · rename_i values hargs
    split at hv
    · simp at hv
    · rename_i body callee rs hl
      split at hv
      · simp at hv
      · have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, st⟩
        rw [hrun] at hmeta
        change st.code = s.code at hmeta
        simp only [hrun] at hv
        rcases r with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only at hv <;> try simp at hv
        split at hv
        · rename_i hsh
          try simp only [Bool.and_eq_true] at hsh
          refine h values body callee rs w hargs hl (by rw [hrun]) hsh.1 _
            (by simp [setVarHOLFinite, fixClockHOLFinite, hmeta]) ?_ ?_ v hv
          · intro k hk
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
          · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        · simp at hv

theorem lookup_total' : originalRuntimeCode.lookup (ofString "rlp_item_total") =
    some ([(ofString "p", .one), (ofString "len", .one)],
      sourceFnBody Guest.Software.guestFn_rlp_item_total, .one) :=
  lookup_of_guestAst_getElem 112 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_item_total) rfl

theorem call_flow_locals {F : Type} (s : PanSemStateFiniteExact 64 F) (f : MlS) (args : List (ExpHOL 64))
    (mid : PanSemStateFiniteExact 64 F)
    (h : evaluateHOLFiniteState s (.call (some (none, none)) f args) = (none, mid)) :
    mid.locals = s.locals ∧ mid.code = s.code := by
  have hmeta := (evaluateHOLFiniteState_metadata s (.call (some (none, none)) f args)).1
  rw [h] at hmeta
  refine ⟨?_, hmeta⟩
  revert h
  rw [evaluateHOLFiniteState_call]
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s _) _ with ⟨r, st⟩
        rcases r with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only <;> (repeat' split) <;> simp
        intro h; rw [← h]

def TotQDom (P L : BitVec 64) (v : ValueHOL 64) : Prop :=
  ∃ t : BitVec 64, v = .val (.word t) ∧ 1 ≤ t.toNat ∧ t.toNat ≤ L.toNat ∧
    sourceBase ≤ P.toNat ∧ P.toNat < heapEnd

theorem total_post_dom {F : Type} (e : PanSemStateFiniteExact 64 F)
    (hcode : e.code = originalRuntimeCode) (hP : GuestInv e)
    (P L : BitVec 64)
    (hp : e.locals.lookup (ofString "p") = some (.val (.word P)))
    (hl : e.locals.lookup (ofString "len") = some (.val (.word L))) :
    RetOK (TotQDom P L) e (sourceFnBody Guest.Software.guestFn_rlp_item_total) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_item_total,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine R_decCall' (fun values body callee rs v hargs hlk hret hsh u hcu hloc hu => ?_)
  simp only [evalListHOLFinite_eq_toExact, evalListHOLExact, evalHOLExact, hp, hl, Option.some.injEq] at hargs
  subst hargs
  rw [hcode] at hlk
  obtain ⟨rfl, hcp, hcl⟩ := callee_p_len lookup_hdr' _ _ body callee rs hlk
  obtain ⟨⟨a, b, c, rfl, h1, h2, _⟩, hp_lo, hp_hi⟩ :=
    hdr_post_dom (callEntryStateHOLFinite e callee) hcode (guestInv_callEntry e callee hP) P L hcp hcl v hret
  refine R_seq (R_ite (fun w _ => ⟨fun _ v hv => absurd hv (call_noret u _ _ v), fun _ => R_skip⟩))
    (fun mid hmid => ?_)
  have hmid_h : mid.locals.lookup (ofString "h") = some (hval a b c) := by
    rw [evaluateHOLFiniteState_ite] at hmid
    split at hmid
    · split at hmid
      · rw [evaluateHOLFiniteState_skip] at hmid
        simp only [Prod.mk.injEq] at hmid
        rw [← hmid.2]; exact hu
      · rw [(call_flow_locals u _ _ mid hmid).1]; exact hu
    · simp at hmid
  refine R_ret (fun v hv => ?_)
  simp [evalHOLExact, evalListHOLExact, hmid_h, hval, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
  subst hv
  refine ⟨a + b, rfl, ?_, ?_, hp_lo, hp_hi⟩
  · rw [BitVec.toNat_add_of_lt (by have := L.isLt; omega)]; omega
  · rw [BitVec.toNat_add_of_lt (by have := L.isLt; omega)]; omega

theorem decCall_flow {F : Type} {s : PanSemStateFiniteExact 64 F} {n : MlS} {sh : ShapeHOL} {f : MlS}
    {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hflow : (evaluateHOLFiniteState s (.decCall n sh f args cont)).1 = none) :
    ∃ (values : List (ValueHOL 64)) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
      (rs : ShapeHOL) (v : ValueHOL 64),
      evalListHOLFinite s (h := fun address => Classical.propDecidable (s.memaddrs address)) args =
        some values ∧
      lookupCodeHOLFinite s.code.lookup f values = some (body, callee, rs) ∧
      (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1 = some (.returned v) ∧
      ∃ u : PanSemStateFiniteExact 64 F, u.code = s.code ∧
        (∀ k, k ≠ n → u.locals.lookup k = s.locals.lookup k) ∧ u.locals.lookup n = some v ∧
        (evaluateHOLFiniteState u cont).1 = none ∧
        ∀ k, k ≠ n → (evaluateHOLFiniteState s (.decCall n sh f args cont)).2.locals.lookup k =
          (evaluateHOLFiniteState u cont).2.locals.lookup k := by
  revert hflow
  rw [evaluateHOLFiniteState_decCall_total]
  split
  · simp
  rename_i values hargs
  split
  · simp
  rename_i body callee rs hl
  split
  · simp
  have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).1
  rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, st⟩
  rw [hrun] at hmeta
  change st.code = s.code at hmeta
  simp only [hrun]
  cases r with
  | none => simp
  | some r =>
    cases r with
    | returned w =>
      dsimp only
      split
      · intro hflow
        refine ⟨values, body, callee, rs, w, hargs, hl, by rw [hrun], _,
          by simp [setVarHOLFinite, fixClockHOLFinite, hmeta], ?_, ?_, hflow, ?_⟩
        · intro k hk
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
        · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        · intro k hk
          simp only
          rw [PanRunBounded.resVarEq_lookup, if_neg hk]
      · simp
    | _ => simp

def countCond : ExpHOL 64 := .cmp .lower (.var .local (ofString "off")) (.var .local (ofString "len"))

def countBody : ProgHOL 64 :=
  .decCall (ofString "total") .one (ofString "rlp_item_total")
    [.op .add [.var .local (ofString "p"), .var .local (ofString "off")],
      .op .sub [.var .local (ofString "len"), .var .local (ofString "off")]]
    (.seq (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "total")]))
      (.assign .local (ofString "count") (.op .add [.var .local (ofString "count"), .const 1])))

theorem countBody_bound : TerminatingProgBoundedOn GuestInv countBody (K.«rlp_item_total» + 0 + 1) :=
  decCall_guestInv' fb_rlp_item_total (straightOn _ rfl)

theorem countBody_step {F : Type} (s : PanSemStateFiniteExact 64 F) (P y m : BitVec 64)
    (hcode : s.code = originalRuntimeCode) (hP : GuestInv s)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word P)))
    (hy : s.locals.lookup (ofString "off") = some (.val (.word y)))
    (hm : s.locals.lookup (ofString "len") = some (.val (.word m)))
    (hlt : y.toNat < m.toNat)
    (hflow : (evaluateHOLFiniteState s countBody).1 = none) :
    ∃ T : BitVec 64,
      1 ≤ T.toNat ∧ y.toNat + T.toNat ≤ m.toNat ∧
      sourceBase ≤ (P + y).toNat ∧ (P + y).toNat < heapEnd ∧
      (evaluateHOLFiniteState s countBody).2.locals.lookup (ofString "off") = some (.val (.word (y + T))) ∧
      (evaluateHOLFiniteState s countBody).2.locals.lookup (ofString "p") = some (.val (.word P)) ∧
      (evaluateHOLFiniteState s countBody).2.locals.lookup (ofString "len") = some (.val (.word m)) := by
  unfold countBody at hflow ⊢
  obtain ⟨values, body, callee, rs, v, hargs, hl, hret, u, hcu, hloc, hu, hcont, hfin⟩ := decCall_flow hflow
  simp only [evalListHOLFinite_eq_toExact, evalListHOLExact, evalHOLExact, hp, hy, hm,
    wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self,
    ↓reduceIte, List.foldr, add_zero, Option.some.injEq] at hargs
  subst hargs
  rw [hcode] at hl
  obtain ⟨rfl, hcp, hcl⟩ := callee_p_len lookup_total' _ _ body callee rs hl
  have hsub : (m - y).toNat = m.toNat - y.toNat := by rw [BitVec.toNat_sub]; omega
  obtain ⟨T, rfl, hT1, hT2, hpy_lo, hpy_hi⟩ :=
    total_post_dom (callEntryStateHOLFinite s callee) hcode (guestInv_callEntry s callee hP)
      (P + y) (m - y) hcp hcl v hret
  rw [hsub] at hT2
  have huoff : u.locals.lookup (ofString "off") = some (.val (.word y)) := by
    rw [hloc _ (by decide)]; exact hy
  have hfirst : evaluateHOLFiniteState u
      (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "total")])) =
      (none, setKvarHOLFinite .local (ofString "off") (.val (.word (y + T))) u) := by
    rw [evaluateHOLFiniteState_assign]
    simp [evalHOLExact, evalListHOLExact, huoff, hu, wordOpHOL, wordOp, valueIsWord, valueWord,
      isValidValueHOLFinite, lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL]
  have hc2 := hcont
  rw [evaluateHOLFiniteState_seq_line780, hfirst] at hc2
  dsimp only at hc2
  have hkeep_off := evaluate_avoidsLocal_flowing (ofString "off")
    (.assign .local (ofString "count") (.op .add [.var .local (ofString "count"), .const 1]))
    (by decide) (setKvarHOLFinite .local (ofString "off") (.val (.word (y + T))) u)
    (Or.inl hc2)
  have hkp := evaluate_avoidsLocal_flowing (ofString "p") countBody (by decide) s (Or.inl hflow)
  have hklen := evaluate_avoidsLocal_flowing (ofString "len") countBody (by decide) s (Or.inl hflow)
  refine ⟨T, hT1, by omega, hpy_lo, hpy_hi, ?_, hkp.trans hp, hklen.trans hm⟩
  rw [hfin (ofString "off") (by decide), evaluateHOLFiniteState_seq_line780, hfirst]
  dsimp only
  rw [hkeep_off]
  simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

def CountLoopInv {F : Type} (s : PanSemStateFiniteExact 64 F) (vis : Finset (Fin domainBytes)) : Prop :=
  GuestInv s ∧
  ∃ P y m : BitVec 64,
    s.locals.lookup (ofString "p") = some (.val (.word P)) ∧
    s.locals.lookup (ofString "off") = some (.val (.word y)) ∧
    s.locals.lookup (ofString "len") = some (.val (.word m)) ∧
    ∀ k ∈ vis, ∃ d : BitVec 64, d.toNat < y.toNat ∧
      sourceBase ≤ (P + d).toNat ∧ (P + d).toNat < heapEnd ∧
      k.val = (P + d).toNat - sourceBase

theorem count_while_aux :
    ∀ (fuel : Nat) {F : Type} (s : PanSemStateFiniteExact 64 F) (vis : Finset (Fin domainBytes)),
      s.code = originalRuntimeCode →
      CountLoopInv s vis →
      domainBytes - vis.card ≤ fuel →
      TerminatingRunBounded s (.while countCond countBody)
        ((fuel + 1) * ((K.«rlp_item_total» + 0 + 1) + 1)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro F s vis hcode hinv hfuel hnt
    have hnt0 := hnt
    obtain ⟨hG, P, y, m, hp, hy, hm, hvis⟩ := hinv
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    split; swap; · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    rename_i word hword
    simp only [hword] at hnt
    by_cases hzero : word = 0
    · rw [if_neg (by simp [hzero])]; exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    · rw [if_pos hzero] at hnt ⊢
      by_cases hclk : s.clock = 0
      · rw [if_pos hclk] at hnt; exact absurd rfl hnt
      · rw [if_neg hclk] at hnt ⊢
        obtain ⟨y', m', hy', hm', hlt⟩ := eval_lower_locals s
          (h := fun a => Classical.propDecidable (s.memaddrs a))
          (ofString "off") (ofString "len") word (by rw [← evalHOLFinite_eq_toExact]; exact hword) hzero
        have hy_eq : y' = y := by rw [hy] at hy'; injection hy' with h; injection h with h; injection h with h; exact h.symm
        have hm_eq : m' = m := by rw [hm] at hm'; injection hm' with h; injection h with h; injection h with h; exact h.symm
        subst y'; subst m'
        set sd := decClockHOLFinite s
        have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
        have hb := countBody_bound sd hcode hGd
        have hnc := evaluate_noTopContinue countBody rfl sd
        unfold TerminatingRunBounded at hb
        rcases hrun : evaluateHOLFiniteState sd countBody with ⟨res, post⟩
        simp only [sd, hrun] at hnt hb hnc ⊢
        cases res with
        | some r =>
          cases r with
          | «continue» => exact absurd rfl hnc
          | timeOut => exact absurd rfl hnt
          | _ =>
            obtain ⟨hspent, hkept⟩ := hb (by simp)
            change s.clock - 1 ≤ post.clock + (K.«rlp_item_total» + 0 + 1) at hspent
            change post.clock ≤ s.clock - 1 at hkept
            dsimp only
            exact ⟨by omega, by omega⟩
        | none =>
          -- Impossible! `countBody_step` gives a fresh `k_now ∉ vis`, contradicting `domainBytes ≤ vis.card`!
          obtain ⟨T, _, _, hpy_lo, hpy_hi, _, _, _⟩ :=
            countBody_step sd P y m hcode hGd hp hy hm hlt (by rw [hrun])
          have hk_lt : (P + y).toNat - sourceBase < domainBytes := by
            have eD : domainBytes = heapEnd - sourceBase := rfl; omega
          let k_now : Fin domainBytes := ⟨(P + y).toNat - sourceBase, hk_lt⟩
          have hfresh : k_now ∉ vis := by
            intro hmem
            obtain ⟨d, hd_lt, _, _, hk_eq⟩ := hvis k_now hmem
            have hbv : P + d = P + y := BitVec.eq_of_toNat_eq (by change (P + y).toNat - sourceBase = _ at hk_eq; omega)
            have hdy : d = y := by
              have hsub := congrArg (fun x => -P + x) hbv
              simpa [← BitVec.add_assoc] using hsub
            subst hdy; omega
          have hle : (insert k_now vis).card ≤ domainBytes := by
            simpa using Finset.card_le_univ (insert k_now vis)
          rw [Finset.card_insert_of_notMem hfresh] at hle
          omega
  | succ n ih =>
    intro F s vis hcode hinv hfuel hnt
    have hnt0 := hnt
    obtain ⟨hG, P, y, m, hp, hy, hm, hvis⟩ := hinv
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    split; swap; · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    rename_i word hword
    simp only [hword] at hnt
    by_cases hzero : word = 0
    · rw [if_neg (by simp [hzero])]; exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    · rw [if_pos hzero] at hnt ⊢
      by_cases hclk : s.clock = 0
      · rw [if_pos hclk] at hnt; exact absurd rfl hnt
      · rw [if_neg hclk] at hnt ⊢
        obtain ⟨y', m', hy', hm', hlt⟩ := eval_lower_locals s
          (h := fun a => Classical.propDecidable (s.memaddrs a))
          (ofString "off") (ofString "len") word (by rw [← evalHOLFinite_eq_toExact]; exact hword) hzero
        have hy_eq : y' = y := by rw [hy] at hy'; injection hy' with h; injection h with h; injection h with h; exact h.symm
        have hm_eq : m' = m := by rw [hm] at hm'; injection hm' with h; injection h with h; injection h with h; exact h.symm
        subst y'; subst m'
        set sd := decClockHOLFinite s
        have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
        have hb := countBody_bound sd hcode hGd
        have hunfold := while_unfold_continue countCond countBody s word hword hzero hclk
        have hmeta := (evaluateHOLFiniteState_metadata sd countBody).1
        have hnc := evaluate_noTopContinue countBody rfl sd
        unfold TerminatingRunBounded at hb
        rcases hrun : evaluateHOLFiniteState sd countBody with ⟨res, post⟩
        simp only [sd, hrun] at hnt hb hunfold hmeta hnc ⊢
        have hge1 : (K.«rlp_item_total» + 0 + 1) + 1 ≤
            (n + 1 + 1) * ((K.«rlp_item_total» + 0 + 1) + 1) :=
          Nat.le_mul_of_pos_left _ (by omega)
        cases res with
        | some r =>
          cases r with
          | «continue» => exact absurd rfl hnc
          | timeOut => exact absurd rfl hnt
          | _ =>
            obtain ⟨hspent, hkept⟩ := hb (by simp)
            change s.clock - 1 ≤ post.clock + (K.«rlp_item_total» + 0 + 1) at hspent
            change post.clock ≤ s.clock - 1 at hkept
            dsimp only
            exact ⟨by omega, by omega⟩
        | none =>
          dsimp only
          obtain ⟨hspent, hkept⟩ := hb (by simp)
          change s.clock - 1 ≤ post.clock + (K.«rlp_item_total» + 0 + 1) at hspent
          change post.clock ≤ s.clock - 1 at hkept
          change post.code = s.code at hmeta
          have hsame := hunfold (Or.inl rfl)
          have hnt_post : (evaluateHOLFiniteState post (.while countCond countBody)).1 ≠ some .timeOut := by
            rw [← hsame]; exact hnt0
          have hG_post : GuestInv post := by
            have h := guestInv_evaluate sd countBody hGd
            rwa [hrun] at h
          obtain ⟨T, hT1, hyT_le, hpy_lo, hpy_hi, hp_off, hp_p, hp_len⟩ :=
            countBody_step sd P y m hcode hGd hp hy hm hlt (by rw [hrun])
          rw [hrun] at hp_off hp_p hp_len; dsimp only at hp_off hp_p hp_len
          have hk_lt : (P + y).toNat - sourceBase < domainBytes := by
            have eD : domainBytes = heapEnd - sourceBase := rfl; omega
          let k_now : Fin domainBytes := ⟨(P + y).toNat - sourceBase, hk_lt⟩
          have hfresh : k_now ∉ vis := by
            intro hmem
            obtain ⟨d, hd_lt, _, _, hk_eq⟩ := hvis k_now hmem
            have hbv : P + d = P + y := BitVec.eq_of_toNat_eq (by change (P + y).toNat - sourceBase = _ at hk_eq; omega)
            have hdy : d = y := by
              have hsub := congrArg (fun x => -P + x) hbv
              simpa [← BitVec.add_assoc] using hsub
            subst hdy; omega
          have hle_ins : (insert k_now vis).card ≤ domainBytes := by
            simpa using Finset.card_le_univ (insert k_now vis)
          have hcard_ins := Finset.card_insert_of_notMem hfresh
          have hyT_nat : (y + T).toNat = y.toNat + T.toNat :=
            BitVec.toNat_add_of_lt (by have := m.isLt; omega)
          have hinv_post : CountLoopInv post (insert k_now vis) := by
            refine ⟨hG_post, P, y + T, m, hp_p, hp_off, hp_len, ?_⟩
            intro k hk
            rcases Finset.mem_insert.mp hk with rfl | hk
            · exact ⟨y, by omega, hpy_lo, hpy_hi, rfl⟩
            · obtain ⟨d, hd, h1, h2, h3⟩ := hvis k hk
              exact ⟨d, by omega, h1, h2, h3⟩
          obtain ⟨htail, htailKept⟩ := ih post (insert k_now vis) (hmeta.trans hcode) hinv_post
            (by omega) hnt_post
          have hmul : (n + 1) * ((K.«rlp_item_total» + 0 + 1) + 1) + ((K.«rlp_item_total» + 0 + 1) + 1) =
              (n + 1 + 1) * ((K.«rlp_item_total» + 0 + 1) + 1) := (Nat.succ_mul (n + 1) _).symm
          exact ⟨by omega, by omega⟩

end RlpListCount

theorem fb_rlp_list_count :
    TerminatingFunBoundedOn GuestInv (ofString "rlp_list_count") K.«rlp_list_count» := by
  refine ⟨_, _, _, lookup_of_guestAst_getElem 113 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_rlp_list_count) rfl, ?_⟩
  intro F state0 hcode0 hG0
  dsimp only [extractFn, Guest.Software.guestFn_rlp_list_count,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map]
  apply TerminatingProgBoundedOn.weaken'
    (P := GuestInv)
    (K := ((domainBytes + 1) + 1) * ((K.«rlp_item_total» + 0 + 1) + 1) + 0)
    ?_ (by unfold K.«rlp_list_count»; simp only [Nat.add_zero]; exact Nat.le_refl _) state0 hcode0 hG0
  apply dec_guestInv
  apply dec_val_on (Q := fun s => GuestInv s ∧ s.locals.lookup (ofString "off") = some (.val (.word 0)))
  · intro F2 s v hP hv _
    simp only [evalHOLExact, Option.some.injEq] at hv; subst hv
    exact ⟨guestInv_setVar _ _ _ hP, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
  · refine seq_on'
      (P := fun s => GuestInv s ∧ s.locals.lookup (ofString "off") = some (.val (.word 0)))
      (Q := GuestInv)
      (a := ((domainBytes + 1) + 1) * ((K.«rlp_item_total» + 0 + 1) + 1))
      (b := 0)
      ?_ (fun s _ hP _ => guestInv_evaluate s _ hP.1) (straightOn _ rfl)
    intro F2 s hcode ⟨hG, hoff0⟩
    change TerminatingRunBounded s (.while countCond countBody)
      (((domainBytes + 1) + 1) * ((K.«rlp_item_total» + 0 + 1) + 1))
    by_cases hp_word : ∃ P : BitVec 64, s.locals.lookup (ofString "p") = some (.val (.word P))
    · obtain ⟨P, hp⟩ := hp_word
      by_cases hlen_word : ∃ L : BitVec 64, s.locals.lookup (ofString "len") = some (.val (.word L))
      · obtain ⟨L, hlen⟩ := hlen_word
        exact (count_while_aux domainBytes s ∅ hcode
          ⟨hG, P, 0, L, hp, hoff0, hlen, by simp⟩ (Nat.le_refl _)).weaken
          (Nat.mul_le_mul_right _ (Nat.le_succ _))
      · intro hnt
        rw [evaluateHOLFiniteState_while_fixClockRewrite]
        have hc_none : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) countCond = none := by
          rw [evalHOLFinite_eq_toExact]
          rcases hlen : s.locals.lookup (ofString "len") with _ | ⟨⟨L⟩⟩ | _ | _
          · simp [countCond, evalHOLExact, hoff0, hlen]
          · exact absurd ⟨L, hlen⟩ hlen_word
          · simp [countCond, evalHOLExact, hoff0, hlen]
          · simp [countCond, evalHOLExact, hoff0, hlen]
        rw [hc_none]
        exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    · intro hnt
      rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
      split; swap; · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
      rename_i word hword
      simp only [hword] at hnt
      by_cases hzero : word = 0
      · rw [if_neg (by simp [hzero])]; exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
      · rw [if_pos hzero] at hnt ⊢
        by_cases hclk : s.clock = 0
        · rw [if_pos hclk] at hnt; exact absurd rfl hnt
        · rw [if_neg hclk]
          have herr : evaluateHOLFiniteState (decClockHOLFinite s) countBody =
              (some .error, decClockHOLFinite s) := by
            unfold countBody
            rw [evaluateHOLFiniteState_decCall_total]
            have ha_none : evalListHOLFinite (decClockHOLFinite s)
                (h := fun a => Classical.propDecidable ((decClockHOLFinite s).memaddrs a))
                [.op .add [.var .local (ofString "p"), .var .local (ofString "off")],
                 .op .sub [.var .local (ofString "len"), .var .local (ofString "off")]] = none := by
              rw [evalListHOLFinite_eq_toExact]
              rcases hp : s.locals.lookup (ofString "p") with _ | ⟨⟨P⟩⟩ | _ | _
              · simp [evalListHOLExact, evalHOLExact, decClockHOLFinite, hp, hoff0]
              · exact absurd ⟨P, hp⟩ hp_word
              · simp [evalListHOLExact, evalHOLExact, decClockHOLFinite, hp, hoff0, valueIsWord]
              · simp [evalListHOLExact, evalHOLExact, decClockHOLFinite, hp, hoff0, valueIsWord]
            rw [ha_none]
          rw [herr]; dsimp only
          have hge1 : 1 ≤ ((domainBytes + 1) + 1) * ((K.«rlp_item_total» + 0 + 1) + 1) :=
            Nat.mul_pos (by omega) (by omega)
          change s.clock ≤ (s.clock - 1) + _ ∧ (s.clock - 1) ≤ s.clock
          exact ⟨by omega, by omega⟩

/-! ### `fb_rlp_item`, `fb_rlp_decode_fully`, `fb_rlp_list_to_slices`, `fb_decode_account_from_leaf` -/

section RlpIncr

def IncrBody (i : MlS) (body : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (y : BitVec 64),
    s.locals.lookup i = some (.val (.word y)) →
    (evaluateHOLFiniteState s body).1 = none →
    (evaluateHOLFiniteState s body).2.locals.lookup i = some (.val (.word (y + 1)))

theorem incr_last (i : MlS) : IncrBody i (.assign .local i (.op .add [.var .local i, .const 1])) := by
  intro F s y hy hflow
  rw [evaluateHOLFiniteState_assign] at hflow ⊢
  simp [evalHOLExact, evalListHOLExact, hy, wordOpHOL, wordOp, valueIsWord, valueWord,
    isValidValueHOLFinite, lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite,
    setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

theorem incr_seq {i : MlS} {a b : ProgHOL 64} (ha : avoidsLocal i a = true) (hb : IncrBody i b) :
    IncrBody i (.seq a b) := by
  intro F s y hy hflow
  rw [evaluateHOLFiniteState_seq_line780] at hflow ⊢
  rcases hr : evaluateHOLFiniteState s a with ⟨r, mid⟩
  simp only [hr] at hflow ⊢
  cases r with
  | none =>
    have hk := evaluate_avoidsLocal_flowing i a ha s (by rw [hr]; exact Or.inl rfl)
    rw [hr] at hk
    exact hb mid y (hk.trans hy) hflow
  | some _ => simp at hflow

theorem incr_dec {i n : MlS} {sh : ShapeHOL} {e : ExpHOL 64} {b : ProgHOL 64} (hne : n ≠ i)
    (hb : IncrBody i b) : IncrBody i (.dec n sh e b) := by
  intro F s y hy hflow
  revert hflow
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · simp
  · rename_i v hv
    split
    · intro hflow
      dsimp only
      rw [PanRunBounded.resVarEq_lookup, if_neg (Ne.symm hne)]
      exact hb _ y (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hy]) hflow
    · simp

theorem incr_decCall {i n : MlS} {sh : ShapeHOL} {f : MlS} {args : List (ExpHOL 64)} {c : ProgHOL 64}
    (hne : n ≠ i) (hc : IncrBody i c) : IncrBody i (.decCall n sh f args c) := by
  intro F s y hy hflow
  obtain ⟨_, _, _, _, _, _, _, _, u, _, hloc, _, hcont, hfin⟩ := decCall_flow hflow
  rw [hfin i (Ne.symm hne)]
  exact hc u y ((hloc i (Ne.symm hne)).trans hy) hcont

theorem lim_var {n : MlS} {body : ProgHOL 64} (hn : avoidsLocal n body = true) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState s body).1 = none →
      @evalHOLExact 64 F _ (evaluateHOLFiniteState s body).2.toExact
          (fun a => Classical.propDecidable ((evaluateHOLFiniteState s body).2.memaddrs a)) (.var .local n) =
        @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.var .local n) := by
  intro F s hflow
  have := evaluate_avoidsLocal_flowing n body hn s (Or.inl hflow)
  simpa [evalHOLExact] using this

theorem lim_rfield {f : MlS} {k : Nat} {body : ProgHOL 64} (hf : avoidsLocal f body = true) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState s body).1 = none →
      @evalHOLExact 64 F _ (evaluateHOLFiniteState s body).2.toExact
          (fun a => Classical.propDecidable ((evaluateHOLFiniteState s body).2.memaddrs a))
          (.rfield k (.var .local f)) =
        @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.rfield k (.var .local f)) := by
  intro F s hflow
  have := evaluate_avoidsLocal_flowing f body hf s (Or.inl hflow)
  simp [evalHOLExact, this]

end RlpIncr

syntax "incr_auto" : tactic
macro_rules
  | `(tactic| incr_auto) => `(tactic| first
      | exact incr_last _
      | (apply incr_seq (by decide); incr_auto)
      | (apply incr_dec (by decide); incr_auto)
      | (apply incr_decCall (by decide); incr_auto))

macro_rules
  | `(tactic| fb_auto) => `(tactic|
      (apply while_ctr_expr
       · fb_auto
       · intro _ s y _ hy hnone; exact (by incr_auto : IncrBody _ _) s y hy hnone
       · first
         | exact lim_var (by decide)
         | exact lim_rfield (by decide)
       · rfl))

theorem fb_rlp_item : TerminatingFunBoundedOn GuestInv (ofString "rlp_item") K.«rlp_item» := by
  fb_prove 107 Guest.Software.guestFn_rlp_item K.«rlp_item»

theorem fb_rlp_decode_fully :
    TerminatingFunBoundedOn GuestInv (ofString "rlp_decode_fully") K.«rlp_decode_fully» := by
  fb_prove 108 Guest.Software.guestFn_rlp_decode_fully K.«rlp_decode_fully»

theorem fb_rlp_list_to_slices :
    TerminatingFunBoundedOn GuestInv (ofString "rlp_list_to_slices") K.«rlp_list_to_slices» := by
  fb_unfold 115 Guest.Software.guestFn_rlp_list_to_slices
  apply TerminatingProgBoundedOn.weaken'
  · fb_auto
  · unfold K.«rlp_list_to_slices»
    generalize_K
    omega

theorem fb_decode_account_from_leaf :
    TerminatingFunBoundedOn GuestInv (ofString "decode_account_from_leaf") K.«decode_account_from_leaf» := by
  fb_unfold 293 Guest.Software.guestFn_decode_account_from_leaf
  apply TerminatingProgBoundedOn.weaken'
  · fb_auto
  · unfold K.«decode_account_from_leaf»
    generalize_K
    simp only [Nat.add_zero, Nat.zero_add, max_def]
    split_ifs <;> omega

/-! ### `fb_trie_walk` (`(71723149827058354885847154688 + 1) * ...`), `fb_trie_lookup`, and `fb_set_storage` -/

namespace TrieR10

def good (f : MlS) : Bool := f == ofString "mpt_fail" || f == ofString "memeq"

theorem good_ro : ∀ function, good function = true → ∀ values body callee rs,
    PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
      some (body, callee, rs) → roProg good body = true := by
  intro function hf values body callee rs hl
  simp only [good, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with rfl | rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 246 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_mpt_fail) rfl) hl
    subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 18 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_memeq) rfl) hl
    subst hb; rfl

def cond : ExpHOL 64 := .cmp .notEqual (.var .local (ofString "node")) (.const 0)

def body : ProgHOL 64 :=
  match sourceFnBody Guest.Software.guestFn_trie_walk with
  | .dec _ _ _ (.seq (.while _ b) _) => b
  | _ => .skip

def bodyK : Nat := Nat.max (K.«mpt_fail» + 1) 0 +
  Nat.max (Nat.max (K.«memeq» + 1) 0) 0 + Nat.max (K.«memeq» + 1) 0

theorem body_bound : TerminatingProgBoundedOn GuestInv body bodyK := by
  apply TerminatingProgBoundedOn.weaken'
  · dsimp only [body, sourceFnBody, sourceFunctionEntry, extractFn, Guest.Software.guestFn_trie_walk,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    fb_auto
  · unfold bodyK
    simp only [max_def]
    split_ifs <;> omega

theorem body_avoids (k : MlS) (hn : k ≠ ofString "node") (hp : k ≠ ofString "pos") :
    avoidsLocal k body = true := by
  simp [body, sourceFnBody, sourceFunctionEntry, extractFn, Guest.Software.guestFn_trie_walk,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    avoidsLocal, beq_iff_eq, Ne.symm hn, Ne.symm hp]

/-- Any flowing run of `body` evaluates `load .one (node + 0)`, proving `ordinaryDomain node`! -/
theorem body_flows_node_dom {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hflow : Flowing (evaluateHOLFiniteState s body).1) :
    ∃ a : BitVec 64,
      s.locals.lookup (ofString "node") = some (.val (.word a)) ∧
      s.memaddrs a := by
  dsimp only [body, sourceFnBody, sourceFunctionEntry, extractFn, Guest.Software.guestFn_trie_walk,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hflow
  rw [evaluateHOLFiniteState_dec_total] at hflow
  dsimp only at hflow
  split at hflow
  · simp [Flowing] at hflow
  · rename_i val hval
    obtain ⟨addr, haddr, hdom, _⟩ := eval_load_one s
      (h := fun x => Classical.propDecidable (s.memaddrs x)) _ val hval
    simp only [evalHOLExact, evalListHOLExact] at haddr
    rcases hn : s.locals.lookup (ofString "node") with _ | ⟨⟨a⟩⟩ | _ | _ <;>
      simp [hn, wordOpHOL, wordOp, valueIsWord, valueWord] at haddr
    subst haddr
    exact ⟨a, rfl, hdom⟩

abbrev trieKeys : Nat := 3888119741 * 2 ^ 64

def kappa {F : Type} (s : PanSemStateFiniteExact 64 F) : Fin trieKeys :=
  match s.locals.lookup (ofString "node"), s.locals.lookup (ofString "pos") with
  | some (.val (.word a)), some (.val (.word b)) =>
    if h : sourceBase ≤ a.toNat ∧ a.toNat + 8 ≤ heapEnd then
      ⟨((a.toNat - sourceBase) / 8) * 2 ^ 64 + b.toNat, by
        have e1 : sourceBase = 2701131776 := by decide
        have e2 : heapEnd = 2701131776 + 8 * 3888119741 := by decide
        have e3 : trieKeys = 3888119741 * 2 ^ 64 := rfl
        have hb := b.isLt
        have hdiv : (a.toNat - sourceBase) / 8 < 3888119741 := by omega
        calc ((a.toNat - sourceBase) / 8) * 2 ^ 64 + b.toNat
            < ((a.toNat - sourceBase) / 8) * 2 ^ 64 + 2 ^ 64 := by omega
          _ = (((a.toNat - sourceBase) / 8) + 1) * 2 ^ 64 := by rw [Nat.succ_mul]
          _ ≤ 3888119741 * 2 ^ 64 := Nat.mul_le_mul_right _ hdiv⟩
    else ⟨0, by decide⟩
  | _, _ => ⟨0, by decide⟩

def Rel {F : Type} (s t : PanSemStateFiniteExact 64 F) : Prop :=
  WordLocal (ofString "pos") s ∧ WordLocal (ofString "pos") t ∧
  t.memory = s.memory ∧ t.globals = s.globals ∧ t.ffi = s.ffi ∧
  t.topAddr = s.topAddr ∧ t.code = s.code ∧ t.memaddrs = s.memaddrs ∧
  t.shMemaddrs = s.shMemaddrs ∧ t.be = s.be ∧ t.eshapes = s.eshapes ∧
  t.baseAddr = s.baseAddr ∧ t.structs = s.structs ∧
  (∀ k, k ≠ ofString "node" → k ≠ ofString "pos" → t.locals.lookup k = s.locals.lookup k)

theorem Rel_trans {F : Type} (a b c : PanSemStateFiniteExact 64 F)
    (h1 : Rel a b) (h2 : Rel b c) : Rel a c := by
  obtain ⟨wa, _, m1, g1, f1, t1, c1, ma1, sh1, be1, es1, ba1, st1, k1⟩ := h1
  obtain ⟨_, wc, m2, g2, f2, t2, c2, ma2, sh2, be2, es2, ba2, st2, k2⟩ := h2
  exact ⟨wa, wc, m2.trans m1, g2.trans g1, f2.trans f1, t2.trans t1, c2.trans c1,
    ma2.trans ma1, sh2.trans sh1, be2.trans be1, es2.trans es1, ba2.trans ba1,
    st2.trans st1, fun k hn hp => (k2 k hn hp).trans (k1 k hn hp)⟩

theorem Rel_key {F : Type} (a b : PanSemStateFiniteExact 64 F)
    (hGa : GuestInv a) (hGb : GuestInv b) (hR : Rel a b)
    (hdoma : ∃ na, a.locals.lookup (ofString "node") = some (.val (.word na)) ∧ a.memaddrs na)
    (hdomb : ∃ nb, b.locals.lookup (ofString "node") = some (.val (.word nb)) ∧ b.memaddrs nb)
    (hk : kappa a = kappa b) : b = { a with clock := b.clock } := by
  obtain ⟨⟨pa, hpa⟩, ⟨pb, hpb⟩, m1, g1, f1, t1, c1, ma1, sh1, be1, es1, ba1, st1, k1⟩ := hR
  obtain ⟨na, hna, hma⟩ := hdoma
  obtain ⟨nb, hnb, hmb⟩ := hdomb
  rw [hGa.memaddrs] at hma
  rw [hGb.memaddrs] at hmb
  have hbnda := ordinaryDomain_bounds na hma
  have hbndb := ordinaryDomain_bounds nb hmb
  have hala := ordinaryDomain_aligned na hma
  have halb := ordinaryDomain_aligned nb hmb
  have hk_val := congrArg Fin.val hk
  simp only [kappa, hna, hpa, hnb, hpb, dif_pos hbnda, dif_pos hbndb] at hk_val
  have hpa_lt := pa.isLt; have hpb_lt := pb.isLt
  have hdiv_eq : (na.toNat - sourceBase) / 8 = (nb.toNat - sourceBase) / 8 := by omega
  have hp_eq : pa.toNat = pb.toNat := by omega
  have heS : sourceBase % 8 = 0 := by decide
  have hn_eq : na.toNat = nb.toNat := by omega
  have hloc : b.locals = a.locals := locals_ext fun k => by
    by_cases kn : k = ofString "node"
    · subst kn; rw [hna, hnb, BitVec.eq_of_toNat_eq hn_eq]
    by_cases kp : k = ofString "pos"
    · subst kp; rw [hpa, hpb, BitVec.eq_of_toNat_eq hp_eq]
    exact k1 k kn kp
  cases a; cases b
  simp only at m1 g1 f1 t1 c1 ma1 sh1 be1 es1 ba1 st1 hloc ⊢
  subst m1 g1 f1 t1 c1 ma1 sh1 be1 es1 ba1 st1 hloc
  rfl

def Pinv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ WordLocal (ofString "pos") s

def VisitedTrie {F : Type} (state : PanSemStateFiniteExact 64 F) (visited : Finset (Fin trieKeys)) : Prop :=
  ∀ k ∈ visited, ∃ earlier : PanSemStateFiniteExact 64 F,
    kappa earlier = k ∧ GuestInv earlier ∧ Rel earlier state ∧
    (∃ na, earlier.locals.lookup (ofString "node") = some (.val (.word na)) ∧ earlier.memaddrs na) ∧
    state.clock < earlier.clock ∧
    evaluateHOLFiniteState earlier (.while cond body) = evaluateHOLFiniteState state (.while cond body)

theorem trie_while_aux :
    ∀ (n : Nat) {F : Type} (state : PanSemStateFiniteExact 64 F) (visited : Finset (Fin trieKeys)),
      state.code = originalRuntimeCode →
      Pinv state →
      trieKeys ≤ visited.card + n →
      VisitedTrie state visited →
      TerminatingRunBounded state (.while cond body) ((n + 1) * (bodyK + 1)) := by
  intro n
  induction n with
  | zero =>
    intro F state visited hcode hP hcard hvis hnt
    have hnt0 := hnt
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    split; swap; · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    rename_i word hword
    simp only [hword] at hnt
    by_cases hzero : word = 0
    · rw [if_neg (by simp [hzero])]; exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    · rw [if_pos hzero] at hnt ⊢
      by_cases hclock : state.clock = 0
      · rw [if_pos hclock] at hnt; exact absurd rfl hnt
      · rw [if_neg hclock] at hnt ⊢
        have hGd : GuestInv (decClockHOLFinite state) := guestInv_congr (s := state) rfl rfl rfl rfl hP.1
        have hb := body_bound (decClockHOLFinite state) hcode hGd
        unfold TerminatingRunBounded at hb
        rcases hrun : evaluateHOLFiniteState (decClockHOLFinite state) body with ⟨result, post⟩
        simp only [hrun] at hnt hb ⊢
        have hcont (hflow : result = none ∨ result = some .continue) : False := by
          have hdom_sd := body_flows_node_dom (decClockHOLFinite state)
            (by rw [hrun]; exact hflow.elim Or.inl (fun h => Or.inr (Or.inr h)))
          have hdom : ∃ na, state.locals.lookup (ofString "node") = some (.val (.word na)) ∧ state.memaddrs na :=
            hdom_sd
          have hfresh : kappa state ∉ visited := by
            intro hmem
            obtain ⟨earlier, hk, hGe, hRe, hdome, hlt, hsame⟩ := hvis _ hmem
            have heq := Rel_key earlier state hGe hP.1 hRe hdome hdom hk
            exact evaluate_ne_of_clock_lt _ state earlier (by rw [heq]) hlt hsame hnt0
          have hle : (insert (kappa state) visited).card ≤ trieKeys := by
            simpa using Finset.card_le_univ (insert (kappa state) visited)
          rw [Finset.card_insert_of_notMem hfresh] at hle
          omega
        cases result with
        | none => exact False.elim (hcont (Or.inl rfl))
        | some r =>
          cases r with
          | «continue» => exact False.elim (hcont (Or.inr rfl))
          | timeOut => exact absurd rfl hnt
          | _ =>
            obtain ⟨hspent, hkept⟩ := hb (by simp)
            change state.clock - 1 ≤ post.clock + bodyK at hspent
            change post.clock ≤ state.clock - 1 at hkept
            dsimp only
            exact ⟨by omega, by omega⟩
  | succ n ih =>
    intro F state visited hcode hP hcard hvis hnt
    have hnt0 := hnt
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    split; swap; · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    rename_i word hword
    simp only [hword] at hnt
    by_cases hzero : word = 0
    · rw [if_neg (by simp [hzero])]; exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    · rw [if_pos hzero] at hnt ⊢
      by_cases hclock : state.clock = 0
      · rw [if_pos hclock] at hnt; exact absurd rfl hnt
      · rw [if_neg hclock] at hnt ⊢
        have hGd : GuestInv (decClockHOLFinite state) := guestInv_congr (s := state) rfl rfl rfl rfl hP.1
        have hb := body_bound (decClockHOLFinite state) hcode hGd
        have hunfold := while_unfold_continue cond body state word hword hzero hclock
        have hmeta := (evaluateHOLFiniteState_metadata (decClockHOLFinite state) body).1
        unfold TerminatingRunBounded at hb
        rcases hrun : evaluateHOLFiniteState (decClockHOLFinite state) body with ⟨result, post⟩
        simp only [hrun] at hnt hb hunfold hmeta ⊢
        change post.code = state.code at hmeta
        have hge1 : bodyK + 1 ≤ (n + 1 + 1) * (bodyK + 1) := Nat.le_mul_of_pos_left _ (by omega)
        have hcont (hflow : result = none ∨ result = some .continue) :
            state.clock ≤ (evaluateHOLFiniteState post (.while cond body)).2.clock +
              (n + 1 + 1) * (bodyK + 1) ∧
            (evaluateHOLFiniteState post (.while cond body)).2.clock ≤ state.clock := by
          have hsafe : result ≠ some .timeOut := by rcases hflow with h | h <;> simp [h]
          obtain ⟨hspent, hkept⟩ := hb hsafe
          change state.clock - 1 ≤ post.clock + bodyK at hspent
          change post.clock ≤ state.clock - 1 at hkept
          have hdom : ∃ na, state.locals.lookup (ofString "node") = some (.val (.word na)) ∧ state.memaddrs na :=
            body_flows_node_dom (decClockHOLFinite state)
              (by rw [hrun]; exact hflow.elim Or.inl (fun h => Or.inr (Or.inr h)))
          have hfresh : kappa state ∉ visited := by
            intro hmem
            obtain ⟨earlier, hk, hGe, hRe, hdome, hlt, hsame⟩ := hvis _ hmem
            have heq := Rel_key earlier state hGe hP.1 hRe hdome hdom hk
            exact evaluate_ne_of_clock_lt _ state earlier (by rw [heq]) hlt hsame hnt0
          -- Prove `Pinv post` and `Rel state post`:
          have hflow' : Flowing (evaluateHOLFiniteState (decClockHOLFinite state) body).1 := by
            rw [hrun]; exact hflow.elim Or.inl (fun h => Or.inr (Or.inr h))
          have wp := evaluate_wordLocal (ofString "pos") body rfl (decClockHOLFinite state) hP.2 hflow'
          have fr := evaluate_ro good good_ro body rfl (decClockHOLFinite state) hcode
          have mt := evalMeta (decClockHOLFinite state) body
          have hGpost : GuestInv post := by
            have h := guestInv_evaluate (decClockHOLFinite state) body hGd
            rwa [hrun] at h
          rw [hrun] at wp fr mt; dsimp only at wp fr mt
          have hRpost : Rel state post :=
            ⟨hP.2, wp, fr.1, fr.2.1, fr.2.2.1, fr.2.2.2, mt.1, mt.2.1, mt.2.2.1,
             mt.2.2.2.1, mt.2.2.2.2.1, mt.2.2.2.2.2.1, mt.2.2.2.2.2.2, fun k hn hp => by
              have hk := evaluate_avoidsLocal_flowing k body (body_avoids k hn hp) (decClockHOLFinite state) hflow'
              rwa [hrun] at hk⟩
          have hsame := hunfold hflow
          have hntPost : (evaluateHOLFiniteState post (.while cond body)).1 ≠ some .timeOut := by
            rw [← hsame]; exact hnt0
          obtain ⟨htail, htailKept⟩ := ih post (insert (kappa state) visited)
            (hmeta.trans hcode) ⟨hGpost, wp⟩
            (by rw [Finset.card_insert_of_notMem hfresh]; omega)
            (fun k hk => by
              rcases Finset.mem_insert.mp hk with rfl | hk
              · exact ⟨state, rfl, hP.1, hRpost, hdom, by omega, hsame⟩
              · obtain ⟨earlier, hke, hGe, hRe, hdome, hlt, hsameE⟩ := hvis k hk
                exact ⟨earlier, hke, hGe, Rel_trans _ _ _ hRe hRpost, hdome, by omega,
                  hsameE.trans hsame⟩)
            hntPost
          have hmul : (n + 1) * (bodyK + 1) + (bodyK + 1) = (n + 1 + 1) * (bodyK + 1) :=
            (Nat.succ_mul (n + 1) _).symm
          exact ⟨by omega, by omega⟩
        cases result with
        | none => exact hcont (Or.inl rfl)
        | some r =>
          cases r with
          | «continue» => exact hcont (Or.inr rfl)
          | timeOut => exact absurd rfl hnt
          | _ =>
            obtain ⟨hspent, hkept⟩ := hb (by simp)
            change state.clock - 1 ≤ post.clock + bodyK at hspent
            change post.clock ≤ state.clock - 1 at hkept
            dsimp only
            exact ⟨by omega, by omega⟩

theorem loop_bound : TerminatingProgBoundedOn Pinv (.while cond body)
    ((71723149827058354885847154688 + 1) * (bodyK + 1)) := by
  intro F state hcode hP
  have hle : trieKeys ≤ 71723149827058354885847154688 := by decide
  exact (trie_while_aux trieKeys state ∅ hcode hP (by simp) (by simp [VisitedTrie])).weaken
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right hle 1))

end TrieR10

theorem tail_clock_of_body {F : Type}
    (state post : PanSemStateFiniteExact 64 F)
    (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (result : Option (PanSemResultExact 64))
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body, callee, returnShape))
    (clock : state.clock ≠ 0)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (result, post))
    (noTimeout : result ≠ some .timeOut) :
    let output := evaluateHOLFiniteState state (.call none function arguments)
    output.1 ≠ some .timeOut ∧ output.2.clock = post.clock := by
  dsimp only
  rw [evaluateHOLFiniteState_call, args]
  dsimp only
  rw [lookup]
  dsimp only
  rw [if_neg clock, run]
  cases result with
  | none => simp
  | some result =>
    cases result <;> simp_all [emptyLocalsHOLFinite]
    split <;> simp

theorem tailCall_guestInv {fname : MlS} {B : Nat}
    (hf : TerminatingFunBoundedOn GuestInv fname B) (arguments : List (ExpHOL 64)) :
    TerminatingProgBoundedOn GuestInv (.call none fname arguments) (B + 1) := by
  obtain ⟨params, fbody, ret, hlook, hbody⟩ := hf
  intro F state hcode hP hnt
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  cases hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
  | none => exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  | some values =>
    rw [hargs] at hnt; dsimp only at hnt ⊢
    cases hlookup : lookupCodeHOLFinite state.code.lookup fname values with
    | none => exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    | some found =>
      obtain ⟨body, callee, returnShape⟩ := found
      rw [hlookup] at hnt; dsimp only at hnt ⊢
      by_cases hzero : state.clock = 0
      · rw [if_pos hzero] at hnt; exact absurd rfl hnt
      · rw [if_neg hzero] at hnt ⊢
        obtain ⟨_, hentry⟩ := callee_body_bound hlook hbody (callEntryOn_guestInv fname arguments)
          state hcode hP values body callee returnShape hargs hlookup
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
          ⟨result, post⟩
        rw [hrun] at hnt
        have hntBody : result ≠ some .timeOut := fun hbad => by subst hbad; simp at hnt
        have hbound := hentry (by rw [hrun]; exact hntBody)
        rw [hrun] at hbound
        obtain ⟨hspent, hkept⟩ := hbound
        have hpair := tail_clock_of_body state post fname arguments values body callee
          returnShape result hargs hlookup hzero hrun hntBody
        dsimp only at hpair
        rw [evaluateHOLFiniteState_call, hargs] at hpair; dsimp only at hpair
        rw [hlookup] at hpair; dsimp only at hpair
        rw [if_neg hzero, hrun] at hpair
        rw [hpair.2]
        change state.clock - 1 ≤ post.clock + B at hspent
        change post.clock ≤ state.clock - 1 at hkept
        exact ⟨by omega, by omega⟩

macro_rules
  | `(tactic| fb_auto) => `(tactic| (apply tailCall_guestInv; callee_fb))

theorem fb_trie_walk : TerminatingFunBoundedOn GuestInv (ofString "trie_walk") K.«trie_walk» := by
  fb_unfold 266 Guest.Software.guestFn_trie_walk
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_on' (Q := TrieR10.Pinv)
    · intro F s v hP hv
      exact ⟨guestInv_setVar _ _ _ hP, setVar_word s _ v hv⟩
    · exact seq_on' TrieR10.loop_bound
        (fun s _ hP _ => guestInv_evaluate s _ hP.1)
        (straightOn _ rfl)
  · unfold K.«trie_walk» TrieR10.bodyK
    generalize_K
    simp only [Nat.add_zero, max_def]
    split_ifs <;> omega

theorem fb_trie_lookup :
    TerminatingFunBoundedOn GuestInv (ofString "trie_lookup") K.«trie_lookup» := by
  fb_prove 267 Guest.Software.guestFn_trie_lookup K.«trie_lookup»

theorem fb_ws_account_leaf :
    TerminatingFunBoundedOn GuestInv (ofString "ws_account_leaf") K.«ws_account_leaf» := by
  fb_prove 365 Guest.Software.guestFn_ws_account_leaf K.«ws_account_leaf»

theorem fb_ws_get_account_optional :
    TerminatingFunBoundedOn GuestInv (ofString "ws_get_account_optional") K.«ws_get_account_optional» := by
  fb_prove 366 Guest.Software.guestFn_ws_get_account_optional K.«ws_get_account_optional»

theorem fb_get_pre_state_account_optional :
    TerminatingFunBoundedOn GuestInv (ofString "get_pre_state_account_optional") K.«get_pre_state_account_optional» := by
  fb_prove 372 Guest.Software.guestFn_get_pre_state_account_optional K.«get_pre_state_account_optional»

theorem fb_get_account_optional :
    TerminatingFunBoundedOn GuestInv (ofString "get_account_optional") K.«get_account_optional» := by
  fb_prove 374 Guest.Software.guestFn_get_account_optional K.«get_account_optional»

theorem fb_set_storage :
    TerminatingFunBoundedOn GuestInv (ofString "set_storage") K.«set_storage» := by
  fb_prove 388 Guest.Software.guestFn_set_storage K.«set_storage»

end InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30
