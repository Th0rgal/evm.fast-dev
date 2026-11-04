import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.LogsBloom

/-!
# R16j EncodeReceipt: `wk_encode_receipt`

Complete proof of `wk_encode_receipt`, matching the frozen statement in
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

/-! ## Section 1: Lookups and 4-word parameter unpacking -/

theorem lookup_logs_encoded_bound :
    originalRuntimeCode.lookup (ofString "logs_encoded_bound") =
      some ([(ofString "logs", .one)],
        sourceFnBody Guest.Software.guestFn_logs_encoded_bound, .one) :=
  lookup_of_guestAst_getElem 834 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_logs_encoded_bound) rfl

theorem lookup_encode_logs :
    originalRuntimeCode.lookup (ofString "encode_logs") =
      some ([(ofString "dst", .one), (ofString "logs", .one)],
        sourceFnBody Guest.Software.guestFn_encode_logs, .one) :=
  lookup_of_guestAst_getElem 835 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_encode_logs) rfl

theorem lookup_encode_receipt :
    originalRuntimeCode.lookup (ofString "encode_receipt") =
      some ([(ofString "tx_type", .one), (ofString "succeeded", .one),
             (ofString "cumulative_gas", .one), (ofString "logs", .one)],
        sourceFnBody Guest.Software.guestFn_encode_receipt, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 836 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_encode_receipt) rfl

private theorem lookupCode_four_words {fname p1 p2 p3 p4 : MlS} {body : ProgHOL 64} {rs : ShapeHOL}
    {vals : List (ValueHOL 64)} {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (hne12 : p2 ≠ p1) (hne13 : p3 ≠ p1) (hne14 : p4 ≠ p1)
    (hne23 : p3 ≠ p2) (hne24 : p4 ≠ p2) (hne34 : p4 ≠ p3)
    (hlook : originalRuntimeCode.lookup fname =
      some ([(p1, .one), (p2, .one), (p3, .one), (p4, .one)], body, rs))
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, L, rs)) :
    ∃ w1 w2 w3 w4 : BitVec 64,
      vals = [.val (.word w1), .val (.word w2), .val (.word w3), .val (.word w4)] ∧
      L.lookup p1 = some (.val (.word w1)) ∧
      L.lookup p2 = some (.val (.word w2)) ∧
      L.lookup p3 = some (.val (.word w3)) ∧
      L.lookup p4 = some (.val (.word w4)) := by
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup fname vals body L rs hl
  simp only [lookupCodeHOLExact, hlook] at hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, _ | _⟩⟩⟩⟩
  · simp at hx
  · simp at hx
  · simp at hx
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hx
    rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hx
    rcases v3 with ⟨⟨w3⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hx
    rcases v4 with ⟨⟨w4⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hx
    refine ⟨w1, w2, w3, w4, rfl, ?_, ?_, ?_, ?_⟩
    · rw [← hx.2]; simp [Ne.symm hne14, Ne.symm hne13, Ne.symm hne12]
    · rw [← hx.2]; simp [Ne.symm hne24, Ne.symm hne23]
    · rw [← hx.2]; simp [Ne.symm hne34]
    · rw [← hx.2]; simp
  · simp at hx

/-! ## Section 2: `LogsListOK` preservation across `HeapByteEff` into `keccak_pad`/`keccak_st` -/

private def receiptKeccakIvls {F : Type} (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
   (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)]

private theorem receiptKeccakIvls_subset_fixedObjects {F : Type} (s : PanSemStateFiniteExact 64 F)
    {iv : Ivl} (hiv : iv ∈ receiptKeccakIvls s) : iv ∈ fixedObjects s := by
  unfold fixedObjects
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  simp only [receiptKeccakIvls, List.mem_cons, List.not_mem_nil, or_false] at hiv
  rcases hiv with rfl | rfl
  · exact List.mem_map.2 ⟨("keccak_pad", 136), by decide, rfl⟩
  · exact List.mem_map.2 ⟨("keccak_st", 200), by decide, rfl⟩

private theorem mem_eq_of_allocated_disj_fixed {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (heff : HeapByteEff s post (receiptKeccakIvls s) ["heap_ptr"])
    (hA : ArenaOK s) (hma : s.memaddrs = ordinaryDomain)
    {iv : Ivl} (hal : Allocated s iv)
    (hdj : ∀ f ∈ fixedObjects s, Disj iv f)
    {a : Nat} (ha8 : a % 8 = 0) (ha1 : iv.1 ≤ a) (ha2 : a + 8 ≤ iv.1 + iv.2) :
    post.memory (BitVec.ofNat 64 a) = s.memory (BitVec.ofNat 64 a) := by
  have hib : iv.1 + iv.2 ≤ 2 ^ 64 := M13.allocated_le_2pow64 hA hal
  have ha64 : a < 2 ^ 64 := by omega
  have hbit : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha64
  by_cases hdom : ordinaryDomain (BitVec.ofNat 64 a)
  · apply mem_eq_of_bytes_eq heff.be _ hdom
    intro k hk
    rw [hbit]
    by_contra hne
    have hin : InIvl (a + k) iv := ⟨by omega, by omega⟩
    have hnfree := allocated_not_in_free hA (Or.inr hal) hin
    rcases heff.byte_frame (a + k) (by omega) hne with ⟨x, hx, hbx⟩ | hfg | hhf
    · have hfx := receiptKeccakIvls_subset_fixedObjects s hx
      have hd := hdj x hfx
      obtain ⟨_, _⟩ := hbx
      rcases hd with d | d | d | d <;> omega
    · exact hnfree.1 hfg
    · exact hnfree.2 hhf
  · by_contra hne
    exact hdom (hma ▸ heff.out_dom _ hne)

private theorem memW_eq_of_allocated_disj_fixed {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (heff : HeapByteEff s post (receiptKeccakIvls s) ["heap_ptr"])
    (hA : ArenaOK s) (hma : s.memaddrs = ordinaryDomain)
    {iv : Ivl} (hal : Allocated s iv)
    (hdj : ∀ f ∈ fixedObjects s, Disj iv f)
    {a : Nat} (ha8 : a % 8 = 0) (ha1 : iv.1 ≤ a) (ha2 : a + 8 ≤ iv.1 + iv.2) :
    memW post a = memW s a := by
  unfold memW
  rw [mem_eq_of_allocated_disj_fixed heff hA hma hal hdj ha8 ha1 ha2]

private theorem wordAt_post_of_s {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hma_eq : post.memaddrs = s.memaddrs) {a : Nat} (hw : WordAt s a) : WordAt post a := by
  obtain ⟨_, hdom, _⟩ := hw
  cases hm : post.memory (BitVec.ofNat 64 a) with
  | word w' => exact ⟨w', hma_eq ▸ hdom, hm⟩

private theorem wordsOK_post_of_s {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hma_eq : post.memaddrs = s.memaddrs) {iv : Ivl} (hw : WordsOK s iv) : WordsOK post iv :=
  ⟨hw.1, hw.2.1, fun k hk => wordAt_post_of_s hma_eq (hw.2.2 k hk)⟩

private theorem logsListOK_preserved {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {logs : Nat}
    (hA : ArenaOK s) (hma : s.memaddrs = ordinaryDomain)
    (heff : HeapByteEff s post (receiptKeccakIvls s) ["heap_ptr"])
    (hl_nz : logs ≠ 0)
    (hLL : LogsListOK s logs)
    (hDF : LogsDisjFixed s logs) :
    memW post (logs + 8) < 2 ^ 28 ∧ LogsListOK post logs := by
  rcases hLL with rfl | ⟨hw_hdr, hal_hdr, hn_lt, hn_le_cap, hentries⟩
  · exact absurd rfl hl_nz
  rcases hDF with rfl | ⟨hal_arr, hdisj⟩
  · exact absurd rfl hl_nz
  have hdj_hdr : ∀ f ∈ fixedObjects s, Disj (logs, 24) f :=
    fun f hf => hdisj (logs, 24) (List.mem_append_left _ List.mem_cons_self) f hf
  have hdj_arr : ∀ f ∈ fixedObjects s, Disj (memW s logs, 8 * memW s (logs + 8)) f :=
    fun f hf => hdisj (memW s logs, 8 * memW s (logs + 8))
      (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)) f hf
  have hl8 : logs % 8 = 0 := hw_hdr.1
  have hm0 : memW post logs = memW s logs := by
    have := memW_eq_of_allocated_disj_fixed heff hA hma hal_hdr hdj_hdr (a := logs) hl8
      (by dsimp only; omega) (by dsimp only; omega)
    exact this
  have hm8 : memW post (logs + 8) = memW s (logs + 8) :=
    memW_eq_of_allocated_disj_fixed heff hA hma hal_hdr hdj_hdr (by omega)
      (by dsimp only; omega) (by dsimp only; omega)
  have hm16 : memW post (logs + 16) = memW s (logs + 16) :=
    memW_eq_of_allocated_disj_fixed heff hA hma hal_hdr hdj_hdr (by omega)
      (by dsimp only; omega) (by dsimp only; omega)
  refine ⟨by rw [hm8]; exact hn_lt, Or.inr ⟨wordsOK_post_of_s heff.memaddrs hw_hdr,
    M13.allocated_mono heff.hp_le heff.sp_le hal_hdr,
    by rw [hm8]; exact hn_lt,
    by rw [hm8, hm16]; exact hn_le_cap, ?_⟩⟩
  intro i hi
  rw [hm8] at hi
  rw [hm0]
  obtain ⟨hwa_i, hle_i⟩ := hentries i hi
  have ha_i_lt : memW s logs + 8 * i < 2 ^ 64 := by
    have := M13.allocated_le_2pow64 hA hal_arr; dsimp only at this; omega
  have ha_i8 : (memW s logs + 8 * i) % 8 = 0 := by
    obtain ⟨_, hdom_i, _⟩ := hwa_i
    rw [hma, ordinaryDomain_iff] at hdom_i
    have hbit : (BitVec.ofNat 64 (memW s logs + 8 * i)).toNat = memW s logs + 8 * i :=
      Nat.mod_eq_of_lt ha_i_lt
    rw [hbit] at hdom_i; exact hdom_i.1
  have hm_elem : memW post (memW s logs + 8 * i) = memW s (memW s logs + 8 * i) :=
    memW_eq_of_allocated_disj_fixed heff hA hma hal_arr hdj_arr ha_i8
      (by dsimp only; omega) (by dsimp only; omega)
  rw [hm_elem]
  refine ⟨wordAt_post_of_s heff.memaddrs hwa_i, ?_⟩
  set log := memW s (memW s logs + 8 * i)
  obtain ⟨hw_log, hin_log, hnt_le, hdlen_lt, hin_a, hin_t, hin_d⟩ := hle_i
  have hal_log : Allocated s (log, 40) := Or.inl hin_log
  have hlog_in_owned : (log, 40) ∈ logOwnedIvls s log := by
    unfold logOwnedIvls
    refine List.mem_filter.2 ⟨by simp [logRecordIvls], ?_⟩
    simp only [bne_iff_ne, ne_eq, Prod.mk.injEq, not_and]
    intro _ h40; omega
  have hlog_in_flat : (log, 40) ∈ (List.range (memW s (logs + 8))).flatMap
      (fun idx => logOwnedIvls s (memW s (memW s logs + 8 * idx))) :=
    List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, hlog_in_owned⟩
  have hdj_log : ∀ f ∈ fixedObjects s, Disj (log, 40) f :=
    fun f hf => hdisj (log, 40) (List.mem_append_right _ hlog_in_flat) f hf
  have hlog8 : log % 8 = 0 := hw_log.1
  have hlog0 : memW post log = memW s log :=
    memW_eq_of_allocated_disj_fixed heff hA hma hal_log hdj_log hlog8
      (by dsimp only; omega) (by dsimp only; omega)
  have hlog_8 : memW post (log + 8) = memW s (log + 8) :=
    memW_eq_of_allocated_disj_fixed heff hA hma hal_log hdj_log (by omega)
      (by dsimp only; omega) (by dsimp only; omega)
  have hlog_16 : memW post (log + 16) = memW s (log + 16) :=
    memW_eq_of_allocated_disj_fixed heff hA hma hal_log hdj_log (by omega)
      (by dsimp only; omega) (by dsimp only; omega)
  have hlog_24 : memW post (log + 24) = memW s (log + 24) :=
    memW_eq_of_allocated_disj_fixed heff hA hma hal_log hdj_log (by omega)
      (by dsimp only; omega) (by dsimp only; omega)
  have hlog_32 : memW post (log + 32) = memW s (log + 32) :=
    memW_eq_of_allocated_disj_fixed heff hA hma hal_log hdj_log (by omega)
      (by dsimp only; omega) (by dsimp only; omega)
  have hhp_le := heff.hp_le
  refine ⟨wordsOK_post_of_s heff.memaddrs hw_log,
    ⟨hin_log.1, le_trans hin_log.2 hhp_le⟩,
    by rw [hlog_16]; exact hnt_le,
    by rw [hlog_32]; exact hdlen_lt,
    by rw [hlog0]; exact ⟨hin_a.1, le_trans hin_a.2 hhp_le⟩,
    by rw [hlog_8, hlog_16]; exact ⟨hin_t.1, le_trans hin_t.2 hhp_le⟩,
    by rw [hlog_24, hlog_32]; exact ⟨hin_d.1, le_trans hin_d.2 hhp_le⟩⟩

/-! ## Section 3: Reusable `rlp_finish_list` body & local-call combinators, and `logs_bloom` call -/

private theorem eval_rlp_finish_list_body_exact {F : Type}
    (ent : PanSemStateFiniteExact 64 F) (dst0 pend0 : BitVec 64) (Rl : List Ivl)
    (hcode : ent.code = originalRuntimeCode) (hAR_ent : ArenaReady ent)
    (hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hent_pend : ent.locals.lookup (ofString "payload_end") = some (.val (.word pend0)))
    (hle : dst0.toNat + 9 ≤ pend0.toNat)
    (_hfit : pend0.toNat ≤ heapEnd)
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ pend0.toNat ≤ ivl.1 + ivl.2)
    (hnt_body : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_finish_list)).1 ≠
      some .timeOut) :
    let out := evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_finish_list)
    let payload := pend0.toNat - (dst0.toNat + 9)
    let total := rlpHeaderLenPure payload + payload
    (∀ rv, out.1 = some (.returned rv) →
      ∃ tw : BitVec 64,
        rv = .val (.word tw) ∧
        tw.toNat = total ∧
        total ≤ pend0.toNat - dst0.toNat ∧
        out.2.globals = ent.globals ∧
        HeapByteEff ent out.2 Rl []) ∧
    (∀ r, out.1 = some r → (∀ rv, r ≠ .returned rv) → ¬ Resumes (some r)) := by
  intro out payload total; dsimp only [out]
  have hhe264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  have hb_fl : sourceFnBody Guest.Software.guestFn_rlp_finish_list =
      .dec (ofString "payload") .one
        (.op .sub [.var .local (ofString "payload_end"),
          .op .add [.var .local (ofString "dst"), .const 9]])
        (.decCall (ofString "hl") .one (ofString "rlp_list_header_len")
          [.var .local (ofString "payload")]
          (.seq
            (.call (some (none, none)) (ofString "memcpy")
              [.op .add [.var .local (ofString "dst"), .var .local (ofString "hl")],
               .op .add [.var .local (ofString "dst"), .const 9],
               .var .local (ofString "payload")])
            (.seq
              (.call (some (none, none)) (ofString "rlp_encode_list_header")
                [.var .local (ofString "dst"), .var .local (ofString "payload")])
              (.return (.op .add [.var .local (ofString "hl"), .var .local (ofString "payload")]))))) := rfl
  have hd9_nat : (dst0 + 9).toNat = dst0.toNat + 9 := by
    rw [BitVec.toNat_add]; change (dst0.toNat + 9) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
  let pw : BitVec 64 := pend0 - (dst0 + 9)
  have hpw_nat : pw.toNat = payload := by
    change (pend0 - (dst0 + 9)).toNat = pend0.toNat - (dst0.toNat + 9)
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hd9_nat]; exact hle)), hd9_nat]
  rw [hb_fl, evaluateHOLFiniteState_dec_total] at hnt_body
  have hev_pw : @evalHOLExact 64 F _ ent.toExact
      (fun a => Classical.propDecidable (ent.memaddrs a))
      (.op .sub [.var .local (ofString "payload_end"),
        .op .add [.var .local (ofString "dst"), .const 9]]) =
      some (.val (.word pw)) := by
    simp [evalHOLExact, evalListHOLExact, hent_pend, hent_dst, wordOpHOL, wordOp, valueIsWord, valueWord, pw]
  have hsh_pw : shapeEqHOL .one (shapeOfHOLExact (.val (.word pw) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  dsimp only at hnt_body; rw [hev_pw] at hnt_body; dsimp only at hnt_body; rw [if_pos hsh_pw] at hnt_body
  set s1 := setVarHOLFinite (ofString "payload") (.val (.word pw)) ent
  have hAR_s1 : ArenaReady s1 := ⟨guestInv_setVar _ _ _ hAR_ent.1, hAR_ent.2⟩
  have hs1_pw : s1.locals.lookup (ofString "payload") = some (.val (.word pw)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_dst : s1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_dst,
      show ofString "payload" ≠ ofString "dst" by decide]
  obtain ⟨m1, hhl_nat, hhl1, hhl9, hm1_g, hm1_m, hm1_loc, heff_m1, hnt_m1, h_lhl_eq⟩ :=
    eval_decCall_rlp_list_header_len s1 "hl" (.var .local (ofString "payload")) pw _ Rl []
      hcode hAR_s1 hs1_pw hnt_body
  set hlw := BitVec.ofNat 64 (rlpHeaderLenPure pw.toNat)
  have hhl_nat' : hlw.toNat = rlpHeaderLenPure payload := by rw [hhl_nat, hpw_nat]
  have hm1_hl : m1.locals.lookup (ofString "hl") = some (.val (.word hlw)) := by
    rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hm1_pw : m1.locals.lookup (ofString "payload") = some (.val (.word pw)) := by
    rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_pw,
      show ofString "hl" ≠ ofString "payload" by decide]
  have hm1_dst : m1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
    rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_dst,
      show ofString "hl" ≠ ofString "dst" by decide]
  have hdhl_nat : (dst0 + hlw).toNat = dst0.toNat + hlw.toNat := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  rw [evaluateHOLFiniteState_seq_line780] at hnt_m1
  rcases hc_mc : evaluateHOLFiniteState m1
    (.call (some (none, none)) (ofString "memcpy")
      [.op .add [.var .local (ofString "dst"), .var .local (ofString "hl")],
       .op .add [.var .local (ofString "dst"), .const 9],
       .var .local (ofString "payload")]) with ⟨rmc, m2⟩
  have hnt_mc : rmc ≠ some .timeOut := by
    rintro rfl; rw [hc_mc] at hnt_m1; exact hnt_m1 rfl
  have hmc := eval_call_memcpy_heap m1
    (.op .add [.var .local (ofString "dst"), .var .local (ofString "hl")])
    (.op .add [.var .local (ofString "dst"), .const 9])
    (.var .local (ofString "payload"))
    (dst0 + hlw) (dst0 + 9) pw Rl [] heff_m1.arena.1.code heff_m1.arena
    (by simp [evalHOLExact, evalListHOLExact, hm1_dst, hm1_hl, wordOpHOL, wordOp, valueIsWord, valueWord])
    (by simp [evalHOLExact, evalListHOLExact, hm1_dst, wordOpHOL, wordOp, valueIsWord, valueWord])
    (by simp [evalHOLExact, hm1_pw])
    (fun _ => by
      obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
      exact ⟨ivl, hivl, by rw [hdhl_nat]; omega, by rw [hdhl_nat, hpw_nat]; omega⟩)
    (by rw [hc_mc]; exact hnt_mc)
  dsimp only at hmc; rw [hc_mc] at hmc
  have hbody_step1 : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_finish_list) =
      (let o := evaluateHOLFiniteState m1
          (.seq
            (.call (some (none, none)) (ofString "memcpy")
              [.op .add [.var .local (ofString "dst"), .var .local (ofString "hl")],
               .op .add [.var .local (ofString "dst"), .const 9],
               .var .local (ofString "payload")])
            (.seq
              (.call (some (none, none)) (ofString "rlp_encode_list_header")
                [.var .local (ofString "dst"), .var .local (ofString "payload")])
              (.return (.op .add [.var .local (ofString "hl"), .var .local (ofString "payload")]))));
       (o.1,
        { o.2 with
          locals := HolFiniteMapExact.resVarEq
            (HolFiniteMapExact.resVarEq o.2.locals (ofString "hl", s1.locals.lookup (ofString "hl")))
            (ofString "payload", ent.locals.lookup (ofString "payload")) })) := by
    rw [hb_fl, evaluateHOLFiniteState_dec_total]
    dsimp only; rw [hev_pw]; dsimp only; rw [if_pos hsh_pw]
    rw [h_lhl_eq]
  cases rmc with
  | some r_mc =>
    rw [hbody_step1, evaluateHOLFiniteState_seq_line780, hc_mc]
    dsimp only
    refine ⟨fun rv h => ?_, fun r hr hne_ret => ?_⟩
    · exfalso
      injection h with h'; subst h'
      exact hmc.2 (by simp) (Or.inl ⟨rv, rfl⟩)
    · injection hr with h'; subst h'
      exact hmc.2 (by simp)
  | none =>
    rw [hc_mc] at hnt_m1; dsimp only at hnt_m1
    obtain ⟨heff_m2, hm2_loc, _⟩ := hmc.1 rfl
    have hm2_hl : m2.locals.lookup (ofString "hl") = some (.val (.word hlw)) := by
      rw [hm2_loc]; exact hm1_hl
    have hm2_pw : m2.locals.lookup (ofString "payload") = some (.val (.word pw)) := by
      rw [hm2_loc]; exact hm1_pw
    have hm2_dst : m2.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      rw [hm2_loc]; exact hm1_dst
    rw [evaluateHOLFiniteState_seq_line780] at hnt_m1
    rcases hc_lh : evaluateHOLFiniteState m2
      (.call (some (none, none)) (ofString "rlp_encode_list_header")
        [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "payload")]) with ⟨rlh, m3⟩
    have hnt_lh : rlh ≠ some .timeOut := by
      rintro rfl; rw [hc_lh] at hnt_m1; exact hnt_m1 rfl
    have hlh := eval_call_rlp_encode_list_header m2
      (ExpHOL.var VarKind.local (ofString "dst")) (ExpHOL.var VarKind.local (ofString "payload"))
      dst0 pw Rl [] heff_m2.arena.1.code heff_m2.arena
      (by simp [evalHOLExact, hm2_dst])
      (by simp [evalHOLExact, hm2_pw])
      (by obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
          exact ⟨ivl, hivl, h1, by rw [hpw_nat]; have := rlpHeaderLenPure_bounds payload; omega⟩)
      (by rw [hc_lh]; exact hnt_lh)
    dsimp only at hlh; rw [hc_lh] at hlh
    cases rlh with
    | some r_lh =>
      rw [hbody_step1, evaluateHOLFiniteState_seq_line780, hc_mc]; dsimp only
      rw [evaluateHOLFiniteState_seq_line780, hc_lh]; dsimp only
      refine ⟨fun rv h => ?_, fun r hr _ => ?_⟩
      · exfalso
        injection h with h'; subst h'
        exact hlh.2 (by simp) (Or.inl ⟨rv, rfl⟩)
      · injection hr with h'; subst h'
        exact hlh.2 (by simp)
    | none =>
      obtain ⟨_, heff_m3, hm3_loc⟩ := hlh.1 rfl
      have hm3_hl : m3.locals.lookup (ofString "hl") = some (.val (.word hlw)) := by
        rw [hm3_loc]; exact hm2_hl
      have hm3_pw : m3.locals.lookup (ofString "payload") = some (.val (.word pw)) := by
        rw [hm3_loc]; exact hm2_pw
      let tw : BitVec 64 := hlw + pw
      have hhl_bds : rlpHeaderLenPure (pend0.toNat - (dst0.toNat + 9)) ≤ 9 :=
        (rlpHeaderLenPure_bounds (pend0.toNat - (dst0.toNat + 9))).2
      have htw_lt : rlpHeaderLenPure payload + payload < 2 ^ 64 := by
        dsimp [payload]; omega
      have htw_nat : tw.toNat = total := by
        change (hlw + pw).toNat = rlpHeaderLenPure payload + payload
        rw [BitVec.toNat_add, hhl_nat', hpw_nat]
        change (rlpHeaderLenPure payload + payload) % 2 ^ 64 = _
        exact Nat.mod_eq_of_lt htw_lt
      have hret_m3 : evaluateHOLFiniteState m3
          (.return (.op .add [ExpHOL.var VarKind.local (ofString "hl"), ExpHOL.var VarKind.local (ofString "payload")])) =
          (some (.returned (.val (.word tw))), m3.emptyLocalsHOLFinite) := by
        rw [evaluateHOLFiniteState_return]
        have hev_tw : @evalHOLExact 64 F _ m3.toExact
            (fun a => Classical.propDecidable (m3.memaddrs a))
            (.op .add [ExpHOL.var VarKind.local (ofString "hl"), ExpHOL.var VarKind.local (ofString "payload")]) =
            some (.val (.word tw)) := by
          simp [evalHOLExact, evalListHOLExact, hm3_hl, hm3_pw, wordOpHOL, wordOp, valueIsWord, valueWord, tw]
        rw [hev_tw]; dsimp only
        have hsz : sizeOfShapeWithContextHOL m3.structs (shapeOfHOLExact (.val (.word tw) : ValueHOL 64)) ≤ 32 := by
          simp [shapeOfHOLExact]
        rw [if_pos hsz]
      rw [hbody_step1, evaluateHOLFiniteState_seq_line780, hc_mc]; dsimp only
      rw [evaluateHOLFiniteState_seq_line780, hc_lh]; dsimp only
      rw [hret_m3]; dsimp only
      have heff_ent_s1 : HeapByteEff ent s1 Rl [] :=
        (HeapByteEff.refl hAR_ent Rl []).locals_clock s1.locals s1.clock
      have heff_ent_m3 : HeapByteEff ent m3 Rl [] :=
        ((heff_ent_s1.trans heff_m1).trans heff_m2).trans heff_m3
      have hm3_g : m3.globals = ent.globals := by
        apply HolFiniteMapExact.ext_lookup
        intro k
        exact (heff_ent_m3.globals k (by simp)).symm
      refine ⟨fun rv h => ?_, fun r hr hne_ret => ?_⟩
      · injection h with h'; injection h' with h''
        exact ⟨tw, h''.symm, htw_nat, by dsimp [total, payload]; omega, hm3_g,
          heff_ent_m3.locals_clock _ m3.clock⟩
      · injection hr with h'
        exact False.elim (hne_ret (.val (.word tw)) h'.symm)

theorem eval_call_local_rlp_finish_list {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (dstExp pendExp : ExpHOL 64)
    (dst0 pend0 : BitVec 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl_old : ∃ w_old : BitVec 64, s.locals.lookup (ofString lname) = some (.val (.word w_old)))
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hpend : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) pendExp =
      some (.val (.word pend0)))
    (hle : dst0.toNat + 9 ≤ pend0.toNat)
    (hfit : pend0.toNat ≤ heapEnd)
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ pend0.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "rlp_finish_list")
        [dstExp, pendExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "rlp_finish_list")
        [dstExp, pendExp])
    let payload := pend0.toNat - (dst0.toNat + 9)
    let total := rlpHeaderLenPure payload + payload
    (out.1 = none →
      ∃ tw : BitVec 64,
        tw.toNat = total ∧
        total ≤ pend0.toNat - dst0.toNat ∧
        out.2.globals = s.globals ∧
        out.2.locals = s.locals.update (ofString lname, .val (.word tw)) ∧
        HeapByteEff s out.2 Rl gw) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  intro out payload total; dsimp only [out]
  obtain ⟨w_old, hw_old⟩ := hl_old
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, pendExp] = some [.val (.word dst0), .val (.word pend0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hpend]
  have hlk := pan_two_word_lookup s.code.lookup (ofString "rlp_finish_list")
    (ofString "dst") (ofString "payload_end")
    (sourceFnBody Guest.Software.guestFn_rlp_finish_list) dst0 pend0 (by decide)
    (by rw [hcode]; exact lookup_rlp_finish_list)
  simp only [ha, hlk] at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set cmap := (HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
      (ofString "payload_end", ValueHOL.val (.word pend0))
    set ent := callEntryStateHOLFinite s cmap
    have hAR_ent : ArenaReady ent := ⟨guestInv_callEntry s cmap hAR.1, hAR.2⟩
    have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "payload_end" ≠ ofString "dst" by decide]
    have hent_pend : ent.locals.lookup (ofString "payload_end") = some (.val (.word pend0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hfl : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_finish_list) with ⟨rfl0, sfl⟩
    have hnt_fl : rfl0 ≠ some .timeOut := by
      rintro rfl; rw [hfl] at hnt; exact hnt rfl
    obtain ⟨hret, hnonret⟩ := eval_rlp_finish_list_body_exact ent dst0 pend0 Rl
      hcode hAR_ent hent_dst hent_pend hle hfit hin_ivl (by rw [hfl]; exact hnt_fl)
    rw [hfl] at hret hnonret
    dsimp only at hret hnonret
    simp only [hfl] at hnt ⊢
    cases rfl0 with
    | none => exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt_fl
      | exception eid ev =>
        exact ⟨fun h => by simp at h, fun _ => hnonret (.exception eid ev) rfl (fun _ h => by cases h)⟩
      | returned rv =>
        obtain ⟨tw, rfl, htw_nat, htw_le, hg_sfl, heff_fl⟩ := hret rv rfl
        have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word tw) : ValueHOL 64)) .one = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        have hval : isValidValueHOLExact s.toExact VarKind.local (ofString lname) (.val (.word tw)) = true := by
          simp [isValidValueHOLExact, lookupKvarHOLExact, hw_old, shapeOfHOLExact, shapeEqHOL]
        dsimp only
        rw [if_pos hsh, if_pos hval]
        let mid := setVarHOLFinite (ofString lname) (.val (.word tw)) { sfl with locals := s.locals }
        have heff0 : HeapByteEff s ent Rl [] :=
          (HeapByteEff.refl hAR Rl []).locals_clock ent.locals ent.clock
        have heff_mid0 : HeapByteEff s mid Rl [] :=
          (heff0.trans heff_fl).locals_clock mid.locals mid.clock
        have heff_mid : HeapByteEff s mid Rl gw :=
          heff_mid0.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩) (fun _ h => by cases h)
        exact ⟨fun _ => ⟨tw, htw_nat, htw_le, hg_sfl, rfl, heff_mid⟩,
          fun h => False.elim (h rfl)⟩
      | «break» | «continue» | error =>
        exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
      | finalFfi _ =>
        exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

private theorem heapByteEff_of_seq_none {F : Type}
    {s0 s m : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64} {Rl : List Ivl} {gw : List String}
    (ha : evaluateHOLFiniteState s a = (none, m))
    (hb : HeapByteEff s0 (evaluateHOLFiniteState m b).2 Rl gw) :
    HeapByteEff s0 (evaluateHOLFiniteState s (.seq a b)).2 Rl gw := by
  rw [evaluateHOLFiniteState_seq_line780, ha]
  exact hb

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

private theorem call0_any_locals_er {F : Type} (s : PanSemStateFiniteExact 64 F)
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

private def erLogsBloomInnerBody : ProgHOL 64 :=
  .seq
    (.call (some (none, none)) (ofString "add_to_bloom")
      [ExpHOL.var VarKind.local (ofString "out"),
       .op .add
         [.load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 8]),
          .panop .mul [ExpHOL.var VarKind.local (ofString "j"), .const 32]],
       .const 32])
    (.assign VarKind.local (ofString "j")
      (.op .add [ExpHOL.var VarKind.local (ofString "j"), .const 1]))

private def erLogsBloomInnerWhile : ProgHOL 64 :=
  .while (.cmp .less (ExpHOL.var VarKind.local (ofString "j"))
    (ExpHOL.var VarKind.local (ofString "nt"))) erLogsBloomInnerBody

private theorem erLogsBloomInnerWhile_eff {F : Type}
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
    (hnt : (evaluateHOLFiniteState s erLogsBloomInnerWhile).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState s erLogsBloomInnerWhile).1 = none ∨
      Resumes (evaluateHOLFiniteState s erLogsBloomInnerWhile).1) :
    let out := evaluateHOLFiniteState s erLogsBloomInnerWhile
    HeapByteEff s out.2 Rl gw ∧
    (out.1 = none →
      out.2.locals.lookup (ofString "out") = some (.val (.word out0)) ∧
      out.2.locals.lookup (ofString "i") = s.locals.lookup (ofString "i") ∧
      out.2.locals.lookup (ofString "n") = s.locals.lookup (ofString "n") ∧
      out.2.locals.lookup (ofString "p") = s.locals.lookup (ofString "p")) := by
  induction clk generalizing s with
  | zero =>
    dsimp only [erLogsBloomInnerWhile] at hnt hor ⊢
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
    dsimp only [erLogsBloomInnerWhile] at hnt hor ⊢
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
          dsimp only [erLogsBloomInnerBody] at hnt hor ⊢
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
              dsimp only [erLogsBloomInnerWhile, erLogsBloomInnerBody] at ih_res
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

private def erLogsBloomOuterBody : ProgHOL 64 :=
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
          (.seq erLogsBloomInnerWhile
            (.assign VarKind.local (ofString "i")
              (.op .add [ExpHOL.var VarKind.local (ofString "i"), .const 1]))))))

private def erLogsBloomOuterWhile : ProgHOL 64 :=
  .while (.cmp .less (ExpHOL.var VarKind.local (ofString "i"))
    (ExpHOL.var VarKind.local (ofString "n"))) erLogsBloomOuterBody

private theorem erLogsBloomOuterBody_step {F : Type}
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
    (hnt : (evaluateHOLFiniteState s erLogsBloomOuterBody).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState s erLogsBloomOuterBody).1 = none ∨
      Resumes (evaluateHOLFiniteState s erLogsBloomOuterBody).1) :
    let out := evaluateHOLFiniteState s erLogsBloomOuterBody
    HeapByteEff s out.2 Rl gw ∧
    out.1 ≠ some .continue ∧
    out.1 ≠ some .break ∧
    (out.1 = none → out.2.locals.lookup (ofString "out") = some (.val (.word out0))) := by
  intro out; dsimp only [out]; dsimp only [erLogsBloomOuterBody] at hnt hor ⊢
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
            rw [evaluateHOLFiniteState_dec_total] at hnt hor ⊢
            simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt hor ⊢
            set s4 := setVarHOLFinite (ofString "j") (.val (.word 0)) s3
            have heff_s_s4 : HeapByteEff s s4 Rl gw := heff_s_s2.locals_clock s4.locals s4.clock
            have hs4_out : s4.locals.lookup (ofString "out") = some (.val (.word out0)) := by
              simp [s4, s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_out,
                show ofString "j" ≠ ofString "out" by decide,
                show ofString "nt" ≠ ofString "out" by decide]
            rw [evaluateHOLFiniteState_seq_line780] at hnt hor ⊢
            rcases hwi : evaluateHOLFiniteState s4 erLogsBloomInnerWhile with ⟨rwi, s5⟩
            have hnt_wi : rwi ≠ some .timeOut := by rintro rfl; rw [hwi] at hnt; exact hnt rfl
            have hwi_nbc : rwi ≠ some .break ∧ rwi ≠ some .continue := by
              have hwnbc : ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock ≤ k →
                  (evaluateHOLFiniteState st erLogsBloomInnerWhile).1 ≠ some .break ∧
                  (evaluateHOLFiniteState st erLogsBloomInnerWhile).1 ≠ some .continue := by
                intro k
                induction k with
                | zero =>
                  intro st hst_k; dsimp only [erLogsBloomInnerWhile]; rw [evaluateHOLFiniteState_while_total]
                  split
                  · split
                    · split
                      · simp
                      · omega
                    · simp
                  · simp
                | succ k ih_k =>
                  intro st hst_k; dsimp only [erLogsBloomInnerWhile]; rw [evaluateHOLFiniteState_while_total]
                  split
                  · split
                    · split
                      · simp
                      · dsimp only; rw [fixClockHOLFinite_evaluateState]
                        have hrem_k := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) erLogsBloomInnerBody
                        rcases hbk : evaluateHOLFiniteState (decClockHOLFinite st) erLogsBloomInnerBody with ⟨rbk, mbk⟩
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
            have hwi_eff := erLogsBloomInnerWhile_eff s4.clock s0 s4 out0 Rl gw le_rfl
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

private theorem erLogsBloomOuterWhile_eff {F : Type}
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
    (hnt : (evaluateHOLFiniteState s erLogsBloomOuterWhile).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState s erLogsBloomOuterWhile).1 = none ∨
      Resumes (evaluateHOLFiniteState s erLogsBloomOuterWhile).1) :
    HeapByteEff s (evaluateHOLFiniteState s erLogsBloomOuterWhile).2 Rl gw := by
  induction clk generalizing s with
  | zero =>
    dsimp only [erLogsBloomOuterWhile] at hnt ⊢
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
    dsimp only [erLogsBloomOuterWhile] at hnt hor ⊢
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
          have hcle := evaluateHOLFiniteState_clock_le sd erLogsBloomOuterBody
          rcases hbr : evaluateHOLFiniteState sd erLogsBloomOuterBody with ⟨rb, mid⟩
          have hnt_b : rb ≠ some .timeOut := by
            rintro rfl; rw [hbr] at hnt; exact hnt rfl
          have hnbc_b : rb ≠ some .break ∧ rb ≠ some .continue := by
            dsimp only [erLogsBloomOuterBody] at hbr
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
                          rcases hwi_t : evaluateHOLFiniteState st_wi erLogsBloomInnerWhile with ⟨rwi_t, mwi_t⟩
                          have hwnbc : ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock ≤ k →
                              (evaluateHOLFiniteState st erLogsBloomInnerWhile).1 ≠ some .break ∧
                              (evaluateHOLFiniteState st erLogsBloomInnerWhile).1 ≠ some .continue := by
                            intro k0
                            induction k0 with
                            | zero =>
                              intro st hst_k; dsimp only [erLogsBloomInnerWhile]; rw [evaluateHOLFiniteState_while_total]
                              split
                              · split
                                · split
                                  · simp
                                  · omega
                                · simp
                              · simp
                            | succ k0 ih_k =>
                              intro st _; dsimp only [erLogsBloomInnerWhile]; rw [evaluateHOLFiniteState_while_total]
                              split
                              · split
                                · split
                                  · simp
                                  · dsimp only; rw [fixClockHOLFinite_evaluateState]
                                    have hrem_k := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) erLogsBloomInnerBody
                                    rcases hbk : evaluateHOLFiniteState (decClockHOLFinite st) erLogsBloomInnerBody with ⟨rbk, mbk⟩
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
          have hstep := erLogsBloomOuterBody_step s0 sd out0 Rl gw
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

private theorem eval_call_logs_bloom {F : Type}
    (s : PanSemStateFiniteExact 64 F) (logsExp outExp : ExpHOL 64)
    (logs0 out0 : BitVec 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hlogs : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) logsExp =
      some (.val (.word logs0)))
    (hout : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) outExp =
      some (.val (.word out0)))
    (hout_in : ∃ ivl ∈ Rl, ivl.1 ≤ out0.toNat ∧ out0.toNat + 256 ≤ ivl.1 + ivl.2)
    (hpad_in : globN s "keccak_pad" ≠ 0 →
      ∃ ivl ∈ Rl, ivl.1 ≤ globN s "keccak_pad" ∧ globN s "keccak_pad" + 136 ≤ ivl.1 + ivl.2)
    (hst_in : globN s "keccak_st" ≠ 0 →
      ∃ ivl ∈ Rl, ivl.1 ≤ globN s "keccak_st" ∧ globN s "keccak_st" + 200 ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "logs_bloom") [logsExp, outExp])).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "logs_bloom") [logsExp, outExp])).1 = none ∨
      Resumes (evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "logs_bloom") [logsExp, outExp])).1) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "logs_bloom") [logsExp, outExp])
    HeapByteEff s out.2 Rl ["heap_ptr"] ∧
    (out.1 = none → out.2.locals = s.locals) := by
  intro out; dsimp only [out]
  refine ⟨?_, call0_any_locals_er s (ofString "logs_bloom") [logsExp, outExp]⟩
  rw [evaluateHOLFiniteState_call] at hnt hor ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [logsExp, outExp] = some [.val (.word logs0), .val (.word out0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hlogs, hout]
  have hlk := pan_two_word_lookup s.code.lookup (ofString "logs_bloom")
    (ofString "logs") (ofString "out")
    (sourceFnBody Guest.Software.guestFn_logs_bloom) logs0 out0 (by decide)
    (by rw [hcode]; exact lookup_logs_bloom)
  simp only [ha, hlk] at hnt hor ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt hor ⊢
    set cmap := (HolFiniteMapExact.empty.update (ofString "logs", ValueHOL.val (.word logs0))).update
      (ofString "out", ValueHOL.val (.word out0))
    set ent := callEntryStateHOLFinite s cmap
    have hent_AR : ArenaReady ent := ⟨guestInv_callEntry s cmap hAR.1, hAR.2⟩
    have hent_out : ent.locals.lookup (ofString "out") = some (.val (.word out0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    suffices hbody_eff : HeapByteEff ent
        (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_logs_bloom)).2 Rl ["heap_ptr"] by
      have heff_s_ent : HeapByteEff s ent Rl ["heap_ptr"] :=
        (HeapByteEff.refl hAR Rl ["heap_ptr"]).locals_clock ent.locals ent.clock
      have heff_post : HeapByteEff s
          (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_logs_bloom)).2 Rl ["heap_ptr"] :=
        heff_s_ent.trans hbody_eff
      rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_logs_bloom) with ⟨rb, sb⟩
      rw [hrun] at heff_post
      change HeapByteEff s (let x := evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_logs_bloom); _) Rl ["heap_ptr"]
      rw [hrun]; dsimp only
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
    have hnt2 : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_logs_bloom)).1 ≠ some .timeOut := by
      rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_logs_bloom) with ⟨rb, sb⟩
      rintro rfl; rw [hrun] at hnt; exact hnt rfl
    have hres2 : Resumes (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_logs_bloom)).1 := by
      rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_logs_bloom) with ⟨rb, sb⟩
      rw [hrun] at hor; dsimp only at hor ⊢
      cases rb with
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
    have hb : sourceFnBody Guest.Software.guestFn_logs_bloom =
        .seq (.call (some (none, none)) (ofString "memzero")
            [ExpHOL.var VarKind.local (ofString "out"), .const 256])
          (.dec (ofString "n") .one
            (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "logs"), .const 8]))
            (.dec (ofString "p") .one
              (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "logs"), .const 0]))
              (.dec (ofString "i") .one (.const 0)
                (.seq erLogsBloomOuterWhile
                  (.return (.const 0)))))) := rfl
    rw [hb] at hnt2 hres2 ⊢
    rw [evaluateHOLFiniteState_seq_line780] at hnt2 hres2
    rcases hmz : evaluateHOLFiniteState ent
        (.call (some (none, none)) (ofString "memzero")
          [ExpHOL.var VarKind.local (ofString "out"), .const 256]) with ⟨rmz, s1⟩
    have hnt_mz : rmz ≠ some .timeOut := by rintro rfl; rw [hmz] at hnt2; exact hnt2 rfl
    have h1 := eval_call_memzero_heap ent
      (ExpHOL.var VarKind.local (ofString "out")) (.const 256)
      out0 256 Rl ["heap_ptr"] hcode hent_AR hent_out rfl
      (fun _ => hout_in)
      (by rw [hmz]; exact hnt_mz)
    dsimp only at h1; rw [hmz] at h1 hnt2 hres2
    cases rmz with
    | some _ => exfalso; exact h1.2 (by simp) hres2
    | none =>
      dsimp only at hnt2 hres2 h1
      refine heapByteEff_of_seq_none hmz ?_
      obtain ⟨hdom_fn, heff01, hs1_loc, _⟩ := h1.1 rfl
      have hdom : sourceBase ≤ out0.toNat ∧ out0.toNat + 256 ≤ heapEnd := hdom_fn (by decide)
      rw [evaluateHOLFiniteState_dec_total] at hnt2 hres2 ⊢
      rcases hn_ev : evalHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
          (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "logs"), .const 8])) with _ | vn
      · simp only [evalHOLFinite] at hn_ev; simp only [hn_ev]; exact heff01
      · simp only [evalHOLFinite] at hn_ev; simp only [hn_ev] at hnt2 hres2 ⊢
        by_cases hsh_n : shapeEqHOL .one (shapeOfHOLExact vn) = true
        · rw [if_pos hsh_n] at hnt2 hres2 ⊢
          dsimp only at hnt2 hres2 ⊢
          set s2 := setVarHOLFinite (ofString "n") vn s1
          suffices hs2_tail : HeapByteEff ent
              (evaluateHOLFiniteState s2
                (.dec (ofString "p") .one
                  (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "logs"), .const 0]))
                  (.dec (ofString "i") .one (.const 0)
                    (.seq erLogsBloomOuterWhile (.return (.const 0)))))).2 Rl ["heap_ptr"] by
            exact hs2_tail.locals_clock _ _
          rw [evaluateHOLFiniteState_dec_total] at hnt2 hres2 ⊢
          rcases hp_ev : evalHOLFinite s2 (h := fun a => Classical.propDecidable (s2.memaddrs a))
              (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "logs"), .const 0])) with _ | vp
          · simp only [evalHOLFinite] at hp_ev; simp only [hp_ev]; exact heff01.locals_clock s2.locals s2.clock
          · simp only [evalHOLFinite] at hp_ev; simp only [hp_ev] at hnt2 hres2 ⊢
            by_cases hsh_p : shapeEqHOL .one (shapeOfHOLExact vp) = true
            · rw [if_pos hsh_p] at hnt2 hres2 ⊢
              dsimp only at hnt2 hres2 ⊢
              set s3 := setVarHOLFinite (ofString "p") vp s2
              suffices hs3_tail : HeapByteEff ent
                  (evaluateHOLFiniteState s3
                    (.dec (ofString "i") .one (.const 0)
                      (.seq erLogsBloomOuterWhile (.return (.const 0))))).2 Rl ["heap_ptr"] by
                exact hs3_tail.locals_clock _ _
              rw [evaluateHOLFiniteState_dec_total] at hnt2 hres2 ⊢
              simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt2 hres2 ⊢
              set s4 := setVarHOLFinite (ofString "i") (.val (.word 0)) s3
              have heff_ent_s4 : HeapByteEff ent s4 Rl ["heap_ptr"] := heff01.locals_clock s4.locals s4.clock
              have hs4_out : s4.locals.lookup (ofString "out") = some (.val (.word out0)) := by
                simp [s4, s3, s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_loc, hent_out,
                  show ofString "i" ≠ ofString "out" by decide,
                  show ofString "p" ≠ ofString "out" by decide,
                  show ofString "n" ≠ ofString "out" by decide]
              suffices hs4_tail : HeapByteEff ent
                  (evaluateHOLFiniteState s4 (.seq erLogsBloomOuterWhile (.return (.const 0)))).2 Rl ["heap_ptr"] by
                exact hs4_tail.locals_clock _ _
              rw [evaluateHOLFiniteState_seq_line780] at hnt2 hres2 ⊢
              rcases hwo : evaluateHOLFiniteState s4 erLogsBloomOuterWhile with ⟨rwo, s5⟩
              have hnt_wo : rwo ≠ some .timeOut := by rintro rfl; rw [hwo] at hnt2; exact hnt2 rfl
              have hor_wo : rwo = none ∨ Resumes rwo := by
                cases rwo with
                | none => exact Or.inl rfl
                | some _ => rw [hwo] at hres2; right; exact hres2
              have hwo_eff := erLogsBloomOuterWhile_eff s4.clock ent s4 out0 Rl ["heap_ptr"] le_rfl
                heff_ent_s4 (by simp) (by decide) (by decide) hs4_out hdom hout_in
                hpad_in hst_in (by rw [hwo]; exact hnt_wo) (by rw [hwo]; exact hor_wo)
              rw [hwo] at hwo_eff
              have heff_ent_s5 : HeapByteEff ent s5 Rl ["heap_ptr"] := heff_ent_s4.trans hwo_eff
              cases rwo with
              | some _ => exact heff_ent_s5
              | none =>
                dsimp only
                exact heff_ent_s5.trans
                  (HeapByteEff.of_byteEff heff_ent_s5.arena (R13Shards.Keccak256.byteEff_return s5 (.const 0) Rl))
            · rw [if_neg hsh_p]; exact heff01.locals_clock s2.locals s2.clock
        · rw [if_neg hsh_n]; exact heff01

/-! ## Section 4: `logs_encoded_bound` and `encode_logs` -/

private def logsEncodedSum {F : Type} (s : PanSemStateFiniteExact 64 F) (p : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let log := memW s (p + 8 * k)
    logsEncodedSum s p k + 64 + 33 * memW s (log + 16) + memW s (log + 32)

private theorem logsEncodedSum_bound {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p : Nat) (k : Nat)
    (hstep : ∀ i < k, memW s (memW s (p + 8 * i) + 16) ≤ 4 ∧
      memW s (memW s (p + 8 * i) + 32) < 2 ^ 32) :
    logsEncodedSum s p k ≤ k * (2 ^ 32 + 196) := by
  induction k with
  | zero => simp [logsEncodedSum]
  | succ k ih =>
    have hk := hstep k (by omega)
    have hih := ih (fun i hi => hstep i (by omega))
    simp only [logsEncodedSum]
    have hmul : (k + 1) * (2 ^ 32 + 196) = k * (2 ^ 32 + 196) + (2 ^ 32 + 196) := by
      rw [Nat.add_mul, Nat.one_mul]
    rw [hmul]
    omega

private theorem mem_load_one_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (addrExp : ExpHOL 64) (addr : BitVec 64)
    (haddr : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) addrExp =
      some (.val (.word addr)))
    (hwa : WordAt s addr.toNat) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.load .one addrExp) =
      some (.val (.word (BitVec.ofNat 64 (memW s addr.toNat)))) := by
  have hb_eq : BitVec.ofNat 64 addr.toNat = addr := BitVec.ofNat_toNat 64 addr
  obtain ⟨w, hdom, hm⟩ := hwa
  rw [hb_eq] at hdom hm
  have hmw : memW s addr.toNat = w.toNat := by
    unfold memW; rw [hb_eq, hm]
  rw [hmw, BitVec.ofNat_toNat]
  simp [evalHOLExact, haddr, memLoadHOLExact, isWfShapeExactHOL, hdom, hm]

private theorem logsListOK_parts {F : Type} {s : PanSemStateFiniteExact 64 F} {logs : Nat}
    (hA : ArenaOK s)
    (hl_nz : logs ≠ 0) (hLL : LogsListOK s logs) (hDF : LogsDisjFixed s logs) :
    WordsOK s (logs, 24) ∧
    Allocated s (logs, 24) ∧
    Allocated s (memW s logs, 8 * memW s (logs + 8)) ∧
    logs + 24 ≤ 2 ^ 64 ∧
    memW s logs + 8 * memW s (logs + 8) ≤ 2 ^ 64 ∧
    memW s (logs + 8) < 2 ^ 28 ∧
    WordAt s logs ∧ WordAt s (logs + 8) ∧
    (∀ i, i < memW s (logs + 8) →
      WordAt s (memW s logs + 8 * i) ∧
      LogEntryOK s (memW s (memW s logs + 8 * i)) ∧
      let log := memW s (memW s logs + 8 * i)
      log + 40 ≤ globN s "heap_ptr" ∧
      WordAt s log ∧ WordAt s (log + 8) ∧ WordAt s (log + 16) ∧
      WordAt s (log + 24) ∧ WordAt s (log + 32)) := by
  rcases hLL with rfl | ⟨hw_hdr, hal_hdr, hn_lt, _, hentries⟩
  · exact absurd rfl hl_nz
  rcases hDF with rfl | ⟨hal_arr, _⟩
  · exact absurd rfl hl_nz
  have hhdr_b := M13.allocated_le_2pow64 hA hal_hdr
  have harr_b := M13.allocated_le_2pow64 hA hal_arr
  have hw0 : WordAt s logs := by
    have := hw_hdr.2.2 0 (by show 0 < 24 / 8; decide); simpa using this
  have hw8 : WordAt s (logs + 8) := by
    have := hw_hdr.2.2 1 (by show 1 < 24 / 8; decide); simpa using this
  refine ⟨hw_hdr, hal_hdr, hal_arr, hhdr_b, harr_b, hn_lt, hw0, hw8, fun i hi => ?_⟩
  obtain ⟨hwa_i, hle_i⟩ := hentries i hi
  set log := memW s (memW s logs + 8 * i)
  have hw_log : WordsOK s (log, 40) := hle_i.1
  have hin_log : Inside (log, 40) sourceBase (globN s "heap_ptr") := hle_i.2.1
  have hl0 : WordAt s log := by have := hw_log.2.2 0 (by show 0 < 40 / 8; decide); simpa using this
  have hl8 : WordAt s (log + 8) := by have := hw_log.2.2 1 (by show 1 < 40 / 8; decide); simpa using this
  have hl16 : WordAt s (log + 16) := by have := hw_log.2.2 2 (by show 2 < 40 / 8; decide); simpa using this
  have hl24 : WordAt s (log + 24) := by have := hw_log.2.2 3 (by show 3 < 40 / 8; decide); simpa using this
  have hl32 : WordAt s (log + 32) := by have := hw_log.2.2 4 (by show 4 < 40 / 8; decide); simpa using this
  exact ⟨hwa_i, hle_i, hin_log.2, hl0, hl8, hl16, hl24, hl32⟩

private def lebBody : ProgHOL 64 :=
  .dec (ofString "log") .one
    (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "p"),
      .panop .mul [ExpHOL.var VarKind.local (ofString "i"), .const 8]]))
    (.seq
      (.assign VarKind.local (ofString "total")
        (.op .add [ExpHOL.var VarKind.local (ofString "total"),
          .const 64,
          .panop .mul
            [.load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 16]),
             .const 33],
          .load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 32])]))
      (.assign VarKind.local (ofString "i")
        (.op .add [ExpHOL.var VarKind.local (ofString "i"), .const 1])))

private def lebWhile : ProgHOL 64 :=
  .while (.cmp .less (ExpHOL.var VarKind.local (ofString "i"))
    (ExpHOL.var VarKind.local (ofString "n"))) lebBody

private theorem lebWhile_exact {F : Type}
    (clk : Nat) (s0 t : PanSemStateFiniteExact 64 F)
    (nw pw iw totw : BitVec 64)
    (hclk : t.clock ≤ clk)
    (hlf : M13.LocFrame s0 t)
    (hA0 : ArenaOK s0) (hma0 : s0.memaddrs = ordinaryDomain)
    (hn_lt : nw.toNat < 2 ^ 28)
    (hp_b : pw.toNat + 8 * nw.toNat ≤ 2 ^ 64)
    (hi_le : iw.toNat ≤ nw.toNat)
    (htot_eq : totw.toNat = 16 + logsEncodedSum s0 pw.toNat iw.toNat)
    (ht_n : t.locals.lookup (ofString "n") = some (.val (.word nw)))
    (ht_p : t.locals.lookup (ofString "p") = some (.val (.word pw)))
    (ht_i : t.locals.lookup (ofString "i") = some (.val (.word iw)))
    (ht_tot : t.locals.lookup (ofString "total") = some (.val (.word totw)))
    (hentries : ∀ k, k < nw.toNat →
      WordAt s0 (pw.toNat + 8 * k) ∧
      let log := memW s0 (pw.toNat + 8 * k)
      log + 40 ≤ globN s0 "heap_ptr" ∧
      memW s0 (log + 16) ≤ 4 ∧ memW s0 (log + 32) < 2 ^ 32 ∧
      WordAt s0 (log + 16) ∧ WordAt s0 (log + 32))
    (hnt : (evaluateHOLFiniteState t lebWhile).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState t lebWhile
    out.1 = none ∧
    M13.LocFrame s0 out.2 ∧
    ∃ tot_f : BitVec 64,
      out.2.locals.lookup (ofString "total") = some (.val (.word tot_f)) ∧
      tot_f.toNat = 16 + logsEncodedSum s0 pw.toNat nw.toNat := by
  have hhp_lim : globN s0 "heap_ptr" ≤ heapLimit := hA0.2.1
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  induction clk generalizing t iw totw with
  | zero =>
    dsimp only [lebWhile] at hnt ⊢
    rw [evaluateHOLFiniteState_while_total] at hnt ⊢
    have hcond : evalHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        (.cmp .less (ExpHOL.var VarKind.local (ofString "i"))
          (ExpHOL.var VarKind.local (ofString "n"))) =
        some (.val (.word (if iw.toNat < nw.toNat then 1#64 else 0#64))) := by
      rw [evalHOLFinite_eq_toExact]
      simp only [evalHOLExact, ht_i, ht_n, Compiler.Encoders.Asm.wordCmpHOL,
        holAsmSignedLess_small iw nw (by omega) (by omega), decide_eq_true_eq]
      by_cases hlt : iw.toNat < nw.toNat <;> simp [hlt]
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hlt : iw.toNat < nw.toNat
    · have hz : t.clock = 0 := by omega
      rw [if_pos hlt, if_pos (by decide : (1#64 : BitVec 64) ≠ 0), if_pos hz] at hnt
      exact absurd rfl hnt
    · rw [if_neg hlt]
      have hi_eq : iw.toNat = nw.toNat := by omega
      exact ⟨rfl, hlf, totw, ht_tot, by rw [← hi_eq]; exact htot_eq⟩
  | succ k ih =>
    dsimp only [lebWhile] at hnt ⊢
    rw [evaluateHOLFiniteState_while_total] at hnt ⊢
    have hcond : evalHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        (.cmp .less (ExpHOL.var VarKind.local (ofString "i"))
          (ExpHOL.var VarKind.local (ofString "n"))) =
        some (.val (.word (if iw.toNat < nw.toNat then 1#64 else 0#64))) := by
      rw [evalHOLFinite_eq_toExact]
      simp only [evalHOLExact, ht_i, ht_n, Compiler.Encoders.Asm.wordCmpHOL,
        holAsmSignedLess_small iw nw (by omega) (by omega), decide_eq_true_eq]
      by_cases hlt : iw.toNat < nw.toNat <;> simp [hlt]
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hlt : iw.toNat < nw.toNat
    · rw [if_pos hlt, if_pos (by decide : (1#64 : BitVec 64) ≠ 0)] at hnt ⊢
      by_cases hz : t.clock = 0
      · rw [if_pos hz] at hnt; exact absurd rfl hnt
      · rw [if_neg hz] at hnt ⊢
        rw [fixClockHOLFinite_evaluateState] at hnt ⊢
        let td := decClockHOLFinite t
        have hlf_td : M13.LocFrame s0 td := by
          unfold M13.LocFrame at hlf ⊢; change { t with clock := _ } = _; rw [hlf]; rfl
        have htd_ma : td.memaddrs = ordinaryDomain := by
          have : td.memaddrs = s0.memaddrs := by unfold M13.LocFrame at hlf_td; rw [hlf_td]
          rw [this]; exact hma0
        have htd_mem : td.memory = s0.memory := hlf_td.memory
        obtain ⟨hwa_i, hlog_hp, hnt_le, hdlen_lt, hwa16, hwa32⟩ := hentries iw.toNat hlt
        set logNat := memW s0 (pw.toNat + 8 * iw.toNat)
        have hmul8 : (iw * 8#64).toNat = 8 * iw.toNat := by
          rw [BitVec.toNat_mul]; change (iw.toNat * 8) % 2 ^ 64 = 8 * iw.toNat
          rw [Nat.mul_comm]; exact Nat.mod_eq_of_lt (by omega)
        have hp_add_nat : (pw + iw * 8#64).toNat = pw.toNat + 8 * iw.toNat := by
          rw [BitVec.toNat_add, hmul8]; exact Nat.mod_eq_of_lt (by omega)
        have hwa_i_td : WordAt td (pw + iw * 8#64).toNat := by
          rw [hp_add_nat]
          obtain ⟨w, hd, hm⟩ := hwa_i
          exact ⟨w, by rw [htd_ma, ← hma0]; exact hd, by rw [htd_mem]; exact hm⟩
        have hev_elem_addr : @evalHOLExact 64 F _ td.toExact (fun a => Classical.propDecidable (td.memaddrs a))
            (.op .add [ExpHOL.var VarKind.local (ofString "p"),
              .panop .mul [ExpHOL.var VarKind.local (ofString "i"), .const 8]]) =
            some (.val (.word (pw + iw * 8#64))) := by
          have hz_i8 : iw * 8#64 + 0 = iw * 8#64 := BitVec.add_zero _
          simp [evalHOLExact, evalListHOLExact, show td.locals = t.locals from rfl, ht_p, ht_i,
            wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord, hz_i8]
        have hev_log := mem_load_one_word td _ (pw + iw * 8#64) hev_elem_addr hwa_i_td
        have hmw_td : ∀ a, memW td a = memW s0 a := fun a => by unfold memW; rw [htd_mem]
        rw [hmw_td, hp_add_nat] at hev_log
        let logw := BitVec.ofNat 64 logNat
        have hlogw_nat : logw.toNat = logNat := by
          dsimp [logw]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
        dsimp only [lebBody] at hnt ⊢
        rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
        dsimp only at hnt ⊢; rw [hev_log] at hnt ⊢
        have hsh1 : shapeEqHOL .one (shapeOfHOLExact (.val (.word logw) : ValueHOL 64)) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        dsimp only at hnt ⊢; rw [if_pos hsh1] at hnt ⊢; dsimp only at hnt ⊢
        set s1 := setVarHOLFinite (ofString "log") (.val (.word logw)) td
        have hs1_ma : s1.memaddrs = ordinaryDomain := htd_ma
        have hs1_mem : s1.memory = s0.memory := htd_mem
        have hs1_log : s1.locals.lookup (ofString "log") = some (.val (.word logw)) := by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hs1_tot : s1.locals.lookup (ofString "total") = some (.val (.word totw)) := by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show td.locals = t.locals from rfl, ht_tot, show ofString "log" ≠ ofString "total" by decide]
        have hs1_i : s1.locals.lookup (ofString "i") = some (.val (.word iw)) := by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show td.locals = t.locals from rfl, ht_i, show ofString "log" ≠ ofString "i" by decide]
        have hlog16_nat : (logw + 16#64).toNat = logNat + 16 := by
          rw [BitVec.toNat_add, hlogw_nat]; change (logNat + 16) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
        have hlog32_nat : (logw + 32#64).toNat = logNat + 32 := by
          rw [BitVec.toNat_add, hlogw_nat]; change (logNat + 32) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
        have hwa16_s1 : WordAt s1 (logw + 16#64).toNat := by
          rw [hlog16_nat]; obtain ⟨w, hd, hm⟩ := hwa16
          exact ⟨w, by rw [hs1_ma, ← hma0]; exact hd, by rw [hs1_mem]; exact hm⟩
        have hwa32_s1 : WordAt s1 (logw + 32#64).toNat := by
          rw [hlog32_nat]; obtain ⟨w, hd, hm⟩ := hwa32
          exact ⟨w, by rw [hs1_ma, ← hma0]; exact hd, by rw [hs1_mem]; exact hm⟩
        have hev16 := mem_load_one_word s1
          (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 16]) (logw + 16#64)
          (by simp [evalHOLExact, evalListHOLExact, hs1_log, wordOpHOL, wordOp, valueIsWord, valueWord])
          hwa16_s1
        have hev32 := mem_load_one_word s1
          (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 32]) (logw + 32#64)
          (by simp [evalHOLExact, evalListHOLExact, hs1_log, wordOpHOL, wordOp, valueIsWord, valueWord])
          hwa32_s1
        have hmw_s1 : ∀ a, memW s1 a = memW s0 a := fun a => by unfold memW; rw [hs1_mem]
        rw [hmw_s1, hlog16_nat] at hev16
        rw [hmw_s1, hlog32_nat] at hev32
        let ntw := BitVec.ofNat 64 (memW s0 (logNat + 16))
        let dlenw := BitVec.ofNat 64 (memW s0 (logNat + 32))
        let totw' : BitVec 64 := totw + (64#64 + (ntw * 33#64 + (dlenw + 0#64)))
        have hev_mul : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
            (.panop .mul
              [.load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 16]),
               .const 33]) =
            some (.val (.word (ntw * 33#64))) := by
          unfold evalHOLExact
          unfold evalListHOLExact
          rw [hev16]
          have hc33 : @evalListHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
              [.const 33] = some [.val (.word 33#64)] := rfl
          rw [hc33]
          simp [panOpHOL, valueIsWord, valueWord, ntw]
        have hev_list : @evalListHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
            [ExpHOL.var VarKind.local (ofString "total"),
              .const 64,
              .panop .mul
                [.load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 16]),
                 .const 33],
              .load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 32])] =
            some [.val (.word totw), .val (.word 64#64), .val (.word (ntw * 33#64)), .val (.word dlenw)] := by
          have ht0 : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
              (ExpHOL.var VarKind.local (ofString "total")) = some (.val (.word totw)) := by
            simp [evalHOLExact, hs1_tot]
          have hc64 : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
              (.const 64) = some (.val (.word 64#64)) := rfl
          unfold evalListHOLExact
          rw [ht0]
          unfold evalListHOLExact
          rw [hc64]
          unfold evalListHOLExact
          rw [hev_mul]
          unfold evalListHOLExact
          rw [hev32]
          rfl
        have hev_rhs : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
            (.op .add [ExpHOL.var VarKind.local (ofString "total"),
              .const 64,
              .panop .mul
                [.load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 16]),
                 .const 33],
              .load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 32])]) =
            some (.val (.word totw')) := by
          unfold evalHOLExact
          rw [hev_list]
          simp [wordOpHOL, wordOp, valueIsWord, valueWord, totw']
        have hstep_bds : ∀ j < iw.toNat, memW s0 (memW s0 (pw.toNat + 8 * j) + 16) ≤ 4 ∧
            memW s0 (memW s0 (pw.toNat + 8 * j) + 32) < 2 ^ 32 := by
          intro j hj; obtain ⟨_, _, h1, h2, _, _⟩ := hentries j (by omega); exact ⟨h1, h2⟩
        have hsum_le := logsEncodedSum_bound s0 pw.toNat iw.toNat hstep_bds
        have hi_lt28 : iw.toNat < 2 ^ 28 := by omega
        have hntw_nat : ntw.toNat = memW s0 (logNat + 16) := by
          dsimp [ntw]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
        have hdlenw_nat : dlenw.toNat = memW s0 (logNat + 32) := by
          dsimp [dlenw]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
        have hnt33 : (ntw * 33#64).toNat = 33 * memW s0 (logNat + 16) := by
          rw [BitVec.toNat_mul, hntw_nat]; change (_ * 33) % 2 ^ 64 = _; rw [Nat.mul_comm]
          exact Nat.mod_eq_of_lt (by omega)
        have htot_bound : 16 + logsEncodedSum s0 pw.toNat iw.toNat + 64 +
            33 * memW s0 (logNat + 16) + memW s0 (logNat + 32) < 2 ^ 61 := by
          have : iw.toNat * (2 ^ 32 + 196) ≤ (2 ^ 28 - 1) * (2 ^ 32 + 196) :=
            Nat.mul_le_mul_right _ (by omega)
          omega
        have htotw'_nat : totw'.toNat = 16 + logsEncodedSum s0 pw.toNat (iw.toNat + 1) := by
          have hdz : dlenw + 0#64 = dlenw := BitVec.add_zero _
          have h1 : (ntw * 33#64 + (dlenw + 0#64)).toNat = 33 * memW s0 (logNat + 16) + memW s0 (logNat + 32) := by
            rw [hdz, BitVec.toNat_add, hnt33, hdlenw_nat]; exact Nat.mod_eq_of_lt (by omega)
          have h2 : (64#64 + (ntw * 33#64 + (dlenw + 0#64))).toNat =
              64 + 33 * memW s0 (logNat + 16) + memW s0 (logNat + 32) := by
            rw [BitVec.toNat_add, h1]; change (64 + _) % 2 ^ 64 = _
            rw [← Nat.add_assoc]; exact Nat.mod_eq_of_lt (by omega)
          dsimp only [totw', logsEncodedSum]
          rw [BitVec.toNat_add, htot_eq, h2]
          have h3 : 16 + logsEncodedSum s0 pw.toNat iw.toNat +
              (64 + 33 * memW s0 (logNat + 16) + memW s0 (logNat + 32)) =
              16 + (logsEncodedSum s0 pw.toNat iw.toNat + 64 +
                33 * memW s0 (logNat + 16) + memW s0 (logNat + 32)) := by omega
          rw [h3]
          exact Nat.mod_eq_of_lt (by omega)
        have hass_tot : evaluateHOLFiniteState s1
            (.assign VarKind.local (ofString "total")
              (.op .add [ExpHOL.var VarKind.local (ofString "total"),
                .const 64,
                .panop .mul
                  [.load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 16]),
                   .const 33],
                .load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 32])])) =
            (none, setVarHOLFinite (ofString "total") (.val (.word totw')) s1) := by
          rw [evaluateHOLFiniteState_assign]
          rw [hev_rhs]; dsimp only
          have hvv : isValidValueHOLFinite s1 VarKind.local (ofString "total") (.val (.word totw')) = true := by
            simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hs1_tot, shapeOfHOLExact, shapeEqHOL]
          rw [if_pos hvv]; rfl
        set s2 := setVarHOLFinite (ofString "total") (.val (.word totw')) s1
        have hs2_i : s2.locals.lookup (ofString "i") = some (.val (.word iw)) := by
          simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_i,
            show ofString "total" ≠ ofString "i" by decide]
        let iw' : BitVec 64 := iw + 1#64
        have hiw'_nat : iw'.toNat = iw.toNat + 1 := by
          change (iw + 1#64).toNat = iw.toNat + 1
          rw [BitVec.toNat_add]; change (iw.toNat + 1) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
        have hass_i : evaluateHOLFiniteState s2
            (.assign VarKind.local (ofString "i")
              (.op .add [ExpHOL.var VarKind.local (ofString "i"), .const 1])) =
            (none, setVarHOLFinite (ofString "i") (.val (.word iw')) s2) := by
          rw [evaluateHOLFiniteState_assign]
          have hev_i : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
              (.op .add [ExpHOL.var VarKind.local (ofString "i"), .const 1]) =
              some (.val (.word iw')) := by
            simp [evalHOLExact, evalListHOLExact, hs2_i, wordOpHOL, wordOp, valueIsWord, valueWord, iw']
          rw [hev_i]; dsimp only
          have hvv : isValidValueHOLFinite s2 VarKind.local (ofString "i") (.val (.word iw')) = true := by
            simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hs2_i, shapeOfHOLExact, shapeEqHOL]
          rw [if_pos hvv]; rfl
        rw [evaluateHOLFiniteState_seq_line780, hass_tot] at hnt ⊢; dsimp only at hnt ⊢
        rw [hass_i] at hnt ⊢; dsimp only at hnt ⊢
        set mid : PanSemStateFiniteExact 64 F :=
          { (setVarHOLFinite (ofString "i") (.val (.word iw')) s2) with
            locals := HolFiniteMapExact.resVarEq
              (setVarHOLFinite (ofString "i") (.val (.word iw')) s2).locals
              (ofString "log", td.locals.lookup (ofString "log")) }
        have hmid_clk : mid.clock ≤ k := by change t.clock - 1 ≤ k; omega
        have hlf_mid : M13.LocFrame s0 mid :=
          (((hlf_td.setVar _ _).setVar _ _).setVar _ _).locals _
        have hlr : ∀ (m : HolFiniteMapExact MlS (ValueHOL 64)) (v : MlS) (old : Option (ValueHOL 64)) (x : MlS),
            x ≠ v → (m.resVarEq (v, old)).lookup x = m.lookup x := by
          intro m v old x hne
          simp only [HolFiniteMapExact.resVarEq]
          cases old <;> simp [FDOMSUB_HOL, FUPDATE_HOL, hne, Ne.symm hne]
        have hmid_n : mid.locals.lookup (ofString "n") = some (.val (.word nw)) := by
          simp only [mid, hlr _ _ _ _ (show ofString "n" ≠ ofString "log" by decide),
            s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show (ofString "i" == ofString "n") = false by decide,
            show (ofString "total" == ofString "n") = false by decide,
            show (ofString "log" == ofString "n") = false by decide,
            Bool.false_eq_true, ↓reduceIte]
          exact ht_n
        have hmid_p : mid.locals.lookup (ofString "p") = some (.val (.word pw)) := by
          simp only [mid, hlr _ _ _ _ (show ofString "p" ≠ ofString "log" by decide),
            s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show (ofString "i" == ofString "p") = false by decide,
            show (ofString "total" == ofString "p") = false by decide,
            show (ofString "log" == ofString "p") = false by decide,
            Bool.false_eq_true, ↓reduceIte]
          exact ht_p
        have hmid_i : mid.locals.lookup (ofString "i") = some (.val (.word iw')) := by
          simp only [mid, hlr _ _ _ _ (show ofString "i" ≠ ofString "log" by decide),
            setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show (ofString "i" == ofString "i") = true by decide, ↓reduceIte]
        have hmid_tot : mid.locals.lookup (ofString "total") = some (.val (.word totw')) := by
          simp only [mid, hlr _ _ _ _ (show ofString "total" ≠ ofString "log" by decide),
            s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show (ofString "i" == ofString "total") = false by decide,
            show (ofString "total" == ofString "total") = true by decide,
            Bool.false_eq_true, ↓reduceIte]
        exact ih mid iw' totw' hmid_clk hlf_mid (by rw [hiw'_nat]; omega)
          (by rw [hiw'_nat]; exact htotw'_nat) hmid_n hmid_p hmid_i hmid_tot hnt
    · rw [if_neg hlt]
      have hi_eq : iw.toNat = nw.toNat := by omega
      exact ⟨rfl, hlf, totw, ht_tot, by rw [← hi_eq]; exact htot_eq⟩

private theorem eval_decCall_logs_encoded_bound {F : Type}
    (s : PanSemStateFiniteExact 64 F) (logs0 : BitVec 64) (cont : ProgHOL 64)
    (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hlogs : s.locals.lookup (ofString "logs") = some (.val (.word logs0)))
    (hLL : LogsListOK s logs0.toNat)
    (hDF : LogsDisjFixed s logs0.toNat)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString "bound") .one (ofString "logs_encoded_bound")
        [ExpHOL.var VarKind.local (ofString "logs")] cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString "bound") .one (ofString "logs_encoded_bound")
        [ExpHOL.var VarKind.local (ofString "logs")] cont)).1) :
    logs0.toNat ≠ 0 ∧
    ∃ (boundw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      boundw.toNat = 16 + logsEncodedSum s (memW s logs0.toNat) (memW s (logs0.toNat + 8)) ∧
      boundw.toNat + 400 < 2 ^ 61 ∧
      mid.globals = s.globals ∧
      mid.memory = s.memory ∧
      mid.locals = s.locals.update (ofString "bound", .val (.word boundw)) ∧
      HeapByteEff s mid Rl gw ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      evaluateHOLFiniteState s
        (.decCall (ofString "bound") .one (ofString "logs_encoded_bound")
          [ExpHOL.var VarKind.local (ofString "logs")] cont) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString "bound", s.locals.lookup (ofString "bound")) }) := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [ExpHOL.var VarKind.local (ofString "logs")] = some [.val (.word logs0)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hlogs]
  have hlk := pan_one_word_lookup s.code.lookup (ofString "logs_encoded_bound")
    (ofString "logs") (sourceFnBody Guest.Software.guestFn_logs_encoded_bound) logs0
    (by rw [hcode]; exact lookup_logs_encoded_bound)
  simp only [ha, hlk] at hnt hres ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt hres ⊢
    set cmap := HolFiniteMapExact.empty.update (ofString "logs", ValueHOL.val (.word logs0))
    set ent := callEntryStateHOLFinite s cmap
    have hent_logs : ent.locals.lookup (ofString "logs") = some (.val (.word logs0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hlf_ent : M13.LocFrame s ent := rfl
    have hent_ma : ent.memaddrs = ordinaryDomain := hAR.1.memaddrs
    have hb_leb : sourceFnBody Guest.Software.guestFn_logs_encoded_bound =
        .dec (ofString "n") .one
          (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "logs"), .const 8]))
          (.dec (ofString "p") .one
            (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "logs"), .const 0]))
            (.dec (ofString "total") .one (.const 16)
              (.dec (ofString "i") .one (.const 0)
                (.seq lebWhile
                  (.return (ExpHOL.var VarKind.local (ofString "total"))))))) := rfl
    by_cases hlz : logs0.toNat = 0
    · exfalso
      have hl0_eq : logs0 = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hlz)
      subst hl0_eq
      have hndom8 : ¬ ent.memaddrs 8#64 := by
        rw [hent_ma, ordinaryDomain_iff]; rw [sourceBase_val]; decide
      have hev_fail : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
          (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "logs"), .const 8])) = none := by
        simp [evalHOLExact, evalListHOLExact, hent_logs, wordOpHOL, wordOp, valueIsWord, valueWord,
          memLoadHOLExact, hndom8]
      have hbody_err : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_logs_encoded_bound)).1 =
          some .error := by
        rw [hb_leb, evaluateHOLFiniteState_dec_total]; dsimp only; rw [hev_fail]
      rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_logs_encoded_bound) with ⟨rb, sb⟩
      rw [hrun] at hbody_err hres
      dsimp only at hbody_err; subst hbody_err
      exact not_resumes_error hres
    · refine ⟨hlz, ?_⟩
      obtain ⟨_, _, _, hhdr_b, harr_b, hn_lt, hw0, hw8, hentries⟩ :=
        logsListOK_parts hAR.2 hlz hLL hDF
      have hl8_nat : (logs0 + 8#64).toNat = logs0.toNat + 8 := by
        rw [BitVec.toNat_add]; change (logs0.toNat + 8) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
      have hl0_nat : (logs0 + 0#64).toNat = logs0.toNat := by simp
      have hnt_ent : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_logs_encoded_bound)).1 ≠
          some .timeOut := by
        rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_logs_encoded_bound) with ⟨rb, sb⟩
        rintro rfl; rw [hrun] at hnt; exact hnt rfl
      have hev_n := mem_load_one_word ent
        (.op .add [ExpHOL.var VarKind.local (ofString "logs"), .const 8]) (logs0 + 8#64)
        (by simp [evalHOLExact, evalListHOLExact, hent_logs, wordOpHOL, wordOp, valueIsWord, valueWord])
        (by rw [hl8_nat]; exact hw8)
      have hmw_ent : ∀ a, memW ent a = memW s a := fun _ => rfl
      rw [hl8_nat, hmw_ent] at hev_n
      let nw := BitVec.ofNat 64 (memW s (logs0.toNat + 8))
      have hnw_nat : nw.toNat = memW s (logs0.toNat + 8) := by
        dsimp [nw]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      set e1 := setVarHOLFinite (ofString "n") (.val (.word nw)) ent
      have he1_logs : e1.locals.lookup (ofString "logs") = some (.val (.word logs0)) := by
        simp [e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_logs,
          show ofString "n" ≠ ofString "logs" by decide]
      have hev_p := mem_load_one_word e1
        (.op .add [ExpHOL.var VarKind.local (ofString "logs"), .const 0]) (logs0 + 0#64)
        (by simp [evalHOLExact, evalListHOLExact, he1_logs, wordOpHOL, wordOp, valueIsWord, valueWord])
        (by rw [hl0_nat]; exact hw0)
      have hmw_e1 : ∀ a, memW e1 a = memW s a := fun _ => rfl
      rw [hl0_nat, hmw_e1] at hev_p
      have hp_lt_264 : memW s logs0.toNat < 2 ^ 64 := by
        unfold memW; cases s.memory (BitVec.ofNat 64 logs0.toNat); exact BitVec.isLt _
      let pw := BitVec.ofNat 64 (memW s logs0.toNat)
      have hpw_nat : pw.toNat = memW s logs0.toNat := by
        dsimp [pw]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hp_lt_264
      set e2 := setVarHOLFinite (ofString "p") (.val (.word pw)) e1
      set e3 := setVarHOLFinite (ofString "total") (.val (.word 16#64)) e2
      set e4 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) e3
      have hstep_dec : ∀ (q : ProgHOL 64),
          evaluateHOLFiniteState ent
            (.dec (ofString "n") .one
              (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "logs"), .const 8]))
              (.dec (ofString "p") .one
                (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "logs"), .const 0]))
                (.dec (ofString "total") .one (.const 16)
                  (.dec (ofString "i") .one (.const 0) q)))) =
          (let o := evaluateHOLFiniteState e4 q
           (o.1,
            { o.2 with
              locals := HolFiniteMapExact.resVarEq
                (HolFiniteMapExact.resVarEq
                  (HolFiniteMapExact.resVarEq
                    (HolFiniteMapExact.resVarEq o.2.locals (ofString "i", e3.locals.lookup (ofString "i")))
                    (ofString "total", e2.locals.lookup (ofString "total")))
                  (ofString "p", e1.locals.lookup (ofString "p")))
                (ofString "n", ent.locals.lookup (ofString "n")) })) := by
        intro q
        have hstep1 : evaluateHOLFiniteState ent
            (.dec (ofString "n") .one
              (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "logs"), .const 8]))
              (.dec (ofString "p") .one
                (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "logs"), .const 0]))
                (.dec (ofString "total") .one (.const 16)
                  (.dec (ofString "i") .one (.const 0) q)))) =
          (let o1 := evaluateHOLFiniteState e1
            (.dec (ofString "p") .one
              (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "logs"), .const 0]))
              (.dec (ofString "total") .one (.const 16)
                (.dec (ofString "i") .one (.const 0) q)))
           (o1.1, { o1.2 with locals := HolFiniteMapExact.resVarEq o1.2.locals (ofString "n", ent.locals.lookup (ofString "n")) })) := by
          rw [evaluateHOLFiniteState_dec_total]
          simp only [hev_n, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]; rfl
        have hstep2 : evaluateHOLFiniteState e1
            (.dec (ofString "p") .one
              (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "logs"), .const 0]))
              (.dec (ofString "total") .one (.const 16)
                (.dec (ofString "i") .one (.const 0) q))) =
          (let o2 := evaluateHOLFiniteState e2
            (.dec (ofString "total") .one (.const 16)
              (.dec (ofString "i") .one (.const 0) q))
           (o2.1, { o2.2 with locals := HolFiniteMapExact.resVarEq o2.2.locals (ofString "p", e1.locals.lookup (ofString "p")) })) := by
          rw [evaluateHOLFiniteState_dec_total]
          simp only [hev_p, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]; rfl
        have hstep3 : evaluateHOLFiniteState e2
            (.dec (ofString "total") .one (.const 16)
              (.dec (ofString "i") .one (.const 0) q)) =
          (let o3 := evaluateHOLFiniteState e3 (.dec (ofString "i") .one (.const 0) q)
           (o3.1, { o3.2 with locals := HolFiniteMapExact.resVarEq o3.2.locals (ofString "total", e2.locals.lookup (ofString "total")) })) := by
          rw [evaluateHOLFiniteState_dec_total]
          simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]; rfl
        have hstep4 : evaluateHOLFiniteState e3 (.dec (ofString "i") .one (.const 0) q) =
          (let o4 := evaluateHOLFiniteState e4 q
           (o4.1, { o4.2 with locals := HolFiniteMapExact.resVarEq o4.2.locals (ofString "i", e3.locals.lookup (ofString "i")) })) := by
          rw [evaluateHOLFiniteState_dec_total]
          simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]; rfl
        rw [hstep1, hstep2, hstep3, hstep4]
      rw [hb_leb, hstep_dec] at hnt_ent
      dsimp only at hnt_ent
      rw [evaluateHOLFiniteState_seq_line780] at hnt_ent
      have hnt_w : (evaluateHOLFiniteState e4 lebWhile).1 ≠ some .timeOut := by
        rcases hw : evaluateHOLFiniteState e4 lebWhile with ⟨rw0, sw0⟩
        rintro rfl; rw [hw] at hnt_ent; exact hnt_ent rfl
      have he4_n : e4.locals.lookup (ofString "n") = some (.val (.word nw)) := by
        simp [e4, e3, e2, e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "n" by decide,
          show ofString "total" ≠ ofString "n" by decide,
          show ofString "p" ≠ ofString "n" by decide]
      have he4_p : e4.locals.lookup (ofString "p") = some (.val (.word pw)) := by
        simp [e4, e3, e2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "p" by decide,
          show ofString "total" ≠ ofString "p" by decide]
      have he4_i : e4.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
        simp [e4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have he4_tot : e4.locals.lookup (ofString "total") = some (.val (.word 16#64)) := by
        simp [e4, e3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "total" by decide]
      have hlf_e4 : M13.LocFrame s e4 := by cases s; rfl
      obtain ⟨hw_none, hlf_sw, boundw, hsw_tot, hbound_eq⟩ :=
        lebWhile_exact e4.clock s e4 nw pw 0#64 16#64 le_rfl hlf_e4 hAR.2 hAR.1.memaddrs
          (by rw [hnw_nat]; exact hn_lt)
          (by rw [hpw_nat, hnw_nat]; exact harr_b)
          (by simp)
          (by simp [logsEncodedSum])
          he4_n he4_p he4_i he4_tot
          (fun k hk => by
            rw [hnw_nat] at hk
            rw [hpw_nat]
            obtain ⟨hwa_k, hle_k, hhp_k, _, _, h16_k, _, h32_k⟩ := hentries k hk
            exact ⟨hwa_k, hhp_k, hle_k.2.2.1, hle_k.2.2.2.1, h16_k, h32_k⟩)
          hnt_w
      rcases hweq : evaluateHOLFiniteState e4 lebWhile with ⟨rw_res, sw⟩
      rw [hweq] at hw_none hlf_sw hsw_tot
      dsimp only at hw_none hlf_sw hsw_tot; subst hw_none
      have hret_sw : evaluateHOLFiniteState sw (.return (ExpHOL.var VarKind.local (ofString "total"))) =
          (some (.returned (.val (.word boundw))), sw.emptyLocalsHOLFinite) := by
        rw [evaluateHOLFiniteState_return]
        have hev_t : @evalHOLExact 64 F _ sw.toExact (fun a => Classical.propDecidable (sw.memaddrs a))
            (ExpHOL.var VarKind.local (ofString "total")) = some (.val (.word boundw)) := by
          simp [evalHOLExact, hsw_tot]
        rw [hev_t]; dsimp only
        rw [if_pos (by simp [shapeOfHOLExact] : sizeOfShapeWithContextHOL sw.structs (shapeOfHOLExact (.val (.word boundw) : ValueHOL 64)) ≤ 32)]
      set sb_out : PanSemStateFiniteExact 64 F :=
        { sw.emptyLocalsHOLFinite with
          locals := HolFiniteMapExact.resVarEq
            (HolFiniteMapExact.resVarEq
              (HolFiniteMapExact.resVarEq
                (HolFiniteMapExact.resVarEq sw.emptyLocalsHOLFinite.locals (ofString "i", e3.locals.lookup (ofString "i")))
                (ofString "total", e2.locals.lookup (ofString "total")))
              (ofString "p", e1.locals.lookup (ofString "p")))
            (ofString "n", ent.locals.lookup (ofString "n")) }
      have hbody_eq : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_logs_encoded_bound) =
          (some (.returned (.val (.word boundw))), sb_out) := by
        rw [hb_leb, hstep_dec, evaluateHOLFiniteState_seq_line780, hweq]; dsimp only
        rw [hret_sw]
      have hsh_b : (shapeEqHOL (shapeOfHOLExact (.val (.word boundw) : ValueHOL 64)) .one &&
          shapeEqHOL (shapeOfHOLExact (.val (.word boundw) : ValueHOL 64)) .one) = true := by
        simp [shapeOfHOLExact, shapeEqHOL]
      simp only [hbody_eq, hsh_b, ↓reduceIte] at hnt hres ⊢
      let mid : PanSemStateFiniteExact 64 F :=
        setVarHOLFinite (ofString "bound") (.val (.word boundw)) { sb_out with locals := s.locals }
      have hlf_mid : M13.LocFrame s mid :=
        (((hlf_sw.emptyLocals).locals _).locals _).setVar _ _
      have hstep_all : ∀ j < memW s (logs0.toNat + 8),
          memW s (memW s (memW s logs0.toNat + 8 * j) + 16) ≤ 4 ∧
          memW s (memW s (memW s logs0.toNat + 8 * j) + 32) < 2 ^ 32 := by
        intro j hj; obtain ⟨_, hle_j, _⟩ := hentries j hj; exact ⟨hle_j.2.2.1, hle_j.2.2.2.1⟩
      have hsum_all := logsEncodedSum_bound s (memW s logs0.toNat) (memW s (logs0.toNat + 8)) hstep_all
      rw [hpw_nat, hnw_nat] at hbound_eq
      have hbound400 : boundw.toNat + 400 < 2 ^ 61 := by
        have : memW s (logs0.toNat + 8) * (2 ^ 32 + 196) ≤ (2 ^ 28 - 1) * (2 ^ 32 + 196) :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      refine ⟨boundw, mid, hbound_eq, hbound400, hlf_mid.globals, hlf_mid.memory, rfl,
        HeapByteEff.of_locFrame hAR hlf_mid Rl gw, hnt, hres, rfl⟩

/-! ## Section 5: `encode_logs` -/

private theorem call_noexc_ne_returned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (rk : Option (VarKind × MlS)) (fname : MlS) (args : List (ExpHOL 64)) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s (.call (some (rk, none)) fname args)).1 ≠ some (.returned v) := by
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
          cases rb' with
          | returned _ =>
            cases rk with
            | none => dsimp only; split <;> simp
            | some kv =>
              dsimp only
              split
              · split <;> simp
              · simp
          | _ => simp

private theorem call_noexc_ne_break_continue {F : Type} (s : PanSemStateFiniteExact 64 F)
    (rk : Option (VarKind × MlS)) (fname : MlS) (args : List (ExpHOL 64)) :
    (evaluateHOLFiniteState s (.call (some (rk, none)) fname args)).1 ≠ some .break ∧
    (evaluateHOLFiniteState s (.call (some (rk, none)) fname args)).1 ≠ some .continue := by
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
          cases rb' with
          | returned _ =>
            cases rk with
            | none => dsimp only; split <;> simp
            | some kv =>
              dsimp only
              split
              · split <;> simp
              · simp
          | _ => simp

private theorem decCall_no_break_continue {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : MlS) (sh : ShapeHOL) (fname : MlS) (args : List (ExpHOL 64)) (cont : ProgHOL 64)
    (hc : ∀ m : PanSemStateFiniteExact 64 F,
      (evaluateHOLFiniteState m cont).1 ≠ some .break ∧
      (evaluateHOLFiniteState m cont).1 ≠ some .continue) :
    (evaluateHOLFiniteState s (.decCall v sh fname args cont)).1 ≠ some .break ∧
    (evaluateHOLFiniteState s (.decCall v sh fname args cont)).1 ≠ some .continue := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
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
          cases rb' with
          | returned _ =>
            dsimp only
            split
            · exact hc _
            · simp
          | _ => simp

private theorem while_no_break_continue {F : Type} (s : PanSemStateFiniteExact 64 F)
    (cond : ExpHOL 64) (body : ProgHOL 64) :
    (evaluateHOLFiniteState s (.while cond body)).1 ≠ some .break ∧
    (evaluateHOLFiniteState s (.while cond body)).1 ≠ some .continue := by
  have h : ∀ (k : Nat) (u : PanSemStateFiniteExact 64 F), u.clock = k →
      (evaluateHOLFiniteState u (.while cond body)).1 ≠ some .break ∧
      (evaluateHOLFiniteState u (.while cond body)).1 ≠ some .continue := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro u hclk
      rw [evaluateHOLFiniteState_while_fixClockRewrite]
      split
      · dsimp only
        split
        · split
          · simp
          · have hb_clk := evaluateHOLFiniteState_clock_le (decClockHOLFinite u) body
            have hd_clk : (decClockHOLFinite u).clock < k := by
              simp [decClockHOLFinite, hclk]; omega
            rcases hbo : evaluateHOLFiniteState (decClockHOLFinite u) body with ⟨rb, sb⟩
            simp only [hbo] at hb_clk ⊢
            cases rb with
            | none => exact ih sb.clock (lt_of_le_of_lt hb_clk hd_clk) sb rfl
            | some r =>
              cases r with
              | «continue» => exact ih sb.clock (lt_of_le_of_lt hb_clk hd_clk) sb rfl
              | «break» => simp
              | _ => simp
        · simp
      · simp
  exact h s.clock s rfl

private def elInnerBody : ProgHOL 64 :=
  .seq
    (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
      [ExpHOL.var VarKind.local (ofString "t"),
       .op .add
         [.load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 8]),
          .panop .mul [ExpHOL.var VarKind.local (ofString "j"), .const 32]],
       .const 32])
    (.seq
      (.assign VarKind.local (ofString "t")
        (.op .add [ExpHOL.var VarKind.local (ofString "t"), ExpHOL.var VarKind.local (ofString "w")]))
      (.assign VarKind.local (ofString "j")
        (.op .add [ExpHOL.var VarKind.local (ofString "j"), .const 1])))

private def elInnerWhile : ProgHOL 64 :=
  .while (.cmp .less (ExpHOL.var VarKind.local (ofString "j")) (ExpHOL.var VarKind.local (ofString "nt")))
    elInnerBody

private def elOuterBody : ProgHOL 64 :=
  .dec (ofString "log") .one
    (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "p"),
      .panop .mul [ExpHOL.var VarKind.local (ofString "i"), .const 8]]))
    (.dec (ofString "r") .one (.op .add [ExpHOL.var VarKind.local (ofString "q"), .const 9])
      (.decCall (ofString "w") .one (ofString "rlp_encode_bytes")
        [ExpHOL.var VarKind.local (ofString "r"),
         .load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 0]),
         .const 20]
        (.seq
          (.assign VarKind.local (ofString "r")
            (.op .add [ExpHOL.var VarKind.local (ofString "r"), ExpHOL.var VarKind.local (ofString "w")]))
          (.dec (ofString "tstart") .one (ExpHOL.var VarKind.local (ofString "r"))
            (.dec (ofString "t") .one (.op .add [ExpHOL.var VarKind.local (ofString "r"), .const 9])
              (.dec (ofString "nt") .one (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 16]))
                (.dec (ofString "j") .one (.const 0)
                  (.seq elInnerWhile
                    (.seq
                      (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_finish_list")
                        [ExpHOL.var VarKind.local (ofString "tstart"), ExpHOL.var VarKind.local (ofString "t")])
                      (.seq
                        (.assign VarKind.local (ofString "r")
                          (.op .add [ExpHOL.var VarKind.local (ofString "tstart"), ExpHOL.var VarKind.local (ofString "w")]))
                        (.seq
                          (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
                            [ExpHOL.var VarKind.local (ofString "r"),
                             .load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 24]),
                             .load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 32])])
                          (.seq
                            (.assign VarKind.local (ofString "r")
                              (.op .add [ExpHOL.var VarKind.local (ofString "r"), ExpHOL.var VarKind.local (ofString "w")]))
                            (.seq
                              (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_finish_list")
                                [ExpHOL.var VarKind.local (ofString "q"), ExpHOL.var VarKind.local (ofString "r")])
                              (.seq
                                (.assign VarKind.local (ofString "q")
                                  (.op .add [ExpHOL.var VarKind.local (ofString "q"), ExpHOL.var VarKind.local (ofString "w")]))
                                (.assign VarKind.local (ofString "i")
                                  (.op .add [ExpHOL.var VarKind.local (ofString "i"), .const 1]))))))))))))))))

private def elOuterWhile : ProgHOL 64 :=
  .while (.cmp .less (ExpHOL.var VarKind.local (ofString "i")) (ExpHOL.var VarKind.local (ofString "n")))
    elOuterBody

private theorem mem_eq_of_allocated_fresh_ivl {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} {dst0 bound : Nat}
    (hA0 : ArenaOK s0) (hma0 : s0.memaddrs = ordinaryDomain)
    (heff : HeapByteEff s0 cur [(dst0, bound)] ["heap_ptr"])
    (hdst_ge : globN s0 "heap_ptr" ≤ dst0) (hdst_hi : dst0 + bound ≤ heapLimit)
    {iv : Ivl} (hal : Allocated s0 iv)
    {a : Nat} (ha1 : iv.1 ≤ a) (ha2 : a + 8 ≤ iv.1 + iv.2) :
    cur.memory (BitVec.ofNat 64 a) = s0.memory (BitVec.ofNat 64 a) := by
  have hib : iv.1 + iv.2 ≤ 2 ^ 64 := M13.allocated_le_2pow64 hA0 hal
  have ha64 : a < 2 ^ 64 := by omega
  have hbit : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha64
  by_cases hdom : ordinaryDomain (BitVec.ofNat 64 a)
  · apply mem_eq_of_bytes_eq heff.be _ hdom
    intro k hk
    rw [hbit]
    by_contra hne
    have hin : InIvl (a + k) iv := ⟨by omega, by omega⟩
    have hnfree := allocated_not_in_free hA0 (Or.inr hal) hin
    rcases heff.byte_frame (a + k) (by omega) hne with ⟨x, hx, hbx⟩ | hfg | hhf
    · simp only [List.mem_singleton] at hx; subst hx
      obtain ⟨hb1, hb2⟩ := hbx
      exact hnfree.2 ⟨by dsimp [heapFree]; omega, by dsimp [heapFree]; omega⟩
    · exact hnfree.1 hfg
    · exact hnfree.2 hhf
  · by_contra hne
    exact hdom (hma0 ▸ heff.out_dom _ hne)

private theorem load_word_in_allocated_fresh {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} {dst0 bound : Nat}
    (hA0 : ArenaOK s0) (hma0 : s0.memaddrs = ordinaryDomain)
    (heff : HeapByteEff s0 cur [(dst0, bound)] ["heap_ptr"])
    (hdst_ge : globN s0 "heap_ptr" ≤ dst0) (hdst_hi : dst0 + bound ≤ heapLimit)
    {iv : Ivl} (hal : Allocated s0 iv)
    (addrExp : ExpHOL 64) (addr : BitVec 64)
    (haddr : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) addrExp =
      some (.val (.word addr)))
    (hwa0 : WordAt s0 addr.toNat)
    (ha1 : iv.1 ≤ addr.toNat) (ha2 : addr.toNat + 8 ≤ iv.1 + iv.2) :
    @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) (.load .one addrExp) =
      some (.val (.word (BitVec.ofNat 64 (memW s0 addr.toNat)))) := by
  have hm_eq := mem_eq_of_allocated_fresh_ivl hA0 hma0 heff hdst_ge hdst_hi hal ha1 ha2
  have hwa_cur : WordAt cur addr.toNat := wordAt_post_of_s heff.memaddrs hwa0
  have hload := mem_load_one_word cur addrExp addr haddr hwa_cur
  have hmw : memW cur addr.toNat = memW s0 addr.toNat := by unfold memW; rw [hm_eq]
  rw [hmw] at hload
  exact hload

private theorem elInnerWhile_exact {F : Type} (clk : Nat)
    (s0 s : PanSemStateFiniteExact 64 F)
    (dst0 bound : Nat)
    (logw tsw tw ntw jw : BitVec 64)
    (hl_r : ∃ rw : BitVec 64, s.locals.lookup (ofString "r") = some (.val (.word rw)))
    (dqw iw nw pw dstw : BitVec 64)
    (hclk : s.clock ≤ clk)
    (hA0 : ArenaOK s0) (hma0 : s0.memaddrs = ordinaryDomain)
    (heff0 : HeapByteEff s0 s [(dst0, bound)] ["heap_ptr"])
    (hdst_ge : globN s0 "heap_ptr" ≤ dst0) (hdst_hi : dst0 + bound ≤ heapLimit)
    (hhl_lt : heapLimit < 2 ^ 64)
    (hnt_le4 : ntw.toNat ≤ 4)
    (hj_le : jw.toNat ≤ ntw.toNat)
    (ht_ge : tsw.toNat + 9 ≤ tw.toNat)
    (ht_le : tw.toNat ≤ tsw.toNat + 9 + 33 * jw.toNat)
    (ht_fit : tsw.toNat + 9 + 33 * ntw.toNat ≤ dst0 + bound)
    (hdst_lo : dst0 ≤ tsw.toNat)
    (hal_log : Allocated s0 (logw.toNat, 40))
    (hwa_log8 : WordAt s0 (logw.toNat + 8))
    (hl_log : s.locals.lookup (ofString "log") = some (.val (.word logw)))
    (hl_ts : s.locals.lookup (ofString "tstart") = some (.val (.word tsw)))
    (hl_t : s.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hl_nt : s.locals.lookup (ofString "nt") = some (.val (.word ntw)))
    (hl_j : s.locals.lookup (ofString "j") = some (.val (.word jw)))
    (hl_w : ∃ ww : BitVec 64, s.locals.lookup (ofString "w") = some (.val (.word ww)))
    (hl_q : s.locals.lookup (ofString "q") = some (.val (.word dqw)))
    (hl_i : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hl_n : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hl_p : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hl_dst : s.locals.lookup (ofString "dst") = some (.val (.word dstw)))
    (hnt : (evaluateHOLFiniteState s elInnerWhile).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s elInnerWhile
    (out.1 = none →
      ∃ tf : BitVec 64,
        tsw.toNat + 9 ≤ tf.toNat ∧
        tf.toNat ≤ tsw.toNat + 9 + 33 * ntw.toNat ∧
        HeapByteEff s out.2 [(dst0, bound)] [] ∧
        out.2.locals.lookup (ofString "log") = some (.val (.word logw)) ∧
        out.2.locals.lookup (ofString "tstart") = some (.val (.word tsw)) ∧
        out.2.locals.lookup (ofString "t") = some (.val (.word tf)) ∧
        out.2.locals.lookup (ofString "nt") = some (.val (.word ntw)) ∧
        (∃ ww : BitVec 64, out.2.locals.lookup (ofString "w") = some (.val (.word ww))) ∧
        (∃ rw : BitVec 64, out.2.locals.lookup (ofString "r") = some (.val (.word rw))) ∧
        out.2.locals.lookup (ofString "q") = some (.val (.word dqw)) ∧
        out.2.locals.lookup (ofString "i") = some (.val (.word iw)) ∧
        out.2.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
        out.2.locals.lookup (ofString "p") = some (.val (.word pw)) ∧
        out.2.locals.lookup (ofString "dst") = some (.val (.word dstw))) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  induction clk generalizing s tw jw with
  | zero =>
    intro out; dsimp only [out, elInnerWhile] at hnt ⊢
    rw [evaluateHOLFiniteState_while_total] at hnt ⊢
    have hcond : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .less (ExpHOL.var VarKind.local (ofString "j")) (ExpHOL.var VarKind.local (ofString "nt"))) =
        some (.val (.word (if jw.toNat < ntw.toNat then 1#64 else 0#64))) := by
      rw [evalHOLFinite_eq_toExact]
      simp only [evalHOLExact, hl_j, hl_nt, Compiler.Encoders.Asm.wordCmpHOL,
        holAsmSignedLess_small jw ntw (by omega) (by omega), decide_eq_true_eq]
      by_cases hlt : jw.toNat < ntw.toNat <;> simp [hlt]
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hlt : jw.toNat < ntw.toNat
    · have hz : s.clock = 0 := by omega
      rw [if_pos hlt, if_pos (by decide : (1#64 : BitVec 64) ≠ 0), if_pos hz] at hnt
      exact absurd rfl hnt
    · rw [if_neg hlt, if_neg (by decide : ¬ ((0#64 : BitVec 64) ≠ 0))]
      have hjeq : jw.toNat = ntw.toNat := by omega
      exact ⟨fun _ => ⟨tw, ht_ge, by rw [← hjeq]; exact ht_le, HeapByteEff.refl heff0.arena _ _,
        hl_log, hl_ts, hl_t, hl_nt, hl_w, hl_r, hl_q, hl_i, hl_n, hl_p, hl_dst⟩,
        fun h => False.elim (h rfl)⟩
  | succ k ih =>
    intro out; dsimp only [out, elInnerWhile] at hnt ⊢
    rw [evaluateHOLFiniteState_while_total] at hnt ⊢
    have hcond : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .less (ExpHOL.var VarKind.local (ofString "j")) (ExpHOL.var VarKind.local (ofString "nt"))) =
        some (.val (.word (if jw.toNat < ntw.toNat then 1#64 else 0#64))) := by
      rw [evalHOLFinite_eq_toExact]
      simp only [evalHOLExact, hl_j, hl_nt, Compiler.Encoders.Asm.wordCmpHOL,
        holAsmSignedLess_small jw ntw (by omega) (by omega), decide_eq_true_eq]
      by_cases hlt : jw.toNat < ntw.toNat <;> simp [hlt]
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hlt : jw.toNat < ntw.toNat
    · rw [if_pos hlt, if_pos (by decide : (1#64 : BitVec 64) ≠ 0)] at hnt ⊢
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hnt; exact absurd rfl hnt
      · rw [if_neg hz] at hnt ⊢
        rw [fixClockHOLFinite_evaluateState] at hnt ⊢
        let sd := decClockHOLFinite s
        have heff_s_sd : HeapByteEff s sd [(dst0, bound)] [] :=
          (HeapByteEff.refl heff0.arena _ _).locals_clock sd.locals sd.clock
        have heff0_sd : HeapByteEff s0 sd [(dst0, bound)] ["heap_ptr"] :=
          heff0.trans (heff_s_sd.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩)
            (fun _ h => False.elim (List.not_mem_nil h)))
        have hlog_b := M13.allocated_le_2pow64 hA0 hal_log
        have hlog8_nat : (logw + 8#64).toNat = logw.toNat + 8 := by
          rw [BitVec.toNat_add]; change (logw.toNat + 8) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
        have hev_l8_addr : @evalHOLExact 64 F _ sd.toExact (fun a => Classical.propDecidable (sd.memaddrs a))
            (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 8]) =
            some (.val (.word (logw + 8#64))) := by
          simp [evalHOLExact, evalListHOLExact, show sd.locals = s.locals from rfl, hl_log,
            wordOpHOL, wordOp, valueIsWord, valueWord]
        have hev_l8 := load_word_in_allocated_fresh hA0 hma0 heff0_sd hdst_ge hdst_hi hal_log
          _ (logw + 8#64) hev_l8_addr (by rw [hlog8_nat]; exact hwa_log8)
          (by rw [hlog8_nat]; dsimp only; omega) (by rw [hlog8_nat]; dsimp only; omega)
        rw [hlog8_nat] at hev_l8
        let tptr : BitVec 64 := BitVec.ofNat 64 (memW s0 (logw.toNat + 8)) + jw * 32#64
        have hev_j32 : @evalHOLExact 64 F _ sd.toExact (fun a => Classical.propDecidable (sd.memaddrs a))
            (.panop .mul [ExpHOL.var VarKind.local (ofString "j"), .const 32]) =
            some (.val (.word (jw * 32#64))) := by
          simp [evalHOLExact, evalListHOLExact, show sd.locals = s.locals from rfl, hl_j, panOpHOL,
            valueIsWord, valueWord]
        have hev_src : @evalHOLExact 64 F _ sd.toExact (fun a => Classical.propDecidable (sd.memaddrs a))
            (.op .add
              [.load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 8]),
               .panop .mul [ExpHOL.var VarKind.local (ofString "j"), .const 32]]) =
            some (.val (.word tptr)) := by
          have hz_j32 : jw * 32#64 + 0 = jw * 32#64 := BitVec.add_zero _
          unfold evalHOLExact; simp only [evalListHOLExact]
          rw [hev_l8, hev_j32]
          simp [wordOpHOL, wordOp, valueIsWord, valueWord, hz_j32, tptr]
        have hhl32 : rlpHeaderLenPure (32#64 : BitVec 64).toNat + (32#64 : BitVec 64).toNat = 33 := by
          have : (32#64 : BitVec 64).toNat = 32 := by decide
          rw [this, rlpHeaderLenPure_of_le55 (by decide)]
        dsimp only [elInnerBody] at hnt ⊢
        rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
        rcases hc_eb : evaluateHOLFiniteState sd
          (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
            [ExpHOL.var VarKind.local (ofString "t"),
             .op .add
               [.load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 8]),
                .panop .mul [ExpHOL.var VarKind.local (ofString "j"), .const 32]],
             .const 32]) with ⟨rc, m1⟩
        have hnt_eb : rc ≠ some .timeOut := by rintro rfl; rw [hc_eb] at hnt; exact hnt rfl
        have heb := eval_call_local_rlp_encode_bytes sd "w"
          (ExpHOL.var VarKind.local (ofString "t"))
          (.op .add
            [.load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 8]),
             .panop .mul [ExpHOL.var VarKind.local (ofString "j"), .const 32]])
          (.const 32)
          tw tptr 32#64 [(dst0, bound)] [] heff0_sd.arena.1.code heff0_sd.arena
          hl_w (by simp [evalHOLExact, show sd.locals = s.locals from rfl, hl_t])
          hev_src rfl
          ⟨(dst0, bound), List.mem_singleton.2 rfl, by omega, by
            rw [Nat.add_assoc, hhl32]
            have : 33 * (jw.toNat + 1) ≤ 33 * ntw.toNat := Nat.mul_le_mul_left _ (by omega)
            omega⟩
          (by rw [hc_eb]; exact hnt_eb)
        have hclk_eb := evaluateHOLFiniteState_clock_le sd
          (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
            [ExpHOL.var VarKind.local (ofString "t"),
             .op .add
               [.load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 8]),
                .panop .mul [ExpHOL.var VarKind.local (ofString "j"), .const 32]],
             .const 32])
        have hnbc_eb := call_noexc_ne_break_continue sd (some (VarKind.local, ofString "w"))
          (ofString "rlp_encode_bytes")
          [ExpHOL.var VarKind.local (ofString "t"),
           .op .add
             [.load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 8]),
              .panop .mul [ExpHOL.var VarKind.local (ofString "j"), .const 32]],
           .const 32]
        have hc_eb' : evaluateHOLFiniteState (decClockHOLFinite s)
            (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
              [ExpHOL.var VarKind.local (ofString "t"),
               .op .add
                 [.load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 8]),
                  .panop .mul [ExpHOL.var VarKind.local (ofString "j"), .const 32]],
               .const 32]) = (rc, m1) := hc_eb
        dsimp only at heb; rw [hc_eb] at heb hclk_eb hnbc_eb
        simp only [hc_eb'] at hnt ⊢
        cases rc with
        | some rc' =>
          have hnr := heb.2 (by simp)
          cases rc' with
          | «break» => exact absurd rfl hnbc_eb.1
          | «continue» => exact absurd rfl hnbc_eb.2
          | _ =>
            dsimp only
            exact ⟨fun h => by simp at h, fun _ => hnr⟩
        | none =>
          dsimp only at hnt ⊢
          obtain ⟨ww, hww_le', _, _, hm1_loc', heff_m1⟩ := heb.1 rfl
          have hm1_loc : m1.locals = sd.locals.update (ofString "w", ValueHOL.val (HolWordLab.word ww)) := hm1_loc'
          have hww_le : ww.toNat ≤ 33 := by rw [hhl32] at hww_le'; exact hww_le'
          have hm1_w : m1.locals.lookup (ofString "w") = some (.val (.word ww)) := by
            rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
          have hm1_t : m1.locals.lookup (ofString "t") = some (.val (.word tw)) := by
            rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, show sd.locals = s.locals from rfl, hl_t,
              show ofString "w" ≠ ofString "t" by decide]
          have hm1_j : m1.locals.lookup (ofString "j") = some (.val (.word jw)) := by
            rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, show sd.locals = s.locals from rfl, hl_j,
              show ofString "w" ≠ ofString "j" by decide]
          let tw' : BitVec 64 := tw + ww
          let jw' : BitVec 64 := jw + 1#64
          have htw'_nat : tw'.toNat = tw.toNat + ww.toNat := by
            rw [BitVec.toNat_add]
            have : 33 * (jw.toNat + 1) ≤ 33 * ntw.toNat := Nat.mul_le_mul_left _ (by omega)
            exact Nat.mod_eq_of_lt (by omega)
          have hjw'_nat : jw'.toNat = jw.toNat + 1 := by
            rw [BitVec.toNat_add]; change (jw.toNat + 1) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
          have hass_tj : evaluateHOLFiniteState m1
              (.seq
                (.assign VarKind.local (ofString "t")
                  (.op .add [ExpHOL.var VarKind.local (ofString "t"), ExpHOL.var VarKind.local (ofString "w")]))
                (.assign VarKind.local (ofString "j")
                  (.op .add [ExpHOL.var VarKind.local (ofString "j"), .const 1]))) =
              (none, setVarHOLFinite (ofString "j") (.val (.word jw'))
                (setVarHOLFinite (ofString "t") (.val (.word tw')) m1)) := by
            rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
            have hev_t' : @evalHOLExact 64 F _ m1.toExact (fun a => Classical.propDecidable (m1.memaddrs a))
                (.op .add [ExpHOL.var VarKind.local (ofString "t"), ExpHOL.var VarKind.local (ofString "w")]) =
                some (.val (.word tw')) := by
              simp [evalHOLExact, evalListHOLExact, hm1_t, hm1_w, wordOpHOL, wordOp, valueIsWord, valueWord, tw']
            have hv_t : m1.isValidValueHOLFinite VarKind.local (ofString "t") (.val (.word tw')) = true := by
              simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hm1_t, shapeOfHOLExact, shapeEqHOL]
            rw [hev_t']; dsimp only; rw [if_pos hv_t]
            change evaluateHOLFiniteState (setVarHOLFinite (ofString "t") (.val (.word tw')) m1) _ = _
            rw [evaluateHOLFiniteState_assign]
            set m2 := setVarHOLFinite (ofString "t") (.val (.word tw')) m1
            have hm2_j : m2.locals.lookup (ofString "j") = some (.val (.word jw)) := by
              simp [m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_j,
                show ofString "t" ≠ ofString "j" by decide]
            have hev_j' : @evalHOLExact 64 F _ m2.toExact (fun a => Classical.propDecidable (m2.memaddrs a))
                (.op .add [ExpHOL.var VarKind.local (ofString "j"), .const 1]) =
                some (.val (.word jw')) := by
              simp [evalHOLExact, evalListHOLExact, hm2_j, wordOpHOL, wordOp, valueIsWord, valueWord, jw']
            have hv_j : m2.isValidValueHOLFinite VarKind.local (ofString "j") (.val (.word jw')) = true := by
              simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hm2_j, shapeOfHOLExact, shapeEqHOL]
            rw [hev_j']; dsimp only; rw [if_pos hv_j]; rfl
          rw [hass_tj] at hnt ⊢; dsimp only at hnt ⊢
          set s_next := setVarHOLFinite (ofString "j") (.val (.word jw'))
            (setVarHOLFinite (ofString "t") (.val (.word tw')) m1)
          have heff_s_next : HeapByteEff s s_next [(dst0, bound)] [] :=
            (heff_s_sd.trans heff_m1).locals_clock s_next.locals s_next.clock
          have hs_clk : s_next.clock ≤ k := by
            have : s_next.clock = m1.clock := rfl
            have : m1.clock ≤ s.clock - 1 := hclk_eb
            omega
          obtain ⟨rw0, hrw0⟩ := hl_r
          have hih := ih s_next tw' jw'
            ⟨rw0, by simp [s_next, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_loc,
                      show sd.locals = s.locals from rfl, hrw0,
                      show ofString "j" ≠ ofString "r" by decide,
                      show ofString "t" ≠ ofString "r" by decide,
                      show ofString "w" ≠ ofString "r" by decide]⟩
            hs_clk (heff0.trans (heff_s_next.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩)
              (fun _ h => False.elim (List.not_mem_nil h))))
            (by omega) (by omega)
            (by rw [htw'_nat, hjw'_nat]; omega)
            (by simp [s_next, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_loc,
                  show sd.locals = s.locals from rfl, hl_log,
                  show ofString "j" ≠ ofString "log" by decide,
                  show ofString "t" ≠ ofString "log" by decide,
                  show ofString "w" ≠ ofString "log" by decide])
            (by simp [s_next, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_loc,
                  show sd.locals = s.locals from rfl, hl_ts,
                  show ofString "j" ≠ ofString "tstart" by decide,
                  show ofString "t" ≠ ofString "tstart" by decide,
                  show ofString "w" ≠ ofString "tstart" by decide])
            (by simp [s_next, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "j" ≠ ofString "t" by decide])
            (by simp [s_next, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_loc,
                  show sd.locals = s.locals from rfl, hl_nt,
                  show ofString "j" ≠ ofString "nt" by decide,
                  show ofString "t" ≠ ofString "nt" by decide,
                  show ofString "w" ≠ ofString "nt" by decide])
            (by simp [s_next, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
            ⟨ww, by simp [s_next, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_w,
                      show ofString "j" ≠ ofString "w" by decide,
                      show ofString "t" ≠ ofString "w" by decide]⟩
            (by simp [s_next, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_loc,
                  show sd.locals = s.locals from rfl, hl_q,
                  show ofString "j" ≠ ofString "q" by decide,
                  show ofString "t" ≠ ofString "q" by decide,
                  show ofString "w" ≠ ofString "q" by decide])
            (by simp [s_next, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_loc,
                  show sd.locals = s.locals from rfl, hl_i,
                  show ofString "j" ≠ ofString "i" by decide,
                  show ofString "t" ≠ ofString "i" by decide,
                  show ofString "w" ≠ ofString "i" by decide])
            (by simp [s_next, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_loc,
                  show sd.locals = s.locals from rfl, hl_n,
                  show ofString "j" ≠ ofString "n" by decide,
                  show ofString "t" ≠ ofString "n" by decide,
                  show ofString "w" ≠ ofString "n" by decide])
            (by simp [s_next, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_loc,
                  show sd.locals = s.locals from rfl, hl_p,
                  show ofString "j" ≠ ofString "p" by decide,
                  show ofString "t" ≠ ofString "p" by decide,
                  show ofString "w" ≠ ofString "p" by decide])
            (by simp [s_next, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_loc,
                  show sd.locals = s.locals from rfl, hl_dst,
                  show ofString "j" ≠ ofString "dst" by decide,
                  show ofString "t" ≠ ofString "dst" by decide,
                  show ofString "w" ≠ ofString "dst" by decide])
            hnt
          dsimp only at hih
          refine ⟨fun hnone => ?_, hih.2⟩
          obtain ⟨tf, htf1, htf2, heff_next, hl1, hl2, hl3, hl4, hl5, hl5r, hl6, hl7, hl8, hl9, hl10⟩ := hih.1 hnone
          exact ⟨tf, htf1, htf2, heff_s_next.trans heff_next, hl1, hl2, hl3, hl4, hl5, hl5r, hl6, hl7, hl8, hl9, hl10⟩
    · rw [if_neg hlt, if_neg (by decide : ¬ ((0#64 : BitVec 64) ≠ 0))]
      have hjeq : jw.toNat = ntw.toNat := by omega
      exact ⟨fun _ => ⟨tw, ht_ge, by rw [← hjeq]; exact ht_le, HeapByteEff.refl heff0.arena _ _,
        hl_log, hl_ts, hl_t, hl_nt, hl_w, hl_r, hl_q, hl_i, hl_n, hl_p, hl_dst⟩,
        fun h => False.elim (h rfl)⟩

private theorem eval_decCall_rlp_encode_bytes_outcome {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (dstExp srcExp nExp : ExpHOL 64)
    (dst0 src0 n0 : BitVec 64) (cont : ProgHOL 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) srcExp =
      some (.val (.word src0)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n0)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧
      dst0.toNat + rlpHeaderLenPure n0.toNat + n0.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_encode_bytes") [dstExp, srcExp, nExp] cont)).1 ≠
      some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_encode_bytes") [dstExp, srcExp, nExp] cont)
    (∃ (len : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      len.toNat ≤ rlpHeaderLenPure n0.toNat + n0.toNat ∧
      dst0.toNat < heapEnd ∧
      mid.globals = s.globals ∧
      mid.locals = s.locals.update (ofString lname, .val (.word len)) ∧
      HeapByteEff s mid Rl gw ∧
      mid.clock ≤ s.clock ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      out = ((evaluateHOLFiniteState mid cont).1,
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
            (ofString lname, s.locals.lookup (ofString lname)) })) ∨
    (out.1 ≠ none ∧ out.1 ≠ some .break ∧ out.1 ≠ some .continue ∧ ¬ Resumes out.1) := by
  intro out; dsimp only [out]
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, srcExp, nExp] = some [.val (.word dst0), .val (.word src0), .val (.word n0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hsrc, hn]
  have hlk := pan_three_word_lookup s.code.lookup (ofString "rlp_encode_bytes")
    (ofString "dst") (ofString "src") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes) dst0 src0 n0
    (by decide) (by decide) (by decide)
    (by rw [hcode]; exact lookup_rlp_encode_bytes)
  simp only [ha, hlk] at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set cmap := ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
      (ofString "src", ValueHOL.val (.word src0))).update (ofString "n", ValueHOL.val (.word n0))
    set ent := callEntryStateHOLFinite s cmap
    have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "dst" by decide, show ofString "src" ≠ ofString "dst" by decide]
    have hent_src : ent.locals.lookup (ofString "src") = some (.val (.word src0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "src" by decide]
    have hent_n : ent.locals.lookup (ofString "n") = some (.val (.word n0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hclk_eb := evaluateHOLFiniteState_clock_le ent (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)
    rcases heb : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes) with ⟨reb, seb⟩
    have hnt_eb : reb ≠ some .timeOut := by
      rintro rfl; rw [heb] at hnt; exact hnt rfl
    obtain ⟨hret, hnonret⟩ := eval_rlp_encode_bytes_body_exact ent dst0 src0 n0 Rl
      hcode hAR.1.memaddrs hent_dst hent_src hent_n hin_ivl (by rw [heb]; exact hnt_eb)
    rw [heb] at hret hnonret hclk_eb
    dsimp only at hret hnonret hclk_eb
    simp only [heb] at hnt ⊢
    cases reb with
    | none => exact Or.inr ⟨by simp, by simp, by simp, not_resumes_error⟩
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt_eb
      | exception eid ev =>
        exact Or.inr ⟨by simp, by simp, by simp, hnonret (.exception eid ev) rfl (fun _ h => by cases h)⟩
      | returned rv =>
        obtain ⟨len, rfl, hlen_le, hdst_lt, heff_eb⟩ := hret rv rfl
        have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word len) : ValueHOL 64)) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word len) : ValueHOL 64)) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        dsimp only at hnt ⊢
        rw [if_pos hsh] at hnt ⊢
        let mid := setVarHOLFinite (ofString lname) (.val (.word len))
          { seb with locals := s.locals }
        have heff0 : M11.ByteRegionEffect s ent Rl :=
          (M11.ByteRegionEffect.refl s Rl).with_locals_clock ent.locals ent.clock
        have heff_mid : M11.ByteRegionEffect s mid Rl :=
          (heff0.trans heff_eb).with_locals_clock mid.locals mid.clock
        have hmid_clk : mid.clock ≤ s.clock := by
          have : mid.clock = seb.clock := rfl
          have : ent.clock = s.clock - 1 := rfl
          omega
        exact Or.inl ⟨len, mid, hlen_le, hdst_lt, heff_mid.globals, rfl,
          (HeapByteEff.of_m11_bre hAR heff_mid).mono
            (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩)
            (fun _ h => False.elim (List.not_mem_nil h)),
          hmid_clk, (by intro h; apply hnt; rw [h]), rfl⟩
      | «break» | «continue» | error =>
        exact Or.inr ⟨by simp, by simp, by simp, not_resumes_error⟩
      | finalFfi _ =>
        exact Or.inr ⟨by simp, by simp, by simp, fun h => by
          rcases h with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

private theorem elOuterBody_exact {F : Type}
    (s0 s : PanSemStateFiniteExact 64 F)
    (dst0 bound : Nat) (dstw pw nw qw iw : BitVec 64)
    (hA0 : ArenaOK s0) (hma0 : s0.memaddrs = ordinaryDomain)
    (heff0 : HeapByteEff s0 s [(dst0, bound)] ["heap_ptr"])
    (hdst_ge : globN s0 "heap_ptr" ≤ dst0) (hdst_hi : dst0 + bound ≤ heapLimit)
    (hhl_lt : heapLimit < 2 ^ 64)
    (hal_arr : Allocated s0 (pw.toNat, 8 * nw.toNat))
    (hn_lt : nw.toNat < 2 ^ 28)
    (hi_lt : iw.toNat < nw.toNat)
    (hq_ge : dst0 + 9 ≤ qw.toNat)
    (hq_le : qw.toNat ≤ dst0 + 9 + logsEncodedSum s0 pw.toNat iw.toNat)
    (hfit_sum : 9 + logsEncodedSum s0 pw.toNat nw.toNat ≤ bound)
    (hentries : ∀ k < nw.toNat,
      WordAt s0 (pw.toNat + 8 * k) ∧
      let log := memW s0 (pw.toNat + 8 * k)
      Allocated s0 (log, 40) ∧
      memW s0 (log + 16) ≤ 4 ∧
      memW s0 (log + 32) < 2 ^ 32 ∧
      WordAt s0 log ∧ WordAt s0 (log + 8) ∧ WordAt s0 (log + 16) ∧
      WordAt s0 (log + 24) ∧ WordAt s0 (log + 32))
    (hl_dst : s.locals.lookup (ofString "dst") = some (.val (.word dstw)))
    (hl_p : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hl_n : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hl_q : s.locals.lookup (ofString "q") = some (.val (.word qw)))
    (hl_i : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hnt : (evaluateHOLFiniteState s elOuterBody).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s elOuterBody
    (out.1 = none →
      ∃ qf : BitVec 64,
        dst0 + 9 ≤ qf.toNat ∧
        qf.toNat ≤ dst0 + 9 + logsEncodedSum s0 pw.toNat (iw.toNat + 1) ∧
        HeapByteEff s out.2 [(dst0, bound)] [] ∧
        out.2.locals.lookup (ofString "dst") = some (.val (.word dstw)) ∧
        out.2.locals.lookup (ofString "p") = some (.val (.word pw)) ∧
        out.2.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
        out.2.locals.lookup (ofString "q") = some (.val (.word qf)) ∧
        out.2.locals.lookup (ofString "i") = some (.val (.word (iw + 1#64)))) ∧
    (out.1 ≠ none → out.1 ≠ some .break ∧ out.1 ≠ some .continue ∧ ¬ Resumes out.1) := by
  intro out; dsimp only [out, elOuterBody] at hnt ⊢
  obtain ⟨hwa_pi, hal_log, hnt_le4, hdlen_lt, hwa_l0, hwa_l8, hwa_l16, hwa_l24, hwa_l32⟩ := hentries iw.toNat hi_lt
  set log0 := memW s0 (pw.toNat + 8 * iw.toNat)
  have harr_b := M13.allocated_le_2pow64 hA0 hal_arr
  have hlog_b := M13.allocated_le_2pow64 hA0 hal_log
  have hsum_mono : logsEncodedSum s0 pw.toNat (iw.toNat + 1) ≤ logsEncodedSum s0 pw.toNat nw.toNat := by
    have haux : ∀ a b, a ≤ b → logsEncodedSum s0 pw.toNat a ≤ logsEncodedSum s0 pw.toNat b := by
      intro a b hab
      induction hab with
      | refl => exact le_rfl
      | @step m _ ih =>
        dsimp only [logsEncodedSum]; omega
    exact haux _ _ (by omega)
  have hsum_step : logsEncodedSum s0 pw.toNat (iw.toNat + 1) =
      logsEncodedSum s0 pw.toNat iw.toNat + 64 + 33 * memW s0 (log0 + 16) + memW s0 (log0 + 32) := rfl
  have hpi_nat : (pw + iw * 8#64).toNat = pw.toNat + 8 * iw.toNat := by
    have hi8 : (iw * 8#64).toNat = 8 * iw.toNat := by
      rw [BitVec.toNat_mul]; change (iw.toNat * 8) % 2 ^ 64 = 8 * iw.toNat
      rw [Nat.mul_comm]; exact Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_add, hi8]; exact Nat.mod_eq_of_lt (by omega)
  have hev_pi_addr : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [ExpHOL.var VarKind.local (ofString "p"),
        .panop .mul [ExpHOL.var VarKind.local (ofString "i"), .const 8]]) =
      some (.val (.word (pw + iw * 8#64))) := by
    have hz : iw * 8#64 + 0 = iw * 8#64 := BitVec.add_zero _
    simp [evalHOLExact, evalListHOLExact, hl_p, hl_i, wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord, hz]
  have hev_log := load_word_in_allocated_fresh hA0 hma0 heff0 hdst_ge hdst_hi hal_arr
    _ (pw + iw * 8#64) hev_pi_addr (by rw [hpi_nat]; exact hwa_pi)
    (by rw [hpi_nat]; dsimp only; omega) (by rw [hpi_nat]; dsimp only; omega)
  rw [hpi_nat] at hev_log
  let logw : BitVec 64 := BitVec.ofNat 64 log0
  have hlogw_nat : logw.toNat = log0 := Nat.mod_eq_of_lt (by omega)
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢; rw [hev_log] at hnt ⊢
  have hsh1 : shapeEqHOL .one (shapeOfHOLExact (.val (.word logw) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  dsimp only at hnt ⊢; rw [if_pos hsh1] at hnt ⊢; dsimp only at hnt ⊢
  set s1 := setVarHOLFinite (ofString "log") (.val (.word logw)) s
  have heff0_1 : HeapByteEff s0 s1 [(dst0, bound)] ["heap_ptr"] := heff0.locals_clock s1.locals s1.clock
  let r0w : BitVec 64 := qw + 9#64
  have hr0_nat : r0w.toNat = qw.toNat + 9 := by
    rw [BitVec.toNat_add]; change (qw.toNat + 9) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
  have hs1_q : s1.locals.lookup (ofString "q") = some (.val (.word qw)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_q,
      show ofString "log" ≠ ofString "q" by decide]
  have hev_r0 : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
      (.op .add [ExpHOL.var VarKind.local (ofString "q"), .const 9]) =
      some (.val (.word r0w)) := by
    simp [evalHOLExact, evalListHOLExact, hs1_q, wordOpHOL, wordOp, valueIsWord, valueWord, r0w]
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢; rw [hev_r0] at hnt ⊢
  have hsh_r0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word r0w) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  dsimp only at hnt ⊢; rw [if_pos hsh_r0] at hnt ⊢; dsimp only at hnt ⊢
  set s2 := setVarHOLFinite (ofString "r") (.val (.word r0w)) s1
  have heff0_2 : HeapByteEff s0 s2 [(dst0, bound)] ["heap_ptr"] := heff0_1.locals_clock s2.locals s2.clock
  have hs2_r : s2.locals.lookup (ofString "r") = some (.val (.word r0w)) := by
    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs2_log : s2.locals.lookup (ofString "log") = some (.val (.word logw)) := by
    simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "r" ≠ ofString "log" by decide]
  have hev_l0_addr : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
      (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 0]) =
      some (.val (.word logw)) := by
    simp [evalHOLExact, evalListHOLExact, hs2_log, wordOpHOL, wordOp, valueIsWord, valueWord]
  have hal_logw : Allocated s0 (logw.toNat, 40) := by rw [hlogw_nat]; exact hal_log
  have hev_l0 := load_word_in_allocated_fresh hA0 hma0 heff0_2 hdst_ge hdst_hi hal_logw
    _ logw hev_l0_addr (by rw [hlogw_nat]; exact hwa_l0)
    (by dsimp only; omega) (by dsimp only; omega)
  have hhl20 : rlpHeaderLenPure (20#64 : BitVec 64).toNat + (20#64 : BitVec 64).toNat = 21 := by
    have : (20#64 : BitVec 64).toNat = 20 := by decide
    rw [this, rlpHeaderLenPure_of_le55 (by decide)]
  rcases eval_decCall_rlp_encode_bytes_outcome s2 "w"
      (ExpHOL.var VarKind.local (ofString "r"))
      (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 0]))
      (.const 20)
      r0w (BitVec.ofNat 64 (memW s0 logw.toNat)) 20#64
      _ [(dst0, bound)] [] heff0_2.arena.1.code heff0_2.arena
      (by simp [evalHOLExact, hs2_r]) hev_l0 rfl
      ⟨(dst0, bound), List.mem_singleton.mpr rfl, by dsimp only; omega,
        by rw [Nat.add_assoc, hhl20]; dsimp only; omega⟩
      hnt with ⟨w1, s3, hw1_le', _, _, hs3_loc, heff_2_3, _, hnt3, hs2_eq⟩ | ⟨hne2, hnb2, hnc2, hnr2⟩
  · rw [hs2_eq]; dsimp only
    have hw1_le : w1.toNat ≤ 21 := by rw [hhl20] at hw1_le'; exact hw1_le'
    have heff0_3 : HeapByteEff s0 s3 [(dst0, bound)] ["heap_ptr"] :=
      heff0_2.trans (heff_2_3.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩)
        (fun _ h => False.elim (List.not_mem_nil h)))
    have hs3_r : s3.locals.lookup (ofString "r") = some (.val (.word r0w)) := by
      rw [hs3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs2_r,
        show ofString "w" ≠ ofString "r" by decide]
    have hs3_w : s3.locals.lookup (ofString "w") = some (.val (.word w1)) := by
      rw [hs3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    let r1w : BitVec 64 := r0w + w1
    have hr1_nat : r1w.toNat = r0w.toNat + w1.toNat := by
      rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign] at hnt3 ⊢
    have hev_r1 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
        (.op .add [ExpHOL.var VarKind.local (ofString "r"), ExpHOL.var VarKind.local (ofString "w")]) =
        some (.val (.word r1w)) := by
      simp [evalHOLExact, evalListHOLExact, hs3_r, hs3_w, wordOpHOL, wordOp, valueIsWord, valueWord, r1w]
    have hv_r1 : s3.isValidValueHOLFinite VarKind.local (ofString "r") (.val (.word r1w)) = true := by
      simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hs3_r, shapeOfHOLExact, shapeEqHOL]
    rw [hev_r1] at hnt3 ⊢; dsimp only at hnt3 ⊢; rw [if_pos hv_r1] at hnt3 ⊢
    have hsk4 : setKvarHOLFinite VarKind.local (ofString "r") (.val (.word r1w)) s3 =
        setVarHOLFinite (ofString "r") (.val (.word r1w)) s3 := rfl
    rw [hsk4] at hnt3 ⊢
    set s4 := setVarHOLFinite (ofString "r") (.val (.word r1w)) s3
    have heff0_4 : HeapByteEff s0 s4 [(dst0, bound)] ["heap_ptr"] := heff0_3.locals_clock s4.locals s4.clock
    have hs4_r : s4.locals.lookup (ofString "r") = some (.val (.word r1w)) := by
      simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs4_log : s4.locals.lookup (ofString "log") = some (.val (.word logw)) := by
      simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_loc, hs2_log,
        show ofString "r" ≠ ofString "log" by decide, show ofString "w" ≠ ofString "log" by decide]
    rw [evaluateHOLFiniteState_dec_total] at hnt3 ⊢
    have hev_ts : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
        (ExpHOL.var VarKind.local (ofString "r")) = some (.val (.word r1w)) := by
      simp [evalHOLExact, hs4_r]
    dsimp only at hnt3 ⊢; rw [hev_ts] at hnt3 ⊢
    have hsh_ts : shapeEqHOL .one (shapeOfHOLExact (.val (.word r1w) : ValueHOL 64)) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    dsimp only at hnt3 ⊢; rw [if_pos hsh_ts] at hnt3 ⊢; dsimp only at hnt3 ⊢
    set s5 := setVarHOLFinite (ofString "tstart") (.val (.word r1w)) s4
    let t0w : BitVec 64 := r1w + 9#64
    have ht0_nat : t0w.toNat = r1w.toNat + 9 := by
      rw [BitVec.toNat_add]; change (r1w.toNat + 9) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
    have hs5_r : s5.locals.lookup (ofString "r") = some (.val (.word r1w)) := by
      simp [s5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs4_r,
        show ofString "tstart" ≠ ofString "r" by decide]
    rw [evaluateHOLFiniteState_dec_total] at hnt3 ⊢
    have hev_t0 : @evalHOLExact 64 F _ s5.toExact (fun a => Classical.propDecidable (s5.memaddrs a))
        (.op .add [ExpHOL.var VarKind.local (ofString "r"), .const 9]) = some (.val (.word t0w)) := by
      simp [evalHOLExact, evalListHOLExact, hs5_r, wordOpHOL, wordOp, valueIsWord, valueWord, t0w]
    dsimp only at hnt3 ⊢; rw [hev_t0] at hnt3 ⊢
    have hsh_t0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word t0w) : ValueHOL 64)) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    dsimp only at hnt3 ⊢; rw [if_pos hsh_t0] at hnt3 ⊢; dsimp only at hnt3 ⊢
    set s6 := setVarHOLFinite (ofString "t") (.val (.word t0w)) s5
    have heff0_6 : HeapByteEff s0 s6 [(dst0, bound)] ["heap_ptr"] := heff0_4.locals_clock s6.locals s6.clock
    have hs6_log : s6.locals.lookup (ofString "log") = some (.val (.word logw)) := by
      simp [s6, s5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs4_log,
        show ofString "t" ≠ ofString "log" by decide, show ofString "tstart" ≠ ofString "log" by decide]
    have hlog16_nat : (logw + 16#64).toNat = log0 + 16 := by
      rw [BitVec.toNat_add, hlogw_nat]; change (log0 + 16) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
    have hev_l16_addr : @evalHOLExact 64 F _ s6.toExact (fun a => Classical.propDecidable (s6.memaddrs a))
        (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 16]) =
        some (.val (.word (logw + 16#64))) := by
      simp [evalHOLExact, evalListHOLExact, hs6_log, wordOpHOL, wordOp, valueIsWord, valueWord]
    have hev_nt := load_word_in_allocated_fresh hA0 hma0 heff0_6 hdst_ge hdst_hi hal_logw
      _ (logw + 16#64) hev_l16_addr (by rw [hlog16_nat]; exact hwa_l16)
      (by rw [hlog16_nat, hlogw_nat]; dsimp only; omega) (by rw [hlog16_nat, hlogw_nat]; dsimp only; omega)
    rw [hlog16_nat] at hev_nt
    let ntw : BitVec 64 := BitVec.ofNat 64 (memW s0 (log0 + 16))
    have hntw_nat : ntw.toNat = memW s0 (log0 + 16) := Nat.mod_eq_of_lt (by omega)
    rw [evaluateHOLFiniteState_dec_total] at hnt3 ⊢
    dsimp only at hnt3 ⊢; rw [hev_nt] at hnt3 ⊢
    have hsh_nt : shapeEqHOL .one (shapeOfHOLExact (.val (.word ntw) : ValueHOL 64)) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    dsimp only at hnt3 ⊢; rw [if_pos hsh_nt] at hnt3 ⊢; dsimp only at hnt3 ⊢
    set s7 := setVarHOLFinite (ofString "nt") (.val (.word ntw)) s6
    rw [evaluateHOLFiniteState_dec_total] at hnt3 ⊢
    have hev_j0 : @evalHOLExact 64 F _ s7.toExact (fun a => Classical.propDecidable (s7.memaddrs a))
        (.const 0) = some (.val (.word 0#64)) := rfl
    dsimp only at hnt3 ⊢; rw [hev_j0] at hnt3 ⊢
    have hsh_j0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0#64) : ValueHOL 64)) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    dsimp only at hnt3 ⊢; rw [if_pos hsh_j0] at hnt3 ⊢; dsimp only at hnt3 ⊢
    set s8 := setVarHOLFinite (ofString "j") (.val (.word 0#64)) s7
    have heff0_8 : HeapByteEff s0 s8 [(dst0, bound)] ["heap_ptr"] := heff0_6.locals_clock s8.locals s8.clock
    have hhl_he : heapLimit ≤ heapEnd := by rw [heapLimit_val, heapEnd_val]; decide
    rw [evaluateHOLFiniteState_seq_line780] at hnt3 ⊢
    rcases hiw : evaluateHOLFiniteState s8 elInnerWhile with ⟨riw, s9⟩
    have hnt_iw : riw ≠ some .timeOut := by rintro rfl; rw [hiw] at hnt3; exact hnt3 rfl
    have hj0_nat : (0#64 : BitVec 64).toNat = 0 := by decide
    have hiw_res := elInnerWhile_exact s8.clock s0 s8 dst0 bound logw r1w t0w ntw 0#64
      ⟨r1w, by simp [s8, s7, s6, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs5_r,
                show ofString "j" ≠ ofString "r" by decide, show ofString "nt" ≠ ofString "r" by decide,
                show ofString "t" ≠ ofString "r" by decide]⟩
      qw iw nw pw dstw
      le_rfl hA0 hma0 heff0_8 hdst_ge hdst_hi hhl_lt (by rw [hntw_nat]; exact hnt_le4)
      (by rw [hj0_nat]; omega) (by omega)
      (by rw [hj0_nat]; omega)
      (by rw [hntw_nat]; omega) (by omega)
      hal_logw (by rw [hlogw_nat]; exact hwa_l8)
      (by simp [s8, s7, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs6_log,
            show ofString "j" ≠ ofString "log" by decide, show ofString "nt" ≠ ofString "log" by decide])
      (by simp [s8, s7, s6, s5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "j" ≠ ofString "tstart" by decide, show ofString "nt" ≠ ofString "tstart" by decide,
            show ofString "t" ≠ ofString "tstart" by decide])
      (by simp [s8, s7, s6, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "j" ≠ ofString "t" by decide, show ofString "nt" ≠ ofString "t" by decide])
      (by simp [s8, s7, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "j" ≠ ofString "nt" by decide])
      (by simp [s8, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      ⟨w1, by simp [s8, s7, s6, s5, s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_w,
                show ofString "j" ≠ ofString "w" by decide, show ofString "nt" ≠ ofString "w" by decide,
                show ofString "t" ≠ ofString "w" by decide, show ofString "tstart" ≠ ofString "w" by decide,
                show ofString "r" ≠ ofString "w" by decide]⟩
      (by simp [s8, s7, s6, s5, s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_loc,
            s2, s1, hl_q,
            show ofString "j" ≠ ofString "q" by decide, show ofString "nt" ≠ ofString "q" by decide,
            show ofString "t" ≠ ofString "q" by decide, show ofString "tstart" ≠ ofString "q" by decide,
            show ofString "r" ≠ ofString "q" by decide, show ofString "w" ≠ ofString "q" by decide,
            show ofString "log" ≠ ofString "q" by decide])
      (by simp [s8, s7, s6, s5, s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_loc,
            s2, s1, hl_i,
            show ofString "j" ≠ ofString "i" by decide, show ofString "nt" ≠ ofString "i" by decide,
            show ofString "t" ≠ ofString "i" by decide, show ofString "tstart" ≠ ofString "i" by decide,
            show ofString "r" ≠ ofString "i" by decide, show ofString "w" ≠ ofString "i" by decide,
            show ofString "log" ≠ ofString "i" by decide])
      (by simp [s8, s7, s6, s5, s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_loc,
            s2, s1, hl_n,
            show ofString "j" ≠ ofString "n" by decide, show ofString "nt" ≠ ofString "n" by decide,
            show ofString "t" ≠ ofString "n" by decide, show ofString "tstart" ≠ ofString "n" by decide,
            show ofString "r" ≠ ofString "n" by decide, show ofString "w" ≠ ofString "n" by decide,
            show ofString "log" ≠ ofString "n" by decide])
      (by simp [s8, s7, s6, s5, s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_loc,
            s2, s1, hl_p,
            show ofString "j" ≠ ofString "p" by decide, show ofString "nt" ≠ ofString "p" by decide,
            show ofString "t" ≠ ofString "p" by decide, show ofString "tstart" ≠ ofString "p" by decide,
            show ofString "r" ≠ ofString "p" by decide, show ofString "w" ≠ ofString "p" by decide,
            show ofString "log" ≠ ofString "p" by decide])
      (by simp [s8, s7, s6, s5, s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_loc,
            s2, s1, hl_dst,
            show ofString "j" ≠ ofString "dst" by decide, show ofString "nt" ≠ ofString "dst" by decide,
            show ofString "t" ≠ ofString "dst" by decide, show ofString "tstart" ≠ ofString "dst" by decide,
            show ofString "r" ≠ ofString "dst" by decide, show ofString "w" ≠ ofString "dst" by decide,
            show ofString "log" ≠ ofString "dst" by decide])
      (by rw [hiw]; exact hnt_iw)
    have hnbc_iw : (evaluateHOLFiniteState s8 elInnerWhile).1 ≠ some .break ∧
        (evaluateHOLFiniteState s8 elInnerWhile).1 ≠ some .continue :=
      while_no_break_continue s8
        (.cmp .less (ExpHOL.var VarKind.local (ofString "j")) (ExpHOL.var VarKind.local (ofString "nt"))) elInnerBody
    dsimp only at hiw_res
    rw [hiw] at hiw_res hnbc_iw
    dsimp only at hiw_res hnbc_iw
    simp only [hiw] at hnt3 ⊢
    cases riw with
    | some riw' =>
      have hnr := hiw_res.2 (by simp)
      dsimp only
      exact ⟨fun h => by simp at h, fun _ => ⟨hnbc_iw.1, hnbc_iw.2, hnr⟩⟩
    | none =>
      dsimp only at hnt3 ⊢
      obtain ⟨tf, htf_ge, htf_le, heff_8_9, hs9_log, hs9_ts, hs9_t, hs9_nt, hs9_w, hs9_r, hs9_q, hs9_i, hs9_n, hs9_p, hs9_dst⟩ :=
        hiw_res.1 rfl
      have heff0_9 : HeapByteEff s0 s9 [(dst0, bound)] ["heap_ptr"] :=
        heff0_8.trans (heff_8_9.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩)
          (fun _ h => False.elim (List.not_mem_nil h)))
      -- Step 7: call (local w) "rlp_finish_list" [tstart, t]
      rw [evaluateHOLFiniteState_seq_line780] at hnt3 ⊢
      rcases hfl1 : evaluateHOLFiniteState s9
        (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_finish_list")
          [ExpHOL.var VarKind.local (ofString "tstart"), ExpHOL.var VarKind.local (ofString "t")]) with ⟨rfl1, s10⟩
      have hnt_fl1 : rfl1 ≠ some .timeOut := by rintro rfl; rw [hfl1] at hnt3; exact hnt3 rfl
      have hfl1_res := eval_call_local_rlp_finish_list s9 "w"
        (ExpHOL.var VarKind.local (ofString "tstart")) (ExpHOL.var VarKind.local (ofString "t"))
        r1w tf [(dst0, bound)] [] heff0_9.arena.1.code heff0_9.arena
        hs9_w (by simp [evalHOLExact, hs9_ts]) (by simp [evalHOLExact, hs9_t])
        htf_ge (by rw [hntw_nat] at htf_le; omega)
        ⟨(dst0, bound), List.mem_singleton.mpr rfl, by dsimp only; omega, by rw [hntw_nat] at htf_le; dsimp only; omega⟩
        (by rw [hfl1]; exact hnt_fl1)
      have hnbc_fl1 := call_noexc_ne_break_continue s9 (some (VarKind.local, ofString "w"))
        (ofString "rlp_finish_list")
        [ExpHOL.var VarKind.local (ofString "tstart"), ExpHOL.var VarKind.local (ofString "t")]
      dsimp only at hfl1_res; rw [hfl1] at hfl1_res hnbc_fl1
      simp only [hfl1] at hnt3 ⊢
      cases rfl1 with
      | some rfl1' =>
        have hnr := hfl1_res.2 (by simp)
        dsimp only
        exact ⟨fun h => by simp at h, fun _ => ⟨hnbc_fl1.1, hnbc_fl1.2, hnr⟩⟩
      | none =>
        dsimp only at hnt3 ⊢
        obtain ⟨w2, hw2_eq, hw2_le_diff, _, hs10_loc', heff_9_10⟩ := hfl1_res.1 rfl
        have hs10_loc : s10.locals = s9.locals.update (ofString "w", .val (.word w2)) := hs10_loc'
        have heff0_10 : HeapByteEff s0 s10 [(dst0, bound)] ["heap_ptr"] :=
          heff0_9.trans (heff_9_10.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩)
            (fun _ h => False.elim (List.not_mem_nil h)))
        have hw2_le : w2.toNat ≤ 9 + 33 * memW s0 (log0 + 16) := by rw [hntw_nat] at htf_le; omega
        -- Step 8: assign "r" = tstart + w
        let r2w : BitVec 64 := r1w + w2
        have hr2_nat : r2w.toNat = r1w.toNat + w2.toNat := by
          rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
        have hs10_ts : s10.locals.lookup (ofString "tstart") = some (.val (.word r1w)) := by
          rw [hs10_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs9_ts,
            show ofString "w" ≠ ofString "tstart" by decide]
        have hs10_w : s10.locals.lookup (ofString "w") = some (.val (.word w2)) := by
          rw [hs10_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        obtain ⟨rw9, hs9_rw⟩ := hs9_r
        have hs10_rw : s10.locals.lookup (ofString "r") = some (.val (.word rw9)) := by
          rw [hs10_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs9_rw,
            show ofString "w" ≠ ofString "r" by decide]
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign] at hnt3 ⊢
        have hev_r2 : @evalHOLExact 64 F _ s10.toExact (fun a => Classical.propDecidable (s10.memaddrs a))
            (.op .add [ExpHOL.var VarKind.local (ofString "tstart"), ExpHOL.var VarKind.local (ofString "w")]) =
            some (.val (.word r2w)) := by
          simp [evalHOLExact, evalListHOLExact, hs10_ts, hs10_w, wordOpHOL, wordOp, valueIsWord, valueWord, r2w]
        have hv_r2 : s10.isValidValueHOLFinite VarKind.local (ofString "r") (.val (.word r2w)) = true := by
          simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hs10_rw, shapeOfHOLExact, shapeEqHOL]
        rw [hev_r2] at hnt3 ⊢; dsimp only at hnt3 ⊢; rw [if_pos hv_r2] at hnt3 ⊢
        have hsk11 : setKvarHOLFinite VarKind.local (ofString "r") (.val (.word r2w)) s10 =
            setVarHOLFinite (ofString "r") (.val (.word r2w)) s10 := rfl
        rw [hsk11] at hnt3 ⊢
        set s11 := setVarHOLFinite (ofString "r") (.val (.word r2w)) s10
        have heff0_11 : HeapByteEff s0 s11 [(dst0, bound)] ["heap_ptr"] := heff0_10.locals_clock s11.locals s11.clock
        -- Step 9: call (local w) "rlp_encode_bytes" [r, load (log + 24), load (log + 32)]
        have hs11_r : s11.locals.lookup (ofString "r") = some (.val (.word r2w)) := by
          simp [s11, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hs11_log : s11.locals.lookup (ofString "log") = some (.val (.word logw)) := by
          simp [s11, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs10_loc, hs9_log,
            show ofString "r" ≠ ofString "log" by decide, show ofString "w" ≠ ofString "log" by decide]
        have hs11_w : s11.locals.lookup (ofString "w") = some (.val (.word w2)) := by
          simp [s11, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs10_w,
            show ofString "r" ≠ ofString "w" by decide]
        have hlog24_nat : (logw + 24#64).toNat = log0 + 24 := by
          rw [BitVec.toNat_add, hlogw_nat]; change (log0 + 24) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
        have hlog32_nat : (logw + 32#64).toNat = log0 + 32 := by
          rw [BitVec.toNat_add, hlogw_nat]; change (log0 + 32) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
        have hev_l24_addr : @evalHOLExact 64 F _ s11.toExact (fun a => Classical.propDecidable (s11.memaddrs a))
            (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 24]) =
            some (.val (.word (logw + 24#64))) := by
          simp [evalHOLExact, evalListHOLExact, hs11_log, wordOpHOL, wordOp, valueIsWord, valueWord]
        have hev_l32_addr : @evalHOLExact 64 F _ s11.toExact (fun a => Classical.propDecidable (s11.memaddrs a))
            (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 32]) =
            some (.val (.word (logw + 32#64))) := by
          simp [evalHOLExact, evalListHOLExact, hs11_log, wordOpHOL, wordOp, valueIsWord, valueWord]
        have hev_l24 := load_word_in_allocated_fresh hA0 hma0 heff0_11 hdst_ge hdst_hi hal_logw
          _ (logw + 24#64) hev_l24_addr (by rw [hlog24_nat]; exact hwa_l24)
          (by rw [hlog24_nat, hlogw_nat]; dsimp only; omega) (by rw [hlog24_nat, hlogw_nat]; dsimp only; omega)
        rw [hlog24_nat] at hev_l24
        have hev_l32 := load_word_in_allocated_fresh hA0 hma0 heff0_11 hdst_ge hdst_hi hal_logw
          _ (logw + 32#64) hev_l32_addr (by rw [hlog32_nat]; exact hwa_l32)
          (by rw [hlog32_nat, hlogw_nat]; dsimp only; omega) (by rw [hlog32_nat, hlogw_nat]; dsimp only; omega)
        rw [hlog32_nat] at hev_l32
        let dptrw : BitVec 64 := BitVec.ofNat 64 (memW s0 (log0 + 24))
        let dlenw : BitVec 64 := BitVec.ofNat 64 (memW s0 (log0 + 32))
        have hdlenw_nat : dlenw.toNat = memW s0 (log0 + 32) := Nat.mod_eq_of_lt (by omega)
        have hhl_dlen := (rlpHeaderLenPure_bounds dlenw.toNat).2
        rw [evaluateHOLFiniteState_seq_line780] at hnt3 ⊢
        rcases heb2 : evaluateHOLFiniteState s11
          (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
            [ExpHOL.var VarKind.local (ofString "r"),
             .load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 24]),
             .load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 32])]) with ⟨reb2, s12⟩
        have hnt_eb2 : reb2 ≠ some .timeOut := by rintro rfl; rw [heb2] at hnt3; exact hnt3 rfl
        have heb2_res := eval_call_local_rlp_encode_bytes s11 "w"
          (ExpHOL.var VarKind.local (ofString "r"))
          (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 24]))
          (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 32]))
          r2w dptrw dlenw [(dst0, bound)] [] heff0_11.arena.1.code heff0_11.arena
          ⟨w2, hs11_w⟩ (by simp [evalHOLExact, hs11_r]) hev_l24 hev_l32
          ⟨(dst0, bound), List.mem_singleton.mpr rfl, by dsimp only; omega,
            by rw [hdlenw_nat] at hhl_dlen ⊢; dsimp only; omega⟩
          (by rw [heb2]; exact hnt_eb2)
        have hnbc_eb2 := call_noexc_ne_break_continue s11 (some (VarKind.local, ofString "w"))
          (ofString "rlp_encode_bytes")
          [ExpHOL.var VarKind.local (ofString "r"),
           .load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 24]),
           .load .one (.op .add [ExpHOL.var VarKind.local (ofString "log"), .const 32])]
        dsimp only at heb2_res; rw [heb2] at heb2_res hnbc_eb2
        simp only [heb2] at hnt3 ⊢
        cases reb2 with
        | some reb2' =>
          have hnr := heb2_res.2 (by simp)
          dsimp only
          exact ⟨fun h => by simp at h, fun _ => ⟨hnbc_eb2.1, hnbc_eb2.2, hnr⟩⟩
        | none =>
          dsimp only at hnt3 ⊢
          obtain ⟨w3, hw3_le', _, _, hs12_loc', heff_11_12⟩ := heb2_res.1 rfl
          have hs12_loc : s12.locals = s11.locals.update (ofString "w", .val (.word w3)) := hs12_loc'
          have heff0_12 : HeapByteEff s0 s12 [(dst0, bound)] ["heap_ptr"] :=
            heff0_11.trans (heff_11_12.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩)
              (fun _ h => False.elim (List.not_mem_nil h)))
          have hw3_le : w3.toNat ≤ 9 + memW s0 (log0 + 32) := by
            rw [hdlenw_nat] at hw3_le' hhl_dlen; omega
          -- Step 10: assign "r" = r + w
          let r3w : BitVec 64 := r2w + w3
          have hr3_nat : r3w.toNat = r2w.toNat + w3.toNat := by
            rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
          have hs12_r : s12.locals.lookup (ofString "r") = some (.val (.word r2w)) := by
            rw [hs12_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs11_r,
              show ofString "w" ≠ ofString "r" by decide]
          have hs12_w : s12.locals.lookup (ofString "w") = some (.val (.word w3)) := by
            rw [hs12_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign] at hnt3 ⊢
          have hev_r3 : @evalHOLExact 64 F _ s12.toExact (fun a => Classical.propDecidable (s12.memaddrs a))
              (.op .add [ExpHOL.var VarKind.local (ofString "r"), ExpHOL.var VarKind.local (ofString "w")]) =
              some (.val (.word r3w)) := by
            simp [evalHOLExact, evalListHOLExact, hs12_r, hs12_w, wordOpHOL, wordOp, valueIsWord, valueWord, r3w]
          have hv_r3 : s12.isValidValueHOLFinite VarKind.local (ofString "r") (.val (.word r3w)) = true := by
            simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hs12_r, shapeOfHOLExact, shapeEqHOL]
          rw [hev_r3] at hnt3 ⊢; dsimp only at hnt3 ⊢; rw [if_pos hv_r3] at hnt3 ⊢
          have hsk13 : setKvarHOLFinite VarKind.local (ofString "r") (.val (.word r3w)) s12 =
              setVarHOLFinite (ofString "r") (.val (.word r3w)) s12 := rfl
          rw [hsk13] at hnt3 ⊢
          set s13 := setVarHOLFinite (ofString "r") (.val (.word r3w)) s12
          have heff0_13 : HeapByteEff s0 s13 [(dst0, bound)] ["heap_ptr"] := heff0_12.locals_clock s13.locals s13.clock
          -- Step 11: call (local w) "rlp_finish_list" [q, r]
          have hs13_q : s13.locals.lookup (ofString "q") = some (.val (.word qw)) := by
            simp [s13, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs12_loc,
              s11, hs10_loc, hs9_q,
              show ofString "r" ≠ ofString "q" by decide, show ofString "w" ≠ ofString "q" by decide]
          have hs13_r : s13.locals.lookup (ofString "r") = some (.val (.word r3w)) := by
            simp [s13, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hs13_w : s13.locals.lookup (ofString "w") = some (.val (.word w3)) := by
            simp [s13, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs12_w,
              show ofString "r" ≠ ofString "w" by decide]
          rw [evaluateHOLFiniteState_seq_line780] at hnt3 ⊢
          rcases hfl2 : evaluateHOLFiniteState s13
            (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_finish_list")
              [ExpHOL.var VarKind.local (ofString "q"), ExpHOL.var VarKind.local (ofString "r")]) with ⟨rfl2, s14⟩
          have hnt_fl2 : rfl2 ≠ some .timeOut := by rintro rfl; rw [hfl2] at hnt3; exact hnt3 rfl
          have hfl2_res := eval_call_local_rlp_finish_list s13 "w"
            (ExpHOL.var VarKind.local (ofString "q")) (ExpHOL.var VarKind.local (ofString "r"))
            qw r3w [(dst0, bound)] [] heff0_13.arena.1.code heff0_13.arena
            ⟨w3, hs13_w⟩ (by simp [evalHOLExact, hs13_q]) (by simp [evalHOLExact, hs13_r])
            (by omega) (by omega)
            ⟨(dst0, bound), List.mem_singleton.mpr rfl, by dsimp only; omega, by dsimp only; omega⟩
            (by rw [hfl2]; exact hnt_fl2)
          have hnbc_fl2 := call_noexc_ne_break_continue s13 (some (VarKind.local, ofString "w"))
            (ofString "rlp_finish_list")
            [ExpHOL.var VarKind.local (ofString "q"), ExpHOL.var VarKind.local (ofString "r")]
          dsimp only at hfl2_res; rw [hfl2] at hfl2_res hnbc_fl2
          simp only [hfl2] at hnt3 ⊢
          cases rfl2 with
          | some rfl2' =>
            have hnr := hfl2_res.2 (by simp)
            dsimp only
            exact ⟨fun h => by simp at h, fun _ => ⟨hnbc_fl2.1, hnbc_fl2.2, hnr⟩⟩
          | none =>
            dsimp only at hnt3 ⊢
            obtain ⟨w4, hw4_eq, hw4_le_diff, _, hs14_loc', heff_13_14⟩ := hfl2_res.1 rfl
            have hs14_loc : s14.locals = s13.locals.update (ofString "w", .val (.word w4)) := hs14_loc'
            have hw4_ge1 : 1 ≤ w4.toNat := by
              have := (rlpHeaderLenPure_bounds (r3w.toNat - (qw.toNat + 9))).1; omega
            have hw4_le : w4.toNat ≤ 64 + 33 * memW s0 (log0 + 16) + memW s0 (log0 + 32) := by omega
            -- Step 12: assign "q" = q + w, assign "i" = i + 1
            let qf : BitVec 64 := qw + w4
            let iw' : BitVec 64 := iw + 1#64
            have hqf_nat : qf.toNat = qw.toNat + w4.toNat := by
              rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
            have hs14_q : s14.locals.lookup (ofString "q") = some (.val (.word qw)) := by
              rw [hs14_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs13_q,
                show ofString "w" ≠ ofString "q" by decide]
            have hs14_w : s14.locals.lookup (ofString "w") = some (.val (.word w4)) := by
              rw [hs14_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
            have hs14_i : s14.locals.lookup (ofString "i") = some (.val (.word iw)) := by
              rw [hs14_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
                s13, setVarHOLFinite, hs12_loc, s11, hs10_loc, hs9_i,
                show ofString "w" ≠ ofString "i" by decide, show ofString "r" ≠ ofString "i" by decide]
            have hass_qi : evaluateHOLFiniteState s14
                (.seq
                  (.assign VarKind.local (ofString "q")
                    (.op .add [ExpHOL.var VarKind.local (ofString "q"), ExpHOL.var VarKind.local (ofString "w")]))
                  (.assign VarKind.local (ofString "i")
                    (.op .add [ExpHOL.var VarKind.local (ofString "i"), .const 1]))) =
                (none, setVarHOLFinite (ofString "i") (.val (.word iw'))
                  (setVarHOLFinite (ofString "q") (.val (.word qf)) s14)) := by
              rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
              have hev_qf : @evalHOLExact 64 F _ s14.toExact (fun a => Classical.propDecidable (s14.memaddrs a))
                  (.op .add [ExpHOL.var VarKind.local (ofString "q"), ExpHOL.var VarKind.local (ofString "w")]) =
                  some (.val (.word qf)) := by
                simp [evalHOLExact, evalListHOLExact, hs14_q, hs14_w, wordOpHOL, wordOp, valueIsWord, valueWord, qf]
              have hv_qf : s14.isValidValueHOLFinite VarKind.local (ofString "q") (.val (.word qf)) = true := by
                simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hs14_q, shapeOfHOLExact, shapeEqHOL]
              rw [hev_qf]; dsimp only; rw [if_pos hv_qf]
              change evaluateHOLFiniteState (setVarHOLFinite (ofString "q") (.val (.word qf)) s14) _ = _
              rw [evaluateHOLFiniteState_assign]
              set m_q := setVarHOLFinite (ofString "q") (.val (.word qf)) s14
              have hm_i : m_q.locals.lookup (ofString "i") = some (.val (.word iw)) := by
                simp [m_q, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs14_i,
                  show ofString "q" ≠ ofString "i" by decide]
              have hev_i' : @evalHOLExact 64 F _ m_q.toExact (fun a => Classical.propDecidable (m_q.memaddrs a))
                  (.op .add [ExpHOL.var VarKind.local (ofString "i"), .const 1]) =
                  some (.val (.word iw')) := by
                simp [evalHOLExact, evalListHOLExact, hm_i, wordOpHOL, wordOp, valueIsWord, valueWord, iw']
              have hv_i' : m_q.isValidValueHOLFinite VarKind.local (ofString "i") (.val (.word iw')) = true := by
                simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hm_i, shapeOfHOLExact, shapeEqHOL]
              rw [hev_i']; dsimp only; rw [if_pos hv_i']; rfl
            rw [hass_qi]; dsimp only
            set s15 := setVarHOLFinite (ofString "i") (.val (.word iw'))
              (setVarHOLFinite (ofString "q") (.val (.word qf)) s14)
            have heff_s_15 : HeapByteEff s s15 [(dst0, bound)] [] := by
              have h_s_2 : HeapByteEff s s2 [(dst0, bound)] [] :=
                (HeapByteEff.refl heff0.arena _ _).locals_clock s2.locals s2.clock
              have h_2_8 : HeapByteEff s2 s8 [(dst0, bound)] [] :=
                heff_2_3.locals_clock s8.locals s8.clock
              have h_8_11 : HeapByteEff s8 s11 [(dst0, bound)] [] :=
                (heff_8_9.trans heff_9_10).locals_clock s11.locals s11.clock
              have h_11_13 : HeapByteEff s11 s13 [(dst0, bound)] [] :=
                heff_11_12.locals_clock s13.locals s13.clock
              exact ((((h_s_2.trans h_2_8).trans h_8_11).trans h_11_13).trans heff_13_14).locals_clock _ _
            refine ⟨fun _ => ⟨qf, by omega, by omega, heff_s_15.locals_clock _ _, ?_, ?_, ?_, ?_, ?_⟩,
              fun h => False.elim (h rfl)⟩
            · simp [PanRunBounded.resVarEq_lookup, s15, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                hs14_loc, s13, hs12_loc, s11, hs10_loc, hs9_dst,
                show ofString "dst" ≠ ofString "log" by decide, show ofString "dst" ≠ ofString "r" by decide,
                show ofString "dst" ≠ ofString "w" by decide, show ofString "dst" ≠ ofString "tstart" by decide,
                show ofString "dst" ≠ ofString "t" by decide, show ofString "dst" ≠ ofString "nt" by decide,
                show ofString "dst" ≠ ofString "j" by decide,
                show ofString "i" ≠ ofString "dst" by decide, show ofString "q" ≠ ofString "dst" by decide,
                show ofString "w" ≠ ofString "dst" by decide, show ofString "r" ≠ ofString "dst" by decide]
            · simp [PanRunBounded.resVarEq_lookup, s15, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                hs14_loc, s13, hs12_loc, s11, hs10_loc, hs9_p,
                show ofString "p" ≠ ofString "log" by decide, show ofString "p" ≠ ofString "r" by decide,
                show ofString "p" ≠ ofString "w" by decide, show ofString "p" ≠ ofString "tstart" by decide,
                show ofString "p" ≠ ofString "t" by decide, show ofString "p" ≠ ofString "nt" by decide,
                show ofString "p" ≠ ofString "j" by decide,
                show ofString "i" ≠ ofString "p" by decide, show ofString "q" ≠ ofString "p" by decide,
                show ofString "w" ≠ ofString "p" by decide, show ofString "r" ≠ ofString "p" by decide]
            · simp [PanRunBounded.resVarEq_lookup, s15, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                hs14_loc, s13, hs12_loc, s11, hs10_loc, hs9_n,
                show ofString "n" ≠ ofString "log" by decide, show ofString "n" ≠ ofString "r" by decide,
                show ofString "n" ≠ ofString "w" by decide, show ofString "n" ≠ ofString "tstart" by decide,
                show ofString "n" ≠ ofString "t" by decide, show ofString "n" ≠ ofString "nt" by decide,
                show ofString "n" ≠ ofString "j" by decide,
                show ofString "i" ≠ ofString "n" by decide, show ofString "q" ≠ ofString "n" by decide,
                show ofString "w" ≠ ofString "n" by decide, show ofString "r" ≠ ofString "n" by decide]
            · simp [PanRunBounded.resVarEq_lookup, s15, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "q" ≠ ofString "log" by decide, show ofString "q" ≠ ofString "r" by decide,
                show ofString "q" ≠ ofString "w" by decide, show ofString "q" ≠ ofString "tstart" by decide,
                show ofString "q" ≠ ofString "t" by decide, show ofString "q" ≠ ofString "nt" by decide,
                show ofString "q" ≠ ofString "j" by decide,
                show ofString "i" ≠ ofString "q" by decide]
            · simp [PanRunBounded.resVarEq_lookup, s15, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                iw', show ofString "i" ≠ ofString "log" by decide, show ofString "i" ≠ ofString "r" by decide,
                show ofString "i" ≠ ofString "w" by decide, show ofString "i" ≠ ofString "tstart" by decide,
                show ofString "i" ≠ ofString "t" by decide, show ofString "i" ≠ ofString "nt" by decide,
                show ofString "i" ≠ ofString "j" by decide]
  · exact ⟨fun h => False.elim (hne2 h), fun _ => ⟨hnb2, hnc2, hnr2⟩⟩

private theorem elOuterWhile_exact {F : Type}
    (clk : Nat) (s0 s : PanSemStateFiniteExact 64 F)
    (dst0 bound : Nat) (dstw pw nw qw iw : BitVec 64)
    (hclk : s.clock ≤ clk)
    (hA0 : ArenaOK s0) (hma0 : s0.memaddrs = ordinaryDomain)
    (heff0 : HeapByteEff s0 s [(dst0, bound)] ["heap_ptr"])
    (hdst_ge : globN s0 "heap_ptr" ≤ dst0) (hdst_hi : dst0 + bound ≤ heapLimit)
    (hhl_lt : heapLimit < 2 ^ 64)
    (hal_arr : Allocated s0 (pw.toNat, 8 * nw.toNat))
    (hn_lt : nw.toNat < 2 ^ 28)
    (hi_le : iw.toNat ≤ nw.toNat)
    (hq_ge : dst0 + 9 ≤ qw.toNat)
    (hq_le : qw.toNat ≤ dst0 + 9 + logsEncodedSum s0 pw.toNat iw.toNat)
    (hfit_sum : 9 + logsEncodedSum s0 pw.toNat nw.toNat ≤ bound)
    (hentries : ∀ k < nw.toNat,
      WordAt s0 (pw.toNat + 8 * k) ∧
      let log := memW s0 (pw.toNat + 8 * k)
      Allocated s0 (log, 40) ∧
      memW s0 (log + 16) ≤ 4 ∧
      memW s0 (log + 32) < 2 ^ 32 ∧
      WordAt s0 log ∧ WordAt s0 (log + 8) ∧ WordAt s0 (log + 16) ∧
      WordAt s0 (log + 24) ∧ WordAt s0 (log + 32))
    (hl_dst : s.locals.lookup (ofString "dst") = some (.val (.word dstw)))
    (hl_p : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hl_n : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hl_q : s.locals.lookup (ofString "q") = some (.val (.word qw)))
    (hl_i : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hnt : (evaluateHOLFiniteState s elOuterWhile).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s elOuterWhile
    (out.1 = none →
      ∃ qf : BitVec 64,
        dst0 + 9 ≤ qf.toNat ∧
        qf.toNat ≤ dst0 + 9 + logsEncodedSum s0 pw.toNat nw.toNat ∧
        HeapByteEff s out.2 [(dst0, bound)] [] ∧
        out.2.locals.lookup (ofString "dst") = some (.val (.word dstw)) ∧
        out.2.locals.lookup (ofString "q") = some (.val (.word qf))) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  induction clk generalizing s qw iw with
  | zero =>
    intro out; dsimp only [out, elOuterWhile] at hnt ⊢
    rw [evaluateHOLFiniteState_while_total] at hnt ⊢
    have hcond : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .less (ExpHOL.var VarKind.local (ofString "i")) (ExpHOL.var VarKind.local (ofString "n"))) =
        some (.val (.word (if iw.toNat < nw.toNat then 1#64 else 0#64))) := by
      rw [evalHOLFinite_eq_toExact]
      simp only [evalHOLExact, hl_i, hl_n, Compiler.Encoders.Asm.wordCmpHOL,
        holAsmSignedLess_small iw nw (by omega) (by omega), decide_eq_true_eq]
      by_cases hlt : iw.toNat < nw.toNat <;> simp [hlt]
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hlt : iw.toNat < nw.toNat
    · have hz : s.clock = 0 := by omega
      rw [if_pos hlt, if_pos (by decide : (1#64 : BitVec 64) ≠ 0), if_pos hz] at hnt
      exact absurd rfl hnt
    · rw [if_neg hlt, if_neg (by decide : ¬ ((0#64 : BitVec 64) ≠ 0))]
      have hieq : iw.toNat = nw.toNat := by omega
      exact ⟨fun _ => ⟨qw, hq_ge, by rw [← hieq]; exact hq_le, HeapByteEff.refl heff0.arena _ _,
        hl_dst, hl_q⟩,
        fun h => False.elim (h rfl)⟩
  | succ k ih =>
    intro out; dsimp only [out, elOuterWhile] at hnt ⊢
    rw [evaluateHOLFiniteState_while_total] at hnt ⊢
    have hcond : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .less (ExpHOL.var VarKind.local (ofString "i")) (ExpHOL.var VarKind.local (ofString "n"))) =
        some (.val (.word (if iw.toNat < nw.toNat then 1#64 else 0#64))) := by
      rw [evalHOLFinite_eq_toExact]
      simp only [evalHOLExact, hl_i, hl_n, Compiler.Encoders.Asm.wordCmpHOL,
        holAsmSignedLess_small iw nw (by omega) (by omega), decide_eq_true_eq]
      by_cases hlt : iw.toNat < nw.toNat <;> simp [hlt]
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hlt : iw.toNat < nw.toNat
    · rw [if_pos hlt, if_pos (by decide : (1#64 : BitVec 64) ≠ 0)] at hnt ⊢
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hnt; exact absurd rfl hnt
      · rw [if_neg hz] at hnt ⊢
        rw [fixClockHOLFinite_evaluateState] at hnt ⊢
        let sd := decClockHOLFinite s
        have heff_s_sd : HeapByteEff s sd [(dst0, bound)] [] :=
          (HeapByteEff.refl heff0.arena _ _).locals_clock sd.locals sd.clock
        have heff0_sd : HeapByteEff s0 sd [(dst0, bound)] ["heap_ptr"] :=
          heff0.trans (heff_s_sd.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩)
            (fun _ h => False.elim (List.not_mem_nil h)))
        rcases hbody : evaluateHOLFiniteState (decClockHOLFinite s) elOuterBody with ⟨rbody, s_next⟩
        have hnt_b : rbody ≠ some .timeOut := by
          rintro rfl
          simp only [hbody] at hnt
          exact hnt rfl
        have hclk_b := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) elOuterBody
        have hb_res := elOuterBody_exact s0 sd dst0 bound dstw pw nw qw iw
          hA0 hma0 heff0_sd hdst_ge hdst_hi hhl_lt hal_arr hn_lt hlt hq_ge hq_le hfit_sum hentries
          hl_dst hl_p hl_n hl_q hl_i (by change (evaluateHOLFiniteState (decClockHOLFinite s) elOuterBody).1 ≠ _; rw [hbody]; exact hnt_b)
        dsimp only at hb_res
        change ((evaluateHOLFiniteState (decClockHOLFinite s) elOuterBody).1 = none → _) ∧ _ at hb_res
        rw [hbody] at hb_res hclk_b
        simp only [hbody] at hnt ⊢
        cases rbody with
        | some rb =>
          obtain ⟨hnb, hnc, hnr⟩ := hb_res.2 (by simp)
          cases rb with
          | «break» => exact absurd rfl hnb
          | «continue» => exact absurd rfl hnc
          | _ =>
            dsimp only
            exact ⟨fun h => by simp at h, fun _ => hnr⟩
        | none =>
          dsimp only at hnt ⊢
          obtain ⟨q1, hq1_ge, hq1_le, heff_sd_next, hn_dst, hn_p, hn_n, hn_q, hn_i⟩ := hb_res.1 rfl
          have heff_s_next : HeapByteEff s s_next [(dst0, bound)] [] := heff_s_sd.trans heff_sd_next
          have hs_clk : s_next.clock ≤ k := by
            have : s_next.clock ≤ s.clock - 1 := hclk_b
            omega
          have hiw1_nat : (iw + 1#64).toNat = iw.toNat + 1 := by
            rw [BitVec.toNat_add]; change (iw.toNat + 1) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
          have hih := ih s_next q1 (iw + 1#64) hs_clk
            (heff0.trans (heff_s_next.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩)
              (fun _ h => False.elim (List.not_mem_nil h))))
            (by rw [hiw1_nat]; omega) hq1_ge (by rw [hiw1_nat]; exact hq1_le)
            hn_dst hn_p hn_n hn_q hn_i hnt
          dsimp only at hih
          refine ⟨fun hnone => ?_, hih.2⟩
          obtain ⟨qf, hqf1, hqf2, heff_next_f, hf_dst, hf_q⟩ := hih.1 hnone
          exact ⟨qf, hqf1, hqf2, heff_s_next.trans heff_next_f, hf_dst, hf_q⟩
    · rw [if_neg hlt, if_neg (by decide : ¬ ((0#64 : BitVec 64) ≠ 0))]
      have hieq : iw.toNat = nw.toNat := by omega
      exact ⟨fun _ => ⟨qw, hq_ge, by rw [← hieq]; exact hq_le, HeapByteEff.refl heff0.arena _ _,
        hl_dst, hl_q⟩,
        fun h => False.elim (h rfl)⟩

private theorem eval_call_local_encode_logs {F : Type}
    (s0 s : PanSemStateFiniteExact 64 F) (lname : String) (dstExp logsExp : ExpHOL 64)
    (dstw logsw : BitVec 64) (bound : Nat) (Rl : List Ivl) (gw : List String)
    (hA0 : ArenaOK s0) (hma0 : s0.memaddrs = ordinaryDomain)
    (heff0_fresh : HeapByteEff s0 s [(dstw.toNat, bound)] ["heap_ptr"])
    (hdst_ge : globN s0 "heap_ptr" ≤ dstw.toNat) (hdst_hi : dstw.toNat + bound ≤ heapLimit)
    (hhl_lt : heapLimit < 2 ^ 64)
    (hl_nz : logsw.toNat ≠ 0)
    (hLL0 : LogsListOK s0 logsw.toNat)
    (hal_arr0 : Allocated s0 (memW s0 logsw.toNat, 8 * memW s0 (logsw.toNat + 8)))
    (hfit_sum : 9 + logsEncodedSum s0 (memW s0 logsw.toNat) (memW s0 (logsw.toNat + 8)) ≤ bound)
    (hin_Rl : ∃ ivl ∈ Rl, ivl.1 ≤ dstw.toNat ∧ dstw.toNat + bound ≤ ivl.1 + ivl.2)
    (hl_old : ∃ w_old : BitVec 64, s.locals.lookup (ofString lname) = some (.val (.word w_old)))
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dstw)))
    (hlogs : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) logsExp =
      some (.val (.word logsw)))
    (hnt : (evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "encode_logs")
        [dstExp, logsExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "encode_logs")
        [dstExp, logsExp])
    (out.1 = none →
      ∃ tw : BitVec 64,
        tw.toNat ≤ 9 + logsEncodedSum s0 (memW s0 logsw.toNat) (memW s0 (logsw.toNat + 8)) ∧
        out.2.globals = s.globals ∧
        out.2.locals = s.locals.update (ofString lname, .val (.word tw)) ∧
        HeapByteEff s out.2 Rl gw) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  intro out; dsimp only [out]
  obtain ⟨w_old, hw_old⟩ := hl_old
  have hcode : s.code = originalRuntimeCode := heff0_fresh.arena.1.code
  have hAR : ArenaReady s := heff0_fresh.arena
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, logsExp] = some [.val (.word dstw), .val (.word logsw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hlogs]
  have hlk := pan_two_word_lookup s.code.lookup (ofString "encode_logs")
    (ofString "dst") (ofString "logs")
    (sourceFnBody Guest.Software.guestFn_encode_logs) dstw logsw (by decide)
    (by rw [hcode]; exact lookup_encode_logs)
  simp only [ha, hlk] at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set cmap := (HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dstw))).update
      (ofString "logs", ValueHOL.val (.word logsw))
    set ent := callEntryStateHOLFinite s cmap
    have heff_s_ent : HeapByteEff s ent [(dstw.toNat, bound)] [] :=
      (HeapByteEff.refl hAR [(dstw.toNat, bound)] []).locals_clock ent.locals ent.clock
    have heff0_ent : HeapByteEff s0 ent [(dstw.toNat, bound)] ["heap_ptr"] :=
      heff0_fresh.trans (heff_s_ent.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩)
        (fun _ h => False.elim (List.not_mem_nil h)))
    have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dstw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "logs" ≠ ofString "dst" by decide]
    have hent_logs : ent.locals.lookup (ofString "logs") = some (.val (.word logsw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hLL_parts : WordsOK s0 (logsw.toNat, 24) ∧
        Allocated s0 (logsw.toNat, 24) ∧
        Allocated s0 (memW s0 logsw.toNat, 8 * memW s0 (logsw.toNat + 8)) ∧
        logsw.toNat + 24 ≤ 2 ^ 64 ∧
        memW s0 logsw.toNat + 8 * memW s0 (logsw.toNat + 8) ≤ 2 ^ 64 ∧
        memW s0 (logsw.toNat + 8) < 2 ^ 28 ∧
        WordAt s0 logsw.toNat ∧ WordAt s0 (logsw.toNat + 8) ∧
        (∀ i, i < memW s0 (logsw.toNat + 8) →
          WordAt s0 (memW s0 logsw.toNat + 8 * i) ∧
          LogEntryOK s0 (memW s0 (memW s0 logsw.toNat + 8 * i)) ∧
          let log := memW s0 (memW s0 logsw.toNat + 8 * i)
          log + 40 ≤ globN s0 "heap_ptr" ∧
          WordAt s0 log ∧ WordAt s0 (log + 8) ∧ WordAt s0 (log + 16) ∧
          WordAt s0 (log + 24) ∧ WordAt s0 (log + 32)) := by
      rcases hLL0 with h0 | ⟨hw_hdr, hal_hdr, hn_lt, _, hentries⟩
      · exact absurd h0 hl_nz
      have hhdr_b := M13.allocated_le_2pow64 hA0 hal_hdr
      have harr_b := M13.allocated_le_2pow64 hA0 hal_arr0
      have hw0 : WordAt s0 logsw.toNat := by
        have := hw_hdr.2.2 0 (by show 0 < 24 / 8; decide); simpa using this
      have hw8 : WordAt s0 (logsw.toNat + 8) := by
        have := hw_hdr.2.2 1 (by show 1 < 24 / 8; decide); simpa using this
      refine ⟨hw_hdr, hal_hdr, hal_arr0, hhdr_b, harr_b, hn_lt, hw0, hw8, fun i hi => ?_⟩
      obtain ⟨hwa_i, hle_i⟩ := hentries i hi
      set log := memW s0 (memW s0 logsw.toNat + 8 * i)
      have hw_log : WordsOK s0 (log, 40) := hle_i.1
      have hin_log : Inside (log, 40) sourceBase (globN s0 "heap_ptr") := hle_i.2.1
      have hl0 : WordAt s0 log := by have := hw_log.2.2 0 (by show 0 < 40 / 8; decide); simpa using this
      have hl8 : WordAt s0 (log + 8) := by have := hw_log.2.2 1 (by show 1 < 40 / 8; decide); simpa using this
      have hl16 : WordAt s0 (log + 16) := by have := hw_log.2.2 2 (by show 2 < 40 / 8; decide); simpa using this
      have hl24 : WordAt s0 (log + 24) := by have := hw_log.2.2 3 (by show 3 < 40 / 8; decide); simpa using this
      have hl32 : WordAt s0 (log + 32) := by have := hw_log.2.2 4 (by show 4 < 40 / 8; decide); simpa using this
      exact ⟨hwa_i, hle_i, hin_log.2, hl0, hl8, hl16, hl24, hl32⟩
    obtain ⟨_, hal_hdr, hal_arr, hhdr_b, harr_b, hn_lt, hw0, hw8, hentries0⟩ := hLL_parts
    have hlogs8_nat : (logsw + 8#64).toNat = logsw.toNat + 8 := by
      rw [BitVec.toNat_add]; change (logsw.toNat + 8) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
    have hlogs0_nat : (logsw + 0#64).toNat = logsw.toNat := by simp
    have hev_l8_addr : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
        (.op .add [ExpHOL.var VarKind.local (ofString "logs"), .const 8]) =
        some (.val (.word (logsw + 8#64))) := by
      simp [evalHOLExact, evalListHOLExact, hent_logs, wordOpHOL, wordOp, valueIsWord, valueWord]
    have hev_n := load_word_in_allocated_fresh hA0 hma0 heff0_ent hdst_ge hdst_hi hal_hdr
      _ (logsw + 8#64) hev_l8_addr (by rw [hlogs8_nat]; exact hw8)
      (by rw [hlogs8_nat]; dsimp only; omega) (by rw [hlogs8_nat]; dsimp only; omega)
    rw [hlogs8_nat] at hev_n
    let nw : BitVec 64 := BitVec.ofNat 64 (memW s0 (logsw.toNat + 8))
    have hnw_nat : nw.toNat = memW s0 (logsw.toNat + 8) := Nat.mod_eq_of_lt (by omega)
    set e1 := setVarHOLFinite (ofString "n") (.val (.word nw)) ent
    have heff0_e1 : HeapByteEff s0 e1 [(dstw.toNat, bound)] ["heap_ptr"] := heff0_ent.locals_clock e1.locals e1.clock
    have he1_logs : e1.locals.lookup (ofString "logs") = some (.val (.word logsw)) := by
      simp [e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_logs,
        show ofString "n" ≠ ofString "logs" by decide]
    have hev_l0_addr : @evalHOLExact 64 F _ e1.toExact (fun a => Classical.propDecidable (e1.memaddrs a))
        (.op .add [ExpHOL.var VarKind.local (ofString "logs"), .const 0]) =
        some (.val (.word logsw)) := by
      simp [evalHOLExact, evalListHOLExact, he1_logs, wordOpHOL, wordOp, valueIsWord, valueWord]
    have hev_p := load_word_in_allocated_fresh hA0 hma0 heff0_e1 hdst_ge hdst_hi hal_hdr
      _ logsw hev_l0_addr hw0 (by dsimp only; omega) (by dsimp only; omega)
    have hp_lt_264 : memW s0 logsw.toNat < 2 ^ 64 := by
      unfold memW; cases s0.memory (BitVec.ofNat 64 logsw.toNat); exact BitVec.isLt _
    let pw : BitVec 64 := BitVec.ofNat 64 (memW s0 logsw.toNat)
    have hpw_nat : pw.toNat = memW s0 logsw.toNat := Nat.mod_eq_of_lt hp_lt_264
    set e2 := setVarHOLFinite (ofString "p") (.val (.word pw)) e1
    let q0w : BitVec 64 := dstw + 9#64
    have hq0_nat : q0w.toNat = dstw.toNat + 9 := by
      rw [BitVec.toNat_add]; change (dstw.toNat + 9) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
    have he2_dst : e2.locals.lookup (ofString "dst") = some (.val (.word dstw)) := by
      simp [e2, e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_dst,
        show ofString "p" ≠ ofString "dst" by decide, show ofString "n" ≠ ofString "dst" by decide]
    have hev_q0 : @evalHOLExact 64 F _ e2.toExact (fun a => Classical.propDecidable (e2.memaddrs a))
        (.op .add [ExpHOL.var VarKind.local (ofString "dst"), .const 9]) =
        some (.val (.word q0w)) := by
      simp [evalHOLExact, evalListHOLExact, he2_dst, wordOpHOL, wordOp, valueIsWord, valueWord, q0w]
    set e3 := setVarHOLFinite (ofString "q") (.val (.word q0w)) e2
    set e4 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) e3
    have hb_el : sourceFnBody Guest.Software.guestFn_encode_logs =
        (.dec (ofString "n") .one (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "logs"), .const 8]))
          (.dec (ofString "p") .one (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "logs"), .const 0]))
            (.dec (ofString "q") .one (.op .add [ExpHOL.var VarKind.local (ofString "dst"), .const 9])
              (.dec (ofString "i") .one (.const 0)
                (.seq elOuterWhile
                  (.decCall (ofString "total") .one (ofString "rlp_finish_list")
                    [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "q")]
                    (.return (ExpHOL.var VarKind.local (ofString "total"))))))))) := rfl
    have hstep_dec : ∀ (prog_k : ProgHOL 64),
        evaluateHOLFiniteState ent
          (.dec (ofString "n") .one (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "logs"), .const 8]))
            (.dec (ofString "p") .one (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "logs"), .const 0]))
              (.dec (ofString "q") .one (.op .add [ExpHOL.var VarKind.local (ofString "dst"), .const 9])
                (.dec (ofString "i") .one (.const 0) prog_k)))) =
        (let o := evaluateHOLFiniteState e4 prog_k
         (o.1,
          { o.2 with
            locals := HolFiniteMapExact.resVarEq
              (HolFiniteMapExact.resVarEq
                (HolFiniteMapExact.resVarEq
                  (HolFiniteMapExact.resVarEq o.2.locals (ofString "i", e3.locals.lookup (ofString "i")))
                  (ofString "q", e2.locals.lookup (ofString "q")))
                (ofString "p", e1.locals.lookup (ofString "p")))
              (ofString "n", ent.locals.lookup (ofString "n")) })) := by
      intro prog_k
      have h1 : evaluateHOLFiniteState ent
          (.dec (ofString "n") .one (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "logs"), .const 8]))
            (.dec (ofString "p") .one (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "logs"), .const 0]))
              (.dec (ofString "q") .one (.op .add [ExpHOL.var VarKind.local (ofString "dst"), .const 9])
                (.dec (ofString "i") .one (.const 0) prog_k)))) =
        (let o1 := evaluateHOLFiniteState e1
          (.dec (ofString "p") .one (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "logs"), .const 0]))
            (.dec (ofString "q") .one (.op .add [ExpHOL.var VarKind.local (ofString "dst"), .const 9])
              (.dec (ofString "i") .one (.const 0) prog_k)))
         (o1.1, { o1.2 with locals := HolFiniteMapExact.resVarEq o1.2.locals (ofString "n", ent.locals.lookup (ofString "n")) })) := by
        rw [evaluateHOLFiniteState_dec_total]
        simp only [hev_n, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]; rfl
      have h2 : evaluateHOLFiniteState e1
          (.dec (ofString "p") .one (.load .one (.op .add [ExpHOL.var VarKind.local (ofString "logs"), .const 0]))
            (.dec (ofString "q") .one (.op .add [ExpHOL.var VarKind.local (ofString "dst"), .const 9])
              (.dec (ofString "i") .one (.const 0) prog_k))) =
        (let o2 := evaluateHOLFiniteState e2
          (.dec (ofString "q") .one (.op .add [ExpHOL.var VarKind.local (ofString "dst"), .const 9])
            (.dec (ofString "i") .one (.const 0) prog_k))
         (o2.1, { o2.2 with locals := HolFiniteMapExact.resVarEq o2.2.locals (ofString "p", e1.locals.lookup (ofString "p")) })) := by
        rw [evaluateHOLFiniteState_dec_total]
        simp only [hev_p, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]; rfl
      have h3 : evaluateHOLFiniteState e2
          (.dec (ofString "q") .one (.op .add [ExpHOL.var VarKind.local (ofString "dst"), .const 9])
            (.dec (ofString "i") .one (.const 0) prog_k)) =
        (let o3 := evaluateHOLFiniteState e3 (.dec (ofString "i") .one (.const 0) prog_k)
         (o3.1, { o3.2 with locals := HolFiniteMapExact.resVarEq o3.2.locals (ofString "q", e2.locals.lookup (ofString "q")) })) := by
        rw [evaluateHOLFiniteState_dec_total]
        simp only [hev_q0, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]; rfl
      have h4 : evaluateHOLFiniteState e3 (.dec (ofString "i") .one (.const 0) prog_k) =
        (let o4 := evaluateHOLFiniteState e4 prog_k
         (o4.1, { o4.2 with locals := HolFiniteMapExact.resVarEq o4.2.locals (ofString "i", e3.locals.lookup (ofString "i")) })) := by
        rw [evaluateHOLFiniteState_dec_total]
        simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]; rfl
      rw [h1, h2, h3, h4]
    have hnt_ent : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_encode_logs)).1 ≠ some .timeOut := by
      rcases hb : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_encode_logs) with ⟨rb, sb⟩
      rintro rfl; rw [hb] at hnt; exact hnt rfl
    rw [hb_el, hstep_dec] at hnt_ent ⊢
    dsimp only at hnt_ent ⊢
    rw [evaluateHOLFiniteState_seq_line780] at hnt_ent ⊢
    rcases how : evaluateHOLFiniteState e4 elOuterWhile with ⟨row, sw⟩
    have hnt_ow : row ≠ some .timeOut := by rintro rfl; rw [how] at hnt_ent; exact hnt_ent rfl
    have heff0_e4 : HeapByteEff s0 e4 [(dstw.toNat, bound)] ["heap_ptr"] := heff0_ent.locals_clock e4.locals e4.clock
    have how_res := elOuterWhile_exact e4.clock s0 e4 dstw.toNat bound dstw pw nw q0w 0#64
      le_rfl hA0 hma0 heff0_e4 hdst_ge hdst_hi hhl_lt
      (by rw [hpw_nat, hnw_nat]; exact hal_arr)
      (by rw [hnw_nat]; exact hn_lt)
      (by simp)
      (by rw [hq0_nat])
      (by rw [hq0_nat]; simp [logsEncodedSum])
      (by rw [hpw_nat, hnw_nat]; exact hfit_sum)
      (fun k hk => by
        rw [hnw_nat] at hk
        rw [hpw_nat]
        obtain ⟨hwa_k, hle_k, _, hl0_k, hl8_k, hl16_k, hl24_k, hl32_k⟩ := hentries0 k hk
        exact ⟨hwa_k, Or.inl hle_k.2.1, hle_k.2.2.1, hle_k.2.2.2.1, hl0_k, hl8_k, hl16_k, hl24_k, hl32_k⟩)
      (by simp [e4, e3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, he2_dst,
            show ofString "i" ≠ ofString "dst" by decide, show ofString "q" ≠ ofString "dst" by decide])
      (by simp [e4, e3, e2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "i" ≠ ofString "p" by decide, show ofString "q" ≠ ofString "p" by decide])
      (by simp [e4, e3, e2, e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "i" ≠ ofString "n" by decide, show ofString "q" ≠ ofString "n" by decide,
            show ofString "p" ≠ ofString "n" by decide])
      (by simp [e4, e3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "i" ≠ ofString "q" by decide])
      (by simp [e4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      (by rw [how]; exact hnt_ow)
    have hnbc_ow := while_no_break_continue e4
      (.cmp .less (ExpHOL.var VarKind.local (ofString "i")) (ExpHOL.var VarKind.local (ofString "n"))) elOuterBody
    have how' : evaluateHOLFiniteState e4 (.while (.cmp .less (ExpHOL.var VarKind.local (ofString "i")) (ExpHOL.var VarKind.local (ofString "n"))) elOuterBody) = (row, sw) := how
    dsimp only at how_res; rw [how] at how_res; rw [how'] at hnbc_ow
    simp only [how, how'] at hnt_ent hnt ⊢
    cases row with
    | some r_ow =>
      have hnr := how_res.2 (by simp)
      cases r_ow with
      | timeOut => exact absurd rfl hnt_ow
      | «break» => exact absurd rfl hnbc_ow.1
      | «continue» => exact absurd rfl hnbc_ow.2
      | returned rv =>
        exact False.elim (hnr (Or.inl ⟨rv, rfl⟩))
      | exception eid ev =>
        exact ⟨fun h => by simp at h, fun _ => hnr⟩
      | error => exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
      | finalFfi _ =>
        exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
    | none =>
      dsimp only at hnt_ent hnt ⊢
      obtain ⟨qf, hqf_ge, hqf_le, heff_e4_sw, hsw_dst, hsw_q⟩ := how_res.1 rfl
      dsimp only at heff_e4_sw hsw_dst hsw_q
      have hhl_he : heapLimit ≤ heapEnd := by rw [heapLimit_val, heapEnd_val]; decide
      -- Now decCall "total" .one "rlp_finish_list" [dst, q] (return total)
      by_cases hres_fl : Resumes (evaluateHOLFiniteState sw
          (.decCall (ofString "total") .one (ofString "rlp_finish_list")
            [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "q")]
            (.return (ExpHOL.var VarKind.local (ofString "total"))))).1
      · obtain ⟨tw, mid_fl, htw_eq, htw_le_diff, hmid_g, hmid_loc, heff_sw_mid, _, _, hfl_eq⟩ :=
          eval_decCall_rlp_finish_list sw "total"
            (ExpHOL.var VarKind.local (ofString "dst")) (ExpHOL.var VarKind.local (ofString "q"))
            dstw qf (.return (ExpHOL.var VarKind.local (ofString "total")))
            [(dstw.toNat, bound)] [] heff_e4_sw.arena.1.code heff_e4_sw.arena
            (by simp [evalHOLExact, hsw_dst]) (by simp [evalHOLExact, hsw_q])
            hqf_ge (by rw [hpw_nat, hnw_nat] at hqf_le; omega)
            ⟨(dstw.toNat, bound), List.mem_singleton.mpr rfl, le_rfl,
              by rw [hpw_nat, hnw_nat] at hqf_le; dsimp only; omega⟩
            hnt_ent hres_fl
        have hmid_tot : mid_fl.locals.lookup (ofString "total") = some (.val (.word tw)) := by
          rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        have hret_mid : evaluateHOLFiniteState mid_fl (.return (ExpHOL.var VarKind.local (ofString "total"))) =
            (some (.returned (.val (.word tw))), mid_fl.emptyLocalsHOLFinite) := by
          rw [evaluateHOLFiniteState_return]
          have hev_tot : @evalHOLExact 64 F _ mid_fl.toExact
              (fun a => Classical.propDecidable (mid_fl.memaddrs a))
              (ExpHOL.var VarKind.local (ofString "total")) = some (.val (.word tw)) := by
            simp [evalHOLExact, hmid_tot]
          rw [hev_tot]; dsimp only
          rw [if_pos (by simp [shapeOfHOLExact] : sizeOfShapeWithContextHOL mid_fl.structs (shapeOfHOLExact (.val (.word tw) : ValueHOL 64)) ≤ 32)]
        rw [hfl_eq, hret_mid]
        dsimp only
        have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word tw) : ValueHOL 64)) .one = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        have hval : isValidValueHOLExact s.toExact VarKind.local (ofString lname) (.val (.word tw)) = true := by
          simp [isValidValueHOLExact, lookupKvarHOLExact, hw_old, shapeOfHOLExact, shapeEqHOL]
        rw [if_pos hsh, if_pos hval]
        let out_st := setVarHOLFinite (ofString lname) (.val (.word tw))
          { mid_fl.emptyLocalsHOLFinite with locals := s.locals }
        have heff_s_e4 : HeapByteEff s e4 [(dstw.toNat, bound)] [] :=
          heff_s_ent.locals_clock e4.locals e4.clock
        have heff_s_out0 : HeapByteEff s out_st [(dstw.toNat, bound)] [] :=
          ((heff_s_e4.trans heff_e4_sw).trans heff_sw_mid).locals_clock out_st.locals out_st.clock
        have heff_s_out : HeapByteEff s out_st Rl gw :=
          heff_s_out0.mono
            (fun i hi _ => by
              simp only [List.mem_singleton] at hi; subst hi
              obtain ⟨ivl, hivl, h1, h2⟩ := hin_Rl
              exact Or.inl ⟨ivl, hivl, h1, h2⟩)
            (fun _ h => False.elim (List.not_mem_nil h))
        have hg_eq : out_st.globals = s.globals := by
          apply HolFiniteMapExact.ext_lookup
          intro k
          exact (heff_s_out0.globals k (by simp)).symm
        have htw_bound : tw.toNat ≤ 9 + logsEncodedSum s0 (memW s0 logsw.toNat) (memW s0 (logsw.toNat + 8)) := by
          rw [hpw_nat, hnw_nat] at hqf_le; omega
        exact ⟨fun _ => ⟨tw, htw_bound, hg_eq, rfl, heff_s_out⟩, fun h => False.elim (h rfl)⟩
      · rcases hfl_r : evaluateHOLFiniteState sw
            (.decCall (ofString "total") .one (ofString "rlp_finish_list")
              [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "q")]
              (.return (ExpHOL.var VarKind.local (ofString "total")))) with ⟨rfl_res, sfl⟩
        simp only [hfl_r] at hnt_ent hres_fl ⊢
        cases rfl_res with
        | none => exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
        | some r' =>
          cases r' with
          | timeOut => exact absurd rfl hnt_ent
          | returned rv => exact False.elim (hres_fl (Or.inl ⟨rv, rfl⟩))
          | exception eid ev => exact ⟨fun h => by simp at h, fun _ => hres_fl⟩
          | «break» | «continue» | error => exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
          | finalFfi _ =>
            exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

/-! ## Section 6: `wk_encode_receipt` -/

/-- `encode_receipt` (AST line 32051): relational world step with output region and extra `RetReceiptBounded`. -/
theorem «wk_encode_receipt» :
    WorldKeeps ((fun s => WorldOK s ∧ LogsListOK s (locN s "logs") ∧ LogsDisjFixed s (locN s "logs"))) (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    RetReceiptBounded (ofString "encode_receipt") := by
  refine ⟨_, _, _, lookup_encode_receipt, fun {F} s hcode ⟨hW, hLL, hDF⟩ hparams hnt hres => ?_⟩
  have hAR : ArenaReady s := hW.1
  have hA0 : ArenaOK s := hAR.2
  have hma0 : s.memaddrs = ordinaryDomain := hAR.1.memaddrs
  have hhl_lt : heapLimit < 2 ^ 64 := by rw [heapLimit_val]; decide
  have hhl_261 : heapLimit < 2 ^ 61 := by rw [heapLimit_val]; decide
  have hhe_lt : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  have hhl_he : heapLimit ≤ heapEnd := by rw [heapLimit_val, heapEnd_val]; decide
  have hsb_pos : 0 < sourceBase := by rw [sourceBase_val]; decide
  obtain ⟨vals, hl_args⟩ := hparams
  obtain ⟨txType0, succ0, cgas0, logs0, _, htx, hsucc, hcgas, hlogs⟩ :=
    lookupCode_four_words (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      lookup_encode_receipt hl_args
  have hlogs_locN : locN s "logs" = logs0.toNat := by simp [locN, hlogs]
  rw [hlogs_locN] at hLL hDF
  let R0 : List Ivl := receiptKeccakIvls s
  suffices hmain :
      HeapByteEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_encode_receipt)).2
        R0 ["heap_ptr"] ∧
      (∀ v, (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_encode_receipt)).1 =
          some (.returned v) →
        ∃ a b : BitVec 64,
          v = .rStruct [.val (.word a), .val (.word b)] ∧
          Inside (a.toNat, b.toNat) sourceBase
            (globN (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_encode_receipt)).2 "heap_ptr") ∧
          a.toNat < 2 ^ 61 ∧ b.toNat < 2 ^ 61 ∧
          memW (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_encode_receipt)).2 (locN s "logs" + 8) < 2 ^ 28 ∧
          LogsListOK (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_encode_receipt)).2 (locN s "logs")) by
    have heff_ws : HeapByteEff s
        (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_encode_receipt)).2
        (receiptKeccakIvls s ++ ([] : List (String × Nat)).map (bufferRegion s)) ["heap_ptr"] := by
      simpa using hmain.1
    exact HeapByteEff.to_worldStep
      (R := fun t => [(globN t "keccak_pad", if globN t "keccak_pad" = 0 then 0 else 136),
                      (globN t "keccak_st", if globN t "keccak_st" = 0 then 0 else 200)])
      (B := [])
      (by intro _ h; cases h)
      (by intro g hg; simp at hg; exact Or.inl hg)
      hW heff_ws (fun _ _ _ _ _ v hv => hmain.2 v hv)
  -- Unfold `guestFn_encode_receipt`
  have hb_er : sourceFnBody Guest.Software.guestFn_encode_receipt =
      .decCall (ofString "bound") .one (ofString "logs_encoded_bound") [ExpHOL.var VarKind.local (ofString "logs")]
        (.decCall (ofString "buf") .one (ofString "alloc")
          [.op .add [ExpHOL.var VarKind.local (ofString "bound"), .const 400]]
          (.dec (ofString "start") .one (.op .add [ExpHOL.var VarKind.local (ofString "buf"), .const 1])
            (.dec (ofString "p") .one (.op .add [ExpHOL.var VarKind.local (ofString "start"), .const 9])
              (.dec (ofString "w") .one (.const 0)
                (.seq
                  (.ite (.cmp .notEqual (ExpHOL.var VarKind.local (ofString "succeeded")) (.const 0))
                    (.seq (.storeByte (ExpHOL.var VarKind.local (ofString "p")) (.const 1))
                      (.assign VarKind.local (ofString "w") (.const 1)))
                    (.seq (.storeByte (ExpHOL.var VarKind.local (ofString "p")) (.const 128))
                      (.assign VarKind.local (ofString "w") (.const 1))))
                  (.seq
                    (.assign VarKind.local (ofString "p")
                      (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")]))
                    (.seq
                      (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
                        [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "cumulative_gas")])
                      (.seq
                        (.assign VarKind.local (ofString "p")
                          (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")]))
                        (.decCall (ofString "bloom") .one (ofString "alloc") [.const 256]
                          (.seq
                            (.call (some (none, none)) (ofString "logs_bloom")
                              [ExpHOL.var VarKind.local (ofString "logs"), ExpHOL.var VarKind.local (ofString "bloom")])
                            (.seq
                              (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
                                [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "bloom"), .const 256])
                              (.seq
                                (.assign VarKind.local (ofString "p")
                                  (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")]))
                                (.seq
                                  (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "encode_logs")
                                    [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "logs")])
                                  (.seq
                                    (.assign VarKind.local (ofString "p")
                                      (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")]))
                                    (.seq
                                      (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_finish_list")
                                        [ExpHOL.var VarKind.local (ofString "start"), ExpHOL.var VarKind.local (ofString "p")])
                                      (.seq
                                        (.ite (.cmp .notEqual (ExpHOL.var VarKind.local (ofString "tx_type")) (.const 0))
                                          (.seq
                                            (.storeByte (.op .sub [ExpHOL.var VarKind.local (ofString "start"), .const 1])
                                              (ExpHOL.var VarKind.local (ofString "tx_type")))
                                            (.return (.rstruct
                                              [.op .sub [ExpHOL.var VarKind.local (ofString "start"), .const 1],
                                               .op .add [ExpHOL.var VarKind.local (ofString "w"), .const 1]])))
                                          .skip)
                                        (.return (.rstruct
                                          [ExpHOL.var VarKind.local (ofString "start"),
                                           ExpHOL.var VarKind.local (ofString "w")])))))))))))))))))) := rfl
  rw [hb_er] at hnt hres ⊢
  -- Step 1: `decCall "bound" .one "logs_encoded_bound" [logs]`
  obtain ⟨hl_nz, boundw, m1, hbound_eq, hbound_261, hm1_g, hm1_m, hm1_loc, heff_s_m1, hnt1, hres1, heq1⟩ :=
    eval_decCall_logs_encoded_bound s logs0 _ R0 ["heap_ptr"] hcode hAR hlogs hLL hDF hnt hres
  rw [heq1]; dsimp only
  -- Step 2: `decCall "buf" .one "alloc" [bound + 400]`
  obtain ⟨bufw, n_alloc, hp1, m2, hn_alloc_ev, hbuf_hp, hbuf8, hhp1_eq, hbuf_fit, hhp1_hi, hhp1_8,
      hm2_hp, hm2_g, hm2_m, hm2_loc, heff_m1_m2, hnt2, hres2, heq2⟩ :=
    eval_decCall_alloc_resumes m1 "buf"
      (.op .add [ExpHOL.var VarKind.local (ofString "bound"), .const 400]) _ R0 ["heap_ptr"]
      heff_s_m1.arena.1.code heff_s_m1.arena (by simp) hnt1 hres1
  rw [heq2]; dsimp only
  have hm1_bound : m1.locals.lookup (ofString "bound") = some (.val (.word boundw)) := by
    rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hn_alloc_val : n_alloc = boundw + 400#64 := by
    simp [evalHOLExact, evalListHOLExact, hm1_bound, wordOpHOL, wordOp, valueIsWord, valueWord] at hn_alloc_ev
    exact hn_alloc_ev.symm
  have hn_alloc_nat : n_alloc.toNat = boundw.toNat + 400 := by
    rw [hn_alloc_val, BitVec.toNat_add]
    change (boundw.toNat + 400) % 2 ^ 64 = _
    exact Nat.mod_eq_of_lt (by omega)
  have hbuf_hp0 : bufw.toNat = globN s "heap_ptr" := by
    rw [hbuf_hp]; unfold globN; rw [hm1_g]
  have hbuf_lo : sourceBase ≤ bufw.toNat := by
    rw [hbuf_hp0]; exact hA0.1
  have hbuf_end_hp1 : bufw.toNat + (boundw.toNat + 400) ≤ hp1.toNat := by
    rw [← hn_alloc_nat]; exact hbuf_fit
  -- Local lookups in `m2`
  have hm2_buf : m2.locals.lookup (ofString "buf") = some (.val (.word bufw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hm2_tx : m2.locals.lookup (ofString "tx_type") = some (.val (.word txType0)) := by
    rw [hm2_loc, hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, htx,
      show ofString "buf" ≠ ofString "tx_type" by decide,
      show ofString "bound" ≠ ofString "tx_type" by decide]
  have hm2_succ : m2.locals.lookup (ofString "succeeded") = some (.val (.word succ0)) := by
    rw [hm2_loc, hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hsucc,
      show ofString "buf" ≠ ofString "succeeded" by decide,
      show ofString "bound" ≠ ofString "succeeded" by decide]
  have hm2_cgas : m2.locals.lookup (ofString "cumulative_gas") = some (.val (.word cgas0)) := by
    rw [hm2_loc, hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hcgas,
      show ofString "buf" ≠ ofString "cumulative_gas" by decide,
      show ofString "bound" ≠ ofString "cumulative_gas" by decide]
  have hm2_logs : m2.locals.lookup (ofString "logs") = some (.val (.word logs0)) := by
    rw [hm2_loc, hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hlogs,
      show ofString "buf" ≠ ofString "logs" by decide,
      show ofString "bound" ≠ ofString "logs" by decide]
  -- Step 3: `dec "start" = buf + 1`, `dec "p" = start + 9`, `dec "w" = 0`
  let startw : BitVec 64 := bufw + 1#64
  have hstart_nat : startw.toNat = bufw.toNat + 1 := by
    change (bufw + 1#64).toNat = bufw.toNat + 1
    rw [BitVec.toNat_add]; change (bufw.toNat + 1) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
  let p0w : BitVec 64 := startw + 9#64
  have hp0_nat : p0w.toNat = bufw.toNat + 10 := by
    change (startw + 9#64).toNat = bufw.toNat + 10
    rw [BitVec.toNat_add, hstart_nat]; change (bufw.toNat + 1 + 9) % 2 ^ 64 = _
    exact Nat.mod_eq_of_lt (by omega)
  have hev_start : @evalHOLExact 64 F _ m2.toExact (fun a => Classical.propDecidable (m2.memaddrs a))
      (.op .add [ExpHOL.var VarKind.local (ofString "buf"), .const 1]) = some (.val (.word startw)) := by
    simp [evalHOLExact, evalListHOLExact, hm2_buf, wordOpHOL, wordOp, valueIsWord, valueWord, startw]
  set d1 := setVarHOLFinite (ofString "start") (.val (.word startw)) m2
  have hd1_start : d1.locals.lookup (ofString "start") = some (.val (.word startw)) := by
    simp [d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hev_p0 : @evalHOLExact 64 F _ d1.toExact (fun a => Classical.propDecidable (d1.memaddrs a))
      (.op .add [ExpHOL.var VarKind.local (ofString "start"), .const 9]) = some (.val (.word p0w)) := by
    simp [evalHOLExact, evalListHOLExact, hd1_start, wordOpHOL, wordOp, valueIsWord, valueWord, p0w]
  set d2 := setVarHOLFinite (ofString "p") (.val (.word p0w)) d1
  set d3 := setVarHOLFinite (ofString "w") (.val (.word 0#64)) d2
  have hstep_decs : ∀ (prog_k : ProgHOL 64),
      evaluateHOLFiniteState m2
        (.dec (ofString "start") .one (.op .add [ExpHOL.var VarKind.local (ofString "buf"), .const 1])
          (.dec (ofString "p") .one (.op .add [ExpHOL.var VarKind.local (ofString "start"), .const 9])
            (.dec (ofString "w") .one (.const 0) prog_k))) =
      (let o := evaluateHOLFiniteState d3 prog_k
       (o.1,
        { o.2 with
          locals := HolFiniteMapExact.resVarEq
            (HolFiniteMapExact.resVarEq
              (HolFiniteMapExact.resVarEq o.2.locals (ofString "w", d2.locals.lookup (ofString "w")))
              (ofString "p", d1.locals.lookup (ofString "p")))
            (ofString "start", m2.locals.lookup (ofString "start")) })) := by
    intro prog_k
    have hs1 : evaluateHOLFiniteState m2
        (.dec (ofString "start") .one (.op .add [ExpHOL.var VarKind.local (ofString "buf"), .const 1])
          (.dec (ofString "p") .one (.op .add [ExpHOL.var VarKind.local (ofString "start"), .const 9])
            (.dec (ofString "w") .one (.const 0) prog_k))) =
      (let o1 := evaluateHOLFiniteState d1
        (.dec (ofString "p") .one (.op .add [ExpHOL.var VarKind.local (ofString "start"), .const 9])
          (.dec (ofString "w") .one (.const 0) prog_k))
       (o1.1, { o1.2 with locals := HolFiniteMapExact.resVarEq o1.2.locals (ofString "start", m2.locals.lookup (ofString "start")) })) := by
      rw [evaluateHOLFiniteState_dec_total]; simp only [hev_start, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]; rfl
    have hs2 : evaluateHOLFiniteState d1
        (.dec (ofString "p") .one (.op .add [ExpHOL.var VarKind.local (ofString "start"), .const 9])
          (.dec (ofString "w") .one (.const 0) prog_k)) =
      (let o2 := evaluateHOLFiniteState d2 (.dec (ofString "w") .one (.const 0) prog_k)
       (o2.1, { o2.2 with locals := HolFiniteMapExact.resVarEq o2.2.locals (ofString "p", d1.locals.lookup (ofString "p")) })) := by
      rw [evaluateHOLFiniteState_dec_total]; simp only [hev_p0, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]; rfl
    have hs3 : evaluateHOLFiniteState d2 (.dec (ofString "w") .one (.const 0) prog_k) =
      (let o3 := evaluateHOLFiniteState d3 prog_k
       (o3.1, { o3.2 with locals := HolFiniteMapExact.resVarEq o3.2.locals (ofString "w", d2.locals.lookup (ofString "w")) })) := by
      rw [evaluateHOLFiniteState_dec_total]; simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]; rfl
    rw [hs1, hs2, hs3]
  let erBodyProg : ProgHOL 64 :=
    .seq
      (.ite (.cmp .notEqual (ExpHOL.var VarKind.local (ofString "succeeded")) (.const 0))
        (.seq (.storeByte (ExpHOL.var VarKind.local (ofString "p")) (.const 1))
          (.assign VarKind.local (ofString "w") (.const 1)))
        (.seq (.storeByte (ExpHOL.var VarKind.local (ofString "p")) (.const 128))
          (.assign VarKind.local (ofString "w") (.const 1))))
      (.seq
        (.assign VarKind.local (ofString "p")
          (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")]))
        (.seq
          (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
            [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "cumulative_gas")])
          (.seq
            (.assign VarKind.local (ofString "p")
              (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")]))
            (.decCall (ofString "bloom") .one (ofString "alloc") [.const 256]
              (.seq
                (.call (some (none, none)) (ofString "logs_bloom")
                  [ExpHOL.var VarKind.local (ofString "logs"), ExpHOL.var VarKind.local (ofString "bloom")])
                (.seq
                  (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
                    [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "bloom"), .const 256])
                  (.seq
                    (.assign VarKind.local (ofString "p")
                      (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")]))
                    (.seq
                      (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "encode_logs")
                        [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "logs")])
                      (.seq
                        (.assign VarKind.local (ofString "p")
                          (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")]))
                        (.seq
                          (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_finish_list")
                            [ExpHOL.var VarKind.local (ofString "start"), ExpHOL.var VarKind.local (ofString "p")])
                          (.seq
                            (.ite (.cmp .notEqual (ExpHOL.var VarKind.local (ofString "tx_type")) (.const 0))
                              (.seq
                                (.storeByte (.op .sub [ExpHOL.var VarKind.local (ofString "start"), .const 1])
                                  (ExpHOL.var VarKind.local (ofString "tx_type")))
                                (.return (.rstruct
                                  [.op .sub [ExpHOL.var VarKind.local (ofString "start"), .const 1],
                                   .op .add [ExpHOL.var VarKind.local (ofString "w"), .const 1]])))
                              .skip)
                            (.return (.rstruct
                              [ExpHOL.var VarKind.local (ofString "start"),
                               ExpHOL.var VarKind.local (ofString "w")])))))))))))))
  rw [hstep_decs erBodyProg] at hnt2 hres2 ⊢
  dsimp only at hnt2 hres2 ⊢
  let bufIvl : Ivl := (bufw.toNat, boundw.toNat + 400)
  have heff_s_d3 : HeapByteEff s d3 R0 ["heap_ptr"] :=
    (heff_s_m1.trans heff_m1_m2).locals_clock d3.locals d3.clock
  suffices hd3 :
      HeapByteEff s (evaluateHOLFiniteState d3 erBodyProg).2 R0 ["heap_ptr"] ∧
      (∀ v, (evaluateHOLFiniteState d3 erBodyProg).1 = some (.returned v) →
        ∃ a b : BitVec 64,
          v = .rStruct [.val (.word a), .val (.word b)] ∧
          Inside (a.toNat, b.toNat) sourceBase
            (globN (evaluateHOLFiniteState d3 erBodyProg).2 "heap_ptr") ∧
          a.toNat < 2 ^ 61 ∧ b.toNat < 2 ^ 61) by
    let post0 := (evaluateHOLFiniteState d3 erBodyProg).2
    let post1 : PanSemStateFiniteExact 64 F :=
      { post0 with
        locals := HolFiniteMapExact.resVarEq
          (HolFiniteMapExact.resVarEq
            (HolFiniteMapExact.resVarEq post0.locals (ofString "w", d2.locals.lookup (ofString "w")))
            (ofString "p", d1.locals.lookup (ofString "p")))
          (ofString "start", m2.locals.lookup (ofString "start")) }
    let post2 : PanSemStateFiniteExact 64 F :=
      { post1 with locals := HolFiniteMapExact.resVarEq post1.locals (ofString "buf", m1.locals.lookup (ofString "buf")) }
    let post3 : PanSemStateFiniteExact 64 F :=
      { post2 with locals := HolFiniteMapExact.resVarEq post2.locals (ofString "bound", s.locals.lookup (ofString "bound")) }
    have heff_post3 : HeapByteEff s post3 R0 ["heap_ptr"] :=
      ((hd3.1.locals_clock post1.locals post1.clock).locals_clock post2.locals post2.clock).locals_clock post3.locals post3.clock
    refine ⟨heff_post3, fun v hv => ?_⟩
    obtain ⟨a, b, rfl, hin, ha261, hb261⟩ := hd3.2 v hv
    have hLL_post := logsListOK_preserved hA0 hma0 heff_post3 hl_nz hLL hDF
    refine ⟨a, b, rfl, hin, ha261, hb261, ?_, ?_⟩
    · rw [hlogs_locN]; exact hLL_post.1
    · rw [hlogs_locN]; exact hLL_post.2
  dsimp only [erBodyProg] at hnt2 hres2 ⊢
  have hd3_start : d3.locals.lookup (ofString "start") = some (.val (.word startw)) := by
    simp [d3, d2, d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "w" ≠ ofString "start" by decide,
      show ofString "p" ≠ ofString "start" by decide]
  have hd3_p : d3.locals.lookup (ofString "p") = some (.val (.word p0w)) := by
    simp [d3, d2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "w" ≠ ofString "p" by decide]
  have hd3_w : d3.locals.lookup (ofString "w") = some (.val (.word 0#64)) := by
    simp [d3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hd3_tx : d3.locals.lookup (ofString "tx_type") = some (.val (.word txType0)) := by
    simp [d3, d2, d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm2_tx,
      show ofString "w" ≠ ofString "tx_type" by decide,
      show ofString "p" ≠ ofString "tx_type" by decide,
      show ofString "start" ≠ ofString "tx_type" by decide]
  have hd3_succ : d3.locals.lookup (ofString "succeeded") = some (.val (.word succ0)) := by
    simp [d3, d2, d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm2_succ,
      show ofString "w" ≠ ofString "succeeded" by decide,
      show ofString "p" ≠ ofString "succeeded" by decide,
      show ofString "start" ≠ ofString "succeeded" by decide]
  have hd3_cgas : d3.locals.lookup (ofString "cumulative_gas") = some (.val (.word cgas0)) := by
    simp [d3, d2, d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm2_cgas,
      show ofString "w" ≠ ofString "cumulative_gas" by decide,
      show ofString "p" ≠ ofString "cumulative_gas" by decide,
      show ofString "start" ≠ ofString "cumulative_gas" by decide]
  have hd3_logs : d3.locals.lookup (ofString "logs") = some (.val (.word logs0)) := by
    simp [d3, d2, d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm2_logs,
      show ofString "w" ≠ ofString "logs" by decide,
      show ofString "p" ≠ ofString "logs" by decide,
      show ofString "start" ≠ ofString "logs" by decide]
  have hstep_buf_trans : ∀ {cur nxt : PanSemStateFiniteExact 64 F},
      HeapByteEff s cur R0 ["heap_ptr"] →
      HeapByteEff cur nxt [bufIvl] ["heap_ptr"] →
      HeapByteEff s nxt R0 ["heap_ptr"] := by
    intro cur nxt hsc hcn
    have h1 : HeapByteEff s cur (bufIvl :: R0) ["heap_ptr"] :=
      hsc.mono (fun i hi _ => Or.inl ⟨i, List.mem_cons_of_mem _ hi, le_rfl, le_rfl⟩) (fun _ h => h)
    have h2 : HeapByteEff cur nxt (bufIvl :: R0) ["heap_ptr"] :=
      hcn.mono (fun i hi _ => by simp at hi; subst hi; exact Or.inl ⟨bufIvl, List.mem_cons_self, le_rfl, le_rfl⟩)
        (fun _ h => h)
    exact (h1.trans h2).mono
      (fun i hi _ => by
        rcases List.mem_cons.1 hi with rfl | hR0
        · exact Or.inr (Or.inr ⟨by dsimp [bufIvl]; rw [← hbuf_hp0], by dsimp [bufIvl]; omega⟩)
        · exact Or.inl ⟨i, hR0, le_rfl, le_rfl⟩)
      (fun _ h => h)
  -- Step 4: `ite (succeeded != 0) (storeByte p 1; w := 1) (storeByte p 128; w := 1)`
  have hstep4 : ∃ d4 : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState d3
        (.ite (.cmp .notEqual (ExpHOL.var VarKind.local (ofString "succeeded")) (.const 0))
          (.seq (.storeByte (ExpHOL.var VarKind.local (ofString "p")) (.const 1))
            (.assign VarKind.local (ofString "w") (.const 1)))
          (.seq (.storeByte (ExpHOL.var VarKind.local (ofString "p")) (.const 128))
            (.assign VarKind.local (ofString "w") (.const 1)))) = (none, d4) ∧
      HeapByteEff d3 d4 [bufIvl] ["heap_ptr"] ∧
      d4.locals = d3.locals.update (ofString "w", .val (.word 1#64)) := by
    let sb_val : ExpHOL 64 := if succ0 ≠ 0#64 then .const 1 else .const 128
    have hite_eq : evaluateHOLFiniteState d3
        (.ite (.cmp .notEqual (ExpHOL.var VarKind.local (ofString "succeeded")) (.const 0))
          (.seq (.storeByte (ExpHOL.var VarKind.local (ofString "p")) (.const 1))
            (.assign VarKind.local (ofString "w") (.const 1)))
          (.seq (.storeByte (ExpHOL.var VarKind.local (ofString "p")) (.const 128))
            (.assign VarKind.local (ofString "w") (.const 1)))) =
      evaluateHOLFiniteState d3
        (.seq (.storeByte (ExpHOL.var VarKind.local (ofString "p")) sb_val)
          (.assign VarKind.local (ofString "w") (.const 1))) := by
      rw [evaluateHOLFiniteState_ite]
      have hcond : @evalHOLExact 64 F _ d3.toExact (fun a => Classical.propDecidable (d3.memaddrs a))
          (.cmp .notEqual (ExpHOL.var VarKind.local (ofString "succeeded")) (.const 0)) =
          some (.val (.word (if succ0 ≠ 0#64 then 1#64 else 0#64))) := by
        simp only [evalHOLExact, hd3_succ, Compiler.Encoders.Asm.wordCmpHOL]
        by_cases hsz : succ0 = 0#64 <;> simp [hsz]
      rw [hcond]; dsimp only
      by_cases hsz : succ0 = 0#64
      · simp [hsz, sb_val]
      · simp [hsz, sb_val]
    rw [hite_eq]
    have hsb_eff := (R13Shards.Keccak256.byteEff_storeByte (Rl := [bufIvl]) heff_s_d3.arena.1
      (ExpHOL.var VarKind.local (ofString "p")) sb_val
      (fun x hx _ => by
        simp [evalHOLExact, hd3_p] at hx; subst hx
        exact ⟨bufIvl, List.mem_singleton.mpr rfl, by dsimp [bufIvl]; omega, by dsimp [bufIvl]; omega⟩)).1
    have hsb_val_ev : ∃ vb : BitVec 64,
        @evalHOLExact 64 F _ d3.toExact (fun a => Classical.propDecidable (d3.memaddrs a)) sb_val =
          some (.val (.word vb)) := by
      by_cases hsz : succ0 = 0#64
      · exact ⟨128#64, by simp [sb_val, hsz, evalHOLExact]⟩
      · exact ⟨1#64, by simp [sb_val, hsz, evalHOLExact]⟩
    obtain ⟨vb, hvb_ev⟩ := hsb_val_ev
    have hp0_in_dom : d3.memaddrs (panByteAlignHOL p0w) := by
      rw [heff_s_d3.memaddrs, hma0, ordinaryDomain_iff]
      refine ⟨by rw [panByteAlign_toNat64]; omega, ?_, ?_⟩
      · rw [panByteAlign_toNat64]; omega
      · rw [panByteAlign_toNat64]; omega
    have hsb_exact : ∃ d3_sb : PanSemStateFiniteExact 64 F,
        evaluateHOLFiniteState d3 (.storeByte (ExpHOL.var VarKind.local (ofString "p")) sb_val) = (none, d3_sb) ∧
        d3_sb.locals = d3.locals := by
      rw [evaluateHOLFiniteState_storeByte]
      have hp_evf : @evalHOLExact 64 F _ d3.toExact (fun a => Classical.propDecidable (d3.memaddrs a))
          (ExpHOL.var VarKind.local (ofString "p")) = some (.val (.word p0w)) := hd3_p
      rw [hp_evf, hvb_ev]; dsimp only
      unfold panMemStoreByteWord8HOL; dsimp only
      cases hm_cell : d3.memory (panByteAlignHOL p0w) with
      | word cell =>
        rw [if_pos hp0_in_dom]; dsimp only
        exact ⟨_, rfl, rfl⟩
    obtain ⟨d3_sb, hsb_r, hd3_sb_loc⟩ := hsb_exact
    rw [hsb_r] at hsb_eff
    rw [evaluateHOLFiniteState_seq_line780, hsb_r]; dsimp only
    rw [evaluateHOLFiniteState_assign]
    have hv_w1 : d3_sb.isValidValueHOLFinite VarKind.local (ofString "w") (.val (.word 1#64)) = true := by
      simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hd3_sb_loc, hd3_w, shapeOfHOLExact, shapeEqHOL]
    have hev_1 : @evalHOLExact 64 F _ d3_sb.toExact (fun a => Classical.propDecidable (d3_sb.memaddrs a)) (.const 1) =
        some (.val (.word 1#64)) := rfl
    rw [hev_1]; dsimp only; rw [if_pos hv_w1]
    have hsk : setKvarHOLFinite VarKind.local (ofString "w") (.val (.word 1#64)) d3_sb =
        setVarHOLFinite (ofString "w") (.val (.word 1#64)) d3_sb := rfl
    rw [hsk]
    refine ⟨setVarHOLFinite (ofString "w") (.val (.word 1#64)) d3_sb, rfl,
      (HeapByteEff.of_byteEff heff_s_d3.arena hsb_eff).locals_clock _ _, ?_⟩
    simp [setVarHOLFinite, hd3_sb_loc]
  obtain ⟨d4, hd4_eq, heff_d3_d4_buf, hd4_loc⟩ := hstep4
  rw [evaluateHOLFiniteState_seq_line780, hd4_eq] at hnt2 hres2 ⊢
  dsimp only at hnt2 hres2 ⊢
  have heff_s_d4 : HeapByteEff s d4 R0 ["heap_ptr"] := hstep_buf_trans heff_s_d3 heff_d3_d4_buf
  -- Step 4b: `p := p + w` (`p1 = bufw + 11`)
  let p1w : BitVec 64 := p0w + 1#64
  have hp1w_nat : p1w.toNat = bufw.toNat + 11 := by
    change (p0w + 1#64).toNat = bufw.toNat + 11
    rw [BitVec.toNat_add, hp0_nat]; change (bufw.toNat + 10 + 1) % 2 ^ 64 = _
    exact Nat.mod_eq_of_lt (by omega)
  have hd4_w : d4.locals.lookup (ofString "w") = some (.val (.word 1#64)) := by
    rw [hd4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hd4_p : d4.locals.lookup (ofString "p") = some (.val (.word p0w)) := by
    rw [hd4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hd3_p,
      show ofString "w" ≠ ofString "p" by decide]
  have hd4_start : d4.locals.lookup (ofString "start") = some (.val (.word startw)) := by
    rw [hd4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hd3_start,
      show ofString "w" ≠ ofString "start" by decide]
  have hd4_tx : d4.locals.lookup (ofString "tx_type") = some (.val (.word txType0)) := by
    rw [hd4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hd3_tx,
      show ofString "w" ≠ ofString "tx_type" by decide]
  have hd4_cgas : d4.locals.lookup (ofString "cumulative_gas") = some (.val (.word cgas0)) := by
    rw [hd4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hd3_cgas,
      show ofString "w" ≠ ofString "cumulative_gas" by decide]
  have hd4_logs : d4.locals.lookup (ofString "logs") = some (.val (.word logs0)) := by
    rw [hd4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hd3_logs,
      show ofString "w" ≠ ofString "logs" by decide]
  have hass4b : evaluateHOLFiniteState d4
      (.assign VarKind.local (ofString "p")
        (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])) =
      (none, setVarHOLFinite (ofString "p") (.val (.word p1w)) d4) := by
    rw [evaluateHOLFiniteState_assign]
    have hev : @evalHOLExact 64 F _ d4.toExact (fun a => Classical.propDecidable (d4.memaddrs a))
        (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")]) =
        some (.val (.word p1w)) := by
      simp [evalHOLExact, evalListHOLExact, hd4_p, hd4_w, wordOpHOL, wordOp, valueIsWord, valueWord, p1w]
    have hval : d4.isValidValueHOLFinite VarKind.local (ofString "p") (.val (.word p1w)) = true := by
      simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hd4_p, shapeOfHOLExact, shapeEqHOL]
    rw [hev]; dsimp only; rw [if_pos hval]; rfl
  rw [evaluateHOLFiniteState_seq_line780, hass4b] at hnt2 hres2 ⊢
  dsimp only at hnt2 hres2 ⊢
  set d5 := setVarHOLFinite (ofString "p") (.val (.word p1w)) d4
  have heff_s_d5 : HeapByteEff s d5 R0 ["heap_ptr"] := heff_s_d4.locals_clock d5.locals d5.clock
  have hd5_p : d5.locals.lookup (ofString "p") = some (.val (.word p1w)) := by
    simp [d5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hd5_w : d5.locals.lookup (ofString "w") = some (.val (.word 1#64)) := by
    simp [d5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd4_w,
      show ofString "p" ≠ ofString "w" by decide]
  have hd5_start : d5.locals.lookup (ofString "start") = some (.val (.word startw)) := by
    simp [d5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd4_start,
      show ofString "p" ≠ ofString "start" by decide]
  have hd5_tx : d5.locals.lookup (ofString "tx_type") = some (.val (.word txType0)) := by
    simp [d5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd4_tx,
      show ofString "p" ≠ ofString "tx_type" by decide]
  have hd5_cgas : d5.locals.lookup (ofString "cumulative_gas") = some (.val (.word cgas0)) := by
    simp [d5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd4_cgas,
      show ofString "p" ≠ ofString "cumulative_gas" by decide]
  have hd5_logs : d5.locals.lookup (ofString "logs") = some (.val (.word logs0)) := by
    simp [d5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd4_logs,
      show ofString "p" ≠ ofString "logs" by decide]
  -- Step 5: `w = rlp_encode_word(p, cumulative_gas)`
  rw [evaluateHOLFiniteState_seq_line780] at hnt2 hres2 ⊢
  rcases hc5 : evaluateHOLFiniteState d5
      (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
        [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "cumulative_gas")]) with ⟨r5, d6⟩
  have hnt_c5 : r5 ≠ some .timeOut := by
    rintro rfl; simp only [hc5] at hnt2; exact hnt2 rfl
  have h5 := eval_call_local_rlp_encode_word d5 "w"
    (ExpHOL.var VarKind.local (ofString "p")) (ExpHOL.var VarKind.local (ofString "cumulative_gas"))
    p1w cgas0 [bufIvl] ["heap_ptr"] heff_s_d5.arena.1.code heff_s_d5.arena ⟨1#64, hd5_w⟩ hd5_p hd5_cgas
    ⟨bufIvl, List.mem_singleton.mpr rfl, by dsimp [bufIvl]; omega, by dsimp [bufIvl]; omega⟩
    (by rw [hc5]; exact hnt_c5)
  dsimp only at h5; rw [hc5] at h5
  simp only [hc5] at hnt2 hres2 ⊢
  cases r5 with
  | some _ => dsimp only at hres2; exfalso; exact h5.2 (by simp) hres2
  | none =>
    dsimp only at hnt2 hres2 ⊢
    obtain ⟨wcgas, hwcgas_lo, hwcgas_hi, _, hd6_g, hd6_loc, heff_d5_d6_buf⟩ := h5.1 rfl
    have heff_s_d6 : HeapByteEff s d6 R0 ["heap_ptr"] := hstep_buf_trans heff_s_d5 heff_d5_d6_buf
    have hd6_w : d6.locals.lookup (ofString "w") = some (.val (.word wcgas)) := by
      rw [hd6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hd6_p : d6.locals.lookup (ofString "p") = some (.val (.word p1w)) := by
      rw [hd6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hd5_p,
        show ofString "w" ≠ ofString "p" by decide]
    have hd6_start : d6.locals.lookup (ofString "start") = some (.val (.word startw)) := by
      rw [hd6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hd5_start,
        show ofString "w" ≠ ofString "start" by decide]
    have hd6_tx : d6.locals.lookup (ofString "tx_type") = some (.val (.word txType0)) := by
      rw [hd6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hd5_tx,
        show ofString "w" ≠ ofString "tx_type" by decide]
    have hd6_logs : d6.locals.lookup (ofString "logs") = some (.val (.word logs0)) := by
      rw [hd6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hd5_logs,
        show ofString "w" ≠ ofString "logs" by decide]
    -- Step 5b: `p := p + w` (`bufw + 12 ≤ p2w ≤ bufw + 20`)
    let p2w : BitVec 64 := p1w + wcgas
    have hp2w_nat : p2w.toNat = p1w.toNat + wcgas.toNat := by
      change (p1w + wcgas).toNat = p1w.toNat + wcgas.toNat
      rw [BitVec.toNat_add]; change (p1w.toNat + wcgas.toNat) % 2 ^ 64 = _
      exact Nat.mod_eq_of_lt (by omega)
    have hass5b : evaluateHOLFiniteState d6
        (.assign VarKind.local (ofString "p")
          (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])) =
        (none, setVarHOLFinite (ofString "p") (.val (.word p2w)) d6) := by
      rw [evaluateHOLFiniteState_assign]
      have hev : @evalHOLExact 64 F _ d6.toExact (fun a => Classical.propDecidable (d6.memaddrs a))
          (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")]) =
          some (.val (.word p2w)) := by
        simp [evalHOLExact, evalListHOLExact, hd6_p, hd6_w, wordOpHOL, wordOp, valueIsWord, valueWord, p2w]
      have hval : d6.isValidValueHOLFinite VarKind.local (ofString "p") (.val (.word p2w)) = true := by
        simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hd6_p, shapeOfHOLExact, shapeEqHOL]
      rw [hev]; dsimp only; rw [if_pos hval]; rfl
    rw [evaluateHOLFiniteState_seq_line780, hass5b] at hnt2 hres2 ⊢
    dsimp only at hnt2 hres2 ⊢
    set d7 := setVarHOLFinite (ofString "p") (.val (.word p2w)) d6
    have heff_s_d7 : HeapByteEff s d7 R0 ["heap_ptr"] := heff_s_d6.locals_clock d7.locals d7.clock
    have hd7_p : d7.locals.lookup (ofString "p") = some (.val (.word p2w)) := by
      simp [d7, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hd7_w : d7.locals.lookup (ofString "w") = some (.val (.word wcgas)) := by
      simp [d7, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd6_w,
        show ofString "p" ≠ ofString "w" by decide]
    have hd7_start : d7.locals.lookup (ofString "start") = some (.val (.word startw)) := by
      simp [d7, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd6_start,
        show ofString "p" ≠ ofString "start" by decide]
    have hd7_tx : d7.locals.lookup (ofString "tx_type") = some (.val (.word txType0)) := by
      simp [d7, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd6_tx,
        show ofString "p" ≠ ofString "tx_type" by decide]
    have hd7_logs : d7.locals.lookup (ofString "logs") = some (.val (.word logs0)) := by
      simp [d7, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd6_logs,
        show ofString "p" ≠ ofString "logs" by decide]
    -- Step 6: `decCall "bloom" .one "alloc" [256]`
    obtain ⟨bloomw, n256, hp_bloom, d8, hn256_ev, hbloom_hp, hbloom8, hhp_bloom_eq, hbloom_fit,
        hhp_bloom_hi, hhp_bloom_8, hd8_hp, hd8_g, hd8_m, hd8_loc, heff_d7_d8, hnt8, hres8, heq8⟩ :=
      eval_decCall_alloc_resumes d7 "bloom" (.const 256) _ R0 ["heap_ptr"]
        heff_s_d7.arena.1.code heff_s_d7.arena (by simp) hnt2 hres2
    rw [heq8]; dsimp only
    have hn256_eq : n256 = 256#64 := by simp [evalHOLExact] at hn256_ev; exact hn256_ev.symm
    subst hn256_eq
    have h256_val : (256#64 : BitVec 64).toNat = 256 := by decide
    have hbloom_hi : bloomw.toNat + 256 ≤ heapLimit := by rw [← h256_val]; omega
    have hbloom_ge_s : globN s "heap_ptr" ≤ bloomw.toNat := by
      rw [hbloom_hp]; exact heff_s_d7.hp_le
    have heff_s_d8 : HeapByteEff s d8 R0 ["heap_ptr"] := heff_s_d7.trans heff_d7_d8
    let bloomTailProg : ProgHOL 64 :=
      .seq
        (.call (some (none, none)) (ofString "logs_bloom")
          [ExpHOL.var VarKind.local (ofString "logs"), ExpHOL.var VarKind.local (ofString "bloom")])
        (.seq
          (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
            [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "bloom"), .const 256])
          (.seq
            (.assign VarKind.local (ofString "p")
              (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")]))
            (.seq
              (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "encode_logs")
                [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "logs")])
              (.seq
                (.assign VarKind.local (ofString "p")
                  (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")]))
                (.seq
                  (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_finish_list")
                    [ExpHOL.var VarKind.local (ofString "start"), ExpHOL.var VarKind.local (ofString "p")])
                  (.seq
                    (.ite (.cmp .notEqual (ExpHOL.var VarKind.local (ofString "tx_type")) (.const 0))
                      (.seq
                        (.storeByte (.op .sub [ExpHOL.var VarKind.local (ofString "start"), .const 1])
                          (ExpHOL.var VarKind.local (ofString "tx_type")))
                        (.return (.rstruct
                          [.op .sub [ExpHOL.var VarKind.local (ofString "start"), .const 1],
                           .op .add [ExpHOL.var VarKind.local (ofString "w"), .const 1]])))
                      .skip)
                    (.return (.rstruct
                      [ExpHOL.var VarKind.local (ofString "start"),
                       ExpHOL.var VarKind.local (ofString "w")]))))))))
    suffices hd8 :
        HeapByteEff s (evaluateHOLFiniteState d8 bloomTailProg).2 R0 ["heap_ptr"] ∧
        (∀ v, (evaluateHOLFiniteState d8 bloomTailProg).1 = some (.returned v) →
          ∃ a b : BitVec 64,
            v = .rStruct [.val (.word a), .val (.word b)] ∧
            Inside (a.toNat, b.toNat) sourceBase
              (globN (evaluateHOLFiniteState d8 bloomTailProg).2 "heap_ptr") ∧
            a.toNat < 2 ^ 61 ∧ b.toNat < 2 ^ 61) by
      exact ⟨hd8.1.locals_clock _ _, fun v hv => hd8.2 v hv⟩
    dsimp only [bloomTailProg] at hnt8 hres8 ⊢
    have hd8_bloom : d8.locals.lookup (ofString "bloom") = some (.val (.word bloomw)) := by
      rw [hd8_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hd8_p : d8.locals.lookup (ofString "p") = some (.val (.word p2w)) := by
      rw [hd8_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hd7_p,
        show ofString "bloom" ≠ ofString "p" by decide]
    have hd8_w : d8.locals.lookup (ofString "w") = some (.val (.word wcgas)) := by
      rw [hd8_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hd7_w,
        show ofString "bloom" ≠ ofString "w" by decide]
    have hd8_start : d8.locals.lookup (ofString "start") = some (.val (.word startw)) := by
      rw [hd8_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hd7_start,
        show ofString "bloom" ≠ ofString "start" by decide]
    have hd8_tx : d8.locals.lookup (ofString "tx_type") = some (.val (.word txType0)) := by
      rw [hd8_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hd7_tx,
        show ofString "bloom" ≠ ofString "tx_type" by decide]
    have hd8_logs : d8.locals.lookup (ofString "logs") = some (.val (.word logs0)) := by
      rw [hd8_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hd7_logs,
        show ofString "bloom" ≠ ofString "logs" by decide]
    -- Step 7: `logs_bloom(logs, bloom)`
    let Rbloom : List Ivl := (bloomw.toNat, 256) :: R0
    have hkpad_d8 : globN d8 "keccak_pad" = globN s "keccak_pad" := by
      unfold globN; rw [← heff_s_d8.globals (ofString "keccak_pad") (by decide)]
    have hkst_d8 : globN d8 "keccak_st" = globN s "keccak_st" := by
      unfold globN; rw [← heff_s_d8.globals (ofString "keccak_st") (by decide)]
    rw [evaluateHOLFiniteState_seq_line780] at hnt8 hres8 ⊢
    have hnr_c7 := call_noexc_ne_returned d8 none (ofString "logs_bloom")
      [ExpHOL.var VarKind.local (ofString "logs"), ExpHOL.var VarKind.local (ofString "bloom")]
    rcases hc7 : evaluateHOLFiniteState d8
        (.call (some (none, none)) (ofString "logs_bloom")
          [ExpHOL.var VarKind.local (ofString "logs"), ExpHOL.var VarKind.local (ofString "bloom")]) with ⟨r7, d9⟩
    have hnt_c7 : r7 ≠ some .timeOut := by
      rintro rfl; simp only [hc7] at hnt8; exact hnt8 rfl
    have hor_c7 : r7 = none ∨ Resumes r7 := by
      cases r7 with
      | none => exact Or.inl rfl
      | some rk => right; simp only [hc7] at hres8; exact hres8
    have h7 := eval_call_logs_bloom d8
      (ExpHOL.var VarKind.local (ofString "logs")) (ExpHOL.var VarKind.local (ofString "bloom"))
      logs0 bloomw Rbloom heff_s_d8.arena.1.code heff_s_d8.arena hd8_logs hd8_bloom
      ⟨(bloomw.toNat, 256), List.mem_cons_self, le_rfl, le_rfl⟩
      (fun hnz => by
        rw [hkpad_d8] at hnz ⊢
        exact ⟨(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
          List.mem_cons_of_mem _ List.mem_cons_self, le_rfl, by simp [hnz]⟩)
      (fun hnz => by
        rw [hkst_d8] at hnz ⊢
        exact ⟨(globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), le_rfl, by simp [hnz]⟩)
      (by rw [hc7]; exact hnt_c7)
      (by rw [hc7]; exact hor_c7)
    dsimp only at h7
    rw [hc7] at h7 hnr_c7
    simp only [hc7] at hnt8 hres8 ⊢
    have heff_s_d9 : HeapByteEff s d9 R0 ["heap_ptr"] := by
      have h_lift : HeapByteEff s d8 Rbloom ["heap_ptr"] :=
        heff_s_d8.mono (fun i hi _ => Or.inl ⟨i, List.mem_cons_of_mem _ hi, le_rfl, le_rfl⟩) (fun _ h => h)
      exact (h_lift.trans h7.1).mono
        (fun i hi _ => by
          rcases List.mem_cons.1 hi with rfl | hR0
          · exact Or.inr (Or.inr ⟨hbloom_ge_s, hbloom_hi⟩)
          · exact Or.inl ⟨i, hR0, le_rfl, le_rfl⟩)
        (fun _ h => h)
    cases r7 with
    | some rk =>
      dsimp only at hres8 ⊢
      refine ⟨heff_s_d9, fun v hv => ?_⟩
      exfalso
      exact hnr_c7 v hv
    | none =>
      dsimp only at hnt8 hres8 ⊢
      have hd9_loc : d9.locals = d8.locals := h7.2 rfl
      -- Step 8: `w = rlp_encode_bytes(p, bloom, 256)`
      rw [evaluateHOLFiniteState_seq_line780] at hnt8 hres8 ⊢
      have hhl256 : rlpHeaderLenPure 256 + 256 ≤ 265 := by
        have hb9 := rlpHeaderLenPure_bounds 256
        omega
      have hhl256' : rlpHeaderLenPure (256#64 : BitVec 64).toNat + (256#64 : BitVec 64).toNat ≤ 265 := by
        rw [h256_val]; exact hhl256
      have hd9_p : d9.locals.lookup (ofString "p") = some (.val (.word p2w)) := by rw [hd9_loc]; exact hd8_p
      have hd9_w : d9.locals.lookup (ofString "w") = some (.val (.word wcgas)) := by rw [hd9_loc]; exact hd8_w
      have hd9_bloom : d9.locals.lookup (ofString "bloom") = some (.val (.word bloomw)) := by rw [hd9_loc]; exact hd8_bloom
      have hd9_start : d9.locals.lookup (ofString "start") = some (.val (.word startw)) := by rw [hd9_loc]; exact hd8_start
      have hd9_tx : d9.locals.lookup (ofString "tx_type") = some (.val (.word txType0)) := by rw [hd9_loc]; exact hd8_tx
      have hd9_logs : d9.locals.lookup (ofString "logs") = some (.val (.word logs0)) := by rw [hd9_loc]; exact hd8_logs
      rcases hc8 : evaluateHOLFiniteState d9
          (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
            [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "bloom"), .const 256]) with ⟨r8, d10⟩
      have hnt_c8 : r8 ≠ some .timeOut := by
        rintro rfl; simp only [hc8] at hnt8; exact hnt8 rfl
      have h8 := eval_call_local_rlp_encode_bytes d9 "w"
        (ExpHOL.var VarKind.local (ofString "p")) (ExpHOL.var VarKind.local (ofString "bloom")) (.const 256)
        p2w bloomw 256#64 [bufIvl] ["heap_ptr"] heff_s_d9.arena.1.code heff_s_d9.arena
        ⟨wcgas, hd9_w⟩ hd9_p hd9_bloom rfl
        ⟨bufIvl, List.mem_singleton.mpr rfl, by dsimp [bufIvl]; omega,
          by dsimp [bufIvl]; omega⟩
        (by rw [hc8]; exact hnt_c8)
      dsimp only at h8; rw [hc8] at h8
      simp only [hc8] at hnt8 hres8 ⊢
      cases r8 with
      | some _ => dsimp only at hres8; exfalso; exact h8.2 (by simp) hres8
      | none =>
        dsimp only at hnt8 hres8 ⊢
        obtain ⟨wbloom, hwbloom_hi', hwbloom_lo, hd10_g, hd10_loc, heff_d9_d10_buf⟩ := h8.1 rfl
        have hwbloom_hi : wbloom.toNat ≤ 265 := le_trans hwbloom_hi' hhl256'
        have heff_s_d10 : HeapByteEff s d10 R0 ["heap_ptr"] := hstep_buf_trans heff_s_d9 heff_d9_d10_buf
        have hd10_w : d10.locals.lookup (ofString "w") = some (.val (.word wbloom)) := by
          rw [hd10_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        have hd10_p : d10.locals.lookup (ofString "p") = some (.val (.word p2w)) := by
          rw [hd10_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hd9_p,
            show ofString "w" ≠ ofString "p" by decide]
        have hd10_start : d10.locals.lookup (ofString "start") = some (.val (.word startw)) := by
          rw [hd10_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hd9_start,
            show ofString "w" ≠ ofString "start" by decide]
        have hd10_tx : d10.locals.lookup (ofString "tx_type") = some (.val (.word txType0)) := by
          rw [hd10_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hd9_tx,
            show ofString "w" ≠ ofString "tx_type" by decide]
        have hd10_logs : d10.locals.lookup (ofString "logs") = some (.val (.word logs0)) := by
          rw [hd10_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hd9_logs,
            show ofString "w" ≠ ofString "logs" by decide]
        -- Step 8b: `p := p + w` (`bufw + 13 ≤ p3w ≤ bufw + 285`)
        let p3w : BitVec 64 := p2w + wbloom
        have hp3w_nat : p3w.toNat = p2w.toNat + wbloom.toNat := by
          change (p2w + wbloom).toNat = p2w.toNat + wbloom.toNat
          rw [BitVec.toNat_add]; change (p2w.toNat + wbloom.toNat) % 2 ^ 64 = _
          exact Nat.mod_eq_of_lt (by omega)
        have hass8b : evaluateHOLFiniteState d10
            (.assign VarKind.local (ofString "p")
              (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])) =
            (none, setVarHOLFinite (ofString "p") (.val (.word p3w)) d10) := by
          rw [evaluateHOLFiniteState_assign]
          have hev : @evalHOLExact 64 F _ d10.toExact (fun a => Classical.propDecidable (d10.memaddrs a))
              (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")]) =
              some (.val (.word p3w)) := by
            simp [evalHOLExact, evalListHOLExact, hd10_p, hd10_w, wordOpHOL, wordOp, valueIsWord, valueWord, p3w]
          have hval : d10.isValidValueHOLFinite VarKind.local (ofString "p") (.val (.word p3w)) = true := by
            simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hd10_p, shapeOfHOLExact, shapeEqHOL]
          rw [hev]; dsimp only; rw [if_pos hval]; rfl
        rw [evaluateHOLFiniteState_seq_line780, hass8b] at hnt8 hres8 ⊢
        dsimp only at hnt8 hres8 ⊢
        set d11 := setVarHOLFinite (ofString "p") (.val (.word p3w)) d10
        have heff_s_d11 : HeapByteEff s d11 R0 ["heap_ptr"] := heff_s_d10.locals_clock d11.locals d11.clock
        have hd11_p : d11.locals.lookup (ofString "p") = some (.val (.word p3w)) := by
          simp [d11, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hd11_w : d11.locals.lookup (ofString "w") = some (.val (.word wbloom)) := by
          simp [d11, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd10_w,
            show ofString "p" ≠ ofString "w" by decide]
        have hd11_start : d11.locals.lookup (ofString "start") = some (.val (.word startw)) := by
          simp [d11, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd10_start,
            show ofString "p" ≠ ofString "start" by decide]
        have hd11_tx : d11.locals.lookup (ofString "tx_type") = some (.val (.word txType0)) := by
          simp [d11, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd10_tx,
            show ofString "p" ≠ ofString "tx_type" by decide]
        have hd11_logs : d11.locals.lookup (ofString "logs") = some (.val (.word logs0)) := by
          simp [d11, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd10_logs,
            show ofString "p" ≠ ofString "logs" by decide]
        -- Step 9: `w = encode_logs(p, logs)` via `s0_snap := { d11 with globals := s.globals }`
        let s0_snap : PanSemStateFiniteExact 64 F := { d11 with globals := s.globals }
        have hA_snap : ArenaOK s0_snap := arenaOK_congr rfl hA0
        have hma_snap : s0_snap.memaddrs = ordinaryDomain := by
          change d11.memaddrs = ordinaryDomain; rw [heff_s_d11.memaddrs]; exact hma0
        have hAR_snap : ArenaReady s0_snap :=
          ⟨guestInv_congr (s := d11) rfl rfl rfl rfl heff_s_d11.arena.1, hA_snap⟩
        have heff_snap_d11 : HeapByteEff s0_snap d11 [(p3w.toNat, boundw.toNat)] ["heap_ptr"] := by
          refine ⟨heff_s_d11.arena, rfl, ?_, ?_, ?_, rfl, ?_,
            fun _ h => False.elim (h rfl), fun _ h => False.elim (h rfl), fun _ _ h => False.elim (h rfl)⟩
          · change globN s "heap_ptr" ≤ globN d11 "heap_ptr"; exact heff_s_d11.hp_le
          · change globN d11 "frame_mem_ptr" = globN s "frame_mem_ptr"; exact heff_s_d11.fp_eq
          · change globN d11 "scratch_ptr" ≤ globN s "scratch_ptr"; exact heff_s_d11.sp_le
          · intro k hk; exact heff_s_d11.globals k hk
        have heff_s_snap : HeapByteEff s s0_snap R0 ["heap_ptr"] := by
          refine ⟨hAR_snap, heff_s_d11.memaddrs, le_rfl, rfl, le_rfl, heff_s_d11.be,
            fun _ _ => rfl, heff_s_d11.out_dom, heff_s_d11.cell_frame, heff_s_d11.byte_frame⟩
        have hLL_snap : LogsListOK s0_snap logs0.toNat :=
          (logsListOK_preserved hA0 hma0 heff_s_snap hl_nz hLL hDF).2
        have hal_arr_snap : Allocated s0_snap (memW s0_snap logs0.toNat, 8 * memW s0_snap (logs0.toNat + 8)) ∧
            logsEncodedSum s0_snap (memW s0_snap logs0.toNat) (memW s0_snap (logs0.toNat + 8)) =
              logsEncodedSum s (memW s logs0.toNat) (memW s (logs0.toNat + 8)) := by
          rcases hLL with h0 | ⟨hw_hdr, hal_hdr, hn_lt, _, hentries⟩
          · exact absurd h0 hl_nz
          rcases hDF with h0 | ⟨hal_arr, hdisj⟩
          · exact absurd h0 hl_nz
          have hdj_hdr : ∀ f ∈ fixedObjects s, Disj (logs0.toNat, 24) f :=
            fun f hf => hdisj (logs0.toNat, 24) (List.mem_append_left _ List.mem_cons_self) f hf
          have hdj_arr : ∀ f ∈ fixedObjects s, Disj (memW s logs0.toNat, 8 * memW s (logs0.toNat + 8)) f :=
            fun f hf => hdisj (memW s logs0.toNat, 8 * memW s (logs0.toNat + 8))
              (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)) f hf
          have hm0 : memW s0_snap logs0.toNat = memW s logs0.toNat :=
            memW_eq_of_allocated_disj_fixed heff_s_snap hA0 hma0 hal_hdr hdj_hdr hw_hdr.1
              (by dsimp only; omega) (by dsimp only; omega)
          have hm8 : memW s0_snap (logs0.toNat + 8) = memW s (logs0.toNat + 8) :=
            memW_eq_of_allocated_disj_fixed heff_s_snap hA0 hma0 hal_hdr hdj_hdr (by have := hw_hdr.1; omega)
              (by dsimp only; omega) (by dsimp only; omega)
          rw [hm0, hm8]
          have hal_arr' : Allocated s0_snap (memW s logs0.toNat, 8 * memW s (logs0.toNat + 8)) :=
            M13.allocated_mono (le_rfl : globN s "heap_ptr" ≤ globN s0_snap "heap_ptr")
              (le_rfl : globN s0_snap "scratch_ptr" ≤ globN s "scratch_ptr") hal_arr
          refine ⟨hal_arr', ?_⟩
          have hsum_eq : ∀ k, k ≤ memW s (logs0.toNat + 8) →
              logsEncodedSum s0_snap (memW s logs0.toNat) k = logsEncodedSum s (memW s logs0.toNat) k := by
            intro k hk
            induction k with
            | zero => rfl
            | succ k ih =>
              have hk_lt : k < memW s (logs0.toNat + 8) := by omega
              obtain ⟨hwa_k, hle_k⟩ := hentries k hk_lt
              have ha_k_lt : memW s logs0.toNat + 8 * k < 2 ^ 64 := by
                have := M13.allocated_le_2pow64 hA0 hal_arr; dsimp only at this; omega
              have ha_k8 : (memW s logs0.toNat + 8 * k) % 8 = 0 := by
                obtain ⟨_, hdom_k, _⟩ := hwa_k
                rw [hma0, ordinaryDomain_iff] at hdom_k
                have hbv_k : (BitVec.ofNat 64 (memW s logs0.toNat + 8 * k)).toNat =
                    memW s logs0.toNat + 8 * k := by
                  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt ha_k_lt
                rw [hbv_k] at hdom_k; exact hdom_k.1
              have hm_elem : memW s0_snap (memW s logs0.toNat + 8 * k) = memW s (memW s logs0.toNat + 8 * k) :=
                memW_eq_of_allocated_disj_fixed heff_s_snap hA0 hma0 hal_arr hdj_arr ha_k8
                  (by dsimp only; omega) (by dsimp only; omega)
              let log := memW s (memW s logs0.toNat + 8 * k)
              obtain ⟨hw_log, hin_log, _⟩ := hle_k
              have hal_log : Allocated s (log, 40) := Or.inl hin_log
              have hlog_in_owned : (log, 40) ∈ logOwnedIvls s log := by
                unfold logOwnedIvls
                refine List.mem_filter.2 ⟨by simp [logRecordIvls], ?_⟩
                simp only [bne_iff_ne, ne_eq, Prod.mk.injEq, not_and]; intro _ h40; omega
              have hlog_in_flat : (log, 40) ∈ (List.range (memW s (logs0.toNat + 8))).flatMap
                  (fun idx => logOwnedIvls s (memW s (memW s logs0.toNat + 8 * idx))) :=
                List.mem_flatMap.2 ⟨k, List.mem_range.2 hk_lt, hlog_in_owned⟩
              have hdj_log : ∀ f ∈ fixedObjects s, Disj (log, 40) f :=
                fun f hf => hdisj (log, 40) (List.mem_append_right _ hlog_in_flat) f hf
              have hlog16 : memW s0_snap (log + 16) = memW s (log + 16) :=
                memW_eq_of_allocated_disj_fixed heff_s_snap hA0 hma0 hal_log hdj_log (by have := hw_log.1; omega)
                  (by dsimp [log]; omega) (by dsimp [log]; omega)
              have hlog32 : memW s0_snap (log + 32) = memW s (log + 32) :=
                memW_eq_of_allocated_disj_fixed heff_s_snap hA0 hma0 hal_log hdj_log (by have := hw_log.1; omega)
                  (by dsimp [log]; omega) (by dsimp [log]; omega)
              dsimp [log] at hlog16 hlog32
              simp only [logsEncodedSum, ih (by omega), hm_elem, hlog16, hlog32]
          exact hsum_eq _ le_rfl
        rw [evaluateHOLFiniteState_seq_line780] at hnt8 hres8 ⊢
        rcases hc9 : evaluateHOLFiniteState d11
            (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "encode_logs")
              [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "logs")]) with ⟨r9, d12⟩
        have hnt_c9 : r9 ≠ some .timeOut := by
          rintro rfl; simp only [hc9] at hnt8; exact hnt8 rfl
        have h9 := eval_call_local_encode_logs s0_snap d11 "w"
          (ExpHOL.var VarKind.local (ofString "p")) (ExpHOL.var VarKind.local (ofString "logs"))
          p3w logs0 boundw.toNat [bufIvl] ["heap_ptr"]
          hA_snap hma_snap heff_snap_d11
          (by change globN s "heap_ptr" ≤ p3w.toNat; rw [← hbuf_hp0]; omega)
          (by omega) hhl_lt hl_nz hLL_snap hal_arr_snap.1
          (by rw [hal_arr_snap.2, hbound_eq]; omega)
          ⟨bufIvl, List.mem_singleton.mpr rfl, by dsimp [bufIvl]; omega, by dsimp [bufIvl]; omega⟩
          ⟨wbloom, hd11_w⟩ hd11_p hd11_logs
          (by rw [hc9]; exact hnt_c9)
        dsimp only at h9; rw [hc9] at h9
        simp only [hc9] at hnt8 hres8 ⊢
        cases r9 with
        | some _ => dsimp only at hres8; exfalso; exact h9.2 (by simp) hres8
        | none =>
          dsimp only at hnt8 hres8 ⊢
          obtain ⟨wlogs, hwlogs_hi', hd12_g, hd12_loc, heff_d11_d12_buf⟩ := h9.1 rfl
          have hwlogs_hi : wlogs.toNat ≤ boundw.toNat := by
            rw [hal_arr_snap.2] at hwlogs_hi'; omega
          have heff_s_d12 : HeapByteEff s d12 R0 ["heap_ptr"] := hstep_buf_trans heff_s_d11 heff_d11_d12_buf
          have hd12_w : d12.locals.lookup (ofString "w") = some (.val (.word wlogs)) := by
            rw [hd12_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
          have hd12_p : d12.locals.lookup (ofString "p") = some (.val (.word p3w)) := by
            rw [hd12_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hd11_p,
              show ofString "w" ≠ ofString "p" by decide]
          have hd12_start : d12.locals.lookup (ofString "start") = some (.val (.word startw)) := by
            rw [hd12_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hd11_start,
              show ofString "w" ≠ ofString "start" by decide]
          have hd12_tx : d12.locals.lookup (ofString "tx_type") = some (.val (.word txType0)) := by
            rw [hd12_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hd11_tx,
              show ofString "w" ≠ ofString "tx_type" by decide]
          -- Step 9b: `p := p + w` (`startw + 9 ≤ p4w ≤ bufw + boundw + 285`)
          let p4w : BitVec 64 := p3w + wlogs
          have hp4w_nat : p4w.toNat = p3w.toNat + wlogs.toNat := by
            change (p3w + wlogs).toNat = p3w.toNat + wlogs.toNat
            rw [BitVec.toNat_add]; change (p3w.toNat + wlogs.toNat) % 2 ^ 64 = _
            exact Nat.mod_eq_of_lt (by omega)
          have hass9b : evaluateHOLFiniteState d12
              (.assign VarKind.local (ofString "p")
                (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])) =
              (none, setVarHOLFinite (ofString "p") (.val (.word p4w)) d12) := by
            rw [evaluateHOLFiniteState_assign]
            have hev : @evalHOLExact 64 F _ d12.toExact (fun a => Classical.propDecidable (d12.memaddrs a))
                (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")]) =
                some (.val (.word p4w)) := by
              simp [evalHOLExact, evalListHOLExact, hd12_p, hd12_w, wordOpHOL, wordOp, valueIsWord, valueWord, p4w]
            have hval : d12.isValidValueHOLFinite VarKind.local (ofString "p") (.val (.word p4w)) = true := by
              simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hd12_p, shapeOfHOLExact, shapeEqHOL]
            rw [hev]; dsimp only; rw [if_pos hval]; rfl
          rw [evaluateHOLFiniteState_seq_line780, hass9b] at hnt8 hres8 ⊢
          dsimp only at hnt8 hres8 ⊢
          set d13 := setVarHOLFinite (ofString "p") (.val (.word p4w)) d12
          have heff_s_d13 : HeapByteEff s d13 R0 ["heap_ptr"] := heff_s_d12.locals_clock d13.locals d13.clock
          have hd13_p : d13.locals.lookup (ofString "p") = some (.val (.word p4w)) := by
            simp [d13, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hd13_w : d13.locals.lookup (ofString "w") = some (.val (.word wlogs)) := by
            simp [d13, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd12_w,
              show ofString "p" ≠ ofString "w" by decide]
          have hd13_start : d13.locals.lookup (ofString "start") = some (.val (.word startw)) := by
            simp [d13, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd12_start,
              show ofString "p" ≠ ofString "start" by decide]
          have hd13_tx : d13.locals.lookup (ofString "tx_type") = some (.val (.word txType0)) := by
            simp [d13, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd12_tx,
              show ofString "p" ≠ ofString "tx_type" by decide]
          -- Step 10: `w = rlp_finish_list(start, p)`
          rw [evaluateHOLFiniteState_seq_line780] at hnt8 hres8 ⊢
          rcases hc10 : evaluateHOLFiniteState d13
              (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_finish_list")
                [ExpHOL.var VarKind.local (ofString "start"), ExpHOL.var VarKind.local (ofString "p")]) with ⟨r10, d14⟩
          have hnt_c10 : r10 ≠ some .timeOut := by
            rintro rfl; simp only [hc10] at hnt8; exact hnt8 rfl
          have h10 := eval_call_local_rlp_finish_list d13 "w"
            (ExpHOL.var VarKind.local (ofString "start")) (ExpHOL.var VarKind.local (ofString "p"))
            startw p4w [bufIvl] ["heap_ptr"] heff_s_d13.arena.1.code heff_s_d13.arena
            ⟨wlogs, hd13_w⟩ hd13_start hd13_p (by omega) (by omega)
            ⟨bufIvl, List.mem_singleton.mpr rfl, by dsimp [bufIvl]; omega, by dsimp [bufIvl]; omega⟩
            (by rw [hc10]; exact hnt_c10)
          dsimp only at h10; rw [hc10] at h10
          simp only [hc10] at hnt8 hres8 ⊢
          cases r10 with
          | some _ => dsimp only at hres8; exfalso; exact h10.2 (by simp) hres8
          | none =>
            dsimp only at hnt8 hres8 ⊢
            obtain ⟨wfin, hwfin_nat, hwfin_le, hd14_g, hd14_loc, heff_d13_d14_buf⟩ := h10.1 rfl
            have heff_s_d14 : HeapByteEff s d14 R0 ["heap_ptr"] := hstep_buf_trans heff_s_d13 heff_d13_d14_buf
            have hd14_w : d14.locals.lookup (ofString "w") = some (.val (.word wfin)) := by
              rw [hd14_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
            have hd14_start : d14.locals.lookup (ofString "start") = some (.val (.word startw)) := by
              rw [hd14_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hd13_start,
                show ofString "w" ≠ ofString "start" by decide]
            have hd14_tx : d14.locals.lookup (ofString "tx_type") = some (.val (.word txType0)) := by
              rw [hd14_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hd13_tx,
                show ofString "w" ≠ ofString "tx_type" by decide]
            have hd14_hp_ge : hp1.toNat ≤ globN d14 "heap_ptr" := by
              have hm2_d3 : globN m2 "heap_ptr" = globN d3 "heap_ptr" := rfl
              have h_m2_d14 : globN m2 "heap_ptr" ≤ globN d14 "heap_ptr" := by
                have h4 : globN d3 "heap_ptr" ≤ globN d4 "heap_ptr" := heff_d3_d4_buf.hp_le
                have h45 : globN d4 "heap_ptr" = globN d5 "heap_ptr" := rfl
                have h6 : globN d5 "heap_ptr" ≤ globN d6 "heap_ptr" := heff_d5_d6_buf.hp_le
                have h67 : globN d6 "heap_ptr" = globN d7 "heap_ptr" := rfl
                have h8' : globN d7 "heap_ptr" ≤ globN d8 "heap_ptr" := heff_d7_d8.hp_le
                have h9' : globN d8 "heap_ptr" ≤ globN d9 "heap_ptr" := h7.1.hp_le
                have h10' : globN d9 "heap_ptr" ≤ globN d10 "heap_ptr" := heff_d9_d10_buf.hp_le
                have h1011 : globN d10 "heap_ptr" = globN d11 "heap_ptr" := rfl
                have h12' : globN d11 "heap_ptr" ≤ globN d12 "heap_ptr" := heff_d11_d12_buf.hp_le
                have h1213 : globN d12 "heap_ptr" = globN d13 "heap_ptr" := rfl
                have h14' : globN d13 "heap_ptr" ≤ globN d14 "heap_ptr" := heff_d13_d14_buf.hp_le
                omega
              omega
            -- Step 11: `ite (tx_type != 0) (storeByte (start - 1) tx_type; return (rstruct [start - 1, w + 1])) skip; return (rstruct [start, w])`
            rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt8 hres8 ⊢
            have hcond_tx : @evalHOLExact 64 F _ d14.toExact (fun a => Classical.propDecidable (d14.memaddrs a))
                (.cmp .notEqual (ExpHOL.var VarKind.local (ofString "tx_type")) (.const 0)) =
                some (.val (.word (if txType0 ≠ 0#64 then 1#64 else 0#64))) := by
              simp only [evalHOLExact, hd14_tx, Compiler.Encoders.Asm.wordCmpHOL]
              by_cases htz : txType0 = 0#64 <;> simp [htz]
            rw [hcond_tx] at hnt8 hres8 ⊢
            dsimp only at hnt8 hres8 ⊢
            by_cases htz : txType0 = 0#64
            · simp only [htz, ne_eq, not_true_eq_false, ↓reduceIte,
                (show (0#64 : BitVec 64) = 0 by decide)] at hnt8 hres8 ⊢
              simp only [evaluateHOLFiniteState_skip]
              have hret0 : evaluateHOLFiniteState d14
                  (.return (.rstruct [ExpHOL.var VarKind.local (ofString "start"),
                                      ExpHOL.var VarKind.local (ofString "w")])) =
                  (some (.returned (.rStruct [.val (.word startw), .val (.word wfin)])),
                   d14.emptyLocalsHOLFinite) := by
                rw [evaluateHOLFiniteState_return]
                have hev_ret0 : @evalHOLExact 64 F _ d14.toExact (fun a => Classical.propDecidable (d14.memaddrs a))
                    (.rstruct [ExpHOL.var VarKind.local (ofString "start"),
                               ExpHOL.var VarKind.local (ofString "w")]) =
                    some (.rStruct [.val (.word startw), .val (.word wfin)]) := by
                  simp [evalHOLExact, evalListHOLExact, hd14_start, hd14_w]
                rw [hev_ret0]; dsimp only
                have hsz0 : sizeOfShapeWithContextHOL d14.structs
                    (shapeOfHOLExact (.rStruct [.val (.word startw), .val (.word wfin)] : ValueHOL 64)) ≤ 32 := by
                  simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
                rw [if_pos hsz0]
              simp only [hret0]
              refine ⟨heff_s_d14.locals_clock _ _, fun v hv => ?_⟩
              simp only [Option.some.injEq, PanSemResultExact.returned.injEq] at hv
              subst hv
              refine ⟨startw, wfin, rfl, ?_, by omega, by omega⟩
              exact ⟨by omega, by change startw.toNat + wfin.toNat ≤ globN d14 "heap_ptr"; omega⟩
            · simp only [htz, ne_eq, not_false_eq_true, ↓reduceIte,
                (show ¬ ((1#64 : BitVec 64) = 0) by decide)] at hnt8 hres8 ⊢
              have hsub_start : startw - 1#64 = bufw := by
                change bufw + 1#64 - 1#64 = bufw; bv_omega
              have hbuf_in_dom : d14.memaddrs (panByteAlignHOL bufw) := by
                rw [heff_s_d14.memaddrs, hma0, ordinaryDomain_iff]
                refine ⟨by rw [panByteAlign_toNat64]; omega, ?_, ?_⟩
                · rw [panByteAlign_toNat64]; omega
                · rw [panByteAlign_toNat64]; omega
              have hsb_tx_eff := (R13Shards.Keccak256.byteEff_storeByte (Rl := [bufIvl]) heff_s_d14.arena.1
                (.op .sub [ExpHOL.var VarKind.local (ofString "start"), .const 1])
                (ExpHOL.var VarKind.local (ofString "tx_type"))
                (fun x hx _ => by
                  simp [evalHOLExact, evalListHOLExact, hd14_start, wordOpHOL, wordOp, valueIsWord, valueWord, hsub_start] at hx
                  subst hx
                  exact ⟨bufIvl, List.mem_singleton.mpr rfl, by dsimp [bufIvl]; omega, by dsimp [bufIvl]; omega⟩)).1
              have hsb_tx_exact : ∃ d15 : PanSemStateFiniteExact 64 F,
                  evaluateHOLFiniteState d14
                    (.storeByte (.op .sub [ExpHOL.var VarKind.local (ofString "start"), .const 1])
                      (ExpHOL.var VarKind.local (ofString "tx_type"))) = (none, d15) ∧
                  d15.locals = d14.locals ∧ d15.globals = d14.globals := by
                rw [evaluateHOLFiniteState_storeByte]
                have ha_ev : @evalHOLExact 64 F _ d14.toExact (fun a => Classical.propDecidable (d14.memaddrs a))
                    (.op .sub [ExpHOL.var VarKind.local (ofString "start"), .const 1]) =
                    some (.val (.word bufw)) := by
                  simp [evalHOLExact, evalListHOLExact, hd14_start, wordOpHOL, wordOp, valueIsWord, valueWord, hsub_start]
                have hv_ev : @evalHOLExact 64 F _ d14.toExact (fun a => Classical.propDecidable (d14.memaddrs a))
                    (ExpHOL.var VarKind.local (ofString "tx_type")) =
                    some (.val (.word txType0)) := hd14_tx
                rw [ha_ev, hv_ev]; dsimp only
                unfold panMemStoreByteWord8HOL; dsimp only
                cases hm_cell : d14.memory (panByteAlignHOL bufw) with
                | word cell =>
                  rw [if_pos hbuf_in_dom]; dsimp only
                  exact ⟨_, rfl, rfl, rfl⟩
              obtain ⟨d15, hsb_tx_r, hd15_loc, hd15_g⟩ := hsb_tx_exact
              rw [hsb_tx_r] at hsb_tx_eff
              have heff_d14_d15_buf : HeapByteEff d14 d15 [bufIvl] ["heap_ptr"] :=
                HeapByteEff.of_byteEff heff_s_d14.arena hsb_tx_eff
              have heff_s_d15 : HeapByteEff s d15 R0 ["heap_ptr"] := hstep_buf_trans heff_s_d14 heff_d14_d15_buf
              let w1 : BitVec 64 := wfin + 1#64
              have hw1_nat : w1.toNat = wfin.toNat + 1 := by
                change (wfin + 1#64).toNat = wfin.toNat + 1
                rw [BitVec.toNat_add]; change (wfin.toNat + 1) % 2 ^ 64 = _
                exact Nat.mod_eq_of_lt (by omega)
              have hret1 : evaluateHOLFiniteState d15
                  (.return (.rstruct
                    [.op .sub [ExpHOL.var VarKind.local (ofString "start"), .const 1],
                     .op .add [ExpHOL.var VarKind.local (ofString "w"), .const 1]])) =
                  (some (.returned (.rStruct [.val (.word bufw), .val (.word w1)])),
                   d15.emptyLocalsHOLFinite) := by
                rw [evaluateHOLFiniteState_return]
                have hev_ret1 : @evalHOLExact 64 F _ d15.toExact (fun a => Classical.propDecidable (d15.memaddrs a))
                    (.rstruct
                      [.op .sub [ExpHOL.var VarKind.local (ofString "start"), .const 1],
                       .op .add [ExpHOL.var VarKind.local (ofString "w"), .const 1]]) =
                    some (.rStruct [.val (.word bufw), .val (.word w1)]) := by
                  simp [evalHOLExact, evalListHOLExact, hd15_loc, hd14_start, hd14_w,
                    wordOpHOL, wordOp, valueIsWord, valueWord, hsub_start, w1]
                rw [hev_ret1]; dsimp only
                have hsz1 : sizeOfShapeWithContextHOL d15.structs
                    (shapeOfHOLExact (.rStruct [.val (.word bufw), .val (.word w1)] : ValueHOL 64)) ≤ 32 := by
                  simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
                rw [if_pos hsz1]
              have hite_branch : evaluateHOLFiniteState d14
                  ((ProgHOL.storeByte (.op .sub [ExpHOL.var VarKind.local (ofString "start"), .const 1])
                      (ExpHOL.var VarKind.local (ofString "tx_type"))).seq
                    (.return (.rstruct
                      [.op .sub [ExpHOL.var VarKind.local (ofString "start"), .const 1],
                       .op .add [ExpHOL.var VarKind.local (ofString "w"), .const 1]]))) =
                  (some (.returned (.rStruct [.val (.word bufw), .val (.word w1)])),
                   d15.emptyLocalsHOLFinite) := by
                rw [evaluateHOLFiniteState_seq_line780]
                simp only [hsb_tx_r, hret1]
              simp only [hite_branch]
              refine ⟨heff_s_d15.locals_clock _ _, fun v hv => ?_⟩
              simp only [Option.some.injEq, PanSemResultExact.returned.injEq] at hv
              subst hv
              refine ⟨bufw, w1, rfl, ?_, by omega, by omega⟩
              exact ⟨hbuf_lo, by change bufw.toNat + w1.toNat ≤ globN d15 "heap_ptr"; unfold globN at hd14_hp_ge ⊢; rw [hd15_g]; omega⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
