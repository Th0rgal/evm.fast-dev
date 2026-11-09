import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkScBoTxHelpers

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.EvmBase (stdKeep)
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8Leaves.Rlp

section Phases1To4EncodeTxBounded

open private txEnc_wordsOK_wordAt_memW txEnc_wordAt_memW_below_hp txEnc_wordsOK_below_hp
  accessListPayloadSumPure_congr authListPayloadSumPure_congr
  eval_decCall_tx_encode_bound txEncodeBoundPure
  accessListPayloadSumPure authListPayloadSumPure txEnc_eval_load_word_below_hp
  txEnc_eval_load_u256_below_hp txEnc_seq_non_timeout
  u256ByteLengthPure_bounds
  eval_call_local_tx_put_u256 eval_call_local_tx_put_to
  eval_call_local_tx_put_access_list eval_call_local_tx_put_blob_hashes
  eval_call_local_tx_put_authorizations
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeTransaction

private theorem txEnc_skip_hp {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {cont : ProgHOL 64} {pw : BitVec 64} {bound : Nat}
    (heff0 : HeapByteEff s0 s Rl gw)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hw : ∃ w_old : BitVec 64, s.locals.lookup (ofString "w") = some (.val (.word w_old)))
    (hnt : (evaluateHOLFiniteState s (.seq .skip cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (.seq .skip cont)).1) :
    ∃ (p' : BitVec 64) (m : PanSemStateFiniteExact 64 F),
      pw.toNat ≤ p'.toNat ∧ p'.toNat ≤ pw.toNat + bound ∧
      (∀ k, k ≠ ofString "w" → k ≠ ofString "p" → m.locals.lookup k = s.locals.lookup k) ∧
      (∃ w_f : BitVec 64, m.locals.lookup (ofString "w") = some (.val (.word w_f))) ∧
      m.locals.lookup (ofString "p") = some (.val (.word p')) ∧
      HeapByteEff s0 m Rl gw ∧
      globN s "heap_ptr" ≤ globN m "heap_ptr" ∧
      (evaluateHOLFiniteState m cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState m cont).1 ∧
      evaluateHOLFiniteState s (.seq .skip cont) = evaluateHOLFiniteState m cont := by
  have heq : evaluateHOLFiniteState s (.seq .skip cont) = evaluateHOLFiniteState s cont := by
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_skip]
  rw [heq] at hnt hres ⊢
  exact ⟨pw, s, le_rfl, Nat.le_add_right _ _, fun _ _ _ => rfl, hw, hp, heff0, le_rfl, hnt, hres, rfl⟩

private theorem txEnc_call_access_list_step_hp {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {cont : ProgHOL 64} {txw pw : BitVec 64}
    (hAR0 : ArenaReady s0)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hRl_ge : ∀ ivl ∈ Rl, 0 < ivl.2 → globN s0 "heap_ptr" ≤ ivl.1)
    (htx_ins : Inside (txw.toNat, 384) sourceBase (globN s0 "heap_ptr"))
    (htx_wok : WordsOK s0 (txw.toNat, 384))
    (hnal_lt : memW s0 (txw.toNat + 216) < 2 ^ 32)
    (hslots_lt : txAccessSlots s0 txw.toNat < 2 ^ 32)
    (hal_ins : 0 < memW s0 (txw.toNat + 216) →
      Inside (memW s0 (txw.toNat + 208), 24 * memW s0 (txw.toNat + 216)) sourceBase (globN s0 "heap_ptr"))
    (hal_wok : 0 < memW s0 (txw.toNat + 216) →
      WordsOK s0 (memW s0 (txw.toNat + 208), 24 * memW s0 (txw.toNat + 216)))
    (hmw208_lt : memW s0 (txw.toNat + 208) < 2 ^ 64)
    (htx : s.locals.lookup (ofString "tx") = some (.val (.word txw)))
    (hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hw : ∃ w_old : BitVec 64, s.locals.lookup (ofString "w") = some (.val (.word w_old)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ pw.toNat ∧
      pw.toNat + 9 + accessListPayloadSumPure s0 (memW s0 (txw.toNat + 208)) (memW s0 (txw.toNat + 216)) ≤
        ivl.1 + ivl.2 ∧ ivl.1 + ivl.2 ≤ heapLimit)
    (hnt : (evaluateHOLFiniteState s
      (.seq
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_access_list")
            [.var .local (ofString "p"),
             .load .one (.op .add [.var .local (ofString "tx"), .const 208#64]),
             .load .one (.op .add [.var .local (ofString "tx"), .const 216#64])])
          (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
        cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_access_list")
            [.var .local (ofString "p"),
             .load .one (.op .add [.var .local (ofString "tx"), .const 208#64]),
             .load .one (.op .add [.var .local (ofString "tx"), .const 216#64])])
          (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
        cont)).1) :
    ∃ (len : BitVec 64) (m : PanSemStateFiniteExact 64 F),
      len.toNat ≤ 9 + accessListPayloadSumPure s0 (memW s0 (txw.toNat + 208)) (memW s0 (txw.toNat + 216)) ∧
      (pw + len).toNat = pw.toNat + len.toNat ∧
      (∀ k, k ≠ ofString "w" → k ≠ ofString "p" → m.locals.lookup k = s.locals.lookup k) ∧
      (∃ w_f : BitVec 64, m.locals.lookup (ofString "w") = some (.val (.word w_f))) ∧
      m.locals.lookup (ofString "p") = some (.val (.word (pw + len))) ∧
      HeapByteEff s0 m Rl gw ∧
      globN s "heap_ptr" ≤ globN m "heap_ptr" ∧
      (evaluateHOLFiniteState m cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState m cont).1 ∧
      evaluateHOLFiniteState s
        (.seq
          (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_access_list")
              [.var .local (ofString "p"),
               .load .one (.op .add [.var .local (ofString "tx"), .const 208#64]),
               .load .one (.op .add [.var .local (ofString "tx"), .const 216#64])])
            (.assign .local (ofString "p")
              (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
          cont) = evaluateHOLFiniteState m cont := by
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  have h232 : (2 ^ 32 : Nat) = 4294967296 := rfl
  have hev_recs := txEnc_eval_load_word_below_hp hAR0 heff0 hRl_ge htx_ins htx_wok "tx" htx 208 (by decide) (by decide)
  have hev_n := txEnc_eval_load_word_below_hp hAR0 heff0 hRl_ge htx_ins htx_wok "tx" htx 216 (by decide) (by decide)
  let recsw := BitVec.ofNat 64 (memW s0 (txw.toNat + 208))
  let nw := BitVec.ofNat 64 (memW s0 (txw.toNat + 216))
  have hrecsw_nat : recsw.toNat = memW s0 (txw.toNat + 208) := by
    change (BitVec.ofNat 64 (memW s0 (txw.toNat + 208))).toNat = _
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hmw208_lt
  have hnw_nat : nw.toNat = memW s0 (txw.toNat + 216) := by
    change (BitVec.ofNat 64 (memW s0 (txw.toNat + 216))).toNat = _
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hbnd_hl := rlpHeaderLenPure_bounds (accessListPayloadSumPure s0 recsw.toNat nw.toNat)
  have hnt_1 := txEnc_seq_non_timeout s _ _ hnt
  have hnt_c := txEnc_seq_non_timeout s _ _ hnt_1
  have hc := eval_call_local_tx_put_access_list s0 s "w"
    (.var .local (ofString "p"))
    (.load .one (.op .add [.var .local (ofString "tx"), .const 208#64]))
    (.load .one (.op .add [.var .local (ofString "tx"), .const 216#64]))
    pw recsw nw Rl gw hAR0 heff0 hRl_ge hw
    (by simp [evalHOLExact, hp]) hev_recs hev_n
    (by rw [hnw_nat]; exact hnal_lt)
    (by rw [hrecsw_nat, hnw_nat]; exact hslots_lt)
    (by rw [hrecsw_nat, hnw_nat]; exact hal_ins)
    (by rw [hrecsw_nat, hnw_nat]; exact hal_wok)
    (by
      obtain ⟨ivl, hivl, h1, h2, h3⟩ := hin_ivl
      rw [hrecsw_nat, hnw_nat] at hbnd_hl ⊢
      exact ⟨ivl, hivl, h1, by omega, h3⟩)
    hnt_c
  dsimp only at hc
  exact txEnc_call_assign_p_step_hp heff0 hp
    (by obtain ⟨_, _, _, _, _⟩ := hin_ivl; omega)
    ⟨fun hnone => by
      obtain ⟨len, _, hlen_le, hloc, heff_c⟩ := hc.1 hnone
      rw [hrecsw_nat, hnw_nat] at hlen_le
      exact ⟨len, hlen_le, hloc, heff_c⟩, hc.2⟩
    hnt hres

private theorem txEnc_call_blob_hashes_step_hp {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {cont : ProgHOL 64} {txw pw : BitVec 64}
    (hAR0 : ArenaReady s0)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hRl_ge : ∀ ivl ∈ Rl, 0 < ivl.2 → globN s0 "heap_ptr" ≤ ivl.1)
    (htx_ins : Inside (txw.toNat, 384) sourceBase (globN s0 "heap_ptr"))
    (htx_wok : WordsOK s0 (txw.toNat, 384))
    (hnbh_lt : memW s0 (txw.toNat + 264) < 2 ^ 32)
    (htx : s.locals.lookup (ofString "tx") = some (.val (.word txw)))
    (hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hw : ∃ w_old : BitVec 64, s.locals.lookup (ofString "w") = some (.val (.word w_old)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ pw.toNat ∧
      pw.toNat + 9 + 33 * memW s0 (txw.toNat + 264) ≤ ivl.1 + ivl.2 ∧ ivl.1 + ivl.2 ≤ heapLimit)
    (hnt : (evaluateHOLFiniteState s
      (.seq
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_blob_hashes")
            [.var .local (ofString "p"),
             .load .one (.op .add [.var .local (ofString "tx"), .const 256#64]),
             .load .one (.op .add [.var .local (ofString "tx"), .const 264#64])])
          (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
        cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_blob_hashes")
            [.var .local (ofString "p"),
             .load .one (.op .add [.var .local (ofString "tx"), .const 256#64]),
             .load .one (.op .add [.var .local (ofString "tx"), .const 264#64])])
          (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
        cont)).1) :
    ∃ (len : BitVec 64) (m : PanSemStateFiniteExact 64 F),
      len.toNat ≤ 9 + 33 * memW s0 (txw.toNat + 264) ∧
      (pw + len).toNat = pw.toNat + len.toNat ∧
      (∀ k, k ≠ ofString "w" → k ≠ ofString "p" → m.locals.lookup k = s.locals.lookup k) ∧
      (∃ w_f : BitVec 64, m.locals.lookup (ofString "w") = some (.val (.word w_f))) ∧
      m.locals.lookup (ofString "p") = some (.val (.word (pw + len))) ∧
      HeapByteEff s0 m Rl gw ∧
      globN s "heap_ptr" ≤ globN m "heap_ptr" ∧
      (evaluateHOLFiniteState m cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState m cont).1 ∧
      evaluateHOLFiniteState s
        (.seq
          (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_blob_hashes")
              [.var .local (ofString "p"),
               .load .one (.op .add [.var .local (ofString "tx"), .const 256#64]),
               .load .one (.op .add [.var .local (ofString "tx"), .const 264#64])])
            (.assign .local (ofString "p")
              (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
          cont) = evaluateHOLFiniteState m cont := by
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  have h232 : (2 ^ 32 : Nat) = 4294967296 := rfl
  have hev_buf := txEnc_eval_load_word_below_hp hAR0 heff0 hRl_ge htx_ins htx_wok "tx" htx 256 (by decide) (by decide)
  have hev_n := txEnc_eval_load_word_below_hp hAR0 heff0 hRl_ge htx_ins htx_wok "tx" htx 264 (by decide) (by decide)
  let nw := BitVec.ofNat 64 (memW s0 (txw.toNat + 264))
  have hnw_nat : nw.toNat = memW s0 (txw.toNat + 264) := by
    change (BitVec.ofNat 64 (memW s0 (txw.toNat + 264))).toNat = _
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hbnd_hl := rlpHeaderLenPure_bounds (33 * nw.toNat)
  have hnt_1 := txEnc_seq_non_timeout s _ _ hnt
  have hnt_c := txEnc_seq_non_timeout s _ _ hnt_1
  have hc := eval_call_local_tx_put_blob_hashes s "w"
    (.var .local (ofString "p"))
    (.load .one (.op .add [.var .local (ofString "tx"), .const 256#64]))
    (.load .one (.op .add [.var .local (ofString "tx"), .const 264#64]))
    pw (BitVec.ofNat 64 (memW s0 (txw.toNat + 256))) nw
    Rl gw heff0.arena.1.code heff0.arena hw
    (by simp [evalHOLExact, hp]) hev_buf hev_n
    (by rw [hnw_nat]; exact hnbh_lt)
    (by
      obtain ⟨ivl, hivl, h1, h2, h3⟩ := hin_ivl
      rw [hnw_nat] at hbnd_hl ⊢
      exact ⟨ivl, hivl, h1, by omega, h3⟩)
    hnt_c
  dsimp only at hc
  exact txEnc_call_assign_p_step_hp heff0 hp
    (by obtain ⟨_, _, _, _, _⟩ := hin_ivl; omega)
    ⟨fun hnone => by
      obtain ⟨len, _, hlen_le, hloc, heff_c⟩ := hc.1 hnone
      rw [hnw_nat] at hlen_le
      exact ⟨len, hlen_le, hloc, heff_c⟩, hc.2⟩
    hnt hres

private theorem txEnc_call_authorizations_step_hp {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {cont : ProgHOL 64} {txw pw : BitVec 64}
    (hAR0 : ArenaReady s0)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hgw : "heap_ptr" ∈ gw)
    (hRl_ge : ∀ ivl ∈ Rl, 0 < ivl.2 → globN s0 "heap_ptr" ≤ ivl.1)
    (htx_ins : Inside (txw.toNat, 384) sourceBase (globN s0 "heap_ptr"))
    (htx_wok : WordsOK s0 (txw.toNat, 384))
    (hnau_lt : memW s0 (txw.toNat + 280) < 2 ^ 32)
    (hau_ins : 0 < memW s0 (txw.toNat + 280) →
      Inside (memW s0 (txw.toNat + 272), 120 * memW s0 (txw.toNat + 280)) sourceBase (globN s0 "heap_ptr"))
    (hau_wok : 0 < memW s0 (txw.toNat + 280) →
      WordsOK s0 (memW s0 (txw.toNat + 272), 120 * memW s0 (txw.toNat + 280)))
    (hmw272_lt : memW s0 (txw.toNat + 272) < 2 ^ 64)
    (htx : s.locals.lookup (ofString "tx") = some (.val (.word txw)))
    (hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hw : ∃ w_old : BitVec 64, s.locals.lookup (ofString "w") = some (.val (.word w_old)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ pw.toNat ∧
      pw.toNat + 9 + authListPayloadSumPure s0 (memW s0 (txw.toNat + 272)) (memW s0 (txw.toNat + 280)) ≤
        ivl.1 + ivl.2 ∧ ivl.1 + ivl.2 ≤ heapLimit)
    (hnt : (evaluateHOLFiniteState s
      (.seq
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_authorizations")
            [.var .local (ofString "p"),
             .load .one (.op .add [.var .local (ofString "tx"), .const 272#64]),
             .load .one (.op .add [.var .local (ofString "tx"), .const 280#64])])
          (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
        cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_authorizations")
            [.var .local (ofString "p"),
             .load .one (.op .add [.var .local (ofString "tx"), .const 272#64]),
             .load .one (.op .add [.var .local (ofString "tx"), .const 280#64])])
          (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
        cont)).1) :
    ∃ (len : BitVec 64) (m : PanSemStateFiniteExact 64 F),
      len.toNat ≤ 9 + authListPayloadSumPure s0 (memW s0 (txw.toNat + 272)) (memW s0 (txw.toNat + 280)) ∧
      (pw + len).toNat = pw.toNat + len.toNat ∧
      (∀ k, k ≠ ofString "w" → k ≠ ofString "p" → m.locals.lookup k = s.locals.lookup k) ∧
      (∃ w_f : BitVec 64, m.locals.lookup (ofString "w") = some (.val (.word w_f))) ∧
      m.locals.lookup (ofString "p") = some (.val (.word (pw + len))) ∧
      HeapByteEff s0 m Rl gw ∧
      globN s "heap_ptr" ≤ globN m "heap_ptr" ∧
      (evaluateHOLFiniteState m cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState m cont).1 ∧
      evaluateHOLFiniteState s
        (.seq
          (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_authorizations")
              [.var .local (ofString "p"),
               .load .one (.op .add [.var .local (ofString "tx"), .const 272#64]),
               .load .one (.op .add [.var .local (ofString "tx"), .const 280#64])])
            (.assign .local (ofString "p")
              (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
          cont) = evaluateHOLFiniteState m cont := by
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  have h232 : (2 ^ 32 : Nat) = 4294967296 := rfl
  have hev_recs := txEnc_eval_load_word_below_hp hAR0 heff0 hRl_ge htx_ins htx_wok "tx" htx 272 (by decide) (by decide)
  have hev_n := txEnc_eval_load_word_below_hp hAR0 heff0 hRl_ge htx_ins htx_wok "tx" htx 280 (by decide) (by decide)
  let recsw := BitVec.ofNat 64 (memW s0 (txw.toNat + 272))
  let nw := BitVec.ofNat 64 (memW s0 (txw.toNat + 280))
  have hrecsw_nat : recsw.toNat = memW s0 (txw.toNat + 272) := by
    change (BitVec.ofNat 64 (memW s0 (txw.toNat + 272))).toNat = _
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hmw272_lt
  have hnw_nat : nw.toNat = memW s0 (txw.toNat + 280) := by
    change (BitVec.ofNat 64 (memW s0 (txw.toNat + 280))).toNat = _
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hbnd_hl := rlpHeaderLenPure_bounds (authListPayloadSumPure s0 recsw.toNat nw.toNat)
  have hnt_1 := txEnc_seq_non_timeout s _ _ hnt
  have hnt_c := txEnc_seq_non_timeout s _ _ hnt_1
  have hc := eval_call_local_tx_put_authorizations s0 s "w"
    (.var .local (ofString "p"))
    (.load .one (.op .add [.var .local (ofString "tx"), .const 272#64]))
    (.load .one (.op .add [.var .local (ofString "tx"), .const 280#64]))
    pw recsw nw Rl gw hAR0 heff0 hgw hRl_ge hw
    (by simp [evalHOLExact, hp]) hev_recs hev_n
    (by rw [hnw_nat]; exact hnau_lt)
    (by rw [hrecsw_nat, hnw_nat]; exact hau_ins)
    (by rw [hrecsw_nat, hnw_nat]; exact hau_wok)
    (by
      obtain ⟨ivl, hivl, h1, h2, h3⟩ := hin_ivl
      rw [hrecsw_nat, hnw_nat] at hbnd_hl ⊢
      exact ⟨ivl, hivl, h1, by omega, h3⟩)
    hnt_c
  dsimp only at hc
  exact txEnc_call_assign_p_step_hp heff0 hp
    (by obtain ⟨_, _, _, _, _⟩ := hin_ivl; omega)
    ⟨fun hnone => by
      obtain ⟨len, _, hlen_le, hloc, heff_c⟩ := hc.1 hnone
      rw [hrecsw_nat, hnw_nat] at hlen_le
      exact ⟨len, hlen_le, hloc, heff_c⟩, hc.2⟩
    hnt hres

private theorem eval_tx_encode_generic_mode0_bounded_resumes {F : Type}
    (ent : PanSemStateFiniteExact 64 F) (tx0 : BitVec 64)
    (hAR_ent : ArenaReady ent)
    (htx_enc : TxValidEncodeAt ent tx0.toNat)
    (hent_tx : ent.locals.lookup (ofString "tx") = some (.val (.word tx0)))
    (hent_mode : ent.locals.lookup (ofString "mode") = some (.val (.word 0#64)))
    (hnt_body : (evaluateHOLFiniteState ent
      (sourceFnBody Guest.Software.guestFn_tx_encode_generic)).1 ≠ some .timeOut)
    (hres_body : Resumes (evaluateHOLFiniteState ent
      (sourceFnBody Guest.Software.guestFn_tx_encode_generic)).1) :
    TxEncBoundedOut ent [] ["heap_ptr"]
      (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_tx_encode_generic)) := by
  obtain ⟨htx_v, _, _, _, hal_enc, hbh_enc, hau_enc⟩ := htx_enc
  obtain ⟨htx_wok, htx_ins, htx_t_le, hdata_lt, hnal_lt, hslots_lt, hnbh_lt, hnau_lt, hal_wok, hau_wok⟩ := htx_v
  have hgw : "heap_ptr" ∈ (["heap_ptr"] : List String) := by simp
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  have h384_lt : 384 < 2 ^ 40 := by decide
  have hmw_lt64 : ∀ off, off % 8 = 0 → off + 8 ≤ 384 → memW ent (tx0.toNat + off) < 2 ^ 64 := by
    intro off hoff8 hoff_hi
    obtain ⟨⟨w, _, hm⟩, _, _⟩ := txEnc_wordsOK_wordAt_memW hAR_ent (M13.LocFrame.refl ent)
      htx_wok off hoff8 hoff_hi h384_lt
    unfold memW; rw [hm]; simp [w.isLt]
  have hb_gen : sourceFnBody Guest.Software.guestFn_tx_encode_generic =
      .decCall (ofString "bound") .one (ofString "tx_encode_bound") [.var .local (ofString "tx")]
        (.decCall (ofString "buf") .one (ofString "alloc") [.var .local (ofString "bound")]
          (.dec (ofString "body") .one (.op .add [.var .local (ofString "buf"), .const 10#64])
            (.dec (ofString "p") .one (.var .local (ofString "body"))
              (.dec (ofString "t") .one (.load .one (.op .add [.var .local (ofString "tx"), .const 0#64]))
                (.dec (ofString "w") .one (.const 0#64)
                  (.seq
                    (.ite (.cmp .notEqual (.var .local (ofString "t")) (.const 0#64))
                      (.seq
                        (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
                          [.var .local (ofString "p"),
                           .load .one (.op .add [.var .local (ofString "tx"), .const 8#64])])
                        (.assign .local (ofString "p")
                          (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
                      .skip)
                    (.seq
                      (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
                        [.var .local (ofString "p"),
                         .load (.comb [.one, .one, .one, .one])
                           (.op .add [.var .local (ofString "tx"), .const 16#64])])
                      (.seq
                        (.assign .local (ofString "p")
                          (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                        (.seq
                          (.ite (.cmp .notLower (.const 1#64) (.var .local (ofString "t")))
                            (.seq
                              (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
                                [.var .local (ofString "p"),
                                 .load (.comb [.one, .one, .one, .one])
                                   (.op .add [.var .local (ofString "tx"), .const 48#64])])
                              (.assign .local (ofString "p")
                                (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
                            (.seq
                              (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
                                [.var .local (ofString "p"),
                                 .load (.comb [.one, .one, .one, .one])
                                   (.op .add [.var .local (ofString "tx"), .const 80#64])])
                              (.seq
                                (.assign .local (ofString "p")
                                  (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                (.seq
                                  (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
                                    [.var .local (ofString "p"),
                                     .load (.comb [.one, .one, .one, .one])
                                       (.op .add [.var .local (ofString "tx"), .const 112#64])])
                                  (.assign .local (ofString "p")
                                    (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))))))
                          (.seq
                            (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
                              [.var .local (ofString "p"),
                               .load .one (.op .add [.var .local (ofString "tx"), .const 144#64])])
                            (.seq
                              (.assign .local (ofString "p")
                                (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                              (.seq
                                (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_to")
                                  [.var .local (ofString "p"),
                                   .load .one (.op .add [.var .local (ofString "tx"), .const 152#64])])
                                (.seq
                                  (.assign .local (ofString "p")
                                    (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                  (.seq
                                    (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
                                      [.var .local (ofString "p"),
                                       .load (.comb [.one, .one, .one, .one])
                                         (.op .add [.var .local (ofString "tx"), .const 160#64])])
                                    (.seq
                                      (.assign .local (ofString "p")
                                        (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                      (.seq
                                        (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
                                          [.var .local (ofString "p"),
                                           .load .one (.op .add [.var .local (ofString "tx"), .const 192#64]),
                                           .load .one (.op .add [.var .local (ofString "tx"), .const 200#64])])
                                        (.seq
                                          (.assign .local (ofString "p")
                                            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                          (.seq
                                            (.ite (.cmp .notEqual (.var .local (ofString "t")) (.const 0#64))
                                              (.seq
                                                (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_access_list")
                                                  [.var .local (ofString "p"),
                                                   .load .one (.op .add [.var .local (ofString "tx"), .const 208#64]),
                                                   .load .one (.op .add [.var .local (ofString "tx"), .const 216#64])])
                                                (.assign .local (ofString "p")
                                                  (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
                                              .skip)
                                            (.seq
                                              (.ite (.cmp .equal (.var .local (ofString "t")) (.const 3#64))
                                                (.seq
                                                  (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
                                                    [.var .local (ofString "p"),
                                                     .load (.comb [.one, .one, .one, .one])
                                                       (.op .add [.var .local (ofString "tx"), .const 224#64])])
                                                  (.seq
                                                    (.assign .local (ofString "p")
                                                      (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                                    (.seq
                                                      (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_blob_hashes")
                                                        [.var .local (ofString "p"),
                                                         .load .one (.op .add [.var .local (ofString "tx"), .const 256#64]),
                                                         .load .one (.op .add [.var .local (ofString "tx"), .const 264#64])])
                                                      (.assign .local (ofString "p")
                                                        (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))))
                                                .skip)
                                              (.seq
                                                (.ite (.cmp .equal (.var .local (ofString "t")) (.const 4#64))
                                                  (.seq
                                                    (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_authorizations")
                                                      [.var .local (ofString "p"),
                                                       .load .one (.op .add [.var .local (ofString "tx"), .const 272#64]),
                                                       .load .one (.op .add [.var .local (ofString "tx"), .const 280#64])])
                                                    (.assign .local (ofString "p")
                                                      (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
                                                  .skip)
                                                (.seq
                                                  (.ite (.cmp .equal (.var .local (ofString "mode")) (.const 0#64))
                                                    (.seq
                                                      (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
                                                        [.var .local (ofString "p"),
                                                         .load (.comb [.one, .one, .one, .one])
                                                           (.op .add [.var .local (ofString "tx"), .const 288#64])])
                                                      (.seq
                                                        (.assign .local (ofString "p")
                                                          (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                                        (.seq
                                                          (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
                                                            [.var .local (ofString "p"),
                                                             .load (.comb [.one, .one, .one, .one])
                                                               (.op .add [.var .local (ofString "tx"), .const 320#64])])
                                                          (.seq
                                                            (.assign .local (ofString "p")
                                                              (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                                            (.seq
                                                              (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
                                                                [.var .local (ofString "p"),
                                                                 .load (.comb [.one, .one, .one, .one])
                                                                   (.op .add [.var .local (ofString "tx"), .const 352#64])])
                                                              (.assign .local (ofString "p")
                                                                (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))))))
                                                    .skip)
                                                  (.seq
                                                    (.ite (.cmp .equal (.var .local (ofString "mode")) (.const 2#64))
                                                      (.seq
                                                        (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
                                                          [.var .local (ofString "p"), .var .local (ofString "chain_id")])
                                                        (.seq
                                                          (.assign .local (ofString "p")
                                                            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                                          (.seq
                                                            (.storeByte (.var .local (ofString "p")) (.const 128#64))
                                                            (.seq
                                                              (.storeByte (.op .add [.var .local (ofString "p"), .const 1#64]) (.const 128#64))
                                                              (.assign .local (ofString "p")
                                                                (.op .add [.var .local (ofString "p"), .const 2#64]))))))
                                                      .skip)
                                                    (.dec (ofString "payload_len") .one
                                                      (.op .sub [.var .local (ofString "p"), .var .local (ofString "body")])
                                                      (.decCall (ofString "hl") .one (ofString "rlp_list_header_len")
                                                        [.var .local (ofString "payload_len")]
                                                        (.dec (ofString "start") .one
                                                          (.op .sub [.var .local (ofString "body"), .var .local (ofString "hl")])
                                                          (.seq
                                                            (.call (some (none, none)) (ofString "rlp_encode_list_header")
                                                              [.var .local (ofString "start"), .var .local (ofString "payload_len")])
                                                            (.seq
                                                              (.ite (.cmp .notEqual (.var .local (ofString "t")) (.const 0#64))
                                                                (.seq
                                                                  (.assign .local (ofString "start")
                                                                    (.op .sub [.var .local (ofString "start"), .const 1#64]))
                                                                  (.storeByte (.var .local (ofString "start")) (.var .local (ofString "t"))))
                                                                .skip)
                                                              (.return (.rstruct [
                                                                .var .local (ofString "start"),
                                                                .op .sub [.var .local (ofString "p"), .var .local (ofString "start")]]))))))))))))))))))))))))))))) := rfl
  rw [hb_gen] at hnt_body hres_body ⊢
  obtain ⟨m1, hbnd_nat, hbnd_lt40, hm1_mem, hm1_loc, heff_m1_empty, hnt1, hdc_bnd⟩ :=
    eval_decCall_tx_encode_bound ent "bound" (.var .local (ofString "tx")) tx0 _ [] []
      hAR_ent ⟨htx_wok, htx_ins, htx_t_le, hdata_lt, hnal_lt, hslots_lt, hnbh_lt, hnau_lt, hal_wok, hau_wok⟩
      (by simp [evalHOLExact, hent_tx]) hnt_body
  rw [hdc_bnd] at hres_body; dsimp only at hres_body
  apply txEnc_eff_ret_of_eq_resVar hdc_bnd
  let bnd := BitVec.ofNat 64 (txEncodeBoundPure ent tx0.toNat)
  have hm1_bnd : m1.locals.lookup (ofString "bound") = some (.val (.word bnd)) := by
    rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, bnd]
  have hm1_tx : m1.locals.lookup (ofString "tx") = some (.val (.word tx0)) := by
    rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hent_tx,
      show ofString "bound" ≠ ofString "tx" from M13.mls_ne rfl]
  have hm1_mode : m1.locals.lookup (ofString "mode") = some (.val (.word 0#64)) := by
    rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hent_mode,
      show ofString "bound" ≠ ofString "mode" from M13.mls_ne rfl]
  have hm1_hp_eq : globN m1 "heap_ptr" = globN ent "heap_ptr" := by
    unfold globN; rw [← heff_m1_empty.globals (ofString "heap_ptr") (by simp)]
  obtain ⟨buf, bnd', q, m2_raw, hev_bnd', hbuf_hp_m1, hbuf8, hq_nat, hbuf_bnd_le_q, hq_le_hl,
      hq8, hm2_hp, hm2_glob, hm2_mem, hm2_loc, heff_m1_m2_empty, hnt2_raw, hres2_raw, hdc_alloc⟩ :=
    eval_decCall_alloc_resumes m1 "buf" (.var .local (ofString "bound")) _ [] ["heap_ptr"]
      heff_m1_empty.arena.1.code heff_m1_empty.arena hgw hnt1 hres_body
  have hbnd'_eq : bnd' = bnd := by simp [evalHOLExact, hm1_bnd] at hev_bnd'; exact hev_bnd'.symm
  subst hbnd'_eq
  rw [hdc_alloc] at hres_body; dsimp only at hres_body
  apply txEnc_eff_ret_of_eq_resVar hdc_alloc
  have hbuf_hp : buf.toNat = globN ent "heap_ptr" := hbuf_hp_m1.trans hm1_hp_eq
  have hbuf_lo : sourceBase ≤ buf.toNat := by rw [hbuf_hp]; exact hAR_ent.2.1
  have hbuf_bnd_le_hp_m2 : buf.toNat + bnd.toNat ≤ globN m2_raw "heap_ptr" := by
    rw [hm2_hp]; exact hbuf_bnd_le_q
  have hbuf_bnd_le_hl : buf.toNat + bnd.toNat ≤ heapLimit := le_trans hbuf_bnd_le_q hq_le_hl
  let Rl : List Ivl := [(buf.toNat, bnd.toNat)]
  have hRl_ge : ∀ ivl ∈ Rl, 0 < ivl.2 → globN ent "heap_ptr" ≤ ivl.1 := by
    intro ivl hivl _; simp [Rl] at hivl; subst hivl; rw [hbuf_hp]
  refine txEncBoundedOut_mono (R1 := Rl) (gw1 := ["heap_ptr"]) ?_ ?_ (fun _ h => h)
  swap
  · intro ivl hivl _; simp [Rl] at hivl; subst hivl; right; right; dsimp only
    rw [hbuf_hp]; exact ⟨le_rfl, hbuf_hp ▸ hbuf_bnd_le_hl⟩
  have heff_ent_m2 : HeapByteEff ent m2_raw Rl ["heap_ptr"] :=
    (heff_m1_empty.mono (fun _ h => False.elim (List.not_mem_nil h))
      (fun _ h => False.elim (List.not_mem_nil h))).trans
      (heff_m1_m2_empty.mono (fun _ h => False.elim (List.not_mem_nil h)) (fun _ h => h))
  let data_n := memW ent (tx0.toNat + 200)
  let al_sum := accessListPayloadSumPure ent (memW ent (tx0.toNat + 208)) (memW ent (tx0.toNat + 216))
  let au_sum := authListPayloadSumPure ent (memW ent (tx0.toNat + 272)) (memW ent (tx0.toNat + 280))
  let bh_sum := 33 * memW ent (tx0.toNat + 264)
  have hbnd_decomp : bnd.toNat = 655 + data_n + al_sum + au_sum + bh_sum := by rw [hbnd_nat]; rfl
  have hm2_buf : m2_raw.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hm2_tx : m2_raw.locals.lookup (ofString "tx") = some (.val (.word tx0)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_tx,
      show ofString "buf" ≠ ofString "tx" from M13.mls_ne rfl]
  have hm2_mode : m2_raw.locals.lookup (ofString "mode") = some (.val (.word 0#64)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_mode,
      show ofString "buf" ≠ ofString "mode" from M13.mls_ne rfl]
  rw [evaluateHOLFiniteState_dec_total] at hnt2_raw hres2_raw; dsimp only at hnt2_raw hres2_raw
  let bodyw : BitVec 64 := buf + 10#64
  have hbodyw_nat : bodyw.toNat = buf.toNat + 10 := by
    change (buf + 10#64).toNat = _; rw [BitVec.toNat_add]
    have h10 : (10#64 : BitVec 64).toNat = 10 := rfl
    rw [h10]; exact Nat.mod_eq_of_lt (by omega)
  have hev_body : @evalHOLExact 64 F _ m2_raw.toExact (fun a => Classical.propDecidable (m2_raw.memaddrs a))
      (.op .add [.var .local (ofString "buf"), .const 10#64]) = some (.val (.word bodyw)) := by
    simp [evalHOLExact, evalListHOLExact, hm2_buf, wordOpHOL, wordOp, valueIsWord, valueWord, bodyw]
  have hsh_body : shapeEqHOL .one (shapeOfHOLExact (.val (.word bodyw) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  have hdec_body : ∀ cont_b : ProgHOL 64,
      evaluateHOLFiniteState m2_raw
        (.dec (ofString "body") .one (.op .add [.var .local (ofString "buf"), .const 10#64]) cont_b) =
      ((evaluateHOLFiniteState (setVarHOLFinite (ofString "body") (.val (.word bodyw)) m2_raw) cont_b).1,
       { (evaluateHOLFiniteState (setVarHOLFinite (ofString "body") (.val (.word bodyw)) m2_raw) cont_b).2 with
         locals := (evaluateHOLFiniteState (setVarHOLFinite (ofString "body") (.val (.word bodyw)) m2_raw) cont_b).2.locals.resVarEq
           (ofString "body", m2_raw.locals.lookup (ofString "body")) }) := by
    intro cont_b; rw [evaluateHOLFiniteState_dec_total]; dsimp only; rw [hev_body]; dsimp only; rw [if_pos hsh_body]
  apply txEnc_eff_ret_of_eq_resVar (hdec_body _)
  rw [hev_body] at hnt2_raw hres2_raw; dsimp only at hnt2_raw hres2_raw
  rw [if_pos hsh_body] at hnt2_raw hres2_raw; dsimp only at hnt2_raw hres2_raw
  let m3 := setVarHOLFinite (ofString "body") (.val (.word bodyw)) m2_raw
  have heff_m3 : HeapByteEff ent m3 Rl ["heap_ptr"] := heff_ent_m2.locals_clock m3.locals m3.clock
  have hm3_body : m3.locals.lookup (ofString "body") = some (.val (.word bodyw)) := by
    simp [m3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hm3_tx : m3.locals.lookup (ofString "tx") = some (.val (.word tx0)) := by
    simp [m3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm2_tx,
      show ofString "body" ≠ ofString "tx" from M13.mls_ne rfl]
  have hm3_mode : m3.locals.lookup (ofString "mode") = some (.val (.word 0#64)) := by
    simp [m3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm2_mode,
      show ofString "body" ≠ ofString "mode" from M13.mls_ne rfl]
  have hev_p0 : @evalHOLExact 64 F _ m3.toExact (fun a => Classical.propDecidable (m3.memaddrs a))
      (.var .local (ofString "body")) = some (.val (.word bodyw)) := by simp [evalHOLExact, hm3_body]
  have hdec_p : ∀ cont_p : ProgHOL 64,
      evaluateHOLFiniteState m3 (.dec (ofString "p") .one (.var .local (ofString "body")) cont_p) =
      ((evaluateHOLFiniteState (setVarHOLFinite (ofString "p") (.val (.word bodyw)) m3) cont_p).1,
       { (evaluateHOLFiniteState (setVarHOLFinite (ofString "p") (.val (.word bodyw)) m3) cont_p).2 with
         locals := (evaluateHOLFiniteState (setVarHOLFinite (ofString "p") (.val (.word bodyw)) m3) cont_p).2.locals.resVarEq
           (ofString "p", m3.locals.lookup (ofString "p")) }) := by
    intro cont_p; rw [evaluateHOLFiniteState_dec_total]; dsimp only; rw [hev_p0]; dsimp only; rw [if_pos hsh_body]
  rw [hdec_p] at hnt2_raw hres2_raw; dsimp only at hnt2_raw hres2_raw
  apply txEnc_eff_ret_of_eq_resVar (hdec_p _)
  let m4 := setVarHOLFinite (ofString "p") (.val (.word bodyw)) m3
  have heff_m4 : HeapByteEff ent m4 Rl ["heap_ptr"] := heff_m3.locals_clock m4.locals m4.clock
  have hm4_p : m4.locals.lookup (ofString "p") = some (.val (.word bodyw)) := by
    simp [m4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hm4_body : m4.locals.lookup (ofString "body") = some (.val (.word bodyw)) := by
    simp [m4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm3_body,
      show ofString "p" ≠ ofString "body" from M13.mls_ne rfl]
  have hm4_tx : m4.locals.lookup (ofString "tx") = some (.val (.word tx0)) := by
    simp [m4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm3_tx,
      show ofString "p" ≠ ofString "tx" from M13.mls_ne rfl]
  have hm4_mode : m4.locals.lookup (ofString "mode") = some (.val (.word 0#64)) := by
    simp [m4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm3_mode,
      show ofString "p" ≠ ofString "mode" from M13.mls_ne rfl]
  let tw := BitVec.ofNat 64 (memW ent tx0.toNat)
  have htw_nat : tw.toNat = memW ent tx0.toNat := by
    dsimp [tw]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hev_t0 : @evalHOLExact 64 F _ m4.toExact (fun a => Classical.propDecidable (m4.memaddrs a))
      (.load .one (.op .add [.var .local (ofString "tx"), .const 0#64])) = some (.val (.word tw)) := by
    have h0 := txEnc_eval_load_word_below_hp hAR_ent heff_m4 hRl_ge htx_ins htx_wok "tx" hm4_tx 0 (by decide) (by decide)
    simp only [Nat.add_zero] at h0; exact h0
  have hsh_t : shapeEqHOL .one (shapeOfHOLExact (.val (.word tw) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  have hdec_t : ∀ cont_t : ProgHOL 64,
      evaluateHOLFiniteState m4
        (.dec (ofString "t") .one (.load .one (.op .add [.var .local (ofString "tx"), .const 0#64])) cont_t) =
      ((evaluateHOLFiniteState (setVarHOLFinite (ofString "t") (.val (.word tw)) m4) cont_t).1,
       { (evaluateHOLFiniteState (setVarHOLFinite (ofString "t") (.val (.word tw)) m4) cont_t).2 with
         locals := (evaluateHOLFiniteState (setVarHOLFinite (ofString "t") (.val (.word tw)) m4) cont_t).2.locals.resVarEq
           (ofString "t", m4.locals.lookup (ofString "t")) }) := by
    intro cont_t; rw [evaluateHOLFiniteState_dec_total]; dsimp only; rw [hev_t0]; dsimp only; rw [if_pos hsh_t]
  rw [hdec_t] at hnt2_raw hres2_raw; dsimp only at hnt2_raw hres2_raw
  apply txEnc_eff_ret_of_eq_resVar (hdec_t _)
  let m5 := setVarHOLFinite (ofString "t") (.val (.word tw)) m4
  have heff_m5 : HeapByteEff ent m5 Rl ["heap_ptr"] := heff_m4.locals_clock m5.locals m5.clock
  have hm5_t : m5.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [m5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hm5_p : m5.locals.lookup (ofString "p") = some (.val (.word bodyw)) := by
    simp [m5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm4_p,
      show ofString "t" ≠ ofString "p" from M13.mls_ne rfl]
  have hm5_body : m5.locals.lookup (ofString "body") = some (.val (.word bodyw)) := by
    simp [m5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm4_body,
      show ofString "t" ≠ ofString "body" from M13.mls_ne rfl]
  have hm5_tx : m5.locals.lookup (ofString "tx") = some (.val (.word tx0)) := by
    simp [m5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm4_tx,
      show ofString "t" ≠ ofString "tx" from M13.mls_ne rfl]
  have hm5_mode : m5.locals.lookup (ofString "mode") = some (.val (.word 0#64)) := by
    simp [m5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm4_mode,
      show ofString "t" ≠ ofString "mode" from M13.mls_ne rfl]
  have hsh_0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0#64) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  have hdec_w : ∀ cont_w : ProgHOL 64,
      evaluateHOLFiniteState m5 (.dec (ofString "w") .one (.const 0#64) cont_w) =
      ((evaluateHOLFiniteState (setVarHOLFinite (ofString "w") (.val (.word 0#64)) m5) cont_w).1,
       { (evaluateHOLFiniteState (setVarHOLFinite (ofString "w") (.val (.word 0#64)) m5) cont_w).2 with
         locals := (evaluateHOLFiniteState (setVarHOLFinite (ofString "w") (.val (.word 0#64)) m5) cont_w).2.locals.resVarEq
           (ofString "w", m5.locals.lookup (ofString "w")) }) := by
    intro cont_w; rw [evaluateHOLFiniteState_dec_total]; dsimp only
    have hc0 : @evalHOLExact 64 F _ m5.toExact (fun a => Classical.propDecidable (m5.memaddrs a)) (.const 0#64) =
        some (.val (.word 0#64)) := rfl
    rw [hc0]; dsimp only; rw [if_pos hsh_0]
  rw [hdec_w] at hnt2_raw hres2_raw; dsimp only at hnt2_raw hres2_raw
  apply txEnc_eff_ret_of_eq_resVar (hdec_w _)
  let s_cur0 := setVarHOLFinite (ofString "w") (.val (.word 0#64)) m5
  have heff0 : HeapByteEff ent s_cur0 Rl ["heap_ptr"] := heff_m5.locals_clock s_cur0.locals s_cur0.clock
  have hhp0 : buf.toNat + bnd.toNat ≤ globN s_cur0 "heap_ptr" := hbuf_bnd_le_hp_m2
  have hs0_w : ∃ w_f : BitVec 64, s_cur0.locals.lookup (ofString "w") = some (.val (.word w_f)) :=
    ⟨0#64, by simp [s_cur0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
  have hs0_t : s_cur0.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [s_cur0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm5_t,
      show ofString "w" ≠ ofString "t" from M13.mls_ne rfl]
  have hs0_p : s_cur0.locals.lookup (ofString "p") = some (.val (.word bodyw)) := by
    simp [s_cur0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm5_p,
      show ofString "w" ≠ ofString "p" from M13.mls_ne rfl]
  have hs0_body : s_cur0.locals.lookup (ofString "body") = some (.val (.word bodyw)) := by
    simp [s_cur0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm5_body,
      show ofString "w" ≠ ofString "body" from M13.mls_ne rfl]
  have hs0_tx : s_cur0.locals.lookup (ofString "tx") = some (.val (.word tx0)) := by
    simp [s_cur0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm5_tx,
      show ofString "w" ≠ ofString "tx" from M13.mls_ne rfl]
  have hs0_mode : s_cur0.locals.lookup (ofString "mode") = some (.val (.word 0#64)) := by
    simp [s_cur0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm5_mode,
      show ofString "w" ≠ ofString "mode" from M13.mls_ne rfl]
  have hRl_mem : (buf.toNat, bnd.toNat) ∈ Rl := by simp [Rl]
  have hne_tw : ofString "t" ≠ ofString "w" := M13.mls_ne rfl
  have hne_tp : ofString "t" ≠ ofString "p" := M13.mls_ne rfl
  have hne_bw : ofString "body" ≠ ofString "w" := M13.mls_ne rfl
  have hne_bp : ofString "body" ≠ ofString "p" := M13.mls_ne rfl
  have hne_txw : ofString "tx" ≠ ofString "w" := M13.mls_ne rfl
  have hne_txp : ofString "tx" ≠ ofString "p" := M13.mls_ne rfl
  have hne_mw : ofString "mode" ≠ ofString "w" := M13.mls_ne rfl
  have hne_mp : ofString "mode" ≠ ofString "p" := M13.mls_ne rfl
  -- Field 1
  obtain ⟨p1, s1, hp1_lo, hp1_hi, hs1_frame, hs1_w, hs1_p, heff1, hhp1, hnt1_s, hres1_s, heq1⟩ :=
    txEnc_ite_hp (bound := 9) heff0
      (cw := if tw ≠ 0#64 then 1#64 else 0#64)
      (by simp [evalHOLExact, hs0_t, Compiler.Encoders.Asm.wordCmpHOL])
      hs0_p
      (fun _ hnt_br hres_br => by
        obtain ⟨len, m, hlen_le, hadd, hfr, hw, hp, heff_m, hhp_m, hnt_m, hres_m, heq_m⟩ :=
          txEnc_call_word_step_hp 8 hAR_ent heff0 hRl_ge htx_ins htx_wok (by decide) (by decide)
            hs0_tx hs0_p hs0_w
            ⟨(buf.toNat, bnd.toNat), hRl_mem, by omega, by omega, hbuf_bnd_le_hl⟩
            hnt_br hres_br
        exact ⟨bodyw + len, m, by omega, by omega, hfr, hw, hp, heff_m, hhp_m, hnt_m, hres_m, heq_m⟩)
      (fun _ hnt_br hres_br => txEnc_skip_hp heff0 hs0_p hs0_w hnt_br hres_br)
      hnt2_raw hres2_raw
  rw [heq1]
  have hs1_t : s1.locals.lookup (ofString "t") = some (.val (.word tw)) :=
    (hs1_frame _ hne_tw hne_tp).trans hs0_t
  have hs1_body : s1.locals.lookup (ofString "body") = some (.val (.word bodyw)) :=
    (hs1_frame _ hne_bw hne_bp).trans hs0_body
  have hs1_tx : s1.locals.lookup (ofString "tx") = some (.val (.word tx0)) :=
    (hs1_frame _ hne_txw hne_txp).trans hs0_tx
  have hs1_mode : s1.locals.lookup (ofString "mode") = some (.val (.word 0#64)) :=
    (hs1_frame _ hne_mw hne_mp).trans hs0_mode
  -- Field 2
  obtain ⟨len2, s2, hlen2_le, hp2_add, hs2_frame, hs2_w, hs2_p, heff2, hhp2, hnt2_s, hres2_s, heq2⟩ :=
    txEnc_seq_call_u256_hp 16 hAR_ent heff1 hgw hRl_ge htx_ins htx_wok (by decide) (by decide)
      hs1_tx hs1_p hs1_w
      ⟨(buf.toNat, bnd.toNat), hRl_mem, by omega, by omega, hbuf_bnd_le_hl⟩
      hnt1_s hres1_s
  rw [heq2]
  set p2 := p1 + len2
  have hp2_lo : bodyw.toNat ≤ p2.toNat := by omega
  have hp2_hi : p2.toNat ≤ bodyw.toNat + 42 := by omega
  have hs2_t : s2.locals.lookup (ofString "t") = some (.val (.word tw)) :=
    (hs2_frame _ hne_tw hne_tp).trans hs1_t
  have hs2_body : s2.locals.lookup (ofString "body") = some (.val (.word bodyw)) :=
    (hs2_frame _ hne_bw hne_bp).trans hs1_body
  have hs2_tx : s2.locals.lookup (ofString "tx") = some (.val (.word tx0)) :=
    (hs2_frame _ hne_txw hne_txp).trans hs1_tx
  have hs2_mode : s2.locals.lookup (ofString "mode") = some (.val (.word 0#64)) :=
    (hs2_frame _ hne_mw hne_mp).trans hs1_mode
  -- Field 3
  obtain ⟨p3, s3, hp3_lo, hp3_hi_rel, hs3_frame, hs3_w, hs3_p, heff3, hhp3, hnt3_s, hres3_s, heq3⟩ :=
    txEnc_ite_hp (bound := 66) heff2
      (cw := if tw ≤ 1#64 then 1#64 else 0#64)
      (by simp [evalHOLExact, hs2_t, Compiler.Encoders.Asm.wordCmpHOL])
      hs2_p
      (fun _ hnt_br hres_br => by
        obtain ⟨len, m, hlen_le, hadd, hfr, hw, hp, heff_m, hhp_m, hnt_m, hres_m, heq_m⟩ :=
          txEnc_call_u256_step_hp 48 hAR_ent heff2 hgw hRl_ge htx_ins htx_wok (by decide) (by decide)
            hs2_tx hs2_p hs2_w
            ⟨(buf.toNat, bnd.toNat), hRl_mem, by omega, by omega, hbuf_bnd_le_hl⟩
            hnt_br hres_br
        exact ⟨p2 + len, m, by omega, by omega, hfr, hw, hp, heff_m, hhp_m, hnt_m, hres_m, heq_m⟩)
      (fun _ hnt_br hres_br => by
        have heq_assoc : ∀ (a b c d : ProgHOL 64),
            evaluateHOLFiniteState s2 (.seq (.seq a (.seq b c)) d) =
            evaluateHOLFiniteState s2 (.seq a (.seq b (.seq c d))) := by
          intro a b c d
          simp only [evaluateHOLFiniteState_seq_line780]
          cases evaluateHOLFiniteState s2 a with | mk ra sa =>
          cases ra with
          | some _ => rfl
          | none =>
            dsimp only
            cases evaluateHOLFiniteState sa b with | mk rb sb =>
            cases rb <;> rfl
        rw [heq_assoc] at hnt_br hres_br ⊢
        obtain ⟨lena, ma, hlena_le, hadda, hfra, hwa, hpa, heff_ma, hhp_ma, hnt_ma, hres_ma, heq_ma⟩ :=
          txEnc_seq_call_u256_hp 80 hAR_ent heff2 hgw hRl_ge htx_ins htx_wok (by decide) (by decide)
            hs2_tx hs2_p hs2_w
            ⟨(buf.toNat, bnd.toNat), hRl_mem, by omega, by omega, hbuf_bnd_le_hl⟩
            hnt_br hres_br
        have hma_tx : ma.locals.lookup (ofString "tx") = some (.val (.word tx0)) :=
          (hfra _ hne_txw hne_txp).trans hs2_tx
        obtain ⟨lenb, mb, hlenb_le, haddb, hfrb, hwb, hpb, heff_mb, hhp_mb, hnt_mb, hres_mb, heq_mb⟩ :=
          txEnc_call_u256_step_hp 112 hAR_ent heff_ma hgw hRl_ge htx_ins htx_wok (by decide) (by decide)
            hma_tx hpa hwa
            ⟨(buf.toNat, bnd.toNat), hRl_mem, by omega, by omega, hbuf_bnd_le_hl⟩
            hnt_ma hres_ma
        exact ⟨p2 + lena + lenb, mb, by omega, by omega,
          fun k hkw hkp => (hfrb k hkw hkp).trans (hfra k hkw hkp),
          hwb, hpb, heff_mb, le_trans hhp_ma hhp_mb, hnt_mb, hres_mb, heq_ma.trans heq_mb⟩)
      hnt2_s hres2_s
  rw [heq3]
  have hp3_ge_body : bodyw.toNat ≤ p3.toNat := le_trans hp2_lo hp3_lo
  have hp3_hi : p3.toNat ≤ bodyw.toNat + 108 := by omega
  have hs3_t : s3.locals.lookup (ofString "t") = some (.val (.word tw)) :=
    (hs3_frame _ hne_tw hne_tp).trans hs2_t
  have hs3_body : s3.locals.lookup (ofString "body") = some (.val (.word bodyw)) :=
    (hs3_frame _ hne_bw hne_bp).trans hs2_body
  have hs3_tx : s3.locals.lookup (ofString "tx") = some (.val (.word tx0)) :=
    (hs3_frame _ hne_txw hne_txp).trans hs2_tx
  have hs3_mode : s3.locals.lookup (ofString "mode") = some (.val (.word 0#64)) :=
    (hs3_frame _ hne_mw hne_mp).trans hs2_mode
  -- Field 4
  obtain ⟨len4, s4, hlen4_le, hp4_add, hs4_frame, hs4_w, hs4_p, heff4, hhp4, hnt4_s, hres4_s, heq4⟩ :=
    txEnc_seq_call_word_hp 144 hAR_ent heff3 hRl_ge htx_ins htx_wok (by decide) (by decide)
      hs3_tx hs3_p hs3_w
      ⟨(buf.toNat, bnd.toNat), hRl_mem, by omega, by omega, hbuf_bnd_le_hl⟩
      hnt3_s hres3_s
  rw [heq4]
  set p4 := p3 + len4
  have hp4_lo : bodyw.toNat ≤ p4.toNat := by omega
  have hp4_hi : p4.toNat ≤ bodyw.toNat + 117 := by omega
  have hs4_t : s4.locals.lookup (ofString "t") = some (.val (.word tw)) :=
    (hs4_frame _ hne_tw hne_tp).trans hs3_t
  have hs4_body : s4.locals.lookup (ofString "body") = some (.val (.word bodyw)) :=
    (hs4_frame _ hne_bw hne_bp).trans hs3_body
  have hs4_tx : s4.locals.lookup (ofString "tx") = some (.val (.word tx0)) :=
    (hs4_frame _ hne_txw hne_txp).trans hs3_tx
  have hs4_mode : s4.locals.lookup (ofString "mode") = some (.val (.word 0#64)) :=
    (hs4_frame _ hne_mw hne_mp).trans hs3_mode
  -- Field 5
  obtain ⟨len5, s5, hlen5_le, hp5_add, hs5_frame, hs5_w, hs5_p, heff5, hhp5, hnt5_s, hres5_s, heq5⟩ :=
    txEnc_seq_call_to_hp 152 hAR_ent heff4 hRl_ge htx_ins htx_wok (by decide) (by decide)
      hs4_tx hs4_p hs4_w
      ⟨(buf.toNat, bnd.toNat), hRl_mem, by omega, by omega, hbuf_bnd_le_hl⟩
      hnt4_s hres4_s
  rw [heq5]
  set p5 := p4 + len5
  have hp5_lo : bodyw.toNat ≤ p5.toNat := by omega
  have hp5_hi : p5.toNat ≤ bodyw.toNat + 138 := by omega
  have hs5_t : s5.locals.lookup (ofString "t") = some (.val (.word tw)) :=
    (hs5_frame _ hne_tw hne_tp).trans hs4_t
  have hs5_body : s5.locals.lookup (ofString "body") = some (.val (.word bodyw)) :=
    (hs5_frame _ hne_bw hne_bp).trans hs4_body
  have hs5_tx : s5.locals.lookup (ofString "tx") = some (.val (.word tx0)) :=
    (hs5_frame _ hne_txw hne_txp).trans hs4_tx
  have hs5_mode : s5.locals.lookup (ofString "mode") = some (.val (.word 0#64)) :=
    (hs5_frame _ hne_mw hne_mp).trans hs4_mode
  -- Field 6
  obtain ⟨len6, s6, hlen6_le, hp6_add, hs6_frame, hs6_w, hs6_p, heff6, hhp6, hnt6_s, hres6_s, heq6⟩ :=
    txEnc_seq_call_u256_hp 160 hAR_ent heff5 hgw hRl_ge htx_ins htx_wok (by decide) (by decide)
      hs5_tx hs5_p hs5_w
      ⟨(buf.toNat, bnd.toNat), hRl_mem, by omega, by omega, hbuf_bnd_le_hl⟩
      hnt5_s hres5_s
  rw [heq6]
  set p6 := p5 + len6
  have hp6_lo : bodyw.toNat ≤ p6.toNat := by omega
  have hp6_hi : p6.toNat ≤ bodyw.toNat + 171 := by omega
  have hs6_t : s6.locals.lookup (ofString "t") = some (.val (.word tw)) :=
    (hs6_frame _ hne_tw hne_tp).trans hs5_t
  have hs6_body : s6.locals.lookup (ofString "body") = some (.val (.word bodyw)) :=
    (hs6_frame _ hne_bw hne_bp).trans hs5_body
  have hs6_tx : s6.locals.lookup (ofString "tx") = some (.val (.word tx0)) :=
    (hs6_frame _ hne_txw hne_txp).trans hs5_tx
  have hs6_mode : s6.locals.lookup (ofString "mode") = some (.val (.word 0#64)) :=
    (hs6_frame _ hne_mw hne_mp).trans hs5_mode
  -- Field 7
  obtain ⟨len7, s7, hlen7_le, hp7_add, hs7_frame, hs7_w, hs7_p, heff7, hhp7, hnt7_s, hres7_s, heq7⟩ :=
    txEnc_seq_call_bytes_hp hAR_ent heff6 hRl_ge htx_ins htx_wok hdata_lt
      hs6_tx hs6_p hs6_w
      ⟨(buf.toNat, bnd.toNat), hRl_mem, by omega, by
        have : memW ent (tx0.toNat + 200) = data_n := rfl
        omega, hbuf_bnd_le_hl⟩
      hnt6_s hres6_s
  rw [heq7]
  set p7 := p6 + len7
  have hp7_lo : bodyw.toNat ≤ p7.toNat := by omega
  have hp7_hi : p7.toNat ≤ bodyw.toNat + 180 + data_n := by
    have : memW ent (tx0.toNat + 200) = data_n := rfl
    omega
  have hs7_t : s7.locals.lookup (ofString "t") = some (.val (.word tw)) :=
    (hs7_frame _ hne_tw hne_tp).trans hs6_t
  have hs7_body : s7.locals.lookup (ofString "body") = some (.val (.word bodyw)) :=
    (hs7_frame _ hne_bw hne_bp).trans hs6_body
  have hs7_tx : s7.locals.lookup (ofString "tx") = some (.val (.word tx0)) :=
    (hs7_frame _ hne_txw hne_txp).trans hs6_tx
  have hs7_mode : s7.locals.lookup (ofString "mode") = some (.val (.word 0#64)) :=
    (hs7_frame _ hne_mw hne_mp).trans hs6_mode
  -- Field 8
  obtain ⟨p8, s8, hp8_lo, hp8_hi_rel, hs8_frame, hs8_w, hs8_p, heff8, hhp8, hnt8_s, hres8_s, heq8⟩ :=
    txEnc_ite_hp (bound := 9 + al_sum) heff7
      (cw := if tw ≠ 0#64 then 1#64 else 0#64)
      (by simp [evalHOLExact, hs7_t, Compiler.Encoders.Asm.wordCmpHOL])
      hs7_p
      (fun _ hnt_br hres_br => by
        obtain ⟨len, m, hlen_le, hadd, hfr, hw, hp, heff_m, hhp_m, hnt_m, hres_m, heq_m⟩ :=
          txEnc_call_access_list_step_hp hAR_ent heff7 hRl_ge htx_ins htx_wok
            hnal_lt hslots_lt (fun hpos => (hal_enc hpos).1) hal_wok
            (hmw_lt64 208 (by decide) (by decide))
            hs7_tx hs7_p hs7_w
            ⟨(buf.toNat, bnd.toNat), hRl_mem, by omega, by
              have : accessListPayloadSumPure ent (memW ent (tx0.toNat + 208)) (memW ent (tx0.toNat + 216)) = al_sum := rfl
              omega, hbuf_bnd_le_hl⟩
            hnt_br hres_br
        have : accessListPayloadSumPure ent (memW ent (tx0.toNat + 208)) (memW ent (tx0.toNat + 216)) = al_sum := rfl
        exact ⟨p7 + len, m, by omega, by omega, hfr, hw, hp, heff_m, hhp_m, hnt_m, hres_m, heq_m⟩)
      (fun _ hnt_br hres_br => txEnc_skip_hp heff7 hs7_p hs7_w hnt_br hres_br)
      hnt7_s hres7_s
  rw [heq8]
  have hp8_ge_body : bodyw.toNat ≤ p8.toNat := le_trans hp7_lo hp8_lo
  have hp8_hi : p8.toNat ≤ bodyw.toNat + 189 + data_n + al_sum := by omega
  have hs8_t : s8.locals.lookup (ofString "t") = some (.val (.word tw)) :=
    (hs8_frame _ hne_tw hne_tp).trans hs7_t
  have hs8_body : s8.locals.lookup (ofString "body") = some (.val (.word bodyw)) :=
    (hs8_frame _ hne_bw hne_bp).trans hs7_body
  have hs8_tx : s8.locals.lookup (ofString "tx") = some (.val (.word tx0)) :=
    (hs8_frame _ hne_txw hne_txp).trans hs7_tx
  have hs8_mode : s8.locals.lookup (ofString "mode") = some (.val (.word 0#64)) :=
    (hs8_frame _ hne_mw hne_mp).trans hs7_mode
  -- Field 9
  obtain ⟨p9, s9, hp9_lo, hp9_hi_rel, hs9_frame, hs9_w, hs9_p, heff9, hhp9, hnt9_s, hres9_s, heq9⟩ :=
    txEnc_ite_hp (bound := 42 + bh_sum) heff8
      (cw := if tw = 3#64 then 1#64 else 0#64)
      (by simp [evalHOLExact, hs8_t, Compiler.Encoders.Asm.wordCmpHOL])
      hs8_p
      (fun _ hnt_br hres_br => by
        have heq_assoc : ∀ (a b c d : ProgHOL 64),
            evaluateHOLFiniteState s8 (.seq (.seq a (.seq b c)) d) =
            evaluateHOLFiniteState s8 (.seq a (.seq b (.seq c d))) := by
          intro a b c d
          simp only [evaluateHOLFiniteState_seq_line780]
          cases evaluateHOLFiniteState s8 a with | mk ra sa =>
          cases ra with
          | some _ => rfl
          | none =>
            dsimp only
            cases evaluateHOLFiniteState sa b with | mk rb sb =>
            cases rb <;> rfl
        rw [heq_assoc] at hnt_br hres_br ⊢
        obtain ⟨lena, ma, hlena_le, hadda, hfra, hwa, hpa, heff_ma, hhp_ma, hnt_ma, hres_ma, heq_ma⟩ :=
          txEnc_seq_call_u256_hp 224 hAR_ent heff8 hgw hRl_ge htx_ins htx_wok (by decide) (by decide)
            hs8_tx hs8_p hs8_w
            ⟨(buf.toNat, bnd.toNat), hRl_mem, by omega, by omega, hbuf_bnd_le_hl⟩
            hnt_br hres_br
        have hma_tx : ma.locals.lookup (ofString "tx") = some (.val (.word tx0)) :=
          (hfra _ hne_txw hne_txp).trans hs8_tx
        obtain ⟨lenb, mb, hlenb_le, haddb, hfrb, hwb, hpb, heff_mb, hhp_mb, hnt_mb, hres_mb, heq_mb⟩ :=
          txEnc_call_blob_hashes_step_hp hAR_ent heff_ma hRl_ge htx_ins htx_wok hnbh_lt
            hma_tx hpa hwa
            ⟨(buf.toNat, bnd.toNat), hRl_mem, by omega, by
              have : 33 * memW ent (tx0.toNat + 264) = bh_sum := rfl
              omega, hbuf_bnd_le_hl⟩
            hnt_ma hres_ma
        have : 33 * memW ent (tx0.toNat + 264) = bh_sum := rfl
        exact ⟨p8 + lena + lenb, mb, by omega, by omega,
          fun k hkw hkp => (hfrb k hkw hkp).trans (hfra k hkw hkp),
          hwb, hpb, heff_mb, le_trans hhp_ma hhp_mb, hnt_mb, hres_mb, heq_ma.trans heq_mb⟩)
      (fun _ hnt_br hres_br => txEnc_skip_hp heff8 hs8_p hs8_w hnt_br hres_br)
      hnt8_s hres8_s
  rw [heq9]
  have hp9_ge_body : bodyw.toNat ≤ p9.toNat := le_trans hp8_ge_body hp9_lo
  have hp9_hi : p9.toNat ≤ bodyw.toNat + 231 + data_n + al_sum + bh_sum := by omega
  have hs9_t : s9.locals.lookup (ofString "t") = some (.val (.word tw)) :=
    (hs9_frame _ hne_tw hne_tp).trans hs8_t
  have hs9_body : s9.locals.lookup (ofString "body") = some (.val (.word bodyw)) :=
    (hs9_frame _ hne_bw hne_bp).trans hs8_body
  have hs9_tx : s9.locals.lookup (ofString "tx") = some (.val (.word tx0)) :=
    (hs9_frame _ hne_txw hne_txp).trans hs8_tx
  have hs9_mode : s9.locals.lookup (ofString "mode") = some (.val (.word 0#64)) :=
    (hs9_frame _ hne_mw hne_mp).trans hs8_mode
  -- Field 10
  obtain ⟨p10, s10, hp10_lo, hp10_hi_rel, hs10_frame, hs10_w, hs10_p, heff10, hhp10, hnt10_s, hres10_s, heq10⟩ :=
    txEnc_ite_hp (bound := 9 + au_sum) heff9
      (cw := if tw = 4#64 then 1#64 else 0#64)
      (by simp [evalHOLExact, hs9_t, Compiler.Encoders.Asm.wordCmpHOL])
      hs9_p
      (fun hc_t4 hnt_br hres_br => by
        have htw4 : tw = 4#64 := by
          by_contra hne4; simp [hne4] at hc_t4
        have hmem_t4 : memW ent tx0.toNat = 4 := by
          rw [← htw_nat, htw4]; rfl
        obtain ⟨len, m, hlen_le, hadd, hfr, hw, hp, heff_m, hhp_m, hnt_m, hres_m, heq_m⟩ :=
          txEnc_call_authorizations_step_hp hAR_ent heff9 hgw hRl_ge htx_ins htx_wok
            hnau_lt (fun hpos => (hau_enc ⟨hmem_t4, hpos⟩).1) hau_wok
            (hmw_lt64 272 (by decide) (by decide))
            hs9_tx hs9_p hs9_w
            ⟨(buf.toNat, bnd.toNat), hRl_mem, by omega, by
              have : authListPayloadSumPure ent (memW ent (tx0.toNat + 272)) (memW ent (tx0.toNat + 280)) = au_sum := rfl
              omega, hbuf_bnd_le_hl⟩
            hnt_br hres_br
        have : authListPayloadSumPure ent (memW ent (tx0.toNat + 272)) (memW ent (tx0.toNat + 280)) = au_sum := rfl
        exact ⟨p9 + len, m, by omega, by omega, hfr, hw, hp, heff_m, hhp_m, hnt_m, hres_m, heq_m⟩)
      (fun _ hnt_br hres_br => txEnc_skip_hp heff9 hs9_p hs9_w hnt_br hres_br)
      hnt9_s hres9_s
  rw [heq10]
  have hp10_ge_body : bodyw.toNat ≤ p10.toNat := le_trans hp9_ge_body hp10_lo
  have hp10_hi : p10.toNat ≤ bodyw.toNat + 240 + data_n + al_sum + bh_sum + au_sum := by omega
  have hs10_t : s10.locals.lookup (ofString "t") = some (.val (.word tw)) :=
    (hs10_frame _ hne_tw hne_tp).trans hs9_t
  have hs10_body : s10.locals.lookup (ofString "body") = some (.val (.word bodyw)) :=
    (hs10_frame _ hne_bw hne_bp).trans hs9_body
  have hs10_tx : s10.locals.lookup (ofString "tx") = some (.val (.word tx0)) :=
    (hs10_frame _ hne_txw hne_txp).trans hs9_tx
  have hs10_mode : s10.locals.lookup (ofString "mode") = some (.val (.word 0#64)) :=
    (hs10_frame _ hne_mw hne_mp).trans hs9_mode
  -- Field 11
  obtain ⟨p11, s11, hp11_lo, hp11_hi_rel, hs11_frame, hs11_w, hs11_p, heff11, hhp11, hnt11_s, hres11_s, heq11⟩ :=
    txEnc_ite_hp (bound := 99) heff10
      (cw := 1#64)
      (by simp [evalHOLExact, hs10_mode, Compiler.Encoders.Asm.wordCmpHOL])
      hs10_p
      (fun _ hnt_br hres_br => by
        have heq_assoc3 : ∀ (a1 a2 b1 b2 c d : ProgHOL 64),
            evaluateHOLFiniteState s10 (.seq (.seq a1 (.seq a2 (.seq b1 (.seq b2 c)))) d) =
            evaluateHOLFiniteState s10 (.seq a1 (.seq a2 (.seq b1 (.seq b2 (.seq c d))))) := by
          intro a1 a2 b1 b2 c d
          simp only [evaluateHOLFiniteState_seq_line780]
          cases evaluateHOLFiniteState s10 a1 with | mk ra1 sa1 =>
          cases ra1 with
          | some _ => rfl
          | none =>
            dsimp only
            cases evaluateHOLFiniteState sa1 a2 with | mk ra2 sa2 =>
            cases ra2 with
            | some _ => rfl
            | none =>
              dsimp only
              cases evaluateHOLFiniteState sa2 b1 with | mk rb1 sb1 =>
              cases rb1 with
              | some _ => rfl
              | none =>
                dsimp only
                cases evaluateHOLFiniteState sb1 b2 with | mk rb2 sb2 =>
                cases rb2 <;> rfl
        rw [heq_assoc3] at hnt_br hres_br ⊢
        obtain ⟨lena, ma, hlena_le, hadda, hfra, hwa, hpa, heff_ma, hhp_ma, hnt_ma, hres_ma, heq_ma⟩ :=
          txEnc_seq_call_u256_hp 288 hAR_ent heff10 hgw hRl_ge htx_ins htx_wok (by decide) (by decide)
            hs10_tx hs10_p hs10_w
            ⟨(buf.toNat, bnd.toNat), hRl_mem, by omega, by omega, hbuf_bnd_le_hl⟩
            hnt_br hres_br
        have hma_tx : ma.locals.lookup (ofString "tx") = some (.val (.word tx0)) :=
          (hfra _ hne_txw hne_txp).trans hs10_tx
        obtain ⟨lenb, mb, hlenb_le, haddb, hfrb, hwb, hpb, heff_mb, hhp_mb, hnt_mb, hres_mb, heq_mb⟩ :=
          txEnc_seq_call_u256_hp 320 hAR_ent heff_ma hgw hRl_ge htx_ins htx_wok (by decide) (by decide)
            hma_tx hpa hwa
            ⟨(buf.toNat, bnd.toNat), hRl_mem, by omega, by omega, hbuf_bnd_le_hl⟩
            hnt_ma hres_ma
        have hmb_tx : mb.locals.lookup (ofString "tx") = some (.val (.word tx0)) :=
          (hfrb _ hne_txw hne_txp).trans hma_tx
        obtain ⟨lenc, mc, hlenc_le, haddc, hfrc, hwc, hpc, heff_mc, hhp_mc, hnt_mc, hres_mc, heq_mc⟩ :=
          txEnc_call_u256_step_hp 352 hAR_ent heff_mb hgw hRl_ge htx_ins htx_wok (by decide) (by decide)
            hmb_tx hpb hwb
            ⟨(buf.toNat, bnd.toNat), hRl_mem, by omega, by omega, hbuf_bnd_le_hl⟩
            hnt_mb hres_mb
        exact ⟨p10 + lena + lenb + lenc, mc, by omega, by omega,
          fun k hkw hkp => (hfrc k hkw hkp).trans ((hfrb k hkw hkp).trans (hfra k hkw hkp)),
          hwc, hpc, heff_mc, le_trans hhp_ma (le_trans hhp_mb hhp_mc), hnt_mc, hres_mc,
          heq_ma.trans (heq_mb.trans heq_mc)⟩)
      (fun hc0 => by cases hc0)
      hnt10_s hres10_s
  rw [heq11]
  have hp11_ge_body : bodyw.toNat ≤ p11.toNat := le_trans hp10_ge_body hp11_lo
  have hp11_le_end : p11.toNat ≤ buf.toNat + bnd.toNat := by omega
  have hs11_t : s11.locals.lookup (ofString "t") = some (.val (.word tw)) :=
    (hs11_frame _ hne_tw hne_tp).trans hs10_t
  have hs11_body : s11.locals.lookup (ofString "body") = some (.val (.word bodyw)) :=
    (hs11_frame _ hne_bw hne_bp).trans hs10_body
  have hs11_mode : s11.locals.lookup (ofString "mode") = some (.val (.word 0#64)) :=
    (hs11_frame _ hne_mw hne_mp).trans hs10_mode
  -- Field 12
  obtain ⟨p12, s12, hp12_lo, hp12_hi_rel, hs12_frame, _, hs12_p, heff12, hhp12, hnt12_s, hres12_s, heq12⟩ :=
    txEnc_ite_hp (bound := 0) heff11
      (cw := 0#64)
      (by simp [evalHOLExact, hs11_mode, Compiler.Encoders.Asm.wordCmpHOL])
      hs11_p
      (fun hc1 => False.elim (hc1 rfl))
      (fun _ hnt_br hres_br => txEnc_skip_hp heff11 hs11_p hs11_w hnt_br hres_br)
      hnt11_s hres11_s
  rw [heq12]
  have hs12_t : s12.locals.lookup (ofString "t") = some (.val (.word tw)) :=
    (hs12_frame _ hne_tw hne_tp).trans hs11_t
  have hs12_body : s12.locals.lookup (ofString "body") = some (.val (.word bodyw)) :=
    (hs12_frame _ hne_bw hne_bp).trans hs11_body
  have hbuf_bnd_le_hp12 : buf.toNat + bnd.toNat ≤ globN s12 "heap_ptr" := by omega
  exact txEnc_trailer_bounded_resumes heff12 hRl_mem hbuf_lo (by omega) hbuf_bnd_le_hp12 hbuf_bnd_le_hl
    hbodyw_nat (le_trans hp11_ge_body hp12_lo) (by omega) hs12_p hs12_body hs12_t hnt12_s hres12_s

/-- Strengthened `WorldKeeps` for `encode_transaction` exposing `RetTxSliceBounded`
(`PtxBlockOutUnhit` + returned `(a, b)` inside `[sourceBase, heap_ptr)` with `a, b < 2^40`). -/
theorem «wk_encode_transaction_bounded» :
    WorldKeeps (fun s => WorldOK s ∧ TxValidEncodeReady s) (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
     ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    RetTxSliceBounded (ofString "encode_transaction") := by
  refine ⟨_, _, _, lookup_encode_transaction_strong,
    fun {F} s hcode hW hparams hnt hres => ?_⟩
  have hWOK : WorldOK s := hW.1
  suffices hmain : TxEncBoundedOut s ([] ++ ([] : List (String × Nat)).map (bufferRegion s)) ["heap_ptr"]
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_encode_transaction)) by
    exact hmain.1.to_worldStep (R := fun _ => []) (B := [])
      (by intro _ h; cases h) (by intro g hg; simp at hg; exact Or.inl hg)
      hWOK (fun _ _ _ _ _ => ⟨ptxBlockOutUnhit_of_heapByteEff hWOK hmain.1 (by intro _ h; simp at h), hmain.2⟩)
  simp only [List.append_nil, List.map_nil]
  have hbody : sourceFnBody Guest.Software.guestFn_encode_transaction =
      .call none (ofString "tx_encode_generic")
        [.var .local (ofString "tx"), .const 0, .const 0] := rfl
  rw [hbody] at hnt hres ⊢
  rw [evaluateHOLFiniteState_call] at hnt hres ⊢
  obtain ⟨vals, hl_tx⟩ := hparams
  obtain ⟨tx0, _, htx0⟩ := lookupCode_one_word_any lookup_encode_transaction_strong hl_tx
  have hAR : ArenaReady s := hW.1.1
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "tx"), .const 0, .const 0] =
      some [.val (.word tx0), .val (.word 0#64), .val (.word 0#64)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, htx0]
  rw [ha] at hnt hres ⊢
  have hlk : lookupCodeHOLFinite s.code.lookup (ofString "tx_encode_generic")
      [.val (.word tx0), .val (.word 0#64), .val (.word 0#64)] =
      some (sourceFnBody Guest.Software.guestFn_tx_encode_generic,
        ((HolFiniteMapExact.empty.update (ofString "tx", ValueHOL.val (.word tx0))).update
          (ofString "mode", ValueHOL.val (.word 0#64))).update
          (ofString "chain_id", ValueHOL.val (.word 0#64)),
        .comb [.one, .one]) := by
    have hraw : lookupCodeHOLExact s.code.lookup (ofString "tx_encode_generic")
        [.val (.word tx0), .val (.word 0#64), .val (.word 0#64)] =
        some (sourceFnBody Guest.Software.guestFn_tx_encode_generic,
          (fun key => if key = ofString "chain_id" then some (.val (.word 0#64))
            else if key = ofString "mode" then some (.val (.word 0#64))
            else if key = ofString "tx" then some (.val (.word tx0)) else none),
          .comb [.one, .one]) := by
      have hne1 : ofString "tx" ≠ ofString "mode" := by decide
      have hne2 : ofString "tx" ≠ ofString "chain_id" := by decide
      have hne3 : ofString "mode" ≠ ofString "chain_id" := by decide
      simp [lookupCodeHOLExact, hcode, lookup_tx_encode_generic, shapeOfHOLExact, shapeEqHOL,
        shapeEqHOL.shapeEqListHOL, hne1, hne2, hne3]
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite
    split
    · rename_i missing; rw [hraw] at missing; cases missing
    · rename_i foundBody foundLocals foundShape found
      have equal := Option.some.inj (found.symm.trans hraw)
      obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
      apply congrArg (fun locals => some (sourceFnBody Guest.Software.guestFn_tx_encode_generic, locals, ShapeHOL.comb [.one, .one]))
      apply HolFiniteMapExact.ext; funext key
      by_cases hc : key = ofString "chain_id"
      · subst key; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]
      · by_cases hm : key = ofString "mode"
        · subst key; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY,
            show ofString "chain_id" ≠ ofString "mode" from by decide, hc]
        · by_cases ht : key = ofString "tx"
          · subst key; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY,
              show ofString "chain_id" ≠ ofString "tx" from by decide,
              show ofString "mode" ≠ ofString "tx" from by decide, hc, hm]
          · simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY,
              hc, hm, ht, Ne.symm hc, Ne.symm hm, Ne.symm ht]
  simp only [hlk] at hnt hres ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt hres ⊢
    set cmap : HolFiniteMapExact MlS (ValueHOL 64) :=
      ((HolFiniteMapExact.empty.update (ofString "tx", ValueHOL.val (.word tx0))).update
        (ofString "mode", ValueHOL.val (.word 0#64))).update (ofString "chain_id", ValueHOL.val (.word 0#64))
    let ent := callEntryStateHOLFinite s cmap
    have hent_tx : ent.locals.lookup (ofString "tx") = some (.val (.word tx0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "chain_id" ≠ ofString "tx" by decide,
        show ofString "mode" ≠ ofString "tx" by decide]
    have hent_mode : ent.locals.lookup (ofString "mode") = some (.val (.word 0#64)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "chain_id" ≠ ofString "mode" by decide]
    have heff_s_ent : HeapByteEff s ent [] ["heap_ptr"] :=
      (HeapByteEff.refl hAR [] ["heap_ptr"]).locals_clock ent.locals ent.clock
    have hAR_ent : ArenaReady ent := heff_s_ent.arena
    rcases hbody_ev : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_tx_encode_generic) with ⟨rbody, sbody⟩
    change evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_tx_encode_generic) = (rbody, sbody) at hbody_ev
    simp only [hbody_ev] at hnt hres ⊢
    have hnt_body : rbody ≠ some .timeOut := by
      rintro rfl; exact hnt rfl
    have hres_body : Resumes rbody := by
      cases rbody with
      | none => exact False.elim (not_resumes_error hres)
      | some r =>
        cases r with
        | timeOut => exact absurd rfl hnt_body
        | returned rv =>
          dsimp only at hres
          split at hres
          · exact Or.inl ⟨_, rfl⟩
          · exact False.elim (not_resumes_error hres)
        | exception eid ev => exact hres
        | «break» | «continue» | error => exact False.elim (not_resumes_error hres)
        | finalFfi _ => rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
    have htx_enc_ent : TxValidEncodeAt ent tx0.toNat := by
      have hloc_tx : locN s "tx" = tx0.toNat := by simp [locN, htx0]
      exact hloc_tx ▸ hW.2
    have hgen := eval_tx_encode_generic_mode0_bounded_resumes ent tx0 hAR_ent htx_enc_ent hent_tx hent_mode
      (by rw [hbody_ev]; exact hnt_body) (by rw [hbody_ev]; exact hres_body)
    rw [hbody_ev] at hgen
    have hbody_eff : HeapByteEff s sbody [] ["heap_ptr"] := heff_s_ent.trans hgen.1
    cases rbody with
    | none => exact False.elim (not_resumes_error hres)
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt_body
      | returned rv =>
        dsimp only at hres ⊢
        split
        · exact ⟨hbody_eff.locals_clock _ _, fun v hv => by
            injection hv with hv; injection hv with hv; subst rv
            exact hgen.2 v rfl⟩
        · rename_i hbad
          rw [if_neg hbad] at hres
          exact False.elim (not_resumes_error hres)
      | «break» | «continue» | error =>
        exact False.elim (not_resumes_error hres)
      | exception eid ev =>
        exact ⟨hbody_eff.locals_clock _ _, fun _ hv => by cases hv⟩
      | finalFfi _ =>
        rcases hres_body with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h



end Phases1To4EncodeTxBounded
end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
