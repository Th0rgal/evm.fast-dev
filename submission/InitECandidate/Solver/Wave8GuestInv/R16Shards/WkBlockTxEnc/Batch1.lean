import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.RlpHelpers

/-!
# R16e Batch 1: `wk_encode_withdrawal_rlp`, `wk_compute_contract_address`, `wk_encode_account`, `wk_calculate_blob_gas_price`

Zero-sorry proofs of the first four C08 `WorldKeeps` leaves, matching the frozen
statements in `ContractParts/C08.lean` verbatim.
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

/-! ## Section 1: Generic `call (some (some (VarKind.local, x), none))` combinators for `rlp_encode_word` & `rlp_encode_bytes`, plus `st_be64` -/

theorem eval_call_local_rlp_encode_word {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (dstExp wExp : ExpHOL 64)
    (dst0 w0 : BitVec 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl_old : ∃ w_old : BitVec 64, s.locals.lookup (ofString lname) = some (.val (.word w_old)))
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hw : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) wExp =
      some (.val (.word w0)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + 9 ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "rlp_encode_word") [dstExp, wExp])).1 ≠
      some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "rlp_encode_word") [dstExp, wExp])
    (out.1 = none →
      ∃ len : BitVec 64,
        1 ≤ len.toNat ∧ len.toNat ≤ 9 ∧ dst0.toNat < heapEnd ∧
        out.2.globals = s.globals ∧
        out.2.locals = s.locals.update (ofString lname, .val (.word len)) ∧
        HeapByteEff s out.2 Rl gw) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  intro out; dsimp only [out]
  obtain ⟨w_old, hw_old⟩ := hl_old
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, wExp] = some [.val (.word dst0), .val (.word w0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hw]
  have hlk := pan_two_word_lookup s.code.lookup (ofString "rlp_encode_word")
    (ofString "dst") (ofString "w")
    (sourceFnBody Guest.Software.guestFn_rlp_encode_word) dst0 w0 (by decide)
    (by rw [hcode]; exact lookup_rlp_encode_word)
  simp only [ha, hlk] at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set cmap := (HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
      (ofString "w", ValueHOL.val (.word w0))
    set ent := callEntryStateHOLFinite s cmap
    have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "w" ≠ ofString "dst" by decide]
    have hent_w : ent.locals.lookup (ofString "w") = some (.val (.word w0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hew : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_encode_word) with ⟨rew, sew⟩
    have hnt_ew : rew ≠ some .timeOut := by
      rintro rfl; rw [hew] at hnt; exact hnt rfl
    obtain ⟨hret, hnonret⟩ := eval_rlp_encode_word_body_exact ent dst0 w0 Rl
      hcode hAR.1.memaddrs hent_dst hent_w hin_ivl (by rw [hew]; exact hnt_ew)
    rw [hew] at hret hnonret
    dsimp only at hret hnonret
    simp only [hew] at hnt ⊢
    cases rew with
    | none => exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt_ew
      | exception eid ev =>
        exact ⟨fun h => by simp at h, fun _ => hnonret (.exception eid ev) rfl (fun _ h => by cases h)⟩
      | returned rv =>
        obtain ⟨len, rfl, hlen1, hlen9, hdst_lt, heff_ew⟩ := hret rv rfl
        have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word len) : ValueHOL 64)) .one = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        have hval : isValidValueHOLExact s.toExact VarKind.local (ofString lname) (.val (.word len)) = true := by
          simp [isValidValueHOLExact, lookupKvarHOLExact, hw_old, shapeOfHOLExact, shapeEqHOL]
        dsimp only
        rw [if_pos hsh]
        rw [if_pos hval]
        let mid := setVarHOLFinite (ofString lname) (.val (.word len)) { sew with locals := s.locals }
        have heff0 : M11.ByteRegionEffect s ent Rl :=
          (M11.ByteRegionEffect.refl s Rl).with_locals_clock ent.locals ent.clock
        have heff_mid : M11.ByteRegionEffect s mid Rl :=
          (heff0.trans heff_ew).with_locals_clock mid.locals mid.clock
        exact ⟨fun _ => ⟨len, hlen1, hlen9, hdst_lt, heff_mid.globals, rfl,
          HeapByteEff.of_m11_bre hAR heff_mid⟩,
          fun h => False.elim (h rfl)⟩
      | «break» | «continue» | error =>
        exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
      | finalFfi _ =>
        exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

theorem eval_call_local_rlp_encode_bytes {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (dstExp srcExp nExp : ExpHOL 64)
    (dst0 src0 n0 : BitVec 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl_old : ∃ w_old : BitVec 64, s.locals.lookup (ofString lname) = some (.val (.word w_old)))
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) srcExp =
      some (.val (.word src0)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n0)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧
      dst0.toNat + rlpHeaderLenPure n0.toNat + n0.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "rlp_encode_bytes")
        [dstExp, srcExp, nExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "rlp_encode_bytes")
        [dstExp, srcExp, nExp])
    (out.1 = none →
      ∃ len : BitVec 64,
        len.toNat ≤ rlpHeaderLenPure n0.toNat + n0.toNat ∧ dst0.toNat < heapEnd ∧
        out.2.globals = s.globals ∧
        out.2.locals = s.locals.update (ofString lname, .val (.word len)) ∧
        HeapByteEff s out.2 Rl gw) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  intro out; dsimp only [out]
  obtain ⟨w_old, hw_old⟩ := hl_old
  rw [evaluateHOLFiniteState_call] at hnt ⊢
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
    rcases heb : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes) with ⟨reb, seb⟩
    have hnt_eb : reb ≠ some .timeOut := by
      rintro rfl; rw [heb] at hnt; exact hnt rfl
    obtain ⟨hret, hnonret⟩ := eval_rlp_encode_bytes_body_exact ent dst0 src0 n0 Rl
      hcode hAR.1.memaddrs hent_dst hent_src hent_n hin_ivl (by rw [heb]; exact hnt_eb)
    rw [heb] at hret hnonret
    dsimp only at hret hnonret
    simp only [heb] at hnt ⊢
    cases reb with
    | none => exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt_eb
      | exception eid ev =>
        exact ⟨fun h => by simp at h, fun _ => hnonret (.exception eid ev) rfl (fun _ h => by cases h)⟩
      | returned rv =>
        obtain ⟨len, rfl, hlen_le, hdst_lt, heff_eb⟩ := hret rv rfl
        have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word len) : ValueHOL 64)) .one = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        have hval : isValidValueHOLExact s.toExact VarKind.local (ofString lname) (.val (.word len)) = true := by
          simp [isValidValueHOLExact, lookupKvarHOLExact, hw_old, shapeOfHOLExact, shapeEqHOL]
        dsimp only
        rw [if_pos hsh]
        rw [if_pos hval]
        let mid := setVarHOLFinite (ofString lname) (.val (.word len)) { seb with locals := s.locals }
        have heff0 : M11.ByteRegionEffect s ent Rl :=
          (M11.ByteRegionEffect.refl s Rl).with_locals_clock ent.locals ent.clock
        have heff_mid : M11.ByteRegionEffect s mid Rl :=
          (heff0.trans heff_eb).with_locals_clock mid.locals mid.clock
        exact ⟨fun _ => ⟨len, hlen_le, hdst_lt, heff_mid.globals, rfl,
          HeapByteEff.of_m11_bre hAR heff_mid⟩,
          fun h => False.elim (h rfl)⟩
      | «break» | «continue» | error =>
        exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
      | finalFfi _ =>
        exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

/-! ## Section 2: `wk_encode_withdrawal_rlp` -/

theorem lookup_encode_withdrawal_rlp :
    originalRuntimeCode.lookup (ofString "encode_withdrawal_rlp") =
      some ([(ofString "wd", .one)],
        sourceFnBody Guest.Software.guestFn_encode_withdrawal_rlp, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 838 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_encode_withdrawal_rlp) rfl

private theorem eval_or_loadBytes_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64)
    (h_op : ∃ args, e = .op .or args) :
    ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some v →
      ∃ w : BitVec 64, v = .val (.word w) := by
  obtain ⟨args, rfl⟩ := h_op
  intro v hv
  simp only [evalHOLExact] at hv
  split at hv
  · split at hv
    · simp only [Option.map_eq_some_iff] at hv
      obtain ⟨_, _, rfl⟩ := hv; exact ⟨_, rfl⟩
    · cases hv
  · cases hv

private theorem call_local_not_resumes_of_arg_none {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (fname : MlS) (e1 e2 : ExpHOL 64)
    (cont : ProgHOL 64)
    (he2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 = none) :
    ¬ Resumes (evaluateHOLFiniteState s
      (.seq (.call (some (some (VarKind.local, ofString lname), none)) fname [e1, e2]) cont)).1 := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call]
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1, e2] = none := by
    unfold evalListHOLFinite
    rcases h1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | v1
    · simp [evalListHOLExact, h1]
    · simp [evalListHOLExact, h1, he2]
  rw [ha]; dsimp only
  exact not_resumes_error

private theorem decCall_not_resumes_of_arg2_none {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (fname : MlS) (e1 e2 : ExpHOL 64)
    (cont : ProgHOL 64)
    (he2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 = none) :
    ¬ Resumes (evaluateHOLFiniteState s (.decCall (ofString lname) .one fname [e1, e2] cont)).1 := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1, e2] = none := by
    unfold evalListHOLFinite
    rcases h1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | v1
    · simp [evalListHOLExact, h1]
    · simp [evalListHOLExact, h1, he2]
  rw [ha]; dsimp only
  exact not_resumes_error

theorem lookupCode_one_word_any {fname p1 : MlS} {body : ProgHOL 64} {rs : ShapeHOL}
    {vals : List (ValueHOL 64)} {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one)], body, rs))
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, L, rs)) :
    ∃ w1 : BitVec 64,
      vals = [.val (.word w1)] ∧
      L.lookup p1 = some (.val (.word w1)) := by
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup fname vals body L rs hl
  simp only [lookupCodeHOLExact, hlook] at hx
  rcases vals with _ | ⟨v1, _ | _⟩
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hx
    exact ⟨w1, rfl, by rw [← hx]; simp⟩
  · simp at hx

theorem «wk_encode_withdrawal_rlp» :
    WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
     ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "encode_withdrawal_rlp") := by
  refine ⟨_, _, _, lookup_encode_withdrawal_rlp, fun {F} s hcode hW hparams hnt hres => ?_⟩
  have hAR : ArenaReady s := hW.1
  have hhl264 : heapLimit < 2 ^ 64 := by rw [heapLimit_val]; decide
  obtain ⟨vals, hl_wd⟩ := hparams
  obtain ⟨wd, _, hwd⟩ := lookupCode_one_word_any lookup_encode_withdrawal_rlp hl_wd
  -- Unfold body of `encode_withdrawal_rlp`:
  have hb : ∃ (e0 e8 e36 : ExpHOL 64),
      (∃ a0, e0 = .op .or a0) ∧ (∃ a8, e8 = .op .or a8) ∧ (∃ a36, e36 = .op .or a36) ∧
      sourceFnBody Guest.Software.guestFn_encode_withdrawal_rlp =
      .decCall (ofString "buf") .one (ofString "alloc") [.const 64]
        (.dec (ofString "p") .one (.op .add [ExpHOL.var VarKind.local (ofString "buf"), .const 9])
          (.decCall (ofString "w") .one (ofString "rlp_encode_word")
            [ExpHOL.var VarKind.local (ofString "p"), e0]
            (.seq (.assign VarKind.local (ofString "p")
                (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")]))
              (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
                  [ExpHOL.var VarKind.local (ofString "p"), e8])
                (.seq (.assign VarKind.local (ofString "p")
                    (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")]))
                  (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
                      [ExpHOL.var VarKind.local (ofString "p"),
                       .op .add [ExpHOL.var VarKind.local (ofString "wd"), .const 16],
                       .const 20])
                    (.seq (.assign VarKind.local (ofString "p")
                        (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")]))
                      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
                          [ExpHOL.var VarKind.local (ofString "p"), e36])
                        (.seq (.assign VarKind.local (ofString "p")
                            (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")]))
                          (.decCall (ofString "total") .one (ofString "rlp_finish_list")
                            [ExpHOL.var VarKind.local (ofString "buf"), ExpHOL.var VarKind.local (ofString "p")]
                            (.return (.rstruct [ExpHOL.var VarKind.local (ofString "buf"),
                              ExpHOL.var VarKind.local (ofString "total")])))))))))))) := by
    refine ⟨_, _, _, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, rfl⟩
  obtain ⟨e0, e8, e36, ho0, ho8, ho36, hbody⟩ := hb
  suffices hmain : HeapByteEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_encode_withdrawal_rlp)).2
      ([] ++ ([] : List (String × Nat)).map (bufferRegion s)) ["heap_ptr"] by
    exact hmain.to_worldStep (R := fun _ => []) (B := [])
      (by intro _ h; cases h) (by intro g hg; simp at hg; exact Or.inl hg)
      hW (fun _ _ _ _ _ => trivial)
  rw [hbody] at hnt hres ⊢
  -- Step 1: `var 1 buf = alloc(64)`
  obtain ⟨buf, n64, q, s1, h64_ev, hbuf_hp, hbuf8, hq_nat, hpq, hq_hi, hq8, hs1_hp, hs1_g, hs1_m, hs1_loc,
      heff1, hnt1, hres1, heq1⟩ :=
    eval_decCall_alloc_resumes s "buf" (.const 64) _ [] ["heap_ptr"] hcode hAR (by simp) hnt hres
  have hn64 : n64 = 64 := by simp [evalHOLExact] at h64_ev; exact h64_ev.symm
  subst hn64
  have h64_val : (64 : BitVec 64).toNat = 64 := by decide
  rw [h64_val] at hq_nat
  have hq_eq : q.toNat = buf.toNat + 64 := by omega
  -- Note `buf.toNat = globN s "heap_ptr"` and `buf.toNat + 64 = q.toNat ≤ heapLimit`:
  have hbuf_in_free : ∀ a b, buf.toNat ≤ a → b ≤ buf.toNat + 64 →
      ∃ ivl ∈ ([(buf.toNat, 64)] : List Ivl), ivl.1 ≤ a ∧ b ≤ ivl.1 + ivl.2 :=
    fun a b h1 h2 => ⟨(buf.toNat, 64), List.mem_singleton.2 rfl, h1, h2⟩
  -- Inside `s1`, we track writes within `[(buf.toNat, 64)]`, then lift `[(buf.toNat, 64)]` into `heapFree s`!
  rw [heq1]; dsimp only
  have hs1_buf : s1.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_wd : s1.locals.lookup (ofString "wd") = some (.val (.word wd)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hwd,
      show ofString "buf" ≠ ofString "wd" by decide]
  -- Step 2: `var p = buf + 9`
  rw [evaluateHOLFiniteState_dec_total] at hnt1 hres1 ⊢
  let p0 : BitVec 64 := buf + 9
  have hp0_nat : p0.toNat = buf.toNat + 9 := by
    change (buf + 9).toNat = buf.toNat + 9
    rw [BitVec.toNat_add]; change (buf.toNat + 9) % 2 ^ 64 = _
    exact Nat.mod_eq_of_lt (by omega)
  have hev_p0 : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
      (.op .add [ExpHOL.var VarKind.local (ofString "buf"), .const 9]) = some (.val (.word p0)) := by
    simp [evalHOLExact, evalListHOLExact, hs1_buf, wordOpHOL, wordOp, valueIsWord, valueWord, p0]
  have hsh_p0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word p0) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  dsimp only at hnt1 hres1 ⊢
  rw [hev_p0] at hnt1 hres1 ⊢; dsimp only at hnt1 hres1 ⊢
  rw [if_pos hsh_p0] at hnt1 hres1 ⊢; dsimp only
  set s2 := setVarHOLFinite (ofString "p") (.val (.word p0)) s1
  have hAR2 : ArenaReady s2 := ⟨guestInv_setVar _ _ _ heff1.arena.1, heff1.arena.2⟩
  have hs2_p : s2.locals.lookup (ofString "p") = some (.val (.word p0)) := by
    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs2_buf : s2.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_buf,
      show ofString "p" ≠ ofString "buf" by decide]
  have hs2_wd : s2.locals.lookup (ofString "wd") = some (.val (.word wd)) := by
    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_wd,
      show ofString "p" ≠ ofString "wd" by decide]
  -- Step 3: `var 1 w = rlp_encode_word(p, e0)`
  rcases hev0 : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a)) e0 with _ | v0
  · exact False.elim (decCall_not_resumes_of_arg2_none s2 "w" _ _ _ _ hev0 hres1)
  obtain ⟨w0, rfl⟩ := eval_or_loadBytes_word s2 e0 ho0 v0 hev0
  obtain ⟨len1, s3, hlen1_lo, hlen1_hi, _, hs3_g, hs3_loc, heff23, hnt3, hres3, heq3⟩ :=
    eval_decCall_rlp_encode_word s2 "w" (ExpHOL.var VarKind.local (ofString "p")) e0 p0 w0 _
      [(buf.toNat, 64)] [] hAR2.1.code hAR2 hs2_p hev0
      (hbuf_in_free p0.toNat (p0.toNat + 9) (by omega) (by omega)) hnt1 hres1
  rw [heq3]; dsimp only
  have hs3_w : s3.locals.lookup (ofString "w") = some (.val (.word len1)) := by
    rw [hs3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hs3_p : s3.locals.lookup (ofString "p") = some (.val (.word p0)) := by
    rw [hs3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs2_p,
      show ofString "w" ≠ ofString "p" by decide]
  have hs3_buf : s3.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
    rw [hs3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs2_buf,
      show ofString "w" ≠ ofString "buf" by decide]
  have hs3_wd : s3.locals.lookup (ofString "wd") = some (.val (.word wd)) := by
    rw [hs3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs2_wd,
      show ofString "w" ≠ ofString "wd" by decide]
  -- Step 4: `p = p + w`
  let p1 : BitVec 64 := p0 + len1
  have hp1_nat : p1.toNat = p0.toNat + len1.toNat := by
    change (p0 + len1).toNat = p0.toNat + len1.toNat
    rw [BitVec.toNat_add]; change (p0.toNat + len1.toNat) % 2 ^ 64 = _
    exact Nat.mod_eq_of_lt (by omega)
  have hass1 : evaluateHOLFiniteState s3
      (.assign VarKind.local (ofString "p")
        (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])) =
      (none, setVarHOLFinite (ofString "p") (.val (.word p1)) s3) := by
    rw [evaluateHOLFiniteState_assign]
    have hev : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
        (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")]) =
        some (.val (.word p1)) := by
      simp [evalHOLExact, evalListHOLExact, hs3_p, hs3_w, wordOpHOL, wordOp, valueIsWord, valueWord, p1]
    have hval : s3.isValidValueHOLFinite VarKind.local (ofString "p") (.val (.word p1)) = true := by
      simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hs3_p, shapeOfHOLExact, shapeEqHOL]
    rw [hev]; dsimp only; rw [if_pos hval]; rfl
  rw [evaluateHOLFiniteState_seq_line780, hass1] at hnt3 hres3 ⊢
  dsimp only at hnt3 hres3 ⊢
  set s4 := setVarHOLFinite (ofString "p") (.val (.word p1)) s3
  have hAR4 : ArenaReady s4 := ⟨guestInv_setVar _ _ _ heff23.arena.1, heff23.arena.2⟩
  have hs4_p : s4.locals.lookup (ofString "p") = some (.val (.word p1)) := by
    simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs4_w : s4.locals.lookup (ofString "w") = some (.val (.word len1)) := by
    simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_w,
      show ofString "p" ≠ ofString "w" by decide]
  have hs4_buf : s4.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
    simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_buf,
      show ofString "p" ≠ ofString "buf" by decide]
  have hs4_wd : s4.locals.lookup (ofString "wd") = some (.val (.word wd)) := by
    simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_wd,
      show ofString "p" ≠ ofString "wd" by decide]
  -- Step 5: `w = rlp_encode_word(p, e8)`
  rcases hev8 : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a)) e8 with _ | v8
  · exact False.elim (call_local_not_resumes_of_arg_none s4 "w" _ _ _ _ hev8 hres3)
  obtain ⟨w8, rfl⟩ := eval_or_loadBytes_word s4 e8 ho8 v8 hev8
  rw [evaluateHOLFiniteState_seq_line780] at hnt3 hres3 ⊢
  rcases hc5 : evaluateHOLFiniteState s4
    (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
      [ExpHOL.var VarKind.local (ofString "p"), e8]) with ⟨r5, s5⟩
  have hnt_c5 : r5 ≠ some .timeOut := by rintro rfl; rw [hc5] at hnt3; exact hnt3 rfl
  have h5 := eval_call_local_rlp_encode_word s4 "w" (ExpHOL.var VarKind.local (ofString "p")) e8 p1 w8
    [(buf.toNat, 64)] [] hAR4.1.code hAR4 ⟨len1, hs4_w⟩ hs4_p hev8
    (hbuf_in_free p1.toNat (p1.toNat + 9) (by omega) (by omega)) (by rw [hc5]; exact hnt_c5)
  dsimp only at h5; rw [hc5] at h5 hnt3 hres3
  cases r5 with
  | some r_5 =>
    exfalso
    have hnr := h5.2 (by simp)
    dsimp only at hres3
    exact hnr hres3
  | none =>
    dsimp only at hnt3 hres3 ⊢
    obtain ⟨len2, hlen2_lo, hlen2_hi, _, hs5_g, hs5_loc, heff45⟩ := h5.1 rfl
    have hs5_w : s5.locals.lookup (ofString "w") = some (.val (.word len2)) := by
      rw [hs5_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hs5_p : s5.locals.lookup (ofString "p") = some (.val (.word p1)) := by
      rw [hs5_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs4_p,
        show ofString "w" ≠ ofString "p" by decide]
    have hs5_buf : s5.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
      rw [hs5_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs4_buf,
        show ofString "w" ≠ ofString "buf" by decide]
    have hs5_wd : s5.locals.lookup (ofString "wd") = some (.val (.word wd)) := by
      rw [hs5_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs4_wd,
        show ofString "w" ≠ ofString "wd" by decide]
    -- Step 6: `p = p + w`
    let p2 : BitVec 64 := p1 + len2
    have hp2_nat : p2.toNat = p1.toNat + len2.toNat := by
      change (p1 + len2).toNat = p1.toNat + len2.toNat
      rw [BitVec.toNat_add]; change (p1.toNat + len2.toNat) % 2 ^ 64 = _
      exact Nat.mod_eq_of_lt (by omega)
    have hass2 : evaluateHOLFiniteState s5
        (.assign VarKind.local (ofString "p")
          (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])) =
        (none, setVarHOLFinite (ofString "p") (.val (.word p2)) s5) := by
      rw [evaluateHOLFiniteState_assign]
      have hev : @evalHOLExact 64 F _ s5.toExact (fun a => Classical.propDecidable (s5.memaddrs a))
          (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")]) =
          some (.val (.word p2)) := by
        simp [evalHOLExact, evalListHOLExact, hs5_p, hs5_w, wordOpHOL, wordOp, valueIsWord, valueWord, p2]
      have hval : s5.isValidValueHOLFinite VarKind.local (ofString "p") (.val (.word p2)) = true := by
        simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hs5_p, shapeOfHOLExact, shapeEqHOL]
      rw [hev]; dsimp only; rw [if_pos hval]; rfl
    rw [evaluateHOLFiniteState_seq_line780, hass2] at hnt3 hres3 ⊢
    dsimp only at hnt3 hres3 ⊢
    set s6 := setVarHOLFinite (ofString "p") (.val (.word p2)) s5
    have hAR6 : ArenaReady s6 := ⟨guestInv_setVar _ _ _ heff45.arena.1, heff45.arena.2⟩
    have hs6_p : s6.locals.lookup (ofString "p") = some (.val (.word p2)) := by
      simp [s6, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs6_w : s6.locals.lookup (ofString "w") = some (.val (.word len2)) := by
      simp [s6, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs5_w,
        show ofString "p" ≠ ofString "w" by decide]
    have hs6_buf : s6.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
      simp [s6, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs5_buf,
        show ofString "p" ≠ ofString "buf" by decide]
    have hs6_wd : s6.locals.lookup (ofString "wd") = some (.val (.word wd)) := by
      simp [s6, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs5_wd,
        show ofString "p" ≠ ofString "wd" by decide]
    -- Step 7: `w = rlp_encode_bytes(p, wd + 16, 20)`
    rw [evaluateHOLFiniteState_seq_line780] at hnt3 hres3 ⊢
    rcases hc7 : evaluateHOLFiniteState s6
      (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
        [ExpHOL.var VarKind.local (ofString "p"),
         .op .add [ExpHOL.var VarKind.local (ofString "wd"), .const 16],
         .const 20]) with ⟨r7, s7⟩
    have hnt_c7 : r7 ≠ some .timeOut := by rintro rfl; rw [hc7] at hnt3; exact hnt3 rfl
    have hhl20 : rlpHeaderLenPure (20 : BitVec 64).toNat + (20 : BitVec 64).toNat = 21 := by
      have : (20 : BitVec 64).toNat = 20 := by decide
      rw [this, rlpHeaderLenPure_of_le55 (by decide)]
    have h7 := eval_call_local_rlp_encode_bytes s6 "w"
      (ExpHOL.var VarKind.local (ofString "p"))
      (.op .add [ExpHOL.var VarKind.local (ofString "wd"), .const 16]) (.const 20)
      p2 (wd + 16) 20 [(buf.toNat, 64)] [] hAR6.1.code hAR6 ⟨len2, hs6_w⟩ hs6_p
      (by simp [evalHOLExact, evalListHOLExact, hs6_wd, wordOpHOL, wordOp, valueIsWord, valueWord])
      rfl
      (by rw [Nat.add_assoc, hhl20]; exact hbuf_in_free p2.toNat (p2.toNat + 21) (by omega) (by omega))
      (by rw [hc7]; exact hnt_c7)
    dsimp only at h7; rw [hc7] at h7 hnt3 hres3
    cases r7 with
    | some r_7 =>
      exfalso; exact h7.2 (by simp) hres3
    | none =>
      dsimp only at hnt3 hres3 ⊢
      obtain ⟨len3, hlen3_hi', _, hs7_g, hs7_loc, heff67⟩ := h7.1 rfl
      have hlen3_hi : len3.toNat ≤ 21 := by rw [hhl20] at hlen3_hi'; exact hlen3_hi'
      have hs7_w : s7.locals.lookup (ofString "w") = some (.val (.word len3)) := by
        rw [hs7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
      have hs7_p : s7.locals.lookup (ofString "p") = some (.val (.word p2)) := by
        rw [hs7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs6_p,
          show ofString "w" ≠ ofString "p" by decide]
      have hs7_buf : s7.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
        rw [hs7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs6_buf,
          show ofString "w" ≠ ofString "buf" by decide]
      have hs7_wd : s7.locals.lookup (ofString "wd") = some (.val (.word wd)) := by
        rw [hs7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs6_wd,
          show ofString "w" ≠ ofString "wd" by decide]
      -- Step 8: `p = p + w`
      let p3 : BitVec 64 := p2 + len3
      have hp3_nat : p3.toNat = p2.toNat + len3.toNat := by
        change (p2 + len3).toNat = p2.toNat + len3.toNat
        rw [BitVec.toNat_add]; change (p2.toNat + len3.toNat) % 2 ^ 64 = _
        exact Nat.mod_eq_of_lt (by omega)
      have hass3 : evaluateHOLFiniteState s7
          (.assign VarKind.local (ofString "p")
            (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])) =
          (none, setVarHOLFinite (ofString "p") (.val (.word p3)) s7) := by
        rw [evaluateHOLFiniteState_assign]
        have hev : @evalHOLExact 64 F _ s7.toExact (fun a => Classical.propDecidable (s7.memaddrs a))
            (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")]) =
            some (.val (.word p3)) := by
          simp [evalHOLExact, evalListHOLExact, hs7_p, hs7_w, wordOpHOL, wordOp, valueIsWord, valueWord, p3]
        have hval : s7.isValidValueHOLFinite VarKind.local (ofString "p") (.val (.word p3)) = true := by
          simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hs7_p, shapeOfHOLExact, shapeEqHOL]
        rw [hev]; dsimp only; rw [if_pos hval]; rfl
      rw [evaluateHOLFiniteState_seq_line780, hass3] at hnt3 hres3 ⊢
      dsimp only at hnt3 hres3 ⊢
      set s8 := setVarHOLFinite (ofString "p") (.val (.word p3)) s7
      have hAR8 : ArenaReady s8 := ⟨guestInv_setVar _ _ _ heff67.arena.1, heff67.arena.2⟩
      have hs8_p : s8.locals.lookup (ofString "p") = some (.val (.word p3)) := by
        simp [s8, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hs8_w : s8.locals.lookup (ofString "w") = some (.val (.word len3)) := by
        simp [s8, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs7_w,
          show ofString "p" ≠ ofString "w" by decide]
      have hs8_buf : s8.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
        simp [s8, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs7_buf,
          show ofString "p" ≠ ofString "buf" by decide]
      -- Step 9: `w = rlp_encode_word(p, e36)`
      rcases hev36 : @evalHOLExact 64 F _ s8.toExact (fun a => Classical.propDecidable (s8.memaddrs a)) e36 with _ | v36
      · exact False.elim (call_local_not_resumes_of_arg_none s8 "w" _ _ _ _ hev36 hres3)
      obtain ⟨w36, rfl⟩ := eval_or_loadBytes_word s8 e36 ho36 v36 hev36
      rw [evaluateHOLFiniteState_seq_line780] at hnt3 hres3 ⊢
      rcases hc9 : evaluateHOLFiniteState s8
        (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
          [ExpHOL.var VarKind.local (ofString "p"), e36]) with ⟨r9, s9⟩
      have hnt_c9 : r9 ≠ some .timeOut := by rintro rfl; rw [hc9] at hnt3; exact hnt3 rfl
      have h9 := eval_call_local_rlp_encode_word s8 "w" (ExpHOL.var VarKind.local (ofString "p")) e36 p3 w36
        [(buf.toNat, 64)] [] hAR8.1.code hAR8 ⟨len3, hs8_w⟩ hs8_p hev36
        (hbuf_in_free p3.toNat (p3.toNat + 9) (by omega) (by omega)) (by rw [hc9]; exact hnt_c9)
      dsimp only at h9; rw [hc9] at h9 hnt3 hres3
      cases r9 with
      | some r_9 =>
        exfalso; exact h9.2 (by simp) hres3
      | none =>
        dsimp only at hnt3 hres3 ⊢
        obtain ⟨len4, hlen4_lo, hlen4_hi, _, hs9_g, hs9_loc, heff89⟩ := h9.1 rfl
        have hs9_w : s9.locals.lookup (ofString "w") = some (.val (.word len4)) := by
          rw [hs9_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        have hs9_p : s9.locals.lookup (ofString "p") = some (.val (.word p3)) := by
          rw [hs9_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs8_p,
            show ofString "w" ≠ ofString "p" by decide]
        have hs9_buf : s9.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
          rw [hs9_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs8_buf,
            show ofString "w" ≠ ofString "buf" by decide]
        -- Step 10: `p = p + w`
        let p4 : BitVec 64 := p3 + len4
        have hp4_nat : p4.toNat = p3.toNat + len4.toNat := by
          change (p3 + len4).toNat = p3.toNat + len4.toNat
          rw [BitVec.toNat_add]; change (p3.toNat + len4.toNat) % 2 ^ 64 = _
          exact Nat.mod_eq_of_lt (by omega)
        have hass4 : evaluateHOLFiniteState s9
            (.assign VarKind.local (ofString "p")
              (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])) =
            (none, setVarHOLFinite (ofString "p") (.val (.word p4)) s9) := by
          rw [evaluateHOLFiniteState_assign]
          have hev : @evalHOLExact 64 F _ s9.toExact (fun a => Classical.propDecidable (s9.memaddrs a))
              (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")]) =
              some (.val (.word p4)) := by
            simp [evalHOLExact, evalListHOLExact, hs9_p, hs9_w, wordOpHOL, wordOp, valueIsWord, valueWord, p4]
          have hval : s9.isValidValueHOLFinite VarKind.local (ofString "p") (.val (.word p4)) = true := by
            simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hs9_p, shapeOfHOLExact, shapeEqHOL]
          rw [hev]; dsimp only; rw [if_pos hval]; rfl
        rw [evaluateHOLFiniteState_seq_line780, hass4] at hnt3 hres3 ⊢
        dsimp only at hnt3 hres3 ⊢
        set s10 := setVarHOLFinite (ofString "p") (.val (.word p4)) s9
        have hAR10 : ArenaReady s10 := ⟨guestInv_setVar _ _ _ heff89.arena.1, heff89.arena.2⟩
        have hs10_p : s10.locals.lookup (ofString "p") = some (.val (.word p4)) := by
          simp [s10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hs10_buf : s10.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
          simp [s10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs9_buf,
            show ofString "p" ≠ ofString "buf" by decide]
        -- Step 11: `var 1 total = rlp_finish_list(buf, p); return <buf, total>;`
        have hp4_fit : p4.toNat ≤ heapEnd := by
          have : heapLimit ≤ heapEnd := by rw [heapLimit_val, heapEnd_val]; decide
          omega
        obtain ⟨tw, s11, _, _, _, hs11_loc, heff1011, _, _, heq11⟩ :=
          eval_decCall_rlp_finish_list s10 "total"
            (ExpHOL.var VarKind.local (ofString "buf"))
            (ExpHOL.var VarKind.local (ofString "p"))
            buf p4 _ [(buf.toNat, 64)] [] hAR10.1.code hAR10 hs10_buf hs10_p
            (by omega) hp4_fit (hbuf_in_free buf.toNat p4.toNat le_rfl (by omega)) hnt3 hres3
        rw [heq11]
        -- Step 12: `.return (.rStruct [buf, total])` only touches locals & clock:
        have heff_ret : HeapByteEff s11
            (evaluateHOLFiniteState s11
              (.return (.rstruct [ExpHOL.var VarKind.local (ofString "buf"),
                                  ExpHOL.var VarKind.local (ofString "total")]))).2
            [(buf.toNat, 64)] [] :=
          HeapByteEff.of_byteEff heff1011.arena
            (R13Shards.Keccak256.byteEff_return s11 _ [(buf.toNat, 64)])
        -- Chain all `HeapByteEff` steps from `s1` to `s11`'s `.return` inside `[(buf.toNat, 64)]`:
        have heff_s1_ret : HeapByteEff s1
            (evaluateHOLFiniteState s11
              (.return (.rstruct [ExpHOL.var VarKind.local (ofString "buf"),
                                  ExpHOL.var VarKind.local (ofString "total")]))).2
            [(buf.toNat, 64)] [] := by
          have h12 : HeapByteEff s1 s2 [(buf.toNat, 64)] [] :=
            (HeapByteEff.refl heff1.arena [(buf.toNat, 64)] []).locals_clock s2.locals s2.clock
          have h34 : HeapByteEff s3 s4 [(buf.toNat, 64)] [] :=
            (HeapByteEff.refl heff23.arena [(buf.toNat, 64)] []).locals_clock s4.locals s4.clock
          have h56 : HeapByteEff s5 s6 [(buf.toNat, 64)] [] :=
            (HeapByteEff.refl heff45.arena [(buf.toNat, 64)] []).locals_clock s6.locals s6.clock
          have h78 : HeapByteEff s7 s8 [(buf.toNat, 64)] [] :=
            (HeapByteEff.refl heff67.arena [(buf.toNat, 64)] []).locals_clock s8.locals s8.clock
          have h910 : HeapByteEff s9 s10 [(buf.toNat, 64)] [] :=
            (HeapByteEff.refl heff89.arena [(buf.toNat, 64)] []).locals_clock s10.locals s10.clock
          exact (((((((((h12.trans heff23).trans h34).trans heff45).trans h56).trans heff67).trans h78).trans heff89).trans h910).trans heff1011).trans heff_ret
        -- Lift `[(buf.toNat, 64)]` into `heapFree s` (`buf.toNat = globN s "heap_ptr"`, `buf.toNat + 64 ≤ heapLimit`):
        have hcomb : HeapByteEff s
            (evaluateHOLFiniteState s11
              (.return (.rstruct [ExpHOL.var VarKind.local (ofString "buf"),
                                  ExpHOL.var VarKind.local (ofString "total")]))).2
            [(buf.toNat, 64)] ["heap_ptr"] :=
          (heff1.mono (fun _ h _ => by cases h) (fun _ hg => hg)).trans
            (heff_s1_ret.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩) (fun _ h => by cases h))
        exact (hcomb.mono
          (fun i hi _ => by
            simp at hi; subst hi
            exact Or.inr (Or.inr ⟨by rw [← hbuf_hp], by omega⟩))
          (fun _ hg => hg)).locals_clock _ _

/-! ## Section 3: `wk_compute_contract_address` -/

theorem lookup_compute_contract_address :
    originalRuntimeCode.lookup (ofString "compute_contract_address") =
      some ([(ofString "addr", .one), (ofString "nonce", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_compute_contract_address, .one) :=
  lookup_of_guestAst_getElem 596 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_compute_contract_address) rfl

/-- Helper to lift a `HeapByteEff` across `.dec x .one e body` when `e` evaluates to a word `w`. -/
private theorem heapByteEff_of_dec_word {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {x : MlS} {e : ExpHOL 64} {w : BitVec 64}
    {body : ProgHOL 64} {Rl : List Ivl} {gw : List String}
    (hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e =
      some (.val (.word w)))
    (hb : HeapByteEff s0 (evaluateHOLFiniteState (setVarHOLFinite x (.val (.word w)) s) body).2 Rl gw) :
    HeapByteEff s0 (evaluateHOLFiniteState s (.dec x .one e body)).2 Rl gw := by
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only; rw [hev]; dsimp only
  have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word w) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  rw [if_pos hsh]
  exact hb.locals_clock _ (evaluateHOLFiniteState (setVarHOLFinite x (.val (.word w)) s) body).2.clock

/-- Helper to lift a `HeapByteEff` across `.seq a b` when `a` evaluates to `(none, m)`. -/
private theorem heapByteEff_of_seq_none {F : Type}
    {s0 s m : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64} {Rl : List Ivl} {gw : List String}
    (ha : evaluateHOLFiniteState s a = (none, m))
    (hb : HeapByteEff s0 (evaluateHOLFiniteState m b).2 Rl gw) :
    HeapByteEff s0 (evaluateHOLFiniteState s (.seq a b)).2 Rl gw := by
  rw [evaluateHOLFiniteState_seq_line780, ha]
  exact hb

/-- Helper to lift a `HeapByteEff` across `.seq a b` when `a` evaluates to `(some r, m)`. -/
private theorem heapByteEff_of_seq_some {F : Type}
    {s0 s m : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64} {r : PanSemResultExact 64}
    {Rl : List Ivl} {gw : List String}
    (ha : evaluateHOLFiniteState s a = (some r, m))
    (hm : HeapByteEff s0 m Rl gw) :
    HeapByteEff s0 (evaluateHOLFiniteState s (.seq a b)).2 Rl gw := by
  rw [evaluateHOLFiniteState_seq_line780, ha]
  exact hm

/-- Helper to lift a `HeapByteEff` across `heq : evaluateHOLFiniteState s p = (r', { q.2 with locals := L })`. -/
private theorem heapByteEff_of_eq_resVar {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {p : ProgHOL 64}
    {r' : Option (PanSemResultExact 64)} {q : PanSemStateFiniteExact 64 F}
    {L : HolFiniteMapExact MlS (ValueHOL 64)} {Rl : List Ivl} {gw : List String}
    (heq : evaluateHOLFiniteState s p = (r', { q with locals := L }))
    (hq : HeapByteEff s0 q Rl gw) :
    HeapByteEff s0 (evaluateHOLFiniteState s p).2 Rl gw := by
  rw [heq]
  exact hq.locals_clock L q.clock

theorem «wk_compute_contract_address» :
    WorldKeeps WorldOK (fun s => [(locN s "out", 20), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "compute_contract_address") := by
  refine ⟨_, _, _, lookup_compute_contract_address, fun {F} s hcode hW hparams hnt hres => ?_⟩
  have hAR : ArenaReady s := hW.1
  have hhl264 : heapLimit < 2 ^ 64 := by rw [heapLimit_val]; decide
  have hhl_he : heapLimit ≤ heapEnd := by rw [heapLimit_val, heapEnd_val]; decide
  obtain ⟨vals, hl_args⟩ := hparams
  obtain ⟨addr0, nonce0, out0, _, haddr, hnonce, hout⟩ :=
    R13Shards.Keccak256.lookupCode_three_words (by decide) (by decide) (by decide)
      lookup_compute_contract_address hl_args
  have hout_locN : locN s "out" = out0.toNat := by simp [locN, hout]
  let Rs : List Ivl :=
    [(locN s "out", 20),
     (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
     (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)]
  suffices hmain : HeapByteEff s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_compute_contract_address)).2
      (Rs ++ ([] : List (String × Nat)).map (bufferRegion s)) ["heap_ptr"] by
    exact hmain.to_worldStep (R := fun t =>
        [(locN t "out", 20),
         (globN t "keccak_pad", if globN t "keccak_pad" = 0 then 0 else 136),
         (globN t "keccak_st", if globN t "keccak_st" = 0 then 0 else 200)])
      (B := [])
      (by intro _ h; cases h)
      (by intro g hg; simp at hg; exact Or.inl hg)
      hW (fun _ _ _ _ _ => trivial)
  have hb : sourceFnBody Guest.Software.guestFn_compute_contract_address =
      .decCall (ofString "mark") .one (ofString "heap_mark") []
        (.decCall (ofString "buf") .one (ofString "alloc") [.const 64]
          (.dec (ofString "p") .one (.op .add [ExpHOL.var VarKind.local (ofString "buf"), .const 9])
            (.decCall (ofString "w") .one (ofString "rlp_encode_bytes")
              [ExpHOL.var VarKind.local (ofString "p"),
               ExpHOL.var VarKind.local (ofString "addr"), .const 20]
              (.seq (.assign VarKind.local (ofString "p")
                  (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")]))
                (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
                    [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "nonce")])
                  (.seq (.assign VarKind.local (ofString "p")
                      (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")]))
                    (.dec (ofString "payload") .one
                      (.op .sub [ExpHOL.var VarKind.local (ofString "p"),
                        .op .add [ExpHOL.var VarKind.local (ofString "buf"), .const 9]])
                      (.decCall (ofString "hl") .one (ofString "rlp_list_header_len")
                        [ExpHOL.var VarKind.local (ofString "payload")]
                        (.seq (.call (some (none, none)) (ofString "rlp_encode_list_header")
                            [.op .sub [.op .add [ExpHOL.var VarKind.local (ofString "buf"), .const 9],
                              ExpHOL.var VarKind.local (ofString "hl")],
                             ExpHOL.var VarKind.local (ofString "payload")])
                          (.decCall (ofString "h") .one (ofString "alloc") [.const 32]
                            (.seq (.call (some (none, none)) (ofString "keccak256")
                                [.op .sub [.op .add [ExpHOL.var VarKind.local (ofString "buf"), .const 9],
                                  ExpHOL.var VarKind.local (ofString "hl")],
                                 .op .add [ExpHOL.var VarKind.local (ofString "payload"),
                                  ExpHOL.var VarKind.local (ofString "hl")],
                                 ExpHOL.var VarKind.local (ofString "h")])
                              (.seq (.call (some (none, none)) (ofString "memcpy")
                                  [ExpHOL.var VarKind.local (ofString "out"),
                                   .op .add [ExpHOL.var VarKind.local (ofString "h"), .const 12],
                                   .const 20])
                                (.seq (.call (some (none, none)) (ofString "heap_release")
                                    [ExpHOL.var VarKind.local (ofString "mark")])
                                  (.return (.const 0))))))))))))))) := rfl
  rw [hb] at hnt hres ⊢
  -- Step 1: `var 1 mark = heap_mark()`
  obtain ⟨mark, s1, hhp_s, hmark_nat, hs1_g, hs1_m, hs1_loc, heff01, hnt1, heq1⟩ :=
    eval_decCall_heap_mark s "mark" _ Rs ["heap_ptr"] hcode hAR hnt
  rw [heq1] at hres; dsimp only at hres
  refine heapByteEff_of_eq_resVar heq1 ?_
  have hs1_mark : s1.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_addr : s1.locals.lookup (ofString "addr") = some (.val (.word addr0)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, haddr,
      show ofString "mark" ≠ ofString "addr" by decide]
  have hs1_nonce : s1.locals.lookup (ofString "nonce") = some (.val (.word nonce0)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hnonce,
      show ofString "mark" ≠ ofString "nonce" by decide]
  have hs1_out : s1.locals.lookup (ofString "out") = some (.val (.word out0)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hout,
      show ofString "mark" ≠ ofString "out" by decide]
  -- Step 2: `var 1 buf = alloc(64)`
  obtain ⟨buf, n64, q1, s2, h64_ev, hbuf_hp, hbuf8, hq1_nat, _, hq1_hi, hq1_8, hs2_hp, hs2_g, hs2_m, hs2_loc,
      heff12, hnt2, hres2, heq2⟩ :=
    eval_decCall_alloc_resumes s1 "buf" (.const 64) _ Rs ["heap_ptr"] heff01.arena.1.code heff01.arena
      (by simp) hnt1 hres
  have hn64 : n64 = 64 := by simp [evalHOLExact] at h64_ev; exact h64_ev.symm
  subst hn64
  have h64_val : (64 : BitVec 64).toNat = 64 := by decide
  rw [h64_val] at hq1_nat
  have hbuf_eq_mark : buf.toNat = mark.toNat := by
    rw [hbuf_hp, hmark_nat]; simp [globN, hs1_g]
  have hq1_eq : q1.toNat = buf.toNat + 64 := by omega
  refine heapByteEff_of_eq_resVar heq2 ?_
  let Rbuf : List Ivl := (buf.toNat, 64) :: Rs
  have hs2_buf : s2.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
    rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hs2_mark : s2.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
    rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_mark,
      show ofString "buf" ≠ ofString "mark" by decide]
  have hs2_addr : s2.locals.lookup (ofString "addr") = some (.val (.word addr0)) := by
    rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_addr,
      show ofString "buf" ≠ ofString "addr" by decide]
  have hs2_nonce : s2.locals.lookup (ofString "nonce") = some (.val (.word nonce0)) := by
    rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_nonce,
      show ofString "buf" ≠ ofString "nonce" by decide]
  have hs2_out : s2.locals.lookup (ofString "out") = some (.val (.word out0)) := by
    rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_out,
      show ofString "buf" ≠ ofString "out" by decide]
  -- Step 3: `var p = buf + 9`
  rw [evaluateHOLFiniteState_dec_total] at hnt2 hres2
  let p0 : BitVec 64 := buf + 9
  have hp0_nat : p0.toNat = buf.toNat + 9 := by
    change (buf + 9).toNat = buf.toNat + 9
    rw [BitVec.toNat_add]; change (buf.toNat + 9) % 2 ^ 64 = _
    exact Nat.mod_eq_of_lt (by omega)
  have hev_p0 : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
      (.op .add [ExpHOL.var VarKind.local (ofString "buf"), .const 9]) = some (.val (.word p0)) := by
    simp [evalHOLExact, evalListHOLExact, hs2_buf, wordOpHOL, wordOp, valueIsWord, valueWord, p0]
  have hsh_p0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word p0) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  dsimp only at hnt2 hres2
  rw [hev_p0] at hnt2 hres2; dsimp only at hnt2 hres2
  rw [if_pos hsh_p0] at hnt2 hres2
  refine heapByteEff_of_dec_word hev_p0 ?_
  set s3 := setVarHOLFinite (ofString "p") (.val (.word p0)) s2
  have hAR3 : ArenaReady s3 := ⟨guestInv_setVar _ _ _ heff12.arena.1, heff12.arena.2⟩
  have hs3_p : s3.locals.lookup (ofString "p") = some (.val (.word p0)) := by
    simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs3_buf : s3.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
    simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_buf,
      show ofString "p" ≠ ofString "buf" by decide]
  have hs3_mark : s3.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
    simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_mark,
      show ofString "p" ≠ ofString "mark" by decide]
  have hs3_addr : s3.locals.lookup (ofString "addr") = some (.val (.word addr0)) := by
    simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_addr,
      show ofString "p" ≠ ofString "addr" by decide]
  have hs3_nonce : s3.locals.lookup (ofString "nonce") = some (.val (.word nonce0)) := by
    simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_nonce,
      show ofString "p" ≠ ofString "nonce" by decide]
  have hs3_out : s3.locals.lookup (ofString "out") = some (.val (.word out0)) := by
    simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_out,
      show ofString "p" ≠ ofString "out" by decide]
  -- Step 4: `var 1 w = rlp_encode_bytes(p, addr, 20)`
  have hhl20 : rlpHeaderLenPure (20 : BitVec 64).toNat + (20 : BitVec 64).toNat = 21 := by
    have : (20 : BitVec 64).toNat = 20 := by decide
    rw [this, rlpHeaderLenPure_of_le55 (by decide)]
  obtain ⟨len1, s4, hlen1_hi', _, hs4_g, hs4_loc, heff34, hnt4, hres4, heq4⟩ :=
    eval_decCall_rlp_encode_bytes s3 "w"
      (ExpHOL.var VarKind.local (ofString "p"))
      (ExpHOL.var VarKind.local (ofString "addr")) (.const 20)
      p0 addr0 20 _ Rbuf [] hAR3.1.code hAR3 hs3_p hs3_addr rfl
      (by rw [Nat.add_assoc, hhl20]; exact ⟨(buf.toNat, 64), List.mem_cons_self, by omega, by omega⟩)
      hnt2 hres2
  have hlen1_hi : len1.toNat ≤ 21 := by rw [hhl20] at hlen1_hi'; exact hlen1_hi'
  refine heapByteEff_of_eq_resVar heq4 ?_
  have hs4_w : s4.locals.lookup (ofString "w") = some (.val (.word len1)) := by
    rw [hs4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hs4_p : s4.locals.lookup (ofString "p") = some (.val (.word p0)) := by
    rw [hs4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs3_p,
      show ofString "w" ≠ ofString "p" by decide]
  have hs4_buf : s4.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
    rw [hs4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs3_buf,
      show ofString "w" ≠ ofString "buf" by decide]
  have hs4_mark : s4.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
    rw [hs4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs3_mark,
      show ofString "w" ≠ ofString "mark" by decide]
  have hs4_nonce : s4.locals.lookup (ofString "nonce") = some (.val (.word nonce0)) := by
    rw [hs4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs3_nonce,
      show ofString "w" ≠ ofString "nonce" by decide]
  have hs4_out : s4.locals.lookup (ofString "out") = some (.val (.word out0)) := by
    rw [hs4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs3_out,
      show ofString "w" ≠ ofString "out" by decide]
  -- Step 5: `p = p + w`
  let p1 : BitVec 64 := p0 + len1
  have hp1_nat : p1.toNat = p0.toNat + len1.toNat := by
    change (p0 + len1).toNat = p0.toNat + len1.toNat
    rw [BitVec.toNat_add]; change (p0.toNat + len1.toNat) % 2 ^ 64 = _
    exact Nat.mod_eq_of_lt (by omega)
  have hass1 : evaluateHOLFiniteState s4
      (.assign VarKind.local (ofString "p")
        (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])) =
      (none, setVarHOLFinite (ofString "p") (.val (.word p1)) s4) := by
    rw [evaluateHOLFiniteState_assign]
    have hev : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
        (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")]) =
        some (.val (.word p1)) := by
      simp [evalHOLExact, evalListHOLExact, hs4_p, hs4_w, wordOpHOL, wordOp, valueIsWord, valueWord, p1]
    have hval : s4.isValidValueHOLFinite VarKind.local (ofString "p") (.val (.word p1)) = true := by
      simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hs4_p, shapeOfHOLExact, shapeEqHOL]
    rw [hev]; dsimp only; rw [if_pos hval]; rfl
  rw [evaluateHOLFiniteState_seq_line780, hass1] at hnt4 hres4
  dsimp only at hnt4 hres4
  refine heapByteEff_of_seq_none hass1 ?_
  set s5 := setVarHOLFinite (ofString "p") (.val (.word p1)) s4
  have hAR5 : ArenaReady s5 := ⟨guestInv_setVar _ _ _ heff34.arena.1, heff34.arena.2⟩
  have hs5_p : s5.locals.lookup (ofString "p") = some (.val (.word p1)) := by
    simp [s5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs5_w : s5.locals.lookup (ofString "w") = some (.val (.word len1)) := by
    simp [s5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs4_w,
      show ofString "p" ≠ ofString "w" by decide]
  have hs5_buf : s5.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
    simp [s5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs4_buf,
      show ofString "p" ≠ ofString "buf" by decide]
  have hs5_mark : s5.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
    simp [s5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs4_mark,
      show ofString "p" ≠ ofString "mark" by decide]
  have hs5_nonce : s5.locals.lookup (ofString "nonce") = some (.val (.word nonce0)) := by
    simp [s5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs4_nonce,
      show ofString "p" ≠ ofString "nonce" by decide]
  have hs5_out : s5.locals.lookup (ofString "out") = some (.val (.word out0)) := by
    simp [s5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs4_out,
      show ofString "p" ≠ ofString "out" by decide]
  -- Step 6: `w = rlp_encode_word(p, nonce)`
  rw [evaluateHOLFiniteState_seq_line780] at hnt4 hres4
  rcases hc6 : evaluateHOLFiniteState s5
    (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
      [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "nonce")]) with ⟨r6, s6⟩
  have hnt_c6 : r6 ≠ some .timeOut := by rintro rfl; rw [hc6] at hnt4; exact hnt4 rfl
  have h6 := eval_call_local_rlp_encode_word s5 "w"
    (ExpHOL.var VarKind.local (ofString "p")) (ExpHOL.var VarKind.local (ofString "nonce"))
    p1 nonce0 Rbuf [] hAR5.1.code hAR5 ⟨len1, hs5_w⟩ hs5_p hs5_nonce
    ⟨(buf.toNat, 64), List.mem_cons_self, by omega, by omega⟩ (by rw [hc6]; exact hnt_c6)
  dsimp only at h6; rw [hc6] at h6 hnt4 hres4
  cases r6 with
  | some _ => exfalso; exact h6.2 (by simp) hres4
  | none =>
    dsimp only at hnt4 hres4
    refine heapByteEff_of_seq_none hc6 ?_
    obtain ⟨len2, hlen2_lo, hlen2_hi, _, hs6_g, hs6_loc, heff56⟩ := h6.1 rfl
    have hs6_w : s6.locals.lookup (ofString "w") = some (.val (.word len2)) := by
      rw [hs6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hs6_p : s6.locals.lookup (ofString "p") = some (.val (.word p1)) := by
      rw [hs6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs5_p,
        show ofString "w" ≠ ofString "p" by decide]
    have hs6_buf : s6.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
      rw [hs6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs5_buf,
        show ofString "w" ≠ ofString "buf" by decide]
    have hs6_mark : s6.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
      rw [hs6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs5_mark,
        show ofString "w" ≠ ofString "mark" by decide]
    have hs6_out : s6.locals.lookup (ofString "out") = some (.val (.word out0)) := by
      rw [hs6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs5_out,
        show ofString "w" ≠ ofString "out" by decide]
    -- Step 7: `p = p + w`
    let p2 : BitVec 64 := p1 + len2
    have hp2_nat : p2.toNat = p1.toNat + len2.toNat := by
      change (p1 + len2).toNat = p1.toNat + len2.toNat
      rw [BitVec.toNat_add]; change (p1.toNat + len2.toNat) % 2 ^ 64 = _
      exact Nat.mod_eq_of_lt (by omega)
    have hass2 : evaluateHOLFiniteState s6
        (.assign VarKind.local (ofString "p")
          (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])) =
        (none, setVarHOLFinite (ofString "p") (.val (.word p2)) s6) := by
      rw [evaluateHOLFiniteState_assign]
      have hev : @evalHOLExact 64 F _ s6.toExact (fun a => Classical.propDecidable (s6.memaddrs a))
          (.op .add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")]) =
          some (.val (.word p2)) := by
        simp [evalHOLExact, evalListHOLExact, hs6_p, hs6_w, wordOpHOL, wordOp, valueIsWord, valueWord, p2]
      have hval : s6.isValidValueHOLFinite VarKind.local (ofString "p") (.val (.word p2)) = true := by
        simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hs6_p, shapeOfHOLExact, shapeEqHOL]
      rw [hev]; dsimp only; rw [if_pos hval]; rfl
    rw [evaluateHOLFiniteState_seq_line780, hass2] at hnt4 hres4
    dsimp only at hnt4 hres4
    refine heapByteEff_of_seq_none hass2 ?_
    set s7 := setVarHOLFinite (ofString "p") (.val (.word p2)) s6
    have hAR7 : ArenaReady s7 := ⟨guestInv_setVar _ _ _ heff56.arena.1, heff56.arena.2⟩
    have hs7_p : s7.locals.lookup (ofString "p") = some (.val (.word p2)) := by
      simp [s7, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs7_buf : s7.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
      simp [s7, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs6_buf,
        show ofString "p" ≠ ofString "buf" by decide]
    have hs7_mark : s7.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
      simp [s7, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs6_mark,
        show ofString "p" ≠ ofString "mark" by decide]
    have hs7_out : s7.locals.lookup (ofString "out") = some (.val (.word out0)) := by
      simp [s7, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs6_out,
        show ofString "p" ≠ ofString "out" by decide]
    -- Step 8: `var payload = p - (buf + 9)`
    let pay : BitVec 64 := p2 - p0
    have hpay_nat : pay.toNat = len1.toNat + len2.toNat := by
      change (p2 - p0).toNat = len1.toNat + len2.toNat
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))]
      omega
    rw [evaluateHOLFiniteState_dec_total] at hnt4 hres4
    have hev_pay : @evalHOLExact 64 F _ s7.toExact (fun a => Classical.propDecidable (s7.memaddrs a))
        (.op .sub [ExpHOL.var VarKind.local (ofString "p"),
          .op .add [ExpHOL.var VarKind.local (ofString "buf"), .const 9]]) = some (.val (.word pay)) := by
      simp [evalHOLExact, evalListHOLExact, hs7_p, hs7_buf, wordOpHOL, wordOp, valueIsWord, valueWord, pay, p0]
    have hsh_pay : shapeEqHOL .one (shapeOfHOLExact (.val (.word pay) : ValueHOL 64)) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    dsimp only at hnt4 hres4
    rw [hev_pay] at hnt4 hres4; dsimp only at hnt4 hres4
    rw [if_pos hsh_pay] at hnt4 hres4
    refine heapByteEff_of_dec_word hev_pay ?_
    set s8 := setVarHOLFinite (ofString "payload") (.val (.word pay)) s7
    have hAR8 : ArenaReady s8 := ⟨guestInv_setVar _ _ _ hAR7.1, hAR7.2⟩
    have hs8_pay : s8.locals.lookup (ofString "payload") = some (.val (.word pay)) := by
      simp [s8, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs8_buf : s8.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
      simp [s8, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs7_buf,
        show ofString "payload" ≠ ofString "buf" by decide]
    have hs8_mark : s8.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
      simp [s8, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs7_mark,
        show ofString "payload" ≠ ofString "mark" by decide]
    have hs8_out : s8.locals.lookup (ofString "out") = some (.val (.word out0)) := by
      simp [s8, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs7_out,
        show ofString "payload" ≠ ofString "out" by decide]
    -- Step 9: `var 1 hl = rlp_list_header_len(payload)`
    obtain ⟨s9, hhl_nat, hhl1, hhl9, hs9_g, hs9_m, hs9_loc, heff89, hnt9, heq9⟩ :=
      eval_decCall_rlp_list_header_len s8 "hl" (ExpHOL.var VarKind.local (ofString "payload")) pay _
        Rbuf [] hAR8.1.code hAR8 hs8_pay hnt4
    set hlw := BitVec.ofNat 64 (rlpHeaderLenPure pay.toNat)
    rw [heq9] at hres4; dsimp only at hres4
    refine heapByteEff_of_eq_resVar heq9 ?_
    have hs9_hl : s9.locals.lookup (ofString "hl") = some (.val (.word hlw)) := by
      rw [hs9_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hs9_pay : s9.locals.lookup (ofString "payload") = some (.val (.word pay)) := by
      rw [hs9_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs8_pay,
        show ofString "hl" ≠ ofString "payload" by decide]
    have hs9_buf : s9.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
      rw [hs9_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs8_buf,
        show ofString "hl" ≠ ofString "buf" by decide]
    have hs9_mark : s9.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
      rw [hs9_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs8_mark,
        show ofString "hl" ≠ ofString "mark" by decide]
    have hs9_out : s9.locals.lookup (ofString "out") = some (.val (.word out0)) := by
      rw [hs9_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs8_out,
        show ofString "hl" ≠ ofString "out" by decide]
    -- Step 10: `rlp_encode_list_header(buf + 9 - hl, payload)`
    let dstL : BitVec 64 := p0 - hlw
    have hdstL_nat : dstL.toNat = buf.toNat + 9 - hlw.toNat := by
      change (p0 - hlw).toNat = buf.toNat + 9 - hlw.toNat
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega)), hp0_nat]
    rw [evaluateHOLFiniteState_seq_line780] at hnt9 hres4
    rcases hc10 : evaluateHOLFiniteState s9
      (.call (some (none, none)) (ofString "rlp_encode_list_header")
        [.op .sub [.op .add [ExpHOL.var VarKind.local (ofString "buf"), .const 9],
          ExpHOL.var VarKind.local (ofString "hl")],
         ExpHOL.var VarKind.local (ofString "payload")]) with ⟨r10, s10⟩
    have hnt_c10 : r10 ≠ some .timeOut := by rintro rfl; rw [hc10] at hnt9; exact hnt9 rfl
    have h10 := eval_call_rlp_encode_list_header s9
      (.op .sub [.op .add [ExpHOL.var VarKind.local (ofString "buf"), .const 9],
        ExpHOL.var VarKind.local (ofString "hl")])
      (ExpHOL.var VarKind.local (ofString "payload")) dstL pay Rbuf []
      heff89.arena.1.code heff89.arena
      (by simp [evalHOLExact, evalListHOLExact, hs9_buf, hs9_hl, wordOpHOL, wordOp, valueIsWord, valueWord, dstL, p0])
      hs9_pay
      ⟨(buf.toNat, 64), List.mem_cons_self, by omega, by omega⟩
      (by rw [hc10]; exact hnt_c10)
    dsimp only at h10; rw [hc10] at h10 hnt9 hres4
    cases r10 with
    | some _ => exfalso; exact h10.2 (by simp) hres4
    | none =>
      dsimp only at hnt9 hres4
      refine heapByteEff_of_seq_none hc10 ?_
      obtain ⟨_, heff910, hs10_loc⟩ := h10.1 rfl
      have hs10_hl : s10.locals.lookup (ofString "hl") = some (.val (.word hlw)) := by
        rw [hs10_loc]; exact hs9_hl
      have hs10_pay : s10.locals.lookup (ofString "payload") = some (.val (.word pay)) := by
        rw [hs10_loc]; exact hs9_pay
      have hs10_buf : s10.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
        rw [hs10_loc]; exact hs9_buf
      have hs10_mark : s10.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
        rw [hs10_loc]; exact hs9_mark
      have hs10_out : s10.locals.lookup (ofString "out") = some (.val (.word out0)) := by
        rw [hs10_loc]; exact hs9_out
      -- Note globals of `s10` equal globals of `s2` (so `heap_ptr = q1 = buf + 64`, `keccak_pad`/`keccak_st` = `s`'s):
      have hs2_s10_eff : HeapByteEff s2 s10 Rbuf [] := by
        have h23 : HeapByteEff s2 s3 Rbuf [] :=
          (HeapByteEff.refl heff12.arena Rbuf []).locals_clock s3.locals s3.clock
        have h45 : HeapByteEff s4 s5 Rbuf [] :=
          (HeapByteEff.refl heff34.arena Rbuf []).locals_clock s5.locals s5.clock
        have h67 : HeapByteEff s6 s7 Rbuf [] :=
          (HeapByteEff.refl heff56.arena Rbuf []).locals_clock s7.locals s7.clock
        have h78 : HeapByteEff s7 s8 Rbuf [] :=
          (HeapByteEff.refl hAR7 Rbuf []).locals_clock s8.locals s8.clock
        exact ((((((h23.trans heff34).trans h45).trans heff56).trans h67).trans h78).trans heff89).trans heff910
      -- Step 11: `var 1 h = alloc(32)`
      obtain ⟨hw, n32, q2, s11, h32_ev, hhw_hp, hhw8, hq2_nat, _, hq2_hi, hq2_8, hs11_hp, hs11_g, hs11_m, hs11_loc,
          heff1011, hnt11, hres11, heq11⟩ :=
        eval_decCall_alloc_resumes s10 "h" (.const 32) _ Rbuf ["heap_ptr"]
          heff910.arena.1.code heff910.arena (by simp) hnt9 hres4
      have hn32 : n32 = 32 := by simp [evalHOLExact] at h32_ev; exact h32_ev.symm
      subst hn32
      have h32_val : (32 : BitVec 64).toNat = 32 := by decide
      rw [h32_val] at hq2_nat
      have hhw_eq_q1 : hw.toNat = q1.toNat := by
        rw [hhw_hp, ← hs2_hp]
        unfold globN
        rw [← hs2_s10_eff.globals (ofString "heap_ptr") (by simp)]
      have hq2_eq : q2.toNat = hw.toNat + 32 := by omega
      refine heapByteEff_of_eq_resVar heq11 ?_
      let Rall : List Ivl := (hw.toNat, 32) :: Rbuf
      have hs11_h : s11.locals.lookup (ofString "h") = some (.val (.word hw)) := by
        rw [hs11_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
      have hs11_hl : s11.locals.lookup (ofString "hl") = some (.val (.word hlw)) := by
        rw [hs11_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs10_hl,
          show ofString "h" ≠ ofString "hl" by decide]
      have hs11_pay : s11.locals.lookup (ofString "payload") = some (.val (.word pay)) := by
        rw [hs11_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs10_pay,
          show ofString "h" ≠ ofString "payload" by decide]
      have hs11_buf : s11.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
        rw [hs11_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs10_buf,
          show ofString "h" ≠ ofString "buf" by decide]
      have hs11_mark : s11.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
        rw [hs11_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs10_mark,
          show ofString "h" ≠ ofString "mark" by decide]
      have hs11_out : s11.locals.lookup (ofString "out") = some (.val (.word out0)) := by
        rw [hs11_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs10_out,
          show ofString "h" ≠ ofString "out" by decide]
      -- Step 12: `keccak256(buf + 9 - hl, payload + hl, h)`
      have heff_s_s11 : HeapByteEff s s11 Rall ["heap_ptr"] := by
        have m01 : HeapByteEff s s1 Rall ["heap_ptr"] :=
          heff01.mono (fun i hi _ => Or.inl ⟨i, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hi), le_rfl, le_rfl⟩)
            (fun _ hg => hg)
        have m12 : HeapByteEff s1 s2 Rall ["heap_ptr"] :=
          heff12.mono (fun i hi _ => Or.inl ⟨i, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hi), le_rfl, le_rfl⟩)
            (fun _ hg => hg)
        have m210 : HeapByteEff s2 s10 Rall ["heap_ptr"] :=
          hs2_s10_eff.mono (fun i hi _ => Or.inl ⟨i, List.mem_cons_of_mem _ hi, le_rfl, le_rfl⟩) (fun _ h => by cases h)
        have m1011 : HeapByteEff s10 s11 Rall ["heap_ptr"] :=
          heff1011.mono (fun i hi _ => Or.inl ⟨i, List.mem_cons_of_mem _ hi, le_rfl, le_rfl⟩) (fun _ hg => hg)
        exact ((m01.trans m12).trans m210).trans m1011
      have hkpad_eq : globN s11 "keccak_pad" = globN s "keccak_pad" := by
        unfold globN; rw [← heff_s_s11.globals (ofString "keccak_pad") (by decide)]
      have hkst_eq : globN s11 "keccak_st" = globN s "keccak_st" := by
        unfold globN; rw [← heff_s_s11.globals (ofString "keccak_st") (by decide)]
      rw [evaluateHOLFiniteState_seq_line780] at hnt11 hres11
      rcases hc12 : evaluateHOLFiniteState s11
        (.call (some (none, none)) (ofString "keccak256")
          [.op .sub [.op .add [ExpHOL.var VarKind.local (ofString "buf"), .const 9],
            ExpHOL.var VarKind.local (ofString "hl")],
           .op .add [ExpHOL.var VarKind.local (ofString "payload"),
            ExpHOL.var VarKind.local (ofString "hl")],
           ExpHOL.var VarKind.local (ofString "h")]) with ⟨r12, s12⟩
      have hnt_c12 : r12 ≠ some .timeOut := by rintro rfl; rw [hc12] at hnt11; exact hnt11 rfl
      have hor_c12 : r12 = none ∨ Resumes r12 := by
        cases r12 with
        | none => exact Or.inl rfl
        | some rk =>
          right
          rw [hc12] at hres11; dsimp only at hres11
          exact hres11
      have h12 := eval_call_keccak256_heap s11
        (.op .sub [.op .add [ExpHOL.var VarKind.local (ofString "buf"), .const 9],
          ExpHOL.var VarKind.local (ofString "hl")])
        (.op .add [ExpHOL.var VarKind.local (ofString "payload"),
          ExpHOL.var VarKind.local (ofString "hl")])
        (ExpHOL.var VarKind.local (ofString "h"))
        dstL (pay + hlw) hw Rall [] heff1011.arena.1.code heff1011.arena
        (by simp [evalHOLExact, evalListHOLExact, hs11_buf, hs11_hl, wordOpHOL, wordOp, valueIsWord, valueWord, dstL, p0])
        (by simp [evalHOLExact, evalListHOLExact, hs11_pay, hs11_hl, wordOpHOL, wordOp, valueIsWord, valueWord])
        hs11_h
        ⟨(hw.toNat, 32), List.mem_cons_self, le_rfl, le_rfl⟩
        (fun hnz => by
          rw [hkpad_eq] at hnz ⊢
          exact ⟨(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
            by simp [Rall, Rbuf, Rs], le_rfl, by simp [hnz]⟩)
        (fun hnz => by
          rw [hkst_eq] at hnz ⊢
          exact ⟨(globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
            by simp [Rall, Rbuf, Rs], le_rfl, by simp [hnz]⟩)
        (by rw [hc12]; exact hnt_c12)
        (by rw [hc12]; exact hor_c12)
      rw [hc12] at h12 hnt11 hres11
      cases r12 with
      | some r_12 =>
        have heff_fin : HeapByteEff s s12 Rall ["heap_ptr"] :=
          heff_s_s11.trans (h12.1.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩) (fun _ h => by cases h))
        refine heapByteEff_of_seq_some hc12 ?_
        exact heff_fin.mono
          (fun i hi _ => by
            simp only [Rall, Rbuf, List.mem_cons] at hi
            rcases hi with rfl | rfl | hi_rs
            · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
            · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
            · exact Or.inl ⟨i, by simpa using hi_rs, le_rfl, le_rfl⟩)
          (fun _ hg => hg)
      | none =>
        dsimp only at hnt11 hres11
        refine heapByteEff_of_seq_none hc12 ?_
        obtain ⟨hs12_loc, hs12_g⟩ := h12.2 rfl
        have hs12_h : s12.locals.lookup (ofString "h") = some (.val (.word hw)) := by
          rw [hs12_loc]; exact hs11_h
        have hs12_mark : s12.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
          rw [hs12_loc]; exact hs11_mark
        have hs12_out : s12.locals.lookup (ofString "out") = some (.val (.word out0)) := by
          rw [hs12_loc]; exact hs11_out
        -- Step 13: `memcpy(out, h + 12, 20)`
        rw [evaluateHOLFiniteState_seq_line780] at hnt11 hres11
        rcases hc13 : evaluateHOLFiniteState s12
          (.call (some (none, none)) (ofString "memcpy")
            [ExpHOL.var VarKind.local (ofString "out"),
             .op .add [ExpHOL.var VarKind.local (ofString "h"), .const 12],
             .const 20]) with ⟨r13, s13⟩
        have hnt_c13 : r13 ≠ some .timeOut := by rintro rfl; rw [hc13] at hnt11; exact hnt11 rfl
        have h13 := eval_call_memcpy_heap s12
          (ExpHOL.var VarKind.local (ofString "out"))
          (.op .add [ExpHOL.var VarKind.local (ofString "h"), .const 12])
          (.const 20) out0 (hw + 12) 20 Rall [] h12.1.arena.1.code h12.1.arena
          hs12_out
          (by simp [evalHOLExact, evalListHOLExact, hs12_h, wordOpHOL, wordOp, valueIsWord, valueWord])
          rfl
          (fun _ => ⟨(locN s "out", 20), by simp [Rall, Rbuf, Rs],
            by rw [hout_locN], by rw [hout_locN]; change out0.toNat + 20 ≤ out0.toNat + 20; omega⟩)
          (by rw [hc13]; exact hnt_c13)
        dsimp only at h13; rw [hc13] at h13 hnt11 hres11
        cases r13 with
        | some _ => exfalso; exact h13.2 (by simp) hres11
        | none =>
          dsimp only at hnt11 hres11
          refine heapByteEff_of_seq_none hc13 ?_
          obtain ⟨heff1213, hs13_loc, hs13_g⟩ := h13.1 rfl
          have hs13_mark : s13.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
            rw [hs13_loc]; exact hs12_mark
          have heff_s_s13 : HeapByteEff s s13 Rall ["heap_ptr"] :=
            (heff_s_s11.trans (h12.1.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩) (fun _ h => by cases h))).trans
              (heff1213.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩) (fun _ h => by cases h))
          -- Step 14: `heap_release(mark)`
          rw [evaluateHOLFiniteState_seq_line780] at hnt11 hres11
          rcases hc14 : evaluateHOLFiniteState s13
            (.call (some (none, none)) (ofString "heap_release")
              [ExpHOL.var VarKind.local (ofString "mark")]) with ⟨r14, s14⟩
          have hnt_c14 : r14 ≠ some .timeOut := by
            rintro rfl; rw [hc14] at hnt11; exact hnt11 rfl
          have h14 := eval_call_heap_release s13 (ExpHOL.var VarKind.local (ofString "mark")) mark
            Rall ["heap_ptr"] heff1213.arena.1.code heff_s_s13 (by simp) hs13_mark
            (by rw [hmark_nat]) (by rw [hmark_nat]; exact hAR.2.1)
            (by rw [hmark_nat]; exact hAR.2.2.1)
            (by rw [hmark_nat]; exact hAR.2.2.2.2.2.2.1) (by rw [hc14]; exact hnt_c14)
          dsimp only at h14
          rw [hc14] at h14
          obtain ⟨rfl, _, _, _, heff_s_s14⟩ := h14
          refine heapByteEff_of_seq_none hc14 ?_
          have heff_ret : HeapByteEff s14
              (evaluateHOLFiniteState s14 (.return (.const 0))).2 Rall ["heap_ptr"] :=
            HeapByteEff.of_byteEff heff_s_s14.arena
              (R13Shards.Keccak256.byteEff_return s14 (.const 0) Rall)
          have heff_all : HeapByteEff s
              (evaluateHOLFiniteState s14 (.return (.const 0))).2 Rall ["heap_ptr"] :=
            heff_s_s14.trans heff_ret
          exact heff_all.mono
            (fun i hi _ => by
              simp only [Rall, Rbuf, List.mem_cons] at hi
              rcases hi with rfl | rfl | hi_rs
              · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
              · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
              · exact Or.inl ⟨i, by simpa using hi_rs, le_rfl, le_rfl⟩)
            (fun _ hg => hg)

/-! ## Section 4: `st_be64` combinator and `wk_encode_account` -/

private theorem eval_bswap64_body_word {F : Type}
    (s : PanSemStateFiniteExact 64 F) (x0 : BitVec 64)
    (hx : s.locals.lookup (ofString "x") = some (.val (.word x0))) :
    ∃ (rv : BitVec 64),
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_bswap64)).1 =
        some (.returned (.val (.word rv))) ∧
      M13.LocFrame s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_bswap64)).2 := by
  have hlf : M13.LocFrame s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_bswap64)).2 :=
    M13.locFrameW_eval _ (by decide) s
  have hb : sourceFnBody Guest.Software.guestFn_bswap64 =
      .seq (.assign VarKind.local (ofString "x")
          (.op .or [.shift .lsl (.op .and [ExpHOL.var VarKind.local (ofString "x"), .const 71777214294589695]) (.const 8),
            .op .and [.shift .lsr (ExpHOL.var VarKind.local (ofString "x")) (.const 8), .const 71777214294589695]]))
        (.seq (.assign VarKind.local (ofString "x")
            (.op .or [.shift .lsl (.op .and [ExpHOL.var VarKind.local (ofString "x"), .const 281470681808895]) (.const 16),
              .op .and [.shift .lsr (ExpHOL.var VarKind.local (ofString "x")) (.const 16), .const 281470681808895]]))
          (.return (.op .or [.shift .lsl (ExpHOL.var VarKind.local (ofString "x")) (.const 32),
            .shift .lsr (ExpHOL.var VarKind.local (ofString "x")) (.const 32)]))) := rfl
  let x1 : BitVec 64 :=
    OrOp.or ((x0 &&& 71777214294589695#64) <<< 8) (OrOp.or (x0 >>> 8 &&& 71777214294589695#64) 0#64)
  let x2 : BitVec 64 :=
    OrOp.or ((x1 &&& 281470681808895#64) <<< 16) (OrOp.or (x1 >>> 16 &&& 281470681808895#64) 0#64)
  let x3 : BitVec 64 :=
    OrOp.or (x2 <<< 32) (OrOp.or (x2 >>> 32) 0#64)
  refine ⟨x3, ?_, hlf⟩
  rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
  have hev1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .or [.shift .lsl (.op .and [ExpHOL.var VarKind.local (ofString "x"), .const 71777214294589695]) (.const 8),
        .op .and [.shift .lsr (ExpHOL.var VarKind.local (ofString "x")) (.const 8), .const 71777214294589695]]) =
      some (.val (.word x1)) := by
    simp [evalHOLExact, evalListHOLExact, hx, wordOpHOL, wordOp, wordShiftHOL, valueIsWord, valueWord, x1]
  have hv1 : s.isValidValueHOLFinite VarKind.local (ofString "x") (.val (.word x1)) = true := by
    simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hx, shapeOfHOLExact, shapeEqHOL]
  rw [hev1]; dsimp only; rw [if_pos hv1]; dsimp only [setKvarHOLFinite]
  set s1 := setVarHOLFinite (ofString "x") (.val (.word x1)) s
  have hx1 : s1.locals.lookup (ofString "x") = some (.val (.word x1)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
  have hev2 : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
      (.op .or [.shift .lsl (.op .and [ExpHOL.var VarKind.local (ofString "x"), .const 281470681808895]) (.const 16),
        .op .and [.shift .lsr (ExpHOL.var VarKind.local (ofString "x")) (.const 16), .const 281470681808895]]) =
      some (.val (.word x2)) := by
    simp [evalHOLExact, evalListHOLExact, hx1, wordOpHOL, wordOp, wordShiftHOL, valueIsWord, valueWord, x2]
  have hv2 : s1.isValidValueHOLFinite VarKind.local (ofString "x") (.val (.word x2)) = true := by
    simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hx1, shapeOfHOLExact, shapeEqHOL]
  rw [hev2]; dsimp only; rw [if_pos hv2]; dsimp only [setKvarHOLFinite]
  set s2 := setVarHOLFinite (ofString "x") (.val (.word x2)) s1
  have hx2 : s2.locals.lookup (ofString "x") = some (.val (.word x2)) := by
    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [evaluateHOLFiniteState_return]
  have hev3 : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
      (.op .or [.shift .lsl (ExpHOL.var VarKind.local (ofString "x")) (.const 32),
        .shift .lsr (ExpHOL.var VarKind.local (ofString "x")) (.const 32)]) =
      some (.val (.word x3)) := by
    simp [evalHOLExact, evalListHOLExact, hx2, wordOpHOL, wordOp, wordShiftHOL, valueIsWord, valueWord, x3]
  rw [hev3]; dsimp only
  have hsz : sizeOfShapeWithContextHOL s2.structs (shapeOfHOLExact (.val (.word x3) : ValueHOL 64)) ≤ 32 := by
    simp [shapeOfHOLExact]
  rw [if_pos hsz]

private theorem storeByte_only_none_or_error' {F : Type}
    (t : PanSemStateFiniteExact 64 F) (dst val : ExpHOL 64) :
    (evaluateHOLFiniteState t (.storeByte dst val)).1 = none ∧
      (evaluateHOLFiniteState t (.storeByte dst val)).2.locals = t.locals ∨
      (evaluateHOLFiniteState t (.storeByte dst val)).1 = some .error := by
  rw [evaluateHOLFiniteState_storeByte]
  split
  · split
    · split
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr rfl
    · exact Or.inr rfl
  · exact Or.inr rfl

private theorem store_only_none_or_error' {F : Type}
    (t : PanSemStateFiniteExact 64 F) (dst val : ExpHOL 64) :
    (evaluateHOLFiniteState t (.store dst val)).1 = none ∧
      (evaluateHOLFiniteState t (.store dst val)).2.locals = t.locals ∨
      (evaluateHOLFiniteState t (.store dst val)).1 = some .error := by
  rw [evaluateHOLFiniteState_store]
  split
  · split
    · split
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr rfl
    · exact Or.inr rfl
  · exact Or.inr rfl

private theorem eval_st_be32_body_eff {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (p0 v0 : BitVec 64)
    (hG : GuestInv s0)
    (hp : s0.locals.lookup (ofString "p") = some (.val (.word p0)))
    (_hv : s0.locals.lookup (ofString "v") = some (.val (.word v0))) :
    let out := evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_st_be32)
    (∀ rv, out.1 = some (.returned rv) →
      rv = .val (.word 0) ∧
      sourceBase ≤ p0.toNat ∧ p0.toNat + 4 ≤ heapEnd ∧
      R13Shards.Keccak256.ByteEff s0 out.2 [(p0.toNat, 4)]) ∧
    (∀ r, out.1 = some r → (∀ rv, r ≠ .returned rv) → ¬ Resumes (some r)) := by
  have hhe264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  have hb : sourceFnBody Guest.Software.guestFn_st_be32 =
      .seq (.storeByte (ExpHOL.var VarKind.local (ofString "p"))
          (.shift .lsr (ExpHOL.var VarKind.local (ofString "v")) (.const 24)))
        (.seq (.storeByte (.op .add [ExpHOL.var VarKind.local (ofString "p"), .const 1])
            (.shift .lsr (ExpHOL.var VarKind.local (ofString "v")) (.const 16)))
          (.seq (.storeByte (.op .add [ExpHOL.var VarKind.local (ofString "p"), .const 2])
              (.shift .lsr (ExpHOL.var VarKind.local (ofString "v")) (.const 8)))
            (.seq (.storeByte (.op .add [ExpHOL.var VarKind.local (ofString "p"), .const 3])
                (ExpHOL.var VarKind.local (ofString "v")))
              (.return (.const 0))))) := rfl
  dsimp only
  rw [hb, evaluateHOLFiniteState_seq_line780]
  rcases h1 : evaluateHOLFiniteState s0
    (.storeByte (ExpHOL.var VarKind.local (ofString "p"))
      (.shift .lsr (ExpHOL.var VarKind.local (ofString "v")) (.const 24))) with ⟨r1, s1⟩
  have ho1 := storeByte_only_none_or_error' s0
    (ExpHOL.var VarKind.local (ofString "p"))
    (.shift .lsr (ExpHOL.var VarKind.local (ofString "v")) (.const 24))
  rw [h1] at ho1
  rcases ho1 with ⟨hr1, hl1⟩ | hr1
  · dsimp only at hr1 hl1; subst hr1; dsimp only
    have hp1 : s1.locals.lookup (ofString "p") = some (.val (.word p0)) := by rw [hl1]; exact hp
    have hb0 := R13Shards.Keccak256.byteEff_storeByte (Rl := [(p0.toNat, 4)]) hG
      (ExpHOL.var VarKind.local (ofString "p"))
      (.shift .lsr (ExpHOL.var VarKind.local (ofString "v")) (.const 24))
      (fun x hx _ => by
        simp [evalHOLExact, hp] at hx; subst hx
        exact ⟨(p0.toNat, 4), List.mem_singleton.2 rfl, le_rfl, by omega⟩)
    rw [h1] at hb0
    obtain ⟨heff1, hdom1⟩ := hb0
    obtain ⟨x0, hx0, hd0_lo, hd0_hi⟩ := hdom1 rfl
    simp [evalHOLExact, hp] at hx0; subst hx0
    have hG1 : GuestInv s1 := guestInv_congr heff1.code heff1.memaddrs heff1.shMemaddrs heff1.baseAddr hG
    rw [evaluateHOLFiniteState_seq_line780]
    rcases h2 : evaluateHOLFiniteState s1
      (.storeByte (.op .add [ExpHOL.var VarKind.local (ofString "p"), .const 1])
        (.shift .lsr (ExpHOL.var VarKind.local (ofString "v")) (.const 16))) with ⟨r2, s2⟩
    have ho2 := storeByte_only_none_or_error' s1
      (.op .add [ExpHOL.var VarKind.local (ofString "p"), .const 1])
      (.shift .lsr (ExpHOL.var VarKind.local (ofString "v")) (.const 16))
    rw [h2] at ho2
    rcases ho2 with ⟨hr2, hl2⟩ | hr2
    · dsimp only at hr2 hl2; subst hr2; dsimp only
      have hp2 : s2.locals.lookup (ofString "p") = some (.val (.word p0)) := by rw [hl2]; exact hp1
      have hp0_1 : (p0 + 1#64).toNat = p0.toNat + 1 := by
        rw [BitVec.toNat_add]; change (p0.toNat + 1) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
      have hb1 := R13Shards.Keccak256.byteEff_storeByte (Rl := [(p0.toNat, 4)]) hG1
        (.op .add [ExpHOL.var VarKind.local (ofString "p"), .const 1])
        (.shift .lsr (ExpHOL.var VarKind.local (ofString "v")) (.const 16))
        (fun x hx _ => by
          simp [evalHOLExact, evalListHOLExact, hp1, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
          subst hx; exact ⟨(p0.toNat, 4), List.mem_singleton.2 rfl, by omega, by omega⟩)
      rw [h2] at hb1
      obtain ⟨heff2, hdom2⟩ := hb1
      obtain ⟨x1, hx1, _, hd1_hi⟩ := hdom2 rfl
      simp [evalHOLExact, evalListHOLExact, hp1, wordOpHOL, wordOp, valueIsWord, valueWord] at hx1
      subst hx1
      have hG2 : GuestInv s2 := guestInv_congr heff2.code heff2.memaddrs heff2.shMemaddrs heff2.baseAddr hG1
      rw [evaluateHOLFiniteState_seq_line780]
      rcases h3 : evaluateHOLFiniteState s2
        (.storeByte (.op .add [ExpHOL.var VarKind.local (ofString "p"), .const 2])
          (.shift .lsr (ExpHOL.var VarKind.local (ofString "v")) (.const 8))) with ⟨r3, s3⟩
      have ho3 := storeByte_only_none_or_error' s2
        (.op .add [ExpHOL.var VarKind.local (ofString "p"), .const 2])
        (.shift .lsr (ExpHOL.var VarKind.local (ofString "v")) (.const 8))
      rw [h3] at ho3
      rcases ho3 with ⟨hr3, hl3⟩ | hr3
      · dsimp only at hr3 hl3; subst hr3; dsimp only
        have hp3 : s3.locals.lookup (ofString "p") = some (.val (.word p0)) := by rw [hl3]; exact hp2
        have hp0_2 : (p0 + 2#64).toNat = p0.toNat + 2 := by
          rw [BitVec.toNat_add]; change (p0.toNat + 2) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
        have hb2 := R13Shards.Keccak256.byteEff_storeByte (Rl := [(p0.toNat, 4)]) hG2
          (.op .add [ExpHOL.var VarKind.local (ofString "p"), .const 2])
          (.shift .lsr (ExpHOL.var VarKind.local (ofString "v")) (.const 8))
          (fun x hx _ => by
            simp [evalHOLExact, evalListHOLExact, hp2, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
            subst hx; exact ⟨(p0.toNat, 4), List.mem_singleton.2 rfl, by omega, by omega⟩)
        rw [h3] at hb2
        obtain ⟨heff3, hdom3⟩ := hb2
        obtain ⟨x2, hx2, _, hd2_hi⟩ := hdom3 rfl
        simp [evalHOLExact, evalListHOLExact, hp2, wordOpHOL, wordOp, valueIsWord, valueWord] at hx2
        subst hx2
        have hG3 : GuestInv s3 := guestInv_congr heff3.code heff3.memaddrs heff3.shMemaddrs heff3.baseAddr hG2
        rw [evaluateHOLFiniteState_seq_line780]
        rcases h4 : evaluateHOLFiniteState s3
          (.storeByte (.op .add [ExpHOL.var VarKind.local (ofString "p"), .const 3])
            (ExpHOL.var VarKind.local (ofString "v"))) with ⟨r4, s4⟩
        have ho4 := storeByte_only_none_or_error' s3
          (.op .add [ExpHOL.var VarKind.local (ofString "p"), .const 3])
          (ExpHOL.var VarKind.local (ofString "v"))
        rw [h4] at ho4
        rcases ho4 with ⟨hr4, _⟩ | hr4
        · dsimp only at hr4; subst hr4; dsimp only
          have hp0_3 : (p0 + 3#64).toNat = p0.toNat + 3 := by
            rw [BitVec.toNat_add]; change (p0.toNat + 3) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
          have hb3 := R13Shards.Keccak256.byteEff_storeByte (Rl := [(p0.toNat, 4)]) hG3
            (.op .add [ExpHOL.var VarKind.local (ofString "p"), .const 3])
            (ExpHOL.var VarKind.local (ofString "v"))
            (fun x hx _ => by
              simp [evalHOLExact, evalListHOLExact, hp3, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
              subst hx; exact ⟨(p0.toNat, 4), List.mem_singleton.2 rfl, by omega, by omega⟩)
          rw [h4] at hb3
          obtain ⟨heff4, hdom4⟩ := hb3
          obtain ⟨x3, hx3, _, hd3_hi⟩ := hdom4 rfl
          simp [evalHOLExact, evalListHOLExact, hp3, wordOpHOL, wordOp, valueIsWord, valueWord] at hx3
          subst hx3
          have hret4 : evaluateHOLFiniteState s4 (.return (.const 0)) =
              (some (.returned (.val (.word 0))), s4.emptyLocalsHOLFinite) := by
            rw [evaluateHOLFiniteState_return]
            have hc0 : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a)) (.const 0) =
                some (.val (.word 0)) := rfl
            rw [hc0]; dsimp only
            have hsz : sizeOfShapeWithContextHOL s4.structs (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) ≤ 32 := by
              simp [shapeOfHOLExact]
            rw [if_pos hsz]
          rw [hret4]
          refine ⟨fun rv hrv => ?_, fun r hr hne => ?_⟩
          · injection hrv with e1; injection e1 with e2
            exact ⟨e2.symm, hd0_lo, by omega,
              (((heff1.trans heff2).trans heff3).trans heff4).locals_clock _ _⟩
          · injection hr with e1; exact False.elim (hne _ e1.symm)
        · dsimp only at hr4; subst hr4; dsimp only
          exact ⟨fun _ h => by simp at h, fun r hr _ => by injection hr with e; subst e; exact not_resumes_error⟩
      · dsimp only at hr3; subst hr3; dsimp only
        exact ⟨fun _ h => by simp at h, fun r hr _ => by injection hr with e; subst e; exact not_resumes_error⟩
    · dsimp only at hr2; subst hr2; dsimp only
      exact ⟨fun _ h => by simp at h, fun r hr _ => by injection hr with e; subst e; exact not_resumes_error⟩
  · dsimp only at hr1; subst hr1; dsimp only
    exact ⟨fun _ h => by simp at h, fun r hr _ => by injection hr with e; subst e; exact not_resumes_error⟩

theorem eval_call_st_be64_heap {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pExp vExp : ExpHOL 64)
    (p0 v0 : BitVec 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hp : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) pExp =
      some (.val (.word p0)))
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) vExp =
      some (.val (.word v0)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ p0.toNat ∧ p0.toNat + 8 ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "st_be64") [pExp, vExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "st_be64") [pExp, vExp])
    (out.1 = none →
      sourceBase ≤ p0.toNat ∧ p0.toNat + 8 ≤ heapEnd ∧
      HeapByteEff s out.2 Rl gw ∧ out.2.locals = s.locals ∧ out.2.globals = s.globals) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  intro out; dsimp only [out]
  have hhe264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [pExp, vExp] = some [.val (.word p0), .val (.word v0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hp, hv]
  have hlk := pan_two_word_lookup s.code.lookup (ofString "st_be64")
    (ofString "p") (ofString "v")
    (sourceFnBody Guest.Software.guestFn_st_be64) p0 v0 (by decide)
    (by rw [hcode]; exact lookup_st_be64)
  simp only [ha, hlk] at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set cmap := (HolFiniteMapExact.empty.update (ofString "p", ValueHOL.val (.word p0))).update
      (ofString "v", ValueHOL.val (.word v0))
    set ent := callEntryStateHOLFinite s cmap
    have hGe : GuestInv ent := guestInv_callEntry s cmap hAR.1
    have hent_p : ent.locals.lookup (ofString "p") = some (.val (.word p0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "v" ≠ ofString "p" by decide]
    have hent_v : ent.locals.lookup (ofString "v") = some (.val (.word v0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hb64 : sourceFnBody Guest.Software.guestFn_st_be64 =
        .seq (.ite (.cmp .equal (.op .and [ExpHOL.var VarKind.local (ofString "p"), .const 7]) (.const 0))
            (.decCall (ofString "w") .one (ofString "bswap64") [ExpHOL.var VarKind.local (ofString "v")]
              (.seq (.store (ExpHOL.var VarKind.local (ofString "p")) (ExpHOL.var VarKind.local (ofString "w")))
                (.return (.const 0))))
            .skip)
          (.seq (.call (some (none, none)) (ofString "st_be32")
              [ExpHOL.var VarKind.local (ofString "p"),
               .shift .lsr (ExpHOL.var VarKind.local (ofString "v")) (.const 32)])
            (.seq (.call (some (none, none)) (ofString "st_be32")
                [.op .add [ExpHOL.var VarKind.local (ofString "p"), .const 4],
                 ExpHOL.var VarKind.local (ofString "v")])
              (.return (.const 0)))) := rfl
    -- Evaluate `st_be64` body on `ent`:
    suffices hbody :
        let bout := evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_st_be64)
        (∀ rv, bout.1 = some (.returned rv) →
          rv = .val (.word 0) ∧
          sourceBase ≤ p0.toNat ∧ p0.toNat + 8 ≤ heapEnd ∧
          R13Shards.Keccak256.ByteEff ent bout.2 Rl) ∧
        (∀ r, bout.1 = some r → (∀ rv, r ≠ .returned rv) → ¬ Resumes (some r)) by
      dsimp only at hbody
      rcases hb_ev : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_st_be64) with ⟨rb, sb⟩
      have hnt_b : rb ≠ some .timeOut := by rintro rfl; rw [hb_ev] at hnt; exact hnt rfl
      rw [hb_ev] at hbody
      simp only [hb_ev] at hnt ⊢
      cases rb with
      | none => exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
      | some r =>
        cases r with
        | timeOut => exact absurd rfl hnt_b
        | exception eid ev =>
          exact ⟨fun h => by simp at h, fun _ => hbody.2 (.exception eid ev) rfl (fun _ h => by cases h)⟩
        | returned rv =>
          obtain ⟨rfl, hd_lo, hd_hi, heff_b⟩ := hbody.1 rv rfl
          have hsh0 : shapeEqHOL (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) .one = true := by
            simp [shapeOfHOLExact, shapeEqHOL]
          dsimp only; rw [if_pos hsh0]
          have heff_all : R13Shards.Keccak256.ByteEff s { sb with locals := s.locals } Rl :=
            (((R13Shards.Keccak256.ByteEff.refl s Rl).locals_clock ent.locals ent.clock).trans heff_b).locals_clock s.locals sb.clock
          exact ⟨fun _ => ⟨hd_lo, hd_hi, HeapByteEff.of_byteEff hAR heff_all, rfl, heff_all.globals⟩,
            fun h => False.elim (h rfl)⟩
        | «break» | «continue» | error =>
          exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
        | finalFfi _ =>
          exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
    dsimp only
    rw [hb64, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
    have hev_cond : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
        (.cmp .equal (.op .and [ExpHOL.var VarKind.local (ofString "p"), .const 7]) (.const 0)) =
        some (.val (.word (if (p0 &&& 7) = 0 then 1 else 0))) := by
      simp [evalHOLExact, evalListHOLExact, hent_p, wordOpHOL, wordOp, valueIsWord, valueWord,
        Compiler.Encoders.Asm.wordCmpHOL]
    rw [hev_cond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hal : (p0 &&& 7) = 0
    · -- Aligned path (`(p0 &&& 7) = 0`):
      have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
      simp only [hal, ↓reduceIte, h10] at hnt ⊢
      rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
      have ha_bs : evalListHOLFinite ent (h := fun a => Classical.propDecidable (ent.memaddrs a))
          [ExpHOL.var VarKind.local (ofString "v")] = some [.val (.word v0)] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hent_v]
      have hlk_bs := pan_one_word_lookup ent.code.lookup (ofString "bswap64") (ofString "x")
        (sourceFnBody Guest.Software.guestFn_bswap64) v0
        (by change s.code.lookup _ = _; rw [hcode]; exact lookup_bswap64)
      simp only [ha_bs, hlk_bs] at hnt ⊢
      by_cases hcz2 : ent.clock = 0
      · simp [hcz2] at hnt
      · simp only [hcz2, ↓reduceIte] at hnt ⊢
        set cmap_bs := HolFiniteMapExact.empty.update (ofString "x", ValueHOL.val (.word v0))
        set ent_bs := callEntryStateHOLFinite ent cmap_bs
        have hx_bs : ent_bs.locals.lookup (ofString "x") = some (.val (.word v0)) := by
          simp [ent_bs, cmap_bs, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        obtain ⟨wv, hr_bs, hlf_bs⟩ := eval_bswap64_body_word ent_bs v0 hx_bs
        rcases hbs_ev : evaluateHOLFiniteState ent_bs (sourceFnBody Guest.Software.guestFn_bswap64) with ⟨rbs, sbs⟩
        rw [hbs_ev] at hr_bs hlf_bs
        dsimp only at hr_bs hlf_bs
        subst hr_bs
        have hsh_wv : (shapeEqHOL (shapeOfHOLExact (.val (.word wv) : ValueHOL 64)) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word wv) : ValueHOL 64)) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        simp only [hbs_ev] at hnt ⊢
        rw [if_pos hsh_wv]; dsimp only
        set mid_w := setVarHOLFinite (ofString "w") (.val (.word wv)) { sbs with locals := ent.locals }
        have hlf_mid_w : M13.LocFrame ent mid_w := by
          have h1 : M13.LocFrame ent ent_bs := by cases s; rfl
          exact (((h1.trans hlf_bs).locals _).setVar _ _)
        have hG_mw : GuestInv mid_w := (hlf_mid_w.arenaReady ⟨hGe, hAR.2⟩).1
        have hp_mw : mid_w.locals.lookup (ofString "p") = some (.val (.word p0)) := by
          simp [mid_w, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_p,
            show ofString "w" ≠ ofString "p" by decide]
        have hw_mw : mid_w.locals.lookup (ofString "w") = some (.val (.word wv)) := by
          simp [mid_w, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        rw [evaluateHOLFiniteState_seq_line780]
        rcases hst_ev : evaluateHOLFiniteState mid_w
          (.store (ExpHOL.var VarKind.local (ofString "p")) (ExpHOL.var VarKind.local (ofString "w"))) with ⟨rst, sst⟩
        have ho_st := store_only_none_or_error' mid_w
          (ExpHOL.var VarKind.local (ofString "p")) (ExpHOL.var VarKind.local (ofString "w"))
        rw [hst_ev] at ho_st
        rcases ho_st with ⟨hrst, _⟩ | hrst
        · dsimp only at hrst; subst hrst; dsimp only
          have hbst := R13Shards.Keccak256.byteEff_store_one (Rl := Rl) hG_mw
            (ExpHOL.var VarKind.local (ofString "p")) (ExpHOL.var VarKind.local (ofString "w"))
            (fun val hval => by simp [evalHOLExact, hw_mw] at hval; exact ⟨wv, hval.symm⟩)
            (fun x hx _ => by simp [evalHOLExact, hp_mw] at hx; subst hx; exact hin_ivl)
          rw [hst_ev] at hbst
          obtain ⟨heff_st, hdom_st⟩ := hbst
          obtain ⟨x_st, hx_st, hd_lo, hd_hi, _⟩ := hdom_st rfl
          simp [evalHOLExact, hp_mw] at hx_st; subst hx_st
          have hret_sst : evaluateHOLFiniteState sst (.return (.const 0)) =
              (some (.returned (.val (.word 0))), sst.emptyLocalsHOLFinite) := by
            rw [evaluateHOLFiniteState_return]
            have hc0 : @evalHOLExact 64 F _ sst.toExact (fun a => Classical.propDecidable (sst.memaddrs a)) (.const 0) =
                some (.val (.word 0)) := rfl
            rw [hc0]; dsimp only
            have hsz : sizeOfShapeWithContextHOL sst.structs (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) ≤ 32 := by
              simp [shapeOfHOLExact]
            rw [if_pos hsz]
          rw [hret_sst]; dsimp only
          have heff_mw0 : R13Shards.Keccak256.ByteEff ent mid_w Rl := by
            unfold M13.LocFrame at hlf_mid_w
            rw [hlf_mid_w]
            exact (R13Shards.Keccak256.ByteEff.refl ent Rl).locals_clock _ _
          refine ⟨fun rv hrv => ?_, fun r hr hne => ?_⟩
          · injection hrv with e1; injection e1 with e2
            exact ⟨e2.symm, hd_lo, hd_hi,
              ((heff_mw0.trans heff_st).locals_clock _ _).locals_clock _ _⟩
          · injection hr with e1; exact False.elim (hne _ e1.symm)
        · dsimp only at hrst; subst hrst; dsimp only
          exact ⟨fun _ h => by simp at h, fun r hr _ => by injection hr with e; subst e; exact not_resumes_error⟩
    · -- Unaligned path: two `st_be32` calls!
      simp only [hal, ↓reduceIte, evaluateHOLFiniteState_skip] at hnt ⊢
      rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
      -- First `st_be32(p, v >>> 32)`:
      rcases hc1 : evaluateHOLFiniteState ent
        (.call (some (none, none)) (ofString "st_be32")
          [ExpHOL.var VarKind.local (ofString "p"),
           .shift .lsr (ExpHOL.var VarKind.local (ofString "v")) (.const 32)]) with ⟨r1, m1⟩
      have hnt_c1 : r1 ≠ some .timeOut := by rintro rfl; rw [hc1] at hnt; exact hnt rfl
      -- Unpack `call st_be32`:
      have hc1_spec :
          (r1 = none →
            sourceBase ≤ p0.toNat ∧ p0.toNat + 4 ≤ heapEnd ∧
            R13Shards.Keccak256.ByteEff ent m1 Rl ∧ m1.locals = ent.locals) ∧
          (r1 ≠ none → ¬ Resumes r1) := by
        have hc1' := hc1
        rw [evaluateHOLFiniteState_call] at hc1'
        have ha1 : evalListHOLFinite ent (h := fun a => Classical.propDecidable (ent.memaddrs a))
            [ExpHOL.var VarKind.local (ofString "p"),
             .shift .lsr (ExpHOL.var VarKind.local (ofString "v")) (.const 32)] =
            some [.val (.word p0), .val (.word (v0 >>> 32))] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hent_p, hent_v, wordShiftHOL, valueIsWord, valueWord]
        have hlk1 := pan_two_word_lookup ent.code.lookup (ofString "st_be32")
          (ofString "p") (ofString "v")
          (sourceFnBody Guest.Software.guestFn_st_be32) p0 (v0 >>> 32) (by decide)
          (by change s.code.lookup _ = _; rw [hcode]; exact lookup_st_be32)
        simp only [ha1, hlk1] at hc1'
        by_cases hcz1 : ent.clock = 0
        · simp [hcz1] at hc1'; exact absurd hc1'.1.symm hnt_c1
        · simp only [hcz1, ↓reduceIte] at hc1'
          set cm1 := (HolFiniteMapExact.empty.update (ofString "p", ValueHOL.val (.word p0))).update
            (ofString "v", ValueHOL.val (.word (v0 >>> 32)))
          set e1 := callEntryStateHOLFinite ent cm1
          have he1_p : e1.locals.lookup (ofString "p") = some (.val (.word p0)) := by
            simp [e1, cm1, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "v" ≠ ofString "p" by decide]
          have he1_v : e1.locals.lookup (ofString "v") = some (.val (.word (v0 >>> 32))) := by
            simp [e1, cm1, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have h32_1 := eval_st_be32_body_eff e1 p0 (v0 >>> 32) (guestInv_callEntry ent cm1 hGe) he1_p he1_v
          rcases hb1 : evaluateHOLFiniteState e1 (sourceFnBody Guest.Software.guestFn_st_be32) with ⟨rb1, sb1⟩
          rw [hb1] at hc1' h32_1
          cases rb1 with
          | none => injection hc1' with hr _; subst hr; exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
          | some rb1' =>
            cases rb1' with
            | timeOut => injection hc1' with hr _; exact absurd hr.symm hnt_c1
            | exception eid ev =>
              injection hc1' with hr _; subst hr
              exact ⟨fun h => by simp at h, fun _ => h32_1.2 (.exception eid ev) rfl (fun _ h => by cases h)⟩
            | returned rv1 =>
              obtain ⟨rfl, hd_lo1, hd_hi1, heff_b1⟩ := h32_1.1 rv1 rfl
              have hsh0 : shapeEqHOL (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) .one = true := by
                simp [shapeOfHOLExact, shapeEqHOL]
              dsimp only at hc1'; rw [if_pos hsh0] at hc1'
              injection hc1' with hr hm1; subst hr hm1
              have heff_m1 : R13Shards.Keccak256.ByteEff ent { sb1 with locals := ent.locals } Rl :=
                (((R13Shards.Keccak256.ByteEff.refl ent _).locals_clock e1.locals e1.clock).trans heff_b1).locals_clock ent.locals sb1.clock
                |>.mono (fun i hi _ => by
                  simp at hi; subst hi
                  obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
                  exact ⟨ivl, hivl, h1, by omega⟩)
              exact ⟨fun _ => ⟨hd_lo1, hd_hi1, heff_m1, rfl⟩, fun h => False.elim (h rfl)⟩
            | «break» | «continue» | error =>
              injection hc1' with hr _; subst hr; exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
            | finalFfi _ =>
              injection hc1' with hr _; subst hr
              exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
      rw [hc1] at hnt
      cases r1 with
      | some r_1 =>
        dsimp only
        exact ⟨fun rv hrv => False.elim (hc1_spec.2 (by simp) (Or.inl ⟨rv, hrv⟩)),
          fun r hr _ => by injection hr with e; subst e; exact hc1_spec.2 (by simp)⟩
      | none =>
        dsimp only at hnt ⊢
        obtain ⟨hd_lo1, hd_hi1, heff_m1, hm1_loc⟩ := hc1_spec.1 rfl
        have hm1_p : m1.locals.lookup (ofString "p") = some (.val (.word p0)) := by rw [hm1_loc]; exact hent_p
        have hm1_v : m1.locals.lookup (ofString "v") = some (.val (.word v0)) := by rw [hm1_loc]; exact hent_v
        have hGm1 : GuestInv m1 := guestInv_congr heff_m1.code heff_m1.memaddrs heff_m1.shMemaddrs heff_m1.baseAddr hGe
        have hc_m1 : m1.code = originalRuntimeCode := heff_m1.code.trans hcode
        have hp4_nat : (p0 + 4).toNat = p0.toNat + 4 := by
          rw [BitVec.toNat_add]; change (p0.toNat + 4) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
        -- Second `st_be32(p + 4, v)`:
        rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
        rcases hc2 : evaluateHOLFiniteState m1
          (.call (some (none, none)) (ofString "st_be32")
            [.op .add [ExpHOL.var VarKind.local (ofString "p"), .const 4],
             ExpHOL.var VarKind.local (ofString "v")]) with ⟨r2, m2⟩
        have hnt_c2 : r2 ≠ some .timeOut := by rintro rfl; rw [hc2] at hnt; exact hnt rfl
        have hc2_spec :
            (r2 = none →
              p0.toNat + 8 ≤ heapEnd ∧
              R13Shards.Keccak256.ByteEff m1 m2 Rl) ∧
            (r2 ≠ none → ¬ Resumes r2) := by
          have hc2' := hc2
          rw [evaluateHOLFiniteState_call] at hc2'
          have ha2 : evalListHOLFinite m1 (h := fun a => Classical.propDecidable (m1.memaddrs a))
              [.op .add [ExpHOL.var VarKind.local (ofString "p"), .const 4],
               ExpHOL.var VarKind.local (ofString "v")] =
              some [.val (.word (p0 + 4)), .val (.word v0)] := by
            simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hm1_p, hm1_v, wordOpHOL, wordOp, valueIsWord, valueWord]
          have hlk2 := pan_two_word_lookup m1.code.lookup (ofString "st_be32")
            (ofString "p") (ofString "v")
            (sourceFnBody Guest.Software.guestFn_st_be32) (p0 + 4) v0 (by decide)
            (by rw [hc_m1]; exact lookup_st_be32)
          simp only [ha2, hlk2] at hc2'
          by_cases hcz2 : m1.clock = 0
          · simp [hcz2] at hc2'; exact absurd hc2'.1.symm hnt_c2
          · simp only [hcz2, ↓reduceIte] at hc2'
            set cm2 := (HolFiniteMapExact.empty.update (ofString "p", ValueHOL.val (.word (p0 + 4)))).update
              (ofString "v", ValueHOL.val (.word v0))
            set e2 := callEntryStateHOLFinite m1 cm2
            have he2_p : e2.locals.lookup (ofString "p") = some (.val (.word (p0 + 4))) := by
              simp [e2, cm2, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "v" ≠ ofString "p" by decide]
            have he2_v : e2.locals.lookup (ofString "v") = some (.val (.word v0)) := by
              simp [e2, cm2, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have h32_2 := eval_st_be32_body_eff e2 (p0 + 4) v0 (guestInv_callEntry m1 cm2 hGm1) he2_p he2_v
            rcases hb2 : evaluateHOLFiniteState e2 (sourceFnBody Guest.Software.guestFn_st_be32) with ⟨rb2, sb2⟩
            rw [hb2] at hc2' h32_2
            cases rb2 with
            | none => injection hc2' with hr _; subst hr; exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
            | some rb2' =>
              cases rb2' with
              | timeOut => injection hc2' with hr _; exact absurd hr.symm hnt_c2
              | exception eid ev =>
                injection hc2' with hr _; subst hr
                exact ⟨fun h => by simp at h, fun _ => h32_2.2 (.exception eid ev) rfl (fun _ h => by cases h)⟩
              | returned rv2 =>
                obtain ⟨rfl, _, hd_hi2, heff_b2⟩ := h32_2.1 rv2 rfl
                have hsh0 : shapeEqHOL (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) .one = true := by
                  simp [shapeOfHOLExact, shapeEqHOL]
                dsimp only at hc2'; rw [if_pos hsh0] at hc2'
                injection hc2' with hr hm2; subst hr hm2
                have heff_m2 : R13Shards.Keccak256.ByteEff m1 { sb2 with locals := m1.locals } Rl :=
                  (((R13Shards.Keccak256.ByteEff.refl m1 _).locals_clock e2.locals e2.clock).trans heff_b2).locals_clock m1.locals sb2.clock
                  |>.mono (fun i hi _ => by
                    simp [hp4_nat] at hi; subst hi
                    obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
                    exact ⟨ivl, hivl, by omega, by omega⟩)
                exact ⟨fun _ => ⟨by rw [hp4_nat] at hd_hi2; omega, heff_m2⟩, fun h => False.elim (h rfl)⟩
              | «break» | «continue» | error =>
                injection hc2' with hr _; subst hr; exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
              | finalFfi _ =>
                injection hc2' with hr _; subst hr
                exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
        cases r2 with
        | some r_2 =>
          dsimp only
          exact ⟨fun rv hrv => False.elim (hc2_spec.2 (by simp) (Or.inl ⟨rv, hrv⟩)),
            fun r hr _ => by injection hr with e; subst e; exact hc2_spec.2 (by simp)⟩
        | none =>
          dsimp only
          obtain ⟨hd_hi2, heff_m2⟩ := hc2_spec.1 rfl
          have hret_m2 : evaluateHOLFiniteState m2 (.return (.const 0)) =
              (some (.returned (.val (.word 0))), m2.emptyLocalsHOLFinite) := by
            rw [evaluateHOLFiniteState_return]
            have hc0 : @evalHOLExact 64 F _ m2.toExact (fun a => Classical.propDecidable (m2.memaddrs a)) (.const 0) =
                some (.val (.word 0)) := rfl
            rw [hc0]; dsimp only
            have hsz : sizeOfShapeWithContextHOL m2.structs (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) ≤ 32 := by
              simp [shapeOfHOLExact]
            rw [if_pos hsz]
          rw [hret_m2]
          refine ⟨fun rv hrv => ?_, fun r hr hne => ?_⟩
          · injection hrv with e1; injection e1 with e2
            exact ⟨e2.symm, hd_lo1, hd_hi2, (heff_m1.trans heff_m2).locals_clock _ _⟩
          · injection hr with e1; exact False.elim (hne _ e1.symm)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
