import InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28_Exec

/-! Concrete `FunByteEff` instances (`memzero`, `memcpy`, `st_*`, `addr_from_words`,
`keccak256`, `sha256_pair`) and all simple init contracts:
`wk_blake2_init`, `wk_bls_precompiles_init`, `wk_bn254_init`, `wk_evm_init`,
`wk_fork_init`, `wk_header_init`, `wk_keccak_init`, `wk_mpt_init`, `wk_ripemd160_init`,
`wk_sha256_init`, `wk_ssz_init`. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false

namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. Lookup helpers & `FunByteEff` instances -/

def valWordNat : ValueHOL 64 → Nat
  | .val (.word w) => w.toNat
  | _ => 0

def globMapN (G : HolFiniteMapExact MlS (ValueHOL 64)) (name : String) : Nat :=
  match G.lookup (ofString name) with
  | some (.val (.word w)) => w.toNat
  | _ => 0

def globBufIvl (G : HolFiniteMapExact MlS (ValueHOL 64)) (name : String) (sz : Nat) : Ivl :=
  (globMapN G name, if globMapN G name = 0 then 0 else sz)

theorem globBufIvl_eq_bufferRegion {F : Type} (s : PanSemStateFiniteExact 64 F) (name : String) (sz : Nat) :
    globBufIvl s.globals name sz = bufferRegion s (name, sz) := rfl

theorem lookupCode_one_word {fname p1 : MlS} {body : ProgHOL 64} {vals : List (ValueHOL 64)}
    {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one)], body, .one))
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, L, .one)) :
    ∃ w1 : BitVec 64,
      vals = [.val (.word w1)] ∧
      L.lookup p1 = some (.val (.word w1)) := by
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup fname vals body L .one hl
  simp only [lookupCodeHOLExact, hlook] at hx
  rcases vals with _ | ⟨v1, _ | _⟩
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hx
    exact ⟨w1, rfl, by rw [← hx]; simp⟩
  · simp at hx

theorem lookupCode_two_words {fname p1 p2 : MlS} {body : ProgHOL 64} {vals : List (ValueHOL 64)}
    {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (hne : p1 ≠ p2)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one)], body, .one))
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, L, .one)) :
    ∃ w1 w2 : BitVec 64,
      vals = [.val (.word w1), .val (.word w2)] ∧
      L.lookup p1 = some (.val (.word w1)) ∧
      L.lookup p2 = some (.val (.word w2)) := by
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup fname vals body L .one hl
  simp only [lookupCodeHOLExact, hlook] at hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩
  · simp at hx
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL] at hx
    obtain ⟨_, hL⟩ := hx
    refine ⟨w1, w2, rfl, ?_, ?_⟩ <;> (rw [← hL]; simp [hne, Ne.symm hne])
  · simp at hx

theorem lookupCode_three_words {fname p1 p2 p3 : MlS} {body : ProgHOL 64} {vals : List (ValueHOL 64)}
    {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one), (p3, .one)], body, .one))
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, L, .one)) :
    ∃ w1 w2 w3 : BitVec 64,
      vals = [.val (.word w1), .val (.word w2), .val (.word w3)] ∧
      L.lookup p1 = some (.val (.word w1)) ∧
      L.lookup p2 = some (.val (.word w2)) ∧
      L.lookup p3 = some (.val (.word w3)) := by
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup fname vals body L .one hl
  simp only [lookupCodeHOLExact, hlook] at hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩
  · simp at hx
  · simp at hx
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;>
      rcases v3 with ⟨⟨w3⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hx
    obtain ⟨_, hL⟩ := hx
    refine ⟨w1, w2, w3, rfl, ?_, ?_, ?_⟩ <;>
      (rw [← hL]; simp [h12, h13, h23, Ne.symm h12, Ne.symm h13, Ne.symm h23])
  · simp at hx

theorem lookupCode_four_words {fname p1 p2 p3 p4 : MlS} {body : ProgHOL 64} {vals : List (ValueHOL 64)}
    {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (hlook : originalRuntimeCode.lookup fname =
      some ([(p1, .one), (p2, .one), (p3, .one), (p4, .one)], body, .one))
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, L, .one)) :
    ∃ w1 w2 w3 w4 : BitVec 64,
      vals = [.val (.word w1), .val (.word w2), .val (.word w3), .val (.word w4)] ∧
      L.lookup p1 = some (.val (.word w1)) ∧
      L.lookup p2 = some (.val (.word w2)) ∧
      L.lookup p3 = some (.val (.word w3)) ∧
      L.lookup p4 = some (.val (.word w4)) := by
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup fname vals body L .one hl
  simp only [lookupCodeHOLExact, hlook] at hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, _ | _⟩⟩⟩⟩
  · simp at hx
  · simp at hx
  · simp at hx
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;>
      rcases v3 with ⟨⟨w3⟩⟩ | _ | _ <;> rcases v4 with ⟨⟨w4⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL] at hx
    obtain ⟨_, hL⟩ := hx
    refine ⟨w1, w2, w3, w4, rfl, ?_, ?_, ?_, ?_⟩ <;>
      (rw [← hL]; simp [h12, h13, h14, h23, h24, h34,
        Ne.symm h12, Ne.symm h13, Ne.symm h14, Ne.symm h23, Ne.symm h24, Ne.symm h24, Ne.symm h34])
  · simp at hx

theorem funByteEff_memzero :
    FunByteEff (ofString "memzero")
      (fun vals _ => [(valWordNat (vals[0]?.getD (.rStruct [])), valWordNat (vals[1]?.getD (.rStruct [])))]) := by
  refine ⟨_, _, _, lookup_memzero, fun entry vals hc hG hl _ hres => ?_⟩
  obtain ⟨dst0, n0, rfl, hdst, hn⟩ := lookupCode_two_words (by decide) lookup_memzero hl
  exact (memzero_body_eff entry dst0 n0 hc hG hdst hn hres).1

theorem funByteEff_memcpy :
    FunByteEff (ofString "memcpy")
      (fun vals _ => [(valWordNat (vals[0]?.getD (.rStruct [])), valWordNat (vals[2]?.getD (.rStruct [])))]) := by
  have hlook : originalRuntimeCode.lookup (ofString "memcpy") =
      some ([(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memcpy, .one) :=
    lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_memcpy) rfl
  refine ⟨_, _, _, hlook, fun entry vals hc hG hl _ hres => ?_⟩
  obtain ⟨dst0, _, n0, rfl, hdst, _, hn⟩ := lookupCode_three_words (by decide) (by decide) (by decide) hlook hl
  exact (memcpy_body_eff entry dst0 n0 hc hG hdst hn hres).1

theorem four_byte_stores_eff {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (p : BitVec 64)
    (v0 v1 v2 v3 : ExpHOL 64)
    (hG : GuestInv s0)
    (hp : s0.locals.lookup (ofString "p") = some (.val (.word p)))
    (hres : Resumes (evaluateHOLFiniteState s0
      (.seq (.storeByte (.var .local (ofString "p")) v0)
        (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 1]) v1)
          (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 2]) v2)
            (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 3]) v3)
              (.return (.const 0))))))).1) :
    ByteEff s0 (evaluateHOLFiniteState s0
      (.seq (.storeByte (.var .local (ofString "p")) v0)
        (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 1]) v1)
          (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 2]) v2)
            (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 3]) v3)
              (.return (.const 0))))))).2 [(p.toNat, 4)] ∧
    sourceBase ≤ p.toNat ∧ p.toNat + 4 ≤ heapEnd := by
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  have seq_res : ∀ (t : PanSemStateFiniteExact 64 F) (a b : ProgHOL 64),
      (∀ x : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState x a).1 = none ∨ (evaluateHOLFiniteState x a).1 = some .error) →
      (evaluateHOLFiniteState t a).2.locals = t.locals →
      Resumes (evaluateHOLFiniteState t (.seq a b)).1 →
      (evaluateHOLFiniteState t a).1 = none ∧
      Resumes (evaluateHOLFiniteState (evaluateHOLFiniteState t a).2 b).1 ∧
      (evaluateHOLFiniteState t (.seq a b)).2 =
        (evaluateHOLFiniteState (evaluateHOLFiniteState t a).2 b).2 ∧
      (evaluateHOLFiniteState t a).2.locals = t.locals := by
    intro t a b ha hloc hr
    rw [evaluateHOLFiniteState_seq_line780] at hr ⊢
    rcases he : evaluateHOLFiniteState t a with ⟨r1, m⟩
    have ha_t := ha t
    rw [he] at hr hloc ha_t
    rcases ha_t with rfl | rfl
    · exact ⟨rfl, hr, rfl, hloc⟩
    · exact False.elim (not_resumes_error hr)
  obtain ⟨hs0, hr1, heq1, hl1⟩ := seq_res s0 _ _
    (fun x => (evaluate_storeByte_control_frame x _ _).1)
    (evaluate_storeByte_control_frame s0 _ _).2.2.1 hres
  let s1 := (evaluateHOLFiniteState s0 (.storeByte (.var .local (ofString "p")) v0)).2
  have hG1 : GuestInv s1 := guestInv_evaluate s0 _ hG
  obtain ⟨hs1, hr2, heq2, hl2⟩ := seq_res s1 _ _
    (fun x => (evaluate_storeByte_control_frame x _ _).1)
    (evaluate_storeByte_control_frame s1 _ _).2.2.1 hr1
  let s2 := (evaluateHOLFiniteState s1 (.storeByte (.op .add [.var .local (ofString "p"), .const 1]) v1)).2
  have hG2 : GuestInv s2 := guestInv_evaluate s1 _ hG1
  obtain ⟨hs2, hr3, heq3, hl3⟩ := seq_res s2 _ _
    (fun x => (evaluate_storeByte_control_frame x _ _).1)
    (evaluate_storeByte_control_frame s2 _ _).2.2.1 hr2
  let s3 := (evaluateHOLFiniteState s2 (.storeByte (.op .add [.var .local (ofString "p"), .const 2]) v2)).2
  have hG3 : GuestInv s3 := guestInv_evaluate s2 _ hG2
  obtain ⟨hs3, _, heq4, _⟩ := seq_res s3 _ _
    (fun x => (evaluate_storeByte_control_frame x _ _).1)
    (evaluate_storeByte_control_frame s3 _ _).2.2.1 hr3
  let s4 := (evaluateHOLFiniteState s3 (.storeByte (.op .add [.var .local (ofString "p"), .const 3]) v3)).2
  have hp1 : s1.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hl1]; exact hp
  have hp2 : s2.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hl2]; exact hp1
  have hp3 : s3.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hl3]; exact hp2
  have ex0 : @evalHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a))
      (.var .local (ofString "p")) = some (.val (.word p)) := hp
  have ex1 : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
      (.op .add [.var .local (ofString "p"), .const 1]) = some (.val (.word (p + 1))) := by
    simp [evalHOLExact, evalListHOLExact, hp1, valueIsWord, valueWord, wordOpHOL, wordOp]
  have ex2 : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
      (.op .add [.var .local (ofString "p"), .const 2]) = some (.val (.word (p + 2))) := by
    simp [evalHOLExact, evalListHOLExact, hp2, valueIsWord, valueWord, wordOpHOL, wordOp]
  have ex3 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
      (.op .add [.var .local (ofString "p"), .const 3]) = some (.val (.word (p + 3))) := by
    simp [evalHOLExact, evalListHOLExact, hp3, valueIsWord, valueWord, wordOpHOL, wordOp]
  obtain ⟨x0, hx0, hd0_lo, _⟩ := storeByte_domain hG _ v0 hs0
  obtain ⟨x1, hx1, _, hd1_hi⟩ := storeByte_domain hG1 _ v1 hs1
  obtain ⟨x2, hx2, _, hd2_hi⟩ := storeByte_domain hG2 _ v2 hs2
  obtain ⟨x3, hx3, _, hd3_hi⟩ := storeByte_domain hG3 _ v3 hs3
  rw [ex0] at hx0; injection hx0 with hx0; injection hx0 with hx0; injection hx0 with hx0; subst hx0
  rw [ex1] at hx1; injection hx1 with hx1; injection hx1 with hx1; injection hx1 with hx1; subst hx1
  rw [ex2] at hx2; injection hx2 with hx2; injection hx2 with hx2; injection hx2 with hx2; subst hx2
  rw [ex3] at hx3; injection hx3 with hx3; injection hx3 with hx3; injection hx3 with hx3; subst hx3
  have a1 : (p + 1).toNat = p.toNat + 1 := BitVec.toNat_add_of_lt (by change p.toNat + 1 < 2 ^ 64; omega)
  have a2 : (p + 2).toNat = p.toNat + 2 := by rw [a1] at hd1_hi; exact BitVec.toNat_add_of_lt (by change p.toNat + 2 < 2 ^ 64; omega)
  have a3 : (p + 3).toNat = p.toNat + 3 := by rw [a2] at hd2_hi; exact BitVec.toNat_add_of_lt (by change p.toNat + 3 < 2 ^ 64; omega)
  have hp4_hi : p.toNat + 4 ≤ heapEnd := by rw [a3] at hd3_hi; omega
  have hin4 : 0 < 4 → ∃ i ∈ [(p.toNat, 4)], i.1 ≤ p.toNat ∧ p.toNat + 4 ≤ i.1 + i.2 :=
    fun _ => ⟨(p.toNat, 4), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩
  have eff0 := byteEff_storeByte_at hG _ v0 p 0 4 hp4_hi hin4 (by omega) (by simpa [BitVec.add_zero] using ex0)
  have eff1 := byteEff_storeByte_at hG1 _ v1 p 1 4 hp4_hi hin4 (by omega) ex1
  have eff2 := byteEff_storeByte_at hG2 _ v2 p 2 4 hp4_hi hin4 (by omega) ex2
  have eff3 := byteEff_storeByte_at hG3 _ v3 p 3 4 hp4_hi hin4 (by omega) ex3
  have eff4 : ByteEff s4 (evaluateHOLFiniteState s4 (.return (.const 0))).2 [(p.toNat, 4)] :=
    byteEff_return s4 _ _
  refine ⟨?_, hd0_lo, hp4_hi⟩
  rw [heq1, heq2, heq3, heq4]
  exact eff0.trans (eff1.trans (eff2.trans (eff3.trans eff4)))

theorem st_le32_body_eff {F : Type} (s0 : PanSemStateFiniteExact 64 F) (p : BitVec 64)
    (hG : GuestInv s0) (hp : s0.locals.lookup (ofString "p") = some (.val (.word p)))
    (hres : Resumes (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_st_le32)).1) :
    ByteEff s0 (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_st_le32)).2 [(p.toNat, 4)] ∧
    sourceBase ≤ p.toNat ∧ p.toNat + 4 ≤ heapEnd :=
  four_byte_stores_eff s0 p _ _ _ _ hG hp hres

theorem st_be32_body_eff {F : Type} (s0 : PanSemStateFiniteExact 64 F) (p : BitVec 64)
    (hG : GuestInv s0) (hp : s0.locals.lookup (ofString "p") = some (.val (.word p)))
    (hres : Resumes (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_st_be32)).1) :
    ByteEff s0 (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_st_be32)).2 [(p.toNat, 4)] ∧
    sourceBase ≤ p.toNat ∧ p.toNat + 4 ≤ heapEnd :=
  four_byte_stores_eff s0 p _ _ _ _ hG hp hres

theorem funByteEff_st_be32 :
    FunByteEff (ofString "st_be32")
      (fun vals _ => [(valWordNat (vals[0]?.getD (.rStruct [])), 4)]) := by
  have hlook : originalRuntimeCode.lookup (ofString "st_be32") =
      some ([(ofString "p", .one), (ofString "v", .one)],
        sourceFnBody Guest.Software.guestFn_st_be32, .one) :=
    lookup_of_guestAst_getElem 27 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_st_be32) rfl
  refine ⟨_, _, _, hlook, fun entry vals _ hG hl _ hres => ?_⟩
  obtain ⟨p, _, rfl, hp, _⟩ := lookupCode_two_words (by decide) hlook hl
  exact (st_be32_body_eff entry p hG hp hres).1

/-- Extract return postcondition + caller locals preservation for a successful `call (some (none, none))`! -/
theorem call0_two_word_success {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname p1 p2 : MlS) (body : ProgHOL 64) (a1 a2 : ExpHOL 64) (w1 w2 : BitVec 64)
    (hne : p1 ≠ p2)
    (hc : s.code = originalRuntimeCode)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one)], body, .one))
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [a1, a2] =
      some [.val (.word w1), .val (.word w2)])
    (hnone : (evaluateHOLFiniteState s (.call (some (none, none)) fname [a1, a2])).1 = none) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fname [a1, a2])).2.locals = s.locals ∧
    ∃ rv, (evaluateHOLFiniteState
      (callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2))))
      body).1 = some (.returned rv) := by
  rw [evaluateHOLFiniteState_call, ha] at hnone ⊢
  dsimp only at hnone ⊢
  have hl := pan_two_word_lookup s.code.lookup fname p1 p2 body w1 w2 hne (by rw [hc]; exact hlook)
  rw [hl] at hnone ⊢; dsimp only at hnone ⊢
  split at hnone
  · simp at hnone
  · rename_i hclk
    rw [if_neg hclk]
    rcases hb : evaluateHOLFiniteState
      (callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2))))
      body with ⟨rb, pb⟩
    rw [hb] at hnone ⊢
    cases rb with
    | none => simp at hnone
    | some rb' =>
      cases rb' with
      | returned rv =>
        dsimp only at hnone ⊢
        split at hnone
        · rename_i hsh; rw [if_pos hsh]; exact ⟨rfl, rv, rfl⟩
        · simp at hnone
      | _ => simp at hnone

theorem funByteEff_st_le64 :
    FunByteEff (ofString "st_le64")
      (fun vals _ => [(valWordNat (vals[0]?.getD (.rStruct [])), 8)]) := by
  have hlook32 : originalRuntimeCode.lookup (ofString "st_le32") =
      some ([(ofString "p", .one), (ofString "v", .one)],
        sourceFnBody Guest.Software.guestFn_st_le32, .one) :=
    lookup_of_guestAst_getElem 25 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_st_le32) rfl
  have hlook64 : originalRuntimeCode.lookup (ofString "st_le64") =
      some ([(ofString "p", .one), (ofString "v", .one)],
        sourceFnBody Guest.Software.guestFn_st_le64, .one) :=
    lookup_of_guestAst_getElem 26 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_st_le64) rfl
  have hf32 : FunByteEff (ofString "st_le32")
      (fun vals _ => [(valWordNat (vals[0]?.getD (.rStruct [])), 4)]) := by
    refine ⟨_, _, _, hlook32, fun entry vals _ hG hl _ hres => ?_⟩
    obtain ⟨p, _, rfl, hp, _⟩ := lookupCode_two_words (by decide) hlook32 hl
    exact (st_le32_body_eff entry p hG hp hres).1
  refine ⟨_, _, _, hlook64, fun entry vals hc hG hl hnt hres => ?_⟩
  obtain ⟨p, v, rfl, hp, hv⟩ := lookupCode_two_words (by decide) hlook64 hl
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  have hbody : sourceFnBody Guest.Software.guestFn_st_le64 =
      .seq (.call (some (none, none)) (ofString "st_le32") [.var .local (ofString "p"), .var .local (ofString "v")])
        (.seq (.call (some (none, none)) (ofString "st_le32")
            [.op .add [.var .local (ofString "p"), .const 4], .shift .lsr (.var .local (ofString "v")) (.const 32)])
          (.return (.const 0))) := rfl
  rw [hbody] at hnt hres ⊢
  rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
  rcases hc1 : evaluateHOLFiniteState entry
      (.call (some (none, none)) (ofString "st_le32") [.var .local (ofString "p"), .var .local (ofString "v")]) with ⟨r1, s1⟩
  rw [hc1] at hnt hres
  have hnt1 : r1 ≠ some .timeOut := by intro h; subst h; simp at hnt
  have hargs1 : evalListHOLFinite entry (h := fun a => Classical.propDecidable (entry.memaddrs a))
      [.var .local (ofString "p"), .var .local (ofString "v")] = some [.val (.word p), .val (.word v)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp, hv]
  have heff1 : ByteEff entry s1 [(p.toNat, 8)] := by
    have := call0_byteEff hf32 entry _ [(p.toNat, 8)] hc hG
      (fun vs hvs i hi _ => by
        rw [hargs1] at hvs; injection hvs with hvs; subst hvs
        simp [valWordNat] at hi; subst hi; exact ⟨(p.toNat, 8), List.mem_singleton.2 rfl, le_rfl, by omega⟩)
      (by rw [hc1]; exact hnt1)
      (by rw [hc1]; cases r1 with | none => exact Or.inl rfl | some _ => exact Or.inr hres)
    rwa [hc1] at this
  cases r1 with
  | some _ => exact heff1
  | none =>
    obtain ⟨hs1_loc, rv1, hrv1⟩ := call0_two_word_success entry _ _ _ _ _ _ p v (by decide) hc hlook32 hargs1 (by rw [hc1])
    rw [hc1] at hs1_loc
    have hp_hi4 : p.toNat + 4 ≤ heapEnd :=
      (st_le32_body_eff _ p (guestInv_callEntry entry _ hG)
        (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "v" ≠ ofString "p" by decide])
        (Or.inl ⟨rv1, hrv1⟩)).2.2
    dsimp only at hnt hres ⊢
    rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
    rcases hc2 : evaluateHOLFiniteState s1
        (.call (some (none, none)) (ofString "st_le32")
          [.op .add [.var .local (ofString "p"), .const 4], .shift .lsr (.var .local (ofString "v")) (.const 32)]) with ⟨r2, s2⟩
    rw [hc2] at hnt hres
    have hnt2 : r2 ≠ some .timeOut := by intro h; subst h; simp at hnt
    have hGs1 : GuestInv s1 := guestInv_congr heff1.code heff1.memaddrs heff1.shMemaddrs heff1.baseAddr hG
    have hc_s1 : s1.code = originalRuntimeCode := heff1.code.trans hc
    have hp_s1 : s1.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hs1_loc]; exact hp
    have hv_s1 : s1.locals.lookup (ofString "v") = some (.val (.word v)) := by rw [hs1_loc]; exact hv
    have hp4_add : (p + 4).toNat = p.toNat + 4 := BitVec.toNat_add_of_lt (by change p.toNat + 4 < 2 ^ 64; omega)
    have hargs2 : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
        [.op .add [.var .local (ofString "p"), .const 4], .shift .lsr (.var .local (ofString "v")) (.const 32)] =
        some [.val (.word (p + 4)), .val (.word (v >>> 32))] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp_s1, hv_s1,
        valueIsWord, valueWord, wordOpHOL, wordOp, wordShiftHOL]
    have heff2 : ByteEff s1 s2 [(p.toNat, 8)] := by
      have := call0_byteEff hf32 s1 _ [(p.toNat, 8)] hc_s1 hGs1
        (fun vs hvs i hi _ => by
          rw [hargs2] at hvs; injection hvs with hvs; subst hvs
          simp [valWordNat, hp4_add] at hi; subst hi
          exact ⟨(p.toNat, 8), List.mem_singleton.2 rfl, by omega, by omega⟩)
        (by rw [hc2]; exact hnt2)
        (by rw [hc2]; cases r2 with | none => exact Or.inl rfl | some _ => exact Or.inr hres)
      rwa [hc2] at this
    cases r2 with
    | some _ => exact heff1.trans heff2
    | none => exact (heff1.trans heff2).trans (byteEff_return s2 _ _)

theorem bswap64_locFrame {F : Type} (s : PanSemStateFiniteExact 64 F) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_bswap64)
    out.2 = { s with locals := out.2.locals, clock := out.2.clock } := by
  dsimp only
  have hbody : sourceFnBody Guest.Software.guestFn_bswap64 =
      .seq (.assign .local (ofString "x")
          (.op .or [.shift .lsl (.op .and [.var .local (ofString "x"), .const 71777214294589695]) (.const 8),
            .op .and [.shift .lsr (.var .local (ofString "x")) (.const 8), .const 71777214294589695]]))
        (.seq (.assign .local (ofString "x")
            (.op .or [.shift .lsl (.op .and [.var .local (ofString "x"), .const 281470681808895]) (.const 16),
              .op .and [.shift .lsr (.var .local (ofString "x")) (.const 16), .const 281470681808895]]))
          (.return (.op .or [.shift .lsl (.var .local (ofString "x")) (.const 32),
            .shift .lsr (.var .local (ofString "x")) (.const 32)]))) := rfl
  rw [hbody, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
  split
  · cases s; rfl
  · split
    · dsimp only [setKvarHOLFinite, setVarHOLFinite]
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
      split
      · rfl
      · split
        · dsimp only [setKvarHOLFinite, setVarHOLFinite]
          rw [evaluateHOLFiniteState_return]
          split
          · rfl
          · split <;> rfl
        · rfl
    · cases s; rfl

theorem funByteEff_st_be64 :
    FunByteEff (ofString "st_be64")
      (fun vals _ => [(valWordNat (vals[0]?.getD (.rStruct [])), 8)]) := by
  have hlook_bs : originalRuntimeCode.lookup (ofString "bswap64") =
      some ([(ofString "x", .one)], sourceFnBody Guest.Software.guestFn_bswap64, .one) :=
    lookup_of_guestAst_getElem 23 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_bswap64) rfl
  have hlook32 : originalRuntimeCode.lookup (ofString "st_be32") =
      some ([(ofString "p", .one), (ofString "v", .one)],
        sourceFnBody Guest.Software.guestFn_st_be32, .one) :=
    lookup_of_guestAst_getElem 27 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_st_be32) rfl
  have hlook64 : originalRuntimeCode.lookup (ofString "st_be64") =
      some ([(ofString "p", .one), (ofString "v", .one)],
        sourceFnBody Guest.Software.guestFn_st_be64, .one) :=
    lookup_of_guestAst_getElem 28 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_st_be64) rfl
  refine ⟨_, _, _, hlook64, fun entry vals hc hG hl hnt hres => ?_⟩
  obtain ⟨p, v, rfl, hp, hv⟩ := lookupCode_two_words (by decide) hlook64 hl
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  have hbody : sourceFnBody Guest.Software.guestFn_st_be64 =
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
  rw [hbody] at hnt hres ⊢
  rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
  dsimp only [valWordNat]
  rcases h1 : evaluateHOLFiniteState entry
      (.ite (.cmp .equal (.op .and [.var .local (ofString "p"), .const 7]) (.const 0))
        (.decCall (ofString "w") .one (ofString "bswap64") [.var .local (ofString "v")]
          (.seq (.store (.var .local (ofString "p")) (.var .local (ofString "w")))
            (.return (.const 0))))
        .skip) with ⟨r1, s1⟩
  rw [h1] at hnt hres
  -- Analyze `ite`: if true branch taken, `decCall` either returns `(0)` or errors/times out (never `none`!).
  -- If false branch taken, `.skip` returns `(none, entry)`!
  have hite_branch : (r1 = none ∧ s1 = entry) ∨ (r1 ≠ none ∧ ByteEff entry s1 [(p.toNat, 8)]) := by
    rw [evaluateHOLFiniteState_ite] at h1
    split at h1
    · split at h1
      · rw [evaluateHOLFiniteState_skip] at h1; injection h1 with hr1 hs1; exact Or.inl ⟨hr1.symm, hs1.symm⟩
      · right
        rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at h1
        have hargs_bs : evalListHOLFinite entry (h := fun a => Classical.propDecidable (entry.memaddrs a))
            [.var .local (ofString "v")] = some [.val (.word v)] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hv]
        rw [hargs_bs] at h1; dsimp only at h1
        have hl_bs := pan_one_word_lookup entry.code.lookup (ofString "bswap64") (ofString "x")
          (sourceFnBody Guest.Software.guestFn_bswap64) v (by rw [hc]; exact hlook_bs)
        rw [hl_bs] at h1; dsimp only at h1
        split at h1
        · injection h1 with hr1 hs1; subst hr1 hs1; exact ⟨by simp, (ByteEff.refl entry _).locals_clock _ _⟩
        · have hbs := bswap64_locFrame (callEntryStateHOLFinite entry (HolFiniteMapExact.empty.update (ofString "x", .val (.word v))))
          rcases hrun_bs : evaluateHOLFiniteState (callEntryStateHOLFinite entry (HolFiniteMapExact.empty.update (ofString "x", .val (.word v))))
            (sourceFnBody Guest.Software.guestFn_bswap64) with ⟨rbs, pbs⟩
          rw [hrun_bs] at h1 hbs; dsimp only at hbs
          have heff_pbs : ByteEff entry pbs [(p.toNat, 8)] := by
            rw [hbs]; exact (ByteEff.refl entry _).locals_clock _ _
          cases rbs with
          | none => injection h1 with hr1 hs1; subst hr1 hs1; exact ⟨by simp, heff_pbs.locals_clock _ _⟩
          | some rbs' =>
            cases rbs' with
            | returned rv =>
              dsimp only at h1; split at h1
              · rename_i hsh_rv
                rcases rv with ⟨⟨wv⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hsh_rv)
                let st_w := setVarHOLFinite (ofString "w") (.val (.word wv)) { pbs with locals := entry.locals }
                have hGw : GuestInv st_w := guestInv_setVar _ _ _
                  (guestInv_congr heff_pbs.code heff_pbs.memaddrs heff_pbs.shMemaddrs heff_pbs.baseAddr hG)
                have hp_w : st_w.locals.lookup (ofString "p") = some (.val (.word p)) := by
                  simp [st_w, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp, show ofString "w" ≠ ofString "p" by decide]
                have hw_w : st_w.locals.lookup (ofString "w") = some (.val (.word wv)) := by
                  simp [st_w, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                rw [evaluateHOLFiniteState_seq_line780] at h1
                have heff_st := (byteEff_store_one (Rl := [(p.toNat, 8)]) hGw
                  (.var .local (ofString "p")) (.var .local (ofString "w"))
                  (fun val hval => by simp [evalHOLExact, hw_w] at hval; exact ⟨wv, hval.symm⟩)
                  (fun x hx _ => by
                    simp [evalHOLExact, hp_w] at hx; subst hx
                    exact ⟨(p.toNat, 8), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)).1
                rcases hst_ev : evaluateHOLFiniteState st_w (.store (.var .local (ofString "p")) (.var .local (ofString "w"))) with ⟨rst, mst⟩
                rw [hst_ev] at h1 heff_st
                cases rst with
                | some rst' =>
                  injection h1 with hr1 hs1; subst hr1 hs1
                  exact ⟨by simp, ((heff_pbs.locals_clock _ _).trans heff_st).locals_clock _ _⟩
                | none =>
                  dsimp only at h1
                  have heff_ret := byteEff_return mst (.const 0) [(p.toNat, 8)]
                  have hret_nz : (evaluateHOLFiniteState mst (.return (.const 0))).1 ≠ none := by
                    rw [evaluateHOLFiniteState_return]; dsimp only [evalHOLExact, shapeOfHOLExact]; split <;> simp
                  rcases hret_ev : evaluateHOLFiniteState mst (.return (.const 0)) with ⟨rret, mret⟩
                  rw [hret_ev] at h1 heff_ret hret_nz
                  injection h1 with hr1 hs1; subst hr1 hs1
                  exact ⟨hret_nz, (((heff_pbs.locals_clock _ _).trans heff_st).trans heff_ret).locals_clock _ _⟩
              · injection h1 with hr1 hs1; subst hr1 hs1; exact ⟨by simp, heff_pbs.locals_clock _ _⟩
            | timeOut | error | «break» | «continue» | exception _ _ | finalFfi _ =>
              dsimp only at h1
              injection h1 with hr1 hs1; subst hr1 hs1; exact ⟨by simp, heff_pbs.locals_clock _ _⟩
    · injection h1 with hr1 hs1; subst hr1 hs1; exact Or.inr ⟨by simp, ByteEff.refl entry _⟩
  rcases hite_branch with ⟨rfl, hs1_eq⟩ | ⟨hr1_ne, heff1⟩
  · subst hs1_eq
    -- False branch: two `st_be32` calls!
    dsimp only at hnt hres ⊢
    rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
    rcases hc1 : evaluateHOLFiniteState s1
        (.call (some (none, none)) (ofString "st_be32")
          [.var .local (ofString "p"), .shift .lsr (.var .local (ofString "v")) (.const 32)]) with ⟨rc1_r, m1⟩
    rw [hc1] at hnt hres
    have hnt1 : rc1_r ≠ some .timeOut := by intro h; subst h; simp at hnt
    have hargs1 : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
        [.var .local (ofString "p"), .shift .lsr (.var .local (ofString "v")) (.const 32)] =
        some [.val (.word p), .val (.word (v >>> 32))] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp, hv, valueIsWord, valueWord, wordShiftHOL]
    have heff_c1 : ByteEff s1 m1 [(p.toNat, 8)] := by
      have := call0_byteEff funByteEff_st_be32 s1 _ [(p.toNat, 8)] hc hG
        (fun vs hvs i hi _ => by
          rw [hargs1] at hvs; injection hvs with hvs; subst hvs
          simp [valWordNat] at hi; subst hi; exact ⟨(p.toNat, 8), List.mem_singleton.2 rfl, le_rfl, by omega⟩)
        (by rw [hc1]; exact hnt1)
        (by rw [hc1]; cases rc1_r with | none => exact Or.inl rfl | some _ => exact Or.inr hres)
      rwa [hc1] at this
    cases rc1_r with
    | some _ => exact heff_c1
    | none =>
      obtain ⟨hm1_loc, rv1, hrv1⟩ := call0_two_word_success s1 _ _ _ _ _ _ p (v >>> 32) (by decide) hc hlook32 hargs1 (by rw [hc1])
      rw [hc1] at hm1_loc
      have hp_hi4 : p.toNat + 4 ≤ heapEnd :=
        (st_be32_body_eff _ p (guestInv_callEntry s1 _ hG)
          (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "v" ≠ ofString "p" by decide])
          (Or.inl ⟨rv1, hrv1⟩)).2.2
      dsimp only at hnt hres ⊢
      rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
      rcases hc2 : evaluateHOLFiniteState m1
          (.call (some (none, none)) (ofString "st_be32")
            [.op .add [.var .local (ofString "p"), .const 4], .var .local (ofString "v")]) with ⟨rc2_r, m2⟩
      rw [hc2] at hnt hres
      have hnt2 : rc2_r ≠ some .timeOut := by intro h; subst h; simp at hnt
      have hGm1 : GuestInv m1 := guestInv_congr heff_c1.code heff_c1.memaddrs heff_c1.shMemaddrs heff_c1.baseAddr hG
      have hc_m1 : m1.code = originalRuntimeCode := heff_c1.code.trans hc
      have hp_m1 : m1.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hm1_loc]; exact hp
      have hv_m1 : m1.locals.lookup (ofString "v") = some (.val (.word v)) := by rw [hm1_loc]; exact hv
      have hp4_add : (p + 4).toNat = p.toNat + 4 := BitVec.toNat_add_of_lt (by change p.toNat + 4 < 2 ^ 64; omega)
      have hargs2 : evalListHOLFinite m1 (h := fun a => Classical.propDecidable (m1.memaddrs a))
          [.op .add [.var .local (ofString "p"), .const 4], .var .local (ofString "v")] =
          some [.val (.word (p + 4)), .val (.word v)] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp_m1, hv_m1, valueIsWord, valueWord, wordOpHOL, wordOp]
      have heff_c2 : ByteEff m1 m2 [(p.toNat, 8)] := by
        have := call0_byteEff funByteEff_st_be32 m1 _ [(p.toNat, 8)] hc_m1 hGm1
          (fun vs hvs i hi _ => by
            rw [hargs2] at hvs; injection hvs with hvs; subst hvs
            simp [valWordNat, hp4_add] at hi; subst hi
            exact ⟨(p.toNat, 8), List.mem_singleton.2 rfl, by omega, by omega⟩)
          (by rw [hc2]; exact hnt2)
          (by rw [hc2]; cases rc2_r with | none => exact Or.inl rfl | some _ => exact Or.inr hres)
        rwa [hc2] at this
      cases rc2_r with
      | some _ => exact heff_c1.trans heff_c2
      | none => exact (heff_c1.trans heff_c2).trans (byteEff_return m2 _ _)
  · cases r1 with
    | none => exact absurd rfl hr1_ne
    | some _ => exact heff1

/-! ## 2. Declarative checker `checkConstStores` & `checkByteStoresAt` -/

/-- Check that `prog` writes only to `[base, base + sz)` via `.storeByte` at `ptrVar + off`
(`off < sz` and `sz ≤ sourceBase`, so `base + off` cannot wrap when in `ordinaryDomain`!)
and never assigns/declares `ptrVar` or modifies globals. Covers `sha256_pair` (512 steps) in 1 `rfl`! -/
def checkByteStoresLocal (ptrVar : MlS) (sz : Nat) : ProgHOL 64 → Bool
  | .dec nm _ _ b => !(nm == ptrVar) && checkByteStoresLocal ptrVar sz b
  | .seq a b => checkByteStoresLocal ptrVar sz a && checkByteStoresLocal ptrVar sz b
  | .ite _ a b => checkByteStoresLocal ptrVar sz a && checkByteStoresLocal ptrVar sz b
  | .while _ b => checkByteStoresLocal ptrVar sz b
  | .assign .local nm _ => !(nm == ptrVar)
  | .storeByte (.var .local nm) _ => (nm == ptrVar) && decide (1 ≤ sz)
  | .storeByte (.op .add [.var .local nm, .const off]) _ =>
      (nm == ptrVar) && decide (off.toNat < sz)
  | .skip | .break | .continue | .return _ | .raise _ _ | .annot _ _ => true
  | _ => false

theorem checkByteStoresLocal_sound {F : Type} (ptrVar : MlS) (sz : Nat) (hsz : sz ≤ 2048)
    (prog : ProgHOL 64) (hok : checkByteStoresLocal ptrVar sz prog = true)
    (s : PanSemStateFiniteExact 64 F) (p : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hp : s.locals.lookup ptrVar = some (.val (.word p))) :
    ByteEff s (evaluateHOLFiniteState s prog).2 [(p.toNat, sz)] ∧
    ((evaluateHOLFiniteState s prog).1 = none ∨
     (evaluateHOLFiniteState s prog).1 = some .break ∨
     (evaluateHOLFiniteState s prog).1 = some .continue →
      (evaluateHOLFiniteState s prog).2.locals.lookup ptrVar = some (.val (.word p))) := by
  have hsb : 2048 < sourceBase := by rw [sourceBase_val]; decide
  cases shape : prog with
  | skip => rw [evaluateHOLFiniteState_skip]; exact ⟨ByteEff.refl s _, fun _ => hp⟩
  | «break» => rw [evaluateHOLFiniteState_break]; exact ⟨ByteEff.refl s _, fun _ => hp⟩
  | «continue» => rw [evaluateHOLFiniteState_continue]; exact ⟨ByteEff.refl s _, fun _ => hp⟩
  | annot _ _ => rw [evaluateHOLFiniteState_annot]; exact ⟨ByteEff.refl s _, fun _ => hp⟩
  | «return» e =>
    refine ⟨byteEff_return s e _, fun h => ?_⟩
    rw [evaluateHOLFiniteState_return] at h
    split at h
    · simp at h
    · split at h <;> simp at h
  | raise _ _ =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split
      · exact ⟨(ByteEff.refl s _).locals_clock _ _, by simp⟩
      · exact ⟨ByteEff.refl s _, by simp⟩
    · exact ⟨ByteEff.refl s _, by simp⟩
  | assign k nm e =>
    cases k with
    | global => simp [shape, checkByteStoresLocal] at hok
    | «local» =>
      have hne : nm ≠ ptrVar := by simpa [shape, checkByteStoresLocal] using hok
      refine ⟨byteEff_assign_local s nm e _, fun h => ?_⟩
      rw [evaluateHOLFiniteState_assign] at h ⊢
      rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | val
      · simp [hev] at h
      · simp only [hev] at h ⊢
        split at h
        · rename_i hv; rw [if_pos hv]
          simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hp]
        · simp at h
  | dec nm sh init b =>
    have h12 : nm ≠ ptrVar ∧ checkByteStoresLocal ptrVar sz b = true := by
      simpa [shape, checkByteStoresLocal, Bool.and_eq_true] using hok
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    split
    · exact ⟨ByteEff.refl s _, by simp⟩
    · rename_i val hval
      split
      · have hp' : (setVarHOLFinite nm val s).locals.lookup ptrVar = some (.val (.word p)) := by
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h12.1, hp]
        have ih := checkByteStoresLocal_sound ptrVar sz hsz b h12.2 (setVarHOLFinite nm val s) p
          hc (guestInv_setVar nm val s hG) hp'
        refine ⟨(((ByteEff.refl s _).locals_clock _ _).trans ih.1).locals_clock _ _, fun h => ?_⟩
        dsimp only at h ⊢
        rw [resVarEq_lookup_ne _ nm ptrVar _ (Ne.symm h12.1), ih.2 h]
      · exact ⟨ByteEff.refl s _, by simp⟩
  | seq a b =>
    have h12 : checkByteStoresLocal ptrVar sz a = true ∧ checkByteStoresLocal ptrVar sz b = true := by
      simpa [shape, checkByteStoresLocal, Bool.and_eq_true] using hok
    have rem := evaluateHOLFiniteState_clock_le s a
    have iha := checkByteStoresLocal_sound ptrVar sz hsz a h12.1 s p hc hG hp
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hra : evaluateHOLFiniteState s a with ⟨r1, m⟩
    rw [hra] at iha rem
    cases r1 with
    | none =>
      have mclk : m.clock ≤ s.clock := rem
      have hpm := iha.2 (Or.inl rfl)
      have hGm := guestInv_congr iha.1.code iha.1.memaddrs iha.1.shMemaddrs iha.1.baseAddr hG
      have ihb := checkByteStoresLocal_sound ptrVar sz hsz b h12.2 m p (iha.1.code.trans hc) hGm hpm
      exact ⟨iha.1.trans ihb.1, ihb.2⟩
    | some _ => exact iha
  | ite c a b =>
    have h12 : checkByteStoresLocal ptrVar sz a = true ∧ checkByteStoresLocal ptrVar sz b = true := by
      simpa [shape, checkByteStoresLocal, Bool.and_eq_true] using hok
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact checkByteStoresLocal_sound ptrVar sz hsz b h12.2 s p hc hG hp
      · exact checkByteStoresLocal_sound ptrVar sz hsz a h12.1 s p hc hG hp
    · exact ⟨ByteEff.refl s _, by simp⟩
  | «while» c b =>
    have hb : checkByteStoresLocal ptrVar sz b = true := by simpa [shape, checkByteStoresLocal] using hok
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · exact ⟨(ByteEff.refl s _).locals_clock _ _, by simp⟩
        · have dec_lt : (decClockHOLFinite s).clock < s.clock := by simp only [decClockHOLFinite]; omega
          dsimp only; rw [fixClockHOLFinite_evaluateState]
          have hGd : GuestInv (decClockHOLFinite s) := guestInv_congr (s := s) rfl rfl rfl rfl hG
          have ih1 := checkByteStoresLocal_sound ptrVar sz hsz b hb (decClockHOLFinite s) p hc hGd hp
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) b
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) b with ⟨r1, mid⟩
          rw [hbr] at ih1 rem
          have smaller : mid.clock < s.clock := by change mid.clock ≤ s.clock - 1 at rem; omega
          have heff1 : ByteEff s mid [(p.toNat, sz)] := ((ByteEff.refl s _).locals_clock _ _).trans ih1.1
          have hGm : GuestInv mid := guestInv_congr heff1.code heff1.memaddrs heff1.shMemaddrs heff1.baseAddr hG
          cases r1 with
          | none =>
            have ihw := checkByteStoresLocal_sound ptrVar sz hsz (.while c b) (by simpa [checkByteStoresLocal] using hb)
              mid p (heff1.code.trans hc) hGm (ih1.2 (Or.inl rfl))
            exact ⟨heff1.trans ihw.1, ihw.2⟩
          | some res =>
            cases res with
            | «continue» =>
              have ihw := checkByteStoresLocal_sound ptrVar sz hsz (.while c b) (by simpa [checkByteStoresLocal] using hb)
                mid p (heff1.code.trans hc) hGm (ih1.2 (Or.inr (Or.inr rfl)))
              exact ⟨heff1.trans ihw.1, ihw.2⟩
            | «break» => exact ⟨heff1, fun _ => ih1.2 (Or.inr (Or.inl rfl))⟩
            | _ => exact ⟨heff1, by simp⟩
      · exact ⟨ByteEff.refl s _, fun _ => hp⟩
    · exact ⟨ByteEff.refl s _, by simp⟩
  | storeByte dst vexp =>
    have hloc_sb := (evaluate_storeByte_control_frame s dst vexp).2.2.1
    refine ⟨?_, fun _ => by rw [hloc_sb]; exact hp⟩
    cases dst with
    | var vk nm =>
      cases vk with
      | global => simp [shape, checkByteStoresLocal] at hok
      | «local» =>
        simp only [shape, checkByteStoresLocal, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
        rcases hok with ⟨rfl, hsz1⟩
        exact (byteEff_storeByte hG (.var .local nm) vexp (fun x hx _ => by
          simp [evalHOLExact, hp] at hx; subst hx
          exact ⟨(p.toNat, sz), List.mem_singleton.2 rfl, le_rfl, by omega⟩)).1
    | op bop args =>
      cases bop <;> try (simp [shape, checkByteStoresLocal] at hok)
      rcases args with _ | ⟨e1, _ | ⟨e2, _ | _⟩⟩ <;> try (simp [shape, checkByteStoresLocal] at hok)
      cases e1 with
      | var vk1 nm1 =>
        cases vk1 <;> try (simp [shape, checkByteStoresLocal] at hok)
        cases e2 with
        | const off =>
          simp only [shape, checkByteStoresLocal, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
          rcases hok with ⟨rfl, hoff⟩
          refine (byteEff_storeByte hG (.op .add [.var .local nm1, .const off]) vexp (fun x hx hdom => ?_)).1
          simp [evalHOLExact, evalListHOLExact, hp, valueIsWord, valueWord, wordOpHOL, wordOp] at hx
          subst hx
          rw [hG.memaddrs, ordinaryDomain_iff] at hdom
          have hal := panByteAlign_toNat64 (p + off)
          have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
          have hp_lt := p.isLt; have hoff_lt := off.isLt
          have hnw : p.toNat + off.toNat < 2 ^ 64 := by
            by_contra hge
            have : (p + off).toNat = p.toNat + off.toNat - 2 ^ 64 := by rw [BitVec.toNat_add]; omega
            omega
          have hadd : (p + off).toNat = p.toNat + off.toNat := BitVec.toNat_add_of_lt hnw
          exact ⟨(p.toNat, sz), List.mem_singleton.2 rfl, by omega, by omega⟩
        | _ => simp [shape, checkByteStoresLocal] at hok
      | _ => simp [shape, checkByteStoresLocal] at hok
    | _ => simp [shape, checkByteStoresLocal] at hok
  | _ => simp [shape, checkByteStoresLocal] at hok
termination_by (s.clock, sizeOf prog)
decreasing_by
  all_goals
    subst shape
    simp_wf
    first
      | exact Prod.Lex.left _ _ dec_lt
      | exact Prod.Lex.left _ _ smaller
      | exact Prod.Lex.right _ (by omega)
      | (rcases Nat.lt_or_eq_of_le mclk with h | h
         · exact Prod.Lex.left _ _ h
         · rw [h]; exact Prod.Lex.right _ (by omega))

theorem funByteEff_sha256_pair :
    FunByteEff (ofString "sha256_pair")
      (fun vals _ => [(valWordNat (vals[2]?.getD (.rStruct [])), 32)]) := by
  have hlook : originalRuntimeCode.lookup (ofString "sha256_pair") =
      some ([(ofString "input_a", .one), (ofString "input_b", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_sha256_pair, .one) :=
    lookup_of_guestAst_getElem 96 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_sha256_pair) rfl
  refine ⟨_, _, _, hlook, fun entry vals hc hG hl _ _ => ?_⟩
  obtain ⟨_, _, out, rfl, _, _, hout⟩ := lookupCode_three_words (by decide) (by decide) (by decide) hlook hl
  exact (checkByteStoresLocal_sound (ofString "out") 32 (by omega)
    (sourceFnBody Guest.Software.guestFn_sha256_pair) rfl entry out hc hG hout).1

theorem funByteEff_addr_from_words :
    FunByteEff (ofString "addr_from_words")
      (fun vals _ => [(valWordNat (vals[0]?.getD (.rStruct [])), 20)]) := by
  have hlook32 : originalRuntimeCode.lookup (ofString "st_be32") =
      some ([(ofString "p", .one), (ofString "v", .one)],
        sourceFnBody Guest.Software.guestFn_st_be32, .one) :=
    lookup_of_guestAst_getElem 27 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_st_be32) rfl
  have hlook64 : originalRuntimeCode.lookup (ofString "st_be64") =
      some ([(ofString "p", .one), (ofString "v", .one)],
        sourceFnBody Guest.Software.guestFn_st_be64, .one) :=
    lookup_of_guestAst_getElem 28 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_st_be64) rfl
  have hlook : originalRuntimeCode.lookup (ofString "addr_from_words") =
      some ([(ofString "out", .one), (ofString "hi4", .one), (ofString "mid8", .one), (ofString "lo8", .one)],
        sourceFnBody Guest.Software.guestFn_addr_from_words, .one) :=
    lookup_of_guestAst_getElem 860 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_addr_from_words) rfl
  refine ⟨_, _, _, hlook, fun entry vals hc hG hl hnt hres => ?_⟩
  obtain ⟨out, hi4, mid8, lo8, rfl, hout, hhi, hmid, hlo⟩ :=
    lookupCode_four_words (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hlook hl
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  have hsb : 20 < sourceBase := by rw [sourceBase_val]; decide
  have hbody : sourceFnBody Guest.Software.guestFn_addr_from_words =
      .seq (.call (some (none, none)) (ofString "st_be32") [.var .local (ofString "out"), .var .local (ofString "hi4")])
        (.seq (.call (some (none, none)) (ofString "st_be64")
            [.op .add [.var .local (ofString "out"), .const 4], .var .local (ofString "mid8")])
          (.seq (.call (some (none, none)) (ofString "st_be64")
              [.op .add [.var .local (ofString "out"), .const 12], .var .local (ofString "lo8")])
            (.return (.const 0)))) := rfl
  rw [hbody] at hnt hres ⊢
  dsimp only [valWordNat]
  rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
  rcases hc1 : evaluateHOLFiniteState entry
      (.call (some (none, none)) (ofString "st_be32") [.var .local (ofString "out"), .var .local (ofString "hi4")]) with ⟨r1, s1⟩
  rw [hc1] at hnt hres
  have hnt1 : r1 ≠ some .timeOut := by intro h; subst h; simp at hnt
  have hargs1 : evalListHOLFinite entry (h := fun a => Classical.propDecidable (entry.memaddrs a))
      [.var .local (ofString "out"), .var .local (ofString "hi4")] = some [.val (.word out), .val (.word hi4)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hout, hhi]
  have heff1 : ByteEff entry s1 [(out.toNat, 20)] := by
    have := call0_byteEff funByteEff_st_be32 entry _ [(out.toNat, 20)] hc hG
      (fun vs hvs i hi _ => by
        rw [hargs1] at hvs; injection hvs with hvs; subst hvs
        simp [valWordNat] at hi; subst hi; exact ⟨(out.toNat, 20), List.mem_singleton.2 rfl, le_rfl, by omega⟩)
      (by rw [hc1]; exact hnt1)
      (by rw [hc1]; cases r1 with | none => exact Or.inl rfl | some _ => exact Or.inr hres)
    rwa [hc1] at this
  cases r1 with
  | some _ => exact heff1
  | none =>
    obtain ⟨hs1_loc, rv1, hrv1⟩ := call0_two_word_success entry _ _ _ _ _ _ out hi4 (by decide) hc hlook32 hargs1 (by rw [hc1])
    rw [hc1] at hs1_loc
    have hout_hi : out.toNat + 4 ≤ heapEnd :=
      (st_be32_body_eff _ out (guestInv_callEntry entry _ hG)
        (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "v" ≠ ofString "p" by decide])
        (Or.inl ⟨rv1, hrv1⟩)).2.2
    have h264_plus : heapEnd + 16 < 2 ^ 64 := by rw [heapEnd_val]; decide
    have ha4 : (out + 4).toNat = out.toNat + 4 := BitVec.toNat_add_of_lt (by change out.toNat + 4 < 2 ^ 64; omega)
    have ha12 : (out + 12).toNat = out.toNat + 12 := BitVec.toNat_add_of_lt (by change out.toNat + 12 < 2 ^ 64; omega)
    dsimp only at hnt hres ⊢
    rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
    rcases hc2 : evaluateHOLFiniteState s1
        (.call (some (none, none)) (ofString "st_be64")
          [.op .add [.var .local (ofString "out"), .const 4], .var .local (ofString "mid8")]) with ⟨r2, s2⟩
    rw [hc2] at hnt hres
    have hnt2 : r2 ≠ some .timeOut := by intro h; subst h; simp at hnt
    have hGs1 : GuestInv s1 := guestInv_congr heff1.code heff1.memaddrs heff1.shMemaddrs heff1.baseAddr hG
    have hc_s1 : s1.code = originalRuntimeCode := heff1.code.trans hc
    have hout_s1 : s1.locals.lookup (ofString "out") = some (.val (.word out)) := by rw [hs1_loc]; exact hout
    have hmid_s1 : s1.locals.lookup (ofString "mid8") = some (.val (.word mid8)) := by rw [hs1_loc]; exact hmid
    have hargs2 : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
        [.op .add [.var .local (ofString "out"), .const 4], .var .local (ofString "mid8")] =
        some [.val (.word (out + 4)), .val (.word mid8)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hout_s1, hmid_s1, valueIsWord, valueWord, wordOpHOL, wordOp]
    have heff2 : ByteEff s1 s2 [(out.toNat, 20)] := by
      have := call0_byteEff funByteEff_st_be64 s1 _ [(out.toNat, 20)] hc_s1 hGs1
        (fun vs hvs i hi _ => by
          rw [hargs2] at hvs; injection hvs with hvs; subst hvs
          simp [valWordNat, ha4] at hi; subst hi
          exact ⟨(out.toNat, 20), List.mem_singleton.2 rfl, by omega, by omega⟩)
        (by rw [hc2]; exact hnt2)
        (by rw [hc2]; cases r2 with | none => exact Or.inl rfl | some _ => exact Or.inr hres)
      rwa [hc2] at this
    cases r2 with
    | some _ => exact heff1.trans heff2
    | none =>
      obtain ⟨hs2_loc, _, _⟩ := call0_two_word_success s1 _ _ _ _ _ _ (out + 4) mid8 (by decide) hc_s1 hlook64 hargs2 (by rw [hc2])
      rw [hc2] at hs2_loc
      dsimp only at hnt hres ⊢
      rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
      rcases hc3 : evaluateHOLFiniteState s2
          (.call (some (none, none)) (ofString "st_be64")
            [.op .add [.var .local (ofString "out"), .const 12], .var .local (ofString "lo8")]) with ⟨r3, s3⟩
      rw [hc3] at hnt hres
      have hnt3 : r3 ≠ some .timeOut := by intro h; subst h; simp at hnt
      have hGs2 : GuestInv s2 := guestInv_congr heff2.code heff2.memaddrs heff2.shMemaddrs heff2.baseAddr hGs1
      have hc_s2 : s2.code = originalRuntimeCode := heff2.code.trans hc_s1
      have hout_s2 : s2.locals.lookup (ofString "out") = some (.val (.word out)) := by rw [hs2_loc]; exact hout_s1
      have hlo_s2 : s2.locals.lookup (ofString "lo8") = some (.val (.word lo8)) := by rw [hs2_loc]; exact (hs1_loc ▸ hlo)
      have hargs3 : evalListHOLFinite s2 (h := fun a => Classical.propDecidable (s2.memaddrs a))
          [.op .add [.var .local (ofString "out"), .const 12], .var .local (ofString "lo8")] =
          some [.val (.word (out + 12)), .val (.word lo8)] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hout_s2, hlo_s2, valueIsWord, valueWord, wordOpHOL, wordOp]
      have heff3 : ByteEff s2 s3 [(out.toNat, 20)] := by
        have := call0_byteEff funByteEff_st_be64 s2 _ [(out.toNat, 20)] hc_s2 hGs2
          (fun vs hvs i hi _ => by
            rw [hargs3] at hvs; injection hvs with hvs; subst hvs
            simp [valWordNat, ha12] at hi; subst hi
            exact ⟨(out.toNat, 20), List.mem_singleton.2 rfl, by omega, by omega⟩)
          (by rw [hc3]; exact hnt3)
          (by rw [hc3]; cases r3 with | none => exact Or.inl rfl | some _ => exact Or.inr hres)
        rwa [hc3] at this
      cases r3 with
      | some _ => exact (heff1.trans heff2).trans heff3
      | none => exact ((heff1.trans heff2).trans heff3).trans (byteEff_return s3 _ _)

/-! ## 3. `keccak_f1600`, `keccak_absorb_block`, `keccak256` -/

/-- Check that `prog` writes only to `[base, base + sz)` via single-word `.store` at `ptrVar + off`
(`off + 8 ≤ sz ≤ 2048`), with single-word value expressions (`const`, `op`, `shift`, `load .one`,
or local variable in `wordVars` whose wordness is preserved!), and never modifies `ptrVar` or globals. -/
def isGuaranteedWordExp (wordVars : List MlS) : ExpHOL 64 → Bool
  | .const _ | .load .one _ | .loadByte _ | .load32 _
  | .op _ _ | .panop _ _ | .cmp _ _ _ | .shift _ _ _ | .baseAddr | .topAddr => true
  | .var .local nm => wordVars.contains nm
  | _ => false

theorem eval_isGuaranteedWordExp {F : Type} (s : PanSemStateFiniteExact 64 F)
    (wordVars : List MlS)
    (hwv : ∀ nm ∈ wordVars, ∃ w : BitVec 64, s.locals.lookup nm = some (.val (.word w)))
    (e : ExpHOL 64) (he : isGuaranteedWordExp wordVars e = true) :
    ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some v →
      ∃ w : BitVec 64, v = .val (.word w) := by
  intro v hv
  cases e with
  | const c => simp [evalHOLExact] at hv; exact ⟨c, hv.symm⟩
  | baseAddr => simp [evalHOLExact] at hv; exact ⟨s.baseAddr, hv.symm⟩
  | topAddr => simp [evalHOLExact] at hv; exact ⟨s.topAddr, hv.symm⟩
  | var vk nm =>
    cases vk with
    | global => simp [isGuaranteedWordExp] at he
    | «local» =>
      have hmem : nm ∈ wordVars := List.contains_iff_mem.1 (by simpa [isGuaranteedWordExp] using he)
      obtain ⟨w, hw⟩ := hwv nm hmem
      simp [evalHOLExact, hw] at hv; exact ⟨w, hv.symm⟩
  | load sh addrExp =>
    cases sh with
    | one => exact eval_load_one_word s addrExp v hv
    | comb _ | named _ => simp [isGuaranteedWordExp] at he
  | loadByte _ =>
    simp only [evalHOLExact] at hv
    split at hv
    · simp only [Option.map_eq_some_iff] at hv
      obtain ⟨_, _, rfl⟩ := hv; exact ⟨_, rfl⟩
    · cases hv
  | load32 _ =>
    simp only [evalHOLExact] at hv
    split at hv
    · simp only [Option.map_eq_some_iff] at hv
      obtain ⟨_, _, rfl⟩ := hv; exact ⟨_, rfl⟩
    · cases hv
  | op _ _ =>
    simp only [evalHOLExact] at hv
    split at hv
    · split at hv
      · simp only [Option.map_eq_some_iff] at hv
        obtain ⟨_, _, rfl⟩ := hv; exact ⟨_, rfl⟩
      · cases hv
    · cases hv
  | panop _ _ =>
    simp only [evalHOLExact] at hv
    split at hv
    · split at hv
      · simp only [Option.map_eq_some_iff] at hv
        obtain ⟨_, _, rfl⟩ := hv; exact ⟨_, rfl⟩
      · cases hv
    · cases hv
  | cmp _ _ _ =>
    simp only [evalHOLExact] at hv
    split at hv
    · injection hv with h; exact ⟨_, h.symm⟩
    · cases hv
  | shift _ _ _ =>
    simp only [evalHOLExact] at hv
    split at hv
    · simp only [Option.map_eq_some_iff] at hv
      obtain ⟨_, _, rfl⟩ := hv; exact ⟨_, rfl⟩
    · cases hv
  | _ => simp [isGuaranteedWordExp] at he

def checkWordStoresLocal (ptrVar : MlS) (sz : Nat) (wordVars : List MlS) : ProgHOL 64 → Bool
  | .dec nm .one init b =>
      !(nm == ptrVar) && isGuaranteedWordExp wordVars init &&
      checkWordStoresLocal ptrVar sz (nm :: wordVars) b
  | .seq a b => checkWordStoresLocal ptrVar sz wordVars a && checkWordStoresLocal ptrVar sz wordVars b
  | .ite _ a b => checkWordStoresLocal ptrVar sz wordVars a && checkWordStoresLocal ptrVar sz wordVars b
  | .while _ b => checkWordStoresLocal ptrVar sz wordVars b
  | .assign .local nm e => !(nm == ptrVar) &&
      (!(wordVars.contains nm) || isGuaranteedWordExp wordVars e)
  | .store (.var .local nm) vexp =>
      (nm == ptrVar) && decide (8 ≤ sz) && isGuaranteedWordExp wordVars vexp
  | .store (.op .add [.var .local nm, .const off]) vexp =>
      (nm == ptrVar) && decide (off.toNat + 8 ≤ sz) && isGuaranteedWordExp wordVars vexp
  | .skip | .break | .continue | .return _ | .raise _ _ | .annot _ _ => true
  | _ => false

theorem checkWordStoresLocal_sound {F : Type} (ptrVar : MlS) (sz : Nat) (hsz : sz ≤ 2048)
    (wordVars : List MlS) (prog : ProgHOL 64)
    (hok : checkWordStoresLocal ptrVar sz wordVars prog = true)
    (s : PanSemStateFiniteExact 64 F) (p : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hp : s.locals.lookup ptrVar = some (.val (.word p)))
    (hwv : ∀ nm ∈ wordVars, ∃ w : BitVec 64, s.locals.lookup nm = some (.val (.word w))) :
    ByteEff s (evaluateHOLFiniteState s prog).2 [(p.toNat, sz)] ∧
    ((evaluateHOLFiniteState s prog).1 = none ∨
     (evaluateHOLFiniteState s prog).1 = some .break ∨
     (evaluateHOLFiniteState s prog).1 = some .continue →
      (evaluateHOLFiniteState s prog).2.locals.lookup ptrVar = some (.val (.word p)) ∧
      ∀ nm ∈ wordVars, ∃ w : BitVec 64,
        (evaluateHOLFiniteState s prog).2.locals.lookup nm = some (.val (.word w))) := by
  have hsb : 2048 < sourceBase := by rw [sourceBase_val]; decide
  cases shape : prog with
  | skip => rw [evaluateHOLFiniteState_skip]; exact ⟨ByteEff.refl s _, fun _ => ⟨hp, hwv⟩⟩
  | «break» => rw [evaluateHOLFiniteState_break]; exact ⟨ByteEff.refl s _, fun _ => ⟨hp, hwv⟩⟩
  | «continue» => rw [evaluateHOLFiniteState_continue]; exact ⟨ByteEff.refl s _, fun _ => ⟨hp, hwv⟩⟩
  | annot _ _ => rw [evaluateHOLFiniteState_annot]; exact ⟨ByteEff.refl s _, fun _ => ⟨hp, hwv⟩⟩
  | «return» e =>
    refine ⟨byteEff_return s e _, fun h => ?_⟩
    rw [evaluateHOLFiniteState_return] at h
    split at h
    · simp at h
    · split at h <;> simp at h
  | raise _ _ =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split
      · exact ⟨(ByteEff.refl s _).locals_clock _ _, by simp⟩
      · exact ⟨ByteEff.refl s _, by simp⟩
    · exact ⟨ByteEff.refl s _, by simp⟩
  | assign k nm e =>
    cases k with
    | global => simp [shape, checkWordStoresLocal] at hok
    | «local» =>
      have h12 : nm ≠ ptrVar ∧ (!(wordVars.contains nm) || isGuaranteedWordExp wordVars e) = true := by
        simpa [shape, checkWordStoresLocal, Bool.and_eq_true] using hok
      refine ⟨byteEff_assign_local s nm e _, fun h => ?_⟩
      rw [evaluateHOLFiniteState_assign] at h ⊢
      rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | val
      · simp [hev] at h
      · simp only [hev] at h ⊢
        split at h
        · rename_i hv; rw [if_pos hv]
          refine ⟨by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h12.1, hp],
            fun m hm => ?_⟩
          by_cases hmn : m = nm
          · subst hmn
            have hge : isGuaranteedWordExp wordVars e = true := by
              have hmem : wordVars.contains m = true := List.contains_iff_mem.2 hm
              have h2 := h12.2
              rw [hmem] at h2; simpa using h2
            obtain ⟨w, rfl⟩ := eval_isGuaranteedWordExp s wordVars hwv e hge val hev
            exact ⟨w, by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
          · obtain ⟨w, hw⟩ := hwv m hm
            exact ⟨w, by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hmn, hw]⟩
        · simp at h
  | dec nm sh init b =>
    cases sh with
    | comb _ | named _ => simp [shape, checkWordStoresLocal] at hok
    | one =>
      have h123 : (nm ≠ ptrVar ∧ isGuaranteedWordExp wordVars init = true) ∧
          checkWordStoresLocal ptrVar sz (nm :: wordVars) b = true := by
        simpa [shape, checkWordStoresLocal, Bool.and_eq_true] using hok
      rw [evaluateHOLFiniteState_dec_total]; dsimp only
      rcases hinit : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init with _ | val
      · exact ⟨ByteEff.refl s _, by simp⟩
      · dsimp only
        split
        · obtain ⟨wi, rfl⟩ := eval_isGuaranteedWordExp s wordVars hwv init h123.1.2 val hinit
          have hp' : (setVarHOLFinite nm (.val (.word wi)) s).locals.lookup ptrVar = some (.val (.word p)) := by
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h123.1.1, hp]
          have hwv' : ∀ m ∈ nm :: wordVars, ∃ w : BitVec 64,
              (setVarHOLFinite nm (.val (.word wi)) s).locals.lookup m = some (.val (.word w)) := by
            intro m hm
            by_cases hmn : m = nm
            · subst hmn; exact ⟨wi, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
            · have hm_old : m ∈ wordVars := by simp [hmn] at hm; exact hm
              obtain ⟨w, hw⟩ := hwv m hm_old
              exact ⟨w, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hmn, hw]⟩
          have ih := checkWordStoresLocal_sound ptrVar sz hsz (nm :: wordVars) b h123.2
            (setVarHOLFinite nm (.val (.word wi)) s) p hc (guestInv_setVar nm _ s hG) hp' hwv'
          refine ⟨(((ByteEff.refl s _).locals_clock _ _).trans ih.1).locals_clock _ _, fun h => ?_⟩
          dsimp only at h ⊢
          obtain ⟨hp_post, hwv_post⟩ := ih.2 h
          refine ⟨by rw [resVarEq_lookup_ne _ nm ptrVar _ (Ne.symm h123.1.1), hp_post], fun m hm => ?_⟩
          by_cases hmn : m = nm
          · subst hmn
            obtain ⟨w0, hw0⟩ := hwv m hm
            exact ⟨w0, by simp [HolFiniteMapExact.resVarEq, hw0, HolFiniteMapExact.updateEq, FUPDATE_HOL]⟩
          · obtain ⟨w', hw'⟩ := hwv_post m (List.mem_cons_of_mem _ hm)
            exact ⟨w', by rw [resVarEq_lookup_ne _ nm m _ hmn, hw']⟩
        · exact ⟨ByteEff.refl s _, by simp⟩
  | seq a b =>
    have h12 : checkWordStoresLocal ptrVar sz wordVars a = true ∧
        checkWordStoresLocal ptrVar sz wordVars b = true := by
      simpa [shape, checkWordStoresLocal, Bool.and_eq_true] using hok
    have rem := evaluateHOLFiniteState_clock_le s a
    have iha := checkWordStoresLocal_sound ptrVar sz hsz wordVars a h12.1 s p hc hG hp hwv
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hra : evaluateHOLFiniteState s a with ⟨r1, m⟩
    rw [hra] at iha rem
    cases r1 with
    | none =>
      have mclk : m.clock ≤ s.clock := rem
      obtain ⟨hpm, hwvm⟩ := iha.2 (Or.inl rfl)
      have hGm := guestInv_congr iha.1.code iha.1.memaddrs iha.1.shMemaddrs iha.1.baseAddr hG
      have ihb := checkWordStoresLocal_sound ptrVar sz hsz wordVars b h12.2 m p (iha.1.code.trans hc) hGm hpm hwvm
      exact ⟨iha.1.trans ihb.1, ihb.2⟩
    | some _ => exact iha
  | ite c a b =>
    have h12 : checkWordStoresLocal ptrVar sz wordVars a = true ∧
        checkWordStoresLocal ptrVar sz wordVars b = true := by
      simpa [shape, checkWordStoresLocal, Bool.and_eq_true] using hok
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact checkWordStoresLocal_sound ptrVar sz hsz wordVars b h12.2 s p hc hG hp hwv
      · exact checkWordStoresLocal_sound ptrVar sz hsz wordVars a h12.1 s p hc hG hp hwv
    · exact ⟨ByteEff.refl s _, by simp⟩
  | «while» c b =>
    have hb : checkWordStoresLocal ptrVar sz wordVars b = true := by
      simpa [shape, checkWordStoresLocal] using hok
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · exact ⟨(ByteEff.refl s _).locals_clock _ _, by simp⟩
        · have dec_lt : (decClockHOLFinite s).clock < s.clock := by simp only [decClockHOLFinite]; omega
          dsimp only; rw [fixClockHOLFinite_evaluateState]
          have hGd : GuestInv (decClockHOLFinite s) := guestInv_congr (s := s) rfl rfl rfl rfl hG
          have ih1 := checkWordStoresLocal_sound ptrVar sz hsz wordVars b hb (decClockHOLFinite s) p hc hGd hp hwv
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) b
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) b with ⟨r1, mid⟩
          rw [hbr] at ih1 rem
          have smaller : mid.clock < s.clock := by change mid.clock ≤ s.clock - 1 at rem; omega
          have heff1 : ByteEff s mid [(p.toNat, sz)] := ((ByteEff.refl s _).locals_clock _ _).trans ih1.1
          have hGm : GuestInv mid := guestInv_congr heff1.code heff1.memaddrs heff1.shMemaddrs heff1.baseAddr hG
          cases r1 with
          | none =>
            obtain ⟨hpm, hwvm⟩ := ih1.2 (Or.inl rfl)
            have ihw := checkWordStoresLocal_sound ptrVar sz hsz wordVars (.while c b)
              (by simpa [checkWordStoresLocal] using hb) mid p (heff1.code.trans hc) hGm hpm hwvm
            exact ⟨heff1.trans ihw.1, ihw.2⟩
          | some res =>
            cases res with
            | «continue» =>
              obtain ⟨hpm, hwvm⟩ := ih1.2 (Or.inr (Or.inr rfl))
              have ihw := checkWordStoresLocal_sound ptrVar sz hsz wordVars (.while c b)
                (by simpa [checkWordStoresLocal] using hb) mid p (heff1.code.trans hc) hGm hpm hwvm
              exact ⟨heff1.trans ihw.1, ihw.2⟩
            | «break» => exact ⟨heff1, fun _ => ih1.2 (Or.inr (Or.inl rfl))⟩
            | _ => exact ⟨heff1, by simp⟩
      · exact ⟨ByteEff.refl s _, fun _ => ⟨hp, hwv⟩⟩
    · exact ⟨ByteEff.refl s _, by simp⟩
  | store dst vexp =>
    have hloc_st := (evaluate_store_control_frame s dst vexp).2.1
    refine ⟨?_, fun _ => by rw [hloc_st]; exact ⟨hp, hwv⟩⟩
    cases dst with
    | var vk nm =>
      cases vk with
      | global => simp [shape, checkWordStoresLocal] at hok
      | «local» =>
        have h123 : (nm = ptrVar ∧ 8 ≤ sz) ∧ isGuaranteedWordExp wordVars vexp = true := by
          simpa [shape, checkWordStoresLocal, Bool.and_eq_true] using hok
        rcases h123 with ⟨⟨rfl, hsz8⟩, hv_ok⟩
        exact (byteEff_store_one hG (.var .local nm) vexp
          (eval_isGuaranteedWordExp s wordVars hwv vexp hv_ok)
          (fun x hx _ => by
            simp [evalHOLExact, hp] at hx; subst hx
            exact ⟨(p.toNat, sz), List.mem_singleton.2 rfl, le_rfl, by omega⟩)).1
    | op bop args =>
      cases bop <;> try (simp [shape, checkWordStoresLocal] at hok)
      rcases args with _ | ⟨e1, _ | ⟨e2, _ | _⟩⟩ <;> try (simp [shape, checkWordStoresLocal] at hok)
      cases e1 with
      | var vk1 nm1 =>
        cases vk1 <;> try (simp [shape, checkWordStoresLocal] at hok)
        cases e2 with
        | const off =>
          have h123 : (nm1 = ptrVar ∧ off.toNat + 8 ≤ sz) ∧ isGuaranteedWordExp wordVars vexp = true := by
            simpa [shape, checkWordStoresLocal, Bool.and_eq_true] using hok
          rcases h123 with ⟨⟨rfl, hoff⟩, hv_ok⟩
          refine (byteEff_store_one hG (.op .add [.var .local nm1, .const off]) vexp
            (eval_isGuaranteedWordExp s wordVars hwv vexp hv_ok) (fun x hx hdom => ?_)).1
          simp [evalHOLExact, evalListHOLExact, hp, valueIsWord, valueWord, wordOpHOL, wordOp] at hx
          subst hx
          rw [hG.memaddrs, ordinaryDomain_iff] at hdom
          have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
          have hp_lt := p.isLt; have hoff_lt := off.isLt
          have hnw : p.toNat + off.toNat < 2 ^ 64 := by
            by_contra hge
            have : (p + off).toNat = p.toNat + off.toNat - 2 ^ 64 := by rw [BitVec.toNat_add]; omega
            omega
          have hadd : (p + off).toNat = p.toNat + off.toNat := BitVec.toNat_add_of_lt hnw
          exact ⟨(p.toNat, sz), List.mem_singleton.2 rfl, by omega, by omega⟩
        | _ => simp [shape, checkWordStoresLocal] at hok
      | _ => simp [shape, checkWordStoresLocal] at hok
    | _ => simp [shape, checkWordStoresLocal] at hok
  | _ => simp [shape, checkWordStoresLocal] at hok
termination_by (s.clock, sizeOf prog)
decreasing_by
  all_goals
    subst shape
    simp_wf
    first
      | exact Prod.Lex.left _ _ dec_lt
      | exact Prod.Lex.left _ _ smaller
      | exact Prod.Lex.right _ (by omega)
      | (rcases Nat.lt_or_eq_of_le mclk with h | h
         · exact Prod.Lex.left _ _ h
         · rw [h]; exact Prod.Lex.right _ (by omega))

theorem funByteEff_keccak_f1600 :
    FunByteEff (ofString "keccak_f1600")
      (fun vals _ => [(valWordNat (vals[0]?.getD (.rStruct [])), 200)]) := by
  have hlook : originalRuntimeCode.lookup (ofString "keccak_f1600") =
      some ([(ofString "stp", .one)], sourceFnBody Guest.Software.guestFn_keccak_f1600, .one) :=
    lookup_of_guestAst_getElem 101 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_keccak_f1600) rfl
  refine ⟨_, _, _, hlook, fun entry vals hc hG hl _ _ => ?_⟩
  obtain ⟨stp, rfl, hstp⟩ := lookupCode_one_word hlook hl
  exact (checkWordStoresLocal_sound (ofString "stp") 200 (by omega) []
    (sourceFnBody Guest.Software.guestFn_keccak_f1600) rfl entry stp hc hG hstp
    (fun _ h => by simp at h)).1

/-- `keccak_absorb_block(stp, blk)`: loop updates `stp + i` for `i <s 136`, then calls `keccak_f1600(stp)`. -/
private theorem absorb_loop_eff {F : Type}
    (valExp : ExpHOL 64)
    (hval : ∀ (t : PanSemStateFiniteExact 64 F) v,
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) valExp = some v →
      ∃ w : BitVec 64, v = .val (.word w))
    (k : Nat) (s : PanSemStateFiniteExact 64 F) (stp iw : BitVec 64)
    (hk : s.clock ≤ k) (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hstp : s.locals.lookup (ofString "stp") = some (.val (.word stp)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hi_bound : iw.toNat ≤ 136 ∧ iw.toNat % 8 = 0) :
    let body := ProgHOL.seq
      (.store (.op .add [.var .local (ofString "stp"), .var .local (ofString "i")]) valExp)
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8]))
    let lp := ProgHOL.while (.cmp .less (.var .local (ofString "i")) (.const 136)) body
    ByteEff s (evaluateHOLFiniteState s lp).2 [(stp.toNat, 200)] ∧
    ((evaluateHOLFiniteState s lp).1 = none →
      (evaluateHOLFiniteState s lp).2.locals.lookup (ofString "stp") = some (.val (.word stp))) := by
  have hsb : 200 < sourceBase := by rw [sourceBase_val]; decide
  induction k generalizing s iw with
  | zero =>
    dsimp only; rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · exact ⟨(ByteEff.refl s _).locals_clock _ _, by simp⟩
        · omega
      · exact ⟨ByteEff.refl s _, fun _ => hstp⟩
    · exact ⟨ByteEff.refl s _, by simp⟩
  | succ k ih =>
    dsimp only; rw [evaluateHOLFiniteState_while_total]
    split
    · rename_i cw hcond
      split
      · rename_i hnz
        split
        · exact ⟨(ByteEff.refl s _).locals_clock _ _, by simp⟩
        · dsimp only; rw [fixClockHOLFinite_evaluateState]
          have hlt136 : iw.toNat < 136 := by
            rw [evalHOLFinite_eq_toExact] at hcond
            simp only [evalHOLExact, hi, Compiler.Encoders.Asm.wordCmpHOL,
              holAsmSignedLess_small iw 136 (by omega) (by decide)] at hcond
            by_cases hlt : iw.toNat < (136 : BitVec 64).toNat
            · exact hlt
            · have h136_val : (136 : BitVec 64).toNat = 136 := rfl
              rw [h136_val] at hlt
              simp [hlt] at hcond; exact absurd hcond.symm hnz
          let sd := decClockHOLFinite s
          have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
          have heff_st : ByteEff sd
              (evaluateHOLFiniteState sd (.store (.op .add [.var .local (ofString "stp"), .var .local (ofString "i")]) valExp)).2
              [(stp.toNat, 200)] := by
            refine (byteEff_store_one hGd _ valExp (hval sd) (fun x hx hdom => ?_)).1
            have ex := eval_add2_locals sd _ _ stp iw hstp hi
            rw [ex] at hx; injection hx with hx; injection hx with hx; injection hx with hx; subst hx
            rw [hGd.memaddrs, ordinaryDomain_iff] at hdom
            have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
            have hs_lt := stp.isLt
            have hnw : stp.toNat + iw.toNat < 2 ^ 64 := by
              by_contra hge
              have : (stp + iw).toNat = stp.toNat + iw.toNat - 2 ^ 64 := by rw [BitVec.toNat_add]; omega
              omega
            have hadd : (stp + iw).toNat = stp.toNat + iw.toNat := BitVec.toNat_add_of_lt hnw
            exact ⟨(stp.toNat, 200), List.mem_singleton.2 rfl, by omega, by omega⟩
          have hloc_st := (evaluate_store_control_frame sd (.op .add [.var .local (ofString "stp"), .var .local (ofString "i")]) valExp).2.1
          have hclk_st := (evaluate_store_control_frame sd (.op .add [.var .local (ofString "stp"), .var .local (ofString "i")]) valExp).2.2
          rw [evaluateHOLFiniteState_seq_line780]
          rcases hst_r : evaluateHOLFiniteState sd (.store (.op .add [.var .local (ofString "stp"), .var .local (ofString "i")]) valExp) with ⟨r1, m1⟩
          rw [hst_r] at heff_st hloc_st hclk_st
          cases r1 with
          | some r1' =>
            have hcf := (evaluate_store_control_frame sd (.op .add [.var .local (ofString "stp"), .var .local (ofString "i")]) valExp).1
            rw [hst_r] at hcf
            rcases hcf with h | h <;> simp at h; subst h
            exact ⟨((ByteEff.refl s _).locals_clock _ _).trans heff_st, by simp⟩
          | none =>
            dsimp only
            have hi_m1 : m1.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hloc_st]; exact hi
            have hstp_m1 : m1.locals.lookup (ofString "stp") = some (.val (.word stp)) := by rw [hloc_st]; exact hstp
            have hasgn : evaluateHOLFiniteState m1
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])) =
                (none, setVarHOLFinite (ofString "i") (.val (.word (iw + 8))) m1) := by
              simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hi_m1, wordOpHOL, wordOp,
                valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
                shapeOfHOLExact, shapeEqHOL]
            rw [hasgn]; dsimp only
            let m2 := setVarHOLFinite (ofString "i") (.val (.word (iw + 8))) m1
            have heff_m2 : ByteEff s m2 [(stp.toNat, 200)] :=
              (((ByteEff.refl s _).locals_clock _ _).trans heff_st).locals_clock _ _
            have hGm2 : GuestInv m2 := guestInv_congr heff_m2.code heff_m2.memaddrs heff_m2.shMemaddrs heff_m2.baseAddr hG
            have hstp_m2 : m2.locals.lookup (ofString "stp") = some (.val (.word stp)) := by
              simp [m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hstp_m1, show ofString "i" ≠ ofString "stp" by decide]
            have hi_m2 : m2.locals.lookup (ofString "i") = some (.val (.word (iw + 8))) := by
              simp [m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have hi8_le : (iw + 8).toNat ≤ 136 ∧ (iw + 8).toNat % 8 = 0 := by
              have : (iw + 8).toNat = iw.toNat + 8 := BitVec.toNat_add_of_lt (by change iw.toNat + 8 < 2 ^ 64; omega)
              omega
            have hm2_clk : m2.clock ≤ k := by
              change m1.clock ≤ k; rw [hclk_st]; change s.clock - 1 ≤ k; omega
            have ih_res := ih m2 (iw + 8) hm2_clk (heff_m2.code.trans hc) hGm2 hstp_m2 hi_m2 hi8_le
            exact ⟨heff_m2.trans ih_res.1, ih_res.2⟩
      · exact ⟨ByteEff.refl s _, fun _ => hstp⟩
    · exact ⟨ByteEff.refl s _, by simp⟩

theorem funByteEff_keccak_absorb_block :
    FunByteEff (ofString "keccak_absorb_block")
      (fun vals _ => [(valWordNat (vals[0]?.getD (.rStruct [])), 200)]) := by
  have hlook : originalRuntimeCode.lookup (ofString "keccak_absorb_block") =
      some ([(ofString "stp", .one), (ofString "blk", .one)],
        sourceFnBody Guest.Software.guestFn_keccak_absorb_block, .one) :=
    lookup_of_guestAst_getElem 102 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_keccak_absorb_block) rfl
  refine ⟨_, _, _, hlook, fun {F} entry vals hc hG hl hnt hres => ?_⟩
  obtain ⟨stp, blk, rfl, hstp, _⟩ := lookupCode_two_words (by decide) hlook hl
  change ByteEff entry _ [(stp.toNat, 200)]
  have hop_word : ∀ (t : PanSemStateFiniteExact 64 F) bop eL v,
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) (.op bop eL) = some v →
      ∃ w : BitVec 64, v = .val (.word w) :=
    fun t bop eL => eval_isGuaranteedWordExp t [] (fun _ h => by simp at h) (.op bop eL) rfl
  let vAligned : ExpHOL 64 := InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural
    (Exp.op BinOp.xor
      [Exp.load Shape.one (Exp.op BinOp.add [Exp.var VarKind.local "stp", Exp.var VarKind.local "i"]),
       Exp.load Shape.one (Exp.op BinOp.add [Exp.var VarKind.local "blk", Exp.var VarKind.local "i"])])
  let vUnaligned : ExpHOL 64 := InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural
    (Exp.op BinOp.xor
      [Exp.load Shape.one (Exp.op BinOp.add [Exp.var VarKind.local "stp", Exp.var VarKind.local "i"]),
       Exp.op BinOp.or
        [(Exp.op BinOp.add [Exp.var VarKind.local "blk", Exp.var VarKind.local "i"]).loadByte,
         Exp.shift Shift.lsl (Exp.op BinOp.add [Exp.var VarKind.local "blk", Exp.var VarKind.local "i", Exp.const 1#64]).loadByte (Exp.const 8#64),
         Exp.shift Shift.lsl (Exp.op BinOp.add [Exp.var VarKind.local "blk", Exp.var VarKind.local "i", Exp.const 2#64]).loadByte (Exp.const 16#64),
         Exp.shift Shift.lsl (Exp.op BinOp.add [Exp.var VarKind.local "blk", Exp.var VarKind.local "i", Exp.const 3#64]).loadByte (Exp.const 24#64),
         Exp.shift Shift.lsl
          (Exp.op BinOp.or
            [(Exp.op BinOp.add [Exp.var VarKind.local "blk", Exp.var VarKind.local "i", Exp.const 4#64]).loadByte,
             Exp.shift Shift.lsl (Exp.op BinOp.add [Exp.var VarKind.local "blk", Exp.var VarKind.local "i", Exp.const 4#64, Exp.const 1#64]).loadByte (Exp.const 8#64),
             Exp.shift Shift.lsl (Exp.op BinOp.add [Exp.var VarKind.local "blk", Exp.var VarKind.local "i", Exp.const 4#64, Exp.const 2#64]).loadByte (Exp.const 16#64),
             Exp.shift Shift.lsl (Exp.op BinOp.add [Exp.var VarKind.local "blk", Exp.var VarKind.local "i", Exp.const 4#64, Exp.const 3#64]).loadByte (Exp.const 24#64)])
          (Exp.const 32#64)]])
  let lpA := ProgHOL.while (.cmp .less (.var .local (ofString "i")) (.const 136))
    (.seq (.store (.op .add [.var .local (ofString "stp"), .var .local (ofString "i")]) vAligned)
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])))
  let lpU := ProgHOL.while (.cmp .less (.var .local (ofString "i")) (.const 136))
    (.seq (.store (.op .add [.var .local (ofString "stp"), .var .local (ofString "i")]) vUnaligned)
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])))
  have hbody : sourceFnBody Guest.Software.guestFn_keccak_absorb_block =
      .dec (ofString "i") .one (.const 0)
        (.seq (.ite (.cmp .equal (.op .and [.var .local (ofString "blk"), .const 7]) (.const 0)) lpA lpU)
          (.seq (.call (some (none, none)) (ofString "keccak_f1600") [.var .local (ofString "stp")])
            (.return (.const 0)))) := rfl
  rw [hbody] at hnt hres ⊢
  rw [evaluateHOLFiniteState_dec_total] at hnt hres ⊢
  have hev0 : @evalHOLExact 64 F _ entry.toExact (fun a => Classical.propDecidable (entry.memaddrs a)) (.const 0) =
      some (.val (.word 0)) := rfl
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only at hnt hres ⊢
  rw [hev0] at hnt hres ⊢; dsimp only at hnt hres ⊢
  rw [if_pos hsh0] at hnt hres ⊢; dsimp only at hnt hres ⊢
  let si := setVarHOLFinite (ofString "i") (.val (.word 0)) entry
  have hGi : GuestInv si := guestInv_setVar _ _ entry hG
  have hstp_i : si.locals.lookup (ofString "stp") = some (.val (.word stp)) := by
    simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hstp, show ofString "i" ≠ ofString "stp" by decide]
  have hi_i : si.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
  have hite_eff : ByteEff si (evaluateHOLFiniteState si
      (.ite (.cmp .equal (.op .and [.var .local (ofString "blk"), .const 7]) (.const 0)) lpA lpU)).2 [(stp.toNat, 200)] ∧
      ((evaluateHOLFiniteState si
        (.ite (.cmp .equal (.op .and [.var .local (ofString "blk"), .const 7]) (.const 0)) lpA lpU)).1 = none →
        (evaluateHOLFiniteState si
          (.ite (.cmp .equal (.op .and [.var .local (ofString "blk"), .const 7]) (.const 0)) lpA lpU)).2.locals.lookup
          (ofString "stp") = some (.val (.word stp))) := by
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact absorb_loop_eff vUnaligned (fun t => hop_word t _ _) si.clock si stp 0 le_rfl hc hGi hstp_i hi_i ⟨by simp, by simp⟩
      · exact absorb_loop_eff vAligned (fun t => hop_word t _ _) si.clock si stp 0 le_rfl hc hGi hstp_i hi_i ⟨by simp, by simp⟩
    · exact ⟨ByteEff.refl si _, by simp⟩
  rcases h1 : evaluateHOLFiniteState si
      (.ite (.cmp .equal (.op .and [.var .local (ofString "blk"), .const 7]) (.const 0)) lpA lpU) with ⟨r1, s1⟩
  rw [h1] at hnt hres hite_eff
  have heff_e1 : ByteEff entry s1 [(stp.toNat, 200)] := ((ByteEff.refl entry _).locals_clock _ _).trans hite_eff.1
  cases r1 with
  | some _ => exact heff_e1.locals_clock _ _
  | none =>
    dsimp only at hnt hres ⊢
    have hstp_1 : s1.locals.lookup (ofString "stp") = some (.val (.word stp)) := hite_eff.2 rfl
    have hGs1 : GuestInv s1 := guestInv_congr heff_e1.code heff_e1.memaddrs heff_e1.shMemaddrs heff_e1.baseAddr hG
    have hc_s1 : s1.code = originalRuntimeCode := heff_e1.code.trans hc
    rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
    rcases hc_f : evaluateHOLFiniteState s1
        (.call (some (none, none)) (ofString "keccak_f1600") [.var .local (ofString "stp")]) with ⟨rf, sf⟩
    rw [hc_f] at hnt hres
    have hnt_f : rf ≠ some .timeOut := by intro h; subst h; simp at hnt
    have hargs_f : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
        [.var .local (ofString "stp")] = some [.val (.word stp)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hstp_1]
    have heff_f : ByteEff s1 sf [(stp.toNat, 200)] := by
      have := call0_byteEff funByteEff_keccak_f1600 s1 _ [(stp.toNat, 200)] hc_s1 hGs1
        (fun vs hvs i hi _ => by
          rw [hargs_f] at hvs; injection hvs with hvs; subst hvs
          simp [valWordNat] at hi; subst hi
          exact ⟨(stp.toNat, 200), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
        (by rw [hc_f]; exact hnt_f)
        (by rw [hc_f]; cases rf with | none => exact Or.inl rfl | some _ => exact Or.inr hres)
      rwa [hc_f] at this
    cases rf with
    | some _ => exact (heff_e1.trans heff_f).locals_clock _ _
    | none => exact ((heff_e1.trans heff_f).trans (byteEff_return sf _ _)).locals_clock _ _

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

private theorem eval_cmp_notLower_i136 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (n iw cw : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hev : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 136])) =
      some (.val (.word cw))) :
    cw = if (iw + 136).toNat ≤ n.toNat then 1 else 0 := by
  rw [evalHOLFinite_eq_toExact] at hev
  simp [evalHOLExact, evalListHOLExact, hn, hi, valueIsWord, valueWord, wordOpHOL, wordOp,
    Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, BitVec.le_def] at hev
  by_cases hle : (iw + 136).toNat ≤ n.toNat
  · have hnl : ¬ (n.toNat < (iw + 136).toNat) := by omega
    simp [hle, hnl] at hev ⊢; exact hev.symm
  · have hl : n.toNat < (iw + 136).toNat := by omega
    simp [hle, hl] at hev ⊢; exact hev.symm

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

private theorem keccak_main_loop_eff {F : Type}
    (k : Nat) (s : PanSemStateFiniteExact 64 F) (stp p n iw : BitVec 64)
    (hk : s.clock ≤ k) (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hstp : s.locals.lookup (ofString "stp") = some (.val (.word stp)))
    (hp : s.locals.lookup (ofString "p") = some (.val (.word p)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hle : iw.toNat ≤ n.toNat)
    (hnt : (evaluateHOLFiniteState s
      (.while (.cmp .notLower (.var .local (ofString "n"))
          (.op .add [.var .local (ofString "i"), .const 136]))
        (.seq (.call (some (none, none)) (ofString "keccak_absorb_block")
            [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 136]))))).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState s
      (.while (.cmp .notLower (.var .local (ofString "n"))
          (.op .add [.var .local (ofString "i"), .const 136]))
        (.seq (.call (some (none, none)) (ofString "keccak_absorb_block")
            [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 136]))))).1 = none ∨
      Resumes (evaluateHOLFiniteState s
        (.while (.cmp .notLower (.var .local (ofString "n"))
            (.op .add [.var .local (ofString "i"), .const 136]))
          (.seq (.call (some (none, none)) (ofString "keccak_absorb_block")
              [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
            (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 136]))))).1) :
    let out := evaluateHOLFiniteState s
      (.while (.cmp .notLower (.var .local (ofString "n"))
          (.op .add [.var .local (ofString "i"), .const 136]))
        (.seq (.call (some (none, none)) (ofString "keccak_absorb_block")
            [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 136]))))
    ByteEff s out.2 [(stp.toNat, 200)] ∧
    (out.1 = none →
      (∀ v, v ≠ ofString "i" → out.2.locals.lookup v = s.locals.lookup v) ∧
      ∃ iw' : BitVec 64,
        out.2.locals.lookup (ofString "i") = some (.val (.word iw')) ∧
        (n - iw').toNat < 136) := by
  induction k generalizing s iw with
  | zero =>
    dsimp only at hnt hor ⊢
    rw [evaluateHOLFiniteState_while_total] at hnt hor ⊢
    rcases hc_ev : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 136])) with _ | cv
    · simp only [hc_ev] at hor ⊢; exact ⟨ByteEff.refl s _, by simp⟩
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try (simp only [hc_ev] at hor ⊢; exact ⟨ByteEff.refl s _, by simp⟩)
      simp only [hc_ev] at hnt hor ⊢
      by_cases hnz : cw ≠ 0
      · have hz : s.clock = 0 := by omega
        rw [if_pos hnz, if_pos hz] at hnt
        exact absurd rfl hnt
      · have hcw0 : cw = 0 := Classical.not_not.1 hnz
        subst hcw0
        rw [if_neg (by simp)]
        refine ⟨ByteEff.refl s _, fun _ => ⟨fun _ _ => rfl, iw, hi, ?_⟩⟩
        have hcw_eq := eval_cmp_notLower_i136 s n iw 0 hn hi hc_ev
        have hnlt := n.isLt; have hilt := iw.isLt
        have hsub : (n - iw).toNat = n.toNat - iw.toNat := by rw [BitVec.toNat_sub]; omega
        by_cases hlt136 : (iw + 136).toNat ≤ n.toNat
        · rw [if_pos hlt136] at hcw_eq; cases hcw_eq
        · by_cases hwrap : iw.toNat + 136 < 2 ^ 64
          · have : (iw + 136).toNat = iw.toNat + 136 := BitVec.toNat_add_of_lt hwrap
            omega
          · omega
  | succ k ih =>
    dsimp only at hnt hor ⊢
    rw [evaluateHOLFiniteState_while_total] at hnt hor ⊢
    rcases hc_ev : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 136])) with _ | cv
    · simp only [hc_ev] at hor ⊢; exact ⟨ByteEff.refl s _, by simp⟩
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try (simp only [hc_ev] at hor ⊢; exact ⟨ByteEff.refl s _, by simp⟩)
      simp only [hc_ev] at hnt hor ⊢
      by_cases hnz : cw ≠ 0
      · rw [if_pos hnz] at hnt hor ⊢
        by_cases hz : s.clock = 0
        · rw [if_pos hz] at hnt; exact absurd rfl hnt
        · rw [if_neg hz] at hnt hor ⊢
          rw [fixClockHOLFinite_evaluateState] at hnt hor ⊢
          have hik_le : (iw + 136).toNat ≤ n.toNat := by
            have hcw_eq := eval_cmp_notLower_i136 s n iw cw hn hi hc_ev
            by_cases hle' : (iw + 136).toNat ≤ n.toNat
            · exact hle'
            · rw [if_neg hle'] at hcw_eq; exact absurd hcw_eq hnz
          let sd := decClockHOLFinite s
          have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
          rw [evaluateHOLFiniteState_seq_line780] at hnt hor ⊢
          rcases hcall : evaluateHOLFiniteState (decClockHOLFinite s)
              (.call (some (none, none)) (ofString "keccak_absorb_block")
                [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]]) with ⟨rc, m1⟩
          have hnt' := hnt; have hor' := hor
          rw [hcall] at hnt' hor'
          have hnt_c : rc ≠ some .timeOut := by
            intro h; subst h; simp at hnt'
          have hnbc := call0_ne_break_continue (decClockHOLFinite s) (ofString "keccak_absorb_block")
            [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]]
          rw [hcall] at hnbc
          have hor_c : rc = none ∨ Resumes rc := by
            cases rc with
            | none => exact Or.inl rfl
            | some rc' =>
              cases rc' with
              | returned v => exact Or.inr (Or.inl ⟨v, rfl⟩)
              | exception e v =>
                rcases hor' with h | ⟨_, h⟩ | ⟨e', v', h, hne⟩
                · simp at h
                · simp at h
                · simp at h; obtain ⟨rfl, _⟩ := h; exact Or.inr (Or.inr ⟨e, v, rfl, hne⟩)
              | «break» => exact absurd rfl hnbc.1
              | «continue» => exact absurd rfl hnbc.2
              | error | timeOut | finalFfi _ =>
                exfalso; rcases hor' with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
          have hargs_c : evalListHOLFinite sd (h := fun a => Classical.propDecidable (sd.memaddrs a))
              [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]] =
              some [.val (.word stp), .val (.word (p + iw))] := by
            simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, sd, decClockHOLFinite, hstp, hp, hi,
              valueIsWord, valueWord, wordOpHOL, wordOp]
          have heff_c : ByteEff sd m1 [(stp.toNat, 200)] := by
            have := call0_byteEff funByteEff_keccak_absorb_block sd _ [(stp.toNat, 200)] hc hGd
              (fun vs hvs i hi_in _ => by
                rw [hargs_c] at hvs; injection hvs with hvs; subst hvs
                simp [valWordNat] at hi_in; subst hi_in
                exact ⟨(stp.toNat, 200), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
              (by dsimp only [sd]; rw [hcall]; exact hnt_c)
              (by dsimp only [sd]; rw [hcall]; exact hor_c)
            dsimp only [sd] at this; rwa [hcall] at this
          have hclk_c := evaluateHOLFiniteState_clock_le (decClockHOLFinite s)
            (.call (some (none, none)) (ofString "keccak_absorb_block")
              [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
          rw [hcall] at hclk_c
          cases rc with
          | some rc' =>
            cases rc' with
            | «break» => exact absurd rfl hnbc.1
            | «continue» => exact absurd rfl hnbc.2
            | _ => exact ⟨((ByteEff.refl s _).locals_clock _ _).trans heff_c, by simp⟩
          | none =>
            have hloc_m1 : m1.locals = sd.locals := by
              have := call0_any_locals (decClockHOLFinite s) (ofString "keccak_absorb_block")
                [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]]
                (by rw [hcall])
              rwa [hcall] at this
            dsimp only at hnt' hor' ⊢
            have hi_m1 : m1.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hloc_m1]; exact hi
            have hasgn : evaluateHOLFiniteState m1
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 136])) =
                (none, setVarHOLFinite (ofString "i") (.val (.word (iw + 136))) m1) := by
              simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hi_m1, wordOpHOL, wordOp,
                valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
                shapeOfHOLExact, shapeEqHOL]
            rw [hasgn] at hnt' hor' ⊢
            dsimp only at hnt' hor' ⊢
            let m2 := setVarHOLFinite (ofString "i") (.val (.word (iw + 136))) m1
            have heff_m2 : ByteEff s m2 [(stp.toNat, 200)] :=
              (((ByteEff.refl s _).locals_clock _ _).trans heff_c).locals_clock _ _
            have hGm2 : GuestInv m2 := guestInv_congr heff_m2.code heff_m2.memaddrs heff_m2.shMemaddrs heff_m2.baseAddr hG
            have hm2_other : ∀ v, v ≠ ofString "i" → m2.locals.lookup v = s.locals.lookup v := by
              intro v hv
              have hv' : (ofString "i" == v) = false := beq_eq_false_iff_ne.2 (Ne.symm hv)
              simp only [m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hv',
                Bool.false_eq_true, ↓reduceIte, hloc_m1]
              rfl
            have hi_m2 : m2.locals.lookup (ofString "i") = some (.val (.word (iw + 136))) := by
              simp [m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have hm2_clk : m2.clock ≤ k := by change m1.clock ≤ k; change m1.clock ≤ s.clock - 1 at hclk_c; omega
            have ih_res := ih m2 (iw + 136) hm2_clk (heff_m2.code.trans hc) hGm2
              (by rw [hm2_other _ (by decide)]; exact hstp)
              (by rw [hm2_other _ (by decide)]; exact hp)
              (by rw [hm2_other _ (by decide)]; exact hn)
              hi_m2 hik_le hnt' hor'
            refine ⟨heff_m2.trans ih_res.1, fun hnone => ?_⟩
            obtain ⟨ho, hr⟩ := ih_res.2 hnone
            exact ⟨fun v hv => (ho v hv).trans (hm2_other v hv), hr⟩
      · have hcw0 : cw = 0 := Classical.not_not.1 hnz
        subst hcw0
        rw [if_neg (by simp)]
        refine ⟨ByteEff.refl s _, fun _ => ⟨fun _ _ => rfl, iw, hi, ?_⟩⟩
        have hcw_eq := eval_cmp_notLower_i136 s n iw 0 hn hi hc_ev
        have hnlt := n.isLt; have hilt := iw.isLt
        have hsub : (n - iw).toNat = n.toNat - iw.toNat := by rw [BitVec.toNat_sub]; omega
        by_cases hlt136 : (iw + 136).toNat ≤ n.toNat
        · rw [if_pos hlt136] at hcw_eq; cases hcw_eq
        · by_cases hwrap : iw.toNat + 136 < 2 ^ 64
          · have : (iw + 136).toNat = iw.toNat + 136 := BitVec.toNat_add_of_lt hwrap
            omega
          · omega

theorem call0_two_word_resumes {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname p1 p2 : MlS) (body : ProgHOL 64) (a1 a2 : ExpHOL 64) (w1 w2 : BitVec 64)
    (hne : p1 ≠ p2)
    (hc : s.code = originalRuntimeCode)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one)], body, .one))
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [a1, a2] =
      some [.val (.word w1), .val (.word w2)])
    (hor : (evaluateHOLFiniteState s (.call (some (none, none)) fname [a1, a2])).1 = none ∨
      Resumes (evaluateHOLFiniteState s (.call (some (none, none)) fname [a1, a2])).1) :
    Resumes (evaluateHOLFiniteState
      (callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2))))
      body).1 := by
  rw [evaluateHOLFiniteState_call, ha] at hor
  dsimp only at hor
  have hl := pan_two_word_lookup s.code.lookup fname p1 p2 body w1 w2 hne (by rw [hc]; exact hlook)
  rw [hl] at hor; dsimp only at hor
  split at hor
  · rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
  · rcases hb : evaluateHOLFiniteState
        (callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2))))
        body with ⟨rb, pb⟩
    rw [hb] at hor ⊢
    cases rb with
    | none => rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
    | some rb' =>
      cases rb' with
      | returned rv => exact Or.inl ⟨rv, rfl⟩
      | exception eid ev =>
        rcases hor with h | ⟨_, h⟩ | ⟨e', v', h, hne_t⟩
        · simp at h
        · simp at h
        · simp at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨eid, ev, rfl, hne_t⟩
      | _ => rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h

private theorem keccak_out_ite_eff {F : Type}
    (s : PanSemStateFiniteExact 64 F) (out stp : BitVec 64) (Rl : List Ivl)
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hout : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (hstp : s.locals.lookup (ofString "stp") = some (.val (.word stp)))
    (hout_in : ∀ i ∈ [(out.toNat, 32)], 0 < i.2 → ∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2)
    (hnt : (evaluateHOLFiniteState s
      (.ite (.cmp .equal (.op .and [.var .local (ofString "out"), .const 7]) (.const 0))
        (.seq (.store (.var .local (ofString "out")) (.load .one (.var .local (ofString "stp"))))
          (.seq (.store (.op .add [.var .local (ofString "out"), .const 8])
              (.load .one (.op .add [.var .local (ofString "stp"), .const 8])))
            (.seq (.store (.op .add [.var .local (ofString "out"), .const 16])
                (.load .one (.op .add [.var .local (ofString "stp"), .const 16])))
              (.store (.op .add [.var .local (ofString "out"), .const 24])
                (.load .one (.op .add [.var .local (ofString "stp"), .const 24]))))))
        (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "out"), .var .local (ofString "stp"), .const 32]))).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState s
      (.ite (.cmp .equal (.op .and [.var .local (ofString "out"), .const 7]) (.const 0))
        (.seq (.store (.var .local (ofString "out")) (.load .one (.var .local (ofString "stp"))))
          (.seq (.store (.op .add [.var .local (ofString "out"), .const 8])
              (.load .one (.op .add [.var .local (ofString "stp"), .const 8])))
            (.seq (.store (.op .add [.var .local (ofString "out"), .const 16])
                (.load .one (.op .add [.var .local (ofString "stp"), .const 16])))
              (.store (.op .add [.var .local (ofString "out"), .const 24])
                (.load .one (.op .add [.var .local (ofString "stp"), .const 24]))))))
        (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "out"), .var .local (ofString "stp"), .const 32]))).1 = none ∨
      Resumes (evaluateHOLFiniteState s
        (.ite (.cmp .equal (.op .and [.var .local (ofString "out"), .const 7]) (.const 0))
          (.seq (.store (.var .local (ofString "out")) (.load .one (.var .local (ofString "stp"))))
            (.seq (.store (.op .add [.var .local (ofString "out"), .const 8])
                (.load .one (.op .add [.var .local (ofString "stp"), .const 8])))
              (.seq (.store (.op .add [.var .local (ofString "out"), .const 16])
                  (.load .one (.op .add [.var .local (ofString "stp"), .const 16])))
                (.store (.op .add [.var .local (ofString "out"), .const 24])
                  (.load .one (.op .add [.var .local (ofString "stp"), .const 24]))))))
          (.call (some (none, none)) (ofString "memcpy")
            [.var .local (ofString "out"), .var .local (ofString "stp"), .const 32]))).1) :
    ByteEff s (evaluateHOLFiniteState s
      (.ite (.cmp .equal (.op .and [.var .local (ofString "out"), .const 7]) (.const 0))
        (.seq (.store (.var .local (ofString "out")) (.load .one (.var .local (ofString "stp"))))
          (.seq (.store (.op .add [.var .local (ofString "out"), .const 8])
              (.load .one (.op .add [.var .local (ofString "stp"), .const 8])))
            (.seq (.store (.op .add [.var .local (ofString "out"), .const 16])
                (.load .one (.op .add [.var .local (ofString "stp"), .const 16])))
              (.store (.op .add [.var .local (ofString "out"), .const 24])
                (.load .one (.op .add [.var .local (ofString "stp"), .const 24]))))))
        (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "out"), .var .local (ofString "stp"), .const 32]))).2 Rl := by
  rw [evaluateHOLFiniteState_ite] at hnt hor ⊢
  rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.op .and [.var .local (ofString "out"), .const 7]) (.const 0)) with _ | cv
  · exact ByteEff.refl s Rl
  · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try exact ByteEff.refl s Rl
    have hnt' := hnt; have hor' := hor
    rw [hev] at hnt' hor'
    dsimp only at hnt' hor' ⊢
    by_cases h0 : cw = 0
    · rw [if_pos h0] at hnt' hor' ⊢
      have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
          [.var .local (ofString "out"), .var .local (ofString "stp"), .const 32] =
          some [.val (.word out), .val (.word stp), .val (.word 32)] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hout, hstp]
      exact call0_byteEff funByteEff_memcpy s _ Rl hc hG
        (fun vs hvs i hi hp => by
          rw [hargs] at hvs; injection hvs with hvs; subst hvs
          simp [valWordNat] at hi; subst hi
          exact hout_in (out.toNat, 32) (List.mem_singleton.2 rfl) hp)
        hnt' hor'
    · rw [if_neg h0]
      exact (checkWordStoresLocal_sound (ofString "out") 32 (by omega) [] _ rfl s out hc hG hout
        (fun _ h => by simp at h)).1.mono hout_in

theorem funByteEff_keccak256 :
    FunByteEff (ofString "keccak256")
      (fun vals G =>
        [globBufIvl G "keccak_st" 200, globBufIvl G "keccak_pad" 136,
         (valWordNat (vals[2]?.getD (.rStruct [])), 32)]) := by
  have hlook : originalRuntimeCode.lookup (ofString "keccak256") =
      some ([(ofString "p", .one), (ofString "n", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_keccak256, .one) :=
    lookup_of_guestAst_getElem 103 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_keccak256) rfl
  have hlook_mz : originalRuntimeCode.lookup (ofString "memzero") =
      some ([(ofString "dst", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memzero, .one) := lookup_memzero
  refine ⟨_, _, _, hlook, fun {F} entry vals hc hG hl hnt hres => ?_⟩
  obtain ⟨p, n, out, rfl, hp0, hn0, hout0⟩ :=
    lookupCode_three_words (by decide) (by decide) (by decide) hlook hl
  let Rl := [globBufIvl entry.globals "keccak_st" 200,
    globBufIvl entry.globals "keccak_pad" 136, (out.toNat, 32)]
  change ByteEff entry (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_keccak256)).2 Rl
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  have seq_step : ∀ (t : PanSemStateFiniteExact 64 F) (a b : ProgHOL 64),
      (evaluateHOLFiniteState t (.seq a b)).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState t (.seq a b)).1 = none ∨ Resumes (evaluateHOLFiniteState t (.seq a b)).1) →
      (evaluateHOLFiniteState t a).1 ≠ some .timeOut ∧
      ((evaluateHOLFiniteState t a).1 = none ∨ Resumes (evaluateHOLFiniteState t a).1) := by
    intro t a b h1 h2
    rw [evaluateHOLFiniteState_seq_line780] at h1 h2
    rcases ha : evaluateHOLFiniteState t a with ⟨ra, ma⟩
    rw [ha] at h1 h2
    refine ⟨fun h => by subst h; simp at h1, ?_⟩
    cases ra with
    | none => exact Or.inl rfl
    | some _ =>
      right
      rcases h2 with h | h
      · simp at h
      · exact h
  -- Unfold outer `dec "stp"`
  have hbody : sourceFnBody Guest.Software.guestFn_keccak256 =
      .dec (ofString "stp") .one (.var .global (ofString "keccak_st"))
        (.seq (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "stp"), .const 200])
          (.dec (ofString "i") .one (.const 0)
            (.seq (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 136]))
                (.seq (.call (some (none, none)) (ofString "keccak_absorb_block")
                    [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
                  (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 136]))))
              (.dec (ofString "rem") .one (.op .sub [.var .local (ofString "n"), .var .local (ofString "i")])
                (.seq (.call (some (none, none)) (ofString "memzero") [.var .global (ofString "keccak_pad"), .const 136])
                  (.seq (.call (some (none, none)) (ofString "memcpy")
                      [.var .global (ofString "keccak_pad"),
                       .op .add [.var .local (ofString "p"), .var .local (ofString "i")],
                       .var .local (ofString "rem")])
                    (.seq (.storeByte (.op .add [.var .global (ofString "keccak_pad"), .var .local (ofString "rem")]) (.const 1))
                      (.seq (.storeByte (.op .add [.var .global (ofString "keccak_pad"), .const 135])
                          (.op .or [.loadByte (.op .add [.var .global (ofString "keccak_pad"), .const 135]), .const 128]))
                        (.seq (.call (some (none, none)) (ofString "keccak_absorb_block")
                            [.var .local (ofString "stp"), .var .global (ofString "keccak_pad")])
                          (.seq (.ite (.cmp .equal (.op .and [.var .local (ofString "out"), .const 7]) (.const 0))
                              (.seq (.store (.var .local (ofString "out")) (.load .one (.var .local (ofString "stp"))))
                                (.seq (.store (.op .add [.var .local (ofString "out"), .const 8])
                                    (.load .one (.op .add [.var .local (ofString "stp"), .const 8])))
                                  (.seq (.store (.op .add [.var .local (ofString "out"), .const 16])
                                      (.load .one (.op .add [.var .local (ofString "stp"), .const 16])))
                                    (.store (.op .add [.var .local (ofString "out"), .const 24])
                                      (.load .one (.op .add [.var .local (ofString "stp"), .const 24]))))))
                              (.call (some (none, none)) (ofString "memcpy")
                                [.var .local (ofString "out"), .var .local (ofString "stp"), .const 32]))
                            (.return (.const 0)))))))))))) := rfl
  rw [hbody] at hnt hres ⊢
  rw [evaluateHOLFiniteState_dec_total] at hnt hres ⊢
  dsimp only at hnt hres ⊢
  rcases hgst : entry.globals.lookup (ofString "keccak_st") with _ | vst
  · simp only [evalHOLExact, hgst]; exact ByteEff.refl entry Rl
  · rcases vst with ⟨⟨stp⟩⟩ | _ | _ <;>
      try (simp only [evalHOLExact, hgst, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hres ⊢
           exact ByteEff.refl entry Rl)
    simp only [evalHOLExact, hgst, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt hres ⊢
    have hsb_pos : 0 < sourceBase := by rw [sourceBase_val]; decide
    let s0 := setVarHOLFinite (ofString "stp") (.val (.word stp)) entry
    have hGs0 : GuestInv s0 := guestInv_setVar _ _ entry hG
    have hstp_0 : s0.locals.lookup (ofString "stp") = some (.val (.word stp)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hp_0 : s0.locals.lookup (ofString "p") = some (.val (.word p)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp0, show ofString "stp" ≠ ofString "p" by decide]
    have hn_0 : s0.locals.lookup (ofString "n") = some (.val (.word n)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn0, show ofString "stp" ≠ ofString "n" by decide]
    have hout_0 : s0.locals.lookup (ofString "out") = some (.val (.word out)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hout0, show ofString "stp" ≠ ofString "out" by decide]
    -- Step 1: `memzero(stp, 200)`
    obtain ⟨hnt1, hor1⟩ := seq_step s0 _ _ hnt (Or.inr hres)
    have hargs1 : evalListHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
        [.var .local (ofString "stp"), .const 200] = some [.val (.word stp), .val (.word 200)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hstp_0]
    have hres_mz1 := call0_two_word_resumes s0 _ _ _ _ _ _ stp 200 (by decide) hc hlook_mz hargs1 hor1
    let c0 := callEntryStateHOLFinite s0
      ((HolFiniteMapExact.empty.update (ofString "dst", .val (.word stp))).update (ofString "n", .val (.word 200)))
    have hstp_dom := (memzero_body_eff c0 stp 200 hc (guestInv_callEntry s0 _ hGs0)
      (by simp [c0, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "n" ≠ ofString "dst" by decide])
      (by simp [c0, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      hres_mz1).2 (by decide)
    have hstp_nz : stp.toNat ≠ 0 := by omega
    have hstp_sub : ∀ i ∈ [(stp.toNat, 200)], 0 < i.2 → ∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2 := by
      intro i hi _
      simp at hi; subst hi
      refine ⟨globBufIvl entry.globals "keccak_st" 200, List.mem_cons_self, ?_, ?_⟩ <;>
        simp [globBufIvl, globMapN, hgst, hstp_nz]
    rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
    rcases hm1 : evaluateHOLFiniteState s0
        (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "stp"), .const 200]) with ⟨r1, s1⟩
    rw [hm1] at hnt hres
    have heff1 : ByteEff s0 s1 Rl := by
      have := call0_byteEff funByteEff_memzero s0 _ Rl hc hGs0
        (fun vs hvs i hi hp => by
          rw [hargs1] at hvs; injection hvs with hvs; subst hvs
          simp [valWordNat] at hi; subst hi
          exact hstp_sub (stp.toNat, 200) (List.mem_singleton.2 rfl) hp)
        hnt1 hor1
      rwa [hm1] at this
    have heff_e1 : ByteEff entry s1 Rl := ((ByteEff.refl entry Rl).locals_clock _ _).trans heff1
    cases r1 with
    | some _ => exact heff_e1.locals_clock _ _
    | none =>
      have hs1_loc : s1.locals = s0.locals := by
        have := call0_any_locals s0 _ _ (by rw [hm1])
        rwa [hm1] at this
      have hGs1 : GuestInv s1 := guestInv_congr heff_e1.code heff_e1.memaddrs heff_e1.shMemaddrs heff_e1.baseAddr hG
      have hc_s1 : s1.code = originalRuntimeCode := heff_e1.code.trans hc
      -- Step 2: `dec "i" 0`
      dsimp only at hnt hres ⊢
      rw [evaluateHOLFiniteState_dec_total] at hnt hres ⊢
      simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt hres ⊢
      let s2 := setVarHOLFinite (ofString "i") (.val (.word 0)) s1
      have hGs2 : GuestInv s2 := guestInv_setVar _ _ s1 hGs1
      have hstp_2 : s2.locals.lookup (ofString "stp") = some (.val (.word stp)) := by
        simp only [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "stp" by decide, ↓reduceIte, hs1_loc]; exact hstp_0
      have hp_2 : s2.locals.lookup (ofString "p") = some (.val (.word p)) := by
        simp only [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "p" by decide, ↓reduceIte, hs1_loc]; exact hp_0
      have hn_2 : s2.locals.lookup (ofString "n") = some (.val (.word n)) := by
        simp only [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "n" by decide, ↓reduceIte, hs1_loc]; exact hn_0
      have hout_2 : s2.locals.lookup (ofString "out") = some (.val (.word out)) := by
        simp only [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "out" by decide, ↓reduceIte, hs1_loc]; exact hout_0
      have hi_2 : s2.locals.lookup (ofString "i") = some (.val (.word 0)) := by
        simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      -- Step 3: `while (n >=u i + 136)`
      obtain ⟨hnt_w, hor_w⟩ := seq_step s2 _ _ hnt (Or.inr hres)
      have hw_eff := keccak_main_loop_eff s2.clock s2 stp p n 0 le_rfl hc_s1 hGs2
        hstp_2 hp_2 hn_2 hi_2 (Nat.zero_le _) hnt_w hor_w
      rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
      rcases hw : evaluateHOLFiniteState s2 _ with ⟨rw_res, s3⟩
      rw [hw] at hnt hres hw_eff
      have heff_e3 : ByteEff entry s3 Rl :=
        (heff_e1.locals_clock _ _).trans (hw_eff.1.mono hstp_sub)
      cases rw_res with
      | some _ => exact (heff_e3.locals_clock _ _).locals_clock _ _
      | none =>
        obtain ⟨hs3_other, iw, hi_3, hrem_lt⟩ := hw_eff.2 rfl
        have hGs3 : GuestInv s3 := guestInv_congr heff_e3.code heff_e3.memaddrs heff_e3.shMemaddrs heff_e3.baseAddr hG
        have hc_s3 : s3.code = originalRuntimeCode := heff_e3.code.trans hc
        have hglob_s3 : s3.globals = entry.globals := heff_e3.globals
        have hstp_3 : s3.locals.lookup (ofString "stp") = some (.val (.word stp)) := by
          rw [hs3_other _ (by decide)]; exact hstp_2
        have hp_3 : s3.locals.lookup (ofString "p") = some (.val (.word p)) := by
          rw [hs3_other _ (by decide)]; exact hp_2
        have hn_3 : s3.locals.lookup (ofString "n") = some (.val (.word n)) := by
          rw [hs3_other _ (by decide)]; exact hn_2
        have hout_3 : s3.locals.lookup (ofString "out") = some (.val (.word out)) := by
          rw [hs3_other _ (by decide)]; exact hout_2
        -- Step 4: `dec "rem" (n - i)`
        dsimp only at hnt hres ⊢
        rw [evaluateHOLFiniteState_dec_total] at hnt hres ⊢
        have hi_3' : s3.locals.lookup (ofString "i") = some (.val (.word iw)) := hi_3
        have hev_rem : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
            (.op .sub [.var .local (ofString "n"), .var .local (ofString "i")]) = some (.val (.word (n - iw))) := by
          simp [evalHOLExact, evalListHOLExact, hn_3, hi_3', valueIsWord, valueWord, wordOpHOL, wordOp]
        simp only [hev_rem, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt hres ⊢
        let remw := n - iw
        let s4 := setVarHOLFinite (ofString "rem") (.val (.word remw)) s3
        have hGs4 : GuestInv s4 := guestInv_setVar _ _ s3 hGs3
        have hstp_4 : s4.locals.lookup (ofString "stp") = some (.val (.word stp)) := by
          simp only [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "rem" ≠ ofString "stp" by decide, ↓reduceIte]; exact hstp_3
        have hp_4 : s4.locals.lookup (ofString "p") = some (.val (.word p)) := by
          simp only [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "rem" ≠ ofString "p" by decide, ↓reduceIte]; exact hp_3
        have hi_4 : s4.locals.lookup (ofString "i") = some (.val (.word iw)) := by
          simp only [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "rem" ≠ ofString "i" by decide, ↓reduceIte]; exact hi_3'
        have hout_4 : s4.locals.lookup (ofString "out") = some (.val (.word out)) := by
          simp only [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "rem" ≠ ofString "out" by decide, ↓reduceIte]; exact hout_3
        have hrem_4 : s4.locals.lookup (ofString "rem") = some (.val (.word remw)) := by
          simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        -- Step 5: `memzero(keccak_pad, 136)`
        obtain ⟨hnt_p1, hor_p1⟩ := seq_step s4 _ _ hnt (Or.inr hres)
        have hnot_err : ∀ r, r = some .error → ¬ (r = none ∨ Resumes r) := by
          rintro _ rfl (h | ⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h
        rcases hgpad : entry.globals.lookup (ofString "keccak_pad") with _ | vpad
        · exfalso
          apply hnot_err _ _ hor_p1
          rw [evaluateHOLFiniteState_call]
          have hgpad4 : s4.globals.lookup (ofString "keccak_pad") = none := by
            change s3.globals.lookup _ = none; rw [hglob_s3]; exact hgpad
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hgpad4]
        · have hpad_w : ∃ pad : BitVec 64, vpad = .val (.word pad) := by
            by_cases hsh1 : shapeEqHOL .one (shapeOfHOLExact vpad) = true
            · cases vpad with
              | val wlab =>
                cases wlab with
                | word pad => exact ⟨pad, rfl⟩
              | rStruct _ => simp [shapeOfHOLExact, shapeEqHOL] at hsh1
              | nStruct _ _ => simp [shapeOfHOLExact, shapeEqHOL] at hsh1
            · exfalso
              apply hnot_err _ _ hor_p1
              rw [evaluateHOLFiniteState_call]
              have hgpad4 : s4.globals.lookup (ofString "keccak_pad") = some vpad := by
                change s3.globals.lookup _ = _; rw [hglob_s3]; exact hgpad
              have hargs_bad : evalListHOLFinite s4 (h := fun a => Classical.propDecidable (s4.memaddrs a))
                  [.var .global (ofString "keccak_pad"), .const 136] =
                  some [vpad, .val (.word 136)] := by
                simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hgpad4]
              rw [hargs_bad]; dsimp only
              have hl_bad : lookupCodeHOLFinite s4.code.lookup (ofString "memzero") [vpad, .val (.word 136)] = none := by
                apply Option.eq_none_iff_forall_not_mem.2
                intro ⟨b, c, r⟩ hmem
                have hx := lookupCodeHOLFinite_eq_some s4.code.lookup _ _ b c r hmem
                have hc4 : s4.code = originalRuntimeCode := hc_s3
                rw [hc4] at hx
                simp [lookupCodeHOLExact, hlook_mz] at hx
                exact hsh1 hx.1.2.1
              rw [hl_bad]
          obtain ⟨pad, rfl⟩ := hpad_w
          have hgpad4 : s4.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) := by
            change s3.globals.lookup _ = _; rw [hglob_s3]; exact hgpad
          have hargs_p1 : evalListHOLFinite s4 (h := fun a => Classical.propDecidable (s4.memaddrs a))
              [.var .global (ofString "keccak_pad"), .const 136] = some [.val (.word pad), .val (.word 136)] := by
            simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hgpad4]
          have hres_p1 := call0_two_word_resumes s4 _ _ _ _ _ _ pad 136 (by decide) hc_s3 hlook_mz hargs_p1 hor_p1
          let cp1 := callEntryStateHOLFinite s4
            ((HolFiniteMapExact.empty.update (ofString "dst", .val (.word pad))).update (ofString "n", .val (.word 136)))
          have hpad_dom := (memzero_body_eff cp1 pad 136 hc_s3 (guestInv_callEntry s4 _ hGs4)
            (by simp [cp1, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "n" ≠ ofString "dst" by decide])
            (by simp [cp1, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
            hres_p1).2 (by decide)
          have hpad_nz : pad.toNat ≠ 0 := by omega
          have hpad_sub : ∀ i ∈ [(pad.toNat, 136)], 0 < i.2 → ∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2 := by
            intro i hi _
            simp at hi; subst hi
            refine ⟨globBufIvl entry.globals "keccak_pad" 136, List.mem_cons_of_mem _ List.mem_cons_self, ?_, ?_⟩ <;>
              simp [globBufIvl, globMapN, hgpad, hpad_nz]
          have hpad_in : 0 < 136 → ∃ i ∈ Rl, i.1 ≤ pad.toNat ∧ pad.toNat + 136 ≤ i.1 + i.2 :=
            fun hp => hpad_sub (pad.toNat, 136) (List.mem_singleton.2 rfl) hp
          rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
          rcases hmp1 : evaluateHOLFiniteState s4
              (.call (some (none, none)) (ofString "memzero") [.var .global (ofString "keccak_pad"), .const 136]) with ⟨rp1, s5⟩
          rw [hmp1] at hnt hres
          have heff_p1 : ByteEff s4 s5 Rl := by
            have := call0_byteEff funByteEff_memzero s4 _ Rl hc_s3 hGs4
              (fun vs hvs i hi hp => by
                rw [hargs_p1] at hvs; injection hvs with hvs; subst hvs
                simp [valWordNat] at hi; subst hi
                exact hpad_sub (pad.toNat, 136) (List.mem_singleton.2 rfl) hp)
              hnt_p1 hor_p1
            rwa [hmp1] at this
          have heff_e5 : ByteEff entry s5 Rl := (heff_e3.locals_clock _ _).trans heff_p1
          cases rp1 with
          | some _ => exact ((heff_e5.locals_clock _ _).locals_clock _ _).locals_clock _ _
          | none =>
            have hs5_loc : s5.locals = s4.locals := by
              have := call0_any_locals s4 _ _ (by rw [hmp1]); rwa [hmp1] at this
            have hGs5 : GuestInv s5 := guestInv_congr heff_e5.code heff_e5.memaddrs heff_e5.shMemaddrs heff_e5.baseAddr hG
            have hc_s5 : s5.code = originalRuntimeCode := heff_e5.code.trans hc
            have hgpad5 : s5.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) := by
              rw [heff_e5.globals]; exact hgpad
            -- Step 6: `memcpy(keccak_pad, p + i, rem)`
            dsimp only at hnt hres ⊢
            obtain ⟨hnt_mc, hor_mc⟩ := seq_step s5 _ _ hnt (Or.inr hres)
            have hargs_mc : evalListHOLFinite s5 (h := fun a => Classical.propDecidable (s5.memaddrs a))
                [.var .global (ofString "keccak_pad"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")],
                 .var .local (ofString "rem")] =
                some [.val (.word pad), .val (.word (p + iw)), .val (.word remw)] := by
              simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hgpad5, hs5_loc, hp_4, hi_4, hrem_4,
                valueIsWord, valueWord, wordOpHOL, wordOp]
            rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
            rcases hmc : evaluateHOLFiniteState s5
                (.call (some (none, none)) (ofString "memcpy")
                  [.var .global (ofString "keccak_pad"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")],
                   .var .local (ofString "rem")]) with ⟨rmc, s6⟩
            rw [hmc] at hnt hres
            have heff_mc : ByteEff s5 s6 Rl := by
              have := call0_byteEff funByteEff_memcpy s5 _ Rl hc_s5 hGs5
                (fun vs hvs i hi hp => by
                  rw [hargs_mc] at hvs; injection hvs with hvs; subst hvs
                  simp [valWordNat] at hi; subst hi
                  refine ⟨globBufIvl entry.globals "keccak_pad" 136, List.mem_cons_of_mem _ List.mem_cons_self, ?_, ?_⟩
                  · simp [globBufIvl, globMapN, hgpad, hpad_nz]
                  · simp only [globBufIvl, globMapN, hgpad, hpad_nz, ↓reduceIte]
                    change pad.toNat + (n - iw).toNat ≤ pad.toNat + 136; omega)
                hnt_mc hor_mc
              rwa [hmc] at this
            have heff_e6 : ByteEff entry s6 Rl := heff_e5.trans heff_mc
            cases rmc with
            | some _ => exact ((heff_e6.locals_clock _ _).locals_clock _ _).locals_clock _ _
            | none =>
              have hs6_loc : s6.locals = s4.locals := by
                have := call0_any_locals s5 _ _ (by rw [hmc]); rw [hmc] at this; exact this.trans hs5_loc
              have hGs6 : GuestInv s6 := guestInv_congr heff_e6.code heff_e6.memaddrs heff_e6.shMemaddrs heff_e6.baseAddr hG
              have hgpad6 : s6.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) := by
                rw [heff_e6.globals]; exact hgpad
              -- Step 7: `storeByte(keccak_pad + rem, 1)`
              dsimp only at hnt hres ⊢
              rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
              have hev_sb1 : @evalHOLExact 64 F _ s6.toExact (fun a => Classical.propDecidable (s6.memaddrs a))
                  (.op .add [.var .global (ofString "keccak_pad"), .var .local (ofString "rem")]) =
                  some (.val (.word (pad + BitVec.ofNat 64 remw.toNat))) := by
                simp [evalHOLExact, evalListHOLExact, hgpad6, hs6_loc, hrem_4, valueIsWord, valueWord, wordOpHOL, wordOp]
              have heff_sb1 : ByteEff s6 (evaluateHOLFiniteState s6
                  (.storeByte (.op .add [.var .global (ofString "keccak_pad"), .var .local (ofString "rem")]) (.const 1))).2 Rl :=
                byteEff_storeByte_at hGs6 _ _ pad remw.toNat 136 hpad_dom.2 hpad_in hrem_lt hev_sb1
              rcases hsb1 : evaluateHOLFiniteState s6
                  (.storeByte (.op .add [.var .global (ofString "keccak_pad"), .var .local (ofString "rem")]) (.const 1)) with ⟨rsb1, s7⟩
              rw [hsb1] at hnt hres heff_sb1
              have heff_e7 : ByteEff entry s7 Rl := heff_e6.trans heff_sb1
              cases rsb1 with
              | some _ => exact ((heff_e7.locals_clock _ _).locals_clock _ _).locals_clock _ _
              | none =>
                have hs7_loc : s7.locals = s4.locals := by
                  have := (evaluate_storeByte_control_frame s6
                    (.op .add [.var .global (ofString "keccak_pad"), .var .local (ofString "rem")]) (.const 1)).2.2.1
                  rw [hsb1] at this; exact this.trans hs6_loc
                have hGs7 : GuestInv s7 := guestInv_congr heff_e7.code heff_e7.memaddrs heff_e7.shMemaddrs heff_e7.baseAddr hG
                have hgpad7 : s7.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) := by
                  rw [heff_e7.globals]; exact hgpad
                -- Step 8: `storeByte(keccak_pad + 135, ...)`
                dsimp only at hnt hres ⊢
                rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
                have hev_sb2 : @evalHOLExact 64 F _ s7.toExact (fun a => Classical.propDecidable (s7.memaddrs a))
                    (.op .add [.var .global (ofString "keccak_pad"), .const 135]) =
                    some (.val (.word (pad + 135))) := by
                  simp [evalHOLExact, evalListHOLExact, hgpad7, valueIsWord, valueWord, wordOpHOL, wordOp]
                have heff_sb2 : ByteEff s7 (evaluateHOLFiniteState s7
                    (.storeByte (.op .add [.var .global (ofString "keccak_pad"), .const 135])
                      (.op .or [.loadByte (.op .add [.var .global (ofString "keccak_pad"), .const 135]), .const 128]))).2 Rl :=
                  byteEff_storeByte_at hGs7 _ _ pad 135 136 hpad_dom.2 hpad_in (by decide) hev_sb2
                rcases hsb2 : evaluateHOLFiniteState s7
                    (.storeByte (.op .add [.var .global (ofString "keccak_pad"), .const 135])
                      (.op .or [.loadByte (.op .add [.var .global (ofString "keccak_pad"), .const 135]), .const 128])) with ⟨rsb2, s8⟩
                rw [hsb2] at hnt hres heff_sb2
                have heff_e8 : ByteEff entry s8 Rl := heff_e7.trans heff_sb2
                cases rsb2 with
                | some _ => exact ((heff_e8.locals_clock _ _).locals_clock _ _).locals_clock _ _
                | none =>
                  have hs8_loc : s8.locals = s4.locals := by
                    have := (evaluate_storeByte_control_frame s7
                      (.op .add [.var .global (ofString "keccak_pad"), .const 135])
                      (.op .or [.loadByte (.op .add [.var .global (ofString "keccak_pad"), .const 135]), .const 128])).2.2.1
                    rw [hsb2] at this; exact this.trans hs7_loc
                  have hGs8 : GuestInv s8 := guestInv_congr heff_e8.code heff_e8.memaddrs heff_e8.shMemaddrs heff_e8.baseAddr hG
                  have hc_s8 : s8.code = originalRuntimeCode := heff_e8.code.trans hc
                  have hgpad8 : s8.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) := by
                    rw [heff_e8.globals]; exact hgpad
                  -- Step 9: `keccak_absorb_block(stp, keccak_pad)`
                  dsimp only at hnt hres ⊢
                  obtain ⟨hnt_ab, hor_ab⟩ := seq_step s8 _ _ hnt (Or.inr hres)
                  have hargs_ab : evalListHOLFinite s8 (h := fun a => Classical.propDecidable (s8.memaddrs a))
                      [.var .local (ofString "stp"), .var .global (ofString "keccak_pad")] =
                      some [.val (.word stp), .val (.word pad)] := by
                    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs8_loc, hstp_4, hgpad8]
                  rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
                  rcases hab : evaluateHOLFiniteState s8
                      (.call (some (none, none)) (ofString "keccak_absorb_block")
                        [.var .local (ofString "stp"), .var .global (ofString "keccak_pad")]) with ⟨rab, s9⟩
                  rw [hab] at hnt hres
                  have heff_ab : ByteEff s8 s9 Rl := by
                    have := call0_byteEff funByteEff_keccak_absorb_block s8 _ Rl hc_s8 hGs8
                      (fun vs hvs i hi hp => by
                        rw [hargs_ab] at hvs; injection hvs with hvs; subst hvs
                        simp [valWordNat] at hi; subst hi
                        exact hstp_sub (stp.toNat, 200) (List.mem_singleton.2 rfl) hp)
                      hnt_ab hor_ab
                    rwa [hab] at this
                  have heff_e9 : ByteEff entry s9 Rl := heff_e8.trans heff_ab
                  cases rab with
                  | some _ => exact ((heff_e9.locals_clock _ _).locals_clock _ _).locals_clock _ _
                  | none =>
                    have hs9_loc : s9.locals = s4.locals := by
                      have := call0_any_locals s8 _ _ (by rw [hab]); rw [hab] at this; exact this.trans hs8_loc
                    have hGs9 : GuestInv s9 := guestInv_congr heff_e9.code heff_e9.memaddrs heff_e9.shMemaddrs heff_e9.baseAddr hG
                    have hc_s9 : s9.code = originalRuntimeCode := heff_e9.code.trans hc
                    -- Step 10: `ite` output 32 bytes to `out`, then `return 0`!
                    dsimp only at hnt hres ⊢
                    obtain ⟨hnt_oi, hor_oi⟩ := seq_step s9 _ _ hnt (Or.inr hres)
                    have hout_sub : ∀ i ∈ [(out.toNat, 32)], 0 < i.2 → ∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2 := by
                      intro i hi _
                      simp at hi; subst hi
                      exact ⟨(out.toNat, 32), List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), le_rfl, le_rfl⟩
                    have heff_oi := keccak_out_ite_eff s9 out stp Rl hc_s9 hGs9
                      (by rw [hs9_loc]; exact hout_4) (by rw [hs9_loc]; exact hstp_4)
                      hout_sub hnt_oi hor_oi
                    rw [evaluateHOLFiniteState_seq_line780] at ⊢
                    rcases hoi : evaluateHOLFiniteState s9 _ with ⟨roi, s10⟩
                    rw [hoi] at heff_oi
                    have heff_e10 : ByteEff entry s10 Rl := heff_e9.trans heff_oi
                    cases roi with
                    | some _ => exact ((heff_e10.locals_clock _ _).locals_clock _ _).locals_clock _ _
                    | none =>
                      exact (((heff_e10.trans (byteEff_return s10 _ Rl)).locals_clock _ _).locals_clock _ _).locals_clock _ _

end InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28
