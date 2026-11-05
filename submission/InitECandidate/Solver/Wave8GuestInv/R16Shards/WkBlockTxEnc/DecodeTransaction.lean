import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkCacheGetRoot
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.ro_tx_is_blob
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.Common
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M08.Base

/-!
# R16 Shard `WkBlockTxEnc.DecodeTransaction`: `wk_decode_transaction_strong`

Complete proof of `wk_decode_transaction_strong` (`RetDecodedTx` on `ofString "decode_transaction"`
under guard `fun s => WorldOK s ∧ DecodeTxReady s`).
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.nameCheck false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc

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
open InitECandidate.Solver.Wave8GuestInv.Fast_C08WkShard03
open InitECandidate.Solver.Wave8GuestInv.R16Shards

/-! ## Section 1: `DecodeTxReady` and `worldOwned` Preservation -/

def DecodeTxReady {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  locN s "len" < 2 ^ 32 ∧
  locN s "p" + locN s "len" ≤ 2 ^ 64 ∧
  IvlsDisj [(locN s "p", locN s "len")] [(globN s "heap_ptr", scratchEnd - globN s "heap_ptr")]

/-! ## Section 1: `ReadOnlyFn` for `u256_from_be` -/

private def u256FromBeGood (f : MlS) : Bool :=
  f == ofString "bswap64"

private theorem ro_u256_from_be : ReadOnlyFn (ofString "u256_from_be") := by
  change InitECandidate.Solver.Wave8Contracts.M18.ReadOnlyFn (ofString "u256_from_be")
  refine InitECandidate.Solver.Wave8Contracts.M18.readOnlyFn_of_guestAst 86
    (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_from_be rfl u256FromBeGood ?_ (by decide)
  intro function hfn values body callee rs hfound
  simp only [u256FromBeGood, beq_iff_eq] at hfn
  subst hfn
  exact InitECandidate.Solver.Wave8Contracts.M18.installed_body_readOnly 23
    (by rw [guestAst_len]; decide) Guest.Software.guestFn_bswap64 rfl u256FromBeGood (by decide) hfound

private theorem ro_memeq_vvh : ReadOnlyFn (ofString "memeq") := by
  change InitECandidate.Solver.Wave8Contracts.M18.ReadOnlyFn (ofString "memeq")
  exact InitECandidate.Solver.Wave8Contracts.M18.readOnlyFn_of_guestAst 18
    (by rw [guestAst_len]; decide) Guest.Software.guestFn_memeq rfl
    (fun _ => false) (fun _ h => by cases h) (by decide)

/-! ## Section 2: General `WorldEff` Helpers for `B := []` -/

private theorem ws_no_gb_vvh : ∀ gs ∈ globalBuffers, ofString gs.1 ∉ wsGw.map ofString := by
  decide

private theorem ws_core_out_vvh : ∀ g ∈ coreWorldGlobals, ofString g ∉ wsGw.map ofString := by
  decide

private theorem panMemStores_eff_vvh
    (dom : BitVec 64 → Prop) [DecidablePred dom] (be : Bool)
    (hdom_ord : dom = ordinaryDomain) :
    ∀ (ws : List (HolWordLab 64)) (addr : BitVec 64)
      (mem mem' : BitVec 64 → HolWordLab 64),
      addr.toNat + 8 * ws.length < 2 ^ 64 →
      panMemStoresHOL addr ws dom mem = some mem' →
      (∀ x : BitVec 64, mem' x ≠ mem x →
        dom x ∧ addr.toNat ≤ x.toNat ∧ x.toNat + 8 ≤ addr.toNat + 8 * ws.length) ∧
      (∀ b : Nat, b < 2 ^ 64 →
        (memByteAt mem' be (BitVec.ofNat 64 b)).toNat ≠ (memByteAt mem be (BitVec.ofNat 64 b)).toNat →
        addr.toNat ≤ b ∧ b < addr.toNat + 8 * ws.length)
  | [], _, mem, mem', _, hst => by
    simp [panMemStoresHOL] at hst; subst hst
    exact ⟨fun _ h => absurd rfl h, fun _ _ h => absurd rfl h⟩
  | w :: rest, addr, mem, mem', hlt, hst => by
    simp only [panMemStoresHOL, panMemStoreHOL] at hst
    by_cases hd : dom addr
    · simp only [hd, ↓reduceIte] at hst
      have hbw : (panBytesInWord 64 : BitVec 64).toNat = 8 := rfl
      have hnext_add : (addr + panBytesInWord 64).toNat = addr.toNat + 8 := by
        apply BitVec.toNat_add_of_lt
        rw [hbw]; simp [List.length_cons] at hlt; omega
      have hlt_rest : (addr + panBytesInWord 64).toNat + 8 * rest.length < 2 ^ 64 := by
        rw [hnext_add]; simp [List.length_cons] at hlt; omega
      let mid := fun current => if current = addr then w else mem current
      obtain ⟨ih_c, ih_b⟩ := panMemStores_eff_vvh dom be hdom_ord rest (addr + panBytesInWord 64) mid mem' hlt_rest hst
      have hd_ord : addr.toNat % 8 = 0 := by
        rw [hdom_ord, ordinaryDomain_iff] at hd; exact hd.1
      refine ⟨?_, ?_⟩
      · intro x hne
        by_cases hxm : mem' x = mid x
        · rw [hxm] at hne
          by_cases hxa : x = addr
          · subst hxa; simp only [List.length_cons]; exact ⟨hd, le_rfl, by omega⟩
          · simp [mid, hxa] at hne
        · obtain ⟨hdx, hx1, hx2⟩ := ih_c x hxm
          rw [hnext_add] at hx1 hx2
          simp only [List.length_cons]; exact ⟨hdx, by omega, by omega⟩
      · intro b hb64 hne
        by_cases hbm : (memByteAt mem' be (BitVec.ofNat 64 b)).toNat =
            (memByteAt mid be (BitVec.ofNat 64 b)).toNat
        · rw [hbm] at hne
          by_cases hal : panByteAlignHOL (BitVec.ofNat 64 b) = addr
          · have hc_nat := panByteAlign_toNat64 (BitVec.ofNat 64 b)
            rw [hal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb64] at hc_nat
            simp only [List.length_cons]; omega
          · unfold memByteAt memWordAt at hne; simp [mid, hal] at hne
        · obtain ⟨hb1, hb2⟩ := ih_b b hb64 hbm
          rw [hnext_add] at hb1 hb2
          simp only [List.length_cons]; omega
    · simp [hd] at hst

private theorem worldEff_store_heap_bounded {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    (dstExp valExp : ExpHOL 64) (sz : Nat)
    (hval_len : ∀ v, @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp =
      some v → 8 * (flattenHOL v).length ≤ sz)
    (hin : ∀ x : BitVec 64,
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) dstExp =
        some (.val (.word x)) →
      globN s "heap_ptr" ≤ x.toNat ∧ x.toNat + sz ≤ heapLimit) :
    WorldEff s (evaluateHOLFiniteState cur (.store dstExp valExp)).2 Rl B gw := by
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  rw [evaluateHOLFiniteState_store]
  rcases hx : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) dstExp with _ | dv
  · exact h
  · rcases dv with ⟨⟨x⟩⟩ | _ | _ <;> try exact h
    rcases hv : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp with _ | val
    · exact h
    · dsimp only
      split
      · rename_i mem' hmem
        have hlen := hval_len val hv
        obtain ⟨hx_lo, hx_hi⟩ := hin x hx
        have hlt : x.toNat + 8 * (flattenHOL val).length < 2 ^ 64 := by omega
        obtain ⟨hc, hb⟩ := @panMemStores_eff_vvh cur.memaddrs (fun a => Classical.propDecidable (cur.memaddrs a))
          cur.be h.arena.1.memaddrs (flattenHOL val) x cur.memory mem' hlt hmem
        have hb_eff : ByteEff cur { cur with memory := mem' } [(x.toNat, 8 * (flattenHOL val).length)] := by
          refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
            fun a hne => (hc a hne).1,
            fun a hne => ?_,
            fun b hb64 hne => ?_⟩
          · obtain ⟨_, h1, h2⟩ := hc a hne
            exact ⟨(x.toNat, 8 * (flattenHOL val).length), List.mem_singleton.2 rfl, by omega, by omega, by omega⟩
          · rw [memB_eq_memByteAt, memB_eq_memByteAt] at hne
            obtain ⟨h1, h2⟩ := hb b hb64 hne
            exact ⟨(x.toNat, 8 * (flattenHOL val).length), List.mem_singleton.2 rfl, by omega, by omega⟩
        exact h.of_byteEff hb_eff (fun iv hiv _ => by
          simp at hiv; subst hiv
          exact Or.inr (Or.inr (Or.inr ⟨hx_lo, by omega⟩)))
      · exact h

private theorem flattenHOL_len_one (v : ValueHOL 64)
    (hsh : shapeEqHOL (shapeOfHOLExact v) .one = true) :
    8 * (flattenHOL v).length ≤ 8 := by
  cases v with
  | val w => simp [flattenHOL]
  | rStruct vs => simp [shapeOfHOLExact, shapeEqHOL] at hsh
  | nStruct _ => simp [shapeOfHOLExact, shapeEqHOL] at hsh

private theorem flattenHOL_len_four (v : ValueHOL 64)
    (hsh : shapeEqHOL (shapeOfHOLExact v) (.comb [.one, .one, .one, .one]) = true) :
    8 * (flattenHOL v).length ≤ 32 := by
  cases v with
  | val w => simp [shapeOfHOLExact, shapeEqHOL] at hsh
  | nStruct _ => simp [shapeOfHOLExact, shapeEqHOL] at hsh
  | rStruct vs =>
    rcases vs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, rest⟩⟩⟩⟩⟩
    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh
    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh
    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh
    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh
    · simp only [shapeOfHOLExact, List.map_cons, List.map_nil, shapeEqHOL, shapeEqHOL.shapeEqListHOL,
        Bool.and_eq_true, Bool.and_true] at hsh
      rcases hsh with ⟨h0, h1, h2, h3⟩
      have l0 := flattenHOL_len_one v0 h0
      have l1 := flattenHOL_len_one v1 h1
      have l2 := flattenHOL_len_one v2 h2
      have l3 := flattenHOL_len_one v3 h3
      simp only [flattenHOL, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.length_append, List.length_nil]
      omega
    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh

private theorem call0_or_resumes_vvh {F : Type}
    (s : PanSemStateFiniteExact 64 F) (fname : MlS) (args : List (ExpHOL 64))
    (hcr : ContOrRes (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 = none ∨
    Resumes (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 := by
  rcases hcr with h | h | h | hr
  · exact Or.inl h
  · exfalso
    rw [evaluateHOLFiniteState_call] at h
    revert h; split <;> [simp; (split <;> [simp; (split <;> [simp; skip])])]
    rcases evaluateHOLFiniteState (callEntryStateHOLFinite s _) _ with ⟨rc, _⟩
    rcases rc with _ | (_ | _ | _ | _ | _ | _ | _) <;> dsimp only <;> (repeat' split) <;> simp
  · exfalso
    rw [evaluateHOLFiniteState_call] at h
    revert h; split <;> [simp; (split <;> [simp; (split <;> [simp; skip])])]
    rcases evaluateHOLFiniteState (callEntryStateHOLFinite s _) _ with ⟨rc, _⟩
    rcases rc with _ | (_ | _ | _ | _ | _ | _ | _) <;> dsimp only <;> (repeat' split) <;> simp
  · exact Or.inr hr

private theorem worldEff_call0_funByteEff_vvh {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    {fname : MlS} {argR : List (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64) → List Ivl}
    (hf : FunByteEff fname argR)
    (args : List (ExpHOL 64)) (Sub : List Ivl)
    (hsub_args : ∀ vals,
      evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args = some vals →
      ∀ i ∈ argR vals cur.globals, 0 < i.2 → ∃ j ∈ Sub, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2)
    (hsub_world : ∀ iv ∈ Sub, 0 < iv.2 →
      (∃ j ∈ Rl, j.1 ≤ iv.1 ∧ iv.1 + iv.2 ≤ j.1 + j.2) ∨
      (∃ gs ∈ B, (bufferRegion s gs).1 ≤ iv.1 ∧ iv.1 + iv.2 ≤ (bufferRegion s gs).1 + (bufferRegion s gs).2) ∨
      (globN s "frame_mem_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ globN s "scratch_ptr") ∨
      (globN s "heap_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ heapLimit))
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) fname args)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call (some (none, none)) fname args)).1) :
    WorldEff s (evaluateHOLFiniteState cur (.call (some (none, none)) fname args)).2 Rl B gw :=
  h.of_byteEff (call0_byteEff hf cur args Sub h.code h.arena.1 hsub_args hnt (call0_or_resumes_vvh cur fname args hcr))
    hsub_world

private theorem worldEff_call_local_eff {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    (nm : MlS) (fname : MlS) (args : List (ExpHOL 64))
    (params : List (MlS × ShapeHOL)) (fbody : ProgHOL 64) (retSh : ShapeHOL)
    (hlook : originalRuntimeCode.lookup fname = some (params, fbody, retSh))
    (hcallee : ∀ (callee : HolFiniteMapExact MlS (ValueHOL 64)) (vals : List (ValueHOL 64)),
      evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args = some vals →
      lookupCodeHOLFinite cur.code.lookup fname vals = some (fbody, callee, retSh) →
      let entry := callEntryStateHOLFinite cur callee
      (evaluateHOLFiniteState entry fbody).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState entry fbody).1 →
      WorldEff s (evaluateHOLFiniteState entry fbody).2 Rl B gw)
    (hnt : (evaluateHOLFiniteState cur (.call (some (some (.local, nm), none)) fname args)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call (some (some (.local, nm), none)) fname args)).1) :
    WorldEff s (evaluateHOLFiniteState cur (.call (some (some (.local, nm), none)) fname args)).2 Rl B gw := by
  rw [evaluateHOLFiniteState_call] at hnt hcr ⊢
  rcases hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args with _ | vals
  · exact h
  · simp only [hargs] at hnt hcr ⊢
    rcases hl : lookupCodeHOLFinite cur.code.lookup fname vals with _ | ⟨body', callee, ret'⟩
    · exact h
    · simp only [hl] at hnt hcr ⊢
      have hsame := lookupCodeHOLFinite_installed_body cur.code.lookup fname params fbody body'
        retSh ret' vals callee (by rw [h.code]; exact hlook) hl
      cases hsame
      have hret_eq := lookupCodeHOLFinite_installed_return cur fname params fbody fbody
        retSh ret' vals callee (by rw [h.code]; exact hlook) hl
      cases hret_eq
      by_cases hz : cur.clock = 0
      · rw [if_pos hz] at hnt; exact absurd rfl hnt
      · rw [if_neg hz] at hnt hcr ⊢
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite cur callee) fbody with ⟨res, cpost⟩
        simp only [hrun] at hnt hcr ⊢
        cases res with
        | none => rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
        | some r1 =>
          cases r1 with
          | timeOut => exact absurd rfl hnt
          | «break» | «continue» | error | finalFfi _ =>
            rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
          | returned rv =>
            dsimp only at hcr ⊢
            split
            · split
              · have heff_c := hcallee callee vals hargs hl (by rw [hrun]; simp)
                  (by rw [hrun]; exact Or.inl ⟨rv, rfl⟩)
                rw [hrun] at heff_c
                exact heff_c.locals_clock _ _
              · rename_i hbad; rw [if_neg hbad] at hcr
                rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
            · rename_i hbad; rw [if_neg hbad] at hcr
              rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
          | exception exId exVal =>
            have hres_e : Resumes (some (.exception exId exVal)) := by
              rcases hcr with hc0 | hc0 | hc0 | hr <;> [simp at hc0; simp at hc0; simp at hc0; exact hr]
            have heff_c := hcallee callee vals hargs hl (by rw [hrun]; simp)
              (by rw [hrun]; exact hres_e)
            rw [hrun] at heff_c
            exact heff_c.locals_clock _ _

private theorem call_local_none_keeps {F : Type}
    (cur mid : PanSemStateFiniteExact 64 F)
    (nm fname : MlS) (args : List (ExpHOL 64))
    (hrun : evaluateHOLFiniteState cur (.call (some (some (.local, nm), none)) fname args) = (none, mid)) :
    (∀ key : MlS, key ≠ nm → mid.locals.lookup key = cur.locals.lookup key) ∧
    (∃ rv : ValueHOL 64,
      mid.locals.lookup nm = some rv ∧
      (∀ v0, cur.locals.lookup nm = some v0 → shapeEqHOL (shapeOfHOLExact rv) (shapeOfHOLExact v0) = true)) := by
  rw [evaluateHOLFiniteState_call] at hrun
  rcases hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args with _ | vs
  · rw [hargs] at hrun; cases hrun
  · rw [hargs] at hrun; dsimp only at hrun
    rcases hlk : lookupCodeHOLFinite cur.code.lookup fname vs with _ | ⟨b', c', r'⟩
    · rw [hlk] at hrun; cases hrun
    · rw [hlk] at hrun; dsimp only at hrun
      by_cases hz : cur.clock = 0
      · rw [if_pos hz] at hrun; cases hrun
      · rw [if_neg hz] at hrun
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite cur c') b' with ⟨res_b, pb⟩
        rw [hb] at hrun
        cases res_b with
        | none => cases hrun
        | some rb =>
          cases rb with
          | returned rv =>
            dsimp only at hrun
            by_cases hsh : shapeEqHOL (shapeOfHOLExact rv) r' = true
            · rw [if_pos hsh] at hrun
              by_cases hval : isValidValueHOLExact cur.toExact .local nm rv = true
              · rw [if_pos hval] at hrun
                injection hrun with _ hm; subst hm
                refine ⟨fun key hne => ?_, rv, ?_, fun v0 hv0 => ?_⟩
                · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne]
                · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                · simpa [isValidValueHOLExact, lookupKvarHOLExact, toExact, hv0] using hval
              · rw [if_neg hval] at hrun; cases hrun
            · rw [if_neg hsh] at hrun; cases hrun
          | _ => cases hrun

private theorem call0_none_locals {F : Type}
    (cur mid : PanSemStateFiniteExact 64 F)
    (fname : MlS) (args : List (ExpHOL 64))
    (hrun : evaluateHOLFiniteState cur (.call (some (none, none)) fname args) = (none, mid)) :
    mid.locals = cur.locals := by
  rw [evaluateHOLFiniteState_call] at hrun
  rcases hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args with _ | vs
  · rw [hargs] at hrun; cases hrun
  · rw [hargs] at hrun; dsimp only at hrun
    rcases hlk : lookupCodeHOLFinite cur.code.lookup fname vs with _ | ⟨b', c', r'⟩
    · rw [hlk] at hrun; cases hrun
    · rw [hlk] at hrun; dsimp only at hrun
      by_cases hz : cur.clock = 0
      · rw [if_pos hz] at hrun; cases hrun
      · rw [if_neg hz] at hrun
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite cur c') b' with ⟨res_b, pb⟩
        rw [hb] at hrun
        rcases res_b with _ | (_ | _ | _ | _ | rv | _ | _) <;> dsimp only at hrun <;> try cases hrun
        split at hrun <;> cases hrun
        rfl

private theorem assign_local_none_keeps {F : Type}
    (cur mid : PanSemStateFiniteExact 64 F)
    (nm : MlS) (e : ExpHOL 64)
    (hrun : evaluateHOLFiniteState cur (.assign .local nm e) = (none, mid)) :
    (∀ key : MlS, key ≠ nm → mid.locals.lookup key = cur.locals.lookup key) ∧
    (∃ rv : ValueHOL 64,
      mid.locals.lookup nm = some rv ∧
      (∀ v0, cur.locals.lookup nm = some v0 → shapeEqHOL (shapeOfHOLExact rv) (shapeOfHOLExact v0) = true)) := by
  rw [evaluateHOLFiniteState_assign] at hrun
  rcases hv : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) e with _ | rv
  · rw [hv] at hrun; cases hrun
  · rw [hv] at hrun; dsimp only at hrun
    by_cases hval : isValidValueHOLFinite cur .local nm rv = true
    · rw [if_pos hval] at hrun
      injection hrun with _ hm; subst hm
      refine ⟨fun key hne => ?_, rv, ?_, fun v0 hv0 => ?_⟩
      · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne]
      · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      · simpa [isValidValueHOLFinite, lookupKvarHOLFinite, hv0] using hval
    · rw [if_neg hval] at hrun; cases hrun

private theorem ite_none_keeps {F : Type}
    {P : PanSemStateFiniteExact 64 F → Prop}
    {cur mid : PanSemStateFiniteExact 64 F}
    {c : ExpHOL 64} {yes no : ProgHOL 64}
    (hy : ∀ m, evaluateHOLFiniteState cur yes = (none, m) → P m)
    (hn : ∀ m, evaluateHOLFiniteState cur no = (none, m) → P m)
    (hrun : evaluateHOLFiniteState cur (.ite c yes no) = (none, mid)) :
    P mid := by
  rw [evaluateHOLFiniteState_ite] at hrun
  split at hrun
  · split at hrun
    · exact hn mid hrun
    · exact hy mid hrun
  · cases hrun

private theorem worldEff_while_cond_vvh {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (cond : ExpHOL 64) {body : ProgHOL 64}
    (Inv : PanSemStateFiniteExact 64 F → Prop)
    (hdec : ∀ t, Inv t → Inv (decClockHOLFinite t))
    (hb : ∀ t (cw : BitVec 64),
      @evalHOLFinite 64 F _ t (fun a => Classical.propDecidable (t.memaddrs a)) cond = some (.val (.word cw)) →
      cw ≠ 0 →
      WorldEff s (decClockHOLFinite t) Rl B gw → Inv (decClockHOLFinite t) →
      (evaluateHOLFiniteState (decClockHOLFinite t) body).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState (decClockHOLFinite t) body).1 →
      WorldEff s (evaluateHOLFiniteState (decClockHOLFinite t) body).2 Rl B gw ∧
      (((evaluateHOLFiniteState (decClockHOLFinite t) body).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite t) body).1 = some .continue) →
        Inv (evaluateHOLFiniteState (decClockHOLFinite t) body).2)) :
    ∀ (k : Nat) (cur : PanSemStateFiniteExact 64 F), cur.clock = k →
      WorldEff s cur Rl B gw → Inv cur →
      (evaluateHOLFiniteState cur (.while cond body)).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState cur (.while cond body)).1 →
      WorldEff s (evaluateHOLFiniteState cur (.while cond body)).2 Rl B gw := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro cur hclk heff hinv hnt hcr
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt hcr ⊢
    rcases hc : @evalHOLFinite 64 F _ cur (fun a => Classical.propDecidable (cur.memaddrs a)) cond with _ | cv
    · exact heff
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try exact heff
      rw [hc] at hnt hcr; dsimp only at hnt hcr ⊢
      by_cases hw0 : cw = 0
      · subst hw0; simp; exact heff
      · rw [if_pos hw0] at hnt hcr ⊢
        by_cases hk0 : cur.clock = 0
        · rw [if_pos hk0] at hnt; exact absurd rfl hnt
        · rw [if_neg hk0] at hnt hcr ⊢
          have heff_d : WorldEff s (decClockHOLFinite cur) Rl B gw := heff.locals_clock cur.locals (cur.clock - 1)
          have hinv_d : Inv (decClockHOLFinite cur) := hdec cur hinv
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite cur) body
          rcases hbo : evaluateHOLFiniteState (decClockHOLFinite cur) body with ⟨rb, sb⟩
          simp only [hbo] at hnt hcr hrem ⊢
          have hlt : sb.clock < k := by
            change sb.clock ≤ cur.clock - 1 at hrem; omega
          cases rb with
          | none =>
            obtain ⟨heff_b, hinv_b⟩ := hb cur cw hc hw0 heff_d hinv_d
              (by rw [hbo]; simp) (by rw [hbo]; exact Or.inl rfl)
            rw [hbo] at heff_b hinv_b
            exact ih sb.clock hlt sb rfl heff_b (hinv_b (Or.inl rfl)) hnt hcr
          | some r1 =>
            cases r1 with
            | «continue» =>
              obtain ⟨heff_b, hinv_b⟩ := hb cur cw hc hw0 heff_d hinv_d
                (by rw [hbo]; simp) (by rw [hbo]; exact Or.inr (Or.inr (Or.inl rfl)))
              rw [hbo] at heff_b hinv_b
              exact ih sb.clock hlt sb rfl heff_b (hinv_b (Or.inr rfl)) hnt hcr
            | «break» =>
              obtain ⟨heff_b, _⟩ := hb cur cw hc hw0 heff_d hinv_d
                (by rw [hbo]; simp) (by rw [hbo]; exact Or.inr (Or.inl rfl))
              rw [hbo] at heff_b; exact heff_b
            | timeOut => exact absurd rfl hnt
            | returned v =>
              obtain ⟨heff_b, _⟩ := hb cur cw hc hw0 heff_d hinv_d
                (by rw [hbo]; simp) (by rw [hbo]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨v, rfl⟩))))
              rw [hbo] at heff_b; exact heff_b
            | exception eid ev =>
              have hres_e : Resumes (some (.exception eid ev)) := by
                rcases hcr with h | h | h | hr <;> [cases h; cases h; cases h; exact hr]
              obtain ⟨heff_b, _⟩ := hb cur cw hc hw0 heff_d hinv_d
                (by rw [hbo]; simp) (by rw [hbo]; exact Or.inr (Or.inr (Or.inr hres_e)))
              rw [hbo] at heff_b; exact heff_b
            | error =>
              rcases hcr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> cases h
            | finalFfi _ =>
              rcases hcr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> cases h

private theorem eval_assign_flowing_keeps_vvh {F : Type}
    (u : PanSemStateFiniteExact 64 F) (nm : MlS) (e : ExpHOL 64) (key : MlS)
    (hk : key ≠ nm)
    (hf : (evaluateHOLFiniteState u (.assign .local nm e)).1 = none ∨
      (evaluateHOLFiniteState u (.assign .local nm e)).1 = some .continue) :
    (evaluateHOLFiniteState u (.assign .local nm e)).2.locals.lookup key = u.locals.lookup key := by
  revert hf
  rw [evaluateHOLFiniteState_assign]
  rcases hv : @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) e with _ | val
  · simp
  · dsimp only
    by_cases hval : isValidValueHOLFinite u .local nm val = true
    · rw [if_pos hval]
      intro _
      simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
    · rw [if_neg hval]; simp

private theorem eval_store_flowing_inv_vvh {F : Type}
    (u : PanSemStateFiniteExact 64 F) (d e : ExpHOL 64) {rest : ProgHOL 64}
    (hf : (evaluateHOLFiniteState u (.seq (.store d e) rest)).1 = none ∨
      (evaluateHOLFiniteState u (.seq (.store d e) rest)).1 = some .continue) :
    ∃ u1, evaluateHOLFiniteState u (.store d e) = (none, u1) ∧ u1.locals = u.locals ∧
      ((evaluateHOLFiniteState u1 rest).1 = none ∨ (evaluateHOLFiniteState u1 rest).1 = some .continue) ∧
      (evaluateHOLFiniteState u (.seq (.store d e) rest)).2 = (evaluateHOLFiniteState u1 rest).2 := by
  rw [evaluateHOLFiniteState_seq_line780] at hf ⊢
  rcases hs : evaluateHOLFiniteState u (.store d e) with ⟨r, u1⟩
  rw [hs] at hf
  cases r with
  | none =>
    have hloc : u1.locals = u.locals := by
      have hcf := (evaluate_store_control_frame u d e).2.1
      rwa [hs] at hcf
    exact ⟨u1, rfl, hloc, hf, rfl⟩
  | some r =>
    exfalso
    have hse : r = .error := by
      rw [evaluateHOLFiniteState_store] at hs
      revert hs; repeat' split
      all_goals (intro hs; injection hs with hs1 _; cases hs1 <;> rfl)
    subst hse
    rcases hf with hf | hf <;> simp at hf

private theorem eval_decCall_flowing_keeps {F : Type}
    (t : PanSemStateFiniteExact 64 F) (nm : MlS) (sh : ShapeHOL) (fname : MlS) (args : List (ExpHOL 64))
    (cont : ProgHOL 64) (key : MlS) (hk : key ≠ nm)
    (hcont : ∀ (u : PanSemStateFiniteExact 64 F),
      ((evaluateHOLFiniteState u cont).1 = none ∨ (evaluateHOLFiniteState u cont).1 = some .continue) →
      (evaluateHOLFiniteState u cont).2.locals.lookup key = u.locals.lookup key)
    (hf : (evaluateHOLFiniteState t (.decCall nm sh fname args cont)).1 = none ∨
      (evaluateHOLFiniteState t (.decCall nm sh fname args cont)).1 = some .continue) :
    (evaluateHOLFiniteState t (.decCall nm sh fname args cont)).2.locals.lookup key = t.locals.lookup key := by
  revert hf
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args with _ | vs
  · simp
  · simp only [hargs]
    rcases hlk : lookupCodeHOLFinite t.code.lookup fname vs with _ | ⟨b', c', r'⟩
    · simp
    · simp only [hlk]
      by_cases hz : t.clock = 0
      · simp [hz]
      · simp only [hz, ↓reduceIte]
        rcases hcal : evaluateHOLFiniteState (callEntryStateHOLFinite t c') b' with ⟨rc, st⟩
        simp only [hcal]
        rcases rc with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only <;> try simp
        split
        · intro hf
          dsimp only
          rw [resVarEq_lookup_local, if_neg hk]
          let u0 := setVarHOLFinite nm w { st with locals := t.locals }
          have hu0_k : u0.locals.lookup key = t.locals.lookup key := by
            simp [u0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
          exact (hcont u0 hf).trans hu0_k
        · simp

private theorem eval_dec_flowing_keeps {F : Type}
    (t : PanSemStateFiniteExact 64 F) (nm : MlS) (sh : ShapeHOL) (init : ExpHOL 64)
    (cont : ProgHOL 64) (key : MlS) (hk : key ≠ nm)
    (hcont : ∀ (u : PanSemStateFiniteExact 64 F),
      ((evaluateHOLFiniteState u cont).1 = none ∨ (evaluateHOLFiniteState u cont).1 = some .continue) →
      (evaluateHOLFiniteState u cont).2.locals.lookup key = u.locals.lookup key)
    (hf : (evaluateHOLFiniteState t (.dec nm sh init cont)).1 = none ∨
      (evaluateHOLFiniteState t (.dec nm sh init cont)).1 = some .continue) :
    (evaluateHOLFiniteState t (.dec nm sh init cont)).2.locals.lookup key = t.locals.lookup key := by
  revert hf
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · simp
  · split
    · rename_i v _ _
      intro hf
      dsimp only
      rw [resVarEq_lookup_local, if_neg hk]
      let u0 := setVarHOLFinite nm v t
      have hu0_k : u0.locals.lookup key = t.locals.lookup key := by
        simp [u0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
      exact (hcont u0 hf).trans hu0_k
    · simp

private theorem eval_guard_raise_flowing_inv {F : Type}
    (u : PanSemStateFiniteExact 64 F) (c : ExpHOL 64) (eid : MlS) (rexp : ExpHOL 64) {rest : ProgHOL 64}
    (hf : (evaluateHOLFiniteState u (.seq (.ite c (.raise eid rexp) .skip) rest)).1 = none ∨
      (evaluateHOLFiniteState u (.seq (.ite c (.raise eid rexp) .skip) rest)).1 = some .continue) :
    ((evaluateHOLFiniteState u rest).1 = none ∨ (evaluateHOLFiniteState u rest).1 = some .continue) ∧
    (evaluateHOLFiniteState u (.seq (.ite c (.raise eid rexp) .skip) rest)).2 = (evaluateHOLFiniteState u rest).2 := by
  rw [evaluateHOLFiniteState_seq_line780] at hf ⊢
  rcases hs : evaluateHOLFiniteState u (.ite c (.raise eid rexp) .skip) with ⟨r, u1⟩
  rw [hs] at hf
  cases r with
  | none =>
    have hu1 : u1 = u := by
      rw [evaluateHOLFiniteState_ite] at hs
      split at hs
      · split at hs
        · rw [evaluateHOLFiniteState_skip] at hs; injection hs with _ hm; exact hm.symm
        · rw [evaluateHOLFiniteState_raise] at hs
          split at hs <;> [ (dsimp only at hs; split at hs <;> cases hs); cases hs ]
      · cases hs
    subst hu1; exact ⟨hf, rfl⟩
  | some r =>
    exfalso
    have hnc : (evaluateHOLFiniteState u (.ite c (.raise eid rexp) .skip)).1 ≠ some .continue := by
      rw [evaluateHOLFiniteState_ite]
      split
      · split
        · rw [evaluateHOLFiniteState_skip]; simp
        · rw [evaluateHOLFiniteState_raise]
          split <;> [ (dsimp only; split <;> simp); simp ]
      · simp
    rw [hs] at hnc
    rcases hf with hf | hf <;> [simp at hf; exact hnc (by simpa using hf)]

private theorem eval_call_local_flowing_keeps {F : Type}
    (u : PanSemStateFiniteExact 64 F) (nm fname : MlS) (args : List (ExpHOL 64)) (key : MlS) (hk : key ≠ nm)
    {rest : ProgHOL 64}
    (hf : (evaluateHOLFiniteState u (.seq (.call (some (some (.local, nm), none)) fname args) rest)).1 = none ∨
      (evaluateHOLFiniteState u (.seq (.call (some (some (.local, nm), none)) fname args) rest)).1 = some .continue) :
    ∃ u1, evaluateHOLFiniteState u (.call (some (some (.local, nm), none)) fname args) = (none, u1) ∧
      u1.locals.lookup key = u.locals.lookup key ∧
      ((evaluateHOLFiniteState u1 rest).1 = none ∨ (evaluateHOLFiniteState u1 rest).1 = some .continue) ∧
      (evaluateHOLFiniteState u (.seq (.call (some (some (.local, nm), none)) fname args) rest)).2 =
        (evaluateHOLFiniteState u1 rest).2 := by
  rw [evaluateHOLFiniteState_seq_line780] at hf ⊢
  rcases hs : evaluateHOLFiniteState u (.call (some (some (.local, nm), none)) fname args) with ⟨r, u1⟩
  rw [hs] at hf
  cases r with
  | none =>
    exact ⟨u1, rfl, (call_local_none_keeps u u1 nm fname args hs).1 key hk, hf, rfl⟩
  | some r =>
    exfalso
    have hnc : (evaluateHOLFiniteState u (.call (some (some (.local, nm), none)) fname args)).1 ≠ some .continue := by
      rw [evaluateHOLFiniteState_call]
      split <;> [simp; (split <;> [simp; (split <;> [simp; skip])])]
      rcases evaluateHOLFiniteState (callEntryStateHOLFinite u _) _ with ⟨rc, _⟩
      rcases rc with _ | (_ | _ | _ | _ | _ | _ | _) <;> dsimp only <;> (repeat' split) <;> simp
    rw [hs] at hnc
    rcases hf with hf | hf <;> [cases hf; exact hnc hf]

private theorem eval_call0_flowing_inv {F : Type}
    (u : PanSemStateFiniteExact 64 F) (fname : MlS) (args : List (ExpHOL 64)) {rest : ProgHOL 64}
    (hf : (evaluateHOLFiniteState u (.seq (.call (some (none, none)) fname args) rest)).1 = none ∨
      (evaluateHOLFiniteState u (.seq (.call (some (none, none)) fname args) rest)).1 = some .continue) :
    ∃ u1, evaluateHOLFiniteState u (.call (some (none, none)) fname args) = (none, u1) ∧
      u1.locals = u.locals ∧
      ((evaluateHOLFiniteState u1 rest).1 = none ∨ (evaluateHOLFiniteState u1 rest).1 = some .continue) ∧
      (evaluateHOLFiniteState u (.seq (.call (some (none, none)) fname args) rest)).2 =
        (evaluateHOLFiniteState u1 rest).2 := by
  rw [evaluateHOLFiniteState_seq_line780] at hf ⊢
  rcases hs : evaluateHOLFiniteState u (.call (some (none, none)) fname args) with ⟨r, u1⟩
  rw [hs] at hf
  cases r with
  | none =>
    exact ⟨u1, rfl, call0_none_locals u u1 fname args hs, hf, rfl⟩
  | some r =>
    exfalso
    have hnc : (evaluateHOLFiniteState u (.call (some (none, none)) fname args)).1 ≠ some .continue := by
      rw [evaluateHOLFiniteState_call]
      split <;> [simp; (split <;> [simp; (split <;> [simp; skip])])]
      rcases evaluateHOLFiniteState (callEntryStateHOLFinite u _) _ with ⟨rc, _⟩
      rcases rc with _ | (_ | _ | _ | _ | _ | _ | _) <;> dsimp only <;> (repeat' split) <;> simp
    rw [hs] at hnc
    rcases hf with hf | hf <;> [cases hf; exact hnc hf]

private theorem eval_while_flowing_keeps {F : Type}
    (cond : ExpHOL 64) (body : ProgHOL 64) (key : MlS)
    (hb : ∀ (t : PanSemStateFiniteExact 64 F),
      ((evaluateHOLFiniteState t body).1 = none ∨ (evaluateHOLFiniteState t body).1 = some .continue) →
      (evaluateHOLFiniteState t body).2.locals.lookup key = t.locals.lookup key)
    (hnb : ∀ (t : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState t body).1 ≠ some .break) :
    ∀ (k : Nat) (cur : PanSemStateFiniteExact 64 F), cur.clock ≤ k →
      ((evaluateHOLFiniteState cur (.while cond body)).1 = none ∨
       (evaluateHOLFiniteState cur (.while cond body)).1 = some .continue) →
      (evaluateHOLFiniteState cur (.while cond body)).2.locals.lookup key = cur.locals.lookup key := by
  intro k
  induction k with
  | zero =>
    intro cur hck hf
    revert hf
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    rcases hc : @evalHOLFinite 64 F _ cur (fun a => Classical.propDecidable (cur.memaddrs a)) cond with _ | cv
    · simp
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
      by_cases hw0 : cw = 0#64
      · subst hw0; simp
      · rw [if_neg hw0]
        have hk0 : cur.clock = 0 := by omega
        rw [if_pos hk0]; simp
  | succ k ih =>
    intro cur hck hf
    revert hf
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    rcases hc : @evalHOLFinite 64 F _ cur (fun a => Classical.propDecidable (cur.memaddrs a)) cond with _ | cv
    · simp
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
      by_cases hw0 : cw = 0#64
      · subst hw0; simp
      · rw [if_neg hw0]
        by_cases hk0 : cur.clock = 0
        · rw [if_pos hk0]; simp
        · rw [if_neg hk0]
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite cur) body
          have hnb_d := hnb (decClockHOLFinite cur)
          rcases hbo : evaluateHOLFiniteState (decClockHOLFinite cur) body with ⟨rb, sb⟩
          simp only [hbo] at hrem hnb_d ⊢
          have hlt : sb.clock ≤ k := by change sb.clock ≤ cur.clock - 1 at hrem; omega
          cases rb with
          | none =>
            intro hf
            have hsb := hb (decClockHOLFinite cur) (by rw [hbo]; exact Or.inl rfl)
            rw [hbo] at hsb
            exact (ih sb hlt hf).trans hsb
          | some r1 =>
            cases r1 with
            | «continue» =>
              intro hf
              have hsb := hb (decClockHOLFinite cur) (by rw [hbo]; exact Or.inr rfl)
              rw [hbo] at hsb
              exact (ih sb hlt hf).trans hsb
            | «break» => exact absurd rfl hnb_d
            | _ => simp

/-! ## Section 3: RLP Scratch Walkers & Return Bounds for `B := []` -/

private theorem ws_nil_sub_vvh : ∀ gs ∈ ([] : List (String × Nat)), gs ∈ globalBuffers :=
  fun _ h => by cases h

private theorem lookup__rlp_validate_items_body_vvh :
    originalRuntimeCode.lookup (ofString "_rlp_validate_items_body") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn__rlp_validate_items_body, .one) :=
  lookup_of_guestAst_getElem 110 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__rlp_validate_items_body) rfl

private theorem lookup_rlp_validate_items_vvh :
    originalRuntimeCode.lookup (ofString "rlp_validate_items") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_validate_items, .one) :=
  lookup_of_guestAst_getElem 111 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_validate_items) rfl

private theorem lookup_rlp_item_total_vvh :
    originalRuntimeCode.lookup (ofString "rlp_item_total") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_item_total, .one) :=
  lookup_of_guestAst_getElem 112 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_item_total) rfl

private theorem lookup_rlp_list_count_vvh :
    originalRuntimeCode.lookup (ofString "rlp_list_count") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_list_count, .one) :=
  lookup_of_guestAst_getElem 113 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_list_count) rfl

private theorem lookup_rlp_item_vvh :
    originalRuntimeCode.lookup (ofString "rlp_item") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_item, .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 107 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_item) rfl

private theorem lookup_rlp_decode_fully_vvh :
    originalRuntimeCode.lookup (ofString "rlp_decode_fully") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_decode_fully, .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 108 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_decode_fully) rfl

private theorem lookup_rlp_list_to_slices_vvh :
    originalRuntimeCode.lookup (ofString "rlp_list_to_slices") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_list_to_slices, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 115 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_list_to_slices) rfl

private theorem lookupCode_two_words_any_vvh {fname p1 p2 : MlS} {body : ProgHOL 64} {retShape : ShapeHOL}
    {vals : List (ValueHOL 64)} {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (hne : p1 ≠ p2)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one)], body, retShape))
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, L, retShape)) :
    ∃ w1 w2 : BitVec 64,
      vals = [.val (.word w1), .val (.word w2)] ∧
      L.lookup p1 = some (.val (.word w1)) ∧
      L.lookup p2 = some (.val (.word w2)) := by
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup fname vals body L retShape hl
  simp only [lookupCodeHOLExact, hlook] at hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩
  · simp at hx
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL] at hx
    obtain ⟨_, hL⟩ := hx
    refine ⟨w1, w2, rfl, ?_, ?_⟩ <;> (rw [← hL]; simp [hne, Ne.symm hne])
  · simp at hx

private def vibPushProg_vvh : ProgHOL 64 :=
  .decCall (ofString "rec") .one (ofString "scratch_alloc") [.const 24]
    (.seq (.store (.var .local (ofString "rec")) (.var .local (ofString "after")))
      (.seq (.store (.op .add [.var .local (ofString "rec"), .const 8]) (.var .local (ofString "end")))
        (.seq (.store (.op .add [.var .local (ofString "rec"), .const 16]) (.var .local (ofString "top")))
          (.seq (.assign .local (ofString "top") (.var .local (ofString "rec")))
            (.seq (.assign .local (ofString "pos") (.var .local (ofString "payload")))
              (.assign .local (ofString "end") (.var .local (ofString "after"))))))))

private theorem worldEff_vibPush_vvh {F : Type}
    {s t3 : PanSemStateFiniteExact 64 F}
    (hAR : ArenaReady s)
    (heff_t3 : WorldEff s t3 [] [] wsGw)
    (w_top w_end w_aft : BitVec 64)
    (ht3_aft : t3.locals.lookup (ofString "after") = some (.val (.word w_aft)))
    (ht3_end : t3.locals.lookup (ofString "end") = some (.val (.word w_end)))
    (ht3_top : t3.locals.lookup (ofString "top") = some (.val (.word w_top)))
    (hnt_push : (evaluateHOLFiniteState t3 vibPushProg_vvh).1 ≠ some .timeOut)
    (hcr_push : ContOrRes (evaluateHOLFiniteState t3 vibPushProg_vvh).1) :
    WorldEff s (evaluateHOLFiniteState t3 vibPushProg_vvh).2 [] [] wsGw := by
  dsimp only [vibPushProg_vvh] at hnt_push hcr_push ⊢
  refine worldEff_decCall_scratch_alloc heff_t3 (by decide) _ _ hnt_push hcr_push
    (fun qw nw mid hsz_ev _ hmid_loc _ heff_mid _ hqw_lo hqw_add hsp_le _ _ hnt_ps hcr_ps => ?_)
  have hnw_eq : nw = 24 := by simp [evalHOLExact] at hsz_ev; exact hsz_ev.symm
  subst hnw_eq
  have h24 : ((24 : BitVec 64).toNat + 7) / 8 * 8 = 24 := by decide
  rw [h24] at hqw_add
  have hse_lt : scratchEnd < 2 ^ 64 := by decide
  have hsp_s_hi : globN s "scratch_ptr" ≤ scratchEnd := hAR.2.2.2.2.2.1
  have hqw8 : (qw + 8#64).toNat = qw.toNat + 8 := BitVec.toNat_add_of_lt (by change qw.toNat + 8 < 2 ^ 64; omega)
  have hqw16 : (qw + 16#64).toNat = qw.toNat + 16 := BitVec.toNat_add_of_lt (by change qw.toNat + 16 < 2 ^ 64; omega)
  have hmid_rec : mid.locals.lookup (ofString "rec") = some (.val (.word qw)) := by
    rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hmid_aft : mid.locals.lookup (ofString "after") = some (.val (.word w_aft)) := by
    rw [hmid_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, ht3_aft, show ofString "rec" ≠ ofString "after" by decide]
  have hmid_end : mid.locals.lookup (ofString "end") = some (.val (.word w_end)) := by
    rw [hmid_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, ht3_end, show ofString "rec" ≠ ofString "end" by decide]
  have hmid_top : mid.locals.lookup (ofString "top") = some (.val (.word w_top)) := by
    rw [hmid_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, ht3_top, show ofString "rec" ≠ ofString "top" by decide]
  refine worldEff_seq hnt_ps hcr_ps
    (fun _ _ => worldEff_store_word heff_mid _ _
      (fun v hv => by simp [evalHOLExact, hmid_aft] at hv; exact ⟨_, hv.symm⟩)
      (fun x hx _ => by
        simp [evalHOLExact, hmid_rec] at hx; subst hx
        exact Or.inr (Or.inr (Or.inl ⟨hqw_lo, by omega⟩))))
    (fun u1 hu1 heff_u1 hnt_u1 hcr_u1 => ?_)
  have hu1_loc : u1.locals = mid.locals := by
    have hcf := (evaluate_store_control_frame mid (.var .local (ofString "rec")) (.var .local (ofString "after"))).2.1
    rwa [hu1] at hcf
  refine worldEff_seq hnt_u1 hcr_u1
    (fun _ _ => worldEff_store_word heff_u1 _ _
      (fun v hv => by simp [evalHOLExact, hu1_loc, hmid_end] at hv; exact ⟨_, hv.symm⟩)
      (fun x hx _ => by
        simp [evalHOLExact, evalListHOLExact, hu1_loc, hmid_rec, valueIsWord, valueWord, wordOpHOL, wordOp] at hx
        subst hx
        exact Or.inr (Or.inr (Or.inl ⟨by rw [hqw8]; omega, by rw [hqw8]; omega⟩))))
    (fun u2 hu2 heff_u2 hnt_u2 hcr_u2 => ?_)
  have hu2_loc : u2.locals = mid.locals := by
    have hcf := (evaluate_store_control_frame u1 (.op .add [.var .local (ofString "rec"), .const 8]) (.var .local (ofString "end"))).2.1
    rw [hu2] at hcf; exact hcf.trans hu1_loc
  refine worldEff_seq hnt_u2 hcr_u2
    (fun _ _ => worldEff_store_word heff_u2 _ _
      (fun v hv => by simp [evalHOLExact, hu2_loc, hmid_top] at hv; exact ⟨_, hv.symm⟩)
      (fun x hx _ => by
        simp [evalHOLExact, evalListHOLExact, hu2_loc, hmid_rec, valueIsWord, valueWord, wordOpHOL, wordOp] at hx
        subst hx
        exact Or.inr (Or.inr (Or.inl ⟨by rw [hqw16]; omega, by rw [hqw16]; omega⟩))))
    (fun u3 _ heff_u3 hnt_u3 hcr_u3 =>
      worldEff_seq hnt_u3 hcr_u3
        (fun _ _ => worldEff_assign_local heff_u3 _ _)
        (fun u4 _ heff_u4 hnt_u4 hcr_u4 =>
          worldEff_seq hnt_u4 hcr_u4
            (fun _ _ => worldEff_assign_local heff_u4 _ _)
            (fun u5 _ heff_u5 _ _ => worldEff_assign_local heff_u5 _ _)))

private def vibLoopBody_vvh : ProgHOL 64 :=
  .ite (.cmp .equal (.var .local (ofString "pos")) (.var .local (ofString "end")))
    (.ite (.cmp .equal (.var .local (ofString "top")) (.const 0))
      (.assign .local (ofString "go") (.const 0))
      (.seq
        (.assign .local (ofString "pos") (.load .one (.op .add [.var .local (ofString "top"), .const 0])))
        (.seq
          (.assign .local (ofString "end") (.load .one (.op .add [.var .local (ofString "top"), .const 8])))
          (.assign .local (ofString "top") (.load .one (.op .add [.var .local (ofString "top"), .const 16]))))))
    (.decCall (ofString "h") (.comb [.one, .one, .one]) (ofString "rlp_item_header")
      [.var .local (ofString "pos"), .op .sub [.var .local (ofString "end"), .var .local (ofString "pos")]]
      (.dec (ofString "payload") .one (.op .add [.var .local (ofString "pos"), .rfield 0 (.var .local (ofString "h"))])
        (.dec (ofString "after") .one (.op .add [.var .local (ofString "payload"), .rfield 1 (.var .local (ofString "h"))])
          (.ite (.cmp .notEqual (.rfield 2 (.var .local (ofString "h"))) (.const 0))
            vibPushProg_vvh
            (.assign .local (ofString "pos") (.var .local (ofString "after")))))))

private theorem worldEff_vibLoopBody_vvh {F : Type}
    {s t : PanSemStateFiniteExact 64 F}
    (hAR : ArenaReady s)
    (heff_t : WorldEff s t [] [] wsGw)
    (hinv_t : WordLocals ["top", "pos", "end", "go"] t)
    (hnt_b : (evaluateHOLFiniteState t vibLoopBody_vvh).1 ≠ some .timeOut)
    (hcr_b : ContOrRes (evaluateHOLFiniteState t vibLoopBody_vvh).1) :
    WorldEff s (evaluateHOLFiniteState t vibLoopBody_vvh).2 [] [] wsGw := by
  dsimp only [vibLoopBody_vvh] at hnt_b hcr_b ⊢
  refine worldEff_ite heff_t _ hnt_b hcr_b
    (fun _ _ _ hnt_eq hcr_eq =>
      worldEff_ite heff_t _ hnt_eq hcr_eq
        (fun _ _ _ _ _ => worldEff_assign_local heff_t _ _)
        (fun _ hnt_pop hcr_pop =>
          worldEff_seq hnt_pop hcr_pop
            (fun _ _ => worldEff_assign_local heff_t _ _)
            (fun m1 _ heff_m1 hnt_p2 hcr_p2 =>
              worldEff_seq hnt_p2 hcr_p2
                (fun _ _ => worldEff_assign_local heff_m1 _ _)
                (fun m2 _ heff_m2 _ _ => worldEff_assign_local heff_m2 _ _))))
    (fun _ hnt_neq hcr_neq => ?_)
  refine worldEff_decCall_ro heff_t InitECandidate.Solver.Wave8GuestInv.R13.ro_rlp_item_header
    (ofString "h") (.comb [.one, .one, .one]) _ hnt_neq hcr_neq (fun rvh cpost _ hcpost hnt_c1 hcr_c1 => ?_)
  let t1 := setVarHOLFinite (ofString "h") rvh { cpost with locals := t.locals }
  have heff_t1 : WorldEff s t1 [] [] wsGw := (heff_t.of_readOnly hcpost).locals_clock _ _
  obtain ⟨w_top, htop_t⟩ := hinv_t "top" (by simp)
  obtain ⟨w_end, hend_t⟩ := hinv_t "end" (by simp)
  refine worldEff_dec heff_t1 _ _ _ hnt_c1 hcr_c1 (fun vpay _ hsh_pay hnt_c2 hcr_c2 => ?_)
  rcases vpay with ⟨⟨wpay⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh_pay
  let t2 := setVarHOLFinite (ofString "payload") (.val (.word wpay)) t1
  have heff_t2 : WorldEff s t2 [] [] wsGw := heff_t1.locals_clock _ _
  refine worldEff_dec heff_t2 _ _ _ hnt_c2 hcr_c2 (fun vaft _ hsh_aft hnt_c3 hcr_c3 => ?_)
  rcases vaft with ⟨⟨waft⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh_aft
  let t3 := setVarHOLFinite (ofString "after") (.val (.word waft)) t2
  have heff_t3 : WorldEff s t3 [] [] wsGw := heff_t2.locals_clock _ _
  refine worldEff_ite heff_t3 _ hnt_c3 hcr_c3
    (fun _ _ _ hnt_push hcr_push =>
      worldEff_vibPush_vvh hAR heff_t3 w_top w_end waft
        (by simp [t3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
        (by simp [t3, t2, t1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hend_t,
              show ofString "after" ≠ ofString "end" by decide,
              show ofString "payload" ≠ ofString "end" by decide,
              show ofString "h" ≠ ofString "end" by decide])
        (by simp [t3, t2, t1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, htop_t,
              show ofString "after" ≠ ofString "top" by decide,
              show ofString "payload" ≠ ofString "top" by decide,
              show ofString "h" ≠ ofString "top" by decide])
        hnt_push hcr_push)
    (fun _ _ _ => worldEff_assign_local heff_t3 _ _)

private theorem worldEff__rlp_validate_items_body_vvh {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "_rlp_validate_items_body") vals =
      some (sourceFnBody Guest.Software.guestFn__rlp_validate_items_body, s.locals, .one))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__rlp_validate_items_body)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__rlp_validate_items_body)).1) :
    WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__rlp_validate_items_body)).2
      [] [] wsGw := by
  obtain ⟨wp, wlen, rfl, hp_lk, hlen_lk⟩ :=
    lookupCode_two_words_any_vvh (by decide) lookup__rlp_validate_items_body_vvh hl
  have heff0 : WorldEff s s [] [] wsGw := WorldEff.refl s [] [] wsGw hAR hc
  have hbody : sourceFnBody Guest.Software.guestFn__rlp_validate_items_body =
      .dec (ofString "top") .one (.const 0)
        (.dec (ofString "pos") .one (.var .local (ofString "p"))
          (.dec (ofString "end") .one (.op .add [.var .local (ofString "p"), .var .local (ofString "len")])
            (.dec (ofString "go") .one (.const 1)
              (.seq
                (.while (.cmp .notEqual (.var .local (ofString "go")) (.const 0)) vibLoopBody_vvh)
                (.return (.const 0)))))) := rfl
  rw [hbody] at hnt hres ⊢
  refine worldEff_dec heff0 _ _ _ hnt (Or.inr (Or.inr (Or.inr hres))) (fun vtop hvtop _ hnt1 hcr1 => ?_)
  have hvtop_eq : vtop = .val (.word 0) := by simp [evalHOLExact] at hvtop; exact hvtop.symm
  subst hvtop_eq
  let s1 := setVarHOLFinite (ofString "top") (.val (.word 0)) s
  have heff1 : WorldEff s s1 [] [] wsGw := heff0.locals_clock _ _
  refine worldEff_dec heff1 _ _ _ hnt1 hcr1 (fun vpos hvpos _ hnt2 hcr2 => ?_)
  have hvpos_eq : vpos = .val (.word wp) := by
    simp [s1, setVarHOLFinite, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE, hp_lk,
      show ofString "top" ≠ ofString "p" by decide] at hvpos
    exact hvpos.symm
  subst hvpos_eq
  let s2 := setVarHOLFinite (ofString "pos") (.val (.word wp)) s1
  have heff2 : WorldEff s s2 [] [] wsGw := heff1.locals_clock _ _
  refine worldEff_dec heff2 _ _ _ hnt2 hcr2 (fun vend hvend _ hnt3 hcr3 => ?_)
  have hvend_eq : vend = .val (.word (wp + wlen)) := by
    simp [s2, s1, setVarHOLFinite, evalHOLExact, evalListHOLExact, HolFiniteMapExact.lookup_update, FUPDATE,
      hp_lk, hlen_lk, valueIsWord, valueWord, wordOpHOL, wordOp,
      show ofString "pos" ≠ ofString "p" by decide, show ofString "top" ≠ ofString "p" by decide,
      show ofString "pos" ≠ ofString "len" by decide, show ofString "top" ≠ ofString "len" by decide] at hvend
    exact hvend.symm
  subst hvend_eq
  let s3 := setVarHOLFinite (ofString "end") (.val (.word (wp + wlen))) s2
  have heff3 : WorldEff s s3 [] [] wsGw := heff2.locals_clock _ _
  refine worldEff_dec heff3 _ _ _ hnt3 hcr3 (fun vgo hvgo _ hnt4 hcr4 => ?_)
  have hvgo_eq : vgo = .val (.word 1) := by simp [evalHOLExact] at hvgo; exact hvgo.symm
  subst hvgo_eq
  let s4 := setVarHOLFinite (ofString "go") (.val (.word 1)) s3
  have heff4 : WorldEff s s4 [] [] wsGw := heff3.locals_clock _ _
  have hw4 : WordLocals ["top", "pos", "end", "go"] s4 := by
    intro nm hnm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hnm
    rcases hnm with rfl | rfl | rfl | rfl
    · exact ⟨0, by simp [s4, s3, s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "go" ≠ ofString "top" by decide, show ofString "end" ≠ ofString "top" by decide,
        show ofString "pos" ≠ ofString "top" by decide]⟩
    · exact ⟨wp, by simp [s4, s3, s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "go" ≠ ofString "pos" by decide, show ofString "end" ≠ ofString "pos" by decide]⟩
    · exact ⟨wp + wlen, by simp [s4, s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "go" ≠ ofString "end" by decide]⟩
    · exact ⟨1, by simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
  have hws_vib : wsafe vibLoopBody_vvh = true := by decide
  refine worldEff_seq hnt4 hcr4
    (fun hnt_w hcr_w =>
      worldEff_while _ (WordLocals ["top", "pos", "end", "go"])
        (fun _ hinv => hinv)
        (fun t heff_t hinv_t hnt_b hcr_b =>
          ⟨worldEff_vibLoopBody_vvh hAR heff_t hinv_t hnt_b hcr_b,
           fun hf => wordLocals_flowing hws_vib hinv_t
             (by rcases hf with h | h; exact Or.inl h; exact Or.inr (Or.inr h))⟩)
        s4.clock s4 rfl heff4 hw4 hnt_w hcr_w)
    (fun mid _ heff_mid _ _ => worldEff_return heff_mid _)

private theorem handledCall_raise_keeps_local_vvh {F : Type}
    (cur mid : PanSemStateFiniteExact 64 F)
    (eid evar fname : MlS) (preProg : ProgHOL 64) (rexp : ExpHOL 64) (args : List (ExpHOL 64))
    (key : MlS) (hrun : evaluateHOLFiniteState cur
      (.call (some (none, some (eid, evar, .seq preProg (.raise eid rexp)))) fname args) = (none, mid)) :
    mid.locals.lookup key = cur.locals.lookup key := by
  rw [evaluateHOLFiniteState_call] at hrun
  rcases hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args with _ | vs
  · rw [hargs] at hrun; cases hrun
  · rw [hargs] at hrun; dsimp only at hrun
    rcases hlk : lookupCodeHOLFinite cur.code.lookup fname vs with _ | ⟨b', c', r'⟩
    · rw [hlk] at hrun; cases hrun
    · rw [hlk] at hrun; dsimp only at hrun
      by_cases hz : cur.clock = 0
      · rw [if_pos hz] at hrun; cases hrun
      · rw [if_neg hz] at hrun
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite cur c') b' with ⟨res_b, pb⟩
        rw [hb] at hrun
        cases res_b with
        | none => cases hrun
        | some rb =>
          cases rb with
          | returned rv =>
            dsimp only at hrun
            by_cases hsh : shapeEqHOL (shapeOfHOLExact rv) r' = true
            · rw [if_pos hsh] at hrun; injection hrun with _ hm; rw [← hm]
            · rw [if_neg hsh] at hrun; cases hrun
          | exception exId exVal =>
            dsimp only at hrun
            by_cases he : exId = eid
            · subst exId; rw [if_pos rfl] at hrun
              rcases hes : cur.eshapes.lookup eid with _ | esh
              · rw [hes] at hrun; cases hrun
              · rw [hes] at hrun; dsimp only at hrun
                by_cases hok : (shapeEqHOL (shapeOfHOLExact exVal) esh &&
                    isValidValueHOLExact cur.toExact .local evar exVal) = true
                · rw [if_pos hok, evaluateHOLFiniteState_seq_line780] at hrun
                  rcases hp : evaluateHOLFiniteState _ preProg with ⟨rp, mp⟩
                  rw [hp] at hrun
                  cases rp with
                  | some _ => cases hrun
                  | none =>
                    dsimp only at hrun
                    rw [evaluateHOLFiniteState_raise] at hrun
                    rcases hes2 : mp.eshapes.lookup eid with _ | esh2
                    · rw [hes2] at hrun; cases hrun
                    · rw [hes2] at hrun
                      rcases hrv : @evalHOLExact 64 F _ mp.toExact
                          (fun a => Classical.propDecidable (mp.memaddrs a)) rexp with _ | rval
                      · rw [hrv] at hrun; cases hrun
                      · rw [hrv] at hrun; dsimp only at hrun
                        split at hrun <;> cases hrun
                · rw [if_neg hok] at hrun; cases hrun
            · rw [if_neg he] at hrun; cases hrun
          | _ => cases hrun

private theorem worldEff_rlp_validate_items_vvh {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_validate_items") vals =
      some (sourceFnBody Guest.Software.guestFn_rlp_validate_items, s.locals, .one))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_validate_items)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_validate_items)).1) :
    WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_validate_items)).2
      [] [] wsGw := by
  have _ := hl
  have heff0 : WorldEff s s [] [] wsGw := WorldEff.refl s [] [] wsGw hAR hc
  have hbody : sourceFnBody Guest.Software.guestFn_rlp_validate_items =
      .decCall (ofString "mark") .one (ofString "scratch_mark") []
        (.dec (ofString "e") .one (.const 0)
          (.seq
            (.call (some (none, some (ofString "RlpErr", ofString "e",
                .seq
                  (.call (some (none, none)) (ofString "scratch_release") [.var .local (ofString "mark")])
                  (.raise (ofString "RlpErr") (.var .local (ofString "e"))))))
              (ofString "_rlp_validate_items_body") [.var .local (ofString "p"), .var .local (ofString "len")])
            (.seq
              (.call (some (none, none)) (ofString "scratch_release") [.var .local (ofString "mark")])
              (.return (.const 0))))) := rfl
  rw [hbody] at hnt hres ⊢
  refine worldEff_decCall_scratch_mark heff0 _ hnt (Or.inr (Or.inr (Or.inr hres)))
    (fun sp mid1 _ _ hsp_al hsp_lo hsp_hi hmid1_eq heff1 hnt1 hcr1 => ?_)
  refine worldEff_dec heff1 _ _ _ hnt1 hcr1 (fun ve hve _ hnt2 hcr2 => ?_)
  have hve_eq : ve = .val (.word (0 : BitVec 64)) := by simp [evalHOLExact] at hve; exact hve.symm
  subst hve_eq
  let mid2 := setVarHOLFinite (ofString "e") (.val (.word (0 : BitVec 64))) mid1
  have heff2 : WorldEff s mid2 [] [] wsGw := heff1.locals_clock _ _
  have hmark_m2 : mid2.locals.lookup (ofString "mark") = some (.val (.word sp)) := by
    simp [mid2, setVarHOLFinite, hmid1_eq, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "e" ≠ ofString "mark" by decide]
  refine worldEff_seq hnt2 hcr2
    (fun hnt_c hcr_c =>
      worldEff_handledCall heff2 none (ofString "RlpErr") (ofString "e") _
        (ofString "_rlp_validate_items_body") _
        (fun _ _ h => by cases h) (by decide) _ _ _ lookup__rlp_validate_items_body_vvh
        (fun callee cvals _ hlc hnt_cb hres_cb =>
          heff2.trans_noBuf
            (WorldEff.from_locals_clock
              (worldEff__rlp_validate_items_body_vvh (callEntryStateHOLFinite mid2 callee) cvals
                heff2.code (localsFree_arenaReady mid2 callee _ heff2.arena)
                (by simpa [heff2.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
            ws_nil_sub_vvh ws_no_gb_vvh)
        (fun exVal cpost heff_cp hnt_h hcr_h => by
          let hst := setVarHOLFinite (ofString "e") exVal { cpost with locals := mid2.locals }
          have heff_hst : WorldEff s hst [] [] wsGw := heff_cp.locals_clock _ _
          have hmark_hst : @evalHOLExact 64 F _ hst.toExact (fun a => Classical.propDecidable (hst.memaddrs a))
              (.var .local (ofString "mark")) = some (.val (.word sp)) := by
            simp [hst, setVarHOLFinite, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE, hmark_m2,
              show ofString "e" ≠ ofString "mark" by decide]
          exact worldEff_seq hnt_h hcr_h
            (fun hnt_sr _ => (worldEff_call0_scratch_release hAR.2 heff_hst (by decide) _ sp hmark_hst hsp_lo hsp_hi hsp_al hnt_sr).2.choose_spec.2)
            (fun m_sr _ heff_sr _ _ => worldEff_raise heff_sr _ _))
        hnt_c hcr_c)
    (fun mid3 hmid3 heff3 hnt3 hcr3 => ?_)
  have hmark_m3 : mid3.locals.lookup (ofString "mark") = some (.val (.word sp)) := by
    rw [handledCall_raise_keeps_local_vvh mid2 mid3 _ _ _ _ _ _ _ hmid3]
    exact hmark_m2
  have hmark_ev3 : @evalHOLExact 64 F _ mid3.toExact (fun a => Classical.propDecidable (mid3.memaddrs a))
      (.var .local (ofString "mark")) = some (.val (.word sp)) := hmark_m3
  exact worldEff_seq hnt3 hcr3
    (fun hnt_sr _ => (worldEff_call0_scratch_release hAR.2 heff3 (by decide) _ sp hmark_ev3 hsp_lo hsp_hi hsp_al hnt_sr).2.choose_spec.2)
    (fun m_sr _ heff_sr _ _ => worldEff_return heff_sr _)

private theorem worldEff_rlp_item_total_vvh {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_item_total") vals =
      some (sourceFnBody Guest.Software.guestFn_rlp_item_total, s.locals, .one))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_item_total)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_item_total)).1) :
    WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_item_total)).2
      [] [] wsGw := by
  have _ := hl
  have heff0 : WorldEff s s [] [] wsGw := WorldEff.refl s [] [] wsGw hAR hc
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_item_total,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_decCall_ro heff0 InitECandidate.Solver.Wave8GuestInv.R13.ro_rlp_item_header
    _ _ _ hnt (Or.inr (Or.inr (Or.inr hres))) (fun rvh cpost _ hcpost hnt1 hcr1 => ?_)
  let s1 := setVarHOLFinite (ofString "h") rvh { cpost with locals := s.locals }
  have heff1 : WorldEff s s1 [] [] wsGw := (heff0.of_readOnly hcpost).locals_clock _ _
  refine worldEff_seq hnt1 hcr1
    (fun hnt_i hcr_i =>
      worldEff_ite heff1 _ hnt_i hcr_i
        (fun _ _ _ hnt_c hcr_c =>
          worldEff_call0_eff heff1 (ofString "rlp_validate_items") _ _ _ _ lookup_rlp_validate_items_vvh
            (fun callee cvals _ hlc hnt_cb hres_cb =>
              heff1.trans_noBuf
                (WorldEff.from_locals_clock
                  (worldEff_rlp_validate_items_vvh (callEntryStateHOLFinite s1 callee) cvals
                    heff1.code (localsFree_arenaReady s1 callee _ heff1.arena)
                    (by simpa [heff1.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
                ws_nil_sub_vvh ws_no_gb_vvh)
            hnt_c hcr_c)
        (fun _ _ _ => worldEff_skip heff1))
    (fun mid _ heff_mid _ _ => worldEff_return heff_mid _)

private theorem worldEff_rlp_list_count_vvh {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_list_count") vals =
      some (sourceFnBody Guest.Software.guestFn_rlp_list_count, s.locals, .one))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_count)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_count)).1) :
    WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_count)).2
      [] [] wsGw := by
  have _ := hl
  have heff0 : WorldEff s s [] [] wsGw := WorldEff.refl s [] [] wsGw hAR hc
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_list_count,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_dec heff0 _ _ _ hnt (Or.inr (Or.inr (Or.inr hres))) (fun vcnt _ _ hnt1 hcr1 => ?_)
  let s1 := setVarHOLFinite (ofString "count") vcnt s
  have heff1 : WorldEff s s1 [] [] wsGw := heff0.locals_clock _ _
  refine worldEff_dec heff1 _ _ _ hnt1 hcr1 (fun voff _ _ hnt2 hcr2 => ?_)
  let s2 := setVarHOLFinite (ofString "off") voff s1
  have heff2 : WorldEff s s2 [] [] wsGw := heff1.locals_clock _ _
  refine worldEff_seq hnt2 hcr2
    (fun hnt_w hcr_w =>
      worldEff_while _ (fun _ => True) (fun _ _ => trivial)
        (fun t heff_t _ hnt_b hcr_b =>
          ⟨worldEff_decCall_eff heff_t (ofString "total") .one (ofString "rlp_item_total") _ _ _ _ lookup_rlp_item_total_vvh
            (fun callee cvals _ hlc hnt_cb hres_cb =>
              heff_t.trans_noBuf
                (WorldEff.from_locals_clock
                  (worldEff_rlp_item_total_vvh (callEntryStateHOLFinite t callee) cvals
                    heff_t.code (localsFree_arenaReady t callee _ heff_t.arena)
                    (by simpa [heff_t.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
                ws_nil_sub_vvh ws_no_gb_vvh)
            (fun _ _ rv cpost _ _ _ _ heff_cp hnt_k hcr_k =>
              worldEff_seq hnt_k hcr_k
                (fun _ _ => worldEff_assign_local (heff_cp.locals_clock _ _) _ _)
                (fun m2 _ heff_m2 _ _ => worldEff_assign_local heff_m2 _ _))
            hnt_b hcr_b,
           fun _ => trivial⟩)
        s2.clock s2 rfl heff2 trivial hnt_w hcr_w)
    (fun mid _ heff_mid _ _ => worldEff_return heff_mid _)

private theorem worldEff_rlp_item_vvh {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_item") vals =
      some (sourceFnBody Guest.Software.guestFn_rlp_item, s.locals, .comb [.one, .one, .one, .one]))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_item)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_item)).1) :
    WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_item)).2
      [] [] wsGw := by
  have _ := hl
  have heff0 : WorldEff s s [] [] wsGw := WorldEff.refl s [] [] wsGw hAR hc
  have hrf := InitECandidate.Solver.Wave8GuestInv.R13.ro_rlp_fail
  have hrrl := InitECandidate.Solver.Wave8GuestInv.R13.ro_rlp_read_length
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_item,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_seq hnt (Or.inr (Or.inr (Or.inr hres)))
    (fun hnt_0 hcr_0 =>
      worldEff_ite heff0 _ hnt_0 hcr_0
        (fun _ _ _ hnt_f hcr_f => worldEff_call0_ro heff0 hrf _ hnt_f hcr_f)
        (fun _ _ _ => worldEff_skip heff0))
    (fun m0 _ heff_m0 hnt_m0 hcr_m0 => ?_)
  refine worldEff_dec heff_m0 _ _ _ hnt_m0 hcr_m0 (fun vb _ _ hnt_b hcr_b => ?_)
  let sb := setVarHOLFinite (ofString "b") vb m0
  have heff_sb : WorldEff s sb [] [] wsGw := heff_m0.locals_clock _ _
  refine worldEff_seq hnt_b hcr_b
    (fun hnt_1 hcr_1 =>
      worldEff_ite heff_sb _ hnt_1 hcr_1
        (fun _ _ _ _ _ => worldEff_return heff_sb _)
        (fun _ _ _ => worldEff_skip heff_sb))
    (fun m1 _ heff_m1 hnt_m1 hcr_m1 => ?_)
  refine worldEff_seq hnt_m1 hcr_m1
    (fun hnt_2 hcr_2 =>
      worldEff_ite heff_m1 _ hnt_2 hcr_2
        (fun _ _ _ hnt_t2 hcr_t2 =>
          worldEff_dec heff_m1 _ _ _ hnt_t2 hcr_t2 (fun vn _ _ hnt_n hcr_n =>
            let sn := setVarHOLFinite (ofString "n") vn m1
            have heff_sn : WorldEff s sn [] [] wsGw := heff_m1.locals_clock _ _
            worldEff_seq hnt_n hcr_n
              (fun hnt_c1 hcr_c1 =>
                worldEff_ite heff_sn _ hnt_c1 hcr_c1
                  (fun _ _ _ hnt_f hcr_f => worldEff_call0_ro heff_sn hrf _ hnt_f hcr_f)
                  (fun _ _ _ => worldEff_skip heff_sn))
              (fun mn1 _ heff_mn1 hnt_c2 hcr_c2 =>
                worldEff_seq hnt_c2 hcr_c2
                  (fun hnt_c3 hcr_c3 =>
                    worldEff_ite heff_mn1 _ hnt_c3 hcr_c3
                      (fun _ _ _ hnt_c4 hcr_c4 =>
                        worldEff_ite heff_mn1 _ hnt_c4 hcr_c4
                          (fun _ _ _ hnt_f hcr_f => worldEff_call0_ro heff_mn1 hrf _ hnt_f hcr_f)
                          (fun _ _ _ => worldEff_skip heff_mn1))
                      (fun _ _ _ => worldEff_skip heff_mn1))
                  (fun mn2 _ heff_mn2 _ _ => worldEff_return heff_mn2 _))))
        (fun _ _ _ => worldEff_skip heff_m1))
    (fun m2 _ heff_m2 hnt_m2 hcr_m2 => ?_)
  refine worldEff_seq hnt_m2 hcr_m2
    (fun hnt_3 hcr_3 =>
      worldEff_ite heff_m2 _ hnt_3 hcr_3
        (fun _ _ _ hnt_t3 hcr_t3 =>
          worldEff_dec heff_m2 _ _ _ hnt_t3 hcr_t3 (fun vll _ _ hnt_ll hcr_ll =>
            let sll := setVarHOLFinite (ofString "ll") vll m2
            have heff_sll : WorldEff s sll [] [] wsGw := heff_m2.locals_clock _ _
            worldEff_seq hnt_ll hcr_ll
              (fun hnt_c1 hcr_c1 =>
                worldEff_ite heff_sll _ hnt_c1 hcr_c1
                  (fun _ _ _ hnt_f hcr_f => worldEff_call0_ro heff_sll hrf _ hnt_f hcr_f)
                  (fun _ _ _ => worldEff_skip heff_sll))
              (fun mll1 _ heff_mll1 hnt_dc hcr_dc =>
                worldEff_decCall_ro heff_mll1 hrrl _ _ _ hnt_dc hcr_dc (fun rvn cpost _ hcpost hnt_k hcr_k =>
                  let mll2 := setVarHOLFinite (ofString "n") rvn { cpost with locals := mll1.locals }
                  have heff_mll2 : WorldEff s mll2 [] [] wsGw := (heff_mll1.of_readOnly hcpost).locals_clock _ _
                  worldEff_seq hnt_k hcr_k
                    (fun hnt_k1 hcr_k1 =>
                      worldEff_ite heff_mll2 _ hnt_k1 hcr_k1
                        (fun _ _ _ hnt_f hcr_f => worldEff_call0_ro heff_mll2 hrf _ hnt_f hcr_f)
                        (fun _ _ _ => worldEff_skip heff_mll2))
                    (fun mll3 _ heff_mll3 hnt_k2 hcr_k2 =>
                      worldEff_seq hnt_k2 hcr_k2
                        (fun hnt_k3 hcr_k3 =>
                          worldEff_ite heff_mll3 _ hnt_k3 hcr_k3
                            (fun _ _ _ hnt_f hcr_f => worldEff_call0_ro heff_mll3 hrf _ hnt_f hcr_f)
                            (fun _ _ _ => worldEff_skip heff_mll3))
                        (fun mll4 _ heff_mll4 _ _ => worldEff_return heff_mll4 _))))))
        (fun _ _ _ => worldEff_skip heff_m2))
    (fun m3 _ heff_m3 hnt_m3 hcr_m3 => ?_)
  refine worldEff_seq hnt_m3 hcr_m3
    (fun hnt_4 hcr_4 =>
      worldEff_ite heff_m3 _ hnt_4 hcr_4
        (fun _ _ _ hnt_t4 hcr_t4 =>
          worldEff_dec heff_m3 _ _ _ hnt_t4 hcr_t4 (fun vn _ _ hnt_n hcr_n =>
            let sn := setVarHOLFinite (ofString "n") vn m3
            have heff_sn : WorldEff s sn [] [] wsGw := heff_m3.locals_clock _ _
            worldEff_seq hnt_n hcr_n
              (fun hnt_c1 hcr_c1 =>
                worldEff_ite heff_sn _ hnt_c1 hcr_c1
                  (fun _ _ _ hnt_f hcr_f => worldEff_call0_ro heff_sn hrf _ hnt_f hcr_f)
                  (fun _ _ _ => worldEff_skip heff_sn))
              (fun mn1 _ heff_mn1 hnt_c2 hcr_c2 =>
                worldEff_seq hnt_c2 hcr_c2
                  (fun hnt_lc hcr_lc =>
                    worldEff_call0_eff heff_mn1 (ofString "rlp_list_count") _ _ _ _ lookup_rlp_list_count_vvh
                      (fun callee cvals _ hlc hnt_cb hres_cb =>
                        heff_mn1.trans_noBuf
                          (WorldEff.from_locals_clock
                            (worldEff_rlp_list_count_vvh (callEntryStateHOLFinite mn1 callee) cvals
                              heff_mn1.code (localsFree_arenaReady mn1 callee _ heff_mn1.arena)
                              (by simpa [heff_mn1.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
                          ws_nil_sub_vvh ws_no_gb_vvh)
                      hnt_lc hcr_lc)
                  (fun mn2 _ heff_mn2 _ _ => worldEff_return heff_mn2 _))))
        (fun _ _ _ => worldEff_skip heff_m3))
    (fun m4 _ heff_m4 hnt_m4 hcr_m4 => ?_)
  refine worldEff_dec heff_m4 _ _ _ hnt_m4 hcr_m4 (fun vll _ _ hnt_ll hcr_ll => ?_)
  let sll := setVarHOLFinite (ofString "ll") vll m4
  have heff_sll : WorldEff s sll [] [] wsGw := heff_m4.locals_clock _ _
  refine worldEff_seq hnt_ll hcr_ll
    (fun hnt_c1 hcr_c1 =>
      worldEff_ite heff_sll _ hnt_c1 hcr_c1
        (fun _ _ _ hnt_f hcr_f => worldEff_call0_ro heff_sll hrf _ hnt_f hcr_f)
        (fun _ _ _ => worldEff_skip heff_sll))
    (fun mll1 _ heff_mll1 hnt_dc hcr_dc =>
      worldEff_decCall_ro heff_mll1 hrrl _ _ _ hnt_dc hcr_dc (fun rvn cpost _ hcpost hnt_k hcr_k =>
        let mll2 := setVarHOLFinite (ofString "n") rvn { cpost with locals := mll1.locals }
        have heff_mll2 : WorldEff s mll2 [] [] wsGw := (heff_mll1.of_readOnly hcpost).locals_clock _ _
        worldEff_seq hnt_k hcr_k
          (fun hnt_k1 hcr_k1 =>
            worldEff_ite heff_mll2 _ hnt_k1 hcr_k1
              (fun _ _ _ hnt_f hcr_f => worldEff_call0_ro heff_mll2 hrf _ hnt_f hcr_f)
              (fun _ _ _ => worldEff_skip heff_mll2))
          (fun mll3 _ heff_mll3 hnt_k2 hcr_k2 =>
            worldEff_seq hnt_k2 hcr_k2
              (fun hnt_k3 hcr_k3 =>
                worldEff_ite heff_mll3 _ hnt_k3 hcr_k3
                  (fun _ _ _ hnt_f hcr_f => worldEff_call0_ro heff_mll3 hrf _ hnt_f hcr_f)
                  (fun _ _ _ => worldEff_skip heff_mll3))
              (fun mll4 _ heff_mll4 hnt_k4 hcr_k4 =>
                worldEff_seq hnt_k4 hcr_k4
                  (fun hnt_lc hcr_lc =>
                    worldEff_call0_eff heff_mll4 (ofString "rlp_list_count") _ _ _ _ lookup_rlp_list_count_vvh
                      (fun callee cvals _ hlc hnt_cb hres_cb =>
                        heff_mll4.trans_noBuf
                          (WorldEff.from_locals_clock
                            (worldEff_rlp_list_count_vvh (callEntryStateHOLFinite mll4 callee) cvals
                              heff_mll4.code (localsFree_arenaReady mll4 callee _ heff_mll4.arena)
                              (by simpa [heff_mll4.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
                          ws_nil_sub_vvh ws_no_gb_vvh)
                      hnt_lc hcr_lc)
                  (fun mll5 _ heff_mll5 _ _ => worldEff_return heff_mll5 _)))))

private theorem worldEff_rlp_decode_fully_vvh {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_decode_fully") vals =
      some (sourceFnBody Guest.Software.guestFn_rlp_decode_fully, s.locals, .comb [.one, .one, .one, .one]))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_decode_fully)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_decode_fully)).1) :
    WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_decode_fully)).2
      [] [] wsGw := by
  have _ := hl
  have heff0 : WorldEff s s [] [] wsGw := WorldEff.refl s [] [] wsGw hAR hc
  have hrf := InitECandidate.Solver.Wave8GuestInv.R13.ro_rlp_fail
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_decode_fully,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_decCall_eff heff0 (ofString "it") (.comb [.one, .one, .one, .one])
    (ofString "rlp_item") _ _ _ _ lookup_rlp_item_vvh
    (fun callee cvals _ hlc hnt_cb hres_cb =>
      heff0.trans_noBuf
        (WorldEff.from_locals_clock
          (worldEff_rlp_item_vvh (callEntryStateHOLFinite s callee) cvals
            heff0.code (localsFree_arenaReady s callee _ heff0.arena)
            (by simpa [heff0.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
        ws_nil_sub_vvh ws_no_gb_vvh)
    (fun _ _ rv cpost _ _ _ _ heff_cp hnt_k hcr_k =>
      let m1 := setVarHOLFinite (ofString "it") rv { cpost with locals := s.locals }
      have heff_m1 : WorldEff s m1 [] [] wsGw := heff_cp.locals_clock _ _
      worldEff_seq hnt_k hcr_k
        (fun hnt_i hcr_i =>
          worldEff_ite heff_m1 _ hnt_i hcr_i
            (fun _ _ _ hnt_f hcr_f => worldEff_call0_ro heff_m1 hrf _ hnt_f hcr_f)
            (fun _ _ _ => worldEff_skip heff_m1))
        (fun m2 _ heff_m2 _ _ => worldEff_return heff_m2 _))
    hnt (Or.inr (Or.inr (Or.inr hres)))

/-! ### `rlp_list_count` return bound (`wcnt.toNat ≤ domainBytes`) & `rlp_list_to_slices` -/

private def RetOK_vvh (Q : ValueHOL 64 → Prop) {F : Type} (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64) :
    Prop :=
  ∀ v, (evaluateHOLFiniteState s p).1 = some (.returned v) → Q v

private theorem R_seq_vvh {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64}
    (ha : RetOK_vvh Q s a) (hb : ∀ mid, evaluateHOLFiniteState s a = (none, mid) → RetOK_vvh Q mid b) :
    RetOK_vvh Q s (.seq a b) := by
  intro v hv
  rw [evaluateHOLFiniteState_seq_line780] at hv
  rcases hr : evaluateHOLFiniteState s a with ⟨r, mid⟩
  rw [hr] at hv
  cases r with
  | none => exact hb mid hr v hv
  | some _ => apply ha v; rw [hr]; simpa using hv

private theorem R_ite_vvh {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {c : ExpHOL 64}
    {yes no : ProgHOL 64}
    (h : ∀ w : BitVec 64, @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) c =
      some (.val (.word w)) → (w ≠ 0 → RetOK_vvh Q s yes) ∧ (w = 0 → RetOK_vvh Q s no)) :
    RetOK_vvh Q s (.ite c yes no) := by
  intro v hv
  rw [evaluateHOLFiniteState_ite] at hv
  split at hv
  · rename_i w hw
    split at hv
    · exact (h w hw).2 (by assumption) v hv
    · exact (h w hw).1 (by assumption) v hv
  · simp at hv

private theorem R_dec_vvh {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {n : MlS}
    {sh : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (h : ∀ v, @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) init =
      some v → shapeEqHOL sh (shapeOfHOLExact v) = true → RetOK_vvh Q (setVarHOLFinite n v s) body) :
    RetOK_vvh Q s (.dec n sh init body) := by
  intro v hv
  rw [evaluateHOLFiniteState_dec_total] at hv
  dsimp only at hv
  split at hv
  · simp at hv
  · rename_i val hval
    split at hv
    · rename_i hsh; exact h val hval hsh v hv
    · simp at hv

private theorem R_ret_vvh {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {e : ExpHOL 64}
    (h : ∀ v, @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e =
      some v → Q v) :
    RetOK_vvh Q s (.return e) := by
  intro v hv
  rw [evaluateHOLFiniteState_return] at hv
  split at hv
  · simp at hv
  · rename_i val hval
    split at hv
    · simp at hv; subst hv; exact h val hval
    · simp at hv

private theorem R_skip_vvh {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} :
    RetOK_vvh Q s .skip := by
  intro v hv; rw [evaluateHOLFiniteState_skip] at hv; simp at hv

private theorem rlp_fail_noret_vvh {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_fail)).1 ≠ some (.returned v) := by
  have hb : sourceFnBody Guest.Software.guestFn_rlp_fail =
      .seq (.raise (ofString "RlpErr") (.var .local (ofString "code"))) (.return (.const 0)) := rfl
  have hraise : ∀ w, (evaluateHOLFiniteState s (.raise (ofString "RlpErr") (.var .local (ofString "code")) :
        ProgHOL 64)).1 ≠ some (.returned w) ∧
      (evaluateHOLFiniteState s (.raise (ofString "RlpErr") (.var .local (ofString "code")) :
        ProgHOL 64)).1 ≠ none := by
    intro w
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> simp
    · simp
  rw [hb, evaluateHOLFiniteState_seq_line780]
  rcases hr : evaluateHOLFiniteState s (.raise (ofString "RlpErr") (.var .local (ofString "code")) :
    ProgHOL 64) with ⟨r, mid⟩
  rw [hr] at hraise
  cases r with
  | none => exact absurd rfl (hraise v).2
  | some _ => dsimp only; exact (hraise v).1

private theorem lookup_rlp_fail_vvh : originalRuntimeCode.lookup (ofString "rlp_fail") =
    some ([(ofString "code", .one)], sourceFnBody Guest.Software.guestFn_rlp_fail, .one) :=
  lookup_of_guestAst_getElem 105 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_fail) rfl

private theorem lookup_rlp_item_header_vvh : originalRuntimeCode.lookup (ofString "rlp_item_header") =
    some ([(ofString "p", .one), (ofString "len", .one)],
      sourceFnBody Guest.Software.guestFn_rlp_item_header, .comb [.one, .one, .one]) :=
  lookup_of_guestAst_getElem 109 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_item_header) rfl

private theorem call_noret_vvh {F : Type} (s : PanSemStateFiniteExact 64 F) (f : MlS) (args : List (ExpHOL 64))
    (v : ValueHOL 64) :
    (evaluateHOLFiniteState s (.call (some (none, none)) f args)).1 ≠ some (.returned v) := by
  rw [evaluateHOLFiniteState_call]
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s _) _ with ⟨r, st⟩
        rcases r with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only <;> (repeat' split) <;> simp

private theorem call_fail_nonone_vvh {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (args : List (ExpHOL 64)) :
    (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "rlp_fail") args)).1 ≠ none := by
  rw [evaluateHOLFiniteState_call]
  split
  · simp
  · rename_i values _
    split
    · simp
    · rename_i body callee rs hl
      have hb := lookupCodeHOLFinite_installed_body s.code.lookup _ _ _ body _ rs values callee
        (by rw [hcode]; exact lookup_rlp_fail_vvh) hl
      subst hb
      split
      · simp
      · have hnr := fun w => rlp_fail_noret_vvh (callEntryStateHOLFinite s callee) w
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
            (sourceFnBody Guest.Software.guestFn_rlp_fail) with ⟨r, st⟩
        rw [hrun] at hnr
        rcases r with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only <;> (repeat' split) <;> try simp
        exact absurd rfl (hnr w)

private theorem R_guard_vvh {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hcode : s.code = originalRuntimeCode) {c : ExpHOL 64} {args : List (ExpHOL 64)} {rest : ProgHOL 64}
    (h : ∀ w : BitVec 64, @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) c =
      some (.val (.word w)) → w = 0 → RetOK_vvh Q s rest) :
    RetOK_vvh Q s (.seq (.ite c (.call (some (none, none)) (ofString "rlp_fail") args) .skip) rest) := by
  apply R_seq_vvh
  · apply R_ite_vvh
    intro w _
    exact ⟨fun _ v hv => absurd hv (call_noret_vvh s _ args v), fun _ => R_skip_vvh⟩
  · intro mid hmid
    rw [evaluateHOLFiniteState_ite] at hmid
    split at hmid
    · rename_i w hw
      split at hmid
      · rename_i hw0
        rw [evaluateHOLFiniteState_skip] at hmid
        simp only [Prod.mk.injEq] at hmid
        obtain ⟨-, rfl⟩ := hmid
        exact h w hw hw0
      · exact absurd (by rw [hmid]) (call_fail_nonone_vvh s hcode args)
    · simp at hmid

private theorem R_decCall_vvh {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {n : MlS}
    {sh : ShapeHOL} {f : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (h : ∀ (u : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), shapeEqHOL (shapeOfHOLExact v) sh = true →
      u.code = s.code → (∀ k, k ≠ n → u.locals.lookup k = s.locals.lookup k) →
      u.locals.lookup n = some v → RetOK_vvh Q u cont) :
    RetOK_vvh Q s (.decCall n sh f args cont) := by
  intro v hv
  rw [evaluateHOLFiniteState_decCall_total] at hv
  split at hv
  · simp at hv
  · split at hv
    · simp at hv
    · rename_i body callee rs _
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
          refine h _ w hsh.1 (by simp [setVarHOLFinite, fixClockHOLFinite, hmeta]) ?_ ?_ v hv
          · intro k hk
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
          · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        · simp at hv

private theorem R_decCall'_vvh {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {n : MlS}
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
        RetOK_vvh Q u cont) :
    RetOK_vvh Q s (.decCall n sh f args cont) := by
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

private def abrupt_vvh : ProgHOL 64 → Bool
  | .return _ => true
  | .raise _ _ => true
  | .seq _ b => abrupt_vvh b
  | .dec _ _ _ b => abrupt_vvh b
  | .decCall _ _ _ _ c => abrupt_vvh c
  | .ite _ y n => abrupt_vvh y && abrupt_vvh n
  | _ => false

private theorem abrupt_nonone_vvh {F : Type} (p : ProgHOL 64) (h : abrupt_vvh p = true) (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s p).1 ≠ none := by
  match p, h with
  | .return e, _ =>
    rw [evaluateHOLFiniteState_return]
    split
    · simp
    · split <;> simp
  | .raise n e, _ =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> simp
    · simp
  | .seq a b, h =>
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hr : evaluateHOLFiniteState s a with ⟨r, mid⟩
    cases r with
    | none => exact abrupt_nonone_vvh b (by simpa [abrupt_vvh] using h) mid
    | some _ => simp
  | .dec n sh e b, h =>
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · split
      · exact abrupt_nonone_vvh b (by simpa [abrupt_vvh] using h) _
      · simp
  | .decCall n sh f args c, h =>
    rw [evaluateHOLFiniteState_decCall_total]
    split
    · simp
    · split
      · simp
      · rename_i body callee rs _
        split
        · simp
        · rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, st⟩
          simp only [hrun]
          rcases r with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only <;> try simp
          split
          · exact abrupt_nonone_vvh c (by simpa [abrupt_vvh] using h) _
          · simp
  | .ite c y n, h =>
    have hh : abrupt_vvh y = true ∧ abrupt_vvh n = true := by simpa [abrupt_vvh] using h
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact abrupt_nonone_vvh n hh.2 s
      · exact abrupt_nonone_vvh y hh.1 s
    · simp

private theorem R_branch_vvh {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {c : ExpHOL 64}
    {yes rest : ProgHOL 64} (hab : abrupt_vvh yes = true)
    (hy : ∀ w : BitVec 64, @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) c =
      some (.val (.word w)) → w ≠ 0 → RetOK_vvh Q s yes)
    (hr : ∀ w : BitVec 64, @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) c =
      some (.val (.word w)) → w = 0 → RetOK_vvh Q s rest) :
    RetOK_vvh Q s (.seq (.ite c yes .skip) rest) := by
  apply R_seq_vvh
  · apply R_ite_vvh
    intro w hw
    exact ⟨hy w hw, fun _ => R_skip_vvh⟩
  · intro mid hmid
    rw [evaluateHOLFiniteState_ite] at hmid
    split at hmid
    · rename_i w hw
      split at hmid
      · rename_i hw0
        rw [evaluateHOLFiniteState_skip] at hmid
        simp only [Prod.mk.injEq] at hmid
        obtain ⟨-, rfl⟩ := hmid
        exact hr w hw hw0
      · exact absurd (by rw [hmid]) (abrupt_nonone_vvh yes hab s)
    · simp at hmid

private theorem R_check2_vvh {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hcode : s.code = originalRuntimeCode) {c c' : ExpHOL 64} {args : List (ExpHOL 64)} {rest : ProgHOL 64}
    (hr : RetOK_vvh Q s rest) :
    RetOK_vvh Q s (.seq (.ite c (.ite c' (.call (some (none, none)) (ofString "rlp_fail") args) .skip) .skip)
      rest) := by
  apply R_seq_vvh
  · apply R_ite_vvh
    intro w _
    refine ⟨fun _ => ?_, fun _ => R_skip_vvh⟩
    apply R_ite_vvh
    intro w' _
    exact ⟨fun _ v hv => absurd hv (call_noret_vvh s _ args v), fun _ => R_skip_vvh⟩
  · intro mid hmid
    rw [evaluateHOLFiniteState_ite] at hmid
    split at hmid
    · split at hmid
      · rw [evaluateHOLFiniteState_skip] at hmid
        simp only [Prod.mk.injEq] at hmid
        obtain ⟨-, rfl⟩ := hmid
        exact hr
      · rw [evaluateHOLFiniteState_ite] at hmid
        split at hmid
        · split at hmid
          · rw [evaluateHOLFiniteState_skip] at hmid
            simp only [Prod.mk.injEq] at hmid
            obtain ⟨-, rfl⟩ := hmid
            exact hr
          · exact absurd (by rw [hmid]) (call_fail_nonone_vvh s hcode args)
        · simp at hmid
    · simp at hmid

private def hval_vvh (a b c : BitVec 64) : ValueHOL 64 :=
  .rStruct [.val (.word a), .val (.word b), .val (.word c)]

private def HdrQ_vvh (L : BitVec 64) (v : ValueHOL 64) : Prop :=
  ∃ a b c : BitVec 64, v = hval_vvh a b c ∧ 1 ≤ a.toNat + b.toNat ∧ a.toNat + b.toNat ≤ L.toNat

private theorem loadByte_word_dom_vvh {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) (v : ValueHOL 64)
    (hv : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) (.loadByte e) =
      some v) :
    ∃ a B : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e =
        some (.val (.word a)) ∧
      s.memaddrs (panByteAlignHOL (width := 64) a) ∧
      v = .val (.word B) := by
  simp only [evalHOLExact] at hv
  split at hv
  · rename_i a ha
    dsimp only [panMemLoadByteHOL] at hv
    split at hv
    · rename_i hdom
      simp only [Option.map_some, Option.some.injEq] at hv
      exact ⟨a, _, ha, hdom, hv.symm⟩
    · simp at hv
  · simp at hv

private theorem lk_set_vvh {F : Type} (st : PanSemStateFiniteExact 64 F) (k : MlS) (x : ValueHOL 64) (k' : MlS)
    (hk : k ≠ k') : (setVarHOLFinite k x st).locals.lookup k' = st.locals.lookup k' := by
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hk]

private theorem lk_set'_vvh {F : Type} (st : PanSemStateFiniteExact 64 F) (k : MlS) (x : ValueHOL 64) :
    (setVarHOLFinite k x st).locals.lookup k = some x := by
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

private theorem toNat_sub_one_vvh (L : BitVec 64) (hL : L ≠ 0) : (L - 1#64).toNat = L.toNat - 1 := by
  have : L.toNat ≠ 0 := fun h => hL (BitVec.eq_of_toNat_eq (by simpa using h))
  rw [BitVec.toNat_sub]; simp; omega

private theorem short_branch_vvh {F : Type} (st : PanSemStateFiniteExact 64 F) (hcode : st.code = originalRuntimeCode)
    (L B off flag : BitVec 64) (hL : L ≠ 0)
    (hl : st.locals.lookup (ofString "len") = some (.val (.word L)))
    (hb : st.locals.lookup (ofString "b") = some (.val (.word B))) :
    RetOK_vvh (HdrQ_vvh L) st
      (.dec (ofString "n") .one (.op .sub [.var .local (ofString "b"), .const off])
        (.seq (.ite (.cmp .lower (.op .sub [.var .local (ofString "len"), .const 1#64])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "rlp_fail") [.const 3#64]) .skip)
          (.return (.rstruct [.const 1#64, .var .local (ofString "n"), .const flag])))) := by
  refine R_dec_vvh (fun v hv _ => ?_)
  simp [evalHOLExact, evalListHOLExact, hb, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
  subst hv
  refine R_guard_vvh (by exact hcode) (fun w hw hw0 => R_ret_vvh (fun v hv => ?_))
  have hL1 := toNat_sub_one_vvh L hL
  have hne_nlen : ofString "n" ≠ ofString "len" := by decide
  have hN : (B - off).toNat ≤ L.toNat - 1 := by
    simp [evalHOLExact, evalListHOLExact, lk_set_vvh, lk_set'_vvh, hne_nlen, hl, wordOpHOL, wordOp, valueIsWord,
      valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hw
    subst hw0
    by_contra hc
    have : L - 1#64 < B - off := by rw [BitVec.lt_def, hL1]; omega
    simp [this] at hw
  simp [evalHOLExact, evalListHOLExact, lk_set_vvh, lk_set'_vvh] at hv
  subst hv
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  refine ⟨1, B - off, flag, rfl, by simp, ?_⟩
  rw [h1]
  have : L.toNat ≠ 0 := fun h => hL (BitVec.eq_of_toNat_eq (by simpa using h))
  omega

private theorem long_branch_vvh {F : Type} (st : PanSemStateFiniteExact 64 F) (hcode : st.code = originalRuntimeCode)
    (L B off flag : BitVec 64) (hL : L ≠ 0)
    (hl : st.locals.lookup (ofString "len") = some (.val (.word L)))
    (hb : st.locals.lookup (ofString "b") = some (.val (.word B))) :
    RetOK_vvh (HdrQ_vvh L) st
      (.dec (ofString "ll") .one (.op .sub [.var .local (ofString "b"), .const off])
        (.seq (.ite (.cmp .lower (.op .sub [.var .local (ofString "len"), .const 1#64])
              (.var .local (ofString "ll")))
            (.call (some (none, none)) (ofString "rlp_fail") [.const 3#64]) .skip)
          (.decCall (ofString "n") .one (ofString "rlp_read_length")
            [.op .add [.var .local (ofString "p"), .const 1#64], .var .local (ofString "ll")]
            (.seq (.ite (.cmp .notLower (.const 55#64) (.var .local (ofString "n")))
                (.call (some (none, none)) (ofString "rlp_fail") [.const 5#64]) .skip)
              (.seq (.ite (.cmp .lower (.op .sub [.op .sub [.var .local (ofString "len"), .const 1#64],
                    .var .local (ofString "ll")]) (.var .local (ofString "n")))
                  (.call (some (none, none)) (ofString "rlp_fail") [.const 3#64]) .skip)
                (.return (.rstruct [.op .add [.const 1#64, .var .local (ofString "ll")],
                  .var .local (ofString "n"), .const flag]))))))) := by
  refine R_dec_vvh (fun v hv _ => ?_)
  simp [evalHOLExact, evalListHOLExact, hb, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
  subst hv
  have hL1 := toNat_sub_one_vvh L hL
  have hne_ll_len : ofString "ll" ≠ ofString "len" := by decide
  refine R_guard_vvh (by exact hcode) (fun w hw hw0 => ?_)
  have hLL : (B - off).toNat ≤ L.toNat - 1 := by
    simp [evalHOLExact, evalListHOLExact, lk_set_vvh, lk_set'_vvh, hne_ll_len, hl, wordOpHOL, wordOp, valueIsWord,
      valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hw
    subst hw0
    by_contra hc
    have : L - 1#64 < B - off := by rw [BitVec.lt_def, hL1]; omega
    simp [this] at hw
  refine R_decCall_vvh (fun u v hsh hcu hloc hn => ?_)
  have hvw : ∃ N : BitVec 64, v = .val (.word N) := by
    rcases v with ⟨⟨N⟩⟩ | fs | ⟨nm, fs⟩ <;> simp_all [shapeEqHOL, shapeOfHOLExact]
  obtain ⟨N, rfl⟩ := hvw
  have hul : u.locals.lookup (ofString "len") = some (.val (.word L)) := by
    rw [hloc _ (by decide), lk_set_vvh _ _ _ _ (by decide)]; exact hl
  have hull : u.locals.lookup (ofString "ll") = some (.val (.word (B - off))) := by
    rw [hloc _ (by decide), lk_set'_vvh]
  have hcu' : u.code = originalRuntimeCode := hcu.trans hcode
  refine R_guard_vvh hcu' (fun w _ _ => ?_)
  refine R_guard_vvh hcu' (fun w hw hw0 => R_ret_vvh (fun v hv => ?_))
  have hsub : (L - 1#64 - (B - off)).toNat = L.toNat - 1 - (B - off).toNat := by
    rw [BitVec.toNat_sub, hL1]; have := (B - off).isLt; omega
  have hNle : N.toNat ≤ L.toNat - 1 - (B - off).toNat := by
    simp [evalHOLExact, evalListHOLExact, hul, hull, hn, wordOpHOL, wordOp, valueIsWord,
      valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hw
    subst hw0
    by_contra hc
    have : L - 1#64 - (B - off) < N := by rw [BitVec.lt_def, hsub]; omega
    simp [this] at hw
  simp [evalHOLExact, evalListHOLExact, hull, hn, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
  subst hv
  have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
  have hadd : (1#64 + (B - off)).toNat = 1 + (B - off).toNat := by
    rw [BitVec.toNat_add_of_lt (by rw [h1]; have := L.isLt; omega), h1]
  refine ⟨1#64 + (B - off), N, flag, rfl, ?_, ?_⟩
  · rw [hadd]; omega
  · rw [hadd]
    have : L.toNat ≠ 0 := fun h => hL (BitVec.eq_of_toNat_eq (by simpa using h))
    omega

private theorem hdr_post_dom_vvh {F : Type} (e : PanSemStateFiniteExact 64 F)
    (hcode : e.code = originalRuntimeCode) (hP : GuestInv e)
    (P L : BitVec 64)
    (hp : e.locals.lookup (ofString "p") = some (.val (.word P)))
    (hl : e.locals.lookup (ofString "len") = some (.val (.word L)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState e (sourceFnBody Guest.Software.guestFn_rlp_item_header)).1 =
      some (.returned v)) :
    HdrQ_vvh L v ∧ sourceBase ≤ P.toNat ∧ P.toNat < heapEnd := by
  revert v hret
  change RetOK_vvh (fun v => HdrQ_vvh L v ∧ sourceBase ≤ P.toNat ∧ P.toNat < heapEnd) e
    (sourceFnBody Guest.Software.guestFn_rlp_item_header)
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_item_header,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine R_guard_vvh hcode (fun w hw hw0 => ?_)
  have hL : L ≠ 0 := by
    intro h; subst h; simp [evalHOLExact, hl, Compiler.Encoders.Asm.wordCmpHOL] at hw; subst hw0
    simp at hw
  refine R_dec_vvh (fun v hv _ => ?_)
  obtain ⟨P', B, ha, hdom, rfl⟩ := loadByte_word_dom_vvh e _ v hv
  simp only [evalHOLExact, PanSemStateFiniteExact.toExact, hp, Option.some.injEq, ValueHOL.val.injEq,
    HolWordLab.word.injEq] at ha
  subst ha
  rw [hP.memaddrs, ordinaryDomain_iff] at hdom
  have hhe8 : heapEnd % 8 = 0 := by decide
  have hsb8 : sourceBase % 8 = 0 := by decide
  have hal := panByteAlign_toNat64 P
  have hp_in : sourceBase ≤ P.toNat ∧ P.toNat < heapEnd := ⟨by omega, by omega⟩
  have liftQ : ∀ {st : PanSemStateFiniteExact 64 F} {pr : ProgHOL 64},
      RetOK_vvh (HdrQ_vvh L) st pr →
      RetOK_vvh (fun v => HdrQ_vvh L v ∧ sourceBase ≤ P.toNat ∧ P.toNat < heapEnd) st pr :=
    fun h v hv => ⟨h v hv, hp_in⟩
  apply liftQ
  set e1 := setVarHOLFinite (ofString "b") (.val (.word B)) e with he1
  have hb1 : e1.locals.lookup (ofString "b") = some (.val (.word B)) := by
    simp [he1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hl1 : e1.locals.lookup (ofString "len") = some (.val (.word L)) := by
    simp [he1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "b" ≠ ofString "len" by decide, hl]
  have hc1 : e1.code = originalRuntimeCode := hcode
  refine R_branch_vvh (by rfl) (fun w _ _ => R_ret_vvh (fun v hv => ?_)) (fun w _ _ => ?_)
  · simp [evalHOLExact, evalListHOLExact] at hv
    subst hv
    refine ⟨0, 1, 0, rfl, by simp, ?_⟩
    have : L.toNat ≠ 0 := fun h => hL (BitVec.eq_of_toNat_eq (by simpa using h))
    simp; omega
  have hL1 := toNat_sub_one_vvh L hL
  refine R_branch_vvh (by rfl) (fun w _ _ => R_dec_vvh (fun v hv _ => ?_)) (fun w _ _ => ?_)
  · simp [evalHOLExact, evalListHOLExact, hb1, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
    subst hv
    set e2 := setVarHOLFinite (ofString "n") (.val (.word (B - 128#64))) e1 with he2
    have hc2 : e2.code = originalRuntimeCode := hcode
    refine R_guard_vvh hc2 (fun w hw hw0 => ?_)
    have hN : (B - 128#64).toNat ≤ L.toNat - 1 := by
      simp [evalHOLExact, evalListHOLExact, he2, lk_set_vvh, lk_set'_vvh,
        show ofString "n" ≠ ofString "len" by decide, hl1, wordOpHOL, wordOp, valueIsWord,
        valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hw
      subst hw0
      by_contra hc
      have : L - 1#64 < B - 128#64 := by rw [BitVec.lt_def, hL1]; omega
      simp [this] at hw
    refine R_check2_vvh hc2 (R_ret_vvh (fun v hv => ?_))
    simp [evalHOLExact, evalListHOLExact, he2, lk_set_vvh, lk_set'_vvh] at hv
    subst hv
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    refine ⟨1, B - 128#64, 0, rfl, by simp, ?_⟩
    rw [h1]
    have : L.toNat ≠ 0 := fun h => hL (BitVec.eq_of_toNat_eq (by simpa using h))
    omega
  refine R_branch_vvh (by rfl) (fun w _ _ => long_branch_vvh e1 hc1 L B 183#64 0#64 hL hl1 hb1) (fun w _ _ => ?_)
  refine R_branch_vvh (by rfl) (fun w _ _ => short_branch_vvh e1 hc1 L B 192#64 1#64 hL hl1 hb1) (fun w _ _ => ?_)
  exact long_branch_vvh e1 hc1 L B 247#64 1#64 hL hl1 hb1

private theorem call_flow_locals_vvh {F : Type} (s : PanSemStateFiniteExact 64 F) (f : MlS) (args : List (ExpHOL 64))
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

private theorem callee_p_len_vvh {fname : MlS} {body0 : ProgHOL 64} {rs0 : ShapeHOL}
    (hlook : originalRuntimeCode.lookup fname =
      some ([(ofString "p", .one), (ofString "len", .one)], body0, rs0))
    (v1 v2 : ValueHOL 64) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (rs : ShapeHOL)
    (hl : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup fname [v1, v2] =
      some (body, callee, rs)) :
    body = body0 ∧ callee.lookup (ofString "p") = some v1 ∧ callee.lookup (ofString "len") = some v2 := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
  split at hl
  · simp at hl
  · rename_i b cl r heq
    simp only [Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl, rfl⟩ := hl
    simp only [lookupCodeHOLExact, hlook] at heq
    split at heq
    · simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      refine ⟨rfl, ?_, by simp⟩
      simp [List.zip, List.foldl, show ofString "p" ≠ ofString "len" by decide]
    · simp at heq

private def TotQDom_vvh (P L : BitVec 64) (v : ValueHOL 64) : Prop :=
  ∃ t : BitVec 64, v = .val (.word t) ∧ 1 ≤ t.toNat ∧ t.toNat ≤ L.toNat ∧
    sourceBase ≤ P.toNat ∧ P.toNat < heapEnd

private theorem total_post_dom_vvh {F : Type} (e : PanSemStateFiniteExact 64 F)
    (hcode : e.code = originalRuntimeCode) (hP : GuestInv e)
    (P L : BitVec 64)
    (hp : e.locals.lookup (ofString "p") = some (.val (.word P)))
    (hl : e.locals.lookup (ofString "len") = some (.val (.word L))) :
    RetOK_vvh (TotQDom_vvh P L) e (sourceFnBody Guest.Software.guestFn_rlp_item_total) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_item_total,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine R_decCall'_vvh (fun values body callee rs v hargs hlk hret _ u _ _ hu => ?_)
  simp only [evalListHOLFinite_eq_toExact, evalListHOLExact, evalHOLExact, hp, hl, Option.some.injEq] at hargs
  subst hargs
  rw [hcode] at hlk
  obtain ⟨rfl, hcp, hcl⟩ := callee_p_len_vvh lookup_rlp_item_header_vvh _ _ body callee rs hlk
  obtain ⟨⟨a, b, c, rfl, h1, h2⟩, hp_lo, hp_hi⟩ :=
    hdr_post_dom_vvh (callEntryStateHOLFinite e callee) hcode (guestInv_callEntry e callee hP) P L hcp hcl v hret
  refine R_seq_vvh (R_ite_vvh (fun w _ => ⟨fun _ v hv => absurd hv (call_noret_vvh u _ _ v), fun _ => R_skip_vvh⟩))
    (fun mid hmid => ?_)
  have hmid_h : mid.locals.lookup (ofString "h") = some (hval_vvh a b c) := by
    rw [evaluateHOLFiniteState_ite] at hmid
    split at hmid
    · split at hmid
      · rw [evaluateHOLFiniteState_skip] at hmid
        simp only [Prod.mk.injEq] at hmid
        rw [← hmid.2]; exact hu
      · rw [(call_flow_locals_vvh u _ _ mid hmid).1]; exact hu
    · simp at hmid
  refine R_ret_vvh (fun v hv => ?_)
  simp [evalHOLExact, evalListHOLExact, hmid_h, hval_vvh, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
  subst hv
  refine ⟨a + b, rfl, ?_, ?_, hp_lo, hp_hi⟩
  · rw [BitVec.toNat_add_of_lt (by have := L.isLt; omega)]; omega
  · rw [BitVec.toNat_add_of_lt (by have := L.isLt; omega)]; omega

private theorem decCall_flow_vvh {F : Type} {s : PanSemStateFiniteExact 64 F} {n : MlS} {sh : ShapeHOL} {f : MlS}
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
          rw [resVarEq_lookup_local, if_neg hk]
      · simp
    | _ => simp

private def countCond_vvh : ExpHOL 64 :=
  .cmp .lower (.var .local (ofString "off")) (.var .local (ofString "len"))

private def countBody_vvh : ProgHOL 64 :=
  .decCall (ofString "total") .one (ofString "rlp_item_total")
    [.op .add [.var .local (ofString "p"), .var .local (ofString "off")],
      .op .sub [.var .local (ofString "len"), .var .local (ofString "off")]]
    (.seq (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "total")]))
      (.assign .local (ofString "count") (.op .add [.var .local (ofString "count"), .const 1])))

private theorem countBody_step_vvh {F : Type} (s : PanSemStateFiniteExact 64 F) (P y m c : BitVec 64)
    (hcode : s.code = originalRuntimeCode) (hP : GuestInv s)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word P)))
    (hy : s.locals.lookup (ofString "off") = some (.val (.word y)))
    (hm : s.locals.lookup (ofString "len") = some (.val (.word m)))
    (hc : s.locals.lookup (ofString "count") = some (.val (.word c)))
    (hlt : y.toNat < m.toNat)
    (hflow : (evaluateHOLFiniteState s countBody_vvh).1 = none) :
    ∃ T : BitVec 64,
      1 ≤ T.toNat ∧ y.toNat + T.toNat ≤ m.toNat ∧
      sourceBase ≤ (P + y).toNat ∧ (P + y).toNat < heapEnd ∧
      (evaluateHOLFiniteState s countBody_vvh).2.locals.lookup (ofString "off") = some (.val (.word (y + T))) ∧
      (evaluateHOLFiniteState s countBody_vvh).2.locals.lookup (ofString "count") = some (.val (.word (c + 1#64))) ∧
      (evaluateHOLFiniteState s countBody_vvh).2.locals.lookup (ofString "p") = some (.val (.word P)) ∧
      (evaluateHOLFiniteState s countBody_vvh).2.locals.lookup (ofString "len") = some (.val (.word m)) := by
  unfold countBody_vvh at hflow ⊢
  obtain ⟨values, body, callee, rs, v, hargs, hl, hret, u, hcu, hloc, hu, hcont, hfin⟩ := decCall_flow_vvh hflow
  simp only [evalListHOLFinite_eq_toExact, evalListHOLExact, evalHOLExact, hp, hy, hm,
    wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self,
    ↓reduceIte, List.foldr, add_zero, Option.some.injEq] at hargs
  subst hargs
  rw [hcode] at hl
  obtain ⟨rfl, hcp, hcl⟩ := callee_p_len_vvh lookup_rlp_item_total_vvh _ _ body callee rs hl
  have hsub : (m - y).toNat = m.toNat - y.toNat := by rw [BitVec.toNat_sub]; omega
  obtain ⟨T, rfl, hT1, hT2, hpy_lo, hpy_hi⟩ :=
    total_post_dom_vvh (callEntryStateHOLFinite s callee) hcode (guestInv_callEntry s callee hP)
      (P + y) (m - y) hcp hcl v hret
  rw [hsub] at hT2
  have huoff : u.locals.lookup (ofString "off") = some (.val (.word y)) := by
    rw [hloc _ (by decide)]; exact hy
  have hucnt : u.locals.lookup (ofString "count") = some (.val (.word c)) := by
    rw [hloc _ (by decide)]; exact hc
  have hup : u.locals.lookup (ofString "p") = some (.val (.word P)) := by
    rw [hloc _ (by decide)]; exact hp
  have hulen : u.locals.lookup (ofString "len") = some (.val (.word m)) := by
    rw [hloc _ (by decide)]; exact hm
  have hfirst : evaluateHOLFiniteState u
      (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "total")])) =
      (none, setKvarHOLFinite .local (ofString "off") (.val (.word (y + T))) u) := by
    rw [evaluateHOLFiniteState_assign]
    simp [evalHOLExact, evalListHOLExact, huoff, hu, wordOpHOL, wordOp, valueIsWord, valueWord,
      isValidValueHOLFinite, lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL]
  let u1 := setKvarHOLFinite .local (ofString "off") (.val (.word (y + T))) u
  have hu1_cnt : u1.locals.lookup (ofString "count") = some (.val (.word c)) := by
    simp [u1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hucnt,
      show ofString "off" ≠ ofString "count" by decide]
  have hsecond : evaluateHOLFiniteState u1
      (.assign .local (ofString "count") (.op .add [.var .local (ofString "count"), .const 1])) =
      (none, setKvarHOLFinite .local (ofString "count") (.val (.word (c + 1#64))) u1) := by
    rw [evaluateHOLFiniteState_assign]
    simp [evalHOLExact, evalListHOLExact, hu1_cnt, wordOpHOL, wordOp, valueIsWord, valueWord,
      isValidValueHOLFinite, lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL]
  refine ⟨T, hT1, by omega, hpy_lo, hpy_hi, ?_, ?_, ?_, ?_⟩
  · rw [hfin (ofString "off") (by decide), evaluateHOLFiniteState_seq_line780, hfirst]; dsimp only
    rw [hsecond]; dsimp only
    simp [u1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "count" ≠ ofString "off" by decide]
  · rw [hfin (ofString "count") (by decide), evaluateHOLFiniteState_seq_line780, hfirst]; dsimp only
    rw [hsecond]; dsimp only
    simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · rw [hfin (ofString "p") (by decide), evaluateHOLFiniteState_seq_line780, hfirst]; dsimp only
    rw [hsecond]; dsimp only
    simp [u1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hup,
      show ofString "count" ≠ ofString "p" by decide, show ofString "off" ≠ ofString "p" by decide]
  · rw [hfin (ofString "len") (by decide), evaluateHOLFiniteState_seq_line780, hfirst]; dsimp only
    rw [hsecond]; dsimp only
    simp [u1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hulen,
      show ofString "count" ≠ ofString "len" by decide, show ofString "off" ≠ ofString "len" by decide]

private def CountRetInv_vvh {F : Type} (P m : BitVec 64) (s : PanSemStateFiniteExact 64 F) : Prop :=
  s.code = originalRuntimeCode ∧ GuestInv s ∧
  ∃ (vis : Finset (Fin domainBytes)) (y c : BitVec 64),
    s.locals.lookup (ofString "p") = some (.val (.word P)) ∧
    s.locals.lookup (ofString "off") = some (.val (.word y)) ∧
    s.locals.lookup (ofString "len") = some (.val (.word m)) ∧
    s.locals.lookup (ofString "count") = some (.val (.word c)) ∧
    c.toNat = vis.card ∧
    c.toNat ≤ y.toNat ∧ y.toNat ≤ m.toNat ∧
    ∀ k ∈ vis, ∃ d : BitVec 64, d.toNat < y.toNat ∧
      sourceBase ≤ (P + d).toNat ∧ (P + d).toNat < heapEnd ∧
      k.val = (P + d).toNat - sourceBase

private theorem countBody_no_bc_vvh {F : Type} (t : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState t countBody_vvh).1 ≠ some .break ∧
    (evaluateHOLFiniteState t countBody_vvh).1 ≠ some .continue := by
  unfold countBody_vvh
  rw [evaluateHOLFiniteState_decCall_total]
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rename_i body callee _ _ _
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body with ⟨r, st⟩
        simp only [hrun]
        cases r with
        | none => simp
        | some r =>
          cases r with
          | returned w =>
            dsimp only
            split
            · dsimp only
              rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
              split
              · simp
              · split
                · dsimp only
                  rw [evaluateHOLFiniteState_assign]
                  split <;> [simp; (split <;> simp)]
                · simp
            · simp
          | _ => simp

private theorem while_countRetInv_vvh {F : Type} (P m : BitVec 64)
    (k : Nat) (s post : PanSemStateFiniteExact 64 F)
    (hclk : s.clock ≤ k) (hinv : CountRetInv_vvh P m s)
    (hrun : evaluateHOLFiniteState s (.while countCond_vvh countBody_vvh) = (none, post)) :
    CountRetInv_vvh P m post := by
  induction k generalizing s with
  | zero =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · split at hrun <;> [simp at hrun; omega]
      · rename_i hnotnz
        have hcw0 : cw = 0 := Classical.not_not.1 hnotnz
        subst hcw0; simp at hrun; subst hrun; exact hinv
    · simp at hrun
  | succ k ih =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · rename_i hnz
        split at hrun
        · simp at hrun
        · dsimp only at hrun
          rw [fixClockHOLFinite_evaluateState] at hrun
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) countBody_vvh
          have hbc := countBody_no_bc_vvh (decClockHOLFinite s)
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) countBody_vvh with ⟨r1, mid⟩
          rw [hbr] at hrun rem hbc
          cases r1 with
          | none =>
            obtain ⟨hc_s, hG_s, vis, y, c, hp, hy, hm, hc_cnt, hcard, hcy, hym, hvis⟩ := hinv
            have hlt : y.toNat < m.toNat := by
              simp [countCond_vvh, evalHOLExact, hy, hm, Compiler.Encoders.Asm.wordCmpHOL] at hcond
              by_contra hge
              have hge' : ¬ (y < m) := by rw [BitVec.lt_def]; omega
              simp [hge'] at hcond
              exact hnz hcond.symm
            let sd := decClockHOLFinite s
            have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG_s
            have hmeta := (evaluateHOLFiniteState_metadata sd countBody_vvh).1
            have hG_mid : GuestInv mid := by
              have hg := guestInv_evaluate sd countBody_vvh hGd
              rwa [hbr] at hg
            obtain ⟨T, hT1, hyT_le, hpy_lo, hpy_hi, hm_off, hm_cnt, hm_p, hm_len⟩ :=
              countBody_step_vvh sd P y m c hc_s hGd hp hy hm hc_cnt hlt (by rw [hbr])
            rw [hbr] at hm_off hm_cnt hm_p hm_len hmeta
            dsimp only at hm_off hm_cnt hm_p hm_len
            change mid.code = s.code at hmeta
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
            have hdb_lt : domainBytes < 2 ^ 64 := by decide
            have hc1_nat : (c + 1#64).toNat = c.toNat + 1 :=
              BitVec.toNat_add_of_lt (by change c.toNat + 1 < 2 ^ 64; omega)
            have hyT_nat : (y + T).toNat = y.toNat + T.toNat :=
              BitVec.toNat_add_of_lt (by have := m.isLt; omega)
            have hinv_mid : CountRetInv_vvh P m mid := by
              refine ⟨hmeta.trans hc_s, hG_mid, insert k_now vis, y + T, c + 1#64,
                hm_p, hm_off, hm_len, hm_cnt, by omega, by omega, by omega, ?_⟩
              intro k' hk'
              rcases Finset.mem_insert.mp hk' with rfl | hk'
              · exact ⟨y, by omega, hpy_lo, hpy_hi, rfl⟩
              · obtain ⟨d, hd, h1, h2, h3⟩ := hvis k' hk'
                exact ⟨d, by omega, h1, h2, h3⟩
            exact ih mid (by change mid.clock ≤ s.clock - 1 at rem; omega) hinv_mid hrun
          | some r1 =>
            cases r1 with
            | «continue» => exact absurd rfl hbc.2
            | «break» => exact absurd rfl hbc.1
            | _ => simp at hrun
      · rename_i hnotnz
        have hcw0 : cw = 0 := Classical.not_not.1 hnotnz
        subst hcw0; simp at hrun; subst hrun; exact hinv
    · simp at hrun

private theorem countBody_no_return_vvh {F : Type} (st : PanSemStateFiniteExact 64 F) (rv : ValueHOL 64) :
    (evaluateHOLFiniteState st countBody_vvh).1 ≠ some (.returned rv) := by
  unfold countBody_vvh
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  rcases hargs : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
      [.op .add [.var .local (ofString "p"), .var .local (ofString "off")],
       .op .sub [.var .local (ofString "len"), .var .local (ofString "off")]] with _ | vs
  · simp
  · simp only [hargs]
    rcases hlk : lookupCodeHOLFinite st.code.lookup (ofString "rlp_item_total") vs with _ | ⟨b', c', r'⟩
    · simp
    · simp only [hlk]
      by_cases hz : st.clock = 0
      · simp [hz]
      · simp only [hz, ↓reduceIte]
        rcases hcal : evaluateHOLFiniteState (callEntryStateHOLFinite st c') b' with ⟨rc, cst⟩
        simp only [hcal]
        rcases rc with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only <;> try simp
        split
        · dsimp only
          let u0 := setVarHOLFinite (ofString "total") w { cst with locals := st.locals }
          change (evaluateHOLFiniteState u0 _).1 ≠ some (.returned rv)
          rw [evaluateHOLFiniteState_seq_line780]
          have ha1 : ∀ x : Option (PanSemResultExact 64),
              (evaluateHOLFiniteState u0 (.assign .local (ofString "off")
                (.op .add [.var .local (ofString "off"), .var .local (ofString "total")]))).1 = x →
              x = none ∨ x = some .error := by
            intro x hx; rw [← hx, evaluateHOLFiniteState_assign]
            rcases @evalHOLExact 64 F _ u0.toExact (fun a => Classical.propDecidable (u0.memaddrs a))
                (.op .add [.var .local (ofString "off"), .var .local (ofString "total")]) with _ | v1
            · exact Or.inr rfl
            · dsimp only
              by_cases hv : isValidValueHOLFinite u0 .local (ofString "off") v1 = true
              · rw [if_pos hv]; exact Or.inl rfl
              · rw [if_neg hv]; exact Or.inr rfl
          rcases h1 : evaluateHOLFiniteState u0 (.assign .local (ofString "off")
              (.op .add [.var .local (ofString "off"), .var .local (ofString "total")])) with ⟨r1, u1⟩
          rcases ha1 r1 (by rw [h1]) with rfl | rfl
          · dsimp only
            rw [evaluateHOLFiniteState_assign]
            rcases @evalHOLExact 64 F _ u1.toExact (fun a => Classical.propDecidable (u1.memaddrs a))
                (.op .add [.var .local (ofString "count"), .const 1]) with _ | v2
            · simp
            · dsimp only
              by_cases hv2 : isValidValueHOLFinite u1 .local (ofString "count") v2 = true
              · rw [if_pos hv2]; simp
              · rw [if_neg hv2]; simp
          · simp
        · simp

private theorem while_count_no_return_vvh {F : Type} (rv : ValueHOL 64) :
    ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock ≤ k →
      (evaluateHOLFiniteState st (.while countCond_vvh countBody_vvh)).1 ≠ some (.returned rv) := by
  intro k
  induction k with
  | zero =>
    intro st hck; rw [evaluateHOLFiniteState_while_fixClockRewrite]
    rcases hc : @evalHOLFinite 64 F _ st (fun a => Classical.propDecidable (st.memaddrs a)) countCond_vvh with _ | cv
    · simp
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
      by_cases hw0 : cw = 0#64
      · subst hw0; simp
      · rw [if_neg hw0]
        have hk0 : st.clock = 0 := by omega
        rw [if_pos hk0]; simp
  | succ k ih =>
    intro st hck; rw [evaluateHOLFiniteState_while_fixClockRewrite]
    rcases hc : @evalHOLFinite 64 F _ st (fun a => Classical.propDecidable (st.memaddrs a)) countCond_vvh with _ | cv
    · simp
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
      by_cases hw0 : cw = 0#64
      · subst hw0; simp
      · rw [if_neg hw0]
        by_cases hk0 : st.clock = 0
        · rw [if_pos hk0]; simp
        · rw [if_neg hk0]
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) countBody_vvh
          have hb_nr := countBody_no_return_vvh (decClockHOLFinite st) rv
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite st) countBody_vvh with ⟨r1, m1⟩
          simp only [hbr] at rem hb_nr ⊢
          cases r1 with
          | none => exact ih m1 (by change m1.clock ≤ st.clock - 1 at rem; omega)
          | some r1 =>
            cases r1 with
            | «continue» => exact ih m1 (by change m1.clock ≤ st.clock - 1 at rem; omega)
            | «break» => simp
            | returned v' =>
              intro heq; injection heq with heq'; injection heq' with heq''; subst heq''
              exact hb_nr rfl
            | _ => simp

private theorem rlp_list_count_ret_le_len_vvh {F : Type}
    (s cpost : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64)) (rv : ValueHOL 64)
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_list_count") vals =
      some (sourceFnBody Guest.Software.guestFn_rlp_list_count, s.locals, .one))
    (hret : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_count) =
      (some (.returned rv), cpost)) :
    ∃ wcnt : BitVec 64, rv = .val (.word wcnt) ∧
      wcnt.toNat ≤ domainBytes ∧ wcnt.toNat ≤ locN s "len" := by
  obtain ⟨P, m, rfl, hp, hm⟩ := lookupCode_two_words_any_vvh (by decide) lookup_rlp_list_count_vvh hl
  have hloc_m : locN s "len" = m.toNat := by simp [locN, hm]
  have hbody : sourceFnBody Guest.Software.guestFn_rlp_list_count =
      .dec (ofString "count") .one (.const 0)
        (.dec (ofString "off") .one (.const 0)
          (.seq (.while countCond_vvh countBody_vvh)
            (.return (.var .local (ofString "count"))))) := rfl
  have hret1 : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_count)).1 =
      some (.returned rv) := by rw [hret]
  clear hret
  rw [hbody] at hret1
  revert rv hret1
  change RetOK_vvh (fun rv => ∃ wcnt : BitVec 64, rv = .val (.word wcnt) ∧
    wcnt.toNat ≤ domainBytes ∧ wcnt.toNat ≤ locN s "len") s _
  refine R_dec_vvh (fun vcnt hvcnt _ => ?_)
  have hvcnt_eq : vcnt = .val (.word 0) := by simp [evalHOLExact] at hvcnt; exact hvcnt.symm
  subst hvcnt_eq
  refine R_dec_vvh (fun voff hvoff _ => ?_)
  have hvoff_eq : voff = .val (.word 0) := by simp [evalHOLExact] at hvoff; exact hvoff.symm
  subst hvoff_eq
  let s2 := setVarHOLFinite (ofString "off") (.val (.word 0))
    (setVarHOLFinite (ofString "count") (.val (.word 0)) s)
  have hinv2 : CountRetInv_vvh P m s2 := by
    refine ⟨hc, guestInv_setVar _ _ _ (guestInv_setVar _ _ _ hG), ∅, 0, 0, ?_, ?_, ?_, ?_,
      by simp, by simp, by simp, by simp⟩
    · simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp,
        show ofString "off" ≠ ofString "p" by decide, show ofString "count" ≠ ofString "p" by decide]
    · simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm,
        show ofString "off" ≠ ofString "len" by decide, show ofString "count" ≠ ofString "len" by decide]
    · simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "off" ≠ ofString "count" by decide]
  refine R_seq_vvh ?_ (fun mid hmid => ?_)
  · intro rv hwhile_ret
    exact absurd hwhile_ret (while_count_no_return_vvh rv s2.clock s2 le_rfl)
  · obtain ⟨_, _, vis, _, c, _, _, _, hm_cnt, hcard, hcy, hym, _⟩ :=
      while_countRetInv_vvh P m s2.clock s2 mid le_rfl hinv2 hmid
    refine R_ret_vvh (fun v hv => ?_)
    simp [evalHOLExact, hm_cnt] at hv; subst hv
    have hle : vis.card ≤ domainBytes := by simpa using Finset.card_le_univ vis
    exact ⟨c, rfl, by omega, by omega⟩

private theorem rlp_list_count_ret_bound_vvh {F : Type}
    (s cpost : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64)) (rv : ValueHOL 64)
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_list_count") vals =
      some (sourceFnBody Guest.Software.guestFn_rlp_list_count, s.locals, .one))
    (hret : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_count) =
      (some (.returned rv), cpost)) :
    ∃ wcnt : BitVec 64, rv = .val (.word wcnt) ∧ wcnt.toNat ≤ domainBytes := by
  obtain ⟨wcnt, hrv, hdom, _⟩ := rlp_list_count_ret_le_len_vvh s cpost vals rv hc hG hl hret
  exact ⟨wcnt, hrv, hdom⟩

private def ltsLoopBody_vvh : ProgHOL 64 :=
  .decCall (ofString "total") .one (ofString "rlp_item_total_unchecked")
    [.op .add [.var .local (ofString "p"), .var .local (ofString "off")]]
    (.seq
      (.store (.op .add [.var .local (ofString "arr"),
          .panop .mul [.var .local (ofString "i"), .const 16]])
        (.op .add [.var .local (ofString "p"), .var .local (ofString "off")]))
      (.seq
        (.store (.op .add [.var .local (ofString "arr"),
            .panop .mul [.var .local (ofString "i"), .const 16], .const 8])
          (.var .local (ofString "total")))
        (.seq
          (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "total")]))
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))))

private def LtsInv_vvh {F : Type} (pw wcnt : BitVec 64) (t : PanSemStateFiniteExact 64 F) : Prop :=
  t.locals.lookup (ofString "arr") = some (.val (.word pw)) ∧
  t.locals.lookup (ofString "count") = some (.val (.word wcnt)) ∧
  WordLocals ["p", "off", "i"] t

private theorem lts_addr_in_heap_vvh {globN_hp : Nat} (pw wcnt wi : BitVec 64)
    (hcnt_dom : wcnt.toNat ≤ domainBytes)
    (hp_lo : globN_hp ≤ pw.toNat)
    (halloc_hi : pw.toNat + ((wcnt * 16#64).toNat + 7) / 8 * 8 ≤ heapLimit)
    (hlt : wi < wcnt) :
    globN_hp ≤ (pw + wi * 16#64).toNat ∧
    (pw + wi * 16#64).toNat + 8 ≤ heapLimit ∧
    globN_hp ≤ (pw + (wi * 16#64) + 8#64).toNat ∧
    (pw + (wi * 16#64) + 8#64).toNat + 8 ≤ heapLimit := by
  have hdb : domainBytes = 31104957928 := by decide
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hlt_nat : wi.toNat < wcnt.toNat := BitVec.lt_def.mp hlt
  have hcnt16 : (wcnt * 16#64).toNat = wcnt.toNat * 16 :=
    BitVec.toNat_mul_of_lt (by change wcnt.toNat * 16 < 2 ^ 64; omega)
  have hwi16 : (wi * 16#64).toNat = wi.toNat * 16 :=
    BitVec.toNat_mul_of_lt (by change wi.toNat * 16 < 2 ^ 64; omega)
  have halign : ((wcnt * 16#64).toNat + 7) / 8 * 8 = wcnt.toNat * 16 := by
    rw [hcnt16]; omega
  rw [halign] at halloc_hi
  have hp_wi16 : (pw + wi * 16#64).toNat = pw.toNat + wi.toNat * 16 := by
    rw [BitVec.toNat_add_of_lt (by rw [hwi16]; omega), hwi16]
  have hp_wi16_8 : (pw + (wi * 16#64) + 8#64).toNat = pw.toNat + wi.toNat * 16 + 8 := by
    rw [BitVec.toNat_add_of_lt (by rw [hp_wi16]; change pw.toNat + wi.toNat * 16 + 8 < 2 ^ 64; omega), hp_wi16]
    rfl
  exact ⟨by omega, by omega, by omega, by omega⟩

private theorem ltsLoopBody_keeps_local_vvh {F : Type}
    (t : PanSemStateFiniteExact 64 F) (key : MlS)
    (hk1 : key ≠ ofString "total") (hk2 : key ≠ ofString "off") (hk3 : key ≠ ofString "i")
    (hf : (evaluateHOLFiniteState t ltsLoopBody_vvh).1 = none ∨
      (evaluateHOLFiniteState t ltsLoopBody_vvh).1 = some .continue) :
    (evaluateHOLFiniteState t ltsLoopBody_vvh).2.locals.lookup key = t.locals.lookup key := by
  refine eval_decCall_flowing_keeps t _ _ _ _ _ key hk1
    (fun u0 => ?_) hf
  intro hf0
  obtain ⟨u1, _, hu1_loc, hf1, heq1⟩ := eval_store_flowing_inv_vvh u0 _ _ hf0
  rw [heq1]
  obtain ⟨u2, _, hu2_loc, hf2, heq2⟩ := eval_store_flowing_inv_vvh u1 _ _ hf1
  rw [heq2]
  rw [evaluateHOLFiniteState_seq_line780] at hf2 ⊢
  rcases ha1 : evaluateHOLFiniteState u2 (.assign .local (ofString "off")
      (.op .add [.var .local (ofString "off"), .var .local (ofString "total")])) with ⟨ra1, u3⟩
  rw [ha1] at hf2
  cases ra1 with
  | some _ =>
    exfalso
    have hbad : (evaluateHOLFiniteState u2 (.assign .local (ofString "off")
        (.op .add [.var .local (ofString "off"), .var .local (ofString "total")]))).1 ≠ some .continue := by
      rw [evaluateHOLFiniteState_assign]; split <;> [simp; (split <;> simp)]
    rw [ha1] at hbad
    rcases hf2 with hf2 | hf2 <;> [cases hf2; exact hbad hf2]
  | none =>
    have hu3_k : u3.locals.lookup key = u2.locals.lookup key := by
      have := eval_assign_flowing_keeps_vvh u2 (ofString "off")
        (.op .add [.var .local (ofString "off"), .var .local (ofString "total")]) key hk2
        (by rw [ha1]; exact Or.inl rfl)
      rwa [ha1] at this
    have hu4_k := eval_assign_flowing_keeps_vvh u3 (ofString "i")
      (.op .add [.var .local (ofString "i"), .const 1]) key hk3 hf2
    dsimp only
    rw [hu4_k, hu3_k, hu2_loc, hu1_loc]

private theorem ltsLoopBody_keeps_arr_count_vvh {F : Type}
    (t : PanSemStateFiniteExact 64 F) (pw wcnt : BitVec 64)
    (harr : t.locals.lookup (ofString "arr") = some (.val (.word pw)))
    (hcnt : t.locals.lookup (ofString "count") = some (.val (.word wcnt)))
    (hf : (evaluateHOLFiniteState t ltsLoopBody_vvh).1 = none ∨
      (evaluateHOLFiniteState t ltsLoopBody_vvh).1 = some .continue) :
    (evaluateHOLFiniteState t ltsLoopBody_vvh).2.locals.lookup (ofString "arr") = some (.val (.word pw)) ∧
    (evaluateHOLFiniteState t ltsLoopBody_vvh).2.locals.lookup (ofString "count") = some (.val (.word wcnt)) :=
  ⟨(ltsLoopBody_keeps_local_vvh t (ofString "arr") (by decide) (by decide) (by decide) hf).trans harr,
   (ltsLoopBody_keeps_local_vvh t (ofString "count") (by decide) (by decide) (by decide) hf).trans hcnt⟩

private theorem ltsLoopBody_no_bc_ret_vvh {F : Type} (t : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState t ltsLoopBody_vvh).1 ≠ some .break ∧
    (∀ rv, (evaluateHOLFiniteState t ltsLoopBody_vvh).1 ≠ some (.returned rv)) := by
  unfold ltsLoopBody_vvh
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
      [.op .add [.var .local (ofString "p"), .var .local (ofString "off")]] with _ | vs
  · simp
  · simp only [hargs]
    rcases hlk : lookupCodeHOLFinite t.code.lookup (ofString "rlp_item_total_unchecked") vs with _ | ⟨b', c', r'⟩
    · simp
    · simp only [hlk]
      by_cases hz : t.clock = 0
      · simp [hz]
      · simp only [hz, ↓reduceIte]
        rcases hcal : evaluateHOLFiniteState (callEntryStateHOLFinite t c') b' with ⟨rc, cst⟩
        simp only [hcal]
        rcases rc with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only <;> try simp
        split
        · dsimp only
          let u0 := setVarHOLFinite (ofString "total") w { cst with locals := t.locals }
          change (evaluateHOLFiniteState u0 _).1 ≠ some .break ∧
            ∀ rv, (evaluateHOLFiniteState u0 _).1 ≠ some (.returned rv)
          have hst : ∀ (st0 : PanSemStateFiniteExact 64 F) (d e : ExpHOL 64) {r0 u'},
              evaluateHOLFiniteState st0 (.store d e) = (r0, u') → r0 = none ∨ r0 = some .error := by
            intro st0 d e r0 u' hrun0
            rw [evaluateHOLFiniteState_store] at hrun0
            repeat' split at hrun0
            all_goals (injection hrun0 with hr0 _; subst hr0; simp)
          have has : ∀ (st0 : PanSemStateFiniteExact 64 F) (nm : MlS) (e : ExpHOL 64) {r0 u'},
              evaluateHOLFiniteState st0 (.assign .local nm e) = (r0, u') → r0 = none ∨ r0 = some .error := by
            intro st0 nm e r0 u' hrun0
            rw [evaluateHOLFiniteState_assign] at hrun0
            repeat' split at hrun0
            all_goals (injection hrun0 with hr0 _; subst hr0; simp)
          rw [evaluateHOLFiniteState_seq_line780]
          rcases h1 : evaluateHOLFiniteState u0 _ with ⟨r1, u1⟩
          rcases hst u0 _ _ h1 with rfl | rfl
          · dsimp only; rw [evaluateHOLFiniteState_seq_line780]
            rcases h2 : evaluateHOLFiniteState u1 _ with ⟨r2, u2⟩
            rcases hst u1 _ _ h2 with rfl | rfl
            · dsimp only; rw [evaluateHOLFiniteState_seq_line780]
              rcases h3 : evaluateHOLFiniteState u2 _ with ⟨r3, u3⟩
              rcases has u2 _ _ h3 with rfl | rfl
              · dsimp only
                rcases h4 : evaluateHOLFiniteState u3 _ with ⟨r4, u4⟩
                rcases has u3 _ _ h4 with rfl | rfl <;> simp
              · simp
            · simp
          · simp
        · simp

private theorem while_lts_no_return_vvh {F : Type} (cond : ExpHOL 64) (rv : ValueHOL 64) :
    ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock ≤ k →
      (evaluateHOLFiniteState st (.while cond ltsLoopBody_vvh)).1 ≠ some (.returned rv) := by
  intro k
  induction k with
  | zero =>
    intro st hck; rw [evaluateHOLFiniteState_while_fixClockRewrite]
    rcases hc : @evalHOLFinite 64 F _ st (fun a => Classical.propDecidable (st.memaddrs a)) cond with _ | cv
    · simp
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
      by_cases hw0 : cw = 0#64
      · subst hw0; simp
      · rw [if_neg hw0]
        have hk0 : st.clock = 0 := by omega
        rw [if_pos hk0]; simp
  | succ k ih =>
    intro st hck; rw [evaluateHOLFiniteState_while_fixClockRewrite]
    rcases hc : @evalHOLFinite 64 F _ st (fun a => Classical.propDecidable (st.memaddrs a)) cond with _ | cv
    · simp
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
      by_cases hw0 : cw = 0#64
      · subst hw0; simp
      · rw [if_neg hw0]
        by_cases hk0 : st.clock = 0
        · rw [if_pos hk0]; simp
        · rw [if_neg hk0]
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) ltsLoopBody_vvh
          have hb_nr := (ltsLoopBody_no_bc_ret_vvh (decClockHOLFinite st)).2 rv
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite st) ltsLoopBody_vvh with ⟨r1, m1⟩
          simp only [hbr] at rem hb_nr ⊢
          cases r1 with
          | none => exact ih m1 (by change m1.clock ≤ st.clock - 1 at rem; omega)
          | some r1 =>
            cases r1 with
            | «continue» => exact ih m1 (by change m1.clock ≤ st.clock - 1 at rem; omega)
            | «break» => simp
            | returned v' =>
              intro heq; injection heq with heq'; injection heq' with heq''; subst heq''
              exact hb_nr rfl
            | _ => simp

private theorem worldEff_rlp_list_to_slices_vvh {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_list_to_slices") vals =
      some (sourceFnBody Guest.Software.guestFn_rlp_list_to_slices, s.locals, .comb [.one, .one]))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_to_slices)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_to_slices)).1) :
    WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_to_slices)).2
      [] [] wsGw := by
  obtain ⟨wp, wlen, rfl, hp_lk, _⟩ := lookupCode_two_words_any_vvh (by decide) lookup_rlp_list_to_slices_vvh hl
  have heff0 : WorldEff s s [] [] wsGw := WorldEff.refl s [] [] wsGw hAR hc
  have hbody : sourceFnBody Guest.Software.guestFn_rlp_list_to_slices =
      .decCall (ofString "count") .one (ofString "rlp_list_count")
        [.var .local (ofString "p"), .var .local (ofString "len")]
        (.decCall (ofString "arr") .one (ofString "alloc")
          [.panop .mul [.var .local (ofString "count"), .const 16]]
          (.dec (ofString "i") .one (.const 0)
            (.dec (ofString "off") .one (.const 0)
              (.seq
                (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "count")))
                  ltsLoopBody_vvh)
                (.return (.rstruct [.var .local (ofString "arr"), .var .local (ofString "count")])))))) := rfl
  rw [hbody] at hnt hres ⊢
  refine worldEff_decCall_eff heff0 (ofString "count") .one (ofString "rlp_list_count") _ _ _ _ lookup_rlp_list_count_vvh
    (fun callee cvals _ hlc hnt_cb hres_cb =>
      heff0.trans_noBuf
        (WorldEff.from_locals_clock
          (worldEff_rlp_list_count_vvh (callEntryStateHOLFinite s callee) cvals
            heff0.code (localsFree_arenaReady s callee _ heff0.arena)
            (by simpa [heff0.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
        ws_nil_sub_vvh ws_no_gb_vvh)
    (fun callee cvals rv cpost _ hlc hrun_c _ heff_cp hnt_k1 hcr_k1 => ?_)
    hnt (Or.inr (Or.inr (Or.inr hres)))
  obtain ⟨wcnt, rfl, hcnt_dom⟩ :=
    rlp_list_count_ret_bound_vvh (callEntryStateHOLFinite s callee) cpost cvals rv
      heff0.code (guestInv_callEntry s callee heff0.arena.1)
      (by simpa [heff0.code, callEntryStateHOLFinite] using hlc) hrun_c
  let m1 := setVarHOLFinite (ofString "count") (.val (.word wcnt)) { cpost with locals := s.locals }
  have heff_m1 : WorldEff s m1 [] [] wsGw := heff_cp.locals_clock _ _
  have hm1_cnt : m1.locals.lookup (ofString "count") = some (.val (.word wcnt)) := by
    simp [m1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hm1_p : m1.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    simp [m1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_lk,
      show ofString "count" ≠ ofString "p" by decide]
  refine worldEff_decCall_alloc heff_m1 (by decide) (ofString "arr") _ hnt_k1 hcr_k1
    (fun pw nw m2 hsz_ev _ hm2_loc _ heff_m2 _ _ hpw_lo_s hpw_add hhp_m2_hi _ hnt_k2 hcr_k2 => ?_)
  have hnw_eq : nw = wcnt * 16#64 := by
    simp [evalHOLExact, evalListHOLExact, hm1_cnt, panOpHOL, valueIsWord, valueWord] at hsz_ev
    exact hsz_ev.symm
  subst hnw_eq
  have halloc_hi : pw.toNat + ((wcnt * 16#64).toNat + 7) / 8 * 8 ≤ heapLimit := by omega
  refine worldEff_dec heff_m2 _ _ _ hnt_k2 hcr_k2 (fun vi hvi _ hnt_k3 hcr_k3 => ?_)
  have hvi_eq : vi = .val (.word 0) := by simp [evalHOLExact] at hvi; exact hvi.symm
  subst hvi_eq
  let m3 := setVarHOLFinite (ofString "i") (.val (.word 0)) m2
  have heff_m3 : WorldEff s m3 [] [] wsGw := heff_m2.locals_clock _ _
  refine worldEff_dec heff_m3 _ _ _ hnt_k3 hcr_k3 (fun voff hvoff _ hnt_k4 hcr_k4 => ?_)
  have hvoff_eq : voff = .val (.word 0) := by simp [evalHOLExact] at hvoff; exact hvoff.symm
  subst hvoff_eq
  let m4 := setVarHOLFinite (ofString "off") (.val (.word 0)) m3
  have heff_m4 : WorldEff s m4 [] [] wsGw := heff_m3.locals_clock _ _
  have hinv_m4 : LtsInv_vvh pw wcnt m4 := by
    refine ⟨?_, ?_, ?_⟩
    · simp [m4, m3, setVarHOLFinite, hm2_loc, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "off" ≠ ofString "arr" by decide, show ofString "i" ≠ ofString "arr" by decide]
    · simp [m4, m3, setVarHOLFinite, hm2_loc, hm1_cnt, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "off" ≠ ofString "count" by decide, show ofString "i" ≠ ofString "count" by decide,
        show ofString "arr" ≠ ofString "count" by decide]
    · intro nm hnm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hnm
      rcases hnm with rfl | rfl | rfl
      · exact ⟨wp, by simp [m4, m3, setVarHOLFinite, hm2_loc, hm1_p, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "off" ≠ ofString "p" by decide, show ofString "i" ≠ ofString "p" by decide,
          show ofString "arr" ≠ ofString "p" by decide]⟩
      · exact ⟨0, by simp [m4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
      · exact ⟨0, by simp [m4, m3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "off" ≠ ofString "i" by decide]⟩
  have hws_lts : wsafe ltsLoopBody_vvh = true := by decide
  refine worldEff_seq hnt_k4 hcr_k4
    (fun hnt_w hcr_w =>
      worldEff_while_cond_vvh _ (LtsInv_vvh pw wcnt)
        (fun _ hinv => hinv)
        (fun t0 cw hcond hnz heff_t hinv_t hnt_b hcr_b => ?_)
        m4.clock m4 rfl heff_m4 hinv_m4 hnt_w hcr_w)
    (fun mid _ heff_mid _ _ => worldEff_return heff_mid _)
  set t := decClockHOLFinite t0
  obtain ⟨ht_arr, ht_cnt, ht_wloc⟩ := hinv_t
  obtain ⟨wp_t, htp⟩ := ht_wloc "p" (by simp)
  obtain ⟨woff_t, htoff⟩ := ht_wloc "off" (by simp)
  obtain ⟨wi_t, hti⟩ := ht_wloc "i" (by simp)
  have ht0_i : t0.locals.lookup (ofString "i") = some (.val (.word wi_t)) := hti
  have ht0_cnt : t0.locals.lookup (ofString "count") = some (.val (.word wcnt)) := ht_cnt
  have hlt_i : wi_t < wcnt := by
    rw [evalHOLFinite_eq_toExact] at hcond
    simp [evalHOLExact, ht0_i, ht0_cnt, Compiler.Encoders.Asm.wordCmpHOL] at hcond
    by_contra hge
    simp [hge] at hcond
    exact hnz hcond.symm
  obtain ⟨ha0_lo, ha0_hi, ha8_lo, ha8_hi⟩ :=
    lts_addr_in_heap_vvh pw wcnt wi_t hcnt_dom hpw_lo_s halloc_hi hlt_i
  refine ⟨?_, fun hf => ?_⟩
  · dsimp only [ltsLoopBody_vvh] at hnt_b hcr_b ⊢
    refine worldEff_decCall_ro heff_t InitECandidate.Solver.Wave8GuestInv.R13.ro_rlp_item_total_unchecked
      (ofString "total") .one _ hnt_b hcr_b (fun rvt cpost hsh_rvt hcpost hnt_s1 hcr_s1 => ?_)
    have hrvt_w : ∃ wt : BitVec 64, rvt = .val (.word wt) := by
      rcases rvt with ⟨⟨wt⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh_rvt
      exact ⟨wt, rfl⟩
    obtain ⟨wt, rfl⟩ := hrvt_w
    let u0 := setVarHOLFinite (ofString "total") (.val (.word wt)) { cpost with locals := t.locals }
    have heff_u0 : WorldEff s u0 [] [] wsGw := (heff_t.of_readOnly hcpost).locals_clock _ _
    have hu0_arr : u0.locals.lookup (ofString "arr") = some (.val (.word pw)) := by
      simp [u0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht_arr,
        show ofString "total" ≠ ofString "arr" by decide]
    have hu0_i : u0.locals.lookup (ofString "i") = some (.val (.word wi_t)) := by
      simp [u0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hti,
        show ofString "total" ≠ ofString "i" by decide]
    have hu0_p : u0.locals.lookup (ofString "p") = some (.val (.word wp_t)) := by
      simp [u0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, htp,
        show ofString "total" ≠ ofString "p" by decide]
    have hu0_off : u0.locals.lookup (ofString "off") = some (.val (.word woff_t)) := by
      simp [u0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, htoff,
        show ofString "total" ≠ ofString "off" by decide]
    have hu0_tot : u0.locals.lookup (ofString "total") = some (.val (.word wt)) := by
      simp [u0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    refine worldEff_seq hnt_s1 hcr_s1
      (fun _ _ => worldEff_store_word heff_u0 _ _
        (fun v hv => by
          simp [evalHOLExact, evalListHOLExact, hu0_p, hu0_off, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
          exact ⟨_, hv.symm⟩)
        (fun x hx _ => by
          simp [evalHOLExact, evalListHOLExact, hu0_arr, hu0_i, panOpHOL, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
          subst hx
          exact Or.inr (Or.inr (Or.inr ⟨ha0_lo, ha0_hi⟩))))
      (fun u1 hu1 heff_u1 hnt_s2 hcr_s2 => ?_)
    have hu1_loc : u1.locals = u0.locals := by
      have hcf := (evaluate_store_control_frame u0
        (.op .add [.var .local (ofString "arr"), .panop .mul [.var .local (ofString "i"), .const 16]])
        (.op .add [.var .local (ofString "p"), .var .local (ofString "off")])).2.1
      rwa [hu1] at hcf
    refine worldEff_seq hnt_s2 hcr_s2
      (fun _ _ => worldEff_store_word heff_u1 _ _
        (fun v hv => by
          simp [evalHOLExact, hu1_loc, hu0_tot] at hv
          exact ⟨_, hv.symm⟩)
        (fun x hx _ => by
          simp [evalHOLExact, evalListHOLExact, hu1_loc, hu0_arr, hu0_i, panOpHOL, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
          subst hx
          have hadd_assoc : pw + (wi_t * 16#64 + 8#64) = pw + wi_t * 16#64 + 8#64 :=
            (BitVec.add_assoc pw (wi_t * 16#64) 8#64).symm
          rw [hadd_assoc]
          exact Or.inr (Or.inr (Or.inr ⟨ha8_lo, ha8_hi⟩))))
      (fun u2 _ heff_u2 hnt_s3 hcr_s3 =>
        worldEff_seq hnt_s3 hcr_s3
          (fun _ _ => worldEff_assign_local heff_u2 _ _)
          (fun u3 _ heff_u3 _ _ => worldEff_assign_local heff_u3 _ _))
  · obtain ⟨hkeep_arr, hkeep_cnt⟩ := ltsLoopBody_keeps_arr_count_vvh t pw wcnt ht_arr ht_cnt hf
    exact ⟨hkeep_arr, hkeep_cnt,
      wordLocals_flowing hws_lts ht_wloc (by rcases hf with h | h; exact Or.inl h; exact Or.inr (Or.inr h))⟩

private theorem rlp_list_to_slices_ret_le_len_vvh {F : Type}
    (s cpost : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64)) (rv : ValueHOL 64)
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_list_to_slices") vals =
      some (sourceFnBody Guest.Software.guestFn_rlp_list_to_slices, s.locals, .comb [.one, .one]))
    (hret : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_to_slices) =
      (some (.returned rv), cpost)) :
    ∃ warr wcnt : BitVec 64,
      rv = .rStruct [.val (.word warr), .val (.word wcnt)] ∧
      wcnt.toNat ≤ domainBytes ∧ wcnt.toNat ≤ locN s "len" := by
  obtain ⟨wp, wlen, rfl, hp_lk, hlen_lk⟩ := lookupCode_two_words_any_vvh (by decide) lookup_rlp_list_to_slices_vvh hl
  have hloc_len : locN s "len" = wlen.toNat := by simp [locN, hlen_lk]
  have hbody : sourceFnBody Guest.Software.guestFn_rlp_list_to_slices =
      .decCall (ofString "count") .one (ofString "rlp_list_count")
        [.var .local (ofString "p"), .var .local (ofString "len")]
        (.decCall (ofString "arr") .one (ofString "alloc")
          [.panop .mul [.var .local (ofString "count"), .const 16]]
          (.dec (ofString "i") .one (.const 0)
            (.dec (ofString "off") .one (.const 0)
              (.seq
                (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "count")))
                  ltsLoopBody_vvh)
                (.return (.rstruct [.var .local (ofString "arr"), .var .local (ofString "count")])))))) := rfl
  have hret1 : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_to_slices)).1 =
      some (.returned rv) := by rw [hret]
  clear hret
  rw [hbody] at hret1
  revert rv hret1
  change RetOK_vvh (fun rv => ∃ warr wcnt : BitVec 64,
    rv = .rStruct [.val (.word warr), .val (.word wcnt)] ∧
    wcnt.toNat ≤ domainBytes ∧ wcnt.toNat ≤ locN s "len") s _
  intro rv hret1
  revert rv hret1
  refine R_decCall'_vvh (fun cvals cbody callee crs vcnt hargs hlk hrun_c1 _ u1 _ _ hu1_cnt => ?_)
  simp only [evalListHOLFinite_eq_toExact, evalListHOLExact, evalHOLExact, hp_lk, hlen_lk, Option.some.injEq] at hargs
  subst hargs
  have hsame := lookupCodeHOLFinite_installed_body s.code.lookup _ _ _ cbody _ crs [.val (.word wp), .val (.word wlen)] callee
    (by rw [hc]; exact lookup_rlp_list_count_vvh) hlk
  subst hsame
  have hret_eq := lookupCodeHOLFinite_installed_return s _ _ _ _ _ crs [.val (.word wp), .val (.word wlen)] callee
    (by rw [hc]; exact lookup_rlp_list_count_vvh) hlk
  subst hret_eq
  have hlk_c : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_list_count")
      [.val (.word wp), .val (.word wlen)] =
      some (sourceFnBody Guest.Software.guestFn_rlp_list_count, callee, .one) := by
    simpa [hc] using hlk
  obtain ⟨_, _, hcallee_len⟩ := callee_p_len_vvh lookup_rlp_list_count_vvh _ _ _ callee _ hlk_c
  have hloc_callee : locN (callEntryStateHOLFinite s callee) "len" = wlen.toNat := by
    simp [locN, callEntryStateHOLFinite, hcallee_len]
  rcases hrun_c : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (sourceFnBody Guest.Software.guestFn_rlp_list_count) with ⟨rc, st_c⟩
  rw [hrun_c] at hrun_c1
  dsimp only at hrun_c1
  subst hrun_c1
  obtain ⟨wcnt, rfl, hcnt_dom, hcnt_le⟩ :=
    rlp_list_count_ret_le_len_vvh (callEntryStateHOLFinite s callee) st_c [.val (.word wp), .val (.word wlen)] vcnt
      hc (guestInv_callEntry s callee hG)
      (by simpa [callEntryStateHOLFinite] using hlk_c) hrun_c
  rw [hloc_callee, ← hloc_len] at hcnt_le
  refine R_decCall_vvh (fun u2 varr hsh_arr _ hloc2 hu2_arr => ?_)
  rcases varr with ⟨⟨warr⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh_arr
  have hu2_cnt : u2.locals.lookup (ofString "count") = some (.val (.word wcnt)) := by
    rw [hloc2 _ (by decide)]; exact hu1_cnt
  refine R_dec_vvh (fun vi _ _ => R_dec_vvh (fun voff _ _ => ?_))
  let u4 := setVarHOLFinite (ofString "off") voff (setVarHOLFinite (ofString "i") vi u2)
  have hu4_arr : u4.locals.lookup (ofString "arr") = some (.val (.word warr)) := by
    simp [u4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu2_arr,
      show ofString "off" ≠ ofString "arr" by decide, show ofString "i" ≠ ofString "arr" by decide]
  have hu4_cnt : u4.locals.lookup (ofString "count") = some (.val (.word wcnt)) := by
    simp [u4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu2_cnt,
      show ofString "off" ≠ ofString "count" by decide, show ofString "i" ≠ ofString "count" by decide]
  refine R_seq_vvh (fun rv hw => absurd hw (while_lts_no_return_vvh _ rv u4.clock u4 le_rfl))
    (fun mid hmid => ?_)
  have hkeep_arr : mid.locals.lookup (ofString "arr") = some (.val (.word warr)) := by
    have hk := eval_while_flowing_keeps _ ltsLoopBody_vvh (ofString "arr")
      (fun t hf => ltsLoopBody_keeps_local_vvh t (ofString "arr") (by decide) (by decide) (by decide) hf)
      (fun t => (ltsLoopBody_no_bc_ret_vvh t).1)
      u4.clock u4 le_rfl (by rw [hmid]; exact Or.inl rfl)
    rw [hmid] at hk; exact hk.trans hu4_arr
  have hkeep_cnt : mid.locals.lookup (ofString "count") = some (.val (.word wcnt)) := by
    have hk := eval_while_flowing_keeps _ ltsLoopBody_vvh (ofString "count")
      (fun t hf => ltsLoopBody_keeps_local_vvh t (ofString "count") (by decide) (by decide) (by decide) hf)
      (fun t => (ltsLoopBody_no_bc_ret_vvh t).1)
      u4.clock u4 le_rfl (by rw [hmid]; exact Or.inl rfl)
    rw [hmid] at hk; exact hk.trans hu4_cnt
  refine R_ret_vvh (fun v hv => ?_)
  simp [evalHOLExact, evalListHOLExact, hkeep_arr, hkeep_cnt] at hv
  exact ⟨warr, wcnt, hv.symm, hcnt_dom, hcnt_le⟩

private theorem rlp_list_to_slices_ret_bound_vvh {F : Type}
    (s cpost : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64)) (rv : ValueHOL 64)
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_list_to_slices") vals =
      some (sourceFnBody Guest.Software.guestFn_rlp_list_to_slices, s.locals, .comb [.one, .one]))
    (hret : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_to_slices) =
      (some (.returned rv), cpost)) :
    ∃ warr wcnt : BitVec 64,
      rv = .rStruct [.val (.word warr), .val (.word wcnt)] ∧ wcnt.toNat ≤ domainBytes := by
  obtain ⟨warr, wcnt, hrv, hdom, _⟩ := rlp_list_to_slices_ret_le_len_vvh s cpost vals rv hc hG hl hret
  exact ⟨warr, wcnt, hrv, hdom⟩

/-! ## Section 4: Transaction Decoding Helpers (`tx_*`, `decode_*`) and `wk_is_valid_versioned_hashes` -/

private theorem lookup_tx_scalar_item_vvh :
    originalRuntimeCode.lookup (ofString "tx_scalar_item") =
      some ([(ofString "arr", .one), (ofString "i", .one), (ofString "maxb", .one)],
        sourceFnBody Guest.Software.guestFn_tx_scalar_item, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 296 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_tx_scalar_item) rfl

private theorem lookup_tx_scalar_u256_vvh :
    originalRuntimeCode.lookup (ofString "tx_scalar_u256") =
      some ([(ofString "arr", .one), (ofString "i", .one), (ofString "maxb", .one)],
        sourceFnBody Guest.Software.guestFn_tx_scalar_u256, .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 297 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_tx_scalar_u256) rfl

private theorem lookup_tx_scalar_word_vvh :
    originalRuntimeCode.lookup (ofString "tx_scalar_word") =
      some ([(ofString "arr", .one), (ofString "i", .one), (ofString "maxb", .one), (ofString "envcode", .one)],
        sourceFnBody Guest.Software.guestFn_tx_scalar_word, .one) :=
  lookup_of_guestAst_getElem 298 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_tx_scalar_word) rfl

private theorem lookup_tx_bytes_item_vvh :
    originalRuntimeCode.lookup (ofString "tx_bytes_item") =
      some ([(ofString "arr", .one), (ofString "i", .one)],
        sourceFnBody Guest.Software.guestFn_tx_bytes_item, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 299 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_tx_bytes_item) rfl

private theorem lookup_tx_fixed_bytes_vvh :
    originalRuntimeCode.lookup (ofString "tx_fixed_bytes") =
      some ([(ofString "arr", .one), (ofString "i", .one), (ofString "width", .one)],
        sourceFnBody Guest.Software.guestFn_tx_fixed_bytes, .one) :=
  lookup_of_guestAst_getElem 300 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_tx_fixed_bytes) rfl

private theorem lookup_tx_to_item_vvh :
    originalRuntimeCode.lookup (ofString "tx_to_item") =
      some ([(ofString "arr", .one), (ofString "i", .one)],
        sourceFnBody Guest.Software.guestFn_tx_to_item, .one) :=
  lookup_of_guestAst_getElem 301 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_tx_to_item) rfl

private theorem lookup_tx_list_item_vvh :
    originalRuntimeCode.lookup (ofString "tx_list_item") =
      some ([(ofString "arr", .one), (ofString "i", .one)],
        sourceFnBody Guest.Software.guestFn_tx_list_item, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 302 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_tx_list_item) rfl

private theorem lookup_decode_access_list_vvh :
    originalRuntimeCode.lookup (ofString "decode_access_list") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_decode_access_list, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 303 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_decode_access_list) rfl

private theorem lookup_decode_blob_hashes_vvh :
    originalRuntimeCode.lookup (ofString "decode_blob_hashes") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_decode_blob_hashes, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 304 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_decode_blob_hashes) rfl

private theorem lookup_decode_authorizations_vvh :
    originalRuntimeCode.lookup (ofString "decode_authorizations") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_decode_authorizations, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 305 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_decode_authorizations) rfl

private theorem lookup_decode_transaction_rlp_vvh :
    originalRuntimeCode.lookup (ofString "decode_transaction_rlp") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_decode_transaction_rlp, .one) :=
  lookup_of_guestAst_getElem 306 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_decode_transaction_rlp) rfl

private theorem lookup_decode_transaction_vvh :
    originalRuntimeCode.lookup (ofString "decode_transaction") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_decode_transaction, .one) :=
  lookup_of_guestAst_getElem 307 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_decode_transaction) rfl

private theorem lookup_is_valid_versioned_hashes_vvh :
    originalRuntimeCode.lookup (ofString "is_valid_versioned_hashes") =
      some ([(ofString "si", .one)],
        sourceFnBody Guest.Software.guestFn_is_valid_versioned_hashes, .one) :=
  lookup_of_guestAst_getElem 868 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_is_valid_versioned_hashes) rfl

private theorem worldEff_tailCall_ro_vvh {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    {fname : MlS} (hf : ReadOnlyFn fname) (args : List (ExpHOL 64))
    (hnt : (evaluateHOLFiniteState cur (.call none fname args)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call none fname args)).1) :
    WorldEff s (evaluateHOLFiniteState cur (.call none fname args)).2 Rl B gw := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  exact worldEff_tailCall_eff h fname args params body ret hlook
    (fun callee vals _ hl hnt_b hres_b => by
      have hentryEq : callEntryStateHOLFinite cur callee =
          { cur with locals := callee, clock := (callEntryStateHOLFinite cur callee).clock } := by
        cases cur; rfl
      have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup fname vs =
          some (body, (callEntryStateHOLFinite cur callee).locals, ret) :=
        ⟨vals, by simpa only [h.code, callEntryStateHOLFinite] using hl⟩
      have hro := hspec (callEntryStateHOLFinite cur callee) h.code
        (guestInv_callEntry cur callee h.arena.1) hex hnt_b hres_b
      exact h.of_readOnly (InitECandidate.Solver.Wave8GuestInv.R13.state_trans_locals_clock hentryEq hro))
    hnt hcr

private theorem worldEff_tx_scalar_item_vvh {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "tx_scalar_item") vals =
      some (sourceFnBody Guest.Software.guestFn_tx_scalar_item, s.locals, .comb [.one, .one]))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_tx_scalar_item)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_tx_scalar_item)).1) :
    WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_tx_scalar_item)).2
      [] [] wsGw := by
  have _ := hl
  have heff0 : WorldEff s s [] [] wsGw := WorldEff.refl s [] [] wsGw hAR hc
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_tx_scalar_item,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_decCall_eff heff0 (ofString "it") (.comb [.one, .one, .one, .one])
    (ofString "rlp_item") _ _ _ _ lookup_rlp_item_vvh
    (fun callee cvals _ hlc hnt_cb hres_cb =>
      heff0.trans_noBuf
        (WorldEff.from_locals_clock
          (worldEff_rlp_item_vvh (callEntryStateHOLFinite s callee) cvals
            heff0.code (localsFree_arenaReady s callee _ heff0.arena)
            (by simpa [heff0.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
        ws_nil_sub_vvh ws_no_gb_vvh)
    (fun _ _ rv cpost _ _ _ _ heff_cp hnt_k hcr_k =>
      let m1 := setVarHOLFinite (ofString "it") rv { cpost with locals := s.locals }
      have heff_m1 : WorldEff s m1 [] [] wsGw := heff_cp.locals_clock _ _
      worldEff_seq hnt_k hcr_k
        (fun hnt_1 hcr_1 =>
          worldEff_ite heff_m1 _ hnt_1 hcr_1
            (fun _ _ _ _ _ => worldEff_raise heff_m1 _ _)
            (fun _ _ _ => worldEff_skip heff_m1))
        (fun m2 _ heff_m2 hnt_2 hcr_2 =>
          worldEff_seq hnt_2 hcr_2
            (fun hnt_3 hcr_3 =>
              worldEff_ite heff_m2 _ hnt_3 hcr_3
                (fun _ _ _ hnt_4 hcr_4 =>
                  worldEff_ite heff_m2 _ hnt_4 hcr_4
                    (fun _ _ _ _ _ => worldEff_raise heff_m2 _ _)
                    (fun _ _ _ => worldEff_skip heff_m2))
                (fun _ _ _ => worldEff_skip heff_m2))
            (fun m3 _ heff_m3 hnt_5 hcr_5 =>
              worldEff_seq hnt_5 hcr_5
                (fun hnt_6 hcr_6 =>
                  worldEff_ite heff_m3 _ hnt_6 hcr_6
                    (fun _ _ _ hnt_7 hcr_7 =>
                      worldEff_ite heff_m3 _ hnt_7 hcr_7
                        (fun _ _ _ _ _ => worldEff_raise heff_m3 _ _)
                        (fun _ _ _ => worldEff_skip heff_m3))
                    (fun _ _ _ => worldEff_skip heff_m3))
                (fun m4 _ heff_m4 _ _ => worldEff_return heff_m4 _))))
    hnt (Or.inr (Or.inr (Or.inr hres)))

private theorem worldEff_tx_scalar_u256_vvh {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "tx_scalar_u256") vals =
      some (sourceFnBody Guest.Software.guestFn_tx_scalar_u256, s.locals, .comb [.one, .one, .one, .one]))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_tx_scalar_u256)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_tx_scalar_u256)).1) :
    WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_tx_scalar_u256)).2
      [] [] wsGw := by
  have _ := hl
  have heff0 : WorldEff s s [] [] wsGw := WorldEff.refl s [] [] wsGw hAR hc
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_tx_scalar_u256,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_decCall_eff heff0 (ofString "f") (.comb [.one, .one])
    (ofString "tx_scalar_item") _ _ _ _ lookup_tx_scalar_item_vvh
    (fun callee cvals _ hlc hnt_cb hres_cb =>
      heff0.trans_noBuf
        (WorldEff.from_locals_clock
          (worldEff_tx_scalar_item_vvh (callEntryStateHOLFinite s callee) cvals
            heff0.code (localsFree_arenaReady s callee _ heff0.arena)
            (by simpa [heff0.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
        ws_nil_sub_vvh ws_no_gb_vvh)
    (fun _ _ rv cpost _ _ _ _ heff_cp hnt_k hcr_k =>
      let m1 := setVarHOLFinite (ofString "f") rv { cpost with locals := s.locals }
      have heff_m1 : WorldEff s m1 [] [] wsGw := heff_cp.locals_clock _ _
      worldEff_seq hnt_k hcr_k
        (fun hnt_1 hcr_1 =>
          worldEff_ite heff_m1 _ hnt_1 hcr_1
            (fun _ _ _ _ _ => worldEff_raise heff_m1 _ _)
            (fun _ _ _ => worldEff_skip heff_m1))
        (fun m2 _ heff_m2 hnt_2 hcr_2 =>
          worldEff_tailCall_ro_vvh heff_m2 ro_u256_from_be _ hnt_2 hcr_2))
    hnt (Or.inr (Or.inr (Or.inr hres)))

private theorem worldEff_tx_scalar_word_vvh {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "tx_scalar_word") vals =
      some (sourceFnBody Guest.Software.guestFn_tx_scalar_word, s.locals, .one))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_tx_scalar_word)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_tx_scalar_word)).1) :
    WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_tx_scalar_word)).2
      [] [] wsGw := by
  have _ := hl
  have heff0 : WorldEff s s [] [] wsGw := WorldEff.refl s [] [] wsGw hAR hc
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_tx_scalar_word,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_decCall_eff heff0 (ofString "f") (.comb [.one, .one])
    (ofString "tx_scalar_item") _ _ _ _ lookup_tx_scalar_item_vvh
    (fun callee cvals _ hlc hnt_cb hres_cb =>
      heff0.trans_noBuf
        (WorldEff.from_locals_clock
          (worldEff_tx_scalar_item_vvh (callEntryStateHOLFinite s callee) cvals
            heff0.code (localsFree_arenaReady s callee _ heff0.arena)
            (by simpa [heff0.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
        ws_nil_sub_vvh ws_no_gb_vvh)
    (fun _ _ rv cpost _ _ _ _ heff_cp hnt_k hcr_k =>
      let m1 := setVarHOLFinite (ofString "f") rv { cpost with locals := s.locals }
      have heff_m1 : WorldEff s m1 [] [] wsGw := heff_cp.locals_clock _ _
      worldEff_seq hnt_k hcr_k
        (fun hnt_1 hcr_1 =>
          worldEff_ite heff_m1 _ hnt_1 hcr_1
            (fun _ _ _ _ _ => worldEff_raise heff_m1 _ _)
            (fun _ _ _ => worldEff_skip heff_m1))
        (fun m2 _ heff_m2 hnt_2 hcr_2 =>
          worldEff_dec heff_m2 _ _ _ hnt_2 hcr_2 (fun vv _ _ hnt_3 hcr_3 =>
            let m3 := setVarHOLFinite (ofString "v") vv m2
            have heff_m3 : WorldEff s m3 [] [] wsGw := heff_m2.locals_clock _ _
            worldEff_dec heff_m3 _ _ _ hnt_3 hcr_3 (fun vj _ _ hnt_4 hcr_4 =>
              let m4 := setVarHOLFinite (ofString "j") vj m3
              have heff_m4 : WorldEff s m4 [] [] wsGw := heff_m3.locals_clock _ _
              worldEff_seq hnt_4 hcr_4
                (fun hnt_w hcr_w =>
                  worldEff_while _ (fun _ => True) (fun _ h => h)
                    (fun t heff_t _ hnt_b hcr_b =>
                      ⟨worldEff_seq hnt_b hcr_b
                        (fun _ _ => worldEff_assign_local heff_t _ _)
                        (fun u1 _ heff_u1 _ _ => worldEff_assign_local heff_u1 _ _),
                       fun _ => trivial⟩)
                    m4.clock m4 rfl heff_m4 trivial hnt_w hcr_w)
                (fun m5 _ heff_m5 _ _ => worldEff_return heff_m5 _)))))
    hnt (Or.inr (Or.inr (Or.inr hres)))

private theorem worldEff_tx_bytes_item_vvh {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "tx_bytes_item") vals =
      some (sourceFnBody Guest.Software.guestFn_tx_bytes_item, s.locals, .comb [.one, .one]))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_tx_bytes_item)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_tx_bytes_item)).1) :
    WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_tx_bytes_item)).2
      [] [] wsGw := by
  have _ := hl
  have heff0 : WorldEff s s [] [] wsGw := WorldEff.refl s [] [] wsGw hAR hc
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_tx_bytes_item,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_decCall_eff heff0 (ofString "it") (.comb [.one, .one, .one, .one])
    (ofString "rlp_item") _ _ _ _ lookup_rlp_item_vvh
    (fun callee cvals _ hlc hnt_cb hres_cb =>
      heff0.trans_noBuf
        (WorldEff.from_locals_clock
          (worldEff_rlp_item_vvh (callEntryStateHOLFinite s callee) cvals
            heff0.code (localsFree_arenaReady s callee _ heff0.arena)
            (by simpa [heff0.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
        ws_nil_sub_vvh ws_no_gb_vvh)
    (fun _ _ rv cpost _ _ _ _ heff_cp hnt_k hcr_k =>
      let m1 := setVarHOLFinite (ofString "it") rv { cpost with locals := s.locals }
      have heff_m1 : WorldEff s m1 [] [] wsGw := heff_cp.locals_clock _ _
      worldEff_seq hnt_k hcr_k
        (fun hnt_1 hcr_1 =>
          worldEff_ite heff_m1 _ hnt_1 hcr_1
            (fun _ _ _ _ _ => worldEff_raise heff_m1 _ _)
            (fun _ _ _ => worldEff_skip heff_m1))
        (fun m2 _ heff_m2 _ _ => worldEff_return heff_m2 _))
    hnt (Or.inr (Or.inr (Or.inr hres)))

private theorem worldEff_tx_fixed_bytes_vvh {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "tx_fixed_bytes") vals =
      some (sourceFnBody Guest.Software.guestFn_tx_fixed_bytes, s.locals, .one))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_tx_fixed_bytes)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_tx_fixed_bytes)).1) :
    WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_tx_fixed_bytes)).2
      [] [] wsGw := by
  have _ := hl
  have heff0 : WorldEff s s [] [] wsGw := WorldEff.refl s [] [] wsGw hAR hc
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_tx_fixed_bytes,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_decCall_eff heff0 (ofString "it") (.comb [.one, .one, .one, .one])
    (ofString "rlp_item") _ _ _ _ lookup_rlp_item_vvh
    (fun callee cvals _ hlc hnt_cb hres_cb =>
      heff0.trans_noBuf
        (WorldEff.from_locals_clock
          (worldEff_rlp_item_vvh (callEntryStateHOLFinite s callee) cvals
            heff0.code (localsFree_arenaReady s callee _ heff0.arena)
            (by simpa [heff0.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
        ws_nil_sub_vvh ws_no_gb_vvh)
    (fun _ _ rv cpost _ _ _ _ heff_cp hnt_k hcr_k =>
      let m1 := setVarHOLFinite (ofString "it") rv { cpost with locals := s.locals }
      have heff_m1 : WorldEff s m1 [] [] wsGw := heff_cp.locals_clock _ _
      worldEff_seq hnt_k hcr_k
        (fun hnt_1 hcr_1 =>
          worldEff_ite heff_m1 _ hnt_1 hcr_1
            (fun _ _ _ _ _ => worldEff_raise heff_m1 _ _)
            (fun _ _ _ => worldEff_skip heff_m1))
        (fun m2 _ heff_m2 hnt_2 hcr_2 =>
          worldEff_seq hnt_2 hcr_2
            (fun hnt_3 hcr_3 =>
              worldEff_ite heff_m2 _ hnt_3 hcr_3
                (fun _ _ _ _ _ => worldEff_raise heff_m2 _ _)
                (fun _ _ _ => worldEff_skip heff_m2))
            (fun m3 _ heff_m3 _ _ => worldEff_return heff_m3 _)))
    hnt (Or.inr (Or.inr (Or.inr hres)))

private theorem worldEff_tx_to_item_vvh {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "tx_to_item") vals =
      some (sourceFnBody Guest.Software.guestFn_tx_to_item, s.locals, .one))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_tx_to_item)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_tx_to_item)).1) :
    WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_tx_to_item)).2
      [] [] wsGw := by
  have _ := hl
  have heff0 : WorldEff s s [] [] wsGw := WorldEff.refl s [] [] wsGw hAR hc
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_tx_to_item,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_decCall_eff heff0 (ofString "it") (.comb [.one, .one, .one, .one])
    (ofString "rlp_item") _ _ _ _ lookup_rlp_item_vvh
    (fun callee cvals _ hlc hnt_cb hres_cb =>
      heff0.trans_noBuf
        (WorldEff.from_locals_clock
          (worldEff_rlp_item_vvh (callEntryStateHOLFinite s callee) cvals
            heff0.code (localsFree_arenaReady s callee _ heff0.arena)
            (by simpa [heff0.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
        ws_nil_sub_vvh ws_no_gb_vvh)
    (fun _ _ rv cpost _ _ _ _ heff_cp hnt_k hcr_k =>
      let m1 := setVarHOLFinite (ofString "it") rv { cpost with locals := s.locals }
      have heff_m1 : WorldEff s m1 [] [] wsGw := heff_cp.locals_clock _ _
      worldEff_seq hnt_k hcr_k
        (fun hnt_1 hcr_1 =>
          worldEff_ite heff_m1 _ hnt_1 hcr_1
            (fun _ _ _ _ _ => worldEff_raise heff_m1 _ _)
            (fun _ _ _ => worldEff_skip heff_m1))
        (fun m2 _ heff_m2 hnt_2 hcr_2 =>
          worldEff_seq hnt_2 hcr_2
            (fun hnt_3 hcr_3 =>
              worldEff_ite heff_m2 _ hnt_3 hcr_3
                (fun _ _ _ _ _ => worldEff_return heff_m2 _)
                (fun _ _ _ => worldEff_skip heff_m2))
            (fun m3 _ heff_m3 hnt_4 hcr_4 =>
              worldEff_seq hnt_4 hcr_4
                (fun hnt_5 hcr_5 =>
                  worldEff_ite heff_m3 _ hnt_5 hcr_5
                    (fun _ _ _ _ _ => worldEff_raise heff_m3 _ _)
                    (fun _ _ _ => worldEff_skip heff_m3))
                (fun m4 _ heff_m4 _ _ => worldEff_return heff_m4 _))))
    hnt (Or.inr (Or.inr (Or.inr hres)))

private theorem worldEff_tx_list_item_vvh {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "tx_list_item") vals =
      some (sourceFnBody Guest.Software.guestFn_tx_list_item, s.locals, .comb [.one, .one]))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_tx_list_item)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_tx_list_item)).1) :
    WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_tx_list_item)).2
      [] [] wsGw := by
  have _ := hl
  have heff0 : WorldEff s s [] [] wsGw := WorldEff.refl s [] [] wsGw hAR hc
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_tx_list_item,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_decCall_eff heff0 (ofString "it") (.comb [.one, .one, .one, .one])
    (ofString "rlp_item") _ _ _ _ lookup_rlp_item_vvh
    (fun callee cvals _ hlc hnt_cb hres_cb =>
      heff0.trans_noBuf
        (WorldEff.from_locals_clock
          (worldEff_rlp_item_vvh (callEntryStateHOLFinite s callee) cvals
            heff0.code (localsFree_arenaReady s callee _ heff0.arena)
            (by simpa [heff0.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
        ws_nil_sub_vvh ws_no_gb_vvh)
    (fun _ _ rv cpost _ _ _ _ heff_cp hnt_k hcr_k =>
      let m1 := setVarHOLFinite (ofString "it") rv { cpost with locals := s.locals }
      have heff_m1 : WorldEff s m1 [] [] wsGw := heff_cp.locals_clock _ _
      worldEff_seq hnt_k hcr_k
        (fun hnt_1 hcr_1 =>
          worldEff_ite heff_m1 _ hnt_1 hcr_1
            (fun _ _ _ _ _ => worldEff_raise heff_m1 _ _)
            (fun _ _ _ => worldEff_skip heff_m1))
        (fun m2 _ heff_m2 _ _ => worldEff_return heff_m2 _))
    hnt (Or.inr (Or.inr (Or.inr hres)))

private theorem heap_slice_stride_in_heap_vvh {globN_hp : Nat} (pw wcnt wi : BitVec 64)
    (stride off sz : Nat)
    (hcnt_dom : wcnt.toNat ≤ domainBytes)
    (hstride8 : stride % 8 = 0)
    (hstride_hi : stride ≤ 120)
    (hoff_sz : off + sz ≤ stride)
    (hp_lo : globN_hp ≤ pw.toNat)
    (halloc_hi : pw.toNat + ((wcnt * BitVec.ofNat 64 stride).toNat + 7) / 8 * 8 ≤ heapLimit)
    (hlt : wi < wcnt) :
    globN_hp ≤ (pw + wi * BitVec.ofNat 64 stride + BitVec.ofNat 64 off).toNat ∧
    (pw + wi * BitVec.ofNat 64 stride + BitVec.ofNat 64 off).toNat + sz ≤ heapLimit := by
  have hdb : domainBytes = 31104957928 := by decide
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hlt_nat : wi.toNat < wcnt.toNat := BitVec.lt_def.mp hlt
  have hstride_bv : (BitVec.ofNat 64 stride).toNat = stride :=
    Nat.mod_eq_of_lt (by omega)
  have hoff_bv : (BitVec.ofNat 64 off).toNat = off :=
    Nat.mod_eq_of_lt (by omega)
  have hcnt_mul_lt : wcnt.toNat * stride < 2 ^ 64 :=
    calc wcnt.toNat * stride ≤ 31104957928 * 120 := Nat.mul_le_mul (by omega) hstride_hi
      _ < 2 ^ 64 := by decide
  have hwi_mul_le : wi.toNat * stride + stride ≤ wcnt.toNat * stride := by
    calc wi.toNat * stride + stride = (wi.toNat + 1) * stride := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ wcnt.toNat * stride := Nat.mul_le_mul_right stride hlt_nat
  have hwi_mul_lt : wi.toNat * stride < 2 ^ 64 := by omega
  have hcnt_s : (wcnt * BitVec.ofNat 64 stride).toNat = wcnt.toNat * stride := by
    rw [BitVec.toNat_mul_of_lt (by rw [hstride_bv]; exact hcnt_mul_lt), hstride_bv]
  have hwi_s : (wi * BitVec.ofNat 64 stride).toNat = wi.toNat * stride := by
    rw [BitVec.toNat_mul_of_lt (by rw [hstride_bv]; exact hwi_mul_lt), hstride_bv]
  have halign : ((wcnt * BitVec.ofNat 64 stride).toNat + 7) / 8 * 8 = wcnt.toNat * stride := by
    rw [hcnt_s]
    obtain ⟨q, rfl⟩ : ∃ q, stride = 8 * q := ⟨stride / 8, by omega⟩
    have hmul8 : wcnt.toNat * (8 * q) = 8 * (wcnt.toNat * q) := by
      rw [← Nat.mul_assoc, Nat.mul_comm wcnt.toNat 8, Nat.mul_assoc]
    rw [hmul8]; omega
  rw [halign] at halloc_hi
  have hp_wi : (pw + wi * BitVec.ofNat 64 stride).toNat = pw.toNat + wi.toNat * stride := by
    rw [BitVec.toNat_add_of_lt (by rw [hwi_s]; omega), hwi_s]
  have hp_wi_off : (pw + wi * BitVec.ofNat 64 stride + BitVec.ofNat 64 off).toNat =
      pw.toNat + wi.toNat * stride + off := by
    rw [BitVec.toNat_add_of_lt (by rw [hp_wi, hoff_bv]; omega), hp_wi, hoff_bv]
  exact ⟨by omega, by omega⟩

private def bhLoopBody_vvh : ProgHOL 64 :=
  .decCall (ofString "h") .one (ofString "tx_fixed_bytes")
    [.rfield 0 (.var .local (ofString "lst")), .var .local (ofString "i"), .const 32]
    (.seq
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "i"), .const 32]],
         .var .local (ofString "h"), .const 32])
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))

private theorem bhLoopBody_keeps_local_vvh {F : Type}
    (t : PanSemStateFiniteExact 64 F) (key : MlS)
    (hk1 : key ≠ ofString "h") (hk2 : key ≠ ofString "i")
    (hf : (evaluateHOLFiniteState t bhLoopBody_vvh).1 = none ∨
      (evaluateHOLFiniteState t bhLoopBody_vvh).1 = some .continue) :
    (evaluateHOLFiniteState t bhLoopBody_vvh).2.locals.lookup key = t.locals.lookup key := by
  refine eval_decCall_flowing_keeps t _ _ _ _ _ key hk1 (fun u0 hf0 => ?_) hf
  obtain ⟨u1, _, hu1_loc, hf1, heq1⟩ := eval_call0_flowing_inv u0 _ _ hf0
  rw [heq1]
  exact (eval_assign_flowing_keeps_vvh u1 _ _ key hk2 hf1).trans (by rw [hu1_loc])

private theorem worldEff_decode_blob_hashes_vvh {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "decode_blob_hashes") vals =
      some (sourceFnBody Guest.Software.guestFn_decode_blob_hashes, s.locals, .comb [.one, .one]))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_blob_hashes)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_blob_hashes)).1) :
    WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_blob_hashes)).2
      [] [] wsGw := by
  have _ := hl
  have heff0 : WorldEff s s [] [] wsGw := WorldEff.refl s [] [] wsGw hAR hc
  have hbody : sourceFnBody Guest.Software.guestFn_decode_blob_hashes =
      .decCall (ofString "lst") (.comb [.one, .one]) (ofString "rlp_list_to_slices")
        [.var .local (ofString "p"), .var .local (ofString "len")]
        (.decCall (ofString "buf") .one (ofString "alloc")
          [.panop .mul [.rfield 1 (.var .local (ofString "lst")), .const 32]]
          (.dec (ofString "i") .one (.const 0)
            (.seq
              (.while (.cmp .lower (.var .local (ofString "i")) (.rfield 1 (.var .local (ofString "lst"))))
                bhLoopBody_vvh)
              (.return (.rstruct [.var .local (ofString "buf"), .rfield 1 (.var .local (ofString "lst"))]))))) := rfl
  rw [hbody] at hnt hres ⊢
  refine worldEff_decCall_eff heff0 (ofString "lst") (.comb [.one, .one]) (ofString "rlp_list_to_slices")
    _ _ _ _ lookup_rlp_list_to_slices_vvh
    (fun callee cvals _ hlc hnt_cb hres_cb =>
      heff0.trans_noBuf
        (WorldEff.from_locals_clock
          (worldEff_rlp_list_to_slices_vvh (callEntryStateHOLFinite s callee) cvals
            heff0.code (localsFree_arenaReady s callee _ heff0.arena)
            (by simpa [heff0.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
        ws_nil_sub_vvh ws_no_gb_vvh)
    (fun callee cvals rv cpost _ hlc hrun_c _ heff_cp hnt_k1 hcr_k1 => ?_)
    hnt (Or.inr (Or.inr (Or.inr hres)))
  obtain ⟨warr, wcnt, rfl, hcnt_dom⟩ :=
    rlp_list_to_slices_ret_bound_vvh (callEntryStateHOLFinite s callee) cpost cvals rv
      heff0.code (guestInv_callEntry s callee heff0.arena.1)
      (by simpa [heff0.code, callEntryStateHOLFinite] using hlc) hrun_c
  let m1 := setVarHOLFinite (ofString "lst") (.rStruct [.val (.word warr), .val (.word wcnt)])
    { cpost with locals := s.locals }
  have heff_m1 : WorldEff s m1 [] [] wsGw := heff_cp.locals_clock _ _
  have hm1_lst : m1.locals.lookup (ofString "lst") =
      some (.rStruct [.val (.word warr), .val (.word wcnt)]) := by
    simp [m1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  refine worldEff_decCall_alloc heff_m1 (by decide) (ofString "buf") _ hnt_k1 hcr_k1
    (fun pbuf nw m2 hsz_ev _ hm2_loc _ heff_m2 _ _ hpbuf_lo_s hpbuf_add hhp_m2_hi _ hnt_k2 hcr_k2 => ?_)
  have hnw_eq : nw = wcnt * 32#64 := by
    simp [evalHOLExact, evalListHOLExact, hm1_lst, panOpHOL, valueIsWord, valueWord] at hsz_ev
    exact hsz_ev.symm
  subst hnw_eq
  have halloc_hi : pbuf.toNat + ((wcnt * 32#64).toNat + 7) / 8 * 8 ≤ heapLimit := by omega
  refine worldEff_dec heff_m2 _ _ _ hnt_k2 hcr_k2 (fun vi hvi _ hnt_k3 hcr_k3 => ?_)
  have hvi_eq : vi = .val (.word 0) := by simp [evalHOLExact] at hvi; exact hvi.symm
  subst hvi_eq
  let m3 := setVarHOLFinite (ofString "i") (.val (.word 0)) m2
  have heff_m3 : WorldEff s m3 [] [] wsGw := heff_m2.locals_clock _ _
  let BhInv := fun (t : PanSemStateFiniteExact 64 F) =>
    t.locals.lookup (ofString "buf") = some (.val (.word pbuf)) ∧
    t.locals.lookup (ofString "lst") = some (.rStruct [.val (.word warr), .val (.word wcnt)]) ∧
    WordLocals ["i"] t
  have hinv_m3 : BhInv m3 := by
    refine ⟨?_, ?_, ?_⟩
    · simp [m3, setVarHOLFinite, hm2_loc, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "i" ≠ ofString "buf" by decide]
    · simp [m3, setVarHOLFinite, hm2_loc, hm1_lst, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "i" ≠ ofString "lst" by decide, show ofString "buf" ≠ ofString "lst" by decide]
    · intro nm hnm; simp at hnm; subst hnm
      exact ⟨0, by simp [m3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
  have hws_bh : wsafe bhLoopBody_vvh = true := by decide
  refine worldEff_seq hnt_k3 hcr_k3
    (fun hnt_w hcr_w =>
      worldEff_while_cond_vvh _ BhInv (fun _ hinv => hinv)
        (fun t0 cw hcond hnz heff_t hinv_t hnt_b hcr_b => ?_)
        m3.clock m3 rfl heff_m3 hinv_m3 hnt_w hcr_w)
    (fun mid _ heff_mid _ _ => worldEff_return heff_mid _)
  set t := decClockHOLFinite t0
  obtain ⟨ht_buf, ht_lst, ht_wloc⟩ := hinv_t
  obtain ⟨wi_t, hti⟩ := ht_wloc "i" (by simp)
  have ht0_i : t0.locals.lookup (ofString "i") = some (.val (.word wi_t)) := hti
  have ht0_lst : t0.locals.lookup (ofString "lst") =
      some (.rStruct [.val (.word warr), .val (.word wcnt)]) := ht_lst
  have hlt_i : wi_t < wcnt := by
    rw [evalHOLFinite_eq_toExact] at hcond
    simp [evalHOLExact, ht0_i, ht0_lst, Compiler.Encoders.Asm.wordCmpHOL] at hcond
    by_contra hge; simp [hge] at hcond; exact hnz hcond.symm
  obtain ⟨hcp_lo, hcp_hi⟩ :=
    heap_slice_stride_in_heap_vvh pbuf wcnt wi_t 32 0 32 hcnt_dom (by decide) (by decide) (by decide)
      hpbuf_lo_s halloc_hi hlt_i
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hcp_lo hcp_hi
  refine ⟨?_, fun hf => ?_⟩
  · dsimp only [bhLoopBody_vvh] at hnt_b hcr_b ⊢
    refine worldEff_decCall_eff heff_t (ofString "h") .one (ofString "tx_fixed_bytes")
      _ _ _ _ lookup_tx_fixed_bytes_vvh
      (fun callee cvals _ hlc hnt_cb hres_cb =>
        heff_t.trans_noBuf
          (WorldEff.from_locals_clock
            (worldEff_tx_fixed_bytes_vvh (callEntryStateHOLFinite t callee) cvals
              heff_t.code (localsFree_arenaReady t callee _ heff_t.arena)
              (by simpa [heff_t.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
          ws_nil_sub_vvh ws_no_gb_vvh)
      (fun _ _ rvh cpost _ _ _ hsh_h heff_cp hnt_s1 hcr_s1 => ?_)
      hnt_b hcr_b
    rcases rvh with ⟨⟨wh⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh_h
    let u0 := setVarHOLFinite (ofString "h") (.val (.word wh)) { cpost with locals := t.locals }
    have heff_u0 : WorldEff s u0 [] [] wsGw := heff_cp.locals_clock _ _
    have hu0_buf : u0.locals.lookup (ofString "buf") = some (.val (.word pbuf)) := by
      simp [u0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht_buf,
        show ofString "h" ≠ ofString "buf" by decide]
    have hu0_i : u0.locals.lookup (ofString "i") = some (.val (.word wi_t)) := by
      simp [u0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hti,
        show ofString "h" ≠ ofString "i" by decide]
    have hu0_h : u0.locals.lookup (ofString "h") = some (.val (.word wh)) := by
      simp [u0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    refine worldEff_seq hnt_s1 hcr_s1
      (fun hnt_mc hcr_mc =>
        worldEff_call0_funByteEff_vvh heff_u0 funByteEff_memcpy _
          [((pbuf + wi_t * 32#64).toNat, 32)]
          (fun cvals hcvals iv hiv _ => by
            have hargs_mc : evalListHOLFinite u0 (h := fun a => Classical.propDecidable (u0.memaddrs a))
                [.op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "i"), .const 32]],
                 .var .local (ofString "h"), .const 32] =
                some [.val (.word (pbuf + wi_t * 32#64)), .val (.word wh), .val (.word 32#64)] := by
              simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hu0_buf, hu0_i, hu0_h,
                panOpHOL, wordOpHOL, wordOp, valueIsWord, valueWord]
            rw [hargs_mc] at hcvals; injection hcvals with hcvals; subst hcvals
            have hiv' : iv = ((pbuf + wi_t * 32#64).toNat, 32) := by
              simpa [valWordNat] using hiv
            subst hiv'
            exact ⟨_, List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
          (fun iv hiv _ => by
            have hiv' : iv = ((pbuf + wi_t * 32#64).toNat, 32) := List.mem_singleton.mp hiv
            subst hiv'
            exact Or.inr (Or.inr (Or.inr ⟨hcp_lo, hcp_hi⟩)))
          hnt_mc hcr_mc)
      (fun u1 _ heff_u1 _ _ => worldEff_assign_local heff_u1 _ _)
  · exact ⟨(bhLoopBody_keeps_local_vvh t _ (by decide) (by decide) hf).trans ht_buf,
           (bhLoopBody_keeps_local_vvh t _ (by decide) (by decide) hf).trans ht_lst,
           wordLocals_flowing hws_bh ht_wloc (by rcases hf with h | h; exact Or.inl h; exact Or.inr (Or.inr h))⟩

private def dalInnerBody_vvh : ProgHOL 64 :=
  .decCall (ofString "k") .one (ofString "tx_fixed_bytes")
    [.rfield 0 (.var .local (ofString "slots")), .var .local (ofString "j"), .const 32]
    (.seq
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "keys"), .panop .mul [.var .local (ofString "j"), .const 32]],
         .var .local (ofString "k"), .const 32])
      (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1])))

private theorem dalInnerBody_keeps_local_vvh {F : Type}
    (t : PanSemStateFiniteExact 64 F) (key : MlS)
    (hk1 : key ≠ ofString "k") (hk2 : key ≠ ofString "j")
    (hf : (evaluateHOLFiniteState t dalInnerBody_vvh).1 = none ∨
      (evaluateHOLFiniteState t dalInnerBody_vvh).1 = some .continue) :
    (evaluateHOLFiniteState t dalInnerBody_vvh).2.locals.lookup key = t.locals.lookup key := by
  refine eval_decCall_flowing_keeps t _ _ _ _ _ key hk1 (fun u0 hf0 => ?_) hf
  obtain ⟨u1, _, hu1_loc, hf1, heq1⟩ := eval_call0_flowing_inv u0 _ _ hf0
  rw [heq1]
  exact (eval_assign_flowing_keeps_vvh u1 _ _ key hk2 hf1).trans (by rw [hu1_loc])

private theorem dalInnerBody_no_break_vvh {F : Type} (t : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState t dalInnerBody_vvh).1 ≠ some .break := by
  dsimp only [dalInnerBody_vvh]
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
      [.rfield 0 (.var .local (ofString "slots")), .var .local (ofString "j"), .const 32] with _ | vs
  · simp
  · simp only [hargs]
    rcases hlk : lookupCodeHOLFinite t.code.lookup (ofString "tx_fixed_bytes") vs with _ | ⟨b', c', r'⟩
    · simp
    · simp only [hlk]
      by_cases hz : t.clock = 0
      · simp [hz]
      · simp only [hz, ↓reduceIte]
        rcases hcal : evaluateHOLFiniteState (callEntryStateHOLFinite t c') b' with ⟨rc, st⟩
        simp only [hcal]
        rcases rc with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only <;> try simp
        split
        · dsimp only
          rw [evaluateHOLFiniteState_seq_line780]
          have hnb_c0 : ∀ (u : PanSemStateFiniteExact 64 F) (fn : MlS) (as_ : List (ExpHOL 64)),
              (evaluateHOLFiniteState u (.call (some (none, none)) fn as_)).1 ≠ some .break := by
            intro u fn as_
            rw [evaluateHOLFiniteState_call]
            rcases evalListHOLFinite u (h := fun a => Classical.propDecidable (u.memaddrs a)) as_ with _ | vs2
            · simp
            · dsimp only
              rcases lookupCodeHOLFinite u.code.lookup fn vs2 with _ | ⟨b2, c2, r2⟩
              · simp
              · dsimp only
                by_cases hz2 : u.clock = 0
                · rw [if_pos hz2]; simp
                · rw [if_neg hz2]
                  rcases evaluateHOLFiniteState (callEntryStateHOLFinite u c2) b2 with ⟨rc2, _⟩
                  rcases rc2 with _ | (_ | _ | _ | _ | _ | _ | _) <;> dsimp only <;> (repeat' split) <;> simp
          have hnb0 := hnb_c0 (setVarHOLFinite (ofString "k") w { st with locals := t.locals })
            (ofString "memcpy")
            [.op .add [.var .local (ofString "keys"), .panop .mul [.var .local (ofString "j"), .const 32]],
             .var .local (ofString "k"), .const 32]
          rcases hc0 : evaluateHOLFiniteState (setVarHOLFinite (ofString "k") w { st with locals := t.locals })
              (.call (some (none, none)) (ofString "memcpy")
                [.op .add [.var .local (ofString "keys"), .panop .mul [.var .local (ofString "j"), .const 32]],
                 .var .local (ofString "k"), .const 32]) with ⟨r0, m1⟩
          rw [hc0] at hnb0
          cases r0 with
          | none =>
            dsimp only
            rw [evaluateHOLFiniteState_assign]
            split <;> [simp; (split <;> simp)]
          | some r0 => exact hnb0
        · simp

private def dalOuterBody_vvh : ProgHOL 64 :=
  .decCall (ofString "it") (.comb [.one, .one, .one, .one]) (ofString "rlp_item")
    [.load .one (.op .add [.rfield 0 (.var .local (ofString "lst")), .panop .mul [.var .local (ofString "i"), .const 16]]),
     .load .one (.op .add [.rfield 0 (.var .local (ofString "lst")), .panop .mul [.var .local (ofString "i"), .const 16], .const 8])]
    (.seq
      (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "it"))) (.const 1))
        (.raise (ofString "TxErr") (.const 19))
        .skip)
      (.decCall (ofString "ent") (.comb [.one, .one]) (ofString "rlp_list_to_slices")
        [.rfield 1 (.var .local (ofString "it")), .rfield 2 (.var .local (ofString "it"))]
        (.seq
          (.ite (.cmp .notEqual (.rfield 1 (.var .local (ofString "ent"))) (.const 2))
            (.raise (ofString "TxErr") (.const 19))
            .skip)
          (.decCall (ofString "addr") .one (ofString "tx_fixed_bytes")
            [.rfield 0 (.var .local (ofString "ent")), .const 0, .const 20]
            (.decCall (ofString "sl") (.comb [.one, .one]) (ofString "tx_list_item")
              [.rfield 0 (.var .local (ofString "ent")), .const 1]
              (.decCall (ofString "slots") (.comb [.one, .one]) (ofString "rlp_list_to_slices")
                [.rfield 0 (.var .local (ofString "sl")), .rfield 1 (.var .local (ofString "sl"))]
                (.decCall (ofString "keys") .one (ofString "alloc")
                  [.panop .mul [.rfield 1 (.var .local (ofString "slots")), .const 32]]
                  (.dec (ofString "j") .one (.const 0)
                    (.seq
                      (.while (.cmp .lower (.var .local (ofString "j")) (.rfield 1 (.var .local (ofString "slots"))))
                        dalInnerBody_vvh)
                      (.dec (ofString "rec") .one
                        (.op .add [.var .local (ofString "recs"), .panop .mul [.var .local (ofString "i"), .const 24]])
                        (.seq
                          (.store (.op .add [.var .local (ofString "rec"), .const 0]) (.var .local (ofString "addr")))
                          (.seq
                            (.store (.op .add [.var .local (ofString "rec"), .const 8]) (.var .local (ofString "keys")))
                            (.seq
                              (.store (.op .add [.var .local (ofString "rec"), .const 16]) (.rfield 1 (.var .local (ofString "slots"))))
                              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))))))))))))))

private theorem dalOuterBody_keeps_recs_lst_vvh {F : Type}
    (t : PanSemStateFiniteExact 64 F) (key : MlS)
    (hk_recs_lst : key = ofString "recs" ∨ key = ofString "lst")
    (hf : (evaluateHOLFiniteState t dalOuterBody_vvh).1 = none ∨
      (evaluateHOLFiniteState t dalOuterBody_vvh).1 = some .continue) :
    (evaluateHOLFiniteState t dalOuterBody_vvh).2.locals.lookup key = t.locals.lookup key := by
  have hk_it : key ≠ ofString "it" := by rcases hk_recs_lst with rfl | rfl <;> decide
  have hk_ent : key ≠ ofString "ent" := by rcases hk_recs_lst with rfl | rfl <;> decide
  have hk_addr : key ≠ ofString "addr" := by rcases hk_recs_lst with rfl | rfl <;> decide
  have hk_sl : key ≠ ofString "sl" := by rcases hk_recs_lst with rfl | rfl <;> decide
  have hk_slots : key ≠ ofString "slots" := by rcases hk_recs_lst with rfl | rfl <;> decide
  have hk_keys : key ≠ ofString "keys" := by rcases hk_recs_lst with rfl | rfl <;> decide
  have hk_j : key ≠ ofString "j" := by rcases hk_recs_lst with rfl | rfl <;> decide
  have hk_k : key ≠ ofString "k" := by rcases hk_recs_lst with rfl | rfl <;> decide
  have hk_rec : key ≠ ofString "rec" := by rcases hk_recs_lst with rfl | rfl <;> decide
  have hk_i : key ≠ ofString "i" := by rcases hk_recs_lst with rfl | rfl <;> decide
  refine eval_decCall_flowing_keeps t _ _ _ _ _ key hk_it (fun u1 hf1 => ?_) hf
  obtain ⟨hf2, heq2⟩ := eval_guard_raise_flowing_inv u1 _ _ _ hf1
  rw [heq2]
  refine eval_decCall_flowing_keeps u1 _ _ _ _ _ key hk_ent (fun u3 hf3 => ?_) hf2
  obtain ⟨hf4, heq4⟩ := eval_guard_raise_flowing_inv u3 _ _ _ hf3
  rw [heq4]
  refine eval_decCall_flowing_keeps u3 _ _ _ _ _ key hk_addr (fun u5 hf5 => ?_) hf4
  refine eval_decCall_flowing_keeps u5 _ _ _ _ _ key hk_sl (fun u6 hf6 => ?_) hf5
  refine eval_decCall_flowing_keeps u6 _ _ _ _ _ key hk_slots (fun u7 hf7 => ?_) hf6
  refine eval_decCall_flowing_keeps u7 _ _ _ _ _ key hk_keys (fun u8 hf8 => ?_) hf7
  refine eval_dec_flowing_keeps u8 _ _ _ _ key hk_j (fun u9 hf9 => ?_) hf8
  rw [evaluateHOLFiniteState_seq_line780] at hf9 ⊢
  rcases hw : evaluateHOLFiniteState u9
      (.while (.cmp .lower (.var .local (ofString "j")) (.rfield 1 (.var .local (ofString "slots")))) dalInnerBody_vvh)
      with ⟨rw0, uw⟩
  rw [hw] at hf9
  cases rw0 with
  | some r =>
    exfalso
    have hnc : (evaluateHOLFiniteState u9
        (.while (.cmp .lower (.var .local (ofString "j")) (.rfield 1 (.var .local (ofString "slots")))) dalInnerBody_vvh)).1 ≠
        some .continue := by
      -- while never produces .continue!
      have : ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock ≤ k →
          (evaluateHOLFiniteState st (.while (.cmp .lower (.var .local (ofString "j"))
            (.rfield 1 (.var .local (ofString "slots")))) dalInnerBody_vvh)).1 ≠ some .continue := by
        intro k
        induction k with
        | zero =>
          intro st hck; rw [evaluateHOLFiniteState_while_fixClockRewrite]
          rcases @evalHOLFinite 64 F _ st (fun a => Classical.propDecidable (st.memaddrs a)) _ with _ | cv
          · simp
          · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
            by_cases hw0 : cw = 0#64
            · subst hw0; simp
            · rw [if_neg hw0]; have hk0 : st.clock = 0 := by omega
              rw [if_pos hk0]; simp
        | succ k ih =>
          intro st hck; rw [evaluateHOLFiniteState_while_fixClockRewrite]
          rcases @evalHOLFinite 64 F _ st (fun a => Classical.propDecidable (st.memaddrs a)) _ with _ | cv
          · simp
          · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
            by_cases hw0 : cw = 0#64
            · subst hw0; simp
            · rw [if_neg hw0]
              by_cases hk0 : st.clock = 0
              · rw [if_pos hk0]; simp
              · rw [if_neg hk0]
                have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) dalInnerBody_vvh
                rcases hbr : evaluateHOLFiniteState (decClockHOLFinite st) dalInnerBody_vvh with ⟨r1, m1⟩
                simp only [hbr] at rem ⊢
                rcases r1 with _ | (_ | _ | _ | _ | _ | _ | _)
                · exact ih m1 (by change m1.clock ≤ st.clock - 1 at rem; omega)
                · simp
                · simp
                · simp
                · exact ih m1 (by change m1.clock ≤ st.clock - 1 at rem; omega)
                · simp
                · simp
                · simp
      exact this u9.clock u9 le_rfl
    rw [hw] at hnc
    rcases hf9 with hf9 | hf9 <;> [cases hf9; exact hnc hf9]
  | none =>
    dsimp only at hf9 ⊢
    have huw_k : uw.locals.lookup key = u9.locals.lookup key := by
      have hk := eval_while_flowing_keeps _ dalInnerBody_vvh key
        (fun s0 hf0 => dalInnerBody_keeps_local_vvh s0 key hk_k hk_j hf0)
        dalInnerBody_no_break_vvh u9.clock u9 le_rfl (by rw [hw]; exact Or.inl rfl)
      rwa [hw] at hk
    refine (eval_dec_flowing_keeps uw _ _ _ _ key hk_rec (fun u10 hf10 => ?_) hf9).trans huw_k
    obtain ⟨u11, _, hu11_loc, hf11, heq11⟩ := eval_store_flowing_inv_vvh u10 _ _ hf10
    rw [heq11]
    obtain ⟨u12, _, hu12_loc, hf12, heq12⟩ := eval_store_flowing_inv_vvh u11 _ _ hf11
    rw [heq12]
    obtain ⟨u13, _, hu13_loc, hf13, heq13⟩ := eval_store_flowing_inv_vvh u12 _ _ hf12
    rw [heq13]
    exact (eval_assign_flowing_keeps_vvh u13 _ _ key hk_i hf13).trans
      (by rw [hu13_loc, hu12_loc, hu11_loc])

private theorem worldEff_decode_access_list_vvh {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "decode_access_list") vals =
      some (sourceFnBody Guest.Software.guestFn_decode_access_list, s.locals, .comb [.one, .one]))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_access_list)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_access_list)).1) :
    WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_access_list)).2
      [] [] wsGw := by
  have _ := hl
  have heff0 : WorldEff s s [] [] wsGw := WorldEff.refl s [] [] wsGw hAR hc
  have hbody : sourceFnBody Guest.Software.guestFn_decode_access_list =
      .decCall (ofString "lst") (.comb [.one, .one]) (ofString "rlp_list_to_slices")
        [.var .local (ofString "p"), .var .local (ofString "len")]
        (.decCall (ofString "recs") .one (ofString "alloc")
          [.panop .mul [.rfield 1 (.var .local (ofString "lst")), .const 24]]
          (.dec (ofString "i") .one (.const 0)
            (.seq
              (.while (.cmp .lower (.var .local (ofString "i")) (.rfield 1 (.var .local (ofString "lst"))))
                dalOuterBody_vvh)
              (.return (.rstruct [.var .local (ofString "recs"), .rfield 1 (.var .local (ofString "lst"))]))))) := rfl
  rw [hbody] at hnt hres ⊢
  refine worldEff_decCall_eff heff0 (ofString "lst") (.comb [.one, .one]) (ofString "rlp_list_to_slices")
    _ _ _ _ lookup_rlp_list_to_slices_vvh
    (fun callee cvals _ hlc hnt_cb hres_cb =>
      heff0.trans_noBuf
        (WorldEff.from_locals_clock
          (worldEff_rlp_list_to_slices_vvh (callEntryStateHOLFinite s callee) cvals
            heff0.code (localsFree_arenaReady s callee _ heff0.arena)
            (by simpa [heff0.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
        ws_nil_sub_vvh ws_no_gb_vvh)
    (fun callee cvals rv cpost _ hlc hrun_c _ heff_cp hnt_k1 hcr_k1 => ?_)
    hnt (Or.inr (Or.inr (Or.inr hres)))
  obtain ⟨warr, wcnt, rfl, hcnt_dom⟩ :=
    rlp_list_to_slices_ret_bound_vvh (callEntryStateHOLFinite s callee) cpost cvals rv
      heff0.code (guestInv_callEntry s callee heff0.arena.1)
      (by simpa [heff0.code, callEntryStateHOLFinite] using hlc) hrun_c
  let m1 := setVarHOLFinite (ofString "lst") (.rStruct [.val (.word warr), .val (.word wcnt)])
    { cpost with locals := s.locals }
  have heff_m1 : WorldEff s m1 [] [] wsGw := heff_cp.locals_clock _ _
  have hm1_lst : m1.locals.lookup (ofString "lst") =
      some (.rStruct [.val (.word warr), .val (.word wcnt)]) := by
    simp [m1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  refine worldEff_decCall_alloc heff_m1 (by decide) (ofString "recs") _ hnt_k1 hcr_k1
    (fun precs nw m2 hsz_ev _ hm2_loc _ heff_m2 _ _ hprecs_lo_s hprecs_add hhp_m2_hi _ hnt_k2 hcr_k2 => ?_)
  have hnw_eq : nw = wcnt * 24#64 := by
    simp [evalHOLExact, evalListHOLExact, hm1_lst, panOpHOL, valueIsWord, valueWord] at hsz_ev
    exact hsz_ev.symm
  subst hnw_eq
  have halloc_hi : precs.toNat + ((wcnt * 24#64).toNat + 7) / 8 * 8 ≤ heapLimit := by omega
  refine worldEff_dec heff_m2 _ _ _ hnt_k2 hcr_k2 (fun vi hvi _ hnt_k3 hcr_k3 => ?_)
  have hvi_eq : vi = .val (.word 0) := by simp [evalHOLExact] at hvi; exact hvi.symm
  subst hvi_eq
  let m3 := setVarHOLFinite (ofString "i") (.val (.word 0)) m2
  have heff_m3 : WorldEff s m3 [] [] wsGw := heff_m2.locals_clock _ _
  let DalInv := fun (t : PanSemStateFiniteExact 64 F) =>
    t.locals.lookup (ofString "recs") = some (.val (.word precs)) ∧
    t.locals.lookup (ofString "lst") = some (.rStruct [.val (.word warr), .val (.word wcnt)]) ∧
    WordLocals ["i"] t
  have hinv_m3 : DalInv m3 := by
    refine ⟨?_, ?_, ?_⟩
    · simp [m3, setVarHOLFinite, hm2_loc, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "i" ≠ ofString "recs" by decide]
    · simp [m3, setVarHOLFinite, hm2_loc, hm1_lst, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "i" ≠ ofString "lst" by decide, show ofString "recs" ≠ ofString "lst" by decide]
    · intro nm hnm; simp at hnm; subst hnm
      exact ⟨0, by simp [m3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
  have hws_dal : wsafe dalOuterBody_vvh = true := by decide
  refine worldEff_seq hnt_k3 hcr_k3
    (fun hnt_w hcr_w =>
      worldEff_while_cond_vvh _ DalInv (fun _ hinv => hinv)
        (fun t0 cw hcond hnz heff_t hinv_t hnt_b hcr_b => ?_)
        m3.clock m3 rfl heff_m3 hinv_m3 hnt_w hcr_w)
    (fun mid _ heff_mid _ _ => worldEff_return heff_mid _)
  set t := decClockHOLFinite t0
  obtain ⟨ht_recs, ht_lst, ht_wloc⟩ := hinv_t
  obtain ⟨wi_t, hti⟩ := ht_wloc "i" (by simp)
  have ht0_i : t0.locals.lookup (ofString "i") = some (.val (.word wi_t)) := hti
  have ht0_lst : t0.locals.lookup (ofString "lst") =
      some (.rStruct [.val (.word warr), .val (.word wcnt)]) := ht_lst
  have hlt_i : wi_t < wcnt := by
    rw [evalHOLFinite_eq_toExact] at hcond
    simp [evalHOLExact, ht0_i, ht0_lst, Compiler.Encoders.Asm.wordCmpHOL] at hcond
    by_contra hge; simp [hge] at hcond; exact hnz hcond.symm
  obtain ⟨hrec0_lo, hrec0_hi⟩ :=
    heap_slice_stride_in_heap_vvh precs wcnt wi_t 24 0 8 hcnt_dom (by decide) (by decide) (by decide)
      hprecs_lo_s halloc_hi hlt_i
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hrec0_lo hrec0_hi
  obtain ⟨hrec8_lo, hrec8_hi⟩ :=
    heap_slice_stride_in_heap_vvh precs wcnt wi_t 24 8 8 hcnt_dom (by decide) (by decide) (by decide)
      hprecs_lo_s halloc_hi hlt_i
  obtain ⟨hrec16_lo, hrec16_hi⟩ :=
    heap_slice_stride_in_heap_vvh precs wcnt wi_t 24 16 8 hcnt_dom (by decide) (by decide) (by decide)
      hprecs_lo_s halloc_hi hlt_i
  refine ⟨?_, fun hf => ?_⟩
  · dsimp only [dalOuterBody_vvh] at hnt_b hcr_b ⊢
    refine worldEff_decCall_eff heff_t (ofString "it") (.comb [.one, .one, .one, .one]) (ofString "rlp_item")
      _ _ _ _ lookup_rlp_item_vvh
      (fun callee cvals _ hlc hnt_cb hres_cb =>
        heff_t.trans_noBuf
          (WorldEff.from_locals_clock
            (worldEff_rlp_item_vvh (callEntryStateHOLFinite t callee) cvals
              heff_t.code (localsFree_arenaReady t callee _ heff_t.arena)
              (by simpa [heff_t.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
          ws_nil_sub_vvh ws_no_gb_vvh)
      (fun _ _ rvit cpost1 _ _ _ _ heff_cp1 hnt_1 hcr_1 => ?_)
      hnt_b hcr_b
    let u1 := setVarHOLFinite (ofString "it") rvit { cpost1 with locals := t.locals }
    have heff_u1 : WorldEff s u1 [] [] wsGw := heff_cp1.locals_clock _ _
    have hu1_recs : u1.locals.lookup (ofString "recs") = some (.val (.word precs)) := by
      simp [u1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht_recs,
        show ofString "it" ≠ ofString "recs" by decide]
    have hu1_i : u1.locals.lookup (ofString "i") = some (.val (.word wi_t)) := by
      simp [u1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hti,
        show ofString "it" ≠ ofString "i" by decide]
    refine worldEff_seq hnt_1 hcr_1
      (fun hnt_g1 hcr_g1 =>
        worldEff_ite heff_u1 _ hnt_g1 hcr_g1
          (fun _ _ _ _ _ => worldEff_raise heff_u1 _ _)
          (fun _ _ _ => worldEff_skip heff_u1))
      (fun u2 hu2 heff_u2 hnt_2 hcr_2 => ?_)
    have hu2_eq : u2 = u1 := by
      rw [evaluateHOLFiniteState_ite] at hu2
      split at hu2
      · split at hu2
        · rw [evaluateHOLFiniteState_skip] at hu2; injection hu2 with _ hm; exact hm.symm
        · rw [evaluateHOLFiniteState_raise] at hu2
          split at hu2 <;> [ (dsimp only at hu2; split at hu2 <;> cases hu2); cases hu2 ]
      · cases hu2
    subst hu2_eq
    refine worldEff_decCall_eff heff_u1 (ofString "ent") (.comb [.one, .one]) (ofString "rlp_list_to_slices")
      _ _ _ _ lookup_rlp_list_to_slices_vvh
      (fun callee cvals _ hlc hnt_cb hres_cb =>
        heff_u1.trans_noBuf
          (WorldEff.from_locals_clock
            (worldEff_rlp_list_to_slices_vvh (callEntryStateHOLFinite u1 callee) cvals
              heff_u1.code (localsFree_arenaReady u1 callee _ heff_u1.arena)
              (by simpa [heff_u1.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
          ws_nil_sub_vvh ws_no_gb_vvh)
      (fun _ _ rvent cpost2 _ _ _ _ heff_cp2 hnt_3 hcr_3 => ?_)
      hnt_2 hcr_2
    let u3 := setVarHOLFinite (ofString "ent") rvent { cpost2 with locals := u1.locals }
    have heff_u3 : WorldEff s u3 [] [] wsGw := heff_cp2.locals_clock _ _
    have hu3_recs : u3.locals.lookup (ofString "recs") = some (.val (.word precs)) := by
      simp [u3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu1_recs,
        show ofString "ent" ≠ ofString "recs" by decide]
    have hu3_i : u3.locals.lookup (ofString "i") = some (.val (.word wi_t)) := by
      simp [u3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu1_i,
        show ofString "ent" ≠ ofString "i" by decide]
    refine worldEff_seq hnt_3 hcr_3
      (fun hnt_g2 hcr_g2 =>
        worldEff_ite heff_u3 _ hnt_g2 hcr_g2
          (fun _ _ _ _ _ => worldEff_raise heff_u3 _ _)
          (fun _ _ _ => worldEff_skip heff_u3))
      (fun u4 hu4 heff_u4 hnt_4 hcr_4 => ?_)
    have hu4_eq : u4 = u3 := by
      rw [evaluateHOLFiniteState_ite] at hu4
      split at hu4
      · split at hu4
        · rw [evaluateHOLFiniteState_skip] at hu4; injection hu4 with _ hm; exact hm.symm
        · rw [evaluateHOLFiniteState_raise] at hu4
          split at hu4 <;> [ (dsimp only at hu4; split at hu4 <;> cases hu4); cases hu4 ]
      · cases hu4
    subst hu4_eq
    refine worldEff_decCall_eff heff_u3 (ofString "addr") .one (ofString "tx_fixed_bytes")
      _ _ _ _ lookup_tx_fixed_bytes_vvh
      (fun callee cvals _ hlc hnt_cb hres_cb =>
        heff_u3.trans_noBuf
          (WorldEff.from_locals_clock
            (worldEff_tx_fixed_bytes_vvh (callEntryStateHOLFinite u3 callee) cvals
              heff_u3.code (localsFree_arenaReady u3 callee _ heff_u3.arena)
              (by simpa [heff_u3.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
          ws_nil_sub_vvh ws_no_gb_vvh)
      (fun _ _ rvaddr cpost3 _ _ _ hsh_addr heff_cp3 hnt_5 hcr_5 => ?_)
      hnt_4 hcr_4
    rcases rvaddr with ⟨⟨waddr⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh_addr
    let u5 := setVarHOLFinite (ofString "addr") (.val (.word waddr)) { cpost3 with locals := u3.locals }
    have heff_u5 : WorldEff s u5 [] [] wsGw := heff_cp3.locals_clock _ _
    have hu5_recs : u5.locals.lookup (ofString "recs") = some (.val (.word precs)) := by
      simp [u5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu3_recs,
        show ofString "addr" ≠ ofString "recs" by decide]
    have hu5_i : u5.locals.lookup (ofString "i") = some (.val (.word wi_t)) := by
      simp [u5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu3_i,
        show ofString "addr" ≠ ofString "i" by decide]
    have hu5_addr : u5.locals.lookup (ofString "addr") = some (.val (.word waddr)) := by
      simp [u5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    refine worldEff_decCall_eff heff_u5 (ofString "sl") (.comb [.one, .one]) (ofString "tx_list_item")
      _ _ _ _ lookup_tx_list_item_vvh
      (fun callee cvals _ hlc hnt_cb hres_cb =>
        heff_u5.trans_noBuf
          (WorldEff.from_locals_clock
            (worldEff_tx_list_item_vvh (callEntryStateHOLFinite u5 callee) cvals
              heff_u5.code (localsFree_arenaReady u5 callee _ heff_u5.arena)
              (by simpa [heff_u5.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
          ws_nil_sub_vvh ws_no_gb_vvh)
      (fun _ _ rvsl cpost4 _ _ _ _ heff_cp4 hnt_6 hcr_6 => ?_)
      hnt_5 hcr_5
    let u6 := setVarHOLFinite (ofString "sl") rvsl { cpost4 with locals := u5.locals }
    have heff_u6 : WorldEff s u6 [] [] wsGw := heff_cp4.locals_clock _ _
    have hu6_recs : u6.locals.lookup (ofString "recs") = some (.val (.word precs)) := by
      simp [u6, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu5_recs,
        show ofString "sl" ≠ ofString "recs" by decide]
    have hu6_i : u6.locals.lookup (ofString "i") = some (.val (.word wi_t)) := by
      simp [u6, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu5_i,
        show ofString "sl" ≠ ofString "i" by decide]
    have hu6_addr : u6.locals.lookup (ofString "addr") = some (.val (.word waddr)) := by
      simp [u6, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu5_addr,
        show ofString "sl" ≠ ofString "addr" by decide]
    refine worldEff_decCall_eff heff_u6 (ofString "slots") (.comb [.one, .one]) (ofString "rlp_list_to_slices")
      _ _ _ _ lookup_rlp_list_to_slices_vvh
      (fun callee cvals _ hlc hnt_cb hres_cb =>
        heff_u6.trans_noBuf
          (WorldEff.from_locals_clock
            (worldEff_rlp_list_to_slices_vvh (callEntryStateHOLFinite u6 callee) cvals
              heff_u6.code (localsFree_arenaReady u6 callee _ heff_u6.arena)
              (by simpa [heff_u6.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
          ws_nil_sub_vvh ws_no_gb_vvh)
      (fun callee cvals rvslots cpost5 _ hlc hrun_c5 _ heff_cp5 hnt_7 hcr_7 => ?_)
      hnt_6 hcr_6
    obtain ⟨wsl_arr, wsl_cnt, rfl, hsl_dom⟩ :=
      rlp_list_to_slices_ret_bound_vvh (callEntryStateHOLFinite u6 callee) cpost5 cvals rvslots
        heff_u6.code (guestInv_callEntry u6 callee heff_u6.arena.1)
        (by simpa [heff_u6.code, callEntryStateHOLFinite] using hlc) hrun_c5
    let u7 := setVarHOLFinite (ofString "slots") (.rStruct [.val (.word wsl_arr), .val (.word wsl_cnt)])
      { cpost5 with locals := u6.locals }
    have heff_u7 : WorldEff s u7 [] [] wsGw := heff_cp5.locals_clock _ _
    have hu7_slots : u7.locals.lookup (ofString "slots") =
        some (.rStruct [.val (.word wsl_arr), .val (.word wsl_cnt)]) := by
      simp [u7, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hu7_recs : u7.locals.lookup (ofString "recs") = some (.val (.word precs)) := by
      simp [u7, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu6_recs,
        show ofString "slots" ≠ ofString "recs" by decide]
    have hu7_i : u7.locals.lookup (ofString "i") = some (.val (.word wi_t)) := by
      simp [u7, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu6_i,
        show ofString "slots" ≠ ofString "i" by decide]
    have hu7_addr : u7.locals.lookup (ofString "addr") = some (.val (.word waddr)) := by
      simp [u7, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu6_addr,
        show ofString "slots" ≠ ofString "addr" by decide]
    refine worldEff_decCall_alloc heff_u7 (by decide) (ofString "keys") _ hnt_7 hcr_7
      (fun pkeys nwk u8 hsz_k _ hu8_loc _ heff_u8 _ _ hpkeys_lo_s hpkeys_add hhp_u8_hi _ hnt_8 hcr_8 => ?_)
    have hnwk_eq : nwk = wsl_cnt * 32#64 := by
      simp [evalHOLExact, evalListHOLExact, hu7_slots, panOpHOL, valueIsWord, valueWord] at hsz_k
      exact hsz_k.symm
    subst hnwk_eq
    have hkeys_hi : pkeys.toNat + ((wsl_cnt * 32#64).toNat + 7) / 8 * 8 ≤ heapLimit := by omega
    refine worldEff_dec heff_u8 _ _ _ hnt_8 hcr_8 (fun vj hvj _ hnt_9 hcr_9 => ?_)
    have hvj_eq : vj = .val (.word 0) := by simp [evalHOLExact] at hvj; exact hvj.symm
    subst hvj_eq
    let u9 := setVarHOLFinite (ofString "j") (.val (.word 0)) u8
    have heff_u9 : WorldEff s u9 [] [] wsGw := heff_u8.locals_clock _ _
    have hu9_slots : u9.locals.lookup (ofString "slots") =
        some (.rStruct [.val (.word wsl_arr), .val (.word wsl_cnt)]) := by
      simp [u9, setVarHOLFinite, hu8_loc, hu7_slots, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "j" ≠ ofString "slots" by decide, show ofString "keys" ≠ ofString "slots" by decide]
    have hu9_keys : u9.locals.lookup (ofString "keys") = some (.val (.word pkeys)) := by
      simp [u9, setVarHOLFinite, hu8_loc, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "j" ≠ ofString "keys" by decide]
    have hu9_recs : u9.locals.lookup (ofString "recs") = some (.val (.word precs)) := by
      simp [u9, setVarHOLFinite, hu8_loc, hu7_recs, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "j" ≠ ofString "recs" by decide, show ofString "keys" ≠ ofString "recs" by decide]
    have hu9_i : u9.locals.lookup (ofString "i") = some (.val (.word wi_t)) := by
      simp [u9, setVarHOLFinite, hu8_loc, hu7_i, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "j" ≠ ofString "i" by decide, show ofString "keys" ≠ ofString "i" by decide]
    have hu9_addr : u9.locals.lookup (ofString "addr") = some (.val (.word waddr)) := by
      simp [u9, setVarHOLFinite, hu8_loc, hu7_addr, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "j" ≠ ofString "addr" by decide, show ofString "keys" ≠ ofString "addr" by decide]
    let InnerInv := fun (z : PanSemStateFiniteExact 64 F) =>
      z.locals.lookup (ofString "keys") = some (.val (.word pkeys)) ∧
      z.locals.lookup (ofString "slots") = some (.rStruct [.val (.word wsl_arr), .val (.word wsl_cnt)]) ∧
      WordLocals ["j"] z
    have hinv_u9 : InnerInv u9 := ⟨hu9_keys, hu9_slots, fun nm hnm => by
      simp at hnm; subst hnm; exact ⟨0, by simp [u9, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩⟩
    have hws_in : wsafe dalInnerBody_vvh = true := by decide
    refine worldEff_seq hnt_9 hcr_9
      (fun hnt_iw hcr_iw =>
        worldEff_while_cond_vvh _ InnerInv (fun _ hinv => hinv)
          (fun z0 cw_j hcond_j hnz_j heff_z hinv_z hnt_ib hcr_ib => ?_)
          u9.clock u9 rfl heff_u9 hinv_u9 hnt_iw hcr_iw)
      (fun uw huw heff_uw hnt_10 hcr_10 => ?_)
    · set z := decClockHOLFinite z0
      obtain ⟨hz_keys, hz_slots, hz_wloc⟩ := hinv_z
      obtain ⟨wj_z, hzj⟩ := hz_wloc "j" (by simp)
      have hz0_j : z0.locals.lookup (ofString "j") = some (.val (.word wj_z)) := hzj
      have hz0_slots : z0.locals.lookup (ofString "slots") =
          some (.rStruct [.val (.word wsl_arr), .val (.word wsl_cnt)]) := hz_slots
      have hlt_j : wj_z < wsl_cnt := by
        rw [evalHOLFinite_eq_toExact] at hcond_j
        simp [evalHOLExact, hz0_j, hz0_slots, Compiler.Encoders.Asm.wordCmpHOL] at hcond_j
        by_contra hge; simp [hge] at hcond_j; exact hnz_j hcond_j.symm
      obtain ⟨hk_lo, hk_hi⟩ :=
        heap_slice_stride_in_heap_vvh pkeys wsl_cnt wj_z 32 0 32 hsl_dom (by decide) (by decide) (by decide)
          hpkeys_lo_s hkeys_hi hlt_j
      simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hk_lo hk_hi
      refine ⟨?_, fun hfz => ?_⟩
      · dsimp only [dalInnerBody_vvh] at hnt_ib hcr_ib ⊢
        refine worldEff_decCall_eff heff_z (ofString "k") .one (ofString "tx_fixed_bytes")
          _ _ _ _ lookup_tx_fixed_bytes_vvh
          (fun callee cvals _ hlc hnt_cb hres_cb =>
            heff_z.trans_noBuf
              (WorldEff.from_locals_clock
                (worldEff_tx_fixed_bytes_vvh (callEntryStateHOLFinite z callee) cvals
                  heff_z.code (localsFree_arenaReady z callee _ heff_z.arena)
                  (by simpa [heff_z.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
              ws_nil_sub_vvh ws_no_gb_vvh)
          (fun _ _ rvk cpostk _ _ _ hsh_k heff_cpk hnt_is hcr_is => ?_)
          hnt_ib hcr_ib
        rcases rvk with ⟨⟨wk⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh_k
        let z1 := setVarHOLFinite (ofString "k") (.val (.word wk)) { cpostk with locals := z.locals }
        have heff_z1 : WorldEff s z1 [] [] wsGw := heff_cpk.locals_clock _ _
        have hz1_keys : z1.locals.lookup (ofString "keys") = some (.val (.word pkeys)) := by
          simp [z1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hz_keys,
            show ofString "k" ≠ ofString "keys" by decide]
        have hz1_j : z1.locals.lookup (ofString "j") = some (.val (.word wj_z)) := by
          simp [z1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hzj,
            show ofString "k" ≠ ofString "j" by decide]
        have hz1_k : z1.locals.lookup (ofString "k") = some (.val (.word wk)) := by
          simp [z1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        refine worldEff_seq hnt_is hcr_is
          (fun hnt_mc hcr_mc =>
            worldEff_call0_funByteEff_vvh heff_z1 funByteEff_memcpy _
              [((pkeys + wj_z * 32#64).toNat, 32)]
              (fun cvals hcvals iv hiv _ => by
                have hargs_mc : evalListHOLFinite z1 (h := fun a => Classical.propDecidable (z1.memaddrs a))
                    [.op .add [.var .local (ofString "keys"), .panop .mul [.var .local (ofString "j"), .const 32]],
                     .var .local (ofString "k"), .const 32] =
                    some [.val (.word (pkeys + wj_z * 32#64)), .val (.word wk), .val (.word 32#64)] := by
                  simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hz1_keys, hz1_j, hz1_k,
                    panOpHOL, wordOpHOL, wordOp, valueIsWord, valueWord]
                rw [hargs_mc] at hcvals; injection hcvals with hcvals; subst hcvals
                have hiv' : iv = ((pkeys + wj_z * 32#64).toNat, 32) := by
                  simpa [valWordNat] using hiv
                subst hiv'
                exact ⟨_, List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
              (fun iv hiv _ => by
                have hiv' : iv = ((pkeys + wj_z * 32#64).toNat, 32) := List.mem_singleton.mp hiv
                subst hiv'
                exact Or.inr (Or.inr (Or.inr ⟨hk_lo, hk_hi⟩)))
              hnt_mc hcr_mc)
          (fun z2 _ heff_z2 _ _ => worldEff_assign_local heff_z2 _ _)
      · exact ⟨(dalInnerBody_keeps_local_vvh z _ (by decide) (by decide) hfz).trans hz_keys,
               (dalInnerBody_keeps_local_vvh z _ (by decide) (by decide) hfz).trans hz_slots,
               wordLocals_flowing hws_in hz_wloc (by rcases hfz with h | h; exact Or.inl h; exact Or.inr (Or.inr h))⟩
    · have huw_keep : ∀ key, key ≠ ofString "k" → key ≠ ofString "j" →
          uw.locals.lookup key = u9.locals.lookup key := by
        intro key hk1 hk2
        have hk := eval_while_flowing_keeps _ dalInnerBody_vvh key
          (fun s0 hf0 => dalInnerBody_keeps_local_vvh s0 key hk1 hk2 hf0)
          dalInnerBody_no_break_vvh u9.clock u9 le_rfl (by rw [huw]; exact Or.inl rfl)
        rwa [huw] at hk
      have huw_recs : uw.locals.lookup (ofString "recs") = some (.val (.word precs)) :=
        (huw_keep _ (by decide) (by decide)).trans hu9_recs
      have huw_i : uw.locals.lookup (ofString "i") = some (.val (.word wi_t)) :=
        (huw_keep _ (by decide) (by decide)).trans hu9_i
      have huw_addr : uw.locals.lookup (ofString "addr") = some (.val (.word waddr)) :=
        (huw_keep _ (by decide) (by decide)).trans hu9_addr
      have huw_keys : uw.locals.lookup (ofString "keys") = some (.val (.word pkeys)) :=
        (huw_keep _ (by decide) (by decide)).trans hu9_keys
      have huw_slots : uw.locals.lookup (ofString "slots") =
          some (.rStruct [.val (.word wsl_arr), .val (.word wsl_cnt)]) :=
        (huw_keep _ (by decide) (by decide)).trans hu9_slots
      refine worldEff_dec heff_uw _ _ _ hnt_10 hcr_10 (fun vrec hvrec _ hnt_11 hcr_11 => ?_)
      have hvrec_eq : vrec = .val (.word (precs + wi_t * 24#64)) := by
        simp [evalHOLExact, evalListHOLExact, huw_recs, huw_i,
          panOpHOL, wordOpHOL, wordOp, valueIsWord, valueWord] at hvrec
        exact hvrec.symm
      subst hvrec_eq
      let u10 := setVarHOLFinite (ofString "rec") (.val (.word (precs + wi_t * 24#64))) uw
      have heff_u10 : WorldEff s u10 [] [] wsGw := heff_uw.locals_clock _ _
      have hu10_rec : u10.locals.lookup (ofString "rec") =
          some (.val (.word (precs + wi_t * 24#64))) := by
        simp [u10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hu10_addr : u10.locals.lookup (ofString "addr") = some (.val (.word waddr)) := by
        simp [u10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, huw_addr,
          show ofString "rec" ≠ ofString "addr" by decide]
      have hu10_keys : u10.locals.lookup (ofString "keys") = some (.val (.word pkeys)) := by
        simp [u10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, huw_keys,
          show ofString "rec" ≠ ofString "keys" by decide]
      have hu10_slots : u10.locals.lookup (ofString "slots") =
          some (.rStruct [.val (.word wsl_arr), .val (.word wsl_cnt)]) := by
        simp [u10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, huw_slots,
          show ofString "rec" ≠ ofString "slots" by decide]
      refine worldEff_seq hnt_11 hcr_11
        (fun _ _ => worldEff_store_word heff_u10 _ _
          (fun v hv => by simp [evalHOLExact, hu10_addr] at hv; exact ⟨_, hv.symm⟩)
          (fun x hx _ => by
            simp [evalHOLExact, evalListHOLExact, hu10_rec, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
            subst hx; exact Or.inr (Or.inr (Or.inr ⟨hrec0_lo, hrec0_hi⟩))))
        (fun u11 hu11 heff_u11 hnt_12 hcr_12 => ?_)
      have hu11_loc : u11.locals = u10.locals := by
        have hcf := (evaluate_store_control_frame u10
          (.op .add [.var .local (ofString "rec"), .const 0]) (.var .local (ofString "addr"))).2.1
        rwa [hu11] at hcf
      refine worldEff_seq hnt_12 hcr_12
        (fun _ _ => worldEff_store_word heff_u11 _ _
          (fun v hv => by simp [evalHOLExact, hu11_loc, hu10_keys] at hv; exact ⟨_, hv.symm⟩)
          (fun x hx _ => by
            simp [evalHOLExact, evalListHOLExact, hu11_loc, hu10_rec, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
            subst hx; exact Or.inr (Or.inr (Or.inr ⟨hrec8_lo, hrec8_hi⟩))))
        (fun u12 hu12 heff_u12 hnt_13 hcr_13 => ?_)
      have hu12_loc : u12.locals = u10.locals := by
        have hcf := (evaluate_store_control_frame u11
          (.op .add [.var .local (ofString "rec"), .const 8]) (.var .local (ofString "keys"))).2.1
        rw [hu12] at hcf; exact hcf.trans hu11_loc
      refine worldEff_seq hnt_13 hcr_13
        (fun _ _ => worldEff_store_word heff_u12 _ _
          (fun v hv => by simp [evalHOLExact, hu12_loc, hu10_slots] at hv; exact ⟨_, hv.symm⟩)
          (fun x hx _ => by
            simp [evalHOLExact, evalListHOLExact, hu12_loc, hu10_rec, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
            subst hx; exact Or.inr (Or.inr (Or.inr ⟨hrec16_lo, hrec16_hi⟩))))
        (fun u13 _ heff_u13 _ _ => worldEff_assign_local heff_u13 _ _)
  · exact ⟨(dalOuterBody_keeps_recs_lst_vvh t _ (Or.inl rfl) hf).trans ht_recs,
           (dalOuterBody_keeps_recs_lst_vvh t _ (Or.inr rfl) hf).trans ht_lst,
           wordLocals_flowing hws_dal ht_wloc (by rcases hf with h | h; exact Or.inl h; exact Or.inr (Or.inr h))⟩

private def dauLoopBody_vvh : ProgHOL 64 :=
  .decCall (ofString "it") (.comb [.one, .one, .one, .one]) (ofString "rlp_item")
    [.load .one (.op .add [.rfield 0 (.var .local (ofString "lst")), .panop .mul [.var .local (ofString "i"), .const 16]]),
     .load .one (.op .add [.rfield 0 (.var .local (ofString "lst")), .panop .mul [.var .local (ofString "i"), .const 16], .const 8])]
    (.seq
      (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "it"))) (.const 1))
        (.raise (ofString "TxErr") (.const 20))
        .skip)
      (.decCall (ofString "ent") (.comb [.one, .one]) (ofString "rlp_list_to_slices")
        [.rfield 1 (.var .local (ofString "it")), .rfield 2 (.var .local (ofString "it"))]
        (.seq
          (.ite (.cmp .notEqual (.rfield 1 (.var .local (ofString "ent"))) (.const 6))
            (.raise (ofString "TxErr") (.const 20))
            .skip)
          (.dec (ofString "a") .one
            (.op .add [.var .local (ofString "recs"), .panop .mul [.var .local (ofString "i"), .const 120]])
            (.decCall (ofString "cid") (.comb [.one, .one, .one, .one]) (ofString "tx_scalar_u256")
              [.rfield 0 (.var .local (ofString "ent")), .const 0, .const 32]
              (.seq
                (.store (.op .add [.var .local (ofString "a"), .const 0]) (.var .local (ofString "cid")))
                (.decCall (ofString "addr") .one (ofString "tx_fixed_bytes")
                  [.rfield 0 (.var .local (ofString "ent")), .const 1, .const 20]
                  (.seq
                    (.store (.op .add [.var .local (ofString "a"), .const 32]) (.var .local (ofString "addr")))
                    (.decCall (ofString "w") .one (ofString "tx_scalar_word")
                      [.rfield 0 (.var .local (ofString "ent")), .const 2, .const 8, .const 12]
                      (.seq
                        (.store (.op .add [.var .local (ofString "a"), .const 40]) (.var .local (ofString "w")))
                        (.seq
                          (.call (some (some (.local, ofString "w"), none)) (ofString "tx_scalar_word")
                            [.rfield 0 (.var .local (ofString "ent")), .const 3, .const 1, .const 12])
                          (.seq
                            (.store (.op .add [.var .local (ofString "a"), .const 48]) (.var .local (ofString "w")))
                            (.decCall (ofString "r") (.comb [.one, .one, .one, .one]) (ofString "tx_scalar_u256")
                              [.rfield 0 (.var .local (ofString "ent")), .const 4, .const 32]
                              (.seq
                                (.store (.op .add [.var .local (ofString "a"), .const 56]) (.var .local (ofString "r")))
                                (.decCall (ofString "s") (.comb [.one, .one, .one, .one]) (ofString "tx_scalar_u256")
                                  [.rfield 0 (.var .local (ofString "ent")), .const 5, .const 32]
                                  (.seq
                                    (.store (.op .add [.var .local (ofString "a"), .const 88]) (.var .local (ofString "s")))
                                    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))))))))))))))))

private theorem dauLoopBody_keeps_recs_lst_vvh {F : Type}
    (t : PanSemStateFiniteExact 64 F) (key : MlS)
    (hk_recs_lst : key = ofString "recs" ∨ key = ofString "lst")
    (hf : (evaluateHOLFiniteState t dauLoopBody_vvh).1 = none ∨
      (evaluateHOLFiniteState t dauLoopBody_vvh).1 = some .continue) :
    (evaluateHOLFiniteState t dauLoopBody_vvh).2.locals.lookup key = t.locals.lookup key := by
  have hk_it : key ≠ ofString "it" := by rcases hk_recs_lst with rfl | rfl <;> decide
  have hk_ent : key ≠ ofString "ent" := by rcases hk_recs_lst with rfl | rfl <;> decide
  have hk_a : key ≠ ofString "a" := by rcases hk_recs_lst with rfl | rfl <;> decide
  have hk_cid : key ≠ ofString "cid" := by rcases hk_recs_lst with rfl | rfl <;> decide
  have hk_addr : key ≠ ofString "addr" := by rcases hk_recs_lst with rfl | rfl <;> decide
  have hk_w : key ≠ ofString "w" := by rcases hk_recs_lst with rfl | rfl <;> decide
  have hk_r : key ≠ ofString "r" := by rcases hk_recs_lst with rfl | rfl <;> decide
  have hk_s : key ≠ ofString "s" := by rcases hk_recs_lst with rfl | rfl <;> decide
  have hk_i : key ≠ ofString "i" := by rcases hk_recs_lst with rfl | rfl <;> decide
  refine eval_decCall_flowing_keeps t _ _ _ _ _ key hk_it (fun u1 hf1 => ?_) hf
  obtain ⟨hf2, heq2⟩ := eval_guard_raise_flowing_inv u1 _ _ _ hf1
  rw [heq2]
  refine eval_decCall_flowing_keeps u1 _ _ _ _ _ key hk_ent (fun u3 hf3 => ?_) hf2
  obtain ⟨hf4, heq4⟩ := eval_guard_raise_flowing_inv u3 _ _ _ hf3
  rw [heq4]
  refine eval_dec_flowing_keeps u3 _ _ _ _ key hk_a (fun u5 hf5 => ?_) hf4
  refine eval_decCall_flowing_keeps u5 _ _ _ _ _ key hk_cid (fun u6 hf6 => ?_) hf5
  obtain ⟨u7, _, hu7_loc, hf7, heq7⟩ := eval_store_flowing_inv_vvh u6 _ _ hf6
  rw [heq7]
  refine (eval_decCall_flowing_keeps u7 _ _ _ _ _ key hk_addr (fun u8 hf8 => ?_) hf7).trans (by rw [hu7_loc])
  obtain ⟨u9, _, hu9_loc, hf9, heq9⟩ := eval_store_flowing_inv_vvh u8 _ _ hf8
  rw [heq9]
  refine (eval_decCall_flowing_keeps u9 _ _ _ _ _ key hk_w (fun u10 hf10 => ?_) hf9).trans (by rw [hu9_loc])
  obtain ⟨u11, _, hu11_loc, hf11, heq11⟩ := eval_store_flowing_inv_vvh u10 _ _ hf10
  rw [heq11]
  obtain ⟨u12, _, hu12_k, hf12, heq12⟩ := eval_call_local_flowing_keeps u11 _ _ _ key hk_w hf11
  rw [heq12]
  obtain ⟨u13, _, hu13_loc, hf13, heq13⟩ := eval_store_flowing_inv_vvh u12 _ _ hf12
  rw [heq13]
  refine (eval_decCall_flowing_keeps u13 _ _ _ _ _ key hk_r (fun u14 hf14 => ?_) hf13).trans
    (by rw [hu13_loc, hu12_k, hu11_loc])
  obtain ⟨u15, _, hu15_loc, hf15, heq15⟩ := eval_store_flowing_inv_vvh u14 _ _ hf14
  rw [heq15]
  refine (eval_decCall_flowing_keeps u15 _ _ _ _ _ key hk_s (fun u16 hf16 => ?_) hf15).trans (by rw [hu15_loc])
  obtain ⟨u17, _, hu17_loc, hf17, heq17⟩ := eval_store_flowing_inv_vvh u16 _ _ hf16
  rw [heq17]
  exact (eval_assign_flowing_keeps_vvh u17 _ _ key hk_i hf17).trans (by rw [hu17_loc])

private theorem worldEff_decode_authorizations_vvh {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "decode_authorizations") vals =
      some (sourceFnBody Guest.Software.guestFn_decode_authorizations, s.locals, .comb [.one, .one]))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_authorizations)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_authorizations)).1) :
    WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_authorizations)).2
      [] [] wsGw := by
  have _ := hl
  have heff0 : WorldEff s s [] [] wsGw := WorldEff.refl s [] [] wsGw hAR hc
  have hbody : sourceFnBody Guest.Software.guestFn_decode_authorizations =
      .decCall (ofString "lst") (.comb [.one, .one]) (ofString "rlp_list_to_slices")
        [.var .local (ofString "p"), .var .local (ofString "len")]
        (.decCall (ofString "recs") .one (ofString "alloc")
          [.panop .mul [.rfield 1 (.var .local (ofString "lst")), .const 120]]
          (.dec (ofString "i") .one (.const 0)
            (.seq
              (.while (.cmp .lower (.var .local (ofString "i")) (.rfield 1 (.var .local (ofString "lst"))))
                dauLoopBody_vvh)
              (.return (.rstruct [.var .local (ofString "recs"), .rfield 1 (.var .local (ofString "lst"))]))))) := rfl
  rw [hbody] at hnt hres ⊢
  refine worldEff_decCall_eff heff0 (ofString "lst") (.comb [.one, .one]) (ofString "rlp_list_to_slices")
    _ _ _ _ lookup_rlp_list_to_slices_vvh
    (fun callee cvals _ hlc hnt_cb hres_cb =>
      heff0.trans_noBuf
        (WorldEff.from_locals_clock
          (worldEff_rlp_list_to_slices_vvh (callEntryStateHOLFinite s callee) cvals
            heff0.code (localsFree_arenaReady s callee _ heff0.arena)
            (by simpa [heff0.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
        ws_nil_sub_vvh ws_no_gb_vvh)
    (fun callee cvals rv cpost _ hlc hrun_c _ heff_cp hnt_k1 hcr_k1 => ?_)
    hnt (Or.inr (Or.inr (Or.inr hres)))
  obtain ⟨warr, wcnt, rfl, hcnt_dom⟩ :=
    rlp_list_to_slices_ret_bound_vvh (callEntryStateHOLFinite s callee) cpost cvals rv
      heff0.code (guestInv_callEntry s callee heff0.arena.1)
      (by simpa [heff0.code, callEntryStateHOLFinite] using hlc) hrun_c
  let m1 := setVarHOLFinite (ofString "lst") (.rStruct [.val (.word warr), .val (.word wcnt)])
    { cpost with locals := s.locals }
  have heff_m1 : WorldEff s m1 [] [] wsGw := heff_cp.locals_clock _ _
  have hm1_lst : m1.locals.lookup (ofString "lst") =
      some (.rStruct [.val (.word warr), .val (.word wcnt)]) := by
    simp [m1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  refine worldEff_decCall_alloc heff_m1 (by decide) (ofString "recs") _ hnt_k1 hcr_k1
    (fun precs nw m2 hsz_ev _ hm2_loc _ heff_m2 _ _ hprecs_lo_s hprecs_add hhp_m2_hi _ hnt_k2 hcr_k2 => ?_)
  have hnw_eq : nw = wcnt * 120#64 := by
    simp [evalHOLExact, evalListHOLExact, hm1_lst, panOpHOL, valueIsWord, valueWord] at hsz_ev
    exact hsz_ev.symm
  subst hnw_eq
  have halloc_hi : precs.toNat + ((wcnt * 120#64).toNat + 7) / 8 * 8 ≤ heapLimit := by omega
  refine worldEff_dec heff_m2 _ _ _ hnt_k2 hcr_k2 (fun vi hvi _ hnt_k3 hcr_k3 => ?_)
  have hvi_eq : vi = .val (.word 0) := by simp [evalHOLExact] at hvi; exact hvi.symm
  subst hvi_eq
  let m3 := setVarHOLFinite (ofString "i") (.val (.word 0)) m2
  have heff_m3 : WorldEff s m3 [] [] wsGw := heff_m2.locals_clock _ _
  let DauInv := fun (t : PanSemStateFiniteExact 64 F) =>
    t.locals.lookup (ofString "recs") = some (.val (.word precs)) ∧
    t.locals.lookup (ofString "lst") = some (.rStruct [.val (.word warr), .val (.word wcnt)]) ∧
    WordLocals ["i"] t
  have hinv_m3 : DauInv m3 := by
    refine ⟨?_, ?_, ?_⟩
    · simp [m3, setVarHOLFinite, hm2_loc, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "i" ≠ ofString "recs" by decide]
    · simp [m3, setVarHOLFinite, hm2_loc, hm1_lst, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "i" ≠ ofString "lst" by decide, show ofString "recs" ≠ ofString "lst" by decide]
    · intro nm hnm; simp at hnm; subst hnm
      exact ⟨0, by simp [m3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
  have hws_dau : wsafe dauLoopBody_vvh = true := by decide
  refine worldEff_seq hnt_k3 hcr_k3
    (fun hnt_w hcr_w =>
      worldEff_while_cond_vvh _ DauInv (fun _ hinv => hinv)
        (fun t0 cw hcond hnz heff_t hinv_t hnt_b hcr_b => ?_)
        m3.clock m3 rfl heff_m3 hinv_m3 hnt_w hcr_w)
    (fun mid _ heff_mid _ _ => worldEff_return heff_mid _)
  set t := decClockHOLFinite t0
  obtain ⟨ht_recs, ht_lst, ht_wloc⟩ := hinv_t
  obtain ⟨wi_t, hti⟩ := ht_wloc "i" (by simp)
  have ht0_i : t0.locals.lookup (ofString "i") = some (.val (.word wi_t)) := hti
  have ht0_lst : t0.locals.lookup (ofString "lst") =
      some (.rStruct [.val (.word warr), .val (.word wcnt)]) := ht_lst
  have hlt_i : wi_t < wcnt := by
    rw [evalHOLFinite_eq_toExact] at hcond
    simp [evalHOLExact, ht0_i, ht0_lst, Compiler.Encoders.Asm.wordCmpHOL] at hcond
    by_contra hge; simp [hge] at hcond; exact hnz hcond.symm
  obtain ⟨ha0_lo, ha0_hi⟩ :=
    heap_slice_stride_in_heap_vvh precs wcnt wi_t 120 0 32 hcnt_dom (by decide) (by decide) (by decide)
      hprecs_lo_s halloc_hi hlt_i
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at ha0_lo ha0_hi
  obtain ⟨ha32_lo, ha32_hi⟩ :=
    heap_slice_stride_in_heap_vvh precs wcnt wi_t 120 32 8 hcnt_dom (by decide) (by decide) (by decide)
      hprecs_lo_s halloc_hi hlt_i
  obtain ⟨ha40_lo, ha40_hi⟩ :=
    heap_slice_stride_in_heap_vvh precs wcnt wi_t 120 40 8 hcnt_dom (by decide) (by decide) (by decide)
      hprecs_lo_s halloc_hi hlt_i
  obtain ⟨ha48_lo, ha48_hi⟩ :=
    heap_slice_stride_in_heap_vvh precs wcnt wi_t 120 48 8 hcnt_dom (by decide) (by decide) (by decide)
      hprecs_lo_s halloc_hi hlt_i
  obtain ⟨ha56_lo, ha56_hi⟩ :=
    heap_slice_stride_in_heap_vvh precs wcnt wi_t 120 56 32 hcnt_dom (by decide) (by decide) (by decide)
      hprecs_lo_s halloc_hi hlt_i
  obtain ⟨ha88_lo, ha88_hi⟩ :=
    heap_slice_stride_in_heap_vvh precs wcnt wi_t 120 88 32 hcnt_dom (by decide) (by decide) (by decide)
      hprecs_lo_s halloc_hi hlt_i
  refine ⟨?_, fun hf => ?_⟩
  · dsimp only [dauLoopBody_vvh] at hnt_b hcr_b ⊢
    refine worldEff_decCall_eff heff_t (ofString "it") (.comb [.one, .one, .one, .one]) (ofString "rlp_item")
      _ _ _ _ lookup_rlp_item_vvh
      (fun callee cvals _ hlc hnt_cb hres_cb =>
        heff_t.trans_noBuf
          (WorldEff.from_locals_clock
            (worldEff_rlp_item_vvh (callEntryStateHOLFinite t callee) cvals
              heff_t.code (localsFree_arenaReady t callee _ heff_t.arena)
              (by simpa [heff_t.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
          ws_nil_sub_vvh ws_no_gb_vvh)
      (fun _ _ rvit cpost1 _ _ _ _ heff_cp1 hnt_1 hcr_1 => ?_)
      hnt_b hcr_b
    let u1 := setVarHOLFinite (ofString "it") rvit { cpost1 with locals := t.locals }
    have heff_u1 : WorldEff s u1 [] [] wsGw := heff_cp1.locals_clock _ _
    have hu1_recs : u1.locals.lookup (ofString "recs") = some (.val (.word precs)) := by
      simp [u1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht_recs,
        show ofString "it" ≠ ofString "recs" by decide]
    have hu1_i : u1.locals.lookup (ofString "i") = some (.val (.word wi_t)) := by
      simp [u1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hti,
        show ofString "it" ≠ ofString "i" by decide]
    refine worldEff_seq hnt_1 hcr_1
      (fun hnt_g1 hcr_g1 =>
        worldEff_ite heff_u1 _ hnt_g1 hcr_g1
          (fun _ _ _ _ _ => worldEff_raise heff_u1 _ _)
          (fun _ _ _ => worldEff_skip heff_u1))
      (fun u2 hu2 heff_u2 hnt_2 hcr_2 => ?_)
    have hu2_eq : u2 = u1 := by
      rw [evaluateHOLFiniteState_ite] at hu2
      split at hu2
      · split at hu2
        · rw [evaluateHOLFiniteState_skip] at hu2; injection hu2 with _ hm; exact hm.symm
        · rw [evaluateHOLFiniteState_raise] at hu2
          split at hu2 <;> [ (dsimp only at hu2; split at hu2 <;> cases hu2); cases hu2 ]
      · cases hu2
    subst hu2_eq
    refine worldEff_decCall_eff heff_u1 (ofString "ent") (.comb [.one, .one]) (ofString "rlp_list_to_slices")
      _ _ _ _ lookup_rlp_list_to_slices_vvh
      (fun callee cvals _ hlc hnt_cb hres_cb =>
        heff_u1.trans_noBuf
          (WorldEff.from_locals_clock
            (worldEff_rlp_list_to_slices_vvh (callEntryStateHOLFinite u1 callee) cvals
              heff_u1.code (localsFree_arenaReady u1 callee _ heff_u1.arena)
              (by simpa [heff_u1.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
          ws_nil_sub_vvh ws_no_gb_vvh)
      (fun _ _ rvent cpost2 _ _ _ _ heff_cp2 hnt_3 hcr_3 => ?_)
      hnt_2 hcr_2
    let u3 := setVarHOLFinite (ofString "ent") rvent { cpost2 with locals := u1.locals }
    have heff_u3 : WorldEff s u3 [] [] wsGw := heff_cp2.locals_clock _ _
    have hu3_recs : u3.locals.lookup (ofString "recs") = some (.val (.word precs)) := by
      simp [u3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu1_recs,
        show ofString "ent" ≠ ofString "recs" by decide]
    have hu3_i : u3.locals.lookup (ofString "i") = some (.val (.word wi_t)) := by
      simp [u3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu1_i,
        show ofString "ent" ≠ ofString "i" by decide]
    refine worldEff_seq hnt_3 hcr_3
      (fun hnt_g2 hcr_g2 =>
        worldEff_ite heff_u3 _ hnt_g2 hcr_g2
          (fun _ _ _ _ _ => worldEff_raise heff_u3 _ _)
          (fun _ _ _ => worldEff_skip heff_u3))
      (fun u4 hu4 heff_u4 hnt_4 hcr_4 => ?_)
    have hu4_eq : u4 = u3 := by
      rw [evaluateHOLFiniteState_ite] at hu4
      split at hu4
      · split at hu4
        · rw [evaluateHOLFiniteState_skip] at hu4; injection hu4 with _ hm; exact hm.symm
        · rw [evaluateHOLFiniteState_raise] at hu4
          split at hu4 <;> [ (dsimp only at hu4; split at hu4 <;> cases hu4); cases hu4 ]
      · cases hu4
    subst hu4_eq
    refine worldEff_dec heff_u3 _ _ _ hnt_4 hcr_4 (fun va hva _ hnt_5 hcr_5 => ?_)
    have hva_eq : va = .val (.word (precs + wi_t * 120#64)) := by
      simp [evalHOLExact, evalListHOLExact, hu3_recs, hu3_i,
        panOpHOL, wordOpHOL, wordOp, valueIsWord, valueWord] at hva
      exact hva.symm
    subst hva_eq
    let u5 := setVarHOLFinite (ofString "a") (.val (.word (precs + wi_t * 120#64))) u3
    have heff_u5 : WorldEff s u5 [] [] wsGw := heff_u3.locals_clock _ _
    have hu5_a : u5.locals.lookup (ofString "a") =
        some (.val (.word (precs + wi_t * 120#64))) := by
      simp [u5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    refine worldEff_decCall_eff heff_u5 (ofString "cid") (.comb [.one, .one, .one, .one]) (ofString "tx_scalar_u256")
      _ _ _ _ lookup_tx_scalar_u256_vvh
      (fun callee cvals _ hlc hnt_cb hres_cb =>
        heff_u5.trans_noBuf
          (WorldEff.from_locals_clock
            (worldEff_tx_scalar_u256_vvh (callEntryStateHOLFinite u5 callee) cvals
              heff_u5.code (localsFree_arenaReady u5 callee _ heff_u5.arena)
              (by simpa [heff_u5.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
          ws_nil_sub_vvh ws_no_gb_vvh)
      (fun _ _ rvcid cpost3 _ _ _ hsh_cid heff_cp3 hnt_6 hcr_6 => ?_)
      hnt_5 hcr_5
    let u6 := setVarHOLFinite (ofString "cid") rvcid { cpost3 with locals := u5.locals }
    have heff_u6 : WorldEff s u6 [] [] wsGw := heff_cp3.locals_clock _ _
    have hu6_a : u6.locals.lookup (ofString "a") =
        some (.val (.word (precs + wi_t * 120#64))) := by
      simp [u6, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu5_a,
        show ofString "cid" ≠ ofString "a" by decide]
    have hu6_cid : u6.locals.lookup (ofString "cid") = some rvcid := by
      simp [u6, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    refine worldEff_seq hnt_6 hcr_6
      (fun _ _ => worldEff_store_heap_bounded heff_u6 _ _ 32
        (fun v hv => by
          simp [evalHOLExact, hu6_cid] at hv; subst hv
          exact flattenHOL_len_four rvcid hsh_cid)
        (fun x hx => by
          simp [evalHOLExact, evalListHOLExact, hu6_a, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
          subst hx; exact ⟨ha0_lo, ha0_hi⟩))
      (fun u7 hu7 heff_u7 hnt_7 hcr_7 => ?_)
    have hu7_loc : u7.locals = u6.locals := by
      have hcf := (evaluate_store_control_frame u6
        (.op .add [.var .local (ofString "a"), .const 0])
        (.var .local (ofString "cid"))).2.1
      rwa [hu7] at hcf
    refine worldEff_decCall_eff heff_u7 (ofString "addr") .one (ofString "tx_fixed_bytes")
      _ _ _ _ lookup_tx_fixed_bytes_vvh
      (fun callee cvals _ hlc hnt_cb hres_cb =>
        heff_u7.trans_noBuf
          (WorldEff.from_locals_clock
            (worldEff_tx_fixed_bytes_vvh (callEntryStateHOLFinite u7 callee) cvals
              heff_u7.code (localsFree_arenaReady u7 callee _ heff_u7.arena)
              (by simpa [heff_u7.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
          ws_nil_sub_vvh ws_no_gb_vvh)
      (fun _ _ rvaddr cpost4 _ _ _ hsh_addr heff_cp4 hnt_8 hcr_8 => ?_)
      hnt_7 hcr_7
    let u8 := setVarHOLFinite (ofString "addr") rvaddr { cpost4 with locals := u7.locals }
    have heff_u8 : WorldEff s u8 [] [] wsGw := heff_cp4.locals_clock _ _
    have hu8_a : u8.locals.lookup (ofString "a") =
        some (.val (.word (precs + wi_t * 120#64))) := by
      simp [u8, setVarHOLFinite, hu7_loc, hu6_a, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "addr" ≠ ofString "a" by decide]
    have hu8_addr : u8.locals.lookup (ofString "addr") = some rvaddr := by
      simp [u8, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    refine worldEff_seq hnt_8 hcr_8
      (fun _ _ => worldEff_store_heap_bounded heff_u8 _ _ 8
        (fun v hv => by
          simp [evalHOLExact, hu8_addr] at hv; subst hv
          exact flattenHOL_len_one rvaddr hsh_addr)
        (fun x hx => by
          simp [evalHOLExact, evalListHOLExact, hu8_a, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
          subst hx; exact ⟨ha32_lo, ha32_hi⟩))
      (fun u9 hu9 heff_u9 hnt_9 hcr_9 => ?_)
    have hu9_loc : u9.locals = u8.locals := by
      have hcf := (evaluate_store_control_frame u8
        (.op .add [.var .local (ofString "a"), .const 32])
        (.var .local (ofString "addr"))).2.1
      rwa [hu9] at hcf
    refine worldEff_decCall_eff heff_u9 (ofString "w") .one (ofString "tx_scalar_word")
      _ _ _ _ lookup_tx_scalar_word_vvh
      (fun callee cvals _ hlc hnt_cb hres_cb =>
        heff_u9.trans_noBuf
          (WorldEff.from_locals_clock
            (worldEff_tx_scalar_word_vvh (callEntryStateHOLFinite u9 callee) cvals
              heff_u9.code (localsFree_arenaReady u9 callee _ heff_u9.arena)
              (by simpa [heff_u9.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
          ws_nil_sub_vvh ws_no_gb_vvh)
      (fun _ _ rvw cpost5 _ _ _ hsh_w heff_cp5 hnt_10 hcr_10 => ?_)
      hnt_9 hcr_9
    let u10 := setVarHOLFinite (ofString "w") rvw { cpost5 with locals := u9.locals }
    have heff_u10 : WorldEff s u10 [] [] wsGw := heff_cp5.locals_clock _ _
    have hu10_a : u10.locals.lookup (ofString "a") =
        some (.val (.word (precs + wi_t * 120#64))) := by
      simp [u10, setVarHOLFinite, hu9_loc, hu8_a, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "w" ≠ ofString "a" by decide]
    have hu10_w : u10.locals.lookup (ofString "w") = some rvw := by
      simp [u10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    refine worldEff_seq hnt_10 hcr_10
      (fun _ _ => worldEff_store_heap_bounded heff_u10 _ _ 8
        (fun v hv => by
          simp [evalHOLExact, hu10_w] at hv; subst hv
          exact flattenHOL_len_one rvw hsh_w)
        (fun x hx => by
          simp [evalHOLExact, evalListHOLExact, hu10_a, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
          subst hx; exact ⟨ha40_lo, ha40_hi⟩))
      (fun u11 hu11 heff_u11 hnt_11 hcr_11 => ?_)
    have hu11_loc : u11.locals = u10.locals := by
      have hcf := (evaluate_store_control_frame u10
        (.op .add [.var .local (ofString "a"), .const 40])
        (.var .local (ofString "w"))).2.1
      rwa [hu11] at hcf
    refine worldEff_seq hnt_11 hcr_11
      (fun hnt_c1 hcr_c1 =>
        worldEff_call_local_eff heff_u11 (ofString "w") (ofString "tx_scalar_word") _
          _ _ _ lookup_tx_scalar_word_vvh
          (fun callee cvals _ hlc hnt_cb hres_cb =>
            heff_u11.trans_noBuf
              (WorldEff.from_locals_clock
                (worldEff_tx_scalar_word_vvh (callEntryStateHOLFinite u11 callee) cvals
                  heff_u11.code (localsFree_arenaReady u11 callee _ heff_u11.arena)
                  (by simpa [heff_u11.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
              ws_nil_sub_vvh ws_no_gb_vvh)
          hnt_c1 hcr_c1)
      (fun u12 hu12 heff_u12 hnt_12 hcr_12 => ?_)
    obtain ⟨hu12_other, rvw2, hu12_w, hu12_wsh⟩ := call_local_none_keeps u11 u12 _ _ _ hu12
    have hu12_a : u12.locals.lookup (ofString "a") =
        some (.val (.word (precs + wi_t * 120#64))) := by
      rw [hu12_other _ (by decide), hu11_loc]; exact hu10_a
    have hsh_w2 : shapeEqHOL (shapeOfHOLExact rvw2) .one = true := by
      have h1 := hu12_wsh rvw (by rw [hu11_loc]; exact hu10_w)
      rcases rvw with ⟨⟨_⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh_w
      simpa [shapeOfHOLExact] using h1
    refine worldEff_seq hnt_12 hcr_12
      (fun _ _ => worldEff_store_heap_bounded heff_u12 _ _ 8
        (fun v hv => by
          simp [evalHOLExact, hu12_w] at hv; subst hv
          exact flattenHOL_len_one rvw2 hsh_w2)
        (fun x hx => by
          simp [evalHOLExact, evalListHOLExact, hu12_a, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
          subst hx; exact ⟨ha48_lo, ha48_hi⟩))
      (fun u13 hu13 heff_u13 hnt_13 hcr_13 => ?_)
    have hu13_loc : u13.locals = u12.locals := by
      have hcf := (evaluate_store_control_frame u12
        (.op .add [.var .local (ofString "a"), .const 48])
        (.var .local (ofString "w"))).2.1
      rwa [hu13] at hcf
    refine worldEff_decCall_eff heff_u13 (ofString "r") (.comb [.one, .one, .one, .one]) (ofString "tx_scalar_u256")
      _ _ _ _ lookup_tx_scalar_u256_vvh
      (fun callee cvals _ hlc hnt_cb hres_cb =>
        heff_u13.trans_noBuf
          (WorldEff.from_locals_clock
            (worldEff_tx_scalar_u256_vvh (callEntryStateHOLFinite u13 callee) cvals
              heff_u13.code (localsFree_arenaReady u13 callee _ heff_u13.arena)
              (by simpa [heff_u13.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
          ws_nil_sub_vvh ws_no_gb_vvh)
      (fun _ _ rvr cpost6 _ _ _ hsh_r heff_cp6 hnt_14 hcr_14 => ?_)
      hnt_13 hcr_13
    let u14 := setVarHOLFinite (ofString "r") rvr { cpost6 with locals := u13.locals }
    have heff_u14 : WorldEff s u14 [] [] wsGw := heff_cp6.locals_clock _ _
    have hu14_a : u14.locals.lookup (ofString "a") =
        some (.val (.word (precs + wi_t * 120#64))) := by
      simp [u14, setVarHOLFinite, hu13_loc, hu12_a, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "r" ≠ ofString "a" by decide]
    have hu14_r : u14.locals.lookup (ofString "r") = some rvr := by
      simp [u14, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    refine worldEff_seq hnt_14 hcr_14
      (fun _ _ => worldEff_store_heap_bounded heff_u14 _ _ 32
        (fun v hv => by
          simp [evalHOLExact, hu14_r] at hv; subst hv
          exact flattenHOL_len_four rvr hsh_r)
        (fun x hx => by
          simp [evalHOLExact, evalListHOLExact, hu14_a, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
          subst hx; exact ⟨ha56_lo, ha56_hi⟩))
      (fun u15 hu15 heff_u15 hnt_15 hcr_15 => ?_)
    have hu15_loc : u15.locals = u14.locals := by
      have hcf := (evaluate_store_control_frame u14
        (.op .add [.var .local (ofString "a"), .const 56])
        (.var .local (ofString "r"))).2.1
      rwa [hu15] at hcf
    refine worldEff_decCall_eff heff_u15 (ofString "s") (.comb [.one, .one, .one, .one]) (ofString "tx_scalar_u256")
      _ _ _ _ lookup_tx_scalar_u256_vvh
      (fun callee cvals _ hlc hnt_cb hres_cb =>
        heff_u15.trans_noBuf
          (WorldEff.from_locals_clock
            (worldEff_tx_scalar_u256_vvh (callEntryStateHOLFinite u15 callee) cvals
              heff_u15.code (localsFree_arenaReady u15 callee _ heff_u15.arena)
              (by simpa [heff_u15.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
          ws_nil_sub_vvh ws_no_gb_vvh)
      (fun _ _ rvs cpost7 _ _ _ hsh_s heff_cp7 hnt_16 hcr_16 => ?_)
      hnt_15 hcr_15
    let u16 := setVarHOLFinite (ofString "s") rvs { cpost7 with locals := u15.locals }
    have heff_u16 : WorldEff s u16 [] [] wsGw := heff_cp7.locals_clock _ _
    have hu16_a : u16.locals.lookup (ofString "a") =
        some (.val (.word (precs + wi_t * 120#64))) := by
      simp [u16, setVarHOLFinite, hu15_loc, hu14_a, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "s" ≠ ofString "a" by decide]
    have hu16_s : u16.locals.lookup (ofString "s") = some rvs := by
      simp [u16, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    refine worldEff_seq hnt_16 hcr_16
      (fun _ _ => worldEff_store_heap_bounded heff_u16 _ _ 32
        (fun v hv => by
          simp [evalHOLExact, hu16_s] at hv; subst hv
          exact flattenHOL_len_four rvs hsh_s)
        (fun x hx => by
          simp [evalHOLExact, evalListHOLExact, hu16_a, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
          subst hx; exact ⟨ha88_lo, ha88_hi⟩))
      (fun u17 _ heff_u17 _ _ => worldEff_assign_local heff_u17 _ _)
  · exact ⟨(dauLoopBody_keeps_recs_lst_vvh t _ (Or.inl rfl) hf).trans ht_recs,
           (dauLoopBody_keeps_recs_lst_vvh t _ (Or.inr rfl) hf).trans ht_lst,
           wordLocals_flowing hws_dau ht_wloc (by rcases hf with h | h; exact Or.inl h; exact Or.inr (Or.inr h))⟩

private def dtxInv_vvh {F : Type} (ptx : BitVec 64) (u : PanSemStateFiniteExact 64 F) : Prop :=
  u.locals.lookup (ofString "tx") = some (.val (.word ptx)) ∧
  (∃ rvt, u.locals.lookup (ofString "top") = some rvt ∧
    shapeEqHOL (shapeOfHOLExact rvt) (.comb [.one, .one, .one, .one]) = true) ∧
  (∃ wt, u.locals.lookup (ofString "t") = some (.val (.word wt))) ∧
  (∃ wnf, u.locals.lookup (ofString "nfields") = some (.val (.word wnf)))

private theorem dtxInv_set_t_vvh {F : Type} {ptx : BitVec 64} {u m : PanSemStateFiniteExact 64 F}
    (h : dtxInv_vvh ptx u) (nm : MlS) (e : ExpHOL 64) (hnm : nm = ofString "t" ∨ nm = ofString "nfields")
    (hrun : evaluateHOLFiniteState u (.assign .local nm e) = (none, m)) :
    dtxInv_vvh ptx m := by
  obtain ⟨hother, rv, hnm_m, hsh⟩ := assign_local_none_keeps u m nm e hrun
  obtain ⟨htx, ⟨rvt, htop, htop_sh⟩, ⟨wt, ht⟩, ⟨wnf, hnf⟩⟩ := h
  rcases hnm with rfl | rfl
  · have hsh1 : shapeEqHOL (shapeOfHOLExact rv) .one = true := by
      simpa [shapeOfHOLExact] using hsh (.val (.word wt)) ht
    rcases rv with ⟨⟨w'⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh1
    exact ⟨(hother _ (by decide)).trans htx,
           ⟨rvt, (hother _ (by decide)).trans htop, htop_sh⟩,
           ⟨w', hnm_m⟩,
           ⟨wnf, (hother _ (by decide)).trans hnf⟩⟩
  · have hsh1 : shapeEqHOL (shapeOfHOLExact rv) .one = true := by
      simpa [shapeOfHOLExact] using hsh (.val (.word wnf)) hnf
    rcases rv with ⟨⟨w'⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh1
    exact ⟨(hother _ (by decide)).trans htx,
           ⟨rvt, (hother _ (by decide)).trans htop, htop_sh⟩,
           ⟨wt, (hother _ (by decide)).trans ht⟩,
           ⟨w', hnm_m⟩⟩

private theorem dtxInv_set_top_vvh {F : Type} {ptx : BitVec 64} {u m : PanSemStateFiniteExact 64 F}
    (h : dtxInv_vvh ptx u) (fn : MlS) (args : List (ExpHOL 64))
    (hrun : evaluateHOLFiniteState u (.call (some (some (.local, ofString "top"), none)) fn args) = (none, m)) :
    dtxInv_vvh ptx m := by
  obtain ⟨hother, rv, hnm_m, hsh⟩ := call_local_none_keeps u m (ofString "top") fn args hrun
  obtain ⟨htx, ⟨rvt, htop, htop_sh⟩, ⟨wt, ht⟩, ⟨wnf, hnf⟩⟩ := h
  have hsh4 : shapeEqHOL (shapeOfHOLExact rv) (.comb [.one, .one, .one, .one]) = true := by
    have h1 := hsh rvt htop
    rcases rvt with _ | rs | _ <;> simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at htop_sh
    rcases rs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩⟩ <;>
      simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at htop_sh
    rcases v0 with ⟨⟨_⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at htop_sh
    rcases v1 with ⟨⟨_⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at htop_sh
    rcases v2 with ⟨⟨_⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at htop_sh
    rcases v3 with ⟨⟨_⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at htop_sh
    simpa [shapeOfHOLExact] using h1
  exact ⟨(hother _ (by decide)).trans htx,
         ⟨rv, hnm_m, hsh4⟩,
         ⟨wt, (hother _ (by decide)).trans ht⟩,
         ⟨wnf, (hother _ (by decide)).trans hnf⟩⟩

private def dtxInv2_vvh {F : Type} (ptx : BitVec 64) (u : PanSemStateFiniteExact 64 F) : Prop :=
  u.locals.lookup (ofString "tx") = some (.val (.word ptx)) ∧
  (∃ wk, u.locals.lookup (ofString "k") = some (.val (.word wk))) ∧
  (∃ ww, u.locals.lookup (ofString "w") = some (.val (.word ww))) ∧
  (∃ rvv, u.locals.lookup (ofString "v") = some rvv ∧
    shapeEqHOL (shapeOfHOLExact rvv) (.comb [.one, .one, .one, .one]) = true)

private theorem shapeEq_quad_trans_vvh (rv rvv : ValueHOL 64)
    (h1 : shapeEqHOL (shapeOfHOLExact rv) (shapeOfHOLExact rvv) = true)
    (h2 : shapeEqHOL (shapeOfHOLExact rvv) (.comb [.one, .one, .one, .one]) = true) :
    shapeEqHOL (shapeOfHOLExact rv) (.comb [.one, .one, .one, .one]) = true := by
  rcases rvv with _ | rs | _ <;> simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h2
  rcases rs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩⟩ <;>
    simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h2
  rcases v0 with ⟨⟨_⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at h2
  rcases v1 with ⟨⟨_⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at h2
  rcases v2 with ⟨⟨_⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at h2
  rcases v3 with ⟨⟨_⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at h2
  simpa [shapeOfHOLExact] using h1

private theorem dtxInv2_assign_k_vvh {F : Type} {ptx : BitVec 64} {u m : PanSemStateFiniteExact 64 F}
    (h : dtxInv2_vvh ptx u) (e : ExpHOL 64)
    (hrun : evaluateHOLFiniteState u (.assign .local (ofString "k") e) = (none, m)) :
    dtxInv2_vvh ptx m := by
  obtain ⟨hother, rv, hnm_m, hsh⟩ := assign_local_none_keeps u m (ofString "k") e hrun
  obtain ⟨htx, ⟨wk, hk⟩, ⟨ww, hw⟩, ⟨rvv, hv, hv_sh⟩⟩ := h
  have hsh1 : shapeEqHOL (shapeOfHOLExact rv) .one = true := by
    simpa [shapeOfHOLExact] using hsh (.val (.word wk)) hk
  rcases rv with ⟨⟨w'⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh1
  exact ⟨(hother _ (by decide)).trans htx, ⟨w', hnm_m⟩,
         ⟨ww, (hother _ (by decide)).trans hw⟩,
         ⟨rvv, (hother _ (by decide)).trans hv, hv_sh⟩⟩

private theorem dtxInv2_assign_v_vvh {F : Type} {ptx : BitVec 64} {u m : PanSemStateFiniteExact 64 F}
    (h : dtxInv2_vvh ptx u) (e : ExpHOL 64)
    (hrun : evaluateHOLFiniteState u (.assign .local (ofString "v") e) = (none, m)) :
    dtxInv2_vvh ptx m := by
  obtain ⟨hother, rv, hnm_m, hsh⟩ := assign_local_none_keeps u m (ofString "v") e hrun
  obtain ⟨htx, ⟨wk, hk⟩, ⟨ww, hw⟩, ⟨rvv, hv, hv_sh⟩⟩ := h
  exact ⟨(hother _ (by decide)).trans htx,
         ⟨wk, (hother _ (by decide)).trans hk⟩,
         ⟨ww, (hother _ (by decide)).trans hw⟩,
         ⟨rv, hnm_m, shapeEq_quad_trans_vvh rv rvv (hsh rvv hv) hv_sh⟩⟩

private theorem dtxInv2_call_w_vvh {F : Type} {ptx : BitVec 64} {u m : PanSemStateFiniteExact 64 F}
    (h : dtxInv2_vvh ptx u) (fn : MlS) (args : List (ExpHOL 64))
    (hrun : evaluateHOLFiniteState u (.call (some (some (.local, ofString "w"), none)) fn args) = (none, m)) :
    dtxInv2_vvh ptx m := by
  obtain ⟨hother, rv, hnm_m, hsh⟩ := call_local_none_keeps u m (ofString "w") fn args hrun
  obtain ⟨htx, ⟨wk, hk⟩, ⟨ww, hw⟩, ⟨rvv, hv, hv_sh⟩⟩ := h
  have hsh1 : shapeEqHOL (shapeOfHOLExact rv) .one = true := by
    simpa [shapeOfHOLExact] using hsh (.val (.word ww)) hw
  rcases rv with ⟨⟨w'⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh1
  exact ⟨(hother _ (by decide)).trans htx,
         ⟨wk, (hother _ (by decide)).trans hk⟩,
         ⟨w', hnm_m⟩,
         ⟨rvv, (hother _ (by decide)).trans hv, hv_sh⟩⟩

private theorem dtxInv2_call_v_vvh {F : Type} {ptx : BitVec 64} {u m : PanSemStateFiniteExact 64 F}
    (h : dtxInv2_vvh ptx u) (fn : MlS) (args : List (ExpHOL 64))
    (hrun : evaluateHOLFiniteState u (.call (some (some (.local, ofString "v"), none)) fn args) = (none, m)) :
    dtxInv2_vvh ptx m := by
  obtain ⟨hother, rv, hnm_m, hsh⟩ := call_local_none_keeps u m (ofString "v") fn args hrun
  obtain ⟨htx, ⟨wk, hk⟩, ⟨ww, hw⟩, ⟨rvv, hv, hv_sh⟩⟩ := h
  exact ⟨(hother _ (by decide)).trans htx,
         ⟨wk, (hother _ (by decide)).trans hk⟩,
         ⟨ww, (hother _ (by decide)).trans hw⟩,
         ⟨rv, hnm_m, shapeEq_quad_trans_vvh rv rvv (hsh rvv hv) hv_sh⟩⟩

private theorem dtxInv2_store_vvh {F : Type} {ptx : BitVec 64} {u m : PanSemStateFiniteExact 64 F}
    (h : dtxInv2_vvh ptx u) (d e : ExpHOL 64)
    (hrun : evaluateHOLFiniteState u (.store d e) = (none, m)) :
    dtxInv2_vvh ptx m := by
  have hloc : m.locals = u.locals := by
    have hcf := (evaluate_store_control_frame u d e).2.1
    rwa [hrun] at hcf
  obtain ⟨htx, hk, hw, hv⟩ := h
  exact ⟨by rw [hloc]; exact htx, by rw [hloc]; exact hk, by rw [hloc]; exact hw, by rw [hloc]; exact hv⟩

private theorem decCall_none_inv_vvh {F : Type}
    {P : PanSemStateFiniteExact 64 F → Prop}
    {u m : PanSemStateFiniteExact 64 F}
    (nm : MlS) (sh : ShapeHOL) (fname : MlS) (args : List (ExpHOL 64)) (cont : ProgHOL 64)
    (hstep : ∀ (rv : ValueHOL 64) (cpost z : PanSemStateFiniteExact 64 F),
      shapeEqHOL (shapeOfHOLExact rv) sh = true →
      evaluateHOLFiniteState (setVarHOLFinite nm rv { cpost with locals := u.locals }) cont = (none, z) →
      P { z with locals := HolFiniteMapExact.resVarEq z.locals (nm, u.locals.lookup nm) })
    (hrun : evaluateHOLFiniteState u (.decCall nm sh fname args cont) = (none, m)) :
    P m := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun
  rcases hargs : evalListHOLFinite u (h := fun a => Classical.propDecidable (u.memaddrs a)) args with _ | vs
  · rw [hargs] at hrun; cases hrun
  · rw [hargs] at hrun; dsimp only at hrun
    rcases hlk : lookupCodeHOLFinite u.code.lookup fname vs with _ | ⟨b', c', r'⟩
    · rw [hlk] at hrun; cases hrun
    · rw [hlk] at hrun; dsimp only at hrun
      by_cases hz : u.clock = 0
      · rw [if_pos hz] at hrun; cases hrun
      · rw [if_neg hz] at hrun
        rcases hcal : evaluateHOLFiniteState (callEntryStateHOLFinite u c') b' with ⟨rc, st⟩
        rw [hcal] at hrun
        rcases rc with _ | (_ | _ | _ | _ | rv | _ | _) <;> dsimp only at hrun <;> try cases hrun
        by_cases hsh : shapeEqHOL (shapeOfHOLExact rv) sh && shapeEqHOL (shapeOfHOLExact rv) r'
        · rw [if_pos hsh] at hrun
          rcases hc : evaluateHOLFiniteState (setVarHOLFinite nm rv { st with locals := u.locals }) cont with ⟨rc2, z⟩
          rw [hc] at hrun; dsimp only at hrun
          injection hrun with hr hm; subst hr hm
          have hsh1 : shapeEqHOL (shapeOfHOLExact rv) sh = true := (Bool.and_eq_true _ _).mp hsh |>.1
          exact hstep rv st z hsh1 hc
        · rw [if_neg hsh] at hrun; cases hrun

private theorem dtxInv2_setVar_other_vvh {F : Type} {ptx : BitVec 64}
    {u cpost : PanSemStateFiniteExact 64 F}
    (h : dtxInv2_vvh ptx u) (nm : MlS) (rv : ValueHOL 64)
    (h1 : nm ≠ ofString "tx") (h2 : nm ≠ ofString "k")
    (h3 : nm ≠ ofString "w") (h4 : nm ≠ ofString "v") :
    dtxInv2_vvh ptx (setVarHOLFinite nm rv { cpost with locals := u.locals }) := by
  obtain ⟨htx, ⟨wk, hk⟩, ⟨ww, hw⟩, ⟨rvv, hv, hvsh⟩⟩ := h
  exact ⟨by simp [setVarHOLFinite, htx, HolFiniteMapExact.lookup_update, FUPDATE, h1],
         ⟨wk, by simp [setVarHOLFinite, hk, HolFiniteMapExact.lookup_update, FUPDATE, h2]⟩,
         ⟨ww, by simp [setVarHOLFinite, hw, HolFiniteMapExact.lookup_update, FUPDATE, h3]⟩,
         ⟨rvv, by simp [setVarHOLFinite, hv, HolFiniteMapExact.lookup_update, FUPDATE, h4], hvsh⟩⟩

private theorem dtxInv2_resVar_other_vvh {F : Type} {ptx : BitVec 64}
    {z : PanSemStateFiniteExact 64 F}
    (h : dtxInv2_vvh ptx z) (nm : MlS) (old : Option (ValueHOL 64))
    (h1 : nm ≠ ofString "tx") (h2 : nm ≠ ofString "k")
    (h3 : nm ≠ ofString "w") (h4 : nm ≠ ofString "v") :
    dtxInv2_vvh ptx { z with locals := HolFiniteMapExact.resVarEq z.locals (nm, old) } := by
  obtain ⟨htx, ⟨wk, hk⟩, ⟨ww, hw⟩, ⟨rvv, hv, hvsh⟩⟩ := h
  refine ⟨?_, ⟨wk, ?_⟩, ⟨ww, ?_⟩, ⟨rvv, ?_, hvsh⟩⟩
  · dsimp only; rw [resVarEq_lookup_local, if_neg (Ne.symm h1)]; exact htx
  · dsimp only; rw [resVarEq_lookup_local, if_neg (Ne.symm h2)]; exact hk
  · dsimp only; rw [resVarEq_lookup_local, if_neg (Ne.symm h3)]; exact hw
  · dsimp only; rw [resVarEq_lookup_local, if_neg (Ne.symm h4)]; exact hv

private theorem dtx_off_in_heap_vvh {F : Type} {s : PanSemStateFiniteExact 64 F}
    (ptx : BitVec 64) (off sz : Nat)
    (hoff : off + sz ≤ 400)
    (hlo : globN s "heap_ptr" ≤ ptx.toNat)
    (hhi : ptx.toNat + 400 ≤ heapLimit) :
    globN s "heap_ptr" ≤ (ptx + BitVec.ofNat 64 off).toNat ∧
    (ptx + BitVec.ofNat 64 off).toNat + sz ≤ heapLimit := by
  have hhl : heapLimit < 2 ^ 64 := by rw [heapLimit_val]; decide
  have hoff_lt : off < 2 ^ 64 := by omega
  have hoff_bv : (BitVec.ofNat 64 off).toNat = off := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff_lt]
  have hadd : (ptx + BitVec.ofNat 64 off).toNat = ptx.toNat + off := by
    rw [BitVec.toNat_add_of_lt (by rw [hoff_bv]; omega), hoff_bv]
  rw [hadd]; exact ⟨by omega, by omega⟩

private theorem worldEff_store_tx_w_vvh {F : Type} {s u : PanSemStateFiniteExact 64 F}
    {ptx : BitVec 64} (heff : WorldEff s u [] [] wsGw) (hinv : dtxInv2_vvh ptx u)
    (off : Nat) (hoff : off + 8 ≤ 400)
    (hlo : globN s "heap_ptr" ≤ ptx.toNat) (hhi : ptx.toNat + 400 ≤ heapLimit) :
    WorldEff s (evaluateHOLFiniteState u
      (.store (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])
              (.var .local (ofString "w")))).2 [] [] wsGw := by
  obtain ⟨htx, _, ⟨ww, hw⟩, _⟩ := hinv
  have hbnd := dtx_off_in_heap_vvh ptx off 8 hoff hlo hhi
  exact worldEff_store_heap_bounded heff _ _ 8
    (fun v hv => by simp [evalHOLExact, hw] at hv; subst hv; simp [flattenHOL])
    (fun x hx => by
      simp [evalHOLExact, evalListHOLExact, htx, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
      subst hx; exact hbnd)

private theorem worldEff_store_tx_v_vvh {F : Type} {s u : PanSemStateFiniteExact 64 F}
    {ptx : BitVec 64} (heff : WorldEff s u [] [] wsGw) (hinv : dtxInv2_vvh ptx u)
    (off : Nat) (hoff : off + 32 ≤ 400)
    (hlo : globN s "heap_ptr" ≤ ptx.toNat) (hhi : ptx.toNat + 400 ≤ heapLimit) :
    WorldEff s (evaluateHOLFiniteState u
      (.store (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])
              (.var .local (ofString "v")))).2 [] [] wsGw := by
  obtain ⟨htx, _, _, ⟨rvv, hv, hv_sh⟩⟩ := hinv
  have hbnd := dtx_off_in_heap_vvh ptx off 32 hoff hlo hhi
  exact worldEff_store_heap_bounded heff _ _ 32
    (fun v hv' => by simp [evalHOLExact, hv] at hv'; subst hv'; exact flattenHOL_len_four rvv hv_sh)
    (fun x hx => by
      simp [evalHOLExact, evalListHOLExact, htx, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
      subst hx; exact hbnd)

private theorem worldEff_store_tx_pair_vvh {F : Type} {s u : PanSemStateFiniteExact 64 F}
    {ptx : BitVec 64} {nm : MlS} {rvp : ValueHOL 64}
    (heff : WorldEff s u [] [] wsGw)
    (htx : u.locals.lookup (ofString "tx") = some (.val (.word ptx)))
    (hnm : u.locals.lookup nm = some rvp)
    (hsh : shapeEqHOL (shapeOfHOLExact rvp) (.comb [.one, .one]) = true)
    (idx : Nat) (hidx : idx = 0 ∨ idx = 1)
    (off : Nat) (hoff : off + 8 ≤ 400)
    (hlo : globN s "heap_ptr" ≤ ptx.toNat) (hhi : ptx.toNat + 400 ≤ heapLimit) :
    WorldEff s (evaluateHOLFiniteState u
      (.store (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])
              (.rfield idx (.var .local nm)))).2 [] [] wsGw := by
  have hbnd := dtx_off_in_heap_vvh ptx off 8 hoff hlo hhi
  rcases rvp with _ | rs | _ <;> simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh
  rcases rs with _ | ⟨v0, _ | ⟨v1, _ | _⟩⟩ <;>
    simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh
  rcases v0 with ⟨⟨w0⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh
  rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh
  exact worldEff_store_heap_bounded heff _ _ 8
    (fun v hv => by
      rcases hidx with rfl | rfl <;> (simp [evalHOLExact, hnm] at hv; subst hv; simp [flattenHOL]))
    (fun x hx => by
      simp [evalHOLExact, evalListHOLExact, htx, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
      subst hx; exact hbnd)

private theorem worldEff_call_u256_v_vvh {F : Type} {s u : PanSemStateFiniteExact 64 F}
    (heff : WorldEff s u [] [] wsGw) (args : List (ExpHOL 64))
    (hnt : (evaluateHOLFiniteState u (.call (some (some (.local, ofString "v"), none)) (ofString "tx_scalar_u256") args)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState u (.call (some (some (.local, ofString "v"), none)) (ofString "tx_scalar_u256") args)).1) :
    WorldEff s (evaluateHOLFiniteState u (.call (some (some (.local, ofString "v"), none)) (ofString "tx_scalar_u256") args)).2 [] [] wsGw :=
  worldEff_call_local_eff heff (ofString "v") (ofString "tx_scalar_u256") args
    _ _ _ lookup_tx_scalar_u256_vvh
    (fun callee cvals _ hlc hnt_cb hres_cb =>
      heff.trans_noBuf
        (WorldEff.from_locals_clock
          (worldEff_tx_scalar_u256_vvh (callEntryStateHOLFinite u callee) cvals
            heff.code (localsFree_arenaReady u callee _ heff.arena)
            (by simpa [heff.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
        ws_nil_sub_vvh ws_no_gb_vvh)
    hnt hcr

private theorem worldEff_call_word_w_vvh {F : Type} {s u : PanSemStateFiniteExact 64 F}
    (heff : WorldEff s u [] [] wsGw) (args : List (ExpHOL 64))
    (hnt : (evaluateHOLFiniteState u (.call (some (some (.local, ofString "w"), none)) (ofString "tx_scalar_word") args)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState u (.call (some (some (.local, ofString "w"), none)) (ofString "tx_scalar_word") args)).1) :
    WorldEff s (evaluateHOLFiniteState u (.call (some (some (.local, ofString "w"), none)) (ofString "tx_scalar_word") args)).2 [] [] wsGw :=
  worldEff_call_local_eff heff (ofString "w") (ofString "tx_scalar_word") args
    _ _ _ lookup_tx_scalar_word_vvh
    (fun callee cvals _ hlc hnt_cb hres_cb =>
      heff.trans_noBuf
        (WorldEff.from_locals_clock
          (worldEff_tx_scalar_word_vvh (callEntryStateHOLFinite u callee) cvals
            heff.code (localsFree_arenaReady u callee _ heff.arena)
            (by simpa [heff.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
        ws_nil_sub_vvh ws_no_gb_vvh)
    hnt hcr

private theorem worldEff_decode_transaction_rlp_vvh {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "decode_transaction_rlp") vals =
      some (sourceFnBody Guest.Software.guestFn_decode_transaction_rlp, s.locals, .one))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_transaction_rlp)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_transaction_rlp)).1) :
    WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_transaction_rlp)).2
      [] [] wsGw := by
  obtain ⟨wp, wlen, rfl, hsp, hslen⟩ :=
    lookupCode_two_words (by decide) lookup_decode_transaction_rlp_vvh hl
  have heff0 : WorldEff s s [] [] wsGw := WorldEff.refl s [] [] wsGw hAR hc
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_decode_transaction_rlp,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_seq hnt (Or.inr (Or.inr (Or.inr hres)))
    (fun hnt_g0 hcr_g0 =>
      worldEff_ite heff0 _ hnt_g0 hcr_g0
        (fun _ _ _ _ _ => worldEff_raise heff0 _ _)
        (fun _ _ _ => worldEff_skip heff0))
    (fun m0 hm0 heff_m0 hnt_1 hcr_1 => ?_)
  have hm0_eq : m0 = s := by
    rw [evaluateHOLFiniteState_ite] at hm0
    split at hm0
    · split at hm0
      · rw [evaluateHOLFiniteState_skip] at hm0; injection hm0 with _ hm; exact hm.symm
      · rw [evaluateHOLFiniteState_raise] at hm0
        split at hm0 <;> [ (dsimp only at hm0; split at hm0 <;> cases hm0); cases hm0 ]
    · cases hm0
  subst m0
  refine worldEff_dec heff0 _ _ _ hnt_1 hcr_1 (fun vb0 _ hvsh0 hnt_2 hcr_2 => ?_)
  rcases vb0 with ⟨⟨wb0⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hvsh0
  let m1 := setVarHOLFinite (ofString "b0") (.val (.word wb0)) s
  have heff_m1 : WorldEff s m1 [] [] wsGw := heff0.locals_clock _ _
  have hm1_p : m1.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    simp [m1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsp,
      show ofString "b0" ≠ ofString "p" by decide]
  have hm1_len : m1.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    simp [m1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hslen,
      show ofString "b0" ≠ ofString "len" by decide]
  refine worldEff_decCall_alloc heff_m1 (by decide) (ofString "tx") _ hnt_2 hcr_2
    (fun ptx nw m2 hsz_ev _ hm2_loc _ heff_m2 _ _ hptx_lo hptx_add hhp_m2_hi _ hnt_3 hcr_3 => ?_)
  have hnw_eq : nw = 400#64 := by simp [evalHOLExact] at hsz_ev; exact hsz_ev.symm
  subst hnw_eq
  have hptx_hi : ptx.toNat + 400 ≤ heapLimit := by
    have h400 : ((400#64 : BitVec 64).toNat + 7) / 8 * 8 = 400 := by decide
    omega
  have hm2_tx : m2.locals.lookup (ofString "tx") = some (.val (.word ptx)) := by
    simp [hm2_loc, HolFiniteMapExact.lookup_update, FUPDATE]
  have hm2_p : m2.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    simp [hm2_loc, hm1_p, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "tx" ≠ ofString "p" by decide]
  have hm2_len : m2.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    simp [hm2_loc, hm1_len, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "tx" ≠ ofString "len" by decide]
  refine worldEff_seq hnt_3 hcr_3
    (fun hnt_mz hcr_mz =>
      worldEff_call0_funByteEff_vvh heff_m2 funByteEff_memzero _ [(ptx.toNat, 400)]
        (fun vals hvals iv hiv _ => by
          have hargs_mz : evalListHOLFinite m2 (h := fun a => Classical.propDecidable (m2.memaddrs a))
              [.var .local (ofString "tx"), .const 400#64] =
              some [.val (.word ptx), .val (.word 400#64)] := by
            simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hm2_tx]
          rw [hargs_mz] at hvals; injection hvals with hvals; subst hvals
          have hiv' : iv = (ptx.toNat, 400) := by
            simpa [valWordNat] using hiv
          subst hiv'
          exact ⟨(ptx.toNat, 400), List.Mem.head _, le_rfl, le_rfl⟩)
        (fun iv hiv _ => by
          have hiv' : iv = (ptx.toNat, 400) := List.mem_singleton.mp hiv
          subst hiv'
          exact Or.inr (Or.inr (Or.inr ⟨hptx_lo, hptx_hi⟩)))
        hnt_mz hcr_mz)
    (fun m3 hm3 heff_m3 hnt_4 hcr_4 => ?_)
  have hm3_loc : m3.locals = m2.locals := call0_none_locals m2 m3 _ _ hm3
  have hm3_tx : m3.locals.lookup (ofString "tx") = some (.val (.word ptx)) := by
    rw [hm3_loc]; exact hm2_tx
  have hm3_p : m3.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    rw [hm3_loc]; exact hm2_p
  have hm3_len : m3.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    rw [hm3_loc]; exact hm2_len
  refine worldEff_seq hnt_4 hcr_4
    (fun _ _ => worldEff_store_heap_bounded heff_m3 _ _ 8
      (fun v hv => by simp [evalHOLExact, hm3_p] at hv; subst hv; simp [flattenHOL])
      (fun x hx => by
        simp [evalHOLExact, evalListHOLExact, hm3_tx, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
        subst hx; exact dtx_off_in_heap_vvh ptx 384 8 (by decide) hptx_lo hptx_hi))
    (fun m4 hm4 heff_m4 hnt_5 hcr_5 => ?_)
  have hm4_loc : m4.locals = m3.locals := by
    have hcf := (evaluate_store_control_frame m3
      (.op .add [.var .local (ofString "tx"), .const 384#64])
      (.var .local (ofString "p"))).2.1
    rwa [hm4] at hcf
  refine worldEff_seq hnt_5 hcr_5
    (fun _ _ => worldEff_store_heap_bounded heff_m4 _ _ 8
      (fun v hv => by simp [evalHOLExact, hm4_loc, hm3_len] at hv; subst hv; simp [flattenHOL])
      (fun x hx => by
        simp [evalHOLExact, evalListHOLExact, hm4_loc, hm3_tx, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
        subst hx; exact dtx_off_in_heap_vvh ptx 392 8 (by decide) hptx_lo hptx_hi))
    (fun m5 hm5 heff_m5 hnt_6 hcr_6 => ?_)
  have hm5_loc : m5.locals = m4.locals := by
    have hcf := (evaluate_store_control_frame m4
      (.op .add [.var .local (ofString "tx"), .const 392#64])
      (.var .local (ofString "len"))).2.1
    rwa [hm5] at hcf
  refine worldEff_dec heff_m5 _ _ _ hnt_6 hcr_6 (fun vtop hvtop _ hnt_7 hcr_7 => ?_)
  have hvtop_eq : vtop = .rStruct [.val (.word 0), .val (.word 0), .val (.word 0), .val (.word 0)] := by
    simp [evalHOLExact, evalListHOLExact] at hvtop; exact hvtop.symm
  subst hvtop_eq
  let m6 := setVarHOLFinite (ofString "top")
    (.rStruct [.val (.word 0), .val (.word 0), .val (.word 0), .val (.word 0)]) m5
  have heff_m6 : WorldEff s m6 [] [] wsGw := heff_m5.locals_clock _ _
  refine worldEff_dec heff_m6 _ _ _ hnt_7 hcr_7 (fun vt hvt _ hnt_8 hcr_8 => ?_)
  have hvt_eq : vt = .val (.word 0) := by simp [evalHOLExact] at hvt; exact hvt.symm
  subst hvt_eq
  let m7 := setVarHOLFinite (ofString "t") (.val (.word 0)) m6
  have heff_m7 : WorldEff s m7 [] [] wsGw := heff_m6.locals_clock _ _
  refine worldEff_dec heff_m7 _ _ _ hnt_8 hcr_8 (fun vnf hvnf _ hnt_9 hcr_9 => ?_)
  have hvnf_eq : vnf = .val (.word 9) := by simp [evalHOLExact] at hvnf; exact hvnf.symm
  subst hvnf_eq
  let m8 := setVarHOLFinite (ofString "nfields") (.val (.word 9)) m7
  have heff_m8 : WorldEff s m8 [] [] wsGw := heff_m7.locals_clock _ _
  have hinv_m8 : dtxInv_vvh ptx m8 := by
    refine ⟨?_, ⟨.rStruct [.val (.word 0), .val (.word 0), .val (.word 0), .val (.word 0)], ?_, by simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]⟩, ⟨0, ?_⟩, ⟨9, ?_⟩⟩
    · simp [m8, m7, m6, setVarHOLFinite, hm5_loc, hm4_loc, hm3_tx, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "nfields" ≠ ofString "tx" by decide,
        show ofString "t" ≠ ofString "tx" by decide,
        show ofString "top" ≠ ofString "tx" by decide]
    · simp [m8, m7, m6, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "nfields" ≠ ofString "top" by decide,
        show ofString "t" ≠ ofString "top" by decide]
    · simp [m8, m7, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "nfields" ≠ ofString "t" by decide]
    · simp [m8, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  refine worldEff_seq hnt_9 hcr_9
    (fun hnt_hd hcr_hd =>
      worldEff_ite heff_m8 _ hnt_hd hcr_hd
        (fun _ _ _ hnt_ty hcr_ty =>
          worldEff_seq hnt_ty hcr_ty
            (fun hnt_df1 hcr_df1 =>
              worldEff_call_local_eff heff_m8 (ofString "top") (ofString "rlp_decode_fully") _
                _ _ _ lookup_rlp_decode_fully_vvh
                (fun callee cvals _ hlc hnt_cb hres_cb =>
                  heff_m8.trans_noBuf
                    (WorldEff.from_locals_clock
                      (worldEff_rlp_decode_fully_vvh (callEntryStateHOLFinite m8 callee) cvals
                        heff_m8.code (localsFree_arenaReady m8 callee _ heff_m8.arena)
                        (by simpa [heff_m8.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
                    ws_nil_sub_vvh ws_no_gb_vvh)
                hnt_df1 hcr_df1)
            (fun y1 _ heff_y1 hnt_y1 hcr_y1 =>
              worldEff_seq hnt_y1 hcr_y1
                (fun _ _ => worldEff_assign_local heff_y1 _ _)
                (fun y2 _ heff_y2 hnt_y2 hcr_y2 =>
                  worldEff_seq hnt_y2 hcr_y2
                    (fun hnt_i1 hcr_i1 =>
                      worldEff_ite heff_y2 _ hnt_i1 hcr_i1
                        (fun _ _ _ _ _ => worldEff_assign_local heff_y2 _ _)
                        (fun _ _ _ => worldEff_skip heff_y2))
                    (fun y3 _ heff_y3 hnt_y3 hcr_y3 =>
                      worldEff_seq hnt_y3 hcr_y3
                        (fun hnt_i2 hcr_i2 =>
                          worldEff_ite heff_y3 _ hnt_i2 hcr_i2
                            (fun _ _ _ _ _ => worldEff_assign_local heff_y3 _ _)
                            (fun _ _ _ => worldEff_skip heff_y3))
                        (fun y4 _ heff_y4 hnt_y4 hcr_y4 =>
                          worldEff_seq hnt_y4 hcr_y4
                            (fun hnt_i3 hcr_i3 =>
                              worldEff_ite heff_y4 _ hnt_i3 hcr_i3
                                (fun _ _ _ _ _ => worldEff_assign_local heff_y4 _ _)
                                (fun _ _ _ => worldEff_skip heff_y4))
                            (fun y5 _ heff_y5 hnt_y5 hcr_y5 =>
                              worldEff_ite heff_y5 _ hnt_y5 hcr_y5
                                (fun _ _ _ _ _ => worldEff_assign_local heff_y5 _ _)
                                (fun _ _ _ => worldEff_skip heff_y5)))))))
        (fun _ hnt_lg hcr_lg =>
          worldEff_ite heff_m8 _ hnt_lg hcr_lg
            (fun _ _ _ hnt_df2 hcr_df2 =>
              worldEff_call_local_eff heff_m8 (ofString "top") (ofString "rlp_decode_fully") _
                _ _ _ lookup_rlp_decode_fully_vvh
                (fun callee cvals _ hlc hnt_cb hres_cb =>
                  heff_m8.trans_noBuf
                    (WorldEff.from_locals_clock
                      (worldEff_rlp_decode_fully_vvh (callEntryStateHOLFinite m8 callee) cvals
                        heff_m8.code (localsFree_arenaReady m8 callee _ heff_m8.arena)
                        (by simpa [heff_m8.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
                    ws_nil_sub_vvh ws_no_gb_vvh)
                hnt_df2 hcr_df2)
            (fun _ _ _ => worldEff_raise heff_m8 _ _)))
    (fun m9 hm9 heff_m9 hnt_10 hcr_10 => ?_)
  have hinv_m9 : dtxInv_vvh ptx m9 := by
    refine ite_none_keeps (P := dtxInv_vvh ptx) (fun y hm_y => ?_) (fun n hm_n => ?_) hm9
    · rw [evaluateHOLFiniteState_seq_line780] at hm_y
      rcases hs1 : evaluateHOLFiniteState m8 _ with ⟨r1, y1⟩; rw [hs1] at hm_y
      cases r1 <;> [dsimp only at hm_y; cases hm_y]
      have hi1 := dtxInv_set_top_vvh hinv_m8 _ _ hs1
      rw [evaluateHOLFiniteState_seq_line780] at hm_y
      rcases hs2 : evaluateHOLFiniteState y1 _ with ⟨r2, y2⟩; rw [hs2] at hm_y
      cases r2 <;> [dsimp only at hm_y; cases hm_y]
      have hi2 := dtxInv_set_t_vvh hi1 _ _ (Or.inl rfl) hs2
      rw [evaluateHOLFiniteState_seq_line780] at hm_y
      rcases hs3 : evaluateHOLFiniteState y2 _ with ⟨r3, y3⟩; rw [hs3] at hm_y
      cases r3 <;> [dsimp only at hm_y; cases hm_y]
      have hi3 : dtxInv_vvh ptx y3 := ite_none_keeps (P := dtxInv_vvh ptx)
        (fun z hz => dtxInv_set_t_vvh hi2 _ _ (Or.inr rfl) hz)
        (fun z hz => by rw [evaluateHOLFiniteState_skip] at hz; injection hz with _ h; subst h; exact hi2) hs3
      rw [evaluateHOLFiniteState_seq_line780] at hm_y
      rcases hs4 : evaluateHOLFiniteState y3 _ with ⟨r4, y4⟩; rw [hs4] at hm_y
      cases r4 <;> [dsimp only at hm_y; cases hm_y]
      have hi4 : dtxInv_vvh ptx y4 := ite_none_keeps (P := dtxInv_vvh ptx)
        (fun z hz => dtxInv_set_t_vvh hi3 _ _ (Or.inr rfl) hz)
        (fun z hz => by rw [evaluateHOLFiniteState_skip] at hz; injection hz with _ h; subst h; exact hi3) hs4
      rw [evaluateHOLFiniteState_seq_line780] at hm_y
      rcases hs5 : evaluateHOLFiniteState y4 _ with ⟨r5, y5⟩; rw [hs5] at hm_y
      cases r5 <;> [dsimp only at hm_y; cases hm_y]
      have hi5 : dtxInv_vvh ptx y5 := ite_none_keeps (P := dtxInv_vvh ptx)
        (fun z hz => dtxInv_set_t_vvh hi4 _ _ (Or.inr rfl) hz)
        (fun z hz => by rw [evaluateHOLFiniteState_skip] at hz; injection hz with _ h; subst h; exact hi4) hs5
      exact ite_none_keeps (P := dtxInv_vvh ptx)
        (fun z hz => dtxInv_set_t_vvh hi5 _ _ (Or.inr rfl) hz)
        (fun z hz => by rw [evaluateHOLFiniteState_skip] at hz; injection hz with _ h; subst h; exact hi5) hm_y
    · refine ite_none_keeps (P := dtxInv_vvh ptx) (fun z hz => dtxInv_set_top_vvh hinv_m8 _ _ hz) (fun z hz => ?_) hm_n
      rw [evaluateHOLFiniteState_raise] at hz
      split at hz <;> [ (dsimp only at hz; split at hz <;> cases hz); cases hz ]
  obtain ⟨hm9_tx, ⟨rvtop, hm9_top, _⟩, ⟨wt, hm9_t⟩, ⟨wnf, hm9_nf⟩⟩ := hinv_m9
  refine worldEff_seq hnt_10 hcr_10
    (fun _ _ => worldEff_store_heap_bounded heff_m9 _ _ 8
      (fun v hv => by simp [evalHOLExact, hm9_t] at hv; subst hv; simp [flattenHOL])
      (fun x hx => by
        simp [evalHOLExact, evalListHOLExact, hm9_tx, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
        subst hx; simpa using dtx_off_in_heap_vvh ptx 0 8 (by decide) hptx_lo hptx_hi))
    (fun m10 hm10 heff_m10 hnt_11 hcr_11 => ?_)
  have hm10_loc : m10.locals = m9.locals := by
    have hcf := (evaluate_store_control_frame m9
      (.op .add [.var .local (ofString "tx"), .const 0#64])
      (.var .local (ofString "t"))).2.1
    rwa [hm10] at hcf
  refine worldEff_seq hnt_11 hcr_11
    (fun hnt_g1 hcr_g1 =>
      worldEff_ite heff_m10 _ hnt_g1 hcr_g1
        (fun _ _ _ _ _ => worldEff_raise heff_m10 _ _)
        (fun _ _ _ => worldEff_skip heff_m10))
    (fun m11 hm11 heff_m11 hnt_12 hcr_12 => ?_)
  have hm11_eq : m11 = m10 := by
    rw [evaluateHOLFiniteState_ite] at hm11
    split at hm11
    · split at hm11
      · rw [evaluateHOLFiniteState_skip] at hm11; injection hm11 with _ hm; exact hm.symm
      · rw [evaluateHOLFiniteState_raise] at hm11
        split at hm11 <;> [ (dsimp only at hm11; split at hm11 <;> cases hm11); cases hm11 ]
    · cases hm11
  subst m11
  refine worldEff_decCall_eff heff_m10 (ofString "lst") (.comb [.one, .one]) (ofString "rlp_list_to_slices")
    _ _ _ _ lookup_rlp_list_to_slices_vvh
    (fun callee cvals _ hlc hnt_cb hres_cb =>
      heff_m10.trans_noBuf
        (WorldEff.from_locals_clock
          (worldEff_rlp_list_to_slices_vvh (callEntryStateHOLFinite m10 callee) cvals
            heff_m10.code (localsFree_arenaReady m10 callee _ heff_m10.arena)
            (by simpa [heff_m10.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
        ws_nil_sub_vvh ws_no_gb_vvh)
    (fun callee cvals rvlst cpost_lst _ hlc_lst hrun_lst _ heff_cp_lst hnt_13 hcr_13 => ?_)
    hnt_12 hcr_12
  obtain ⟨warr, wcnt, rfl, _⟩ :=
    rlp_list_to_slices_ret_bound_vvh (callEntryStateHOLFinite m10 callee) cpost_lst cvals rvlst
      heff_m10.code (guestInv_callEntry m10 callee heff_m10.arena.1)
      (by simpa [heff_m10.code, callEntryStateHOLFinite] using hlc_lst) hrun_lst
  let m12 := setVarHOLFinite (ofString "lst") (.rStruct [.val (.word warr), .val (.word wcnt)])
    { cpost_lst with locals := m10.locals }
  have heff_m12 : WorldEff s m12 [] [] wsGw := heff_cp_lst.locals_clock _ _
  have hm12_lst : m12.locals.lookup (ofString "lst") =
      some (.rStruct [.val (.word warr), .val (.word wcnt)]) := by
    simp [m12, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  refine worldEff_dec heff_m12 _ _ _ hnt_13 hcr_13 (fun varr hvarr _ hnt_14 hcr_14 => ?_)
  have hvarr_eq : varr = .val (.word warr) := by
    simp [evalHOLExact, hm12_lst] at hvarr; exact hvarr.symm
  subst hvarr_eq
  let m13 := setVarHOLFinite (ofString "arr") (.val (.word warr)) m12
  have heff_m13 : WorldEff s m13 [] [] wsGw := heff_m12.locals_clock _ _
  refine worldEff_seq hnt_14 hcr_14
    (fun hnt_g2 hcr_g2 =>
      worldEff_ite heff_m13 _ hnt_g2 hcr_g2
        (fun _ _ _ _ _ => worldEff_raise heff_m13 _ _)
        (fun _ _ _ => worldEff_skip heff_m13))
    (fun m14 hm14 heff_m14 hnt_15 hcr_15 => ?_)
  have hm14_eq : m14 = m13 := by
    rw [evaluateHOLFiniteState_ite] at hm14
    split at hm14
    · split at hm14
      · rw [evaluateHOLFiniteState_skip] at hm14; injection hm14 with _ hm; exact hm.symm
      · rw [evaluateHOLFiniteState_raise] at hm14
        split at hm14 <;> [ (dsimp only at hm14; split at hm14 <;> cases hm14); cases hm14 ]
    · cases hm14
  subst m14
  refine worldEff_dec heff_m13 _ _ _ hnt_15 hcr_15 (fun vk hvk _ hnt_16 hcr_16 => ?_)
  have hvk_eq : vk = .val (.word 0) := by simp [evalHOLExact] at hvk; exact hvk.symm
  subst hvk_eq
  let m15 := setVarHOLFinite (ofString "k") (.val (.word 0)) m13
  have heff_m15 : WorldEff s m15 [] [] wsGw := heff_m13.locals_clock _ _
  refine worldEff_dec heff_m15 _ _ _ hnt_16 hcr_16 (fun vw hvw _ hnt_17 hcr_17 => ?_)
  have hvw_eq : vw = .val (.word 0) := by simp [evalHOLExact] at hvw; exact hvw.symm
  subst hvw_eq
  let m16 := setVarHOLFinite (ofString "w") (.val (.word 0)) m15
  have heff_m16 : WorldEff s m16 [] [] wsGw := heff_m15.locals_clock _ _
  have hm16_tx : m16.locals.lookup (ofString "tx") = some (.val (.word ptx)) := by
    simp [m16, m15, m13, m12, setVarHOLFinite, hm10_loc, hm9_tx, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "w" ≠ ofString "tx" by decide,
      show ofString "k" ≠ ofString "tx" by decide,
      show ofString "arr" ≠ ofString "tx" by decide,
      show ofString "lst" ≠ ofString "tx" by decide]
  have hm16_w : m16.locals.lookup (ofString "w") = some (.val (.word 0)) := by
    simp [m16, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hm16_k : m16.locals.lookup (ofString "k") = some (.val (.word 0)) := by
    simp [m16, m15, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "w" ≠ ofString "k" by decide]
  refine worldEff_seq hnt_17 hcr_17
    (fun hnt_cid hcr_cid =>
      worldEff_ite heff_m16 _ hnt_cid hcr_cid
        (fun _ _ _ hnt_cy hcr_cy =>
          worldEff_seq hnt_cy hcr_cy
            (fun hnt_cw hcr_cw => worldEff_call_word_w_vvh heff_m16 _ hnt_cw hcr_cw)
            (fun q1 hq1 heff_q1 hnt_q1 hcr_q1 => by
              obtain ⟨hq1_other, rvw1, hq1_w, hq1_sh⟩ := call_local_none_keeps m16 q1 _ _ _ hq1
              have hsh1 : shapeEqHOL (shapeOfHOLExact rvw1) .one = true := by
                simpa [shapeOfHOLExact] using hq1_sh (.val (.word 0)) hm16_w
              rcases rvw1 with ⟨⟨ww1⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh1
              exact worldEff_seq hnt_q1 hcr_q1
                (fun _ _ => worldEff_store_heap_bounded heff_q1 _ _ 8
                  (fun v hv => by simp [evalHOLExact, hq1_w] at hv; subst hv; simp [flattenHOL])
                  (fun x hx => by
                    have hq1_tx := (hq1_other _ (by decide)).trans hm16_tx
                    simp [evalHOLExact, evalListHOLExact, hq1_tx, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
                    subst hx; exact dtx_off_in_heap_vvh ptx 8 8 (by decide) hptx_lo hptx_hi))
                (fun q2 _ heff_q2 _ _ => worldEff_assign_local heff_q2 _ _)))
        (fun _ _ _ => worldEff_skip heff_m16))
    (fun m17 hm17 heff_m17 hnt_18 hcr_18 => ?_)
  have hm17_inv_pre :
      m17.locals.lookup (ofString "tx") = some (.val (.word ptx)) ∧
      (∃ wk, m17.locals.lookup (ofString "k") = some (.val (.word wk))) ∧
      (∃ ww, m17.locals.lookup (ofString "w") = some (.val (.word ww))) := by
    refine ite_none_keeps (P := fun st =>
      st.locals.lookup (ofString "tx") = some (.val (.word ptx)) ∧
      (∃ wk, st.locals.lookup (ofString "k") = some (.val (.word wk))) ∧
      (∃ ww, st.locals.lookup (ofString "w") = some (.val (.word ww))))
      (fun y hm_y => ?_) (fun n hm_n => ?_) hm17
    · rw [evaluateHOLFiniteState_seq_line780] at hm_y
      rcases hs1 : evaluateHOLFiniteState m16 _ with ⟨r1, q1⟩; rw [hs1] at hm_y
      cases r1 <;> [dsimp only at hm_y; cases hm_y]
      obtain ⟨hq1_other, rvw1, hq1_w, hq1_sh⟩ := call_local_none_keeps m16 q1 _ _ _ hs1
      have hsh1 : shapeEqHOL (shapeOfHOLExact rvw1) .one = true := by
        simpa [shapeOfHOLExact] using hq1_sh (.val (.word 0)) hm16_w
      rcases rvw1 with ⟨⟨ww1⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh1
      rw [evaluateHOLFiniteState_seq_line780] at hm_y
      rcases hs2 : evaluateHOLFiniteState q1 _ with ⟨r2, q2⟩; rw [hs2] at hm_y
      cases r2 <;> [dsimp only at hm_y; cases hm_y]
      have hq2_loc : q2.locals = q1.locals := by
        have hcf := (evaluate_store_control_frame q1
          (.op .add [.var .local (ofString "tx"), .const 8#64])
          (.var .local (ofString "w"))).2.1
        rwa [hs2] at hcf
      obtain ⟨hy_other, rvk1, hy_k, hy_ksh⟩ := assign_local_none_keeps q2 y _ _ hm_y
      have hq2_k : q2.locals.lookup (ofString "k") = some (.val (.word 0)) := by
        rw [hq2_loc]; exact (hq1_other _ (by decide)).trans hm16_k
      have hshk : shapeEqHOL (shapeOfHOLExact rvk1) .one = true := by
        simpa [shapeOfHOLExact] using hy_ksh (.val (.word 0)) hq2_k
      rcases rvk1 with ⟨⟨wk1⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hshk
      exact ⟨(hy_other _ (by decide)).trans (by rw [hq2_loc]; exact (hq1_other _ (by decide)).trans hm16_tx),
             ⟨wk1, hy_k⟩,
             ⟨ww1, (hy_other _ (by decide)).trans (by rw [hq2_loc]; exact hq1_w)⟩⟩
    · rw [evaluateHOLFiniteState_skip] at hm_n; injection hm_n with _ h; subst h
      exact ⟨hm16_tx, ⟨0, hm16_k⟩, ⟨0, hm16_w⟩⟩
  refine worldEff_dec heff_m17 _ _ _ hnt_18 hcr_18 (fun vv hvv _ hnt_19 hcr_19 => ?_)
  have hvv_eq : vv = .rStruct [.val (.word 0), .val (.word 0), .val (.word 0), .val (.word 0)] := by
    simp [evalHOLExact, evalListHOLExact] at hvv; exact hvv.symm
  subst hvv_eq
  let m18 := setVarHOLFinite (ofString "v")
    (.rStruct [.val (.word 0), .val (.word 0), .val (.word 0), .val (.word 0)]) m17
  have heff_m18 : WorldEff s m18 [] [] wsGw := heff_m17.locals_clock _ _
  have hinv_m18 : dtxInv2_vvh ptx m18 := by
    obtain ⟨htx17, ⟨wk17, hk17⟩, ⟨ww17, hw17⟩⟩ := hm17_inv_pre
    refine ⟨?_, ⟨wk17, ?_⟩, ⟨ww17, ?_⟩, ⟨.rStruct [.val (.word 0), .val (.word 0), .val (.word 0), .val (.word 0)], ?_, by simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]⟩⟩
    · simp [m18, setVarHOLFinite, htx17, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "v" ≠ ofString "tx" by decide]
    · simp [m18, setVarHOLFinite, hk17, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "v" ≠ ofString "k" by decide]
    · simp [m18, setVarHOLFinite, hw17, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "v" ≠ ofString "w" by decide]
    · simp [m18, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  -- Nonce (t == 4 ? tx_scalar_word + assign v : tx_scalar_u256), store tx+16, k += 1
  refine worldEff_seq hnt_19 hcr_19
    (fun hnt_n hcr_n =>
      worldEff_ite heff_m18 _ hnt_n hcr_n
        (fun _ _ _ hnt_ny hcr_ny =>
          worldEff_seq hnt_ny hcr_ny
            (fun hnt_cw hcr_cw => worldEff_call_word_w_vvh heff_m18 _ hnt_cw hcr_cw)
            (fun z1 _ heff_z1 _ _ => worldEff_assign_local heff_z1 _ _))
        (fun _ hnt_nn hcr_nn => worldEff_call_u256_v_vvh heff_m18 _ hnt_nn hcr_nn))
    (fun m19 hm19 heff_m19 hnt_20 hcr_20 => ?_)
  have hinv_m19 : dtxInv2_vvh ptx m19 := by
    refine ite_none_keeps (P := dtxInv2_vvh ptx) (fun y hm_y => ?_) (fun n hm_n => dtxInv2_call_v_vvh hinv_m18 _ _ hm_n) hm19
    rw [evaluateHOLFiniteState_seq_line780] at hm_y
    rcases hs1 : evaluateHOLFiniteState m18 _ with ⟨r1, z1⟩; rw [hs1] at hm_y
    cases r1 <;> [dsimp only at hm_y; cases hm_y]
    exact dtxInv2_assign_v_vvh (dtxInv2_call_w_vvh hinv_m18 _ _ hs1) _ hm_y
  refine worldEff_seq hnt_20 hcr_20
    (fun _ _ => worldEff_store_tx_v_vvh heff_m19 hinv_m19 16 (by decide) hptx_lo hptx_hi)
    (fun m20 hm20 heff_m20 hnt_21 hcr_21 => ?_)
  have hinv_m20 := dtxInv2_store_vvh hinv_m19 _ _ hm20
  refine worldEff_seq hnt_21 hcr_21
    (fun _ _ => worldEff_assign_local heff_m20 _ _)
    (fun m21 hm21 heff_m21 hnt_22 hcr_22 => ?_)
  have hinv_m21 := dtxInv2_assign_k_vvh hinv_m20 _ hm21
  -- Fee fields (1 <=? t ? gas_price (tx+48) : max_priority (tx+80) + max_fee (tx+112))
  refine worldEff_seq hnt_22 hcr_22
    (fun hnt_f hcr_f =>
      worldEff_ite heff_m21 _ hnt_f hcr_f
        (fun _ _ _ hnt_fy hcr_fy =>
          worldEff_seq hnt_fy hcr_fy
            (fun hnt_cv hcr_cv => worldEff_call_u256_v_vvh heff_m21 _ hnt_cv hcr_cv)
            (fun z1 hz1 heff_z1 hnt_z1 hcr_z1 =>
              worldEff_seq hnt_z1 hcr_z1
                (fun _ _ => worldEff_store_tx_v_vvh heff_z1 (dtxInv2_call_v_vvh hinv_m21 _ _ hz1) 48 (by decide) hptx_lo hptx_hi)
                (fun z2 _ heff_z2 _ _ => worldEff_assign_local heff_z2 _ _)))
        (fun _ hnt_fn hcr_fn =>
          worldEff_seq hnt_fn hcr_fn
            (fun hnt_cv1 hcr_cv1 => worldEff_call_u256_v_vvh heff_m21 _ hnt_cv1 hcr_cv1)
            (fun z1 hz1 heff_z1 hnt_z1 hcr_z1 => by
              have hi_z1 := dtxInv2_call_v_vvh hinv_m21 _ _ hz1
              exact worldEff_seq hnt_z1 hcr_z1
                (fun _ _ => worldEff_store_tx_v_vvh heff_z1 hi_z1 80 (by decide) hptx_lo hptx_hi)
                (fun z2 hz2 heff_z2 hnt_z2 hcr_z2 => by
                  have hi_z2 := dtxInv2_store_vvh hi_z1 _ _ hz2
                  exact worldEff_seq hnt_z2 hcr_z2
                    (fun hnt_cv2 hcr_cv2 => worldEff_call_u256_v_vvh heff_z2 _ hnt_cv2 hcr_cv2)
                    (fun z3 hz3 heff_z3 hnt_z3 hcr_z3 =>
                      worldEff_seq hnt_z3 hcr_z3
                        (fun _ _ => worldEff_store_tx_v_vvh heff_z3 (dtxInv2_call_v_vvh hi_z2 _ _ hz3) 112 (by decide) hptx_lo hptx_hi)
                        (fun z4 _ heff_z4 _ _ => worldEff_assign_local heff_z4 _ _))))))
    (fun m22 hm22 heff_m22 hnt_23 hcr_23 => ?_)
  have hinv_m22 : dtxInv2_vvh ptx m22 := by
    refine ite_none_keeps (P := dtxInv2_vvh ptx) (fun y hm_y => ?_) (fun n hm_n => ?_) hm22
    · rw [evaluateHOLFiniteState_seq_line780] at hm_y
      rcases hs1 : evaluateHOLFiniteState m21 _ with ⟨r1, z1⟩; rw [hs1] at hm_y
      cases r1 <;> [dsimp only at hm_y; cases hm_y]
      rw [evaluateHOLFiniteState_seq_line780] at hm_y
      rcases hs2 : evaluateHOLFiniteState z1 _ with ⟨r2, z2⟩; rw [hs2] at hm_y
      cases r2 <;> [dsimp only at hm_y; cases hm_y]
      exact dtxInv2_assign_k_vvh (dtxInv2_store_vvh (dtxInv2_call_v_vvh hinv_m21 _ _ hs1) _ _ hs2) _ hm_y
    · rw [evaluateHOLFiniteState_seq_line780] at hm_n
      rcases hs1 : evaluateHOLFiniteState m21 _ with ⟨r1, z1⟩; rw [hs1] at hm_n
      cases r1 <;> [dsimp only at hm_n; cases hm_n]
      rw [evaluateHOLFiniteState_seq_line780] at hm_n
      rcases hs2 : evaluateHOLFiniteState z1 _ with ⟨r2, z2⟩; rw [hs2] at hm_n
      cases r2 <;> [dsimp only at hm_n; cases hm_n]
      rw [evaluateHOLFiniteState_seq_line780] at hm_n
      rcases hs3 : evaluateHOLFiniteState z2 _ with ⟨r3, z3⟩; rw [hs3] at hm_n
      cases r3 <;> [dsimp only at hm_n; cases hm_n]
      rw [evaluateHOLFiniteState_seq_line780] at hm_n
      rcases hs4 : evaluateHOLFiniteState z3 _ with ⟨r4, z4⟩; rw [hs4] at hm_n
      cases r4 <;> [dsimp only at hm_n; cases hm_n]
      exact dtxInv2_assign_k_vvh
        (dtxInv2_store_vvh
          (dtxInv2_call_v_vvh
            (dtxInv2_store_vvh (dtxInv2_call_v_vvh hinv_m21 _ _ hs1) _ _ hs2) _ _ hs3) _ _ hs4) _ hm_n
  -- gas limit: tx_scalar_word -> w, store tx+144, k += 1
  refine worldEff_seq hnt_23 hcr_23
    (fun hnt_cw hcr_cw => worldEff_call_word_w_vvh heff_m22 _ hnt_cw hcr_cw)
    (fun m23 hm23 heff_m23 hnt_24 hcr_24 => ?_)
  have hinv_m23 := dtxInv2_call_w_vvh hinv_m22 _ _ hm23
  refine worldEff_seq hnt_24 hcr_24
    (fun _ _ => worldEff_store_tx_w_vvh heff_m23 hinv_m23 144 (by decide) hptx_lo hptx_hi)
    (fun m24 hm24 heff_m24 hnt_25 hcr_25 => ?_)
  have hinv_m24 := dtxInv2_store_vvh hinv_m23 _ _ hm24
  refine worldEff_seq hnt_25 hcr_25
    (fun _ _ => worldEff_assign_local heff_m24 _ _)
    (fun m25 hm25 heff_m25 hnt_26 hcr_26 => ?_)
  have hinv_m25 := dtxInv2_assign_k_vvh hinv_m24 _ hm25
  -- to: ite (t >= 3) (tx_fixed_bytes -> w) (tx_to_item -> w), store tx+152, k += 1
  refine worldEff_seq hnt_26 hcr_26
    (fun hnt_to hcr_to =>
      worldEff_ite heff_m25 _ hnt_to hcr_to
        (fun _ _ _ hnt_ty hcr_ty =>
          worldEff_call_local_eff heff_m25 (ofString "w") (ofString "tx_fixed_bytes") _
            _ _ _ lookup_tx_fixed_bytes_vvh
            (fun callee cvals _ hlc hnt_cb hres_cb =>
              heff_m25.trans_noBuf
                (WorldEff.from_locals_clock
                  (worldEff_tx_fixed_bytes_vvh (callEntryStateHOLFinite m25 callee) cvals
                    heff_m25.code (localsFree_arenaReady m25 callee _ heff_m25.arena)
                    (by simpa [heff_m25.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
                ws_nil_sub_vvh ws_no_gb_vvh)
            hnt_ty hcr_ty)
        (fun _ hnt_tn hcr_tn =>
          worldEff_call_local_eff heff_m25 (ofString "w") (ofString "tx_to_item") _
            _ _ _ lookup_tx_to_item_vvh
            (fun callee cvals _ hlc hnt_cb hres_cb =>
              heff_m25.trans_noBuf
                (WorldEff.from_locals_clock
                  (worldEff_tx_to_item_vvh (callEntryStateHOLFinite m25 callee) cvals
                    heff_m25.code (localsFree_arenaReady m25 callee _ heff_m25.arena)
                    (by simpa [heff_m25.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
                ws_nil_sub_vvh ws_no_gb_vvh)
            hnt_tn hcr_tn))
    (fun m26 hm26 heff_m26 hnt_27 hcr_27 => ?_)
  have hinv_m26 : dtxInv2_vvh ptx m26 :=
    ite_none_keeps (P := dtxInv2_vvh ptx) (fun y hy => dtxInv2_call_w_vvh hinv_m25 _ _ hy)
      (fun n hn => dtxInv2_call_w_vvh hinv_m25 _ _ hn) hm26
  refine worldEff_seq hnt_27 hcr_27
    (fun _ _ => worldEff_store_tx_w_vvh heff_m26 hinv_m26 152 (by decide) hptx_lo hptx_hi)
    (fun m27 hm27 heff_m27 hnt_28 hcr_28 => ?_)
  have hinv_m27 := dtxInv2_store_vvh hinv_m26 _ _ hm27
  refine worldEff_seq hnt_28 hcr_28
    (fun _ _ => worldEff_assign_local heff_m27 _ _)
    (fun m28 hm28 heff_m28 hnt_29 hcr_29 => ?_)
  have hinv_m28 := dtxInv2_assign_k_vvh hinv_m27 _ hm28
  -- value: tx_scalar_u256 -> v, store tx+160, k += 1
  refine worldEff_seq hnt_29 hcr_29
    (fun hnt_cv hcr_cv => worldEff_call_u256_v_vvh heff_m28 _ hnt_cv hcr_cv)
    (fun m29 hm29 heff_m29 hnt_30 hcr_30 => ?_)
  have hinv_m29 := dtxInv2_call_v_vvh hinv_m28 _ _ hm29
  refine worldEff_seq hnt_30 hcr_30
    (fun _ _ => worldEff_store_tx_v_vvh heff_m29 hinv_m29 160 (by decide) hptx_lo hptx_hi)
    (fun m30 hm30 heff_m30 hnt_31 hcr_31 => ?_)
  have hinv_m30 := dtxInv2_store_vvh hinv_m29 _ _ hm30
  refine worldEff_seq hnt_31 hcr_31
    (fun _ _ => worldEff_assign_local heff_m30 _ _)
    (fun m31 hm31 heff_m31 hnt_32 hcr_32 => ?_)
  have hinv_m31 := dtxInv2_assign_k_vvh hinv_m30 _ hm31
  -- decCall data := tx_bytes_item(arr, k), store tx+192, store tx+200, k += 1
  refine worldEff_decCall_eff heff_m31 (ofString "data") (.comb [.one, .one]) (ofString "tx_bytes_item")
    _ _ _ _ lookup_tx_bytes_item_vvh
    (fun callee cvals _ hlc hnt_cb hres_cb =>
      heff_m31.trans_noBuf
        (WorldEff.from_locals_clock
          (worldEff_tx_bytes_item_vvh (callEntryStateHOLFinite m31 callee) cvals
            heff_m31.code (localsFree_arenaReady m31 callee _ heff_m31.arena)
            (by simpa [heff_m31.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
        ws_nil_sub_vvh ws_no_gb_vvh)
    (fun _ _ rvdata cpost_d _ _ _ hsh_data heff_cp_d hnt_33 hcr_33 => ?_)
    hnt_32 hcr_32
  let m32 := setVarHOLFinite (ofString "data") rvdata { cpost_d with locals := m31.locals }
  have heff_m32 : WorldEff s m32 [] [] wsGw := heff_cp_d.locals_clock _ _
  have hm32_data : m32.locals.lookup (ofString "data") = some rvdata := by
    simp [m32, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hinv_m32 : dtxInv2_vvh ptx m32 := by
    obtain ⟨htx31, ⟨wk31, hk31⟩, ⟨ww31, hw31⟩, ⟨rvv31, hv31, hvsh31⟩⟩ := hinv_m31
    exact ⟨by simp [m32, setVarHOLFinite, htx31, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "data" ≠ ofString "tx" by decide],
           ⟨wk31, by simp [m32, setVarHOLFinite, hk31, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "data" ≠ ofString "k" by decide]⟩,
           ⟨ww31, by simp [m32, setVarHOLFinite, hw31, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "data" ≠ ofString "w" by decide]⟩,
           ⟨rvv31, by simp [m32, setVarHOLFinite, hv31, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "data" ≠ ofString "v" by decide], hvsh31⟩⟩
  refine worldEff_seq hnt_33 hcr_33
    (fun _ _ => worldEff_store_tx_pair_vvh heff_m32 hinv_m32.1 hm32_data hsh_data 0 (Or.inl rfl) 192 (by decide) hptx_lo hptx_hi)
    (fun m33 hm33 heff_m33 hnt_34 hcr_34 => ?_)
  have hm33_loc : m33.locals = m32.locals := by
    have hcf := (evaluate_store_control_frame m32
      (.op .add [.var .local (ofString "tx"), .const 192#64])
      (.rfield 0 (.var .local (ofString "data")))).2.1
    rwa [hm33] at hcf
  have hinv_m33 := dtxInv2_store_vvh hinv_m32 _ _ hm33
  refine worldEff_seq hnt_34 hcr_34
    (fun _ _ => worldEff_store_tx_pair_vvh heff_m33 hinv_m33.1 (by rw [hm33_loc]; exact hm32_data) hsh_data 1 (Or.inr rfl) 200 (by decide) hptx_lo hptx_hi)
    (fun m34 hm34 heff_m34 hnt_35 hcr_35 => ?_)
  have hinv_m34 := dtxInv2_store_vvh hinv_m33 _ _ hm34
  refine worldEff_seq hnt_35 hcr_35
    (fun _ _ => worldEff_assign_local heff_m34 _ _)
    (fun m35 hm35 heff_m35 hnt_36 hcr_36 => ?_)
  have hinv_m35 := dtxInv2_assign_k_vvh hinv_m34 _ hm35
  -- access_list: ite (t != 0) (decCall al := tx_list_item, decCall acc := decode_access_list, store 208, store 216, k += 1) skip
  refine worldEff_seq hnt_36 hcr_36
    (fun hnt_al hcr_al =>
      worldEff_ite heff_m35 _ hnt_al hcr_al
        (fun _ _ _ hnt_aly hcr_aly =>
          worldEff_decCall_eff heff_m35 (ofString "al") (.comb [.one, .one]) (ofString "tx_list_item")
            _ _ _ _ lookup_tx_list_item_vvh
            (fun callee cvals _ hlc hnt_cb hres_cb =>
              heff_m35.trans_noBuf
                (WorldEff.from_locals_clock
                  (worldEff_tx_list_item_vvh (callEntryStateHOLFinite m35 callee) cvals
                    heff_m35.code (localsFree_arenaReady m35 callee _ heff_m35.arena)
                    (by simpa [heff_m35.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
                ws_nil_sub_vvh ws_no_gb_vvh)
            (fun _ _ rval cpost_al _ _ _ _ heff_cp_al hnt_al1 hcr_al1 => by
              let a1 := setVarHOLFinite (ofString "al") rval { cpost_al with locals := m35.locals }
              have heff_a1 : WorldEff s a1 [] [] wsGw := heff_cp_al.locals_clock _ _
              exact worldEff_decCall_eff heff_a1 (ofString "acc") (.comb [.one, .one]) (ofString "decode_access_list")
                _ _ _ _ lookup_decode_access_list_vvh
                (fun callee cvals _ hlc hnt_cb hres_cb =>
                  heff_a1.trans_noBuf
                    (WorldEff.from_locals_clock
                      (worldEff_decode_access_list_vvh (callEntryStateHOLFinite a1 callee) cvals
                        heff_a1.code (localsFree_arenaReady a1 callee _ heff_a1.arena)
                        (by simpa [heff_a1.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
                    ws_nil_sub_vvh ws_no_gb_vvh)
                (fun _ _ rvacc cpost_acc _ _ _ hsh_acc heff_cp_acc hnt_al2 hcr_al2 => by
                  let a2 := setVarHOLFinite (ofString "acc") rvacc { cpost_acc with locals := a1.locals }
                  have heff_a2 : WorldEff s a2 [] [] wsGw := heff_cp_acc.locals_clock _ _
                  have ha2_tx : a2.locals.lookup (ofString "tx") = some (.val (.word ptx)) := by
                    simp [a2, a1, setVarHOLFinite, hinv_m35.1, HolFiniteMapExact.lookup_update, FUPDATE,
                      show ofString "acc" ≠ ofString "tx" by decide,
                      show ofString "al" ≠ ofString "tx" by decide]
                  have ha2_acc : a2.locals.lookup (ofString "acc") = some rvacc := by
                    simp [a2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  exact worldEff_seq hnt_al2 hcr_al2
                    (fun _ _ => worldEff_store_tx_pair_vvh heff_a2 ha2_tx ha2_acc hsh_acc 0 (Or.inl rfl) 208 (by decide) hptx_lo hptx_hi)
                    (fun a3 ha3 heff_a3 hnt_al3 hcr_al3 => by
                      have ha3_loc : a3.locals = a2.locals := by
                        have hcf := (evaluate_store_control_frame a2
                          (.op .add [.var .local (ofString "tx"), .const 208#64])
                          (.rfield 0 (.var .local (ofString "acc")))).2.1
                        rwa [ha3] at hcf
                      exact worldEff_seq hnt_al3 hcr_al3
                        (fun _ _ => worldEff_store_tx_pair_vvh heff_a3
                          (by rw [ha3_loc]; exact ha2_tx) (by rw [ha3_loc]; exact ha2_acc)
                          hsh_acc 1 (Or.inr rfl) 216 (by decide) hptx_lo hptx_hi)
                        (fun a4 _ heff_a4 _ _ => worldEff_assign_local heff_a4 _ _)))
                hnt_al1 hcr_al1)
            hnt_aly hcr_aly)
        (fun _ _ _ => worldEff_skip heff_m35))
    (fun m36 hm36 heff_m36 hnt_37 hcr_37 => ?_)
  have hinv_m36 : dtxInv2_vvh ptx m36 := by
    refine ite_none_keeps (P := dtxInv2_vvh ptx) (fun y hm_y => ?_)
      (fun n hm_n => by rw [evaluateHOLFiniteState_skip] at hm_n; injection hm_n with _ h; subst h; exact hinv_m35) hm36
    refine decCall_none_inv_vvh (P := dtxInv2_vvh ptx) _ _ _ _ _ (fun rval cpost1 z1 _ hz1 => ?_) hm_y
    apply dtxInv2_resVar_other_vvh _ _ _ (by decide) (by decide) (by decide) (by decide)
    let a1_i := setVarHOLFinite (ofString "al") rval { cpost1 with locals := m35.locals }
    have hi_a1 : dtxInv2_vvh ptx a1_i :=
      dtxInv2_setVar_other_vvh hinv_m35 (ofString "al") rval (by decide) (by decide) (by decide) (by decide)
    refine decCall_none_inv_vvh (P := dtxInv2_vvh ptx) _ _ _ _ _ (fun rvacc cpost2 z2 _ hz2 => ?_) hz1
    apply dtxInv2_resVar_other_vvh _ _ _ (by decide) (by decide) (by decide) (by decide)
    let a2_i := setVarHOLFinite (ofString "acc") rvacc { cpost2 with locals := a1_i.locals }
    have hi_a2 : dtxInv2_vvh ptx a2_i :=
      dtxInv2_setVar_other_vvh hi_a1 (ofString "acc") rvacc (by decide) (by decide) (by decide) (by decide)
    rw [evaluateHOLFiniteState_seq_line780] at hz2
    rcases hs1 : evaluateHOLFiniteState a2_i _ with ⟨r1, a3⟩; rw [hs1] at hz2
    cases r1 <;> [dsimp only at hz2; cases hz2]
    rw [evaluateHOLFiniteState_seq_line780] at hz2
    rcases hs2 : evaluateHOLFiniteState a3 _ with ⟨r2, a4⟩; rw [hs2] at hz2
    cases r2 <;> [dsimp only at hz2; cases hz2]
    exact dtxInv2_assign_k_vvh (dtxInv2_store_vvh (dtxInv2_store_vvh hi_a2 _ _ hs1) _ _ hs2) _ hz2
  -- blob_hashes: ite (t == 3) (tx_scalar_u256 -> v, store 224, decCall bl := tx_list_item, decCall bh := decode_blob_hashes, store 256, store 264, k += 2) skip
  refine worldEff_seq hnt_37 hcr_37
    (fun hnt_bh hcr_bh =>
      worldEff_ite heff_m36 _ hnt_bh hcr_bh
        (fun _ _ _ hnt_bhy hcr_bhy =>
          worldEff_seq hnt_bhy hcr_bhy
            (fun hnt_cv hcr_cv => worldEff_call_u256_v_vvh heff_m36 _ hnt_cv hcr_cv)
            (fun b1 hb1 heff_b1 hnt_b1 hcr_b1 => by
              have hi_b1 := dtxInv2_call_v_vvh hinv_m36 _ _ hb1
              exact worldEff_seq hnt_b1 hcr_b1
                (fun _ _ => worldEff_store_tx_v_vvh heff_b1 hi_b1 224 (by decide) hptx_lo hptx_hi)
                (fun b2 hb2 heff_b2 hnt_b2 hcr_b2 => by
                  have hi_b2 := dtxInv2_store_vvh hi_b1 _ _ hb2
                  exact worldEff_decCall_eff heff_b2 (ofString "bl") (.comb [.one, .one]) (ofString "tx_list_item")
                    _ _ _ _ lookup_tx_list_item_vvh
                    (fun callee cvals _ hlc hnt_cb hres_cb =>
                      heff_b2.trans_noBuf
                        (WorldEff.from_locals_clock
                          (worldEff_tx_list_item_vvh (callEntryStateHOLFinite b2 callee) cvals
                            heff_b2.code (localsFree_arenaReady b2 callee _ heff_b2.arena)
                            (by simpa [heff_b2.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
                        ws_nil_sub_vvh ws_no_gb_vvh)
                    (fun _ _ rvbl cpost_bl _ _ _ _ heff_cp_bl hnt_b3 hcr_b3 => by
                      let b3 := setVarHOLFinite (ofString "bl") rvbl { cpost_bl with locals := b2.locals }
                      have heff_b3 : WorldEff s b3 [] [] wsGw := heff_cp_bl.locals_clock _ _
                      exact worldEff_decCall_eff heff_b3 (ofString "bh") (.comb [.one, .one]) (ofString "decode_blob_hashes")
                        _ _ _ _ lookup_decode_blob_hashes_vvh
                        (fun callee cvals _ hlc hnt_cb hres_cb =>
                          heff_b3.trans_noBuf
                            (WorldEff.from_locals_clock
                              (worldEff_decode_blob_hashes_vvh (callEntryStateHOLFinite b3 callee) cvals
                                heff_b3.code (localsFree_arenaReady b3 callee _ heff_b3.arena)
                                (by simpa [heff_b3.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
                            ws_nil_sub_vvh ws_no_gb_vvh)
                        (fun _ _ rvbh cpost_bh _ _ _ hsh_bh heff_cp_bh hnt_b4 hcr_b4 => by
                          let b4 := setVarHOLFinite (ofString "bh") rvbh { cpost_bh with locals := b3.locals }
                          have heff_b4 : WorldEff s b4 [] [] wsGw := heff_cp_bh.locals_clock _ _
                          have hb4_tx : b4.locals.lookup (ofString "tx") = some (.val (.word ptx)) := by
                            simp [b4, b3, setVarHOLFinite, hi_b2.1, HolFiniteMapExact.lookup_update, FUPDATE,
                              show ofString "bh" ≠ ofString "tx" by decide,
                              show ofString "bl" ≠ ofString "tx" by decide]
                          have hb4_bh : b4.locals.lookup (ofString "bh") = some rvbh := by
                            simp [b4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                          exact worldEff_seq hnt_b4 hcr_b4
                            (fun _ _ => worldEff_store_tx_pair_vvh heff_b4 hb4_tx hb4_bh hsh_bh 0 (Or.inl rfl) 256 (by decide) hptx_lo hptx_hi)
                            (fun b5 hb5 heff_b5 hnt_b5 hcr_b5 => by
                              have hb5_loc : b5.locals = b4.locals := by
                                have hcf := (evaluate_store_control_frame b4
                                  (.op .add [.var .local (ofString "tx"), .const 256#64])
                                  (.rfield 0 (.var .local (ofString "bh")))).2.1
                                rwa [hb5] at hcf
                              exact worldEff_seq hnt_b5 hcr_b5
                                (fun _ _ => worldEff_store_tx_pair_vvh heff_b5
                                  (by rw [hb5_loc]; exact hb4_tx) (by rw [hb5_loc]; exact hb4_bh)
                                  hsh_bh 1 (Or.inr rfl) 264 (by decide) hptx_lo hptx_hi)
                                (fun b6 _ heff_b6 _ _ => worldEff_assign_local heff_b6 _ _)))
                        hnt_b3 hcr_b3)
                    hnt_b2 hcr_b2)))
        (fun _ _ _ => worldEff_skip heff_m36))
    (fun m37 hm37 heff_m37 hnt_38 hcr_38 => ?_)
  have hinv_m37 : dtxInv2_vvh ptx m37 := by
    refine ite_none_keeps (P := dtxInv2_vvh ptx) (fun y hm_y => ?_)
      (fun n hm_n => by rw [evaluateHOLFiniteState_skip] at hm_n; injection hm_n with _ h; subst h; exact hinv_m36) hm37
    rw [evaluateHOLFiniteState_seq_line780] at hm_y
    rcases hs1 : evaluateHOLFiniteState m36 _ with ⟨r1, b1⟩; rw [hs1] at hm_y
    cases r1 <;> [dsimp only at hm_y; cases hm_y]
    rw [evaluateHOLFiniteState_seq_line780] at hm_y
    rcases hs2 : evaluateHOLFiniteState b1 _ with ⟨r2, b2⟩; rw [hs2] at hm_y
    cases r2 <;> [dsimp only at hm_y; cases hm_y]
    have hi_b2 := dtxInv2_store_vvh (dtxInv2_call_v_vvh hinv_m36 _ _ hs1) _ _ hs2
    refine decCall_none_inv_vvh (P := dtxInv2_vvh ptx) _ _ _ _ _ (fun rvbl cpost1 z1 _ hz1 => ?_) hm_y
    apply dtxInv2_resVar_other_vvh _ _ _ (by decide) (by decide) (by decide) (by decide)
    let b3_i := setVarHOLFinite (ofString "bl") rvbl { cpost1 with locals := b2.locals }
    have hi_b3 : dtxInv2_vvh ptx b3_i :=
      dtxInv2_setVar_other_vvh hi_b2 (ofString "bl") rvbl (by decide) (by decide) (by decide) (by decide)
    refine decCall_none_inv_vvh (P := dtxInv2_vvh ptx) _ _ _ _ _ (fun rvbh cpost2 z2 _ hz2 => ?_) hz1
    apply dtxInv2_resVar_other_vvh _ _ _ (by decide) (by decide) (by decide) (by decide)
    let b4_i := setVarHOLFinite (ofString "bh") rvbh { cpost2 with locals := b3_i.locals }
    have hi_b4 : dtxInv2_vvh ptx b4_i :=
      dtxInv2_setVar_other_vvh hi_b3 (ofString "bh") rvbh (by decide) (by decide) (by decide) (by decide)
    rw [evaluateHOLFiniteState_seq_line780] at hz2
    rcases hs3 : evaluateHOLFiniteState b4_i _ with ⟨r3, b5⟩; rw [hs3] at hz2
    cases r3 <;> [dsimp only at hz2; cases hz2]
    rw [evaluateHOLFiniteState_seq_line780] at hz2
    rcases hs4 : evaluateHOLFiniteState b5 _ with ⟨r4, b6⟩; rw [hs4] at hz2
    cases r4 <;> [dsimp only at hz2; cases hz2]
    exact dtxInv2_assign_k_vvh (dtxInv2_store_vvh (dtxInv2_store_vvh hi_b4 _ _ hs3) _ _ hs4) _ hz2
  -- authorizations: ite (t == 4) (decCall aul := tx_list_item, decCall au := decode_authorizations, store 272, store 280, k += 1) skip
  refine worldEff_seq hnt_38 hcr_38
    (fun hnt_au hcr_au =>
      worldEff_ite heff_m37 _ hnt_au hcr_au
        (fun _ _ _ hnt_auy hcr_auy =>
          worldEff_decCall_eff heff_m37 (ofString "aul") (.comb [.one, .one]) (ofString "tx_list_item")
            _ _ _ _ lookup_tx_list_item_vvh
            (fun callee cvals _ hlc hnt_cb hres_cb =>
              heff_m37.trans_noBuf
                (WorldEff.from_locals_clock
                  (worldEff_tx_list_item_vvh (callEntryStateHOLFinite m37 callee) cvals
                    heff_m37.code (localsFree_arenaReady m37 callee _ heff_m37.arena)
                    (by simpa [heff_m37.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
                ws_nil_sub_vvh ws_no_gb_vvh)
            (fun _ _ rvaul cpost_aul _ _ _ _ heff_cp_aul hnt_au1 hcr_au1 => by
              let c1 := setVarHOLFinite (ofString "aul") rvaul { cpost_aul with locals := m37.locals }
              have heff_c1 : WorldEff s c1 [] [] wsGw := heff_cp_aul.locals_clock _ _
              exact worldEff_decCall_eff heff_c1 (ofString "au") (.comb [.one, .one]) (ofString "decode_authorizations")
                _ _ _ _ lookup_decode_authorizations_vvh
                (fun callee cvals _ hlc hnt_cb hres_cb =>
                  heff_c1.trans_noBuf
                    (WorldEff.from_locals_clock
                      (worldEff_decode_authorizations_vvh (callEntryStateHOLFinite c1 callee) cvals
                        heff_c1.code (localsFree_arenaReady c1 callee _ heff_c1.arena)
                        (by simpa [heff_c1.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
                    ws_nil_sub_vvh ws_no_gb_vvh)
                (fun _ _ rvau cpost_au _ _ _ hsh_au heff_cp_au hnt_au2 hcr_au2 => by
                  let c2 := setVarHOLFinite (ofString "au") rvau { cpost_au with locals := c1.locals }
                  have heff_c2 : WorldEff s c2 [] [] wsGw := heff_cp_au.locals_clock _ _
                  have hc2_tx : c2.locals.lookup (ofString "tx") = some (.val (.word ptx)) := by
                    simp [c2, c1, setVarHOLFinite, hinv_m37.1, HolFiniteMapExact.lookup_update, FUPDATE,
                      show ofString "au" ≠ ofString "tx" by decide,
                      show ofString "aul" ≠ ofString "tx" by decide]
                  have hc2_au : c2.locals.lookup (ofString "au") = some rvau := by
                    simp [c2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  exact worldEff_seq hnt_au2 hcr_au2
                    (fun _ _ => worldEff_store_tx_pair_vvh heff_c2 hc2_tx hc2_au hsh_au 0 (Or.inl rfl) 272 (by decide) hptx_lo hptx_hi)
                    (fun c3 hc3 heff_c3 hnt_au3 hcr_au3 => by
                      have hc3_loc : c3.locals = c2.locals := by
                        have hcf := (evaluate_store_control_frame c2
                          (.op .add [.var .local (ofString "tx"), .const 272#64])
                          (.rfield 0 (.var .local (ofString "au")))).2.1
                        rwa [hc3] at hcf
                      exact worldEff_seq hnt_au3 hcr_au3
                        (fun _ _ => worldEff_store_tx_pair_vvh heff_c3
                          (by rw [hc3_loc]; exact hc2_tx) (by rw [hc3_loc]; exact hc2_au)
                          hsh_au 1 (Or.inr rfl) 280 (by decide) hptx_lo hptx_hi)
                        (fun c4 _ heff_c4 _ _ => worldEff_assign_local heff_c4 _ _)))
                hnt_au1 hcr_au1)
            hnt_auy hcr_auy)
        (fun _ _ _ => worldEff_skip heff_m37))
    (fun m38 hm38 heff_m38 hnt_39 hcr_39 => ?_)
  have hinv_m38 : dtxInv2_vvh ptx m38 := by
    refine ite_none_keeps (P := dtxInv2_vvh ptx) (fun y hm_y => ?_)
      (fun n hm_n => by rw [evaluateHOLFiniteState_skip] at hm_n; injection hm_n with _ h; subst h; exact hinv_m37) hm38
    refine decCall_none_inv_vvh (P := dtxInv2_vvh ptx) _ _ _ _ _ (fun rvaul cpost1 z1 _ hz1 => ?_) hm_y
    apply dtxInv2_resVar_other_vvh _ _ _ (by decide) (by decide) (by decide) (by decide)
    let c1_i := setVarHOLFinite (ofString "aul") rvaul { cpost1 with locals := m37.locals }
    have hi_c1 : dtxInv2_vvh ptx c1_i :=
      dtxInv2_setVar_other_vvh hinv_m37 (ofString "aul") rvaul (by decide) (by decide) (by decide) (by decide)
    refine decCall_none_inv_vvh (P := dtxInv2_vvh ptx) _ _ _ _ _ (fun rvau cpost2 z2 _ hz2 => ?_) hz1
    apply dtxInv2_resVar_other_vvh _ _ _ (by decide) (by decide) (by decide) (by decide)
    let c2_i := setVarHOLFinite (ofString "au") rvau { cpost2 with locals := c1_i.locals }
    have hi_c2 : dtxInv2_vvh ptx c2_i :=
      dtxInv2_setVar_other_vvh hi_c1 (ofString "au") rvau (by decide) (by decide) (by decide) (by decide)
    rw [evaluateHOLFiniteState_seq_line780] at hz2
    rcases hs1 : evaluateHOLFiniteState c2_i _ with ⟨r1, c3⟩; rw [hs1] at hz2
    cases r1 <;> [dsimp only at hz2; cases hz2]
    rw [evaluateHOLFiniteState_seq_line780] at hz2
    rcases hs2 : evaluateHOLFiniteState c3 _ with ⟨r2, c4⟩; rw [hs2] at hz2
    cases r2 <;> [dsimp only at hz2; cases hz2]
    exact dtxInv2_assign_k_vvh (dtxInv2_store_vvh (dtxInv2_store_vvh hi_c2 _ _ hs1) _ _ hs2) _ hz2
  -- y_parity / v (tx+288), r (tx+320), s (tx+352), return tx
  refine worldEff_seq hnt_39 hcr_39
    (fun hnt_cv1 hcr_cv1 => worldEff_call_u256_v_vvh heff_m38 _ hnt_cv1 hcr_cv1)
    (fun m39 hm39 heff_m39 hnt_40 hcr_40 => ?_)
  have hinv_m39 := dtxInv2_call_v_vvh hinv_m38 _ _ hm39
  refine worldEff_seq hnt_40 hcr_40
    (fun _ _ => worldEff_store_tx_v_vvh heff_m39 hinv_m39 288 (by decide) hptx_lo hptx_hi)
    (fun m40 hm40 heff_m40 hnt_41 hcr_41 => ?_)
  have hinv_m40 := dtxInv2_store_vvh hinv_m39 _ _ hm40
  refine worldEff_seq hnt_41 hcr_41
    (fun hnt_cv2 hcr_cv2 => worldEff_call_u256_v_vvh heff_m40 _ hnt_cv2 hcr_cv2)
    (fun m41 hm41 heff_m41 hnt_42 hcr_42 => ?_)
  have hinv_m41 := dtxInv2_call_v_vvh hinv_m40 _ _ hm41
  refine worldEff_seq hnt_42 hcr_42
    (fun _ _ => worldEff_store_tx_v_vvh heff_m41 hinv_m41 320 (by decide) hptx_lo hptx_hi)
    (fun m42 hm42 heff_m42 hnt_43 hcr_43 => ?_)
  have hinv_m42 := dtxInv2_store_vvh hinv_m41 _ _ hm42
  refine worldEff_seq hnt_43 hcr_43
    (fun hnt_cv3 hcr_cv3 => worldEff_call_u256_v_vvh heff_m42 _ hnt_cv3 hcr_cv3)
    (fun m43 hm43 heff_m43 hnt_44 hcr_44 => ?_)
  have hinv_m43 := dtxInv2_call_v_vvh hinv_m42 _ _ hm43
  refine worldEff_seq hnt_44 hcr_44
    (fun _ _ => worldEff_store_tx_v_vvh heff_m43 hinv_m43 352 (by decide) hptx_lo hptx_hi)
    (fun m44 _ heff_m44 _ _ => worldEff_return heff_m44 _)

private theorem worldEff_decode_transaction_vvh {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "decode_transaction") vals =
      some (sourceFnBody Guest.Software.guestFn_decode_transaction, s.locals, .one))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_transaction)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_transaction)).1) :
    WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_transaction)).2
      [] [] wsGw := by
  have _ := hl
  have heff0 : WorldEff s s [] [] wsGw := WorldEff.refl s [] [] wsGw hAR hc
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_decode_transaction,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_dec heff0 _ _ _ hnt (Or.inr (Or.inr (Or.inr hres))) (fun vtx hvtx _ hnt_1 hcr_1 => ?_)
  have hvtx_eq : vtx = .val (.word 0) := by simp [evalHOLExact] at hvtx; exact hvtx.symm
  subst hvtx_eq
  let m1 := setVarHOLFinite (ofString "tx") (.val (.word 0)) s
  have heff_m1 : WorldEff s m1 [] [] wsGw := heff0.locals_clock _ _
  refine worldEff_dec heff_m1 _ _ _ hnt_1 hcr_1 (fun vrc hvrc _ hnt_2 hcr_2 => ?_)
  have hvrc_eq : vrc = .val (.word 0) := by simp [evalHOLExact] at hvrc; exact hvrc.symm
  subst hvrc_eq
  let m2 := setVarHOLFinite (ofString "rc") (.val (.word 0)) m1
  have heff_m2 : WorldEff s m2 [] [] wsGw := heff_m1.locals_clock _ _
  refine worldEff_seq hnt_2 hcr_2
    (fun hnt_c hcr_c =>
      worldEff_handledCall heff_m2
        (some (.local, ofString "tx")) (ofString "RlpErr") (ofString "rc")
        (.raise (ofString "TxErr") (.op .add [.const 100, .var .local (ofString "rc")]))
        (ofString "decode_transaction_rlp") _
        (fun k _ hk => by cases hk; rfl)
        (by decide)
        _ _ _ lookup_decode_transaction_rlp_vvh
        (fun callee cvals _ hlc hnt_cb hres_cb =>
          heff_m2.trans_noBuf
            (WorldEff.from_locals_clock
              (worldEff_decode_transaction_rlp_vvh (callEntryStateHOLFinite m2 callee) cvals
                heff_m2.code (localsFree_arenaReady m2 callee _ heff_m2.arena)
                (by simpa [heff_m2.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
            ws_nil_sub_vvh ws_no_gb_vvh)
        (fun exVal cpost heff_cp _ _ =>
          worldEff_raise (heff_cp.locals_clock (m2.locals.update (ofString "rc", exVal)) cpost.clock) _ _)
        hnt_c hcr_c)
    (fun m3 _ heff_m3 _ _ => worldEff_return heff_m3 _)


/-! ## Section 5a: `worldOwned` Preservation, Fresh-Heap Disjointness, and `memW`/`memB` Helpers -/

private theorem wsGw_not_mem {g : String} (hg : ofString g ∉ wsGw.map ofString) {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)}
    (heff : WorldEff s post Rl B wsGw) :
    globN post g = globN s g :=
  globN_eq_of_lookup (heff.gw_kept (ofString g) hg)

private theorem fixedObjects_eq_of_wsGw {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hAs : ArenaReady s) (hWT : WorldTypedWith s S Nd)
    (heff : WorldEff s post [] [] wsGw) :
    fixedObjects post = fixedObjects s := by
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT
  have hdom_wr : ∀ a : BitVec 64, post.memory a ≠ s.memory a → s.memaddrs a := heff.out_dom
  have hlow : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 :=
    ⟨mem_low_eq_of_domain_writes hdom_wr hAs.1 (by rw [sourceBase_val]; omega),
     mem_low_eq_of_domain_writes hdom_wr hAs.1 (by rw [sourceBase_val]; omega)⟩
  have hfr_pos : ∀ a : BitVec 64, post.memory a ≠ s.memory a →
      (∃ j ∈ ([freeGap s] : List Ivl), CellHitsPos a.toNat j) ∨ CellHitsPos a.toNat (heapFree s) := by
    intro a hne
    rcases heff.cell_frame a hne with ⟨_, h, _⟩ | ⟨_, h, _⟩ | hfg | hhf
    · cases h
    · cases h
    · exact Or.inl ⟨freeGap s, List.mem_singleton.2 rfl, hfg⟩
    · exact Or.inr hhf
  have hu_wti_aligned : ∀ i ∈ worldTypedIvls s S Nd, Allocated s i → i.1 % 8 = 0 → i.2 % 8 = 0 →
      IvlUnhit s post i := by
    intro i _ hal hi1 hi2
    refine ivlUnhit_of_cellHitsPos hi1 hi2 hfr_pos (fun j hj => ?_) (disj_allocated_heapFree hAs.2 hal)
    simp only [List.mem_singleton] at hj; subst hj
    exact disj_allocated_freeGap hAs.2 hal
  have hu_fix_wti : ∀ i ∈ worldTypedIvls s S Nd, i ∈ fixedObjects s → i.2 ≠ 0 → IvlUnhit s post i := by
    intro i hwti hfi hpos
    rcases hF.1 i hfi with h0 | ⟨hal, hw⟩
    · exact absurd h0 hpos
    · exact hu_wti_aligned i hwti hal hw.1 hw.2.1
  have hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, IvlUnhit s post i := by
    intro t ht i hi
    have hal := ((hT.2.1 t ht).2 i hi).1
    have hw := ((hT.2.1 t ht).1.1 i hi).2
    refine hu_wti_aligned i ?_ hal hw.1 hw.2.1
    unfold worldTypedIvls
    apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
    apply List.mem_append.2; left; apply List.mem_append.2; left
    exact List.mem_flatMap.2 ⟨t, ht, hi⟩
  have hu_bo : globN s "bo" ≠ 0 → IvlUnhit s post (globN s "bo", 88) := fun hnz =>
    hu_fix_wti _
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
          exact List.mem_map.2 ⟨("bo", 88), by simp [typedRecords], by simp [hnz]⟩)
      (by simpa [hnz] using typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by simp [typedRecords]))
      (by simp)
  have hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 → IvlUnhit s post i := fun i hi h24 =>
    hu_fix_wti i
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; right; exact hi)
      (by unfold fixedObjects; apply List.mem_append.2; left; apply List.mem_append.2; right; exact hi)
      (by omega)
  have hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → IvlUnhit s post i := fun i hi hpos =>
    hu_fix_wti i
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; right; exact hi)
      (by unfold fixedObjects; exact List.mem_append.2 (Or.inr hi))
      hpos
  have hbo_g : globN post "bo" = globN s "bo" := wsGw_not_mem (by decide) heff
  have hba_g : globN post "bal_accounts" = globN s "bal_accounts" := wsGw_not_mem (by decide) heff
  have hj_g : globN post "journal" = globN s "journal" := wsGw_not_mem (by decide) heff
  have hjc_g : globN post "journal_cap" = globN s "journal_cap" := wsGw_not_mem (by decide) heff
  have hbo_eq := (blockOutObjects_eq_of_bo_unhit hAs.2 hF hbo_g
    hT.2.2.2.2.2.2.2.2.2.2.1 hu_bo hu_bo_lst).1
  have hbal_eq := (balObjects_eq_of_unhit hAs.2 hT hF hba_g hu_tab hu_bal hlow).1
  have hgb_eq : globalBuffers.map (fun gn => (globN post gn.1, if globN post gn.1 = 0 then 0 else gn.2)) =
      globalBuffers.map (fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) := by
    apply List.map_congr_left
    intro gn hgn
    have hg_eq : globN post gn.1 = globN s gn.1 := wsGw_not_mem (ws_no_gb_vvh gn hgn) heff
    rw [hg_eq]
  unfold fixedObjects
  rw [hgb_eq, hj_g, hjc_g, hbo_eq, hbal_eq]

private theorem htabFootprint_flatMap_eq {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hhtab : ∀ t ∈ S, htabFootprint post t = htabFootprint s t) :
    S.flatMap (htabFootprint post) = S.flatMap (htabFootprint s) := by
  induction S with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.flatMap_cons, hhtab t List.mem_cons_self,
      ih (fun t' ht' => hhtab t' (List.mem_cons_of_mem _ ht'))]

private theorem ivlsDisj_fresh_heap_worldOwned {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {iv : Ivl}
    (hAs : ArenaReady s) (hWT : WorldTypedWith s S Nd)
    (heff : WorldEff s post [] [] wsGw)
    (hnode : nodeExtents post Nd = nodeExtents s Nd)
    (hhtab : ∀ t ∈ S, htabFootprint post t = htabFootprint s t)
    (hin : Inside iv (globN s "heap_ptr") (globN post "heap_ptr")) :
    IvlsDisj [iv] (worldOwned post S Nd) := by
  have hfix : fixedObjects post = fixedObjects s := fixedObjects_eq_of_wsGw hAs hWT heff
  have htab_eq : S.flatMap (htabFootprint post) = S.flatMap (htabFootprint s) :=
    htabFootprint_flatMap_eq hhtab
  have hwo_eq : worldOwned post S Nd = worldOwned s S Nd := by
    unfold worldOwned
    rw [htab_eq, hfix, hnode]
  intro o ho j hj
  simp only [List.mem_singleton] at ho; subst ho
  rw [hwo_eq] at hj
  rcases InitECandidate.Solver.Wave8Contracts.M08.worldOwned_allocated hWT hj with hj0 | hal_j
  · exact Or.inr (Or.inl hj0)
  · exact disj_allocated_fresh_heap hAs.2 heff.arena.2 hal_j hin

private theorem memW_kept_of_worldEff_lt_hp {F : Type}
    {u u' : PanSemStateFiniteExact 64 F}
    (hAu : ArenaReady u)
    (heff : WorldEff u u' [] [] wsGw)
    {a : Nat} (ha : a + 8 ≤ globN u "heap_ptr") :
    memW u' a = memW u a := by
  have hhl : heapLimit < 2 ^ 64 := by decide
  have hhp_hi : globN u "heap_ptr" ≤ heapLimit := hAu.2.2.1
  have ha_lt : a < 2 ^ 64 := by omega
  unfold memW
  have hmem_eq : u'.memory (BitVec.ofNat 64 a) = u.memory (BitVec.ofNat 64 a) := by
    by_contra hne
    have hcases := heff.cell_frame (BitVec.ofNat 64 a) hne
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at hcases
    rcases hcases with ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, hfg1, _⟩ | ⟨_, hhf1, _⟩
    · cases h
    · cases h
    · have hsep : heapLimit ≤ scratchStart := by decide
      have hfmp := hAu.2.2.2.1
      unfold freeGap at hfg1; dsimp at hfg1; omega
    · unfold heapFree at hhf1; dsimp at hhf1; omega
  rw [hmem_eq]

private theorem memB_kept_of_worldEff_disj {F : Type}
    {u u' : PanSemStateFiniteExact 64 F}
    (hAu : ArenaReady u)
    (heff : WorldEff u u' [] [] wsGw)
    {P0 L0 : Nat} (hPL64 : P0 + L0 ≤ 2 ^ 64)
    (hdj : IvlsDisj [(P0, L0)] [(globN u "heap_ptr", scratchEnd - globN u "heap_ptr")])
    {b : Nat} (hb1 : P0 ≤ b) (hb2 : b < P0 + L0) :
    memB u' b = memB u b := by
  have hd : Disj (P0, L0) (globN u "heap_ptr", scratchEnd - globN u "heap_ptr") :=
    hdj _ (List.mem_singleton.2 rfl) _ (List.mem_singleton.2 rfl)
  by_contra hne
  have hb64 : b < 2 ^ 64 := by omega
  have hsep : heapLimit ≤ scratchStart := by decide
  have hhp_hi := hAu.2.2.1
  have hfmp_lo := hAu.2.2.2.1
  have hfmp_hi := hAu.2.2.2.2.1
  have hsp_hi := hAu.2.2.2.2.2.1
  rcases heff.byte_frame b hb64 hne with ⟨_, h, _⟩ | ⟨_, h, _⟩ | hfg | hhf
  · cases h
  · cases h
  · unfold InIvl freeGap at hfg
    rcases hd with h0 | h0 | hle | hge <;> (dsimp at *; omega)
  · unfold InIvl heapFree at hhf
    rcases hd with h0 | h0 | hle | hge <;> (dsimp at *; omega)

private theorem ivlsDisj_mono_hp {P0 L0 hp1 hp2 : Nat}
    (hle : hp1 ≤ hp2) (hhp2_se : hp2 ≤ scratchEnd)
    (hdj : IvlsDisj [(P0, L0)] [(hp1, scratchEnd - hp1)]) :
    IvlsDisj [(P0, L0)] [(hp2, scratchEnd - hp2)] := by
  intro o ho j hj
  simp only [List.mem_singleton] at ho hj; subst ho; subst hj
  have hd := hdj _ (List.mem_singleton.2 rfl) _ (List.mem_singleton.2 rfl)
  rcases hd with h0 | h0 | h1 | h2
  · exact Or.inl h0
  · exact Or.inr (Or.inl (by dsimp at h0 ⊢; omega))
  · exact Or.inr (Or.inr (Or.inl (by dsimp at h1 ⊢; omega)))
  · exact Or.inr (Or.inr (Or.inr (by dsimp at h2 ⊢; omega)))

private theorem input_subregion_worldEff_vvh {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaReady s) (heff : WorldEff s post [] [] wsGw)
    {P L p len : Nat} (hfit : P + L ≤ 2 ^ 64)
    (hdj : IvlsDisj [(P, L)] [(globN s "heap_ptr", scratchEnd - globN s "heap_ptr")])
    (hlo : P ≤ p) (hhi : p + len ≤ P + L) :
    p + len ≤ 2 ^ 64 ∧
      IvlsDisj [(p, len)] [(globN post "heap_ptr", scratchEnd - globN post "heap_ptr")] ∧
      ∀ j < len, memB post (p + j) = memB s (p + j) := by
  have hsub : IvlsDisj [(p, len)]
      [(globN s "heap_ptr", scratchEnd - globN s "heap_ptr")] := by
    intro i hi k hk
    simp only [List.mem_singleton] at hi
    subst hi
    exact disj_of_inside_left ⟨hlo, hhi⟩
      (hdj (P, L) (List.mem_singleton.2 rfl) k hk)
  have hhp : globN post "heap_ptr" ≤ scratchEnd := by
    have hh := heff.arena.2.2.1
    have hsep : heapLimit ≤ scratchEnd := by decide
    omega
  refine ⟨by omega, ivlsDisj_mono_hp heff.hp_lo hhp hsub, ?_⟩
  intro j hj
  exact memB_kept_of_worldEff_disj hAs heff hfit hdj (by omega) (by omega)

private theorem memW_store_word_exact {F : Type}
    {cur post : PanSemStateFiniteExact 64 F}
    {dstExp valExp : ExpHOL 64} {dst w : BitVec 64}
    (hG : GuestInv cur)
    (hdst : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) dstExp =
      some (.val (.word dst)))
    (hval : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp =
      some (.val (.word w)))
    (hflow : evaluateHOLFiniteState cur (.store dstExp valExp) = (none, post)) :
    memW post dst.toNat = w.toNat ∧
    (∀ a : Nat, a < 2 ^ 64 → a ≠ dst.toNat → memW post a = memW cur a) := by
  rw [evaluateHOLFiniteState_store] at hflow
  simp only [hdst, hval, flattenHOL, panMemStoresHOL, panMemStoreHOL] at hflow
  by_cases hd : cur.memaddrs dst
  · simp only [hd, ↓reduceIte, Prod.mk.injEq] at hflow
    obtain ⟨-, rfl⟩ := hflow
    refine ⟨?_, ?_⟩
    · unfold memW
      have hbv : BitVec.ofNat 64 dst.toNat = dst := by simp
      rw [hbv]; simp
    · intro a ha64 hne
      unfold memW
      have hbne : BitVec.ofNat 64 a ≠ dst := by
        intro heq
        apply hne
        have h := congrArg BitVec.toNat heq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha64] at h
        exact h
      simp [hbne]
  · simp [hd] at hflow

private theorem memW_store_disj {F : Type}
    {cur post : PanSemStateFiniteExact 64 F}
    {dstExp valExp : ExpHOL 64} {dst : BitVec 64} {sz : Nat}
    (hG : GuestInv cur)
    (hdst : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) dstExp =
      some (.val (.word dst)))
    (hsz : ∀ v, @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp =
      some v → 8 * (flattenHOL v).length ≤ sz)
    (hfit : dst.toNat + sz < 2 ^ 64)
    (hflow : evaluateHOLFiniteState cur (.store dstExp valExp) = (none, post))
    {a : Nat} (ha64 : a < 2 ^ 64) (hout : a + 8 ≤ dst.toNat ∨ dst.toNat + sz ≤ a) :
    memW post a = memW cur a := by
  rw [evaluateHOLFiniteState_store] at hflow
  simp only [hdst] at hflow
  rcases hv : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp with _ | val
  · simp [hv] at hflow
  · simp only [hv] at hflow
    split at hflow
    · rename_i mem' hmem
      simp only [Prod.mk.injEq] at hflow
      obtain ⟨-, rfl⟩ := hflow
      have hlen := hsz val hv
      obtain ⟨hc, _⟩ := @panMemStores_eff_vvh cur.memaddrs (fun x => Classical.propDecidable (cur.memaddrs x))
        cur.be hG.memaddrs (flattenHOL val) dst cur.memory mem' (by omega) hmem
      unfold memW; dsimp only
      have hmem_eq : mem' (BitVec.ofNat 64 a) = cur.memory (BitVec.ofNat 64 a) := by
        by_contra hne
        obtain ⟨_, hx1, hx2⟩ := hc (BitVec.ofNat 64 a) hne
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha64] at hx1 hx2
        omega
      rw [hmem_eq]
    · simp at hflow

private theorem memW_call0_memzero_zero_vvh {F : Type}
    {cur post : PanSemStateFiniteExact 64 F}
    {dstExp nExp : ExpHOL 64} {dst n : BitVec 64}
    (hc : cur.code = originalRuntimeCode) (hAR : ArenaReady cur)
    (hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a))
      [dstExp, nExp] = some [.val (.word dst), .val (.word n)])
    (hflow : evaluateHOLFiniteState cur
      (.call (some (none, none)) (ofString "memzero") [dstExp, nExp]) = (none, post)) :
    ∀ a : Nat, dst.toNat ≤ a → a + 8 ≤ dst.toNat + n.toNat → a % 8 = 0 → memW post a = 0 := by
  have hzv : InitECandidate.Solver.Wave8GuestInv.FunSpec ArenaReady
      (fun st r' post' => ∀ v, r' = some (.returned v) → ∀ a, locN st "dst" ≤ a →
        a + 8 ≤ locN st "dst" + locN st "n" → a % 8 = 0 → memW post' a = 0)
      (ofString "memzero") := InitECandidate.Solver.Wave8Contracts.M29.zv_memzero
  obtain ⟨params, body, ret, hlook, hspec⟩ := hzv
  rw [evaluateHOLFiniteState_call] at hflow
  rw [hargs] at hflow
  dsimp only at hflow
  rcases hl : lookupCodeHOLFinite cur.code.lookup (ofString "memzero")
      [.val (.word dst), .val (.word n)] with _ | ⟨body', callee, ret'⟩
  · simp [hl] at hflow
  · simp only [hl] at hflow
    by_cases hz : cur.clock = 0
    · simp [hz] at hflow
    · rw [if_neg hz] at hflow
      have hsame := lookupCodeHOLFinite_installed_body cur.code.lookup (ofString "memzero")
        params body body' ret ret' [.val (.word dst), .val (.word n)] callee
        (by rw [hc]; exact hlook) hl
      subst hsame
      have hret_eq := lookupCodeHOLFinite_installed_return cur (ofString "memzero")
        params body' body' ret ret' [.val (.word dst), .val (.word n)] callee
        (by rw [hc]; exact hlook) hl
      subst hret_eq
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "memzero")
          [.val (.word dst), .val (.word n)] = some (body', callee, ret') := by
        simpa [hc] using hl
      have hl_mz : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "memzero")
          [.val (.word dst), .val (.word n)] =
          some (sourceFnBody Guest.Software.guestFn_memzero, callee, .one) := by
        have hlook_eq := hlook
        rw [lookup_memzero] at hlook_eq
        simp only [Option.some.injEq, Prod.mk.injEq] at hlook_eq
        rcases hlook_eq with ⟨_, hbody_mz, hret_mz⟩
        subst hbody_mz hret_mz; exact hl_orig
      obtain ⟨dst0, n0, hveq, hdst_lk, hn_lk⟩ := lookupCode_two_words (by decide) lookup_memzero hl_mz
      simp only [List.cons.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq, and_true] at hveq
      obtain ⟨rfl, rfl⟩ := hveq
      let entry := callEntryStateHOLFinite cur callee
      have hAR_e : ArenaReady entry := localsFree_arenaReady cur callee _ hAR
      rcases hrun : evaluateHOLFiniteState entry body' with ⟨rc, cpost⟩
      dsimp only [entry] at hrun
      rw [hrun] at hflow
      rcases rc with _ | (_ | _ | _ | _ | rv | _ | _) <;> dsimp only at hflow <;> try simp at hflow
      split at hflow <;> simp at hflow
      obtain ⟨-, rfl⟩ := hflow
      have hzero := hspec entry hc hAR_e
        ⟨[.val (.word dst), .val (.word n)], by simpa [entry, callEntryStateHOLFinite] using hl_orig⟩
        (by rw [hrun]; simp) rv (by rw [hrun])
      rw [hrun] at hzero
      have hdst_loc : locN entry "dst" = dst.toNat := by simp [locN, entry, callEntryStateHOLFinite, hdst_lk]
      have hn_loc : locN entry "n" = n.toNat := by simp [locN, entry, callEntryStateHOLFinite, hn_lk]
      rw [hdst_loc, hn_loc] at hzero
      intro a ha_lo ha_hi ha8
      simpa [emptyLocalsHOLFinite, fixClockHOLFinite, memW] using hzero a ha_lo ha_hi ha8

/-! ### Section 5b: `rlp_read_length` Byte-Invariance, `rlp_item_total` vs `rlp_item_total_unchecked` Agreement, and Strengthened `rlp_list_to_slices` -/

private theorem lookup_rlp_read_length_vvh :
    originalRuntimeCode.lookup (ofString "rlp_read_length") =
      some ([(ofString "p", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_read_length, .one) :=
  lookup_of_guestAst_getElem 106 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_read_length) rfl

private theorem lookup_rlp_item_total_unchecked_vvh :
    originalRuntimeCode.lookup (ofString "rlp_item_total_unchecked") =
      some ([(ofString "p", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_item_total_unchecked, .one) :=
  lookup_of_guestAst_getElem 114 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_item_total_unchecked) rfl

private theorem loadByte_eq_memB_vvh {F : Type}
    (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) (v : ValueHOL 64)
    (hv : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) (.loadByte e) =
      some v) :
    ∃ a : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e =
        some (.val (.word a)) ∧
      s.memaddrs (panByteAlignHOL (width := 64) a) ∧
      v = .val (.word (BitVec.ofNat 64 (memB s a.toNat))) := by
  simp only [evalHOLExact] at hv
  split at hv
  · rename_i a ha
    dsimp only [panMemLoadByteHOL] at hv
    split at hv
    · rename_i hdom
      simp only [Option.map_some, Option.some.injEq] at hv
      refine ⟨a, ha, hdom, ?_⟩
      rw [← hv]
      unfold memB
      have ha_bv : BitVec.ofNat 64 a.toNat = a := by simp
      rw [ha_bv]
    · simp at hv
  · simp at hv

private def rlpReadLenAcc (f : Nat → Nat) : Nat → Nat → BitVec 64 → BitVec 64
  | 0, _, acc => acc
  | k + 1, idx, acc => rlpReadLenAcc f k (idx + 1) ((acc <<< 8) ||| BitVec.ofNat 64 (f idx))

private theorem rlpReadLenAcc_congr {f g : Nat → Nat} :
    ∀ (k idx : Nat) (acc : BitVec 64),
      (∀ j, idx ≤ j → j < idx + k → f j = g j) →
      rlpReadLenAcc f k idx acc = rlpReadLenAcc g k idx acc
  | 0, _, _, _ => rfl
  | k + 1, idx, acc, hfg => by
    unfold rlpReadLenAcc
    rw [hfg idx le_rfl (by omega)]
    exact rlpReadLenAcc_congr k (idx + 1) _ (fun j hj1 hj2 => hfg j (by omega) (by omega))

private def rrlCond_vvh : ExpHOL 64 :=
  .cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))

private def rrlBody_vvh : ProgHOL 64 :=
  .seq
    (.assign .local (ofString "v")
      (.op .or [.shift .lsl (.var .local (ofString "v")) (.const 8#64),
        .loadByte (.op .add [.var .local (ofString "p"), .var .local (ofString "i")])]))
    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))

private theorem rrlBody_no_bc_ret_vvh {F : Type} (st : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState st rrlBody_vvh).1 ≠ some .break ∧
    (evaluateHOLFiniteState st rrlBody_vvh).1 ≠ some .continue ∧
    (∀ rv, (evaluateHOLFiniteState st rrlBody_vvh).1 ≠ some (.returned rv)) := by
  unfold rrlBody_vvh
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
  split
  · simp
  · split
    · dsimp only
      rw [evaluateHOLFiniteState_assign]
      split <;> [simp; (split <;> simp)]
    · simp

private theorem while_rrl_no_return_vvh {F : Type} (rv : ValueHOL 64) :
    ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock ≤ k →
      (evaluateHOLFiniteState st (.while rrlCond_vvh rrlBody_vvh)).1 ≠ some (.returned rv) := by
  intro k
  induction k with
  | zero =>
    intro st hck; rw [evaluateHOLFiniteState_while_fixClockRewrite]
    rcases hc : @evalHOLFinite 64 F _ st (fun a => Classical.propDecidable (st.memaddrs a)) rrlCond_vvh with _ | cv
    · simp
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
      by_cases hw0 : cw = 0#64
      · subst hw0; simp
      · rw [if_neg hw0]; rw [if_pos (by omega : st.clock = 0)]; simp
  | succ k ih =>
    intro st hck; rw [evaluateHOLFiniteState_while_fixClockRewrite]
    rcases hc : @evalHOLFinite 64 F _ st (fun a => Classical.propDecidable (st.memaddrs a)) rrlCond_vvh with _ | cv
    · simp
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
      by_cases hw0 : cw = 0#64
      · subst hw0; simp
      · rw [if_neg hw0]
        by_cases hk0 : st.clock = 0
        · rw [if_pos hk0]; simp
        · rw [if_neg hk0]
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) rrlBody_vvh
          have hb_nr := (rrlBody_no_bc_ret_vvh (decClockHOLFinite st)).2.2 rv
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite st) rrlBody_vvh with ⟨r1, m1⟩
          simp only [hbr] at rem hb_nr ⊢
          cases r1 with
          | none => exact ih m1 (by change m1.clock ≤ st.clock - 1 at rem; omega)
          | some r1 =>
            cases r1 with
            | «continue» => exact ih m1 (by change m1.clock ≤ st.clock - 1 at rem; omega)
            | «break» => simp
            | returned v' =>
              intro heq; injection heq with heq'; injection heq' with heq''; subst heq''
              exact hb_nr rfl
            | _ => simp

private def RrlInv_vvh {F : Type} (s0 : PanSemStateFiniteExact 64 F) (P N : BitVec 64)
    (st : PanSemStateFiniteExact 64 F) : Prop :=
  st.memory = s0.memory ∧ st.memaddrs = s0.memaddrs ∧ st.be = s0.be ∧
  ∃ (wi wv : BitVec 64),
    st.locals.lookup (ofString "p") = some (.val (.word P)) ∧
    st.locals.lookup (ofString "n") = some (.val (.word N)) ∧
    st.locals.lookup (ofString "i") = some (.val (.word wi)) ∧
    st.locals.lookup (ofString "v") = some (.val (.word wv)) ∧
    wi.toNat ≤ N.toNat ∧
    rlpReadLenAcc (fun k => memB s0 (P.toNat + k)) (N.toNat - wi.toNat) wi.toNat wv =
      rlpReadLenAcc (fun k => memB s0 (P.toNat + k)) N.toNat 0 0#64

private theorem while_rrlInv_vvh {F : Type} (s0 : PanSemStateFiniteExact 64 F) (P N : BitVec 64)
    (hfit : P.toNat + N.toNat ≤ 2 ^ 64)
    (k : Nat) (st post : PanSemStateFiniteExact 64 F)
    (hclk : st.clock ≤ k) (hinv : RrlInv_vvh s0 P N st)
    (hrun : evaluateHOLFiniteState st (.while rrlCond_vvh rrlBody_vvh) = (none, post)) :
    post.locals.lookup (ofString "v") =
      some (.val (.word (rlpReadLenAcc (fun j => memB s0 (P.toNat + j)) N.toNat 0 0#64))) := by
  induction k generalizing st with
  | zero =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · split at hrun <;> [simp at hrun; omega]
      · rename_i hnotnz
        have hcw0 : cw = 0 := Classical.not_not.1 hnotnz
        subst hcw0; simp at hrun; subst hrun
        obtain ⟨_, _, _, wi, wv, _, hn, hi, hv, hle, hacc⟩ := hinv
        have hge : N.toNat ≤ wi.toNat := by
          simp [evalHOLFinite, rrlCond_vvh, evalHOLExact, hi, hn, Compiler.Encoders.Asm.wordCmpHOL] at hcond
          omega
        have heq : N.toNat - wi.toNat = 0 := by omega
        rw [heq] at hacc
        dsimp [rlpReadLenAcc] at hacc
        rw [hv, hacc]
    · simp at hrun
  | succ k ih =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · rename_i hnz
        rename_i hclk0
        split at hrun
        · simp at hrun
        · rename_i hnz_clk
          dsimp only at hrun
          rw [fixClockHOLFinite_evaluateState] at hrun
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) rrlBody_vvh
          have hbc := rrlBody_no_bc_ret_vvh (decClockHOLFinite st)
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite st) rrlBody_vvh with ⟨r1, mid⟩
          rw [hbr] at hrun rem hbc
          cases r1 with
          | none =>
            obtain ⟨hmem, hdom, hbe, wi, wv, hp, hn, hi, hv, hle, hacc⟩ := hinv
            have hlt : wi.toNat < N.toNat := by
              simp [evalHOLFinite, rrlCond_vvh, evalHOLExact, hi, hn, Compiler.Encoders.Asm.wordCmpHOL] at hcond
              by_contra hge
              have hge' : ¬ (wi < N) := by rw [BitVec.lt_def]; omega
              simp [hge'] at hcond
              exact hnz hcond.symm
            let sd := decClockHOLFinite st
            have hbr' := hbr
            unfold rrlBody_vvh at hbr'
            rw [evaluateHOLFiniteState_seq_line780] at hbr'
            rcases ha1 : evaluateHOLFiniteState sd
                (.assign .local (ofString "v")
                  (.op .or [.shift .lsl (.var .local (ofString "v")) (.const 8#64),
                    .loadByte (.op .add [.var .local (ofString "p"), .var .local (ofString "i")])])) with ⟨ra1, u1⟩
            rw [ha1] at hbr'
            cases ra1 with
            | some _ => simp at hbr'
            | none =>
              dsimp only at hbr'
              rw [evaluateHOLFiniteState_assign] at ha1
              rcases he1 : @evalHOLExact 64 F _ sd.toExact (fun a => Classical.propDecidable (sd.memaddrs a))
                  (.op .or [.shift .lsl (.var .local (ofString "v")) (.const 8#64),
                    .loadByte (.op .add [.var .local (ofString "p"), .var .local (ofString "i")])]) with _ | ve1
              · simp [he1] at ha1
              · rw [he1] at ha1
                dsimp only at ha1
                split at ha1
                · simp only [Prod.mk.injEq] at ha1
                  obtain ⟨-, rfl⟩ := ha1
                  have hsd_p : sd.locals.lookup (ofString "p") = some (.val (.word P)) := hp
                  have hsd_i : sd.locals.lookup (ofString "i") = some (.val (.word wi)) := hi
                  have hsd_v : sd.locals.lookup (ofString "v") = some (.val (.word wv)) := hv
                  rcases hlb : @evalHOLExact 64 F _ sd.toExact (fun a => Classical.propDecidable (sd.memaddrs a))
                      (.loadByte (.op .add [.var .local (ofString "p"), .var .local (ofString "i")])) with _ | vlb
                  · simp [evalHOLExact, evalListHOLExact, hsd_p, hsd_i, hsd_v, wordShiftHOL, wordOpHOL, wordOp,
                      valueIsWord, valueWord] at hlb he1
                    rw [hlb] at he1
                    simp at he1
                  · obtain ⟨addr, haddr, _, rfl⟩ := loadByte_eq_memB_vvh sd _ vlb hlb
                    simp [evalHOLExact, evalListHOLExact, hsd_p, hsd_i, wordOpHOL, wordOp, valueIsWord, valueWord] at haddr
                    subst haddr
                    have hpwi_nat : (P + wi).toNat = P.toNat + wi.toNat :=
                      BitVec.toNat_add_of_lt (by omega)
                    have hmemB_sd : memB sd (P + wi).toNat = memB s0 (P.toNat + wi.toNat) := by
                      rw [hpwi_nat]; unfold memB
                      have hsd_mem : sd.memory = s0.memory := hmem
                      have hsd_be : sd.be = s0.be := hbe
                      rw [hsd_mem, hsd_be]
                    have hve1 : ve1 = .val (.word ((wv <<< 8) ||| BitVec.ofNat 64 (memB s0 (P.toNat + wi.toNat)))) := by
                      rw [← hmemB_sd]
                      simp [evalHOLExact, evalListHOLExact, hsd_p, hsd_i, hsd_v, wordShiftHOL, wordOpHOL, wordOp,
                        valueIsWord, valueWord] at hlb he1
                      obtain ⟨b8, hb8, hb8_eq⟩ := hlb
                      rw [hb8] at he1
                      simp [wordOpHOL, wordOp, valueIsWord, valueWord] at he1
                      rw [← he1, hb8_eq, ← BitVec.toNat_add, hpwi_nat]
                      congr 2
                      change (wv <<< 8) ||| (BitVec.ofNat 64 (memB sd (P.toNat + wi.toNat)) ||| 0#64) = _
                      simp
                    subst hve1
                    let wv' := (wv <<< 8) ||| BitVec.ofNat 64 (memB s0 (P.toNat + wi.toNat))
                    let u1' := setKvarHOLFinite .local (ofString "v") (.val (.word wv')) sd
                    change evaluateHOLFiniteState u1' _ = (none, mid) at hbr'
                    have hu1_i : u1'.locals.lookup (ofString "i") = some (.val (.word wi)) := by
                      simp [u1', setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsd_i,
                        show ofString "v" ≠ ofString "i" by decide]
                    rw [evaluateHOLFiniteState_assign] at hbr'
                    simp [evalHOLExact, evalListHOLExact, hu1_i, wordOpHOL, wordOp, valueIsWord, valueWord,
                      isValidValueHOLFinite, lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL] at hbr'
                    subst hbr'
                    have h1_nat : (1#64 : BitVec 64).toNat = 1 := rfl
                    have hwi1 : (wi + 1#64).toNat = wi.toNat + 1 := by
                      rw [BitVec.toNat_add_of_lt (by rw [h1_nat]; have := N.isLt; omega), h1_nat]
                    have hrem_eq : N.toNat - wi.toNat = (N.toNat - (wi.toNat + 1)) + 1 := by omega
                    rw [hrem_eq] at hacc
                    dsimp [rlpReadLenAcc] at hacc
                    have hclk_next :
                        (setKvarHOLFinite .local (ofString "i") (.val (.word (wi + 1#64))) u1').clock ≤ k := by
                      have hsd_clk : sd.clock = st.clock - 1 := rfl
                      have hu2_clk :
                          (setKvarHOLFinite .local (ofString "i") (.val (.word (wi + 1#64))) u1').clock ≤ sd.clock := rem
                      omega
                    refine ih _ hclk_next ?_ hrun
                    refine ⟨hmem, hdom, hbe, wi + 1#64, wv', ?_, ?_, ?_, ?_, by omega, by rw [hwi1]; exact hacc⟩
                    · simp [u1', setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsd_p,
                        show ofString "i" ≠ ofString "p" by decide, show ofString "v" ≠ ofString "p" by decide]
                    · simp [u1', setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                        show sd.locals.lookup (ofString "n") = some (.val (.word N)) from hn,
                        show ofString "i" ≠ ofString "n" by decide, show ofString "v" ≠ ofString "n" by decide]
                    · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                    · simp [u1', setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                        show ofString "i" ≠ ofString "v" by decide]
                · simp at ha1
          | some r1 =>
            cases r1 with
            | «continue» => exact absurd rfl hbc.2.1
            | «break» => exact absurd rfl hbc.1
            | _ => simp at hrun
      · rename_i hnotnz
        have hcw0 : cw = 0 := Classical.not_not.1 hnotnz
        subst hcw0; simp at hrun; subst hrun
        obtain ⟨_, _, _, wi, wv, _, hn, hi, hv, hle, hacc⟩ := hinv
        have hge : N.toNat ≤ wi.toNat := by
          simp [evalHOLFinite, rrlCond_vvh, evalHOLExact, hi, hn, Compiler.Encoders.Asm.wordCmpHOL] at hcond
          omega
        have heq : N.toNat - wi.toNat = 0 := by omega
        rw [heq] at hacc
        dsimp [rlpReadLenAcc] at hacc
        rw [hv, hacc]
    · simp at hrun

private theorem rlp_read_length_ret_eq_acc_vvh {F : Type}
    (e : PanSemStateFiniteExact 64 F) (hcode : e.code = originalRuntimeCode)
    (P N : BitVec 64) (hfit : P.toNat + N.toNat ≤ 2 ^ 64)
    (hp : e.locals.lookup (ofString "p") = some (.val (.word P)))
    (hn : e.locals.lookup (ofString "n") = some (.val (.word N)))
    (rv : ValueHOL 64)
    (hret : (evaluateHOLFiniteState e (sourceFnBody Guest.Software.guestFn_rlp_read_length)).1 =
      some (.returned rv)) :
    rv = .val (.word (rlpReadLenAcc (fun j => memB e (P.toNat + j)) N.toNat 0 0#64)) := by
  revert rv hret
  change RetOK_vvh (fun rv => rv = .val (.word (rlpReadLenAcc (fun j => memB e (P.toNat + j)) N.toNat 0 0#64))) e
    (sourceFnBody Guest.Software.guestFn_rlp_read_length)
  have hbody : sourceFnBody Guest.Software.guestFn_rlp_read_length =
      .seq
        (.ite (.op .and
            [.cmp .notEqual (.const 0#64) (.cmp .lower (.const 1#64) (.var .local (ofString "n"))),
             .cmp .notEqual (.const 0#64) (.cmp .equal (.loadByte (.var .local (ofString "p"))) (.const 0#64))])
          (.call (some (none, none)) (ofString "rlp_fail") [.const 2#64]) .skip)
        (.dec (ofString "v") .one (.const 0#64)
          (.dec (ofString "i") .one (.const 0#64)
            (.seq (.while rrlCond_vvh rrlBody_vvh)
              (.return (.var .local (ofString "v")))))) := rfl
  rw [hbody]
  refine R_guard_vvh hcode (fun _ _ _ => ?_)
  refine R_dec_vvh (fun vv hvv _ => ?_)
  have hvv_eq : vv = .val (.word 0#64) := by simp [evalHOLExact] at hvv; exact hvv.symm
  subst hvv_eq
  refine R_dec_vvh (fun vi hvi _ => ?_)
  have hvi_eq : vi = .val (.word 0#64) := by simp [evalHOLExact] at hvi; exact hvi.symm
  subst hvi_eq
  let e2 := setVarHOLFinite (ofString "i") (.val (.word 0#64))
    (setVarHOLFinite (ofString "v") (.val (.word 0#64)) e)
  refine R_seq_vvh (fun rv hw => absurd hw (while_rrl_no_return_vvh rv e2.clock e2 le_rfl))
    (fun mid hmid => ?_)
  have hinv2 : RrlInv_vvh e P N e2 := by
    refine ⟨rfl, rfl, rfl, 0#64, 0#64, ?_, ?_, ?_, ?_, by simp, by simp⟩
    · simp [e2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp,
        show ofString "i" ≠ ofString "p" by decide, show ofString "v" ≠ ofString "p" by decide]
    · simp [e2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
        show ofString "i" ≠ ofString "n" by decide, show ofString "v" ≠ ofString "n" by decide]
    · simp [e2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · simp [e2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "i" ≠ ofString "v" by decide]
  have hm_v := while_rrlInv_vvh e P N hfit e2.clock e2 mid le_rfl hinv2 hmid
  refine R_ret_vvh (fun v hv => ?_)
  simp [evalHOLExact, hm_v] at hv
  exact hv.symm

private theorem callee_p_n_vvh {fname : MlS} {body0 : ProgHOL 64} {rs0 : ShapeHOL}
    (hlook : originalRuntimeCode.lookup fname =
      some ([(ofString "p", .one), (ofString "n", .one)], body0, rs0))
    (v1 v2 : ValueHOL 64) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (rs : ShapeHOL)
    (hl : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup fname [v1, v2] =
      some (body, callee, rs)) :
    body = body0 ∧ callee.lookup (ofString "p") = some v1 ∧ callee.lookup (ofString "n") = some v2 := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
  split at hl
  · simp at hl
  · rename_i b cl r heq
    simp only [Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl, rfl⟩ := hl
    simp only [lookupCodeHOLExact, hlook] at heq
    split at heq
    · simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      refine ⟨rfl, ?_, by simp⟩
      simp [List.zip, List.foldl, show ofString "p" ≠ ofString "n" by decide]
    · simp at heq

private theorem callee_one_p_vvh {fname : MlS} {body0 : ProgHOL 64} {rs0 : ShapeHOL}
    (hlook : originalRuntimeCode.lookup fname =
      some ([(ofString "p", .one)], body0, rs0))
    (v1 : ValueHOL 64) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (rs : ShapeHOL)
    (hl : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup fname [v1] =
      some (body, callee, rs)) :
    body = body0 ∧ callee.lookup (ofString "p") = some v1 := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
  split at hl
  · simp at hl
  · rename_i b cl r heq
    simp only [Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl, rfl⟩ := hl
    simp only [lookupCodeHOLExact, hlook] at heq
    split at heq
    · simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact ⟨rfl, by simp [List.zip, List.foldl]⟩
    · simp at heq

private def HdrTotalSpec_vvh {F : Type} (s0 : PanSemStateFiniteExact 64 F) (P L : BitVec 64) (v : ValueHOL 64) : Prop :=
  ∃ hl pl flag : BitVec 64,
    v = hval_vvh hl pl flag ∧
    1 ≤ hl.toNat + pl.toNat ∧
    hl.toNat + pl.toNat ≤ L.toNat ∧
    ∀ e2 : PanSemStateFiniteExact 64 F,
      e2.code = originalRuntimeCode →
      e2.locals.lookup (ofString "p") = some (.val (.word P)) →
      (∀ j < L.toNat, memB e2 (P.toNat + j) = memB s0 (P.toNat + j)) →
      ∀ rv2 : ValueHOL 64,
        (evaluateHOLFiniteState e2 (sourceFnBody Guest.Software.guestFn_rlp_item_total_unchecked)).1 =
          some (.returned rv2) →
        rv2 = .val (.word (hl + pl))

private theorem rlp_item_header_agree_unchecked_vvh {F : Type}
    (e1 : PanSemStateFiniteExact 64 F) (hcode1 : e1.code = originalRuntimeCode)
    (P L : BitVec 64) (hfit : P.toNat + L.toNat ≤ 2 ^ 64)
    (hp1 : e1.locals.lookup (ofString "p") = some (.val (.word P)))
    (hl1 : e1.locals.lookup (ofString "len") = some (.val (.word L))) :
    RetOK_vvh (HdrTotalSpec_vvh e1 P L) e1 (sourceFnBody Guest.Software.guestFn_rlp_item_header) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_item_header,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine R_guard_vvh hcode1 (fun w hw hw0 => ?_)
  have hL : L ≠ 0 := by
    intro h; subst h; simp [evalHOLExact, hl1, Compiler.Encoders.Asm.wordCmpHOL] at hw; subst hw0; simp at hw
  have hL_pos : 0 < L.toNat := by
    have : L.toNat ≠ 0 := fun h => hL (BitVec.eq_of_toNat_eq (by simpa using h))
    omega
  have hL1 := toNat_sub_one_vvh L hL
  refine R_dec_vvh (fun vb hvb _ => ?_)
  obtain ⟨P', ha1, _, rfl⟩ := loadByte_eq_memB_vvh e1 _ vb hvb
  simp only [evalHOLExact, PanSemStateFiniteExact.toExact, hp1, Option.some.injEq, ValueHOL.val.injEq,
    HolWordLab.word.injEq] at ha1
  subst ha1
  let B : BitVec 64 := BitVec.ofNat 64 (memB e1 P.toNat)
  set s1 := setVarHOLFinite (ofString "b") (.val (.word B)) e1 with hs1
  have hs1_b : s1.locals.lookup (ofString "b") = some (.val (.word B)) := by
    simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_p : s1.locals.lookup (ofString "p") = some (.val (.word P)) := by
    simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp1,
      show ofString "b" ≠ ofString "p" by decide]
  have hs1_l : s1.locals.lookup (ofString "len") = some (.val (.word L)) := by
    simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl1,
      show ofString "b" ≠ ofString "len" by decide]
  have hc_s1 : s1.code = originalRuntimeCode := hcode1
  -- Branch 1: B < 128
  refine R_branch_vvh (by rfl) (fun w1 hw1 hw1_nz => R_ret_vvh (fun v hv => ?_)) (fun w1 hw1 hw1_0 => ?_)
  · have hB_lt128 : B < 128#64 := by
      simp [evalHOLExact, hs1_b, Compiler.Encoders.Asm.wordCmpHOL] at hw1
      by_contra hge; simp [hge] at hw1; exact hw1_nz hw1.symm
    simp [evalHOLExact, evalListHOLExact] at hv; subst hv
    refine ⟨0#64, 1#64, 0#64, rfl, by simp, by simp; omega, ?_⟩
    intro e2 hc2 hp2 hbytes rv2 hret2
    revert rv2 hret2
    change RetOK_vvh (fun rv2 => rv2 = .val (.word (0#64 + 1#64))) e2
      (sourceFnBody Guest.Software.guestFn_rlp_item_total_unchecked)
    dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_item_total_unchecked,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    refine R_dec_vvh (fun vb2 hvb2 _ => ?_)
    obtain ⟨P2', ha2, _, rfl⟩ := loadByte_eq_memB_vvh e2 _ vb2 hvb2
    simp only [evalHOLExact, PanSemStateFiniteExact.toExact, hp2, Option.some.injEq, ValueHOL.val.injEq,
      HolWordLab.word.injEq] at ha2; subst ha2
    have hb2_eq : BitVec.ofNat 64 (memB e2 P.toNat) = B := by
      have h0 := hbytes 0 hL_pos; simp at h0; rw [h0]
    rw [hb2_eq]
    refine R_branch_vvh (by rfl) (fun _ _ _ => R_ret_vvh (fun v2 hv2 => ?_)) (fun w2' hw2' hw2'_0 => ?_)
    · simp [evalHOLExact] at hv2; exact hv2.symm
    · simp [evalHOLExact, lk_set'_vvh, Compiler.Encoders.Asm.wordCmpHOL, hB_lt128] at hw2'
      subst hw2'_0; simp at hw2'
  have hB_ge128 : ¬ (B < 128#64) := by
    simp [evalHOLExact, hs1_b, Compiler.Encoders.Asm.wordCmpHOL] at hw1
    subst hw1_0; intro hlt; simp [hlt] at hw1
  -- Branch 2: B ≤ 183 (183 notLower B)
  refine R_branch_vvh (by rfl) (fun w2 hw2 hw2_nz => R_dec_vvh (fun vn hvn _ => ?_)) (fun w2 hw2 hw2_0 => ?_)
  · have hB_le183 : B ≤ 183#64 := by
      simp [evalHOLExact, hs1_b, Compiler.Encoders.Asm.wordCmpHOL] at hw2
      by_contra hgt
      have hnot : ¬ (B ≤ 183#64) := hgt
      simp [hnot] at hw2
      exact hw2_nz hw2.symm
    simp [evalHOLExact, evalListHOLExact, hs1_b, wordOpHOL, wordOp, valueIsWord, valueWord] at hvn; subst hvn
    set s2 := setVarHOLFinite (ofString "n") (.val (.word (B - 128#64))) s1 with hs2
    have hc_s2 : s2.code = originalRuntimeCode := hcode1
    refine R_guard_vvh hc_s2 (fun wg hwg hwg0 => ?_)
    have hN : (B - 128#64).toNat ≤ L.toNat - 1 := by
      simp [evalHOLExact, evalListHOLExact, hs2, lk_set_vvh, lk_set'_vvh,
        show ofString "n" ≠ ofString "len" by decide, hs1_l, wordOpHOL, wordOp, valueIsWord,
        valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hwg
      subst hwg0; by_contra hc
      have : L - 1#64 < B - 128#64 := by rw [BitVec.lt_def, hL1]; omega
      simp [this] at hwg
    refine R_check2_vvh hc_s2 (R_ret_vvh (fun v hv => ?_))
    simp [evalHOLExact, evalListHOLExact, hs2, lk_set_vvh, lk_set'_vvh] at hv; subst hv
    have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
    refine ⟨1#64, B - 128#64, 0#64, rfl, by rw [h1]; omega, by rw [h1]; omega, ?_⟩
    intro e2 hc2 hp2 hbytes rv2 hret2
    revert rv2 hret2
    change RetOK_vvh (fun rv2 => rv2 = .val (.word (1#64 + (B - 128#64)))) e2
      (sourceFnBody Guest.Software.guestFn_rlp_item_total_unchecked)
    dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_item_total_unchecked,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    refine R_dec_vvh (fun vb2 hvb2 _ => ?_)
    obtain ⟨P2', ha2, _, rfl⟩ := loadByte_eq_memB_vvh e2 _ vb2 hvb2
    simp only [evalHOLExact, PanSemStateFiniteExact.toExact, hp2, Option.some.injEq, ValueHOL.val.injEq,
      HolWordLab.word.injEq] at ha2; subst ha2
    have hb2_eq : BitVec.ofNat 64 (memB e2 P.toNat) = B := by
      have h0 := hbytes 0 hL_pos; simp at h0; rw [h0]
    rw [hb2_eq]
    refine R_branch_vvh (by rfl) (fun w2' hw2' hw2'_nz => ?_) (fun _ _ _ => ?_)
    · simp [evalHOLExact, lk_set'_vvh, Compiler.Encoders.Asm.wordCmpHOL, hB_ge128] at hw2'
      exact absurd hw2'.symm hw2'_nz
    refine R_branch_vvh (by rfl) (fun _ _ _ => R_ret_vvh (fun v2 hv2 => ?_)) (fun w2' hw2' hw2'_0 => ?_)
    · simp [evalHOLExact, evalListHOLExact, lk_set'_vvh, wordOpHOL, wordOp, valueIsWord, valueWord] at hv2
      rw [← hv2]; congr 2; bv_omega
    · simp [evalHOLExact, lk_set'_vvh, Compiler.Encoders.Asm.wordCmpHOL, hB_le183] at hw2'
      subst hw2'_0; simp at hw2'
  have hB_notle183 : ¬ (B ≤ 183#64) := by
    simp [evalHOLExact, hs1_b, Compiler.Encoders.Asm.wordCmpHOL] at hw2
    subst hw2_0; intro hle; simp [hle] at hw2
  -- Branch 3: B ≤ 191 (long string)
  refine R_branch_vvh (by rfl) (fun w3 hw3 hw3_nz => ?_) (fun w3 hw3 hw3_0 => ?_)
  · have hB_le191 : B ≤ 191#64 := by
      simp [evalHOLExact, hs1_b, Compiler.Encoders.Asm.wordCmpHOL] at hw3
      by_contra hgt; simp [hgt] at hw3; exact hw3_nz hw3.symm
    refine R_dec_vvh (fun vll hvll _ => ?_)
    simp [evalHOLExact, evalListHOLExact, hs1_b, wordOpHOL, wordOp, valueIsWord, valueWord] at hvll; subst hvll
    set LL := B - 183#64
    refine R_guard_vvh (by exact hcode1) (fun wg hwg hwg0 => ?_)
    have hLL : LL.toNat ≤ L.toNat - 1 := by
      simp [evalHOLExact, evalListHOLExact, lk_set_vvh, lk_set'_vvh,
        show ofString "ll" ≠ ofString "len" by decide, hs1_l, wordOpHOL, wordOp, valueIsWord,
        valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hwg
      subst hwg0; by_contra hc
      have hlt_ll : L - 1#64 < LL := by rw [BitVec.lt_def, hL1]; omega
      simp [hlt_ll] at hwg
    refine R_decCall'_vvh (fun cvals cbody callee crs vn hargs hlk hret_n hsh u hcu hloc hun => ?_)
    have hs_p : (setVarHOLFinite (ofString "ll") (.val (.word LL)) s1).locals.lookup (ofString "p") =
        some (.val (.word P)) := by
      rw [lk_set_vvh _ _ _ _ (by decide)]; exact hs1_p
    have hs_ll : (setVarHOLFinite (ofString "ll") (.val (.word LL)) s1).locals.lookup (ofString "ll") =
        some (.val (.word LL)) := lk_set'_vvh _ _ _
    simp [evalListHOLFinite_eq_toExact, evalListHOLExact, evalHOLExact, hs_p, hs_ll,
      wordOpHOL, wordOp, valueIsWord, valueWord] at hargs
    subst hargs
    have hlk' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_read_length")
        [.val (.word (P + 1#64)), .val (.word LL)] = some (cbody, callee, crs) := by
      simpa [setVarHOLFinite, hc_s1] using hlk
    obtain ⟨rfl, hcp_n, hcn_n⟩ := callee_p_n_vvh lookup_rlp_read_length_vvh _ _ cbody callee crs hlk'
    have h1_nat : (1#64 : BitVec 64).toNat = 1 := rfl
    have hLL0 : 0 < LL.toNat := by
      have hgt183 : 183 < B.toNat := by
        by_contra hle; exact hB_notle183 (by rw [BitVec.le_def]; exact Nat.not_lt.mp hle)
      have h183_nat : (183#64 : BitVec 64).toNat = 183 := rfl
      have hLL_sub : LL.toNat = B.toNat - 183 := by
        change (B - 183#64).toNat = B.toNat - 183
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h183_nat]; omega), h183_nat]
      omega
    have hp1_nat : (P + 1#64).toNat = P.toNat + 1 := by
      have hPlt : P.toNat + 1 < 2 ^ 64 := by omega
      exact BitVec.toNat_add_of_lt (by simpa [h1_nat] using hPlt)
    have hfit_ll : (P + 1#64).toNat + LL.toNat ≤ 2 ^ 64 := by
      have : P.toNat + L.toNat ≤ 2 ^ 64 := hfit
      have : 0 < L.toNat := hL_pos
      have : LL.toNat ≤ L.toNat - 1 := hLL
      rw [hp1_nat]; omega
    have hvn_eq := rlp_read_length_ret_eq_acc_vvh
      (callEntryStateHOLFinite (setVarHOLFinite (ofString "ll") (.val (.word LL)) s1) callee)
      hc_s1 (P + 1#64) LL hfit_ll hcp_n hcn_n vn hret_n
    let N := rlpReadLenAcc (fun j => memB e1 ((P + 1#64).toNat + j)) LL.toNat 0 0#64
    have hvn_eq' : vn = .val (.word N) := hvn_eq
    subst hvn_eq'
    have hul : u.locals.lookup (ofString "len") = some (.val (.word L)) := by
      rw [hloc _ (by decide), lk_set_vvh _ _ _ _ (by decide)]; exact hs1_l
    have hull : u.locals.lookup (ofString "ll") = some (.val (.word LL)) := by
      rw [hloc _ (by decide), lk_set'_vvh]
    have hcu' : u.code = originalRuntimeCode := hcu.trans hc_s1
    refine R_guard_vvh hcu' (fun _ _ _ => ?_)
    refine R_guard_vvh hcu' (fun wg2 hwg2 hwg2_0 => R_ret_vvh (fun v hv => ?_))
    have hsub : (L - 1#64 - LL).toNat = L.toNat - 1 - LL.toNat := by
      rw [BitVec.toNat_sub, hL1]; omega
    have hNle : N.toNat ≤ L.toNat - 1 - LL.toNat := by
      simp [evalHOLExact, evalListHOLExact, hul, hull, hun, wordOpHOL, wordOp, valueIsWord,
        valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hwg2
      subst hwg2_0; by_contra hc
      have : L - 1#64 - LL < N := by rw [BitVec.lt_def, hsub]; omega
      simp [this] at hwg2
    simp [evalHOLExact, evalListHOLExact, hull, hun, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
    subst hv
    have hadd_hl : (1#64 + LL).toNat = 1 + LL.toNat := by
      rw [BitVec.toNat_add_of_lt (by rw [h1_nat]; omega), h1_nat]
    refine ⟨1#64 + LL, N, 0#64, rfl, by rw [hadd_hl]; omega, by rw [hadd_hl]; omega, ?_⟩
    intro e2 hc2 hp2 hbytes rv2 hret2
    revert rv2 hret2
    change RetOK_vvh (fun rv2 => rv2 = .val (.word ((1#64 + LL) + N))) e2
      (sourceFnBody Guest.Software.guestFn_rlp_item_total_unchecked)
    dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_item_total_unchecked,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    refine R_dec_vvh (fun vb2 hvb2 _ => ?_)
    obtain ⟨P2', ha2, _, rfl⟩ := loadByte_eq_memB_vvh e2 _ vb2 hvb2
    simp only [evalHOLExact, PanSemStateFiniteExact.toExact, hp2, Option.some.injEq, ValueHOL.val.injEq,
      HolWordLab.word.injEq] at ha2; subst ha2
    have hb2_eq : BitVec.ofNat 64 (memB e2 P.toNat) = B := by
      have h0 := hbytes 0 hL_pos; simp at h0; rw [h0]
    rw [hb2_eq]
    refine R_branch_vvh (by rfl) (fun w' hw' hw'_nz => ?_) (fun _ _ _ => ?_)
    · simp [evalHOLExact, lk_set'_vvh, Compiler.Encoders.Asm.wordCmpHOL, hB_ge128] at hw'
      exact absurd hw'.symm hw'_nz
    refine R_branch_vvh (by rfl) (fun w' hw' hw'_nz => ?_) (fun _ _ _ => ?_)
    · simp [evalHOLExact, lk_set'_vvh, Compiler.Encoders.Asm.wordCmpHOL, hB_notle183] at hw'
      exact absurd hw'.symm hw'_nz
    refine R_branch_vvh (by rfl) (fun _ _ _ => ?_) (fun w' hw' hw'_0 => ?_)
    · refine R_dec_vvh (fun vll2 hvll2 _ => ?_)
      simp [evalHOLExact, evalListHOLExact, lk_set'_vvh, wordOpHOL, wordOp, valueIsWord, valueWord] at hvll2
      subst hvll2
      refine R_decCall'_vvh (fun cvals2 cbody2 callee2 crs2 vn2 hargs2 hlk2 hret_n2 _ u2 _ hloc2 hun2 => ?_)
      have hup2 : (setVarHOLFinite (ofString "ll") (.val (.word (B - 183#64)))
          (setVarHOLFinite (ofString "b") (.val (.word B)) e2)).locals.lookup (ofString "p") =
          some (.val (.word P)) := by
        rw [lk_set_vvh _ _ _ _ (by decide), lk_set_vvh _ _ _ _ (by decide)]; exact hp2
      have hull2 : (setVarHOLFinite (ofString "ll") (.val (.word (B - 183#64)))
          (setVarHOLFinite (ofString "b") (.val (.word B)) e2)).locals.lookup (ofString "ll") =
          some (.val (.word LL)) := lk_set'_vvh _ _ _
      simp [evalListHOLFinite_eq_toExact, evalListHOLExact, evalHOLExact, hup2, hull2,
        wordOpHOL, wordOp, valueIsWord, valueWord] at hargs2
      subst hargs2
      have hlk2' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_read_length")
          [.val (.word (P + 1#64)), .val (.word LL)] = some (cbody2, callee2, crs2) := by
        simpa [setVarHOLFinite, hc2] using hlk2
      obtain ⟨rfl, hcp2, hcn2⟩ := callee_p_n_vvh lookup_rlp_read_length_vvh _ _ cbody2 callee2 crs2 hlk2'
      have hvn2_eq := rlp_read_length_ret_eq_acc_vvh
        (callEntryStateHOLFinite _ callee2) hc2 (P + 1#64) LL hfit_ll hcp2 hcn2 vn2 hret_n2
      have hacc_eq : rlpReadLenAcc (fun j => memB e2 ((P + 1#64).toNat + j)) LL.toNat 0 0#64 = N := by
        apply rlpReadLenAcc_congr
        intro j _ hj2
        rw [hp1_nat, Nat.add_assoc]
        exact hbytes (1 + j) (by omega)
      change vn2 = .val (.word (rlpReadLenAcc (fun j => memB e2 ((P + 1#64).toNat + j)) LL.toNat 0 0#64)) at hvn2_eq
      rw [hacc_eq] at hvn2_eq
      subst hvn2_eq
      have hu2_ll : u2.locals.lookup (ofString "ll") = some (.val (.word LL)) := by
        rw [hloc2 _ (by decide), lk_set'_vvh]
      refine R_ret_vvh (fun v2 hv2 => ?_)
      simp [evalHOLExact, evalListHOLExact, hu2_ll, hun2, wordOpHOL, wordOp, valueIsWord, valueWord] at hv2
      rw [← hv2]; congr 2; bv_omega
    · simp [evalHOLExact, lk_set'_vvh, Compiler.Encoders.Asm.wordCmpHOL, hB_le191] at hw'
      subst hw'_0; simp at hw'
  have hB_notle191 : ¬ (B ≤ 191#64) := by
    simp [evalHOLExact, hs1_b, Compiler.Encoders.Asm.wordCmpHOL] at hw3
    subst hw3_0; intro hle; simp [hle] at hw3
  -- Branch 4: B ≤ 247 (short list)
  refine R_branch_vvh (by rfl) (fun w4 hw4 hw4_nz => ?_) (fun w4 hw4 hw4_0 => ?_)
  · have hB_le247 : B ≤ 247#64 := by
      simp [evalHOLExact, hs1_b, Compiler.Encoders.Asm.wordCmpHOL] at hw4
      by_contra hgt; simp [hgt] at hw4; exact hw4_nz hw4.symm
    refine R_dec_vvh (fun vn hvn _ => ?_)
    simp [evalHOLExact, evalListHOLExact, hs1_b, wordOpHOL, wordOp, valueIsWord, valueWord] at hvn; subst hvn
    refine R_guard_vvh (by exact hcode1) (fun wg hwg hwg0 => R_ret_vvh (fun v hv => ?_))
    have hN : (B - 192#64).toNat ≤ L.toNat - 1 := by
      simp [evalHOLExact, evalListHOLExact, lk_set_vvh, lk_set'_vvh,
        show ofString "n" ≠ ofString "len" by decide, hs1_l, wordOpHOL, wordOp, valueIsWord,
        valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hwg
      subst hwg0; by_contra hc
      have : L - 1#64 < B - 192#64 := by rw [BitVec.lt_def, hL1]; omega
      simp [this] at hwg
    simp [evalHOLExact, evalListHOLExact, lk_set_vvh, lk_set'_vvh] at hv; subst hv
    have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
    refine ⟨1#64, B - 192#64, 1#64, rfl, by rw [h1]; omega, by rw [h1]; omega, ?_⟩
    intro e2 hc2 hp2 hbytes rv2 hret2
    revert rv2 hret2
    change RetOK_vvh (fun rv2 => rv2 = .val (.word (1#64 + (B - 192#64)))) e2
      (sourceFnBody Guest.Software.guestFn_rlp_item_total_unchecked)
    dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_item_total_unchecked,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    refine R_dec_vvh (fun vb2 hvb2 _ => ?_)
    obtain ⟨P2', ha2, _, rfl⟩ := loadByte_eq_memB_vvh e2 _ vb2 hvb2
    simp only [evalHOLExact, PanSemStateFiniteExact.toExact, hp2, Option.some.injEq, ValueHOL.val.injEq,
      HolWordLab.word.injEq] at ha2; subst ha2
    have hb2_eq : BitVec.ofNat 64 (memB e2 P.toNat) = B := by
      have h0 := hbytes 0 hL_pos; simp at h0; rw [h0]
    rw [hb2_eq]
    refine R_branch_vvh (by rfl) (fun w' hw' hw'_nz => ?_) (fun _ _ _ => ?_)
    · simp [evalHOLExact, lk_set'_vvh, Compiler.Encoders.Asm.wordCmpHOL, hB_ge128] at hw'
      exact absurd hw'.symm hw'_nz
    refine R_branch_vvh (by rfl) (fun w' hw' hw'_nz => ?_) (fun _ _ _ => ?_)
    · simp [evalHOLExact, lk_set'_vvh, Compiler.Encoders.Asm.wordCmpHOL, hB_notle183] at hw'
      exact absurd hw'.symm hw'_nz
    refine R_branch_vvh (by rfl) (fun w' hw' hw'_nz => ?_) (fun _ _ _ => ?_)
    · simp [evalHOLExact, lk_set'_vvh, Compiler.Encoders.Asm.wordCmpHOL, hB_notle191] at hw'
      exact absurd hw'.symm hw'_nz
    refine R_branch_vvh (by rfl) (fun _ _ _ => R_ret_vvh (fun v2 hv2 => ?_)) (fun w' hw' hw'_0 => ?_)
    · simp [evalHOLExact, evalListHOLExact, lk_set'_vvh, wordOpHOL, wordOp, valueIsWord, valueWord] at hv2
      rw [← hv2]; congr 2; bv_omega
    · simp [evalHOLExact, lk_set'_vvh, Compiler.Encoders.Asm.wordCmpHOL, hB_le247] at hw'
      subst hw'_0; simp at hw'
  -- Branch 5: B > 247 (long list)
  have hB_notle247 : ¬ (B ≤ 247#64) := by
    simp [evalHOLExact, hs1_b, Compiler.Encoders.Asm.wordCmpHOL] at hw4
    subst hw4_0; intro hle; simp [hle] at hw4
  refine R_dec_vvh (fun vll hvll _ => ?_)
  simp [evalHOLExact, evalListHOLExact, hs1_b, wordOpHOL, wordOp, valueIsWord, valueWord] at hvll; subst hvll
  set LL := B - 247#64
  refine R_guard_vvh (by exact hcode1) (fun wg hwg hwg0 => ?_)
  have hLL : LL.toNat ≤ L.toNat - 1 := by
    simp [evalHOLExact, evalListHOLExact, lk_set_vvh, lk_set'_vvh,
      show ofString "ll" ≠ ofString "len" by decide, hs1_l, wordOpHOL, wordOp, valueIsWord,
      valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hwg
    subst hwg0; by_contra hc
    have hlt_ll : L - 1#64 < LL := by rw [BitVec.lt_def, hL1]; omega
    simp [hlt_ll] at hwg
  refine R_decCall'_vvh (fun cvals cbody callee crs vn hargs hlk hret_n hsh u hcu hloc hun => ?_)
  have hs_p : (setVarHOLFinite (ofString "ll") (.val (.word LL)) s1).locals.lookup (ofString "p") =
      some (.val (.word P)) := by
    rw [lk_set_vvh _ _ _ _ (by decide)]; exact hs1_p
  have hs_ll : (setVarHOLFinite (ofString "ll") (.val (.word LL)) s1).locals.lookup (ofString "ll") =
      some (.val (.word LL)) := lk_set'_vvh _ _ _
  simp [evalListHOLFinite_eq_toExact, evalListHOLExact, evalHOLExact, hs_p, hs_ll,
    wordOpHOL, wordOp, valueIsWord, valueWord] at hargs
  subst hargs
  have hlk' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_read_length")
      [.val (.word (P + 1#64)), .val (.word LL)] = some (cbody, callee, crs) := by
    simpa [setVarHOLFinite, hc_s1] using hlk
  obtain ⟨rfl, hcp_n, hcn_n⟩ := callee_p_n_vvh lookup_rlp_read_length_vvh _ _ cbody callee crs hlk'
  have h1_nat : (1#64 : BitVec 64).toNat = 1 := rfl
  have hLL0 : 0 < LL.toNat := by
    have hgt247 : 247 < B.toNat := by
      by_contra hle; exact hB_notle247 (by rw [BitVec.le_def]; exact Nat.not_lt.mp hle)
    have hlt256 : B.toNat < 256 := by
      have hm : memB e1 P.toNat < 256 := by
        unfold memB; rcases e1.memory _ with ⟨w⟩; exact (panGetByteHOL _ w e1.be).toNat_lt
      change (BitVec.ofNat 64 (memB e1 P.toNat)).toNat < 256
      rw [BitVec.toNat_ofNat]; omega
    have h247_nat : (247#64 : BitVec 64).toNat = 247 := rfl
    have hLL_sub : LL.toNat = B.toNat - 247 := by
      change (B - 247#64).toNat = B.toNat - 247
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h247_nat]; omega), h247_nat]
    omega
  have hp1_nat : (P + 1#64).toNat = P.toNat + 1 := by
    have hPlt : P.toNat + 1 < 2 ^ 64 := by omega
    exact BitVec.toNat_add_of_lt (by simpa [h1_nat] using hPlt)
  have hfit_ll : (P + 1#64).toNat + LL.toNat ≤ 2 ^ 64 := by
    have : P.toNat + L.toNat ≤ 2 ^ 64 := hfit
    have : 0 < L.toNat := hL_pos
    have : LL.toNat ≤ L.toNat - 1 := hLL
    rw [hp1_nat]; omega
  have hvn_eq := rlp_read_length_ret_eq_acc_vvh
    (callEntryStateHOLFinite (setVarHOLFinite (ofString "ll") (.val (.word LL)) s1) callee)
    hc_s1 (P + 1#64) LL hfit_ll hcp_n hcn_n vn hret_n
  let N := rlpReadLenAcc (fun j => memB e1 ((P + 1#64).toNat + j)) LL.toNat 0 0#64
  have hvn_eq' : vn = .val (.word N) := hvn_eq
  subst hvn_eq'
  have hul : u.locals.lookup (ofString "len") = some (.val (.word L)) := by
    rw [hloc _ (by decide), lk_set_vvh _ _ _ _ (by decide)]; exact hs1_l
  have hull : u.locals.lookup (ofString "ll") = some (.val (.word LL)) := by
    rw [hloc _ (by decide), lk_set'_vvh]
  have hcu' : u.code = originalRuntimeCode := hcu.trans hc_s1
  refine R_guard_vvh hcu' (fun _ _ _ => ?_)
  refine R_guard_vvh hcu' (fun wg2 hwg2 hwg2_0 => R_ret_vvh (fun v hv => ?_))
  have hsub : (L - 1#64 - LL).toNat = L.toNat - 1 - LL.toNat := by
    rw [BitVec.toNat_sub, hL1]; omega
  have hNle : N.toNat ≤ L.toNat - 1 - LL.toNat := by
    simp [evalHOLExact, evalListHOLExact, hul, hull, hun, wordOpHOL, wordOp, valueIsWord,
      valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hwg2
    subst hwg2_0; by_contra hc
    have : L - 1#64 - LL < N := by rw [BitVec.lt_def, hsub]; omega
    simp [this] at hwg2
  simp [evalHOLExact, evalListHOLExact, hull, hun, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
  subst hv
  have hadd_hl : (1#64 + LL).toNat = 1 + LL.toNat := by
    rw [BitVec.toNat_add_of_lt (by rw [h1_nat]; omega), h1_nat]
  refine ⟨1#64 + LL, N, 1#64, rfl, by rw [hadd_hl]; omega, by rw [hadd_hl]; omega, ?_⟩
  intro e2 hc2 hp2 hbytes rv2 hret2
  revert rv2 hret2
  change RetOK_vvh (fun rv2 => rv2 = .val (.word ((1#64 + LL) + N))) e2
    (sourceFnBody Guest.Software.guestFn_rlp_item_total_unchecked)
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_item_total_unchecked,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine R_dec_vvh (fun vb2 hvb2 _ => ?_)
  obtain ⟨P2', ha2, _, rfl⟩ := loadByte_eq_memB_vvh e2 _ vb2 hvb2
  simp only [evalHOLExact, PanSemStateFiniteExact.toExact, hp2, Option.some.injEq, ValueHOL.val.injEq,
    HolWordLab.word.injEq] at ha2; subst ha2
  have hb2_eq : BitVec.ofNat 64 (memB e2 P.toNat) = B := by
    have h0 := hbytes 0 hL_pos; simp at h0; rw [h0]
  rw [hb2_eq]
  refine R_branch_vvh (by rfl) (fun w' hw' hw'_nz => ?_) (fun _ _ _ => ?_)
  · simp [evalHOLExact, lk_set'_vvh, Compiler.Encoders.Asm.wordCmpHOL, hB_ge128] at hw'
    exact absurd hw'.symm hw'_nz
  refine R_branch_vvh (by rfl) (fun w' hw' hw'_nz => ?_) (fun _ _ _ => ?_)
  · simp [evalHOLExact, lk_set'_vvh, Compiler.Encoders.Asm.wordCmpHOL, hB_notle183] at hw'
    exact absurd hw'.symm hw'_nz
  refine R_branch_vvh (by rfl) (fun w' hw' hw'_nz => ?_) (fun _ _ _ => ?_)
  · simp [evalHOLExact, lk_set'_vvh, Compiler.Encoders.Asm.wordCmpHOL, hB_notle191] at hw'
    exact absurd hw'.symm hw'_nz
  refine R_branch_vvh (by rfl) (fun w' hw' hw'_nz => ?_) (fun _ _ _ => ?_)
  · simp [evalHOLExact, lk_set'_vvh, Compiler.Encoders.Asm.wordCmpHOL, hB_notle247] at hw'
    exact absurd hw'.symm hw'_nz
  refine R_dec_vvh (fun vll2 hvll2 _ => ?_)
  simp [evalHOLExact, evalListHOLExact, lk_set'_vvh, wordOpHOL, wordOp, valueIsWord, valueWord] at hvll2
  subst hvll2
  refine R_decCall'_vvh (fun cvals2 cbody2 callee2 crs2 vn2 hargs2 hlk2 hret_n2 _ u2 _ hloc2 hun2 => ?_)
  have hup2 : (setVarHOLFinite (ofString "ll2") (.val (.word (B - 247#64)))
      (setVarHOLFinite (ofString "b") (.val (.word B)) e2)).locals.lookup (ofString "p") =
      some (.val (.word P)) := by
    rw [lk_set_vvh _ _ _ _ (by decide), lk_set_vvh _ _ _ _ (by decide)]; exact hp2
  have hull2 : (setVarHOLFinite (ofString "ll2") (.val (.word (B - 247#64)))
      (setVarHOLFinite (ofString "b") (.val (.word B)) e2)).locals.lookup (ofString "ll2") =
      some (.val (.word LL)) := lk_set'_vvh _ _ _
  simp [evalListHOLFinite_eq_toExact, evalListHOLExact, evalHOLExact, hup2, hull2,
    wordOpHOL, wordOp, valueIsWord, valueWord] at hargs2
  subst hargs2
  have hlk2' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_read_length")
      [.val (.word (P + 1#64)), .val (.word LL)] = some (cbody2, callee2, crs2) := by
    simpa [setVarHOLFinite, hc2] using hlk2
  obtain ⟨rfl, hcp2, hcn2⟩ := callee_p_n_vvh lookup_rlp_read_length_vvh _ _ cbody2 callee2 crs2 hlk2'
  have hvn2_eq := rlp_read_length_ret_eq_acc_vvh
    (callEntryStateHOLFinite _ callee2) hc2 (P + 1#64) LL hfit_ll hcp2 hcn2 vn2 hret_n2
  have hacc_eq : rlpReadLenAcc (fun j => memB e2 ((P + 1#64).toNat + j)) LL.toNat 0 0#64 = N := by
    apply rlpReadLenAcc_congr
    intro j _ hj2
    rw [hp1_nat, Nat.add_assoc]
    exact hbytes (1 + j) (by omega)
  change vn2 = .val (.word (rlpReadLenAcc (fun j => memB e2 ((P + 1#64).toNat + j)) LL.toNat 0 0#64)) at hvn2_eq
  rw [hacc_eq] at hvn2_eq
  subst hvn2_eq
  have hu2_ll : u2.locals.lookup (ofString "ll2") = some (.val (.word LL)) := by
    rw [hloc2 _ (by decide), lk_set'_vvh]
  refine R_ret_vvh (fun v2 hv2 => ?_)
  simp [evalHOLExact, evalListHOLExact, hu2_ll, hun2, wordOpHOL, wordOp, valueIsWord, valueWord] at hv2
  rw [← hv2]; congr 2; bv_omega

private theorem rlp_item_total_agree_unchecked_vvh {F : Type}
    (e1 : PanSemStateFiniteExact 64 F) (hcode1 : e1.code = originalRuntimeCode)
    (P L : BitVec 64) (hfit : P.toNat + L.toNat ≤ 2 ^ 64)
    (hp1 : e1.locals.lookup (ofString "p") = some (.val (.word P)))
    (hl1 : e1.locals.lookup (ofString "len") = some (.val (.word L))) :
    RetOK_vvh (fun v =>
      ∃ T : BitVec 64, v = .val (.word T) ∧ 1 ≤ T.toNat ∧ T.toNat ≤ L.toNat ∧
        ∀ e2 : PanSemStateFiniteExact 64 F,
          e2.code = originalRuntimeCode →
          e2.locals.lookup (ofString "p") = some (.val (.word P)) →
          (∀ j < L.toNat, memB e2 (P.toNat + j) = memB e1 (P.toNat + j)) →
          ∀ rv2 : ValueHOL 64,
            (evaluateHOLFiniteState e2 (sourceFnBody Guest.Software.guestFn_rlp_item_total_unchecked)).1 =
              some (.returned rv2) →
            rv2 = .val (.word T))
      e1 (sourceFnBody Guest.Software.guestFn_rlp_item_total) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_item_total,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine R_decCall'_vvh (fun values body callee rs v hargs hlk hret _ u _ _ hu => ?_)
  simp only [evalListHOLFinite_eq_toExact, evalListHOLExact, evalHOLExact, hp1, hl1, Option.some.injEq] at hargs
  subst hargs
  rw [hcode1] at hlk
  obtain ⟨rfl, hcp, hcl⟩ := callee_p_len_vvh lookup_rlp_item_header_vvh _ _ body callee rs hlk
  obtain ⟨a, b, c, rfl, h1, h2, hagree⟩ :=
    rlp_item_header_agree_unchecked_vvh (callEntryStateHOLFinite e1 callee) hcode1 P L hfit hcp hcl v hret
  refine R_seq_vvh (R_ite_vvh (fun _ _ => ⟨fun _ v hv => absurd hv (call_noret_vvh u _ _ v), fun _ => R_skip_vvh⟩))
    (fun mid hmid => ?_)
  have hmid_h : mid.locals.lookup (ofString "h") = some (hval_vvh a b c) := by
    rw [evaluateHOLFiniteState_ite] at hmid
    split at hmid
    · split at hmid
      · rw [evaluateHOLFiniteState_skip] at hmid
        simp only [Prod.mk.injEq] at hmid
        rw [← hmid.2]; exact hu
      · rw [(call_flow_locals_vvh u _ _ mid hmid).1]; exact hu
    · simp at hmid
  refine R_ret_vvh (fun v hv => ?_)
  simp [evalHOLExact, evalListHOLExact, hmid_h, hval_vvh, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
  subst hv
  have hab_nat : (a + b).toNat = a.toNat + b.toNat :=
    BitVec.toNat_add_of_lt (by have := L.isLt; omega)
  refine ⟨a + b, rfl, by rw [hab_nat]; omega, by rw [hab_nat]; omega, ?_⟩
  intro e2 hc2 hp2 hbytes rv2 hret2
  exact hagree e2 hc2 hp2 hbytes rv2 hret2

private theorem rlp_item_total_worldEff_agree_vvh {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hAs : ArenaReady s)
    (heff : WorldEff s post [] [] wsGw)
    (P L : Nat) (p len : BitVec 64)
    (hfit : P + L ≤ 2 ^ 64)
    (hdj : IvlsDisj [(P, L)] [(globN s "heap_ptr", scratchEnd - globN s "heap_ptr")])
    (hlo : P ≤ p.toNat) (hhi : p.toNat + len.toNat ≤ P + L)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word p)))
    (hlen : s.locals.lookup (ofString "len") = some (.val (.word len)))
    (hppost : post.locals.lookup (ofString "p") = some (.val (.word p))) :
    RetOK_vvh (fun v =>
      ∃ T : BitVec 64, v = .val (.word T) ∧ 1 ≤ T.toNat ∧ T.toNat ≤ len.toNat ∧
        ∀ rv : ValueHOL 64,
          (evaluateHOLFiniteState post (sourceFnBody Guest.Software.guestFn_rlp_item_total_unchecked)).1 =
            some (.returned rv) → rv = .val (.word T))
      s (sourceFnBody Guest.Software.guestFn_rlp_item_total) := by
  obtain ⟨hsubfit, _, hbytes⟩ := input_subregion_worldEff_vvh hAs heff hfit hdj hlo hhi
  intro v hv
  obtain ⟨T, hT, hpos, hbound, hagree⟩ :=
    rlp_item_total_agree_unchecked_vvh s hc p len hsubfit hp hlen v hv
  exact ⟨T, hT, hpos, hbound, hagree post heff.code hppost hbytes⟩

/-! ### Section 5c: Sub-Item Payload Bounds for `rlp_item`, `rlp_decode_fully`, `tx_bytes_item`, and `tx_list_item` -/

private def ItemQ_vvh (P L : BitVec 64) (v : ValueHOL 64) : Prop :=
  ∃ kind pay plen tot : BitVec 64,
    v = .rStruct [.val (.word kind), .val (.word pay), .val (.word plen), .val (.word tot)] ∧
    plen.toNat ≤ L.toNat ∧
    (0 < plen.toNat → P.toNat ≤ pay.toNat ∧ pay.toNat + plen.toNat ≤ P.toNat + L.toNat) ∧
    1 ≤ tot.toNat ∧ tot.toNat ≤ L.toNat

private theorem R_raise_guard_vvh {Q : ValueHOL 64 → Prop} {F : Type}
    {s : PanSemStateFiniteExact 64 F} {c : ExpHOL 64} {eid : MlS} {rexp : ExpHOL 64} {rest : ProgHOL 64}
    (h : ∀ w : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) c =
        some (.val (.word w)) → w = 0 → RetOK_vvh Q s rest) :
    RetOK_vvh Q s (.seq (.ite c (.raise eid rexp) .skip) rest) := by
  have hraise_nr : ∀ u : PanSemStateFiniteExact 64 F, RetOK_vvh Q u (.raise eid rexp) := by
    intro u v hv
    rw [evaluateHOLFiniteState_raise] at hv
    split at hv <;> [ (dsimp only at hv; split at hv <;> simp at hv); simp at hv ]
  apply R_seq_vvh
  · apply R_ite_vvh
    intro w _
    exact ⟨fun _ => hraise_nr s, fun _ => R_skip_vvh⟩
  · intro mid hmid
    rw [evaluateHOLFiniteState_ite] at hmid
    split at hmid
    · rename_i w hw
      split at hmid
      · rename_i hw0
        rw [evaluateHOLFiniteState_skip] at hmid
        simp only [Prod.mk.injEq] at hmid
        obtain ⟨-, rfl⟩ := hmid
        exact h w hw hw0
      · exact absurd (by rw [hmid]) (abrupt_nonone_vvh (.raise eid rexp) rfl s)
    · simp at hmid

private theorem R_call0_flow_vvh {Q : ValueHOL 64 → Prop} {F : Type}
    {s : PanSemStateFiniteExact 64 F} {f : MlS} {args : List (ExpHOL 64)} {rest : ProgHOL 64}
    (h : ∀ mid : PanSemStateFiniteExact 64 F,
      mid.locals = s.locals → mid.code = s.code → RetOK_vvh Q mid rest) :
    RetOK_vvh Q s (.seq (.call (some (none, none)) f args) rest) := by
  apply R_seq_vvh
  · intro v hv
    exact absurd hv (call_noret_vvh s f args v)
  · intro mid hmid
    obtain ⟨hloc, hcd⟩ := call_flow_locals_vvh s f args mid hmid
    exact h mid hloc hcd

private theorem rlp_item_ret_sub_vvh {F : Type}
    (e : PanSemStateFiniteExact 64 F) (hcode : e.code = originalRuntimeCode)
    (P L : BitVec 64) (hfit : P.toNat + L.toNat ≤ 2 ^ 64)
    (hp : e.locals.lookup (ofString "p") = some (.val (.word P)))
    (hl : e.locals.lookup (ofString "len") = some (.val (.word L))) :
    RetOK_vvh (ItemQ_vvh P L) e (sourceFnBody Guest.Software.guestFn_rlp_item) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_item,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine R_guard_vvh hcode (fun w hw hw0 => ?_)
  have hL : L ≠ 0 := by
    intro h; subst h; simp [evalHOLExact, hl, Compiler.Encoders.Asm.wordCmpHOL] at hw; subst hw0
    simp at hw
  have hL_pos : 0 < L.toNat := by
    by_contra hc
    apply hL
    apply BitVec.eq_of_toNat_eq
    simp; omega
  have hL1 := toNat_sub_one_vvh L hL
  have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
  refine R_dec_vvh (fun vb hvb _ => ?_)
  obtain ⟨P', B, ha, _, rfl⟩ := loadByte_word_dom_vvh e _ vb hvb
  simp only [evalHOLExact, PanSemStateFiniteExact.toExact, hp, Option.some.injEq, ValueHOL.val.injEq,
    HolWordLab.word.injEq] at ha
  subst ha
  set e1 := setVarHOLFinite (ofString "b") (.val (.word B)) e with he1
  have hb1 : e1.locals.lookup (ofString "b") = some (.val (.word B)) := lk_set'_vvh _ _ _
  have hp1 : e1.locals.lookup (ofString "p") = some (.val (.word P)) := by
    rw [lk_set_vvh _ _ _ _ (by decide)]; exact hp
  have hl1 : e1.locals.lookup (ofString "len") = some (.val (.word L)) := by
    rw [lk_set_vvh _ _ _ _ (by decide)]; exact hl
  have hc1 : e1.code = originalRuntimeCode := hcode
  -- Branch 1: b < 128
  refine R_branch_vvh (by rfl) (fun _ _ _ => R_ret_vvh (fun v hv => ?_)) (fun _ _ _ => ?_)
  · simp [evalHOLExact, evalListHOLExact, hp1] at hv
    subst hv
    exact ⟨0#64, P, 1#64, 1#64, rfl, by rw [h1]; omega,
      fun _ => ⟨le_rfl, by rw [h1]; omega⟩, by rw [h1], by rw [h1]; omega⟩
  -- Branch 2: b ≤ 183 (short bytes)
  refine R_branch_vvh (by rfl) (fun _ _ _ => R_dec_vvh (fun vn hvn _ => ?_)) (fun _ _ _ => ?_)
  · simp [evalHOLExact, evalListHOLExact, hb1, wordOpHOL, wordOp, valueIsWord, valueWord] at hvn
    subst hvn
    set e2 := setVarHOLFinite (ofString "n") (.val (.word (B - 128#64))) e1 with he2
    have hc2 : e2.code = originalRuntimeCode := hcode
    refine R_guard_vvh hc2 (fun w hw hw0 => ?_)
    have hN : (B - 128#64).toNat ≤ L.toNat - 1 := by
      simp [evalHOLExact, evalListHOLExact, he2, lk_set_vvh, lk_set'_vvh,
        show ofString "n" ≠ ofString "len" by decide, hl1, wordOpHOL, wordOp, valueIsWord,
        valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hw
      subst hw0
      by_contra hc
      have : L - 1#64 < B - 128#64 := by rw [BitVec.lt_def, hL1]; omega
      simp [this] at hw
    refine R_check2_vvh hc2 (R_ret_vvh (fun v hv => ?_))
    have hp2 : e2.locals.lookup (ofString "p") = some (.val (.word P)) := by
      rw [lk_set_vvh _ _ _ _ (by decide)]; exact hp1
    have hn2 : e2.locals.lookup (ofString "n") = some (.val (.word (B - 128#64))) := lk_set'_vvh _ _ _
    simp [evalHOLExact, evalListHOLExact, hp2, hn2, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
    subst hv
    have ht_add : (1#64 + (B - 128#64)).toNat = 1 + (B - 128#64).toNat := by
      rw [BitVec.toNat_add_of_lt (by rw [h1]; have := L.isLt; omega), h1]
    refine ⟨0#64, P + 1#64, B - 128#64, 1#64 + (B - 128#64), rfl, by omega,
      fun hpos => ?_, by rw [ht_add]; omega, by rw [ht_add]; omega⟩
    have hp_add : (P + 1#64).toNat = P.toNat + 1 := by
      rw [BitVec.toNat_add_of_lt (by rw [h1]; omega), h1]
    exact ⟨by rw [hp_add]; omega, by rw [hp_add]; omega⟩
  -- Branch 3: b ≤ 191 (long bytes)
  refine R_branch_vvh (by rfl) (fun _ _ _ => R_dec_vvh (fun vll hvll _ => ?_)) (fun _ _ _ => ?_)
  · simp [evalHOLExact, evalListHOLExact, hb1, wordOpHOL, wordOp, valueIsWord, valueWord] at hvll
    subst hvll
    set e2 := setVarHOLFinite (ofString "ll") (.val (.word (B - 183#64))) e1 with he2
    have hc2 : e2.code = originalRuntimeCode := hcode
    refine R_guard_vvh hc2 (fun w hw hw0 => ?_)
    have hLL : (B - 183#64).toNat ≤ L.toNat - 1 := by
      simp [evalHOLExact, evalListHOLExact, he2, lk_set_vvh, lk_set'_vvh,
        show ofString "ll" ≠ ofString "len" by decide, hl1, wordOpHOL, wordOp, valueIsWord,
        valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hw
      subst hw0
      by_contra hc
      have : L - 1#64 < B - 183#64 := by rw [BitVec.lt_def, hL1]; omega
      simp [this] at hw
    refine R_decCall_vvh (fun u vn hsh hcu hloc hun => ?_)
    rcases vn with ⟨⟨N⟩⟩ | _ | _ <;> simp [shapeEqHOL, shapeOfHOLExact] at hsh
    have hul : u.locals.lookup (ofString "len") = some (.val (.word L)) := by
      rw [hloc _ (by decide), lk_set_vvh _ _ _ _ (by decide)]; exact hl1
    have hup : u.locals.lookup (ofString "p") = some (.val (.word P)) := by
      rw [hloc _ (by decide), lk_set_vvh _ _ _ _ (by decide)]; exact hp1
    have hull : u.locals.lookup (ofString "ll") = some (.val (.word (B - 183#64))) := by
      rw [hloc _ (by decide), lk_set'_vvh]
    have hcu' : u.code = originalRuntimeCode := hcu.trans hc2
    refine R_guard_vvh hcu' (fun _ _ _ => ?_)
    refine R_guard_vvh hcu' (fun w hw hw0 => R_ret_vvh (fun v hv => ?_))
    have hsub : (L - 1#64 - (B - 183#64)).toNat = L.toNat - 1 - (B - 183#64).toNat := by
      rw [BitVec.toNat_sub, hL1]; omega
    have hNle : N.toNat ≤ L.toNat - 1 - (B - 183#64).toNat := by
      simp [evalHOLExact, evalListHOLExact, hul, hull, hun, wordOpHOL, wordOp, valueIsWord,
        valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hw
      subst hw0
      by_contra hc
      have : L - 1#64 - (B - 183#64) < N := by rw [BitVec.lt_def, hsub]; omega
      simp [this] at hw
    simp [evalHOLExact, evalListHOLExact, hup, hull, hun, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
    subst hv
    have htot_add : (1#64 + ((B - 183#64) + N)).toNat = 1 + (B - 183#64).toNat + N.toNat := by
      have hlln : ((B - 183#64) + N).toNat = (B - 183#64).toNat + N.toNat := by
        rw [BitVec.toNat_add_of_lt (by have := L.isLt; omega)]
      rw [BitVec.toNat_add_of_lt (by rw [h1, hlln]; have := L.isLt; omega), h1, hlln]; omega
    refine ⟨0#64, _, N, _, rfl, by omega,
      fun hpos => ?_, by rw [htot_add]; omega, by rw [htot_add]; omega⟩
    have hpay_add : (P + (1#64 + (B - 183#64))).toNat = P.toNat + 1 + (B - 183#64).toNat := by
      have h1ll : (1#64 + (B - 183#64)).toNat = 1 + (B - 183#64).toNat := by
        rw [BitVec.toNat_add_of_lt (by rw [h1]; have := L.isLt; omega), h1]
      rw [BitVec.toNat_add_of_lt (by rw [h1ll]; omega), h1ll]; omega
    exact ⟨by rw [hpay_add]; omega, by rw [hpay_add]; omega⟩
  -- Branch 4: b ≤ 247 (short list)
  refine R_branch_vvh (by decide) (fun _ _ _ => R_dec_vvh (fun vn hvn _ => ?_)) (fun _ _ _ => ?_)
  · simp [evalHOLExact, evalListHOLExact, hb1, wordOpHOL, wordOp, valueIsWord, valueWord] at hvn
    subst hvn
    set e2 := setVarHOLFinite (ofString "n") (.val (.word (B - 192#64))) e1 with he2
    have hc2 : e2.code = originalRuntimeCode := hcode
    refine R_guard_vvh hc2 (fun w hw hw0 => ?_)
    have hN : (B - 192#64).toNat ≤ L.toNat - 1 := by
      simp [evalHOLExact, evalListHOLExact, he2, lk_set_vvh, lk_set'_vvh,
        show ofString "n" ≠ ofString "len" by decide, hl1, wordOpHOL, wordOp, valueIsWord,
        valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hw
      subst hw0
      by_contra hc
      have : L - 1#64 < B - 192#64 := by rw [BitVec.lt_def, hL1]; omega
      simp [this] at hw
    refine R_call0_flow_vvh (fun mid hmid_loc _ => R_ret_vvh (fun v hv => ?_))
    have hp_m : mid.locals.lookup (ofString "p") = some (.val (.word P)) := by
      rw [hmid_loc, lk_set_vvh _ _ _ _ (by decide)]; exact hp1
    have hn_m : mid.locals.lookup (ofString "n") = some (.val (.word (B - 192#64))) := by
      rw [hmid_loc, lk_set'_vvh]
    simp [evalHOLExact, evalListHOLExact, hp_m, hn_m, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
    subst hv
    have ht_add : (1#64 + (B - 192#64)).toNat = 1 + (B - 192#64).toNat := by
      rw [BitVec.toNat_add_of_lt (by rw [h1]; have := L.isLt; omega), h1]
    refine ⟨1#64, P + 1#64, B - 192#64, 1#64 + (B - 192#64), rfl, by omega,
      fun hpos => ?_, by rw [ht_add]; omega, by rw [ht_add]; omega⟩
    have hp_add : (P + 1#64).toNat = P.toNat + 1 := by
      rw [BitVec.toNat_add_of_lt (by rw [h1]; omega), h1]
    exact ⟨by rw [hp_add]; omega, by rw [hp_add]; omega⟩
  -- Branch 5: b > 247 (long list)
  refine R_dec_vvh (fun vll hvll _ => ?_)
  simp [evalHOLExact, evalListHOLExact, hb1, wordOpHOL, wordOp, valueIsWord, valueWord] at hvll
  subst hvll
  set e2 := setVarHOLFinite (ofString "ll") (.val (.word (B - 247#64))) e1 with he2
  have hc2 : e2.code = originalRuntimeCode := hcode
  refine R_guard_vvh hc2 (fun w hw hw0 => ?_)
  have hLL : (B - 247#64).toNat ≤ L.toNat - 1 := by
    simp [evalHOLExact, evalListHOLExact, he2, lk_set_vvh, lk_set'_vvh,
      show ofString "ll" ≠ ofString "len" by decide, hl1, wordOpHOL, wordOp, valueIsWord,
      valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hw
    subst hw0
    by_contra hc
    have : L - 1#64 < B - 247#64 := by rw [BitVec.lt_def, hL1]; omega
    simp [this] at hw
  refine R_decCall_vvh (fun u vn hsh hcu hloc hun => ?_)
  rcases vn with ⟨⟨N⟩⟩ | _ | _ <;> simp [shapeEqHOL, shapeOfHOLExact] at hsh
  have hul : u.locals.lookup (ofString "len") = some (.val (.word L)) := by
    rw [hloc _ (by decide), lk_set_vvh _ _ _ _ (by decide)]; exact hl1
  have hup : u.locals.lookup (ofString "p") = some (.val (.word P)) := by
    rw [hloc _ (by decide), lk_set_vvh _ _ _ _ (by decide)]; exact hp1
  have hull : u.locals.lookup (ofString "ll") = some (.val (.word (B - 247#64))) := by
    rw [hloc _ (by decide), lk_set'_vvh]
  have hcu' : u.code = originalRuntimeCode := hcu.trans hc2
  refine R_guard_vvh hcu' (fun _ _ _ => ?_)
  refine R_guard_vvh hcu' (fun w hw hw0 => ?_)
  have hsub : (L - 1#64 - (B - 247#64)).toNat = L.toNat - 1 - (B - 247#64).toNat := by
    rw [BitVec.toNat_sub, hL1]; omega
  have hNle : N.toNat ≤ L.toNat - 1 - (B - 247#64).toNat := by
    simp [evalHOLExact, evalListHOLExact, hul, hull, hun, wordOpHOL, wordOp, valueIsWord,
      valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hw
    subst hw0
    by_contra hc
    have : L - 1#64 - (B - 247#64) < N := by rw [BitVec.lt_def, hsub]; omega
    simp [this] at hw
  refine R_call0_flow_vvh (fun mid hmid_loc _ => R_ret_vvh (fun v hv => ?_))
  have hup_m : mid.locals.lookup (ofString "p") = some (.val (.word P)) := by
    rw [hmid_loc]; exact hup
  have hull_m : mid.locals.lookup (ofString "ll") = some (.val (.word (B - 247#64))) := by
    rw [hmid_loc]; exact hull
  have hun_m : mid.locals.lookup (ofString "n") = some (.val (.word N)) := by
    rw [hmid_loc]; exact hun
  simp [evalHOLExact, evalListHOLExact, hup_m, hull_m, hun_m, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
  subst hv
  have htot_add : (1#64 + ((B - 247#64) + N)).toNat = 1 + (B - 247#64).toNat + N.toNat := by
    have hlln : ((B - 247#64) + N).toNat = (B - 247#64).toNat + N.toNat := by
      rw [BitVec.toNat_add_of_lt (by have := L.isLt; omega)]
    rw [BitVec.toNat_add_of_lt (by rw [h1, hlln]; have := L.isLt; omega), h1, hlln]; omega
  refine ⟨1#64, _, N, _, rfl, by omega,
    fun hpos => ?_, by rw [htot_add]; omega, by rw [htot_add]; omega⟩
  have hpay_add : (P + (1#64 + (B - 247#64))).toNat = P.toNat + 1 + (B - 247#64).toNat := by
    have h1ll : (1#64 + (B - 247#64)).toNat = 1 + (B - 247#64).toNat := by
      rw [BitVec.toNat_add_of_lt (by rw [h1]; have := L.isLt; omega), h1]
    rw [BitVec.toNat_add_of_lt (by rw [h1ll]; omega), h1ll]; omega
  exact ⟨by rw [hpay_add]; omega, by rw [hpay_add]; omega⟩

private theorem rlp_decode_fully_ret_sub_vvh {F : Type}
    (e : PanSemStateFiniteExact 64 F) (hcode : e.code = originalRuntimeCode)
    (P L : BitVec 64) (hfit : P.toNat + L.toNat ≤ 2 ^ 64)
    (hp : e.locals.lookup (ofString "p") = some (.val (.word P)))
    (hl : e.locals.lookup (ofString "len") = some (.val (.word L))) :
    RetOK_vvh (ItemQ_vvh P L) e (sourceFnBody Guest.Software.guestFn_rlp_decode_fully) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_decode_fully,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine R_decCall'_vvh (fun cvals cbody callee crs vit hargs hlk hret _ u hcu _ huit => ?_)
  simp only [evalListHOLFinite_eq_toExact, evalListHOLExact, evalHOLExact, hp, hl, Option.some.injEq] at hargs
  subst hargs
  rw [hcode] at hlk
  obtain ⟨rfl, hcp, hcl⟩ := callee_p_len_vvh lookup_rlp_item_vvh _ _ cbody callee crs hlk
  have hit := rlp_item_ret_sub_vvh (callEntryStateHOLFinite e callee) hcode P L hfit hcp hcl vit hret
  refine R_guard_vvh (hcu.trans hcode) (fun _ _ _ => R_ret_vvh (fun v hv => ?_))
  simp [evalHOLExact, huit] at hv
  subst hv
  exact hit

private theorem eval_load_one_word_memW_vvh {F : Type}
    (s : PanSemStateFiniteExact 64 F) (addrExp : ExpHOL 64) (v : ValueHOL 64)
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one addrExp) = some v) :
    ∃ addr w : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        addrExp = some (.val (.word addr)) ∧
      v = .val (.word w) ∧ w.toNat = memW s addr.toNat := by
  simp only [evalHOLExact] at hv
  rcases ha : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) addrExp with _ | ev
  · simp [ha] at hv
  · rcases ev with ⟨⟨addr⟩⟩ | _ | _
    · simp only [ha, memLoadHOLExact] at hv
      split at hv
      · cases hm : s.memory addr with
        | word w =>
          rw [hm] at hv
          split at hv
          · injection hv with h
            refine ⟨addr, w, rfl, h.symm, ?_⟩
            unfold memW
            simp [BitVec.ofNat_toNat, hm]
          · cases hv
      · cases hv
    · simp [ha] at hv
    · simp [ha] at hv

private def PairSubQ_vvh (Pi Li : Nat) (v : ValueHOL 64) : Prop :=
  ∃ pay plen : BitVec 64,
    v = .rStruct [.val (.word pay), .val (.word plen)] ∧
    plen.toNat ≤ Li ∧
    (0 < plen.toNat → Pi ≤ pay.toNat ∧ pay.toNat + plen.toNat ≤ Pi + Li)

private theorem tx_bytes_item_ret_sub_vvh {F : Type}
    (e : PanSemStateFiniteExact 64 F) (hcode : e.code = originalRuntimeCode)
    (warr wi : BitVec 64)
    (harr : e.locals.lookup (ofString "arr") = some (.val (.word warr)))
    (hi : e.locals.lookup (ofString "i") = some (.val (.word wi)))
    (hslot_fit : warr.toNat + 16 * wi.toNat + 8 < 2 ^ 64)
    (hslice_fit : memW e (warr.toNat + 16 * wi.toNat) + memW e (warr.toNat + 16 * wi.toNat + 8) ≤ 2 ^ 64) :
    RetOK_vvh (PairSubQ_vvh (memW e (warr.toNat + 16 * wi.toNat)) (memW e (warr.toNat + 16 * wi.toNat + 8)))
      e (sourceFnBody Guest.Software.guestFn_tx_bytes_item) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_tx_bytes_item,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine R_decCall'_vvh (fun cvals cbody callee crs vit hargs hlk hret _ u hcu _ huit => ?_)
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact] at hargs
  split at hargs
  · rename_i v1 vrest h1 hrest
    split at hrest
    · rename_i v2 _ h2 hnil
      simp only [Option.some.injEq] at hnil hrest hargs
      subst hnil
      subst hrest
      subst hargs
      obtain ⟨a1, P, ha1, rfl, hP_mem⟩ := eval_load_one_word_memW_vvh e _ v1 h1
      obtain ⟨a2, L, ha2, rfl, hL_mem⟩ := eval_load_one_word_memW_vvh e _ v2 h2
      have hwi16 : (wi * 16#64).toNat = 16 * wi.toNat := by
        rw [BitVec.toNat_mul_of_lt (by change wi.toNat * 16 < 2 ^ 64; omega)]; change wi.toNat * 16 = 16 * wi.toNat; omega
      have ha1_nat : a1.toNat = warr.toNat + 16 * wi.toNat := by
        simp [evalHOLExact, evalListHOLExact, harr, hi, panOpHOL, wordOpHOL, wordOp, valueIsWord, valueWord] at ha1
        subst ha1
        rw [BitVec.toNat_add_of_lt (by rw [hwi16]; omega), hwi16]
      have ha2_nat : a2.toNat = warr.toNat + 16 * wi.toNat + 8 := by
        simp [evalHOLExact, evalListHOLExact, harr, hi, panOpHOL, wordOpHOL, wordOp, valueIsWord, valueWord] at ha2
        subst ha2
        have h8 : (8#64 : BitVec 64).toNat = 8 := rfl
        have hwi16_8 : (wi * 16#64 + 8#64).toNat = 16 * wi.toNat + 8 := by
          rw [BitVec.toNat_add_of_lt (by rw [hwi16, h8]; omega), hwi16, h8]
        rw [BitVec.toNat_add_of_lt (by rw [hwi16_8]; omega), hwi16_8]; omega
      rw [ha1_nat] at hP_mem
      rw [ha2_nat] at hL_mem
      have hPL_fit : P.toNat + L.toNat ≤ 2 ^ 64 := by omega
      rw [hcode] at hlk
      obtain ⟨rfl, hcp, hcl⟩ := callee_p_len_vvh lookup_rlp_item_vvh _ _ cbody callee crs hlk
      obtain ⟨kind, pay, plen, tot, rfl, hplen_le, hpay_sub, _, _⟩ :=
        rlp_item_ret_sub_vvh (callEntryStateHOLFinite e callee) hcode P L hPL_fit hcp hcl vit hret
      refine R_raise_guard_vvh (fun _ _ _ => R_ret_vvh (fun v hv => ?_))
      simp [evalHOLExact, evalListHOLExact, huit] at hv
      subst hv
      exact ⟨pay, plen, rfl, by omega, fun hpos => by
        obtain ⟨hlo, hhi⟩ := hpay_sub hpos
        exact ⟨by omega, by omega⟩⟩
    · simp at hrest
  · simp at hargs

private theorem tx_list_item_ret_sub_vvh {F : Type}
    (e : PanSemStateFiniteExact 64 F) (hcode : e.code = originalRuntimeCode)
    (warr wi : BitVec 64)
    (harr : e.locals.lookup (ofString "arr") = some (.val (.word warr)))
    (hi : e.locals.lookup (ofString "i") = some (.val (.word wi)))
    (hslot_fit : warr.toNat + 16 * wi.toNat + 8 < 2 ^ 64)
    (hslice_fit : memW e (warr.toNat + 16 * wi.toNat) + memW e (warr.toNat + 16 * wi.toNat + 8) ≤ 2 ^ 64) :
    RetOK_vvh (PairSubQ_vvh (memW e (warr.toNat + 16 * wi.toNat)) (memW e (warr.toNat + 16 * wi.toNat + 8)))
      e (sourceFnBody Guest.Software.guestFn_tx_list_item) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_tx_list_item,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine R_decCall'_vvh (fun cvals cbody callee crs vit hargs hlk hret _ u hcu _ huit => ?_)
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact] at hargs
  split at hargs
  · rename_i v1 vrest h1 hrest
    split at hrest
    · rename_i v2 _ h2 hnil
      simp only [Option.some.injEq] at hnil hrest hargs
      subst hnil
      subst hrest
      subst hargs
      obtain ⟨a1, P, ha1, rfl, hP_mem⟩ := eval_load_one_word_memW_vvh e _ v1 h1
      obtain ⟨a2, L, ha2, rfl, hL_mem⟩ := eval_load_one_word_memW_vvh e _ v2 h2
      have hwi16 : (wi * 16#64).toNat = 16 * wi.toNat := by
        rw [BitVec.toNat_mul_of_lt (by change wi.toNat * 16 < 2 ^ 64; omega)]; change wi.toNat * 16 = 16 * wi.toNat; omega
      have ha1_nat : a1.toNat = warr.toNat + 16 * wi.toNat := by
        simp [evalHOLExact, evalListHOLExact, harr, hi, panOpHOL, wordOpHOL, wordOp, valueIsWord, valueWord] at ha1
        subst ha1
        rw [BitVec.toNat_add_of_lt (by rw [hwi16]; omega), hwi16]
      have ha2_nat : a2.toNat = warr.toNat + 16 * wi.toNat + 8 := by
        simp [evalHOLExact, evalListHOLExact, harr, hi, panOpHOL, wordOpHOL, wordOp, valueIsWord, valueWord] at ha2
        subst ha2
        have h8 : (8#64 : BitVec 64).toNat = 8 := rfl
        have hwi16_8 : (wi * 16#64 + 8#64).toNat = 16 * wi.toNat + 8 := by
          rw [BitVec.toNat_add_of_lt (by rw [hwi16, h8]; omega), hwi16, h8]
        rw [BitVec.toNat_add_of_lt (by rw [hwi16_8]; omega), hwi16_8]; omega
      rw [ha1_nat] at hP_mem
      rw [ha2_nat] at hL_mem
      have hPL_fit : P.toNat + L.toNat ≤ 2 ^ 64 := by omega
      rw [hcode] at hlk
      obtain ⟨rfl, hcp, hcl⟩ := callee_p_len_vvh lookup_rlp_item_vvh _ _ cbody callee crs hlk
      obtain ⟨kind, pay, plen, tot, rfl, hplen_le, hpay_sub, _, _⟩ :=
        rlp_item_ret_sub_vvh (callEntryStateHOLFinite e callee) hcode P L hPL_fit hcp hcl vit hret
      refine R_raise_guard_vvh (fun _ _ _ => R_ret_vvh (fun v hv => ?_))
      simp [evalHOLExact, evalListHOLExact, huit] at hv
      subst hv
      exact ⟨pay, plen, rfl, by omega, fun hpos => by
        obtain ⟨hlo, hhi⟩ := hpay_sub hpos
        exact ⟨by omega, by omega⟩⟩
    · simp at hrest
  · simp at hargs

private theorem memW_stride_sum_kept_of_worldEff_vvh {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaReady s) (heff : WorldEff s post [] [] wsGw)
    (base stride count offset : Nat)
    (hoff : offset + 8 ≤ stride)
    (hheap : base + stride * count ≤ globN s "heap_ptr") :
    ((List.range count).map (fun i => memW post (base + stride * i + offset))).sum =
      ((List.range count).map (fun i => memW s (base + stride * i + offset))).sum := by
  have hmaps : (List.range count).map (fun i => memW post (base + stride * i + offset)) =
      (List.range count).map (fun i => memW s (base + stride * i + offset)) := by
    apply List.map_congr_left
    intro i hi
    have hi_lt : i < count := List.mem_range.mp hi
    have hmul := Nat.mul_le_mul_left stride (Nat.succ_le_of_lt hi_lt)
    rw [Nat.mul_succ] at hmul
    exact memW_kept_of_worldEff_lt_hp hAs heff (by omega)
  rw [hmaps]

/-! ### Section 5d: Trace Agreement for `rlp_list_count` and Slice Specification for `rlp_list_to_slices` -/

private def sliceOff_vvh (ts : List (BitVec 64)) (j : Nat) : Nat :=
  ((List.range j).map (fun r => (ts.getD r 0#64).toNat)).sum

private def CountTraceAt_vvh {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (P m : BitVec 64)
    (ts : List (BitVec 64)) (idx : Nat) (off : BitVec 64) : Prop :=
  off.toNat = sliceOff_vvh ts idx ∧
  off.toNat ≤ m.toNat ∧
  ∀ j < idx,
    1 ≤ (ts.getD j 0#64).toNat ∧
    sliceOff_vvh ts j + (ts.getD j 0#64).toNat ≤ m.toNat ∧
    ∀ (e2 : PanSemStateFiniteExact 64 F),
      e2.code = originalRuntimeCode →
      e2.locals.lookup (ofString "p") =
        some (.val (.word (P + BitVec.ofNat 64 (sliceOff_vvh ts j)))) →
      (∀ k < m.toNat - sliceOff_vvh ts j,
        memB e2 ((P + BitVec.ofNat 64 (sliceOff_vvh ts j)).toNat + k) =
          memB s0 ((P + BitVec.ofNat 64 (sliceOff_vvh ts j)).toNat + k)) →
      ∀ rv2 : ValueHOL 64,
        (evaluateHOLFiniteState e2 (sourceFnBody Guest.Software.guestFn_rlp_item_total_unchecked)).1 =
          some (.returned rv2) →
        rv2 = .val (.word (ts.getD j 0#64))

private def CountTraceInv_vvh {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (P m : BitVec 64)
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  WorldEff s0 s [] [] wsGw ∧
  ∃ (vis : Finset (Fin domainBytes)) (ts : List (BitVec 64)) (y c : BitVec 64),
    s.locals.lookup (ofString "p") = some (.val (.word P)) ∧
    s.locals.lookup (ofString "off") = some (.val (.word y)) ∧
    s.locals.lookup (ofString "len") = some (.val (.word m)) ∧
    s.locals.lookup (ofString "count") = some (.val (.word c)) ∧
    ts.length = c.toNat ∧
    c.toNat = vis.card ∧
    c.toNat ≤ y.toNat ∧
    CountTraceAt_vvh s0 P m ts c.toNat y ∧
    ∀ k ∈ vis, ∃ d : BitVec 64, d.toNat < y.toNat ∧
      sourceBase ≤ (P + d).toNat ∧ (P + d).toNat < heapEnd ∧
      k.val = (P + d).toNat - sourceBase

private theorem sliceOff_succ_vvh (ts : List (BitVec 64)) (j : Nat) :
    sliceOff_vvh ts (j + 1) = sliceOff_vvh ts j + (ts.getD j 0#64).toNat := by
  simp [sliceOff_vvh, List.range_succ, List.sum_append]

private theorem sliceOff_append_singleton_lt_vvh (ts : List (BitVec 64)) (T : BitVec 64)
    {j : Nat} (hj : j ≤ ts.length) :
    sliceOff_vvh (ts ++ [T]) j = sliceOff_vvh ts j := by
  unfold sliceOff_vvh
  congr 1
  apply List.map_congr_left
  intro r hr
  have hr_lt : r < ts.length := Nat.lt_of_lt_of_le (List.mem_range.mp hr) hj
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hr_lt]

private theorem countBody_trace_step_vvh {F : Type}
    (s0 s : PanSemStateFiniteExact 64 F) (P y m c : BitVec 64)
    (hAs0 : ArenaReady s0)
    (heff : WorldEff s0 s [] [] wsGw)
    (hfit : P.toNat + m.toNat ≤ 2 ^ 64)
    (hdj : IvlsDisj [(P.toNat, m.toNat)] [(globN s0 "heap_ptr", scratchEnd - globN s0 "heap_ptr")])
    (hp : s.locals.lookup (ofString "p") = some (.val (.word P)))
    (hy : s.locals.lookup (ofString "off") = some (.val (.word y)))
    (hm : s.locals.lookup (ofString "len") = some (.val (.word m)))
    (hc : s.locals.lookup (ofString "count") = some (.val (.word c)))
    (hlt : y.toNat < m.toNat)
    (hflow : (evaluateHOLFiniteState s countBody_vvh).1 = none) :
    let post := (evaluateHOLFiniteState s countBody_vvh).2
    WorldEff s0 post [] [] wsGw ∧
    ∃ T : BitVec 64,
      1 ≤ T.toNat ∧ y.toNat + T.toNat ≤ m.toNat ∧
      sourceBase ≤ (P + y).toNat ∧ (P + y).toNat < heapEnd ∧
      (∀ (e2 : PanSemStateFiniteExact 64 F),
        e2.code = originalRuntimeCode →
        e2.locals.lookup (ofString "p") = some (.val (.word (P + y))) →
        (∀ k < m.toNat - y.toNat, memB e2 ((P + y).toNat + k) = memB s0 ((P + y).toNat + k)) →
        ∀ rv2 : ValueHOL 64,
          (evaluateHOLFiniteState e2 (sourceFnBody Guest.Software.guestFn_rlp_item_total_unchecked)).1 =
            some (.returned rv2) →
          rv2 = .val (.word T)) ∧
      post.locals.lookup (ofString "off") = some (.val (.word (y + T))) ∧
      post.locals.lookup (ofString "count") = some (.val (.word (c + 1#64))) ∧
      post.locals.lookup (ofString "p") = some (.val (.word P)) ∧
      post.locals.lookup (ofString "len") = some (.val (.word m)) := by
  unfold countBody_vvh at hflow ⊢
  have heff_post : WorldEff s0 (evaluateHOLFiniteState s
      (.decCall (ofString "total") .one (ofString "rlp_item_total")
        [.op .add [.var .local (ofString "p"), .var .local (ofString "off")],
          .op .sub [.var .local (ofString "len"), .var .local (ofString "off")]]
        (.seq (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "total")]))
          (.assign .local (ofString "count") (.op .add [.var .local (ofString "count"), .const 1]))))).2 [] [] wsGw :=
    worldEff_decCall_eff heff (ofString "total") .one (ofString "rlp_item_total") _ _ _ _ lookup_rlp_item_total_vvh
      (fun callee cvals _ hlc hnt_cb hres_cb =>
        heff.trans_noBuf
          (WorldEff.from_locals_clock
            (worldEff_rlp_item_total_vvh (callEntryStateHOLFinite s callee) cvals
              heff.code (localsFree_arenaReady s callee _ heff.arena)
              (by simpa [heff.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
          ws_nil_sub_vvh ws_no_gb_vvh)
      (fun _ _ _ cpost _ _ _ _ heff_cp hnt_k hcr_k =>
        worldEff_seq hnt_k hcr_k
          (fun _ _ => worldEff_assign_local (heff_cp.locals_clock _ _) _ _)
          (fun _ _ heff_m2 _ _ => worldEff_assign_local heff_m2 _ _))
      (by rw [hflow]; simp) (by rw [hflow]; exact Or.inl rfl)
  obtain ⟨values, body, callee, rs, v, hargs, hl, hret, u, hcu, hloc, hu, hcont, hfin⟩ := decCall_flow_vvh hflow
  simp only [evalListHOLFinite_eq_toExact, evalListHOLExact, evalHOLExact, hp, hy, hm,
    wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self,
    ↓reduceIte, List.foldr, add_zero, Option.some.injEq] at hargs
  subst hargs
  have hcode : s.code = originalRuntimeCode := heff.code
  have hG : GuestInv s := heff.arena.1
  rw [hcode] at hl
  obtain ⟨rfl, hcp, hcl⟩ := callee_p_len_vvh lookup_rlp_item_total_vvh _ _ body callee rs hl
  have hsub : (m - y).toNat = m.toNat - y.toNat := by rw [BitVec.toNat_sub]; omega
  have hpy_nat : (P + y).toNat = P.toNat + y.toNat :=
    BitVec.toNat_add_of_lt (by omega)
  have hsub_fit : (P + y).toNat + (m - y).toNat ≤ 2 ^ 64 := by omega
  obtain ⟨T_dom, rfl, hT1, hT2, hpy_lo, hpy_hi⟩ :=
    total_post_dom_vvh (callEntryStateHOLFinite s callee) hcode (guestInv_callEntry s callee hG)
      (P + y) (m - y) hcp hcl v hret
  obtain ⟨T', hv_eq, _, _, hagree_s⟩ :=
    rlp_item_total_agree_unchecked_vvh (callEntryStateHOLFinite s callee) hcode (P + y) (m - y)
      hsub_fit hcp hcl (.val (.word T_dom)) hret
  injection hv_eq with hv_eq'; injection hv_eq' with hT_eq; subst hT_eq
  rw [hsub] at hT2 hagree_s
  have hbytes_s_s0 : ∀ k < m.toNat - y.toNat, memB s ((P + y).toNat + k) = memB s0 ((P + y).toNat + k) := by
    intro k hk
    exact memB_kept_of_worldEff_disj hAs0 heff hfit hdj (by omega) (by omega)
  have huoff : u.locals.lookup (ofString "off") = some (.val (.word y)) := by
    rw [hloc _ (by decide)]; exact hy
  have hucnt : u.locals.lookup (ofString "count") = some (.val (.word c)) := by
    rw [hloc _ (by decide)]; exact hc
  have hup : u.locals.lookup (ofString "p") = some (.val (.word P)) := by
    rw [hloc _ (by decide)]; exact hp
  have hulen : u.locals.lookup (ofString "len") = some (.val (.word m)) := by
    rw [hloc _ (by decide)]; exact hm
  have hfirst : evaluateHOLFiniteState u
      (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "total")])) =
      (none, setKvarHOLFinite .local (ofString "off") (.val (.word (y + T_dom))) u) := by
    rw [evaluateHOLFiniteState_assign]
    simp [evalHOLExact, evalListHOLExact, huoff, hu, wordOpHOL, wordOp, valueIsWord, valueWord,
      isValidValueHOLFinite, lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL]
  let u1 := setKvarHOLFinite .local (ofString "off") (.val (.word (y + T_dom))) u
  have hu1_cnt : u1.locals.lookup (ofString "count") = some (.val (.word c)) := by
    simp [u1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hucnt,
      show ofString "off" ≠ ofString "count" by decide]
  have hsecond : evaluateHOLFiniteState u1
      (.assign .local (ofString "count") (.op .add [.var .local (ofString "count"), .const 1])) =
      (none, setKvarHOLFinite .local (ofString "count") (.val (.word (c + 1#64))) u1) := by
    rw [evaluateHOLFiniteState_assign]
    simp [evalHOLExact, evalListHOLExact, hu1_cnt, wordOpHOL, wordOp, valueIsWord, valueWord,
      isValidValueHOLFinite, lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL]
  refine ⟨heff_post, T_dom, hT1, by omega, hpy_lo, hpy_hi, ?_, ?_, ?_, ?_, ?_⟩
  · intro e2 hc2 hp2 hbytes2 rv2 hret2
    exact hagree_s e2 hc2 hp2 (fun k hk => (hbytes2 k hk).trans (hbytes_s_s0 k hk).symm) rv2 hret2
  · rw [hfin (ofString "off") (by decide), evaluateHOLFiniteState_seq_line780, hfirst]; dsimp only
    rw [hsecond]; dsimp only
    simp [u1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "count" ≠ ofString "off" by decide]
  · rw [hfin (ofString "count") (by decide), evaluateHOLFiniteState_seq_line780, hfirst]; dsimp only
    rw [hsecond]; dsimp only
    simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · rw [hfin (ofString "p") (by decide), evaluateHOLFiniteState_seq_line780, hfirst]; dsimp only
    rw [hsecond]; dsimp only
    simp [u1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hup,
      show ofString "count" ≠ ofString "p" by decide, show ofString "off" ≠ ofString "p" by decide]
  · rw [hfin (ofString "len") (by decide), evaluateHOLFiniteState_seq_line780, hfirst]; dsimp only
    rw [hsecond]; dsimp only
    simp [u1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hulen,
      show ofString "count" ≠ ofString "len" by decide, show ofString "off" ≠ ofString "len" by decide]

private theorem while_countTraceInv_vvh {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (P m : BitVec 64)
    (hAs0 : ArenaReady s0)
    (hfit : P.toNat + m.toNat ≤ 2 ^ 64)
    (hdj : IvlsDisj [(P.toNat, m.toNat)] [(globN s0 "heap_ptr", scratchEnd - globN s0 "heap_ptr")])
    (k : Nat) (s post : PanSemStateFiniteExact 64 F)
    (hclk : s.clock ≤ k) (hinv : CountTraceInv_vvh s0 P m s)
    (hrun : evaluateHOLFiniteState s (.while countCond_vvh countBody_vvh) = (none, post)) :
    CountTraceInv_vvh s0 P m post ∧
    @evalHOLExact 64 F _ post.toExact (fun a => Classical.propDecidable (post.memaddrs a)) countCond_vvh =
      some (.val (.word 0)) := by
  induction k generalizing s with
  | zero =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · split at hrun <;> [simp at hrun; omega]
      · rename_i hnotnz
        have hcw0 : cw = 0 := Classical.not_not.1 hnotnz
        subst hcw0; simp at hrun; subst hrun; exact ⟨hinv, hcond⟩
    · simp at hrun
  | succ k ih =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · rename_i hnz
        split at hrun
        · simp at hrun
        · dsimp only at hrun
          rw [fixClockHOLFinite_evaluateState] at hrun
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) countBody_vvh
          have hbc := countBody_no_bc_vvh (decClockHOLFinite s)
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) countBody_vvh with ⟨r1, mid⟩
          rw [hbr] at hrun rem hbc
          cases r1 with
          | none =>
            obtain ⟨heff_s, vis, ts, y, c, hp, hy, hm, hc_cnt, hts_len, hcard, hcy, htr, hvis⟩ := hinv
            obtain ⟨hy_off, hym, htr_j⟩ := htr
            have hlt : y.toNat < m.toNat := by
              simp [countCond_vvh, evalHOLExact, hy, hm, Compiler.Encoders.Asm.wordCmpHOL] at hcond
              by_contra hge
              have hge' : ¬ (y < m) := by rw [BitVec.lt_def]; omega
              simp [hge'] at hcond
              exact hnz hcond.symm
            let sd := decClockHOLFinite s
            have heff_sd : WorldEff s0 sd [] [] wsGw := heff_s.locals_clock s.locals (s.clock - 1)
            obtain ⟨heff_mid, T, hT1, hyT_le, hpy_lo, hpy_hi, hagree_T, hm_off, hm_cnt, hm_p, hm_len⟩ :=
              countBody_trace_step_vvh s0 sd P y m c hAs0 heff_sd hfit hdj hp hy hm hc_cnt hlt (by rw [hbr])
            rw [hbr] at heff_mid hm_off hm_cnt hm_p hm_len
            dsimp only at heff_mid hm_off hm_cnt hm_p hm_len
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
            have hdb_lt : domainBytes < 2 ^ 64 := by decide
            have hc1_nat : (c + 1#64).toNat = c.toNat + 1 :=
              BitVec.toNat_add_of_lt (by change c.toNat + 1 < 2 ^ 64; omega)
            have hyT_nat : (y + T).toNat = y.toNat + T.toNat :=
              BitVec.toNat_add_of_lt (by have := m.isLt; omega)
            have hgetD_last : (ts ++ [T]).getD c.toNat 0#64 = T := by
              rw [List.getD_eq_getElem?_getD, ← hts_len, List.getElem?_append_right le_rfl,
                Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            have hinv_mid : CountTraceInv_vvh s0 P m mid := by
              refine ⟨heff_mid, insert k_now vis, ts ++ [T], y + T, c + 1#64,
                hm_p, hm_off, hm_len, hm_cnt, by simp [hts_len, hc1_nat], by omega, by omega, ?_, ?_⟩
              · refine ⟨?_, by omega, ?_⟩
                · rw [hyT_nat, hc1_nat, sliceOff_succ_vvh, sliceOff_append_singleton_lt_vvh ts T (by omega),
                    hgetD_last, hy_off]
                · intro j hj
                  rw [hc1_nat] at hj
                  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt | rfl
                  · have hgetD_j : (ts ++ [T]).getD j 0#64 = ts.getD j 0#64 := by
                      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
                        List.getElem?_append_left (by omega)]
                    have hoff_j : sliceOff_vvh (ts ++ [T]) j = sliceOff_vvh ts j :=
                      sliceOff_append_singleton_lt_vvh ts T (by omega)
                    rw [hgetD_j, hoff_j]
                    exact htr_j j hj_lt
                  · have hoff_c : sliceOff_vvh (ts ++ [T]) c.toNat = y.toNat := by
                      rw [sliceOff_append_singleton_lt_vvh ts T (by omega), ← hy_off]
                    have hy_bv : BitVec.ofNat 64 y.toNat = y := by simp
                    rw [hgetD_last, hoff_c, hy_bv]
                    exact ⟨hT1, hyT_le, hagree_T⟩
              · intro k' hk'
                rcases Finset.mem_insert.mp hk' with rfl | hk'
                · exact ⟨y, by omega, hpy_lo, hpy_hi, rfl⟩
                · obtain ⟨d, hd, h1, h2, h3⟩ := hvis k' hk'
                  exact ⟨d, by omega, h1, h2, h3⟩
            exact ih mid (by change mid.clock ≤ s.clock - 1 at rem; omega) hinv_mid hrun
          | some r1 =>
            cases r1 with
            | «continue» => exact absurd rfl hbc.2
            | «break» => exact absurd rfl hbc.1
            | _ => simp at hrun
      · rename_i hnotnz
        have hcw0 : cw = 0 := Classical.not_not.1 hnotnz
        subst hcw0; simp at hrun; subst hrun; exact ⟨hinv, hcond⟩
    · simp at hrun

private theorem rlp_list_count_trace_vvh {F : Type}
    (s cpost : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64)) (rv : ValueHOL 64)
    (hc : s.code = originalRuntimeCode) (hAs : ArenaReady s)
    (P m : BitVec 64)
    (hvals : vals = [.val (.word P), .val (.word m)])
    (hfit : P.toNat + m.toNat ≤ 2 ^ 64)
    (hdj : IvlsDisj [(P.toNat, m.toNat)] [(globN s "heap_ptr", scratchEnd - globN s "heap_ptr")])
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_list_count") vals =
      some (sourceFnBody Guest.Software.guestFn_rlp_list_count, s.locals, .one))
    (hret : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_count) =
      (some (.returned rv), cpost)) :
    ∃ (wcnt : BitVec 64) (ts : List (BitVec 64)),
      rv = .val (.word wcnt) ∧
      wcnt.toNat ≤ domainBytes ∧
      wcnt.toNat ≤ m.toNat ∧
      ts.length = wcnt.toNat ∧
      CountTraceAt_vvh s P m ts wcnt.toNat m := by
  subst hvals
  obtain ⟨-, hp, hm⟩ := callee_p_len_vvh lookup_rlp_list_count_vvh (.val (.word P)) (.val (.word m)) _ s.locals _ hl
  have hbody : sourceFnBody Guest.Software.guestFn_rlp_list_count =
      .dec (ofString "count") .one (.const 0)
        (.dec (ofString "off") .one (.const 0)
          (.seq (.while countCond_vvh countBody_vvh)
            (.return (.var .local (ofString "count"))))) := rfl
  have hret1 : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_count)).1 =
      some (.returned rv) := by rw [hret]
  clear hret
  rw [hbody] at hret1
  revert rv hret1
  change RetOK_vvh (fun rv => ∃ (wcnt : BitVec 64) (ts : List (BitVec 64)),
    rv = .val (.word wcnt) ∧ wcnt.toNat ≤ domainBytes ∧ wcnt.toNat ≤ m.toNat ∧
    ts.length = wcnt.toNat ∧ CountTraceAt_vvh s P m ts wcnt.toNat m) s _
  refine R_dec_vvh (fun vcnt hvcnt _ => ?_)
  have hvcnt_eq : vcnt = .val (.word 0) := by simp [evalHOLExact] at hvcnt; exact hvcnt.symm
  subst hvcnt_eq
  refine R_dec_vvh (fun voff hvoff _ => ?_)
  have hvoff_eq : voff = .val (.word 0) := by simp [evalHOLExact] at hvoff; exact hvoff.symm
  subst hvoff_eq
  let s2 := setVarHOLFinite (ofString "off") (.val (.word 0))
    (setVarHOLFinite (ofString "count") (.val (.word 0)) s)
  have heff2 : WorldEff s s2 [] [] wsGw :=
    ((WorldEff.refl s [] [] wsGw hAs hc).locals_clock _ _).locals_clock _ _
  have hinv2 : CountTraceInv_vvh s P m s2 := by
    refine ⟨heff2, ∅, [], 0, 0, ?_, ?_, ?_, ?_, rfl, by simp, by simp, ?_, by simp⟩
    · simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp,
        show ofString "off" ≠ ofString "p" by decide, show ofString "count" ≠ ofString "p" by decide]
    · simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm,
        show ofString "off" ≠ ofString "len" by decide, show ofString "count" ≠ ofString "len" by decide]
    · simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "off" ≠ ofString "count" by decide]
    · refine ⟨by simp [sliceOff_vvh], by simp, fun j hj => by simp at hj⟩
  refine R_seq_vvh (fun rv hw => absurd hw (while_count_no_return_vvh rv s2.clock s2 le_rfl))
    (fun mid hmid => ?_)
  obtain ⟨⟨_, vis, ts, y, c, _, hm_off, hm_len, hm_cnt, hts_len, hcard, hcy, htr, _⟩, hcond0⟩ :=
    while_countTraceInv_vvh s P m hAs hfit hdj s2.clock s2 mid le_rfl hinv2 hmid
  have hy_ge_m : m.toNat ≤ y.toNat := by
    simp [countCond_vvh, evalHOLExact, hm_off, hm_len, Compiler.Encoders.Asm.wordCmpHOL] at hcond0
    exact BitVec.le_def.mp hcond0
  have hy_eq_m : y = m := BitVec.eq_of_toNat_eq (by have := htr.2.1; omega)
  subst hy_eq_m
  refine R_ret_vvh (fun v hv => ?_)
  simp [evalHOLExact, hm_cnt] at hv; subst hv
  have hle : vis.card ≤ domainBytes := by simpa using Finset.card_le_univ vis
  exact ⟨c, ts, rfl, by omega, by omega, hts_len, htr⟩

theorem «wk_decode_transaction_noExtra» :
    WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
     ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "decode_transaction") :=
  ⟨_, _, _, lookup_decode_transaction_vvh, fun s hc hWOK ⟨vals, hl⟩ hnt hres =>
    (worldEff_decode_transaction_vvh s vals hc hWOK.1 hl hnt hres).to_worldStep_Q
      hWOK (fun _ h => by cases h) ws_core_out_vvh (fun _ _ _ _ _ _ _ _ => trivial)⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
