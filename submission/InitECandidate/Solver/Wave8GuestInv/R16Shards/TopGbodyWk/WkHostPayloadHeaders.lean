import InitECandidate.Solver.Wave8GuestInv.ContractParts.C08
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkCacheGetRootTop
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_max

/-!
# R16k Shard `WkHostPayloadHeaders`: Host Input, SSZ HTR, Header Validation, Trie/NodeDb, and Payload Header

Proves the 7 `WorldKeeps` theorems:
1. `«wk_htr_new_payload_request»`
2. `«wk_validate_header»`
3. `«wk_validate_headers»`
4. `«wk_nodedb_build»`
5. `«wk_decode_host_input»`
6. `«wk_mpt_from_witness»`
7. `«wk_payload_header»`
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

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk

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

/-! ## Section 1: SSZ / HTR Helpers & `«wk_htr_new_payload_request»` -/

private abbrev sszBufs : List (String × Nat) := [("ssz_len_chunk", 32)]
private abbrev hpGw : List String := ["heap_ptr"]

private theorem ssz_B_sub : ∀ gs ∈ sszBufs, gs ∈ globalBuffers := by decide
private theorem ssz_B_ok : ∀ gs ∈ sszBufs, gs ∈ globalBuffers ∧ gs.1 ∉ typedRecords.map Prod.fst := by decide
private theorem hp_no_gb : ∀ gs ∈ globalBuffers, ofString gs.1 ∉ hpGw.map ofString := by decide
private theorem hp_core_out : ∀ g ∈ coreWorldGlobals, ofString g ∉ hpGw.map ofString := by decide

private theorem ro_ceil_log2 : ReadOnlyFn (ofString "ceil_log2") :=
  InitECandidate.Solver.Wave8Contracts.M15.readOnlyFn_of_guestAst 36
    (by rw [guestAst_len]; decide) Guest.Software.guestFn_ceil_log2 rfl
    (fun _ => false) (fun _ h => by cases h) rfl

private theorem ro_max_fn : ReadOnlyFn (ofString "max") :=
  InitECandidate.Solver.Wave8Contracts.M15.«ro_max»

private theorem call0_or_resumes {F : Type}
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

private theorem call0_none_locals {F : Type}
    (s : PanSemStateFiniteExact 64 F) (fn : MlS) (args : List (ExpHOL 64))
    (hnone : (evaluateHOLFiniteState s (.call (some (none, none)) fn args)).1 = none) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fn args)).2.locals = s.locals := by
  rw [evaluateHOLFiniteState_call] at hnone ⊢
  unfold evalListHOLFinite at hnone ⊢
  rcases h1 : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [h1] at hnone
  · simp only [h1] at hnone ⊢
    rcases h2 : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fn vs with _ | ⟨b, c, r⟩
    · simp [h2] at hnone
    · simp only [h2] at hnone ⊢
      split at hnone
      · simp at hnone
      · rename_i hcz; rw [if_neg hcz]
        rcases h3 : evaluateHOLFiniteState (callEntryStateHOLFinite s c) b with ⟨rb, sb⟩
        simp only [h3] at hnone ⊢
        rcases rb with _ | rb'
        · simp at hnone
        · cases rb' with
          | returned rv =>
            dsimp only at hnone ⊢
            split at hnone
            · rename_i hsh; rw [if_pos hsh]
            · simp at hnone
          | _ => simp at hnone

private theorem worldEff_call0_funByteEff {F : Type}
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
  h.of_byteEff
    (call0_byteEff hf cur args Sub h.code h.arena.1 hsub_args hnt (call0_or_resumes cur fname args hcr))
    hsub_world

private theorem worldEff_call_local_alloc {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    (hgw_hp : ofString "heap_ptr" ∈ gw.map ofString)
    (name : MlS) (szExp : ExpHOL 64)
    (hname_ok : ∃ oldw : BitVec 64, cur.locals.lookup name = some (.val (.word oldw)))
    (hnt : (evaluateHOLFiniteState cur (.call (some (some (.local, name), none)) (ofString "alloc") [szExp])).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call (some (some (.local, name), none)) (ofString "alloc") [szExp])).1) :
    WorldEff s (evaluateHOLFiniteState cur (.call (some (some (.local, name), none)) (ofString "alloc") [szExp])).2 Rl B gw ∧
    ((evaluateHOLFiniteState cur (.call (some (some (.local, name), none)) (ofString "alloc") [szExp])).1 = none →
      ∃ (pw nw : BitVec 64),
        @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) szExp = some (.val (.word nw)) ∧
        (evaluateHOLFiniteState cur (.call (some (some (.local, name), none)) (ofString "alloc") [szExp])).2.locals =
          cur.locals.update (name, .val (.word pw)) ∧
        globN s "heap_ptr" ≤ pw.toNat ∧
        pw.toNat + (nw.toNat + 7) / 8 * 8 =
          globN (evaluateHOLFiniteState cur (.call (some (some (.local, name), none)) (ofString "alloc") [szExp])).2 "heap_ptr" ∧
        globN (evaluateHOLFiniteState cur (.call (some (some (.local, name), none)) (ofString "alloc") [szExp])).2 "heap_ptr" ≤ heapLimit) := by
  rw [evaluateHOLFiniteState_call] at hnt hcr ⊢
  rcases hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) [szExp] with _ | values
  · exact ⟨h, fun hn => by simp at hn⟩
  · simp only [hargs] at hnt hcr ⊢
    rcases hl : lookupCodeHOLFinite cur.code.lookup (ofString "alloc") values with _ | ⟨body', callee, ret'⟩
    · exact ⟨h, fun hn => by simp at hn⟩
    · simp only [hl] at hnt hcr ⊢
      by_cases hz : cur.clock = 0
      · rw [if_pos hz] at hnt; exact absurd rfl hnt
      · rw [if_neg hz] at hnt hcr ⊢
        have hsame := lookupCodeHOLFinite_installed_body cur.code.lookup (ofString "alloc") _ _ body'
          _ ret' values callee (by rw [h.code]; exact lookup_alloc) hl
        subst hsame
        have hret_eq := lookupCodeHOLFinite_installed_return cur (ofString "alloc") _ _ _
          _ ret' values callee (by rw [h.code]; exact lookup_alloc) hl
        subst hret_eq
        obtain ⟨nw, rfl, hnw_callee⟩ := lookupCode_one_word lookup_alloc (by rwa [← h.code])
        have hsz_ev : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) szExp =
            some (.val (.word nw)) := by
          rw [evalListHOLFinite_eq_toExact] at hargs
          simp only [evalListHOLExact] at hargs
          split at hargs <;> simp at hargs
          rename_i v hv _; rw [hargs.1] at hv; exact hv
        obtain ⟨pw, hpw_lk⟩ : ∃ pw : BitVec 64, cur.globals.lookup (ofString "heap_ptr") = some (.val (.word pw)) :=
          globalWord_of_globN_pos cur "heap_ptr" (by have := h.arena.2.1; rw [sourceBase_val] at this; omega)
        let entry := callEntryStateHOLFinite cur callee
        rcases hrun : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_alloc) with ⟨res, pa⟩
        dsimp only [entry] at hrun
        simp only [hrun] at hnt hcr ⊢
        have hres_a : Resumes res := by
          cases res with
          | none => rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
          | some r1 =>
            cases r1 with
            | returned rv => exact Or.inl ⟨rv, rfl⟩
            | exception eid ev =>
              rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨e', v', hc0, hne⟩⟩
              · simp at hc0
              · simp at hc0
              · simp at hc0
              · simp at hc0
              · change some (PanSemResultExact.exception eid ev) = some (PanSemResultExact.exception e' v') at hc0
                injection hc0 with hc0'; injection hc0' with he1 he2; subst he1 he2
                exact Or.inr ⟨eid, ev, rfl, hne⟩
            | timeOut => exact absurd rfl hnt
            | _ => rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
        have hal := InitECandidate.Solver.Wave8GuestInv.R13.alloc_body_resumes entry pw h.code hpw_lk
          (by dsimp only [entry]; rw [hrun]; exact hres_a)
        dsimp only [entry] at hal
        rw [hrun] at hal
        obtain ⟨nw', hnw'_lk, hrv_eq, hcmp1, hcmp2, hpa_eq⟩ := hal
        have hnw_eq : nw = nw' := by
          have : entry.locals.lookup (ofString "n") = some (.val (.word nw)) := hnw_callee
          rw [this] at hnw'_lk; injection hnw'_lk with h'; injection h' with h'; injection h'
        subst hnw_eq
        dsimp only at hrv_eq hpa_eq
        subst hrv_eq
        obtain ⟨oldw, holdw⟩ := hname_ok
        have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word pw) : ValueHOL 64)) .one = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        have hval_ok : isValidValueHOLExact cur.toExact .local name (.val (.word pw)) = true := by
          simp [isValidValueHOLExact, lookupKvarHOLExact, toExact, holdw, shapeOfHOLExact, shapeEqHOL]
        dsimp only
        rw [if_pos hsh, if_pos hval_ok]
        let mid := setKvarHOLFinite .local name (.val (.word pw)) { pa with locals := cur.locals }
        have hmid_next : mid = { cur with
            globals := cur.globals.update (ofString "heap_ptr", .val (.word ((pw + (nw + 7)) &&& ((0 : BitVec 64) - 8)))),
            locals := mid.locals, clock := mid.clock } := by
          dsimp only [mid, setKvarHOLFinite, setVarHOLFinite]; rw [hpa_eq]; rfl
        obtain ⟨heff_m, _, _, _, hp_lo_s, hp_add, hp_hi, _⟩ :=
          worldEff_alloc_step h hgw_hp hpw_lk hcmp1 hcmp2 hmid_next
        exact ⟨heff_m, fun _ => ⟨pw, nw, hsz_ev, rfl, hp_lo_s, hp_add, hp_hi⟩⟩

private theorem lookupCode_five_words {fname p1 p2 p3 p4 p5 : MlS} {body : ProgHOL 64} {vals : List (ValueHOL 64)}
    {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4) (h15 : p1 ≠ p5)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h25 : p2 ≠ p5)
    (h34 : p3 ≠ p4) (h35 : p3 ≠ p5) (h45 : p4 ≠ p5)
    (hlook : originalRuntimeCode.lookup fname =
      some ([(p1, .one), (p2, .one), (p3, .one), (p4, .one), (p5, .one)], body, .one))
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, L, .one)) :
    ∃ w1 w2 w3 w4 w5 : BitVec 64,
      vals = [.val (.word w1), .val (.word w2), .val (.word w3), .val (.word w4), .val (.word w5)] ∧
      L.lookup p1 = some (.val (.word w1)) ∧
      L.lookup p2 = some (.val (.word w2)) ∧
      L.lookup p3 = some (.val (.word w3)) ∧
      L.lookup p4 = some (.val (.word w4)) ∧
      L.lookup p5 = some (.val (.word w5)) := by
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup fname vals body L .one hl
  simp only [lookupCodeHOLExact, hlook] at hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, _ | ⟨v5, _ | _⟩⟩⟩⟩⟩
  · simp at hx
  · simp at hx
  · simp at hx
  · simp at hx
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;>
      rcases v3 with ⟨⟨w3⟩⟩ | _ | _ <;> rcases v4 with ⟨⟨w4⟩⟩ | _ | _ <;>
      rcases v5 with ⟨⟨w5⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hx
    obtain ⟨_, hL⟩ := hx
    refine ⟨w1, w2, w3, w4, w5, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (rw [← hL]; simp [h12, h13, h14, h15, h23, h24, h25, h34, h35, h45,
        Ne.symm h12, Ne.symm h13, Ne.symm h14, Ne.symm h15, Ne.symm h23,
        Ne.symm h24, Ne.symm h25, Ne.symm h34, Ne.symm h35, Ne.symm h45])
  · simp at hx

private theorem lookup_mix_in_length :
    originalRuntimeCode.lookup (ofString "mix_in_length") =
      some ([(ofString "root", .one), (ofString "len", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_mix_in_length, .one) :=
  lookup_of_guestAst_getElem 187 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mix_in_length) rfl

private theorem lookup_htr_u64_at :
    originalRuntimeCode.lookup (ofString "htr_u64_at") =
      some ([(ofString "p", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_htr_u64_at, .one) :=
  lookup_of_guestAst_getElem 195 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htr_u64_at) rfl

private theorem lookup_pack_bytes :
    originalRuntimeCode.lookup (ofString "pack_bytes") =
      some ([(ofString "p", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_pack_bytes, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 192 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_pack_bytes) rfl

private theorem lookup_merkleize :
    originalRuntimeCode.lookup (ofString "merkleize") =
      some ([(ofString "p", .one), (ofString "n", .one), (ofString "limit", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_merkleize, .one) :=
  lookup_of_guestAst_getElem 186 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_merkleize) rfl

private theorem lookup_merkleize_progressive :
    originalRuntimeCode.lookup (ofString "merkleize_progressive") =
      some ([(ofString "p", .one), (ofString "n", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_merkleize_progressive, .one) :=
  lookup_of_guestAst_getElem 188 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_merkleize_progressive) rfl

private theorem lookup_htr_plist_chunks :
    originalRuntimeCode.lookup (ofString "htr_plist_chunks") =
      some ([(ofString "roots", .one), (ofString "n", .one), (ofString "len", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_htr_plist_chunks, .one) :=
  lookup_of_guestAst_getElem 189 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htr_plist_chunks) rfl

private theorem lookup_htr_pbytes :
    originalRuntimeCode.lookup (ofString "htr_pbytes") =
      some ([(ofString "p", .one), (ofString "n", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_htr_pbytes, .one) :=
  lookup_of_guestAst_getElem 190 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htr_pbytes) rfl

private theorem lookup_htr_pcontainer :
    originalRuntimeCode.lookup (ofString "htr_pcontainer") =
      some ([(ofString "ch", .one), (ofString "n", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_htr_pcontainer, .one) :=
  lookup_of_guestAst_getElem 191 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htr_pcontainer) rfl

private theorem lookup_htr_bytes_vector :
    originalRuntimeCode.lookup (ofString "htr_bytes_vector") =
      some ([(ofString "p", .one), (ofString "n", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_htr_bytes_vector, .one) :=
  lookup_of_guestAst_getElem 193 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htr_bytes_vector) rfl

private theorem lookup_htr_bytes_list :
    originalRuntimeCode.lookup (ofString "htr_bytes_list") =
      some ([(ofString "p", .one), (ofString "n", .one), (ofString "limit_chunks", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_htr_bytes_list, .one) :=
  lookup_of_guestAst_getElem 194 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htr_bytes_list) rfl

private theorem lookup_htr_withdrawal :
    originalRuntimeCode.lookup (ofString "htr_withdrawal") =
      some ([(ofString "w", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_htr_withdrawal, .one) :=
  lookup_of_guestAst_getElem 208 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htr_withdrawal) rfl

private theorem lookup_htr_payload :
    originalRuntimeCode.lookup (ofString "htr_payload") =
      some ([(ofString "pl", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_htr_payload, .one) :=
  lookup_of_guestAst_getElem 210 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htr_payload) rfl

private theorem lookup_htr_deposit :
    originalRuntimeCode.lookup (ofString "htr_deposit") =
      some ([(ofString "e", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_htr_deposit, .one) :=
  lookup_of_guestAst_getElem 211 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htr_deposit) rfl

private theorem lookup_htr_wdreq :
    originalRuntimeCode.lookup (ofString "htr_wdreq") =
      some ([(ofString "e", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_htr_wdreq, .one) :=
  lookup_of_guestAst_getElem 212 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htr_wdreq) rfl

private theorem lookup_htr_cons :
    originalRuntimeCode.lookup (ofString "htr_cons") =
      some ([(ofString "e", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_htr_cons, .one) :=
  lookup_of_guestAst_getElem 213 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htr_cons) rfl

private theorem lookup_htr_bdep :
    originalRuntimeCode.lookup (ofString "htr_bdep") =
      some ([(ofString "e", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_htr_bdep, .one) :=
  lookup_of_guestAst_getElem 214 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htr_bdep) rfl

private theorem lookup_htr_bexit :
    originalRuntimeCode.lookup (ofString "htr_bexit") =
      some ([(ofString "e", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_htr_bexit, .one) :=
  lookup_of_guestAst_getElem 215 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htr_bexit) rfl

private theorem lookup_htr_request_list :
    originalRuntimeCode.lookup (ofString "htr_request_list") =
      some ([(ofString "kind", .one), (ofString "p", .one), (ofString "n", .one), (ofString "sz", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_htr_request_list, .one) :=
  lookup_of_guestAst_getElem 216 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htr_request_list) rfl

private theorem lookup_htr_requests :
    originalRuntimeCode.lookup (ofString "htr_requests") =
      some ([(ofString "rq", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_htr_requests, .one) :=
  lookup_of_guestAst_getElem 217 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htr_requests) rfl

private theorem lookup_htr_new_payload_request :
    originalRuntimeCode.lookup (ofString "htr_new_payload_request") =
      some ([(ofString "si", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_htr_new_payload_request, .one) :=
  lookup_of_guestAst_getElem 218 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htr_new_payload_request) rfl

private theorem funByteEff_htr_u64_at :
    FunByteEff (ofString "htr_u64_at")
      (fun vals _ => [(valWordNat (vals[1]?.getD (.rStruct [])), 32)]) := by
  refine ⟨_, _, _, lookup_htr_u64_at, fun {F} entry vals hc hG hl hnt hres => ?_⟩
  obtain ⟨pw, outw, rfl, hp, hout⟩ := lookupCode_two_words (by decide) lookup_htr_u64_at hl
  let Rl := [(outw.toNat, 32)]
  change ByteEff entry (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_htr_u64_at)).2 Rl
  have hbody : sourceFnBody Guest.Software.guestFn_htr_u64_at =
      .seq (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "out"), .const 32])
        (.seq (.call (some (none, none)) (ofString "memcpy")
            [.var .local (ofString "out"), .var .local (ofString "p"), .const 8])
          (.return (.const 0))) := rfl
  rw [hbody] at hnt hres ⊢
  rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
  rcases hm1 : evaluateHOLFiniteState entry
      (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "out"), .const 32]) with ⟨r1, s1⟩
  rw [hm1] at hnt hres
  have hargs1 : evalListHOLFinite entry (h := fun a => Classical.propDecidable (entry.memaddrs a))
      [.var .local (ofString "out"), .const 32] = some [.val (.word outw), .val (.word 32)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hout]
  have heff1 : ByteEff entry s1 Rl := by
    have := call0_byteEff funByteEff_memzero entry _ Rl hc hG
      (fun vs hvs i hi _ => by
        rw [hargs1] at hvs; injection hvs with hvs; subst hvs
        simp [valWordNat] at hi; subst hi
        exact ⟨(outw.toNat, 32), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
      (by rw [hm1]; intro h; subst h; simp at hnt)
      (by rw [hm1]; cases r1 with | none => exact Or.inl rfl | some _ => exact Or.inr hres)
    rwa [hm1] at this
  cases r1 with
  | some _ => exact heff1
  | none =>
    have hs1_loc : s1.locals = entry.locals := by
      have := call0_none_locals entry (ofString "memzero") [.var .local (ofString "out"), .const 32] (by rw [hm1])
      rwa [hm1] at this
    dsimp only at hnt hres ⊢
    rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
    rcases hm2 : evaluateHOLFiniteState s1
        (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "out"), .var .local (ofString "p"), .const 8]) with ⟨r2, s2⟩
    rw [hm2] at hnt hres
    have hGs1 : GuestInv s1 := guestInv_congr heff1.code heff1.memaddrs heff1.shMemaddrs heff1.baseAddr hG
    have hc1 : s1.code = originalRuntimeCode := heff1.code.trans hc
    have hargs2 : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
        [.var .local (ofString "out"), .var .local (ofString "p"), .const 8] =
        some [.val (.word outw), .val (.word pw), .val (.word 8)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs1_loc, hout, hp]
    have heff2 : ByteEff s1 s2 Rl := by
      have := call0_byteEff funByteEff_memcpy s1 _ Rl hc1 hGs1
        (fun vs hvs i hi _ => by
          rw [hargs2] at hvs; injection hvs with hvs; subst hvs
          simp [valWordNat] at hi; subst hi
          exact ⟨(outw.toNat, 32), List.mem_singleton.2 rfl, le_rfl, by omega⟩)
        (by rw [hm2]; intro h; subst h; simp at hnt)
        (by rw [hm2]; cases r2 with | none => exact Or.inl rfl | some _ => exact Or.inr hres)
      rwa [hm2] at this
    cases r2 with
    | some _ => exact heff1.trans heff2
    | none => exact (heff1.trans heff2).trans (byteEff_return s2 _ _)

private theorem funByteEff_mix_in_length :
    FunByteEff (ofString "mix_in_length")
      (fun vals G => [globBufIvl G "ssz_len_chunk" 32, (valWordNat (vals[2]?.getD (.rStruct [])), 32)]) := by
  refine ⟨_, _, _, lookup_mix_in_length, fun {F} entry vals hc hG hl hnt hres => ?_⟩
  obtain ⟨rootw, lenw, outw, rfl, hroot, hlen, hout⟩ :=
    lookupCode_three_words (by decide) (by decide) (by decide) lookup_mix_in_length hl
  let Rl := [globBufIvl entry.globals "ssz_len_chunk" 32, (outw.toNat, 32)]
  change ByteEff entry (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_mix_in_length)).2 Rl
  have hbody : sourceFnBody Guest.Software.guestFn_mix_in_length =
      .seq (.call (some (none, none)) (ofString "memzero") [.var .global (ofString "ssz_len_chunk"), .const 32])
        (.seq (.call (some (none, none)) (ofString "st_le64")
            [.var .global (ofString "ssz_len_chunk"), .var .local (ofString "len")])
          (.seq (.call (some (none, none)) (ofString "sha256_pair")
              [.var .local (ofString "root"), .var .global (ofString "ssz_len_chunk"), .var .local (ofString "out")])
            (.return (.const 0)))) := rfl
  rw [hbody] at hnt hres ⊢
  rcases hglk : entry.globals.lookup (ofString "ssz_len_chunk") with _ | gv
  · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call]
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hglk]
    exact ByteEff.refl entry Rl
  · rcases gv with ⟨⟨slc⟩⟩ | gfs | ⟨gnm, gnfs⟩
    case' some.rStruct =>
      exfalso
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hres
      have hc0 : evalListHOLFinite entry (h := fun a => Classical.propDecidable (entry.memaddrs a))
          [.var .global (ofString "ssz_len_chunk"), .const 32] = some [.rStruct gfs, .val (.word 32)] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hglk]
      have hl0 : lookupCodeHOLFinite entry.code.lookup (ofString "memzero") [.rStruct gfs, .val (.word 32)] = none := by
        rw [hc]
        rcases h : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "memzero") [.rStruct gfs, .val (.word 32)] with _ | ⟨b0, L0, r0⟩
        · rfl
        · have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "memzero") _ b0 L0 r0 h
          simp [lookupCodeHOLExact, lookup_memzero, shapeOfHOLExact, shapeEqHOL] at hx
      rw [hc0] at hres; dsimp only at hres; rw [hl0] at hres
      exact not_resumes_error hres
    case' some.nStruct =>
      exfalso
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hres
      have hc0 : evalListHOLFinite entry (h := fun a => Classical.propDecidable (entry.memaddrs a))
          [.var .global (ofString "ssz_len_chunk"), .const 32] = some [.nStruct gnm gnfs, .val (.word 32)] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hglk]
      have hl0 : lookupCodeHOLFinite entry.code.lookup (ofString "memzero") [.nStruct gnm gnfs, .val (.word 32)] = none := by
        rw [hc]
        rcases h : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "memzero") [.nStruct gnm gnfs, .val (.word 32)] with _ | ⟨b0, L0, r0⟩
        · rfl
        · have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "memzero") _ b0 L0 r0 h
          simp [lookupCodeHOLExact, lookup_memzero, shapeOfHOLExact, shapeEqHOL] at hx
      rw [hc0] at hres; dsimp only at hres; rw [hl0] at hres
      exact not_resumes_error hres
    have hsb_pos : 0 < sourceBase := by rw [sourceBase_val]; decide
    rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
    rcases hm1 : evaluateHOLFiniteState entry
        (.call (some (none, none)) (ofString "memzero") [.var .global (ofString "ssz_len_chunk"), .const 32]) with ⟨r1, s1⟩
    rw [hm1] at hnt hres
    have hnt1 : r1 ≠ some .timeOut := fun h => by subst h; simp at hnt
    have hor1 : r1 = none ∨ Resumes r1 := by cases r1 with | none => exact Or.inl rfl | some _ => exact Or.inr hres
    have hargs1 : evalListHOLFinite entry (h := fun a => Classical.propDecidable (entry.memaddrs a))
        [.var .global (ofString "ssz_len_chunk"), .const 32] = some [.val (.word slc), .val (.word 32)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hglk]
    have hres_mz := call0_two_word_resumes entry _ _ _ _ _ _ slc 32 (by decide) hc lookup_memzero hargs1
      (by rw [hm1]; exact hor1)
    let c0 := callEntryStateHOLFinite entry
      ((HolFiniteMapExact.empty.update (ofString "dst", .val (.word slc))).update (ofString "n", .val (.word 32)))
    have hslc_dom := (memzero_body_eff c0 slc 32 hc (guestInv_callEntry entry _ hG)
      (by simp [c0, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "n" ≠ ofString "dst" by decide])
      (by simp [c0, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      hres_mz).2 (by decide)
    have hslc_nz : slc.toNat ≠ 0 := by omega
    have hslc_sub : ∀ k, k ≤ 32 → 0 < k → ∃ j ∈ Rl, j.1 ≤ slc.toNat ∧ slc.toNat + k ≤ j.1 + j.2 := by
      intro k hk _
      refine ⟨globBufIvl entry.globals "ssz_len_chunk" 32, List.mem_cons_self, ?_, ?_⟩
      · simp [globBufIvl, globMapN, hglk, hslc_nz]
      · simp [globBufIvl, globMapN, hglk, hslc_nz]; omega
    have heff1 : ByteEff entry s1 Rl := by
      have := call0_byteEff funByteEff_memzero entry _ Rl hc hG
        (fun vs hvs i hi hp => by
          rw [hargs1] at hvs; injection hvs with hvs; subst hvs
          simp [valWordNat] at hi; subst hi
          exact hslc_sub 32 le_rfl hp)
        (by rw [hm1]; exact hnt1) (by rw [hm1]; exact hor1)
      rwa [hm1] at this
    cases r1 with
    | some _ => exact heff1
    | none =>
      have hs1_loc : s1.locals = entry.locals := by
        have := call0_none_locals entry (ofString "memzero") [.var .global (ofString "ssz_len_chunk"), .const 32] (by rw [hm1])
        rwa [hm1] at this
      have hs1_glob : s1.globals = entry.globals := heff1.globals
      dsimp only at hnt hres ⊢
      rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
      rcases hm2 : evaluateHOLFiniteState s1
          (.call (some (none, none)) (ofString "st_le64")
            [.var .global (ofString "ssz_len_chunk"), .var .local (ofString "len")]) with ⟨r2, s2⟩
      rw [hm2] at hnt hres
      have hGs1 : GuestInv s1 := guestInv_congr heff1.code heff1.memaddrs heff1.shMemaddrs heff1.baseAddr hG
      have hc1 : s1.code = originalRuntimeCode := heff1.code.trans hc
      have hargs2 : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
          [.var .global (ofString "ssz_len_chunk"), .var .local (ofString "len")] =
          some [.val (.word slc), .val (.word lenw)] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs1_glob, hs1_loc, hglk, hlen]
      have heff2 : ByteEff s1 s2 Rl := by
        have := call0_byteEff funByteEff_st_le64 s1 _ Rl hc1 hGs1
          (fun vs hvs i hi hp => by
            rw [hargs2] at hvs; injection hvs with hvs; subst hvs
            simp [valWordNat] at hi; subst hi
            exact hslc_sub 8 (by omega) hp)
          (by rw [hm2]; intro h; subst h; simp at hnt)
          (by rw [hm2]; cases r2 with | none => exact Or.inl rfl | some _ => exact Or.inr hres)
        rwa [hm2] at this
      cases r2 with
      | some _ => exact heff1.trans heff2
      | none =>
        have hs2_loc : s2.locals = s1.locals := by
          have := call0_none_locals s1 (ofString "st_le64")
            [.var .global (ofString "ssz_len_chunk"), .var .local (ofString "len")] (by rw [hm2])
          rwa [hm2] at this
        have hs2_glob : s2.globals = entry.globals := (heff1.trans heff2).globals
        dsimp only at hnt hres ⊢
        rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
        rcases hm3 : evaluateHOLFiniteState s2
            (.call (some (none, none)) (ofString "sha256_pair")
              [.var .local (ofString "root"), .var .global (ofString "ssz_len_chunk"), .var .local (ofString "out")]) with ⟨r3, s3⟩
        rw [hm3] at hnt hres
        have hGs2 : GuestInv s2 := guestInv_congr (heff1.trans heff2).code (heff1.trans heff2).memaddrs
          (heff1.trans heff2).shMemaddrs (heff1.trans heff2).baseAddr hG
        have hc2 : s2.code = originalRuntimeCode := (heff1.trans heff2).code.trans hc
        have hargs3 : evalListHOLFinite s2 (h := fun a => Classical.propDecidable (s2.memaddrs a))
            [.var .local (ofString "root"), .var .global (ofString "ssz_len_chunk"), .var .local (ofString "out")] =
            some [.val (.word rootw), .val (.word slc), .val (.word outw)] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs2_glob, hs2_loc, hs1_loc, hroot, hglk, hout]
        have heff3 : ByteEff s2 s3 Rl := by
          have := call0_byteEff funByteEff_sha256_pair s2 _ Rl hc2 hGs2
            (fun vs hvs i hi _ => by
              rw [hargs3] at hvs; injection hvs with hvs; subst hvs
              simp [valWordNat] at hi; subst hi
              exact ⟨(outw.toNat, 32), List.mem_cons_of_mem _ (List.mem_singleton.2 rfl), le_rfl, le_rfl⟩)
            (by rw [hm3]; intro h; subst h; simp at hnt)
            (by rw [hm3]; cases r3 with | none => exact Or.inl rfl | some _ => exact Or.inr hres)
          rwa [hm3] at this
        cases r3 with
        | some _ => exact (heff1.trans heff2).trans heff3
        | none => exact ((heff1.trans heff2).trans heff3).trans (byteEff_return s3 _ _)

private theorem eval_panMul_of_eval {F : Type} {cur : PanSemStateFiniteExact 64 F}
    {a b : ExpHOL 64} {w : BitVec 64}
    (hev : @evalHOLExact 64 F _ cur.toExact (fun x => Classical.propDecidable (cur.memaddrs x))
      (.panop .mul [a, b]) = some (.val (.word w))) :
    ∃ wa wb : BitVec 64,
      @evalHOLExact 64 F _ cur.toExact (fun x => Classical.propDecidable (cur.memaddrs x)) a = some (.val (.word wa)) ∧
      @evalHOLExact 64 F _ cur.toExact (fun x => Classical.propDecidable (cur.memaddrs x)) b = some (.val (.word wb)) ∧
      w = wa * wb := by
  simp only [evalHOLExact, evalListHOLExact] at hev
  rcases ha : @evalHOLExact 64 F _ cur.toExact (fun x => Classical.propDecidable (cur.memaddrs x)) a with _ | va
  · simp [ha] at hev
  · simp only [ha] at hev
    rcases hb : @evalHOLExact 64 F _ cur.toExact (fun x => Classical.propDecidable (cur.memaddrs x)) b with _ | vb
    · simp [hb] at hev
    · simp only [hb] at hev
      rcases va with ⟨⟨wa⟩⟩ | _ | _ <;> rcases vb with ⟨⟨wb⟩⟩ | _ | _ <;>
        simp [panOpHOL, valueIsWord, valueWord] at hev
      exact ⟨wa, wb, rfl, rfl, hev.symm⟩

private theorem eval_any_word {F : Type} {s : PanSemStateFiniteExact 64 F}
    {e : ExpHOL 64}
    (h : match e with
      | .const _ | .baseAddr | .topAddr | .load .one _ | .loadByte _ | .load32 _
      | .op _ _ | .panop _ _ | .cmp _ _ _ | .shift _ _ _ => True
      | _ => False) :
    ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some v →
      ∃ w : BitVec 64, v = .val (.word w) := by
  intro v hv
  cases e with
  | const c => simp [evalHOLExact] at hv; exact ⟨c, hv.symm⟩
  | baseAddr => simp [evalHOLExact] at hv; exact ⟨s.baseAddr, hv.symm⟩
  | topAddr => simp [evalHOLExact] at hv; exact ⟨s.topAddr, hv.symm⟩
  | load sh addrExp =>
    cases sh with
    | one => exact eval_load_one_word s addrExp v hv
    | comb _ | named _ => exact False.elim h
  | loadByte _ | load32 _ | shift _ _ _ =>
    simp only [evalHOLExact] at hv
    split at hv
    · simp only [Option.map_eq_some_iff] at hv
      obtain ⟨_, _, rfl⟩ := hv; exact ⟨_, rfl⟩
    · cases hv
  | op _ _ | panop _ _ =>
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
  | _ => exact False.elim h

private theorem eval_add_of_eval {F : Type} {cur : PanSemStateFiniteExact 64 F}
    {a b : ExpHOL 64} {w : BitVec 64}
    (hev : @evalHOLExact 64 F _ cur.toExact (fun x => Classical.propDecidable (cur.memaddrs x))
      (.op .add [a, b]) = some (.val (.word w))) :
    ∃ wa wb : BitVec 64,
      @evalHOLExact 64 F _ cur.toExact (fun x => Classical.propDecidable (cur.memaddrs x)) a = some (.val (.word wa)) ∧
      @evalHOLExact 64 F _ cur.toExact (fun x => Classical.propDecidable (cur.memaddrs x)) b = some (.val (.word wb)) ∧
      w = wa + wb := by
  simp only [evalHOLExact, evalListHOLExact] at hev
  rcases ha : @evalHOLExact 64 F _ cur.toExact (fun x => Classical.propDecidable (cur.memaddrs x)) a with _ | va
  · simp [ha] at hev
  · simp only [ha] at hev
    rcases hb : @evalHOLExact 64 F _ cur.toExact (fun x => Classical.propDecidable (cur.memaddrs x)) b with _ | vb
    · simp [hb] at hev
    · simp only [hb] at hev
      rcases va with ⟨⟨wa⟩⟩ | _ | _ <;> rcases vb with ⟨⟨wb⟩⟩ | _ | _ <;>
        simp [valueIsWord, valueWord, wordOpHOL, wordOp] at hev
      exact ⟨wa, wb, rfl, rfl, hev.symm⟩

private theorem eval_sub_of_eval {F : Type} {cur : PanSemStateFiniteExact 64 F}
    {a b : ExpHOL 64} {w : BitVec 64}
    (hev : @evalHOLExact 64 F _ cur.toExact (fun x => Classical.propDecidable (cur.memaddrs x))
      (.op .sub [a, b]) = some (.val (.word w))) :
    ∃ wa wb : BitVec 64,
      @evalHOLExact 64 F _ cur.toExact (fun x => Classical.propDecidable (cur.memaddrs x)) a = some (.val (.word wa)) ∧
      @evalHOLExact 64 F _ cur.toExact (fun x => Classical.propDecidable (cur.memaddrs x)) b = some (.val (.word wb)) ∧
      w = wa - wb := by
  simp only [evalHOLExact, evalListHOLExact] at hev
  rcases ha : @evalHOLExact 64 F _ cur.toExact (fun x => Classical.propDecidable (cur.memaddrs x)) a with _ | va
  · simp [ha] at hev
  · simp only [ha] at hev
    rcases hb : @evalHOLExact 64 F _ cur.toExact (fun x => Classical.propDecidable (cur.memaddrs x)) b with _ | vb
    · simp [hb] at hev
    · simp only [hb] at hev
      rcases va with ⟨⟨wa⟩⟩ | _ | _ <;> rcases vb with ⟨⟨wb⟩⟩ | _ | _ <;>
        simp [valueIsWord, valueWord, wordOpHOL, wordOp] at hev
      exact ⟨wa, wb, rfl, rfl, hev.symm⟩

private theorem call0_three_word_resumes {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname p1 p2 p3 : MlS) (body : ProgHOL 64) (a1 a2 a3 : ExpHOL 64) (w1 w2 w3 : BitVec 64)
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (hc : s.code = originalRuntimeCode)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one), (p3, .one)], body, .one))
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [a1, a2, a3] =
      some [.val (.word w1), .val (.word w2), .val (.word w3)])
    (hor : (evaluateHOLFiniteState s (.call (some (none, none)) fname [a1, a2, a3])).1 = none ∨
      Resumes (evaluateHOLFiniteState s (.call (some (none, none)) fname [a1, a2, a3])).1) :
    Resumes (evaluateHOLFiniteState
      (callEntryStateHOLFinite s
        (((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2))).update
          (p3, .val (.word w3))))
      body).1 := by
  have hl := pan_three_word_lookup s.code.lookup fname p1 p2 p3 body w1 w2 w3 h12 h13 h23
    (by rw [hc]; exact hlook)
  rw [evaluateHOLFiniteState_call, ha] at hor
  dsimp only at hor
  rw [hl] at hor; dsimp only at hor
  split at hor
  · rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
  · rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s _) body with ⟨rc, _⟩
    rw [hrun] at hor
    cases rc with
    | none => rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
    | some r1 =>
      cases r1 with
      | returned rv => exact Or.inl ⟨rv, rfl⟩
      | exception eid ev =>
        rcases hor with h | ⟨_, h⟩ | ⟨e', v', h, hne⟩
        · simp at h
        · simp at h
        · simp at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨eid, ev, rfl, hne⟩
      | _ => rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h

private theorem memcpy_src_domain {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (dst0 src0 n0 : BitVec 64)
    (hG : GuestInv s0)
    (hdst : s0.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hsrc : s0.locals.lookup (ofString "src") = some (.val (.word src0)))
    (hn : s0.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hres : Resumes (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_memcpy)).1)
    (hpos : 0 < n0.toNat) :
    sourceBase ≤ src0.toNat ∧ src0.toNat < heapEnd := by
  have hmem_ord : s0.memaddrs = ordinaryDomain := hG.memaddrs
  have hdom_word : ∀ (t : PanSemStateFiniteExact 64 F) (dExp : ExpHOL 64),
      t.memaddrs = ordinaryDomain →
      t.locals.lookup (ofString "src") = some (.val (.word src0)) →
      t.locals.lookup (ofString "i") = some (.val (.word 0#64)) →
      (evaluateHOLFiniteState t (.store dExp (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))).1 = none →
      sourceBase ≤ src0.toNat ∧ src0.toNat < heapEnd := by
    intro t dExp ht_mem ht_src ht_i hst
    rw [evaluateHOLFiniteState_store] at hst
    split at hst
    · have hs_ev : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.op .add [.var .local (ofString "src"), .var .local (ofString "i")]) = some (.val (.word src0)) := by
        simp [evalHOLExact, evalListHOLExact, toExact, ht_src, ht_i, valueIsWord, valueWord, wordOpHOL, wordOp]
      by_cases hdy : t.memaddrs src0
      · rw [ht_mem, ordinaryDomain_iff] at hdy
        exact ⟨hdy.2.1, hdy.2.2⟩
      · have hln : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
            (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])) = none := by
          unfold evalHOLExact
          rw [hs_ev]
          simp [isWfShapeExactHOL, memLoadHOLExact, panMemLoadHOL, hdy]
        rw [hln] at hst; simp at hst
    · simp at hst
  have hdom_byte : ∀ (t : PanSemStateFiniteExact 64 F) (dExp : ExpHOL 64),
      t.memaddrs = ordinaryDomain →
      t.locals.lookup (ofString "src") = some (.val (.word src0)) →
      t.locals.lookup (ofString "i") = some (.val (.word 0#64)) →
      (evaluateHOLFiniteState t (.storeByte dExp (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))).1 = none →
      sourceBase ≤ src0.toNat ∧ src0.toNat < heapEnd := by
    intro t dExp ht_mem ht_src ht_i hst
    rw [evaluateHOLFiniteState_storeByte] at hst
    split at hst
    · have hs_ev : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.op .add [.var .local (ofString "src"), .var .local (ofString "i")]) = some (.val (.word src0)) := by
        simp [evalHOLExact, evalListHOLExact, toExact, ht_src, ht_i, valueIsWord, valueWord, wordOpHOL, wordOp]
      by_cases hdy : t.memaddrs (panByteAlignHOL src0)
      · rw [ht_mem, ordinaryDomain_iff] at hdy
        have hal := panByteAlign_toNat64 src0
        have hhe8 : heapEnd % 8 = 0 := by decide
        exact ⟨by omega, by omega⟩
      · have hln : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
            (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])) = none := by
          unfold evalHOLExact
          rw [hs_ev]
          simp only [panMemLoadByteHOL]
          cases t.memory (panByteAlignHOL src0) with
          | word _ => simp [hdy]
        rw [hln] at hst; simp at hst
    · simp at hst
  have hwhile_step : ∀ (t : PanSemStateFiniteExact 64 F) (cond : ExpHOL 64) (first rest : ProgHOL 64),
      evalHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) cond = some (.val (.word 1#64)) →
      ((evaluateHOLFiniteState (decClockHOLFinite t) first).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite t) first).1 = some .error) →
      (evaluateHOLFiniteState t (.while cond (.seq first rest))).1 = none →
      (evaluateHOLFiniteState (decClockHOLFinite t) first).1 = none := by
    intro t cond first rest hcond hctrl hw
    rcases hctrl with hnone | herr
    · exact hnone
    · exfalso
      rw [evaluateHOLFiniteState_while_fixClockRewrite, hcond] at hw
      dsimp only at hw
      rw [if_pos (by decide : (1#64 : BitVec 64) ≠ 0)] at hw
      split at hw
      · simp at hw
      · rw [evaluateHOLFiniteState_seq_line780] at hw
        rcases hf : evaluateHOLFiniteState (decClockHOLFinite t) first with ⟨rf, mf⟩
        rw [hf] at herr hw; dsimp only at herr; subst herr; simp at hw
  have hst_ctrl : ∀ (t : PanSemStateFiniteExact 64 F) d v,
      (evaluateHOLFiniteState t (.store d v)).1 = none ∨
      (evaluateHOLFiniteState t (.store d v)).1 = some .error := by
    intro t d v; rw [evaluateHOLFiniteState_store]
    split
    · split
      · split <;> simp
      · simp
    · simp
  have hsb_ctrl : ∀ (t : PanSemStateFiniteExact 64 F) d v,
      (evaluateHOLFiniteState t (.storeByte d v)).1 = none ∨
      (evaluateHOLFiniteState t (.storeByte d v)).1 = some .error := by
    intro t d v; rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split <;> simp
      · simp
    · simp
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memcpy,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    List.map, Option.map] at hres
  rw [evaluateHOLFiniteState_dec_total] at hres
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hres
  let si := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s0
  have hsi_mem : si.memaddrs = ordinaryDomain := hmem_ord
  have hsi_dst : si.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
    simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hdst, show ofString "i" ≠ ofString "dst" by decide]
  have hsi_src : si.locals.lookup (ofString "src") = some (.val (.word src0)) := by
    simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsrc, show ofString "i" ≠ ofString "src" by decide]
  have hsi_n : si.locals.lookup (ofString "n") = some (.val (.word n0)) := by
    simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn, show ofString "i" ≠ ofString "n" by decide]
  have hsi_i : si.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
    simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hwhile_no_res : ∀ (n : Nat) (t : PanSemStateFiniteExact 64 F) (cond : ExpHOL 64) (body : ProgHOL 64),
      t.clock ≤ n →
      (∀ (t' : PanSemStateFiniteExact 64 F), ¬ Resumes (evaluateHOLFiniteState t' body).1) →
      ¬ Resumes (evaluateHOLFiniteState t (.while cond body)).1 := by
    intro n
    induction n with
    | zero =>
      intro t cond body hclk hb hr
      have hc0 : t.clock = 0 := Nat.eq_zero_of_le_zero hclk
      rw [evaluateHOLFiniteState_while_fixClockRewrite] at hr
      split at hr
      · dsimp only at hr
        split at hr
        · simp [hc0] at hr; rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
        · rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      · rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
    | succ n ih =>
      intro t cond body hclk hb hr
      rw [evaluateHOLFiniteState_while_fixClockRewrite] at hr
      split at hr
      · dsimp only at hr
        split at hr
        · split at hr
          · rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
          · rename_i hne0
            rcases hrun : evaluateHOLFiniteState (decClockHOLFinite t) body with ⟨rb, mb⟩
            rw [hrun] at hr
            cases rb with
            | none =>
              have hle0 := evaluateHOLFiniteState_clock_le (decClockHOLFinite t) body
              rw [hrun] at hle0
              have hmb_le : mb.clock ≤ n := by change mb.clock ≤ t.clock - 1 at hle0; omega
              exact ih mb cond body hmb_le hb hr
            | some r =>
              cases r with
              | «break» => rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
              | «continue» =>
                have hle0 := evaluateHOLFiniteState_clock_le (decClockHOLFinite t) body
                rw [hrun] at hle0
                have hmb_le : mb.clock ≤ n := by change mb.clock ≤ t.clock - 1 at hle0; omega
                exact ih mb cond body hmb_le hb hr
              | returned v => exact hb (decClockHOLFinite t) (Or.inl ⟨v, by rw [hrun]⟩)
              | exception eid ev =>
                dsimp only at hr
                rcases hr with ⟨_, h⟩ | ⟨_, _, h, hne⟩
                · simp at h
                · injection h with h; injection h with heid _; subst heid
                  exact hb (decClockHOLFinite t) (Or.inr ⟨eid, ev, by rw [hrun], hne⟩)
              | timeOut | error | finalFfi _ =>
                rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
        · rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      · rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
  have hst_no_res : ∀ (t : PanSemStateFiniteExact 64 F) d v, ¬ Resumes (evaluateHOLFiniteState t (.store d v)).1 := by
    intro t d v hr
    rcases hst_ctrl t d v with h | h <;> (rw [h] at hr; rcases hr with ⟨_, hc⟩ | ⟨_, _, hc, _⟩ <;> simp at hc)
  have hsb_no_res : ∀ (t : PanSemStateFiniteExact 64 F) d v, ¬ Resumes (evaluateHOLFiniteState t (.storeByte d v)).1 := by
    intro t d v hr
    rcases hsb_ctrl t d v with h | h <;> (rw [h] at hr; rcases hr with ⟨_, hc⟩ | ⟨_, _, hc, _⟩ <;> simp at hc)
  have hasgn_no_res : ∀ (t : PanSemStateFiniteExact 64 F) vk vn e, ¬ Resumes (evaluateHOLFiniteState t (.assign vk vn e)).1 := by
    intro t vk vn e hr
    rw [evaluateHOLFiniteState_assign] at hr
    split at hr <;> (try split at hr) <;> (rcases hr with ⟨_, hc⟩ | ⟨_, _, hc, _⟩ <;> simp at hc)
  have hseq_no_res : ∀ {p q : ProgHOL 64},
      (∀ (t : PanSemStateFiniteExact 64 F), ¬ Resumes (evaluateHOLFiniteState t p).1) →
      (∀ (t : PanSemStateFiniteExact 64 F), ¬ Resumes (evaluateHOLFiniteState t q).1) →
      ∀ (t : PanSemStateFiniteExact 64 F), ¬ Resumes (evaluateHOLFiniteState t (.seq p q)).1 := by
    intro p q hp hq t hr
    rw [evaluateHOLFiniteState_seq_line780] at hr
    rcases h : evaluateHOLFiniteState t p with ⟨rp, mp⟩
    rw [h] at hr
    cases rp with
    | none => exact hq mp hr
    | some _ => exact hp t (by rw [h]; exact hr)
  have hite_no_res : ∀ {c : ExpHOL 64} {p q : ProgHOL 64},
      (∀ (t : PanSemStateFiniteExact 64 F), ¬ Resumes (evaluateHOLFiniteState t p).1) →
      (∀ (t : PanSemStateFiniteExact 64 F), ¬ Resumes (evaluateHOLFiniteState t q).1) →
      ∀ (t : PanSemStateFiniteExact 64 F), ¬ Resumes (evaluateHOLFiniteState t (.ite c p q)).1 := by
    intro c p q hp hq t hr
    rw [evaluateHOLFiniteState_ite] at hr
    split at hr
    · split at hr
      · exact hq t hr
      · exact hp t hr
    · rcases hr with ⟨_, hc⟩ | ⟨_, _, hc, _⟩ <;> simp at hc
  have hskip_no_res : ∀ (t : PanSemStateFiniteExact 64 F), ¬ Resumes (evaluateHOLFiniteState t .skip).1 := by
    intro t hr; rw [evaluateHOLFiniteState_skip] at hr; rcases hr with ⟨_, hc⟩ | ⟨_, _, hc, _⟩ <;> simp at hc
  rw [evaluateHOLFiniteState_seq_line780] at hres
  rcases h1 : evaluateHOLFiniteState si _ with ⟨r1, m1⟩
  rw [h1] at hres
  cases r1 with
  | some _ =>
    exfalso
    refine hite_no_res (hseq_no_res
      (fun t => hwhile_no_res t.clock t _ _ le_rfl (hseq_no_res (fun u => hst_no_res u _ _)
        (hseq_no_res (fun u => hst_no_res u _ _) (hseq_no_res (fun u => hst_no_res u _ _)
          (hseq_no_res (fun u => hst_no_res u _ _) (fun u => hasgn_no_res u _ _ _))))))
      (fun t => hwhile_no_res t.clock t _ _ le_rfl (hseq_no_res (fun u => hst_no_res u _ _) (fun u => hasgn_no_res u _ _ _))))
      hskip_no_res si (by rw [h1]; exact hres)
  | none =>
    dsimp only at hres
    rw [evaluateHOLFiniteState_ite] at h1
    split at h1
    · split at h1
      · -- Unaligned branch: `.skip` ran, so `m1 = si`!
        rw [evaluateHOLFiniteState_skip] at h1; injection h1 with _ hm1; subst hm1
        rw [evaluateHOLFiniteState_seq_line780] at hres
        rcases h2 : evaluateHOLFiniteState si _ with ⟨r2, m2⟩
        rw [h2] at hres
        cases r2 with
        | some _ =>
          exfalso
          exact hwhile_no_res si.clock si _ _ le_rfl
            (hseq_no_res (fun u => hsb_no_res u _ _) (hseq_no_res (fun u => hsb_no_res u _ _)
              (hseq_no_res (fun u => hsb_no_res u _ _) (hseq_no_res (fun u => hsb_no_res u _ _)
                (hseq_no_res (fun u => hsb_no_res u _ _) (hseq_no_res (fun u => hsb_no_res u _ _)
                  (hseq_no_res (fun u => hsb_no_res u _ _) (hseq_no_res (fun u => hsb_no_res u _ _)
                    (fun u => hasgn_no_res u _ _ _)))))))))
            (by rw [h2]; exact hres)
        | none =>
          by_cases hn8 : 8 ≤ n0.toNat
          · have hc8 : evalHOLFinite si (h := fun a => Classical.propDecidable (si.memaddrs a))
                (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8#64])) =
                some (.val (.word 1#64)) := by
              rw [evalHOLFinite_eq_toExact]
              have hnl : ¬ (n0 < 8#64) := by rw [BitVec.lt_def]; change ¬ (n0.toNat < 8); omega
              simp [evalHOLExact, evalListHOLExact, hsi_n, hsi_i, valueIsWord, valueWord,
                wordOpHOL, wordOp, Compiler.Encoders.Asm.wordCmpHOL, hnl]
            have hsb := hwhile_step si _ _ _ hc8 (hsb_ctrl (decClockHOLFinite si) _ _) (congrArg Prod.fst h2)
            exact hdom_byte (decClockHOLFinite si) _ hsi_mem hsi_src hsi_i hsb
          · have hc8_f : @evalHOLFinite 64 F _ si (fun a => Classical.propDecidable (si.memaddrs a))
                (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8#64])) =
                some (.val (.word 0#64)) := by
              rw [evalHOLFinite_eq_toExact]
              have hl8 : n0 < 8#64 := by rw [BitVec.lt_def]; change n0.toNat < 8; omega
              simp [evalHOLExact, evalListHOLExact, hsi_n, hsi_i, valueIsWord, valueWord,
                wordOpHOL, wordOp, Compiler.Encoders.Asm.wordCmpHOL, hl8]
            rw [evaluateHOLFiniteState_while_fixClockRewrite, hc8_f] at h2
            simp at h2; subst h2
            dsimp only at hres
            rw [evaluateHOLFiniteState_seq_line780] at hres
            rcases h3 : evaluateHOLFiniteState si _ with ⟨r3, m3⟩
            rw [h3] at hres
            cases r3 with
            | some _ =>
              exfalso
              exact hwhile_no_res si.clock si _ _ le_rfl
                (hseq_no_res (fun u => hsb_no_res u _ _) (fun u => hasgn_no_res u _ _ _))
                (by rw [h3]; exact hres)
            | none =>
              have hc1 : evalHOLFinite si (h := fun a => Classical.propDecidable (si.memaddrs a))
                  (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
                  some (.val (.word 1#64)) := by
                rw [evalHOLFinite_eq_toExact]
                have hl0 : (0#64 : BitVec 64) < n0 := by rw [BitVec.lt_def]; exact hpos
                simp [evalHOLExact, hsi_n, hsi_i, Compiler.Encoders.Asm.wordCmpHOL, hl0]
              have hsb := hwhile_step si _ _ _ hc1 (hsb_ctrl (decClockHOLFinite si) _ _) (congrArg Prod.fst h3)
              exact hdom_byte (decClockHOLFinite si) _ hsi_mem hsi_src hsi_i hsb
      · -- Aligned branch: `seq w32 w8w` ran with `.1 = none`!
        rw [evaluateHOLFiniteState_seq_line780] at h1
        rcases hw32 : evaluateHOLFiniteState si _ with ⟨rw32, mw32⟩
        rw [hw32] at h1
        cases rw32 with
        | some _ => simp at h1
        | none =>
          dsimp only at h1
          by_cases hn32 : 32 ≤ n0.toNat
          · have hc32 : evalHOLFinite si (h := fun a => Classical.propDecidable (si.memaddrs a))
                (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32#64])) =
                some (.val (.word 1#64)) := by
              rw [evalHOLFinite_eq_toExact]
              have hnl : ¬ (n0 < 32#64) := by rw [BitVec.lt_def]; change ¬ (n0.toNat < 32); omega
              simp [evalHOLExact, evalListHOLExact, hsi_n, hsi_i, valueIsWord, valueWord,
                wordOpHOL, wordOp, Compiler.Encoders.Asm.wordCmpHOL, hnl]
            have hsw := hwhile_step si _ _ _ hc32 (hst_ctrl (decClockHOLFinite si) _ _) (congrArg Prod.fst hw32)
            exact hdom_word (decClockHOLFinite si) _ hsi_mem hsi_src hsi_i hsw
          · have hc32_f : @evalHOLFinite 64 F _ si (fun a => Classical.propDecidable (si.memaddrs a))
                (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32#64])) =
                some (.val (.word 0#64)) := by
              rw [evalHOLFinite_eq_toExact]
              have hl32 : n0 < 32#64 := by rw [BitVec.lt_def]; change n0.toNat < 32; omega
              simp [evalHOLExact, evalListHOLExact, hsi_n, hsi_i, valueIsWord, valueWord,
                wordOpHOL, wordOp, Compiler.Encoders.Asm.wordCmpHOL, hl32]
            rw [evaluateHOLFiniteState_while_fixClockRewrite, hc32_f] at hw32
            simp at hw32; subst hw32
            by_cases hn8 : 8 ≤ n0.toNat
            · have hc8 : evalHOLFinite si (h := fun a => Classical.propDecidable (si.memaddrs a))
                  (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8#64])) =
                  some (.val (.word 1#64)) := by
                rw [evalHOLFinite_eq_toExact]
                have hnl : ¬ (n0 < 8#64) := by rw [BitVec.lt_def]; change ¬ (n0.toNat < 8); omega
                simp [evalHOLExact, evalListHOLExact, hsi_n, hsi_i, valueIsWord, valueWord,
                  wordOpHOL, wordOp, Compiler.Encoders.Asm.wordCmpHOL, hnl]
              have hsw := hwhile_step si _ _ _ hc8 (hst_ctrl (decClockHOLFinite si) _ _) (congrArg Prod.fst h1)
              exact hdom_word (decClockHOLFinite si) _ hsi_mem hsi_src hsi_i hsw
            · have hc8_f : @evalHOLFinite 64 F _ si (fun a => Classical.propDecidable (si.memaddrs a))
                  (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8#64])) =
                  some (.val (.word 0#64)) := by
                rw [evalHOLFinite_eq_toExact]
                have hl8 : n0 < 8#64 := by rw [BitVec.lt_def]; change n0.toNat < 8; omega
                simp [evalHOLExact, evalListHOLExact, hsi_n, hsi_i, valueIsWord, valueWord,
                  wordOpHOL, wordOp, Compiler.Encoders.Asm.wordCmpHOL, hl8]
              rw [evaluateHOLFiniteState_while_fixClockRewrite, hc8_f] at h1
              simp at h1; subst h1
              rw [evaluateHOLFiniteState_seq_line780] at hres
              rcases h2 : evaluateHOLFiniteState si _ with ⟨r2, m2⟩
              rw [h2] at hres
              cases r2 with
              | some _ =>
                exfalso
                exact hwhile_no_res si.clock si _ _ le_rfl
                  (hseq_no_res (fun u => hsb_no_res u _ _) (hseq_no_res (fun u => hsb_no_res u _ _)
                    (hseq_no_res (fun u => hsb_no_res u _ _) (hseq_no_res (fun u => hsb_no_res u _ _)
                      (hseq_no_res (fun u => hsb_no_res u _ _) (hseq_no_res (fun u => hsb_no_res u _ _)
                        (hseq_no_res (fun u => hsb_no_res u _ _) (hseq_no_res (fun u => hsb_no_res u _ _)
                          (fun u => hasgn_no_res u _ _ _)))))))))
                  (by rw [h2]; exact hres)
              | none =>
                rw [evaluateHOLFiniteState_while_fixClockRewrite, hc8_f] at h2
                simp at h2; subst h2
                dsimp only at hres
                rw [evaluateHOLFiniteState_seq_line780] at hres
                rcases h3 : evaluateHOLFiniteState si _ with ⟨r3, m3⟩
                rw [h3] at hres
                cases r3 with
                | some _ =>
                  exfalso
                  exact hwhile_no_res si.clock si _ _ le_rfl
                    (hseq_no_res (fun u => hsb_no_res u _ _) (fun u => hasgn_no_res u _ _ _))
                    (by rw [h3]; exact hres)
                | none =>
                  have hc1 : evalHOLFinite si (h := fun a => Classical.propDecidable (si.memaddrs a))
                      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
                      some (.val (.word 1#64)) := by
                    rw [evalHOLFinite_eq_toExact]
                    have hl0 : (0#64 : BitVec 64) < n0 := by rw [BitVec.lt_def]; exact hpos
                    simp [evalHOLExact, hsi_n, hsi_i, Compiler.Encoders.Asm.wordCmpHOL, hl0]
                  have hsb := hwhile_step si _ _ _ hc1 (hsb_ctrl (decClockHOLFinite si) _ _) (congrArg Prod.fst h3)
                  exact hdom_byte (decClockHOLFinite si) _ hsi_mem hsi_src hsi_i hsb
    · simp at h1

/-- Call `memcpy(dstExp, srcExp, nExp)` from a `WorldEff` state: produces `WorldEff`, and on `none`
gives `m'.locals = cur.locals` AND `0 < nw.toNat → sourceBase ≤ dstw.toNat ∧ dstw.toNat + nw.toNat ≤ heapEnd`
AND (if `srcExp` evaluates to `srcw`) `0 < nw.toNat → sourceBase ≤ srcw.toNat ∧ srcw.toNat < heapEnd`! -/
private theorem worldEff_call0_memcpy_word {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (heff : WorldEff s0 cur Rl B gw)
    (dstExp srcExp nExp : ExpHOL 64)
    (dstw nw : BitVec 64)
    (hdst : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) dstExp =
      some (.val (.word dstw)))
    (hn : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) nExp =
      some (.val (.word nw)))
    (hcov : (0 < nw.toNat → sourceBase ≤ dstw.toNat ∧ dstw.toNat + nw.toNat ≤ heapEnd) →
      0 < nw.toNat →
      (∃ j ∈ Rl, j.1 ≤ dstw.toNat ∧ dstw.toNat + nw.toNat ≤ j.1 + j.2) ∨
      (∃ gs ∈ B, (bufferRegion s0 gs).1 ≤ dstw.toNat ∧ dstw.toNat + nw.toNat ≤ (bufferRegion s0 gs).1 + (bufferRegion s0 gs).2) ∨
      (globN s0 "frame_mem_ptr" ≤ dstw.toNat ∧ dstw.toNat + nw.toNat ≤ globN s0 "scratch_ptr") ∨
      (globN s0 "heap_ptr" ≤ dstw.toNat ∧ dstw.toNat + nw.toNat ≤ heapLimit))
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp])).1 ≠
      some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp])).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp])).2
      Rl B gw ∧
    ((evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp])).1 = none →
      (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp])).2.locals =
        cur.locals ∧
      (0 < nw.toNat → sourceBase ≤ dstw.toNat ∧ dstw.toNat + nw.toNat ≤ heapEnd) ∧
      (0 < nw.toNat → ∃ srcw : BitVec 64,
        @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) srcExp =
          some (.val (.word srcw)) ∧
        sourceBase ≤ srcw.toNat ∧ srcw.toNat < heapEnd)) := by
  have hor := call0_or_resumes cur (ofString "memcpy") [dstExp, srcExp, nExp] hcr
  have hboth_dom : 0 < nw.toNat →
      (sourceBase ≤ dstw.toNat ∧ dstw.toNat + nw.toNat ≤ heapEnd) ∧
      ∃ srcw : BitVec 64,
        @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) srcExp =
          some (.val (.word srcw)) ∧
        sourceBase ≤ srcw.toNat ∧ srcw.toNat < heapEnd := by
    intro hpos
    rcases hs : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) srcExp with _ | vs
    · exfalso
      rw [evaluateHOLFiniteState_call] at hor
      have ha0 : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a))
          [dstExp, srcExp, nExp] = none := by
        rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, hdst, hs]
      rw [ha0] at hor; rcases hor with h | h <;> [simp at h; exact not_resumes_error h]
    · have ha0 : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a))
          [dstExp, srcExp, nExp] = some [.val (.word dstw), vs, .val (.word nw)] := by
        rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, hdst, hs, hn]
      rcases hl : lookupCodeHOLFinite cur.code.lookup (ofString "memcpy")
          [.val (.word dstw), vs, .val (.word nw)] with _ | ⟨b0, L0, r0⟩
      · exfalso
        rw [evaluateHOLFiniteState_call, ha0] at hor; dsimp only at hor; rw [hl] at hor
        rcases hor with h | h <;> [simp at h; exact not_resumes_error h]
      · rw [heff.code] at hl
        have hlook_cp : originalRuntimeCode.lookup (ofString "memcpy") =
            some ([(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)],
              sourceFnBody Guest.Software.guestFn_memcpy, .one) :=
          lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide)
            (extractFn Guest.Software.guestFn_memcpy) rfl
        have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "memcpy") _ b0 L0 r0 hl
        simp only [lookupCodeHOLExact, hlook_cp] at hx
        split at hx
        · obtain ⟨hb0, h_rest⟩ := Prod.mk.inj (Option.some.inj hx)
          obtain ⟨_, hr0⟩ := Prod.mk.inj h_rest
          subst hb0 hr0
          obtain ⟨w1, pw, w3, hvs_eq, _, _, _⟩ :=
            lookupCode_three_words (by decide) (by decide) (by decide) hlook_cp hl
          injection hvs_eq with h1 h2
          injection h2 with hvs_pw h3
          subst hvs_pw
          have ha_pw : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a))
              [dstExp, srcExp, nExp] = some [.val (.word dstw), .val (.word pw), .val (.word nw)] := ha0
          have hres_cp := call0_three_word_resumes cur _ _ _ _ _ _ _ _ dstw pw nw
            (by decide) (by decide) (by decide) heff.code hlook_cp ha_pw hor
          let c0 := callEntryStateHOLFinite cur
            (((HolFiniteMapExact.empty.update (ofString "dst", .val (.word dstw))).update
              (ofString "src", .val (.word pw))).update (ofString "n", .val (.word nw)))
          have hdst_c0 : c0.locals.lookup (ofString "dst") = some (.val (.word dstw)) := by
            simp [c0, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "n" ≠ ofString "dst" by decide, show ofString "src" ≠ ofString "dst" by decide]
          have hsrc_c0 : c0.locals.lookup (ofString "src") = some (.val (.word pw)) := by
            simp [c0, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "n" ≠ ofString "src" by decide]
          have hn_c0 : c0.locals.lookup (ofString "n") = some (.val (.word nw)) := by
            simp [c0, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          exact ⟨(memcpy_body_eff c0 dstw nw heff.code (guestInv_callEntry cur _ heff.arena.1)
              hdst_c0 hn_c0 hres_cp).2 hpos,
            pw, rfl, memcpy_src_domain c0 dstw pw nw (guestInv_callEntry cur _ heff.arena.1)
              hdst_c0 hsrc_c0 hn_c0 hres_cp hpos⟩
        · cases hx
  refine ⟨worldEff_call0_funByteEff heff funByteEff_memcpy [dstExp, srcExp, nExp] [(dstw.toNat, nw.toNat)]
    (fun vals hargs i hi _ => by
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact, hdst, hn] at hargs
      rcases hs : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) srcExp with _ | vs
      · simp [hs] at hargs
      · simp only [hs] at hargs
        injection hargs with hargs_eq; subst hargs_eq
        simp [valWordNat] at hi; subst hi
        exact ⟨(dstw.toNat, nw.toNat), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
    (fun iv hiv hpos => by
      simp only [List.mem_singleton] at hiv; subst hiv
      exact hcov (fun hp => (hboth_dom hp).1) hpos)
    hnt hcr, fun hnone => ⟨call0_none_locals cur _ _ hnone, fun hp => (hboth_dom hp).1, fun hp => (hboth_dom hp).2⟩⟩

private theorem count32_bounds (nw : BitVec 64)
    (hn : nw.toNat ≤ heapEnd) :
    let countw := (nw + 31#64) >>> 5#64
    nw.toNat ≤ (countw * 32#64).toNat ∧
    (countw * 32#64 - nw).toNat = (countw * 32#64).toNat - nw.toNat := by
  dsimp only
  have hhe : heapEnd + 64 < 2 ^ 64 := by rw [heapEnd_val]; decide
  have h31 : (31#64 : BitVec 64).toNat = 31 := rfl
  have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
  have h5 : (5#64 : BitVec 64).toNat = 5 := rfl
  have hadd : (nw + 31#64).toNat = nw.toNat + 31 := by
    rw [BitVec.toNat_add_of_lt (by omega), h31]
  have hsh : ((nw + 31#64) >>> 5#64).toNat = (nw.toNat + 31) / 32 := by
    change ((nw + 31#64) >>> (5#64 : BitVec 64).toNat).toNat = (nw.toNat + 31) / 32
    rw [BitVec.toNat_ushiftRight, hadd, h5, Nat.shiftRight_eq_div_pow]
  have hmul : (((nw + 31#64) >>> 5#64) * 32#64).toNat = ((nw.toNat + 31) / 32) * 32 := by
    rw [BitVec.toNat_mul, hsh, h32]; change (((nw.toNat + 31) / 32) * 32) % 2 ^ 64 = _; omega
  refine ⟨by omega, ?_⟩
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.2 (by omega)), hmul]

private theorem worldEff_pack_bytes {F : Type}
    (s0 cur : PanSemStateFiniteExact 64 F) {Rl : List Ivl}
    (heff_cur : WorldEff s0 cur Rl sszBufs hpGw)
    (hnt : (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_pack_bytes)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_pack_bytes)).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_pack_bytes)).2 Rl sszBufs hpGw := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_pack_bytes,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_dec heff_cur (ofString "count") .one _ hnt (Or.inr (Or.inr (Or.inr hres)))
    (fun vcnt hvcnt hvsh hnt1 hcr1 => ?_)
  rcases vcnt with ⟨⟨countw⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hvsh)
  rcases hnp : cur.locals.lookup (ofString "n") with _ | vn
  · simp [evalHOLExact, evalListHOLExact, toExact, hnp] at hvcnt
  · rcases vn with ⟨⟨nw⟩⟩ | _ | _ <;>
      try (simp [evalHOLExact, evalListHOLExact, toExact, hnp, valueIsWord] at hvcnt)
    have hcnt_eq : countw = (nw + 31#64) >>> 5#64 := by
      simp [evalHOLExact, evalListHOLExact, toExact, hnp, valueIsWord, valueWord,
        wordOpHOL, wordOp, wordShiftHOL] at hvcnt
      exact hvcnt.symm
    let m1 := setVarHOLFinite (ofString "count") (.val (.word countw)) cur
    have heff_m1 : WorldEff s0 m1 Rl sszBufs hpGw := heff_cur.locals_clock _ _
    have hm1_cnt : m1.locals.lookup (ofString "count") = some (.val (.word countw)) := by
      simp [m1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hm1_n : m1.locals.lookup (ofString "n") = some (.val (.word nw)) := by
      simp [m1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnp,
        show ofString "count" ≠ ofString "n" by decide]
    refine worldEff_decCall_alloc heff_m1 (by decide) (ofString "buf") _ hnt1 hcr1
      (fun bufw szw m2 hsz_ev _ hm2_loc _ heff_m2 _ _ hbuf_lo hbuf_end hhp_m2 _ hnt2 hcr2 => ?_)
    obtain ⟨wa, wb, hwa, hwb, hsz_mul⟩ := eval_panMul_of_eval hsz_ev
    have hwa_eq : wa = countw := by
      simp [evalHOLExact, toExact, hm1_cnt] at hwa; exact hwa.symm
    have hwb_eq : wb = 32#64 := by
      simp [evalHOLExact] at hwb; exact hwb.symm
    have hsz_eq : szw = countw * 32#64 := by rw [hsz_mul, hwa_eq, hwb_eq]
    have hbuf_cap : bufw.toNat + szw.toNat ≤ heapLimit := by
      have : szw.toNat ≤ (szw.toNat + 7) / 8 * 8 := by omega
      omega
    have hm2_buf : m2.locals.lookup (ofString "buf") = some (.val (.word bufw)) := by
      rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hm2_cnt : m2.locals.lookup (ofString "count") = some (.val (.word countw)) := by
      rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_cnt,
        show ofString "buf" ≠ ofString "count" by decide]
    have hm2_n : m2.locals.lookup (ofString "n") = some (.val (.word nw)) := by
      rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_n,
        show ofString "buf" ≠ ofString "n" by decide]
    have hcp_step : ∀ (hnt_cp : (evaluateHOLFiniteState m2
          (.call (some (none, none)) (ofString "memcpy")
            [.var .local (ofString "buf"), .var .local (ofString "p"), .var .local (ofString "n")])).1 ≠ some .timeOut)
        (hcr_cp : ContOrRes (evaluateHOLFiniteState m2
          (.call (some (none, none)) (ofString "memcpy")
            [.var .local (ofString "buf"), .var .local (ofString "p"), .var .local (ofString "n")])).1),
        WorldEff s0 (evaluateHOLFiniteState m2
          (.call (some (none, none)) (ofString "memcpy")
            [.var .local (ofString "buf"), .var .local (ofString "p"), .var .local (ofString "n")])).2 Rl sszBufs hpGw ∧
        ((evaluateHOLFiniteState m2
          (.call (some (none, none)) (ofString "memcpy")
            [.var .local (ofString "buf"), .var .local (ofString "p"), .var .local (ofString "n")])).1 = none →
          (evaluateHOLFiniteState m2
            (.call (some (none, none)) (ofString "memcpy")
              [.var .local (ofString "buf"), .var .local (ofString "p"), .var .local (ofString "n")])).2.locals = m2.locals ∧
          nw.toNat ≤ heapEnd) := by
      intro hnt_cp hcr_cp
      have hres := worldEff_call0_memcpy_word heff_m2
        (.var .local (ofString "buf")) (.var .local (ofString "p")) (.var .local (ofString "n")) bufw nw
        (by simp [evalHOLExact, toExact, hm2_buf])
        (by simp [evalHOLExact, toExact, hm2_n])
        (fun hdom hpos => by
          obtain ⟨_, hhi⟩ := hdom hpos
          obtain ⟨hle_sz, _⟩ := count32_bounds nw (by omega)
          rw [← hcnt_eq, ← hsz_eq] at hle_sz
          exact Or.inr (Or.inr (Or.inr ⟨hbuf_lo, by omega⟩)))
        hnt_cp hcr_cp
      refine ⟨hres.1, fun hnone => ?_⟩
      obtain ⟨hloc, hdom, _⟩ := hres.2 hnone
      refine ⟨hloc, ?_⟩
      by_cases hp : 0 < nw.toNat
      · obtain ⟨_, hhi⟩ := hdom hp; omega
      · omega
    refine worldEff_seq hnt2 hcr2
      (fun hnt_cp hcr_cp => (hcp_step hnt_cp hcr_cp).1)
      (fun m3 hm3 heff_m3 hnt3 hcr3 => ?_)
    obtain ⟨hm3_loc0, hn_le_he⟩ := (hcp_step
      (by rw [hm3]; simp) (by rw [hm3]; exact Or.inl rfl)).2 (by rw [hm3])
    have hm3_loc : m3.locals = m2.locals := by simpa [hm3] using hm3_loc0
    obtain ⟨hle_sz, hsub_sz⟩ := count32_bounds nw hn_le_he
    rw [← hcnt_eq, ← hsz_eq] at hle_sz hsub_sz
    have hhl_lt : heapLimit < 2 ^ 64 := by decide
    have hbuf_n_add : (bufw + nw).toNat = bufw.toNat + nw.toNat :=
      BitVec.toNat_add_of_lt (by omega)
    refine worldEff_seq hnt3 hcr3
      (fun hnt_mz hcr_mz =>
        worldEff_call0_funByteEff heff_m3 funByteEff_memzero _ [((bufw + nw).toNat, (szw - nw).toNat)]
          (fun vals hargs i hi _ => by
            rw [evalListHOLFinite_eq_toExact] at hargs
            simp only [evalListHOLExact, evalHOLExact, toExact, hm3_loc, hm2_buf, hm2_n, hm2_cnt,
              valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, List.all, List.map, Option.map,
              List.foldr, BitVec.add_zero, Bool.and_self, ↓reduceIte, ← hsz_eq] at hargs
            injection hargs with hargs_eq; subst hargs_eq
            simp [valWordNat] at hi; subst hi
            exact ⟨((bufw + nw).toNat, (szw - nw).toNat), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
          (fun iv hiv _ => by
            simp only [List.mem_singleton] at hiv; subst hiv
            exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
          hnt_mz hcr_mz)
      (fun m4 _ heff_m4 _ _ => worldEff_return heff_m4 _)

private theorem ceil_log2_body_returns {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (nw : BitVec 64)
    (hn : s0.locals.lookup (ofString "n") = some (.val (.word nw)))
    (rv : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_ceil_log2)).1 =
      some (.returned rv)) :
    ∃ dw : BitVec 64, rv = .val (.word dw) ∧
      dw.toNat < 64 ∧ nw.toNat ≤ 2 ^ dw.toNat ∧
      (0 < dw.toNat → 2 ^ (dw.toNat - 1) < nw.toNat) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_ceil_log2,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hret
  rw [evaluateHOLFiniteState_dec_total] at hret
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hret
  let si := setVarHOLFinite (ofString "d") (.val (.word 0#64)) s0
  have hsi_d : si.locals.lookup (ofString "d") = some (.val (.word 0#64)) := by
    simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hsi_n : si.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
      show ofString "d" ≠ ofString "n" by decide]
  rw [evaluateHOLFiniteState_seq_line780] at hret
  let wcond : ExpHOL 64 := .cmp .lower (.shift .lsl (.const 1#64) (.var .local (ofString "d"))) (.var .local (ofString "n"))
  let wbody : ProgHOL 64 := .assign .local (ofString "d") (.op .add [.var .local (ofString "d"), .const 1#64])
  have hfalse_bound : ∀ (cur : PanSemStateFiniteExact 64 F) (d0 : BitVec 64),
      cur.locals.lookup (ofString "d") = some (.val (.word d0)) →
      cur.locals.lookup (ofString "n") = some (.val (.word nw)) →
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) wcond =
        some (.val (.word 0)) →
      d0.toNat < 64 ∧ nw.toNat ≤ 2 ^ d0.toNat := by
    intro cur d0 hd_cur hn_cur hcond
    have hd_lt : d0.toNat < 64 := by
      by_contra hge
      have h64 : ¬ d0.toNat = 0 ∧ 64 ≤ d0.toNat := ⟨by omega, by omega⟩
      simp [wcond, evalHOLExact, hd_cur, hn_cur, wordShiftHOL, h64.1, h64.2] at hcond
    have hnot64 : ¬ (¬ d0.toNat = 0 ∧ 64 ≤ d0.toNat) := by omega
    simp only [wcond, evalHOLExact, hd_cur, hn_cur, wordShiftHOL, hnot64, ↓reduceIte,
      Compiler.Encoders.Asm.wordCmpHOL] at hcond
    have h1sh : (1#64 <<< d0.toNat).toNat = 2 ^ d0.toNat := by
      rw [BitVec.toNat_shiftLeft]
      change ((1 % 2 ^ 64) <<< d0.toNat) % 2 ^ 64 = 2 ^ d0.toNat
      have hlt2 : 1 <<< d0.toNat < 2 ^ 64 := by
        rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.pow_lt_pow_right (by decide) hd_lt
      have h1m : 1 % 2 ^ 64 = 1 := rfl
      rw [h1m, Nat.mod_eq_of_lt hlt2, Nat.shiftLeft_eq, Nat.one_mul]
    by_cases hlt_c : (1#64 <<< d0.toNat) < nw
    · simp [hlt_c] at hcond
    · rw [BitVec.lt_def, h1sh] at hlt_c; exact ⟨hd_lt, by omega⟩
  have htrue_bound : ∀ (cur : PanSemStateFiniteExact 64 F) (d0 cw : BitVec 64),
      cur.locals.lookup (ofString "d") = some (.val (.word d0)) →
      cur.locals.lookup (ofString "n") = some (.val (.word nw)) →
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) wcond =
        some (.val (.word cw)) →
      cw ≠ 0 →
      d0.toNat < 64 ∧ 2 ^ d0.toNat < nw.toNat := by
    intro cur d0 cw hd_cur hn_cur hcond hnz
    have hd_lt : d0.toNat < 64 := by
      by_contra hge
      have h64 : ¬ d0.toNat = 0 ∧ 64 ≤ d0.toNat := ⟨by omega, by omega⟩
      simp [wcond, evalHOLExact, hd_cur, hn_cur, wordShiftHOL, h64.1, h64.2] at hcond
    have hnot64 : ¬ (¬ d0.toNat = 0 ∧ 64 ≤ d0.toNat) := by omega
    simp only [wcond, evalHOLExact, hd_cur, hn_cur, wordShiftHOL, hnot64, ↓reduceIte,
      Compiler.Encoders.Asm.wordCmpHOL] at hcond
    have h1sh : (1#64 <<< d0.toNat).toNat = 2 ^ d0.toNat := by
      rw [BitVec.toNat_shiftLeft]
      change ((1 % 2 ^ 64) <<< d0.toNat) % 2 ^ 64 = 2 ^ d0.toNat
      have hlt2 : 1 <<< d0.toNat < 2 ^ 64 := by
        rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.pow_lt_pow_right (by decide) hd_lt
      have h1m : 1 % 2 ^ 64 = 1 := rfl
      rw [h1m, Nat.mod_eq_of_lt hlt2, Nat.shiftLeft_eq, Nat.one_mul]
    by_cases hlt_c : (1#64 <<< d0.toNat) < nw
    · rw [BitVec.lt_def, h1sh] at hlt_c; exact ⟨hd_lt, hlt_c⟩
    · simp [hlt_c] at hcond; exact absurd hcond.symm hnz
  have hloop : ∀ (k : Nat) (cur post : PanSemStateFiniteExact 64 F) (d0 : BitVec 64),
      cur.clock ≤ k →
      cur.locals.lookup (ofString "d") = some (.val (.word d0)) →
      cur.locals.lookup (ofString "n") = some (.val (.word nw)) →
      (0 < d0.toNat → 2 ^ (d0.toNat - 1) < nw.toNat) →
      evaluateHOLFiniteState cur (.while wcond wbody) = (none, post) →
      ∃ dw : BitVec 64,
        post.locals.lookup (ofString "d") = some (.val (.word dw)) ∧
        dw.toNat < 64 ∧ nw.toNat ≤ 2 ^ dw.toNat ∧
        (0 < dw.toNat → 2 ^ (dw.toNat - 1) < nw.toNat) := by
    intro k
    induction k with
    | zero =>
      intro cur post d0 hk hd_cur hn_cur hprev hrun
      rw [evaluateHOLFiniteState_while_total] at hrun
      split at hrun
      · rename_i cw hcond
        split at hrun
        · split at hrun <;> [simp at hrun; omega]
        · rename_i hnotnz
          have hcw0 : cw = 0 := Classical.not_not.1 hnotnz
          subst hcw0
          simp at hrun; subst hrun
          obtain ⟨hd_lt, hle_pow⟩ := hfalse_bound cur d0 hd_cur hn_cur hcond
          exact ⟨d0, hd_cur, hd_lt, hle_pow, hprev⟩
      · simp at hrun
    | succ k ih =>
      intro cur post d0 hk hd_cur hn_cur hprev hrun
      rw [evaluateHOLFiniteState_while_total] at hrun
      split at hrun
      · rename_i cw hcond
        split at hrun
        · rename_i hcw_nz
          split at hrun
          · simp at hrun
          · dsimp only at hrun
            rw [fixClockHOLFinite_evaluateState] at hrun
            obtain ⟨hd_lt, hpow_lt⟩ := htrue_bound cur d0 cw hd_cur hn_cur hcond hcw_nz
            have hd1_nat : (d0 + 1#64).toNat = d0.toNat + 1 :=
              BitVec.toNat_add_of_lt (by change d0.toNat + 1 < 2 ^ 64; omega)
            have hstep : evaluateHOLFiniteState (decClockHOLFinite cur) wbody =
                (none, setVarHOLFinite (ofString "d") (.val (.word (d0 + 1#64))) (decClockHOLFinite cur)) := by
              simp [wbody, evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact,
                decClockHOLFinite, hd_cur, wordOpHOL, wordOp, valueIsWord, valueWord,
                lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite, setVarHOLFinite,
                shapeOfHOLExact, shapeEqHOL]
            rw [hstep] at hrun; dsimp only at hrun
            let nxt := setVarHOLFinite (ofString "d") (.val (.word (d0 + 1#64))) (decClockHOLFinite cur)
            exact ih nxt post (d0 + 1#64)
              (by change cur.clock - 1 ≤ k; omega)
              (by simp [nxt, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
              (by simp [nxt, setVarHOLFinite, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                    hn_cur, show ofString "d" ≠ ofString "n" by decide])
              (fun _ => by rw [hd1_nat, Nat.add_sub_cancel]; exact hpow_lt)
              hrun
        · rename_i hnotnz
          have hcw0 : cw = 0 := Classical.not_not.1 hnotnz
          subst hcw0
          simp at hrun; subst hrun
          obtain ⟨hd_lt, hle_pow⟩ := hfalse_bound cur d0 hd_cur hn_cur hcond
          exact ⟨d0, hd_cur, hd_lt, hle_pow, hprev⟩
      · simp at hrun
  have hno_ret_while : ∀ (k : Nat) (cur : PanSemStateFiniteExact 64 F),
      cur.clock ≤ k →
      (evaluateHOLFiniteState cur (.while wcond wbody)).1 ≠ some (.returned rv) := by
    intro k
    induction k with
    | zero =>
      intro cur hk hc
      rw [evaluateHOLFiniteState_while_total] at hc
      split at hc
      · split at hc
        · split at hc <;> [simp at hc; omega]
        · simp at hc
      · simp at hc
    | succ k ih =>
      intro cur hk hc
      rw [evaluateHOLFiniteState_while_total] at hc
      split at hc
      · split at hc
        · split at hc
          · simp at hc
          · dsimp only at hc
            rw [fixClockHOLFinite_evaluateState] at hc
            rcases hb : evaluateHOLFiniteState (decClockHOLFinite cur) wbody with ⟨rb, sb⟩
            rw [hb] at hc
            cases rb with
            | none =>
              have hcl := evaluateHOLFiniteState_clock_le (decClockHOLFinite cur) wbody
              rw [hb] at hcl; dsimp only at hcl
              exact ih sb (by change sb.clock ≤ cur.clock - 1 at hcl; omega) hc
            | some rb' =>
              exfalso
              rw [evaluateHOLFiniteState_assign] at hb
              split at hb
              · simp only [Prod.mk.injEq, Option.some.injEq] at hb; obtain ⟨rfl, _⟩ := hb; simp at hc
              · split at hb
                · simp at hb
                · simp only [Prod.mk.injEq, Option.some.injEq] at hb; obtain ⟨rfl, _⟩ := hb; simp at hc
        · simp at hc
      · simp at hc
  rcases hw : evaluateHOLFiniteState si (.while wcond wbody) with ⟨rw1, postw⟩
  rw [hw] at hret
  cases rw1 with
  | some rw1' =>
    dsimp only at hret
    exact absurd hret (by have := hno_ret_while si.clock si le_rfl; rwa [hw] at this)
  | none =>
    dsimp only at hret
    obtain ⟨dw, hdw_lk, hdw_lt, hdw_pow, hdw_min⟩ := hloop si.clock si postw 0#64 le_rfl hsi_d hsi_n
      (fun hpos => absurd hpos (by decide)) hw
    rw [evaluateHOLFiniteState_return] at hret
    simp only [evalHOLExact, toExact, hdw_lk, shapeOfHOLExact] at hret
    split at hret
    · simp only [Option.some.injEq, PanSemResultExact.returned.injEq] at hret
      exact ⟨dw, hret.symm, hdw_lt, hdw_pow, hdw_min⟩
    · simp at hret

private theorem worldEff_decCall_ceil_log2 {F : Type}
    {s cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    (name : MlS) (argExp : ExpHOL 64) {cont : ProgHOL 64}
    (hnt : (evaluateHOLFiniteState cur (.decCall name .one (ofString "ceil_log2") [argExp] cont)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.decCall name .one (ofString "ceil_log2") [argExp] cont)).1)
    (hcont : ∀ (nw dw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) argExp = some (.val (.word nw)) →
      dw.toNat < 64 →
      nw.toNat ≤ 2 ^ dw.toNat →
      (0 < dw.toNat → 2 ^ (dw.toNat - 1) < nw.toNat) →
      mid.locals = cur.locals.update (name, .val (.word dw)) →
      mid = { cur with locals := mid.locals, clock := mid.clock } →
      WorldEff s mid Rl B gw →
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState mid cont).1 →
      WorldEff s (evaluateHOLFiniteState mid cont).2 Rl B gw) :
    WorldEff s (evaluateHOLFiniteState cur (.decCall name .one (ofString "ceil_log2") [argExp] cont)).2 Rl B gw := by
  have hlook : originalRuntimeCode.lookup (ofString "ceil_log2") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_ceil_log2, .one) :=
    lookup_of_guestAst_getElem 36 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_ceil_log2) rfl
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hcr ⊢
  rcases hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) [argExp] with _ | values
  · exact h
  · simp only [hargs] at hnt hcr ⊢
    rcases hl : lookupCodeHOLFinite cur.code.lookup (ofString "ceil_log2") values with _ | ⟨body', callee, ret'⟩
    · exact h
    · simp only [hl] at hnt hcr ⊢
      by_cases hz : cur.clock = 0
      · rw [if_pos hz] at hnt; exact absurd rfl hnt
      · rw [if_neg hz] at hnt hcr ⊢
        have hsame := lookupCodeHOLFinite_installed_body cur.code.lookup (ofString "ceil_log2") _ _ body'
          _ ret' values callee (by rw [h.code]; exact hlook) hl
        subst hsame
        have hret_eq := lookupCodeHOLFinite_installed_return cur (ofString "ceil_log2") _ _ _
          _ ret' values callee (by rw [h.code]; exact hlook) hl
        subst hret_eq
        obtain ⟨nw, rfl, hnw_callee⟩ := lookupCode_one_word hlook (by rwa [← h.code])
        have harg_ev : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) argExp =
            some (.val (.word nw)) := by
          rw [evalListHOLFinite_eq_toExact] at hargs
          simp only [evalListHOLExact] at hargs
          split at hargs <;> simp at hargs
          rename_i v hv _; rw [hargs.1] at hv; exact hv
        have hentryEq : callEntryStateHOLFinite cur callee =
            { cur with locals := callee, clock := (callEntryStateHOLFinite cur callee).clock } := by
          cases cur; rfl
        have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "ceil_log2") vs =
            some (sourceFnBody Guest.Software.guestFn_ceil_log2, (callEntryStateHOLFinite cur callee).locals, .one) :=
          ⟨[.val (.word nw)], by simpa only [h.code, callEntryStateHOLFinite] using hl⟩
        obtain ⟨_, _, _, _, hspec⟩ := ro_ceil_log2
        have hlook_eq := (h.code ▸ hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "ceil_log2") [.val (.word nw)] = _)
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite cur callee) (sourceFnBody Guest.Software.guestFn_ceil_log2) with ⟨res, cpost⟩
        simp only [hrun] at hnt hcr ⊢
        cases res with
        | none => rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
        | some r1 =>
          cases r1 with
          | returned rv =>
            dsimp only at hnt hcr ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact rv) .one && shapeEqHOL (shapeOfHOLExact rv) .one) = true
            · simp only [hsh, ↓reduceIte] at hnt hcr ⊢
              obtain ⟨dw, rfl, hdw_lt, hdw_pow, hdw_min⟩ := ceil_log2_body_returns (callEntryStateHOLFinite cur callee) nw
                hnw_callee rv (by rw [hrun])
              obtain ⟨params0, body0, ret0, hlook0, hspec0⟩ := ro_ceil_log2
              have hinj := Option.some.inj (hlook.symm.trans hlook0)
              obtain ⟨rfl, hinj2⟩ := Prod.mk.inj hinj
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hinj2
              have hro := hspec0 (callEntryStateHOLFinite cur callee) h.code
                (guestInv_callEntry cur callee h.arena.1) hex
                (by rw [hrun]; simp) (by rw [hrun]; exact Or.inl ⟨.val (.word dw), rfl⟩)
              rw [hrun] at hro; dsimp only at hro
              have hcpost : cpost = { cur with locals := cpost.locals, clock := cpost.clock } :=
                InitECandidate.Solver.Wave8GuestInv.R13.state_trans_locals_clock hentryEq hro
              let mid := setVarHOLFinite name (.val (.word dw)) { cpost with locals := cur.locals }
              have hmid_eq : mid = { cur with locals := mid.locals, clock := mid.clock } := by
                dsimp only [mid, setVarHOLFinite]; rw [hcpost]
              have heff_mid : WorldEff s mid Rl B gw := by
                rw [hmid_eq]; exact h.locals_clock _ _
              exact (hcont nw dw mid harg_ev hdw_lt hdw_pow hdw_min rfl hmid_eq heff_mid hnt hcr).locals_clock _ _
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hcr
              rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
          | exception eid ev =>
            obtain ⟨params0, body0, ret0, hlook0, hspec0⟩ := ro_ceil_log2
            have hinj := Option.some.inj (hlook.symm.trans hlook0)
            obtain ⟨rfl, hinj2⟩ := Prod.mk.inj hinj
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hinj2
            have hres_e : Resumes (some (.exception eid ev)) := by
              rcases hcr with hc0 | hc0 | hc0 | hr <;> [simp at hc0; simp at hc0; simp at hc0; exact hr]
            have hro := hspec0 (callEntryStateHOLFinite cur callee) h.code
              (guestInv_callEntry cur callee h.arena.1) hex
              (by rw [hrun]; simp) (by rw [hrun]; exact hres_e)
            rw [hrun] at hro; dsimp only at hro
            have hcpost : cpost = { cur with locals := cpost.locals, clock := cpost.clock } :=
              InitECandidate.Solver.Wave8GuestInv.R13.state_trans_locals_clock hentryEq hro
            rw [hcpost]; exact h.locals_clock _ _
          | timeOut => exact absurd rfl hnt
          | «break» | «continue» | error | finalFfi _ =>
            rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0

private theorem merkleize_pow2_mul32 {dn nw sizew szw : BitVec 64}
    (hdn59 : dn.toNat < 59)
    (hn_pow : nw.toNat ≤ 2 ^ dn.toNat)
    (hsize : sizew = 1#64 <<< dn)
    (hsz : szw = sizew * 32#64) :
    sizew.toNat = 2 ^ dn.toNat ∧
    szw.toNat = 2 ^ dn.toNat * 32 ∧
    (nw * 32#64).toNat = nw.toNat * 32 ∧
    (nw * 32#64).toNat ≤ szw.toNat ∧
    ((sizew - nw) * 32#64).toNat = szw.toNat - (nw * 32#64).toNat := by
  have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
  have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
  have hsize_nat : sizew.toNat = 2 ^ dn.toNat := by
    rw [hsize]
    change (1#64 <<< dn.toNat).toNat = 2 ^ dn.toNat
    rw [BitVec.toNat_shiftLeft, h1, Nat.shiftLeft_eq, one_mul]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))
  have hsz_nat : szw.toNat = 2 ^ dn.toNat * 32 := by
    rw [hsz, BitVec.toNat_mul, hsize_nat, h32]
    exact Nat.mod_eq_of_lt (by
      calc 2 ^ dn.toNat * 32 ≤ 2 ^ 58 * 32 := Nat.mul_le_mul_right 32 (Nat.pow_le_pow_right (by omega) (by omega))
        _ < 2 ^ 64 := by decide)
  have hn32_nat : (nw * 32#64).toNat = nw.toNat * 32 := by
    rw [BitVec.toNat_mul, h32]
    exact Nat.mod_eq_of_lt (by
      calc nw.toNat * 32 ≤ 2 ^ dn.toNat * 32 := Nat.mul_le_mul_right 32 hn_pow
        _ ≤ 2 ^ 58 * 32 := Nat.mul_le_mul_right 32 (Nat.pow_le_pow_right (by omega) (by omega))
        _ < 2 ^ 64 := by decide)
  have hsub_nat : (sizew - nw).toNat = 2 ^ dn.toNat - nw.toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.2 (by omega)), hsize_nat]
  have hrem32_nat : ((sizew - nw) * 32#64).toNat = (2 ^ dn.toNat - nw.toNat) * 32 := by
    rw [BitVec.toNat_mul, hsub_nat, h32]
    exact Nat.mod_eq_of_lt (by
      calc (2 ^ dn.toNat - nw.toNat) * 32 ≤ 2 ^ dn.toNat * 32 := Nat.mul_le_mul_right 32 (Nat.sub_le _ _)
        _ ≤ 2 ^ 58 * 32 := Nat.mul_le_mul_right 32 (Nat.pow_le_pow_right (by omega) (by omega))
        _ < 2 ^ 64 := by decide)
  refine ⟨hsize_nat, hsz_nat, hn32_nat, by omega, by omega⟩

private theorem max_body_returns {F : Type}
    (entry : PanSemStateFiniteExact 64 F) (aw bw : BitVec 64)
    (ha : entry.locals.lookup (ofString "a") = some (.val (.word aw)))
    (hb : entry.locals.lookup (ofString "b") = some (.val (.word bw)))
    {rv : ValueHOL 64}
    (hret : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_max)).1 = some (.returned rv)) :
    ∃ tw : BitVec 64, rv = .val (.word tw) ∧ tw.toNat = Nat.max aw.toNat bw.toNat := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_max,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hret
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
  have hcmp : @evalHOLExact 64 F _ entry.toExact (fun a => Classical.propDecidable (entry.memaddrs a))
      (.cmp .lower (.var .local (ofString "b")) (.var .local (ofString "a"))) =
      some (.val (.word (if bw < aw then 1#64 else 0#64))) := by
    simp [evalHOLExact, toExact, ha, hb, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp] at hret; dsimp only at hret
  by_cases hlt : bw < aw
  · rw [if_pos hlt] at hret
    simp only [show ¬ ((1#64 : BitVec 64) = 0) by decide, ↓reduceIte, evaluateHOLFiniteState_return,
      evalHOLExact, toExact, ha, shapeOfHOLExact, sizeOfShapeWithContextHOL] at hret
    have hle32 : (1 : Nat) ≤ 32 := by decide
    simp only [hle32, ↓reduceIte] at hret
    injection hret with h1; injection h1 with h2
    refine ⟨aw, h2.symm, ?_⟩
    rw [BitVec.lt_def] at hlt; simp only [Nat.max_def]; split <;> omega
  · rw [if_neg hlt] at hret
    have h0 : (0#64 : BitVec 64) = 0 := rfl
    simp only [h0, ↓reduceIte, evaluateHOLFiniteState_skip, evaluateHOLFiniteState_return,
      evalHOLExact, toExact, hb, shapeOfHOLExact, sizeOfShapeWithContextHOL] at hret
    have hle32 : (1 : Nat) ≤ 32 := by decide
    simp only [hle32, ↓reduceIte] at hret
    injection hret with h1; injection h1 with h2
    refine ⟨bw, h2.symm, ?_⟩
    rw [BitVec.lt_def] at hlt; simp only [Nat.max_def]; split <;> omega

private theorem worldEff_decCall_max {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    (name : MlS) (aExp bExp : ExpHOL 64) {cont : ProgHOL 64}
    (hnt : (evaluateHOLFiniteState cur (.decCall name .one (ofString "max") [aExp, bExp] cont)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.decCall name .one (ofString "max") [aExp, bExp] cont)).1)
    (hcont : ∀ (aw bw tw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) aExp = some (.val (.word aw)) →
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) bExp = some (.val (.word bw)) →
      tw.toNat = Nat.max aw.toNat bw.toNat →
      mid.locals.lookup name = some (.val (.word tw)) →
      mid = { cur with locals := cur.locals.update (name, .val (.word tw)), clock := mid.clock } →
      WorldEff s mid Rl B gw →
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState mid cont).1 →
      WorldEff s (evaluateHOLFiniteState mid cont).2 Rl B gw) :
    WorldEff s (evaluateHOLFiniteState cur (.decCall name .one (ofString "max") [aExp, bExp] cont)).2 Rl B gw := by
  have hlook : originalRuntimeCode.lookup (ofString "max") =
      some ([(ofString "a", .one), (ofString "b", .one)], sourceFnBody Guest.Software.guestFn_max, .one) :=
    lookup_of_guestAst_getElem 32 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_max) rfl
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hcr ⊢
  rcases hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) [aExp, bExp] with _ | values
  · exact h
  · simp only [hargs] at hnt hcr ⊢
    rcases hl : lookupCodeHOLFinite cur.code.lookup (ofString "max") values with _ | ⟨body', callee, ret'⟩
    · exact h
    · simp only [hl] at hnt hcr ⊢
      by_cases hz : cur.clock = 0
      · rw [if_pos hz] at hnt; exact absurd rfl hnt
      · rw [if_neg hz] at hnt hcr ⊢
        have hsame := lookupCodeHOLFinite_installed_body cur.code.lookup (ofString "max")
          [(ofString "a", .one), (ofString "b", .one)] (sourceFnBody Guest.Software.guestFn_max) body'
          .one ret' values callee (by rw [h.code]; exact hlook) hl
        subst hsame
        have hret_eq := lookupCodeHOLFinite_installed_return cur (ofString "max")
          [(ofString "a", .one), (ofString "b", .one)] (sourceFnBody Guest.Software.guestFn_max)
          (sourceFnBody Guest.Software.guestFn_max) .one ret' values callee (by rw [h.code]; exact hlook) hl
        subst hret_eq
        obtain ⟨aw, bw, hvals_eq, ha_cal, hb_cal⟩ :=
          lookupCode_two_words (by decide) hlook (by rwa [h.code] at hl)
        subst hvals_eq
        rw [evalListHOLFinite_eq_toExact] at hargs
        simp only [evalListHOLExact] at hargs
        rcases ha_ev : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) aExp with _ | va
        · simp [ha_ev] at hargs
        · rcases hb_ev : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) bExp with _ | vb
          · simp [ha_ev, hb_ev] at hargs
          · simp only [ha_ev, hb_ev] at hargs
            injection hargs with hargs_eq; injection hargs_eq with hva hargs2; injection hargs2 with hvb _
            subst hva hvb
            have hentryEq : callEntryStateHOLFinite cur callee =
                { cur with locals := callee, clock := (callEntryStateHOLFinite cur callee).clock } := by
              cases cur; rfl
            have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "max") vs =
                some (sourceFnBody Guest.Software.guestFn_max, (callEntryStateHOLFinite cur callee).locals, .one) :=
              ⟨[.val (.word aw), .val (.word bw)], by simpa only [h.code, callEntryStateHOLFinite] using hl⟩
            rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite cur callee)
                (sourceFnBody Guest.Software.guestFn_max) with ⟨res, cpost⟩
            simp only [hrun] at hnt hcr ⊢
            cases res with
            | none => rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
            | some r1 =>
              cases r1 with
              | returned rv =>
                dsimp only at hnt hcr ⊢
                by_cases hsh : (shapeEqHOL (shapeOfHOLExact rv) .one && shapeEqHOL (shapeOfHOLExact rv) .one) = true
                · simp only [hsh, ↓reduceIte] at hnt hcr ⊢
                  obtain ⟨tw, rfl, htw_max⟩ := max_body_returns (callEntryStateHOLFinite cur callee) aw bw
                    ha_cal hb_cal (by rw [hrun])
                  obtain ⟨params0, body0, ret0, hlook0, hspec0⟩ := ro_max_fn
                  have hinj := Option.some.inj (hlook.symm.trans hlook0)
                  obtain ⟨rfl, hinj2⟩ := Prod.mk.inj hinj
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hinj2
                  have hro := hspec0 (callEntryStateHOLFinite cur callee) h.code
                    (guestInv_callEntry cur callee h.arena.1) hex
                    (by rw [hrun]; simp) (by rw [hrun]; exact Or.inl ⟨.val (.word tw), rfl⟩)
                  rw [hrun] at hro; dsimp only at hro
                  have hcpost : cpost = { cur with locals := cpost.locals, clock := cpost.clock } :=
                    InitECandidate.Solver.Wave8GuestInv.R13.state_trans_locals_clock hentryEq hro
                  let mid := setVarHOLFinite name (.val (.word tw)) { cpost with locals := cur.locals }
                  have hmid_eq : mid = { cur with locals := cur.locals.update (name, .val (.word tw)), clock := mid.clock } := by
                    dsimp only [mid, setVarHOLFinite]; rw [hcpost]
                  have heff_mid : WorldEff s mid Rl B gw := by
                    rw [hmid_eq]; exact h.locals_clock _ _
                  exact (hcont aw bw tw mid ha_ev hb_ev htw_max
                    (by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
                    hmid_eq heff_mid hnt hcr).locals_clock _ _
                · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hcr
                  rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
              | exception eid ev =>
                obtain ⟨params0, body0, ret0, hlook0, hspec0⟩ := ro_max_fn
                have hinj := Option.some.inj (hlook.symm.trans hlook0)
                obtain ⟨rfl, hinj2⟩ := Prod.mk.inj hinj
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj hinj2
                have hres_e : Resumes (some (.exception eid ev)) := by
                  rcases hcr with hc0 | hc0 | hc0 | hr <;> [simp at hc0; simp at hc0; simp at hc0; exact hr]
                have hro := hspec0 (callEntryStateHOLFinite cur callee) h.code
                  (guestInv_callEntry cur callee h.arena.1) hex
                  (by rw [hrun]; simp) (by rw [hrun]; exact hres_e)
                rw [hrun] at hro; dsimp only at hro
                have hcpost : cpost = { cur with locals := cpost.locals, clock := cpost.clock } :=
                  InitECandidate.Solver.Wave8GuestInv.R13.state_trans_locals_clock hentryEq hro
                rw [hcpost]; exact h.locals_clock _ _
              | timeOut => exact absurd rfl hnt
              | «break» | «continue» | error | finalFfi _ =>
                rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0

/-- Call wrapper for a 0-dest callee that preserves `WorldEff` AND establishes an extra property `P`
when the callee returns normally (`none` at the call site). -/
private theorem worldEff_call0_eff_post {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    (fname : MlS) (args : List (ExpHOL 64))
    (params : List (MlS × ShapeHOL)) (fbody : ProgHOL 64) (retSh : ShapeHOL)
    (hlook : originalRuntimeCode.lookup fname = some (params, fbody, retSh))
    {P : Prop}
    (hcallee : ∀ (callee : HolFiniteMapExact MlS (ValueHOL 64)) (vals : List (ValueHOL 64)),
      evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args = some vals →
      lookupCodeHOLFinite cur.code.lookup fname vals = some (fbody, callee, retSh) →
      let entry := callEntryStateHOLFinite cur callee
      (evaluateHOLFiniteState entry fbody).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState entry fbody).1 →
      WorldEff s (evaluateHOLFiniteState entry fbody).2 Rl B gw ∧
      ((∃ rv, (evaluateHOLFiniteState entry fbody).1 = some (.returned rv)) → P))
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) fname args)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call (some (none, none)) fname args)).1) :
    WorldEff s (evaluateHOLFiniteState cur (.call (some (none, none)) fname args)).2 Rl B gw ∧
    ((evaluateHOLFiniteState cur (.call (some (none, none)) fname args)).1 = none →
      (evaluateHOLFiniteState cur (.call (some (none, none)) fname args)).2.locals = cur.locals ∧ P) := by
  have hloc := fun (hnone : (evaluateHOLFiniteState cur (.call (some (none, none)) fname args)).1 = none) =>
    call0_none_locals cur fname args hnone
  refine ⟨worldEff_call0_eff h fname args params fbody retSh hlook
    (fun callee vals hargs hl hnt_e hres_e => (hcallee callee vals hargs hl hnt_e hres_e).1) hnt hcr, ?_⟩
  intro hnone
  refine ⟨hloc hnone, ?_⟩
  rw [evaluateHOLFiniteState_call] at hnone hnt
  rcases hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args with _ | vals
  · rw [hargs] at hnone; simp at hnone
  · simp only [hargs] at hnone hnt
    rcases hl : lookupCodeHOLFinite cur.code.lookup fname vals with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hnone
    · simp only [hl] at hnone hnt
      have hsame := lookupCodeHOLFinite_installed_body cur.code.lookup fname params fbody body'
        retSh ret' vals callee (by rw [h.code]; exact hlook) hl
      cases hsame
      have hret_eq := lookupCodeHOLFinite_installed_return cur fname params fbody fbody
        retSh ret' vals callee (by rw [h.code]; exact hlook) hl
      cases hret_eq
      split at hnone
      · simp at hnone
      · rename_i hcz
        rw [if_neg hcz] at hnt
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite cur callee) fbody with ⟨res, cpost⟩
        simp only [hrun] at hnone hnt
        cases res with
        | none => simp at hnone
        | some r1 =>
          cases r1 with
          | returned rv =>
            exact (hcallee callee vals hargs hl (by rw [hrun]; simp)
              (by rw [hrun]; exact Or.inl ⟨rv, rfl⟩)).2 ⟨rv, by rw [hrun]⟩
          | _ => simp at hnone

private theorem evalList_last_word {F : Type}
    {cur : PanSemStateFiniteExact 64 F}
    {pre : List (ExpHOL 64)} {outExp : ExpHOL 64}
    {vals : List (ValueHOL 64)} {outw : BitVec 64}
    (hout : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) outExp =
      some (.val (.word outw)))
    (hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) (pre ++ [outExp]) =
      some vals) :
    ∃ preVals : List (ValueHOL 64), vals = preVals ++ [.val (.word outw)] := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  induction pre generalizing vals with
  | nil =>
    simp only [List.nil_append, evalListHOLExact, hout] at hargs
    injection hargs with hargs'
    exact ⟨[], hargs'.symm⟩
  | cons e es ih =>
    simp only [List.cons_append, evalListHOLExact] at hargs
    rcases he : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) e with _ | ve
    · simp [he] at hargs
    · rcases hes : @evalListHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
          (es ++ [outExp]) with _ | ves
      · simp [he, hes] at hargs
      · simp only [he, hes] at hargs
        injection hargs with hargs'
        subst hargs'
        obtain ⟨pv, rfl⟩ := ih (vals := ves) hes
        exact ⟨ve :: pv, rfl⟩

private def OutIvlCovered {F : Type} (s0 : PanSemStateFiniteExact 64 F) (Rl : List Ivl) (outw : BitVec 64) : Prop :=
  (∃ j ∈ Rl, j.1 ≤ outw.toNat ∧ outw.toNat + 32 ≤ j.1 + j.2) ∨
  (globN s0 "heap_ptr" ≤ outw.toNat ∧ outw.toNat + 32 ≤ heapLimit)

private theorem outIvlCovered_to_world {F : Type}
    {s0 : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)} {outw : BitVec 64}
    (hout : OutIvlCovered s0 Rl outw) (k : Nat) (hk : k ≤ 32) :
    (∃ j ∈ Rl, j.1 ≤ outw.toNat ∧ outw.toNat + k ≤ j.1 + j.2) ∨
    (∃ gs ∈ B, (bufferRegion s0 gs).1 ≤ outw.toNat ∧ outw.toNat + k ≤ (bufferRegion s0 gs).1 + (bufferRegion s0 gs).2) ∨
    (globN s0 "frame_mem_ptr" ≤ outw.toNat ∧ outw.toNat + k ≤ globN s0 "scratch_ptr") ∨
    (globN s0 "heap_ptr" ≤ outw.toNat ∧ outw.toNat + k ≤ heapLimit) := by
  rcases hout with ⟨j, hj, h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨j, hj, h1, by omega⟩
  · exact Or.inr (Or.inr (Or.inr ⟨h1, by omega⟩))

private theorem outIvlCovered_heap_offset {F : Type}
    {s0 : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    {basew offw : BitVec 64} {sz : Nat}
    (hlo : globN s0 "heap_ptr" ≤ basew.toNat)
    (hhi : basew.toNat + sz ≤ heapLimit)
    (hoff : offw.toNat + 32 ≤ sz) :
    OutIvlCovered s0 Rl (basew + offw) := by
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hadd : (basew + offw).toNat = basew.toNat + offw.toNat :=
    BitVec.toNat_add_of_lt (by omega)
  exact Or.inr ⟨by omega, by omega⟩

private theorem call0_ne_break {F : Type} (u : PanSemStateFiniteExact 64 F)
    (fn : MlS) (args : List (ExpHOL 64)) :
    (evaluateHOLFiniteState u (.call (some (none, none)) fn args)).1 ≠ some .break := by
  rw [evaluateHOLFiniteState_call]
  rcases evalListHOLFinite u (h := fun a => Classical.propDecidable (u.memaddrs a)) args with _ | vals
  · simp
  · dsimp only
    rcases lookupCodeHOLFinite u.code.lookup fn vals with _ | ⟨body, callee, ret⟩
    · simp
    · dsimp only
      by_cases hk : u.clock = 0
      · rw [if_pos hk]; simp
      · rw [if_neg hk]
        rcases evaluateHOLFiniteState (callEntryStateHOLFinite u callee) body with ⟨r, st⟩
        cases r with
        | none => simp
        | some r1 =>
          cases r1 with
          | returned rv => dsimp only; split <;> simp
          | _ => simp

private theorem assign_local_ne_break {F : Type} (u : PanSemStateFiniteExact 64 F)
    (x : MlS) (e : ExpHOL 64) :
    (evaluateHOLFiniteState u (.assign .local x e)).1 ≠ some .break := by
  rw [evaluateHOLFiniteState_assign]
  rcases @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) e with _ | v
  · simp
  · dsimp only; split <;> simp

private theorem while_ne_break {F : Type} (st : PanSemStateFiniteExact 64 F)
    (c : ExpHOL 64) (b : ProgHOL 64) :
    (evaluateHOLFiniteState st (.while c b)).1 ≠ some .break := by
  induction hclk : st.clock using Nat.strong_induction_on generalizing st with
  | h k ih =>
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    rcases hc0 : @evalHOLFinite 64 F _ st (fun a => Classical.propDecidable (st.memaddrs a)) c with _ | cv0
    · simp
    · rcases cv0 with ⟨⟨cw0⟩⟩ | _ | _ <;> try simp
      by_cases hwz : cw0 = 0#64
      · subst hwz; simp
      · rw [if_neg hwz]
        by_cases hkz : st.clock = 0
        · rw [if_pos hkz]; simp
        · rw [if_neg hkz]
          have hrem0 := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) b
          rcases hb0 : evaluateHOLFiniteState (decClockHOLFinite st) b with ⟨rb0, sb0⟩
          simp only [hb0] at hrem0 ⊢
          have hlt0 : sb0.clock < k := by change sb0.clock ≤ st.clock - 1 at hrem0; omega
          cases rb0 with
          | none => exact ih sb0.clock hlt0 sb0 rfl
          | some r0 => cases r0 <;> simp [ih sb0.clock hlt0 sb0 rfl]

private theorem seq_ne_break {F : Type} (u : PanSemStateFiniteExact 64 F)
    {a b : ProgHOL 64}
    (ha : (evaluateHOLFiniteState u a).1 ≠ some .break)
    (hb : ∀ mid, evaluateHOLFiniteState u a = (none, mid) → (evaluateHOLFiniteState mid b).1 ≠ some .break) :
    (evaluateHOLFiniteState u (.seq a b)).1 ≠ some .break := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases ha0 : evaluateHOLFiniteState u a with ⟨ra, mid⟩
  rw [ha0] at ha
  cases ra with
  | none => exact hb mid ha0
  | some r => simp [ha]

private theorem dec_word_ne_break {F : Type} (u : PanSemStateFiniteExact 64 F)
    (x : MlS) (e : ExpHOL 64) (w : BitVec 64) {body : ProgHOL 64}
    (hev : @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) e = some (.val (.word w)))
    (hb : (evaluateHOLFiniteState (setVarHOLFinite x (.val (.word w)) u) body).1 ≠ some .break) :
    (evaluateHOLFiniteState u (.dec x .one e body)).1 ≠ some .break := by
  rw [evaluateHOLFiniteState_dec_total]
  simp only [hev, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
  exact hb

private theorem call0_ne_continue {F : Type} (u : PanSemStateFiniteExact 64 F)
    (fn : MlS) (args : List (ExpHOL 64)) :
    (evaluateHOLFiniteState u (.call (some (none, none)) fn args)).1 ≠ some .continue := by
  rw [evaluateHOLFiniteState_call]
  rcases evalListHOLFinite u (h := fun a => Classical.propDecidable (u.memaddrs a)) args with _ | vals
  · simp
  · dsimp only
    rcases lookupCodeHOLFinite u.code.lookup fn vals with _ | ⟨body, callee, ret⟩
    · simp
    · dsimp only
      by_cases hk : u.clock = 0
      · rw [if_pos hk]; simp
      · rw [if_neg hk]
        rcases evaluateHOLFiniteState (callEntryStateHOLFinite u callee) body with ⟨r, st⟩
        cases r with
        | none => simp
        | some r1 =>
          cases r1 with
          | returned rv => dsimp only; split <;> simp
          | _ => simp

private theorem while_ne_continue {F : Type} (st : PanSemStateFiniteExact 64 F)
    (c : ExpHOL 64) (b : ProgHOL 64) :
    (evaluateHOLFiniteState st (.while c b)).1 ≠ some .continue := by
  induction hclk : st.clock using Nat.strong_induction_on generalizing st with
  | h k ih =>
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    rcases hc0 : @evalHOLFinite 64 F _ st (fun a => Classical.propDecidable (st.memaddrs a)) c with _ | cv0
    · simp
    · rcases cv0 with ⟨⟨cw0⟩⟩ | _ | _ <;> try simp
      by_cases hwz : cw0 = 0#64
      · subst hwz; simp
      · rw [if_neg hwz]
        by_cases hkz : st.clock = 0
        · rw [if_pos hkz]; simp
        · rw [if_neg hkz]
          have hrem0 := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) b
          rcases hb0 : evaluateHOLFiniteState (decClockHOLFinite st) b with ⟨rb0, sb0⟩
          simp only [hb0] at hrem0 ⊢
          have hlt0 : sb0.clock < k := by change sb0.clock ≤ st.clock - 1 at hrem0; omega
          cases rb0 with
          | none => exact ih sb0.clock hlt0 sb0 rfl
          | some r0 => cases r0 <;> simp [ih sb0.clock hlt0 sb0 rfl]

private theorem evalList3_last_word {F : Type}
    {cur : PanSemStateFiniteExact 64 F}
    {e0 e1 e2 : ExpHOL 64} {vals : List (ValueHOL 64)} {w2 : BitVec 64}
    (he2 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) e2 =
      some (.val (.word w2)))
    (hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) [e0, e1, e2] =
      some vals) :
    ∃ v0 v1, vals = [v0, v1, .val (.word w2)] := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  rcases h0 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) e0 with _ | v0
  · simp [evalListHOLExact, h0] at hargs
  · rcases h1 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) e1 with _ | v1
    · simp [evalListHOLExact, h0, h1] at hargs
    · simp only [evalListHOLExact, h0, h1, he2] at hargs
      injection hargs with hargs_eq
      exact ⟨v0, v1, hargs_eq.symm⟩

private theorem worldEff_while_cond_post {F : Type} {s : PanSemStateFiniteExact 64 F}
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
      WorldEff s (evaluateHOLFiniteState cur (.while cond body)).2 Rl B gw ∧
      ((evaluateHOLFiniteState cur (.while cond body)).1 = none →
        (∀ t, Inv t → (evaluateHOLFiniteState t body).1 ≠ some .break) →
        Inv (evaluateHOLFiniteState cur (.while cond body)).2 ∧
        (∀ cw : BitVec 64,
          @evalHOLFinite 64 F _ (evaluateHOLFiniteState cur (.while cond body)).2
            (fun a => Classical.propDecidable ((evaluateHOLFiniteState cur (.while cond body)).2.memaddrs a)) cond =
            some (.val (.word cw)) → cw = 0)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro cur hclk heff hinv hnt hcr
    have hw_eq := evaluateHOLFiniteState_while_fixClockRewrite cur cond body
    rcases hc : @evalHOLFinite 64 F _ cur (fun a => Classical.propDecidable (cur.memaddrs a)) cond with _ | cv
    · rw [hc] at hw_eq; simp only [hw_eq]
      exact ⟨heff, fun hnone _ => by simp at hnone⟩
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;>
        try (rw [hc] at hw_eq; simp only [hw_eq]; exact ⟨heff, fun hnone _ => by simp at hnone⟩)
      rw [hc] at hw_eq; dsimp only at hw_eq
      by_cases hw0 : cw = 0
      · subst hw0; rw [if_neg (by simp)] at hw_eq; rw [hw_eq]
        refine ⟨heff, fun _ _ => ⟨hinv, fun cw' hcw' => ?_⟩⟩
        change @evalHOLFinite 64 F _ cur (fun a => Classical.propDecidable (cur.memaddrs a)) cond = _ at hcw'
        rw [hc] at hcw'; injection hcw' with h1; injection h1 with h2; injection h2 with h3; exact h3.symm
      · rw [if_pos hw0] at hw_eq
        by_cases hk0 : cur.clock = 0
        · rw [if_pos hk0] at hw_eq; rw [hw_eq] at hnt; exact absurd rfl hnt
        · rw [if_neg hk0] at hw_eq
          have heff_d : WorldEff s (decClockHOLFinite cur) Rl B gw := heff.locals_clock cur.locals (cur.clock - 1)
          have hinv_d : Inv (decClockHOLFinite cur) := hdec cur hinv
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite cur) body
          rcases hbo : evaluateHOLFiniteState (decClockHOLFinite cur) body with ⟨rb, sb⟩
          rw [hbo] at hw_eq hrem
          have hlt : sb.clock < k := by change sb.clock ≤ cur.clock - 1 at hrem; omega
          cases rb with
          | none =>
            dsimp only at hw_eq
            obtain ⟨heff_b, hinv_b⟩ := hb cur cw hc hw0 heff_d hinv_d
              (by rw [hbo]; simp) (by rw [hbo]; exact Or.inl rfl)
            rw [hbo] at heff_b hinv_b
            rw [hw_eq] at hnt hcr ⊢
            exact ih sb.clock hlt sb rfl heff_b (hinv_b (Or.inl rfl)) hnt hcr
          | some r1 =>
            cases r1 with
            | «continue» =>
              dsimp only at hw_eq
              obtain ⟨heff_b, hinv_b⟩ := hb cur cw hc hw0 heff_d hinv_d
                (by rw [hbo]; simp) (by rw [hbo]; exact Or.inr (Or.inr (Or.inl rfl)))
              rw [hbo] at heff_b hinv_b
              rw [hw_eq] at hnt hcr ⊢
              exact ih sb.clock hlt sb rfl heff_b (hinv_b (Or.inr rfl)) hnt hcr
            | «break» =>
              dsimp only at hw_eq; rw [hw_eq]
              obtain ⟨heff_b, _⟩ := hb cur cw hc hw0 heff_d hinv_d
                (by rw [hbo]; simp) (by rw [hbo]; exact Or.inr (Or.inl rfl))
              rw [hbo] at heff_b
              exact ⟨heff_b, fun _ hno_brk => absurd (by rw [hbo]) (hno_brk (decClockHOLFinite cur) hinv_d)⟩
            | timeOut =>
              dsimp only at hw_eq; rw [hw_eq] at hnt; exact absurd rfl hnt
            | returned v =>
              dsimp only at hw_eq; rw [hw_eq]
              obtain ⟨heff_b, _⟩ := hb cur cw hc hw0 heff_d hinv_d
                (by rw [hbo]; simp) (by rw [hbo]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨v, rfl⟩))))
              rw [hbo] at heff_b; exact ⟨heff_b, fun h _ => by simp at h⟩
            | exception eid ev =>
              dsimp only at hw_eq; rw [hw_eq] at hcr ⊢
              have hres_e : Resumes (some (.exception eid ev)) := by
                rcases hcr with h | h | h | hr <;> [cases h; cases h; cases h; exact hr]
              obtain ⟨heff_b, _⟩ := hb cur cw hc hw0 heff_d hinv_d
                (by rw [hbo]; simp) (by rw [hbo]; exact Or.inr (Or.inr (Or.inr hres_e)))
              rw [hbo] at heff_b; exact ⟨heff_b, fun h _ => by simp at h⟩
            | error =>
              dsimp only at hw_eq; rw [hw_eq] at hcr
              rcases hcr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> cases h
            | finalFfi _ =>
              dsimp only at hw_eq; rw [hw_eq] at hcr
              rcases hcr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> cases h

private theorem worldEff_merkleize {F : Type}
    (s0 cur : PanSemStateFiniteExact 64 F) {Rl : List Ivl}
    (hAs0 : ArenaOK s0)
    (heff_cur : WorldEff s0 cur Rl sszBufs hpGw)
    {nw outw : BitVec 64}
    (hn_lk : cur.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hn_bound : nw.toNat < 2 ^ 35)
    (hout_lk : cur.locals.lookup (ofString "out") = some (.val (.word outw)))
    (hout_cov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_merkleize)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_merkleize)).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_merkleize)).2 Rl sszBufs hpGw := by
  have hhl_val : heapLimit = 2952790016 := by decide
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_merkleize,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_decCall_ceil_log2 heff_cur (ofString "dl") (.var .local (ofString "limit"))
    hnt (Or.inr (Or.inr (Or.inr hres)))
    (fun limw dl m1 _ hdl_lt _ _ hm1_loc hm1_eq heff_m1 hnt1 hcr1 => ?_)
  have hm1_out : m1.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hout_lk,
      show ofString "dl" ≠ ofString "out" by decide]
  have hm1_n : m1.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hn_lk,
      show ofString "dl" ≠ ofString "n" by decide]
  refine worldEff_decCall_ceil_log2 heff_m1 (ofString "dn") (.var .local (ofString "n"))
    hnt1 hcr1
    (fun nw' dn m2 hn_ev hdn_lt hn_pow hdn_min hm2_loc hm2_eq heff_m2 hnt2 hcr2 => ?_)
  have hnw_eq : nw = nw' := by
    simp [evalHOLExact, toExact, hm1_n] at hn_ev; exact hn_ev
  subst hnw_eq
  have hdn59 : dn.toNat < 59 := by
    by_contra hge
    have hgt0 : 0 < dn.toNat := by omega
    have hmin := hdn_min hgt0
    have : 2 ^ 58 ≤ 2 ^ (dn.toNat - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hm2_n : m2.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_n,
      show ofString "dn" ≠ ofString "n" by decide]
  have hm2_dn : m2.locals.lookup (ofString "dn") = some (.val (.word dn)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hm2_dl : m2.locals.lookup (ofString "dl") = some (.val (.word dl)) := by
    rw [hm2_loc, hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "dn" ≠ ofString "dl" by decide]
  have hm2_out : m2.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_out,
      show ofString "dn" ≠ ofString "out" by decide]
  refine worldEff_decCall_max heff_m2 (ofString "target") (.var .local (ofString "dl")) (.var .local (ofString "dn"))
    hnt2 hcr2
    (fun dl' dn' targetw m3 hdl_ev hdn_ev htw_max _ hm3_eq heff_m3 hnt3 hcr3 => ?_)
  have hdl_eq : dl = dl' := by simp [evalHOLExact, toExact, hm2_dl] at hdl_ev; exact hdl_ev
  have hdn_eq : dn = dn' := by simp [evalHOLExact, toExact, hm2_dn] at hdn_ev; exact hdn_ev
  subst hdl_eq hdn_eq
  have htw_lt : targetw.toNat < 64 := by
    have : Nat.max dl.toNat dn.toNat < 64 := Nat.max_lt.2 ⟨hdl_lt, hdn_lt⟩
    omega
  have hm3_loc : m3.locals = m2.locals.update (ofString "target", .val (.word targetw)) := by
    rw [hm3_eq]
  have hm3_n : m3.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    rw [hm3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm2_n,
      show ofString "target" ≠ ofString "n" by decide]
  have hm3_dn : m3.locals.lookup (ofString "dn") = some (.val (.word dn)) := by
    rw [hm3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm2_dn,
      show ofString "target" ≠ ofString "dn" by decide]
  have hm3_tw : m3.locals.lookup (ofString "target") = some (.val (.word targetw)) := by
    rw [hm3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hm3_out : m3.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm2_out,
      show ofString "target" ≠ ofString "out" by decide]
  -- `seq (ite (n == 0) (memcpy(out, zero_hashes + target * 32, 32); return 0) skip) ...`
  refine worldEff_seq hnt3 hcr3
    (fun hnt_ite hcr_ite =>
      worldEff_ite heff_m3 _ hnt_ite hcr_ite
        (fun _ _ _ hnt_y hcr_y =>
          worldEff_seq hnt_y hcr_y
            (fun hnt_cp0 hcr_cp0 =>
              (worldEff_call0_memcpy_word heff_m3
                (.var .local (ofString "out")) _ (.const 32#64) outw 32#64
                (by simp [evalHOLExact, toExact, hm3_out])
                rfl
                (fun _ _ => outIvlCovered_to_world hout_cov 32 le_rfl)
                hnt_cp0 hcr_cp0).1)
            (fun m_ret _ heff_mret _ _ => worldEff_return heff_mret _))
        (fun _ _ _ => worldEff_skip heff_m3))
    (fun m3b hm3b heff_m3b hnt4 hcr4 => ?_)
  have hm3b_eq : m3b = m3 ∧ nw ≠ 0#64 := by
    rw [evaluateHOLFiniteState_ite] at hm3b
    by_cases hnw0 : nw = 0#64
    · exfalso
      subst hnw0
      have hc_t : @evalHOLExact 64 F _ m3.toExact (fun a => Classical.propDecidable (m3.memaddrs a))
          (.cmp .equal (.var .local (ofString "n")) (.const 0#64)) = some (.val (.word 1#64)) := by
        simp [evalHOLExact, toExact, hm3_n, Compiler.Encoders.Asm.wordCmpHOL]
      rw [hc_t] at hm3b; dsimp only at hm3b
      rw [if_neg (by decide)] at hm3b
      rw [evaluateHOLFiniteState_seq_line780] at hm3b
      rcases hcp0 : evaluateHOLFiniteState m3 _ with ⟨rcp0, scp0⟩
      rw [hcp0] at hm3b
      cases rcp0 with
      | some _ => simp at hm3b
      | none =>
        dsimp only at hm3b
        rw [evaluateHOLFiniteState_return] at hm3b
        simp [evalHOLExact, shapeOfHOLExact] at hm3b
    · have hc_f : @evalHOLExact 64 F _ m3.toExact (fun a => Classical.propDecidable (m3.memaddrs a))
          (.cmp .equal (.var .local (ofString "n")) (.const 0#64)) = some (.val (.word 0#64)) := by
        simp [evalHOLExact, toExact, hm3_n, Compiler.Encoders.Asm.wordCmpHOL, hnw0]
      rw [hc_f] at hm3b; dsimp only at hm3b; rw [if_pos (by decide), evaluateHOLFiniteState_skip] at hm3b
      exact ⟨(Prod.mk.inj hm3b).2.symm, hnw0⟩
  obtain ⟨rfl, hnw_ne⟩ := hm3b_eq
  -- `mark := heap_mark()`
  refine worldEff_decCall_heap_mark heff_m3 (ofString "mark") hnt4 hcr4
    (fun markw m4 _ _ hmark_al hmark_lo hmark_hi hm4_eq heff_m4 hnt5 hcr5 => ?_)
  have hm4_n : m4.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    rw [hm4_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm3_n,
      show ofString "mark" ≠ ofString "n" by decide]
  have hm4_dn : m4.locals.lookup (ofString "dn") = some (.val (.word dn)) := by
    rw [hm4_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm3_dn,
      show ofString "mark" ≠ ofString "dn" by decide]
  have hm4_tw : m4.locals.lookup (ofString "target") = some (.val (.word targetw)) := by
    rw [hm4_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm3_tw,
      show ofString "mark" ≠ ofString "target" by decide]
  have hm4_out : m4.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm4_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm3_out,
      show ofString "mark" ≠ ofString "out" by decide]
  have hm4_mark : m4.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    rw [hm4_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  -- `dec size := 1 <<< dn`
  refine worldEff_dec heff_m4 (ofString "size") .one _ hnt5 hcr5
    (fun vsz hvsz hvsh5 hnt6 hcr6 => ?_)
  rcases vsz with ⟨⟨sizew⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hvsh5)
  have hsize_eq : sizew = 1#64 <<< dn := by
    simp [evalHOLExact, toExact, hm4_dn, wordShiftHOL, hdn_lt] at hvsz
    exact hvsz.symm
  let m5 := setVarHOLFinite (ofString "size") (.val (.word sizew)) m4
  have heff_m5 : WorldEff s0 m5 Rl sszBufs hpGw := heff_m4.locals_clock _ _
  have hm5_sz : m5.locals.lookup (ofString "size") = some (.val (.word sizew)) := by
    simp [m5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hm5_n : m5.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    simp [m5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm4_n,
      show ofString "size" ≠ ofString "n" by decide]
  have hm5_dn : m5.locals.lookup (ofString "dn") = some (.val (.word dn)) := by
    simp [m5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm4_dn,
      show ofString "size" ≠ ofString "dn" by decide]
  have hm5_tw : m5.locals.lookup (ofString "target") = some (.val (.word targetw)) := by
    simp [m5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm4_tw,
      show ofString "size" ≠ ofString "target" by decide]
  have hm5_out : m5.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    simp [m5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm4_out,
      show ofString "size" ≠ ofString "out" by decide]
  have hm5_mark : m5.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    simp [m5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm4_mark,
      show ofString "size" ≠ ofString "mark" by decide]
  -- `decCall buf := alloc(size * 32)`
  refine worldEff_decCall_alloc heff_m5 (by decide) (ofString "buf") _ hnt6 hcr6
    (fun bufw szw m6 hsz_ev _ hm6_loc _ heff_m6 _ _ hbuf_lo hbuf_end hhp_m6 _ hnt7 hcr7 => ?_)
  obtain ⟨wa, wb, hwa, hwb, hsz_mul⟩ := eval_panMul_of_eval hsz_ev
  have hwa_eq : wa = sizew := by simp [evalHOLExact, toExact, hm5_sz] at hwa; exact hwa.symm
  have hwb_eq : wb = 32#64 := by simp [evalHOLExact] at hwb; exact hwb.symm
  have hsz_eq : szw = sizew * 32#64 := by rw [hsz_mul, hwa_eq, hwb_eq]
  obtain ⟨hsize_nat, hsz_nat, hn32_nat, hn32_le_sz, hrem32_nat⟩ :=
    merkleize_pow2_mul32 hdn59 hn_pow hsize_eq hsz_eq
  have hbuf_cap : bufw.toNat + szw.toNat ≤ heapLimit := by
    have : szw.toNat ≤ (szw.toNat + 7) / 8 * 8 := by omega
    omega
  have hdn26 : dn.toNat ≤ 26 := by
    by_contra hgt
    have : 2 ^ 27 * 32 ≤ 2 ^ dn.toNat * 32 :=
      Nat.mul_le_mul_right 32 (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  have hsize_pos : 1 ≤ sizew.toNat := by
    rw [hsize_nat]; exact Nat.one_le_pow _ _ (by omega)
  have hbuf_32 : bufw.toNat + 32 ≤ heapLimit := by omega
  have hm6_buf : m6.locals.lookup (ofString "buf") = some (.val (.word bufw)) := by
    rw [hm6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hm6_sz : m6.locals.lookup (ofString "size") = some (.val (.word sizew)) := by
    rw [hm6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm5_sz,
      show ofString "buf" ≠ ofString "size" by decide]
  have hm6_n : m6.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    rw [hm6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm5_n,
      show ofString "buf" ≠ ofString "n" by decide]
  have hm6_dn : m6.locals.lookup (ofString "dn") = some (.val (.word dn)) := by
    rw [hm6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm5_dn,
      show ofString "buf" ≠ ofString "dn" by decide]
  have hm6_tw : m6.locals.lookup (ofString "target") = some (.val (.word targetw)) := by
    rw [hm6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm5_tw,
      show ofString "buf" ≠ ofString "target" by decide]
  have hm6_out : m6.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm5_out,
      show ofString "buf" ≠ ofString "out" by decide]
  have hm6_mark : m6.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    rw [hm6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm5_mark,
      show ofString "buf" ≠ ofString "mark" by decide]
  -- `memcpy(buf, p, n * 32)`
  have hpan_n32 : ∀ (st : PanSemStateFiniteExact 64 F),
      st.locals.lookup (ofString "n") = some (.val (.word nw)) →
      @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
        (.panop .mul [.var .local (ofString "n"), .const 32#64]) = some (.val (.word (nw * 32#64))) := by
    intro st hst_n
    have hlt_n32 : nw.toNat * (32#64 : BitVec 64).toNat < 2 ^ 64 := by
      rw [show (32#64 : BitVec 64).toNat = 32 from rfl]; omega
    simp [evalHOLExact, evalListHOLExact, toExact, hst_n, valueIsWord, valueWord, panOpHOL, hlt_n32]
  refine worldEff_seq hnt7 hcr7
    (fun hnt_cp1 hcr_cp1 =>
      (worldEff_call0_memcpy_word heff_m6
        (.var .local (ofString "buf")) (.var .local (ofString "p"))
        (.panop .mul [.var .local (ofString "n"), .const 32#64]) bufw (nw * 32#64)
        (by simp [evalHOLExact, toExact, hm6_buf])
        (hpan_n32 m6 hm6_n)
        (fun _ _ => Or.inr (Or.inr (Or.inr ⟨hbuf_lo, by omega⟩)))
        hnt_cp1 hcr_cp1).1)
    (fun m7 hm7 heff_m7 hnt8 hcr8 => ?_)
  have hm7_loc : m7.locals = m6.locals := by
    have := call0_none_locals m6 (ofString "memcpy") _ (by rw [hm7])
    rwa [hm7] at this
  -- `memzero(buf + n * 32, (size - n) * 32)`
  have hbuf_n32_add : (bufw + nw * 32#64).toNat = bufw.toNat + (nw * 32#64).toNat :=
    BitVec.toNat_add_of_lt (by omega)
  have hsub_nat : (sizew - nw).toNat = sizew.toNat - nw.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.2 (by rw [hsize_nat]; exact hn_pow))
  have hpan_rem32 : @evalHOLExact 64 F _ m7.toExact (fun a => Classical.propDecidable (m7.memaddrs a))
      (.panop .mul [.op .sub [.var .local (ofString "size"), .var .local (ofString "n")], .const 32#64]) =
      some (.val (.word ((sizew - nw) * 32#64))) := by
    have hlt_rem : (sizew - nw).toNat * (32#64 : BitVec 64).toNat < 2 ^ 64 := by
      rw [hsub_nat, show (32#64 : BitVec 64).toNat = 32 from rfl]; omega
    simp [evalHOLExact, evalListHOLExact, toExact, hm7_loc, hm6_sz, hm6_n,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, hlt_rem]
  refine worldEff_seq hnt8 hcr8
    (fun hnt_mz hcr_mz =>
      worldEff_call0_funByteEff heff_m7 funByteEff_memzero _
        [((bufw + nw * 32#64).toNat, ((sizew - nw) * 32#64).toNat)]
        (fun vals hargs i hi _ => by
          rw [evalListHOLFinite_eq_toExact] at hargs
          have hn32_ev := hpan_n32 m7 (by rw [hm7_loc]; exact hm6_n)
          have hbuf_ev : @evalHOLExact 64 F _ m7.toExact (fun a => Classical.propDecidable (m7.memaddrs a))
              (.var .local (ofString "buf")) = some (.val (.word bufw)) := by
            simp [evalHOLExact, toExact, hm7_loc, hm6_buf]
          have ha1 : @evalHOLExact 64 F _ m7.toExact (fun a => Classical.propDecidable (m7.memaddrs a))
              (.op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "n"), .const 32#64]]) =
              some (.val (.word (bufw + nw * 32#64))) := by
            simp [evalHOLExact, evalListHOLExact, toExact, hm7_loc, hm6_buf, hm6_n,
              valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL]
          simp only [evalListHOLExact, ha1, hpan_rem32] at hargs
          injection hargs with hargs_eq; subst hargs_eq
          have hi_eq : i = ((bufw + nw * 32#64).toNat, ((sizew - nw) * 32#64).toNat) := by
            simpa [valWordNat] using hi
          rw [hi_eq]
          exact ⟨((bufw + nw * 32#64).toNat, ((sizew - nw) * 32#64).toNat), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
        (fun iv hiv _ => by
          simp only [List.mem_singleton] at hiv; subst hiv
          exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
        hnt_mz hcr_mz)
    (fun m8 hm8 heff_m8 hnt9 hcr9 => ?_)
  have hm8_loc : m8.locals = m7.locals := by
    have := call0_none_locals m7 (ofString "memzero") _ (by rw [hm8])
    rwa [hm8] at this
  -- `dec cur := size`
  refine worldEff_dec heff_m8 (ofString "cur") .one _ hnt9 hcr9
    (fun vcur hvcur hvsh9 hnt10 hcr10 => ?_)
  rcases vcur with ⟨⟨curw0⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hvsh9)
  have hcur0_eq : sizew = curw0 := by
    simp [evalHOLExact, toExact, hm8_loc, hm7_loc, hm6_sz] at hvcur; exact hvcur
  subst hcur0_eq
  let m9 := setVarHOLFinite (ofString "cur") (.val (.word sizew)) m8
  have heff_m9 : WorldEff s0 m9 Rl sszBufs hpGw := heff_m8.locals_clock _ _
  -- Outer halving loop: `while (1 < cur) { half := cur >>> 1; j := 0; while (j < half) { sha256_pair(..., buf + j * 32); j := j + 1 }; cur := half }`
  let Inv1 : PanSemStateFiniteExact 64 F → Prop := fun st =>
    st.locals.lookup (ofString "buf") = some (.val (.word bufw)) ∧
    st.locals.lookup (ofString "dn") = some (.val (.word dn)) ∧
    st.locals.lookup (ofString "target") = some (.val (.word targetw)) ∧
    st.locals.lookup (ofString "out") = some (.val (.word outw)) ∧
    st.locals.lookup (ofString "mark") = some (.val (.word markw)) ∧
    ∃ curw : BitVec 64, st.locals.lookup (ofString "cur") = some (.val (.word curw)) ∧ curw.toNat ≤ sizew.toNat
  have hInv1_m9 : Inv1 m9 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, sizew, ?_, le_rfl⟩ <;>
      simp [m9, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm8_loc, hm7_loc,
        hm6_buf, hm6_dn, hm6_tw, hm6_out, hm6_mark,
        show ofString "cur" ≠ ofString "buf" by decide,
        show ofString "cur" ≠ ofString "dn" by decide,
        show ofString "cur" ≠ ofString "target" by decide,
        show ofString "cur" ≠ ofString "out" by decide,
        show ofString "cur" ≠ ofString "mark" by decide]
  let body1Prog : ProgHOL 64 :=
    .dec (ofString "half") .one (.shift .lsr (.var .local (ofString "cur")) (.const 1#64))
      (.dec (ofString "j") .one (.const 0#64)
        (.seq
          (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "half")))
            (.seq
              (.call (some (none, none)) (ofString "sha256_pair")
                [.op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "j"), .const 64#64]],
                 .op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "j"), .const 64#64], .const 32#64],
                 .op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "j"), .const 32#64]]])
              (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1#64]))))
          (.assign .local (ofString "cur") (.var .local (ofString "half")))))
  have hbody1 : ∀ t, WorldEff s0 t Rl sszBufs hpGw → Inv1 t →
      (evaluateHOLFiniteState t body1Prog).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState t body1Prog).1 →
      WorldEff s0 (evaluateHOLFiniteState t body1Prog).2 Rl sszBufs hpGw ∧
      (((evaluateHOLFiniteState t body1Prog).1 = none ∨ (evaluateHOLFiniteState t body1Prog).1 = some .continue) →
        Inv1 (evaluateHOLFiniteState t body1Prog).2) := by
    intro t heff_t ⟨ht_buf, ht_dn, ht_tw, ht_out, ht_mark, curw, ht_cur, hcur_le⟩ hnt_b1 hcr_b1
    have half_nat : (curw >>> 1#64).toNat = curw.toNat / 2 := by
      change (curw >>> (1 : Nat)).toNat = curw.toNat / 2
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have hhalf_lt63 : (curw >>> 1#64).toNat < 2 ^ 63 := by omega
    have hvh : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        (.shift .lsr (.var .local (ofString "cur")) (.const 1#64)) = some (.val (.word (curw >>> 1#64))) := by
      simp [evalHOLExact, toExact, ht_cur, wordShiftHOL]
    let th := setVarHOLFinite (ofString "half") (.val (.word (curw >>> 1#64))) t
    have hvj0 : @evalHOLExact 64 F _ th.toExact (fun a => Classical.propDecidable (th.memaddrs a))
        (.const 0#64) = some (.val (.word 0#64)) := rfl
    let tj := setVarHOLFinite (ofString "j") (.val (.word 0#64)) th
    have heff_tj : WorldEff s0 tj Rl sszBufs hpGw := (heff_t.locals_clock _ _).locals_clock _ _
    let InvJ2 : PanSemStateFiniteExact 64 F → Prop := fun st =>
      st.locals.lookup (ofString "buf") = some (.val (.word bufw)) ∧
      st.locals.lookup (ofString "dn") = some (.val (.word dn)) ∧
      st.locals.lookup (ofString "target") = some (.val (.word targetw)) ∧
      st.locals.lookup (ofString "out") = some (.val (.word outw)) ∧
      st.locals.lookup (ofString "mark") = some (.val (.word markw)) ∧
      st.locals.lookup (ofString "cur") = some (.val (.word curw)) ∧
      st.locals.lookup (ofString "half") = some (.val (.word (curw >>> 1#64))) ∧
      ∃ jw : BitVec 64, st.locals.lookup (ofString "j") = some (.val (.word jw)) ∧ jw.toNat ≤ (curw >>> 1#64).toNat
    have hInvJ2_tj : InvJ2 tj := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, 0#64, ?_, Nat.zero_le _⟩ <;>
        simp [tj, th, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          ht_buf, ht_dn, ht_tw, ht_out, ht_mark, ht_cur,
          show ofString "j" ≠ ofString "buf" by decide,
          show ofString "half" ≠ ofString "buf" by decide,
          show ofString "j" ≠ ofString "dn" by decide,
          show ofString "half" ≠ ofString "dn" by decide,
          show ofString "j" ≠ ofString "target" by decide,
          show ofString "half" ≠ ofString "target" by decide,
          show ofString "j" ≠ ofString "out" by decide,
          show ofString "half" ≠ ofString "out" by decide,
          show ofString "j" ≠ ofString "mark" by decide,
          show ofString "half" ≠ ofString "mark" by decide,
          show ofString "j" ≠ ofString "cur" by decide,
          show ofString "half" ≠ ofString "cur" by decide,
          show ofString "j" ≠ ofString "half" by decide]
    have hstepJ : ∀ u (cw : BitVec 64),
        @evalHOLFinite 64 F _ u (fun a => Classical.propDecidable (u.memaddrs a))
          (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "half"))) = some (.val (.word cw)) →
        cw ≠ 0 →
        WorldEff s0 (decClockHOLFinite u) Rl sszBufs hpGw → InvJ2 (decClockHOLFinite u) →
        (evaluateHOLFiniteState (decClockHOLFinite u)
          (.seq
            (.call (some (none, none)) (ofString "sha256_pair")
              [.op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "j"), .const 64#64]],
               .op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "j"), .const 64#64], .const 32#64],
               .op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "j"), .const 32#64]]])
            (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1#64])))).1 ≠ some .timeOut →
        ContOrRes (evaluateHOLFiniteState (decClockHOLFinite u)
          (.seq
            (.call (some (none, none)) (ofString "sha256_pair")
              [.op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "j"), .const 64#64]],
               .op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "j"), .const 64#64], .const 32#64],
               .op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "j"), .const 32#64]]])
            (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1#64])))).1 →
        WorldEff s0 (evaluateHOLFiniteState (decClockHOLFinite u)
          (.seq
            (.call (some (none, none)) (ofString "sha256_pair")
              [.op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "j"), .const 64#64]],
               .op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "j"), .const 64#64], .const 32#64],
               .op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "j"), .const 32#64]]])
            (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1#64])))).2 Rl sszBufs hpGw ∧
        (((evaluateHOLFiniteState (decClockHOLFinite u)
            (.seq
              (.call (some (none, none)) (ofString "sha256_pair")
                [.op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "j"), .const 64#64]],
                 .op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "j"), .const 64#64], .const 32#64],
                 .op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "j"), .const 32#64]]])
              (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1#64])))).1 = none ∨
          (evaluateHOLFiniteState (decClockHOLFinite u)
            (.seq
              (.call (some (none, none)) (ofString "sha256_pair")
                [.op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "j"), .const 64#64]],
                 .op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "j"), .const 64#64], .const 32#64],
                 .op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "j"), .const 32#64]]])
              (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1#64])))).1 = some .continue) →
          InvJ2 (evaluateHOLFiniteState (decClockHOLFinite u)
            (.seq
              (.call (some (none, none)) (ofString "sha256_pair")
                [.op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "j"), .const 64#64]],
                 .op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "j"), .const 64#64], .const 32#64],
                 .op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "j"), .const 32#64]]])
              (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1#64])))).2) := by
      intro u cw hcw hcw_ne heff_ud ⟨hu_buf, hu_dn, hu_tw, hu_out, hu_mark, hu_cur, hu_half, jw, hu_j, hj_le⟩ hnt_uj hcr_uj
      let ud := decClockHOLFinite u
      have hu_j0 : u.locals.lookup (ofString "j") = some (.val (.word jw)) := hu_j
      have hu_h0 : u.locals.lookup (ofString "half") = some (.val (.word (curw >>> 1#64))) := hu_half
      have hj_lt63 : jw.toNat < 2 ^ 63 := by omega
      have hj_lt : jw.toNat < (curw >>> 1#64).toNat := by
        rw [evalHOLFinite_eq_toExact] at hcw
        simp only [evalHOLExact, toExact, hu_j0, hu_h0, Compiler.Encoders.Asm.wordCmpHOL,
          holAsmSignedLess_small jw (curw >>> 1#64) hj_lt63 hhalf_lt63] at hcw
        by_cases hlt : jw.toNat < (curw >>> 1#64).toNat
        · exact hlt
        · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte] at hcw
          injection hcw with hcw1; injection hcw1 with hcw2; injection hcw2 with hcw3
          exact absurd hcw3.symm hcw_ne
      have hj32_lt : jw.toNat * (32#64 : BitVec 64).toNat < 2 ^ 64 := by
        rw [show (32#64 : BitVec 64).toNat = 32 from rfl]; omega
      have hj32_nat : (jw * 32#64).toNat = jw.toNat * 32 := by
        rw [BitVec.toNat_mul, show (32#64 : BitVec 64).toNat = 32 from rfl]
        exact Nat.mod_eq_of_lt hj32_lt
      have hdst_add : (bufw + jw * 32#64).toNat = bufw.toNat + jw.toNat * 32 := by
        rw [BitVec.toNat_add_of_lt (by omega), hj32_nat]
      have hud_buf : ud.locals.lookup (ofString "buf") = some (.val (.word bufw)) := hu_buf
      have hud_j : ud.locals.lookup (ofString "j") = some (.val (.word jw)) := hu_j
      have hwe_uj : WorldEff s0 (evaluateHOLFiniteState ud _).2 Rl sszBufs hpGw :=
        worldEff_seq hnt_uj hcr_uj
          (fun hnt_sp hcr_sp =>
            worldEff_call0_funByteEff heff_ud funByteEff_sha256_pair _
              [((bufw + jw * 32#64).toNat, 32)]
              (fun vals hargs i hi _ => by
                have hlast : @evalHOLExact 64 F _ ud.toExact (fun a => Classical.propDecidable (ud.memaddrs a))
                    (.op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "j"), .const 32#64]]) =
                    some (.val (.word (bufw + jw * 32#64))) := by
                  simp [evalHOLExact, evalListHOLExact, toExact, hud_buf, hud_j,
                    valueIsWord, valueWord, panOpHOL, hj32_lt, wordOpHOL, wordOp]
                obtain ⟨v0, v1, rfl⟩ := evalList3_last_word hlast hargs
                simp only [valWordNat, List.mem_singleton] at hi; subst hi
                exact ⟨((bufw + jw * 32#64).toNat, 32), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
              (fun iv hiv _ => by
                simp only [List.mem_singleton] at hiv; subst hiv
                exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
              hnt_sp hcr_sp)
          (fun m_sp _ heff_sp _ _ => worldEff_assign_local heff_sp _ _)
      refine ⟨hwe_uj, fun hfl_uj => ?_⟩
      have hnc_sp := call0_ne_continue ud (ofString "sha256_pair")
        [.op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "j"), .const 64#64]],
         .op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "j"), .const 64#64], .const 32#64],
         .op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "j"), .const 32#64]]]
      rw [evaluateHOLFiniteState_seq_line780] at hfl_uj ⊢
      rcases hsp : evaluateHOLFiniteState ud _ with ⟨rsp, m_sp⟩
      rw [hsp] at hfl_uj hnc_sp
      cases rsp with
      | some r =>
        rcases hfl_uj with h | h
        · simp at h
        · exact absurd h hnc_sp
      | none =>
        dsimp only at hfl_uj ⊢
        have hmsp_loc : m_sp.locals = ud.locals := by
          have := call0_none_locals ud (ofString "sha256_pair") _ (by rw [hsp])
          rwa [hsp] at this
        have hmsp_j : m_sp.locals.lookup (ofString "j") = some (.val (.word jw)) := by
          rw [hmsp_loc]; exact hud_j
        rw [evaluateHOLFiniteState_assign] at hfl_uj ⊢
        have hj1_ev : @evalHOLExact 64 F _ m_sp.toExact (fun a => Classical.propDecidable (m_sp.memaddrs a))
            (.op .add [.var .local (ofString "j"), .const 1#64]) = some (.val (.word (jw + 1#64))) := by
          simp [evalHOLExact, evalListHOLExact, toExact, hmsp_j,
            valueIsWord, valueWord, wordOpHOL, wordOp]
        have hvv : isValidValueHOLFinite m_sp .local (ofString "j") (.val (.word (jw + 1#64))) = true := by
          simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, toExact, hmsp_j,
            shapeOfHOLExact, shapeEqHOL]
        simp only [hj1_ev, hvv, ↓reduceIte]
        have hj1_nat : (jw + 1#64).toNat = jw.toNat + 1 := by
          have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
          rw [BitVec.toNat_add_of_lt (by omega), h1]
        have hud_buf' : ud.locals.lookup (ofString "buf") = some (.val (.word bufw)) := hu_buf
        have hud_dn' : ud.locals.lookup (ofString "dn") = some (.val (.word dn)) := hu_dn
        have hud_tw' : ud.locals.lookup (ofString "target") = some (.val (.word targetw)) := hu_tw
        have hud_out' : ud.locals.lookup (ofString "out") = some (.val (.word outw)) := hu_out
        have hud_mark' : ud.locals.lookup (ofString "mark") = some (.val (.word markw)) := hu_mark
        have hud_cur' : ud.locals.lookup (ofString "cur") = some (.val (.word curw)) := hu_cur
        have hud_half' : ud.locals.lookup (ofString "half") = some (.val (.word (curw >>> 1#64))) := hu_half
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, jw + 1#64, ?_, by omega⟩ <;>
          simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            hmsp_loc, hud_buf', hud_dn', hud_tw', hud_out', hud_mark', hud_cur', hud_half',
            show ofString "j" ≠ ofString "buf" by decide,
            show ofString "j" ≠ ofString "dn" by decide,
            show ofString "j" ≠ ofString "target" by decide,
            show ofString "j" ≠ ofString "out" by decide,
            show ofString "j" ≠ ofString "mark" by decide,
            show ofString "j" ≠ ofString "cur" by decide,
            show ofString "j" ≠ ofString "half" by decide]
    let innerProg : ProgHOL 64 :=
      .seq
        (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "half")))
          (.seq
            (.call (some (none, none)) (ofString "sha256_pair")
              [.op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "j"), .const 64#64]],
               .op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "j"), .const 64#64], .const 32#64],
               .op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "j"), .const 32#64]]])
            (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1#64]))))
        (.assign .local (ofString "cur") (.var .local (ofString "half")))
    have hbody1_eval : evaluateHOLFiniteState t body1Prog =
        ((evaluateHOLFiniteState tj innerProg).1,
         { (evaluateHOLFiniteState tj innerProg).2 with
           locals := HolFiniteMapExact.resVarEq
             (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState tj innerProg).2.locals
               (ofString "j", th.locals.lookup (ofString "j")))
             (ofString "half", t.locals.lookup (ofString "half")) }) := by
      dsimp only [body1Prog]
      rw [evaluateHOLFiniteState_dec_total]
      simp only [hvh, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
      have hth_eval : evaluateHOLFiniteState th (.dec (ofString "j") .one (.const 0#64) innerProg) =
          ((evaluateHOLFiniteState tj innerProg).1,
           { (evaluateHOLFiniteState tj innerProg).2 with
             locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState tj innerProg).2.locals
               (ofString "j", th.locals.lookup (ofString "j")) }) := by
        rw [evaluateHOLFiniteState_dec_total]
        simp only [hvj0, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
        rfl
      change (let r := evaluateHOLFiniteState th (.dec (ofString "j") .one (.const 0#64) innerProg);
        (r.1, { r.2 with locals := HolFiniteMapExact.resVarEq r.2.locals (ofString "half", t.locals.lookup (ofString "half")) })) = _
      rw [hth_eval]
    have hnt_in : (evaluateHOLFiniteState tj innerProg).1 ≠ some .timeOut := by
      rw [hbody1_eval] at hnt_b1; exact hnt_b1
    have hcr_in : ContOrRes (evaluateHOLFiniteState tj innerProg).1 := by
      rw [hbody1_eval] at hcr_b1; exact hcr_b1
    have hwe_in : WorldEff s0 (evaluateHOLFiniteState tj innerProg).2 Rl sszBufs hpGw :=
      worldEff_seq hnt_in hcr_in
        (fun hnt_wj hcr_wj =>
          (worldEff_while_cond_post (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "half")))
            InvJ2 (fun u hu => hu) hstepJ tj.clock tj rfl heff_tj hInvJ2_tj hnt_wj hcr_wj).1)
        (fun m_ja _ heff_ja _ _ => worldEff_assign_local heff_ja _ _)
    have hwe_b1 : WorldEff s0 (evaluateHOLFiniteState t body1Prog).2 Rl sszBufs hpGw := by
      rw [hbody1_eval]
      exact hwe_in.locals_clock _ _
    refine ⟨hwe_b1, fun hfl_b1 => ?_⟩
    rw [hbody1_eval] at hfl_b1 ⊢
    dsimp only [innerProg] at hfl_b1 hnt_in ⊢
    rw [evaluateHOLFiniteState_seq_line780] at hfl_b1 hnt_in ⊢
    have hnc_wj := while_ne_continue tj
      (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "half")))
      (.seq
        (.call (some (none, none)) (ofString "sha256_pair")
          [.op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "j"), .const 64#64]],
           .op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "j"), .const 64#64], .const 32#64],
           .op .add [.var .local (ofString "buf"), .panop .mul [.var .local (ofString "j"), .const 32#64]]])
        (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1#64])))
    rcases hwj : evaluateHOLFiniteState tj _ with ⟨rwj, m_ja⟩
    rw [hwj] at hfl_b1 hnt_in hnc_wj
    cases rwj with
    | some r =>
      rcases hfl_b1 with h | h
      · simp at h
      · exact absurd h hnc_wj
    | none =>
      dsimp only at hfl_b1 ⊢
      have hwj_post := (worldEff_while_cond_post (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "half")))
        InvJ2 (fun u hu => hu) hstepJ tj.clock tj rfl heff_tj hInvJ2_tj
        (by rw [hwj]; simp) (by rw [hwj]; exact Or.inl rfl)).2 (by rw [hwj])
        (fun u _ => seq_ne_break u (call0_ne_break u _ _) (fun mid _ => assign_local_ne_break mid _ _))
      rw [hwj] at hwj_post; dsimp only at hwj_post
      obtain ⟨⟨hja_buf, hja_dn, hja_tw, hja_out, hja_mark, hja_cur, hja_half, _⟩, _⟩ := hwj_post
      rw [evaluateHOLFiniteState_assign] at hfl_b1 ⊢
      have hhalf_ev : @evalHOLExact 64 F _ m_ja.toExact (fun a => Classical.propDecidable (m_ja.memaddrs a))
          (.var .local (ofString "half")) = some (.val (.word (curw >>> 1#64))) := by
        simp [evalHOLExact, toExact, hja_half]
      have hvv_cur : isValidValueHOLFinite m_ja .local (ofString "cur") (.val (.word (curw >>> 1#64))) = true := by
        simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, toExact, hja_cur,
          shapeOfHOLExact, shapeEqHOL]
      simp only [hhalf_ev, hvv_cur, ↓reduceIte]
      refine ⟨?_, ?_, ?_, ?_, ?_, curw >>> 1#64, ?_, by omega⟩ <;>
        simp [PanRunBounded.resVarEq_lookup, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          hja_buf, hja_dn, hja_tw, hja_out, hja_mark,
          show ofString "buf" ≠ ofString "half" by decide,
          show ofString "buf" ≠ ofString "j" by decide,
          show ofString "dn" ≠ ofString "half" by decide,
          show ofString "dn" ≠ ofString "j" by decide,
          show ofString "target" ≠ ofString "half" by decide,
          show ofString "target" ≠ ofString "j" by decide,
          show ofString "out" ≠ ofString "half" by decide,
          show ofString "out" ≠ ofString "j" by decide,
          show ofString "mark" ≠ ofString "half" by decide,
          show ofString "mark" ≠ ofString "j" by decide,
          show ofString "cur" ≠ ofString "half" by decide,
          show ofString "cur" ≠ ofString "j" by decide,
          show ofString "cur" ≠ ofString "buf" by decide,
          show ofString "cur" ≠ ofString "dn" by decide,
          show ofString "cur" ≠ ofString "target" by decide,
          show ofString "cur" ≠ ofString "out" by decide,
          show ofString "cur" ≠ ofString "mark" by decide]
  -- Sequence outer halving loop with trailing loop + memcpy + heap_release + return 0
  refine worldEff_seq hnt10 hcr10
    (fun hnt_w1 hcr_w1 =>
      (worldEff_while_cond_post (.cmp .less (.const 1#64) (.var .local (ofString "cur")))
        Inv1 (fun u hu => hu)
        (fun u _ _ _ heff_ud hinv_ud hnt_ud hcr_ud => hbody1 (decClockHOLFinite u) heff_ud hinv_ud hnt_ud hcr_ud)
        m9.clock m9 rfl heff_m9 hInv1_m9 hnt_w1 hcr_w1).1)
    (fun m10 hm10 heff_m10 hnt11 hcr11 => ?_)
  have hInv1_m10 : Inv1 m10 := by
    have hp := (worldEff_while_cond_post (.cmp .less (.const 1#64) (.var .local (ofString "cur")))
      Inv1 (fun u hu => hu)
      (fun u _ _ _ heff_ud hinv_ud hnt_ud hcr_ud => hbody1 (decClockHOLFinite u) heff_ud hinv_ud hnt_ud hcr_ud)
      m9.clock m9 rfl heff_m9 hInv1_m9
      (by rw [hm10]; simp) (by rw [hm10]; exact Or.inl rfl)).2 (by rw [hm10])
      (fun u ⟨_, _, _, _, _, curu, hu_cur, _⟩ => by
        dsimp only [body1Prog]
        exact dec_word_ne_break u (ofString "half") _ (curu >>> 1#64)
          (by simp [evalHOLExact, toExact, hu_cur, wordShiftHOL])
          (dec_word_ne_break _ (ofString "j") (.const 0#64) 0#64 rfl
            (seq_ne_break _ (while_ne_break _ _ _) (fun mid _ => assign_local_ne_break mid _ _))))
    rw [hm10] at hp; exact hp.1
  obtain ⟨hm10_buf, hm10_dn, hm10_tw, hm10_out, hm10_mark, _⟩ := hInv1_m10
  -- `dec d := dn`
  refine worldEff_dec heff_m10 (ofString "d") .one _ hnt11 hcr11
    (fun vd hvd hvsh11 hnt12 hcr12 => ?_)
  rcases vd with ⟨⟨dw0⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hvsh11)
  have hdw0_eq : dn = dw0 := by simp [evalHOLExact, toExact, hm10_dn] at hvd; exact hvd
  subst hdw0_eq
  let m11 := setVarHOLFinite (ofString "d") (.val (.word dn)) m10
  have heff_m11 : WorldEff s0 m11 Rl sszBufs hpGw := heff_m10.locals_clock _ _
  let InvD : PanSemStateFiniteExact 64 F → Prop := fun st =>
    st.locals.lookup (ofString "buf") = some (.val (.word bufw)) ∧
    st.locals.lookup (ofString "out") = some (.val (.word outw)) ∧
    st.locals.lookup (ofString "mark") = some (.val (.word markw)) ∧
    ∃ dw : BitVec 64, st.locals.lookup (ofString "d") = some (.val (.word dw))
  have hInvD_m11 : InvD m11 := by
    refine ⟨?_, ?_, ?_, dn, ?_⟩ <;>
      simp [m11, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        hm10_buf, hm10_out, hm10_mark,
        show ofString "d" ≠ ofString "buf" by decide,
        show ofString "d" ≠ ofString "out" by decide,
        show ofString "d" ≠ ofString "mark" by decide]
  have hstepD : ∀ u (cw : BitVec 64),
      @evalHOLFinite 64 F _ u (fun a => Classical.propDecidable (u.memaddrs a))
        (.cmp .less (.var .local (ofString "d")) (.var .local (ofString "target"))) = some (.val (.word cw)) →
      cw ≠ 0 →
      WorldEff s0 (decClockHOLFinite u) Rl sszBufs hpGw → InvD (decClockHOLFinite u) →
      (evaluateHOLFiniteState (decClockHOLFinite u)
        (.seq
          (.call (some (none, none)) (ofString "sha256_pair")
            [.var .local (ofString "buf"),
             .op .add [.var .global (ofString "zero_hashes"), .panop .mul [.var .local (ofString "d"), .const 32#64]],
             .var .local (ofString "buf")])
          (.assign .local (ofString "d") (.op .add [.var .local (ofString "d"), .const 1#64])))).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState (decClockHOLFinite u)
        (.seq
          (.call (some (none, none)) (ofString "sha256_pair")
            [.var .local (ofString "buf"),
             .op .add [.var .global (ofString "zero_hashes"), .panop .mul [.var .local (ofString "d"), .const 32#64]],
             .var .local (ofString "buf")])
          (.assign .local (ofString "d") (.op .add [.var .local (ofString "d"), .const 1#64])))).1 →
      WorldEff s0 (evaluateHOLFiniteState (decClockHOLFinite u)
        (.seq
          (.call (some (none, none)) (ofString "sha256_pair")
            [.var .local (ofString "buf"),
             .op .add [.var .global (ofString "zero_hashes"), .panop .mul [.var .local (ofString "d"), .const 32#64]],
             .var .local (ofString "buf")])
          (.assign .local (ofString "d") (.op .add [.var .local (ofString "d"), .const 1#64])))).2 Rl sszBufs hpGw ∧
      (((evaluateHOLFiniteState (decClockHOLFinite u)
          (.seq
            (.call (some (none, none)) (ofString "sha256_pair")
              [.var .local (ofString "buf"),
               .op .add [.var .global (ofString "zero_hashes"), .panop .mul [.var .local (ofString "d"), .const 32#64]],
               .var .local (ofString "buf")])
            (.assign .local (ofString "d") (.op .add [.var .local (ofString "d"), .const 1#64])))).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite u)
          (.seq
            (.call (some (none, none)) (ofString "sha256_pair")
              [.var .local (ofString "buf"),
               .op .add [.var .global (ofString "zero_hashes"), .panop .mul [.var .local (ofString "d"), .const 32#64]],
               .var .local (ofString "buf")])
            (.assign .local (ofString "d") (.op .add [.var .local (ofString "d"), .const 1#64])))).1 = some .continue) →
        InvD (evaluateHOLFiniteState (decClockHOLFinite u)
          (.seq
            (.call (some (none, none)) (ofString "sha256_pair")
              [.var .local (ofString "buf"),
               .op .add [.var .global (ofString "zero_hashes"), .panop .mul [.var .local (ofString "d"), .const 32#64]],
               .var .local (ofString "buf")])
            (.assign .local (ofString "d") (.op .add [.var .local (ofString "d"), .const 1#64])))).2) := by
    intro u _ _ _ heff_ud ⟨hu_buf, hu_out, hu_mark, dw, hu_d⟩ hnt_ud hcr_ud
    let ud := decClockHOLFinite u
    have hud_buf : ud.locals.lookup (ofString "buf") = some (.val (.word bufw)) := hu_buf
    have hud_d : ud.locals.lookup (ofString "d") = some (.val (.word dw)) := hu_d
    have hwe_ud : WorldEff s0 (evaluateHOLFiniteState ud _).2 Rl sszBufs hpGw :=
      worldEff_seq hnt_ud hcr_ud
        (fun hnt_sp hcr_sp =>
          worldEff_call0_funByteEff heff_ud funByteEff_sha256_pair _
            [(bufw.toNat, 32)]
            (fun vals hargs i hi _ => by
              have hlast : @evalHOLExact 64 F _ ud.toExact (fun a => Classical.propDecidable (ud.memaddrs a))
                  (.var .local (ofString "buf")) = some (.val (.word bufw)) := by
                simp [evalHOLExact, toExact, hud_buf]
              obtain ⟨v0, v1, rfl⟩ := evalList3_last_word hlast hargs
              simp only [valWordNat, List.mem_singleton] at hi; subst hi
              exact ⟨(bufw.toNat, 32), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
            (fun iv hiv _ => by
              simp only [List.mem_singleton] at hiv; subst hiv
              exact Or.inr (Or.inr (Or.inr ⟨hbuf_lo, hbuf_32⟩)))
            hnt_sp hcr_sp)
        (fun m_sp _ heff_sp _ _ => worldEff_assign_local heff_sp _ _)
    refine ⟨hwe_ud, fun hfl_ud => ?_⟩
    have hnc_sp := call0_ne_continue ud (ofString "sha256_pair")
      [.var .local (ofString "buf"),
       .op .add [.var .global (ofString "zero_hashes"), .panop .mul [.var .local (ofString "d"), .const 32#64]],
       .var .local (ofString "buf")]
    rw [evaluateHOLFiniteState_seq_line780] at hfl_ud ⊢
    rcases hsp : evaluateHOLFiniteState ud _ with ⟨rsp, m_sp⟩
    rw [hsp] at hfl_ud hnc_sp
    cases rsp with
    | some r =>
      rcases hfl_ud with h | h
      · simp at h
      · exact absurd h hnc_sp
    | none =>
      dsimp only at hfl_ud ⊢
      have hmsp_loc : m_sp.locals = ud.locals := by
        have := call0_none_locals ud (ofString "sha256_pair") _ (by rw [hsp])
        rwa [hsp] at this
      have hmsp_d : m_sp.locals.lookup (ofString "d") = some (.val (.word dw)) := by
        rw [hmsp_loc]; exact hud_d
      rw [evaluateHOLFiniteState_assign] at hfl_ud ⊢
      have hd1_ev : @evalHOLExact 64 F _ m_sp.toExact (fun a => Classical.propDecidable (m_sp.memaddrs a))
          (.op .add [.var .local (ofString "d"), .const 1#64]) = some (.val (.word (dw + 1#64))) := by
        simp [evalHOLExact, evalListHOLExact, toExact, hmsp_d,
          valueIsWord, valueWord, wordOpHOL, wordOp]
      have hvv_d : isValidValueHOLFinite m_sp .local (ofString "d") (.val (.word (dw + 1#64))) = true := by
        simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, toExact, hmsp_d,
          shapeOfHOLExact, shapeEqHOL]
      simp only [hd1_ev, hvv_d, ↓reduceIte]
      have hud_out : ud.locals.lookup (ofString "out") = some (.val (.word outw)) := hu_out
      have hud_mark : ud.locals.lookup (ofString "mark") = some (.val (.word markw)) := hu_mark
      refine ⟨?_, ?_, ?_, dw + 1#64, ?_⟩ <;>
        simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          hmsp_loc, hud_buf, hud_out, hud_mark,
          show ofString "d" ≠ ofString "buf" by decide,
          show ofString "d" ≠ ofString "out" by decide,
          show ofString "d" ≠ ofString "mark" by decide]
  refine worldEff_seq hnt12 hcr12
    (fun hnt_wd hcr_wd =>
      (worldEff_while_cond_post (.cmp .less (.var .local (ofString "d")) (.var .local (ofString "target")))
        InvD (fun u hu => hu) hstepD m11.clock m11 rfl heff_m11 hInvD_m11 hnt_wd hcr_wd).1)
    (fun m12 hm12 heff_m12 hnt13 hcr13 => ?_)
  have hInvD_m12 : InvD m12 := by
    have hp := (worldEff_while_cond_post (.cmp .less (.var .local (ofString "d")) (.var .local (ofString "target")))
      InvD (fun u hu => hu) hstepD m11.clock m11 rfl heff_m11 hInvD_m11
      (by rw [hm12]; simp) (by rw [hm12]; exact Or.inl rfl)).2 (by rw [hm12])
      (fun u _ => seq_ne_break u (call0_ne_break u _ _) (fun mid _ => assign_local_ne_break mid _ _))
    rw [hm12] at hp; exact hp.1
  obtain ⟨hm12_buf, hm12_out, hm12_mark, _⟩ := hInvD_m12
  -- `memcpy(out, buf, 32); heap_release(mark); return 0`
  refine worldEff_seq hnt13 hcr13
    (fun hnt_cp2 hcr_cp2 =>
      (worldEff_call0_memcpy_word heff_m12
        (.var .local (ofString "out")) (.var .local (ofString "buf")) (.const 32#64) outw 32#64
        (by simp [evalHOLExact, toExact, hm12_out])
        rfl
        (fun _ _ => outIvlCovered_to_world hout_cov 32 le_rfl)
        hnt_cp2 hcr_cp2).1)
    (fun m13 hm13 heff_m13 hnt14 hcr14 => ?_)
  have hm13_loc : m13.locals = m12.locals := by
    have := call0_none_locals m12 (ofString "memcpy") _ (by rw [hm13])
    rwa [hm13] at this
  refine worldEff_seq hnt14 hcr14
    (fun hnt_hr hcr_hr =>
      (worldEff_call0_heap_release hAs0 heff_m13 (by decide) hp_no_gb
        (.var .local (ofString "mark")) markw
        (by simp [evalHOLExact, toExact, hm13_loc, hm12_mark])
        hmark_lo hmark_hi hmark_al hnt_hr).2.choose_spec.2)
    (fun m14 _ heff_m14 _ _ => worldEff_return heff_m14 _)

private theorem worldEff_call0_merkleize {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hAs0 : ArenaOK s0) (heff : WorldEff s0 cur Rl sszBufs hpGw)
    (pExp nExp limitExp outExp : ExpHOL 64) (nw outw : BitVec 64)
    (hn : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      nExp = some (.val (.word nw)))
    (hn_bound : nw.toNat < 2 ^ 35)
    (hout : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      outExp = some (.val (.word outw)))
    (hcov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "merkleize")
      [pExp, nExp, limitExp, outExp])).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "merkleize")
      [pExp, nExp, limitExp, outExp])).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "merkleize")
      [pExp, nExp, limitExp, outExp])).2 Rl sszBufs hpGw := by
  refine worldEff_call0_eff heff (ofString "merkleize") [pExp, nExp, limitExp, outExp]
    _ _ _ lookup_merkleize (fun callee vals hargs hl hnt_e hres_e => ?_) hnt hcr
  rw [heff.code] at hl
  obtain ⟨pw, nw', lw, ow, rfl, hp, hn', hlim, ho⟩ :=
    lookupCode_four_words (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) lookup_merkleize hl
  have how : ow = outw := by
    obtain ⟨preVals, hv⟩ := evalList_last_word (pre := [pExp, nExp, limitExp]) hout hargs
    have ht := congrArg List.getLast? hv
    simpa using ht
  have hnw : nw' = nw := by
    rw [evalListHOLFinite_eq_toExact] at hargs
    simp only [evalListHOLExact, hn] at hargs
    cases hpe : @evalHOLExact 64 F _ cur.toExact
        (fun a => Classical.propDecidable (cur.memaddrs a)) pExp with
    | none => simp [hpe] at hargs
    | some pv =>
      cases hle : @evalHOLExact 64 F _ cur.toExact
          (fun a => Classical.propDecidable (cur.memaddrs a)) limitExp with
      | none => simp [hpe, hle] at hargs
      | some lv =>
        simp [hpe, hle, hout] at hargs
        exact hargs.2.1.symm
  subst hnw how
  exact worldEff_merkleize s0 (callEntryStateHOLFinite cur callee) hAs0
    (heff.locals_clock _ _) hn' hn_bound ho hcov hnt_e hres_e

private theorem worldEff_call0_htr_u64_at {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (heff : WorldEff s0 cur Rl sszBufs hpGw)
    (pExp outExp : ExpHOL 64) (outw : BitVec 64)
    (hout : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      outExp = some (.val (.word outw)))
    (hcov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_u64_at")
      [pExp, outExp])).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_u64_at")
      [pExp, outExp])).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_u64_at")
      [pExp, outExp])).2 Rl sszBufs hpGw := by
  refine worldEff_call0_funByteEff heff funByteEff_htr_u64_at [pExp, outExp]
    [(outw.toNat, 32)] (fun vals hargs i hi _ => ?_)
    (fun iv hiv _ => ?_) hnt hcr
  · rw [evalListHOLFinite_eq_toExact] at hargs
    simp only [evalListHOLExact, hout] at hargs
    cases hp : @evalHOLExact 64 F _ cur.toExact
        (fun a => Classical.propDecidable (cur.memaddrs a)) pExp with
    | none => simp [hp] at hargs
    | some pv =>
      simp only [hp] at hargs
      injection hargs with hv
      subst vals
      simp [valWordNat] at hi
      subst i
      exact ⟨(outw.toNat, 32), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩
  · simp only [List.mem_singleton] at hiv
    subst iv
    exact outIvlCovered_to_world hcov 32 le_rfl

private theorem call0_never_returned {F : Type}
    (s : PanSemStateFiniteExact 64 F) (f : MlS) (args : List (ExpHOL 64)) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s (.call (some (none, none)) f args)).1 ≠ some (.returned v) := by
  rw [evaluateHOLFiniteState_call]
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s _) _ with ⟨r, _⟩
        rcases r with _ | (_ | _ | _ | _ | _ | _ | _) <;> dsimp only <;> (repeat' split) <;> simp

private theorem pack_bytes_ret {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (heff_cur : WorldEff s0 cur Rl sszBufs hpGw)
    (nw : BitVec 64)
    (hn : cur.locals.lookup (ofString "n") = some (.val (.word nw)))
    (rv : ValueHOL 64)
    (hret : (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_pack_bytes)).1 =
      some (.returned rv)) :
    ∃ bufw : BitVec 64,
      rv = .rStruct [.val (.word bufw), .val (.word ((nw + 31#64) >>> 5#64))] ∧
      ((nw + 31#64) >>> 5#64).toNat < 2 ^ 35 := by
  have hhe_val : heapEnd < 2 ^ 36 := by rw [heapEnd_val]; decide
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_pack_bytes,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hret
  rw [evaluateHOLFiniteState_dec_total] at hret
  have hcnt_ev : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      (.shift .lsr (.op .add [.var .local (ofString "n"), .const 31#64]) (.const 5#64)) =
      some (.val (.word ((nw + 31#64) >>> 5#64))) := by
    simp [evalHOLExact, evalListHOLExact, toExact, hn, valueIsWord, valueWord, wordOpHOL, wordOp, wordShiftHOL]
  have hsh1 : shapeEqHOL (shapeOfHOLExact (.val (.word ((nw + 31#64) >>> 5#64)) : ValueHOL 64)) .one = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  simp only [hcnt_ev, shapeOfHOLExact, shapeEqHOL, Bool.true_eq, ↓reduceIte] at hret
  let countw := (nw + 31#64) >>> 5#64
  let m1 := setVarHOLFinite (ofString "count") (.val (.word countw)) cur
  have heff_m1 : WorldEff s0 m1 Rl sszBufs hpGw := heff_cur.locals_clock _ _
  have hm1_n : m1.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    simp [m1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
      show ofString "count" ≠ ofString "n" by decide]
  change (evaluateHOLFiniteState m1 _).1 = some (PanSemResultExact.returned rv) at hret
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
  rcases hargs : evalListHOLFinite m1 (h := fun a => Classical.propDecidable (m1.memaddrs a)) _ with _ | vals
  · rw [hargs] at hret; simp at hret
  · simp only [hargs] at hret
    rcases hl : lookupCodeHOLFinite m1.code.lookup (ofString "alloc") vals with _ | ⟨ab, ac, ar⟩
    · rw [hl] at hret; simp at hret
    · simp only [hl] at hret
      split at hret
      · simp at hret
      · rename_i hcz
        have hsame := lookupCodeHOLFinite_installed_body m1.code.lookup (ofString "alloc") _ _ ab
          _ ar vals ac (by rw [heff_m1.code]; exact lookup_alloc) hl
        subst hsame
        have hret_eq := lookupCodeHOLFinite_installed_return m1 (ofString "alloc") _ _ _
          _ ar vals ac (by rw [heff_m1.code]; exact lookup_alloc) hl
        subst hret_eq
        obtain ⟨szw, rfl, hsz_ac⟩ := lookupCode_one_word lookup_alloc (by rwa [← heff_m1.code])
        obtain ⟨pw, hpw_lk⟩ : ∃ pw : BitVec 64, m1.globals.lookup (ofString "heap_ptr") = some (.val (.word pw)) :=
          globalWord_of_globN_pos m1 "heap_ptr" (by have := heff_m1.arena.2.1; rw [sourceBase_val] at this; omega)
        rcases ha : evaluateHOLFiniteState (callEntryStateHOLFinite m1 ac) (sourceFnBody Guest.Software.guestFn_alloc) with ⟨ra, pa⟩
        rw [ha] at hret
        cases ra with
        | none => simp at hret
        | some ra1 =>
          cases ra1 with
          | returned av =>
            have hal := InitECandidate.Solver.Wave8GuestInv.R13.alloc_body_resumes
              (callEntryStateHOLFinite m1 ac) pw heff_m1.code hpw_lk
              (by rw [ha]; exact Or.inl ⟨av, rfl⟩)
            rw [ha] at hal
            obtain ⟨szw', hsz_ac', hav_eq, hcmp1, hcmp2, hpa_eq⟩ := hal
            dsimp only at hav_eq hpa_eq
            have hsz_eq_ac : szw = szw' := by
              have : (callEntryStateHOLFinite m1 ac).locals.lookup (ofString "n") = some (.val (.word szw)) := hsz_ac
              rw [this] at hsz_ac'; injection hsz_ac' with h1; injection h1 with h1; injection h1
            subst hsz_eq_ac
            injection hav_eq with hav_eq'; injection hav_eq' with hav_eq''; subst hav_eq''
            dsimp only at hret
            simp only [shapeOfHOLExact, shapeEqHOL, Bool.and_self, Bool.true_eq, ↓reduceIte] at hret
            let m2 := setVarHOLFinite (ofString "buf") (.val (.word pw)) { pa with locals := m1.locals }
            have hm2_next : m2 = { m1 with
                globals := m1.globals.update (ofString "heap_ptr", .val (.word ((pw + (szw + 7)) &&& ((0 : BitVec 64) - 8)))),
                locals := m2.locals, clock := m2.clock } := by
              dsimp only [m2, setVarHOLFinite]; rw [hpa_eq]; rfl
            obtain ⟨heff_m2, _, _, _, hp_lo_s, hp_add, hp_hi, _⟩ :=
              worldEff_alloc_step heff_m1 (by decide) hpw_lk hcmp1 hcmp2 hm2_next
            have hm2_buf : m2.locals.lookup (ofString "buf") = some (.val (.word pw)) := by
              simp [m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have hm2_cnt : m2.locals.lookup (ofString "count") = some (.val (.word countw)) := by
              simp [m2, m1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "buf" ≠ ofString "count" by decide]
            have hm2_n : m2.locals.lookup (ofString "n") = some (.val (.word nw)) := by
              simp [m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_n,
                show ofString "buf" ≠ ofString "n" by decide]
            change (evaluateHOLFiniteState m2 _).1 = some (PanSemResultExact.returned rv) at hret
            rw [evaluateHOLFiniteState_seq_line780] at hret
            rcases hcp : evaluateHOLFiniteState m2 _ with ⟨rcp, m3⟩
            rw [hcp] at hret
            cases rcp with
            | some r =>
              cases r with
              | returned v => exact False.elim (call0_never_returned m2 _ _ v (by rw [hcp]))
              | _ => simp at hret
            | none =>
              dsimp only at hret
              have hcp_res := worldEff_call0_memcpy_word heff_m2
                (.var .local (ofString "buf")) (.var .local (ofString "p")) (.var .local (ofString "n")) pw nw
                (by simp [evalHOLExact, toExact, hm2_buf])
                (by simp [evalHOLExact, toExact, hm2_n])
                (fun hdom hpos => by
                  have hnhe : nw.toNat ≤ heapEnd := by have := (hdom hpos).2; omega
                  have hsz_ev : szw = countw * 32#64 := by
                    rw [evalListHOLFinite_eq_toExact] at hargs
                    simpa [evalListHOLExact, evalHOLExact, toExact, m1, setVarHOLFinite,
                      HolFiniteMapExact.lookup_update, FUPDATE, valueIsWord, valueWord,
                      panOpHOL] using hargs.symm
                  obtain ⟨hle_sz, _⟩ := count32_bounds nw hnhe
                  rw [← hsz_ev] at hle_sz
                  exact Or.inr (Or.inr (Or.inr ⟨hp_lo_s, by omega⟩)))
                (by rw [hcp]; simp) (by rw [hcp]; exact Or.inl rfl)
              obtain ⟨hm3_loc0, hdom, _⟩ := hcp_res.2 (by rw [hcp])
              have hm3_loc : m3.locals = m2.locals := by simpa [hcp] using hm3_loc0
              have hnhe : nw.toNat ≤ heapEnd := by
                by_cases hpos : 0 < nw.toNat
                · have := (hdom hpos).2; omega
                · omega
              rw [evaluateHOLFiniteState_seq_line780] at hret
              rcases hmz : evaluateHOLFiniteState m3 _ with ⟨rmz, m4⟩
              rw [hmz] at hret
              cases rmz with
              | some r =>
                cases r with
                | returned v => exact False.elim (call0_never_returned m3 _ _ v (by rw [hmz]))
                | _ => simp at hret
              | none =>
                dsimp only at hret
                have hm4_loc : m4.locals = m3.locals := by
                  have := call0_none_locals m3 (ofString "memzero") _ (by rw [hmz])
                  rwa [hmz] at this
                have hm4_buf : m4.locals.lookup (ofString "buf") = some (.val (.word pw)) := by
                  rw [hm4_loc, hm3_loc]; exact hm2_buf
                have hm4_cnt : m4.locals.lookup (ofString "count") = some (.val (.word countw)) := by
                  rw [hm4_loc, hm3_loc]; exact hm2_cnt
                rw [evaluateHOLFiniteState_return] at hret
                simp only [evalHOLExact, evalListHOLExact, toExact, hm4_buf, hm4_cnt, Option.map,
                  shapeOfHOLExact, Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL,
                  Flapjack.Pancake.PanLang.sizeOfShapesWithContextHOL] at hret
                split at hret
                · dsimp only at hret
                  injection hret with hret'; injection hret' with hrv
                  refine ⟨pw, hrv.symm, ?_⟩
                  have h31 : (31#64 : BitVec 64).toNat = 31 := rfl
                  have h5 : (5#64 : BitVec 64).toNat = 5 := rfl
                  change ((nw + 31#64) >>> (5#64 : BitVec 64).toNat).toNat < 2 ^ 35
                  rw [BitVec.toNat_ushiftRight, BitVec.toNat_add_of_lt (by omega), h31, h5,
                    Nat.shiftRight_eq_div_pow]
                  omega
                · simp at hret
          | _ => simp at hret

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
