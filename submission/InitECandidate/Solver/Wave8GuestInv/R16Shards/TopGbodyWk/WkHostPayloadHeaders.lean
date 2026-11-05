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
    (hn_bound : nw.toNat < 2 ^ 58)
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
  have hm1_n : m1.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hn_lk,
      show ofString "dl" ≠ ofString "n" by decide]
  have hm1_out : m1.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hout_lk,
      show ofString "dl" ≠ ofString "out" by decide]
  refine worldEff_decCall_ceil_log2 heff_m1 (ofString "dn") (.var .local (ofString "n"))
    hnt1 hcr1
    (fun nw' dn m2 hn_ev hdn_lt hn_pow hdn_min hm2_loc hm2_eq heff_m2 hnt2 hcr2 => ?_)
  have hnw_eq : nw = nw' := by simp [evalHOLExact, toExact, hm1_n] at hn_ev; exact hn_ev
  subst hnw_eq
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
  have hdn59 : dn.toNat < 59 := by
    by_contra hge
    have hd_pos : 0 < dn.toNat := by omega
    have hd1_ge : 58 ≤ dn.toNat - 1 := by omega
    have hmin := hdn_min hd_pos
    have hpow58 : 2 ^ 58 ≤ 2 ^ (dn.toNat - 1) := Nat.pow_le_pow_right (by omega) hd1_ge
    omega
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
    (hn_bound : nw.toNat < 2 ^ 58)
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
  have hnw_eq : nw' = nw ∧ ow = outw := by
    rw [evalListHOLFinite_eq_toExact] at hargs
    simp only [evalListHOLExact, hn, hout] at hargs
    rcases hp0 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) pExp with _ | vp
    · simp [hp0] at hargs
    · rcases hl0 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) limitExp with _ | vl
      · simp [hp0, hl0] at hargs
      · simp only [hp0, hl0] at hargs
        injection hargs with h0
        injection h0 with _ h1
        injection h1 with h2 h3
        injection h2 with h2'; injection h2' with h2''
        injection h3 with _ h4
        injection h4 with h4' _; injection h4' with h4''; injection h4'' with h4'''
        exact ⟨h2''.symm, h4'''.symm⟩
  obtain ⟨rfl, rfl⟩ := hnw_eq
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

private theorem worldEff_call0_mix_in_length {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (heff : WorldEff s0 cur Rl sszBufs hpGw)
    (rootExp lenExp outExp : ExpHOL 64) (outw : BitVec 64)
    (hout : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      outExp = some (.val (.word outw)))
    (hcov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "mix_in_length")
      [rootExp, lenExp, outExp])).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "mix_in_length")
      [rootExp, lenExp, outExp])).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "mix_in_length")
      [rootExp, lenExp, outExp])).2 Rl sszBufs hpGw := by
  have hgl_eq : cur.globals.lookup (ofString "ssz_len_chunk") = s0.globals.lookup (ofString "ssz_len_chunk") :=
    (heff.gw_kept (ofString "ssz_len_chunk") (by decide)).symm
  have hbuf_eq : globBufIvl cur.globals "ssz_len_chunk" 32 = bufferRegion s0 ("ssz_len_chunk", 32) := by
    unfold globBufIvl bufferRegion globMapN globN
    dsimp only
    rw [hgl_eq]
    rfl
  refine worldEff_call0_funByteEff heff funByteEff_mix_in_length [rootExp, lenExp, outExp]
    [bufferRegion s0 ("ssz_len_chunk", 32), (outw.toNat, 32)]
    (fun vals hargs i hi _ => ?_)
    (fun iv hiv _ => ?_) hnt hcr
  · obtain ⟨v0, v1, rfl⟩ := evalList3_last_word hout hargs
    rw [hbuf_eq] at hi
    have hi' : i = bufferRegion s0 ("ssz_len_chunk", 32) ∨ i = (outw.toNat, 32) := by
      simpa [valWordNat] using hi
    rcases hi' with rfl | rfl
    · exact ⟨bufferRegion s0 ("ssz_len_chunk", 32), List.mem_cons_self, le_rfl, le_rfl⟩
    · exact ⟨(outw.toNat, 32), List.mem_cons_of_mem _ (List.mem_singleton.2 rfl), le_rfl, le_rfl⟩
  · rcases List.mem_cons.1 hiv with rfl | hiv'
    · exact Or.inr (Or.inl ⟨("ssz_len_chunk", 32), by decide, le_rfl, le_rfl⟩)
    · rcases List.mem_singleton.1 hiv' with rfl
      exact outIvlCovered_to_world hcov 32 le_rfl

private theorem merkleize_prog_pow4_le :
    ∀ k : Nat, k < 28 →
      1 + 3 * (4 ^ k - 1) = 4 ^ k * 3 - 2 ∧
      (4 ^ k - 1) / 3 * 3 = 4 ^ k - 1 ∧
      4 ^ k ≤ 2 ^ 54 := by
  intro k hk
  have hmod : ∀ j : Nat, (4 ^ j - 1) % 3 = 0 := by
    intro j
    induction j with
    | zero => rfl
    | succ m ih =>
      have hposm : 1 ≤ 4 ^ m := Nat.one_le_pow _ _ (by omega)
      have heq : 4 ^ (m + 1) - 1 = 4 * (4 ^ m - 1) + 3 := by
        rw [Nat.pow_succ]; omega
      rw [heq, Nat.add_mod, Nat.mul_mod, ih]
  have hlt54 : 2 * k ≤ 54 := by omega
  have h4k : 4 ^ k = 2 ^ (2 * k) := by
    rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_mul]
  have hle : 4 ^ k ≤ 2 ^ 54 := by
    rw [h4k]; exact Nat.pow_le_pow_right (by omega) hlt54
  have hpos : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by omega)
  have hmodk := hmod k
  refine ⟨by omega, by omega, hle⟩

private theorem worldEff_merkleize_progressive {F : Type}
    (s0 cur : PanSemStateFiniteExact 64 F) {Rl : List Ivl}
    (hAs0 : ArenaOK s0)
    (heff_cur : WorldEff s0 cur Rl sszBufs hpGw)
    {nw outw : BitVec 64}
    (hn_lk : cur.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hn_bound : nw.toNat < 2 ^ 46)
    (hout_lk : cur.locals.lookup (ofString "out") = some (.val (.word outw)))
    (hout_cov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_merkleize_progressive)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_merkleize_progressive)).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_merkleize_progressive)).2 Rl sszBufs hpGw := by
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_merkleize_progressive,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_decCall_heap_mark heff_cur (ofString "mark") hnt (Or.inr (Or.inr (Or.inr hres)))
    (fun markw m1 _ _ hmark_al hmark_lo hmark_hi hm1_eq heff_m1 hnt1 hcr1 => ?_)
  have hm1_n : m1.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hn_lk,
      show ofString "mark" ≠ ofString "n" by decide]
  have hm1_out : m1.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hout_lk,
      show ofString "mark" ≠ ofString "out" by decide]
  have hm1_mark : m1.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  refine worldEff_decCall_alloc heff_m1 (by decide) (ofString "roots") _ hnt1 hcr1
    (fun rootsw rszw m2 hrsz_ev _ hm2_loc _ heff_m2 _ _ hroots_lo hroots_end _ _ hnt2 hcr2 => ?_)
  have hrsz_eq : rszw = 768#64 := by
    simp [evalHOLExact, evalListHOLExact, valueIsWord, valueWord, panOpHOL] at hrsz_ev
    exact hrsz_ev.symm
  subst hrsz_eq
  have hroots_cap : rootsw.toNat + 768 ≤ heapLimit := by
    have : (768#64 : BitVec 64).toNat = 768 := rfl
    omega
  have hm2_roots : m2.locals.lookup (ofString "roots") = some (.val (.word rootsw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hm2_n : m2.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_n,
      show ofString "roots" ≠ ofString "n" by decide]
  have hm2_out : m2.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_out,
      show ofString "roots" ≠ ofString "out" by decide]
  have hm2_mark : m2.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_mark,
      show ofString "roots" ≠ ofString "mark" by decide]
  refine worldEff_decCall_alloc heff_m2 (by decide) (ofString "acc") _ hnt2 hcr2
    (fun accw aszw m3 hasz_ev _ hm3_loc _ heff_m3 _ _ hacc_lo hacc_end _ _ hnt3 hcr3 => ?_)
  have hasz_eq : aszw = 32#64 := by
    simp [evalHOLExact] at hasz_ev; exact hasz_ev.symm
  subst hasz_eq
  have hacc_cap : accw.toNat + 32 ≤ heapLimit := by
    have : (32#64 : BitVec 64).toNat = 32 := rfl
    omega
  have hm3_acc : m3.locals.lookup (ofString "acc") = some (.val (.word accw)) := by
    rw [hm3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hm3_roots : m3.locals.lookup (ofString "roots") = some (.val (.word rootsw)) := by
    rw [hm3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm2_roots,
      show ofString "acc" ≠ ofString "roots" by decide]
  have hm3_n : m3.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    rw [hm3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm2_n,
      show ofString "acc" ≠ ofString "n" by decide]
  have hm3_out : m3.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm2_out,
      show ofString "acc" ≠ ofString "out" by decide]
  have hm3_mark : m3.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    rw [hm3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm2_mark,
      show ofString "acc" ≠ ofString "mark" by decide]
  refine worldEff_dec heff_m3 (ofString "k") .one _ hnt3 hcr3
    (fun vk hvk hvsh3 hnt4 hcr4 => ?_)
  rcases vk with ⟨⟨kw0⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hvsh3)
  have hkw0 : kw0 = 0#64 := by simp [evalHOLExact] at hvk; exact hvk.symm
  subst hkw0
  let m4 := setVarHOLFinite (ofString "k") (.val (.word 0#64)) m3
  have heff_m4 : WorldEff s0 m4 Rl sszBufs hpGw := heff_m3.locals_clock _ _
  refine worldEff_dec heff_m4 (ofString "off") .one _ hnt4 hcr4
    (fun voff hvoff hvsh4 hnt5 hcr5 => ?_)
  rcases voff with ⟨⟨offw0⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hvsh4)
  have hoffw0 : offw0 = 0#64 := by simp [evalHOLExact] at hvoff; exact hvoff.symm
  subst hoffw0
  let m5 := setVarHOLFinite (ofString "off") (.val (.word 0#64)) m4
  have heff_m5 : WorldEff s0 m5 Rl sszBufs hpGw := heff_m4.locals_clock _ _
  refine worldEff_dec heff_m5 (ofString "size") .one _ hnt5 hcr5
    (fun vsz hvsz hvsh5 hnt6 hcr6 => ?_)
  rcases vsz with ⟨⟨szw0⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hvsh5)
  have hszw0 : szw0 = 1#64 := by simp [evalHOLExact] at hvsz; exact hvsz.symm
  subst hszw0
  let m6 := setVarHOLFinite (ofString "size") (.val (.word 1#64)) m5
  have heff_m6 : WorldEff s0 m6 Rl sszBufs hpGw := heff_m5.locals_clock _ _
  -- Loop 1 invariant: `off = (4^k - 1)/3`, `size = 4^k`, `k ≤ 24`
  let Inv1 : PanSemStateFiniteExact 64 F → Prop := fun st =>
    st.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
    st.locals.lookup (ofString "roots") = some (.val (.word rootsw)) ∧
    st.locals.lookup (ofString "acc") = some (.val (.word accw)) ∧
    st.locals.lookup (ofString "out") = some (.val (.word outw)) ∧
    st.locals.lookup (ofString "mark") = some (.val (.word markw)) ∧
    ∃ kw offw sizew : BitVec 64,
      st.locals.lookup (ofString "k") = some (.val (.word kw)) ∧
      st.locals.lookup (ofString "off") = some (.val (.word offw)) ∧
      st.locals.lookup (ofString "size") = some (.val (.word sizew)) ∧
      kw.toNat ≤ 24 ∧
      sizew.toNat = 4 ^ kw.toNat ∧
      3 * offw.toNat + 1 = 4 ^ kw.toNat
  have hInv1_m6 : Inv1 m6 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, 0#64, 0#64, 1#64, ?_, ?_, ?_, by decide, rfl, rfl⟩ <;>
      simp [m6, m5, m4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        hm3_n, hm3_roots, hm3_acc, hm3_out, hm3_mark,
        show ofString "size" ≠ ofString "n" by decide,
        show ofString "size" ≠ ofString "roots" by decide,
        show ofString "size" ≠ ofString "acc" by decide,
        show ofString "size" ≠ ofString "out" by decide,
        show ofString "size" ≠ ofString "mark" by decide,
        show ofString "size" ≠ ofString "k" by decide,
        show ofString "size" ≠ ofString "off" by decide,
        show ofString "off" ≠ ofString "n" by decide,
        show ofString "off" ≠ ofString "roots" by decide,
        show ofString "off" ≠ ofString "acc" by decide,
        show ofString "off" ≠ ofString "out" by decide,
        show ofString "off" ≠ ofString "mark" by decide,
        show ofString "off" ≠ ofString "k" by decide,
        show ofString "k" ≠ ofString "n" by decide,
        show ofString "k" ≠ ofString "roots" by decide,
        show ofString "k" ≠ ofString "acc" by decide,
        show ofString "k" ≠ ofString "out" by decide,
        show ofString "k" ≠ ofString "mark" by decide]
  let body1 : ProgHOL 64 :=
    .dec (ofString "cnt") .one (.op .sub [.var .local (ofString "n"), .var .local (ofString "off")])
      (.seq
        (.ite (.cmp .lower (.var .local (ofString "size")) (.var .local (ofString "cnt")))
          (.assign .local (ofString "cnt") (.var .local (ofString "size")))
          .skip)
        (.seq
          (.call (some (none, none)) (ofString "merkleize")
            [.op .add [.var .local (ofString "p"), .panop .mul [.var .local (ofString "off"), .const 32#64]],
             .var .local (ofString "cnt"),
             .var .local (ofString "size"),
             .op .add [.var .local (ofString "roots"), .panop .mul [.var .local (ofString "k"), .const 32#64]]])
          (.seq
            (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "size")]))
            (.seq
              (.assign .local (ofString "size") (.shift .lsl (.var .local (ofString "size")) (.const 2#64)))
              (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1#64]))))))
  have hstep1 : ∀ u (cw : BitVec 64),
      @evalHOLFinite 64 F _ u (fun a => Classical.propDecidable (u.memaddrs a))
        (.cmp .lower (.var .local (ofString "off")) (.var .local (ofString "n"))) = some (.val (.word cw)) →
      cw ≠ 0 →
      WorldEff s0 (decClockHOLFinite u) Rl sszBufs hpGw → Inv1 (decClockHOLFinite u) →
      (evaluateHOLFiniteState (decClockHOLFinite u) body1).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState (decClockHOLFinite u) body1).1 →
      WorldEff s0 (evaluateHOLFiniteState (decClockHOLFinite u) body1).2 Rl sszBufs hpGw ∧
      (((evaluateHOLFiniteState (decClockHOLFinite u) body1).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite u) body1).1 = some .continue) →
        Inv1 (evaluateHOLFiniteState (decClockHOLFinite u) body1).2) := by
    intro u cw hcw hcw_ne heff_ud ⟨hu_n, hu_roots, hu_acc, hu_out, hu_mark, kw, offw, sizew,
      hu_k, hu_off, hu_sz, hk_le24, hsz_pow, hoff_eq⟩ hnt_b hcr_b
    let ud := decClockHOLFinite u
    have hu_n0 : u.locals.lookup (ofString "n") = some (.val (.word nw)) := hu_n
    have hu_off0 : u.locals.lookup (ofString "off") = some (.val (.word offw)) := hu_off
    have hud_n : ud.locals.lookup (ofString "n") = some (.val (.word nw)) := hu_n
    have hud_roots : ud.locals.lookup (ofString "roots") = some (.val (.word rootsw)) := hu_roots
    have hud_acc : ud.locals.lookup (ofString "acc") = some (.val (.word accw)) := hu_acc
    have hud_out : ud.locals.lookup (ofString "out") = some (.val (.word outw)) := hu_out
    have hud_mark : ud.locals.lookup (ofString "mark") = some (.val (.word markw)) := hu_mark
    have hud_k : ud.locals.lookup (ofString "k") = some (.val (.word kw)) := hu_k
    have hud_off : ud.locals.lookup (ofString "off") = some (.val (.word offw)) := hu_off
    have hud_sz : ud.locals.lookup (ofString "size") = some (.val (.word sizew)) := hu_sz
    have hoff_lt_n : offw.toNat < nw.toNat := by
      rw [evalHOLFinite_eq_toExact] at hcw
      simp only [evalHOLExact, toExact, hu_off0, hu_n0, Compiler.Encoders.Asm.wordCmpHOL] at hcw
      by_cases hlt : offw < nw
      · exact BitVec.lt_def.1 hlt
      · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte] at hcw
        injection hcw with h1; injection h1 with h2; injection h2 with h3
        exact absurd h3.symm hcw_ne
    have hk_lt24 : kw.toNat < 24 := by
      by_contra hge
      have hkeq : kw.toNat = 24 := by omega
      have h4_24 : 4 ^ 24 = 281474976710656 := by decide
      rw [hkeq, h4_24] at hoff_eq
      have : nw.toNat < 70368744177664 := hn_bound
      omega
    have hk32_lt : kw.toNat * (32#64 : BitVec 64).toNat < 2 ^ 64 := by
      rw [show (32#64 : BitVec 64).toNat = 32 from rfl]; omega
    have hk32_nat : (kw * 32#64).toNat = kw.toNat * 32 := by
      rw [BitVec.toNat_mul, show (32#64 : BitVec 64).toNat = 32 from rfl]
      exact Nat.mod_eq_of_lt hk32_lt
    have hcnt0_nat : (nw - offw).toNat = nw.toNat - offw.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_def.2 (by omega))
    have hcnt0_ev : @evalHOLExact 64 F _ ud.toExact (fun a => Classical.propDecidable (ud.memaddrs a))
        (.op .sub [.var .local (ofString "n"), .var .local (ofString "off")]) =
        some (.val (.word (nw - offw))) := by
      simp [evalHOLExact, evalListHOLExact, toExact, hud_n, hud_off,
        valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map]
    have hsz_le46 : sizew.toNat ≤ 2 ^ 46 := by
      rw [hsz_pow]
      calc 4 ^ kw.toNat ≤ 4 ^ 23 := Nat.pow_le_pow_right (by omega) (by omega)
        _ = 2 ^ 46 := by decide
    have hwe_b : WorldEff s0 (evaluateHOLFiniteState ud body1).2 Rl sszBufs hpGw := by
      dsimp only [body1] at hnt_b hcr_b ⊢
      refine worldEff_dec heff_ud (ofString "cnt") .one _ hnt_b hcr_b
        (fun vcnt hvcnt hvsh_c hnt_s1 hcr_s1 => ?_)
      have hvc_eq : vcnt = .val (.word (nw - offw)) := by
        rw [hcnt0_ev] at hvcnt; injection hvcnt with h; exact h.symm
      subst hvc_eq
      let b1 := setVarHOLFinite (ofString "cnt") (.val (.word (nw - offw))) ud
      have heff_b1 : WorldEff s0 b1 Rl sszBufs hpGw := heff_ud.locals_clock _ _
      have hb1_cnt : b1.locals.lookup (ofString "cnt") = some (.val (.word (nw - offw))) := by
        simp [b1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hb1_sz : b1.locals.lookup (ofString "size") = some (.val (.word sizew)) := by
        simp [b1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hud_sz,
          show ofString "cnt" ≠ ofString "size" by decide]
      have hb1_roots : b1.locals.lookup (ofString "roots") = some (.val (.word rootsw)) := by
        simp [b1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hud_roots,
          show ofString "cnt" ≠ ofString "roots" by decide]
      have hb1_k : b1.locals.lookup (ofString "k") = some (.val (.word kw)) := by
        simp [b1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hud_k,
          show ofString "cnt" ≠ ofString "k" by decide]
      refine worldEff_seq hnt_s1 hcr_s1
        (fun hnt_i hcr_i =>
          worldEff_ite heff_b1 _ hnt_i hcr_i
            (fun _ _ _ _ _ => worldEff_assign_local heff_b1 _ _)
            (fun _ _ _ => worldEff_skip heff_b1))
        (fun b2 hb2 heff_b2 hnt_s2 hcr_s2 => ?_)
      have hb2_props : ∃ cntw : BitVec 64,
          cntw.toNat < 2 ^ 58 ∧
          b2.locals.lookup (ofString "cnt") = some (.val (.word cntw)) ∧
          b2.locals.lookup (ofString "roots") = some (.val (.word rootsw)) ∧
          b2.locals.lookup (ofString "k") = some (.val (.word kw)) := by
        rw [evaluateHOLFiniteState_ite] at hb2
        have hcond_ev : @evalHOLExact 64 F _ b1.toExact (fun a => Classical.propDecidable (b1.memaddrs a))
            (.cmp .lower (.var .local (ofString "size")) (.var .local (ofString "cnt"))) =
            some (.val (.word (if sizew < nw - offw then 1#64 else 0#64))) := by
          simp [evalHOLExact, toExact, hb1_sz, hb1_cnt, Compiler.Encoders.Asm.wordCmpHOL]
        rw [hcond_ev] at hb2; dsimp only at hb2
        by_cases hlt_sc : sizew < nw - offw
        · simp only [hlt_sc, decide_true, ↓reduceIte] at hb2
          rw [if_neg (show ¬ ((1#64 : BitVec 64) = 0) by decide)] at hb2
          rw [evaluateHOLFiniteState_assign] at hb2
          have hsz_ev1 : @evalHOLExact 64 F _ b1.toExact (fun a => Classical.propDecidable (b1.memaddrs a))
              (.var .local (ofString "size")) = some (.val (.word sizew)) := by
            simp [evalHOLExact, toExact, hb1_sz]
          have hvv1 : isValidValueHOLFinite b1 .local (ofString "cnt") (.val (.word sizew)) = true := by
            simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, toExact, hb1_cnt,
              shapeOfHOLExact, shapeEqHOL]
          rw [hsz_ev1] at hb2; dsimp only at hb2; rw [if_pos hvv1] at hb2
          obtain ⟨_, rfl⟩ := Prod.mk.inj hb2
          refine ⟨sizew, by omega, ?_, ?_, ?_⟩
          · simp [b1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          · simp [b1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "cnt" ≠ ofString "roots" by decide]; exact hud_roots
          · simp [b1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "cnt" ≠ ofString "k" by decide]; exact hud_k
        · simp only [hlt_sc, decide_false, Bool.false_eq_true, ↓reduceIte] at hb2
          rw [if_pos (show (0#64 : BitVec 64) = 0 by decide), evaluateHOLFiniteState_skip] at hb2
          obtain ⟨_, rfl⟩ := Prod.mk.inj hb2
          exact ⟨nw - offw, by omega, hb1_cnt, hb1_roots, hb1_k⟩
      obtain ⟨cntw, hcnt_lt58, hb2_cnt, hb2_roots, hb2_k⟩ := hb2_props
      refine worldEff_seq hnt_s2 hcr_s2
        (fun hnt_mk hcr_mk =>
          worldEff_call0_merkleize hAs0 heff_b2
            (.op .add [.var .local (ofString "p"), .panop .mul [.var .local (ofString "off"), .const 32#64]])
            (.var .local (ofString "cnt"))
            (.var .local (ofString "size"))
            (.op .add [.var .local (ofString "roots"), .panop .mul [.var .local (ofString "k"), .const 32#64]])
            cntw (rootsw + kw * 32#64)
            (by simp [evalHOLExact, toExact, hb2_cnt])
            hcnt_lt58
            (by simp [evalHOLExact, evalListHOLExact, toExact, hb2_roots, hb2_k,
                  valueIsWord, valueWord, panOpHOL, hk32_lt, wordOpHOL, wordOp,
                  List.all, List.map, Option.map, List.foldr])
            (outIvlCovered_heap_offset hroots_lo hroots_cap (by rw [hk32_nat]; omega))
            hnt_mk hcr_mk)
        (fun b3 _ heff_b3 hnt_s3 hcr_s3 =>
          worldEff_seq hnt_s3 hcr_s3
            (fun _ _ => worldEff_assign_local heff_b3 _ _)
            (fun b4 _ heff_b4 hnt_s4 hcr_s4 =>
              worldEff_seq hnt_s4 hcr_s4
                (fun _ _ => worldEff_assign_local heff_b4 _ _)
                (fun b5 _ heff_b5 _ _ => worldEff_assign_local heff_b5 _ _)))
    refine ⟨hwe_b, fun hfl_b => ?_⟩
    dsimp only [body1] at hfl_b ⊢
    rw [evaluateHOLFiniteState_dec_total] at hfl_b ⊢
    dsimp only at hfl_b ⊢
    rw [hcnt0_ev] at hfl_b ⊢
    simp only [shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hfl_b ⊢
    let b1 := setVarHOLFinite (ofString "cnt") (.val (.word (nw - offw))) ud
    have hb1_cnt : b1.locals.lookup (ofString "cnt") = some (.val (.word (nw - offw))) := by
      simp [b1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hb1_sz : b1.locals.lookup (ofString "size") = some (.val (.word sizew)) := by
      simp [b1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hud_sz,
        show ofString "cnt" ≠ ofString "size" by decide]
    change (evaluateHOLFiniteState b1 _).1 = none ∨ (evaluateHOLFiniteState b1 _).1 = some .continue at hfl_b
    rw [evaluateHOLFiniteState_seq_line780] at hfl_b ⊢
    rcases hite : evaluateHOLFiniteState b1 _ with ⟨rite, b2⟩
    rw [hite] at hfl_b
    have hite_res : rite = none ∧ ∃ cntw : BitVec 64,
        cntw.toNat = Nat.min sizew.toNat (nw - offw).toNat ∧
        b2.code = b1.code ∧
        (b2.locals = b1.locals ∨ b2.locals = b1.locals.update (ofString "cnt", .val (.word cntw))) := by
      rw [evaluateHOLFiniteState_ite] at hite
      have hcond_ev : @evalHOLExact 64 F _ b1.toExact (fun a => Classical.propDecidable (b1.memaddrs a))
          (.cmp .lower (.var .local (ofString "size")) (.var .local (ofString "cnt"))) =
          some (.val (.word (if sizew < nw - offw then 1#64 else 0#64))) := by
        simp [evalHOLExact, toExact, hb1_sz, hb1_cnt, Compiler.Encoders.Asm.wordCmpHOL]
      rw [hcond_ev] at hite; dsimp only at hite
      by_cases hlt_sc : sizew < nw - offw
      · simp only [hlt_sc, decide_true, ↓reduceIte] at hite
        rw [if_neg (show ¬ ((1#64 : BitVec 64) = 0) by decide)] at hite
        rw [evaluateHOLFiniteState_assign] at hite
        have hsz_ev1 : @evalHOLExact 64 F _ b1.toExact (fun a => Classical.propDecidable (b1.memaddrs a))
            (.var .local (ofString "size")) = some (.val (.word sizew)) := by
          simp [evalHOLExact, toExact, hb1_sz]
        have hvv1 : isValidValueHOLFinite b1 .local (ofString "cnt") (.val (.word sizew)) = true := by
          simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, toExact, hb1_cnt,
            shapeOfHOLExact, shapeEqHOL]
        rw [hsz_ev1] at hite; dsimp only at hite; rw [if_pos hvv1] at hite
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hite
        have hlt_nat : sizew.toNat < (nw - offw).toNat := BitVec.lt_def.1 hlt_sc
        exact ⟨rfl, sizew, (Nat.min_eq_left (Nat.le_of_lt hlt_nat)).symm, rfl, Or.inr rfl⟩
      · simp only [hlt_sc, decide_false, Bool.false_eq_true, ↓reduceIte] at hite
        rw [if_pos (show (0#64 : BitVec 64) = 0 by decide), evaluateHOLFiniteState_skip] at hite
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hite
        have hge_nat : (nw - offw).toNat ≤ sizew.toNat :=
          Nat.not_lt.1 (fun h => hlt_sc (BitVec.lt_def.2 h))
        exact ⟨rfl, nw - offw, (Nat.min_eq_right hge_nat).symm, rfl, Or.inl rfl⟩
    obtain ⟨rfl, cntw, hcnt_min, hb2_code, hb2_loc⟩ := hite_res
    dsimp only at hfl_b ⊢
    rw [evaluateHOLFiniteState_seq_line780] at hfl_b ⊢
    have hnc_mk := call0_ne_continue b2 (ofString "merkleize")
      [.op .add [.var .local (ofString "p"), .panop .mul [.var .local (ofString "off"), .const 32#64]],
       .var .local (ofString "cnt"),
       .var .local (ofString "size"),
       .op .add [.var .local (ofString "roots"), .panop .mul [.var .local (ofString "k"), .const 32#64]]]
    rcases hmk : evaluateHOLFiniteState b2 _ with ⟨rmk, b3⟩
    rw [hmk] at hfl_b hnc_mk
    cases rmk with
    | some r =>
      rcases hfl_b with h | h
      · simp at h
      · exact absurd h hnc_mk
    | none =>
      dsimp only at hfl_b ⊢
      have hb3_loc : b3.locals = b2.locals := by
        have := call0_none_locals b2 (ofString "merkleize") _ (by rw [hmk])
        rwa [hmk] at this
      have hb2_non_cnt : ∀ x : MlS, x ≠ ofString "cnt" → b2.locals.lookup x = ud.locals.lookup x := by
        intro x hx
        rcases hb2_loc with hloc | hloc <;>
          simp [hloc, b1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hx]
      have hb3_off : b3.locals.lookup (ofString "off") = some (.val (.word offw)) := by
        rw [hb3_loc, hb2_non_cnt _ (by decide)]; exact hud_off
      have hb3_sz : b3.locals.lookup (ofString "size") = some (.val (.word sizew)) := by
        rw [hb3_loc, hb2_non_cnt _ (by decide)]; exact hud_sz
      have hb3_k : b3.locals.lookup (ofString "k") = some (.val (.word kw)) := by
        rw [hb3_loc, hb2_non_cnt _ (by decide)]; exact hud_k
      rw [evaluateHOLFiniteState_seq_line780] at hfl_b ⊢
      have ha_off : evaluateHOLFiniteState b3
          (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "size")])) =
          (none, setVarHOLFinite (ofString "off") (.val (.word (offw + sizew))) b3) := by
        have hev : @evalHOLExact 64 F _ b3.toExact (fun a => Classical.propDecidable (b3.memaddrs a))
            (.op .add [.var .local (ofString "off"), .var .local (ofString "size")]) =
            some (.val (.word (offw + sizew))) := by
          simp [evalHOLExact, evalListHOLExact, toExact, hb3_off, hb3_sz,
            valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr]
        have hvv : isValidValueHOLFinite b3 .local (ofString "off") (.val (.word (offw + sizew))) = true := by
          simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, toExact, hb3_off, shapeOfHOLExact, shapeEqHOL]
        rw [evaluateHOLFiniteState_assign, hev]; dsimp only; rw [if_pos hvv]; rfl
      rw [ha_off]; dsimp only
      let b4 := setVarHOLFinite (ofString "off") (.val (.word (offw + sizew))) b3
      have hb4_sz : b4.locals.lookup (ofString "size") = some (.val (.word sizew)) := by
        simp [b4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hb3_sz,
          show ofString "off" ≠ ofString "size" by decide]
      have hb4_k : b4.locals.lookup (ofString "k") = some (.val (.word kw)) := by
        simp [b4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hb3_k,
          show ofString "off" ≠ ofString "k" by decide]
      rw [evaluateHOLFiniteState_seq_line780]
      have ha_sz : evaluateHOLFiniteState b4
          (.assign .local (ofString "size") (.shift .lsl (.var .local (ofString "size")) (.const 2#64))) =
          (none, setVarHOLFinite (ofString "size") (.val (.word (sizew <<< 2#64))) b4) := by
        have hev : @evalHOLExact 64 F _ b4.toExact (fun a => Classical.propDecidable (b4.memaddrs a))
            (.shift .lsl (.var .local (ofString "size")) (.const 2#64)) =
            some (.val (.word (sizew <<< 2#64))) := by
          simp [evalHOLExact, toExact, hb4_sz, wordShiftHOL]
        have hvv : isValidValueHOLFinite b4 .local (ofString "size") (.val (.word (sizew <<< 2#64))) = true := by
          simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, toExact, hb4_sz, shapeOfHOLExact, shapeEqHOL]
        rw [evaluateHOLFiniteState_assign, hev]; dsimp only; rw [if_pos hvv]; rfl
      rw [ha_sz]; dsimp only
      let b5 := setVarHOLFinite (ofString "size") (.val (.word (sizew <<< 2#64))) b4
      have hb5_k : b5.locals.lookup (ofString "k") = some (.val (.word kw)) := by
        simp [b5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hb4_k,
          show ofString "size" ≠ ofString "k" by decide]
      have ha_k : evaluateHOLFiniteState b5
          (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1#64])) =
          (none, setVarHOLFinite (ofString "k") (.val (.word (kw + 1#64))) b5) := by
        have hev : @evalHOLExact 64 F _ b5.toExact (fun a => Classical.propDecidable (b5.memaddrs a))
            (.op .add [.var .local (ofString "k"), .const 1#64]) =
            some (.val (.word (kw + 1#64))) := by
          simp [evalHOLExact, evalListHOLExact, toExact, hb5_k,
            valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr]
        have hvv : isValidValueHOLFinite b5 .local (ofString "k") (.val (.word (kw + 1#64))) = true := by
          simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, toExact, hb5_k, shapeOfHOLExact, shapeEqHOL]
        rw [evaluateHOLFiniteState_assign, hev]; dsimp only; rw [if_pos hvv]; rfl
      rw [ha_k]; dsimp only
      have hk1_nat : (kw + 1#64).toNat = kw.toNat + 1 :=
        BitVec.toNat_add_of_lt (by rw [show (1#64 : BitVec 64).toNat = 1 from rfl]; omega)
      have hoff1_nat : (offw + sizew).toNat = offw.toNat + sizew.toNat :=
        BitVec.toNat_add_of_lt (by omega)
      have hsz1_nat : (sizew <<< 2#64).toNat = 4 ^ (kw.toNat + 1) := by
        change (sizew <<< (2#64 : BitVec 64).toNat).toNat = 4 ^ (kw.toNat + 1)
        rw [BitVec.toNat_shiftLeft, show (2#64 : BitVec 64).toNat = 2 from rfl,
          Nat.shiftLeft_eq, hsz_pow, show 2 ^ 2 = 4 from rfl, ← Nat.pow_succ]
        exact Nat.mod_eq_of_lt (by
          calc 4 ^ (kw.toNat + 1) ≤ 4 ^ 24 := Nat.pow_le_pow_right (by omega) (by omega)
            _ < 2 ^ 64 := by decide)
      have hoff1_eq : 3 * (offw + sizew).toNat + 1 = 4 ^ (kw + 1#64).toNat := by
        rw [hoff1_nat, hk1_nat, Nat.pow_succ, hsz_pow]; omega
      dsimp only [Inv1]
      refine ⟨?_, ?_, ?_, ?_, ?_, kw + 1#64, offw + sizew, sizew <<< 2#64,
        ?_, ?_, ?_, by omega, by rwa [hk1_nat], hoff1_eq⟩ <;>
        simp [PanRunBounded.resVarEq_lookup, b5, b4, hb3_loc, hb2_non_cnt,
          setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          hud_n, hud_roots, hud_acc, hud_out, hud_mark,
          show ofString "n" ≠ ofString "cnt" by decide,
          show ofString "roots" ≠ ofString "cnt" by decide,
          show ofString "acc" ≠ ofString "cnt" by decide,
          show ofString "out" ≠ ofString "cnt" by decide,
          show ofString "mark" ≠ ofString "cnt" by decide,
          show ofString "k" ≠ ofString "n" by decide,
          show ofString "k" ≠ ofString "roots" by decide,
          show ofString "k" ≠ ofString "acc" by decide,
          show ofString "k" ≠ ofString "out" by decide,
          show ofString "k" ≠ ofString "mark" by decide,
          show ofString "k" ≠ ofString "off" by decide,
          show ofString "k" ≠ ofString "size" by decide,
          show ofString "k" ≠ ofString "cnt" by decide,
          show ofString "size" ≠ ofString "n" by decide,
          show ofString "size" ≠ ofString "roots" by decide,
          show ofString "size" ≠ ofString "acc" by decide,
          show ofString "size" ≠ ofString "out" by decide,
          show ofString "size" ≠ ofString "mark" by decide,
          show ofString "size" ≠ ofString "off" by decide,
          show ofString "size" ≠ ofString "cnt" by decide,
          show ofString "off" ≠ ofString "n" by decide,
          show ofString "off" ≠ ofString "roots" by decide,
          show ofString "off" ≠ ofString "acc" by decide,
          show ofString "off" ≠ ofString "out" by decide,
          show ofString "off" ≠ ofString "mark" by decide,
          show ofString "off" ≠ ofString "cnt" by decide]
  refine worldEff_seq hnt6 hcr6
    (fun hnt_w1 hcr_w1 =>
      (worldEff_while_cond_post (.cmp .lower (.var .local (ofString "off")) (.var .local (ofString "n")))
        Inv1 (fun u hu => hu) hstep1 m6.clock m6 rfl heff_m6 hInv1_m6 hnt_w1 hcr_w1).1)
    (fun m7 hm7 heff_m7 hnt7 hcr7 => ?_)
  have hInv1_m7 : Inv1 m7 := by
    have hp := (worldEff_while_cond_post (.cmp .lower (.var .local (ofString "off")) (.var .local (ofString "n")))
      Inv1 (fun u hu => hu) hstep1 m6.clock m6 rfl heff_m6 hInv1_m6
      (by rw [hm7]; simp) (by rw [hm7]; exact Or.inl rfl)).2 (by rw [hm7])
      (fun u ⟨hu_n, _, _, _, _, _, offu, _, _, hu_off, _, _, _, _⟩ => by
        refine dec_word_ne_break u (ofString "cnt") _ (nw - offu)
          (by simp [evalHOLExact, evalListHOLExact, toExact, hu_n, hu_off,
                valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map]) ?_
        refine seq_ne_break _ ?_ (fun mid1 _ =>
          seq_ne_break mid1 (call0_ne_break mid1 _ _) (fun mid2 _ =>
            seq_ne_break mid2 (assign_local_ne_break mid2 _ _) (fun mid3 _ =>
              seq_ne_break mid3 (assign_local_ne_break mid3 _ _) (fun mid4 _ =>
                assign_local_ne_break mid4 _ _))))
        rw [evaluateHOLFiniteState_ite]
        rcases hev_c : @evalHOLExact 64 F _ (setVarHOLFinite (ofString "cnt") (.val (.word (nw - offu))) u).toExact
          (fun a => Classical.propDecidable ((setVarHOLFinite (ofString "cnt") (.val (.word (nw - offu))) u).memaddrs a))
          (.cmp .lower (.var .local (ofString "size")) (.var .local (ofString "cnt"))) with _ | cv
        · simp [hev_c]
        · rcases cv with ⟨⟨cw'⟩⟩ | _ | _ <;> simp only [hev_c]
          · by_cases hz : cw' = 0
            · rw [if_pos hz, evaluateHOLFiniteState_skip]; simp
            · rw [if_neg hz]; exact assign_local_ne_break _ _ _
          · simp
          · simp)
    rw [hm7] at hp; exact hp.1
  obtain ⟨_, hm7_roots, hm7_acc, hm7_out, hm7_mark, kw7, _, _, hm7_k, _, _, hkw7_le24, _, _⟩ := hInv1_m7
  -- `memzero(acc, 32)`
  refine worldEff_seq hnt7 hcr7
    (fun hnt_mz hcr_mz =>
      worldEff_call0_funByteEff heff_m7 funByteEff_memzero _
        [(accw.toNat, 32)]
        (fun vals hargs i hi _ => by
          rw [evalListHOLFinite_eq_toExact] at hargs
          simp only [evalListHOLExact, evalHOLExact, toExact, hm7_acc] at hargs
          injection hargs with hargs_eq; subst hargs_eq
          simp only [valWordNat, List.mem_singleton] at hi; subst hi
          exact ⟨(accw.toNat, 32), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
        (fun iv hiv _ => by
          simp only [List.mem_singleton] at hiv; subst hiv
          exact Or.inr (Or.inr (Or.inr ⟨hacc_lo, hacc_cap⟩)))
        hnt_mz hcr_mz)
    (fun m8 hm8 heff_m8 hnt8 hcr8 => ?_)
  have hm8_loc : m8.locals = m7.locals := by
    have := call0_none_locals m7 (ofString "memzero") _ (by rw [hm8])
    rwa [hm8] at this
  -- Loop 2: `while (k != 0) { k := k - 1; sha256_pair(roots + k * 32, acc, acc) }`
  let Inv2 : PanSemStateFiniteExact 64 F → Prop := fun st =>
    st.locals.lookup (ofString "roots") = some (.val (.word rootsw)) ∧
    st.locals.lookup (ofString "acc") = some (.val (.word accw)) ∧
    st.locals.lookup (ofString "out") = some (.val (.word outw)) ∧
    st.locals.lookup (ofString "mark") = some (.val (.word markw)) ∧
    ∃ kw : BitVec 64, st.locals.lookup (ofString "k") = some (.val (.word kw)) ∧ kw.toNat ≤ 24
  have hInv2_m8 : Inv2 m8 := by
    dsimp only [Inv2]
    rw [hm8_loc]
    exact ⟨hm7_roots, hm7_acc, hm7_out, hm7_mark, kw7, hm7_k, hkw7_le24⟩
  let body2 : ProgHOL 64 :=
    .seq
      (.assign .local (ofString "k") (.op .sub [.var .local (ofString "k"), .const 1#64]))
      (.call (some (none, none)) (ofString "sha256_pair")
        [.op .add [.var .local (ofString "roots"), .panop .mul [.var .local (ofString "k"), .const 32#64]],
         .var .local (ofString "acc"),
         .var .local (ofString "acc")])
  have hstep2 : ∀ u (cw : BitVec 64),
      @evalHOLFinite 64 F _ u (fun a => Classical.propDecidable (u.memaddrs a))
        (.cmp .notEqual (.var .local (ofString "k")) (.const 0#64)) = some (.val (.word cw)) →
      cw ≠ 0 →
      WorldEff s0 (decClockHOLFinite u) Rl sszBufs hpGw → Inv2 (decClockHOLFinite u) →
      (evaluateHOLFiniteState (decClockHOLFinite u) body2).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState (decClockHOLFinite u) body2).1 →
      WorldEff s0 (evaluateHOLFiniteState (decClockHOLFinite u) body2).2 Rl sszBufs hpGw ∧
      (((evaluateHOLFiniteState (decClockHOLFinite u) body2).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite u) body2).1 = some .continue) →
        Inv2 (evaluateHOLFiniteState (decClockHOLFinite u) body2).2) := by
    intro u cw hcw hcw_ne heff_ud ⟨hu_roots, hu_acc, hu_out, hu_mark, kw, hu_k, hk_le⟩ hnt_b2 hcr_b2
    let ud := decClockHOLFinite u
    have hu_k0 : u.locals.lookup (ofString "k") = some (.val (.word kw)) := hu_k
    have hud_roots : ud.locals.lookup (ofString "roots") = some (.val (.word rootsw)) := hu_roots
    have hud_acc : ud.locals.lookup (ofString "acc") = some (.val (.word accw)) := hu_acc
    have hud_out : ud.locals.lookup (ofString "out") = some (.val (.word outw)) := hu_out
    have hud_mark : ud.locals.lookup (ofString "mark") = some (.val (.word markw)) := hu_mark
    have hud_k : ud.locals.lookup (ofString "k") = some (.val (.word kw)) := hu_k
    have hk_pos : 0 < kw.toNat := by
      rw [evalHOLFinite_eq_toExact] at hcw
      by_cases hkz : kw = 0#64
      · subst hkz
        simp [evalHOLExact, toExact, hu_k0, Compiler.Encoders.Asm.wordCmpHOL] at hcw
        exact absurd hcw.symm hcw_ne
      · exact Nat.pos_of_ne_zero (fun hz => hkz (BitVec.eq_of_toNat_eq hz))
    have ha_k : evaluateHOLFiniteState ud
        (.assign .local (ofString "k") (.op .sub [.var .local (ofString "k"), .const 1#64])) =
        (none, setVarHOLFinite (ofString "k") (.val (.word (kw - 1#64))) ud) := by
      have hev : @evalHOLExact 64 F _ ud.toExact (fun a => Classical.propDecidable (ud.memaddrs a))
          (.op .sub [.var .local (ofString "k"), .const 1#64]) =
          some (.val (.word (kw - 1#64))) := by
        simp [evalHOLExact, evalListHOLExact, toExact, hud_k,
          valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map]
      have hvv : isValidValueHOLFinite ud .local (ofString "k") (.val (.word (kw - 1#64))) = true := by
        simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, toExact, hud_k, shapeOfHOLExact, shapeEqHOL]
      rw [evaluateHOLFiniteState_assign, hev]; dsimp only; rw [if_pos hvv]; rfl
    let d1 := setVarHOLFinite (ofString "k") (.val (.word (kw - 1#64))) ud
    have hd1_acc : d1.locals.lookup (ofString "acc") = some (.val (.word accw)) := by
      simp [d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hud_acc,
        show ofString "k" ≠ ofString "acc" by decide]
    have hwe_b2 : WorldEff s0 (evaluateHOLFiniteState ud body2).2 Rl sszBufs hpGw := by
      dsimp only [body2] at hnt_b2 hcr_b2 ⊢
      refine worldEff_seq hnt_b2 hcr_b2
        (fun _ _ => worldEff_assign_local heff_ud _ _)
        (fun mid hmid heff_mid hnt_sp hcr_sp => ?_)
      rw [ha_k] at hmid; obtain ⟨_, rfl⟩ := Prod.mk.inj hmid
      exact worldEff_call0_funByteEff heff_mid funByteEff_sha256_pair _
        [(accw.toNat, 32)]
        (fun vals hargs i hi _ => by
          have hlast : @evalHOLExact 64 F _ d1.toExact (fun a => Classical.propDecidable (d1.memaddrs a))
              (.var .local (ofString "acc")) = some (.val (.word accw)) := by
            simp [evalHOLExact, toExact, hd1_acc]
          obtain ⟨v0, v1, rfl⟩ := evalList3_last_word hlast hargs
          simp only [valWordNat, List.mem_singleton] at hi; subst hi
          exact ⟨(accw.toNat, 32), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
        (fun iv hiv _ => by
          simp only [List.mem_singleton] at hiv; subst hiv
          exact Or.inr (Or.inr (Or.inr ⟨hacc_lo, hacc_cap⟩)))
        hnt_sp hcr_sp
    refine ⟨hwe_b2, fun hfl_b2 => ?_⟩
    dsimp only [body2] at hfl_b2 ⊢
    rw [evaluateHOLFiniteState_seq_line780, ha_k] at hfl_b2 ⊢
    dsimp only at hfl_b2 ⊢
    have hnc_sp := call0_ne_continue d1 (ofString "sha256_pair")
      [.op .add [.var .local (ofString "roots"), .panop .mul [.var .local (ofString "k"), .const 32#64]],
       .var .local (ofString "acc"),
       .var .local (ofString "acc")]
    rcases hsp : evaluateHOLFiniteState d1 _ with ⟨rsp, d2⟩
    rw [hsp] at hfl_b2 hnc_sp
    cases rsp with
    | some r =>
      rcases hfl_b2 with h | h
      · simp at h
      · exact absurd h hnc_sp
    | none =>
      dsimp only
      have hd2_loc : d2.locals = d1.locals := by
        have := call0_none_locals d1 (ofString "sha256_pair") _ (by rw [hsp])
        rwa [hsp] at this
      have hk_sub : (kw - 1#64).toNat = kw.toNat - 1 :=
        BitVec.toNat_sub_of_le (BitVec.le_def.2 (by rw [show (1#64 : BitVec 64).toNat = 1 from rfl]; omega))
      dsimp only [Inv2]
      rw [hd2_loc]
      refine ⟨?_, ?_, ?_, ?_, kw - 1#64, ?_, by omega⟩ <;>
        simp [d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          hud_roots, hud_acc, hud_out, hud_mark,
          show ofString "k" ≠ ofString "roots" by decide,
          show ofString "k" ≠ ofString "acc" by decide,
          show ofString "k" ≠ ofString "out" by decide,
          show ofString "k" ≠ ofString "mark" by decide]
  refine worldEff_seq hnt8 hcr8
    (fun hnt_w2 hcr_w2 =>
      (worldEff_while_cond_post (.cmp .notEqual (.var .local (ofString "k")) (.const 0#64))
        Inv2 (fun u hu => hu) hstep2 m8.clock m8 rfl heff_m8 hInv2_m8 hnt_w2 hcr_w2).1)
    (fun m9 hm9 heff_m9 hnt9 hcr9 => ?_)
  have hInv2_m9 : Inv2 m9 := by
    have hp := (worldEff_while_cond_post (.cmp .notEqual (.var .local (ofString "k")) (.const 0#64))
      Inv2 (fun u hu => hu) hstep2 m8.clock m8 rfl heff_m8 hInv2_m8
      (by rw [hm9]; simp) (by rw [hm9]; exact Or.inl rfl)).2 (by rw [hm9])
      (fun u _ => seq_ne_break u (assign_local_ne_break u _ _) (fun mid _ => call0_ne_break mid _ _))
    rw [hm9] at hp; exact hp.1
  obtain ⟨_, hm9_acc, hm9_out, hm9_mark, _⟩ := hInv2_m9
  -- `memcpy(out, acc, 32); heap_release(mark); return 0`
  refine worldEff_seq hnt9 hcr9
    (fun hnt_cp hcr_cp =>
      (worldEff_call0_memcpy_word heff_m9
        (.var .local (ofString "out")) (.var .local (ofString "acc")) (.const 32#64) outw 32#64
        (by simp [evalHOLExact, toExact, hm9_out])
        rfl
        (fun _ _ => outIvlCovered_to_world hout_cov 32 le_rfl)
        hnt_cp hcr_cp).1)
    (fun m10 hm10 heff_m10 hnt10 hcr10 => ?_)
  have hm10_loc : m10.locals = m9.locals := by
    have := call0_none_locals m9 (ofString "memcpy") _ (by rw [hm10])
    rwa [hm10] at this
  refine worldEff_seq hnt10 hcr10
    (fun hnt_hr hcr_hr =>
      (worldEff_call0_heap_release hAs0 heff_m10 (by decide) hp_no_gb
        (.var .local (ofString "mark")) markw
        (by simp [evalHOLExact, toExact, hm10_loc, hm9_mark])
        hmark_lo hmark_hi hmark_al hnt_hr).2.choose_spec.2)
    (fun m11 _ heff_m11 _ _ => worldEff_return heff_m11 _)

private theorem worldEff_call0_merkleize_progressive {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hAs0 : ArenaOK s0) (heff : WorldEff s0 cur Rl sszBufs hpGw)
    (pExp nExp outExp : ExpHOL 64) (nw outw : BitVec 64)
    (hn : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      nExp = some (.val (.word nw)))
    (hn_bound : nw.toNat < 2 ^ 46)
    (hout : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      outExp = some (.val (.word outw)))
    (hcov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "merkleize_progressive")
      [pExp, nExp, outExp])).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "merkleize_progressive")
      [pExp, nExp, outExp])).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "merkleize_progressive")
      [pExp, nExp, outExp])).2 Rl sszBufs hpGw := by
  refine worldEff_call0_eff heff (ofString "merkleize_progressive") [pExp, nExp, outExp]
    _ _ _ lookup_merkleize_progressive (fun callee vals hargs hl hnt_e hres_e => ?_) hnt hcr
  rw [heff.code] at hl
  obtain ⟨pw, nw', ow, rfl, hp, hn', ho⟩ :=
    lookupCode_three_words (by decide) (by decide) (by decide) lookup_merkleize_progressive hl
  have hnw_eq : nw' = nw ∧ ow = outw := by
    rw [evalListHOLFinite_eq_toExact] at hargs
    simp only [evalListHOLExact, hn, hout] at hargs
    rcases hp0 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) pExp with _ | vp
    · simp [hp0] at hargs
    · simp only [hp0] at hargs
      injection hargs with h0
      injection h0 with _ h1
      injection h1 with h2 h3
      injection h2 with h2'; injection h2' with h2''
      injection h3 with h4 _; injection h4 with h4'; injection h4' with h4''
      exact ⟨h2''.symm, h4''.symm⟩
  obtain ⟨rfl, rfl⟩ := hnw_eq
  exact worldEff_merkleize_progressive s0 (callEntryStateHOLFinite cur callee) hAs0
    (heff.locals_clock _ _) hn' hn_bound ho hcov hnt_e hres_e

private theorem worldEff_htr_plist_chunks {F : Type}
    (s0 cur : PanSemStateFiniteExact 64 F) {Rl : List Ivl}
    (hAs0 : ArenaOK s0) (heff_cur : WorldEff s0 cur Rl sszBufs hpGw)
    {nw outw : BitVec 64}
    (hn_lk : cur.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hn_bound : nw.toNat < 2 ^ 46)
    (hout_lk : cur.locals.lookup (ofString "out") = some (.val (.word outw)))
    (hout_cov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_plist_chunks)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_plist_chunks)).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_plist_chunks)).2 Rl sszBufs hpGw := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_htr_plist_chunks,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_seq hnt (Or.inr (Or.inr (Or.inr hres)))
    (fun hnt1 hcr1 =>
      worldEff_call0_merkleize_progressive hAs0 heff_cur
        (.var .local (ofString "roots")) (.var .local (ofString "n")) (.var .local (ofString "out"))
        nw outw
        (by simp [evalHOLExact, toExact, hn_lk]) hn_bound
        (by simp [evalHOLExact, toExact, hout_lk]) hout_cov hnt1 hcr1)
    (fun m1 hm1 heff_m1 hnt2 hcr2 => ?_)
  have hm1_loc : m1.locals = cur.locals := by
    have := call0_none_locals cur (ofString "merkleize_progressive") _ (by rw [hm1])
    rwa [hm1] at this
  refine worldEff_seq hnt2 hcr2
    (fun hnt_mx hcr_mx =>
      worldEff_call0_mix_in_length heff_m1
        (.var .local (ofString "out")) (.var .local (ofString "len")) (.var .local (ofString "out"))
        outw (by simp [evalHOLExact, toExact, hm1_loc, hout_lk]) hout_cov hnt_mx hcr_mx)
    (fun m2 _ heff_m2 _ _ => worldEff_return heff_m2 _)

private theorem worldEff_call0_htr_plist_chunks {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hAs0 : ArenaOK s0) (heff : WorldEff s0 cur Rl sszBufs hpGw)
    (rootsExp nExp lenExp outExp : ExpHOL 64) (nw outw : BitVec 64)
    (hn : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      nExp = some (.val (.word nw)))
    (hn_bound : nw.toNat < 2 ^ 46)
    (hout : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      outExp = some (.val (.word outw)))
    (hcov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_plist_chunks")
      [rootsExp, nExp, lenExp, outExp])).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_plist_chunks")
      [rootsExp, nExp, lenExp, outExp])).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_plist_chunks")
      [rootsExp, nExp, lenExp, outExp])).2 Rl sszBufs hpGw := by
  refine worldEff_call0_eff heff (ofString "htr_plist_chunks") [rootsExp, nExp, lenExp, outExp]
    _ _ _ lookup_htr_plist_chunks (fun callee vals hargs hl hnt_e hres_e => ?_) hnt hcr
  rw [heff.code] at hl
  obtain ⟨rw0, nw', lw, ow, rfl, _, hn', _, ho⟩ :=
    lookupCode_four_words (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) lookup_htr_plist_chunks hl
  have hnw_eq : nw' = nw ∧ ow = outw := by
    rw [evalListHOLFinite_eq_toExact] at hargs
    simp only [evalListHOLExact, hn, hout] at hargs
    rcases hr0 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) rootsExp with _ | vr
    · simp [hr0] at hargs
    · rcases hl0 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) lenExp with _ | vl
      · simp [hr0, hl0] at hargs
      · simp only [hr0, hl0] at hargs
        injection hargs with h0
        injection h0 with _ h1
        injection h1 with h2 h3
        injection h2 with h2'; injection h2' with h2''
        injection h3 with _ h4
        injection h4 with h4' _; injection h4' with h4''; injection h4'' with h4'''
        exact ⟨h2''.symm, h4'''.symm⟩
  obtain ⟨rfl, rfl⟩ := hnw_eq
  exact worldEff_htr_plist_chunks s0 (callEntryStateHOLFinite cur callee) hAs0
    (heff.locals_clock _ _) hn' hn_bound ho hcov hnt_e hres_e

private theorem worldEff_htr_list_roots {F : Type}
    (s0 cur : PanSemStateFiniteExact 64 F) {Rl : List Ivl}
    (hAs0 : ArenaOK s0) (heff_cur : WorldEff s0 cur Rl sszBufs hpGw)
    {nw outw : BitVec 64}
    (hn_lk : cur.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hn_bound : nw.toNat < 2 ^ 58)
    (hout_lk : cur.locals.lookup (ofString "out") = some (.val (.word outw)))
    (hout_cov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_list_roots)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_list_roots)).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_list_roots)).2 Rl sszBufs hpGw := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_htr_list_roots,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_seq hnt (Or.inr (Or.inr (Or.inr hres)))
    (fun hnt1 hcr1 =>
      worldEff_call0_merkleize hAs0 heff_cur
        (.var .local (ofString "roots")) (.var .local (ofString "n"))
        (.var .local (ofString "lim")) (.var .local (ofString "out"))
        nw outw
        (by simp [evalHOLExact, toExact, hn_lk]) hn_bound
        (by simp [evalHOLExact, toExact, hout_lk]) hout_cov hnt1 hcr1)
    (fun m1 hm1 heff_m1 hnt2 hcr2 => ?_)
  have hm1_loc : m1.locals = cur.locals := by
    have := call0_none_locals cur (ofString "merkleize") _ (by rw [hm1])
    rwa [hm1] at this
  refine worldEff_seq hnt2 hcr2
    (fun hnt_mx hcr_mx =>
      worldEff_call0_mix_in_length heff_m1
        (.var .local (ofString "out")) (.var .local (ofString "n")) (.var .local (ofString "out"))
        outw (by simp [evalHOLExact, toExact, hm1_loc, hout_lk]) hout_cov hnt_mx hcr_mx)
    (fun m2 _ heff_m2 _ _ => worldEff_return heff_m2 _)

private theorem lookupCode_two_words_any {fname p1 p2 : MlS} {body : ProgHOL 64} {retShape : ShapeHOL}
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

private theorem worldEff_htr_pbytes {F : Type}
    (s0 cur : PanSemStateFiniteExact 64 F) {Rl : List Ivl}
    (hAs0 : ArenaOK s0) (heff_cur : WorldEff s0 cur Rl sszBufs hpGw)
    {outw : BitVec 64}
    (hout_lk : cur.locals.lookup (ofString "out") = some (.val (.word outw)))
    (hout_cov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_pbytes)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_pbytes)).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_pbytes)).2 Rl sszBufs hpGw := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_htr_pbytes,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_decCall_heap_mark heff_cur (ofString "mark") hnt (Or.inr (Or.inr (Or.inr hres)))
    (fun markw m1 _ _ hmark_al hmark_lo hmark_hi hm1_eq heff_m1 hnt1 hcr1 => ?_)
  have hm1_out : m1.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hout_lk,
      show ofString "mark" ≠ ofString "out" by decide]
  have hm1_mark : m1.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  refine worldEff_decCall_eff heff_m1 (ofString "pk") (.comb [.one, .one]) (ofString "pack_bytes")
    [.var .local (ofString "p"), .var .local (ofString "n")]
    _ _ _ lookup_pack_bytes
    (fun callee vals _ _ hnt_pk hres_pk =>
      worldEff_pack_bytes s0 (callEntryStateHOLFinite m1 callee) (heff_m1.locals_clock _ _) hnt_pk hres_pk)
    (fun callee vals rv cpost hargs hl hrun _ heff_cp hnt2 hcr2 => ?_)
    hnt1 hcr1
  rw [heff_m1.code] at hl
  obtain ⟨pw, nw, rfl, _, hnw_c⟩ := lookupCode_two_words_any (by decide) lookup_pack_bytes hl
  have hnw_callee : (callEntryStateHOLFinite m1 callee).locals.lookup (ofString "n") = some (.val (.word nw)) :=
    hnw_c
  obtain ⟨bufw, rfl, hcnt_lt⟩ :=
    pack_bytes_ret (heff_m1.locals_clock _ _) nw hnw_callee rv
      (congrArg Prod.fst hrun)
  let m2 := setVarHOLFinite (ofString "pk")
    (.rStruct [.val (.word bufw), .val (.word ((nw + 31#64) >>> 5#64))])
    { cpost with locals := m1.locals }
  have heff_m2 : WorldEff s0 m2 Rl sszBufs hpGw := heff_cp.locals_clock _ _
  have hm2_pk : m2.locals.lookup (ofString "pk") =
      some (.rStruct [.val (.word bufw), .val (.word ((nw + 31#64) >>> 5#64))]) := by
    simp [m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hm2_out : m2.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    simp [m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_out,
      show ofString "pk" ≠ ofString "out" by decide]
  have hm2_mark : m2.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    simp [m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_mark,
      show ofString "pk" ≠ ofString "mark" by decide]
  refine worldEff_seq hnt2 hcr2
    (fun hnt_pc hcr_pc =>
      worldEff_call0_htr_plist_chunks hAs0 heff_m2
        (.rfield 0 (.var .local (ofString "pk")))
        (.rfield 1 (.var .local (ofString "pk")))
        (.var .local (ofString "n"))
        (.var .local (ofString "out"))
        ((nw + 31#64) >>> 5#64) outw
        (by simp [evalHOLExact, toExact, hm2_pk])
        (by omega)
        (by simp [evalHOLExact, toExact, hm2_out])
        hout_cov hnt_pc hcr_pc)
    (fun m3 hm3 heff_m3 hnt3 hcr3 => ?_)
  have hm3_loc : m3.locals = m2.locals := by
    have := call0_none_locals m2 (ofString "htr_plist_chunks") _ (by rw [hm3])
    rwa [hm3] at this
  refine worldEff_seq hnt3 hcr3
    (fun hnt_hr _ =>
      (worldEff_call0_heap_release hAs0 heff_m3 (by decide) hp_no_gb
        (.var .local (ofString "mark")) markw
        (by simp [evalHOLExact, toExact, hm3_loc, hm2_mark])
        hmark_lo hmark_hi hmark_al hnt_hr).2.choose_spec.2)
    (fun m4 _ heff_m4 _ _ => worldEff_return heff_m4 _)

private theorem worldEff_call0_htr_pbytes {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hAs0 : ArenaOK s0) (heff : WorldEff s0 cur Rl sszBufs hpGw)
    (pExp nExp outExp : ExpHOL 64) (outw : BitVec 64)
    (hout : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      outExp = some (.val (.word outw)))
    (hcov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_pbytes")
      [pExp, nExp, outExp])).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_pbytes")
      [pExp, nExp, outExp])).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_pbytes")
      [pExp, nExp, outExp])).2 Rl sszBufs hpGw := by
  refine worldEff_call0_eff heff (ofString "htr_pbytes") [pExp, nExp, outExp]
    _ _ _ lookup_htr_pbytes (fun callee vals hargs hl hnt_e hres_e => ?_) hnt hcr
  rw [heff.code] at hl
  obtain ⟨pw, nw', ow, rfl, _, _, ho⟩ :=
    lookupCode_three_words (by decide) (by decide) (by decide) lookup_htr_pbytes hl
  obtain ⟨v0, v1, hv⟩ := evalList3_last_word hout hargs
  injection hv with _ hv1; injection hv1 with _ hv2; injection hv2 with hv3 _
  injection hv3 with hv4; injection hv4 with how_eq
  subst how_eq
  exact worldEff_htr_pbytes s0 (callEntryStateHOLFinite cur callee) hAs0
    (heff.locals_clock _ _) ho hcov hnt_e hres_e

private theorem worldEff_htr_bytes_list {F : Type}
    (s0 cur : PanSemStateFiniteExact 64 F) {Rl : List Ivl}
    (hAs0 : ArenaOK s0) (heff_cur : WorldEff s0 cur Rl sszBufs hpGw)
    {outw : BitVec 64}
    (hout_lk : cur.locals.lookup (ofString "out") = some (.val (.word outw)))
    (hout_cov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_bytes_list)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_bytes_list)).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_bytes_list)).2 Rl sszBufs hpGw := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_htr_bytes_list,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_decCall_heap_mark heff_cur (ofString "mark") hnt (Or.inr (Or.inr (Or.inr hres)))
    (fun markw m1 _ _ hmark_al hmark_lo hmark_hi hm1_eq heff_m1 hnt1 hcr1 => ?_)
  have hm1_out : m1.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hout_lk,
      show ofString "mark" ≠ ofString "out" by decide]
  have hm1_mark : m1.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  refine worldEff_decCall_eff heff_m1 (ofString "pk") (.comb [.one, .one]) (ofString "pack_bytes")
    [.var .local (ofString "p"), .var .local (ofString "n")]
    _ _ _ lookup_pack_bytes
    (fun callee vals _ _ hnt_pk hres_pk =>
      worldEff_pack_bytes s0 (callEntryStateHOLFinite m1 callee) (heff_m1.locals_clock _ _) hnt_pk hres_pk)
    (fun callee vals rv cpost _ hl hrun _ heff_cp hnt2 hcr2 => ?_)
    hnt1 hcr1
  rw [heff_m1.code] at hl
  obtain ⟨pw, nw, rfl, _, hnw_c⟩ := lookupCode_two_words_any (by decide) lookup_pack_bytes hl
  have hnw_callee : (callEntryStateHOLFinite m1 callee).locals.lookup (ofString "n") = some (.val (.word nw)) :=
    hnw_c
  obtain ⟨bufw, rfl, hcnt_lt⟩ :=
    pack_bytes_ret (heff_m1.locals_clock _ _) nw hnw_callee rv
      (congrArg Prod.fst hrun)
  let m2 := setVarHOLFinite (ofString "pk")
    (.rStruct [.val (.word bufw), .val (.word ((nw + 31#64) >>> 5#64))])
    { cpost with locals := m1.locals }
  have heff_m2 : WorldEff s0 m2 Rl sszBufs hpGw := heff_cp.locals_clock _ _
  have hm2_pk : m2.locals.lookup (ofString "pk") =
      some (.rStruct [.val (.word bufw), .val (.word ((nw + 31#64) >>> 5#64))]) := by
    simp [m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hm2_out : m2.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    simp [m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_out,
      show ofString "pk" ≠ ofString "out" by decide]
  have hm2_mark : m2.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    simp [m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_mark,
      show ofString "pk" ≠ ofString "mark" by decide]
  refine worldEff_seq hnt2 hcr2
    (fun hnt_mk hcr_mk =>
      worldEff_call0_merkleize hAs0 heff_m2
        (.rfield 0 (.var .local (ofString "pk")))
        (.rfield 1 (.var .local (ofString "pk")))
        (.var .local (ofString "limit_chunks"))
        (.var .local (ofString "out"))
        ((nw + 31#64) >>> 5#64) outw
        (by simp [evalHOLExact, toExact, hm2_pk])
        (by omega)
        (by simp [evalHOLExact, toExact, hm2_out])
        hout_cov hnt_mk hcr_mk)
    (fun m3 hm3 heff_m3 hnt3 hcr3 => ?_)
  have hm3_loc : m3.locals = m2.locals := by
    have := call0_none_locals m2 (ofString "merkleize") _ (by rw [hm3])
    rwa [hm3] at this
  refine worldEff_seq hnt3 hcr3
    (fun hnt_hr _ =>
      (worldEff_call0_heap_release hAs0 heff_m3 (by decide) hp_no_gb
        (.var .local (ofString "mark")) markw
        (by simp [evalHOLExact, toExact, hm3_loc, hm2_mark])
        hmark_lo hmark_hi hmark_al hnt_hr).2.choose_spec.2)
    (fun m4 hm4 heff_m4 hnt4 hcr4 => ?_)
  have hm4_loc : m4.locals = m3.locals := by
    have := call0_none_locals m3 (ofString "heap_release") _ (by rw [hm4])
    rwa [hm4] at this
  refine worldEff_seq hnt4 hcr4
    (fun hnt_mx hcr_mx =>
      worldEff_call0_mix_in_length heff_m4
        (.var .local (ofString "out")) (.var .local (ofString "n")) (.var .local (ofString "out"))
        outw (by simp [evalHOLExact, toExact, hm4_loc, hm3_loc, hm2_out]) hout_cov hnt_mx hcr_mx)
    (fun m5 _ heff_m5 _ _ => worldEff_return heff_m5 _)

private theorem worldEff_call0_htr_bytes_list {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hAs0 : ArenaOK s0) (heff : WorldEff s0 cur Rl sszBufs hpGw)
    (pExp nExp limExp outExp : ExpHOL 64) (outw : BitVec 64)
    (hout : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      outExp = some (.val (.word outw)))
    (hcov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_bytes_list")
      [pExp, nExp, limExp, outExp])).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_bytes_list")
      [pExp, nExp, limExp, outExp])).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_bytes_list")
      [pExp, nExp, limExp, outExp])).2 Rl sszBufs hpGw := by
  refine worldEff_call0_eff heff (ofString "htr_bytes_list") [pExp, nExp, limExp, outExp]
    _ _ _ lookup_htr_bytes_list (fun callee vals hargs hl hnt_e hres_e => ?_) hnt hcr
  rw [heff.code] at hl
  obtain ⟨pw, nw', lw, ow, rfl, _, _, _, ho⟩ :=
    lookupCode_four_words (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) lookup_htr_bytes_list hl
  have how_eq : ow = outw := by
    rw [evalListHOLFinite_eq_toExact] at hargs
    simp only [evalListHOLExact, hout] at hargs
    rcases hp0 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) pExp with _ | vp
    · simp [hp0] at hargs
    · rcases hn0 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) nExp with _ | vn
      · simp [hp0, hn0] at hargs
      · rcases hl0 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) limExp with _ | vl
        · simp [hp0, hn0, hl0] at hargs
        · simp only [hp0, hn0, hl0] at hargs
          injection hargs with h0
          injection h0 with _ h1
          injection h1 with _ h2
          injection h2 with _ h3
          injection h3 with h4 _; injection h4 with h4'; injection h4' with h4''
          exact h4''.symm
  subst how_eq
  exact worldEff_htr_bytes_list s0 (callEntryStateHOLFinite cur callee) hAs0
    (heff.locals_clock _ _) ho hcov hnt_e hres_e

private theorem worldEff_htr_bytes_vector {F : Type}
    (s0 cur : PanSemStateFiniteExact 64 F) {Rl : List Ivl}
    (hAs0 : ArenaOK s0) (heff_cur : WorldEff s0 cur Rl sszBufs hpGw)
    {nw outw : BitVec 64}
    (hn_lk : cur.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hout_lk : cur.locals.lookup (ofString "out") = some (.val (.word outw)))
    (hout_cov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_bytes_vector)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_bytes_vector)).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_bytes_vector)).2 Rl sszBufs hpGw := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_htr_bytes_vector,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_seq hnt (Or.inr (Or.inr (Or.inr hres)))
    (fun hnt_i hcr_i =>
      worldEff_ite heff_cur _ hnt_i hcr_i
        (fun cw hcw hcw_ne hnt_y hcr_y => by
          have hn_le32 : nw.toNat ≤ 32 := by
            simp only [evalHOLExact, toExact, hn_lk, Compiler.Encoders.Asm.wordCmpHOL] at hcw
            by_cases hlt : 32#64 < nw
            · simp only [hlt, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hcw
              injection hcw with h1; injection h1 with h2; injection h2 with h3
              exact absurd h3.symm hcw_ne
            · have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
              exact Nat.not_lt.1 (fun h => hlt (BitVec.lt_def.2 (by omega)))
          refine worldEff_seq hnt_y hcr_y
            (fun hnt_mz hcr_mz =>
              worldEff_call0_funByteEff heff_cur funByteEff_memzero _ [(outw.toNat, 32)]
                (fun vals hargs i hi _ => by
                  rw [evalListHOLFinite_eq_toExact] at hargs
                  simp only [evalListHOLExact, evalHOLExact, toExact, hout_lk] at hargs
                  injection hargs with hargs_eq; subst hargs_eq
                  simp only [valWordNat, List.mem_singleton] at hi; subst hi
                  exact ⟨(outw.toNat, 32), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
                (fun iv hiv _ => by
                  simp only [List.mem_singleton] at hiv; subst hiv
                  exact outIvlCovered_to_world hout_cov 32 le_rfl)
                hnt_mz hcr_mz)
            (fun m1 hm1 heff_m1 hnt_s2 hcr_s2 => by
              have hm1_loc : m1.locals = cur.locals := by
                have := call0_none_locals cur (ofString "memzero") _ (by rw [hm1])
                rwa [hm1] at this
              refine worldEff_seq hnt_s2 hcr_s2
                (fun hnt_cp hcr_cp =>
                  (worldEff_call0_memcpy_word heff_m1
                    (.var .local (ofString "out")) (.var .local (ofString "p")) (.var .local (ofString "n"))
                    outw nw
                    (by simp [evalHOLExact, toExact, hm1_loc, hout_lk])
                    (by simp [evalHOLExact, toExact, hm1_loc, hn_lk])
                    (fun _ _ => outIvlCovered_to_world hout_cov nw.toNat hn_le32)
                    hnt_cp hcr_cp).1)
                (fun m2 _ heff_m2 _ _ => worldEff_return heff_m2 _)))
        (fun _ _ _ => worldEff_skip heff_cur))
    (fun m0 hm0 heff_m0 hnt0 hcr0 => ?_)
  have hm0_loc : m0.locals = cur.locals := by
    rw [evaluateHOLFiniteState_ite] at hm0
    have hcond_ev : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
        (.cmp .notLower (.const 32#64) (.var .local (ofString "n"))) =
        some (.val (.word (if ¬ (32#64 < nw) then 1#64 else 0#64))) := by
      simp only [evalHOLExact, toExact, hn_lk, Compiler.Encoders.Asm.wordCmpHOL]
      by_cases hlt : 32#64 < nw <;> simp [hlt]
    rw [hcond_ev] at hm0; dsimp only at hm0
    by_cases hlt : 32#64 < nw
    · simp only [hlt, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hm0
      rw [if_pos (show (0#64 : BitVec 64) = 0 by decide), evaluateHOLFiniteState_skip] at hm0
      exact congrArg PanSemStateFiniteExact.locals (Prod.mk.inj hm0).2.symm
    · simp only [hlt, not_false_eq_true, decide_true, ↓reduceIte] at hm0
      rw [if_neg (show ¬ ((1#64 : BitVec 64) = 0) by decide)] at hm0
      rw [evaluateHOLFiniteState_seq_line780] at hm0
      rcases h1 : evaluateHOLFiniteState cur _ with ⟨r1, s1⟩
      rw [h1] at hm0
      cases r1 with
      | some r => cases r with
        | returned v => exact False.elim (call0_never_returned cur _ _ v (by rw [h1]))
        | _ => simp at hm0
      | none =>
        dsimp only at hm0
        rw [evaluateHOLFiniteState_seq_line780] at hm0
        rcases h2 : evaluateHOLFiniteState s1 _ with ⟨r2, s2⟩
        rw [h2] at hm0
        cases r2 with
        | some r => cases r with
          | returned v => exact False.elim (call0_never_returned s1 _ _ v (by rw [h2]))
          | _ => simp at hm0
        | none =>
          dsimp only at hm0
          rw [evaluateHOLFiniteState_return] at hm0
          simp only [evalHOLExact, shapeOfHOLExact] at hm0
          split at hm0 <;> simp at hm0
  refine worldEff_decCall_heap_mark heff_m0 (ofString "mark") hnt0 hcr0
    (fun markw m1 _ _ hmark_al hmark_lo hmark_hi hm1_eq heff_m1 hnt1 hcr1 => ?_)
  have hm1_out : m1.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm0_loc, hout_lk,
      show ofString "mark" ≠ ofString "out" by decide]
  have hm1_mark : m1.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  refine worldEff_decCall_eff heff_m1 (ofString "pk") (.comb [.one, .one]) (ofString "pack_bytes")
    [.var .local (ofString "p"), .var .local (ofString "n")]
    _ _ _ lookup_pack_bytes
    (fun callee vals _ _ hnt_pk hres_pk =>
      worldEff_pack_bytes s0 (callEntryStateHOLFinite m1 callee) (heff_m1.locals_clock _ _) hnt_pk hres_pk)
    (fun callee vals rv cpost _ hl hrun _ heff_cp hnt2 hcr2 => ?_)
    hnt1 hcr1
  rw [heff_m1.code] at hl
  obtain ⟨pw, nw', rfl, _, hnw_c⟩ := lookupCode_two_words_any (by decide) lookup_pack_bytes hl
  have hnw_callee : (callEntryStateHOLFinite m1 callee).locals.lookup (ofString "n") = some (.val (.word nw')) :=
    hnw_c
  obtain ⟨bufw, rfl, hcnt_lt⟩ :=
    pack_bytes_ret (heff_m1.locals_clock _ _) nw' hnw_callee rv
      (congrArg Prod.fst hrun)
  let m2 := setVarHOLFinite (ofString "pk")
    (.rStruct [.val (.word bufw), .val (.word ((nw' + 31#64) >>> 5#64))])
    { cpost with locals := m1.locals }
  have heff_m2 : WorldEff s0 m2 Rl sszBufs hpGw := heff_cp.locals_clock _ _
  have hm2_pk : m2.locals.lookup (ofString "pk") =
      some (.rStruct [.val (.word bufw), .val (.word ((nw' + 31#64) >>> 5#64))]) := by
    simp [m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hm2_out : m2.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    simp [m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_out,
      show ofString "pk" ≠ ofString "out" by decide]
  have hm2_mark : m2.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    simp [m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_mark,
      show ofString "pk" ≠ ofString "mark" by decide]
  refine worldEff_seq hnt2 hcr2
    (fun hnt_mk hcr_mk =>
      worldEff_call0_merkleize hAs0 heff_m2
        (.rfield 0 (.var .local (ofString "pk")))
        (.rfield 1 (.var .local (ofString "pk")))
        (.rfield 1 (.var .local (ofString "pk")))
        (.var .local (ofString "out"))
        ((nw' + 31#64) >>> 5#64) outw
        (by simp [evalHOLExact, toExact, hm2_pk])
        (by omega)
        (by simp [evalHOLExact, toExact, hm2_out])
        hout_cov hnt_mk hcr_mk)
    (fun m3 hm3 heff_m3 hnt3 hcr3 => ?_)
  have hm3_loc : m3.locals = m2.locals := by
    have := call0_none_locals m2 (ofString "merkleize") _ (by rw [hm3])
    rwa [hm3] at this
  refine worldEff_seq hnt3 hcr3
    (fun hnt_hr _ =>
      (worldEff_call0_heap_release hAs0 heff_m3 (by decide) hp_no_gb
        (.var .local (ofString "mark")) markw
        (by simp [evalHOLExact, toExact, hm3_loc, hm2_mark])
        hmark_lo hmark_hi hmark_al hnt_hr).2.choose_spec.2)
    (fun m4 _ heff_m4 _ _ => worldEff_return heff_m4 _)

private theorem worldEff_call0_htr_bytes_vector {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hAs0 : ArenaOK s0) (heff : WorldEff s0 cur Rl sszBufs hpGw)
    (pExp nExp outExp : ExpHOL 64) (outw : BitVec 64)
    (hout : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      outExp = some (.val (.word outw)))
    (hcov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_bytes_vector")
      [pExp, nExp, outExp])).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_bytes_vector")
      [pExp, nExp, outExp])).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_bytes_vector")
      [pExp, nExp, outExp])).2 Rl sszBufs hpGw := by
  refine worldEff_call0_eff heff (ofString "htr_bytes_vector") [pExp, nExp, outExp]
    _ _ _ lookup_htr_bytes_vector (fun callee vals hargs hl hnt_e hres_e => ?_) hnt hcr
  rw [heff.code] at hl
  obtain ⟨pw, nw', ow, rfl, _, hn', ho⟩ :=
    lookupCode_three_words (by decide) (by decide) (by decide) lookup_htr_bytes_vector hl
  obtain ⟨v0, v1, hv⟩ := evalList3_last_word hout hargs
  injection hv with _ hv1; injection hv1 with _ hv2; injection hv2 with hv3 _
  injection hv3 with hv4; injection hv4 with how_eq
  subst how_eq
  exact worldEff_htr_bytes_vector s0 (callEntryStateHOLFinite cur callee) hAs0
    (heff.locals_clock _ _) hn' ho hcov hnt_e hres_e

private theorem worldEff_htr_pcontainer {F : Type}
    (s0 cur : PanSemStateFiniteExact 64 F) {Rl : List Ivl}
    (hAs0 : ArenaOK s0) (heff_cur : WorldEff s0 cur Rl sszBufs hpGw)
    {nw outw : BitVec 64}
    (hn_lk : cur.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hn_bound : nw.toNat ≤ 256)
    (hout_lk : cur.locals.lookup (ofString "out") = some (.val (.word outw)))
    (hout_cov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_pcontainer)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_pcontainer)).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_pcontainer)).2 Rl sszBufs hpGw := by
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_htr_pcontainer,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_decCall_heap_mark heff_cur (ofString "mark") hnt (Or.inr (Or.inr (Or.inr hres)))
    (fun markw m1 _ _ hmark_al hmark_lo hmark_hi hm1_eq heff_m1 hnt1 hcr1 => ?_)
  have hm1_n : m1.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hn_lk,
      show ofString "mark" ≠ ofString "n" by decide]
  have hm1_out : m1.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hout_lk,
      show ofString "mark" ≠ ofString "out" by decide]
  have hm1_mark : m1.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  refine worldEff_decCall_alloc heff_m1 (by decide) (ofString "tmp") _ hnt1 hcr1
    (fun tmpw tszw m2 htsz_ev _ hm2_loc _ heff_m2 _ _ htmp_lo htmp_end _ _ hnt2 hcr2 => ?_)
  have htsz_eq : tszw = 64#64 := by
    simp [evalHOLExact] at htsz_ev; exact htsz_ev.symm
  subst htsz_eq
  have htmp_cap : tmpw.toNat + 64 ≤ heapLimit := by
    have : (64#64 : BitVec 64).toNat = 64 := rfl
    omega
  have hm2_tmp : m2.locals.lookup (ofString "tmp") = some (.val (.word tmpw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hm2_n : m2.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_n,
      show ofString "tmp" ≠ ofString "n" by decide]
  have hm2_out : m2.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_out,
      show ofString "tmp" ≠ ofString "out" by decide]
  have hm2_mark : m2.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_mark,
      show ofString "tmp" ≠ ofString "mark" by decide]
  refine worldEff_seq hnt2 hcr2
    (fun hnt_mp hcr_mp =>
      worldEff_call0_merkleize_progressive hAs0 heff_m2
        (.var .local (ofString "ch")) (.var .local (ofString "n")) (.var .local (ofString "tmp"))
        nw tmpw
        (by simp [evalHOLExact, toExact, hm2_n])
        (by omega)
        (by simp [evalHOLExact, toExact, hm2_tmp])
        (Or.inr ⟨htmp_lo, by omega⟩)
        hnt_mp hcr_mp)
    (fun m3 hm3 heff_m3 hnt3 hcr3 => ?_)
  have hm3_loc : m3.locals = m2.locals := by
    have := call0_none_locals m2 (ofString "merkleize_progressive") _ (by rw [hm3])
    rwa [hm3] at this
  refine worldEff_dec heff_m3 (ofString "act") .one _ hnt3 hcr3
    (fun vact hvact _ hnt4 hcr4 => ?_)
  have hvact_eq : vact = .val (.word (tmpw + 32#64)) := by
    simp [evalHOLExact, evalListHOLExact, toExact, hm3_loc, hm2_tmp,
      valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr] at hvact
    exact hvact.symm
  subst hvact_eq
  let actw := tmpw + 32#64
  have hact_nat : actw.toNat = tmpw.toNat + 32 := by
    have : (32#64 : BitVec 64).toNat = 32 := rfl
    exact BitVec.toNat_add_of_lt (by omega)
  let m4 := setVarHOLFinite (ofString "act") (.val (.word actw)) m3
  have heff_m4 : WorldEff s0 m4 Rl sszBufs hpGw := heff_m3.locals_clock _ _
  have hm4_act : m4.locals.lookup (ofString "act") = some (.val (.word actw)) := by
    simp [m4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hm4_tmp : m4.locals.lookup (ofString "tmp") = some (.val (.word tmpw)) := by
    simp [m4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm3_loc, hm2_tmp,
      show ofString "act" ≠ ofString "tmp" by decide]
  have hm4_n : m4.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    simp [m4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm3_loc, hm2_n,
      show ofString "act" ≠ ofString "n" by decide]
  have hm4_out : m4.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    simp [m4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm3_loc, hm2_out,
      show ofString "act" ≠ ofString "out" by decide]
  have hm4_mark : m4.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    simp [m4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm3_loc, hm2_mark,
      show ofString "act" ≠ ofString "mark" by decide]
  refine worldEff_seq hnt4 hcr4
    (fun hnt_mz hcr_mz =>
      worldEff_call0_funByteEff heff_m4 funByteEff_memzero _ [(actw.toNat, 32)]
        (fun vals hargs i hi _ => by
          rw [evalListHOLFinite_eq_toExact] at hargs
          simp only [evalListHOLExact, evalHOLExact, toExact, hm4_act] at hargs
          injection hargs with hargs_eq; subst hargs_eq
          simp only [valWordNat, List.mem_singleton] at hi; subst hi
          exact ⟨(actw.toNat, 32), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
        (fun iv hiv _ => by
          simp only [List.mem_singleton] at hiv; subst hiv
          exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
        hnt_mz hcr_mz)
    (fun m5 hm5 heff_m5 hnt5 hcr5 => ?_)
  have hm5_loc : m5.locals = m4.locals := by
    have := call0_none_locals m4 (ofString "memzero") _ (by rw [hm5])
    rwa [hm5] at this
  refine worldEff_dec heff_m5 (ofString "i") .one _ hnt5 hcr5
    (fun vi hvi _ hnt6 hcr6 => ?_)
  have hvi_eq : vi = .val (.word 0#64) := by
    simp [evalHOLExact] at hvi; exact hvi.symm
  subst hvi_eq
  let m6 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) m5
  have heff_m6 : WorldEff s0 m6 Rl sszBufs hpGw := heff_m5.locals_clock _ _
  let Inv : PanSemStateFiniteExact 64 F → Prop := fun st =>
    st.locals.lookup (ofString "act") = some (.val (.word actw)) ∧
    st.locals.lookup (ofString "tmp") = some (.val (.word tmpw)) ∧
    st.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
    st.locals.lookup (ofString "out") = some (.val (.word outw)) ∧
    st.locals.lookup (ofString "mark") = some (.val (.word markw)) ∧
    ∃ iw : BitVec 64, st.locals.lookup (ofString "i") = some (.val (.word iw)) ∧ iw.toNat ≤ nw.toNat
  have hInv_m6 : Inv m6 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, 0#64, ?_, Nat.zero_le _⟩ <;>
      simp [m6, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm5_loc,
        hm4_act, hm4_tmp, hm4_n, hm4_out, hm4_mark,
        show ofString "i" ≠ ofString "act" by decide,
        show ofString "i" ≠ ofString "tmp" by decide,
        show ofString "i" ≠ ofString "n" by decide,
        show ofString "i" ≠ ofString "out" by decide,
        show ofString "i" ≠ ofString "mark" by decide]
  let bodyP : ProgHOL 64 :=
    .seq
      (.storeByte
        (.op .add [.var .local (ofString "act"), .shift .lsr (.var .local (ofString "i")) (.const 3#64)])
        (.op .or
          [.loadByte (.op .add [.var .local (ofString "act"), .shift .lsr (.var .local (ofString "i")) (.const 3#64)]),
           .shift .lsl (.const 1#64) (.op .and [.var .local (ofString "i"), .const 7#64])]))
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))
  have hsb_ctrl : ∀ (t : PanSemStateFiniteExact 64 F) d v,
      ((evaluateHOLFiniteState t (.storeByte d v)).1 = none ∧
        (evaluateHOLFiniteState t (.storeByte d v)).2.locals = t.locals) ∨
      (evaluateHOLFiniteState t (.storeByte d v)).1 = some .error := by
    intro t d v
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split <;> simp
      · simp
    · simp
  have hsb_nb : ∀ t : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState t bodyP).1 ≠ some .break := by
    intro t
    dsimp only [bodyP]
    refine seq_ne_break t ?_ (fun mid _ => assign_local_ne_break mid _ _)
    rcases hsb_ctrl t _ _ with ⟨hnone, _⟩ | herr <;> [rw [hnone]; rw [herr]] <;> simp
  have hstepP : ∀ u (cw : BitVec 64),
      @evalHOLFinite 64 F _ u (fun a => Classical.propDecidable (u.memaddrs a))
        (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n"))) = some (.val (.word cw)) →
      cw ≠ 0 →
      WorldEff s0 (decClockHOLFinite u) Rl sszBufs hpGw → Inv (decClockHOLFinite u) →
      (evaluateHOLFiniteState (decClockHOLFinite u) bodyP).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState (decClockHOLFinite u) bodyP).1 →
      WorldEff s0 (evaluateHOLFiniteState (decClockHOLFinite u) bodyP).2 Rl sszBufs hpGw ∧
      (((evaluateHOLFiniteState (decClockHOLFinite u) bodyP).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite u) bodyP).1 = some .continue) →
        Inv (evaluateHOLFiniteState (decClockHOLFinite u) bodyP).2) := by
    intro u cw hcw hcw_ne heff_ud ⟨hu_act, hu_tmp, hu_n, hu_out, hu_mark, iw, hu_i, hi_le⟩ hnt_b hcr_b
    let ud := decClockHOLFinite u
    have hu_i0 : u.locals.lookup (ofString "i") = some (.val (.word iw)) := hu_i
    have hu_n0 : u.locals.lookup (ofString "n") = some (.val (.word nw)) := hu_n
    have hud_act : ud.locals.lookup (ofString "act") = some (.val (.word actw)) := hu_act
    have hud_tmp : ud.locals.lookup (ofString "tmp") = some (.val (.word tmpw)) := hu_tmp
    have hud_n : ud.locals.lookup (ofString "n") = some (.val (.word nw)) := hu_n
    have hud_out : ud.locals.lookup (ofString "out") = some (.val (.word outw)) := hu_out
    have hud_mark : ud.locals.lookup (ofString "mark") = some (.val (.word markw)) := hu_mark
    have hud_i : ud.locals.lookup (ofString "i") = some (.val (.word iw)) := hu_i
    have hi_lt : iw.toNat < nw.toNat := by
      have hi63 : iw.toNat < 2 ^ 63 := by omega
      have hn63 : nw.toNat < 2 ^ 63 := by omega
      rw [evalHOLFinite_eq_toExact] at hcw
      simp only [evalHOLExact, toExact, hu_i0, hu_n0, Compiler.Encoders.Asm.wordCmpHOL,
        holAsmSignedLess_small iw nw hi63 hn63] at hcw
      by_cases hlt : iw.toNat < nw.toNat
      · exact hlt
      · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte] at hcw
        injection hcw with h1; injection h1 with h2; injection h2 with h3
        exact absurd h3.symm hcw_ne
    have hshr_nat : (iw >>> (3 : Nat)).toNat < 32 := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      omega
    have hwe_b : WorldEff s0 (evaluateHOLFiniteState ud bodyP).2 Rl sszBufs hpGw := by
      dsimp only [bodyP] at hnt_b hcr_b ⊢
      refine worldEff_seq hnt_b hcr_b
        (fun _ _ =>
          worldEff_storeByte heff_ud _ _ (fun x hx _ => by
            have hx_eq : x = actw + (iw >>> (3 : Nat)) := by
              have h3 : (3#64 : BitVec 64).toNat = 3 := rfl
              simp [evalHOLExact, evalListHOLExact, toExact, hu_act, hu_i, h3,
                valueIsWord, valueWord, wordOpHOL, wordOp, wordShiftHOL,
                List.all, List.map, Option.map, List.foldr] at hx
              exact hx.symm
            subst hx_eq
            have hx_nat : (actw + (iw >>> (3 : Nat))).toNat = actw.toNat + (iw >>> (3 : Nat)).toNat :=
              BitVec.toNat_add_of_lt (by omega)
            exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))
        (fun mid _ heff_mid _ _ => worldEff_assign_local heff_mid _ _)
    refine ⟨hwe_b, fun hfl_b => ?_⟩
    dsimp only [bodyP] at hfl_b ⊢
    rw [evaluateHOLFiniteState_seq_line780] at hfl_b ⊢
    generalize hsb : evaluateHOLFiniteState (decClockHOLFinite u)
      (.storeByte
        (.op .add [.var .local (ofString "act"), .shift .lsr (.var .local (ofString "i")) (.const 3#64)])
        (.op .or
          [.loadByte (.op .add [.var .local (ofString "act"), .shift .lsr (.var .local (ofString "i")) (.const 3#64)]),
           .shift .lsl (.const 1#64) (.op .and [.var .local (ofString "i"), .const 7#64])])) = sbOut at hfl_b ⊢
    rcases sbOut with ⟨rsb, b1⟩
    have hctrl := hsb_ctrl (decClockHOLFinite u)
      (.op .add [.var .local (ofString "act"), .shift .lsr (.var .local (ofString "i")) (.const 3#64)])
      (.op .or
        [.loadByte (.op .add [.var .local (ofString "act"), .shift .lsr (.var .local (ofString "i")) (.const 3#64)]),
         .shift .lsl (.const 1#64) (.op .and [.var .local (ofString "i"), .const 7#64])])
    rw [hsb] at hctrl
    rcases hctrl with ⟨hsb_none, hb1_l⟩ | hsb_err
    · dsimp only at hsb_none hb1_l hfl_b ⊢
      subst hsb_none
      dsimp only at hfl_b ⊢
      have hb1_i : b1.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hb1_l]; exact hu_i
      have hi1_ev : @evalHOLExact 64 F _ b1.toExact (fun a => Classical.propDecidable (b1.memaddrs a))
          (.op .add [.var .local (ofString "i"), .const 1#64]) = some (.val (.word (iw + 1#64))) := by
        simp [evalHOLExact, evalListHOLExact, toExact, hb1_i,
          valueIsWord, valueWord, wordOpHOL, wordOp,
          List.all, List.map, Option.map, List.foldr]
      have hvv_i : isValidValueHOLFinite b1 .local (ofString "i") (.val (.word (iw + 1#64))) = true := by
        simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, toExact, hb1_i,
          shapeOfHOLExact, shapeEqHOL]
      have ha_i : evaluateHOLFiniteState b1
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])) =
          (none, setVarHOLFinite (ofString "i") (.val (.word (iw + 1#64))) b1) := by
        rw [evaluateHOLFiniteState_assign, hi1_ev]; dsimp only; rw [if_pos hvv_i]; rfl
      rw [ha_i]
      have hi_add : (iw + 1#64).toNat = iw.toNat + 1 := by
        have : (1#64 : BitVec 64).toNat = 1 := rfl
        exact BitVec.toNat_add_of_lt (by omega)
      refine ⟨?_, ?_, ?_, ?_, ?_, iw + 1#64, ?_, by omega⟩ <;>
        simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hb1_l,
          hu_act, hu_tmp, hu_n, hu_out, hu_mark,
          show ofString "i" ≠ ofString "act" by decide,
          show ofString "i" ≠ ofString "tmp" by decide,
          show ofString "i" ≠ ofString "n" by decide,
          show ofString "i" ≠ ofString "out" by decide,
          show ofString "i" ≠ ofString "mark" by decide]
    · dsimp only at hsb_err hfl_b ⊢
      subst hsb_err
      rcases hfl_b with h | h <;> simp at h
  refine worldEff_seq hnt6 hcr6
    (fun hnt_w hcr_w =>
      (worldEff_while_cond_post (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n")))
        Inv (fun u hu => hu) hstepP m6.clock m6 rfl heff_m6 hInv_m6 hnt_w hcr_w).1)
    (fun m7 hm7 heff_m7 hnt7 hcr7 => ?_)
  have hInv_m7 : Inv m7 := by
    have hp := (worldEff_while_cond_post (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n")))
      Inv (fun u hu => hu) hstepP m6.clock m6 rfl heff_m6 hInv_m6
      (by rw [hm7]; simp) (by rw [hm7]; exact Or.inl rfl)).2 (by rw [hm7]) (fun t _ => hsb_nb t)
    rw [hm7] at hp; exact hp.1
  obtain ⟨hm7_act, hm7_tmp, _, hm7_out, hm7_mark, _⟩ := hInv_m7
  refine worldEff_seq hnt7 hcr7
    (fun hnt_sp hcr_sp =>
      worldEff_call0_funByteEff heff_m7 funByteEff_sha256_pair _ [(outw.toNat, 32)]
        (fun vals hargs i hi _ => by
          have hlast : @evalHOLExact 64 F _ m7.toExact (fun a => Classical.propDecidable (m7.memaddrs a))
              (.var .local (ofString "out")) = some (.val (.word outw)) := by
            simp [evalHOLExact, toExact, hm7_out]
          obtain ⟨v0, v1, rfl⟩ := evalList3_last_word hlast hargs
          simp only [valWordNat, List.mem_singleton] at hi; subst hi
          exact ⟨(outw.toNat, 32), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
        (fun iv hiv _ => by
          simp only [List.mem_singleton] at hiv; subst hiv
          exact outIvlCovered_to_world hout_cov 32 le_rfl)
        hnt_sp hcr_sp)
    (fun m8 hm8 heff_m8 hnt8 hcr8 => ?_)
  have hm8_loc : m8.locals = m7.locals := by
    have := call0_none_locals m7 (ofString "sha256_pair") _ (by rw [hm8])
    rwa [hm8] at this
  refine worldEff_seq hnt8 hcr8
    (fun hnt_hr _ =>
      (worldEff_call0_heap_release hAs0 heff_m8 (by decide) hp_no_gb
        (.var .local (ofString "mark")) markw
        (by simp [evalHOLExact, toExact, hm8_loc, hm7_mark])
        hmark_lo hmark_hi hmark_al hnt_hr).2.choose_spec.2)
    (fun m9 _ heff_m9 _ _ => worldEff_return heff_m9 _)

private theorem worldEff_call0_htr_pcontainer {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hAs0 : ArenaOK s0) (heff : WorldEff s0 cur Rl sszBufs hpGw)
    (chExp nExp outExp : ExpHOL 64) (nw outw : BitVec 64)
    (hn : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      nExp = some (.val (.word nw)))
    (hn_bound : nw.toNat ≤ 256)
    (hout : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      outExp = some (.val (.word outw)))
    (hcov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_pcontainer")
      [chExp, nExp, outExp])).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_pcontainer")
      [chExp, nExp, outExp])).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_pcontainer")
      [chExp, nExp, outExp])).2 Rl sszBufs hpGw := by
  refine worldEff_call0_eff heff (ofString "htr_pcontainer") [chExp, nExp, outExp]
    _ _ _ lookup_htr_pcontainer (fun callee vals hargs hl hnt_e hres_e => ?_) hnt hcr
  rw [heff.code] at hl
  obtain ⟨chw, nw', ow, rfl, _, hn', ho⟩ :=
    lookupCode_three_words (by decide) (by decide) (by decide) lookup_htr_pcontainer hl
  have hnw_eq : nw' = nw ∧ ow = outw := by
    rw [evalListHOLFinite_eq_toExact] at hargs
    simp only [evalListHOLExact, hn, hout] at hargs
    rcases hc0 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) chExp with _ | vc
    · simp [hc0] at hargs
    · simp only [hc0] at hargs
      injection hargs with h0
      injection h0 with _ h1
      injection h1 with h2 h3
      injection h2 with h2'; injection h2' with h2''
      injection h3 with h4 _; injection h4 with h4'; injection h4' with h4''
      exact ⟨h2''.symm, h4''.symm⟩
  obtain ⟨rfl, rfl⟩ := hnw_eq
  exact worldEff_htr_pcontainer s0 (callEntryStateHOLFinite cur callee) hAs0
    (heff.locals_clock _ _) hn' hn_bound ho hcov hnt_e hres_e

private theorem worldEff_htr_withdrawal {F : Type}
    (s0 cur : PanSemStateFiniteExact 64 F) {Rl : List Ivl}
    (hAs0 : ArenaOK s0) (heff_cur : WorldEff s0 cur Rl sszBufs hpGw)
    {outw : BitVec 64}
    (hout_lk : cur.locals.lookup (ofString "out") = some (.val (.word outw)))
    (hout_cov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_withdrawal)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_withdrawal)).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_withdrawal)).2 Rl sszBufs hpGw := by
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_htr_withdrawal,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_decCall_heap_mark heff_cur (ofString "mark") hnt (Or.inr (Or.inr (Or.inr hres)))
    (fun markw m1 _ _ hmark_al hmark_lo hmark_hi hm1_eq heff_m1 hnt1 hcr1 => ?_)
  have hm1_out : m1.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hout_lk,
      show ofString "mark" ≠ ofString "out" by decide]
  have hm1_mark : m1.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  refine worldEff_decCall_alloc heff_m1 (by decide) (ofString "ch") _ hnt1 hcr1
    (fun chw szw m2 hsz_ev _ hm2_loc _ heff_m2 _ _ hch_lo hch_end _ _ hnt2 hcr2 => ?_)
  have hsz_eq : szw = 128#64 := by
    simp [evalHOLExact, evalListHOLExact, valueIsWord, valueWord, panOpHOL] at hsz_ev
    exact hsz_ev.symm
  subst hsz_eq
  have hch_cap : chw.toNat + 128 ≤ heapLimit := by
    have : (128#64 : BitVec 64).toNat = 128 := rfl
    omega
  have hm2_ch : m2.locals.lookup (ofString "ch") = some (.val (.word chw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hm2_out : m2.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_out,
      show ofString "ch" ≠ ofString "out" by decide]
  have hm2_mark : m2.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_mark,
      show ofString "ch" ≠ ofString "mark" by decide]
  refine worldEff_seq hnt2 hcr2
    (fun hnt_c1 hcr_c1 =>
      worldEff_call0_htr_u64_at heff_m2 _ (.var .local (ofString "ch")) chw
        (by simp [evalHOLExact, toExact, hm2_ch])
        (Or.inr ⟨hch_lo, by omega⟩) hnt_c1 hcr_c1)
    (fun m3 hm3 heff_m3 hnt3 hcr3 => ?_)
  have hm3_loc : m3.locals = m2.locals := by
    have := call0_none_locals m2 (ofString "htr_u64_at") _ (by rw [hm3]); rwa [hm3] at this
  refine worldEff_seq hnt3 hcr3
    (fun hnt_c2 hcr_c2 =>
      worldEff_call0_htr_u64_at heff_m3 _
        (.op .add [.var .local (ofString "ch"), .const 32#64]) (chw + 32#64)
        (by simp [evalHOLExact, evalListHOLExact, toExact, hm3_loc, hm2_ch,
              valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr])
        (outIvlCovered_heap_offset hch_lo hch_cap (by decide))
        hnt_c2 hcr_c2)
    (fun m4 hm4 heff_m4 hnt4 hcr4 => ?_)
  have hm4_loc : m4.locals = m2.locals := by
    have := call0_none_locals m3 (ofString "htr_u64_at") _ (by rw [hm4])
    rw [hm4] at this; exact this.trans hm3_loc
  refine worldEff_seq hnt4 hcr4
    (fun hnt_c3 hcr_c3 =>
      worldEff_call0_htr_bytes_vector hAs0 heff_m4 _ _
        (.op .add [.var .local (ofString "ch"), .const 64#64]) (chw + 64#64)
        (by simp [evalHOLExact, evalListHOLExact, toExact, hm4_loc, hm2_ch,
              valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr])
        (outIvlCovered_heap_offset hch_lo hch_cap (by decide))
        hnt_c3 hcr_c3)
    (fun m5 hm5 heff_m5 hnt5 hcr5 => ?_)
  have hm5_loc : m5.locals = m2.locals := by
    have := call0_none_locals m4 (ofString "htr_bytes_vector") _ (by rw [hm5])
    rw [hm5] at this; exact this.trans hm4_loc
  refine worldEff_seq hnt5 hcr5
    (fun hnt_c4 hcr_c4 =>
      worldEff_call0_htr_u64_at heff_m5 _
        (.op .add [.var .local (ofString "ch"), .const 96#64]) (chw + 96#64)
        (by simp [evalHOLExact, evalListHOLExact, toExact, hm5_loc, hm2_ch,
              valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr])
        (outIvlCovered_heap_offset hch_lo hch_cap (by decide))
        hnt_c4 hcr_c4)
    (fun m6 hm6 heff_m6 hnt6 hcr6 => ?_)
  have hm6_loc : m6.locals = m2.locals := by
    have := call0_none_locals m5 (ofString "htr_u64_at") _ (by rw [hm6])
    rw [hm6] at this; exact this.trans hm5_loc
  refine worldEff_seq hnt6 hcr6
    (fun hnt_mk hcr_mk =>
      worldEff_call0_merkleize hAs0 heff_m6
        (.var .local (ofString "ch")) (.const 4#64) (.const 4#64) (.var .local (ofString "out"))
        4#64 outw
        (by simp [evalHOLExact]) (by decide)
        (by simp [evalHOLExact, toExact, hm6_loc, hm2_out]) hout_cov hnt_mk hcr_mk)
    (fun m7 hm7 heff_m7 hnt7 hcr7 => ?_)
  have hm7_loc : m7.locals = m2.locals := by
    have := call0_none_locals m6 (ofString "merkleize") _ (by rw [hm7])
    rw [hm7] at this; exact this.trans hm6_loc
  refine worldEff_seq hnt7 hcr7
    (fun hnt_hr _ =>
      (worldEff_call0_heap_release hAs0 heff_m7 (by decide) hp_no_gb
        (.var .local (ofString "mark")) markw
        (by simp [evalHOLExact, toExact, hm7_loc, hm2_mark])
        hmark_lo hmark_hi hmark_al hnt_hr).2.choose_spec.2)
    (fun m8 _ heff_m8 _ _ => worldEff_return heff_m8 _)

private theorem worldEff_call0_htr_withdrawal {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hAs0 : ArenaOK s0) (heff : WorldEff s0 cur Rl sszBufs hpGw)
    (wExp outExp : ExpHOL 64) (outw : BitVec 64)
    (hout : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      outExp = some (.val (.word outw)))
    (hcov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_withdrawal")
      [wExp, outExp])).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_withdrawal")
      [wExp, outExp])).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_withdrawal")
      [wExp, outExp])).2 Rl sszBufs hpGw := by
  refine worldEff_call0_eff heff (ofString "htr_withdrawal") [wExp, outExp]
    _ _ _ lookup_htr_withdrawal (fun callee vals hargs hl hnt_e hres_e => ?_) hnt hcr
  rw [heff.code] at hl
  obtain ⟨ww, ow, rfl, _, ho⟩ := lookupCode_two_words (by decide) lookup_htr_withdrawal hl
  have how_eq : ow = outw := by
    rw [evalListHOLFinite_eq_toExact] at hargs
    simp only [evalListHOLExact, hout] at hargs
    rcases hw0 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) wExp with _ | vw
    · simp [hw0] at hargs
    · simp only [hw0] at hargs
      injection hargs with h0; injection h0 with _ h1; injection h1 with h2 _
      injection h2 with h2'; injection h2' with h2''; exact h2''.symm
  subst how_eq
  exact worldEff_htr_withdrawal s0 (callEntryStateHOLFinite cur callee) hAs0
    (heff.locals_clock _ _) ho hcov hnt_e hres_e

private theorem worldEff_htr_deposit {F : Type}
    (s0 cur : PanSemStateFiniteExact 64 F) {Rl : List Ivl}
    (hAs0 : ArenaOK s0) (heff_cur : WorldEff s0 cur Rl sszBufs hpGw)
    {outw : BitVec 64}
    (hout_lk : cur.locals.lookup (ofString "out") = some (.val (.word outw)))
    (hout_cov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_deposit)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_deposit)).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_deposit)).2 Rl sszBufs hpGw := by
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_htr_deposit,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_decCall_heap_mark heff_cur (ofString "mark") hnt (Or.inr (Or.inr (Or.inr hres)))
    (fun markw m1 _ _ hmark_al hmark_lo hmark_hi hm1_eq heff_m1 hnt1 hcr1 => ?_)
  have hm1_out : m1.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hout_lk,
      show ofString "mark" ≠ ofString "out" by decide]
  have hm1_mark : m1.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  refine worldEff_decCall_alloc heff_m1 (by decide) (ofString "ch") _ hnt1 hcr1
    (fun chw szw m2 hsz_ev _ hm2_loc _ heff_m2 _ _ hch_lo hch_end _ _ hnt2 hcr2 => ?_)
  have hsz_eq : szw = 160#64 := by
    simp [evalHOLExact, evalListHOLExact, valueIsWord, valueWord, panOpHOL] at hsz_ev
    exact hsz_ev.symm
  subst hsz_eq
  have hch_cap : chw.toNat + 160 ≤ heapLimit := by
    have : (160#64 : BitVec 64).toNat = 160 := rfl
    omega
  have hm2_ch : m2.locals.lookup (ofString "ch") = some (.val (.word chw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hm2_out : m2.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_out,
      show ofString "ch" ≠ ofString "out" by decide]
  have hm2_mark : m2.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_mark,
      show ofString "ch" ≠ ofString "mark" by decide]
  refine worldEff_seq hnt2 hcr2
    (fun hnt_c1 hcr_c1 =>
      worldEff_call0_htr_bytes_vector hAs0 heff_m2 _ _ (.var .local (ofString "ch")) chw
        (by simp [evalHOLExact, toExact, hm2_ch])
        (Or.inr ⟨hch_lo, by omega⟩) hnt_c1 hcr_c1)
    (fun m3 hm3 heff_m3 hnt3 hcr3 => ?_)
  have hm3_loc : m3.locals = m2.locals := by
    have := call0_none_locals m2 (ofString "htr_bytes_vector") _ (by rw [hm3]); rwa [hm3] at this
  refine worldEff_seq hnt3 hcr3
    (fun hnt_c2 hcr_c2 =>
      (worldEff_call0_memcpy_word heff_m3
        (.op .add [.var .local (ofString "ch"), .const 32#64]) _ (.const 32#64)
        (chw + 32#64) 32#64
        (by simp [evalHOLExact, evalListHOLExact, toExact, hm3_loc, hm2_ch,
              valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr])
        (by simp [evalHOLExact])
        (fun _ _ => outIvlCovered_to_world
          (outIvlCovered_heap_offset hch_lo hch_cap (by decide))
          32 le_rfl)
        hnt_c2 hcr_c2).1)
    (fun m4 hm4 heff_m4 hnt4 hcr4 => ?_)
  have hm4_loc : m4.locals = m2.locals := by
    have := call0_none_locals m3 (ofString "memcpy") _ (by rw [hm4])
    rw [hm4] at this; exact this.trans hm3_loc
  refine worldEff_seq hnt4 hcr4
    (fun hnt_c3 hcr_c3 =>
      worldEff_call0_htr_u64_at heff_m4 _
        (.op .add [.var .local (ofString "ch"), .const 64#64]) (chw + 64#64)
        (by simp [evalHOLExact, evalListHOLExact, toExact, hm4_loc, hm2_ch,
              valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr])
        (outIvlCovered_heap_offset hch_lo hch_cap (by decide))
        hnt_c3 hcr_c3)
    (fun m5 hm5 heff_m5 hnt5 hcr5 => ?_)
  have hm5_loc : m5.locals = m2.locals := by
    have := call0_none_locals m4 (ofString "htr_u64_at") _ (by rw [hm5])
    rw [hm5] at this; exact this.trans hm4_loc
  refine worldEff_seq hnt5 hcr5
    (fun hnt_c4 hcr_c4 =>
      worldEff_call0_htr_bytes_vector hAs0 heff_m5 _ _
        (.op .add [.var .local (ofString "ch"), .const 96#64]) (chw + 96#64)
        (by simp [evalHOLExact, evalListHOLExact, toExact, hm5_loc, hm2_ch,
              valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr])
        (outIvlCovered_heap_offset hch_lo hch_cap (by decide))
        hnt_c4 hcr_c4)
    (fun m6 hm6 heff_m6 hnt6 hcr6 => ?_)
  have hm6_loc : m6.locals = m2.locals := by
    have := call0_none_locals m5 (ofString "htr_bytes_vector") _ (by rw [hm6])
    rw [hm6] at this; exact this.trans hm5_loc
  refine worldEff_seq hnt6 hcr6
    (fun hnt_c5 hcr_c5 =>
      worldEff_call0_htr_u64_at heff_m6 _
        (.op .add [.var .local (ofString "ch"), .const 128#64]) (chw + 128#64)
        (by simp [evalHOLExact, evalListHOLExact, toExact, hm6_loc, hm2_ch,
              valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr])
        (outIvlCovered_heap_offset hch_lo hch_cap (by decide))
        hnt_c5 hcr_c5)
    (fun m7 hm7 heff_m7 hnt7 hcr7 => ?_)
  have hm7_loc : m7.locals = m2.locals := by
    have := call0_none_locals m6 (ofString "htr_u64_at") _ (by rw [hm7])
    rw [hm7] at this; exact this.trans hm6_loc
  refine worldEff_seq hnt7 hcr7
    (fun hnt_mk hcr_mk =>
      worldEff_call0_merkleize hAs0 heff_m7
        (.var .local (ofString "ch")) (.const 5#64) (.const 5#64) (.var .local (ofString "out"))
        5#64 outw
        (by simp [evalHOLExact]) (by decide)
        (by simp [evalHOLExact, toExact, hm7_loc, hm2_out]) hout_cov hnt_mk hcr_mk)
    (fun m8 hm8 heff_m8 hnt8 hcr8 => ?_)
  have hm8_loc : m8.locals = m2.locals := by
    have := call0_none_locals m7 (ofString "merkleize") _ (by rw [hm8])
    rw [hm8] at this; exact this.trans hm7_loc
  refine worldEff_seq hnt8 hcr8
    (fun hnt_hr _ =>
      (worldEff_call0_heap_release hAs0 heff_m8 (by decide) hp_no_gb
        (.var .local (ofString "mark")) markw
        (by simp [evalHOLExact, toExact, hm8_loc, hm2_mark])
        hmark_lo hmark_hi hmark_al hnt_hr).2.choose_spec.2)
    (fun m9 _ heff_m9 _ _ => worldEff_return heff_m9 _)

private theorem worldEff_call0_htr_deposit {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hAs0 : ArenaOK s0) (heff : WorldEff s0 cur Rl sszBufs hpGw)
    (eExp outExp : ExpHOL 64) (outw : BitVec 64)
    (hout : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      outExp = some (.val (.word outw)))
    (hcov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_deposit")
      [eExp, outExp])).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_deposit")
      [eExp, outExp])).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_deposit")
      [eExp, outExp])).2 Rl sszBufs hpGw := by
  refine worldEff_call0_eff heff (ofString "htr_deposit") [eExp, outExp]
    _ _ _ lookup_htr_deposit (fun callee vals hargs hl hnt_e hres_e => ?_) hnt hcr
  rw [heff.code] at hl
  obtain ⟨ew, ow, rfl, _, ho⟩ := lookupCode_two_words (by decide) lookup_htr_deposit hl
  have how_eq : ow = outw := by
    rw [evalListHOLFinite_eq_toExact] at hargs
    simp only [evalListHOLExact, hout] at hargs
    rcases he0 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) eExp with _ | ve
    · simp [he0] at hargs
    · simp only [he0] at hargs
      injection hargs with h0; injection h0 with _ h1; injection h1 with h2 _
      injection h2 with h2'; injection h2' with h2''; exact h2''.symm
  subst how_eq
  exact worldEff_htr_deposit s0 (callEntryStateHOLFinite cur callee) hAs0
    (heff.locals_clock _ _) ho hcov hnt_e hres_e

private theorem worldEff_htr_wdreq {F : Type}
    (s0 cur : PanSemStateFiniteExact 64 F) {Rl : List Ivl}
    (hAs0 : ArenaOK s0) (heff_cur : WorldEff s0 cur Rl sszBufs hpGw)
    {outw : BitVec 64}
    (hout_lk : cur.locals.lookup (ofString "out") = some (.val (.word outw)))
    (hout_cov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_wdreq)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_wdreq)).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_wdreq)).2 Rl sszBufs hpGw := by
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_htr_wdreq,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_decCall_heap_mark heff_cur (ofString "mark") hnt (Or.inr (Or.inr (Or.inr hres)))
    (fun markw m1 _ _ hmark_al hmark_lo hmark_hi hm1_eq heff_m1 hnt1 hcr1 => ?_)
  have hm1_out : m1.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hout_lk,
      show ofString "mark" ≠ ofString "out" by decide]
  have hm1_mark : m1.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  refine worldEff_decCall_alloc heff_m1 (by decide) (ofString "ch") _ hnt1 hcr1
    (fun chw szw m2 hsz_ev _ hm2_loc _ heff_m2 _ _ hch_lo hch_end _ _ hnt2 hcr2 => ?_)
  have hsz_eq : szw = 96#64 := by
    simp [evalHOLExact, evalListHOLExact, valueIsWord, valueWord, panOpHOL] at hsz_ev
    exact hsz_ev.symm
  subst hsz_eq
  have hch_cap : chw.toNat + 96 ≤ heapLimit := by
    have : (96#64 : BitVec 64).toNat = 96 := rfl
    omega
  have hm2_ch : m2.locals.lookup (ofString "ch") = some (.val (.word chw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hm2_out : m2.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_out,
      show ofString "ch" ≠ ofString "out" by decide]
  have hm2_mark : m2.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_mark,
      show ofString "ch" ≠ ofString "mark" by decide]
  refine worldEff_seq hnt2 hcr2
    (fun hnt_c1 hcr_c1 =>
      worldEff_call0_htr_bytes_vector hAs0 heff_m2 _ _ (.var .local (ofString "ch")) chw
        (by simp [evalHOLExact, toExact, hm2_ch])
        (Or.inr ⟨hch_lo, by omega⟩) hnt_c1 hcr_c1)
    (fun m3 hm3 heff_m3 hnt3 hcr3 => ?_)
  have hm3_loc : m3.locals = m2.locals := by
    have := call0_none_locals m2 (ofString "htr_bytes_vector") _ (by rw [hm3]); rwa [hm3] at this
  refine worldEff_seq hnt3 hcr3
    (fun hnt_c2 hcr_c2 =>
      worldEff_call0_htr_bytes_vector hAs0 heff_m3 _ _
        (.op .add [.var .local (ofString "ch"), .const 32#64]) (chw + 32#64)
        (by simp [evalHOLExact, evalListHOLExact, toExact, hm3_loc, hm2_ch,
              valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr])
        (outIvlCovered_heap_offset hch_lo hch_cap (by decide))
        hnt_c2 hcr_c2)
    (fun m4 hm4 heff_m4 hnt4 hcr4 => ?_)
  have hm4_loc : m4.locals = m2.locals := by
    have := call0_none_locals m3 (ofString "htr_bytes_vector") _ (by rw [hm4])
    rw [hm4] at this; exact this.trans hm3_loc
  refine worldEff_seq hnt4 hcr4
    (fun hnt_c3 hcr_c3 =>
      worldEff_call0_htr_u64_at heff_m4 _
        (.op .add [.var .local (ofString "ch"), .const 64#64]) (chw + 64#64)
        (by simp [evalHOLExact, evalListHOLExact, toExact, hm4_loc, hm2_ch,
              valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr])
        (outIvlCovered_heap_offset hch_lo hch_cap (by decide))
        hnt_c3 hcr_c3)
    (fun m5 hm5 heff_m5 hnt5 hcr5 => ?_)
  have hm5_loc : m5.locals = m2.locals := by
    have := call0_none_locals m4 (ofString "htr_u64_at") _ (by rw [hm5])
    rw [hm5] at this; exact this.trans hm4_loc
  refine worldEff_seq hnt5 hcr5
    (fun hnt_mk hcr_mk =>
      worldEff_call0_merkleize hAs0 heff_m5
        (.var .local (ofString "ch")) (.const 3#64) (.const 3#64) (.var .local (ofString "out"))
        3#64 outw
        (by simp [evalHOLExact]) (by decide)
        (by simp [evalHOLExact, toExact, hm5_loc, hm2_out]) hout_cov hnt_mk hcr_mk)
    (fun m6 hm6 heff_m6 hnt6 hcr6 => ?_)
  have hm6_loc : m6.locals = m2.locals := by
    have := call0_none_locals m5 (ofString "merkleize") _ (by rw [hm6])
    rw [hm6] at this; exact this.trans hm5_loc
  refine worldEff_seq hnt6 hcr6
    (fun hnt_hr _ =>
      (worldEff_call0_heap_release hAs0 heff_m6 (by decide) hp_no_gb
        (.var .local (ofString "mark")) markw
        (by simp [evalHOLExact, toExact, hm6_loc, hm2_mark])
        hmark_lo hmark_hi hmark_al hnt_hr).2.choose_spec.2)
    (fun m7 _ heff_m7 _ _ => worldEff_return heff_m7 _)

private theorem worldEff_call0_htr_wdreq {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hAs0 : ArenaOK s0) (heff : WorldEff s0 cur Rl sszBufs hpGw)
    (eExp outExp : ExpHOL 64) (outw : BitVec 64)
    (hout : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      outExp = some (.val (.word outw)))
    (hcov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_wdreq")
      [eExp, outExp])).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_wdreq")
      [eExp, outExp])).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_wdreq")
      [eExp, outExp])).2 Rl sszBufs hpGw := by
  refine worldEff_call0_eff heff (ofString "htr_wdreq") [eExp, outExp]
    _ _ _ lookup_htr_wdreq (fun callee vals hargs hl hnt_e hres_e => ?_) hnt hcr
  rw [heff.code] at hl
  obtain ⟨ew, ow, rfl, _, ho⟩ := lookupCode_two_words (by decide) lookup_htr_wdreq hl
  have how_eq : ow = outw := by
    rw [evalListHOLFinite_eq_toExact] at hargs
    simp only [evalListHOLExact, hout] at hargs
    rcases he0 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) eExp with _ | ve
    · simp [he0] at hargs
    · simp only [he0] at hargs
      injection hargs with h0; injection h0 with _ h1; injection h1 with h2 _
      injection h2 with h2'; injection h2' with h2''; exact h2''.symm
  subst how_eq
  exact worldEff_htr_wdreq s0 (callEntryStateHOLFinite cur callee) hAs0
    (heff.locals_clock _ _) ho hcov hnt_e hres_e

private theorem worldEff_htr_cons {F : Type}
    (s0 cur : PanSemStateFiniteExact 64 F) {Rl : List Ivl}
    (hAs0 : ArenaOK s0) (heff_cur : WorldEff s0 cur Rl sszBufs hpGw)
    {outw : BitVec 64}
    (hout_lk : cur.locals.lookup (ofString "out") = some (.val (.word outw)))
    (hout_cov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_cons)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_cons)).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_cons)).2 Rl sszBufs hpGw := by
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_htr_cons,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_decCall_heap_mark heff_cur (ofString "mark") hnt (Or.inr (Or.inr (Or.inr hres)))
    (fun markw m1 _ _ hmark_al hmark_lo hmark_hi hm1_eq heff_m1 hnt1 hcr1 => ?_)
  have hm1_out : m1.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hout_lk,
      show ofString "mark" ≠ ofString "out" by decide]
  have hm1_mark : m1.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  refine worldEff_decCall_alloc heff_m1 (by decide) (ofString "ch") _ hnt1 hcr1
    (fun chw szw m2 hsz_ev _ hm2_loc _ heff_m2 _ _ hch_lo hch_end _ _ hnt2 hcr2 => ?_)
  have hsz_eq : szw = 96#64 := by
    simp [evalHOLExact, evalListHOLExact, valueIsWord, valueWord, panOpHOL] at hsz_ev
    exact hsz_ev.symm
  subst hsz_eq
  have hch_cap : chw.toNat + 96 ≤ heapLimit := by
    have : (96#64 : BitVec 64).toNat = 96 := rfl
    omega
  have hm2_ch : m2.locals.lookup (ofString "ch") = some (.val (.word chw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hm2_out : m2.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_out,
      show ofString "ch" ≠ ofString "out" by decide]
  have hm2_mark : m2.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_mark,
      show ofString "ch" ≠ ofString "mark" by decide]
  refine worldEff_seq hnt2 hcr2
    (fun hnt_c1 hcr_c1 =>
      worldEff_call0_htr_bytes_vector hAs0 heff_m2 _ _ (.var .local (ofString "ch")) chw
        (by simp [evalHOLExact, toExact, hm2_ch])
        (Or.inr ⟨hch_lo, by omega⟩) hnt_c1 hcr_c1)
    (fun m3 hm3 heff_m3 hnt3 hcr3 => ?_)
  have hm3_loc : m3.locals = m2.locals := by
    have := call0_none_locals m2 (ofString "htr_bytes_vector") _ (by rw [hm3]); rwa [hm3] at this
  refine worldEff_seq hnt3 hcr3
    (fun hnt_c2 hcr_c2 =>
      worldEff_call0_htr_bytes_vector hAs0 heff_m3 _ _
        (.op .add [.var .local (ofString "ch"), .const 32#64]) (chw + 32#64)
        (by simp [evalHOLExact, evalListHOLExact, toExact, hm3_loc, hm2_ch,
              valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr])
        (outIvlCovered_heap_offset hch_lo hch_cap (by decide))
        hnt_c2 hcr_c2)
    (fun m4 hm4 heff_m4 hnt4 hcr4 => ?_)
  have hm4_loc : m4.locals = m2.locals := by
    have := call0_none_locals m3 (ofString "htr_bytes_vector") _ (by rw [hm4])
    rw [hm4] at this; exact this.trans hm3_loc
  refine worldEff_seq hnt4 hcr4
    (fun hnt_c3 hcr_c3 =>
      worldEff_call0_htr_bytes_vector hAs0 heff_m4 _ _
        (.op .add [.var .local (ofString "ch"), .const 64#64]) (chw + 64#64)
        (by simp [evalHOLExact, evalListHOLExact, toExact, hm4_loc, hm2_ch,
              valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr])
        (outIvlCovered_heap_offset hch_lo hch_cap (by decide))
        hnt_c3 hcr_c3)
    (fun m5 hm5 heff_m5 hnt5 hcr5 => ?_)
  have hm5_loc : m5.locals = m2.locals := by
    have := call0_none_locals m4 (ofString "htr_bytes_vector") _ (by rw [hm5])
    rw [hm5] at this; exact this.trans hm4_loc
  refine worldEff_seq hnt5 hcr5
    (fun hnt_mk hcr_mk =>
      worldEff_call0_merkleize hAs0 heff_m5
        (.var .local (ofString "ch")) (.const 3#64) (.const 3#64) (.var .local (ofString "out"))
        3#64 outw
        (by simp [evalHOLExact]) (by decide)
        (by simp [evalHOLExact, toExact, hm5_loc, hm2_out]) hout_cov hnt_mk hcr_mk)
    (fun m6 hm6 heff_m6 hnt6 hcr6 => ?_)
  have hm6_loc : m6.locals = m2.locals := by
    have := call0_none_locals m5 (ofString "merkleize") _ (by rw [hm6])
    rw [hm6] at this; exact this.trans hm5_loc
  refine worldEff_seq hnt6 hcr6
    (fun hnt_hr _ =>
      (worldEff_call0_heap_release hAs0 heff_m6 (by decide) hp_no_gb
        (.var .local (ofString "mark")) markw
        (by simp [evalHOLExact, toExact, hm6_loc, hm2_mark])
        hmark_lo hmark_hi hmark_al hnt_hr).2.choose_spec.2)
    (fun m7 _ heff_m7 _ _ => worldEff_return heff_m7 _)

private theorem worldEff_call0_htr_cons {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hAs0 : ArenaOK s0) (heff : WorldEff s0 cur Rl sszBufs hpGw)
    (eExp outExp : ExpHOL 64) (outw : BitVec 64)
    (hout : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      outExp = some (.val (.word outw)))
    (hcov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_cons")
      [eExp, outExp])).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_cons")
      [eExp, outExp])).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_cons")
      [eExp, outExp])).2 Rl sszBufs hpGw := by
  refine worldEff_call0_eff heff (ofString "htr_cons") [eExp, outExp]
    _ _ _ lookup_htr_cons (fun callee vals hargs hl hnt_e hres_e => ?_) hnt hcr
  rw [heff.code] at hl
  obtain ⟨ew, ow, rfl, _, ho⟩ := lookupCode_two_words (by decide) lookup_htr_cons hl
  have how_eq : ow = outw := by
    rw [evalListHOLFinite_eq_toExact] at hargs
    simp only [evalListHOLExact, hout] at hargs
    rcases he0 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) eExp with _ | ve
    · simp [he0] at hargs
    · simp only [he0] at hargs
      injection hargs with h0; injection h0 with _ h1; injection h1 with h2 _
      injection h2 with h2'; injection h2' with h2''; exact h2''.symm
  subst how_eq
  exact worldEff_htr_cons s0 (callEntryStateHOLFinite cur callee) hAs0
    (heff.locals_clock _ _) ho hcov hnt_e hres_e

private theorem worldEff_htr_bdep {F : Type}
    (s0 cur : PanSemStateFiniteExact 64 F) {Rl : List Ivl}
    (hAs0 : ArenaOK s0) (heff_cur : WorldEff s0 cur Rl sszBufs hpGw)
    {outw : BitVec 64}
    (hout_lk : cur.locals.lookup (ofString "out") = some (.val (.word outw)))
    (hout_cov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_bdep)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_bdep)).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_bdep)).2 Rl sszBufs hpGw := by
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_htr_bdep,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_decCall_heap_mark heff_cur (ofString "mark") hnt (Or.inr (Or.inr (Or.inr hres)))
    (fun markw m1 _ _ hmark_al hmark_lo hmark_hi hm1_eq heff_m1 hnt1 hcr1 => ?_)
  have hm1_out : m1.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hout_lk,
      show ofString "mark" ≠ ofString "out" by decide]
  have hm1_mark : m1.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  refine worldEff_decCall_alloc heff_m1 (by decide) (ofString "ch") _ hnt1 hcr1
    (fun chw szw m2 hsz_ev _ hm2_loc _ heff_m2 _ _ hch_lo hch_end _ _ hnt2 hcr2 => ?_)
  have hsz_eq : szw = 128#64 := by
    simp [evalHOLExact, evalListHOLExact, valueIsWord, valueWord, panOpHOL] at hsz_ev
    exact hsz_ev.symm
  subst hsz_eq
  have hch_cap : chw.toNat + 128 ≤ heapLimit := by
    have : (128#64 : BitVec 64).toNat = 128 := rfl
    omega
  have hm2_ch : m2.locals.lookup (ofString "ch") = some (.val (.word chw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hm2_out : m2.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_out,
      show ofString "ch" ≠ ofString "out" by decide]
  have hm2_mark : m2.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_mark,
      show ofString "ch" ≠ ofString "mark" by decide]
  refine worldEff_seq hnt2 hcr2
    (fun hnt_c1 hcr_c1 =>
      worldEff_call0_htr_bytes_vector hAs0 heff_m2 _ _ (.var .local (ofString "ch")) chw
        (by simp [evalHOLExact, toExact, hm2_ch])
        (Or.inr ⟨hch_lo, by omega⟩) hnt_c1 hcr_c1)
    (fun m3 hm3 heff_m3 hnt3 hcr3 => ?_)
  have hm3_loc : m3.locals = m2.locals := by
    have := call0_none_locals m2 (ofString "htr_bytes_vector") _ (by rw [hm3]); rwa [hm3] at this
  refine worldEff_seq hnt3 hcr3
    (fun hnt_c2 hcr_c2 =>
      (worldEff_call0_memcpy_word heff_m3
        (.op .add [.var .local (ofString "ch"), .const 32#64]) _ (.const 32#64)
        (chw + 32#64) 32#64
        (by simp [evalHOLExact, evalListHOLExact, toExact, hm3_loc, hm2_ch,
              valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr])
        (by simp [evalHOLExact])
        (fun _ _ => outIvlCovered_to_world
          (outIvlCovered_heap_offset hch_lo hch_cap (by decide))
          32 le_rfl)
        hnt_c2 hcr_c2).1)
    (fun m4 hm4 heff_m4 hnt4 hcr4 => ?_)
  have hm4_loc : m4.locals = m2.locals := by
    have := call0_none_locals m3 (ofString "memcpy") _ (by rw [hm4])
    rw [hm4] at this; exact this.trans hm3_loc
  refine worldEff_seq hnt4 hcr4
    (fun hnt_c3 hcr_c3 =>
      worldEff_call0_htr_u64_at heff_m4 _
        (.op .add [.var .local (ofString "ch"), .const 64#64]) (chw + 64#64)
        (by simp [evalHOLExact, evalListHOLExact, toExact, hm4_loc, hm2_ch,
              valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr])
        (outIvlCovered_heap_offset hch_lo hch_cap (by decide))
        hnt_c3 hcr_c3)
    (fun m5 hm5 heff_m5 hnt5 hcr5 => ?_)
  have hm5_loc : m5.locals = m2.locals := by
    have := call0_none_locals m4 (ofString "htr_u64_at") _ (by rw [hm5])
    rw [hm5] at this; exact this.trans hm4_loc
  refine worldEff_seq hnt5 hcr5
    (fun hnt_c4 hcr_c4 =>
      worldEff_call0_htr_bytes_vector hAs0 heff_m5 _ _
        (.op .add [.var .local (ofString "ch"), .const 96#64]) (chw + 96#64)
        (by simp [evalHOLExact, evalListHOLExact, toExact, hm5_loc, hm2_ch,
              valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr])
        (outIvlCovered_heap_offset hch_lo hch_cap (by decide))
        hnt_c4 hcr_c4)
    (fun m6 hm6 heff_m6 hnt6 hcr6 => ?_)
  have hm6_loc : m6.locals = m2.locals := by
    have := call0_none_locals m5 (ofString "htr_bytes_vector") _ (by rw [hm6])
    rw [hm6] at this; exact this.trans hm5_loc
  refine worldEff_seq hnt6 hcr6
    (fun hnt_mk hcr_mk =>
      worldEff_call0_merkleize hAs0 heff_m6
        (.var .local (ofString "ch")) (.const 4#64) (.const 4#64) (.var .local (ofString "out"))
        4#64 outw
        (by simp [evalHOLExact]) (by decide)
        (by simp [evalHOLExact, toExact, hm6_loc, hm2_out]) hout_cov hnt_mk hcr_mk)
    (fun m7 hm7 heff_m7 hnt7 hcr7 => ?_)
  have hm7_loc : m7.locals = m2.locals := by
    have := call0_none_locals m6 (ofString "merkleize") _ (by rw [hm7])
    rw [hm7] at this; exact this.trans hm6_loc
  refine worldEff_seq hnt7 hcr7
    (fun hnt_hr _ =>
      (worldEff_call0_heap_release hAs0 heff_m7 (by decide) hp_no_gb
        (.var .local (ofString "mark")) markw
        (by simp [evalHOLExact, toExact, hm7_loc, hm2_mark])
        hmark_lo hmark_hi hmark_al hnt_hr).2.choose_spec.2)
    (fun m8 _ heff_m8 _ _ => worldEff_return heff_m8 _)

private theorem worldEff_call0_htr_bdep {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hAs0 : ArenaOK s0) (heff : WorldEff s0 cur Rl sszBufs hpGw)
    (eExp outExp : ExpHOL 64) (outw : BitVec 64)
    (hout : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      outExp = some (.val (.word outw)))
    (hcov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_bdep")
      [eExp, outExp])).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_bdep")
      [eExp, outExp])).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_bdep")
      [eExp, outExp])).2 Rl sszBufs hpGw := by
  refine worldEff_call0_eff heff (ofString "htr_bdep") [eExp, outExp]
    _ _ _ lookup_htr_bdep (fun callee vals hargs hl hnt_e hres_e => ?_) hnt hcr
  rw [heff.code] at hl
  obtain ⟨ew, ow, rfl, _, ho⟩ := lookupCode_two_words (by decide) lookup_htr_bdep hl
  have how_eq : ow = outw := by
    rw [evalListHOLFinite_eq_toExact] at hargs
    simp only [evalListHOLExact, hout] at hargs
    rcases he0 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) eExp with _ | ve
    · simp [he0] at hargs
    · simp only [he0] at hargs
      injection hargs with h0; injection h0 with _ h1; injection h1 with h2 _
      injection h2 with h2'; injection h2' with h2''; exact h2''.symm
  subst how_eq
  exact worldEff_htr_bdep s0 (callEntryStateHOLFinite cur callee) hAs0
    (heff.locals_clock _ _) ho hcov hnt_e hres_e

private theorem worldEff_htr_bexit {F : Type}
    (s0 cur : PanSemStateFiniteExact 64 F) {Rl : List Ivl}
    (hAs0 : ArenaOK s0) (heff_cur : WorldEff s0 cur Rl sszBufs hpGw)
    {outw : BitVec 64}
    (hout_lk : cur.locals.lookup (ofString "out") = some (.val (.word outw)))
    (hout_cov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_bexit)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_bexit)).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_bexit)).2 Rl sszBufs hpGw := by
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_htr_bexit,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_decCall_heap_mark heff_cur (ofString "mark") hnt (Or.inr (Or.inr (Or.inr hres)))
    (fun markw m1 _ _ hmark_al hmark_lo hmark_hi hm1_eq heff_m1 hnt1 hcr1 => ?_)
  have hm1_out : m1.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hout_lk,
      show ofString "mark" ≠ ofString "out" by decide]
  have hm1_mark : m1.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  refine worldEff_decCall_alloc heff_m1 (by decide) (ofString "ch") _ hnt1 hcr1
    (fun chw szw m2 hsz_ev _ hm2_loc _ heff_m2 _ _ hch_lo hch_end _ _ hnt2 hcr2 => ?_)
  have hsz_eq : szw = 64#64 := by
    simp [evalHOLExact, evalListHOLExact, valueIsWord, valueWord, panOpHOL] at hsz_ev
    exact hsz_ev.symm
  subst hsz_eq
  have hch_cap : chw.toNat + 64 ≤ heapLimit := by
    have : (64#64 : BitVec 64).toNat = 64 := rfl
    omega
  have hm2_ch : m2.locals.lookup (ofString "ch") = some (.val (.word chw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hm2_out : m2.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_out,
      show ofString "ch" ≠ ofString "out" by decide]
  have hm2_mark : m2.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_mark,
      show ofString "ch" ≠ ofString "mark" by decide]
  refine worldEff_seq hnt2 hcr2
    (fun hnt_c1 hcr_c1 =>
      worldEff_call0_htr_bytes_vector hAs0 heff_m2 _ _ (.var .local (ofString "ch")) chw
        (by simp [evalHOLExact, toExact, hm2_ch])
        (Or.inr ⟨hch_lo, by omega⟩) hnt_c1 hcr_c1)
    (fun m3 hm3 heff_m3 hnt3 hcr3 => ?_)
  have hm3_loc : m3.locals = m2.locals := by
    have := call0_none_locals m2 (ofString "htr_bytes_vector") _ (by rw [hm3]); rwa [hm3] at this
  refine worldEff_seq hnt3 hcr3
    (fun hnt_c2 hcr_c2 =>
      worldEff_call0_htr_bytes_vector hAs0 heff_m3 _ _
        (.op .add [.var .local (ofString "ch"), .const 32#64]) (chw + 32#64)
        (by simp [evalHOLExact, evalListHOLExact, toExact, hm3_loc, hm2_ch,
              valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr])
        (outIvlCovered_heap_offset hch_lo hch_cap (by decide))
        hnt_c2 hcr_c2)
    (fun m4 hm4 heff_m4 hnt4 hcr4 => ?_)
  have hm4_loc : m4.locals = m2.locals := by
    have := call0_none_locals m3 (ofString "htr_bytes_vector") _ (by rw [hm4])
    rw [hm4] at this; exact this.trans hm3_loc
  refine worldEff_seq hnt4 hcr4
    (fun hnt_mk hcr_mk =>
      worldEff_call0_merkleize hAs0 heff_m4
        (.var .local (ofString "ch")) (.const 2#64) (.const 2#64) (.var .local (ofString "out"))
        2#64 outw
        (by simp [evalHOLExact]) (by decide)
        (by simp [evalHOLExact, toExact, hm4_loc, hm2_out]) hout_cov hnt_mk hcr_mk)
    (fun m5 hm5 heff_m5 hnt5 hcr5 => ?_)
  have hm5_loc : m5.locals = m2.locals := by
    have := call0_none_locals m4 (ofString "merkleize") _ (by rw [hm5])
    rw [hm5] at this; exact this.trans hm4_loc
  refine worldEff_seq hnt5 hcr5
    (fun hnt_hr _ =>
      (worldEff_call0_heap_release hAs0 heff_m5 (by decide) hp_no_gb
        (.var .local (ofString "mark")) markw
        (by simp [evalHOLExact, toExact, hm5_loc, hm2_mark])
        hmark_lo hmark_hi hmark_al hnt_hr).2.choose_spec.2)
    (fun m6 _ heff_m6 _ _ => worldEff_return heff_m6 _)

private theorem worldEff_call0_htr_bexit {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hAs0 : ArenaOK s0) (heff : WorldEff s0 cur Rl sszBufs hpGw)
    (eExp outExp : ExpHOL 64) (outw : BitVec 64)
    (hout : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      outExp = some (.val (.word outw)))
    (hcov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_bexit")
      [eExp, outExp])).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_bexit")
      [eExp, outExp])).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_bexit")
      [eExp, outExp])).2 Rl sszBufs hpGw := by
  refine worldEff_call0_eff heff (ofString "htr_bexit") [eExp, outExp]
    _ _ _ lookup_htr_bexit (fun callee vals hargs hl hnt_e hres_e => ?_) hnt hcr
  rw [heff.code] at hl
  obtain ⟨ew, ow, rfl, _, ho⟩ := lookupCode_two_words (by decide) lookup_htr_bexit hl
  have how_eq : ow = outw := by
    rw [evalListHOLFinite_eq_toExact] at hargs
    simp only [evalListHOLExact, hout] at hargs
    rcases he0 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) eExp with _ | ve
    · simp [he0] at hargs
    · simp only [he0] at hargs
      injection hargs with h0; injection h0 with _ h1; injection h1 with h2 _
      injection h2 with h2'; injection h2' with h2''; exact h2''.symm
  subst how_eq
  exact worldEff_htr_bexit s0 (callEntryStateHOLFinite cur callee) hAs0
    (heff.locals_clock _ _) ho hcov hnt_e hres_e

private theorem ite_call0_skip_ne_break {F : Type}
    (u : PanSemStateFiniteExact 64 F) (c : ExpHOL 64) (fn : MlS) (args : List (ExpHOL 64)) :
    (evaluateHOLFiniteState u (.ite c (.call (some (none, none)) fn args) .skip)).1 ≠ some .break := by
  rw [evaluateHOLFiniteState_ite]
  rcases @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) c with _ | cv
  · simp
  · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
    by_cases hz : cw = 0#64
    · simp [hz, evaluateHOLFiniteState_skip]
    · simp [hz, call0_ne_break]

private theorem ite_call0_skip_none_locals {F : Type}
    (u : PanSemStateFiniteExact 64 F) (c : ExpHOL 64) (fn : MlS) (args : List (ExpHOL 64))
    (hnone : (evaluateHOLFiniteState u (.ite c (.call (some (none, none)) fn args) .skip)).1 = none) :
    (evaluateHOLFiniteState u (.ite c (.call (some (none, none)) fn args) .skip)).2.locals = u.locals := by
  rw [evaluateHOLFiniteState_ite] at hnone ⊢
  generalize @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) c = ec at hnone ⊢
  rcases ec with _ | ⟨⟨cw⟩⟩ | _ | _ <;> try simp
  dsimp only at hnone ⊢
  by_cases hz : cw = 0
  · subst hz; simp [evaluateHOLFiniteState_skip]
  · rw [if_neg hz] at hnone
    have hz64 : cw ≠ 0#64 := hz
    rw [if_neg hz64]
    exact call0_none_locals u fn args hnone

private theorem ite_call0_skip_ne_continue {F : Type}
    (u : PanSemStateFiniteExact 64 F) (c : ExpHOL 64) (fn : MlS) (args : List (ExpHOL 64)) :
    (evaluateHOLFiniteState u (.ite c (.call (some (none, none)) fn args) .skip)).1 ≠ some .continue := by
  rw [evaluateHOLFiniteState_ite]
  rcases @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) c with _ | cv
  · simp
  · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
    by_cases hz : cw = 0#64
    · simp [hz, evaluateHOLFiniteState_skip]
    · simp [hz, call0_ne_continue]

private theorem seq_ite_call0_skip_flow {F : Type}
    (u : PanSemStateFiniteExact 64 F) (c : ExpHOL 64) (fn : MlS) (args : List (ExpHOL 64)) (q : ProgHOL 64)
    (P : PanSemStateFiniteExact 64 F → Prop)
    (hfl : (evaluateHOLFiniteState u (.seq (.ite c (.call (some (none, none)) fn args) .skip) q)).1 = none ∨
           (evaluateHOLFiniteState u (.seq (.ite c (.call (some (none, none)) fn args) .skip) q)).1 = some .continue)
    (hk : ∀ u1, u1.locals = u.locals →
      ((evaluateHOLFiniteState u1 q).1 = none ∨ (evaluateHOLFiniteState u1 q).1 = some .continue) →
      P (evaluateHOLFiniteState u1 q).2) :
    P (evaluateHOLFiniteState u (.seq (.ite c (.call (some (none, none)) fn args) .skip) q)).2 := by
  rw [evaluateHOLFiniteState_seq_line780] at hfl ⊢
  dsimp only at hfl ⊢
  cases hr : (evaluateHOLFiniteState u (.ite c (.call (some (none, none)) fn args) .skip)).1 with
  | some rx =>
    rw [hr] at hfl
    dsimp only at hfl
    rcases hfl with h | h
    · exact absurd (hr.symm.trans h) (by simp)
    · exact absurd h (ite_call0_skip_ne_continue u c fn args)
  | none =>
    rw [hr] at hfl
    dsimp only at hfl ⊢
    exact hk _ (ite_call0_skip_none_locals u c fn args hr) hfl

private theorem worldEff_ite_htr_leaf {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (heff : WorldEff s0 cur Rl sszBufs hpGw)
    (c : ExpHOL 64) (fn : MlS) (eExp outExp : ExpHOL 64)
    (hcall : (evaluateHOLFiniteState cur (.call (some (none, none)) fn [eExp, outExp])).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState cur (.call (some (none, none)) fn [eExp, outExp])).1 →
      WorldEff s0 (evaluateHOLFiniteState cur (.call (some (none, none)) fn [eExp, outExp])).2 Rl sszBufs hpGw)
    (hnt : (evaluateHOLFiniteState cur (.ite c (.call (some (none, none)) fn [eExp, outExp]) .skip)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.ite c (.call (some (none, none)) fn [eExp, outExp]) .skip)).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (.ite c (.call (some (none, none)) fn [eExp, outExp]) .skip)).2 Rl sszBufs hpGw :=
  worldEff_ite heff c hnt hcr
    (fun _ _ _ hnt_y hcr_y => hcall hnt_y hcr_y)
    (fun _ _ _ => worldEff_skip heff)

private theorem worldEff_htr_request_list {F : Type}
    (s0 cur : PanSemStateFiniteExact 64 F) {Rl : List Ivl}
    (hAs0 : ArenaOK s0) (heff_cur : WorldEff s0 cur Rl sszBufs hpGw)
    {nw outw : BitVec 64}
    (hn_lk : cur.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hn_bound : nw.toNat < 2 ^ 46)
    (hout_lk : cur.locals.lookup (ofString "out") = some (.val (.word outw)))
    (hout_cov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_request_list)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_request_list)).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_request_list)).2 Rl sszBufs hpGw := by
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_htr_request_list,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_decCall_heap_mark heff_cur (ofString "mark") hnt (Or.inr (Or.inr (Or.inr hres)))
    (fun markw m1 _ _ hmark_al hmark_lo hmark_hi hm1_eq heff_m1 hnt1 hcr1 => ?_)
  have hm1_n : m1.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hn_lk,
      show ofString "mark" ≠ ofString "n" by decide]
  have hm1_out : m1.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hout_lk,
      show ofString "mark" ≠ ofString "out" by decide]
  have hm1_mark : m1.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  refine worldEff_decCall_alloc heff_m1 (by decide) (ofString "roots") _ hnt1 hcr1
    (fun rootsw rszw m2 hrsz_ev _ hm2_loc _ heff_m2 _ _ hroots_lo hroots_end _ _ hnt2 hcr2 => ?_)
  have hrsz_ev' : @evalHOLExact 64 F _ m1.toExact (fun a => Classical.propDecidable (m1.memaddrs a))
      (.op .add [.panop .mul [.var .local (ofString "n"), .const 32#64], .const 32#64]) =
      some (.val (.word (nw * 32#64 + 32#64))) := by
    simp [evalHOLExact, evalListHOLExact, toExact, hm1_n, panOpHOL,
      valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr]
  have hrsz_eq : rszw = nw * 32#64 + 32#64 := by
    rw [hrsz_ev'] at hrsz_ev; injection hrsz_ev with h; injection h with h'; injection h' with h''; exact h''.symm
  subst hrsz_eq
  have hrsz_nat : (nw * 32#64 + 32#64).toNat = nw.toNat * 32 + 32 := by
    have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
    have hm : (nw * 32#64).toNat = nw.toNat * 32 := by
      rw [BitVec.toNat_mul, h32]; exact Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_add_of_lt (by omega), hm, h32]
  have hroots_cap : rootsw.toNat + (nw.toNat * 32 + 32) ≤ heapLimit := by omega
  have hm2_roots : m2.locals.lookup (ofString "roots") = some (.val (.word rootsw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hm2_n : m2.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_n,
      show ofString "roots" ≠ ofString "n" by decide]
  have hm2_out : m2.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_out,
      show ofString "roots" ≠ ofString "out" by decide]
  have hm2_mark : m2.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_mark,
      show ofString "roots" ≠ ofString "mark" by decide]
  refine worldEff_dec heff_m2 (ofString "i") .one _ hnt2 hcr2
    (fun vi hvi _ hnt3 hcr3 => ?_)
  have hvi_eq : vi = .val (.word 0#64) := by
    simp [evalHOLExact] at hvi; exact hvi.symm
  subst hvi_eq
  let m3 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) m2
  have heff_m3 : WorldEff s0 m3 Rl sszBufs hpGw := heff_m2.locals_clock _ _
  let Inv : PanSemStateFiniteExact 64 F → Prop := fun st =>
    st.locals.lookup (ofString "roots") = some (.val (.word rootsw)) ∧
    st.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
    st.locals.lookup (ofString "out") = some (.val (.word outw)) ∧
    st.locals.lookup (ofString "mark") = some (.val (.word markw)) ∧
    ∃ iw : BitVec 64, st.locals.lookup (ofString "i") = some (.val (.word iw)) ∧ iw.toNat ≤ nw.toNat
  have hInv_m3 : Inv m3 := by
    refine ⟨?_, ?_, ?_, ?_, 0#64, ?_, Nat.zero_le _⟩ <;>
      simp [m3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        hm2_roots, hm2_n, hm2_out, hm2_mark,
        show ofString "i" ≠ ofString "roots" by decide,
        show ofString "i" ≠ ofString "n" by decide,
        show ofString "i" ≠ ofString "out" by decide,
        show ofString "i" ≠ ofString "mark" by decide]
  let eArg : ExpHOL 64 :=
    .op .add [.var .local (ofString "p"), .panop .mul [.var .local (ofString "i"), .var .local (ofString "sz")]]
  let oArg : ExpHOL 64 :=
    .op .add [.var .local (ofString "roots"), .panop .mul [.var .local (ofString "i"), .const 32#64]]
  let s0p : ProgHOL 64 :=
    .ite (.cmp .equal (.var .local (ofString "kind")) (.const 0#64))
      (.call (some (none, none)) (ofString "htr_deposit") [eArg, oArg]) .skip
  let s1p : ProgHOL 64 :=
    .ite (.cmp .equal (.var .local (ofString "kind")) (.const 1#64))
      (.call (some (none, none)) (ofString "htr_wdreq") [eArg, oArg]) .skip
  let s2p : ProgHOL 64 :=
    .ite (.cmp .equal (.var .local (ofString "kind")) (.const 2#64))
      (.call (some (none, none)) (ofString "htr_cons") [eArg, oArg]) .skip
  let s3p : ProgHOL 64 :=
    .ite (.cmp .equal (.var .local (ofString "kind")) (.const 3#64))
      (.call (some (none, none)) (ofString "htr_bdep") [eArg, oArg]) .skip
  let s4p : ProgHOL 64 :=
    .ite (.cmp .equal (.var .local (ofString "kind")) (.const 4#64))
      (.call (some (none, none)) (ofString "htr_bexit") [eArg, oArg]) .skip
  let incP : ProgHOL 64 :=
    .assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])
  let bodyR : ProgHOL 64 := .seq s0p (.seq s1p (.seq s2p (.seq s3p (.seq s4p incP))))
  have hnbR : ∀ t : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState t bodyR).1 ≠ some .break := by
    intro t
    exact seq_ne_break t (ite_call0_skip_ne_break t _ _ _) (fun t1 _ =>
      seq_ne_break t1 (ite_call0_skip_ne_break t1 _ _ _) (fun t2 _ =>
        seq_ne_break t2 (ite_call0_skip_ne_break t2 _ _ _) (fun t3 _ =>
          seq_ne_break t3 (ite_call0_skip_ne_break t3 _ _ _) (fun t4 _ =>
            seq_ne_break t4 (ite_call0_skip_ne_break t4 _ _ _) (fun t5 _ =>
              assign_local_ne_break t5 _ _)))))
  have hstepR : ∀ u (cw : BitVec 64),
      @evalHOLFinite 64 F _ u (fun a => Classical.propDecidable (u.memaddrs a))
        (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n"))) = some (.val (.word cw)) →
      cw ≠ 0 →
      WorldEff s0 (decClockHOLFinite u) Rl sszBufs hpGw → Inv (decClockHOLFinite u) →
      (evaluateHOLFiniteState (decClockHOLFinite u) bodyR).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState (decClockHOLFinite u) bodyR).1 →
      WorldEff s0 (evaluateHOLFiniteState (decClockHOLFinite u) bodyR).2 Rl sszBufs hpGw ∧
      (((evaluateHOLFiniteState (decClockHOLFinite u) bodyR).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite u) bodyR).1 = some .continue) →
        Inv (evaluateHOLFiniteState (decClockHOLFinite u) bodyR).2) := by
    intro u cw hcw hcw_ne heff_ud ⟨hu_roots, hu_n, hu_out, hu_mark, iw, hu_i, hi_le⟩ hnt_b hcr_b
    let ud := decClockHOLFinite u
    have hu_i0 : u.locals.lookup (ofString "i") = some (.val (.word iw)) := hu_i
    have hu_n0 : u.locals.lookup (ofString "n") = some (.val (.word nw)) := hu_n
    have hi_lt : iw.toNat < nw.toNat := by
      have hi63 : iw.toNat < 2 ^ 63 := by omega
      have hn63 : nw.toNat < 2 ^ 63 := by omega
      rw [evalHOLFinite_eq_toExact] at hcw
      simp only [evalHOLExact, toExact, hu_i0, hu_n0, Compiler.Encoders.Asm.wordCmpHOL,
        holAsmSignedLess_small iw nw hi63 hn63] at hcw
      by_cases hlt : iw.toNat < nw.toNat
      · exact hlt
      · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte] at hcw
        injection hcw with h1; injection h1 with h2; injection h2 with h3
        exact absurd h3.symm hcw_ne
    have hcov_i : OutIvlCovered s0 Rl (rootsw + iw * 32#64) := by
      apply outIvlCovered_heap_offset hroots_lo hroots_cap
      have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
      have hm : (iw * 32#64).toNat = iw.toNat * 32 := by
        rw [BitVec.toNat_mul, h32]; exact Nat.mod_eq_of_lt (by omega)
      omega
    have ho_ev : ∀ (st : PanSemStateFiniteExact 64 F),
        st.locals.lookup (ofString "roots") = some (.val (.word rootsw)) →
        st.locals.lookup (ofString "i") = some (.val (.word iw)) →
        @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) oArg =
          some (.val (.word (rootsw + iw * 32#64))) := by
      intro st hsr hsi
      simp [oArg, evalHOLExact, evalListHOLExact, toExact, hsr, hsi, panOpHOL,
        valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr]
    have hwe_b : WorldEff s0 (evaluateHOLFiniteState ud bodyR).2 Rl sszBufs hpGw := by
      dsimp only [bodyR] at hnt_b hcr_b ⊢
      refine worldEff_seq hnt_b hcr_b
        (fun hnt0 hcr0 => worldEff_ite_htr_leaf heff_ud _ _ _ _
          (fun hn0 hc0 => worldEff_call0_htr_deposit hAs0 heff_ud eArg oArg _
            (ho_ev ud hu_roots hu_i) hcov_i hn0 hc0) hnt0 hcr0)
        (fun b1 hb1 heff_b1 hnt1' hcr1' => ?_)
      have hb1_l : b1.locals = ud.locals := by
        have := ite_call0_skip_none_locals ud _ _ _ (by rw [hb1]); rwa [hb1] at this
      refine worldEff_seq hnt1' hcr1'
        (fun hnt0 hcr0 => worldEff_ite_htr_leaf heff_b1 _ _ _ _
          (fun hn0 hc0 => worldEff_call0_htr_wdreq hAs0 heff_b1 eArg oArg _
            (ho_ev b1 (by rw [hb1_l]; exact hu_roots) (by rw [hb1_l]; exact hu_i)) hcov_i hn0 hc0) hnt0 hcr0)
        (fun b2 hb2 heff_b2 hnt2' hcr2' => ?_)
      have hb2_l : b2.locals = ud.locals := by
        have := ite_call0_skip_none_locals b1 _ _ _ (by rw [hb2]); rw [hb2] at this; exact this.trans hb1_l
      refine worldEff_seq hnt2' hcr2'
        (fun hnt0 hcr0 => worldEff_ite_htr_leaf heff_b2 _ _ _ _
          (fun hn0 hc0 => worldEff_call0_htr_cons hAs0 heff_b2 eArg oArg _
            (ho_ev b2 (by rw [hb2_l]; exact hu_roots) (by rw [hb2_l]; exact hu_i)) hcov_i hn0 hc0) hnt0 hcr0)
        (fun b3 hb3 heff_b3 hnt3' hcr3' => ?_)
      have hb3_l : b3.locals = ud.locals := by
        have := ite_call0_skip_none_locals b2 _ _ _ (by rw [hb3]); rw [hb3] at this; exact this.trans hb2_l
      refine worldEff_seq hnt3' hcr3'
        (fun hnt0 hcr0 => worldEff_ite_htr_leaf heff_b3 _ _ _ _
          (fun hn0 hc0 => worldEff_call0_htr_bdep hAs0 heff_b3 eArg oArg _
            (ho_ev b3 (by rw [hb3_l]; exact hu_roots) (by rw [hb3_l]; exact hu_i)) hcov_i hn0 hc0) hnt0 hcr0)
        (fun b4 hb4 heff_b4 hnt4' hcr4' => ?_)
      have hb4_l : b4.locals = ud.locals := by
        have := ite_call0_skip_none_locals b3 _ _ _ (by rw [hb4]); rw [hb4] at this; exact this.trans hb3_l
      refine worldEff_seq hnt4' hcr4'
        (fun hnt0 hcr0 => worldEff_ite_htr_leaf heff_b4 _ _ _ _
          (fun hn0 hc0 => worldEff_call0_htr_bexit hAs0 heff_b4 eArg oArg _
            (ho_ev b4 (by rw [hb4_l]; exact hu_roots) (by rw [hb4_l]; exact hu_i)) hcov_i hn0 hc0) hnt0 hcr0)
        (fun b5 _ heff_b5 _ _ => worldEff_assign_local heff_b5 _ _)
    refine ⟨hwe_b, fun hfl_b => ?_⟩
    dsimp only [bodyR] at hfl_b ⊢
    refine seq_ite_call0_skip_flow ud _ _ _ _ Inv hfl_b (fun b1 hb1_l hfl1 => ?_)
    refine seq_ite_call0_skip_flow b1 _ _ _ _ Inv hfl1 (fun b2 hb2_l hfl2 => ?_)
    refine seq_ite_call0_skip_flow b2 _ _ _ _ Inv hfl2 (fun b3 hb3_l hfl3 => ?_)
    refine seq_ite_call0_skip_flow b3 _ _ _ _ Inv hfl3 (fun b4 hb4_l hfl4 => ?_)
    refine seq_ite_call0_skip_flow b4 _ _ _ _ Inv hfl4 (fun b5 hb5_l _ => ?_)
    have hb5_ud : b5.locals = ud.locals :=
      hb5_l.trans (hb4_l.trans (hb3_l.trans (hb2_l.trans hb1_l)))
    have hb5_i : b5.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hb5_ud]; exact hu_i
    have hi1_ev : @evalHOLExact 64 F _ b5.toExact (fun a => Classical.propDecidable (b5.memaddrs a))
        (.op .add [.var .local (ofString "i"), .const 1#64]) = some (.val (.word (iw + 1#64))) := by
      simp [evalHOLExact, evalListHOLExact, toExact, hb5_i,
        valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr]
    have hvv_i : isValidValueHOLFinite b5 .local (ofString "i") (.val (.word (iw + 1#64))) = true := by
      simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, toExact, hb5_i,
        shapeOfHOLExact, shapeEqHOL]
    have ha_i : evaluateHOLFiniteState b5 incP =
        (none, setVarHOLFinite (ofString "i") (.val (.word (iw + 1#64))) b5) := by
      dsimp only [incP]; rw [evaluateHOLFiniteState_assign, hi1_ev]; dsimp only; rw [if_pos hvv_i]; rfl
    rw [ha_i]
    have hi_add : (iw + 1#64).toNat = iw.toNat + 1 := by
      have : (1#64 : BitVec 64).toNat = 1 := rfl
      exact BitVec.toNat_add_of_lt (by omega)
    have hu_r' : ud.locals.lookup (ofString "roots") = some (.val (.word rootsw)) := hu_roots
    have hu_n' : ud.locals.lookup (ofString "n") = some (.val (.word nw)) := hu_n
    have hu_o' : ud.locals.lookup (ofString "out") = some (.val (.word outw)) := hu_out
    have hu_m' : ud.locals.lookup (ofString "mark") = some (.val (.word markw)) := hu_mark
    refine ⟨?_, ?_, ?_, ?_, iw + 1#64, ?_, by omega⟩ <;>
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hb5_ud,
        hu_r', hu_n', hu_o', hu_m',
        show ofString "i" ≠ ofString "roots" by decide,
        show ofString "i" ≠ ofString "n" by decide,
        show ofString "i" ≠ ofString "out" by decide,
        show ofString "i" ≠ ofString "mark" by decide]
  refine worldEff_seq hnt3 hcr3
    (fun hnt_w hcr_w =>
      (worldEff_while_cond_post (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n")))
        Inv (fun u hu => hu) hstepR m3.clock m3 rfl heff_m3 hInv_m3 hnt_w hcr_w).1)
    (fun m4 hm4 heff_m4 hnt4 hcr4 => ?_)
  have hInv_m4 : Inv m4 := by
    have hp := (worldEff_while_cond_post (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n")))
      Inv (fun u hu => hu) hstepR m3.clock m3 rfl heff_m3 hInv_m3
      (by rw [hm4]; simp) (by rw [hm4]; exact Or.inl rfl)).2 (by rw [hm4]) (fun t _ => hnbR t)
    rw [hm4] at hp; exact hp.1
  obtain ⟨hm4_roots, hm4_n, hm4_out, hm4_mark, _⟩ := hInv_m4
  refine worldEff_seq hnt4 hcr4
    (fun hnt_pc hcr_pc =>
      worldEff_call0_htr_plist_chunks hAs0 heff_m4
        (.var .local (ofString "roots")) (.var .local (ofString "n")) (.var .local (ofString "n"))
        (.var .local (ofString "out")) nw outw
        (by simp [evalHOLExact, toExact, hm4_n]) hn_bound
        (by simp [evalHOLExact, toExact, hm4_out]) hout_cov hnt_pc hcr_pc)
    (fun m5 hm5 heff_m5 hnt5 hcr5 => ?_)
  have hm5_loc : m5.locals = m4.locals := by
    have := call0_none_locals m4 (ofString "htr_plist_chunks") _ (by rw [hm5]); rwa [hm5] at this
  refine worldEff_seq hnt5 hcr5
    (fun hnt_hr _ =>
      (worldEff_call0_heap_release hAs0 heff_m5 (by decide) hp_no_gb
        (.var .local (ofString "mark")) markw
        (by simp [evalHOLExact, toExact, hm5_loc, hm4_mark])
        hmark_lo hmark_hi hmark_al hnt_hr).2.choose_spec.2)
    (fun m6 _ heff_m6 _ _ => worldEff_return heff_m6 _)

private theorem worldEff_call0_htr_request_list {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hAs0 : ArenaOK s0) (heff : WorldEff s0 cur Rl sszBufs hpGw)
    (kindExp pExp nExp szExp outExp : ExpHOL 64) (nw outw : BitVec 64)
    (hn : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      nExp = some (.val (.word nw)))
    (hn_bound : nw.toNat < 2 ^ 46)
    (hout : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      outExp = some (.val (.word outw)))
    (hcov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_request_list")
      [kindExp, pExp, nExp, szExp, outExp])).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_request_list")
      [kindExp, pExp, nExp, szExp, outExp])).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_request_list")
      [kindExp, pExp, nExp, szExp, outExp])).2 Rl sszBufs hpGw := by
  refine worldEff_call0_eff heff (ofString "htr_request_list") [kindExp, pExp, nExp, szExp, outExp]
    _ _ _ lookup_htr_request_list (fun callee vals hargs hl hnt_e hres_e => ?_) hnt hcr
  rw [heff.code] at hl
  obtain ⟨kw, pw, nw', szw, ow, rfl, _, _, hn', _, ho⟩ :=
    lookupCode_five_words (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      lookup_htr_request_list hl
  have hnw_eq : nw' = nw ∧ ow = outw := by
    rw [evalListHOLFinite_eq_toExact] at hargs
    simp only [evalListHOLExact, hn, hout] at hargs
    rcases hk0 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) kindExp with _ | vk
    · simp [hk0] at hargs
    · rcases hp0 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) pExp with _ | vp
      · simp [hk0, hp0] at hargs
      · rcases hs0 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) szExp with _ | vs
        · simp [hk0, hp0, hs0] at hargs
        · simp only [hk0, hp0, hs0] at hargs
          injection hargs with h0
          injection h0 with _ h1
          injection h1 with _ h2
          injection h2 with h3 h4
          injection h3 with h3'; injection h3' with h3''
          injection h4 with _ h5
          injection h5 with h6 _; injection h6 with h6'; injection h6' with h6''
          exact ⟨h3''.symm, h6''.symm⟩
  obtain ⟨rfl, rfl⟩ := hnw_eq
  exact worldEff_htr_request_list s0 (callEntryStateHOLFinite cur callee) hAs0
    (heff.locals_clock _ _) hn' hn_bound ho hcov hnt_e hres_e

private theorem memW_eq_of_worldEff_ivl {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (hAs0 : ArenaOK s0) (heff : WorldEff s0 cur Rl B gw)
    {iv : Ivl}
    (hiv_in : Inside iv sourceBase (globN s0 "heap_ptr"))
    (hdisj_R : ∀ j ∈ Rl, Disj iv j)
    (hdisj_B : ∀ gs ∈ B, Disj iv (bufferRegion s0 gs))
    {off : Nat} (hoff : off + 8 ≤ iv.2) :
    memW cur (iv.1 + off) = memW s0 (iv.1 + off) := by
  have hhl_ss : heapLimit ≤ scratchStart := by decide
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hhp_lim : globN s0 "heap_ptr" ≤ heapLimit := hAs0.2.1
  have hfm_lo : scratchStart ≤ globN s0 "frame_mem_ptr" := hAs0.2.2.1
  unfold Inside at hiv_in
  have ha_lt : iv.1 + off < 2 ^ 64 := by omega
  let a : BitVec 64 := BitVec.ofNat 64 (iv.1 + off)
  have ha_nat : a.toNat = iv.1 + off := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
  by_cases hmem : cur.memory a = s0.memory a
  · unfold memW; change (match cur.memory a with | .word w => w.toNat) = (match s0.memory a with | .word w => w.toNat)
    rw [hmem]
  · exfalso
    rcases heff.cell_frame a hmem with ⟨j, hj, hpos, hc1, hc2⟩ | ⟨gs, hgs, hpos, hc1, hc2⟩ | ⟨hpos, hc1, hc2⟩ | ⟨hpos, hc1, hc2⟩
    · rw [ha_nat] at hc1 hc2
      have hd := hdisj_R j hj
      unfold Disj at hd; omega
    · rw [ha_nat] at hc1 hc2
      have hd := hdisj_B gs hgs
      unfold Disj at hd; omega
    · rw [ha_nat] at hc1 hc2
      dsimp only [freeGap] at hpos hc1 hc2; omega
    · rw [ha_nat] at hc1 hc2
      dsimp only [heapFree] at hpos hc1 hc2; omega

private theorem eval_load_add_value {F : Type}
    {cur : PanSemStateFiniteExact 64 F} {baseVar : MlS} {basew : BitVec 64} {off : Nat} {v : ValueHOL 64}
    (hbase : cur.locals.lookup baseVar = some (.val (.word basew)))
    (hoff_lt : basew.toNat + off < 2 ^ 64)
    (hoff_64 : off < 2 ^ 64)
    (hev : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      (.load .one (.op .add [.var .local baseVar, .const (BitVec.ofNat 64 off)])) =
      some v) :
    ∃ vw : BitVec 64, v = .val (.word vw) ∧ vw.toNat = memW cur (basew.toNat + off) := by
  have hadd_ev : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      (.op .add [.var .local baseVar, .const (BitVec.ofNat 64 off)]) =
      some (.val (.word (basew + BitVec.ofNat 64 off))) := by
    simp [evalHOLExact, evalListHOLExact, toExact, hbase,
      valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr]
  unfold evalHOLExact at hev
  rw [hadd_ev] at hev
  by_cases hdom : cur.memaddrs (basew + BitVec.ofNat 64 off)
  · rcases hcell : cur.memory (basew + BitVec.ofNat 64 off) with ⟨w⟩
    simp [isWfShapeExactHOL, memLoadHOLExact, panMemLoadHOL, toExact, hdom, hcell] at hev
    refine ⟨w, hev.symm, ?_⟩
    have hbv_eq : basew + BitVec.ofNat 64 off = BitVec.ofNat 64 (basew.toNat + off) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff_64,
        Nat.mod_eq_of_lt hoff_lt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff_lt]
    rw [hbv_eq] at hcell
    simp [memW, hcell]
  · simp [isWfShapeExactHOL, memLoadHOLExact, panMemLoadHOL, toExact, hdom] at hev

private theorem eval_load_add_memW {F : Type}
    {cur : PanSemStateFiniteExact 64 F} {baseVar : MlS} {basew : BitVec 64} {off : Nat} {vw : BitVec 64}
    (hbase : cur.locals.lookup baseVar = some (.val (.word basew)))
    (hoff_lt : basew.toNat + off < 2 ^ 64)
    (hoff_64 : off < 2 ^ 64)
    (hev : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      (.load .one (.op .add [.var .local baseVar, .const (BitVec.ofNat 64 off)])) =
      some (.val (.word vw))) :
    vw.toNat = memW cur (basew.toNat + off) := by
  obtain ⟨w, hw, hmem⟩ := eval_load_add_value hbase hoff_lt hoff_64 hev
  injection hw with h1; injection h1 with h2
  subst h2; exact hmem

private theorem worldEff_htr_requests {F : Type}
    (s0 cur : PanSemStateFiniteExact 64 F) {Rl : List Ivl}
    (hAs0 : ArenaOK s0) (heff_cur : WorldEff s0 cur Rl sszBufs hpGw)
    {rqw outw : BitVec 64}
    (hrq_lk : cur.locals.lookup (ofString "rq") = some (.val (.word rqw)))
    (hrq_in : Inside (rqw.toNat, 80) sourceBase (globN s0 "heap_ptr"))
    (hrq_disj_R : ∀ j ∈ Rl, Disj (rqw.toNat, 80) j)
    (hrq_disj_B : ∀ gs ∈ sszBufs, Disj (rqw.toNat, 80) (bufferRegion s0 gs))
    (hrq_at : RequestsAt s0 rqw.toNat)
    (hout_lk : cur.locals.lookup (ofString "out") = some (.val (.word outw)))
    (hout_cov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_requests)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_requests)).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_requests)).2 Rl sszBufs hpGw := by
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hhp_lim : globN s0 "heap_ptr" ≤ heapLimit := hAs0.2.1
  have hrq_hi : rqw.toNat + 80 ≤ heapLimit := le_trans hrq_in.2 hhp_lim
  have hrq_cnt_lt : ∀ idx : Nat, idx < 5 → memW s0 (rqw.toNat + 16 * idx + 8) < 2 ^ 46 := by
    intro idx hidx
    have hb := hrq_at.2 idx hidx
    omega
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_htr_requests,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_decCall_heap_mark heff_cur (ofString "mark") hnt (Or.inr (Or.inr (Or.inr hres)))
    (fun markw m1 _ _ hmark_al hmark_lo hmark_hi hm1_eq heff_m1 hnt1 hcr1 => ?_)
  have hm1_rq : m1.locals.lookup (ofString "rq") = some (.val (.word rqw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hrq_lk,
      show ofString "mark" ≠ ofString "rq" by decide]
  have hm1_out : m1.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hout_lk,
      show ofString "mark" ≠ ofString "out" by decide]
  have hm1_mark : m1.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  refine worldEff_decCall_alloc heff_m1 (by decide) (ofString "ch") _ hnt1 hcr1
    (fun chw szw m2 hsz_ev _ hm2_loc _ heff_m2 _ _ hch_lo hch_end _ _ hnt2 hcr2 => ?_)
  have hsz_eq : szw = 160#64 := by
    simp [evalHOLExact, evalListHOLExact, valueIsWord, valueWord, panOpHOL] at hsz_ev
    exact hsz_ev.symm
  subst hsz_eq
  have hch_cap : chw.toNat + 160 ≤ heapLimit := by
    have : (160#64 : BitVec 64).toNat = 160 := rfl
    omega
  have hm2_ch : m2.locals.lookup (ofString "ch") = some (.val (.word chw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hm2_rq : m2.locals.lookup (ofString "rq") = some (.val (.word rqw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_rq,
      show ofString "ch" ≠ ofString "rq" by decide]
  have hm2_out : m2.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_out,
      show ofString "ch" ≠ ofString "out" by decide]
  have hm2_mark : m2.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_mark,
      show ofString "ch" ≠ ofString "mark" by decide]
  have hrl_call : ∀ {st : PanSemStateFiniteExact 64 F} (heff_st : WorldEff s0 st Rl sszBufs hpGw)
      (hst_rq : st.locals.lookup (ofString "rq") = some (.val (.word rqw)))
      (kindw szcw : BitVec 64) (pOff nOff idx : Nat)
      (hidx : idx < 5) (hnOff : nOff = 16 * idx + 8)
      (houtExp : ExpHOL 64) (hchOut : BitVec 64)
      (hout_ev : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
        houtExp = some (.val (.word hchOut)))
      (hcov_out : OutIvlCovered s0 Rl hchOut)
      (hnt_c : (evaluateHOLFiniteState st (.call (some (none, none)) (ofString "htr_request_list")
        [.const kindw,
         .load .one (.op .add [.var .local (ofString "rq"), .const (BitVec.ofNat 64 pOff)]),
         .load .one (.op .add [.var .local (ofString "rq"), .const (BitVec.ofNat 64 nOff)]),
         .const szcw, houtExp])).1 ≠ some .timeOut)
      (hcr_c : ContOrRes (evaluateHOLFiniteState st (.call (some (none, none)) (ofString "htr_request_list")
        [.const kindw,
         .load .one (.op .add [.var .local (ofString "rq"), .const (BitVec.ofNat 64 pOff)]),
         .load .one (.op .add [.var .local (ofString "rq"), .const (BitVec.ofNat 64 nOff)]),
         .const szcw, houtExp])).1),
      WorldEff s0 (evaluateHOLFiniteState st (.call (some (none, none)) (ofString "htr_request_list")
        [.const kindw,
         .load .one (.op .add [.var .local (ofString "rq"), .const (BitVec.ofNat 64 pOff)]),
         .load .one (.op .add [.var .local (ofString "rq"), .const (BitVec.ofNat 64 nOff)]),
         .const szcw, houtExp])).2 Rl sszBufs hpGw := by
    intro st heff_st hst_rq kindw szcw pOff nOff idx hidx hnOff houtExp hchOut hout_ev hcov_out hnt_c hcr_c
    rcases hn_ev : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "rq"), .const (BitVec.ofNat 64 nOff)])) with _ | vn
    · rw [evaluateHOLFiniteState_call, evalListHOLFinite_eq_toExact]
      have hlist_none : @evalListHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
          [.const kindw,
           .load .one (.op .add [.var .local (ofString "rq"), .const (BitVec.ofNat 64 pOff)]),
           .load .one (.op .add [.var .local (ofString "rq"), .const (BitVec.ofNat 64 nOff)]),
           .const szcw, houtExp] = none := by
        simp only [evalListHOLExact, hn_ev]
        rcases @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
            (.const kindw) with _ | _
        · rfl
        · rcases @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
              (.load .one (.op .add [.var .local (ofString "rq"), .const (BitVec.ofNat 64 pOff)])) with _ | _ <;>
            rfl
      rw [hlist_none]; exact heff_st
    · obtain ⟨nw, rfl, hn_mem⟩ := eval_load_add_value hst_rq (by omega) (by omega) hn_ev
      have hn_eq : nw.toNat = memW s0 (rqw.toNat + 16 * idx + 8) := by
        subst hnOff
        have h2 := memW_eq_of_worldEff_ivl hAs0 heff_st hrq_in hrq_disj_R hrq_disj_B
          (off := 16 * idx + 8) (by omega)
        dsimp only at h2
        rw [hn_mem, h2, Nat.add_assoc]
      exact worldEff_call0_htr_request_list hAs0 heff_st _ _ _ _ houtExp nw hchOut
        hn_ev (by rw [hn_eq]; exact hrq_cnt_lt idx hidx) hout_ev hcov_out hnt_c hcr_c
  refine worldEff_seq hnt2 hcr2
    (fun hnt_c0 hcr_c0 =>
      hrl_call heff_m2 hm2_rq 0#64 192#64 0 8 0 (by decide) rfl
        (.var .local (ofString "ch")) chw
        (by simp [evalHOLExact, toExact, hm2_ch]) (Or.inr ⟨hch_lo, by omega⟩) hnt_c0 hcr_c0)
    (fun m3 hm3 heff_m3 hnt3 hcr3 => ?_)
  have hm3_loc : m3.locals = m2.locals := by
    have := call0_none_locals m2 (ofString "htr_request_list") _ (by rw [hm3]); rwa [hm3] at this
  refine worldEff_seq hnt3 hcr3
    (fun hnt_c1 hcr_c1 =>
      hrl_call heff_m3 (by rw [hm3_loc]; exact hm2_rq) 1#64 76#64 16 24 1 (by decide) rfl
        (.op .add [.var .local (ofString "ch"), .const 32#64]) (chw + 32#64)
        (by simp [evalHOLExact, evalListHOLExact, toExact, hm3_loc, hm2_ch,
              valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr])
        (outIvlCovered_heap_offset hch_lo hch_cap (by decide)) hnt_c1 hcr_c1)
    (fun m4 hm4 heff_m4 hnt4 hcr4 => ?_)
  have hm4_loc : m4.locals = m2.locals := by
    have := call0_none_locals m3 (ofString "htr_request_list") _ (by rw [hm4])
    rw [hm4] at this; exact this.trans hm3_loc
  refine worldEff_seq hnt4 hcr4
    (fun hnt_c2 hcr_c2 =>
      hrl_call heff_m4 (by rw [hm4_loc]; exact hm2_rq) 2#64 116#64 32 40 2 (by decide) rfl
        (.op .add [.var .local (ofString "ch"), .const 64#64]) (chw + 64#64)
        (by simp [evalHOLExact, evalListHOLExact, toExact, hm4_loc, hm2_ch,
              valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr])
        (outIvlCovered_heap_offset hch_lo hch_cap (by decide)) hnt_c2 hcr_c2)
    (fun m5 hm5 heff_m5 hnt5 hcr5 => ?_)
  have hm5_loc : m5.locals = m2.locals := by
    have := call0_none_locals m4 (ofString "htr_request_list") _ (by rw [hm5])
    rw [hm5] at this; exact this.trans hm4_loc
  refine worldEff_seq hnt5 hcr5
    (fun hnt_c3 hcr_c3 =>
      hrl_call heff_m5 (by rw [hm5_loc]; exact hm2_rq) 3#64 184#64 48 56 3 (by decide) rfl
        (.op .add [.var .local (ofString "ch"), .const 96#64]) (chw + 96#64)
        (by simp [evalHOLExact, evalListHOLExact, toExact, hm5_loc, hm2_ch,
              valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr])
        (outIvlCovered_heap_offset hch_lo hch_cap (by decide)) hnt_c3 hcr_c3)
    (fun m6 hm6 heff_m6 hnt6 hcr6 => ?_)
  have hm6_loc : m6.locals = m2.locals := by
    have := call0_none_locals m5 (ofString "htr_request_list") _ (by rw [hm6])
    rw [hm6] at this; exact this.trans hm5_loc
  refine worldEff_seq hnt6 hcr6
    (fun hnt_c4 hcr_c4 =>
      hrl_call heff_m6 (by rw [hm6_loc]; exact hm2_rq) 4#64 68#64 64 72 4 (by decide) rfl
        (.op .add [.var .local (ofString "ch"), .const 128#64]) (chw + 128#64)
        (by simp [evalHOLExact, evalListHOLExact, toExact, hm6_loc, hm2_ch,
              valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr])
        (outIvlCovered_heap_offset hch_lo hch_cap (by decide)) hnt_c4 hcr_c4)
    (fun m7 hm7 heff_m7 hnt7 hcr7 => ?_)
  have hm7_loc : m7.locals = m2.locals := by
    have := call0_none_locals m6 (ofString "htr_request_list") _ (by rw [hm7])
    rw [hm7] at this; exact this.trans hm6_loc
  refine worldEff_seq hnt7 hcr7
    (fun hnt_pc hcr_pc =>
      worldEff_call0_htr_pcontainer hAs0 heff_m7
        (.var .local (ofString "ch")) (.const 5#64) (.var .local (ofString "out"))
        5#64 outw
        (by simp [evalHOLExact]) (by decide)
        (by simp [evalHOLExact, toExact, hm7_loc, hm2_out]) hout_cov hnt_pc hcr_pc)
    (fun m8 hm8 heff_m8 hnt8 hcr8 => ?_)
  have hm8_loc : m8.locals = m2.locals := by
    have := call0_none_locals m7 (ofString "htr_pcontainer") _ (by rw [hm8])
    rw [hm8] at this; exact this.trans hm7_loc
  refine worldEff_seq hnt8 hcr8
    (fun hnt_hr _ =>
      (worldEff_call0_heap_release hAs0 heff_m8 (by decide) hp_no_gb
        (.var .local (ofString "mark")) markw
        (by simp [evalHOLExact, toExact, hm8_loc, hm2_mark])
        hmark_lo hmark_hi hmark_al hnt_hr).2.choose_spec.2)
    (fun m9 _ heff_m9 _ _ => worldEff_return heff_m9 _)

private theorem worldEff_call0_htr_requests {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hAs0 : ArenaOK s0) (heff : WorldEff s0 cur Rl sszBufs hpGw)
    (rqExp outExp : ExpHOL 64) (rqw outw : BitVec 64)
    (hrq : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      rqExp = some (.val (.word rqw)))
    (hrq_in : Inside (rqw.toNat, 80) sourceBase (globN s0 "heap_ptr"))
    (hrq_disj_R : ∀ j ∈ Rl, Disj (rqw.toNat, 80) j)
    (hrq_disj_B : ∀ gs ∈ sszBufs, Disj (rqw.toNat, 80) (bufferRegion s0 gs))
    (hrq_at : RequestsAt s0 rqw.toNat)
    (hout : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      outExp = some (.val (.word outw)))
    (hcov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_requests")
      [rqExp, outExp])).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_requests")
      [rqExp, outExp])).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_requests")
      [rqExp, outExp])).2 Rl sszBufs hpGw := by
  refine worldEff_call0_eff heff (ofString "htr_requests") [rqExp, outExp]
    _ _ _ lookup_htr_requests (fun callee vals hargs hl hnt_e hres_e => ?_) hnt hcr
  rw [heff.code] at hl
  obtain ⟨rw', ow, rfl, hr', ho⟩ := lookupCode_two_words (by decide) lookup_htr_requests hl
  have heq : rw' = rqw ∧ ow = outw := by
    rw [evalListHOLFinite_eq_toExact] at hargs
    simp only [evalListHOLExact, hrq, hout] at hargs
    injection hargs with h0
    injection h0 with h1 h2
    injection h1 with h1'; injection h1' with h1''
    injection h2 with h2' _; injection h2' with h2''; injection h2'' with h2'''
    exact ⟨h1''.symm, h2'''.symm⟩
  obtain ⟨rfl, rfl⟩ := heq
  exact worldEff_htr_requests s0 (callEntryStateHOLFinite cur callee) hAs0
    (heff.locals_clock _ _) hr' hrq_in hrq_disj_R hrq_disj_B hrq_at ho hcov hnt_e hres_e

private theorem worldEff_seq_call0 {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    {fn : MlS} {args : List (ExpHOL 64)} {q : ProgHOL 64}
    (hnt : (evaluateHOLFiniteState cur (.seq (.call (some (none, none)) fn args) q)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.seq (.call (some (none, none)) fn args) q)).1)
    (hcall : (evaluateHOLFiniteState cur (.call (some (none, none)) fn args)).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState cur (.call (some (none, none)) fn args)).1 →
      WorldEff s0 (evaluateHOLFiniteState cur (.call (some (none, none)) fn args)).2 Rl B gw)
    (hk : ∀ next, next.locals = cur.locals → WorldEff s0 next Rl B gw →
      (evaluateHOLFiniteState next q).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState next q).1 →
      WorldEff s0 (evaluateHOLFiniteState next q).2 Rl B gw) :
    WorldEff s0 (evaluateHOLFiniteState cur (.seq (.call (some (none, none)) fn args) q)).2 Rl B gw :=
  worldEff_seq hnt hcr hcall (fun next hnone heff_next hnt_q hcr_q =>
    hk next (by have := call0_none_locals cur fn args (by rw [hnone]); rwa [hnone] at this)
      heff_next hnt_q hcr_q)

private theorem seq_call0_flow {F : Type}
    (u : PanSemStateFiniteExact 64 F) (fn : MlS) (args : List (ExpHOL 64)) (q : ProgHOL 64)
    (P : PanSemStateFiniteExact 64 F → Prop)
    (hfl : (evaluateHOLFiniteState u (.seq (.call (some (none, none)) fn args) q)).1 = none ∨
           (evaluateHOLFiniteState u (.seq (.call (some (none, none)) fn args) q)).1 = some .continue)
    (hk : ∀ u1, u1.locals = u.locals →
      ((evaluateHOLFiniteState u1 q).1 = none ∨ (evaluateHOLFiniteState u1 q).1 = some .continue) →
      P (evaluateHOLFiniteState u1 q).2) :
    P (evaluateHOLFiniteState u (.seq (.call (some (none, none)) fn args) q)).2 := by
  rw [evaluateHOLFiniteState_seq_line780] at hfl ⊢
  dsimp only at hfl ⊢
  cases hr : (evaluateHOLFiniteState u (.call (some (none, none)) fn args)).1 with
  | some rx =>
    rw [hr] at hfl
    dsimp only at hfl
    rcases hfl with h | h
    · exact absurd (hr.symm.trans h) (by simp)
    · exact absurd h (call0_ne_continue u fn args)
  | none =>
    rw [hr] at hfl
    dsimp only at hfl ⊢
    exact hk _ (call0_none_locals u fn args hr) hfl

private theorem worldEff_htr_payload {F : Type}
    (s0 cur : PanSemStateFiniteExact 64 F) {Rl : List Ivl}
    (hAs0 : ArenaOK s0) (heff_cur : WorldEff s0 cur Rl sszBufs hpGw)
    {plw outw : BitVec 64}
    (hpl_lk : cur.locals.lookup (ofString "pl") = some (.val (.word plw)))
    (hpl_in : Inside (plw.toNat, 136) sourceBase (globN s0 "heap_ptr"))
    (hpl_disj_R : ∀ j ∈ Rl, Disj (plw.toNat, 136) j)
    (hpl_disj_B : ∀ gs ∈ sszBufs, Disj (plw.toNat, 136) (bufferRegion s0 gs))
    (hpl_at : PayloadAt s0 plw.toNat)
    (hnwd_lt : memW s0 (plw.toNat + 56) < 2 ^ 32)
    (hout_lk : cur.locals.lookup (ofString "out") = some (.val (.word outw)))
    (hout_cov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_payload)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_payload)).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_payload)).2 Rl sszBufs hpGw := by
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hhp0_le : globN s0 "heap_ptr" ≤ heapLimit := hAs0.2.1
  have hpl_hi : plw.toNat + 136 ≤ 2 ^ 64 := by unfold Inside at hpl_in; omega
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_htr_payload,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_dec heff_cur (ofString "raw") .one _ hnt (Or.inr (Or.inr (Or.inr hres)))
    (fun vraw hvraw hvsh_raw hnt0 hcr0 => ?_)
  rcases vraw with ⟨⟨raww⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hvsh_raw)
  let m0 := setVarHOLFinite (ofString "raw") (.val (.word raww)) cur
  have heff_m0 : WorldEff s0 m0 Rl sszBufs hpGw := heff_cur.locals_clock _ _
  have hm0_pl : m0.locals.lookup (ofString "pl") = some (.val (.word plw)) := by
    simp [m0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hpl_lk,
      show ofString "raw" ≠ ofString "pl" by decide]
  have hm0_out : m0.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    simp [m0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hout_lk,
      show ofString "raw" ≠ ofString "out" by decide]
  refine worldEff_decCall_heap_mark heff_m0 (ofString "mark") hnt0 hcr0
    (fun markw m1 _ _ hmark_al hmark_lo hmark_hi hm1_eq heff_m1 hnt1 hcr1 => ?_)
  have hm1_pl : m1.locals.lookup (ofString "pl") = some (.val (.word plw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm0_pl,
      show ofString "mark" ≠ ofString "pl" by decide]
  have hm1_out : m1.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm0_out,
      show ofString "mark" ≠ ofString "out" by decide]
  have hm1_mark : m1.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  refine worldEff_decCall_alloc heff_m1 (by decide) (ofString "ch") _ hnt1 hcr1
    (fun chw szw m2 hsz_ev _ hm2_loc _ heff_m2 _ _ hch_lo hch_end hhp_m2 _ hnt2 hcr2 => ?_)
  have hsz_eq : szw = 608#64 := by
    simp [evalHOLExact, evalListHOLExact, panOpHOL, valueIsWord, valueWord] at hsz_ev
    exact hsz_ev.symm
  subst hsz_eq
  have hch_cap : chw.toNat + 608 ≤ heapLimit := by
    have : (608#64 : BitVec 64).toNat = 608 := rfl
    omega
  have hm2_ch : m2.locals.lookup (ofString "ch") = some (.val (.word chw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hm2_pl : m2.locals.lookup (ofString "pl") = some (.val (.word plw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_pl,
      show ofString "ch" ≠ ofString "pl" by decide]
  have hm2_out : m2.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_out,
      show ofString "ch" ≠ ofString "out" by decide]
  have hm2_mark : m2.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_mark,
      show ofString "ch" ≠ ofString "mark" by decide]
  have hch_add : ∀ (st : PanSemStateFiniteExact 64 F) (off : BitVec 64),
      st.locals = m2.locals →
      @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
        (.op .add [.var .local (ofString "ch"), .const off]) = some (.val (.word (chw + off))) := by
    intro st off hst_loc
    simp [evalHOLExact, evalListHOLExact, toExact, hst_loc, hm2_ch,
      valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr]
  -- 12 sequential field chunks at ch + 0..384
  refine worldEff_seq_call0 hnt2 hcr2
    (fun hn hc => (worldEff_call0_memcpy_word heff_m2
      (.var .local (ofString "ch")) _ (.const 32#64) chw 32#64
      (by simp [evalHOLExact, toExact, hm2_ch]) (by simp [evalHOLExact])
      (fun _ _ => outIvlCovered_to_world (Or.inr ⟨hch_lo, by omega⟩) 32 le_rfl) hn hc).1)
    (fun s1 hs1_loc heff_s1 hnt_s1 hcr_s1 => ?_)
  refine worldEff_seq_call0 hnt_s1 hcr_s1
    (fun hn hc => worldEff_call0_htr_bytes_vector hAs0 heff_s1 _ _ _ (chw + 32#64)
      (hch_add s1 32#64 hs1_loc) (outIvlCovered_heap_offset hch_lo hch_cap (by decide)) hn hc)
    (fun s2 hs2_loc heff_s2 hnt_s2 hcr_s2 => ?_)
  have hs2_m2 : s2.locals = m2.locals := hs2_loc.trans hs1_loc
  refine worldEff_seq_call0 hnt_s2 hcr_s2
    (fun hn hc => (worldEff_call0_memcpy_word heff_s2 _ _ (.const 32#64) (chw + 64#64) 32#64
      (hch_add s2 64#64 hs2_m2) (by simp [evalHOLExact])
      (fun _ _ => outIvlCovered_to_world (outIvlCovered_heap_offset hch_lo hch_cap (by decide)) 32 le_rfl) hn hc).1)
    (fun s3 hs3_loc heff_s3 hnt_s3 hcr_s3 => ?_)
  have hs3_m2 : s3.locals = m2.locals := hs3_loc.trans hs2_m2
  refine worldEff_seq_call0 hnt_s3 hcr_s3
    (fun hn hc => (worldEff_call0_memcpy_word heff_s3 _ _ (.const 32#64) (chw + 96#64) 32#64
      (hch_add s3 96#64 hs3_m2) (by simp [evalHOLExact])
      (fun _ _ => outIvlCovered_to_world (outIvlCovered_heap_offset hch_lo hch_cap (by decide)) 32 le_rfl) hn hc).1)
    (fun s4 hs4_loc heff_s4 hnt_s4 hcr_s4 => ?_)
  have hs4_m2 : s4.locals = m2.locals := hs4_loc.trans hs3_m2
  refine worldEff_seq_call0 hnt_s4 hcr_s4
    (fun hn hc => worldEff_call0_htr_bytes_vector hAs0 heff_s4 _ _ _ (chw + 128#64)
      (hch_add s4 128#64 hs4_m2) (outIvlCovered_heap_offset hch_lo hch_cap (by decide)) hn hc)
    (fun s5 hs5_loc heff_s5 hnt_s5 hcr_s5 => ?_)
  have hs5_m2 : s5.locals = m2.locals := hs5_loc.trans hs4_m2
  refine worldEff_seq_call0 hnt_s5 hcr_s5
    (fun hn hc => (worldEff_call0_memcpy_word heff_s5 _ _ (.const 32#64) (chw + 160#64) 32#64
      (hch_add s5 160#64 hs5_m2) (by simp [evalHOLExact])
      (fun _ _ => outIvlCovered_to_world (outIvlCovered_heap_offset hch_lo hch_cap (by decide)) 32 le_rfl) hn hc).1)
    (fun s6 hs6_loc heff_s6 hnt_s6 hcr_s6 => ?_)
  have hs6_m2 : s6.locals = m2.locals := hs6_loc.trans hs5_m2
  refine worldEff_seq_call0 hnt_s6 hcr_s6
    (fun hn hc => worldEff_call0_htr_u64_at heff_s6 _ _ (chw + 192#64)
      (hch_add s6 192#64 hs6_m2) (outIvlCovered_heap_offset hch_lo hch_cap (by decide)) hn hc)
    (fun s7 hs7_loc heff_s7 hnt_s7 hcr_s7 => ?_)
  have hs7_m2 : s7.locals = m2.locals := hs7_loc.trans hs6_m2
  refine worldEff_seq_call0 hnt_s7 hcr_s7
    (fun hn hc => worldEff_call0_htr_u64_at heff_s7 _ _ (chw + 224#64)
      (hch_add s7 224#64 hs7_m2) (outIvlCovered_heap_offset hch_lo hch_cap (by decide)) hn hc)
    (fun s8 hs8_loc heff_s8 hnt_s8 hcr_s8 => ?_)
  have hs8_m2 : s8.locals = m2.locals := hs8_loc.trans hs7_m2
  refine worldEff_seq_call0 hnt_s8 hcr_s8
    (fun hn hc => worldEff_call0_htr_u64_at heff_s8 _ _ (chw + 256#64)
      (hch_add s8 256#64 hs8_m2) (outIvlCovered_heap_offset hch_lo hch_cap (by decide)) hn hc)
    (fun s9 hs9_loc heff_s9 hnt_s9 hcr_s9 => ?_)
  have hs9_m2 : s9.locals = m2.locals := hs9_loc.trans hs8_m2
  refine worldEff_seq_call0 hnt_s9 hcr_s9
    (fun hn hc => worldEff_call0_htr_u64_at heff_s9 _ _ (chw + 288#64)
      (hch_add s9 288#64 hs9_m2) (outIvlCovered_heap_offset hch_lo hch_cap (by decide)) hn hc)
    (fun s10 hs10_loc heff_s10 hnt_s10 hcr_s10 => ?_)
  have hs10_m2 : s10.locals = m2.locals := hs10_loc.trans hs9_m2
  refine worldEff_seq_call0 hnt_s10 hcr_s10
    (fun hn hc => worldEff_call0_htr_bytes_list hAs0 heff_s10 _ _ _ _ (chw + 320#64)
      (hch_add s10 320#64 hs10_m2) (outIvlCovered_heap_offset hch_lo hch_cap (by decide)) hn hc)
    (fun s11 hs11_loc heff_s11 hnt_s11 hcr_s11 => ?_)
  have hs11_m2 : s11.locals = m2.locals := hs11_loc.trans hs10_m2
  refine worldEff_seq_call0 hnt_s11 hcr_s11
    (fun hn hc => (worldEff_call0_memcpy_word heff_s11 _ _ (.const 32#64) (chw + 352#64) 32#64
      (hch_add s11 352#64 hs11_m2) (by simp [evalHOLExact])
      (fun _ _ => outIvlCovered_to_world (outIvlCovered_heap_offset hch_lo hch_cap (by decide)) 32 le_rfl) hn hc).1)
    (fun s12 hs12_loc heff_s12 hnt_s12 hcr_s12 => ?_)
  have hs12_m2 : s12.locals = m2.locals := hs12_loc.trans hs11_m2
  refine worldEff_seq_call0 hnt_s12 hcr_s12
    (fun hn hc => (worldEff_call0_memcpy_word heff_s12 _ _ (.const 32#64) (chw + 384#64) 32#64
      (hch_add s12 384#64 hs12_m2) (by simp [evalHOLExact])
      (fun _ _ => outIvlCovered_to_world (outIvlCovered_heap_offset hch_lo hch_cap (by decide)) 32 le_rfl) hn hc).1)
    (fun s13 hs13_loc heff_s13 hnt_s13 hcr_s13 => ?_)
  have hs13_m2 : s13.locals = m2.locals := hs13_loc.trans hs12_m2
  have hs13_pl : s13.locals.lookup (ofString "pl") = some (.val (.word plw)) := by
    rw [hs13_m2]; exact hm2_pl
  -- dec txs := load (pl + 32); dec ntx := load (pl + 40)
  refine worldEff_dec heff_s13 (ofString "txs") .one _ hnt_s13 hcr_s13
    (fun vtxs hvtxs hvsh_txs hnt_txs hcr_txs => ?_)
  rcases vtxs with ⟨⟨txsw⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hvsh_txs)
  let t0 := setVarHOLFinite (ofString "txs") (.val (.word txsw)) s13
  have heff_t0 : WorldEff s0 t0 Rl sszBufs hpGw := heff_s13.locals_clock _ _
  have ht0_pl : t0.locals.lookup (ofString "pl") = some (.val (.word plw)) := by
    simp [t0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs13_pl,
      show ofString "txs" ≠ ofString "pl" by decide]
  refine worldEff_dec heff_t0 (ofString "ntx") .one _ hnt_txs hcr_txs
    (fun vntx hvntx _ hnt_ntx hcr_ntx => ?_)
  obtain ⟨ntxw, rfl, hntxw_mem⟩ := eval_load_add_value ht0_pl (off := 40) (by omega) (by decide) hvntx
  have hntx_s0 : memW t0 (plw.toNat + 40) = memW s0 (plw.toNat + 40) :=
    memW_eq_of_worldEff_ivl hAs0 heff_t0 hpl_in hpl_disj_R hpl_disj_B (by omega)
  have hntx_lt32 : ntxw.toNat < 2 ^ 32 := by
    rw [hntxw_mem, hntx_s0]; exact hpl_at.2.2.1
  let t1 := setVarHOLFinite (ofString "ntx") (.val (.word ntxw)) t0
  have heff_t1 : WorldEff s0 t1 Rl sszBufs hpGw := heff_t0.locals_clock _ _
  have ht1_ch : t1.locals.lookup (ofString "ch") = some (.val (.word chw)) := by
    simp [t1, t0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs13_m2, hm2_ch,
      show ofString "ntx" ≠ ofString "ch" by decide,
      show ofString "txs" ≠ ofString "ch" by decide]
  have ht1_pl : t1.locals.lookup (ofString "pl") = some (.val (.word plw)) := by
    simp [t1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht0_pl,
      show ofString "ntx" ≠ ofString "pl" by decide]
  have ht1_out : t1.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    simp [t1, t0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs13_m2, hm2_out,
      show ofString "ntx" ≠ ofString "out" by decide,
      show ofString "txs" ≠ ofString "out" by decide]
  have ht1_mark : t1.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    simp [t1, t0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs13_m2, hm2_mark,
      show ofString "ntx" ≠ ofString "mark" by decide,
      show ofString "txs" ≠ ofString "mark" by decide]
  have ht1_ntx : t1.locals.lookup (ofString "ntx") = some (.val (.word ntxw)) := by
    simp [t1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  -- decCall m2 := heap_mark(); decCall roots := alloc(ntx * 32 + 32); dec i := 0
  refine worldEff_decCall_heap_mark heff_t1 (ofString "m2") hnt_ntx hcr_ntx
    (fun m2w t2 _ _ hm2w_al hm2w_lo hm2w_hi ht2_eq heff_t2 hnt_t2 hcr_t2 => ?_)
  have ht2_ch : t2.locals.lookup (ofString "ch") = some (.val (.word chw)) := by
    rw [ht2_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, ht1_ch,
      show ofString "m2" ≠ ofString "ch" by decide]
  have ht2_pl : t2.locals.lookup (ofString "pl") = some (.val (.word plw)) := by
    rw [ht2_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, ht1_pl,
      show ofString "m2" ≠ ofString "pl" by decide]
  have ht2_out : t2.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [ht2_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, ht1_out,
      show ofString "m2" ≠ ofString "out" by decide]
  have ht2_mark : t2.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    rw [ht2_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, ht1_mark,
      show ofString "m2" ≠ ofString "mark" by decide]
  have ht2_ntx : t2.locals.lookup (ofString "ntx") = some (.val (.word ntxw)) := by
    rw [ht2_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, ht1_ntx,
      show ofString "m2" ≠ ofString "ntx" by decide]
  have ht2_m2 : t2.locals.lookup (ofString "m2") = some (.val (.word m2w)) := by
    rw [ht2_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  refine worldEff_decCall_alloc heff_t2 (by decide) (ofString "roots") _ hnt_t2 hcr_t2
    (fun roots1w sz1w t3 hsz1_ev _ ht3_loc _ heff_t3 _ _ hroots1_lo hroots1_end _ _ hnt_t3 hcr_t3 => ?_)
  have hsz1_eq : sz1w = ntxw * 32#64 + 32#64 := by
    simp [evalHOLExact, evalListHOLExact, toExact, ht2_ntx, panOpHOL,
      valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr] at hsz1_ev
    exact hsz1_ev.symm
  subst hsz1_eq
  have hsz1_nat : (ntxw * 32#64 + 32#64).toNat = ntxw.toNat * 32 + 32 := by
    have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
    have hm : (ntxw * 32#64).toNat = ntxw.toNat * 32 := by
      rw [BitVec.toNat_mul, h32]; exact Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_add, hm, h32, Nat.mod_eq_of_lt (by omega)]
  have hroots1_cap : roots1w.toNat + (ntxw.toNat * 32 + 32) ≤ heapLimit := by
    rw [← hsz1_nat]
    have : (ntxw * 32#64 + 32#64).toNat ≤ ((ntxw * 32#64 + 32#64).toNat + 7) / 8 * 8 := by omega
    omega
  refine worldEff_dec heff_t3 (ofString "i") .one _ hnt_t3 hcr_t3
    (fun vi0 hvi0 _ hnt_t4 hcr_t4 => ?_)
  have hvi0_eq : vi0 = .val (.word 0#64) := by simp [evalHOLExact] at hvi0; exact hvi0.symm
  subst hvi0_eq
  let t4 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) t3
  have heff_t4 : WorldEff s0 t4 Rl sszBufs hpGw := heff_t3.locals_clock _ _
  let InvTx : PanSemStateFiniteExact 64 F → Prop := fun st =>
    st.locals.lookup (ofString "roots") = some (.val (.word roots1w)) ∧
    st.locals.lookup (ofString "ntx") = some (.val (.word ntxw)) ∧
    st.locals.lookup (ofString "ch") = some (.val (.word chw)) ∧
    st.locals.lookup (ofString "pl") = some (.val (.word plw)) ∧
    st.locals.lookup (ofString "out") = some (.val (.word outw)) ∧
    st.locals.lookup (ofString "mark") = some (.val (.word markw)) ∧
    st.locals.lookup (ofString "m2") = some (.val (.word m2w)) ∧
    ∃ iw : BitVec 64, st.locals.lookup (ofString "i") = some (.val (.word iw)) ∧ iw.toNat ≤ ntxw.toNat
  have hInvTx_t4 : InvTx t4 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, 0#64, ?_, by simp⟩ <;>
      simp [t4, setVarHOLFinite, ht3_loc, HolFiniteMapExact.lookup_update, FUPDATE,
        ht2_ntx, ht2_ch, ht2_pl, ht2_out, ht2_mark, ht2_m2,
        show ofString "i" ≠ ofString "roots" by decide,
        show ofString "i" ≠ ofString "ntx" by decide,
        show ofString "i" ≠ ofString "ch" by decide,
        show ofString "i" ≠ ofString "pl" by decide,
        show ofString "i" ≠ ofString "out" by decide,
        show ofString "i" ≠ ofString "mark" by decide,
        show ofString "i" ≠ ofString "m2" by decide,
        show ofString "roots" ≠ ofString "ntx" by decide,
        show ofString "roots" ≠ ofString "ch" by decide,
        show ofString "roots" ≠ ofString "pl" by decide,
        show ofString "roots" ≠ ofString "out" by decide,
        show ofString "roots" ≠ ofString "mark" by decide,
        show ofString "roots" ≠ ofString "m2" by decide]
  let txArg1 : ExpHOL 64 :=
    .load .one (.op .add [.var .local (ofString "txs"), .panop .mul [.var .local (ofString "i"), .const 16#64]])
  let txArg2 : ExpHOL 64 :=
    .load .one (.op .add [.var .local (ofString "txs"), .panop .mul [.var .local (ofString "i"), .const 16#64], .const 8#64])
  let rootsOutArg : ExpHOL 64 :=
    .op .add [.var .local (ofString "roots"), .panop .mul [.var .local (ofString "i"), .const 32#64]]
  let incI : ProgHOL 64 :=
    .assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])
  let bodyTx : ProgHOL 64 :=
    .seq (.call (some (none, none)) (ofString "htr_pbytes") [txArg1, txArg2, rootsOutArg]) incI
  have hstepTx : ∀ u (cw : BitVec 64),
      @evalHOLFinite 64 F _ u (fun a => Classical.propDecidable (u.memaddrs a))
        (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "ntx"))) = some (.val (.word cw)) →
      cw ≠ 0 →
      WorldEff s0 (decClockHOLFinite u) Rl sszBufs hpGw → InvTx (decClockHOLFinite u) →
      (evaluateHOLFiniteState (decClockHOLFinite u) bodyTx).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState (decClockHOLFinite u) bodyTx).1 →
      WorldEff s0 (evaluateHOLFiniteState (decClockHOLFinite u) bodyTx).2 Rl sszBufs hpGw ∧
      (((evaluateHOLFiniteState (decClockHOLFinite u) bodyTx).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite u) bodyTx).1 = some .continue) →
        InvTx (evaluateHOLFiniteState (decClockHOLFinite u) bodyTx).2) := by
    intro u cw hcw hcw_ne heff_ud ⟨hu_roots, hu_ntx, hu_ch, hu_pl, hu_out, hu_mark, hu_m2, iw, hu_i, hi_le⟩ hnt_b hcr_b
    let ud := decClockHOLFinite u
    have hu_i0 : u.locals.lookup (ofString "i") = some (.val (.word iw)) := hu_i
    have hu_ntx0 : u.locals.lookup (ofString "ntx") = some (.val (.word ntxw)) := hu_ntx
    have hi_lt : iw.toNat < ntxw.toNat := by
      have hi63 : iw.toNat < 2 ^ 63 := by omega
      have hn63 : ntxw.toNat < 2 ^ 63 := by omega
      rw [evalHOLFinite_eq_toExact] at hcw
      simp only [evalHOLExact, toExact, hu_i0, hu_ntx0, Compiler.Encoders.Asm.wordCmpHOL,
        holAsmSignedLess_small iw ntxw hi63 hn63] at hcw
      by_cases hlt : iw.toNat < ntxw.toNat
      · exact hlt
      · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte] at hcw
        injection hcw with h1; injection h1 with h2; injection h2 with h3
        exact absurd h3.symm hcw_ne
    have hcov_i : OutIvlCovered s0 Rl (roots1w + iw * 32#64) := by
      apply outIvlCovered_heap_offset hroots1_lo hroots1_cap
      have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
      have hm : (iw * 32#64).toNat = iw.toNat * 32 := by
        rw [BitVec.toNat_mul, h32]; exact Nat.mod_eq_of_lt (by omega)
      omega
    have hwe_b : WorldEff s0 (evaluateHOLFiniteState ud bodyTx).2 Rl sszBufs hpGw := by
      dsimp only [bodyTx] at hnt_b hcr_b ⊢
      refine worldEff_seq_call0 hnt_b hcr_b
        (fun hn hc => worldEff_call0_htr_pbytes hAs0 heff_ud txArg1 txArg2 rootsOutArg
          (roots1w + iw * 32#64)
          (by simp [rootsOutArg, evalHOLExact, evalListHOLExact, toExact, hu_roots, hu_i, panOpHOL,
                valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr])
          hcov_i hn hc)
        (fun b1 _ heff_b1 _ _ => worldEff_assign_local heff_b1 _ _)
    refine ⟨hwe_b, fun hfl_b => ?_⟩
    dsimp only [bodyTx] at hfl_b ⊢
    refine seq_call0_flow ud _ _ incI InvTx hfl_b (fun b1 hb1_l _ => ?_)
    have hb1_i : b1.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hb1_l]; exact hu_i
    have hi1_ev : @evalHOLExact 64 F _ b1.toExact (fun a => Classical.propDecidable (b1.memaddrs a))
        (.op .add [.var .local (ofString "i"), .const 1#64]) = some (.val (.word (iw + 1#64))) := by
      simp [evalHOLExact, evalListHOLExact, toExact, hb1_i,
        valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr]
    have hvv_i : isValidValueHOLFinite b1 .local (ofString "i") (.val (.word (iw + 1#64))) = true := by
      simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, toExact, hb1_i,
        shapeOfHOLExact, shapeEqHOL]
    have ha_i : evaluateHOLFiniteState b1 incI =
        (none, setVarHOLFinite (ofString "i") (.val (.word (iw + 1#64))) b1) := by
      dsimp only [incI]; rw [evaluateHOLFiniteState_assign, hi1_ev]; dsimp only; rw [if_pos hvv_i]; rfl
    rw [ha_i]
    have hi_add : (iw + 1#64).toNat = iw.toNat + 1 := by
      have : (1#64 : BitVec 64).toNat = 1 := rfl
      exact BitVec.toNat_add_of_lt (by omega)
    have hr' : ud.locals.lookup (ofString "roots") = some (.val (.word roots1w)) := hu_roots
    have hn' : ud.locals.lookup (ofString "ntx") = some (.val (.word ntxw)) := hu_ntx
    have hc' : ud.locals.lookup (ofString "ch") = some (.val (.word chw)) := hu_ch
    have hp' : ud.locals.lookup (ofString "pl") = some (.val (.word plw)) := hu_pl
    have ho' : ud.locals.lookup (ofString "out") = some (.val (.word outw)) := hu_out
    have hm' : ud.locals.lookup (ofString "mark") = some (.val (.word markw)) := hu_mark
    have hm2' : ud.locals.lookup (ofString "m2") = some (.val (.word m2w)) := hu_m2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, iw + 1#64, ?_, by omega⟩ <;>
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hb1_l,
        hr', hn', hc', hp', ho', hm', hm2',
        show ofString "i" ≠ ofString "roots" by decide,
        show ofString "i" ≠ ofString "ntx" by decide,
        show ofString "i" ≠ ofString "ch" by decide,
        show ofString "i" ≠ ofString "pl" by decide,
        show ofString "i" ≠ ofString "out" by decide,
        show ofString "i" ≠ ofString "mark" by decide,
        show ofString "i" ≠ ofString "m2" by decide]
  refine worldEff_seq hnt_t4 hcr_t4
    (fun hnt_w1 hcr_w1 =>
      (worldEff_while_cond_post (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "ntx")))
        InvTx (fun u hu => hu) hstepTx t4.clock t4 rfl heff_t4 hInvTx_t4 hnt_w1 hcr_w1).1)
    (fun t5 ht5 heff_t5 hnt_t5 hcr_t5 => ?_)
  have hInvTx_t5 : InvTx t5 := by
    have hp := (worldEff_while_cond_post (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "ntx")))
      InvTx (fun u hu => hu) hstepTx t4.clock t4 rfl heff_t4 hInvTx_t4
      (by rw [ht5]; simp) (by rw [ht5]; exact Or.inl rfl)).2
    have hnbTx : ∀ st : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState st bodyTx).1 ≠ some .break :=
      fun st => seq_ne_break st (call0_ne_break st _ _) (fun st1 _ => assign_local_ne_break st1 _ _)
    have hpost := hp (by rw [ht5]) (fun st _ => hnbTx st)
    rw [ht5] at hpost
    exact hpost.1
  obtain ⟨ht5_roots, ht5_ntx, ht5_ch, ht5_pl, ht5_out, ht5_mark, ht5_m2, iw_end1, ht5_i, _⟩ := hInvTx_t5
  -- htr_plist_chunks(roots, ntx, ntx, ch + 416); heap_release(m2)
  refine worldEff_seq_call0 hnt_t5 hcr_t5
    (fun hn hc => worldEff_call0_htr_plist_chunks hAs0 heff_t5
      (.var .local (ofString "roots")) (.var .local (ofString "ntx")) (.var .local (ofString "ntx"))
      (.op .add [.var .local (ofString "ch"), .const 416#64]) ntxw (chw + 416#64)
      (by simp [evalHOLExact, toExact, ht5_ntx]) (by omega)
      (by simp [evalHOLExact, evalListHOLExact, toExact, ht5_ch,
            valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr])
      (outIvlCovered_heap_offset hch_lo hch_cap (by decide)) hn hc)
    (fun t6 ht6_loc heff_t6 hnt_t6 hcr_t6 => ?_)
  refine worldEff_seq_call0 hnt_t6 hcr_t6
    (fun hn _ => (worldEff_call0_heap_release hAs0 heff_t6 (by decide) hp_no_gb
      (.var .local (ofString "m2")) m2w
      (by simp [evalHOLExact, toExact, ht6_loc, ht5_m2])
      hm2w_lo hm2w_hi hm2w_al hn).2.choose_spec.2)
    (fun t7 ht7_loc heff_t7 hnt_t7 hcr_t7 => ?_)
  have ht7_t5 : t7.locals = t5.locals := ht7_loc.trans ht6_loc
  have ht7_pl : t7.locals.lookup (ofString "pl") = some (.val (.word plw)) := by rw [ht7_t5]; exact ht5_pl
  -- dec wd := load (pl + 48); dec nwd := load (pl + 56)
  refine worldEff_dec heff_t7 (ofString "wd") .one _ hnt_t7 hcr_t7
    (fun vwd _ hvsh_wd hnt_wd hcr_wd => ?_)
  rcases vwd with ⟨⟨wdw⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hvsh_wd)
  let w0 := setVarHOLFinite (ofString "wd") (.val (.word wdw)) t7
  have heff_w0 : WorldEff s0 w0 Rl sszBufs hpGw := heff_t7.locals_clock _ _
  have hw0_pl : w0.locals.lookup (ofString "pl") = some (.val (.word plw)) := by
    simp [w0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht7_pl,
      show ofString "wd" ≠ ofString "pl" by decide]
  refine worldEff_dec heff_w0 (ofString "nwd") .one _ hnt_wd hcr_wd
    (fun vnwd hvnwd _ hnt_nwd hcr_nwd => ?_)
  obtain ⟨nwdw, rfl, hnwdw_mem⟩ := eval_load_add_value hw0_pl (off := 56) (by omega) (by decide) hvnwd
  have hnwd_s0 : memW w0 (plw.toNat + 56) = memW s0 (plw.toNat + 56) :=
    memW_eq_of_worldEff_ivl hAs0 heff_w0 hpl_in hpl_disj_R hpl_disj_B (by omega)
  have hnwd_lt32 : nwdw.toNat < 2 ^ 32 := by
    rw [hnwdw_mem, hnwd_s0]; exact hnwd_lt
  let w1 := setVarHOLFinite (ofString "nwd") (.val (.word nwdw)) w0
  have heff_w1 : WorldEff s0 w1 Rl sszBufs hpGw := heff_w0.locals_clock _ _
  have hw1_roots_old : w1.locals.lookup (ofString "roots") = some (.val (.word roots1w)) := by
    simp [w1, w0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht7_t5, ht5_roots,
      show ofString "nwd" ≠ ofString "roots" by decide,
      show ofString "wd" ≠ ofString "roots" by decide]
  have hw1_i_old : w1.locals.lookup (ofString "i") = some (.val (.word iw_end1)) := by
    simp [w1, w0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht7_t5, ht5_i,
      show ofString "nwd" ≠ ofString "i" by decide,
      show ofString "wd" ≠ ofString "i" by decide]
  have hw1_nwd : w1.locals.lookup (ofString "nwd") = some (.val (.word nwdw)) := by
    simp [w1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hw1_ch : w1.locals.lookup (ofString "ch") = some (.val (.word chw)) := by
    simp [w1, w0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht7_t5, ht5_ch,
      show ofString "nwd" ≠ ofString "ch" by decide,
      show ofString "wd" ≠ ofString "ch" by decide]
  have hw1_pl : w1.locals.lookup (ofString "pl") = some (.val (.word plw)) := by
    simp [w1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hw0_pl,
      show ofString "nwd" ≠ ofString "pl" by decide]
  have hw1_out : w1.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    simp [w1, w0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht7_t5, ht5_out,
      show ofString "nwd" ≠ ofString "out" by decide,
      show ofString "wd" ≠ ofString "out" by decide]
  have hw1_mark : w1.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    simp [w1, w0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht7_t5, ht5_mark,
      show ofString "nwd" ≠ ofString "mark" by decide,
      show ofString "wd" ≠ ofString "mark" by decide]
  have hw1_m2 : w1.locals.lookup (ofString "m2") = some (.val (.word m2w)) := by
    simp [w1, w0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht7_t5, ht5_m2,
      show ofString "nwd" ≠ ofString "m2" by decide,
      show ofString "wd" ≠ ofString "m2" by decide]
  -- call roots := alloc(nwd * 32 + 32); assign i := 0
  refine worldEff_seq hnt_nwd hcr_nwd
    (fun hn hc => (worldEff_call_local_alloc heff_w1 (by decide) (ofString "roots") _
      ⟨roots1w, hw1_roots_old⟩ hn hc).1)
    (fun w2 hw2_none heff_w2 hnt_w2 hcr_w2 => ?_)
  have hca2 := (worldEff_call_local_alloc heff_w1 (by decide) (ofString "roots")
    (.op .add [.panop .mul [.var .local (ofString "nwd"), .const 32#64], .const 32#64])
    ⟨roots1w, hw1_roots_old⟩
    (by rw [hw2_none]; simp)
    (by rw [hw2_none]; exact Or.inl rfl)).2 (by rw [hw2_none])
  obtain ⟨roots2w, sz2w, hsz2_ev, hw2_loc_raw, hroots2_lo, hroots2_end, hhp_w2⟩ := hca2
  have hw2_loc : w2.locals = w1.locals.update (ofString "roots", .val (.word roots2w)) := by
    rwa [hw2_none] at hw2_loc_raw
  have hsz2_eq : sz2w = nwdw * 32#64 + 32#64 := by
    simp [evalHOLExact, evalListHOLExact, toExact, hw1_nwd, panOpHOL,
      valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr] at hsz2_ev
    exact hsz2_ev.symm
  subst hsz2_eq
  have hsz2_nat : (nwdw * 32#64 + 32#64).toNat = nwdw.toNat * 32 + 32 := by
    have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
    have hm : (nwdw * 32#64).toNat = nwdw.toNat * 32 := by
      rw [BitVec.toNat_mul, h32]; exact Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_add, hm, h32, Nat.mod_eq_of_lt (by omega)]
  have hroots2_cap : roots2w.toNat + (nwdw.toNat * 32 + 32) ≤ heapLimit := by
    rw [← hsz2_nat]
    have h1 : (nwdw * 32#64 + 32#64).toNat ≤ ((nwdw * 32#64 + 32#64).toNat + 7) / 8 * 8 := by omega
    have h2 : roots2w.toNat + ((nwdw * 32#64 + 32#64).toNat + 7) / 8 * 8 ≤ heapLimit := by
      rw [hw2_none] at hroots2_end hhp_w2; omega
    omega
  have hw2_i_old : w2.locals.lookup (ofString "i") = some (.val (.word iw_end1)) := by
    rw [hw2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hw1_i_old,
      show ofString "roots" ≠ ofString "i" by decide]
  have ha_i0 : evaluateHOLFiniteState w2 (.assign .local (ofString "i") (.const 0#64)) =
      (none, setVarHOLFinite (ofString "i") (.val (.word 0#64)) w2) := by
    have hvv : isValidValueHOLFinite w2 .local (ofString "i") (.val (.word 0#64)) = true := by
      simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, toExact, hw2_i_old,
        shapeOfHOLExact, shapeEqHOL]
    change isValidValueHOLExact w2.toExact .local (ofString "i") (.val (.word 0#64)) = true at hvv
    rw [evaluateHOLFiniteState_assign]
    simp [evalHOLExact, hvv, setKvarHOLFinite, setVarHOLFinite]
  refine worldEff_seq hnt_w2 hcr_w2
    (fun _ _ => worldEff_assign_local heff_w2 _ _)
    (fun w3 hw3_none heff_w3 hnt_w3 hcr_w3 => ?_)
  have hw3_eq : w3 = setVarHOLFinite (ofString "i") (.val (.word 0#64)) w2 := by
    have := ha_i0; rw [hw3_none] at this; exact (Prod.mk.inj this).2
  let InvWd : PanSemStateFiniteExact 64 F → Prop := fun st =>
    st.locals.lookup (ofString "roots") = some (.val (.word roots2w)) ∧
    st.locals.lookup (ofString "nwd") = some (.val (.word nwdw)) ∧
    st.locals.lookup (ofString "ch") = some (.val (.word chw)) ∧
    st.locals.lookup (ofString "pl") = some (.val (.word plw)) ∧
    st.locals.lookup (ofString "out") = some (.val (.word outw)) ∧
    st.locals.lookup (ofString "mark") = some (.val (.word markw)) ∧
    st.locals.lookup (ofString "m2") = some (.val (.word m2w)) ∧
    ∃ iw : BitVec 64, st.locals.lookup (ofString "i") = some (.val (.word iw)) ∧ iw.toNat ≤ nwdw.toNat
  have hInvWd_w3 : InvWd w3 := by
    rw [hw3_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, 0#64, ?_, by simp⟩ <;>
      simp [setVarHOLFinite, hw2_loc, HolFiniteMapExact.lookup_update, FUPDATE,
        hw1_nwd, hw1_ch, hw1_pl, hw1_out, hw1_mark, hw1_m2,
        show ofString "i" ≠ ofString "roots" by decide,
        show ofString "i" ≠ ofString "nwd" by decide,
        show ofString "i" ≠ ofString "ch" by decide,
        show ofString "i" ≠ ofString "pl" by decide,
        show ofString "i" ≠ ofString "out" by decide,
        show ofString "i" ≠ ofString "mark" by decide,
        show ofString "i" ≠ ofString "m2" by decide,
        show ofString "roots" ≠ ofString "nwd" by decide,
        show ofString "roots" ≠ ofString "ch" by decide,
        show ofString "roots" ≠ ofString "pl" by decide,
        show ofString "roots" ≠ ofString "out" by decide,
        show ofString "roots" ≠ ofString "mark" by decide,
        show ofString "roots" ≠ ofString "m2" by decide]
  let wdArg : ExpHOL 64 :=
    .op .add [.var .local (ofString "wd"), .panop .mul [.var .local (ofString "i"), .const 44#64]]
  let bodyWd : ProgHOL 64 :=
    .seq (.call (some (none, none)) (ofString "htr_withdrawal") [wdArg, rootsOutArg]) incI
  have hstepWd : ∀ u (cw : BitVec 64),
      @evalHOLFinite 64 F _ u (fun a => Classical.propDecidable (u.memaddrs a))
        (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nwd"))) = some (.val (.word cw)) →
      cw ≠ 0 →
      WorldEff s0 (decClockHOLFinite u) Rl sszBufs hpGw → InvWd (decClockHOLFinite u) →
      (evaluateHOLFiniteState (decClockHOLFinite u) bodyWd).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState (decClockHOLFinite u) bodyWd).1 →
      WorldEff s0 (evaluateHOLFiniteState (decClockHOLFinite u) bodyWd).2 Rl sszBufs hpGw ∧
      (((evaluateHOLFiniteState (decClockHOLFinite u) bodyWd).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite u) bodyWd).1 = some .continue) →
        InvWd (evaluateHOLFiniteState (decClockHOLFinite u) bodyWd).2) := by
    intro u cw hcw hcw_ne heff_ud ⟨hu_roots, hu_nwd, hu_ch, hu_pl, hu_out, hu_mark, hu_m2, iw, hu_i, hi_le⟩ hnt_b hcr_b
    let ud := decClockHOLFinite u
    have hu_i0 : u.locals.lookup (ofString "i") = some (.val (.word iw)) := hu_i
    have hu_nwd0 : u.locals.lookup (ofString "nwd") = some (.val (.word nwdw)) := hu_nwd
    have hi_lt : iw.toNat < nwdw.toNat := by
      have hi63 : iw.toNat < 2 ^ 63 := by omega
      have hn63 : nwdw.toNat < 2 ^ 63 := by omega
      rw [evalHOLFinite_eq_toExact] at hcw
      simp only [evalHOLExact, toExact, hu_i0, hu_nwd0, Compiler.Encoders.Asm.wordCmpHOL,
        holAsmSignedLess_small iw nwdw hi63 hn63] at hcw
      by_cases hlt : iw.toNat < nwdw.toNat
      · exact hlt
      · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte] at hcw
        injection hcw with h1; injection h1 with h2; injection h2 with h3
        exact absurd h3.symm hcw_ne
    have hcov_i : OutIvlCovered s0 Rl (roots2w + iw * 32#64) := by
      apply outIvlCovered_heap_offset hroots2_lo hroots2_cap
      have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
      have hm : (iw * 32#64).toNat = iw.toNat * 32 := by
        rw [BitVec.toNat_mul, h32]; exact Nat.mod_eq_of_lt (by omega)
      omega
    have hwe_b : WorldEff s0 (evaluateHOLFiniteState ud bodyWd).2 Rl sszBufs hpGw := by
      dsimp only [bodyWd] at hnt_b hcr_b ⊢
      refine worldEff_seq_call0 hnt_b hcr_b
        (fun hn hc => worldEff_call0_htr_withdrawal hAs0 heff_ud wdArg rootsOutArg
          (roots2w + iw * 32#64)
          (by simp [rootsOutArg, evalHOLExact, evalListHOLExact, toExact, hu_roots, hu_i, panOpHOL,
                valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr])
          hcov_i hn hc)
        (fun b1 _ heff_b1 _ _ => worldEff_assign_local heff_b1 _ _)
    refine ⟨hwe_b, fun hfl_b => ?_⟩
    dsimp only [bodyWd] at hfl_b ⊢
    refine seq_call0_flow ud _ _ incI InvWd hfl_b (fun b1 hb1_l _ => ?_)
    have hb1_i : b1.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hb1_l]; exact hu_i
    have hi1_ev : @evalHOLExact 64 F _ b1.toExact (fun a => Classical.propDecidable (b1.memaddrs a))
        (.op .add [.var .local (ofString "i"), .const 1#64]) = some (.val (.word (iw + 1#64))) := by
      simp [evalHOLExact, evalListHOLExact, toExact, hb1_i,
        valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr]
    have hvv_i : isValidValueHOLFinite b1 .local (ofString "i") (.val (.word (iw + 1#64))) = true := by
      simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, toExact, hb1_i,
        shapeOfHOLExact, shapeEqHOL]
    have ha_i : evaluateHOLFiniteState b1 incI =
        (none, setVarHOLFinite (ofString "i") (.val (.word (iw + 1#64))) b1) := by
      dsimp only [incI]; rw [evaluateHOLFiniteState_assign, hi1_ev]; dsimp only; rw [if_pos hvv_i]; rfl
    rw [ha_i]
    have hi_add : (iw + 1#64).toNat = iw.toNat + 1 := by
      have : (1#64 : BitVec 64).toNat = 1 := rfl
      exact BitVec.toNat_add_of_lt (by omega)
    have hr' : ud.locals.lookup (ofString "roots") = some (.val (.word roots2w)) := hu_roots
    have hn' : ud.locals.lookup (ofString "nwd") = some (.val (.word nwdw)) := hu_nwd
    have hc' : ud.locals.lookup (ofString "ch") = some (.val (.word chw)) := hu_ch
    have hp' : ud.locals.lookup (ofString "pl") = some (.val (.word plw)) := hu_pl
    have ho' : ud.locals.lookup (ofString "out") = some (.val (.word outw)) := hu_out
    have hm' : ud.locals.lookup (ofString "mark") = some (.val (.word markw)) := hu_mark
    have hm2' : ud.locals.lookup (ofString "m2") = some (.val (.word m2w)) := hu_m2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, iw + 1#64, ?_, by omega⟩ <;>
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hb1_l,
        hr', hn', hc', hp', ho', hm', hm2',
        show ofString "i" ≠ ofString "roots" by decide,
        show ofString "i" ≠ ofString "nwd" by decide,
        show ofString "i" ≠ ofString "ch" by decide,
        show ofString "i" ≠ ofString "pl" by decide,
        show ofString "i" ≠ ofString "out" by decide,
        show ofString "i" ≠ ofString "mark" by decide,
        show ofString "i" ≠ ofString "m2" by decide]
  refine worldEff_seq hnt_w3 hcr_w3
    (fun hnt_ww hcr_ww =>
      (worldEff_while_cond_post (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nwd")))
        InvWd (fun u hu => hu) hstepWd w3.clock w3 rfl heff_w3 hInvWd_w3 hnt_ww hcr_ww).1)
    (fun w4 hw4 heff_w4 hnt_w4 hcr_w4 => ?_)
  have hInvWd_w4 : InvWd w4 := by
    have hp := (worldEff_while_cond_post (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nwd")))
      InvWd (fun u hu => hu) hstepWd w3.clock w3 rfl heff_w3 hInvWd_w3
      (by rw [hw4]; simp) (by rw [hw4]; exact Or.inl rfl)).2
    have hnbWd : ∀ st : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState st bodyWd).1 ≠ some .break :=
      fun st => seq_ne_break st (call0_ne_break st _ _) (fun st1 _ => assign_local_ne_break st1 _ _)
    have hpost := hp (by rw [hw4]) (fun st _ => hnbWd st)
    rw [hw4] at hpost
    exact hpost.1
  obtain ⟨_, hw4_nwd, hw4_ch, _, hw4_out, hw4_mark, hw4_m2, _, _, _⟩ := hInvWd_w4
  have hch_add4 : ∀ (st : PanSemStateFiniteExact 64 F) (off : BitVec 64),
      st.locals = w4.locals →
      @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
        (.op .add [.var .local (ofString "ch"), .const off]) = some (.val (.word (chw + off))) := by
    intro st off hst_loc
    simp [evalHOLExact, evalListHOLExact, toExact, hst_loc, hw4_ch,
      valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr]
  -- htr_plist_chunks(roots, nwd, nwd, ch + 448); heap_release(m2); tail fields; htr_pcontainer; heap_release(mark); return 0
  refine worldEff_seq_call0 hnt_w4 hcr_w4
    (fun hn hc => worldEff_call0_htr_plist_chunks hAs0 heff_w4
      (.var .local (ofString "roots")) (.var .local (ofString "nwd")) (.var .local (ofString "nwd"))
      (.op .add [.var .local (ofString "ch"), .const 448#64]) nwdw (chw + 448#64)
      (by simp [evalHOLExact, toExact, hw4_nwd]) (by omega)
      (hch_add4 w4 448#64 rfl)
      (outIvlCovered_heap_offset hch_lo hch_cap (by decide)) hn hc)
    (fun u1 hu1_loc heff_u1 hnt_u1 hcr_u1 => ?_)
  refine worldEff_seq_call0 hnt_u1 hcr_u1
    (fun hn _ => (worldEff_call0_heap_release hAs0 heff_u1 (by decide) hp_no_gb
      (.var .local (ofString "m2")) m2w
      (by simp [evalHOLExact, toExact, hu1_loc, hw4_m2])
      hm2w_lo hm2w_hi hm2w_al hn).2.choose_spec.2)
    (fun u2 hu2_loc heff_u2 hnt_u2 hcr_u2 => ?_)
  have hu2_w4 : u2.locals = w4.locals := hu2_loc.trans hu1_loc
  refine worldEff_seq_call0 hnt_u2 hcr_u2
    (fun hn hc => worldEff_call0_htr_u64_at heff_u2 _ _ (chw + 480#64)
      (hch_add4 u2 480#64 hu2_w4) (outIvlCovered_heap_offset hch_lo hch_cap (by decide)) hn hc)
    (fun u3 hu3_loc heff_u3 hnt_u3 hcr_u3 => ?_)
  have hu3_w4 : u3.locals = w4.locals := hu3_loc.trans hu2_w4
  refine worldEff_seq_call0 hnt_u3 hcr_u3
    (fun hn hc => worldEff_call0_htr_u64_at heff_u3 _ _ (chw + 512#64)
      (hch_add4 u3 512#64 hu3_w4) (outIvlCovered_heap_offset hch_lo hch_cap (by decide)) hn hc)
    (fun u4 hu4_loc heff_u4 hnt_u4 hcr_u4 => ?_)
  have hu4_w4 : u4.locals = w4.locals := hu4_loc.trans hu3_w4
  refine worldEff_seq_call0 hnt_u4 hcr_u4
    (fun hn hc => worldEff_call0_htr_pbytes hAs0 heff_u4 _ _ _ (chw + 544#64)
      (hch_add4 u4 544#64 hu4_w4) (outIvlCovered_heap_offset hch_lo hch_cap (by decide)) hn hc)
    (fun u5 hu5_loc heff_u5 hnt_u5 hcr_u5 => ?_)
  have hu5_w4 : u5.locals = w4.locals := hu5_loc.trans hu4_w4
  refine worldEff_seq_call0 hnt_u5 hcr_u5
    (fun hn hc => worldEff_call0_htr_u64_at heff_u5 _ _ (chw + 576#64)
      (hch_add4 u5 576#64 hu5_w4) (outIvlCovered_heap_offset hch_lo hch_cap (by decide)) hn hc)
    (fun u6 hu6_loc heff_u6 hnt_u6 hcr_u6 => ?_)
  have hu6_w4 : u6.locals = w4.locals := hu6_loc.trans hu5_w4
  refine worldEff_seq_call0 hnt_u6 hcr_u6
    (fun hn hc => worldEff_call0_htr_pcontainer hAs0 heff_u6
      (.var .local (ofString "ch")) (.const 19#64) (.var .local (ofString "out"))
      19#64 outw
      (by simp [evalHOLExact]) (by decide)
      (by simp [evalHOLExact, toExact, hu6_w4, hw4_out]) hout_cov hn hc)
    (fun u7 hu7_loc heff_u7 hnt_u7 hcr_u7 => ?_)
  have hu7_w4 : u7.locals = w4.locals := hu7_loc.trans hu6_w4
  refine worldEff_seq_call0 hnt_u7 hcr_u7
    (fun hn _ => (worldEff_call0_heap_release hAs0 heff_u7 (by decide) hp_no_gb
      (.var .local (ofString "mark")) markw
      (by simp [evalHOLExact, toExact, hu7_w4, hw4_mark])
      hmark_lo hmark_hi hmark_al hn).2.choose_spec.2)
    (fun u8 _ heff_u8 _ _ => worldEff_return heff_u8 _)

private theorem worldEff_call0_htr_payload {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hAs0 : ArenaOK s0) (heff : WorldEff s0 cur Rl sszBufs hpGw)
    (plExp outExp : ExpHOL 64) (plw outw : BitVec 64)
    (hpl : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      plExp = some (.val (.word plw)))
    (hpl_in : Inside (plw.toNat, 136) sourceBase (globN s0 "heap_ptr"))
    (hpl_disj_R : ∀ j ∈ Rl, Disj (plw.toNat, 136) j)
    (hpl_disj_B : ∀ gs ∈ sszBufs, Disj (plw.toNat, 136) (bufferRegion s0 gs))
    (hpl_at : PayloadAt s0 plw.toNat)
    (hnwd_lt : memW s0 (plw.toNat + 56) < 2 ^ 32)
    (hout : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      outExp = some (.val (.word outw)))
    (hcov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_payload")
      [plExp, outExp])).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_payload")
      [plExp, outExp])).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "htr_payload")
      [plExp, outExp])).2 Rl sszBufs hpGw := by
  refine worldEff_call0_eff heff (ofString "htr_payload") [plExp, outExp]
    _ _ _ lookup_htr_payload (fun callee vals hargs hl hnt_e hres_e => ?_) hnt hcr
  rw [heff.code] at hl
  obtain ⟨pw, ow, rfl, hp, ho⟩ := lookupCode_two_words (by decide) lookup_htr_payload hl
  have heq : pw = plw ∧ ow = outw := by
    rw [evalListHOLFinite_eq_toExact] at hargs
    simp only [evalListHOLExact, hpl, hout] at hargs
    injection hargs with h0
    injection h0 with h1 h2
    injection h1 with h1'; injection h1' with h1''
    injection h2 with h2' _; injection h2' with h2''; injection h2'' with h2'''
    exact ⟨h1''.symm, h2'''.symm⟩
  obtain ⟨rfl, rfl⟩ := heq
  exact worldEff_htr_payload s0 (callEntryStateHOLFinite cur callee) hAs0
    (heff.locals_clock _ _) hp hpl_in hpl_disj_R hpl_disj_B hpl_at hnwd_lt ho hcov hnt_e hres_e

private theorem worldEff_htr_new_payload_request {F : Type}
    (s0 cur : PanSemStateFiniteExact 64 F) {Rl : List Ivl}
    (hAs0 : ArenaOK s0) (heff_cur : WorldEff s0 cur Rl sszBufs hpGw)
    {siw outw : BitVec 64}
    (hsi_lk : cur.locals.lookup (ofString "si") = some (.val (.word siw)))
    (hcells_in : ∀ iv ∈ inputCells s0 siw.toNat, Inside iv sourceBase (globN s0 "heap_ptr"))
    (hcells_disj_R : ∀ iv ∈ inputCells s0 siw.toNat, ∀ j ∈ Rl, Disj iv j)
    (hcells_disj_B : ∀ iv ∈ inputCells s0 siw.toNat, ∀ gs ∈ sszBufs, Disj iv (bufferRegion s0 gs))
    (hpl_at : PayloadAt s0 (memW s0 siw.toNat))
    (hrq_at : RequestsAt s0 (memW s0 (siw.toNat + 32)))
    (hnvh_lt : memW s0 (siw.toNat + 16) < 2 ^ 32)
    (hnwd_lt : memW s0 (memW s0 siw.toNat + 56) < 2 ^ 32)
    (hout_lk : cur.locals.lookup (ofString "out") = some (.val (.word outw)))
    (hout_cov : OutIvlCovered s0 Rl outw)
    (hnt : (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_new_payload_request)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_new_payload_request)).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_htr_new_payload_request)).2 Rl sszBufs hpGw := by
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hhp0_le : globN s0 "heap_ptr" ≤ heapLimit := hAs0.2.1
  have hsi_in : Inside (siw.toNat, 40) sourceBase (globN s0 "heap_ptr") :=
    hcells_in _ (by simp [inputCells])
  have hpl_in : Inside (memW s0 siw.toNat, 136) sourceBase (globN s0 "heap_ptr") :=
    hcells_in _ (by simp [inputCells])
  have hrq_in : Inside (memW s0 (siw.toNat + 32), 80) sourceBase (globN s0 "heap_ptr") :=
    hcells_in _ (by simp [inputCells])
  have hsi_disj_R : ∀ j ∈ Rl, Disj (siw.toNat, 40) j := hcells_disj_R _ (by simp [inputCells])
  have hsi_disj_B : ∀ gs ∈ sszBufs, Disj (siw.toNat, 40) (bufferRegion s0 gs) :=
    hcells_disj_B _ (by simp [inputCells])
  have hsi_hi : siw.toNat + 40 ≤ 2 ^ 64 := by unfold Inside at hsi_in; omega
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_htr_new_payload_request,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_decCall_heap_mark heff_cur (ofString "mark") hnt (Or.inr (Or.inr (Or.inr hres)))
    (fun markw m1 _ _ hmark_al hmark_lo hmark_hi hm1_eq heff_m1 hnt1 hcr1 => ?_)
  have hm1_si : m1.locals.lookup (ofString "si") = some (.val (.word siw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hsi_lk,
      show ofString "mark" ≠ ofString "si" by decide]
  have hm1_out : m1.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hout_lk,
      show ofString "mark" ≠ ofString "out" by decide]
  have hm1_mark : m1.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  refine worldEff_decCall_alloc heff_m1 (by decide) (ofString "ch") _ hnt1 hcr1
    (fun chw szw m2 hsz_ev _ hm2_loc _ heff_m2 _ _ hch_lo hch_end _ _ hnt2 hcr2 => ?_)
  have hsz_eq : szw = 128#64 := by
    simp [evalHOLExact, evalListHOLExact, panOpHOL, valueIsWord, valueWord] at hsz_ev
    exact hsz_ev.symm
  subst hsz_eq
  have hch_cap : chw.toNat + 128 ≤ heapLimit := by
    have : (128#64 : BitVec 64).toNat = 128 := rfl
    omega
  have hm2_ch : m2.locals.lookup (ofString "ch") = some (.val (.word chw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hm2_si : m2.locals.lookup (ofString "si") = some (.val (.word siw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_si,
      show ofString "ch" ≠ ofString "si" by decide]
  have hm2_out : m2.locals.lookup (ofString "out") = some (.val (.word outw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_out,
      show ofString "ch" ≠ ofString "out" by decide]
  have hm2_mark : m2.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_mark,
      show ofString "ch" ≠ ofString "mark" by decide]
  -- 1. htr_payload(load (si + 0), ch)
  refine worldEff_seq_call0 hnt2 hcr2
    (fun hn hc => by
      let plExp : ExpHOL 64 := .load .one (.op .add [.var .local (ofString "si"), .const 0#64])
      rcases hpl_ev : @evalHOLExact 64 F _ m2.toExact (fun a => Classical.propDecidable (m2.memaddrs a)) plExp with _ | vpl
      · rw [evaluateHOLFiniteState_call, evalListHOLFinite_eq_toExact]
        dsimp only [evalListHOLExact]; rw [hpl_ev]; exact heff_m2
      · obtain ⟨plw, rfl, hpl_mem⟩ := eval_load_add_value hm2_si (off := 0) (by omega) (by decide) hpl_ev
        have hpl_eq : plw.toNat = memW s0 siw.toNat := by
          rw [hpl_mem, Nat.add_zero]
          simpa using memW_eq_of_worldEff_ivl hAs0 heff_m2 hsi_in hsi_disj_R hsi_disj_B (off := 0) (by omega)
        exact worldEff_call0_htr_payload hAs0 heff_m2 plExp (.var .local (ofString "ch")) plw chw
          hpl_ev (by rw [hpl_eq]; exact hpl_in)
          (by rw [hpl_eq]; exact hcells_disj_R _ (by simp [inputCells]))
          (by rw [hpl_eq]; exact hcells_disj_B _ (by simp [inputCells]))
          (by rw [hpl_eq]; exact hpl_at) (by rw [hpl_eq]; exact hnwd_lt)
          (by simp [evalHOLExact, toExact, hm2_ch]) (Or.inr ⟨hch_lo, by omega⟩) hn hc)
    (fun m3 hm3_loc heff_m3 hnt3 hcr3 => ?_)
  have hm3_si : m3.locals.lookup (ofString "si") = some (.val (.word siw)) := by rw [hm3_loc]; exact hm2_si
  -- 2. htr_plist_chunks(load (si + 8), load (si + 16), load (si + 16), ch + 32)
  refine worldEff_seq_call0 hnt3 hcr3
    (fun hn hc => by
      let rExp : ExpHOL 64 := .load .one (.op .add [.var .local (ofString "si"), .const 8#64])
      let nExp : ExpHOL 64 := .load .one (.op .add [.var .local (ofString "si"), .const 16#64])
      rcases hn_ev : @evalHOLExact 64 F _ m3.toExact (fun a => Classical.propDecidable (m3.memaddrs a)) nExp with _ | vn
      · rw [evaluateHOLFiniteState_call, evalListHOLFinite_eq_toExact]
        have hlist_none : @evalListHOLExact 64 F _ m3.toExact (fun a => Classical.propDecidable (m3.memaddrs a))
            [rExp, nExp, nExp, .op .add [.var .local (ofString "ch"), .const 32#64]] = none := by
          dsimp only [evalListHOLExact]
          rw [hn_ev]
          cases @evalHOLExact 64 F _ m3.toExact (fun a => Classical.propDecidable (m3.memaddrs a)) rExp <;> rfl
        rw [hlist_none]
        exact heff_m3
      · obtain ⟨nvhw, rfl, hnvh_mem⟩ := eval_load_add_value hm3_si (off := 16) (by omega) (by decide) hn_ev
        have hnvh_eq : nvhw.toNat = memW s0 (siw.toNat + 16) := by
          rw [hnvh_mem]
          exact memW_eq_of_worldEff_ivl hAs0 heff_m3 hsi_in hsi_disj_R hsi_disj_B (off := 16) (by omega)
        exact worldEff_call0_htr_plist_chunks hAs0 heff_m3 rExp nExp nExp
          (.op .add [.var .local (ofString "ch"), .const 32#64]) nvhw (chw + 32#64)
          hn_ev (by rw [hnvh_eq]; omega)
          (by simp [evalHOLExact, evalListHOLExact, toExact, hm3_loc, hm2_ch,
                valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr])
          (outIvlCovered_heap_offset hch_lo hch_cap (by decide)) hn hc)
    (fun m4 hm4_loc heff_m4 hnt4 hcr4 => ?_)
  have hm4_m2 : m4.locals = m2.locals := hm4_loc.trans hm3_loc
  -- 3. memcpy(ch + 64, load (si + 24), 32)
  refine worldEff_seq_call0 hnt4 hcr4
    (fun hn hc => (worldEff_call0_memcpy_word heff_m4
      (.op .add [.var .local (ofString "ch"), .const 64#64])
      (.load .one (.op .add [.var .local (ofString "si"), .const 24#64]))
      (.const 32#64) (chw + 64#64) 32#64
      (by simp [evalHOLExact, evalListHOLExact, toExact, hm4_m2, hm2_ch,
            valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr])
      (by simp [evalHOLExact])
      (fun _ _ => outIvlCovered_to_world (outIvlCovered_heap_offset hch_lo hch_cap (by decide)) 32 le_rfl)
      hn hc).1)
    (fun m5 hm5_loc heff_m5 hnt5 hcr5 => ?_)
  have hm5_m2 : m5.locals = m2.locals := hm5_loc.trans hm4_m2
  have hm5_si : m5.locals.lookup (ofString "si") = some (.val (.word siw)) := by rw [hm5_m2]; exact hm2_si
  -- 4. htr_requests(load (si + 32), ch + 96)
  refine worldEff_seq_call0 hnt5 hcr5
    (fun hn hc => by
      let rqExp : ExpHOL 64 := .load .one (.op .add [.var .local (ofString "si"), .const 32#64])
      rcases hrq_ev : @evalHOLExact 64 F _ m5.toExact (fun a => Classical.propDecidable (m5.memaddrs a)) rqExp with _ | vrq
      · rw [evaluateHOLFiniteState_call, evalListHOLFinite_eq_toExact]
        dsimp only [evalListHOLExact]; rw [hrq_ev]; exact heff_m5
      · obtain ⟨rqw, rfl, hrq_mem⟩ := eval_load_add_value hm5_si (off := 32) (by omega) (by decide) hrq_ev
        have hrq_eq : rqw.toNat = memW s0 (siw.toNat + 32) := by
          rw [hrq_mem]
          exact memW_eq_of_worldEff_ivl hAs0 heff_m5 hsi_in hsi_disj_R hsi_disj_B (off := 32) (by omega)
        exact worldEff_call0_htr_requests hAs0 heff_m5 rqExp
          (.op .add [.var .local (ofString "ch"), .const 96#64]) rqw (chw + 96#64)
          hrq_ev (by rw [hrq_eq]; exact hrq_in)
          (by rw [hrq_eq]; exact hcells_disj_R _ (by simp [inputCells]))
          (by rw [hrq_eq]; exact hcells_disj_B _ (by simp [inputCells]))
          (by rw [hrq_eq]; exact hrq_at)
          (by simp [evalHOLExact, evalListHOLExact, toExact, hm5_m2, hm2_ch,
                valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr])
          (outIvlCovered_heap_offset hch_lo hch_cap (by decide)) hn hc)
    (fun m6 hm6_loc heff_m6 hnt6 hcr6 => ?_)
  have hm6_m2 : m6.locals = m2.locals := hm6_loc.trans hm5_m2
  -- 5. merkleize(ch, 4, 4, out); heap_release(mark); return 0
  refine worldEff_seq_call0 hnt6 hcr6
    (fun hn hc => worldEff_call0_merkleize hAs0 heff_m6
      (.var .local (ofString "ch")) (.const 4#64) (.const 4#64) (.var .local (ofString "out"))
      4#64 outw
      (by simp [evalHOLExact]) (by decide)
      (by simp [evalHOLExact, toExact, hm6_m2, hm2_out]) hout_cov hn hc)
    (fun m7 hm7_loc heff_m7 hnt7 hcr7 => ?_)
  have hm7_m2 : m7.locals = m2.locals := hm7_loc.trans hm6_m2
  refine worldEff_seq_call0 hnt7 hcr7
    (fun hn _ => (worldEff_call0_heap_release hAs0 heff_m7 (by decide) hp_no_gb
      (.var .local (ofString "mark")) markw
      (by simp [evalHOLExact, toExact, hm7_m2, hm2_mark])
      hmark_lo hmark_hi hmark_al hn).2.choose_spec.2)
    (fun m8 _ heff_m8 _ _ => worldEff_return heff_m8 _)

/-- Strengthened entry guard for `htr_new_payload_request`: `InputAt` on `si`, disjointness of
`inputCells` from `(out, 32)`, and 32-bit SSZ element-count bounds on `nvh = memW (si + 16)` and
`nwd = memW (pl + 56)` preventing heap-size overflow in `alloc(nwd * 32 + 32)` and bounding
`merkleize_progressive` tree depth. -/
def HtrNewPayloadReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
    InputAt s (locN s "si") ∧
    IvlsDisj (inputCells s (locN s "si")) [(locN s "out", 32)] ∧
    memW s (locN s "si" + 16) < 2 ^ 32 ∧
    memW s (memW s (locN s "si") + 56) < 2 ^ 32

theorem «wk_htr_new_payload_request_strong» :
    WorldKeeps HtrNewPayloadReady
      (fun s => [(locN s "out", 32),
                 (globN s "ssz_len_chunk", if globN s "ssz_len_chunk" = 0 then 0 else 32)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "htr_new_payload_request") := by
  refine ⟨_, _, _, lookup_htr_new_payload_request, fun {F} s hc hReady ⟨vals, hl⟩ hnt hres => ?_⟩
  obtain ⟨⟨hAr, S, Nd, hWT, hcells, hdisj_ow, _, hPay, hReq⟩, hdisj_out, hnvh_lt, hnwd_lt⟩ := hReady
  have hWOK : WorldOK s := ⟨hAr, S, (worldTyped_iff_with s S).2 ⟨Nd, hWT⟩⟩
  obtain ⟨siw, outw, rfl, hsi_lk, hout_lk⟩ := lookupCode_two_words (by decide) lookup_htr_new_payload_request hl
  have hsi_loc : locN s "si" = siw.toNat := by simp [locN, hsi_lk]
  have hout_loc : locN s "out" = outw.toNat := by simp [locN, hout_lk]
  rw [hsi_loc] at hcells hdisj_ow hdisj_out hPay hReq hnvh_lt hnwd_lt
  rw [hout_loc] at hdisj_out
  let Rfn : ∀ {F' : Type}, PanSemStateFiniteExact 64 F' → List Ivl :=
    fun t => [(locN t "out", 32),
              (globN t "ssz_len_chunk", if globN t "ssz_len_chunk" = 0 then 0 else 32)]
  have heff0 : WorldEff s s (Rfn s) sszBufs hpGw := WorldEff.refl s (Rfn s) sszBufs hpGw hAr hc
  have hcells_disj_B : ∀ iv ∈ inputCells s siw.toNat, ∀ gs ∈ sszBufs, Disj iv (bufferRegion s gs) := by
    intro iv hiv gs hgs
    simp only [sszBufs, List.mem_singleton] at hgs
    subst hgs
    have hmem_wo : bufferRegion s ("ssz_len_chunk", 32) ∈ worldOwned s S Nd := by
      unfold worldOwned fixedObjects
      apply List.mem_append.2; left; apply List.mem_append.2; right
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      exact List.mem_map.2 ⟨("ssz_len_chunk", 32), by decide, rfl⟩
    exact hdisj_ow iv hiv _ hmem_wo
  have hcells_disj_R : ∀ iv ∈ inputCells s siw.toNat, ∀ j ∈ Rfn s, Disj iv j := by
    intro iv hiv j hj
    simp only [Rfn, hout_loc, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact hdisj_out iv hiv (outw.toNat, 32) (by simp)
    · exact hcells_disj_B iv hiv ("ssz_len_chunk", 32) (by simp [sszBufs])
  have hout_cov : OutIvlCovered s (Rfn s) outw :=
    Or.inl ⟨(outw.toNat, 32), by simp [Rfn, hout_loc], le_rfl, le_rfl⟩
  have heff_post : WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htr_new_payload_request)).2
      (Rfn s) sszBufs hpGw :=
    worldEff_htr_new_payload_request s s hAr.2 heff0 hsi_lk
      (fun iv hiv => (hcells iv hiv).1) hcells_disj_R hcells_disj_B
      hPay hReq hnvh_lt hnwd_lt hout_lk hout_cov hnt hres
  exact heff_post.to_worldStep_Q hWOK ssz_B_ok hp_core_out (fun _ _ _ _ _ _ _ _ => trivial)

private theorem byteEff_remove_low_regions {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Sub : List Ivl}
    (hG : GuestInv s) (hb : ByteEff s post Sub) :
    ByteEff s post (Sub.filter (fun iv => sourceBase < iv.1 + iv.2)) := by
  refine ⟨hb.code, hb.memaddrs, hb.shMemaddrs, hb.baseAddr, hb.be,
    hb.globals, hb.eshapes, hb.out_dom, ?_, ?_⟩
  · intro a hne
    obtain ⟨iv, hiv, hpos, h1, h2⟩ := hb.cell_frame a hne
    have hdom := hb.out_dom a hne
    rw [hG.memaddrs, ordinaryDomain_iff] at hdom
    exact ⟨iv, List.mem_filter.2 ⟨hiv, by simpa using (show sourceBase < iv.1 + iv.2 by omega)⟩,
      hpos, h1, h2⟩
  · intro b hb64 hne
    obtain ⟨iv, hiv, h1, h2⟩ := hb.byte_frame b hb64 hne
    have hmem : post.memory (panByteAlignHOL (BitVec.ofNat 64 b)) ≠
        s.memory (panByteAlignHOL (BitVec.ofNat 64 b)) := by
      intro heq
      apply hne
      unfold memB
      rw [heq, hb.be]
    have hdom := hb.out_dom _ hmem
    rw [hG.memaddrs, ordinaryDomain_iff] at hdom
    have hal := panByteAlign_toNat64 (BitVec.ofNat 64 b)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb64] at hal
    exact ⟨iv, List.mem_filter.2 ⟨hiv, by simpa using (show sourceBase < iv.1 + iv.2 by omega)⟩,
      h1, h2⟩

private theorem worldEff_of_byteEff_or_low {F : Type}
    {s cur next : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String} {Sub : List Ivl}
    (h : WorldEff s cur Rl B gw) (hb : ByteEff cur next Sub)
    (hsub : ∀ iv ∈ Sub, 0 < iv.2 →
      iv.1 + iv.2 ≤ sourceBase ∨
      (∃ j ∈ Rl, j.1 ≤ iv.1 ∧ iv.1 + iv.2 ≤ j.1 + j.2) ∨
      (∃ gs ∈ B, (bufferRegion s gs).1 ≤ iv.1 ∧ iv.1 + iv.2 ≤ (bufferRegion s gs).1 + (bufferRegion s gs).2) ∨
      (globN s "frame_mem_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ globN s "scratch_ptr") ∨
      (globN s "heap_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ heapLimit)) :
    WorldEff s next Rl B gw := by
  apply h.of_byteEff (byteEff_remove_low_regions h.arena.1 hb)
  intro iv hiv hpos
  obtain ⟨hmem, hhigh⟩ := List.mem_filter.1 hiv
  have hhigh' : sourceBase < iv.1 + iv.2 := by simpa using hhigh
  rcases hsub iv hmem hpos with hlow | hallowed
  · omega
  · exact hallowed

private theorem worldEff_of_heap_frame {F : Type}
    {s cur next : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)}
    (h : WorldEff s cur Rl B hpGw)
    (hA : ArenaReady next)
    (hma : next.memaddrs = cur.memaddrs)
    (hbe : next.be = cur.be)
    (hes : next.eshapes = cur.eshapes)
    (hhp : globN cur "heap_ptr" ≤ globN next "heap_ptr")
    (hg : ∀ k : MlS, k ≠ ofString "heap_ptr" →
      cur.globals.lookup k = next.globals.lookup k)
    (hdom : ∀ a : BitVec 64, next.memory a ≠ cur.memory a → cur.memaddrs a)
    (hfr : ∀ a : BitVec 64, ¬ CellHits a.toNat
      (globN s "heap_ptr", globN next "heap_ptr" - globN s "heap_ptr") →
      next.memory a = cur.memory a)
    (hs8 : globN s "heap_ptr" % 8 = 0) :
    WorldEff s next Rl B hpGw := by
  have hgl : GlobalsKept hpGw cur next := by
    intro k hk
    exact hg k (by simpa [hpGw] using hk)
  have hfmp := globN_eq_of_lookup (hg (ofString "frame_mem_ptr") (by decide))
  have hsp := globN_eq_of_lookup (hg (ofString "scratch_ptr") (by decide))
  have hhp0 := le_trans h.hp_lo hhp
  have hhpmax := hA.2.2.1
  have hgw : GlobalsKept hpGw s next := fun k hk => (h.gw_kept k hk).trans (hgl k hk)
  refine ⟨hA, hA.1.code, hma.trans h.memaddrs, hbe.trans h.be,
    hes.trans h.eshapes, hhp0, hfmp.trans h.fmp_eq,
    by rw [hsp]; exact h.sp_hi, hgw,
    freshBufsOK_of_no_globalBuf_writes hgw hp_no_gb, ?_, ?_, ?_⟩
  · intro a hne
    by_cases heq : next.memory a = cur.memory a
    · exact h.out_dom a (by simpa only [heq] using hne)
    · rw [← h.memaddrs]
      exact hdom a heq
  · intro a hne
    by_cases heq : next.memory a = cur.memory a
    · exact h.cell_frame a (by simpa only [heq] using hne)
    · have hhit : CellHits a.toNat
          (globN s "heap_ptr", globN next "heap_ptr" - globN s "heap_ptr") := by
        by_contra hn
        exact heq (hfr a hn)
      have hdom_a := hdom a heq
      rw [h.arena.1.memaddrs, ordinaryDomain_iff] at hdom_a
      have ha8 : a.toNat % 8 = 0 := hdom_a.1
      have hn8 : globN next "heap_ptr" % 8 = 0 := hA.2.2.2.2.2.2.1
      obtain ⟨h1, h2⟩ := hhit
      dsimp only at h1 h2
      exact Or.inr (Or.inr (Or.inr ⟨by dsimp [heapFree]; omega,
        by dsimp [heapFree]; omega, by dsimp [heapFree]; omega⟩))
  · intro b hb64 hne
    by_cases heq : memB next b = memB cur b
    · exact h.byte_frame b hb64 (by simpa only [heq] using hne)
    · have hm : next.memory (panByteAlignHOL (BitVec.ofNat 64 b)) ≠
          cur.memory (panByteAlignHOL (BitVec.ofNat 64 b)) := by
        intro hm
        apply heq
        unfold memB
        rw [hm, hbe]
      have hhit : CellHits (panByteAlignHOL (BitVec.ofNat 64 b)).toNat
          (globN s "heap_ptr", globN next "heap_ptr" - globN s "heap_ptr") := by
        by_contra hn
        exact hm (hfr _ hn)
      have hal := panByteAlign_toNat64 (BitVec.ofNat 64 b)
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb64] at hal
      obtain ⟨h1, h2⟩ := hhit
      dsimp only at h1 h2
      have hn8 : globN next "heap_ptr" % 8 = 0 := hA.2.2.2.2.2.2.1
      exact Or.inr (Or.inr (Or.inr ⟨by dsimp [heapFree]; omega,
        by dsimp [heapFree]; omega⟩))

private theorem worldOwned_empty_or_allocated {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hW : WorldTypedWith s S Nd) :
    ∀ j ∈ worldOwned s S Nd, j.2 = 0 ∨ Allocated s j := by
  obtain ⟨hT, _, hF, hTr⟩ := hW
  intro j hj
  unfold worldOwned at hj
  rcases List.mem_append.1 hj with htf | hnd
  · rcases List.mem_append.1 htf with htab | hfix
    · obtain ⟨t, ht, hjt⟩ := List.mem_flatMap.1 htab
      exact Or.inr (((hT.2.1 t ht).2 j hjt).1)
    · rcases hF.1 j hfix with hz | ⟨hal, _⟩
      · exact Or.inl hz
      · exact Or.inr hal
  · obtain ⟨n, hn, hjn⟩ := List.mem_flatMap.1 hnd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hjn
    rcases hjn with rfl | rfl
    · exact Or.inr (hTr.1.1 n hn).2.1
    · unfold nodePath
      split_ifs with hp
      · rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hp.1 with hz | ⟨_, hal, _⟩
        · exact absurd hz hp.2
        · exact Or.inr hal
      · exact Or.inl rfl

private theorem freshTable_disj_entry_world {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hs : ArenaReady s) (hp : ArenaReady post)
    (hW : WorldTypedWith s S Nd)
    (hfp : ∀ i ∈ htabFootprint post t,
      Inside i (globN s "heap_ptr") (globN post "heap_ptr")) :
    IvlsDisj (htabFootprint post t) (worldOwned s S Nd) := by
  intro i hi j hj
  rcases worldOwned_empty_or_allocated hW j hj with hz | hal
  · exact Or.inr (Or.inl hz)
  · exact disj_allocated_fresh_heap hs.2 hp.2 hal (hfp i hi)

private theorem panMemStoresHOL_dom_of_ne {dom : BitVec 64 → Prop} {dec : DecidablePred dom} :
    ∀ (ws : List (HolWordLab 64)) (x : BitVec 64) (mem mem' : BitVec 64 → HolWordLab 64),
      @panMemStoresHOL 64 _ x ws dom dec mem = some mem' →
      ∀ a : BitVec 64, mem' a ≠ mem a → dom a
  | [], _, mem, mem', hst, a, hne => by
    simp only [panMemStoresHOL, Option.some.injEq] at hst
    subst hst
    exact absurd rfl hne
  | w :: ws, x, mem, mem', hst, a, hne => by
    unfold panMemStoresHOL panMemStoreHOL at hst
    split_ifs at hst with hdom
    by_cases hax : a = x
    · subst hax; exact hdom
    · exact panMemStoresHOL_dom_of_ne ws (x + panBytesInWord 64)
        (fun current => if current = x then w else mem current) mem' hst a
        (by simpa only [if_neg hax] using hne)

private theorem panMemStoresHOL_out_dom {dom : BitVec 64 → Prop} {dec : DecidablePred dom}
    {ws : List (HolWordLab 64)} {x : BitVec 64} {mem mem' : BitVec 64 → HolWordLab 64}
    (hst : @panMemStoresHOL 64 _ x ws dom dec mem = some mem')
    {a : BitVec 64} (ha : ¬ dom a) : mem' a = mem a := by
  by_contra hne
  exact ha (panMemStoresHOL_dom_of_ne ws x mem mem' hst a hne)

private theorem panMemStore32HOL_out_dom {dom : BitVec 64 → Prop} {dec : DecidablePred dom}
    {mem mem' : BitVec 64 → HolWordLab 64} {be : Bool} {addr : BitVec 64} {val : BitVec 32}
    (hst : @panMemStore32HOL 64 _ mem dom dec be addr val = some mem')
    {a : BitVec 64} (ha : ¬ dom a) : mem' a = mem a := by
  unfold panMemStore32HOL at hst
  split at hst
  · dsimp only at hst
    cases hm : mem (panByteAlignHOL (width := 64) addr) with
    | word cell =>
      rw [hm] at hst
      dsimp only at hst
      split at hst
      · rename_i hdom
        simp only [Option.some.injEq] at hst
        subst hst
        exact if_neg (fun heq : a = panByteAlignHOL (width := 64) addr =>
          ha (heq.symm ▸ hdom))
      · cases hst
  · cases hst

private theorem panMemStoreByteWord8HOL_out_dom {dom : BitVec 64 → Prop} {dec : DecidablePred dom}
    {mem mem' : BitVec 64 → HolWordLab 64} {be : Bool} {addr : BitVec 64} {b : BitVec 8}
    (hst : @panMemStoreByteWord8HOL 64 _ mem dom dec be addr b = some mem')
    {a : BitVec 64} (ha : ¬ dom a) : mem' a = mem a := by
  unfold panMemStoreByteWord8HOL at hst
  dsimp only at hst
  cases hm : mem (panByteAlignHOL (width := 64) addr) with
  | word cell =>
    rw [hm] at hst
    dsimp only at hst
    split at hst
    · rename_i hdom
      simp only [Option.some.injEq] at hst
      subst hst
      exact if_neg (fun heq : a = panByteAlignHOL (width := 64) addr =>
        ha (heq.symm ▸ hdom))
    · cases hst

private theorem panWriteBytearrayWord8HOL_out_dom {dom : BitVec 64 → Prop} {dec : DecidablePred dom} :
    ∀ (bs : List (BitVec 8)) (addr : BitVec 64) (mem : BitVec 64 → HolWordLab 64) (be : Bool)
      {a : BitVec 64}, ¬ dom a →
      @panWriteBytearrayWord8HOL 64 _ addr bs mem dom dec be a = mem a
  | [], _, _, _, _, _ => rfl
  | b :: bs, addr, mem, be, a, ha => by
    unfold panWriteBytearrayWord8HOL
    cases hst : @panMemStoreByteWord8HOL 64 _
        (@panWriteBytearrayWord8HOL 64 _ (addr + 1) bs mem dom dec be) dom dec be addr b with
    | none => rfl
    | some updated =>
      exact (panMemStoreByteWord8HOL_out_dom hst ha).trans
        (panWriteBytearrayWord8HOL_out_dom bs (addr + 1) mem be ha)

private theorem shMemStore_mem_eq {F : Type} (state : PanSemStateFiniteExact 64 F) (operator : OpSize)
    (address value : ExpHOL 64) :
    (evaluateHOLFiniteState state (.shMemStore operator address value)).2.memory = state.memory := by
  classical
  rw [evaluateHOLFiniteState_shMemStore_total]
  dsimp only
  split
  · unfold shMemStoreHOLExact
    split <;> split
    all_goals simp [ofExact, toExact]
    all_goals split <;> simp
  · rfl

private theorem shMemLoad_mem_eq {F : Type} (state : PanSemStateFiniteExact 64 F) (operator : OpSize)
    (kind : VarKind) (name : MlS) (address : ExpHOL 64) :
    (evaluateHOLFiniteState state (.shMemLoad operator kind name address)).2.memory = state.memory := by
  classical
  rw [evaluateHOLFiniteState_shMemLoad_source]
  split
  · split
    · unfold shMemLoadHOLFiniteExact
      dsimp only
      cases kind <;> split <;> split <;> (try split) <;>
        simp [emptyLocalsHOLFinite, setKvarFfiHOLFinite, setKvarHOLFinite, setVarHOLFinite, setGlobalHOLFinite]
    · rfl
  · rfl

private theorem call_out_dom_aux {F : Type}
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL 64)))
    (function : MlS) (arguments : List (ExpHOL 64)) (state : PanSemStateFiniteExact 64 F)
    {a : BitVec 64} (ha : ¬ state.memaddrs a)
    (ihBody : ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite state.code.lookup function values = some (body, callee, rs) →
      state.clock ≠ 0 →
      (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2.memory a = state.memory a)
    (ihHandler : ∀ dest hid hv hp, info = some (dest, some (hid, hv, hp)) →
      ∀ (t : PanSemStateFiniteExact 64 F),
        t.clock < state.clock → ¬ t.memaddrs a →
        (evaluateHOLFiniteState t hp).2.memory a = t.memory a) :
    (evaluateHOLFiniteState state (.call info function arguments)).2.memory a = state.memory a := by
  rw [evaluateHOLFiniteState_call]
  split
  · rfl
  · rename_i values _
    split
    · rfl
    · rename_i body callee rs found
      split
      · rfl
      · rename_i nonzero
        have ih := ihBody values body callee rs found nonzero
        have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata
          (callEntryStateHOLFinite state callee) body
        have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
        generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at ih meta' cl
        obtain ⟨r, st⟩ := out
        dsimp only at ih meta' cl ⊢
        change st.clock ≤ state.clock - 1 at cl
        have stc : st.clock < state.clock := by omega
        have st_ha : ¬ st.memaddrs a := by
          have hm : st.memaddrs = state.memaddrs := meta'.2.1
          rw [hm]; exact ha
        rcases info with _ | ⟨dest, handler⟩
        · rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
            simp [setKvarHOLFinite, setVarHOLFinite, setGlobalHOLFinite, emptyLocalsHOLFinite, ih]
        · rcases handler with _ | ⟨hid, hv, hp⟩
          · rcases dest with _ | ⟨⟨⟩, nm⟩ <;>
              rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
              simp [setKvarHOLFinite, setVarHOLFinite, setGlobalHOLFinite, emptyLocalsHOLFinite, ih]
          · rcases dest with _ | ⟨⟨⟩, nm⟩ <;>
              rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
              first
                | (exact (ihHandler _ hid hv hp rfl _ (by exact stc) (by exact st_ha)).trans ih)
                | (simp [setKvarHOLFinite, setVarHOLFinite, setGlobalHOLFinite, emptyLocalsHOLFinite, ih])

private theorem evaluateHOLFiniteState_mem_out_dom {F : Type}
    (state : PanSemStateFiniteExact 64 F) (program : ProgHOL 64)
    {a : BitVec 64} (ha : ¬ state.memaddrs a) :
    (evaluateHOLFiniteState state program).2.memory a = state.memory a := by
  cases shape : program with
  | skip => rw [evaluateHOLFiniteState_skip]
  | dec name kind initializer body =>
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · rfl
    · split
      · exact evaluateHOLFiniteState_mem_out_dom _ body ha
      · rfl
  | decCall name kind function arguments continuation =>
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    split
    · rfl
    · rename_i values _
      split
      · rfl
      · rename_i body callee rs found
        split
        · rfl
        · rename_i nonzero
          dsimp only
          have ih : (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2.memory a = state.memory a :=
            evaluateHOLFiniteState_mem_out_dom (callEntryStateHOLFinite state callee) body ha
          have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata
            (callEntryStateHOLFinite state callee) body
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
          generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at ih meta' cl
          obtain ⟨r, st⟩ := out
          dsimp only at ih meta' cl ⊢
          change st.clock ≤ state.clock - 1 at cl
          have st_ha : ¬ st.memaddrs a := by
            have hm : st.memaddrs = state.memaddrs := meta'.2.1
            rw [hm]; exact ha
          rcases r with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only [emptyLocalsHOLFinite])
          all_goals (try exact ih)
          split
          · have small : st.clock < state.clock := by omega
            exact (evaluateHOLFiniteState_mem_out_dom
              (setVarHOLFinite name v { st with locals := state.locals })
              continuation st_ha).trans ih
          · exact ih
  | assign kind name value =>
    rw [evaluateHOLFiniteState_assign]
    split
    · rfl
    · split
      · cases kind <;> rfl
      · rfl
  | seq first second =>
    have memory := evaluateHOLFiniteState_mem_out_dom state first ha
    have remaining := evaluateHOLFiniteState_clock_le state first
    have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata state first
    rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at memory remaining meta'
      dsimp only at memory remaining meta'
      cases result with
      | none =>
        have mclock : middle.clock ≤ state.clock := remaining
        have m_ha : ¬ middle.memaddrs a := by rw [meta'.2.1]; exact ha
        exact (evaluateHOLFiniteState_mem_out_dom middle second m_ha).trans memory
      | some _ => exact memory
  | ite condition yes no =>
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluateHOLFiniteState_mem_out_dom state no ha
      · exact evaluateHOLFiniteState_mem_out_dom state yes ha
    · rfl
  | «while» condition body =>
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · rfl
        · rename_i nonzero
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have memory := evaluateHOLFiniteState_mem_out_dom (decClockHOLFinite state) body ha
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata
            (decClockHOLFinite state) body
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk result middle =>
            rw [bodyRun] at memory remaining meta'
            dsimp only at memory remaining meta'
            have smaller : middle.clock < state.clock := by
              change middle.clock ≤ state.clock - 1 at remaining
              omega
            have m_ha : ¬ middle.memaddrs a := by rw [meta'.2.1]; exact ha
            cases result with
            | none => exact (evaluateHOLFiniteState_mem_out_dom middle (.while condition body) m_ha).trans memory
            | some result =>
              cases result with
              | «continue» =>
                exact (evaluateHOLFiniteState_mem_out_dom middle (.while condition body) m_ha).trans memory
              | «break» | returned _ | exception _ _ | finalFfi _ | error | timeOut => exact memory
      · rfl
    · rfl
  | «break» => rw [evaluateHOLFiniteState_break]
  | «continue» => rw [evaluateHOLFiniteState_continue]
  | annot _ _ => rw [evaluateHOLFiniteState_annot]
  | tick =>
    rw [evaluateHOLFiniteState_tick]
    split <;> rfl
  | raise _ value =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> rfl
    · rfl
  | «return» value =>
    rw [evaluateHOLFiniteState_return]
    split
    · rfl
    · split <;> rfl
  | store destination value =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split
        · rename_i mem' hst
          exact panMemStoresHOL_out_dom hst ha
        · rfl
      · rfl
    · rfl
  | store32 destination value =>
    rw [evaluateHOLFiniteState_store32]
    split
    · split
      · split
        · rename_i mem' hst
          exact panMemStore32HOL_out_dom hst ha
        · rfl
      · rfl
    · rfl
  | storeByte destination value =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split
        · rename_i mem' hst
          exact panMemStoreByteWord8HOL_out_dom hst ha
        · rfl
      · rfl
    · rfl
  | extCall _ _ _ _ _ =>
    rw [evaluateHOLFiniteState_extCall_source]
    split
    · split
      · split
        · rfl
        · dsimp only [ofExact, toExact]
          exact panWriteBytearrayWord8HOL_out_dom _ _ _ _ ha
      · rfl
    · rfl
  | primitive _ _ _ =>
    rw [evaluateHOLFiniteState_primitive]
    split
    · rfl
    · split
      · rfl
      · split <;> rfl
  | shMemStore op addr val =>
    exact congrFun (shMemStore_mem_eq state op addr val) a
  | shMemLoad op kind name addr =>
    exact congrFun (shMemLoad_mem_eq state op kind name addr) a
  | call info function arguments =>
    refine call_out_dom_aux info function arguments state ha
      (fun values body callee rs _ _ =>
        evaluateHOLFiniteState_mem_out_dom (callEntryStateHOLFinite state callee) body ha)
      (fun _ _ _ hp _ t _ tha => evaluateHOLFiniteState_mem_out_dom t hp tha)
termination_by (state.clock, sizeOf program)
decreasing_by
  all_goals
    simp_wf
    apply InitECandidate.Solver.GuestGlobalKeep.lex_of
    try subst shape
    try simp only [setVarHOLFinite, decClockHOLFinite, callEntryStateHOLFinite, ProgHOL.seq.sizeOf_spec,
      ProgHOL.ite.sizeOf_spec, ProgHOL.dec.sizeOf_spec, ProgHOL.while.sizeOf_spec, ProgHOL.decCall.sizeOf_spec, true_and]
    first
      | exact Or.inl small
      | (simp only [callEntryStateHOLFinite] at small; exact Or.inl small)
      | omega
      | (by_cases hc : state.clock = 0
         · right; refine ⟨by omega, ?_⟩; simp +arith
         · left; omega)
      | (rcases Nat.lt_or_eq_of_le mclock with h | h
         · exact Or.inl h
         · right; refine ⟨h, ?_⟩; simp +arith)

private def noCatchableRaise (good : MlS → Bool) : ProgHOL 64 → Bool
  | .dec _ _ _ b => noCatchableRaise good b
  | .seq a b => noCatchableRaise good a && noCatchableRaise good b
  | .ite _ a b => noCatchableRaise good a && noCatchableRaise good b
  | .while _ b => noCatchableRaise good b
  | .decCall _ _ f _ cont => good f && noCatchableRaise good cont
  | .call (some (_, none)) f _ => good f
  | .raise eid _ => eid == ofString "TrapErr"
  | .skip | .break | .continue | .annot _ _ | .return _
  | .assign _ _ _ | .store _ _ | .storeByte _ _ | .store32 _ _
  | .shMemStore _ _ _ | .extCall _ _ _ _ _ => true
  | _ => false

private theorem lex_ncr {a1 a2 b1 b2 : Nat} (h : a1 < a2 ∨ a1 = a2 ∧ b1 < b2) :
    Prod.Lex (· < ·) (· < ·) (a1, b1) (a2, b2) := by
  rcases h with h | ⟨rfl, h⟩
  · exact Prod.Lex.left _ _ h
  · exact Prod.Lex.right _ h

private theorem evaluate_noCatchableRaise {F : Type} (good : MlS → Bool)
    (hgood : ∀ f, good f = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup f values =
        some (body, callee, rs) →
      noCatchableRaise good body = true)
    (p : ProgHOL 64) (hp : noCatchableRaise good p = true)
    (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode) :
    ∀ eid v, eid ≠ ofString "TrapErr" → (evaluateHOLFiniteState s p).1 ≠ some (.exception eid v) := by
  cases shape : p with
  | skip => rw [evaluateHOLFiniteState_skip]; simp
  | «break» => rw [evaluateHOLFiniteState_break]; simp
  | «continue» => rw [evaluateHOLFiniteState_continue]; simp
  | annot _ _ => rw [evaluateHOLFiniteState_annot]; simp
  | «return» _ =>
    rw [evaluateHOLFiniteState_return]
    split
    · simp
    · split <;> simp
  | assign _ _ _ =>
    rw [evaluateHOLFiniteState_assign]
    split
    · simp
    · split <;> simp
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | store32 _ _ =>
    rw [evaluateHOLFiniteState_store32]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | shMemStore _ _ _ =>
    rw [evaluateHOLFiniteState_shMemStore_total]; dsimp only
    split
    · unfold shMemStoreHOLExact
      split <;> split
      all_goals simp [ofExact, toExact]
      all_goals split <;> simp
    · simp
  | extCall _ _ _ _ _ =>
    rw [evaluateHOLFiniteState_extCall_source]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | raise name _ =>
    have htrap : name = ofString "TrapErr" := by
      simpa [shape, noCatchableRaise, beq_iff_eq] using hp
    subst htrap
    intro eid v hne
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only
      split
      · simp [hne.symm]
      · simp
    · simp
  | dec name _ _ body =>
    have hb : noCatchableRaise good body = true := by simpa [shape, noCatchableRaise] using hp
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    split
    · simp
    · rename_i val _
      split
      · exact evaluate_noCatchableRaise good hgood body hb (setVarHOLFinite name val s) hcode
      · simp
  | seq a b =>
    have hab : noCatchableRaise good a = true ∧ noCatchableRaise good b = true := by
      simpa [shape, noCatchableRaise, Bool.and_eq_true] using hp
    have ih1 := evaluate_noCatchableRaise good hgood a hab.1 s hcode
    have rem := evaluateHOLFiniteState_clock_le s a
    have meta' := PanRunBounded.evaluateHOLFiniteState_metadata s a
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hr : evaluateHOLFiniteState s a with ⟨r1, mid⟩
    rw [hr] at ih1 rem meta'
    dsimp only at ih1 rem meta' ⊢
    cases r1 with
    | none =>
      have mclock : mid.clock ≤ s.clock := rem
      exact evaluate_noCatchableRaise good hgood b hab.2 mid (meta'.1.trans hcode)
    | some _ => exact ih1
  | ite _ yes no =>
    have hy : noCatchableRaise good yes = true ∧ noCatchableRaise good no = true := by
      simpa [shape, noCatchableRaise, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noCatchableRaise good hgood no hy.2 s hcode
      · exact evaluate_noCatchableRaise good hgood yes hy.1 s hcode
    · simp
  | «while» cond body =>
    have hb : noCatchableRaise good body = true := by simpa [shape, noCatchableRaise] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp
        · dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := evaluate_noCatchableRaise good hgood body hb (decClockHOLFinite s) hcode
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          have meta' := PanRunBounded.evaluateHOLFiniteState_metadata (decClockHOLFinite s) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at ih1 rem meta'
          dsimp only at ih1 rem meta' ⊢
          have smaller : mid.clock < s.clock := by change mid.clock ≤ s.clock - 1 at rem; omega
          have mCode : mid.code = originalRuntimeCode := meta'.1.trans hcode
          cases r1 with
          | none =>
            exact evaluate_noCatchableRaise good hgood (.while cond body) (by simpa [noCatchableRaise] using hb) mid mCode
          | some r =>
            cases r with
            | «continue» =>
              exact evaluate_noCatchableRaise good hgood (.while cond body) (by simpa [noCatchableRaise] using hb) mid mCode
            | «break» => simp
            | _ => exact ih1
      · simp
    · simp
  | decCall name _ fn args cont =>
    have hc : good fn = true ∧ noCatchableRaise good cont = true := by
      simpa [shape, noCatchableRaise, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
    · simp
    · dsimp only
      rcases hl : lookupCodeHOLFinite s.code.lookup fn values with _ | ⟨body, callee, rs⟩
      · simp
      · dsimp only
        have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup fn values = some (body, callee, rs) := by rwa [← hcode]
        have bodyOk := hgood fn hc.1 values body callee rs hl'
        split
        · simp
        · have ih1 := evaluate_noCatchableRaise good hgood body bodyOk (callEntryStateHOLFinite s callee) hcode
          have meta' := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
          rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, st⟩
          rw [hrun] at ih1 meta' cl
          dsimp only at ih1 meta' cl ⊢
          change st.clock ≤ s.clock - 1 at cl
          have small : st.clock < s.clock := by omega
          have stCode : st.code = originalRuntimeCode := meta'.1.trans hcode
          cases res with
          | none => simp
          | some r =>
            cases r with
            | returned v =>
              dsimp only
              split
              · set resumed := setVarHOLFinite name v { st with locals := s.locals }
                have smallR : resumed.clock < s.clock := small
                have rCode : resumed.code = originalRuntimeCode := stCode
                exact evaluate_noCatchableRaise good hgood cont hc.2 resumed rCode
              · simp
            | «break» => simp
            | «continue» => simp
            | _ => exact ih1
  | call tail fn args =>
    cases tail with
    | none => simp [shape, noCatchableRaise] at hp
    | some th =>
      rcases th with ⟨dest, handler⟩
      cases handler with
      | some _ => simp [shape, noCatchableRaise] at hp
      | none =>
        have hf : good fn = true := by simpa [shape, noCatchableRaise] using hp
        rw [evaluateHOLFiniteState_call]
        rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
        · simp
        · dsimp only
          rcases hl : lookupCodeHOLFinite s.code.lookup fn values with _ | ⟨body, callee, rs⟩
          · simp
          · dsimp only
            have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup fn values = some (body, callee, rs) := by rwa [← hcode]
            have bodyOk := hgood fn hf values body callee rs hl'
            split
            · simp
            · have ih1 := evaluate_noCatchableRaise good hgood body bodyOk (callEntryStateHOLFinite s callee) hcode
              have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
              rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, st⟩
              rw [hrun] at ih1 cl
              dsimp only at ih1 cl ⊢
              change st.clock ≤ s.clock - 1 at cl
              have small : st.clock < s.clock := by omega
              cases res with
              | none => simp
              | some r =>
                cases r with
                | returned retVal =>
                  dsimp only
                  split
                  · cases dest with
                    | none => simp
                    | some kv =>
                      rcases kv with ⟨vk, vn⟩
                      dsimp only
                      by_cases hval : isValidValueHOLExact s.toExact vk vn retVal = true
                      · rw [if_pos hval]; simp
                      · rw [if_neg hval]; simp
                  · simp
                | «break» => simp
                | «continue» => simp
                | _ => exact ih1
  | _ => simp [shape, noCatchableRaise] at hp
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals
    simp_wf
    apply lex_ncr
    try subst shape
    try simp only [setVarHOLFinite, decClockHOLFinite, callEntryStateHOLFinite,
      ProgHOL.seq.sizeOf_spec, ProgHOL.ite.sizeOf_spec, ProgHOL.dec.sizeOf_spec,
      ProgHOL.while.sizeOf_spec, ProgHOL.decCall.sizeOf_spec, ProgHOL.call.sizeOf_spec, true_and]
    first
      | exact Or.inl smallR
      | exact Or.inl smaller
      | exact Or.inl small
      | omega
      | (rcases Nat.lt_or_eq_of_le mclock with h | h
         · exact Or.inl h
         · exact Or.inr ⟨h, by simp +arith⟩)
      | exact Or.inr ⟨rfl, by simp +arith⟩

private def initAllocCallees (f : MlS) : Bool :=
  f == ofString "trap_with" || f == ofString "alloc" || f == ofString "htab_new"

private theorem initAllocCallees_good :
    ∀ f, initAllocCallees f = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup f values =
        some (body, callee, rs) →
      noCatchableRaise initAllocCallees body = true := by
  intro f hf values body callee rs hfound
  obtain ⟨params, rs', hinst⟩ :=
    InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
  simp only [initAllocCallees, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with (rfl | rfl) | rfl
  · have hl := lookup_of_guestAst_getElem 3 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_trap_with) rfl
    change originalRuntimeCode.lookup (ofString "trap_with") = _ at hl
    rw [hl] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_alloc) rfl
    change originalRuntimeCode.lookup (ofString "alloc") = _ at hl
    rw [hl] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [R10Shards.SoloHtabNew.lookup_htab_new] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl

private theorem initAllocCallees_keeps_sp :
    ∀ f, initAllocCallees f = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup f values =
        some (body, callee, rs) →
      InitECandidate.Solver.GuestGlobalKeep.keepsG (ofString "scratch_ptr") initAllocCallees body = true := by
  intro f hf values body callee rs hfound
  obtain ⟨params, rs', hinst⟩ :=
    InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
  simp only [initAllocCallees, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with (rfl | rfl) | rfl
  · have hl := lookup_of_guestAst_getElem 3 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_trap_with) rfl
    change originalRuntimeCode.lookup (ofString "trap_with") = _ at hl
    rw [hl] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_alloc) rfl
    change originalRuntimeCode.lookup (ofString "alloc") = _ at hl
    rw [hl] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [R10Shards.SoloHtabNew.lookup_htab_new] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl

private theorem htab_new_no_catchable_exn {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (e : MlS) (v : ValueHOL 64)
    (hne : e ≠ ofString "TrapErr") :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_new)).1 ≠
      some (.exception e v) :=
  evaluate_noCatchableRaise initAllocCallees initAllocCallees_good
    (sourceFnBody Guest.Software.guestFn_htab_new) rfl s hcode e v hne

private def htabSetCallees (f : MlS) : Bool :=
  f == ofString "trap_with" ||
  f == ofString "alloc" ||
  f == ofString "memcpy" ||
  f == ofString "memeq" ||
  f == ofString "htab_first_diff" ||
  f == ofString "htab_find_leaf" ||
  f == ofString "htab_new_node" ||
  f == ofString "htab_new_leaf" ||
  f == ofString "htab_new_internal" ||
  f == ofString "htab_grow" ||
  f == ofString "htab_set"

private theorem htabSetCallees_noCatchableRaise :
    ∀ f, htabSetCallees f = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup f values =
        some (body, callee, rs) →
      noCatchableRaise htabSetCallees body = true := by
  intro f hf values body callee rs hfound
  obtain ⟨params, rs', hinst⟩ :=
    InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
  simp only [htabSetCallees, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with (((((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl
  · have hl := lookup_of_guestAst_getElem 3 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_trap_with) rfl
    change originalRuntimeCode.lookup (ofString "trap_with") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [R13Shards.lookup_alloc_r13] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [SoloHtabSet.lookup_memcpy_fn] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [SoloHtabSet.lookup_memeq_fn] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [SoloHtabSet.lookup_htab_first_diff] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [SoloHtabSet.lookup_htab_find_leaf] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [SoloHtabSet.lookup_htab_new_node] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [SoloHtabSet.lookup_htab_new_leaf] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [SoloHtabSet.lookup_htab_new_internal] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [SoloHtabSet.lookup_htab_grow] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [SoloHtabSet.lookup_htab_set] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl

private theorem htab_set_no_catchable_exn {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (e : MlS) (v : ValueHOL 64)
    (hne : e ≠ ofString "TrapErr") :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_set)).1 ≠
      some (.exception e v) :=
  evaluate_noCatchableRaise htabSetCallees htabSetCallees_noCatchableRaise
    (sourceFnBody Guest.Software.guestFn_htab_set) rfl s hcode e v hne

private theorem htab_new_heap_props {F : Type}
    (s : PanSemStateFiniteExact 64 F) (kw capw : BitVec 64)
    (hAR : ArenaReady s)
    (hkl : kw.toNat ∈ htabKeyLens)
    (hcl : capw.toNat ≤ htabCapMax)
    (hk : s.locals.lookup (ofString "key_len") = some (.val (.word kw)))
    (hc : s.locals.lookup (ofString "cap") = some (.val (.word capw)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_new)).1 =
      some (.returned v)) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_new)).2
    ∃ tw : BitVec 64,
      v = .val (.word tw) ∧
      globN s "heap_ptr" ≤ tw.toNat ∧
      tw.toNat + 88 ≤ globN post "heap_ptr" ∧
      ArenaReady post ∧
      HtabWF post tw.toNat ∧
      hdr post tw.toNat 3 = 0 ∧
      hdr post tw.toNat 0 = kw.toNat ∧
      (∀ i ∈ htabFootprint post tw.toNat,
        Allocated post i ∧ Inside i (globN s "heap_ptr") (globN post "heap_ptr")) ∧
      FrameOutside s post [(globN s "scratch_ptr", 0)]
        (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") ∧
      (∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = post.globals.lookup k) := by
  dsimp only
  have hpos : 0 < globN s "heap_ptr" := by
    have := hAR.2.1; rw [sourceBase_val] at this; omega
  obtain ⟨p0, hp, _⟩ := R10Shards.SoloHtabNew.global_word_of_pos s "heap_ptr" hpos
  have hnp := R10Shards.SoloHtabNew.htab_new_run s hAR.1.code kw capw p0 hk hc hp hAR hkl hcl v hret
  obtain ⟨tw, rfl, hAp, hAG, hwf, hcnt0, hhdr0, hfp, hfr, hgl⟩ := hnp
  set post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_new)).2
  have hsp_lk : s.globals.lookup (ofString "scratch_ptr") = post.globals.lookup (ofString "scratch_ptr") :=
    (InitECandidate.Solver.GuestGlobalKeep.evaluate_keepsG
      (ofString "scratch_ptr") initAllocCallees initAllocCallees_keeps_sp
      (sourceFnBody Guest.Software.guestFn_htab_new) rfl s hAR.1.code).symm
  have hsp_eq : globN post "scratch_ptr" = globN s "scratch_ptr" :=
    globN_eq_of_lookup hsp_lk
  have hfp_heap : ∀ i ∈ htabFootprint post tw.toNat,
      Allocated post i ∧ Inside i (globN s "heap_ptr") (globN post "heap_ptr") := by
    intro i hi
    obtain ⟨hal_i, hin_or⟩ := hfp i hi
    rcases hin_or with hin_h | hin_s
    · exact ⟨hal_i, hin_h⟩
    · rw [hsp_eq] at hin_s
      have hi0 : i.2 = 0 := by dsimp [Inside] at hin_s; omega
      have hpos_i : 0 < i.2 := by
        simp only [htabFootprint, List.mem_cons, List.not_mem_nil, or_false] at hi
        have hc2 : 2 ≤ hdr post tw.toNat 10 := hwf.2.2.2.2.2.1
        have hst1 : 1 ≤ hdr post tw.toNat 0 := hwf.2.2.1
        have hst_eq : hdr post tw.toNat 1 = (hdr post tw.toNat 0 + 7) / 8 * 8 := hwf.2.2.2.2.1
        rcases hi with rfl | rfl | rfl | rfl
        · dsimp; omega
        · dsimp; rw [hst_eq]
          exact Nat.mul_pos (by omega) (by omega)
        · dsimp; omega
        · dsimp; omega
      omega
  have ht_fp : (tw.toNat, 88) ∈ htabFootprint post tw.toNat := by simp [htabFootprint]
  have ht_in := (hfp_heap _ ht_fp).2
  have hfr_sp0 : FrameOutside s post [(globN s "scratch_ptr", 0)]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
    intro a hk0 hnhf
    apply hfr a
    · intro i hi hch
      simp only [List.mem_singleton] at hi; subst hi
      rw [hsp_eq, Nat.sub_self] at hch
      exact hk0 _ (List.mem_singleton.2 rfl) hch
    · exact hnhf
  have hgl' : ∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = post.globals.lookup k := by
    intro k hk_ne
    by_cases hsp : k = ofString "scratch_ptr"
    · subst hsp; exact hsp_lk
    · apply hgl k
      simp [List.mem_cons, hk_ne, hsp]
  exact ⟨tw, rfl, ht_in.1, ht_in.2, hAp, hwf, hcnt0,
    by simpa [locN, hk] using hhdr0, hfp_heap, hfr_sp0, hgl'⟩

private theorem worldEff_of_htab_new_entry {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {kw capw : BitVec 64}
    (h : WorldEff s cur Rl B hpGw)
    (hkl : kw.toNat ∈ htabKeyLens)
    (hcl : capw.toNat ≤ htabCapMax)
    (hk : callee.lookup (ofString "key_len") = some (.val (.word kw)))
    (hc : callee.lookup (ofString "cap") = some (.val (.word capw)))
    (hs8 : globN s "heap_ptr" % 8 = 0)
    (hres : Resumes (evaluateHOLFiniteState (callEntryStateHOLFinite cur callee)
      (sourceFnBody Guest.Software.guestFn_htab_new)).1) :
    let entry := callEntryStateHOLFinite cur callee
    let post := (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_htab_new)).2
    WorldEff s post Rl B hpGw ∧
    ∃ tw : BitVec 64,
      (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_htab_new)).1 =
        some (.returned (.val (.word tw))) ∧
      HtabWF post tw.toNat ∧
      hdr post tw.toNat 0 = kw.toNat ∧
      (∀ i ∈ htabFootprint post tw.toNat,
        Allocated post i ∧ Inside i (globN s "heap_ptr") (globN post "heap_ptr")) := by
  dsimp only
  set entry := callEntryStateHOLFinite cur callee
  have heff_e : WorldEff s entry Rl B hpGw := h.locals_clock callee (cur.clock - 1)
  rcases hres with ⟨rv, hret⟩ | ⟨e, ev, hex, hne⟩
  · obtain ⟨tw, rfl, _, _, hAp, hwf, _, hhdr0, hfp, hfr, hg⟩ :=
      htab_new_heap_props entry kw capw heff_e.arena hkl hcl hk hc rv hret
    have hm := PanRunBounded.evaluateHOLFiniteState_metadata entry
      (sourceFnBody Guest.Software.guestFn_htab_new)
    set post := (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_htab_new)).2
    have hhp_le : globN entry "heap_ptr" ≤ globN post "heap_ptr" := by
      have ht_fp : (tw.toNat, 88) ∈ htabFootprint post tw.toNat := by simp [htabFootprint]
      have ht_in := (hfp _ ht_fp).2
      dsimp [Inside] at ht_in; omega
    have hhp_s : globN s "heap_ptr" ≤ globN entry "heap_ptr" := heff_e.hp_lo
    have hwe : WorldEff s post Rl B hpGw :=
      worldEff_of_heap_frame heff_e hAp hm.2.1 hm.2.2.1 hm.2.2.2.2 hhp_le hg
        (fun a hne_a => by
          by_contra hn
          exact hne_a (evaluateHOLFiniteState_mem_out_dom entry _ hn))
        (fun a ha => by
          have ha8_or : ¬ entry.memaddrs a ∨ a.toNat % 8 = 0 := by
            by_cases hd : entry.memaddrs a
            · right; rw [heff_e.arena.1.memaddrs, ordinaryDomain_iff] at hd; exact hd.1
            · exact Or.inl hd
          rcases ha8_or with hnd | ha8
          · exact evaluateHOLFiniteState_mem_out_dom entry _ hnd
          · apply hfr a
            · intro i hi hch
              simp only [List.mem_singleton] at hi; subst hi
              have hsp8 : globN entry "scratch_ptr" % 8 = 0 := heff_e.arena.2.2.2.2.2.2.2.2.1
              rcases hch with ⟨_, _⟩; dsimp only at *; omega
            · intro hch
              apply ha
              rcases hch with ⟨h1, h2⟩
              have hn8 : globN post "heap_ptr" % 8 = 0 := hAp.2.2.2.2.2.2.1
              constructor <;> dsimp only at * <;> omega)
        hs8
    exact ⟨hwe, tw, hret, hwf, hhdr0, fun i hi =>
      ⟨(hfp i hi).1, ⟨le_trans hhp_s (hfp i hi).2.1, (hfp i hi).2.2⟩⟩⟩
  · exfalso
    exact htab_new_no_catchable_exn entry heff_e.code e ev hne hex

private theorem worldEff_of_htabExitAt {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {t : Nat} {p : ProgHOL 64}
    (h : WorldEff s cur Rl B hpGw)
    (hexit : SoloHtabSet.HtabExitAt t cur (evaluateHOLFiniteState cur p).2)
    (hfp : ∀ i ∈ htabFootprint cur t,
      Inside i (globN s "heap_ptr") (globN cur "heap_ptr"))
    (hs8 : globN s "heap_ptr" % 8 = 0) :
    WorldEff s (evaluateHOLFiniteState cur p).2 Rl B hpGw ∧
    (∀ i ∈ htabFootprint (evaluateHOLFiniteState cur p).2 t,
      Allocated (evaluateHOLFiniteState cur p).2 i ∧
      Inside i (globN s "heap_ptr") (globN (evaluateHOLFiniteState cur p).2 "heap_ptr")) := by
  obtain ⟨hA, hwf, hk0, hk1, hhp, hnew, hfr, hg⟩ := hexit
  have hhp_s : globN s "heap_ptr" ≤ globN cur "heap_ptr" := h.hp_lo
  have hm := PanRunBounded.evaluateHOLFiniteState_metadata cur p
  refine ⟨worldEff_of_heap_frame h hA hm.2.1 hm.2.2.1 hm.2.2.2.2 hhp
    (fun k hk => hg k (by simpa [List.mem_map, List.mem_singleton] using hk))
    (fun a hne => by
      by_contra hn
      exact hne (evaluateHOLFiniteState_mem_out_dom cur p hn)) ?_ hs8, ?_⟩
  · intro a ha
    by_cases hdom : cur.memaddrs a
    · have ha8 : a.toNat % 8 = 0 := by
        rw [h.arena.1.memaddrs, ordinaryDomain_iff] at hdom; exact hdom.1
      have hn8 : globN (evaluateHOLFiniteState cur p).2 "heap_ptr" % 8 = 0 := hA.2.2.2.2.2.2.1
      have hc8 : globN cur "heap_ptr" % 8 = 0 := h.arena.2.2.2.2.2.2.1
      apply hfr a
      · intro i hi hhit
        have hin := hfp i hi
        rcases hin with ⟨hi1, hi2⟩
        apply ha
        rcases hhit with ⟨h1, h2⟩
        constructor <;> dsimp only at * <;> omega
      · intro hhit
        apply ha
        rcases hhit with ⟨h1, h2⟩
        constructor <;> dsimp only at * <;> omega
    · exact evaluateHOLFiniteState_mem_out_dom cur p hdom
  · intro i hi
    obtain ⟨hal, hold | hfresh⟩ := hnew i hi
    · obtain ⟨j, hj, hij⟩ := hold
      have hjin := hfp j hj
      rcases hij with ⟨h1, h2⟩
      rcases hjin with ⟨h3, h4⟩
      exact ⟨hal, ⟨by dsimp only at *; omega, by dsimp only at *; omega⟩⟩
    · rcases hfresh with ⟨h1, h2⟩
      exact ⟨hal, ⟨by dsimp only at *; omega, by dsimp only at *; omega⟩⟩

/-! ## Section 2: `nodedb_build` (`wk_nodedb_build_strong`) -/

private theorem lookup_nodedb_build :
    originalRuntimeCode.lookup (ofString "nodedb_build") =
      some ([(ofString "slice_arr", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_nodedb_build, .one) :=
  lookup_of_guestAst_getElem 253 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_nodedb_build) rfl

private abbrev nodedbRegions {F : Type} (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
   (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
   (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)]

private theorem byteEff_ivlUnhit_of_disj {F : Type}
    {cur next : PanSemStateFiniteExact 64 F} {Sub : List Ivl} {i : Ivl}
    (hG : GuestInv cur) (hb : ByteEff cur next Sub)
    (hi1 : i.1 % 8 = 0) (hi2 : i.2 % 8 = 0)
    (hdisj : ∀ iv ∈ Sub, iv.1 + iv.2 ≤ sourceBase ∨ Disj i iv) :
    IvlUnhit cur next i := by
  intro a ha8 hhit
  by_contra hne
  have hdom := hb.out_dom a hne
  rw [hG.memaddrs, ordinaryDomain_iff] at hdom
  obtain ⟨iv, hiv, hpos, hc1, hc2⟩ := hb.cell_frame a hne
  rcases hdisj iv hiv with hlow | hdj
  · omega
  · rcases hhit with ⟨hi_lo, hi_hi⟩
    rcases hdj with h0 | h0 | hle | hge <;> omega

private theorem worldEff_decCall_eff_post {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    (name : MlS) (sh : ShapeHOL) (fname : MlS) (args : List (ExpHOL 64)) {cont : ProgHOL 64}
    (params : List (MlS × ShapeHOL)) (fbody : ProgHOL 64) (retSh : ShapeHOL)
    (hlook : originalRuntimeCode.lookup fname = some (params, fbody, retSh))
    {Q : Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}
    (hQ_loc : ∀ r (st : PanSemStateFiniteExact 64 F) L k,
      Q r st → Q r { st with locals := L, clock := k })
    (hQ_nonret : ∀ r st, (∀ rv, r ≠ some (.returned rv)) → Q r st)
    (hcallee : ∀ (callee : HolFiniteMapExact MlS (ValueHOL 64)) (vals : List (ValueHOL 64)),
      evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args = some vals →
      lookupCodeHOLFinite cur.code.lookup fname vals = some (fbody, callee, retSh) →
      let entry := callEntryStateHOLFinite cur callee
      (evaluateHOLFiniteState entry fbody).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState entry fbody).1 →
      WorldEff s (evaluateHOLFiniteState entry fbody).2 Rl B gw)
    (hcont : ∀ (callee : HolFiniteMapExact MlS (ValueHOL 64)) (vals : List (ValueHOL 64))
        (rv : ValueHOL 64) (cpost : PanSemStateFiniteExact 64 F),
      evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args = some vals →
      lookupCodeHOLFinite cur.code.lookup fname vals = some (fbody, callee, retSh) →
      evaluateHOLFiniteState (callEntryStateHOLFinite cur callee) fbody = (some (.returned rv), cpost) →
      shapeEqHOL (shapeOfHOLExact rv) sh = true →
      WorldEff s cpost Rl B gw →
      let mid := setVarHOLFinite name rv { cpost with locals := cur.locals }
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState mid cont).1 →
      WorldEff s (evaluateHOLFiniteState mid cont).2 Rl B gw ∧
      Q (evaluateHOLFiniteState mid cont).1 (evaluateHOLFiniteState mid cont).2)
    (hnt : (evaluateHOLFiniteState cur (.decCall name sh fname args cont)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.decCall name sh fname args cont)).1) :
    WorldEff s (evaluateHOLFiniteState cur (.decCall name sh fname args cont)).2 Rl B gw ∧
    Q (evaluateHOLFiniteState cur (.decCall name sh fname args cont)).1
      (evaluateHOLFiniteState cur (.decCall name sh fname args cont)).2 := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hcr ⊢
  rcases hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args with _ | vals
  · exact ⟨h, hQ_nonret _ _ (by simp)⟩
  · simp only [hargs] at hnt hcr ⊢
    rcases hl : lookupCodeHOLFinite cur.code.lookup fname vals with _ | ⟨body', callee, ret'⟩
    · exact ⟨h, hQ_nonret _ _ (by simp)⟩
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
            dsimp only at hnt hcr ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact rv) sh && shapeEqHOL (shapeOfHOLExact rv) retSh) = true
            · simp only [hsh, ↓reduceIte] at hnt hcr ⊢
              have hsh1 : shapeEqHOL (shapeOfHOLExact rv) sh = true := (Bool.and_eq_true _ _ ▸ hsh).1
              have heff_c := hcallee callee vals hargs hl (by rw [hrun]; simp)
                (by rw [hrun]; exact Or.inl ⟨rv, rfl⟩)
              rw [hrun] at heff_c
              obtain ⟨heff_k, hQ_k⟩ := hcont callee vals rv cpost hargs hl hrun hsh1 heff_c hnt hcr
              exact ⟨heff_k.locals_clock _ _, hQ_loc _ _ _ _ hQ_k⟩
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hcr
              rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
          | exception exId exVal =>
            have hres_e : Resumes (some (.exception exId exVal)) := by
              rcases hcr with hc0 | hc0 | hc0 | hr <;> [simp at hc0; simp at hc0; simp at hc0; exact hr]
            have heff_c := hcallee callee vals hargs hl (by rw [hrun]; simp)
              (by rw [hrun]; exact hres_e)
            rw [hrun] at heff_c
            exact ⟨heff_c.locals_clock _ _, hQ_nonret _ _ (by simp)⟩

private theorem worldEff_dec_post {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    (name : MlS) (sh : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64}
    {Q : Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}
    (hQ_loc : ∀ r (st : PanSemStateFiniteExact 64 F) L k,
      Q r st → Q r { st with locals := L, clock := k })
    (hQ_nonret : ∀ r st, (∀ rv, r ≠ some (.returned rv)) → Q r st)
    (hb : ∀ val,
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) init = some val →
      shapeEqHOL sh (shapeOfHOLExact val) = true →
      let mid := setVarHOLFinite name val cur
      (evaluateHOLFiniteState mid body).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState mid body).1 →
      WorldEff s (evaluateHOLFiniteState mid body).2 Rl B gw ∧
      Q (evaluateHOLFiniteState mid body).1 (evaluateHOLFiniteState mid body).2) :
    (evaluateHOLFiniteState cur (.dec name sh init body)).1 ≠ some .timeOut →
    ContOrRes (evaluateHOLFiniteState cur (.dec name sh init body)).1 →
    WorldEff s (evaluateHOLFiniteState cur (.dec name sh init body)).2 Rl B gw ∧
    Q (evaluateHOLFiniteState cur (.dec name sh init body)).1
      (evaluateHOLFiniteState cur (.dec name sh init body)).2 := by
  intro hnt hcr
  rw [evaluateHOLFiniteState_dec_total] at hnt hcr ⊢
  dsimp only at hnt hcr ⊢
  rcases hval : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) init with _ | val
  · exact ⟨h, hQ_nonret _ _ (by simp)⟩
  · simp only [hval] at hnt hcr ⊢
    by_cases hsh : shapeEqHOL sh (shapeOfHOLExact val) = true
    · simp only [hsh, ↓reduceIte] at hnt hcr ⊢
      obtain ⟨heff_b, hQ_b⟩ := hb val hval hsh hnt hcr
      exact ⟨heff_b.locals_clock _ _, hQ_loc _ _ _ _ hQ_b⟩
    · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hcr ⊢
      exact ⟨h, hQ_nonret _ _ (by simp)⟩

private theorem fixedObjects_eq_of_worldEff_no_bufs {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    {S Nd : List Nat}
    (hAs : ArenaReady s)
    (heff : WorldEff s post Rl ([] : List (String × Nat)) hpGw)
    (hWT : WorldTypedWith s S Nd)
    (hDisjR : IvlsDisj Rl (worldTypedIvls s S Nd)) :
    fixedObjects post = fixedObjects s := by
  obtain ⟨hT, _, hF, _⟩ := hWT
  have hcore : ∀ g ∈ coreWorldGlobals, globN post g = globN s g :=
    fun g hg => globN_eq_of_lookup (heff.gw_kept (ofString g) (hp_core_out g hg))
  have hdom_wr : ∀ a : BitVec 64, post.memory a ≠ s.memory a → s.memaddrs a :=
    heff.out_dom
  have hlow : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 :=
    ⟨mem_low_eq_of_domain_writes hdom_wr hAs.1 (by rw [sourceBase_val]; omega),
     mem_low_eq_of_domain_writes hdom_wr hAs.1 (by rw [sourceBase_val]; omega)⟩
  let keep0 : List Ivl := Rl ++ [freeGap s]
  have hfr_pos : ∀ a : BitVec 64, post.memory a ≠ s.memory a →
      (∃ j ∈ keep0, CellHitsPos a.toNat j) ∨ CellHitsPos a.toNat (heapFree s) := by
    intro a hne
    rcases heff.cell_frame a hne with ⟨ivl, hivl, hhit⟩ | ⟨_, hgs, _⟩ | hfg | hhf
    · exact Or.inl ⟨ivl, List.mem_append_left _ hivl, hhit⟩
    · simp at hgs
    · exact Or.inl ⟨freeGap s, List.mem_append_right _ List.mem_cons_self, hfg⟩
    · exact Or.inr hhf
  have hu_wti_aligned : ∀ i ∈ worldTypedIvls s S Nd, Allocated s i → i.1 % 8 = 0 → i.2 % 8 = 0 →
      IvlUnhit s post i := by
    intro i hi hal hi1 hi2
    refine ivlUnhit_of_cellHitsPos hi1 hi2 hfr_pos (fun j hj => ?_) (disj_allocated_heapFree hAs.2 hal)
    simp only [keep0, List.mem_append, List.mem_singleton] at hj
    rcases hj with hjR | rfl
    · exact Disj.flip (hDisjR j hjR i hi)
    · exact disj_allocated_freeGap hAs.2 hal
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
      (by omega)
  have hbo_eq := (blockOutObjects_eq_of_bo_unhit hAs.2 hF (hcore "bo" (by decide))
    hT.2.2.2.2.2.2.2.2.2.2.1 hu_bo hu_bo_lst).1
  have hbal_eq := (balObjects_eq_of_unhit hAs.2 hT hF (hcore "bal_accounts" (by decide))
    hu_tab hu_bal hlow).1
  have hgb_eq : ∀ gn ∈ globalBuffers, globN post gn.1 = globN s gn.1 :=
    fun gn hgn => globN_eq_of_lookup (heff.gw_kept (ofString gn.1) (hp_no_gb gn hgn))
  unfold fixedObjects
  rw [hbo_eq, hbal_eq, hcore "journal" (by decide), hcore "journal_cap" (by decide)]
  congr 3
  apply List.map_congr_left
  intro gn hgn
  simp [bufferRegion, hgb_eq gn hgn]

private def NodeDbPost {F : Type} (s : PanSemStateFiniteExact 64 F)
    (r : Option (PanSemResultExact 64)) (post : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ rv, r = some (.returned rv) →
    ∃ tw : BitVec 64, rv = .val (.word tw) ∧
      HtabWF post tw.toNat ∧
      hdr post tw.toNat 0 = 32 ∧
      (∀ i ∈ htabFootprint post tw.toNat,
        Inside i (globN s "heap_ptr") (globN post "heap_ptr"))

private theorem nodeDbPost_locals_clock {F : Type} {s : PanSemStateFiniteExact 64 F}
    (r : Option (PanSemResultExact 64)) (st : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (hQ : NodeDbPost s r st) :
    NodeDbPost s r { st with locals := L, clock := k } := by
  intro rv hret
  obtain ⟨tw, rfl, hwf, hhdr0, hfp⟩ := hQ rv hret
  exact ⟨tw, rfl, (htabWF_with_locals st L k tw.toNat).2 hwf, hhdr0, hfp⟩

private theorem nodeDbPost_nonret {F : Type} {s : PanSemStateFiniteExact 64 F}
    (r : Option (PanSemResultExact 64)) (st : PanSemStateFiniteExact 64 F)
    (h : ∀ rv, r ≠ some (.returned rv)) :
    NodeDbPost s r st :=
  fun rv hr => absurd hr (h rv)

private theorem worldEff_seq_post {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    {a b : ProgHOL 64}
    {Q : Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}
    (hQ_nonret : ∀ r st, (∀ rv, r ≠ some (.returned rv)) → Q r st)
    (ha_noret : ∀ rv, (evaluateHOLFiniteState cur a).1 ≠ some (.returned rv))
    (hnt : (evaluateHOLFiniteState cur (.seq a b)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.seq a b)).1)
    (ha : (evaluateHOLFiniteState cur a).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState cur a).1 →
      WorldEff s (evaluateHOLFiniteState cur a).2 Rl B gw)
    (hb : ∀ m, evaluateHOLFiniteState cur a = (none, m) →
      WorldEff s m Rl B gw →
      (evaluateHOLFiniteState m b).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState m b).1 →
      WorldEff s (evaluateHOLFiniteState m b).2 Rl B gw ∧
      Q (evaluateHOLFiniteState m b).1 (evaluateHOLFiniteState m b).2) :
    WorldEff s (evaluateHOLFiniteState cur (.seq a b)).2 Rl B gw ∧
    Q (evaluateHOLFiniteState cur (.seq a b)).1 (evaluateHOLFiniteState cur (.seq a b)).2 := by
  rw [evaluateHOLFiniteState_seq_line780] at hnt hcr ⊢
  rcases hr : evaluateHOLFiniteState cur a with ⟨r1, m⟩
  simp only [hr] at hnt hcr ha_noret ⊢
  cases r1 with
  | none =>
    have heff_a := ha (by rw [hr]; simp) (by rw [hr]; exact Or.inl rfl)
    rw [hr] at heff_a
    exact hb m hr heff_a hnt hcr
  | some r =>
    have heff_a := ha (by rw [hr]; intro h; injection h with h'; subst h'; exact hnt rfl)
      (by rw [hr]; exact hcr)
    rw [hr] at heff_a
    exact ⟨heff_a, hQ_nonret (some r) m ha_noret⟩

private theorem while_noret {F : Type} (st : PanSemStateFiniteExact 64 F)
    (c : ExpHOL 64) (b : ProgHOL 64)
    (hb : ∀ (u : PanSemStateFiniteExact 64 F) rv,
      (evaluateHOLFiniteState u b).1 ≠ some (.returned rv)) :
    ∀ rv, (evaluateHOLFiniteState st (.while c b)).1 ≠ some (.returned rv) := by
  suffices h : ∀ k (cur : PanSemStateFiniteExact 64 F), cur.clock = k →
      ∀ rv, (evaluateHOLFiniteState cur (.while c b)).1 ≠ some (.returned rv) from
    h st.clock st rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro cur hclk rv
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    rcases hc0 : @evalHOLFinite 64 F _ cur (fun a => Classical.propDecidable (cur.memaddrs a)) c with _ | cv0
    · simp
    · rcases cv0 with ⟨⟨cw0⟩⟩ | _ | _ <;> try simp
      by_cases hwz : cw0 = 0#64
      · subst hwz; simp
      · rw [if_neg hwz]
        by_cases hkz : cur.clock = 0
        · rw [if_pos hkz]; simp
        · rw [if_neg hkz]
          have hrem0 := evaluateHOLFiniteState_clock_le (decClockHOLFinite cur) b
          rcases hb0 : evaluateHOLFiniteState (decClockHOLFinite cur) b with ⟨rb0, sb0⟩
          simp only [hb0] at hrem0 ⊢
          have hlt0 : sb0.clock < k := by change sb0.clock ≤ cur.clock - 1 at hrem0; omega
          have hnb := hb (decClockHOLFinite cur) rv
          rw [hb0] at hnb
          cases rb0 with
          | none => exact ih sb0.clock hlt0 sb0 rfl rv
          | some r0 =>
            cases r0 with
            | «continue» => exact ih sb0.clock hlt0 sb0 rfl rv
            | returned _ => exact hnb
            | _ => simp

private theorem call0_noret {F : Type} (u : PanSemStateFiniteExact 64 F)
    (fn : MlS) (args : List (ExpHOL 64)) :
    ∀ rv, (evaluateHOLFiniteState u (.call (some (none, none)) fn args)).1 ≠ some (.returned rv) := by
  intro rv
  rw [evaluateHOLFiniteState_call]
  rcases evalListHOLFinite u (h := fun a => Classical.propDecidable (u.memaddrs a)) args with _ | vals
  · simp
  · dsimp only
    rcases lookupCodeHOLFinite u.code.lookup fn vals with _ | ⟨body, callee, rs⟩
    · simp
    · dsimp only
      split
      · simp
      · rcases evaluateHOLFiniteState (callEntryStateHOLFinite u callee) body with ⟨r, st⟩
        cases r with
        | none => simp
        | some r1 =>
          cases r1 with
          | returned _ => dsimp only; split <;> simp
          | _ => simp

private theorem assign_local_noret {F : Type} (u : PanSemStateFiniteExact 64 F)
    (x : MlS) (e : ExpHOL 64) :
    ∀ rv, (evaluateHOLFiniteState u (.assign .local x e)).1 ≠ some (.returned rv) := by
  intro rv
  rw [evaluateHOLFiniteState_assign]
  rcases @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) e with _ | v
  · simp
  · dsimp only; split <;> simp

private theorem seq_noret {F : Type} (u : PanSemStateFiniteExact 64 F) {a b : ProgHOL 64}
    (ha : ∀ rv, (evaluateHOLFiniteState u a).1 ≠ some (.returned rv))
    (hb : ∀ mid, evaluateHOLFiniteState u a = (none, mid) →
      ∀ rv, (evaluateHOLFiniteState mid b).1 ≠ some (.returned rv)) :
    ∀ rv, (evaluateHOLFiniteState u (.seq a b)).1 ≠ some (.returned rv) := by
  intro rv
  rw [evaluateHOLFiniteState_seq_line780]
  rcases ha0 : evaluateHOLFiniteState u a with ⟨ra, mid⟩
  rw [ha0] at ha
  cases ra with
  | none => exact hb mid ha0 rv
  | some _ => exact ha rv

private theorem nodedb_keccak_unhit_fresh {F : Type}
    {s cur next : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hAs : ArenaReady s) (hWT : WorldTypedWith s S Nd)
    (heff_cur : WorldEff s cur (nodedbRegions s) ([] : List (String × Nat)) hpGw)
    (heff_next : WorldEff s next (nodedbRegions s) ([] : List (String × Nat)) hpGw)
    {Sub : List Ivl}
    (hb : ByteEff cur next Sub)
    (hsub : ∀ iv ∈ Sub,
      iv.1 + iv.2 ≤ sourceBase ∨
      ∃ gn ∈ ([("keccak_st", 200), ("keccak_pad", 136), ("mpt_hash_scratch", 40)] : List (String × Nat)),
        Inside iv (bufferRegion s gn).1 ((bufferRegion s gn).1 + (bufferRegion s gn).2))
    {i : Ivl}
    (hi1 : i.1 % 8 = 0) (hi2 : i.2 % 8 = 0)
    (hin : Inside i (globN s "heap_ptr") (globN cur "heap_ptr")) :
    IvlUnhit cur next i := by
  refine byteEff_ivlUnhit_of_disj heff_cur.arena.1 hb hi1 hi2 (fun iv hiv => ?_)
  rcases hsub iv hiv with hlow | ⟨gn, hgn, hin_gn⟩
  · exact Or.inl hlow
  · right
    have hgn_gb : gn ∈ globalBuffers := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hgn
      rcases hgn with rfl | rfl | rfl <;> decide
    have hmem_fo : bufferRegion s gn ∈ fixedObjects s := by
      unfold fixedObjects
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      exact List.mem_map.2 ⟨gn, hgn_gb, rfl⟩
    have hmem_wo : bufferRegion s gn ∈ worldOwned s S Nd := by
      unfold worldOwned; exact List.mem_append_left _ (List.mem_append_right _ hmem_fo)
    rcases worldOwned_empty_or_allocated hWT _ hmem_wo with hz | hal
    · exact Or.inr (Or.inl (by dsimp [Inside] at hin_gn; omega))
    · exact disj_of_inside_right hin_gn (disj_allocated_fresh_heap hAs.2 heff_cur.arena.2 hal hin)

/-- Entry guard for `nodedb_build`: `WorldOK s` plus `locN s "n" < 2 ^ 31`, preventing 64-bit
overflow in `2 * n + 2` and bounding the power-of-two capacity `cap ≤ 2 ^ 32 = htabCapMax` passed
to `htab_new`. Every caller (`run_attempt`) satisfies `16 * n ≤ heapLimit < 2 ^ 32`. -/
def NodeDbBuildReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧ locN s "n" < 2 ^ 31

theorem «wk_nodedb_build_strong» :
    WorldKeeps NodeDbBuildReady
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetNodeDb (ofString "nodedb_build") := by
  refine ⟨_, _, _, lookup_nodedb_build, fun {F} s hc hReady ⟨vals, hl⟩ hnt hres => ?_⟩
  obtain ⟨hWOK, hn_bound⟩ := hReady
  rcases hWOK with ⟨hAs, S0, hWT0_ex⟩
  have hWOK : WorldOK s := ⟨hAs, S0, hWT0_ex⟩
  obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
  have hs8 : globN s "heap_ptr" % 8 = 0 := hAs.2.2.2.2.2.2.1
  obtain ⟨saw, nw, rfl, hsa_lk, hn_lk⟩ := lookupCode_two_words (by decide) lookup_nodedb_build hl
  have hn_lt : nw.toNat < 2 ^ 31 := by simpa [locN, hn_lk] using hn_bound
  have heff0 : WorldEff s s (nodedbRegions s) ([] : List (String × Nat)) hpGw :=
    WorldEff.refl s (nodedbRegions s) [] hpGw hAs hc
  have hB_ok_nil : ∀ gs ∈ ([] : List (String × Nat)),
      gs ∈ globalBuffers ∧ gs.1 ∉ typedRecords.map Prod.fst := by simp
  suffices hmain :
      WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_nodedb_build)).2
        (nodedbRegions s) ([] : List (String × Nat)) hpGw ∧
      NodeDbPost s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_nodedb_build)).1
        (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_nodedb_build)).2 by
    obtain ⟨heff_post, hpost⟩ := hmain
    refine heff_post.to_worldStep_Q hWOK hB_ok_nil hp_core_out
      (fun S Nd hWT hDisjR hWT_post _ hne_eq hfp_eq rv hret => ?_)
    obtain ⟨tw, rfl, hwf, hhdr0, hfp_in⟩ := hpost rv hret
    have hfix_eq := fixedObjects_eq_of_worldEff_no_bufs hAs heff_post hWT hDisjR
    have htab_eq : S.flatMap (htabFootprint (evaluateHOLFiniteState s
        (sourceFnBody Guest.Software.guestFn_nodedb_build)).2) =
        S.flatMap (htabFootprint s) :=
      List.flatMap_congr hfp_eq
    have hwo_eq : worldOwned (evaluateHOLFiniteState s
        (sourceFnBody Guest.Software.guestFn_nodedb_build)).2 S Nd =
        worldOwned s S Nd := by
      unfold worldOwned
      rw [htab_eq, hfix_eq, hne_eq]
    refine ⟨tw, rfl, hwf, hhdr0, hfp_in, ?_⟩
    rw [hwo_eq]
    exact freshTable_disj_entry_world hAs heff_post.arena hWT hfp_in
  have hcr : ContOrRes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_nodedb_build)).1 :=
    Or.inr (Or.inr (Or.inr hres))
  dsimp only [Guest.Software.guestFn_nodedb_build, sourceFnBody, sourceFunctionEntry,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hcr ⊢
  -- 1. dec cap := 4
  refine worldEff_dec_post heff0 (ofString "cap") .one (.const 4#64)
    nodeDbPost_locals_clock nodeDbPost_nonret
    (fun vcap hvcap _ hnt1 hcr1 => ?_) hnt hcr
  have hvcap_eq : vcap = .val (.word 4#64) := by simp [evalHOLExact] at hvcap; exact hvcap.symm
  subst hvcap_eq
  set s1 := setVarHOLFinite (ofString "cap") (.val (.word 4#64)) s
  have heff1 : WorldEff s s1 (nodedbRegions s) [] hpGw := heff0.locals_clock _ s.clock
  have hs1_sa : s1.locals.lookup (ofString "slice_arr") = some (.val (.word saw)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsa_lk,
      show ofString "cap" ≠ ofString "slice_arr" by decide]
  have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn_lk,
      show ofString "cap" ≠ ofString "n" by decide]
  have hs1_cap : s1.locals.lookup (ofString "cap") = some (.val (.word 4#64)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  -- 2. Loop 1: while (cap < 2 * n + 2) { cap := cap * 2 }
  let cond1 : ExpHOL 64 :=
    .cmp .lower (.var .local (ofString "cap"))
      (.op .add [.panop .mul [.const 2#64, .var .local (ofString "n")], .const 2#64])
  let body1 : ProgHOL 64 :=
    .assign .local (ofString "cap") (.panop .mul [.var .local (ofString "cap"), .const 2#64])
  let Inv1 : PanSemStateFiniteExact 64 F → Prop := fun u =>
    u.locals.lookup (ofString "slice_arr") = some (.val (.word saw)) ∧
    u.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
    ∃ capw : BitVec 64,
      u.locals.lookup (ofString "cap") = some (.val (.word capw)) ∧
      ∃ k : Nat, 2 ≤ k ∧ k ≤ 32 ∧ capw.toNat = 2 ^ k
  have h2n_lt : (2#64 : BitVec 64).toNat * nw.toNat < 2 ^ 64 := by
    rw [show (2#64 : BitVec 64).toNat = 2 from rfl]; omega
  have h2n_nat : (2#64 * nw).toNat = 2 * nw.toNat := by
    rw [BitVec.toNat_mul, show (2#64 : BitVec 64).toNat = 2 from rfl]
    exact Nat.mod_eq_of_lt h2n_lt
  have h2n2_nat : (2#64 * nw + 2#64).toNat = 2 * nw.toNat + 2 := by
    have h2 : (2#64 : BitVec 64).toNat = 2 := rfl
    rw [BitVec.toNat_add_of_lt (by omega), h2n_nat, h2]
  have hw1_step := worldEff_while_cond_post (s := s) (Rl := nodedbRegions s) (B := []) (gw := hpGw)
    cond1 (body := body1) Inv1
    (fun t ht => ht)
    (fun t cw hcw hcw_ne heff_d ⟨hu_sa, hu_n, capw, hu_cap, k, hk2, hk32, hcap_pow⟩ _ _ => by
      have ht_n : t.locals.lookup (ofString "n") = some (.val (.word nw)) := hu_n
      have ht_cap : t.locals.lookup (ofString "cap") = some (.val (.word capw)) := hu_cap
      have hcond_ev : @evalHOLFinite 64 F _ t (fun a => Classical.propDecidable (t.memaddrs a)) cond1 =
          some (.val (.word (if capw.toNat < 2 * nw.toNat + 2 then 1#64 else 0#64))) := by
        simp [cond1, evalHOLFinite, evalHOLExact, evalListHOLExact, toExact, ht_n, ht_cap,
          valueIsWord, valueWord, panOpHOL, h2n_lt, wordOpHOL, wordOp,
          Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, h2n2_nat]
      rw [hcond_ev] at hcw
      injection hcw with h1; injection h1 with h2; injection h2 with h3
      have hcap_lt : capw.toNat < 2 * nw.toNat + 2 := by
        by_cases hlt : capw.toNat < 2 * nw.toNat + 2
        · exact hlt
        · simp [hlt] at h3; exact absurd h3.symm hcw_ne
      have hk31 : k ≤ 31 := by
        by_contra hgt
        have hk_eq : k = 32 := by omega
        subst hk_eq
        omega
      have hmul_lt : capw.toNat * (2#64 : BitVec 64).toNat < 2 ^ 64 := by
        rw [show (2#64 : BitVec 64).toNat = 2 from rfl, hcap_pow]
        have : 2 ^ k ≤ 2 ^ 31 := Nat.pow_le_pow_right (by omega) hk31
        omega
      refine ⟨worldEff_assign_local heff_d _ _, fun _ => ?_⟩
      dsimp only [body1]
      rw [evaluateHOLFiniteState_assign]
      have hev_mul : @evalHOLExact 64 F _ (decClockHOLFinite t).toExact
          (fun a => Classical.propDecidable ((decClockHOLFinite t).memaddrs a))
          (.panop .mul [.var .local (ofString "cap"), .const 2#64]) =
          some (.val (.word (capw * 2#64))) := by
        simp [evalHOLExact, evalListHOLExact, toExact, hu_cap, valueIsWord, valueWord, panOpHOL, hmul_lt]
      have hvv : isValidValueHOLFinite (decClockHOLFinite t) .local (ofString "cap")
          (.val (.word (capw * 2#64))) = true := by
        simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, toExact, hu_cap,
          shapeOfHOLExact, shapeEqHOL]
      simp only [hev_mul, hvv, ↓reduceIte]
      have hmul_nat : (capw * 2#64).toNat = 2 ^ (k + 1) := by
        rw [BitVec.toNat_mul, Nat.mod_eq_of_lt hmul_lt, hcap_pow,
          show (2#64 : BitVec 64).toNat = 2 from rfl, Nat.pow_succ]
      refine ⟨?_, ?_, capw * 2#64, ?_, k + 1, by omega, by omega, hmul_nat⟩ <;>
        simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          hu_sa, hu_n,
          show ofString "cap" ≠ ofString "slice_arr" by decide,
          show ofString "cap" ≠ ofString "n" by decide])
  refine worldEff_seq_post nodeDbPost_nonret
    (while_noret s1 cond1 body1 (fun u => assign_local_noret u _ _))
    hnt1 hcr1
    (fun hnt_w1 hcr_w1 =>
      (hw1_step s1.clock s1 rfl heff1
        ⟨hs1_sa, hs1_n, 4#64, hs1_cap, 2, le_rfl, by omega, rfl⟩ hnt_w1 hcr_w1).1)
    (fun m1 hm1 heff_m1 hnt2 hcr2 => ?_)
  have hw1_inv : Inv1 m1 := by
    have hnone1 : (evaluateHOLFiniteState s1 (.while cond1 body1)).1 = none := by rw [hm1]
    have hpost1 := (hw1_step s1.clock s1 rfl heff1
      ⟨hs1_sa, hs1_n, 4#64, hs1_cap, 2, le_rfl, by omega, rfl⟩
      (by rw [hm1]; simp) (by rw [hm1]; exact Or.inl rfl)).2
      hnone1 (fun u _ => assign_local_ne_break u _ _)
    rw [hm1] at hpost1
    exact hpost1.1
  obtain ⟨hm1_sa, hm1_n, capw, hm1_cap, kcap, _, hkcap_le32, hcap_pow⟩ := hw1_inv
  have hcap_max : capw.toNat ≤ htabCapMax := by
    rw [hcap_pow]
    have hmax : htabCapMax = 2 ^ 32 := rfl
    rw [hmax]
    exact Nat.pow_le_pow_right (by omega) hkcap_le32
  -- 3. decCall t := htab_new(32, cap)
  refine worldEff_decCall_eff_post heff_m1 (ofString "t") .one (ofString "htab_new")
    [.const 32#64, .var .local (ofString "cap")]
    [(ofString "key_len", .one), (ofString "cap", .one)]
    (sourceFnBody Guest.Software.guestFn_htab_new) .one
    R10Shards.SoloHtabNew.lookup_htab_new
    nodeDbPost_locals_clock nodeDbPost_nonret
    (fun callee vals hargs hl_hn _ hres_hn => by
      have hargs_eq : evalListHOLFinite m1 (h := fun a => Classical.propDecidable (m1.memaddrs a))
          [.const 32#64, .var .local (ofString "cap")] =
          some [.val (.word 32#64), .val (.word capw)] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, hm1_cap]
      rw [hargs_eq] at hargs; injection hargs with hargs'; subst hargs'
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "htab_new")
          [.val (.word 32#64), .val (.word capw)] =
          some (sourceFnBody Guest.Software.guestFn_htab_new, callee, .one) := by
        rwa [← heff_m1.code]
      obtain ⟨w1, w2, hw_eq, hk_cal, hc_cal⟩ :=
        lookupCode_two_words (by decide) R10Shards.SoloHtabNew.lookup_htab_new hl_orig
      have hw12 : w1 = 32#64 ∧ w2 = capw := by
        simp only [List.cons.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq, and_true] at hw_eq
        exact ⟨hw_eq.1.symm, hw_eq.2.symm⟩
      rcases hw12 with ⟨rfl, rfl⟩
      exact (worldEff_of_htab_new_entry heff_m1 (by decide) hcap_max hk_cal hc_cal hs8 hres_hn).1)
    (fun callee vals rv cpost hargs hl_hn hrun_hn _ heff_cpost hnt3 hcr3 => ?_)
    hnt2 hcr2
  have hargs_eq : evalListHOLFinite m1 (h := fun a => Classical.propDecidable (m1.memaddrs a))
      [.const 32#64, .var .local (ofString "cap")] =
      some [.val (.word 32#64), .val (.word capw)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, hm1_cap]
  rw [hargs_eq] at hargs; injection hargs with hargs'; subst hargs'
  have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "htab_new")
      [.val (.word 32#64), .val (.word capw)] =
      some (sourceFnBody Guest.Software.guestFn_htab_new, callee, .one) := by
    rwa [← heff_m1.code]
  obtain ⟨w1, w2, hw_eq, hk_cal, hc_cal⟩ :=
    lookupCode_two_words (by decide) R10Shards.SoloHtabNew.lookup_htab_new hl_orig
  have hw12 : w1 = 32#64 ∧ w2 = capw := by
    simp only [List.cons.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq, and_true] at hw_eq
    exact ⟨hw_eq.1.symm, hw_eq.2.symm⟩
  rcases hw12 with ⟨rfl, rfl⟩
  obtain ⟨_, tw, hret_tw, hwf_cpost, hhdr0_cpost, hfp_cpost⟩ :=
    worldEff_of_htab_new_entry heff_m1 (by decide) hcap_max hk_cal hc_cal hs8
      (by rw [hrun_hn]; exact Or.inl ⟨rv, rfl⟩)
  rw [hrun_hn] at hret_tw hwf_cpost hhdr0_cpost hfp_cpost
  injection hret_tw with hrv_eq; injection hrv_eq with hrv_eq'; subst rv
  dsimp only at hwf_cpost hhdr0_cpost hfp_cpost
  set mid_t := setVarHOLFinite (ofString "t") (.val (.word tw)) { cpost with locals := m1.locals }
  -- 4. dec i := 0
  refine worldEff_dec_post (heff_cpost.locals_clock _ cpost.clock)
    (ofString "i") .one (.const 0#64)
    nodeDbPost_locals_clock nodeDbPost_nonret
    (fun vi hvi _ hnt4 hcr4 => ?_) hnt3 hcr3
  have hvi_eq : vi = .val (.word 0#64) := by simp [evalHOLExact] at hvi; exact hvi.symm
  subst hvi_eq
  set s2 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) mid_t
  have heff_s2 : WorldEff s s2 (nodedbRegions s) [] hpGw :=
    heff_cpost.locals_clock s2.locals cpost.clock
  have hs2_sa : s2.locals.lookup (ofString "slice_arr") = some (.val (.word saw)) := by
    simp [s2, mid_t, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_sa,
      show ofString "i" ≠ ofString "slice_arr" by decide,
      show ofString "t" ≠ ofString "slice_arr" by decide]
  have hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    simp [s2, mid_t, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_n,
      show ofString "i" ≠ ofString "n" by decide,
      show ofString "t" ≠ ofString "n" by decide]
  have hs2_t : s2.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [s2, mid_t, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "i" ≠ ofString "t" by decide]
  have hs2_wf : HtabWF s2 tw.toNat :=
    (htabWF_with_locals cpost s2.locals cpost.clock tw.toNat).2 hwf_cpost
  -- 5. Loop 2: while (i < n) { keccak256(...); htab_set(...); i := i + 1 }
  let cond2 : ExpHOL 64 :=
    .cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))
  let callKeccak : ProgHOL 64 :=
    .call (some (none, none)) (ofString "keccak256")
      [.load .one (.op .add [.var .local (ofString "slice_arr"),
          .panop .mul [.var .local (ofString "i"), .const 16#64]]),
       .load .one (.op .add [.var .local (ofString "slice_arr"),
          .panop .mul [.var .local (ofString "i"), .const 16#64], .const 8#64]),
       .var .global (ofString "mpt_hash_scratch")]
  let callSet : ProgHOL 64 :=
    .call (some (none, none)) (ofString "htab_set")
      [.var .local (ofString "t"),
       .var .global (ofString "mpt_hash_scratch"),
       .op .add [.var .local (ofString "slice_arr"),
          .panop .mul [.var .local (ofString "i"), .const 16#64]]]
  let incI : ProgHOL 64 :=
    .assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])
  let body2 : ProgHOL 64 := .seq callKeccak (.seq callSet incI)
  let Inv2 : PanSemStateFiniteExact 64 F → Prop := fun u =>
    u.locals.lookup (ofString "slice_arr") = some (.val (.word saw)) ∧
    u.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
    u.locals.lookup (ofString "t") = some (.val (.word tw)) ∧
    (∃ iw : BitVec 64, u.locals.lookup (ofString "i") = some (.val (.word iw))) ∧
    HtabWF u tw.toNat ∧
    hdr u tw.toNat 0 = 32 ∧
    (∀ iv ∈ htabFootprint u tw.toNat,
      Allocated u iv ∧ Inside iv (globN s "heap_ptr") (globN u "heap_ptr"))
  have hbody2_nobreak : ∀ u : PanSemStateFiniteExact 64 F,
      (evaluateHOLFiniteState u body2).1 ≠ some .break := fun u =>
    seq_ne_break u (call0_ne_break u _ _) (fun m1' _ =>
      seq_ne_break m1' (call0_ne_break m1' _ _) (fun m2' _ => assign_local_ne_break m2' _ _))
  have hbody2_noret : ∀ (u : PanSemStateFiniteExact 64 F) rv,
      (evaluateHOLFiniteState u body2).1 ≠ some (.returned rv) := fun u =>
    seq_noret u (call0_noret u _ _) (fun m1' _ =>
      seq_noret m1' (call0_noret m1' _ _) (fun m2' _ => assign_local_noret m2' _ _))
  have hw2_step := worldEff_while_cond_post (s := s) (Rl := nodedbRegions s) (B := []) (gw := hpGw)
    cond2 (body := body2) Inv2
    (fun u ⟨hsa, hn, ht, hi, hwf, hh0, hfp⟩ =>
      ⟨hsa, hn, ht, hi, (htabWF_with_locals u u.locals (u.clock - 1) tw.toNat).2 hwf, hh0, hfp⟩)
    (fun u cw hcw hcw_ne heff_ud ⟨hu_sa, hu_n, hu_t, ⟨iw, hu_i⟩, hu_wf, hu_h0, hu_fp⟩ hnt_b2 hcr_b2 => by
      set ud := decClockHOLFinite u
      have hud_i : ud.locals.lookup (ofString "i") = some (.val (.word iw)) := hu_i
      have hud_n : ud.locals.lookup (ofString "n") = some (.val (.word nw)) := hu_n
      have hud_sa : ud.locals.lookup (ofString "slice_arr") = some (.val (.word saw)) := hu_sa
      have hud_t : ud.locals.lookup (ofString "t") = some (.val (.word tw)) := hu_t
      have hi_lt_n : iw.toNat < nw.toNat := by
        have hu_i_orig : u.locals.lookup (ofString "i") = some (.val (.word iw)) := hu_i
        have hu_n_orig : u.locals.lookup (ofString "n") = some (.val (.word nw)) := hu_n
        have hcond_ev : @evalHOLFinite 64 F _ u (fun a => Classical.propDecidable (u.memaddrs a)) cond2 =
            some (.val (.word (if iw.toNat < nw.toNat then 1#64 else 0#64))) := by
          simp [cond2, evalHOLFinite, evalHOLExact, evalListHOLExact, toExact, hu_i_orig, hu_n_orig,
            Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
        rw [hcond_ev] at hcw
        injection hcw with h1; injection h1 with h2; injection h2 with h3
        by_cases hlt : iw.toNat < nw.toNat
        · exact hlt
        · simp [hlt] at h3; exact absurd h3.symm hcw_ne
      obtain ⟨mw, hmw_lk_gw⟩ := heff_ud.arena.2.2.2.2.2.2.2.2.2 "mpt_hash_scratch" (by decide)
      have hmw_lk : ud.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word mw)) := hmw_lk_gw
      have hmw_glob_ud : globN ud "mpt_hash_scratch" = mw.toNat := by simp [globN, hmw_lk]
      have hmw_eq_s : globN s "mpt_hash_scratch" = globN ud "mpt_hash_scratch" :=
        globN_eq_of_lookup (heff_ud.gw_kept (ofString "mpt_hash_scratch") (by decide)).symm
      have hmw_glob_s : globN s "mpt_hash_scratch" = mw.toNat := hmw_eq_s.trans hmw_glob_ud
      have hkst_eq : globBufIvl ud.globals "keccak_st" 200 = bufferRegion s ("keccak_st", 200) := by
        rw [globBufIvl_eq_bufferRegion]
        simp [bufferRegion, globN_eq_of_lookup (heff_ud.gw_kept (ofString "keccak_st") (by decide)).symm]
      have hkpad_eq : globBufIvl ud.globals "keccak_pad" 136 = bufferRegion s ("keccak_pad", 136) := by
        rw [globBufIvl_eq_bufferRegion]
        simp [bufferRegion, globN_eq_of_lookup (heff_ud.gw_kept (ofString "keccak_pad") (by decide)).symm]
      let kSub : List Ivl :=
        [bufferRegion s ("keccak_st", 200), bufferRegion s ("keccak_pad", 136), (mw.toNat, 32)]
      have hk_args_sub : ∀ vals,
          evalListHOLFinite ud (h := fun a => Classical.propDecidable (ud.memaddrs a))
            [.load .one (.op .add [.var .local (ofString "slice_arr"),
                .panop .mul [.var .local (ofString "i"), .const 16#64]]),
             .load .one (.op .add [.var .local (ofString "slice_arr"),
                .panop .mul [.var .local (ofString "i"), .const 16#64], .const 8#64]),
             .var .global (ofString "mpt_hash_scratch")] = some vals →
          ∀ iv ∈ [globBufIvl ud.globals "keccak_st" 200,
                  globBufIvl ud.globals "keccak_pad" 136,
                  (valWordNat (vals[2]?.getD (.rStruct [])), 32)],
            0 < iv.2 → ∃ j ∈ kSub, j.1 ≤ iv.1 ∧ iv.1 + iv.2 ≤ j.1 + j.2 := by
        intro vals hargs iv hiv _
        have hlast : @evalHOLExact 64 F _ ud.toExact (fun a => Classical.propDecidable (ud.memaddrs a))
            (.var .global (ofString "mpt_hash_scratch")) = some (.val (.word mw)) := by
          simp [evalHOLExact, toExact, hmw_lk]
        obtain ⟨v0, v1, rfl⟩ := evalList3_last_word hlast hargs
        rw [hkst_eq, hkpad_eq] at hiv
        simp only [valWordNat, List.mem_cons, List.not_mem_nil, or_false] at hiv
        rcases hiv with rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self, le_rfl, le_rfl⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, le_rfl, le_rfl⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), le_rfl, le_rfl⟩
      have hk_world_sub : ∀ iv ∈ kSub, 0 < iv.2 →
          iv.1 + iv.2 ≤ sourceBase ∨
          (∃ j ∈ nodedbRegions s, j.1 ≤ iv.1 ∧ iv.1 + iv.2 ≤ j.1 + j.2) ∨
          (∃ gs ∈ ([] : List (String × Nat)),
            (bufferRegion s gs).1 ≤ iv.1 ∧ iv.1 + iv.2 ≤ (bufferRegion s gs).1 + (bufferRegion s gs).2) ∨
          (globN s "frame_mem_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ globN s "scratch_ptr") ∨
          (globN s "heap_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ heapLimit) := by
        intro iv hiv _
        simp only [kSub, List.mem_cons, List.not_mem_nil, or_false] at hiv
        rcases hiv with rfl | rfl | rfl
        · exact Or.inr (Or.inl ⟨bufferRegion s ("keccak_st", 200),
            by simp [nodedbRegions, bufferRegion], le_rfl, le_rfl⟩)
        · exact Or.inr (Or.inl ⟨bufferRegion s ("keccak_pad", 136),
            by simp [nodedbRegions, bufferRegion], le_rfl, le_rfl⟩)
        · by_cases hm0 : mw.toNat = 0
          · left; rw [hm0, sourceBase_val]; decide
          · right; left
            refine ⟨(globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
              by simp [nodedbRegions], ?_, ?_⟩
            · rw [hmw_glob_s]
            · rw [hmw_glob_s, if_neg hm0]; omega
      have hstep_set : ∀ (mk : PanSemStateFiniteExact 64 F),
          evaluateHOLFiniteState ud callKeccak = (none, mk) →
          WorldEff s mk (nodedbRegions s) [] hpGw →
          (evaluateHOLFiniteState mk (.seq callSet incI)).1 ≠ some .timeOut →
          ContOrRes (evaluateHOLFiniteState mk (.seq callSet incI)).1 →
          WorldEff s (evaluateHOLFiniteState mk (.seq callSet incI)).2 (nodedbRegions s) [] hpGw ∧
          (((evaluateHOLFiniteState mk (.seq callSet incI)).1 = none ∨
            (evaluateHOLFiniteState mk (.seq callSet incI)).1 = some .continue) →
            Inv2 (evaluateHOLFiniteState mk (.seq callSet incI)).2) := by
        intro mk hmk heff_mk hnt_si hcr_si
        have hbe_k : ByteEff ud mk kSub := by
          have hb := call0_byteEff funByteEff_keccak256 ud _ kSub heff_ud.code heff_ud.arena.1
            hk_args_sub (by rw [hmk]; simp) (by rw [hmk]; exact Or.inl rfl)
          rwa [hmk] at hb
        have hmk_loc : mk.locals = ud.locals := by
          have := call0_none_locals ud (ofString "keccak256") _ (by rw [hmk])
          rwa [hmk] at this
        have hmk_hp : globN mk "heap_ptr" = globN ud "heap_ptr" :=
          congrFun (globN_congr hbe_k.globals) "heap_ptr"
        have hkSub_disj : ∀ iv ∈ kSub,
            iv.1 + iv.2 ≤ sourceBase ∨
            ∃ gn ∈ ([("keccak_st", 200), ("keccak_pad", 136), ("mpt_hash_scratch", 40)] : List (String × Nat)),
              Inside iv (bufferRegion s gn).1 ((bufferRegion s gn).1 + (bufferRegion s gn).2) := by
          intro iv hiv
          simp only [kSub, List.mem_cons, List.not_mem_nil, or_false] at hiv
          rcases hiv with rfl | rfl | rfl
          · exact Or.inr ⟨("keccak_st", 200), by simp, le_rfl, le_rfl⟩
          · exact Or.inr ⟨("keccak_pad", 136), by simp, le_rfl, le_rfl⟩
          · by_cases hm0 : mw.toNat = 0
            · left; rw [hm0, sourceBase_val]; decide
            · right
              refine ⟨("mpt_hash_scratch", 40), by simp, ?_, ?_⟩
              · simp [bufferRegion, hmw_glob_s, hm0]
              · simp [bufferRegion, hmw_glob_s, hm0]
        have hu_fp_unhit : ∀ iv ∈ htabFootprint ud tw.toNat, IvlUnhit ud mk iv := by
          intro iv hiv
          have hw_iv := (hu_wf.1 iv hiv).2
          exact nodedb_keccak_unhit_fresh hAs hWT0 heff_ud heff_mk hbe_k hkSub_disj
            hw_iv.1 hw_iv.2.1 (hu_fp iv hiv).2
        have hmk_wf : HtabWF mk tw.toNat :=
          htabWF_congr_unhit heff_ud.arena.1 heff_mk.arena.1 hu_wf hu_fp_unhit
        have ht_fp_ud : (tw.toNat, 88) ∈ htabFootprint ud tw.toNat := by simp [htabFootprint]
        have hhdr_mk : (∀ k, k < 11 → hdr mk tw.toNat k = hdr ud tw.toNat k) ∧
            htabFootprint mk tw.toNat = htabFootprint ud tw.toNat := by
          have hw_t := (hu_wf.1 _ ht_fp_ud).2
          have hhi_t : tw.toNat + 88 ≤ 2 ^ 64 := by
            have hh1 : tw.toNat + 88 ≤ heapEnd := (hu_wf.1 _ ht_fp_ud).1.2
            have h264 : heapEnd ≤ 2 ^ 64 := by decide
            omega
          exact htabFootprint_eq_of_hdr_unhit hw_t.1 hhi_t (hu_fp_unhit _ ht_fp_ud)
        have hmk_h0 : hdr mk tw.toNat 0 = 32 := (hhdr_mk.1 0 (by omega)).trans hu_h0
        have hmk_fp : ∀ iv ∈ htabFootprint mk tw.toNat,
            Allocated mk iv ∧ Inside iv (globN s "heap_ptr") (globN mk "heap_ptr") := by
          rw [hhdr_mk.2, hmk_hp]
          intro iv hiv
          obtain ⟨_, hin_iv⟩ := hu_fp iv hiv
          exact ⟨Or.inl ⟨le_trans hAs.2.1 hin_iv.1, by rw [hmk_hp]; exact hin_iv.2⟩, hin_iv⟩
        have hs_call_step := fun (hnt_s : (evaluateHOLFiniteState mk callSet).1 ≠ some .timeOut)
            (hcr_s : ContOrRes (evaluateHOLFiniteState mk callSet).1) =>
          worldEff_call0_eff_post heff_mk (ofString "htab_set")
            [.var .local (ofString "t"),
             .var .global (ofString "mpt_hash_scratch"),
             .op .add [.var .local (ofString "slice_arr"),
                .panop .mul [.var .local (ofString "i"), .const 16#64]]]
            [(ofString "t", .one), (ofString "key", .one), (ofString "value", .one)]
            (sourceFnBody Guest.Software.guestFn_htab_set) .one
            SoloHtabSet.lookup_htab_set
            (P := (evaluateHOLFiniteState mk callSet).1 = none →
              HtabWF (evaluateHOLFiniteState mk callSet).2 tw.toNat ∧
              hdr (evaluateHOLFiniteState mk callSet).2 tw.toNat 0 = 32 ∧
              (∀ iv ∈ htabFootprint (evaluateHOLFiniteState mk callSet).2 tw.toNat,
                Allocated (evaluateHOLFiniteState mk callSet).2 iv ∧
                Inside iv (globN s "heap_ptr") (globN (evaluateHOLFiniteState mk callSet).2 "heap_ptr")))
            (fun callee vals hargs_s hl_hs _ hres_hs => by
              have hi16_lt : iw.toNat * (16#64 : BitVec 64).toNat < 2 ^ 64 := by
                rw [show (16#64 : BitVec 64).toNat = 16 from rfl]; omega
              have hmk_t : mk.locals.lookup (ofString "t") = some (.val (.word tw)) := by
                rw [hmk_loc]; exact hud_t
              have hmk_sa : mk.locals.lookup (ofString "slice_arr") = some (.val (.word saw)) := by
                rw [hmk_loc]; exact hud_sa
              have hmk_i : mk.locals.lookup (ofString "i") = some (.val (.word iw)) := by
                rw [hmk_loc]; exact hud_i
              have hmk_mw : mk.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word mw)) := by
                rw [hbe_k.globals]; exact hmw_lk
              have hargs_s_eq : evalListHOLFinite mk (h := fun a => Classical.propDecidable (mk.memaddrs a))
                  [.var .local (ofString "t"),
                   .var .global (ofString "mpt_hash_scratch"),
                   .op .add [.var .local (ofString "slice_arr"),
                      .panop .mul [.var .local (ofString "i"), .const 16#64]]] =
                  some [.val (.word tw), .val (.word mw), .val (.word (saw + iw * 16#64))] := by
                simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact,
                  hmk_t, hmk_mw, hmk_sa, hmk_i, valueIsWord, valueWord, panOpHOL, hi16_lt, wordOpHOL, wordOp]
              rw [hargs_s_eq] at hargs_s; injection hargs_s with hargs_s'; subst hargs_s'
              have hl_hs_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "htab_set")
                  [.val (.word tw), .val (.word mw), .val (.word (saw + iw * 16#64))] =
                  some (sourceFnBody Guest.Software.guestFn_htab_set, callee, .one) := by
                rwa [← heff_mk.code]
              obtain ⟨wt, wk, wv, hw_eq, ht_cal, hk_cal, hv_cal⟩ :=
                lookupCode_three_words (by decide) (by decide) (by decide)
                  SoloHtabSet.lookup_htab_set hl_hs_orig
              have hwt_eq : wt = tw := by
                simp only [List.cons.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hw_eq
                exact hw_eq.1.symm
              subst wt
              set ent := callEntryStateHOLFinite mk callee
              have heff_ent : WorldEff s ent (nodedbRegions s) [] hpGw :=
                heff_mk.locals_clock callee (mk.clock - 1)
              have hent_wf : HtabWF ent tw.toNat :=
                (htabWF_with_locals mk callee (mk.clock - 1) tw.toNat).2 hmk_wf
              rcases hres_hs with ⟨rv_s, hret_s⟩ | ⟨exId, exVal, hex_s, hne_s⟩
              · have hexit := SoloHtabSet.htab_set_body_spec ent tw wk wv ht_cal hk_cal hv_cal
                  heff_ent.arena hent_wf (fun iv hiv => (hmk_fp iv hiv).1) rv_s hret_s
                obtain ⟨hwe_s, hfp_s⟩ :=
                  worldEff_of_htabExitAt heff_ent hexit (fun iv hiv => (hmk_fp iv hiv).2) hs8
                refine ⟨hwe_s, fun _ hnone_s => ?_⟩
                have hc_eval : (evaluateHOLFiniteState mk callSet).2 =
                    { (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_htab_set)).2
                      with locals := mk.locals } := by
                  dsimp only [callSet] at hnone_s ⊢
                  rw [evaluateHOLFiniteState_call, hargs_s_eq] at hnone_s ⊢
                  dsimp only at hnone_s ⊢
                  rw [hl_hs] at hnone_s ⊢
                  dsimp only at hnone_s ⊢
                  have hcz : mk.clock ≠ 0 := by intro hz; simp [hz] at hnone_s
                  rw [if_neg hcz] at hnone_s ⊢
                  rcases hrun_s : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_htab_set) with ⟨rs_out, s_out⟩
                  change evaluateHOLFiniteState ent _ = _ at hrun_s
                  rw [hrun_s] at hret_s hnone_s; dsimp only at hret_s
                  subst rs_out
                  dsimp only at hnone_s ⊢
                  split at hnone_s
                  · rename_i hsh_ok
                    rw [if_pos hsh_ok]
                  · simp at hnone_s
                rw [hc_eval]
                set s_out := (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_htab_set)).2
                refine ⟨(htabWF_with_locals s_out mk.locals s_out.clock tw.toNat).2 hexit.2.1,
                  hexit.2.2.1.trans hmk_h0, fun iv hiv => ?_⟩
                exact hfp_s iv hiv
              · exfalso
                exact htab_set_no_catchable_exn ent heff_ent.code exId exVal hne_s hex_s)
            hnt_s hcr_s
        have hwe_si : WorldEff s (evaluateHOLFiniteState mk (.seq callSet incI)).2 (nodedbRegions s) [] hpGw :=
          worldEff_seq hnt_si hcr_si
            (fun hn hc => (hs_call_step hn hc).1)
            (fun ms _ heff_ms _ _ => worldEff_assign_local heff_ms _ _)
        refine ⟨hwe_si, fun hfl_si => ?_⟩
        have hnc_cs := call0_ne_continue mk (ofString "htab_set")
          [.var .local (ofString "t"),
           .var .global (ofString "mpt_hash_scratch"),
           .op .add [.var .local (ofString "slice_arr"),
              .panop .mul [.var .local (ofString "i"), .const 16#64]]]
        rw [evaluateHOLFiniteState_seq_line780] at hfl_si ⊢
        rcases hcs : evaluateHOLFiniteState mk callSet with ⟨rcs, ms⟩
        rw [hcs] at hfl_si hnc_cs
        cases rcs with
        | some r =>
          rcases hfl_si with h | h
          · simp at h
          · exact absurd h hnc_cs
        | none =>
          dsimp only at hfl_si ⊢
          have hpost_cs := (hs_call_step (by rw [hcs]; simp) (by rw [hcs]; exact Or.inl rfl)).2 (by rw [hcs])
          obtain ⟨hms_loc, hpost_cs_fn⟩ := hpost_cs
          have hpost_cs_val := hpost_cs_fn (by rw [hcs])
          rw [hcs] at hms_loc hpost_cs_val
          obtain ⟨hms_wf, hms_h0, hms_fp⟩ := hpost_cs_val
          have hms_i : ms.locals.lookup (ofString "i") = some (.val (.word iw)) := by
            rw [hms_loc, hmk_loc]; exact hud_i
          have hms_sa : ms.locals.lookup (ofString "slice_arr") = some (.val (.word saw)) := by
            rw [hms_loc, hmk_loc]; exact hud_sa
          have hms_n : ms.locals.lookup (ofString "n") = some (.val (.word nw)) := by
            rw [hms_loc, hmk_loc]; exact hud_n
          have hms_t : ms.locals.lookup (ofString "t") = some (.val (.word tw)) := by
            rw [hms_loc, hmk_loc]; exact hud_t
          dsimp only [incI]
          rw [evaluateHOLFiniteState_assign]
          have hi1_ev : @evalHOLExact 64 F _ ms.toExact (fun a => Classical.propDecidable (ms.memaddrs a))
              (.op .add [.var .local (ofString "i"), .const 1#64]) = some (.val (.word (iw + 1#64))) := by
            simp [evalHOLExact, evalListHOLExact, toExact, hms_i, valueIsWord, valueWord, wordOpHOL, wordOp]
          have hvv : isValidValueHOLFinite ms .local (ofString "i") (.val (.word (iw + 1#64))) = true := by
            simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, toExact, hms_i,
              shapeOfHOLExact, shapeEqHOL]
          simp only [hi1_ev, hvv, ↓reduceIte]
          set ms' := setKvarHOLFinite .local (ofString "i") (.val (.word (iw + 1#64))) ms
          refine ⟨?_, ?_, ?_, ⟨iw + 1#64, ?_⟩,
            (htabWF_with_locals ms ms'.locals ms.clock tw.toNat).2 hms_wf,
            hms_h0, hms_fp⟩
          · simp [ms', setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              hms_sa, show ofString "i" ≠ ofString "slice_arr" by decide]
          · simp [ms', setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              hms_n, show ofString "i" ≠ ofString "n" by decide]
          · simp [ms', setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              hms_t, show ofString "i" ≠ ofString "t" by decide]
          · simp [ms', setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hwe_b2 : WorldEff s (evaluateHOLFiniteState ud body2).2 (nodedbRegions s) [] hpGw :=
        worldEff_seq hnt_b2 hcr_b2
          (fun hn_k hcr_k =>
            worldEff_of_byteEff_or_low heff_ud
              (call0_byteEff funByteEff_keccak256 ud _ kSub heff_ud.code heff_ud.arena.1
                hk_args_sub hn_k (call0_or_resumes ud _ _ hcr_k))
              hk_world_sub)
          (fun mk hmk heff_mk hn_si hcr_si => (hstep_set mk hmk heff_mk hn_si hcr_si).1)
      refine ⟨hwe_b2, fun hfl_b2 => ?_⟩
      have hnc_k := call0_ne_continue ud (ofString "keccak256")
        [.load .one (.op .add [.var .local (ofString "slice_arr"),
            .panop .mul [.var .local (ofString "i"), .const 16#64]]),
         .load .one (.op .add [.var .local (ofString "slice_arr"),
            .panop .mul [.var .local (ofString "i"), .const 16#64], .const 8#64]),
         .var .global (ofString "mpt_hash_scratch")]
      dsimp only [body2] at hfl_b2 hnt_b2 hcr_b2 ⊢
      rw [evaluateHOLFiniteState_seq_line780] at hfl_b2 hnt_b2 hcr_b2 ⊢
      rcases hk : evaluateHOLFiniteState ud callKeccak with ⟨rk, mk⟩
      rw [hk] at hfl_b2 hnc_k hnt_b2 hcr_b2
      cases rk with
      | some r =>
        rcases hfl_b2 with h | h
        · simp at h
        · exact absurd h hnc_k
      | none =>
        have heff_mk : WorldEff s mk (nodedbRegions s) [] hpGw := by
          have := worldEff_of_byteEff_or_low heff_ud
            (call0_byteEff funByteEff_keccak256 ud _ kSub heff_ud.code heff_ud.arena.1
              hk_args_sub (by rw [hk]; simp) (by rw [hk]; exact Or.inl rfl))
            hk_world_sub
          rwa [hk] at this
        exact (hstep_set mk hk heff_mk hnt_b2 hcr_b2).2 hfl_b2)
  have hs2_inv : Inv2 s2 :=
    ⟨hs2_sa, hs2_n, hs2_t, ⟨0#64, by simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩,
     hs2_wf, hhdr0_cpost, fun iv hiv =>
       ⟨(hfp_cpost iv hiv).1, (hfp_cpost iv hiv).2⟩⟩
  refine worldEff_seq_post nodeDbPost_nonret
    (while_noret s2 cond2 body2 hbody2_noret)
    hnt4 hcr4
    (fun hnt_w2 hcr_w2 => (hw2_step s2.clock s2 rfl heff_s2 hs2_inv hnt_w2 hcr_w2).1)
    (fun m2 hm2 heff_m2 _ _ => ?_)
  have hw2_inv : Inv2 m2 := by
    change evaluateHOLFiniteState s2 (.while cond2 body2) = (none, m2) at hm2
    have hnone2 : (evaluateHOLFiniteState s2 (.while cond2 body2)).1 = none := by rw [hm2]
    have hpost2 := (hw2_step s2.clock s2 rfl heff_s2 hs2_inv
      (by rw [hm2]; simp) (by rw [hm2]; exact Or.inl rfl)).2 hnone2 (fun u _ => hbody2_nobreak u)
    rw [hm2] at hpost2
    exact hpost2.1
  obtain ⟨_, _, hm2_t, _, hm2_wf, hm2_h0, hm2_fp⟩ := hw2_inv
  refine ⟨worldEff_return heff_m2 _, ?_⟩
  rw [evaluateHOLFiniteState_return]
  have ht_ev : @evalHOLExact 64 F _ m2.toExact (fun a => Classical.propDecidable (m2.memaddrs a))
      (.var .local (ofString "t")) = some (.val (.word tw)) := by
    simp [evalHOLExact, toExact, hm2_t]
  simp only [ht_ev, shapeOfHOLExact]
  split
  · intro rv hret
    injection hret with hret'; injection hret' with hret''; subst hret''
    exact ⟨tw, rfl,
      (htabWF_with_locals m2 (emptyLocalsHOLFinite m2).locals m2.clock tw.toNat).2 hm2_wf,
      hm2_h0, fun iv hiv => (hm2_fp iv hiv).2⟩
  · intro rv hret; simp at hret

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
