import InitECandidate.Solver.Wave8GuestInv.ContractParts.C12

/-! Helpers and guarded-body compositions for `idx_start_storage` and `update_builder_from_tx`
on `wave8/spec-r10`. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

/-! ## 1. AST Lookups -/

theorem lookup_st_le64_fn :
    originalRuntimeCode.lookup (ofString "st_le64") =
      some ((sourceFunctionEntry Guest.Software.guestFn_st_le64).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 26 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_st_le64) rfl

theorem lookup_memcpy_fn :
    originalRuntimeCode.lookup (ofString "memcpy") =
      some ((sourceFunctionEntry Guest.Software.guestFn_memcpy).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memcpy) rfl

theorem «lookup_idx_start_storage» :
    originalRuntimeCode.lookup (ofString "idx_start_storage") =
      some ((sourceFunctionEntry Guest.Software.guestFn_idx_start_storage).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 423 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_idx_start_storage) rfl

theorem lookup_bal_remove_change_fn :
    originalRuntimeCode.lookup (ofString "bal_remove_change") =
      some ((sourceFunctionEntry Guest.Software.guestFn_bal_remove_change).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 425 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_bal_remove_change) rfl

theorem «lookup_update_builder_from_tx» :
    originalRuntimeCode.lookup (ofString "update_builder_from_tx") =
      some ((sourceFunctionEntry Guest.Software.guestFn_update_builder_from_tx).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 427 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_update_builder_from_tx) rfl

namespace R10GbodyIdxBuilder

/-! ## 2. Parameter Lookup Helpers -/

theorem callee_param_two {F : Type} (state : PanSemStateFiniteExact 64 F) (fname p1 p2 : MlS)
    (s1 s2 : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname = some ([(p1, s1), (p2, s2)], body, ret))
    (e1 e2 : ExpHOL 64) (v1 v2 : ValueHOL 64)
    (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (he1 : evalAt state e1 = some v1) (he2 : evalAt state e2 = some v2)
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [e1, e2] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    p1 ≠ p2 ∧ callee.lookup p1 = some v1 ∧ callee.lookup p2 = some v2 := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact, he1, he2, Option.some.injEq] at hargs
  subst hargs
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hlook
  split at hlook
  · cases hlook
  · rename_i exactBody exactLocals exactShape raw
    have heq := Option.some.inj hlook
    rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨rfl, _⟩
    unfold lookupCodeHOLExact at raw
    rw [hl] at raw
    dsimp only at raw
    split at raw
    · rename_i hcond
      have rawEq := Option.some.inj raw
      rcases Prod.mk.inj rawEq with ⟨-, hrest2⟩
      rcases Prod.mk.inj hrest2 with ⟨hloc, -⟩
      subst hloc
      obtain ⟨hnd, -, -⟩ := hcond
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false] at hnd
      refine ⟨hnd.1, ?_, ?_⟩
      · simp [List.zip, List.foldl, hnd.1]
      · simp [List.zip, List.foldl]
    · cases raw

theorem callee_param_three {F : Type} (state : PanSemStateFiniteExact 64 F) (fname p1 p2 p3 : MlS)
    (s1 s2 s3 : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname = some ([(p1, s1), (p2, s2), (p3, s3)], body, ret))
    (e1 e2 e3 : ExpHOL 64) (v1 v2 v3 : ValueHOL 64)
    (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (he1 : evalAt state e1 = some v1) (he2 : evalAt state e2 = some v2)
    (he3 : evalAt state e3 = some v3)
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [e1, e2, e3] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    callee.lookup p1 = some v1 ∧ callee.lookup p2 = some v2 ∧ callee.lookup p3 = some v3 := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact, he1, he2, he3, Option.some.injEq] at hargs
  subst hargs
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hlook
  split at hlook
  · cases hlook
  · rename_i exactBody exactLocals exactShape raw
    have heq := Option.some.inj hlook
    rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨rfl, _⟩
    unfold lookupCodeHOLExact at raw
    rw [hl] at raw
    dsimp only at raw
    split at raw
    · rename_i hcond
      have rawEq := Option.some.inj raw
      rcases Prod.mk.inj rawEq with ⟨-, hrest2⟩
      rcases Prod.mk.inj hrest2 with ⟨hloc, -⟩
      subst hloc
      obtain ⟨hnd, -, -⟩ := hcond
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
        not_or, List.not_mem_nil, or_false] at hnd
      refine ⟨?_, ?_, ?_⟩
      · simp [List.zip, List.foldl, hnd.1.1, hnd.1.2]
      · simp [List.zip, List.foldl, hnd.2.1]
      · simp [List.zip, List.foldl]
    · cases raw

theorem callee_param_four_exp {F : Type} (state : PanSemStateFiniteExact 64 F)
    (fname p1 p2 p3 p4 : MlS) (s1 s2 s3 s4 : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname = some ([(p1, s1), (p2, s2), (p3, s3), (p4, s4)], body, ret))
    (e1 e2 e3 e4 : ExpHOL 64) (v1 v2 v3 v4 : ValueHOL 64)
    (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (he1 : evalAt state e1 = some v1) (he2 : evalAt state e2 = some v2)
    (he3 : evalAt state e3 = some v3) (he4 : evalAt state e4 = some v4)
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [e1, e2, e3, e4] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    callee.lookup p1 = some v1 ∧ callee.lookup p2 = some v2 ∧
      callee.lookup p3 = some v3 ∧ callee.lookup p4 = some v4 := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact, he1, he2, he3, he4, Option.some.injEq] at hargs
  subst hargs
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hlook
  split at hlook
  · cases hlook
  · rename_i exactBody exactLocals exactShape raw
    have heq := Option.some.inj hlook
    rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨rfl, _⟩
    unfold lookupCodeHOLExact at raw
    rw [hl] at raw
    dsimp only at raw
    split at raw
    · rename_i hcond
      have rawEq := Option.some.inj raw
      rcases Prod.mk.inj rawEq with ⟨-, hrest2⟩
      rcases Prod.mk.inj hrest2 with ⟨hloc, -⟩
      subst hloc
      obtain ⟨hnd, -, -⟩ := hcond
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
        not_or, List.not_mem_nil, or_false] at hnd
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [List.zip, List.foldl, hnd.1.1, hnd.1.2.1, hnd.1.2.2]
      · simp [List.zip, List.foldl, hnd.2.1.1, hnd.2.1.2]
      · simp [List.zip, List.foldl, hnd.2.2.1]
      · simp [List.zip, List.foldl]
    · cases raw

/-! ## 3. Domain and Sub-interval Disjointness for `bal_key_buf` -/

theorem addresses_iff (b : BitVec 64) (n : Nat) (x : BitVec 64) :
    Flapjack.Compiler.Backend.StackRemove.addresses b n x ↔
      ∃ i, i < n ∧ x = b + BitVec.ofNat 64 (8 * i) := by
  induction n generalizing b with
  | zero => simp [Flapjack.Compiler.Backend.StackRemove.addresses]
  | succ n ih =>
    simp only [Flapjack.Compiler.Backend.StackRemove.addresses,
      Flapjack.Compiler.Backend.StackRemove.bytesInWord]
    rw [ih]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨0, by omega, by simp⟩
      · refine ⟨i + 1, by omega, ?_⟩
        rw [BitVec.add_assoc]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add]
        omega
    · rintro ⟨i, hi, rfl⟩
      rcases i with _ | i
      · left; simp
      · right
        refine ⟨i, by omega, ?_⟩
        rw [BitVec.add_assoc]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add]
        omega

theorem byteAlign_in_ordinaryDomain {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hma : s.memaddrs = ordinaryDomain) {addr : BitVec 64}
    (hdom : s.memaddrs (panByteAlignHOL addr)) :
    sourceBase ≤ addr.toNat ∧ addr.toNat < heapEnd := by
  rw [hma] at hdom
  unfold ordinaryDomain at hdom
  rw [addresses_iff] at hdom
  obtain ⟨i, hi, heq⟩ := hdom
  have hal : (panByteAlignHOL addr).toNat = addr.toNat / 8 * 8 :=
    InitECandidate.Solver.GuestTrapAndLookup.panByteAlign_toNat64 addr
  have hbase : (BitVec.ofNat 64 sourceBase).toNat = 2701131776 := by decide
  have hi_bound : i < 3888119741 := by
    have : (stackStart - sourceBase) / 8 - globalsWords = 3888119741 := by decide
    omega
  have hadd : (BitVec.ofNat 64 sourceBase + BitVec.ofNat 64 (8 * i)).toNat =
      2701131776 + 8 * i := by
    rw [BitVec.toNat_add, hbase, BitVec.toNat_ofNat]
    have : (8 * i) % 2 ^ 64 = 8 * i := Nat.mod_eq_of_lt (by omega)
    rw [this]
    exact Nat.mod_eq_of_lt (by omega)
  have heq_nat : (panByteAlignHOL addr).toNat = 2701131776 + 8 * i := by
    rw [heq, hadd]
  have hsb : sourceBase = 2701131776 := rfl
  have hhe : heapEnd = 33806089704 := by decide
  omega

theorem storeByte_first_in_domain {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hma : s.memaddrs = ordinaryDomain) (dst val : ExpHOL 64) (addr : BitVec 64)
    (hdst : evalAt s dst = some (.val (.word addr)))
    (hnone : (evaluateHOLFiniteState s (.storeByte dst val)).1 = none) :
    sourceBase ≤ addr.toNat ∧ addr.toNat < heapEnd := by
  rw [evaluateHOLFiniteState_storeByte] at hnone
  unfold evalAt at hdst
  rw [hdst] at hnone
  dsimp only at hnone
  split at hnone
  · rename_i w _
    rcases hst : @panMemStoreByteWord8HOL 64 _ s.memory s.memaddrs
        (fun a => Classical.propDecidable (s.memaddrs a)) s.be addr (BitVec.ofNat 8 w.toNat) with _ | m'
    · rw [hst] at hnone; simp at hnone
    · unfold panMemStoreByteWord8HOL at hst
      dsimp only at hst
      split_ifs at hst with hdom
      exact byteAlign_in_ordinaryDomain hma hdom
  · simp at hnone

theorem st_le64_resumes_nonzero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hr : Resumes (evaluateHOLFiniteState s
      (sourceFunctionEntry Guest.Software.guestFn_st_le64).2.2.1).1) :
    locN s "p" ≠ 0 := by
  have hbody : (sourceFunctionEntry Guest.Software.guestFn_st_le64).2.2.1 =
      .seq (.call (some (none, none)) (ofString "st_le32")
          [.var .local (ofString "p"), .var .local (ofString "v")])
        (.seq (.call (some (none, none)) (ofString "st_le32")
            [.op .add [.var .local (ofString "p"), .const 4],
              .shift .lsr (.var .local (ofString "v")) (.const 32)])
          (.return (.const 0))) := rfl
  rw [hbody, evaluateHOLFiniteState_seq_line780] at hr
  rcases h1 : evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "st_le32")
        [.var .local (ofString "p"), .var .local (ofString "v")]) with ⟨r1, m1⟩
  rw [h1] at hr
  have hnotErr : ¬ Resumes (some (.error : PanSemResultExact 64)) := by
    rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h
  have hnotTo : ¬ Resumes (some (.timeOut : PanSemResultExact 64)) := by
    rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h
  rw [evaluateHOLFiniteState_call] at h1
  rcases hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "p"), .var .local (ofString "v")] with _ | values
  · rw [hargs] at h1; obtain ⟨rfl, _⟩ := h1; exact absurd hr hnotErr
  · rw [hargs] at h1; dsimp only at h1
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "st_le32") values with
      _ | ⟨b32, c32, ret32⟩
    · rw [hl] at h1; obtain ⟨rfl, _⟩ := h1; exact absurd hr hnotErr
    · rw [hl] at h1; dsimp only at h1
      have hlook32 : originalRuntimeCode.lookup (ofString "st_le32") =
          some ((sourceFunctionEntry Guest.Software.guestFn_st_le32).2) :=
        originalRuntimeCode_lookup_of_guestAst_getElem 25 (by rw [guestAst_len]; decide)
          (extractFn Guest.Software.guestFn_st_le32) rfl
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "st_le32")
        _ _ b32 _ ret32 values c32 (by rw [hcode]; exact hlook32) hl
      rcases hp_raw : s.locals.lookup (ofString "p") with _ | vp
      · rw [evalListHOLFinite_eq_toExact] at hargs
        simp [evalListHOLExact, evalHOLExact, hp_raw] at hargs
      · rcases hv_raw : s.locals.lookup (ofString "v") with _ | vv
        · rw [evalListHOLFinite_eq_toExact] at hargs
          simp [evalListHOLExact, evalHOLExact, hp_raw, hv_raw] at hargs
        · have hc32 := callee_param_two s (ofString "st_le32") (ofString "p") (ofString "v")
            .one .one _ .one (by rw [hcode]; exact hlook32)
            (.var .local (ofString "p")) (.var .local (ofString "v")) vp vv
            values b32 c32 ret32
            (by simp [evalAt, evalHOLExact, hp_raw])
            (by simp [evalAt, evalHOLExact, hv_raw]) hargs hl
          by_cases hz : s.clock = 0
          · rw [if_pos hz] at h1; obtain ⟨rfl, _⟩ := h1; exact absurd hr hnotTo
          · rw [if_neg hz] at h1
            have hb32 : b32 =
                .seq (.storeByte (.var .local (ofString "p")) (.var .local (ofString "v")))
                  (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 1])
                      (.shift .lsr (.var .local (ofString "v")) (.const 8)))
                    (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 2])
                        (.shift .lsr (.var .local (ofString "v")) (.const 16)))
                      (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 3])
                          (.shift .lsr (.var .local (ofString "v")) (.const 24)))
                        (.return (.const 0))))) := hsame
            let entry := callEntryStateHOLFinite s c32
            have hentry_ma : entry.memaddrs = ordinaryDomain := hG.memaddrs
            rcases hsb : evaluateHOLFiniteState entry
                (.storeByte (.var .local (ofString "p")) (.var .local (ofString "v"))) with
              ⟨rsb, msb⟩
            have hsb_cases : rsb = none ∨ rsb = some .error := by
              have hfst : (evaluateHOLFiniteState entry
                  (.storeByte (.var .local (ofString "p")) (.var .local (ofString "v")))).1 = rsb :=
                congrArg Prod.fst hsb
              rw [← hfst, evaluateHOLFiniteState_storeByte]
              split
              · split
                · split
                  · exact Or.inl rfl
                  · exact Or.inr rfl
                · exact Or.inr rfl
              · exact Or.inr rfl
            rcases hsb_cases with rfl | rfl
            · have hvp_word : ∃ pw : BitVec 64, vp = .val (.word pw) := by
                have hsb' := congrArg Prod.fst hsb
                rw [evaluateHOLFiniteState_storeByte] at hsb'
                have hep : @evalHOLExact 64 F _ entry.toExact
                    (fun a => Classical.propDecidable (entry.memaddrs a))
                    (.var .local (ofString "p")) = some vp := by
                  simpa [evalHOLExact, entry, callEntryStateHOLFinite] using hc32.2.1
                rw [hep] at hsb'
                rcases vp with wlab | _ | _
                · cases wlab with | word pw => exact ⟨pw, rfl⟩
                · simp at hsb'
                · simp at hsb'
              obtain ⟨pw, rfl⟩ := hvp_word
              have hdom := storeByte_first_in_domain hentry_ma
                (.var .local (ofString "p")) (.var .local (ofString "v")) pw
                (by simpa [evalAt, evalHOLExact, entry, callEntryStateHOLFinite] using hc32.2.1)
                (congrArg Prod.fst hsb)
              have hloc : locN s "p" = pw.toNat := by simp [locN, hp_raw]
              have hsb_pos : 0 < sourceBase := by decide
              omega
            · have hrun32 : evaluateHOLFiniteState entry b32 = (some .error, msb) := by
                rw [hb32, evaluateHOLFiniteState_seq_line780, hsb]
              rw [hrun32] at h1
              obtain ⟨rfl, _⟩ := h1
              exact absurd hr hnotErr

theorem disj_sub_bufferRegion {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    (gn : String × Nat) (hg : gn ∈ globalBuffers) (hu : gn.1 ∉ typedRecords.map Prod.fst)
    (hnz : globN s gn.1 ≠ 0) {off len : Nat} (hle : off + len ≤ gn.2)
    {p : Nat} (hp : p = globN s gn.1 + off) :
    IvlsDisj [(p, len)] (worldTypedIvls s S Nd) := by
  intro o ho j hj
  simp only [List.mem_singleton] at ho
  subst ho
  subst hp
  have hfull := bufferRegion_disj hW gn hg hu j hj
  simp only [bufferRegion, hnz, ↓reduceIte] at hfull
  unfold Disj at hfull ⊢
  dsimp only at hfull ⊢
  omega

theorem bal_key_buf_upper {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    (hnz : globN s "bal_key_buf" ≠ 0) :
    globN s "bal_key_buf" + 64 ≤ scratchEnd := by
  have hmem : (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64) ∈ fixedObjects s := by
    unfold fixedObjects
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨("bal_key_buf", 64), by decide, rfl⟩
  have hft := hW.2.2.1.1 _ hmem
  simp only [hnz, ↓reduceIte] at hft
  rcases hft with h0 | ⟨halloc, _⟩
  · omega
  · rcases halloc with hheap | hscr
    · have hhl : heapLimit ≤ scratchEnd := by decide
      have hp := hA.2.1
      have hi := hheap.2
      dsimp only at hi
      omega
    · have hi := hscr.2
      dsimp only at hi
      exact hi

/-! ## 4. Proof of `gbody_idx_start_storage` -/

def KbState {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  WorldOK s ∧ locN s "kb" = globN s "bal_key_buf"

def KbNzState {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  WorldOK s ∧ locN s "kb" = globN s "bal_key_buf" ∧ globN s "bal_key_buf" ≠ 0

theorem localsOnly_kbState : LocalsOnly ["kb"] KbState := by
  intro F s locals k hl ⟨hW, hkb⟩
  refine ⟨localsFree_worldOK s locals k hW, ?_⟩
  rw [locN_congr s locals k "kb" (hl "kb" (by simp))]
  exact hkb

theorem localsOnly_kbNzState : LocalsOnly ["kb"] KbNzState := by
  intro F s locals k hl ⟨hW, hkb, hnz⟩
  refine ⟨localsFree_worldOK s locals k hW, ?_, hnz⟩
  rw [locN_congr s locals k "kb" (hl "kb" (by simp))]
  exact hkb

theorem hoare_st_le64_kb
    (wst : WorldKeeps WorldOK (fun s => [(locN s "p", 8)]) []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "st_le64")) :
    Hoare KbState
      (.call (some (none, none)) (ofString "st_le64")
        [.var .local (ofString "kb"), .var .global (ofString "bal_index")])
      (fun r t => r = none → KbNzState t) := by
  refine ⟨fun {F} s hcode ⟨hW, hkb⟩ hnt hr => ?_⟩
  rw [evaluateHOLFiniteState_call] at hnt hr ⊢
  rcases hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "kb"), .var .global (ofString "bal_index")] with _ | values
  · rw [hargs] at hr; simp at hr
  · simp only [hargs] at hnt hr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "st_le64") values with
      _ | ⟨body', callee, ret'⟩
    · rw [hl] at hr; simp at hr
    · simp only [hl] at hnt hr ⊢
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hr; simp at hr
      · simp only [hz, ↓reduceIte] at hnt hr ⊢
        rcases hkb_raw : s.locals.lookup (ofString "kb") with _ | vkb
        · rw [evalListHOLFinite_eq_toExact] at hargs
          simp [evalListHOLExact, evalHOLExact, hkb_raw] at hargs
        · rcases hbi_raw : s.globals.lookup (ofString "bal_index") with _ | vbi
          · rw [evalListHOLFinite_eq_toExact] at hargs
            simp [evalListHOLExact, evalHOLExact, hkb_raw, hbi_raw] at hargs
          · have hc := callee_param_two s (ofString "st_le64") (ofString "p") (ofString "v")
              .one .one _ .one (by rw [hcode]; exact lookup_st_le64_fn)
              (.var .local (ofString "kb")) (.var .global (ofString "bal_index")) vkb vbi
              values body' callee ret'
              (by simp [evalAt, evalHOLExact, hkb_raw])
              (by simp [evalAt, evalHOLExact, hbi_raw]) hargs hl
            have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "st_le64")
              _ _ body' _ ret' values callee (by rw [hcode]; exact lookup_st_le64_fn) hl
            have hp_eq : locN (callEntryStateHOLFinite s callee) "p" = locN s "kb" := by
              simp [locN, callEntryStateHOLFinite, hc.2.1, hkb_raw]
            have hentryW : WorldOK (callEntryStateHOLFinite s callee) :=
              localsFree_worldOK s callee (s.clock - 1) hW
            rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with
              ⟨res, post⟩
            have hQc (hsafe : res ≠ some .timeOut) :
                Resumes res → WorldStep (fun s => [(locN s "p", 8)]) []
                  [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
                   ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
                   ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
                  NoExtra (callEntryStateHOLFinite s callee) res post := by
              have := FunSpec.at_lookup wst s hcode values body' callee ret' hl hentryW
                (by rw [hrun]; exact hsafe)
              rw [hrun] at this
              exact this
            simp only [hrun] at hnt hr ⊢
            cases res with
            | none => simp at hr
            | some r =>
              cases r with
              | returned val =>
                dsimp only at hr ⊢
                split at hr <;> rename_i hsh
                · simp only [hsh, ↓reduceIte]
                  have hres_ok : Resumes (some (.returned val)) := Or.inl ⟨val, rfl⟩
                  have hrun_installed : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
                      (sourceFunctionEntry Guest.Software.guestFn_st_le64).2.2.1 =
                      (some (.returned val), post) := by
                    have hbody_eq : body' =
                        (sourceFunctionEntry Guest.Software.guestFn_st_le64).2.2.1 := hsame
                    rw [← hbody_eq]
                    exact hrun
                  have hnz_p := st_le64_resumes_nonzero (callEntryStateHOLFinite s callee)
                    hcode (worldOK_guestInv _ hentryW) (by rw [hrun_installed]; exact hres_ok)
                  have hnz_kb : globN s "bal_key_buf" ≠ 0 := by omega
                  have hstep := hQc (by simp) hres_ok
                  obtain ⟨_, S, hS⟩ := hentryW
                  obtain ⟨Nd, hT⟩ := (worldTyped_iff_with (callEntryStateHOLFinite s callee) S).1 hS
                  have hdisj : IvlsDisj [(locN (callEntryStateHOLFinite s callee) "p", 8)]
                      (worldTypedIvls (callEntryStateHOLFinite s callee) S Nd) :=
                    disj_sub_bufferRegion hT ("bal_key_buf", 64) (by decide) (by decide)
                      hnz_kb (off := 0) (len := 8) (by decide)
                      (by rw [hp_eq, hkb]; simp [globN, callEntryStateHOLFinite])
                  have hpostW : WorldOK post := hstep.worldOK ⟨S, Nd, hT, hdisj⟩
                  have hg_keep : post.globals.lookup (ofString "bal_key_buf") =
                      s.globals.lookup (ofString "bal_key_buf") :=
                    (hstep.2.2.1 (ofString "bal_key_buf") (by simp)).symm
                  have hglob_eq : globN { post with locals := s.locals } "bal_key_buf" =
                      globN s "bal_key_buf" := by
                    simp [globN, hg_keep]
                  refine ⟨localsFree_worldOK post s.locals post.clock hpostW, ?_, ?_⟩
                  · rw [hglob_eq]
                    simpa [locN] using hkb
                  · rw [hglob_eq]
                    exact hnz_kb
                · simp at hr
              | _ => simp at hr

theorem hoare_memcpy_kb_off
    (wmc : WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")]) []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "memcpy"))
    (src : ExpHOL 64) (off len : BitVec 64) (hle : off.toNat + len.toNat ≤ 64) :
    Hoare KbNzState
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "kb"), .const off], src, .const len])
      (fun r t => r = none → KbNzState t) := by
  refine ⟨fun {F} s hcode ⟨hW, hkb, hnz⟩ hnt hr => ?_⟩
  rw [evaluateHOLFiniteState_call] at hnt hr ⊢
  rcases hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.op .add [.var .local (ofString "kb"), .const off], src, .const len] with _ | values
  · rw [hargs] at hr; simp at hr
  · simp only [hargs] at hnt hr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") values with
      _ | ⟨body', callee, ret'⟩
    · rw [hl] at hr; simp at hr
    · simp only [hl] at hnt hr ⊢
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hr; simp at hr
      · simp only [hz, ↓reduceIte] at hnt hr ⊢
        have hargs_ex := hargs
        rw [evalListHOLFinite_eq_toExact] at hargs_ex
        rcases he1 : evalAt s (.op .add [.var .local (ofString "kb"), .const off]) with _ | v1
        · simp [evalListHOLExact, evalAt] at he1 hargs_ex; rw [he1] at hargs_ex; cases hargs_ex
        · rcases he2 : evalAt s src with _ | v2
          · simp [evalListHOLExact, evalAt] at he1 he2 hargs_ex
            rw [he1, he2] at hargs_ex; cases hargs_ex
          · have hc := callee_param_three s (ofString "memcpy")
              (ofString "dst") (ofString "src") (ofString "n")
              .one .one .one _ .one (by rw [hcode]; exact lookup_memcpy_fn)
              (.op .add [.var .local (ofString "kb"), .const off]) src (.const len)
              v1 v2 (.val (.word len)) values body' callee ret'
              he1 he2 (by rfl) hargs hl
            have hentryW : WorldOK (callEntryStateHOLFinite s callee) :=
              localsFree_worldOK s callee (s.clock - 1) hW
            have hA := hW.1.2
            obtain ⟨_, S, hS⟩ := hW
            obtain ⟨Nd, hT⟩ := (worldTyped_iff_with s S).1 hS
            have hbound := bal_key_buf_upper hA hT hnz
            have hse : scratchEnd = 2965299200 := by decide
            have hd_eq : ∃ w1 : BitVec 64, v1 = .val (.word w1) ∧
                w1.toNat = globN s "bal_key_buf" + off.toNat := by
              simp only [evalAt, evalHOLExact, evalListHOLExact] at he1
              rcases hkb_l : s.locals.lookup (ofString "kb") with _ | vkb
              · simp [hkb_l] at he1
              · rcases vkb with wlab | _ | _
                · cases wlab with
                  | word wkb =>
                    simp [hkb_l, valueIsWord, valueWord, wordOpHOL, wordOp] at he1
                    refine ⟨wkb + off, he1.symm, ?_⟩
                    have hwkb : wkb.toNat = globN s "bal_key_buf" := by
                      rw [← hkb]; simp [locN, hkb_l]
                    rw [BitVec.toNat_add, hwkb]
                    exact Nat.mod_eq_of_lt (by omega)
                · simp [hkb_l, valueIsWord] at he1
                · simp [hkb_l, valueIsWord] at he1
            obtain ⟨w1, rfl, hw1⟩ := hd_eq
            have hentryT : WorldTypedWith (callEntryStateHOLFinite s callee) S Nd := by
              have hS' : WorldTyped (callEntryStateHOLFinite s callee) S :=
                (worldTyped_with_locals s callee (s.clock - 1) S).2 hS
              exact ⟨hS'.1, hS'.2.1, hS'.2.2.1, hT.2.2.2⟩
            have hdst_eq : locN (callEntryStateHOLFinite s callee) "dst" =
                globN (callEntryStateHOLFinite s callee) "bal_key_buf" + off.toNat := by
              simp [locN, callEntryStateHOLFinite, hc.1, hw1, globN]
            have hn_eq : locN (callEntryStateHOLFinite s callee) "n" = len.toNat := by
              simp [locN, callEntryStateHOLFinite, hc.2.2]
            rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with
              ⟨res, post⟩
            have hQc (hsafe : res ≠ some .timeOut) :
                Resumes res → WorldStep (fun s => [(locN s "dst", locN s "n")]) []
                  [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
                   ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
                   ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
                  NoExtra (callEntryStateHOLFinite s callee) res post := by
              have := FunSpec.at_lookup wmc s hcode values body' callee ret' hl hentryW
                (by rw [hrun]; exact hsafe)
              rw [hrun] at this
              exact this
            simp only [hrun] at hnt hr ⊢
            cases res with
            | none => simp at hr
            | some r =>
              cases r with
              | returned val =>
                dsimp only at hr ⊢
                split at hr <;> rename_i hsh
                · simp only [hsh, ↓reduceIte]
                  have hstep := hQc (by simp) (Or.inl ⟨val, rfl⟩)
                  have hdisj : IvlsDisj [(locN (callEntryStateHOLFinite s callee) "dst",
                      locN (callEntryStateHOLFinite s callee) "n")]
                      (worldTypedIvls (callEntryStateHOLFinite s callee) S Nd) := by
                    rw [hn_eq]
                    exact disj_sub_bufferRegion hentryT ("bal_key_buf", 64) (by decide) (by decide)
                      hnz hle hdst_eq
                  have hpostW : WorldOK post := hstep.worldOK ⟨S, Nd, hentryT, hdisj⟩
                  have hg_keep : post.globals.lookup (ofString "bal_key_buf") =
                      s.globals.lookup (ofString "bal_key_buf") :=
                    (hstep.2.2.1 (ofString "bal_key_buf") (by simp)).symm
                  have hglob_eq : globN { post with locals := s.locals } "bal_key_buf" =
                      globN s "bal_key_buf" := by
                    simp [globN, hg_keep]
                  refine ⟨localsFree_worldOK post s.locals post.clock hpostW, ?_, ?_⟩
                  · rw [hglob_eq]
                    simpa [locN] using hkb
                  · rw [hglob_eq]
                    exact hnz
                · simp at hr
              | _ => simp at hr

theorem dec_kb_bounded {body : ProgHOL 64} {K : Nat}
    (hbody : TerminatingProgBoundedOn KbState body K) :
    TerminatingProgBoundedOn WorldOK
      (.dec (ofString "kb") .one (.var .global (ofString "bal_key_buf")) body) K := by
  intro F state hcode hW hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  revert hnt
  split <;> intro hnt
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · rename_i val hv
    revert hnt
    split <;> intro hnt
    · rename_i hsh
      have hval_word : ∃ w : BitVec 64, val = .val (.word w) := by
        rcases val with wlab | fs | ⟨nm, fs⟩
        · cases wlab with | word w => exact ⟨w, rfl⟩
        · simp [shapeEqHOL, shapeOfHOLExact] at hsh
        · simp [shapeEqHOL, shapeOfHOLExact] at hsh
      obtain ⟨w, rfl⟩ := hval_word
      have hkb : KbState (setVarHOLFinite (ofString "kb") (.val (.word w)) state) := by
        refine ⟨localsFree_worldOK state _ state.clock hW, ?_⟩
        rw [locN_setVar_same]
        simp only [evalHOLExact] at hv
        simp [globN, setVarHOLFinite, hv]
      have hb := hbody (setVarHOLFinite (ofString "kb") (.val (.word w)) state) hcode hkb hnt
      simpa [setVarHOLFinite] using hb
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

theorem seq_hoare_trans
    {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {first second : ProgHOL 64} {a b : Nat}
    (h1 : TerminatingProgBoundedOn P first a) (hp : Hoare P first (fun r t => r = none → Q t))
    (h2 : TerminatingProgBoundedOn Q second b) :
    TerminatingProgBoundedOn P (.seq first second) (a + b) := by
  intro F state hcode hP
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata state first
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr1 : evaluateHOLFiniteState state first with ⟨r1, mid⟩
  have hmid := hp.run state hcode hP
  simp only [hr1] at hmeta hnt hmid ⊢
  cases r1 with
  | none =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simp [hr1]
    obtain ⟨s1, k1⟩ := h1 state hcode hP hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    obtain ⟨s2, k2⟩ := h2 mid (hmeta.1.trans hcode) (hmid (by simp) rfl) hnt
    exact ⟨by omega, by omega⟩
  | some r =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simpa [hr1] using hnt
    obtain ⟨s1, k1⟩ := h1 state hcode hP hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    exact ⟨by omega, k1⟩

theorem gbody_idx_start_storage_impl :
    (TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc») →
    (TerminatingFunBoundedOn WorldOK (ofString "get_pre_tx_storage") K.«get_pre_tx_storage») →
    (TerminatingFunBoundedOn GuestInv (ofString "htab_get") K.«htab_get») →
    (TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set») →
    (TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy») →
    (TerminatingFunBoundedOn GuestInv (ofString "st_le64") K.«st_le64») →
    (ReadOnlyFn (ofString "htab_get")) →
    (WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")])
      []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "memcpy")) →
    (WorldKeeps WorldOK (fun s => [(locN s "p", 8)])
      []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "st_le64")) →
    TerminatingFunBoundedOn WorldOK (ofString "idx_start_storage") K.«idx_start_storage» := by
  intro hal hgp hget hset hmc hst hrget wmc wst
  refine ⟨_, _, _, «lookup_idx_start_storage», ?_⟩
  simp only [InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (dec_kb_bounded
      (seq_hoare_trans
        (TerminatingProgBoundedOn.call_on hst _ _
          (callEntryOn_of_imp localsFree_guestInv (fun s h => worldOK_guestInv s h.1) _ _))
        (hoare_st_le64_kb wst)
        (TerminatingProgBoundedOn.seq_hoare
          (TerminatingProgBoundedOn.call_on hmc _ _
            (callEntryOn_of_imp localsFree_guestInv (fun s h => worldOK_guestInv s h.1) _ _))
          (hoare_memcpy_kb_off wmc _ 8 20 (by decide))
          (TerminatingProgBoundedOn.seq_hoare
            (TerminatingProgBoundedOn.call_on hmc _ _
              (callEntryOn_of_imp localsFree_guestInv (fun s h => worldOK_guestInv s h.1) _ _))
            (hoare_memcpy_kb_off wmc _ 28 32 (by decide))
            (TerminatingProgBoundedOn.decCall_on hget _ _ _
              (callEntryOn_of_imp localsFree_guestInv (fun s h => worldOK_guestInv s h.1) _ _)
              (ReadOnlyFn.resumeOn localsOnly_kbNzState (fun s h => worldOK_guestInv s h.1)
                hrget _ (by decide) _)
              (TerminatingProgBoundedOn.seq_hoare
                (TerminatingProgBoundedOn.ite_on
                  (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _))
                  (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
                (Hoare.ite_return_skip _ _)
                (TerminatingProgBoundedOn.decCall_on hgp _ _ _
                  (callEntryOn_of_imp localsFree_worldOK (fun s h => h.1) _ _)
                  (decCallResumeOn_guestInv (fun s h => worldOK_guestInv s h.1) _ _ _)
                  (TerminatingProgBoundedOn.decCall_guestInv hal _ _ _
                    (TerminatingProgBoundedOn.seq_guestInv
                      (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                      (TerminatingProgBoundedOn.seq_guestInv
                        (TerminatingProgBoundedOn.call_guestInv hst _ _)
                        (TerminatingProgBoundedOn.seq_guestInv
                          (TerminatingProgBoundedOn.call_guestInv hmc _ _)
                          (TerminatingProgBoundedOn.seq_guestInv
                            (TerminatingProgBoundedOn.call_guestInv hmc _ _)
                            (TerminatingProgBoundedOn.seq_guestInv
                              (TerminatingProgBoundedOn.call_guestInv hset _ _)
                              (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _))))))))))))))) ?_
  unfold K.«idx_start_storage»
  omega

/-! ## 5. Guarded Counted-Loop and WorldOK Combinators for `update_builder_from_tx` -/

inductive IncrBody (c : MlS) : ProgHOL 64 → Prop
  | incr : IncrBody c (.assign .local c (.op .add [.var .local c, .const 1]))
  | seq (first : ProgHOL 64) {tail : ProgHOL 64}
      (avoid : avoidsLocal c first = true) (noCont : noTopContinue first = true)
      (rest : IncrBody c tail) : IncrBody c (.seq first tail)
  | dec (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64}
      (distinct : c ≠ name) (rest : IncrBody c body) : IncrBody c (.dec name shape init body)
  | decCall (name : MlS) (shape : ShapeHOL) (fn : MlS) (args : List (ExpHOL 64))
      {cont : ProgHOL 64} (distinct : c ≠ name) (rest : IncrBody c cont) :
      IncrBody c (.decCall name shape fn args cont)

theorem IncrBody.run {c : MlS} {body : ProgHOL 64} (hb : IncrBody c body) :
    ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      state.locals.lookup c = some (.val (.word w)) →
      (evaluateHOLFiniteState state body).1 ≠ some .continue ∧
      ((evaluateHOLFiniteState state body).1 = none →
        (evaluateHOLFiniteState state body).2.locals.lookup c = some (.val (.word (w + 1)))) := by
  induction hb with
  | incr =>
    intro F state w atC
    have run : evaluateHOLFiniteState state
        (.assign .local c (.op .add [.var .local c, .const 1])) =
        (none, setVarHOLFinite c (.val (.word (w + 1))) state) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, atC, wordOpHOL, wordOp,
        valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
        shapeOfHOLExact, shapeEqHOL]
    rw [run]
    refine ⟨by simp, fun _ => ?_⟩
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  | seq first avoid noCont rest ih =>
    intro F state w atC
    have frame := evaluate_avoidsLocal_flowing c first avoid state
    have noContinue := evaluate_noTopContinue first noCont state
    rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at frame noContinue
      dsimp only at frame noContinue
      cases result with
      | none =>
        dsimp only
        have kept := frame (Or.inl rfl)
        exact ih middle w (by rw [kept]; exact atC)
      | some r =>
        dsimp only
        exact ⟨noContinue, fun h => by simp at h⟩
  | dec name shape init distinct rest ih =>
    intro F state w atC
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · exact ⟨by simp, by simp⟩
    · rename_i val _
      split
      · have atInner : (setVarHOLFinite name val state).locals.lookup c =
            some (.val (.word w)) := by
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm distinct, atC]
        obtain ⟨t1, t2⟩ := ih (setVarHOLFinite name val state) w atInner
        cases run : evaluateHOLFiniteState (setVarHOLFinite name val state) _ with
        | mk res post =>
          rw [run] at t1 t2
          dsimp only at t1 t2 ⊢
          refine ⟨t1, fun normal => ?_⟩
          rw [PanRunBounded.resVarEq_lookup, if_neg distinct]
          exact t2 normal
      · exact ⟨by simp, by simp⟩
  | @decCall name shape fn args cont distinct rest ih =>
    intro F state w atC
    have hcont : (evaluateHOLFiniteState state (.decCall name shape fn args cont)).1 ≠
        some .continue := by
      intro hc
      rcases hrun : evaluateHOLFiniteState state (.decCall name shape fn args cont) with ⟨r, post⟩
      rw [hrun] at hc
      dsimp only at hc
      subst hc
      obtain ⟨_, resumed, _, hloc, _, hcr, _⟩ :=
        decCall_flowing (Or.inr (Or.inr rfl)) hrun
      have atR : resumed.locals.lookup c = some (.val (.word w)) := (hloc c distinct).trans atC
      have := (ih resumed w atR).1
      rw [hcr] at this
      exact this rfl
    refine ⟨hcont, fun hnone => ?_⟩
    rcases hrun : evaluateHOLFiniteState state (.decCall name shape fn args cont) with ⟨r, post⟩
    rw [hrun] at hnone
    dsimp only at hnone
    subst hnone
    obtain ⟨_, resumed, _, hloc, _, hcr, hpost⟩ := decCall_flowing (Or.inl rfl) hrun
    have atR : resumed.locals.lookup c = some (.val (.word w)) := (hloc c distinct).trans atC
    have := (ih resumed w atR).2
    rw [hcr] at this
    rw [hpost, PanRunBounded.resVarEq_lookup, if_neg distinct]
    exact this rfl

private theorem signed_less_eq (left right : BitVec 64) :
    holAsmSignedLess left right = left.slt right := by
  have bl := left.isLt
  have br := right.isLt
  simp only [holAsmSignedLess, BitVec.slt_eq_decide, BitVec.toInt_eq_msb_cond,
    BitVec.msb_eq_decide]
  repeat (any_goals first | split)
  all_goals simp_all only [decide_eq_true_eq]
  all_goals apply Bool.eq_iff_iff.mpr
  all_goals simp_all [decide_eq_true_eq]
  all_goals omega

def signedUpRank (counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup counter with
  | some (.val (.word w)) => (9223372036854775807 - w.toInt).toNat
  | _ => 0

theorem signedUpRank_le (counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    signedUpRank counter s ≤ 2 ^ 64 := by
  unfold signedUpRank
  split
  · rename_i w _
    have := BitVec.le_toInt w
    omega
  · omega

theorem while_less_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : LocalsFree P) (counter : MlS) (bound : ExpHOL 64)
    {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn P body B)
    (hp : Hoare P body (fun r t => r = none → P t))
    (hinc : IncrBody counter body) :
    TerminatingProgBoundedOn P (.while (.cmp .less (.var .local counter) bound) body)
      ((2 ^ 64 + 1) * (B + 1)) := by
  refine TerminatingProgBoundedOn.while_rank (signedUpRank counter)
    (fun s hs => hP s s.locals (s.clock - 1) hs) hbody
    (fun s _ _ _ => signedUpRank_le counter s) ?_
  intro F s hcode hs ⟨result, hcond, hnz⟩ hflow
  change evalAt s _ = _ at hcond
  obtain ⟨w, v, hw, hv, hword⟩ := evalAt_cmp s .less _ _ result hcond
  simp only [evalAt, evalHOLExact] at hw
  have hwl : s.locals.lookup counter = some (.val (.word w)) := by simpa using hw
  obtain ⟨hnc_w, hinc_w⟩ := hinc.run (decClockHOLFinite s) w hwl
  have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none := by
    rcases hflow with h | h
    · exact h
    · exact absurd h hnc_w
  have hnt_b : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 ≠ some .timeOut := by
    rw [hnone]; simp
  have hP_post : P (evaluateHOLFiniteState (decClockHOLFinite s) body).2 :=
    hp.run (decClockHOLFinite s) hcode (hP s s.locals (s.clock - 1) hs) hnt_b hnone
  refine ⟨hP_post, ?_⟩
  have hcmp : wordCmpHOL .less w v = true := by
    by_contra h; simp [h] at hword; exact hnz hword
  have hlt : w.toInt < v.toInt := by
    simpa only [wordCmpHOL, signed_less_eq, BitVec.slt_iff_toInt_lt] using hcmp
  have hvmax := BitVec.toInt_le (x := v)
  have hwmin := BitVec.le_toInt w
  have hwmax := BitVec.toInt_le (x := w)
  have hone : (1 : BitVec 64).toInt = 1 := by decide
  have hnext : (w + 1).toInt = w.toInt + 1 := by
    rw [BitVec.toInt_add, hone]
    apply Int.bmod_eq_of_le <;> omega
  have hi' := hinc_w hnone
  simp only [signedUpRank, hi', hwl, hnext]
  omega

theorem hoare_while_less_preserve {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : LocalsFree P) (counter : MlS) (bound : ExpHOL 64) {body : ProgHOL 64}
    (hp : Hoare P body (fun r t => r = none → P t))
    (hinc : IncrBody counter body)
    (hnb : InitECandidate.Solver.GuestUniformClockBound.noTopBreak body = true) :
    Hoare P (.while (.cmp .less (.var .local counter) bound) body) (fun r t => r = none → P t) := by
  refine ⟨fun {F} s hcode hs _ hr => ?_⟩
  rcases hrun : evaluateHOLFiniteState s (.while (.cmp .less (.var .local counter) bound) body) with
    ⟨r, post⟩
  rw [hrun] at hr
  dsimp only at hr
  subst hr
  suffices ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F),
      st.clock = k → st.code = originalRuntimeCode → P st →
      evaluateHOLFiniteState st (.while (.cmp .less (.var .local counter) bound) body) =
        (none, post) → P post from
    this s.clock s rfl hcode hs hrun
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st hk st_code hPst hst_run
    rw [evaluateHOLFiniteState_while_total] at hst_run
    split at hst_run
    · rename_i res hcond
      split at hst_run
      · rename_i hwnz
        split at hst_run
        · simp at hst_run
        · dsimp only at hst_run
          rw [fixClockHOLFinite_evaluateState] at hst_run
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
          have hmeta := (evaluateHOLFiniteState_metadata (decClockHOLFinite st) body).1
          have hno_brk :=
            InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak body hnb
              (decClockHOLFinite st)
          change evalAt st _ = _ at hcond
          obtain ⟨w, _, hw, _, _⟩ := evalAt_cmp st .less _ _ res hcond
          simp only [evalAt, evalHOLExact] at hw
          have hwl : (decClockHOLFinite st).locals.lookup counter = some (.val (.word w)) := by
            simpa [decClockHOLFinite] using hw
          obtain ⟨hnc_w, _⟩ := hinc.run (decClockHOLFinite st) w hwl
          rcases bRun : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨r1, mid⟩
          rw [bRun] at hst_run hrem hmeta hnc_w hno_brk
          have hclk_lt : mid.clock < k := by
            change mid.clock ≤ st.clock - 1 at hrem
            omega
          cases r1 with
          | none =>
            have hPmid := hp.run (decClockHOLFinite st) st_code
              (hP st st.locals (st.clock - 1) hPst) (by rw [bRun]; simp)
              (by rw [bRun])
            rw [bRun] at hPmid
            exact ih mid.clock hclk_lt mid rfl (hmeta.trans st_code) hPmid hst_run
          | some r1' =>
            cases r1' with
            | «continue» => exact absurd rfl hnc_w
            | «break» => exact absurd rfl hno_brk
            | _ => simp at hst_run
      · simp at hst_run
        obtain ⟨_, rfl⟩ := hst_run
        exact hPst
    · simp at hst_run

/-! ## 6. Bundled `WBounded` (Clock Bound + Fall-through `WorldOK` Preservation) -/

structure WBounded (prog : ProgHOL 64) (K : Nat) : Prop where
  bounded : TerminatingProgBoundedOn WorldOK prog K
  hoare : Hoare WorldOK prog (fun r t => r = none → WorldOK t)

theorem WBounded.skip : WBounded .skip 0 :=
  ⟨TerminatingProgBoundedOn.of_clock (fun s => clock_skip s),
   Hoare.skip (fun _ h _ => h)⟩

theorem WBounded.ret (e : ExpHOL 64) : WBounded (.return e) 0 :=
  ⟨TerminatingProgBoundedOn.of_clock (fun s => clock_return s e),
   ⟨fun s _ _ _ hr => absurd hr (return_ne_none s e)⟩⟩

theorem WBounded.assignLocal (name : MlS) (e : ExpHOL 64) :
    WBounded (.assign .local name e) 0 :=
  ⟨TerminatingProgBoundedOn.of_clock (fun s => clock_assign s .local name e),
   Hoare.assign (fun s v hW _ _ => localsFree_worldOK s (s.locals.update (name, v)) s.clock hW)
     (fun _ _ hr => absurd hr (by simp))⟩

theorem WBounded.dec (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64} {K : Nat}
    (hb : WBounded body K) : WBounded (.dec name shape init body) K :=
  ⟨TerminatingProgBoundedOn.dec_on localsFree_worldOK name shape init hb.bounded,
   Hoare.dec (names := []) (P' := WorldOK) (by simp)
     (fun s v hW _ => localsFree_worldOK s (s.locals.update (name, v)) s.clock hW)
     hb.hoare
     (fun _ t locals _ h hr => localsFree_worldOK t locals t.clock (h hr))
     (fun _ _ hr => absurd hr (by simp))⟩

theorem WBounded.seq {first second : ProgHOL 64} {a b : Nat}
    (h1 : WBounded first a) (h2 : WBounded second b) :
    WBounded (.seq first second) (a + b) :=
  ⟨TerminatingProgBoundedOn.seq_hoare h1.bounded h1.hoare h2.bounded,
   Hoare.seq ⟨fun s hc hP hnt => ⟨h1.hoare.run s hc hP hnt, fun hr h => absurd h hr⟩⟩ h2.hoare⟩

theorem WBounded.ite (cond : ExpHOL 64) {yes no : ProgHOL 64} {a b : Nat}
    (hy : WBounded yes a) (hn : WBounded no b) :
    WBounded (.ite cond yes no) (max a b) :=
  ⟨TerminatingProgBoundedOn.ite_on hy.bounded hn.bounded,
   Hoare.ite (Hoare.mono hy.hoare (fun _ h => h.1))
     (Hoare.mono hn.hoare (fun _ h => h.1))
     (fun _ _ hr => absurd hr (by simp))⟩

theorem WBounded.whileLess (counter : MlS) (bound : ExpHOL 64) {body : ProgHOL 64} {B : Nat}
    (hb : WBounded body B) (hinc : IncrBody counter body)
    (hnb : InitECandidate.Solver.GuestUniformClockBound.noTopBreak body = true) :
    WBounded (.while (.cmp .less (.var .local counter) bound) body) ((2 ^ 64 + 1) * (B + 1)) :=
  ⟨while_less_on localsFree_worldOK counter bound hb.bounded hb.hoare hinc,
   hoare_while_less_preserve localsFree_worldOK counter bound hb.hoare hinc hnb⟩

theorem WBounded.callKeeps {fname : MlS} {B : Nat}
    (hf : TerminatingFunBoundedOn GuestInv fname B)
    (hk : KeepsOn WorldOK WorldOK fname)
    (args : List (ExpHOL 64)) :
    WBounded (.call (some (none, none)) fname args) (B + 1) :=
  ⟨TerminatingProgBoundedOn.call_on hf none args
     (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv fname args),
   Hoare.call_keeps localsFree_worldOK hk args⟩

theorem WBounded.callLocalRO {fname : MlS} {B : Nat}
    (hf : TerminatingFunBoundedOn GuestInv fname B)
    (hro : ReadOnlyFn fname)
    (var : MlS) (args : List (ExpHOL 64)) :
    WBounded (.call (some (some (.local, var), none)) fname args) (B + 1) := by
  refine ⟨TerminatingProgBoundedOn.call_on hf (some (.local, var)) args
    (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv fname args), ?_⟩
  refine ⟨fun {F} s hcode hW hnt hr => ?_⟩
  rw [evaluateHOLFiniteState_call] at hnt hr ⊢
  rcases hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · rw [hargs] at hr; simp at hr
  · simp only [hargs] at hnt hr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · rw [hl] at hr; simp at hr
    · simp only [hl] at hnt hr ⊢
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hr; simp at hr
      · simp only [hz, ↓reduceIte] at hnt hr ⊢
        have hentryG : GuestInv (callEntryStateHOLFinite s callee) :=
          guestInv_callEntry s callee (worldOK_guestInv s hW)
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with
          ⟨res, post⟩
        have hQc (hsafe : res ≠ some .timeOut) :
            Resumes res → post = { callEntryStateHOLFinite s callee with
              locals := post.locals, clock := post.clock } := by
          have := FunSpec.at_lookup hro s hcode values body' callee ret' hl hentryG
            (by rw [hrun]; exact hsafe)
          rw [hrun] at this
          exact this
        simp only [hrun] at hnt hr ⊢
        cases res with
        | none => simp at hr
        | some r =>
          cases r with
          | returned val =>
            dsimp only at hr ⊢
            split at hr <;> rename_i hsh1
            · simp only [hsh1, ↓reduceIte] at hr ⊢
              split at hr <;> rename_i hsh2
              · simp only [hsh2, ↓reduceIte]
                have heq := hQc (by simp) (Or.inl ⟨val, rfl⟩)
                have hpostW : WorldOK post := by
                  rw [heq]
                  exact localsFree_worldOK s post.locals post.clock hW
                exact localsFree_worldOK post (s.locals.update (var, val)) post.clock hpostW
              · simp at hr
            · simp at hr
          | _ => simp at hr

theorem WBounded.decCallRO {fname : MlS} {B Bc : Nat}
    (hf : TerminatingFunBoundedOn GuestInv fname B)
    (hro : ReadOnlyFn fname)
    (name : MlS) (shape : ShapeHOL) (args : List (ExpHOL 64))
    {cont : ProgHOL 64} (hc : WBounded cont Bc) :
    WBounded (.decCall name shape fname args cont) (B + Bc + 1) := by
  have hres : DecCallResumeOn WorldOK WorldOK name fname args :=
    ReadOnlyFn.resumeOn (LocalsOnly.of_localsFree localsFree_worldOK) worldOK_guestInv
      hro name (by simp) args
  refine ⟨TerminatingProgBoundedOn.decCall_on hf name shape args
    (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv fname args) hres hc.bounded, ?_⟩
  refine ⟨fun {F} s hcode hW _ hr => ?_⟩
  rcases hrun : evaluateHOLFiniteState s (.decCall name shape fname args cont) with ⟨r, post⟩
  rw [hrun] at hr
  dsimp only at hr
  subst hr
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun
  rcases hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · rw [hargs] at hrun; simp at hrun
  · rw [hargs] at hrun; dsimp only at hrun
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · rw [hl] at hrun; simp at hrun
    · rw [hl] at hrun; dsimp only at hrun
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hrun; simp at hrun
      · rw [if_neg hz] at hrun
        have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body').1
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with
          ⟨bres, bpost⟩
        rw [hb] at hrun hmeta
        dsimp only at hmeta
        cases bres with
        | none => simp at hrun
        | some br =>
          cases br with
          | returned v =>
            dsimp only at hrun
            split at hrun
            · set resumed := setVarHOLFinite name v { bpost with locals := s.locals }
              have hresW : WorldOK resumed := hres s values body' callee ret' v bpost hcode hW hargs hl hb
              have hresCode : resumed.code = originalRuntimeCode := hmeta.trans hcode
              rcases hcr : evaluateHOLFiniteState resumed cont with ⟨cres, cpost⟩
              rw [hcr] at hrun
              dsimp only at hrun
              obtain ⟨rfl, hpost_eq⟩ := Prod.mk.inj hrun
              have hWc0 := hc.hoare.run resumed hresCode hresW (by rw [hcr]; simp)
              rw [hcr] at hWc0
              dsimp only
              rw [← hpost_eq]
              exact localsFree_worldOK cpost _ cpost.clock (hWc0 rfl)
            · simp at hrun
          | _ => simp [emptyLocalsHOLFinite] at hrun

theorem WBounded.decCallKeeps {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {fname : MlS} {args : List (ExpHOL 64)} {B Bc : Nat}
    (hf : TerminatingFunBoundedOn Pc fname B)
    (hentry : CallEntryOn WorldOK Pc fname args)
    (hk : KeepsOn WorldOK WorldOK fname)
    (name : MlS) (shape : ShapeHOL)
    {cont : ProgHOL 64} (hc : WBounded cont Bc) :
    WBounded (.decCall name shape fname args cont) (B + Bc + 1) := by
  have hres : DecCallResumeOn WorldOK WorldOK name fname args :=
    KeepsOn.resumeOn localsFree_worldOK hk name args
  refine ⟨TerminatingProgBoundedOn.decCall_on hf name shape args hentry hres hc.bounded, ?_⟩
  refine ⟨fun {F} s hcode hW _ hr => ?_⟩
  rcases hrun : evaluateHOLFiniteState s (.decCall name shape fname args cont) with ⟨r, post⟩
  rw [hrun] at hr
  dsimp only at hr
  subst hr
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun
  rcases hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · rw [hargs] at hrun; simp at hrun
  · rw [hargs] at hrun; dsimp only at hrun
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · rw [hl] at hrun; simp at hrun
    · rw [hl] at hrun; dsimp only at hrun
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hrun; simp at hrun
      · rw [if_neg hz] at hrun
        have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body').1
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with
          ⟨bres, bpost⟩
        rw [hb] at hrun hmeta
        dsimp only at hmeta
        cases bres with
        | none => simp at hrun
        | some br =>
          cases br with
          | returned v =>
            dsimp only at hrun
            split at hrun
            · set resumed := setVarHOLFinite name v { bpost with locals := s.locals }
              have hresW : WorldOK resumed := hres s values body' callee ret' v bpost hcode hW hargs hl hb
              have hresCode : resumed.code = originalRuntimeCode := hmeta.trans hcode
              rcases hcr : evaluateHOLFiniteState resumed cont with ⟨cres, cpost⟩
              rw [hcr] at hrun
              dsimp only at hrun
              obtain ⟨rfl, hpost_eq⟩ := Prod.mk.inj hrun
              have hWc0 := hc.hoare.run resumed hresCode hresW (by rw [hcr]; simp)
              rw [hcr] at hWc0
              dsimp only
              rw [← hpost_eq]
              exact localsFree_worldOK cpost _ cpost.clock (hWc0 rfl)
            · simp at hrun
          | _ => simp [emptyLocalsHOLFinite] at hrun

theorem callEntryOn_balChangeArg (addr idx : ExpHOL 64) (which esz : BitVec 64)
    (hwe : (which.toNat = 16 ∧ esz.toNat = 40) ∨
      (which.toNat = 24 ∧ esz.toNat = 16) ∨
      (which.toNat = 32 ∧ esz.toNat = 24)) :
    CallEntryOn WorldOK BalChangeArg (ofString "bal_remove_change")
      [addr, .const which, .const esz, idx] := by
  intro F state values body callee ret hcode hW hargs hlook
  have hargs_ex := hargs
  rw [evalListHOLFinite_eq_toExact] at hargs_ex
  rcases he1 : evalAt state addr with _ | v1
  · simp [evalListHOLExact, evalAt] at he1 hargs_ex; rw [he1] at hargs_ex; cases hargs_ex
  · rcases he4 : evalAt state idx with _ | v4
    · simp [evalListHOLExact, evalAt] at he1 he4 hargs_ex
      rw [he1, he4] at hargs_ex; simp [evalHOLExact] at hargs_ex
    · have hc := callee_param_four_exp state (ofString "bal_remove_change")
        (ofString "addr") (ofString "which") (ofString "esz") (ofString "idx")
        .one .one .one .one _ .one (by rw [hcode]; exact lookup_bal_remove_change_fn)
        addr (.const which) (.const esz) idx
        v1 (.val (.word which)) (.val (.word esz)) v4
        values body callee ret
        he1 (by rfl) (by rfl) he4 hargs hlook
      refine ⟨localsFree_worldOK state callee (state.clock - 1) hW, ?_⟩
      have hw : locN (callEntryStateHOLFinite state callee) "which" = which.toNat := by
        simp [locN, callEntryStateHOLFinite, hc.2.1]
      have he : locN (callEntryStateHOLFinite state callee) "esz" = esz.toNat := by
        simp [locN, callEntryStateHOLFinite, hc.2.2.1]
      rw [hw, he]
      exact hwe

theorem WBounded.callBalRemove {B : Nat}
    (hf : TerminatingFunBoundedOn GuestInv (ofString "bal_remove_change") B)
    (wk : WorldKeeps BalChangeArg (fun _ => []) []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "bal_remove_change"))
    (addr idx : ExpHOL 64) (which esz : BitVec 64)
    (hwe : (which.toNat = 16 ∧ esz.toNat = 40) ∨
      (which.toNat = 24 ∧ esz.toNat = 16) ∨
      (which.toNat = 32 ∧ esz.toNat = 24)) :
    WBounded (.call (some (none, none)) (ofString "bal_remove_change")
      [addr, .const which, .const esz, idx]) (B + 1) := by
  refine ⟨TerminatingProgBoundedOn.call_on hf none _
    (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _), ?_⟩
  refine Hoare.call0 wk (callEntryOn_balChangeArg addr idx which esz hwe)
    (fun s callee post v _ hW hq _ => ?_)
    (fun _ _ hr _ h => absurd h hr)
  have hstep := hq (Or.inl ⟨v, rfl⟩)
  have hpostW : WorldOK post :=
    hstep.worldOK_nil (localsFree_worldOK s callee (s.clock - 1) hW)
  exact localsFree_worldOK post s.locals post.clock hpostW

macro "ub_incr" : tactic => `(tactic| repeat (first
  | exact IncrBody.incr
  | apply IncrBody.dec _ _ _ (by decide)
  | apply IncrBody.decCall _ _ _ _ (by decide)
  | apply IncrBody.seq _ rfl rfl))

theorem gbody_update_builder_from_tx_impl :
    (TerminatingFunBoundedOn GuestInv (ofString "add_balance_change") K.«add_balance_change») →
    (TerminatingFunBoundedOn GuestInv (ofString "add_code_change") K.«add_code_change») →
    (TerminatingFunBoundedOn GuestInv (ofString "add_nonce_change") K.«add_nonce_change») →
    (TerminatingFunBoundedOn GuestInv (ofString "add_storage_write") K.«add_storage_write») →
    (TerminatingFunBoundedOn GuestInv (ofString "bal_remove_change") K.«bal_remove_change») →
    (TerminatingFunBoundedOn GuestInv (ofString "get_code") K.«get_code») →
    (TerminatingFunBoundedOn GuestInv (ofString "htab_item") K.«htab_item») →
    (TerminatingFunBoundedOn GuestInv (ofString "idx_start_account") K.«idx_start_account») →
    (TerminatingFunBoundedOn WorldOK (ofString "idx_start_storage") K.«idx_start_storage») →
    (TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq») →
    (TerminatingFunBoundedOn GuestInv (ofString "remove_storage_write") K.«remove_storage_write») →
    (TerminatingFunBoundedOn GuestInv (ofString "u256_eq") K.«u256_eq») →
    (WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "add_balance_change")) →
    (WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "add_code_change")) →
    (WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "add_nonce_change")) →
    (WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "add_storage_write")) →
    (WorldKeeps BalChangeArg (fun _ => [])
      []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "bal_remove_change")) →
    (WorldKeeps WorldOK (fun s => [(globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "get_code")) →
    (ReadOnlyFn (ofString "htab_item")) →
    (WorldKeeps WorldOK (fun s => [(globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
        (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "idx_start_account")) →
    (WorldKeeps WorldOK (fun s => [(globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
        (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "idx_start_storage")) →
    (ReadOnlyFn (ofString "memeq")) →
    (WorldKeeps WorldOK (fun _ => [])
      []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "remove_storage_write")) →
    (ReadOnlyFn (ofString "u256_eq")) →
    TerminatingFunBoundedOn WorldOK (ofString "update_builder_from_tx") K.«update_builder_from_tx» := by
  intro habc hacc hanc hasw hbrc hgc hhi hisa hiss hme hrsw hueq
    wabc wacc wanc wasw wbrc wgc rhi wisa wiss rme wrsw rueq
  have hk_gc : KeepsOn WorldOK WorldOK (ofString "get_code") := by
    apply wgc.keepsOn_buffer_parts
    intro F s i hi
    change i ∈ [bufferRegion s ("sk_buf", 52)] at hi
    simp only [List.mem_singleton] at hi
    subst hi
    exact ⟨("sk_buf", 64), by decide, by decide, 52, by decide, rfl⟩
  have hk_isa : KeepsOn WorldOK WorldOK (ofString "idx_start_account") := by
    apply wisa.keepsOn_buffers
    intro F s i hi
    change i ∈ [bufferRegion s ("bal_key_buf", 64), bufferRegion s ("keccak_pad", 136),
      bufferRegion s ("keccak_st", 200), bufferRegion s ("mpt_nib_scratch", 64)] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> exact ⟨_, by decide, by decide, rfl⟩
  have hk_iss : KeepsOn WorldOK WorldOK (ofString "idx_start_storage") := by
    apply wiss.keepsOn_buffers
    intro F s i hi
    change i ∈ [bufferRegion s ("bal_key_buf", 64), bufferRegion s ("keccak_pad", 136),
      bufferRegion s ("keccak_st", 200), bufferRegion s ("mpt_nib_scratch", 64)] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> exact ⟨_, by decide, by decide, rfl⟩
  refine ⟨_, _, _, «lookup_update_builder_from_tx», ?_⟩
  simp only [InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (WBounded.dec _ _ _ (WBounded.dec _ _ _ (WBounded.dec _ _ _ (WBounded.dec _ _ _
      (WBounded.seq
        (WBounded.whileLess _ _
          (WBounded.decCallRO hhi rhi _ _ _
            (WBounded.seq
              (WBounded.ite _
                (WBounded.dec _ _ _ (WBounded.dec _ _ _
                  (WBounded.decCallKeeps hisa
                    (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _) hk_isa _ _
                    (WBounded.dec _ _ _ (WBounded.dec _ _ _ (WBounded.dec _ _ _
                      (WBounded.dec _ _ _ (WBounded.dec _ _ _ (WBounded.dec _ _ _
                        (WBounded.seq
                          (WBounded.ite _
                            (WBounded.seq (WBounded.assignLocal _ _)
                              (WBounded.seq (WBounded.assignLocal _ _)
                                (WBounded.assignLocal _ _)))
                            WBounded.skip)
                          (WBounded.decCallRO hueq rueq _ _ _
                            (WBounded.seq
                              (WBounded.ite _
                                (WBounded.callKeeps habc wabc.keepsOn _)
                                (WBounded.callBalRemove hbrc wbrc _ _ 16 40 (by decide)))
                              (WBounded.seq
                                (WBounded.ite _
                                  (WBounded.callKeeps hanc wanc.keepsOn _)
                                  (WBounded.callBalRemove hbrc wbrc _ _ 24 16 (by decide)))
                                (WBounded.seq
                                  (WBounded.callLocalRO hme rme _ _)
                                  (WBounded.ite _
                                    (WBounded.decCallKeeps hgc
                                      (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _)
                                      hk_gc _ _
                                      (WBounded.callKeeps hacc wacc.keepsOn _))
                                    (WBounded.callBalRemove hbrc wbrc _ _ 32 24 (by decide)))))))))))))))))
                WBounded.skip)
              (WBounded.assignLocal _ _)))
          (by ub_incr) rfl)
        (WBounded.dec _ _ _
          (WBounded.seq (WBounded.assignLocal _ _)
            (WBounded.seq (WBounded.assignLocal _ _)
              (WBounded.seq
                (WBounded.whileLess _ _
                  (WBounded.decCallRO hhi rhi _ _ _
                    (WBounded.seq
                      (WBounded.ite _
                        (WBounded.dec _ _ _ (WBounded.dec _ _ _ (WBounded.dec _ _ _
                          (WBounded.whileLess _ _
                            (WBounded.decCallRO hhi rhi _ _ _
                              (WBounded.seq
                                (WBounded.ite _
                                  (WBounded.decCallKeeps hiss
                                    (callEntryOn_of_localsFree localsFree_worldOK _ _) hk_iss _ _
                                    (WBounded.dec _ _ _
                                      (WBounded.decCallRO hueq rueq _ _ _
                                        (WBounded.ite _
                                          (WBounded.callKeeps hasw wasw.keepsOn _)
                                          (WBounded.callKeeps hrsw wrsw.keepsOn _)))))
                                  WBounded.skip)
                                (WBounded.assignLocal _ _)))
                            (by ub_incr) rfl))))
                        WBounded.skip)
                      (WBounded.assignLocal _ _)))
                  (by ub_incr) rfl)
                (WBounded.ret _)))))))))).bounded ?_
  unfold K.«update_builder_from_tx»
  simp only [show ∀ a b : Nat, Nat.max a b = max a b from fun _ _ => rfl]
  omega

end R10GbodyIdxBuilder
end InitECandidate.Solver.Wave8GuestInv
