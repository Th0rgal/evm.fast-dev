import InitECandidate.Solver.Wave8GuestInv.ContractParts.C15

/-! Helper lemmas and proofs for `gbody_process_message` and `gbody_process_create_message`
(`ContractParts/C16.lean`) on `wave8/spec-r10`. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1500000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyProcessMsg

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Backend
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. Runtime code lookups and parameter passing -/

theorem lookup_frame_open :
    originalRuntimeCode.lookup (ofString "frame_open") =
      some ((sourceFunctionEntry Guest.Software.guestFn_frame_open).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 578 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_frame_open) rfl

theorem lookup_process_message :
    originalRuntimeCode.lookup (ofString "process_message") =
      some ((sourceFunctionEntry Guest.Software.guestFn_process_message).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 588 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_process_message) rfl

theorem lookup_process_create_message :
    originalRuntimeCode.lookup (ofString "process_create_message") =
      some ((sourceFunctionEntry Guest.Software.guestFn_process_create_message).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 590 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_process_create_message) rfl

theorem callee_param_two {F : Type} (state : PanSemStateFiniteExact 64 F) (fname p1 p2 : MlS)
    (s1 s2 : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname = some ([(p1, s1), (p2, s2)], body, ret))
    (e1 e2 : ExpHOL 64)
    (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [e1, e2] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    ∃ v1 v2,
      evalAt state e1 = some v1 ∧
      evalAt state e2 = some v2 ∧
      callee.lookup p1 = some v1 ∧
      callee.lookup p2 = some v2 := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact] at hargs
  rcases he1 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e1 with _ | v1
  · simp [he1] at hargs
  · rcases he2 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e2 with _ | v2
    · simp [he1, he2] at hargs
    · simp only [he1, he2, Option.some.injEq] at hargs
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
          refine ⟨v1, v2, he1, he2, ?_, ?_⟩
          · simp [List.zip, List.foldl, hnd.1]
          · simp [List.zip, List.foldl]
        · cases raw

theorem callEntryOn_frameOpenReady :
    CallEntryOn MsgReady FrameOpenReady (ofString "frame_open")
      [.var .local (ofString "msg"), .const 0] := by
  have hl := lookup_frame_open
  rcases hfn : (sourceFunctionEntry Guest.Software.guestFn_frame_open).2 with ⟨ps, b, r⟩
  rw [hfn] at hl
  have hps : ps = [(ofString "msg", .one), (ofString "kind", .one)] := by
    have h1 := congrArg Prod.fst hfn
    simp [sourceFunctionEntry, Guest.Software.guestFn_frame_open,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural] at h1
    exact h1.symm
  subst hps
  intro F state values body' callee ret' hcode hP hargs hlook
  obtain ⟨v1, v2, he1, he2, hc1, hc2⟩ := callee_param_two state (ofString "frame_open")
    (ofString "msg") (ofString "kind") .one .one b r (by rw [hcode]; exact hl)
    (.var .local (ofString "msg")) (.const 0) values body' callee ret' hargs hlook
  have hv1 : state.locals.lookup (ofString "msg") = some v1 := by
    simpa [evalAt, evalHOLExact] using he1
  have hv2 := evalAt_const state 0 v2 he2
  subst hv2
  refine ⟨?_, ?_⟩
  · exact localsOnly_msgReady state callee (state.clock - 1)
      (fun n hn => by simp at hn; subst hn; rw [hc1, hv1]) hP
  · simp [locN, callEntryStateHOLFinite, hc2]

theorem callEntryOn_msgReady_process_message (hl : ∃ body ret,
    originalRuntimeCode.lookup (ofString "process_message") =
      some ([(ofString "msg", .one)], body, ret)) :
    CallEntryOn MsgReady MsgReady (ofString "process_message")
      [.var .local (ofString "msg")] := by
  obtain ⟨b, r, hlook⟩ := hl
  intro F state values body' callee ret' hcode hP hargs hlk
  have hc := callee_param_one state (ofString "process_message") (ofString "msg") .one b r
    (by rw [hcode]; exact hlook) values body' callee ret' hargs hlk
  exact localsOnly_msgReady state callee (state.clock - 1)
    (fun n hn => by simp at hn; subst hn; exact hc) hP

theorem resumeOn_keepsOn_localsFree {P W : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {fname : MlS} {arguments : List (ExpHOL 64)}
    (hentry : CallEntryOn P FrameOpenReady fname arguments)
    (hW : LocalsFree W)
    (hk : KeepsOn FrameOpenReady W fname)
    (name : MlS) :
    DecCallResumeOn P W name fname arguments := by
  obtain ⟨params, body', ret', hlook, hb⟩ := hk
  intro F state values body callee ret value post hcode hP hargs hl hrun
  have hsame := lookupCodeHOLFinite_installed_body state.code.lookup fname params body' body
    ret' ret values callee (by rw [hcode]; exact hlook) hl
  subst hsame
  have hret := lookupCodeHOLFinite_installed_return state fname params body body ret' ret
    values callee (by rw [hcode]; exact hlook) hl
  subst hret
  have hPc := hentry state values body callee ret hcode hP hargs hl
  have hq := hb (callEntryStateHOLFinite state callee) hcode hPc
    ⟨values, by simpa only [hcode, callEntryStateHOLFinite] using hl⟩
    (by rw [hrun]; simp) (by rw [hrun]; exact Or.inl ⟨value, rfl⟩)
  rw [hrun] at hq
  have := hW post (state.locals.update (name, value)) post.clock hq
  simpa [setVarHOLFinite] using this

/-! ## 2. Aligned memory cell preservation and `WorldTypedWith` / `EvmInv` congruence -/

theorem disj_symm {i j : Ivl} (h : Disj i j) : Disj j i := h.flip

theorem disj_zero_left (j : Ivl) : Disj (0, 0) j := Or.inl rfl
theorem disj_zero_right (i : Ivl) : Disj i (0, 0) := Or.inr (Or.inl rfl)

theorem disj_of_inside_left {i i' j : Ivl} (hin : Inside i i'.1 (i'.1 + i'.2))
    (hd : Disj i' j) : Disj i j := by
  rcases hin with ⟨h1, h2⟩
  rcases hd with h | h | h | h
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

theorem disj_of_inside_right {i j j' : Ivl} (hin : Inside j j'.1 (j'.1 + j'.2))
    (hd : Disj i j') : Disj i j :=
  (disj_of_inside_left hin hd.flip).flip

theorem ordinaryDomain_iff (x : BitVec 64) :
    ordinaryDomain x ↔ x.toNat % 8 = 0 ∧ sourceBase ≤ x.toNat ∧ x.toNat < heapEnd := by
  unfold ordinaryDomain
  rw [StackRemove.mem_addresses]
  have hx := x.isLt
  have hconst : (stackStart - sourceBase) / 8 - globalsWords = 3888119741 ∧
      sourceBase = 2701131776 ∧ heapEnd = 33806089704 ∧
      StackRemove.bytesInWord 64 = BitVec.ofNat 64 8 := by
    refine ⟨by decide, by decide, by decide, ?_⟩
    decide
  rcases hconst with ⟨hn, hsb, hhe, hbw⟩
  rw [hn, hbw]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
    simp only [hsb, hhe]
    omega
  · rintro ⟨hal, hlo, hhi⟩
    refine ⟨(x.toNat - sourceBase) / 8, by simp only [hsb, hhe] at hlo hhi; omega, ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
    simp only [hsb, hhe] at hlo hhi ⊢
    omega

def IvlUnhit {F : Type} (s post : PanSemStateFiniteExact 64 F) (i : Ivl) : Prop :=
  i.2 = 0 ∨ ∀ a : BitVec 64, a.toNat % 8 = 0 → CellHits a.toNat i → post.memory a = s.memory a

theorem ivlUnhit_of_single_cell_disj {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {x : BitVec 64} {i : Ivl}
    (hm : ∀ a : BitVec 64, a ≠ x → post.memory a = s.memory a)
    (hd : Disj i (x.toNat, 8)) :
    IvlUnhit s post i := by
  by_cases hz : i.2 = 0
  · exact Or.inl hz
  · right
    intro a _ hhit
    apply hm
    rintro rfl
    rcases i with ⟨i1, i2⟩
    rcases hhit with ⟨h1, h2⟩
    dsimp only at hz h1 h2
    rcases hd with h | h | h | h
    · exact absurd h hz
    · cases h
    · dsimp only at h; omega
    · dsimp only at h; omega

theorem memW_eq_of_ivlUnhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {i : Ivl} (hu : IvlUnhit s post i) {a : Nat}
    (ha8 : a % 8 = 0) (hhi : i.1 + i.2 ≤ 2 ^ 64) (hin : i.1 ≤ a ∧ a + 8 ≤ i.1 + i.2) :
    memW post a = memW s a := by
  rcases hu with hz | hu
  · omega
  · have ha_lt : a < 2 ^ 64 := by omega
    have hmem := hu (BitVec.ofNat 64 a)
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]; exact ha8)
      (by unfold CellHits; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]; omega)
    unfold memW
    rw [hmem]

theorem memB_eq_of_ivlUnhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {i : Ivl} (hu : IvlUnhit s post i) (hbe : post.be = s.be)
    {a : Nat} (hhi : i.1 + i.2 ≤ 2 ^ 64) (hin : i.1 ≤ a ∧ a < i.1 + i.2) :
    memB post a = memB s a := by
  rcases hu with hz | hu
  · omega
  · have ha_lt : a < 2 ^ 64 := by omega
    let c := panByteAlignHOL (BitVec.ofNat 64 a)
    have hc_nat : c.toNat = a / 8 * 8 := by
      have hal : 2 ^ ((64 : Nat) / 8).log2 = 8 := by decide
      change (BitVec.ofNat 64 ((BitVec.ofNat 64 a).toNat / 2 ^ ((64 : Nat) / 8).log2 *
        2 ^ ((64 : Nat) / 8).log2)).toNat = a / 8 * 8
      rw [hal, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt,
        Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self a 8) ha_lt)]
    have hmem := hu c (by rw [hc_nat]; omega) (by unfold CellHits; rw [hc_nat]; omega)
    unfold memB
    change (match post.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 a) v post.be).toNat) =
           (match s.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 a) v s.be).toNat)
    rw [hmem, hbe]

theorem ivl_allocated_bound {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {i : Ivl} (hal : Allocated s i) :
    i.1 + i.2 ≤ heapEnd ∧ i.1 + i.2 ≤ 2 ^ 64 := by
  have h1 : heapLimit ≤ heapEnd := by decide
  have h2 : scratchEnd ≤ heapEnd := by decide
  have h3 : heapEnd < 2 ^ 64 := by decide
  rcases hal with ⟨_, hi⟩ | ⟨_, hi⟩
  · have := hA.2.1; omega
  · have := hA.2.2.2.2.1; omega

theorem wordsOK_transfer {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post) {i : Ivl} (hw : WordsOK s i) :
    WordsOK post i := by
  refine ⟨hw.1, hw.2.1, fun k hk => ?_⟩
  obtain ⟨_, hdom, _⟩ := hw.2.2 k hk
  rcases hm : post.memory (BitVec.ofNat 64 (i.1 + 8 * k)) with ⟨w⟩
  refine ⟨w, ?_, hm⟩
  rw [hgP.memaddrs, ← hgS.memaddrs]
  exact hdom

/-- Congruence of `FreeChain` when all nodes in `Fr` lie in `[1, ncap]` inside an unhit `nodes` block. -/
theorem freeChain_congr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {nodes ncap : Nat} (hn8 : nodes % 8 = 0) (hhi : nodes + (ncap + 1) * 32 ≤ 2 ^ 64)
    (hu : IvlUnhit s post (nodes, (ncap + 1) * 32)) :
    ∀ (Fr : List Nat) (head : Nat),
      (∀ f ∈ Fr, 1 ≤ f ∧ f ≤ ncap) →
      (FreeChain post nodes head Fr ↔ FreeChain s nodes head Fr)
  | [], head, _ => Iff.rfl
  | f :: rest, head, hFr => by
    have hf : 1 ≤ f ∧ f ≤ ncap := hFr f (by simp)
    have hnd : nodeF post nodes f 0 = nodeF s nodes f 0 := by
      unfold nodeF
      exact memW_eq_of_ivlUnhit hu (by omega) hhi ⟨by omega, by omega⟩
    simp only [FreeChain, hnd]
    exact and_congr Iff.rfl (freeChain_congr_unhit hn8 hhi hu rest _ (fun x hx => hFr x (by simp [hx])))

theorem htabFootprint_eq_of_hdr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {t : Nat} (ht8 : t % 8 = 0) (hhdr_hi : t + 88 ≤ 2 ^ 64) (hu : IvlUnhit s post (t, 88)) :
    (∀ k, k < 11 → hdr post t k = hdr s t k) ∧ htabFootprint post t = htabFootprint s t := by
  have hhdr : ∀ k, k < 11 → hdr post t k = hdr s t k := fun k hk => by
    unfold hdr
    exact memW_eq_of_ivlUnhit hu (by omega) hhdr_hi ⟨by omega, by omega⟩
  refine ⟨hhdr, ?_⟩
  simp only [htabFootprint, hhdr 1 (by omega), hhdr 4 (by omega), hhdr 5 (by omega),
    hhdr 6 (by omega), hhdr 10 (by omega)]

theorem nodup_len_le {l : List Nat} {n : Nat} (hnd : l.Nodup)
    (hr : ∀ x ∈ l, 1 ≤ x ∧ x < n) : l.length ≤ n - 1 := by
  have hsub : l.toFinset ⊆ Finset.Ico 1 n := by
    intro x hx
    simp only [List.mem_toFinset] at hx
    simp only [Finset.mem_Ico]
    exact hr x hx
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, Nat.card_Ico] at this
  exact this

theorem htabValues_eq_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {t : Nat} (hwf : HtabWF s t)
    (hu : ∀ i ∈ htabFootprint s t, IvlUnhit s post i) :
    htabValues post t = htabValues s t := by
  have h264 : heapEnd ≤ 2 ^ 64 := by decide
  have hfp := hwf.1
  have ht_fp : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
  have hnd_fp : (hdr s t 5, (hdr s t 10 + 1) * 32) ∈ htabFootprint s t := by simp [htabFootprint]
  have hord_fp : (hdr s t 6, (hdr s t 10 + 1) * 8) ∈ htabFootprint s t := by simp [htabFootprint]
  have ht8 : t % 8 = 0 := (hfp _ ht_fp).2.1
  have hnd8 : (hdr s t 5) % 8 = 0 := (hfp _ hnd_fp).2.1
  have hord8 : (hdr s t 6) % 8 = 0 := (hfp _ hord_fp).2.1
  have hhdr_hi : t + 88 ≤ 2 ^ 64 := by have := (hfp _ ht_fp).1.2; omega
  obtain ⟨hhdr, _⟩ := htabFootprint_eq_of_hdr_unhit ht8 hhdr_hi (hu _ ht_fp)
  have hnd_hi : hdr s t 5 + (hdr s t 10 + 1) * 32 ≤ 2 ^ 64 := by have := (hfp _ hnd_fp).1.2; omega
  have hord_hi : hdr s t 6 + (hdr s t 10 + 1) * 8 ≤ 2 ^ 64 := by have := (hfp _ hord_fp).1.2; omega
  obtain ⟨-, -, -, -, -, _, _, hnext_le, L, I, Fr, hLlen, hnodup, hmem, _, hL, -⟩ := hwf
  have hlen_all := nodup_len_le hnodup (fun x hx => (hmem x).1 hx)
  have hlen_L : L.length ≤ hdr s t 10 := by
    simp only [List.length_append] at hlen_all; omega
  unfold htabValues
  rw [hhdr 3 (by omega), hhdr 5 (by omega), hhdr 6 (by omega)]
  apply List.map_congr_left
  intro idx hidx
  rw [List.mem_range] at hidx
  have hidx_L : idx < L.length := by omega
  have hLi_mem : L[idx] ∈ L ++ I ++ Fr := by
    apply List.mem_append.2; left; apply List.mem_append.2; left; exact List.getElem_mem hidx_L
  have hLi_bound : 1 ≤ L[idx] ∧ L[idx] ≤ hdr s t 10 := by
    have := (hmem L[idx]).1 hLi_mem; omega
  have hord_eq : memW post (hdr s t 6 + 8 * idx) = memW s (hdr s t 6 + 8 * idx) :=
    memW_eq_of_ivlUnhit (hu _ hord_fp) (by omega) hord_hi ⟨by omega, by omega⟩
  rw [hord_eq, (hL idx hidx_L).1]
  unfold nodeF
  exact memW_eq_of_ivlUnhit (hu _ hnd_fp) (by omega) hnd_hi ⟨by omega, by omega⟩

theorem htabValuesIn_congr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {t : Nat} {S S' : List Nat} (hwf : HtabWF s t)
    (hu : ∀ i ∈ htabFootprint s t, IvlUnhit s post i)
    (hsub : ∀ x ∈ S, x ∈ S')
    (hval : HtabValuesIn s t S) :
    HtabValuesIn post t S' := by
  have h264 : heapEnd ≤ 2 ^ 64 := by decide
  have hfp := hwf.1
  have ht_fp : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
  have ht8 : t % 8 = 0 := (hfp _ ht_fp).2.1
  have hhdr_hi : t + 88 ≤ 2 ^ 64 := by have := (hfp _ ht_fp).1.2; omega
  obtain ⟨hhdr, _⟩ := htabFootprint_eq_of_hdr_unhit ht8 hhdr_hi (hu _ ht_fp)
  have hvals := htabValues_eq_of_unhit hwf hu
  intro idx hidx
  rw [hhdr 3 (by omega)] at hidx
  have hmem_s : nodeF s (hdr s t 5) (memW s (hdr s t 6 + 8 * idx)) 8 ∈ S := hval idx hidx
  have hget : (htabValues post t)[idx]? = (htabValues s t)[idx]? := by rw [hvals]
  simp only [htabValues, List.getElem?_map, List.getElem?_range, hhdr 3 (by omega), hidx,
    Option.map_some, Option.some.injEq] at hget
  rw [hget]
  exact hsub _ hmem_s

theorem htabWF_congr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post)
    {t : Nat} (hwf : HtabWF s t)
    (hu : ∀ i ∈ htabFootprint s t, IvlUnhit s post i) :
    HtabWF post t := by
  have h264 : heapEnd ≤ 2 ^ 64 := by decide
  have hfp := hwf.1
  have ht_fp : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
  have hnd_fp : (hdr s t 5, (hdr s t 10 + 1) * 32) ∈ htabFootprint s t := by simp [htabFootprint]
  have hord_fp : (hdr s t 6, (hdr s t 10 + 1) * 8) ∈ htabFootprint s t := by simp [htabFootprint]
  have ht8 : t % 8 = 0 := (hfp _ ht_fp).2.1
  have hnd8 : (hdr s t 5) % 8 = 0 := (hfp _ hnd_fp).2.1
  have hord8 : (hdr s t 6) % 8 = 0 := (hfp _ hord_fp).2.1
  have hhdr_hi : t + 88 ≤ 2 ^ 64 := by have := (hfp _ ht_fp).1.2; omega
  obtain ⟨hhdr, hfp_eq⟩ := htabFootprint_eq_of_hdr_unhit ht8 hhdr_hi (hu _ ht_fp)
  have hnd_hi : hdr s t 5 + (hdr s t 10 + 1) * 32 ≤ 2 ^ 64 := by have := (hfp _ hnd_fp).1.2; omega
  have hord_hi : hdr s t 6 + (hdr s t 10 + 1) * 8 ≤ 2 ^ 64 := by have := (hfp _ hord_fp).1.2; omega
  obtain ⟨hfp1, hfp2, hk1, hk2, hstr, hncap, hnext1, hnext2,
    L, I, Fr, hLlen, hnodup, hmem, hcntI, hL, hI, hr0, hrpos, hnroot, hpI, hdep, hfc⟩ := hwf
  have hlen_all := nodup_len_le hnodup (fun x hx => (hmem x).1 hx)
  have hlen_L : L.length ≤ hdr s t 10 := by
    simp only [List.length_append] at hlen_all; omega
  have hnd_eq : ∀ n, 1 ≤ n → n ≤ hdr s t 10 → ∀ off ∈ ([0, 8, 16, 24] : List Nat),
      nodeF post (hdr s t 5) n off = nodeF s (hdr s t 5) n off := by
    intro n hn1 hn2 off hoff
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    unfold nodeF
    rcases hoff with rfl | rfl | rfl | rfl <;>
      exact memW_eq_of_ivlUnhit (hu _ hnd_fp) (by omega) hnd_hi ⟨by omega, by omega⟩
  have hLI_bound : ∀ n ∈ L ++ I, 1 ≤ n ∧ n ≤ hdr s t 10 := fun n hn => by
    have := (hmem n).1 (List.mem_append.2 (Or.inl hn)); omega
  unfold HtabWF
  rw [hfp_eq, hhdr 0 (by omega), hhdr 1 (by omega), hhdr 3 (by omega), hhdr 5 (by omega),
    hhdr 6 (by omega), hhdr 7 (by omega), hhdr 8 (by omega), hhdr 9 (by omega), hhdr 10 (by omega)]
  refine ⟨fun i hi => ⟨(hfp1 i hi).1, wordsOK_transfer hgS hgP (hfp1 i hi).2⟩,
    hfp2, hk1, hk2, hstr, hncap, hnext1, hnext2, L, I, Fr, hLlen, hnodup, hmem, hcntI,
    ?_, ?_, hr0, ?_, ?_, ?_, ?_, ?_⟩
  · intro idx hidx
    have hLi : L[idx] ∈ L ++ I := List.mem_append.2 (Or.inl (List.getElem_mem hidx))
    obtain ⟨hb1, hb2⟩ := hLI_bound L[idx] hLi
    have hord_eq : memW post (hdr s t 6 + 8 * idx) = memW s (hdr s t 6 + 8 * idx) :=
      memW_eq_of_ivlUnhit (hu _ hord_fp) (by omega) hord_hi ⟨by omega, by omega⟩
    rw [hord_eq, hnd_eq L[idx] hb1 hb2 24 (by simp), hnd_eq L[idx] hb1 hb2 16 (by simp)]
    exact hL idx hidx
  · intro n hn
    have hnLI : n ∈ L ++ I := List.mem_append.2 (Or.inr hn)
    obtain ⟨hb1, hb2⟩ := hLI_bound n hnLI
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩ := hI n hn
    obtain ⟨h8_1, h8_2⟩ := hLI_bound _ hc2
    obtain ⟨h16_1, h16_2⟩ := hLI_bound _ hc3
    rw [hnd_eq n hb1 hb2 24 (by simp), hnd_eq n hb1 hb2 8 (by simp), hnd_eq n hb1 hb2 16 (by simp),
      hnd_eq _ h8_1 h8_2 0 (by simp), hnd_eq _ h16_1 h16_2 0 (by simp)]
    exact ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩
  · intro hpos
    obtain ⟨hrm, hrp⟩ := hrpos hpos
    obtain ⟨hb1, hb2⟩ := hLI_bound _ hrm
    rw [hnd_eq _ hb1 hb2 0 (by simp)]
    exact ⟨hrm, hrp⟩
  · intro n hn
    have hnLI : n ∈ L ++ I := List.mem_append.2 (Or.inr hn)
    obtain ⟨hb1, hb2⟩ := hLI_bound n hnLI
    rw [hnd_eq n hb1 hb2 8 (by simp), hnd_eq n hb1 hb2 16 (by simp)]
    exact hnroot n hn
  · intro n hn hnr
    obtain ⟨hb1, hb2⟩ := hLI_bound n hn
    rw [hnd_eq n hb1 hb2 0 (by simp)]
    exact hpI n hn hnr
  · obtain ⟨dep, hdep⟩ := hdep
    refine ⟨dep, fun n hn hnr => ?_⟩
    obtain ⟨hb1, hb2⟩ := hLI_bound n hn
    have hp_mem : nodeF s (hdr s t 5) n 0 ∈ L ++ I := List.mem_append.2 (Or.inr (hpI n hn hnr))
    obtain ⟨hpb1, hpb2⟩ := hLI_bound _ hp_mem
    rw [hnd_eq n hb1 hb2 0 (by simp), hnd_eq _ hpb1 hpb2 8 (by simp), hnd_eq _ hpb1 hpb2 16 (by simp)]
    exact hdep n hn hnr
  · exact (freeChain_congr_unhit hnd8 hnd_hi (hu _ hnd_fp) Fr (hdr s t 9)
      (fun f hf => by have := (hmem f).1 (List.mem_append.2 (Or.inr hf)); omega)).2 hfc

theorem typedRecord_mem_globalBuffers {r : String × Nat} (hr : r ∈ typedRecords) :
    r ∈ globalBuffers := by
  simp only [typedRecords, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp [globalBuffers]

theorem typedRecord_mem_fixedObjects {F : Type} (s : PanSemStateFiniteExact 64 F)
    {r : String × Nat} (hr : r ∈ typedRecords) :
    (globN s r.1, if globN s r.1 = 0 then 0 else r.2) ∈ fixedObjects s := by
  unfold fixedObjects
  apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
  exact List.mem_map.2 ⟨r, typedRecord_mem_globalBuffers hr, rfl⟩

theorem rec_word_eq_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) (hF : FixedTyped s)
    (g : String) (sz : Nat) (hrec : (g, sz) ∈ typedRecords)
    (hg_eq : globN post g = globN s g) (hgnz : globN s g ≠ 0)
    (hu : IvlUnhit s post (globN s g, sz))
    {k : Nat} (hk8 : k % 8 = 0) (hksz : k + 8 ≤ sz) :
    memW post (globN post g + k) = memW s (globN s g + k) := by
  rw [hg_eq]
  have hmem_fix := typedRecord_mem_fixedObjects s hrec
  simp only [hgnz, ↓reduceIte] at hmem_fix
  have hsz_pos : sz ≠ 0 := by omega
  rcases hF.1 _ hmem_fix with h0 | ⟨hal, hwords⟩
  · exact absurd h0 hsz_pos
  · have hhi := (ivl_allocated_bound hA hal).2
    have hg8 : (globN s g) % 8 = 0 := hwords.1
    exact memW_eq_of_ivlUnhit hu (by omega) hhi ⟨by omega, by omega⟩

theorem nodeHeap_congr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post) (hbe : post.be = s.be)
    (hag : AllocatorGrows s post)
    {Nd : List Nat} (hN : NodeHeap s Nd)
    (hu : ∀ o ∈ nodeExtents s Nd, IvlUnhit s post o) :
    NodeHeap post Nd ∧ nodeExtents post Nd = nodeExtents s Nd := by
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hn_props : ∀ n ∈ Nd,
      memW post n = memW s n ∧
      nodeIvl post n = nodeIvl s n ∧
      (∀ k, k < nodeSize (memW s n) / 8 → memW post (n + 8 * k) = memW s (n + 8 * k)) ∧
      nodePath post n = nodePath s n ∧
      ((memW s n = 1 ∨ memW s n = 2) → KeyIn post Nd (memW post (n + 32)) (memW post (n + 40))) := by
    intro n hn
    obtain ⟨hk3, hal_n, hin_n, hw_n, _, _, hkey_n, _, _, _⟩ := hN.1 n hn
    have hhi_n : n + nodeSize (memW s n) ≤ 2 ^ 64 := by
      have := hin_n.2; dsimp [nodeIvl] at this; omega
    have hn8 : n % 8 = 0 := hw_n.1
    have hu_n : IvlUnhit s post (n, nodeSize (memW s n)) := by
      apply hu; unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodeIvl]⟩
    have hsz_ge32 : 32 ≤ nodeSize (memW s n) := by
      unfold nodeSize; split_ifs <;> omega
    have hw_k : ∀ k, k < nodeSize (memW s n) / 8 → memW post (n + 8 * k) = memW s (n + 8 * k) := by
      intro k hk
      have hsz8 : nodeSize (memW s n) % 8 = 0 := by unfold nodeSize; split_ifs <;> omega
      exact memW_eq_of_ivlUnhit hu_n (by omega) hhi_n ⟨by omega, by omega⟩
    have hw0 : memW post n = memW s n := by simpa using hw_k 0 (by omega)
    have hivl_eq : nodeIvl post n = nodeIvl s n := by simp [nodeIvl, hw0]
    have hpath_eq : nodePath post n = nodePath s n := by
      by_cases h12 : memW s n = 1 ∨ memW s n = 2
      · have hsz_ge56 : 56 ≤ nodeSize (memW s n) := by
          unfold nodeSize; rcases h12 with h1 | h2
          · simp [h1]
          · simp [h2]
        have hw32 : memW post (n + 32) = memW s (n + 32) := hw_k 4 (by omega)
        have hw40 : memW post (n + 40) = memW s (n + 40) := hw_k 5 (by omega)
        unfold nodePath
        rw [hw0, hw32, hw40]
      · unfold nodePath; rw [hw0]; simp [h12]
    exact ⟨hw0, hivl_eq, hw_k, hpath_eq, fun h12 => by
      have hsz_ge56 : 56 ≤ nodeSize (memW s n) := by
        unfold nodeSize; rcases h12 with h1 | h2
        · simp [h1]
        · simp [h2]
      have hw32 : memW post (n + 32) = memW s (n + 32) := hw_k 4 (by omega)
      have hw40 : memW post (n + 40) = memW s (n + 40) := hw_k 5 (by omega)
      rw [hw32, hw40]
      by_cases hlen0 : memW s (n + 40) = 0
      · exact Or.inl hlen0
      · rcases hkey_n h12 with h0 | ⟨hnib, hal_p, hin_p, hdisj_p⟩
        · exact Or.inl h0
        · right
          have hu_p : IvlUnhit s post (memW s (n + 32), memW s (n + 40)) := by
            have hp_ext : (memW s (n + 32), memW s (n + 40)) ∈ nodeExtents s Nd := by
              unfold nodeExtents
              refine List.mem_flatMap.2 ⟨n, hn, ?_⟩
              simp [nodePath, h12, hlen0]
            exact hu _ hp_ext
          have hhi_p : memW s (n + 32) + memW s (n + 40) ≤ 2 ^ 64 := by
            have := hin_p.2; omega
          refine ⟨fun k hk => ?_, hag.allocated hal_p, hin_p, ?_⟩
          · rw [memB_eq_of_ivlUnhit hu_p hbe hhi_p ⟨by omega, by omega⟩]
            exact hnib k hk
          · intro m hm
            have hm_ivl : nodeIvl post m = nodeIvl s m := by
              have hhm_hi : m + nodeSize (memW s m) ≤ 2 ^ 64 := by
                have := (hN.1 m hm).2.2.1.2; dsimp [nodeIvl] at this; omega
              have hm8 : m % 8 = 0 := (hN.1 m hm).2.2.2.1.1
              have hu_m : IvlUnhit s post (m, nodeSize (memW s m)) := by
                apply hu; unfold nodeExtents; exact List.mem_flatMap.2 ⟨m, hm, by simp [nodeIvl]⟩
              have hsz_m : 32 ≤ nodeSize (memW s m) := by unfold nodeSize; split_ifs <;> omega
              have hwm : memW post m = memW s m :=
                memW_eq_of_ivlUnhit hu_m hm8 hhm_hi ⟨by omega, by omega⟩
              simp [nodeIvl, hwm]
            rw [hm_ivl]
            exact hdisj_p m hm⟩
  constructor
  · refine ⟨fun n hn => ?_, fun n hn m hm hne => ?_⟩
    · obtain ⟨hk3, hal_n, hin_n, hw_n, hext, hbr, _, hn16, hn56, hn168⟩ := hN.1 n hn
      obtain ⟨hw0, hivl_eq, hw_k, _, hkey_post⟩ := hn_props n hn
      have hsz_ge32 : 32 ≤ nodeSize (memW s n) := by unfold nodeSize; split_ifs <;> omega
      have hw16 := hw_k 2 (by omega)
      rw [hw0, hivl_eq]
      refine ⟨hk3, hag.allocated hal_n, hin_n, wordsOK_transfer hgS hgP hw_n, ?_, ?_, hkey_post,
        by rw [hw16]; exact hn16, ?_, ?_⟩
      · intro h2
        have hsz : nodeSize (memW s n) = 56 := by unfold nodeSize; simp [h2]
        have hw48 := hw_k 6 (by omega)
        simpa only [Nat.mul_succ, Nat.mul_zero] using (by rw [hw48]; exact hext h2 : RootIn Nd (memW post (n + 48)))
      · intro h3 i hi
        have hsz : nodeSize (memW s n) = 176 := by unfold nodeSize; simp [h3]
        have hw_ch := hw_k (4 + i) (by omega)
        have hadd : n + 8 * (4 + i) = n + 32 + 8 * i := by omega
        rw [← hadd, hw_ch, hadd]
        exact hbr h3 i hi
      · intro h1
        have hsz : nodeSize (memW s n) = 64 := by unfold nodeSize; simp [h1]
        have hw56 := hw_k 7 (by omega)
        rw [hw56]; exact hn56 h1
      · intro h3
        have hsz : nodeSize (memW s n) = 176 := by unfold nodeSize; simp [h3]
        have hw168 := hw_k 21 (by omega)
        rw [hw168]; exact hn168 h3
    · rw [(hn_props n hn).2.1, (hn_props m hm).2.1]
      exact hN.2 n hn m hm hne
  · unfold nodeExtents
    apply List.flatMap_congr
    intro n hn
    rw [(hn_props n hn).2.1, (hn_props n hn).2.2.2.1]

theorem balRecords_eq_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S : List Nat} (hT : TablesTyped s S)
    (hbal_eq : globN post "bal_accounts" = globN s "bal_accounts")
    (hu : globN s "bal_accounts" ≠ 0 → ∀ i ∈ htabFootprint s (globN s "bal_accounts"), IvlUnhit s post i) :
    balRecords post = balRecords s := by
  unfold balRecords
  rw [hbal_eq]
  by_cases hbal : globN s "bal_accounts" = 0
  · simp [hbal]
  · simp only [hbal, ↓reduceIte]
    have hmem_S : globN s "bal_accounts" ∈ S := by
      rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
      · exact absurd h0 hbal
      · exact hm
    have hwf := (hT.2.1 _ hmem_S).1
    exact htabValues_eq_of_unhit hwf (hu hbal)

theorem lstObjects_eq_of_hdr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) (hF : FixedTyped s)
    {l esz : Nat}
    (hl_fix : l ≠ 0 → (l, 24) ∈ fixedObjects s)
    (hu_l : l ≠ 0 → IvlUnhit s post (l, 24)) :
    lstObjects post l esz = lstObjects s l esz ∧
    (l ≠ 0 → memW post (l + 8) = memW s (l + 8) ∧ memW post (l + 16) = memW s (l + 16)) := by
  by_cases hlz : l = 0
  · subst hlz; simp [lstObjects]
  · rcases hF.1 _ (hl_fix hlz) with h0 | ⟨hal, hw⟩
    · simp at h0
    have hhi := (ivl_allocated_bound hA hal).2
    have hl8 : l % 8 = 0 := hw.1
    have hu := hu_l hlz
    have hw0 : memW post l = memW s l := by
      simpa using memW_eq_of_ivlUnhit hu (by omega) hhi ⟨by omega, by omega⟩
    have hw8 : memW post (l + 8) = memW s (l + 8) :=
      memW_eq_of_ivlUnhit hu (by omega) hhi ⟨by omega, by omega⟩
    have hw16 : memW post (l + 16) = memW s (l + 16) :=
      memW_eq_of_ivlUnhit hu (by omega) hhi ⟨by omega, by omega⟩
    refine ⟨?_, fun _ => ⟨hw8, hw16⟩⟩
    unfold lstObjects
    simp [hlz, hw0, hw16]

theorem balObjects_eq_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {S : List Nat} (hT : TablesTyped s S) (hF : FixedTyped s)
    (hbal_eq : globN post "bal_accounts" = globN s "bal_accounts")
    (hm_low : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16)
    (hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, IvlUnhit s post i)
    (hu_bal : ∀ i ∈ balObjects s, IvlUnhit s post i) :
    balObjects post = balObjects s ∧
    (∀ ad ∈ balRecords post, memW post ad = memW s ad ∧ memW post (ad + 8) = memW s (ad + 8) ∧
      htabValues post (memW post ad) = htabValues s (memW s ad) ∧
      (∀ k ∈ ([16, 24, 32] : List Nat), LstOK post (memW post (ad + k))) ∧
      (∀ l ∈ htabValues post (memW post ad), LstOK post l)) := by
  have hrecs : balRecords post = balRecords s :=
    balRecords_eq_of_unhit hT hbal_eq (fun hnz => by
      rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
      · exact absurd h0 hnz
      · exact hu_tab _ hm)
  have hmem_fix_of_bal : ∀ i ∈ balObjects s, i ∈ fixedObjects s := fun i hi => by
    unfold fixedObjects; exact List.mem_append.2 (Or.inr hi)
  have hlst_helper : ∀ (l esz : Nat),
      (l ≠ 0 → (l, 24) ∈ balObjects s) →
      lstObjects post l esz = lstObjects s l esz ∧ (LstOK post l ↔ LstOK s l) := by
    intro l esz hmem_b
    by_cases hlz : l = 0
    · subst hlz
      refine ⟨rfl, ?_⟩
      unfold LstOK; simp [hm_low.1, hm_low.2]
    · obtain ⟨hl_eq, hw816⟩ := lstObjects_eq_of_hdr_unhit hA hF
        (fun hnz => hmem_fix_of_bal _ (hmem_b hnz))
        (fun hnz => hu_bal _ (hmem_b hnz))
      obtain ⟨hw8, hw16⟩ := hw816 hlz
      refine ⟨hl_eq, ?_⟩
      unfold LstOK; rw [hw8, hw16]
  have had_props : ∀ ad ∈ balRecords s,
      (∀ off ∈ ([0, 8, 16, 24, 32] : List Nat), memW post (ad + off) = memW s (ad + off)) ∧
      htabValues post (memW s ad) = htabValues s (memW s ad) ∧
      lstObjects post (memW s (ad + 16)) 40 = lstObjects s (memW s (ad + 16)) 40 ∧
      lstObjects post (memW s (ad + 24)) 16 = lstObjects s (memW s (ad + 24)) 16 ∧
      lstObjects post (memW s (ad + 32)) 24 = lstObjects s (memW s (ad + 32)) 24 ∧
      (∀ k ∈ ([16, 24, 32] : List Nat), LstOK post (memW s (ad + k)) ↔ LstOK s (memW s (ad + k))) ∧
      (∀ l ∈ htabValues s (memW s ad), lstObjects post l 40 = lstObjects s l 40 ∧ (LstOK post l ↔ LstOK s l)) := by
    intro ad had
    have had_bal : (ad, 40) ∈ balObjects s := by
      unfold balObjects
      exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
    rcases hF.1 _ (hmem_fix_of_bal _ had_bal) with h0 | ⟨hal_ad, hw_ad⟩
    · simp at h0
    have hhi_ad := (ivl_allocated_bound hA hal_ad).2
    have had8 : ad % 8 = 0 := hw_ad.1
    have hoff_eq : ∀ off ∈ ([0, 8, 16, 24, 32] : List Nat), memW post (ad + off) = memW s (ad + off) := by
      intro off hoff
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl | rfl | rfl <;>
        exact memW_eq_of_ivlUnhit (hu_bal _ had_bal) (by omega) hhi_ad ⟨by omega, by omega⟩
    have had_T := hT.2.2.2.2.2.2.2.2.2.1 ad had
    have hvals_ad : htabValues post (memW s ad) = htabValues s (memW s ad) :=
      htabValues_eq_of_unhit (hT.2.1 _ had_T.1).1 (hu_tab _ had_T.1)
    have h16 := hlst_helper (memW s (ad + 16)) 40 (fun hnz => by
      unfold balObjects; exact List.mem_flatMap.2 ⟨ad, had, by simp [lstObjects, hnz]⟩)
    have h24 := hlst_helper (memW s (ad + 24)) 16 (fun hnz => by
      unfold balObjects; exact List.mem_flatMap.2 ⟨ad, had, by simp [lstObjects, hnz]⟩)
    have h32 := hlst_helper (memW s (ad + 32)) 24 (fun hnz => by
      unfold balObjects; exact List.mem_flatMap.2 ⟨ad, had, by simp [lstObjects, hnz]⟩)
    refine ⟨hoff_eq, hvals_ad, h16.1, h24.1, h32.1, ?_, ?_⟩
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      · exact h16.2
      · exact h24.2
      · exact h32.2
    · intro l hl
      exact hlst_helper l 40 (fun hnz => by
        unfold balObjects
        refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
        apply List.mem_cons_of_mem
        apply List.mem_append.2; right
        exact List.mem_flatMap.2 ⟨l, hl, by simp [lstObjects, hnz]⟩)
  constructor
  · unfold balObjects
    rw [hrecs]
    apply List.flatMap_congr
    intro ad had
    obtain ⟨hoff_eq, hvals_ad, h16, h24, h32, _, hllst⟩ := had_props ad had
    have h0 := hoff_eq 0 (by simp); simp only [Nat.add_zero] at h0
    have hw16 := hoff_eq 16 (by simp)
    have hw24 := hoff_eq 24 (by simp)
    have hw32 := hoff_eq 32 (by simp)
    have htail : (htabValues post (memW post ad)).flatMap (fun l => lstObjects post l 40) =
        (htabValues s (memW s ad)).flatMap (fun l => lstObjects s l 40) := by
      rw [h0, hvals_ad]
      apply List.flatMap_congr
      intro l hl; exact (hllst l hl).1
    rw [htail, hw16, hw24, hw32, h16, h24, h32]
  · intro ad had
    rw [hrecs] at had
    obtain ⟨hoff_eq, hvals_ad, _, _, _, hkl, hll⟩ := had_props ad had
    have had_T := hT.2.2.2.2.2.2.2.2.2.1 ad had
    have h0 := hoff_eq 0 (by simp); simp only [Nat.add_zero] at h0
    have h8 := hoff_eq 8 (by simp)
    refine ⟨h0, h8, by rw [h0, hvals_ad], ?_, ?_⟩
    · intro k hk
      have hk_in : k ∈ ([0, 8, 16, 24, 32] : List Nat) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
        rcases hk with rfl | rfl | rfl <;> simp
      rw [hoff_eq k hk_in]
      exact (hkl k hk).2 (had_T.2.2.1 k hk)
    · intro l hl
      rw [h0, hvals_ad] at hl
      exact (hll l hl).2.2 (had_T.2.2.2 l hl)

def WorldGlobalsSame {F : Type} (s post : PanSemStateFiniteExact 64 F) : Prop :=
  (∀ gn ∈ globalBuffers, globN post gn.1 = globN s gn.1) ∧
  (∀ g ∈ globalTableRoots, globN post g = globN s g) ∧
  globN post "journal" = globN s "journal" ∧
  globN post "journal_cap" = globN s "journal_cap" ∧
  globN post "journal_n" = globN s "journal_n"

theorem worldGlobalsSame_of_globals_eq {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hg : post.globals = s.globals) : WorldGlobalsSame s post := by
  refine ⟨fun _ _ => by simp [globN, hg], fun _ _ => by simp [globN, hg],
    by simp [globN, hg], by simp [globN, hg], by simp [globN, hg]⟩

theorem blockOutObjects_eq_of_bo_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) (hF : FixedTyped s) (hbo_eq : globN post "bo" = globN s "bo")
    (hbo_lst_ok : globN s "bo" ≠ 0 → ∀ k ∈ ([40, 72] : List Nat), memW s (globN s "bo" + k) ≠ 0 →
      LstOK s (memW s (globN s "bo" + k)))
    (hu_bo : globN s "bo" ≠ 0 → IvlUnhit s post (globN s "bo", 88))
    (hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 → IvlUnhit s post i) :
    blockOutObjects post = blockOutObjects s ∧
    (globN post "bo" ≠ 0 → ∀ k ∈ ([40, 72] : List Nat), memW post (globN post "bo" + k) ≠ 0 →
      LstOK post (memW post (globN post "bo" + k))) := by
  by_cases hbo : globN s "bo" = 0
  · constructor
    · unfold blockOutObjects; simp [hbo_eq, hbo]
    · intro hnz; rw [hbo_eq] at hnz; exact absurd hbo hnz
  · have hkw : ∀ k ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
        memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := by
      intro k hk
      have hk_in : k % 8 = 0 ∧ k + 8 ≤ 88 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      simpa [hbo_eq] using rec_word_eq_of_unhit hA hF "bo" 88 (by simp [typedRecords])
        hbo_eq hbo (hu_bo hbo) hk_in.1 hk_in.2
    have hlst_hdr : ∀ k ∈ ([40, 72] : List Nat), memW s (globN s "bo" + k) ≠ 0 →
        ∀ off ∈ ([0, 8, 16] : List Nat),
          memW post (memW s (globN s "bo" + k) + off) = memW s (memW s (globN s "bo" + k) + off) := by
      intro k hk hknz off hoff
      have hl_bo : (memW s (globN s "bo" + k), 24) ∈ blockOutObjects s := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> simp [blockOutObjects, hbo, hknz]
      have hl_fix : (memW s (globN s "bo" + k), 24) ∈ fixedObjects s := by
        unfold fixedObjects
        exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hl_bo)))
      rcases hF.1 _ hl_fix with h0 | ⟨hal, hw⟩
      · simp at h0
      have hhi := (ivl_allocated_bound hA hal).2
      have hl8 : (memW s (globN s "bo" + k)) % 8 = 0 := hw.1
      have hu := hu_bo_lst _ hl_bo rfl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl <;>
        exact memW_eq_of_ivlUnhit hu (by omega) hhi ⟨by omega, by omega⟩
    constructor
    · unfold blockOutObjects
      simp only [hbo_eq, hbo, false_or,
        hkw 24 (by simp), hkw 32 (by simp), hkw 40 (by simp),
        hkw 56 (by simp), hkw 72 (by simp), hkw 80 (by simp)]
      congr 1; congr 1
      · by_cases h40 : memW s (globN s "bo" + 40) = 0
        · simp [h40]
        · have h0 := hlst_hdr 40 (by simp) h40 0 (by simp)
          have h16 := hlst_hdr 40 (by simp) h40 16 (by simp)
          simp only [Nat.add_zero] at h0
          simp [h40, h0, h16]
      · by_cases h72 : memW s (globN s "bo" + 72) = 0
        · simp [h72]
        · have h0 := hlst_hdr 72 (by simp) h72 0 (by simp)
          have h16 := hlst_hdr 72 (by simp) h72 16 (by simp)
          simp only [Nat.add_zero] at h0
          simp [h72, h0, h16]
    · intro _ k hk hknz
      rw [hbo_eq] at hknz ⊢
      have hk_in : k ∈ ([24, 32, 40, 56, 72, 80] : List Nat) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
        rcases hk with rfl | rfl <;> simp
      rw [hkw k hk_in] at hknz ⊢
      unfold LstOK
      rw [hlst_hdr k hk hknz 8 (by simp), hlst_hdr k hk hknz 16 (by simp)]
      exact hbo_lst_ok hbo k hk hknz

theorem worldRoleSlots_eq_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {S : List Nat} (hT : TablesTyped s S) (hF : FixedTyped s)
    (hgs : WorldGlobalsSame s post)
    (hm_low : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16)
    (hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, IvlUnhit s post i)
    (hu_ws : globN s "ws" ≠ 0 → IvlUnhit s post (globN s "ws", 40))
    (hu_bs : globN s "bs" ≠ 0 → IvlUnhit s post (globN s "bs", 80))
    (hu_ts : globN s "ts" ≠ 0 → IvlUnhit s post (globN s "ts", 72))
    (hu_bal : ∀ i ∈ balObjects s, IvlUnhit s post i) :
    worldRoleSlots post = worldRoleSlots s := by
  have hws_g : globN post "ws" = globN s "ws" := hgs.1 ("ws", 40) (by simp [globalBuffers])
  have hbs_g : globN post "bs" = globN s "bs" := hgs.1 ("bs", 80) (by simp [globalBuffers])
  have hts_g : globN post "ts" = globN s "ts" := hgs.1 ("ts", 72) (by simp [globalBuffers])
  have hba_g : globN post "bal_accounts" = globN s "bal_accounts" := hgs.2.1 "bal_accounts" (by simp [globalTableRoots])
  have hbia_g : globN post "bal_idx_accts" = globN s "bal_idx_accts" := hgs.2.1 "bal_idx_accts" (by simp [globalTableRoots])
  have hbis_g : globN post "bal_idx_stor" = globN s "bal_idx_stor" := hgs.2.1 "bal_idx_stor" (by simp [globalTableRoots])
  have hrec_ws : recRoles post "ws" [(16, "ws+16"), (32, "ws+32")] =
      recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] := by
    unfold recRoles
    by_cases h : globN s "ws" = 0
    · simp [hws_g, h]
    · simp only [hws_g, h, ↓reduceIte]
      apply List.map_congr_left
      intro ⟨k, r⟩ hkr
      have hk : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
        rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
      have hw := rec_word_eq_of_unhit hA hF "ws" 40 (by simp [typedRecords]) hws_g h (hu_ws h) hk.1 hk.2
      simp only [hws_g] at hw
      simp [hw]
  have hrec_bs : recRoles post "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
      (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] =
      recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
      (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] := by
    unfold recRoles
    by_cases h : globN s "bs" = 0
    · simp [hbs_g, h]
    · simp only [hbs_g, h, ↓reduceIte]
      apply List.map_congr_left
      intro ⟨k, r⟩ hkr
      have hk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
        rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
      have hw := rec_word_eq_of_unhit hA hF "bs" 80 (by simp [typedRecords]) hbs_g h (hu_bs h) hk.1 hk.2
      simp only [hbs_g] at hw
      simp [hw]
  have hrec_ts : recRoles post "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
      (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] =
      recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
      (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] := by
    unfold recRoles
    by_cases h : globN s "ts" = 0
    · simp [hts_g, h]
    · simp only [hts_g, h, ↓reduceIte]
      apply List.map_congr_left
      intro ⟨k, r⟩ hkr
      have hk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
        rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
      have hw := rec_word_eq_of_unhit hA hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) hk.1 hk.2
      simp only [hts_g] at hw
      simp [hw]
  have hnest_bs : nestRoles post "bs" "bs.inner" = nestRoles s "bs" "bs.inner" := by
    unfold nestRoles
    by_cases h : globN s "bs" = 0
    · simp [hbs_g, h]
    · have hw32 := rec_word_eq_of_unhit hA hF "bs" 80 (by simp [typedRecords]) hbs_g h (hu_bs h) (k := 32) (by omega) (by omega)
      simp only [hbs_g] at hw32 ⊢
      simp only [h, ↓reduceIte, hw32]
      by_cases h32 : memW s (globN s "bs" + 32) = 0
      · simp [h32]
      · simp only [h32, ↓reduceIte]
        have hmS : memW s (globN s "bs" + 32) ∈ S := by
          rcases hT.2.2.2.2.1 32 (by simp [bsTableSlots]) h with h0 | hm
          · exact absurd h0 h32
          · exact hm
        rw [htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_tab _ hmS)]
  have hnest_ts : nestRoles post "ts" "ts.inner" = nestRoles s "ts" "ts.inner" := by
    unfold nestRoles
    by_cases h : globN s "ts" = 0
    · simp [hts_g, h]
    · have hw32 := rec_word_eq_of_unhit hA hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 32) (by omega) (by omega)
      simp only [hts_g] at hw32 ⊢
      simp only [h, ↓reduceIte, hw32]
      by_cases h32 : memW s (globN s "ts" + 32) = 0
      · simp [h32]
      · simp only [h32, ↓reduceIte]
        have hmS : memW s (globN s "ts" + 32) ∈ S := by
          rcases hT.2.2.2.2.2.1 32 (by simp [tsTableSlots]) h with h0 | hm
          · exact absurd h0 h32
          · exact hm
        rw [htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_tab _ hmS)]
  have hrecs_bal := balRecords_eq_of_unhit hT hba_g (fun hnz => by
    rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
    · exact absurd h0 hnz
    · exact hu_tab _ hm)
  have hbal_part := (balObjects_eq_of_unhit hA hT hF hba_g hm_low hu_tab hu_bal).2
  unfold worldRoleSlots
  rw [hrec_ws, hrec_bs, hrec_ts, hba_g, hbia_g, hbis_g, hnest_bs, hnest_ts, hrecs_bal]
  congr 1; congr 1
  apply List.flatMap_congr
  intro ad had
  rw [← hrecs_bal] at had
  obtain ⟨h0, h8, _⟩ := hbal_part ad had
  rw [h0, h8]

theorem journalRoleSlots_eq_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post)
    (hA : ArenaOK s) (hag : AllocatorGrows s post)
    {S S' : List Nat} (hsub : ∀ x ∈ S, x ∈ S')
    (hJ : JournalTyped s S) (hF : FixedTyped s)
    (hgs : WorldGlobalsSame s post)
    (hu_ts : globN s "ts" ≠ 0 → IvlUnhit s post (globN s "ts", 72))
    (hu_jr : globN s "journal_cap" ≠ 0 → IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap")) :
    journalRoleSlots post = journalRoleSlots s ∧ JournalTyped post S' := by
  have hts_g : globN post "ts" = globN s "ts" := hgs.1 ("ts", 72) (by simp [globalBuffers])
  have hj_g := hgs.2.2.1
  have hjc_g := hgs.2.2.2.1
  have hjn_g := hgs.2.2.2.2
  have hrole_eq : ∀ t, journalRole post t = journalRole s t := fun t => by
    unfold journalRole
    by_cases h : globN s "ts" = 0
    · simp [hts_g, h]
    · have hw16 := rec_word_eq_of_unhit hA hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 16) (by omega) (by omega)
      have hw32 := rec_word_eq_of_unhit hA hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 32) (by omega) (by omega)
      have hw48 := rec_word_eq_of_unhit hA hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 48) (by omega) (by omega)
      have hw64 := rec_word_eq_of_unhit hA hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 64) (by omega) (by omega)
      simp only [hts_g] at hw16 hw32 hw48 hw64 ⊢
      rw [hw16, hw32, hw48, hw64]
  have hj_cells : ∀ i, i < globN s "journal_n" →
      memW post (globN s "journal" + 32 * i) = memW s (globN s "journal" + 32 * i) ∧
      memW post (globN s "journal" + 32 * i + 16) = memW s (globN s "journal" + 32 * i + 16) ∧
      memW post (globN s "journal" + 32 * i + 24) = memW s (globN s "journal" + 32 * i + 24) := by
    intro i hi
    have hcnz : globN s "journal_cap" ≠ 0 := by have := hJ.1; omega
    rcases hJ.2.2.1 with h0 | ⟨hal, hwords⟩
    · exact absurd h0 hcnz
    · have hhi := (ivl_allocated_bound hA hal).2
      have hj8 : (globN s "journal") % 8 = 0 := hwords.1
      have huj := hu_jr hcnz
      have hle : i < globN s "journal_cap" := lt_of_lt_of_le hi hJ.1
      refine ⟨?_, ?_, ?_⟩
      · exact memW_eq_of_ivlUnhit huj (by omega) hhi ⟨by omega, by omega⟩
      · exact memW_eq_of_ivlUnhit huj (by omega) hhi ⟨by omega, by omega⟩
      · exact memW_eq_of_ivlUnhit huj (by omega) hhi ⟨by omega, by omega⟩
  constructor
  · unfold journalRoleSlots
    rw [hjn_g, hj_g]
    apply List.flatMap_congr
    intro i hi
    rw [List.mem_range] at hi
    obtain ⟨hc0, hc16, hc24⟩ := hj_cells i hi
    simp only [hc0, hc16, hc24, hrole_eq]
  · unfold JournalTyped
    rw [hjn_g, hjc_g, hj_g]
    refine ⟨hJ.1, hJ.2.1, ?_, ?_⟩
    · rcases hJ.2.2.1 with h0 | ⟨hal, hwords⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hag.allocated hal, wordsOK_transfer hgS hgP hwords⟩
    · intro i hi
      rw [(hj_cells i hi).1]
      exact hsub _ (hJ.2.2.2 i hi)

theorem fixedObjects_eq_of_parts {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgs : WorldGlobalsSame s post)
    (hbo_obj : blockOutObjects post = blockOutObjects s)
    (hbal_obj : balObjects post = balObjects s) :
    fixedObjects post = fixedObjects s := by
  unfold fixedObjects
  rw [hbo_obj, hbal_obj, hgs.2.2.1, hgs.2.2.2.1]
  congr 3
  apply List.map_congr_left
  intro gn hgn
  rw [hgs.1 gn hgn]

theorem fixedTyped_transfer {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post) (hag : AllocatorGrows s post)
    (hF : FixedTyped s) (hfix_eq : fixedObjects post = fixedObjects s) :
    FixedTyped post := by
  unfold FixedTyped
  rw [hfix_eq]
  refine ⟨fun i hi => ?_, hF.2⟩
  rcases hF.1 i hi with h0 | ⟨hal, hwords⟩
  · exact Or.inl h0
  · exact Or.inr ⟨hag.allocated hal, wordsOK_transfer hgS hgP hwords⟩

theorem worldTypedWith_store_word_disj {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaReady s) {x : BitVec 64}
    (hx_dom : s.memaddrs x)
    (hpost : post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ post.shMemaddrs = s.shMemaddrs ∧
      post.baseAddr = s.baseAddr ∧ post.be = s.be ∧ post.globals = s.globals ∧
      ∀ a : BitVec 64, a ≠ x → post.memory a = s.memory a)
    {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    (hdisj : ∀ j ∈ worldTypedIvls s S Nd, Disj j (x.toNat, 8)) :
    ArenaReady post ∧
    WorldTypedWith post S Nd ∧
    fixedObjects post = fixedObjects s ∧
    nodeExtents post Nd = nodeExtents s Nd ∧
    worldRoleSlots post = worldRoleSlots s ∧
    journalRoleSlots post = journalRoleSlots s ∧
    (∀ t ∈ S, (∀ k, k < 11 → hdr post t k = hdr s t k) ∧ htabFootprint post t = htabFootprint s t) ∧
    worldTableRefs post S = worldTableRefs s S := by
  obtain ⟨hT, hJ, hF, hTr⟩ := hW
  have h264 : heapEnd ≤ 2 ^ 64 := by decide
  have hgP : GuestInv post := guestInv_congr hpost.1 hpost.2.1 hpost.2.2.1 hpost.2.2.2.1 hAs.1
  have hAp : ArenaReady post := by
    refine ⟨hgP, ?_⟩
    unfold ArenaOK; simp only [globN_congr hpost.2.2.2.2.2.1]; exact hAs.2
  have hag : AllocatorGrows s post := by
    unfold AllocatorGrows; simp only [globN_congr hpost.2.2.2.2.2.1]; exact ⟨le_rfl, le_rfl⟩
  have hgs := worldGlobalsSame_of_globals_eq hpost.2.2.2.2.2.1
  have hx_ord : x.toNat % 8 = 0 ∧ sourceBase ≤ x.toNat ∧ x.toNat < heapEnd := by
    rw [hAs.1.memaddrs, ordinaryDomain_iff] at hx_dom; exact hx_dom
  have hsb : 24 < sourceBase := by decide
  have hm_low : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 := by
    obtain ⟨_, hx_lo, _⟩ := hx_ord
    constructor
    · have hne : BitVec.ofNat 64 8 ≠ x := by
        rintro rfl; change sourceBase ≤ 8 at hx_lo; omega
      unfold memW; rw [hpost.2.2.2.2.2.2 _ hne]
    · have hne : BitVec.ofNat 64 16 ≠ x := by
        rintro rfl; change sourceBase ≤ 16 at hx_lo; omega
      unfold memW; rw [hpost.2.2.2.2.2.2 _ hne]
  have hunhit : ∀ i ∈ worldTypedIvls s S Nd, IvlUnhit s post i := fun i hi =>
    ivlUnhit_of_single_cell_disj hpost.2.2.2.2.2.2 (hdisj i hi)
  have hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, IvlUnhit s post i := fun t ht i hi =>
    hunhit i (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; left
      exact List.mem_flatMap.2 ⟨t, ht, hi⟩)
  have hu_ws : globN s "ws" ≠ 0 → IvlUnhit s post (globN s "ws", 40) := fun hnz =>
    hunhit _ (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; right
      exact List.mem_map.2 ⟨("ws", 40), by simp [typedRecords], by simp [hnz]⟩)
  have hu_bs : globN s "bs" ≠ 0 → IvlUnhit s post (globN s "bs", 80) := fun hnz =>
    hunhit _ (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; right
      exact List.mem_map.2 ⟨("bs", 80), by simp [typedRecords], by simp [hnz]⟩)
  have hu_ts : globN s "ts" ≠ 0 → IvlUnhit s post (globN s "ts", 72) := fun hnz =>
    hunhit _ (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; right
      exact List.mem_map.2 ⟨("ts", 72), by simp [typedRecords], by simp [hnz]⟩)
  have hu_bo : globN s "bo" ≠ 0 → IvlUnhit s post (globN s "bo", 88) := fun hnz =>
    hunhit _ (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; right
      exact List.mem_map.2 ⟨("bo", 88), by simp [typedRecords], by simp [hnz]⟩)
  have hu_jr : globN s "journal_cap" ≠ 0 → IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap") := fun hnz =>
    hunhit _ (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; right; simp [hnz])
  have hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 → IvlUnhit s post i := fun i hi _ =>
    hunhit i (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
      exact hi)
  have hu_bal : ∀ i ∈ balObjects s, IvlUnhit s post i := fun i hi =>
    hunhit i (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; right
      exact hi)
  have hu_nd : ∀ o ∈ nodeExtents s Nd, IvlUnhit s post o := fun o ho =>
    hunhit o (by unfold worldTypedIvls; exact List.mem_append.2 (Or.inr ho))
  have hbo_g : globN post "bo" = globN s "bo" := hgs.1 ("bo", 88) (by simp [globalBuffers])
  have hws_g : globN post "ws" = globN s "ws" := hgs.1 ("ws", 40) (by simp [globalBuffers])
  have hbs_g : globN post "bs" = globN s "bs" := hgs.1 ("bs", 80) (by simp [globalBuffers])
  have hts_g : globN post "ts" = globN s "ts" := hgs.1 ("ts", 72) (by simp [globalBuffers])
  have hba_g : globN post "bal_accounts" = globN s "bal_accounts" := hgs.2.1 "bal_accounts" (by simp [globalTableRoots])
  have hbo_part := blockOutObjects_eq_of_bo_unhit hAs.2 hF hbo_g hT.2.2.2.2.2.2.2.2.2.2.1 hu_bo hu_bo_lst
  have hbal_part := balObjects_eq_of_unhit hAs.2 hT hF hba_g hm_low hu_tab hu_bal
  have hfix_eq := fixedObjects_eq_of_parts hgs hbo_part.1 hbal_part.1
  have hF_post := fixedTyped_transfer hAs.1 hAp.1 hag hF hfix_eq
  have hjr_part := journalRoleSlots_eq_of_unhit hAs.1 hAp.1 hAs.2 hag (fun _ hx => hx) hJ hF hgs hu_ts hu_jr
  have hwrs_eq := worldRoleSlots_eq_of_unhit hAs.2 hT hF hgs hm_low hu_tab hu_ws hu_bs hu_ts hu_bal
  have hnd_part := nodeHeap_congr_unhit hAs.1 hAp.1 hpost.2.2.2.2.1 hag hTr.1 hu_nd
  have htab_fp_hdr : ∀ t ∈ S, (∀ k, k < 11 → hdr post t k = hdr s t k) ∧ htabFootprint post t = htabFootprint s t := by
    intro t ht
    have hwf := (hT.2.1 t ht).1
    have ht_fp : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
    have ht8 : t % 8 = 0 := (hwf.1 _ ht_fp).2.1
    have hhi : t + 88 ≤ 2 ^ 64 := by have := (hwf.1 _ ht_fp).1.2; omega
    exact htabFootprint_eq_of_hdr_unhit ht8 hhi (hu_tab t ht _ ht_fp)
  have hT_post : TablesTyped post S := by
    obtain ⟨hndS, hTt, hTp, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, hboT, hroles⟩ := hT
    refine ⟨hndS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo_part.2, ?_⟩
    · intro t ht
      rw [(htab_fp_hdr t ht).2, hfix_eq]
      exact ⟨htabWF_congr_unhit hAs.1 hAp.1 (hTt t ht).1 (hu_tab t ht),
        fun i hi => ⟨hag.allocated ((hTt t ht).2 i hi).1, ((hTt t ht).2 i hi).2⟩⟩
    · intro t ht u hu_mem hne
      rw [(htab_fp_hdr t ht).2, (htab_fp_hdr u hu_mem).2]
      exact hTp t ht u hu_mem hne
    · intro k hk hnz
      rw [hws_g] at hnz
      have hwk : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g hnz (hu_ws hnz) hwk.1 hwk.2]
      exact hwsR k hk hnz
    · intro k hk hnz
      rw [hbs_g] at hnz
      have hbk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g hnz (hu_bs hnz) hbk.1 hbk.2]
      exact hbsR k hk hnz
    · intro k hk hnz
      rw [hts_g] at hnz
      have htk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g hnz (hu_ts hnz) htk.1 htk.2]
      exact htsR k hk hnz
    · intro g hg
      rw [hgs.2.1 g hg]; exact hgR g hg
    · intro hnz hm
      rw [hbs_g] at hnz
      have hw32 := rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g hnz (hu_bs hnz) (k := 32) (by omega) (by omega)
      rw [hw32] at hm ⊢
      exact htabValuesIn_congr_unhit (hTt _ hm).1 (hu_tab _ hm) (fun _ hx => hx) (hbsN hnz hm)
    · intro hnz hm
      rw [hts_g] at hnz
      have hw32 := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g hnz (hu_ts hnz) (k := 32) (by omega) (by omega)
      rw [hw32] at hm ⊢
      exact htabValuesIn_congr_unhit (hTt _ hm).1 (hu_tab _ hm) (fun _ hx => hx) (htsN hnz hm)
    · intro ad had
      obtain ⟨h0, h8, _, hkl, hll⟩ := hbal_part.2 ad had
      have hrecs := balRecords_eq_of_unhit ⟨hndS, hTt, hTp, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, hboT, hroles⟩
        hba_g (fun hnz => by
          rcases hgR "bal_accounts" (by simp [globalTableRoots]) with h0' | hm
          · exact absurd h0' hnz
          · exact hu_tab _ hm)
      rw [hrecs] at had
      have had_old := hbalT ad had
      refine ⟨by rw [h0]; exact had_old.1, by rw [h8]; exact had_old.2.1, hkl, hll⟩
    · unfold RolesOK at hroles ⊢
      rw [hwrs_eq, hjr_part.1]
      refine ⟨fun a ha => ?_, hroles.2.1, hroles.2.2⟩
      obtain ⟨haS, hak⟩ := hroles.1 a ha
      rw [(htab_fp_hdr a.1 haS).1 0 (by omega)]
      exact ⟨haS, hak⟩
  have hTr_post : TriesTypedWith post S Nd := by
    refine ⟨hnd_part.1, ?_, ?_⟩
    · intro o ho
      rw [hnd_part.2] at ho
      rw [hfix_eq]
      refine ⟨fun t ht i hi => ?_, (hTr.2.1 o ho).2⟩
      rw [(htab_fp_hdr t ht).2] at hi
      exact (hTr.2.1 o ho).1 t ht i hi
    · intro hnz
      rw [hws_g] at hnz
      have hw24 := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g hnz (hu_ws hnz) (k := 24) (by omega) (by omega)
      have hw32 := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g hnz (hu_ws hnz) (k := 32) (by omega) (by omega)
      rw [hw24, hw32]
      obtain ⟨hr24, hr32⟩ := hTr.2.2 hnz
      refine ⟨hr24, fun hm i hi => ?_⟩
      have hwf32 := (hT.2.1 _ hm).1
      have hu32 := hu_tab _ hm
      have hh32 := htab_fp_hdr _ hm
      rw [hh32.1 3 (by omega)] at hi
      have hvals := htabValues_eq_of_unhit hwf32 hu32
      have hget : (htabValues post (memW s (globN s "ws" + 32)))[i]? =
          (htabValues s (memW s (globN s "ws" + 32)))[i]? := by rw [hvals]
      simp only [htabValues, List.getElem?_map, List.getElem?_range, hh32.1 3 (by omega), hi,
        Option.map_some, Option.some.injEq] at hget
      rw [hget]
      exact hr32 hm i hi
  have hworldRefs_eq : worldTableRefs post S = worldTableRefs s S := by
    unfold worldTableRefs recordSlots
    have hglob_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, hpost.2.2.2.2.2.1]
    have hrecs_bal := balRecords_eq_of_unhit hT hba_g (fun hnz => by
      rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0' | hm
      · exact absurd h0' hnz
      · exact hu_tab _ hm)
    have hws_sl : (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW post (globN s "ws" + k)) =
        (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW s (globN s "ws" + k)) := by
      split
      · rfl
      · rename_i hnz
        apply List.map_congr_left; intro k hk
        have hwk : k % 8 = 0 ∧ k + 8 ≤ 40 := by
          simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl <;> omega
        simpa [hws_g] using rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g hnz (hu_ws hnz) hwk.1 hwk.2
    have hbs_sl : (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW post (globN s "bs" + k)) =
        (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW s (globN s "bs" + k)) := by
      split
      · rfl
      · rename_i hnz
        apply List.map_congr_left; intro k hk
        have hbk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
          simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
        simpa [hbs_g] using rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g hnz (hu_bs hnz) hbk.1 hbk.2
    have hts_sl : (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW post (globN s "ts" + k)) =
        (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW s (globN s "ts" + k)) := by
      split
      · rfl
      · rename_i hnz
        apply List.map_congr_left; intro k hk
        have htk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
          simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
        simpa [hts_g] using rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g hnz (hu_ts hnz) htk.1 htk.2
    have hnest_bs : (if globN s "bs" ≠ 0 ∧ memW post (globN s "bs" + 32) ∈ S then htabValues post (memW post (globN s "bs" + 32)) else []) =
        (if globN s "bs" ≠ 0 ∧ memW s (globN s "bs" + 32) ∈ S then htabValues s (memW s (globN s "bs" + 32)) else []) := by
      by_cases hnz : globN s "bs" = 0
      · simp [hnz]
      · have hw32 : memW post (globN s "bs" + 32) = memW s (globN s "bs" + 32) := by
          simpa [hbs_g] using rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g hnz (hu_bs hnz) (k := 32) (by omega) (by omega)
        rw [hw32]
        by_cases hmS : memW s (globN s "bs" + 32) ∈ S
        · simp [hnz, hmS, htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_tab _ hmS)]
        · simp [hnz, hmS]
    have hnest_ts : (if globN s "ts" ≠ 0 ∧ memW post (globN s "ts" + 32) ∈ S then htabValues post (memW post (globN s "ts" + 32)) else []) =
        (if globN s "ts" ≠ 0 ∧ memW s (globN s "ts" + 32) ∈ S then htabValues s (memW s (globN s "ts" + 32)) else []) := by
      by_cases hnz : globN s "ts" = 0
      · simp [hnz]
      · have hw32 : memW post (globN s "ts" + 32) = memW s (globN s "ts" + 32) := by
          simpa [hts_g] using rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g hnz (hu_ts hnz) (k := 32) (by omega) (by omega)
        rw [hw32]
        by_cases hmS : memW s (globN s "ts" + 32) ∈ S
        · simp [hnz, hmS, htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_tab _ hmS)]
        · simp [hnz, hmS]
    have hbal_fl : (balRecords s).flatMap (fun ad => [memW post ad, memW post (ad + 8)]) =
        (balRecords s).flatMap (fun ad => [memW s ad, memW s (ad + 8)]) := by
      apply List.flatMap_congr; intro ad had
      rw [← hrecs_bal] at had
      obtain ⟨h0, h8, _⟩ := hbal_part.2 ad had
      rw [h0, h8]
    have hjrn_mp : (List.range (globN s "journal_n")).map (fun k => memW post (globN s "journal" + 32 * k)) =
        (List.range (globN s "journal_n")).map (fun k => memW s (globN s "journal" + 32 * k)) := by
      apply List.map_congr_left; intro k hk
      rw [List.mem_range] at hk
      have hcnz : globN s "journal_cap" ≠ 0 := by have := hJ.1; omega
      rcases hJ.2.2.1 with h0 | ⟨hal, hwords⟩
      · exact absurd h0 hcnz
      · have hhi := (ivl_allocated_bound hAs.2 hal).2
        have hj8 : (globN s "journal") % 8 = 0 := hwords.1
        exact memW_eq_of_ivlUnhit (hu_jr hcnz) (by omega) hhi ⟨by have := hJ.1; omega, by have := hJ.1; omega⟩
    dsimp only
    have hg_map : globalTableRoots.map (globN post) = globalTableRoots.map (globN s) := by
      simp only [globalTableRoots, List.map, hglob_eq]
    simp only [hglob_eq, hrecs_bal, hg_map]
    rw [hws_sl, hbs_sl, hts_sl, hnest_bs, hnest_ts, hbal_fl, hjrn_mp]
  exact ⟨hAp, ⟨hT_post, hjr_part.2, hF_post, hTr_post⟩, hfix_eq, hnd_part.2, hwrs_eq, hjr_part.1,
    htab_fp_hdr, hworldRefs_eq⟩

/-! ## 3. `EvmInv` preservation across `cur_cont + 24 := snapshot` and `EvmAvoids` for global buffers -/

theorem frameWF_bounds {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat} {ec : Ivl}
    (hFW : FrameWF s S ec) :
    ec.1 + 280 ≤ 2 ^ 64 ∧ ec.2 + 104 ≤ 2 ^ 64 ∧ memW s (ec.1 + 88) + 24 ≤ 2 ^ 64 := by
  have hscr := hFW.1
  have he1 := (hscr (ec.1, 280) (by simp)).1
  have he2 := (hscr (ec.2, 104) (by simp)).1
  have he88 := (hscr (memW s (ec.1 + 88), 24) (by simp)).1
  have hse : scratchEnd ≤ 2 ^ 64 := by decide
  exact ⟨le_trans he1.2 hse, le_trans he2.2 hse, le_trans he88.2 hse⟩

theorem logEntryOK_transfer {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post)
    (hhp : globN post "heap_ptr" = globN s "heap_ptr")
    (hA : ArenaOK s)
    (hm : ∀ a : Nat, a < heapLimit → memW post a = memW s a)
    {log : Nat} (hl : LogEntryOK s log) :
    LogEntryOK post log := by
  obtain ⟨hw, hin, h16, h32, hi0, hi8, hi24⟩ := hl
  have hlim : globN s "heap_ptr" ≤ heapLimit := hA.2.1
  have h40 : log + 40 ≤ heapLimit := le_trans hin.2 hlim
  have hw0 : memW post log = memW s log := hm log (by omega)
  have hw8 : memW post (log + 8) = memW s (log + 8) := hm (log + 8) (by omega)
  have hw16 : memW post (log + 16) = memW s (log + 16) := hm (log + 16) (by omega)
  have hw24 : memW post (log + 24) = memW s (log + 24) := hm (log + 24) (by omega)
  have hw32 : memW post (log + 32) = memW s (log + 32) := hm (log + 32) (by omega)
  unfold LogEntryOK
  rw [hhp, hw0, hw8, hw16, hw24, hw32]
  exact ⟨wordsOK_transfer hgS hgP hw, hin, h16, h32, hi0, hi8, hi24⟩

theorem logsListOK_transfer {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post)
    (hhp : globN post "heap_ptr" = globN s "heap_ptr")
    (hsc : globN post "scratch_ptr" = globN s "scratch_ptr")
    (hA : ArenaOK s)
    {x : BitVec 64}
    (hmem_ne : ∀ a : BitVec 64, a ≠ x → post.memory a = s.memory a)
    (hm_heap : ∀ a : Nat, a < heapLimit → memW post a = memW s a)
    {logs : Nat}
    (hd_hdr : logs ≠ 0 → Disj (logs, 24) (x.toNat, 8))
    (hd_arr : logs ≠ 0 → Disj (memW s logs, 8 * memW s (logs + 16)) (x.toNat, 8))
    (harr_al : logs ≠ 0 → (memW s logs) % 8 = 0 ∧ memW s logs + 8 * memW s (logs + 16) ≤ 2 ^ 64)
    (hL : LogsListOK s logs) :
    LogsListOK post logs := by
  rcases hL with rfl | ⟨hw, hal, hlen28, hlen_cap, hent⟩
  · exact Or.inl rfl
  · right
    have hnz : logs ≠ 0 := by
      rintro rfl
      have hsb : 0 < sourceBase := by decide
      have hss : 0 < scratchStart := by decide
      rcases hal with ⟨hlo, _⟩ | ⟨hlo, _⟩
      · change sourceBase ≤ 0 at hlo; omega
      · have := hA.2.2.1; have := hA.2.2.2.1; dsimp only at hlo; omega
    have hhi_l := (ivl_allocated_bound hA hal).2
    have hl8 : logs % 8 = 0 := hw.1
    have hu_hdr := ivlUnhit_of_single_cell_disj hmem_ne (hd_hdr hnz)
    have hw0 : memW post logs = memW s logs := by
      simpa using memW_eq_of_ivlUnhit hu_hdr (by omega) hhi_l ⟨by omega, by omega⟩
    have hw8 : memW post (logs + 8) = memW s (logs + 8) :=
      memW_eq_of_ivlUnhit hu_hdr (by omega) hhi_l ⟨by omega, by omega⟩
    have hw16 : memW post (logs + 16) = memW s (logs + 16) :=
      memW_eq_of_ivlUnhit hu_hdr (by omega) hhi_l ⟨by omega, by omega⟩
    have hal_post : Allocated post (logs, 24) := by
      unfold Allocated at hal ⊢; rw [hhp, hsc]; exact hal
    obtain ⟨harr8, harr_hi⟩ := harr_al hnz
    have hu_arr := ivlUnhit_of_single_cell_disj hmem_ne (hd_arr hnz)
    rw [hw8, hw16, hw0]
    refine ⟨wordsOK_transfer hgS hgP hw, hal_post, hlen28, hlen_cap, fun i hi => ?_⟩
    obtain ⟨⟨w_i, hdom_i, _⟩, hle_i⟩ := hent i hi
    have hwa_post : WordAt post (memW s logs + 8 * i) := by
      rcases hm_p : post.memory (BitVec.ofNat 64 (memW s logs + 8 * i)) with ⟨wp⟩
      exact ⟨wp, by rw [hgP.memaddrs, ← hgS.memaddrs]; exact hdom_i, hm_p⟩
    have hslot_eq : memW post (memW s logs + 8 * i) = memW s (memW s logs + 8 * i) :=
      memW_eq_of_ivlUnhit hu_arr (by omega) harr_hi ⟨by omega, by omega⟩
    rw [hslot_eq]
    exact ⟨hwa_post, logEntryOK_transfer hgS hgP hhp hA hm_heap hle_i⟩

theorem msgOwned_transfer {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post)
    (hhp : globN post "heap_ptr" = globN s "heap_ptr")
    (hsc : globN post "scratch_ptr" = globN s "scratch_ptr")
    {S : List Nat}
    (hfp_eq : ∀ t ∈ S, htabFootprint post t = htabFootprint s t)
    (hfix_eq : fixedObjects post = fixedObjects s)
    (hch_eq : evmChain post = evmChain s)
    (hfo_eq : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec)
    (htr_post : ∀ Nd, TriesTypedWith s S Nd → TriesTypedWith post S Nd ∧ nodeExtents post Nd = nodeExtents s Nd)
    {m : Nat} (hm : MsgOwned s S m) :
    MsgOwned post S m := by
  obtain ⟨hal, hw, hd_tab, hd_fix, hd_fo, ⟨Nd_m, hTr_m, hd_nd⟩⟩ := hm
  have hal_post : Allocated post (m, 176) := by
    unfold Allocated at hal ⊢; rw [hhp, hsc]; exact hal
  obtain ⟨hTr_m_post, hnd_eq⟩ := htr_post Nd_m hTr_m
  refine ⟨hal_post, wordsOK_transfer hgS hgP hw, ?_, ?_, ?_, ⟨Nd_m, hTr_m_post, ?_⟩⟩
  · intro t ht i hi; rw [hfp_eq t ht] at hi; exact hd_tab t ht i hi
  · intro j hj; rw [hfix_eq] at hj; exact hd_fix j hj
  · intro ec hec o ho
    rw [hch_eq] at hec
    rw [hfo_eq ec hec] at ho
    exact hd_fo ec hec o ho
  · intro o ho j hj
    rw [hnd_eq] at hj
    exact hd_nd o ho j hj

theorem evmInv_store_cur_cont_24 {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s) {x : BitVec 64}
    (hx_eq : x.toNat = globN s "cur_cont" + 24)
    (hx_dom : s.memaddrs x)
    (hpost : post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ post.shMemaddrs = s.shMemaddrs ∧
      post.baseAddr = s.baseAddr ∧ post.be = s.be ∧ post.globals = s.globals ∧
      ∀ a : BitVec 64, a ≠ x → post.memory a = s.memory a) :
    EvmInv post := by
  obtain ⟨hAs, S, hW, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW, hFO_pw, hFO_disj, hAT, hMarks, hRoles, hGas⟩ := hInv
  obtain ⟨Nd_at, hTr_at, hAT_at⟩ := hAT
  have hWT : WorldTypedWith s S Nd_at := ⟨hW.1, hW.2.1, hW.2.2.1, hTr_at⟩
  have hch_cons_ex : ∃ tail, evmChain s = (globN s "ev", globN s "cur_cont") :: tail := by
    unfold evmChain
    exact ⟨_, rfl⟩
  obtain ⟨chTail, hch_cons⟩ := hch_cons_ex
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    rw [hch_cons]; exact List.mem_cons_self
  have hhead_FW := hFW_all _ hhead_mem
  obtain ⟨hb_e0, hb_c0, _⟩ := frameWF_bounds hhead_FW
  dsimp only at hb_c0
  have hcont_in_scr : Inside (globN s "cur_cont", 104) (globN s "scratch_ptr") scratchEnd :=
    (hhead_FW.1 (globN s "cur_cont", 104) (by simp)).1
  have hc8 : (globN s "cur_cont") % 8 = 0 :=
    (hhead_FW.1 (globN s "cur_cont", 104) (by simp)).2.1
  have hx_in_cont : Inside (x.toNat, 8) (globN s "cur_cont") (globN s "cur_cont" + 104) := by
    unfold Inside; dsimp only; omega
  have hcont_fo : (globN s "cur_cont", 104) ∈ frameObjects s (globN s "ev", globN s "cur_cont") := by
    simp [frameObjects]
  have hcont_fl : (globN s "cur_cont", 104) ∈ ((evmChain s).map (frameObjects s)).flatten := by
    rw [List.mem_flatten]
    exact ⟨frameObjects s (globN s "ev", globN s "cur_cont"),
      List.mem_map.2 ⟨_, hhead_mem, rfl⟩, hcont_fo⟩
  have hdisj_wti_of_nd : ∀ {Nd : List Nat},
      (∀ j ∈ nodeExtents s Nd, Disj (globN s "cur_cont", 104) j) →
      ∀ j ∈ worldTypedIvls s S Nd, Disj j (x.toNat, 8) := by
    intro Nd hnd_c j hj
    apply disj_of_inside_right (j' := (globN s "cur_cont", 104)) hx_in_cont
    unfold worldTypedIvls at hj
    simp only [List.mem_append] at hj
    rcases hj with ((((h1 | h2) | h3) | h4) | h5) | h6
    · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
      exact ((hFO_disj _ hhead_mem _ hcont_fo).1 t ht j hfp).flip
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
      exact ((hFO_disj _ hhead_mem _ hcont_fo).2 _ (typedRecord_mem_fixedObjects s hr)).flip
    · simp only [List.mem_singleton] at h3; subst h3
      have hfix_j : (if globN s "journal_cap" = 0 then 0 else globN s "journal",
          32 * globN s "journal_cap") ∈ fixedObjects s := by
        unfold fixedObjects
        apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right; simp
      exact ((hFO_disj _ hhead_mem _ hcont_fo).2 _ hfix_j).flip
    · have hfix_bo : j ∈ fixedObjects s := by
        unfold fixedObjects; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr h4)))
      exact ((hFO_disj _ hhead_mem _ hcont_fo).2 _ hfix_bo).flip
    · have hfix_bal : j ∈ fixedObjects s := by
        unfold fixedObjects; exact List.mem_append.2 (Or.inr h5)
      exact ((hFO_disj _ hhead_mem _ hcont_fo).2 _ hfix_bal).flip
    · exact (hnd_c j h6).flip
  have hstep_at := worldTypedWith_store_word_disj hAs hx_dom hpost hWT
    (hdisj_wti_of_nd (fun j hj => hAT_at _ hcont_fl j hj))
  obtain ⟨hAp, hWT_post, hfix_eq, hnd_at_eq, hwrs_eq, hjr_eq, htab_fp_hdr, hworldRefs_eq⟩ := hstep_at
  have hW_post : WorldTyped post S :=
    ⟨hWT_post.1, hWT_post.2.1, hWT_post.2.2.1, Nd_at, hWT_post.2.2.2⟩
  have hglob_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, hpost.2.2.2.2.2.1]
  have hmemW_ne : ∀ a : Nat, a < 2 ^ 64 → a ≠ globN s "cur_cont" + 24 → memW post a = memW s a := by
    intro a ha hne
    unfold memW
    have hbv_ne : BitVec.ofNat 64 a ≠ x := by
      intro heq
      have h1 : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
      rw [heq, hx_eq] at h1
      exact hne h1.symm
    rw [hpost.2.2.2.2.2.2 _ hbv_ne]
  have hx_ge_hl : heapLimit ≤ x.toNat := by
    have hsep : heapLimit ≤ scratchStart := by decide
    have hss : scratchStart ≤ globN s "frame_mem_ptr" := hAs.2.2.2.1
    have hsc : globN s "frame_mem_ptr" ≤ globN s "scratch_ptr" := hAs.2.2.2.2.1
    have hc_lo : globN s "scratch_ptr" ≤ globN s "cur_cont" := hcont_in_scr.1
    omega
  have hm_heap : ∀ a : Nat, a < heapLimit → memW post a = memW s a := by
    intro a ha
    have h264 : heapLimit ≤ 2 ^ 64 := by decide
    exact hmemW_ne a (by omega) (by omega)
  have hnd_disj_any : ∀ {Nd : List Nat}, NodeHeap s Nd → ∀ j ∈ nodeExtents s Nd, Disj j (x.toNat, 8) := by
    intro Nd hN j hj
    unfold nodeExtents at hj
    obtain ⟨n, hn, hj_np⟩ := List.mem_flatMap.1 hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj_np
    rcases hj_np with rfl | rfl
    · have hin := (hN.1 n hn).2.2.1
      exact Or.inr (Or.inr (Or.inl (le_trans hin.2 hx_ge_hl)))
    · unfold nodePath
      split_ifs with hcond
      · rcases (hN.1 n hn).2.2.2.2.2.2.1 hcond.1 with h0 | ⟨_, _, hin, _⟩
        · exact absurd h0 hcond.2
        · exact Or.inr (Or.inr (Or.inl (le_trans hin.2 hx_ge_hl)))
      · exact disj_zero_left _
  have htr_any_post : ∀ Nd, TriesTypedWith s S Nd → TriesTypedWith post S Nd ∧ nodeExtents post Nd = nodeExtents s Nd := by
    intro Nd hTr_any
    have hWT_any : WorldTypedWith s S Nd := ⟨hW.1, hW.2.1, hW.2.2.1, hTr_any⟩
    have hstep_any := worldTypedWith_store_word_disj hAs hx_dom hpost hWT_any (by
      intro j hj
      unfold worldTypedIvls at hj
      rcases List.mem_append.1 hj with hj_rest | hj_nd
      · exact hdisj_wti_of_nd (fun k hk => hAT_at _ hcont_fl k hk) j (List.mem_append.2 (Or.inl hj_rest))
      · exact hnd_disj_any hTr_any.1 j hj_nd)
    exact ⟨hstep_any.2.1.2.2.2, hstep_any.2.2.2.1⟩
  have hpw_head_tail :
      (frameObjects s (globN s "ev", globN s "cur_cont")).Pairwise Disj ∧
      (∀ o1 ∈ frameObjects s (globN s "ev", globN s "cur_cont"),
        ∀ ec ∈ chTail, ∀ o2 ∈ frameObjects s ec, Disj o1 o2) := by
    have hpw := hFO_pw
    rw [hch_cons, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
    refine ⟨hpw.1, fun o1 ho1 ec hec o2 ho2 => hpw.2.2 o1 ho1 o2 ?_⟩
    rw [List.mem_flatten]
    exact ⟨frameObjects s ec, List.mem_map.2 ⟨ec, hec, rfl⟩, ho2⟩
  have hcont_disj_head : ∀ o ∈ [(globN s "ev", 280),
      (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232)),
      (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40)),
      (memW s (globN s "ev" + 88), 24),
      frameLogs s (globN s "ev", globN s "cur_cont"),
      frameRet s (globN s "ev", globN s "cur_cont")],
      Disj (globN s "cur_cont", 104) o := by
    have hpw0 := hpw_head_tail.1
    unfold frameObjects at hpw0
    simp only [List.pairwise_cons] at hpw0
    obtain ⟨hd0, hd1, _⟩ := hpw0
    intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hd0 _ (by simp)).flip
    · exact hd1 _ (by simp)
    · exact hd1 _ (by simp)
    · exact hd1 _ (by simp)
    · exact hd1 _ (by simp)
    · exact hd1 _ (by simp)
  have hrec_other_eq : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → k ≠ 24 → memW post (ec.2 + k) = memW s (ec.2 + k)) ∧
      (∀ k, k + 8 ≤ 24 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) := by
    intro ec hec
    obtain ⟨hb_e, hb_c, hb_88⟩ := frameWF_bounds (hFW_all ec hec)
    have hdisj_e : Disj (globN s "cur_cont", 104) (ec.1, 280) := by
      rw [hch_cons, List.mem_cons] at hec
      rcases hec with rfl | htail
      · exact hcont_disj_head _ (by simp)
      · exact hpw_head_tail.2 _ hcont_fo ec htail _ (by simp [frameObjects])
    have hdisj_88 : Disj (globN s "cur_cont", 104) (memW s (ec.1 + 88), 24) := by
      rw [hch_cons, List.mem_cons] at hec
      rcases hec with rfl | htail
      · exact hcont_disj_head _ (by simp)
      · exact hpw_head_tail.2 _ hcont_fo ec htail _ (by simp [frameObjects])
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      apply hmemW_ne (ec.1 + k) (by omega)
      rcases hdisj_e with h | h | h | h
      · cases h
      · cases h
      · dsimp only at h; omega
      · dsimp only at h; omega
    · intro k hk hkne
      apply hmemW_ne (ec.2 + k) (by omega)
      rw [hch_cons, List.mem_cons] at hec
      rcases hec with rfl | htail
      · dsimp only; omega
      · have hd := hpw_head_tail.2 _ hcont_fo ec htail (ec.2, 104) (by simp [frameObjects])
        rcases hd with h | h | h | h
        · cases h
        · cases h
        · dsimp only at h; omega
        · dsimp only at h; omega
    · intro k hk
      apply hmemW_ne (memW s (ec.1 + 88) + k) (by omega)
      rcases hdisj_88 with h | h | h | h
      · cases h
      · cases h
      · dsimp only at h; omega
      · dsimp only at h; omega
  have hchain_aux : ∀ (fuel e c : Nat),
      (∀ ec ∈ evmChainFrom s fuel e c, ec ∈ evmChain s) →
      evmChainFrom post fuel e c = evmChainFrom s fuel e c := by
    intro fuel
    induction fuel with
    | zero => intros; rfl
    | succ fuel ih =>
      intro e c hsub
      have hec : (e, c) ∈ evmChain s := hsub (e, c) (by simp [evmChainFrom])
      obtain ⟨_, hc_eq, _⟩ := hrec_other_eq (e, c) hec
      have hc16 := hc_eq 16 (by omega) (by omega)
      have hc0 : memW post c = memW s c := by simpa using hc_eq 0 (by omega) (by omega)
      have hc8 := hc_eq 8 (by omega) (by omega)
      simp only [evmChainFrom, hc16, hc0, hc8]
      split
      · rfl
      · rename_i hne16
        rw [ih (memW s c) (memW s (c + 8))]
        intro ec' hec'
        apply hsub ec'
        simp only [evmChainFrom, hne16, ↓reduceIte, List.mem_cons]
        exact Or.inr hec'
  have hchain_eq : evmChain post = evmChain s := by
    unfold evmChain
    rw [hglob_eq "ev", hglob_eq "cur_cont"]
    exact hchain_aux (maxChain + 1) (globN s "ev") (globN s "cur_cont") (fun _ h => h)
  have hframeLogs_eq : ∀ ec ∈ evmChain s, frameLogs post ec = frameLogs s ec := by
    intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_other_eq ec hec
    unfold frameLogs
    rw [he_eq 88 (by omega),
        show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by simpa using h88_eq 0 (by omega),
        h88_eq 16 (by omega)]
  have hframeRet_eq : ∀ ec ∈ evmChain s, frameRet post ec = frameRet s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_other_eq ec hec
    unfold frameRet
    rw [he_eq 216 (by omega), he_eq 144 (by omega)]
  have hframeObjects_eq : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_other_eq ec hec
    unfold frameObjects
    rw [he_eq 8 (by omega), he_eq 232 (by omega),
        he_eq 24 (by omega), he_eq 40 (by omega),
        he_eq 88 (by omega), hframeLogs_eq ec hec, hframeRet_eq ec hec]
  have hframeScratch_eq : ∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_other_eq ec hec
    unfold frameScratch
    rw [he_eq 8 (by omega), he_eq 232 (by omega), he_eq 88 (by omega)]
  have hmap_fo_eq : (evmChain s).map (frameObjects post) = (evmChain s).map (frameObjects s) :=
    List.map_congr_left hframeObjects_eq
  have hframeRoleSlots_eq : frameRoleSlots post (evmChain s) = frameRoleSlots s (evmChain s) := by
    unfold frameRoleSlots
    apply List.flatMap_congr; intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_other_eq ec hec
    rw [he_eq 136 (by omega), he_eq 168 (by omega), he_eq 176 (by omega)]
  refine ⟨hAp, S, hW_post, ?_⟩
  dsimp only
  rw [hchain_eq]
  refine ⟨hch_ne, hch_len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨ec, hec, hk0⟩ := hch_last
    have hec_mem : ec ∈ evmChain s := List.mem_of_mem_getLast? hec
    exact ⟨ec, hec, by rw [(hrec_other_eq ec hec_mem).2.1 16 (by omega) (by omega)]; exact hk0⟩
  · intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_other_eq ec hec
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17⟩ := hFW_all ec hec
    have hd_88_x : Disj (memW s (ec.1 + 88), 24) (x.toNat, 8) := by
      apply disj_of_inside_right (j' := (globN s "cur_cont", 104)) hx_in_cont
      apply Disj.flip
      rw [hch_cons, List.mem_cons] at hec
      rcases hec with rfl | htail
      · exact hcont_disj_head _ (by simp)
      · exact hpw_head_tail.2 _ hcont_fo ec htail _ (by simp [frameObjects])
    have hd_flogs_x : Disj (frameLogs s ec) (x.toNat, 8) := by
      apply disj_of_inside_right (j' := (globN s "cur_cont", 104)) hx_in_cont
      apply Disj.flip
      rw [hch_cons, List.mem_cons] at hec
      rcases hec with rfl | htail
      · exact hcont_disj_head _ (by simp)
      · exact hpw_head_tail.2 _ hcont_fo ec htail _ (by simp [frameObjects])
    have hflogs_al : (memW s (memW s (ec.1 + 88))) % 8 = 0 ∧
        memW s (memW s (ec.1 + 88)) + 8 * memW s (memW s (ec.1 + 88) + 16) ≤ 2 ^ 64 := by
      have hal_fl : Allocated s (frameLogs s ec) := c13
      exact ⟨c14.1, (ivl_allocated_bound hAs.2 hal_fl).2⟩
    have hc16_post : LogsListOK post (memW post (ec.1 + 88)) := by
      rw [he_eq 88 (by omega)]
      exact logsListOK_transfer hAs.1 hAp.1 (hglob_eq "heap_ptr") (hglob_eq "scratch_ptr") hAs.2
        hpost.2.2.2.2.2.2 hm_heap (fun _ => hd_88_x) (fun _ => hd_flogs_x) (fun _ => hflogs_al) c16
    have hc17_post : MsgOwned post S (memW post (ec.1 + 112)) := by
      rw [he_eq 112 (by omega)]
      exact msgOwned_transfer hAs.1 hAp.1 (hglob_eq "heap_ptr") (hglob_eq "scratch_ptr")
        (fun t ht => (htab_fp_hdr t ht).2) hfix_eq hchain_eq hframeObjects_eq htr_any_post c17
    unfold FrameWF
    dsimp only
    rw [he_eq 8 (by omega), he_eq 232 (by omega),
        he_eq 88 (by omega), he_eq 24 (by omega),
        he_eq 40 (by omega), he_eq 16 (by omega),
        he_eq 32 (by omega),
        he_eq 136 (by omega), he_eq 168 (by omega),
        he_eq 176 (by omega),
        h88_eq 16 (by omega), h88_eq 8 (by omega),
        hframeLogs_eq ec hec,
        he_eq 216 (by omega), he_eq 144 (by omega),
        hframeRet_eq ec hec,
        hglob_eq "scratch_ptr", hglob_eq "frame_mem_ptr", hglob_eq "heap_ptr", hglob_eq "evm_empty"]
    refine ⟨?_, c2, wordsOK_transfer hAs.1 hAp.1 c3, c4, c5, c6, c7,
      c8, c9, c10, c11, c12, c13, wordsOK_transfer hAs.1 hAp.1 c14, ?_, ?_, ?_⟩
    · intro i hi
      obtain ⟨hin, hw⟩ := c1 i hi
      exact ⟨hin, wordsOK_transfer hAs.1 hAp.1 hw⟩
    · rcases c15 with h0 | ⟨hin, hw⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hin, wordsOK_transfer hAs.1 hAp.1 hw⟩
    · simpa [he_eq 88 (by omega)] using hc16_post
    · simpa [he_eq 112 (by omega)] using hc17_post
  · intro ec hec
    have hec_mem : ec ∈ evmChain s := List.mem_of_mem_tail hec
    unfold FrameRoom
    rw [(hrec_other_eq ec hec_mem).1 16 (by omega), (hrec_other_eq ec hec_mem).1 232 (by omega)]
    exact hFR_all ec hec
  · intro i hi
    have hi0 : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hi1 : (evmChain s)[i + 1] ∈ evmChain s := List.getElem_mem _
    rw [(hrec_other_eq _ hi0).2.1 80 (by omega) (by omega),
        (hrec_other_eq _ hi0).2.1 72 (by omega) (by omega),
        (hrec_other_eq _ hi1).1 40 (by omega)]
    exact hRW i hi
  · rw [hmap_fo_eq]; exact hFO_pw
  · intro ec hec o ho
    rw [hframeObjects_eq ec hec] at ho
    rw [hfix_eq]
    refine ⟨fun t ht i hi => ?_, (hFO_disj ec hec o ho).2⟩
    rw [(htab_fp_hdr t ht).2] at hi
    exact (hFO_disj ec hec o ho).1 t ht i hi
  · rw [hmap_fo_eq]
    refine ⟨Nd_at, hWT_post.2.2.2, fun o ho j hj => ?_⟩
    rw [hnd_at_eq] at hj
    exact hAT_at o ho j hj
  · have hdelEx_iff : ∀ i t, DelExclusive post S (evmChain s) i t ↔ DelExclusive s S (evmChain s) i t := by
      intro i t
      unfold DelExclusive
      rw [hworldRefs_eq]
      refine and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun hj =>
        forall_congr' fun k => imp_congr_right fun hk => ?_)
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      have hk_ok : k + 8 ≤ 280 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> omega
      rw [(hrec_other_eq _ hj_mem).1 k hk_ok]
    intro i hi
    have hi_mem : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hm_eq := (hrec_other_eq _ hi_mem).2.1 48 (by omega) (by omega)
    have hmm_eq := (hrec_other_eq _ hi_mem).2.1 56 (by omega) (by omega)
    have he24_eq := (hrec_other_eq _ hi_mem).1 24 (by omega)
    have htake_eq : ((evmChain s).take (i + 1)).map (fun ec => memW post (ec.1 + 136)) =
        ((evmChain s).take (i + 1)).map (fun ec => memW s (ec.1 + 136)) := by
      apply List.map_congr_left; intro ec hec
      exact (hrec_other_eq ec (List.mem_of_mem_take hec)).1 136 (by omega)
    have hM := hMarks i hi
    dsimp only at hM ⊢
    rw [hm_eq, hmm_eq, he24_eq, hframeScratch_eq _ hi_mem, hfix_eq, htake_eq]
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM
    refine ⟨m1, m2, m3, m4, ?_, m6, m7, ?_, m9⟩
    · intro j hj hij
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      rw [hframeScratch_eq _ hj_mem, hframeObjects_eq _ hj_mem, hframeLogs_eq _ hj_mem]
      exact m5 j hj hij
    · intro t ht
      rw [(htab_fp_hdr t ht).2, hdelEx_iff i t]
      exact m8 t ht
  · rw [hwrs_eq, hframeRoleSlots_eq, hjr_eq]
    unfold RolesOK at hRoles ⊢
    refine ⟨fun a ha => ?_, hRoles.2⟩
    obtain ⟨haS, hkl⟩ := hRoles.1 a ha
    rw [(htab_fp_hdr a.1 haS).1 0 (by omega)]
    exact ⟨haS, hkl⟩
  · have hmap_gas : ((evmChain s).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)) =
        ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)) := by
      apply List.map_congr_left; intro ec hec
      rw [(hrec_other_eq ec hec).1 64 (by omega), (hrec_other_eq ec hec).1 192 (by omega)]
    rw [hmap_gas]
    exact hGas

def EvmInvSnapWord : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => EvmInv s ∧ ∃ w : BitVec 64, s.locals.lookup (ofString "snapshot") = some (.val (.word w))

theorem value_shape_one_word {v : ValueHOL 64} (h : shapeEqHOL (shapeOfHOLExact v) .one = true) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  cases v with
  | val x =>
    cases x with
    | word w => exact ⟨w, rfl⟩
  | rStruct fs =>
    unfold shapeOfHOLExact at h
    unfold shapeEqHOL at h
    simp at h
  | nStruct nm fs =>
    unfold shapeOfHOLExact at h
    unfold shapeEqHOL at h
    simp at h

theorem decCall_state_snapshot_evmInv {B Bc : Nat}
    (hf : TerminatingFunBoundedOn GuestInv (ofString "state_snapshot") B)
    (hro : ReadOnlyFn (ofString "state_snapshot"))
    {continuation : ProgHOL 64}
    (hcont : TerminatingProgBoundedOn EvmInvSnapWord continuation Bc) :
    TerminatingProgBoundedOn EvmInv
      (.decCall (ofString "snapshot") .one (ofString "state_snapshot") [] continuation)
      (B + Bc + 1) := by
  obtain ⟨params, body, ret, hlook, hbody⟩ := hf
  obtain ⟨params', body2, ret2, hlook2, hb2⟩ := hro
  intro F state hcode hP hnt
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  rcases hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [] with _ | values
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite state.code.lookup (ofString "state_snapshot") values with _ | ⟨body', callee, ret'⟩
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    · simp only [hl] at hnt ⊢
      obtain ⟨hbb, hrunBound⟩ := callee_body_bound hlook hbody
        (callEntryOn_of_imp localsFree_guestInv evmInv_guestInv _ _)
        state hcode hP values body' callee ret' hargs hl
      subst hbb
      have hsame2 := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "state_snapshot")
        params' body2 body' ret2 ret' values callee (by rw [hcode]; exact hlook2) hl
      subst hsame2
      have hret2 := lookupCodeHOLFinite_installed_return state (ofString "state_snapshot")
        params' body' body' ret2 ret' values callee (by rw [hcode]; exact hlook2) hl
      subst hret2
      by_cases hz : state.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) body').1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body' with ⟨res, post⟩
        simp only [hrun] at hnt hmeta ⊢
        change post.code = state.code at hmeta
        have bodyClock (hsafe : res ≠ some .timeOut) :
            state.clock - 1 ≤ post.clock + B ∧ post.clock ≤ state.clock - 1 := by
          have hb := hrunBound (by rw [hrun]; exact hsafe)
          rw [hrun] at hb
          exact hb
        cases res with
        | none =>
          obtain ⟨hs, hk⟩ := bodyClock (by simp)
          exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
        | some r =>
          cases r with
          | returned value =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact value) .one &&
                shapeEqHOL (shapeOfHOLExact value) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt ⊢
              obtain ⟨w, rfl⟩ := value_shape_one_word (Bool.and_eq_true_iff.1 hsh).1
              have hro_eq := hb2 (callEntryStateHOLFinite state callee) hcode
                (guestInv_callEntry state callee (evmInv_guestInv state hP))
                ⟨values, by simpa only [hcode, callEntryStateHOLFinite] using hl⟩
                (by rw [hrun]; simp) (by rw [hrun]; exact Or.inl ⟨.val (.word w), rfl⟩)
              rw [hrun] at hro_eq
              dsimp only at hro_eq
              set resumed := setVarHOLFinite (ofString "snapshot") (.val (.word w)) { post with locals := state.locals }
              have hresCode : resumed.code = originalRuntimeCode := hmeta.trans hcode
              have hpost_inv : EvmInv post := by
                rw [hro_eq]
                exact localsFree_evmInv state post.locals post.clock hP
              have hresInv : EvmInvSnapWord resumed := by
                refine ⟨?_, w, ?_⟩
                · simpa [resumed, setVarHOLFinite] using
                    localsFree_evmInv post (state.locals.update (ofString "snapshot", .val (.word w))) post.clock hpost_inv
                · simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
              obtain ⟨hsc, hkc⟩ := hcont resumed hresCode hresInv hnt
              change post.clock ≤ (evaluateHOLFiniteState resumed continuation).2.clock + Bc at hsc
              change (evaluateHOLFiniteState resumed continuation).2.clock ≤ post.clock at hkc
              exact ⟨by omega, by omega⟩
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte]
              exact ⟨by omega, by omega⟩
          | timeOut => simp at hnt
          | «break» =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
          | «continue» =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
          | _ =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega⟩

theorem seq_hoare_change {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {first second : ProgHOL 64} {a b : Nat}
    (h1 : TerminatingProgBoundedOn P first a)
    (hp : Hoare P first (fun r t => r = none → Q t))
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

theorem hoare_store_cur_cont_24 :
    Hoare EvmInvSnapWord
      (.store (.op .add [.var .global (ofString "cur_cont"), .const 24]) (.var .local (ofString "snapshot")))
      (fun r t => r = none → EvmInv t) := by
  refine ⟨fun {F} s _ ⟨hInv, w_snap, hsnap⟩ _ hr => ?_⟩
  have hrun := evaluateHOLFiniteState_store s
    (.op .add [.var .global (ofString "cur_cont"), .const 24]) (.var .local (ofString "snapshot"))
  rcases hev : evaluateHOLFiniteState s
    (.store (.op .add [.var .global (ofString "cur_cont"), .const 24]) (.var .local (ofString "snapshot"))) with ⟨res, post⟩
  rw [hev] at hr hrun
  dsimp only at hr ⊢
  subst hr
  revert hrun
  rcases hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .global (ofString "cur_cont"), .const 24]) with _ | dv
  · simp
  · rcases dv with ⟨⟨addr⟩⟩ | _ | _
    · have hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.var .local (ofString "snapshot")) = some (.val (.word w_snap)) := by
        simp [evalHOLExact, hsnap]
      rw [hsrc]
      dsimp only
      split
      · rename_i m' hst
        unfold flattenHOL at hst
        unfold panMemStoresHOL at hst
        unfold panMemStoreHOL at hst
        by_cases hdom : s.memaddrs addr
        · simp only [hdom, ↓reduceIte, panMemStoresHOL, Option.some.injEq] at hst
          subst hst
          intro hrun
          injection hrun with _ hpost
          subst hpost
          -- Extract `addr.toNat = globN s "cur_cont" + 24`:
          have haddr_nat : addr.toNat = globN s "cur_cont" + 24 := by
            simp [evalHOLExact, evalListHOLExact] at hdst
            rcases hg : s.globals.lookup (ofString "cur_cont") with _ | gv
            · simp [hg] at hdst
            · rcases gv with ⟨⟨gw⟩⟩ | _ | _
              · simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp] at hdst
                subst hdst
                have hglob : globN s "cur_cont" = gw.toNat := by simp [globN, hg]
                -- Prove no wrap: `globN s "cur_cont" + 104 ≤ 2^64` from `hInv`!
                obtain ⟨_, S, _, _, _, _, hFW_all, _⟩ := hInv
                have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
                  unfold evmChain; exact List.mem_cons_self
                have hb_c := (frameWF_bounds (hFW_all _ hhead_mem)).2.1
                dsimp only at hb_c
                rw [hglob] at hb_c ⊢
                have h24 : (24#64).toNat = 24 := by decide
                rw [BitVec.toNat_add, h24, Nat.mod_eq_of_lt (by omega)]
              · simp [hg, valueIsWord] at hdst
              · simp [hg, valueIsWord] at hdst
          exact evmInv_store_cur_cont_24 hInv haddr_nat hdom
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun a hne => by simp [hne]⟩
        · simp [hdom] at hst
      · simp
    · simp
    · simp

theorem bufferRegion_disj_frameObjects_le {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S : List Nat} (hInv : EvmInvAt s S)
    (gn : String × Nat) (hg : gn ∈ globalBuffers)
    (n : Nat) (hle : n ≤ gn.2) :
    ∀ j ∈ ((evmChain s).map (frameObjects s)).flatten, Disj (bufferRegion s (gn.1, n)) j := by
  obtain ⟨_, _, _, _, _, _, _, _, hFO_disj, _⟩ := hInv
  intro j hj
  rw [List.mem_flatten] at hj
  obtain ⟨fo, hfo_map, hj_fo⟩ := hj
  obtain ⟨ec, hec, rfl⟩ := List.mem_map.1 hfo_map
  have hfix : bufferRegion s gn ∈ fixedObjects s := by
    unfold fixedObjects
    apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
    exact List.mem_map.2 ⟨gn, hg, rfl⟩
  have hd : Disj (bufferRegion s gn) j :=
    ((hFO_disj ec hec j hj_fo).2 _ hfix).flip
  by_cases hz : globN s gn.1 = 0
  · exact Or.inl (by simp [bufferRegion, hz])
  · simp only [bufferRegion, hz, ↓reduceIte] at hd ⊢
    rcases hd with h | h | h | h
    · exact Or.inl (by dsimp only at h ⊢; omega)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (by dsimp only at h ⊢; omega)))
    · exact Or.inr (Or.inr (Or.inr h))

abbrev FrameStartAvoids {F : Type} (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
   (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352),
   (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384),
   (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
   (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
   (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
   (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96),
   (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40),
   (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128),
   (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128),
   (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
   (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64),
   (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52),
   (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)]

theorem evmAvoids_frameStart_of_evmInv {F : Type} (s : PanSemStateFiniteExact 64 F) (h : EvmInv s) :
    EvmAvoids FrameStartAvoids s := by
  obtain ⟨hA, S, hInv⟩ := (evmInv_iff_at s).1 h
  have hW := hInv.1
  obtain ⟨Nd, hTr, _⟩ := hInv.2.2.2.2.2.2.2.2.2.1
  have hWT : WorldTypedWith s S Nd := ⟨hW.1, hW.2.1, hW.2.2.1, hTr⟩
  refine ⟨hA, S, hInv, Nd, hTr, ?_⟩
  intro i hi j hj
  have hi_part : ∃ gn ∈ globalBuffers, gn.1 ∉ typedRecords.map Prod.fst ∧
      ∃ n, n ≤ gn.2 ∧ i = bufferRegion s (gn.1, n) := by
    change i ∈ [bufferRegion s ("b2_v", 128), bufferRegion s ("bn_expw", 352),
      bufferRegion s ("bn_gamma", 384), bufferRegion s ("keccak_pad", 136),
      bufferRegion s ("keccak_st", 200), bufferRegion s ("mpt_nib_scratch", 64),
      bufferRegion s ("pre_hdr_buf", 96), bufferRegion s ("rmd_h", 40),
      bufferRegion s ("rmd_pad", 128), bufferRegion s ("rmd_x", 128),
      bufferRegion s ("sha_pad", 128), bufferRegion s ("sha_st", 64),
      bufferRegion s ("sk_buf", 52), bufferRegion s ("u256_ws", 640)] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨("b2_v", 128), by decide, by decide, 128, le_rfl, rfl⟩
    · exact ⟨("bn_expw", 352), by decide, by decide, 352, le_rfl, rfl⟩
    · exact ⟨("bn_gamma", 384), by decide, by decide, 384, le_rfl, rfl⟩
    · exact ⟨("keccak_pad", 136), by decide, by decide, 136, le_rfl, rfl⟩
    · exact ⟨("keccak_st", 200), by decide, by decide, 200, le_rfl, rfl⟩
    · exact ⟨("mpt_nib_scratch", 64), by decide, by decide, 64, le_rfl, rfl⟩
    · exact ⟨("pre_hdr_buf", 96), by decide, by decide, 96, le_rfl, rfl⟩
    · exact ⟨("rmd_h", 40), by decide, by decide, 40, le_rfl, rfl⟩
    · exact ⟨("rmd_pad", 128), by decide, by decide, 128, le_rfl, rfl⟩
    · exact ⟨("rmd_x", 128), by decide, by decide, 128, le_rfl, rfl⟩
    · exact ⟨("sha_pad", 128), by decide, by decide, 128, le_rfl, rfl⟩
    · exact ⟨("sha_st", 64), by decide, by decide, 64, le_rfl, rfl⟩
    · exact ⟨("sk_buf", 64), by decide, by decide, 52, by decide, rfl⟩
    · exact ⟨("u256_ws", 640), by decide, by decide, 640, le_rfl, rfl⟩
  obtain ⟨gn, hg, hu, n, hle, rfl⟩ := hi_part
  rcases List.mem_append.1 hj with hj_w | hj_f
  · exact bufferRegion_disj_le hWT gn hg hu n hle j hj_w
  · exact bufferRegion_disj_frameObjects_le hInv gn hg n hle j hj_f

/-! ## 4. Proof of `gbody_process_message` -/

theorem hoare_depth0_branch
    (hek_dp : EvmKeeps EvmMsgReady ["heap_ptr", "journal_n", "scratch_ptr"] (ofString "depth0_prepare"))
    (hro_snap : ReadOnlyFn (ofString "state_snapshot"))
    (cond : ExpHOL 64) {handler : ProgHOL 64}
    (hh : Hoare GuestInv handler (fun r t => r = none → EvmInv t)) :
    Hoare EvmMsgReady
      (.ite cond
        (.decCall (ofString "prep_snapshot") .one (ofString "state_snapshot") []
          (.dec (ofString "prep_reservoir") .one
            (.load .one (.op .add [.var .local (ofString "msg"), .const 48]))
            (.dec (ofString "perr") .one (.const 0)
              (.call (some (none, some (ofString "EvmErr", ofString "perr", handler)))
                (ofString "depth0_prepare") []))))
        .skip)
      (fun r t => r = none → EvmInv t) := by
  refine Hoare.ite ?_ (Hoare.skip fun s h _ => evmInv_of_evmMsgReady s h.1) (fun _ _ h => absurd h (by simp))
  -- Inside the `then` branch, we start from `EvmMsgReady s ∧ CondTrue cond s`.
  refine Hoare.mono (P' := EvmMsgReady) ?_ (fun _ h => h.1)
  refine ⟨fun {F} state hcode hP hnt => ?_⟩
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  rcases hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) [] with _ | values
  · intro h; simp at h
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite state.code.lookup (ofString "state_snapshot") values with _ | ⟨body', callee, ret'⟩
    · intro h; simp at h
    · simp only [hl] at hnt ⊢
      by_cases hz : state.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        obtain ⟨params_s, body_s, ret_s, hlook_s, hb_s⟩ := hro_snap
        have hsame_s := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "state_snapshot")
          params_s body_s body' ret_s ret' values callee (by rw [hcode]; exact hlook_s) hl
        subst hsame_s
        have hret_s := lookupCodeHOLFinite_installed_return state (ofString "state_snapshot")
          params_s body' body' ret_s ret' values callee (by rw [hcode]; exact hlook_s) hl
        subst hret_s
        have hmeta_s := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) body').1
        rcases hrun_s : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body' with ⟨res_s, post_s⟩
        simp only [hrun_s] at hnt hmeta_s ⊢
        change post_s.code = state.code at hmeta_s
        cases res_s with
        | none => intro h; simp at h
        | some rs =>
          cases rs with
          | timeOut => simp at hnt
          | returned val_s =>
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact val_s) .one &&
                shapeEqHOL (shapeOfHOLExact val_s) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt ⊢
              have hro_eq := hb_s (callEntryStateHOLFinite state callee) hcode
                (guestInv_callEntry state callee (evmInv_guestInv state (evmInv_of_evmMsgReady state hP)))
                ⟨values, by simpa only [hcode, callEntryStateHOLFinite] using hl⟩
                (by rw [hrun_s]; simp) (by rw [hrun_s]; exact Or.inl ⟨val_s, rfl⟩)
              rw [hrun_s] at hro_eq
              dsimp only at hro_eq
              set s1 := setVarHOLFinite (ofString "prep_snapshot") val_s { post_s with locals := state.locals }
              have hs1_code : s1.code = originalRuntimeCode := hmeta_s.trans hcode
              have hs1_P : EvmMsgReady s1 := by
                have hp_P : EvmMsgReady post_s := by
                  rw [hro_eq]
                  exact localsFree_evmMsgReady state post_s.locals post_s.clock hP
                simpa [s1, setVarHOLFinite] using
                  localsFree_evmMsgReady post_s (state.locals.update (ofString "prep_snapshot", val_s)) post_s.clock hp_P
              have hinner : Hoare EvmMsgReady
                  (.dec (ofString "prep_reservoir") .one
                    (.load .one (.op .add [.var .local (ofString "msg"), .const 48]))
                    (.dec (ofString "perr") .one (.const 0)
                      (.call (some (none, some (ofString "EvmErr", ofString "perr", handler)))
                        (ofString "depth0_prepare") [])))
                  (fun r t => r = none → EvmInv t) := by
                have hpostLoc : PostLocalsOnly [] (fun r t => r = none → EvmInv t) :=
                  fun _ t loc _ h hr => localsFree_evmInv t loc t.clock (h hr)
                refine Hoare.dec (names := []) (by simp)
                  (fun s v hPs _ => by
                    simpa [setVarHOLFinite] using localsFree_evmMsgReady s (s.locals.update (_, v)) s.clock hPs)
                  ?_ hpostLoc (fun _ _ h => absurd h (by simp))
                refine Hoare.dec (names := []) (by simp)
                  (fun s v hPs _ => by
                    simpa [setVarHOLFinite] using localsFree_evmMsgReady s (s.locals.update (_, v)) s.clock hPs)
                  ?_ hpostLoc (fun _ _ h => absurd h (by simp))
                refine Hoare.callH hek_dp (callEntryOn_of_localsFree localsFree_evmMsgReady _ _)
                  (fun s _ post v _ _ hq _ =>
                    localsFree_evmInv post s.locals post.clock (hq (Or.inl ⟨v, rfl⟩)).1)
                  (fun s _ post v _ _ hq => by
                    have hstep := hq (Or.inr ⟨ofString "EvmErr", v, rfl, by decide⟩)
                    exact guestInv_setVar (ofString "perr") v _
                      (guestInv_with_locals_clock post s.locals post.clock (evmInv_guestInv post hstep.1)))
                  hh
                  (fun _ _ hr _ h => absurd h hr)
              have hout := hinner.run s1 hs1_code hs1_P hnt
              intro hr_none
              exact localsFree_evmInv _ _ (evaluateHOLFiniteState s1 _).2.clock (hout hr_none)
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte]
              intro h; simp at h
          | _ => intro h; simp at h

theorem hoare_depth0_handler
    (esr e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 : ExpHOL 64)
    (cond : ExpHOL 64) :
    Hoare GuestInv
      (.seq
        (.ite cond
          (.seq (.call (some (none, none)) (ofString "scratch_release") [esr])
            (.seq (.call (some (none, none)) (ofString "frame_mem_release") [e3])
              (.seq (.assign .global (ofString "ev") e4)
                (.seq (.assign .global (ofString "cur_cont") e5)
                  (.raise (ofString "EvmErr") e6)))))
          .skip)
        (.seq (.call (some (none, none)) (ofString "state_restore") [e7])
          (.seq (.store e8 e9)
            (.seq (.store e10 e11)
              (.seq (.call (some (none, none)) (ofString "refill_frame_state_gas") [])
                (.seq (.call (some (none, none)) (ofString "frame_halt") [e6])
                  (.seq (.assign .global (ofString "ev") e4)
                    (.seq (.assign .global (ofString "cur_cont") e5)
                      (.return e12)))))))))
      (fun r t => r = none → EvmInv t) := by
  have hne : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (p1 p2 : ProgHOL 64),
      (∀ (u : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState u p2).1 ≠ none) →
      (evaluateHOLFiniteState s (.seq p1 p2)).1 ≠ none := by
    intro F s p1 p2 hp2
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hr : evaluateHOLFiniteState s p1 with ⟨r1, mid⟩
    cases r1 with
    | none => exact hp2 mid
    | some _ => simp
  refine ⟨fun {F} s _ _ _ hr => absurd hr ?_⟩
  apply hne; intro u1
  apply hne; intro u2
  apply hne; intro u3
  apply hne; intro u4
  apply hne; intro u5
  apply hne; intro u6
  apply hne; intro u7
  apply hne; intro u8
  exact return_ne_none u8 e12

theorem localsFree_evmAvoids_frameStart : LocalsFree (EvmAvoids FrameStartAvoids) := by
  intro F s locals k h
  obtain ⟨hA, S, hInv, Nd, hTr, hD⟩ := h
  have hA' : ArenaReady { s with locals := locals, clock := k } := localsFree_arenaReady s locals k hA
  have htr_eq : TriesTypedWith { s with locals := locals, clock := k } S Nd ↔ TriesTypedWith s S Nd :=
    Iff.rfl
  have hinvAt_eq : EvmInvAt { s with locals := locals, clock := k } S ↔ EvmInvAt s S := by
    simp only [EvmInvAt, FrameWF, MsgOwned, worldTyped_with_locals, evmChain_with_locals]
    exact Iff.rfl
  refine ⟨hA', S, hinvAt_eq.2 hInv, Nd, htr_eq.2 hTr, ?_⟩
  change IvlsDisj (FrameStartAvoids { s with locals := locals, clock := k })
    (worldTypedIvls { s with locals := locals, clock := k } S Nd ++
      (List.map (frameObjects { s with locals := locals, clock := k })
        (evmChain { s with locals := locals, clock := k })).flatten)
  rw [evmChain_with_locals s locals k]
  exact hD

theorem gbody_process_message_proof :
    (TerminatingFunBoundedOn GuestInv (ofString "depth0_prepare") K.«depth0_prepare») →
    (TerminatingFunBoundedOn GuestInv (ofString "frame_halt") K.«frame_halt») →
    (TerminatingFunBoundedOn GuestInv (ofString "frame_mem_release") K.«frame_mem_release») →
    (TerminatingFunBoundedOn GuestInv (ofString "frame_open") K.«frame_open») →
    (TerminatingFunBoundedOn GuestInv (ofString "frame_start") K.«frame_start») →
    (TerminatingFunBoundedOn GuestInv (ofString "refill_frame_state_gas") K.«refill_frame_state_gas») →
    (TerminatingFunBoundedOn EvmInv (ofString "run_frames") K.«run_frames») →
    (TerminatingFunBoundedOn GuestInv (ofString "scratch_release") K.«scratch_release») →
    (TerminatingFunBoundedOn GuestInv (ofString "state_restore") K.«state_restore») →
    (TerminatingFunBoundedOn GuestInv (ofString "state_snapshot") K.«state_snapshot») →
    (EvmKeeps EvmMsgReady ["heap_ptr", "journal_n", "scratch_ptr"] (ofString "depth0_prepare")) →
    (KeepsOn FrameOpenReady EvmMsgReady (ofString "frame_open")) →
    (EvmKeeps (EvmAvoids FrameStartAvoids) ["bn_expw", "bn_gamma", "heap_ptr", "journal_n", "scratch_ptr"] (ofString "frame_start")) →
    (ReadOnlyFn (ofString "state_snapshot")) →
    TerminatingFunBoundedOn MsgReady (ofString "process_message") K.«process_message» := by
  intro hdp hfh hfmr hfo hfs hrf hrfrm hsr hst hsnap hek_dp hfk_fo hek_fs hro_snap
  have msgReady_guestInv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), MsgReady s → GuestInv s :=
    fun s h => h.1.1
  have evmMsgReady_guestInv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), EvmMsgReady s → GuestInv s :=
    fun s h => h.1.1
  have hhandler_bound : ∀ (esr e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 : ExpHOL 64) (cond : ExpHOL 64),
      TerminatingProgBoundedOn GuestInv
        (.seq
          (.ite cond
            (.seq (.call (some (none, none)) (ofString "scratch_release") [esr])
              (.seq (.call (some (none, none)) (ofString "frame_mem_release") [e3])
                (.seq (.assign .global (ofString "ev") e4)
                  (.seq (.assign .global (ofString "cur_cont") e5)
                    (.raise (ofString "EvmErr") e6)))))
            .skip)
          (.seq (.call (some (none, none)) (ofString "state_restore") [e7])
            (.seq (.store e8 e9)
              (.seq (.store e10 e11)
                (.seq (.call (some (none, none)) (ofString "refill_frame_state_gas") [])
                  (.seq (.call (some (none, none)) (ofString "frame_halt") [e6])
                    (.seq (.assign .global (ofString "ev") e4)
                      (.seq (.assign .global (ofString "cur_cont") e5)
                        (.return e12)))))))))
        (max ((K.«scratch_release» + 1) + ((K.«frame_mem_release» + 1) + (0 + (0 + 0)))) 0 +
          ((K.«state_restore» + 1) + (0 + (0 + ((K.«refill_frame_state_gas» + 1) +
            ((K.«frame_halt» + 1) + (0 + (0 + 0)))))))) := by
    intro esr e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 cond
    exact TerminatingProgBoundedOn.seq_guestInv
      (TerminatingProgBoundedOn.ite_on
        (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hsr _ _)
          (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hfmr _ _)
            (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
              (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
                (TerminatingProgBoundedOn.of_clock (fun s => clock_raise s _ _))))))
        (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
      (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hst _ _)
        (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
          (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
            (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hrf _ _)
              (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hfh _ _)
                (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
                  (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
                    (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))))))))
  have hhoare_fs : Hoare EvmInv (.call (some (none, none)) (ofString "frame_start") [])
      (fun r t => r = none → EvmInv t) :=
    Hoare.call0 hek_fs.keepsOn
      (callEntryOn_of_imp localsFree_evmAvoids_frameStart evmAvoids_frameStart_of_evmInv _ _)
      (fun s _ post v _ _ hq _ => localsFree_evmInv post s.locals post.clock (hq (Or.inl ⟨v, rfl⟩)))
      (fun _ _ hr _ h => absurd h hr)
  refine ⟨_, _, _, lookup_process_message, ?_⟩
  simp only [InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.seq_hoare
      (TerminatingProgBoundedOn.ite_on
        (TerminatingProgBoundedOn.of_clock (fun s => clock_raise s _ _))
        (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
      (Hoare.ite_raise_skip _ _ _)
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s))
        (Hoare.skip fun _ h _ => h)
        (TerminatingProgBoundedOn.dec_onLocals localsOnly_msgReady _ (by decide) _ _
          (TerminatingProgBoundedOn.dec_onLocals localsOnly_msgReady _ (by decide) _ _
            (TerminatingProgBoundedOn.decCall_on hfo _ _ _
              (callEntryOn_of_imp localsFree_guestInv msgReady_guestInv _ _)
              (resumeOn_keepsOn_localsFree callEntryOn_frameOpenReady localsFree_evmMsgReady hfk_fo _)
              (TerminatingProgBoundedOn.seq_hoare
                (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s))
                (Hoare.skip fun _ h _ => h)
                (seq_hoare_change
                  (TerminatingProgBoundedOn.ite_on
                    (TerminatingProgBoundedOn.decCall_on hsnap _ _ _
                      (callEntryOn_of_imp localsFree_guestInv evmMsgReady_guestInv _ _)
                      (ReadOnlyFn.resumeOn (LocalsOnly.of_localsFree localsFree_evmMsgReady) evmMsgReady_guestInv hro_snap _ (by simp) _)
                      (TerminatingProgBoundedOn.dec_onLocals (LocalsOnly.of_localsFree localsFree_evmMsgReady) _ (by simp) _ _
                        (TerminatingProgBoundedOn.dec_onLocals (LocalsOnly.of_localsFree localsFree_evmMsgReady) _ (by simp) _ _
                          (TerminatingProgBoundedOn.callHandle_on hdp evmMsgReady_guestInv _ _ _
                            (hhandler_bound _ _ _ _ _ _ _ _ _ _ _ _) _
                            (callEntryOn_of_imp localsFree_guestInv evmMsgReady_guestInv _ _)))))
                    (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
                  (hoare_depth0_branch hek_dp hro_snap _ (hoare_depth0_handler _ _ _ _ _ _ _ _ _ _ _ _))
                  (TerminatingProgBoundedOn.seq_hoare
                    (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s))
                    (Hoare.skip fun _ h _ => h)
                    (decCall_state_snapshot_evmInv hsnap hro_snap
                      (seq_hoare_change
                        (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                        hoare_store_cur_cont_24
                        (TerminatingProgBoundedOn.seq_hoare
                          (TerminatingProgBoundedOn.call_on hfs _ _
                            (callEntryOn_of_imp localsFree_guestInv evmInv_guestInv _ _))
                          hhoare_fs
                          (TerminatingProgBoundedOn.seq_guestInv_after
                            (TerminatingProgBoundedOn.call_on hrfrm _ _
                              (callEntryOn_of_localsFree localsFree_evmInv _ _))
                            evmInv_guestInv
                            (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))))))))))))) ?_
  unfold K.«process_message»
  simp only [show ∀ a b : Nat, Nat.max a b = max a b from fun _ _ => rfl]
  omega

/-! ## 5. Proof of `gbody_process_create_message` -/

theorem not_cellHits_of_zero_or_nonempty_disj {a p len : Nat} {j : Ivl}
    (ha8 : a % 8 = 0) (hin : p ≤ a ∧ a + 8 ≤ p + len)
    (hj : j = (0, 0) ∨ j.1 % 8 = 0 ∨ j.2 ≠ 0)
    (hdj : Disj (p, len) j) : ¬ CellHits a j := by
  rcases j with ⟨j1, j2⟩
  rintro ⟨hc1, hc2⟩
  change j1 < a + 8 at hc1
  change a < j1 + j2 at hc2
  have hlen_pos : len ≠ 0 := by omega
  rcases hdj with h | h | h | h
  · exact absurd h hlen_pos
  · have hjz : j2 = 0 := h
    rcases hj with heq0 | hj1_8 | hj2_nz
    · injection heq0 with hj1_0 _; omega
    · change j1 % 8 = 0 at hj1_8; omega
    · exact hj2_nz hjz
  · change p + len ≤ j1 at h; omega
  · change j1 + j2 ≤ p at h; omega

theorem globalBuffers_sz_pos : ∀ gn ∈ globalBuffers, gn.2 ≠ 0 := by decide

theorem lstObjects_well_shaped {F : Type} (s : PanSemStateFiniteExact 64 F) (l esz : Nat) :
    ∀ x ∈ lstObjects s l esz, x = (0, 0) ∨ x.2 ≠ 0 := by
  intro x hx
  unfold lstObjects at hx
  by_cases hl0 : l = 0
  · rw [if_pos hl0] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> exact Or.inl rfl
  · rw [if_neg hl0] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact Or.inr (by dsimp only; omega)
    · by_cases hm0 : esz * memW s (l + 16) = 0
      · rw [if_pos hm0]; exact Or.inl (Prod.ext rfl hm0)
      · exact Or.inr hm0

theorem blockOutObjects_well_shaped {F : Type} (s : PanSemStateFiniteExact 64 F) :
    ∀ j ∈ blockOutObjects s, j = (0, 0) ∨ j.2 ≠ 0 := by
  have hobj : ∀ b p len : Nat,
      (if b = 0 ∨ p = 0 ∨ len = 0 then (0, 0) else (p, len)) = (0, 0) ∨
      (if b = 0 ∨ p = 0 ∨ len = 0 then (0, 0) else (p, len)).2 ≠ 0 := by
    intro b p len
    by_cases hc : b = 0 ∨ p = 0 ∨ len = 0
    · exact Or.inl (if_pos hc)
    · rw [if_neg hc]
      exact Or.inr (fun h0 => hc (Or.inr (Or.inr h0)))
  intro j hj
  unfold blockOutObjects at hj
  dsimp only at hj
  rcases List.mem_append.1 hj with h1 | h72
  · rcases List.mem_append.1 h1 with hhead | h40
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hhead
      rcases hhead with rfl | rfl | rfl <;> exact hobj _ _ _
    · by_cases hc : globN s "bo" = 0 ∨ memW s (globN s "bo" + 40) = 0
      · rw [if_pos hc] at h40
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h40
        rcases h40 with rfl | rfl <;> exact Or.inl rfl
      · rw [if_neg hc] at h40
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h40
        rcases h40 with rfl | rfl <;> exact hobj _ _ _
  · by_cases hc : globN s "bo" = 0 ∨ memW s (globN s "bo" + 72) = 0
    · rw [if_pos hc] at h72
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h72
      rcases h72 with rfl | rfl <;> exact Or.inl rfl
    · rw [if_neg hc] at h72
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h72
      rcases h72 with rfl | rfl <;> exact hobj _ _ _

theorem worldOwned_well_shaped {F : Type} {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hWT : WorldTypedWith s S Nd) :
    ∀ j ∈ worldOwned s S Nd, j = (0, 0) ∨ j.1 % 8 = 0 ∨ j.2 ≠ 0 := by
  obtain ⟨hT, _, _, hTr⟩ := hWT
  intro j hj
  unfold worldOwned at hj
  rcases List.mem_append.1 hj with h1 | hnd
  · rcases List.mem_append.1 h1 with htab | hfix
    · obtain ⟨t, ht, hj_fp⟩ := List.mem_flatMap.1 htab
      exact Or.inr (Or.inl (((hT.2.1 t ht).1.1 j hj_fp).2.1))
    · unfold fixedObjects at hfix
      rcases List.mem_append.1 hfix with h2 | hbal
      · rcases List.mem_append.1 h2 with h3 | hbo
        · rcases List.mem_append.1 h3 with hbuf | hjr
          · obtain ⟨gn, hgn, rfl⟩ := List.mem_map.1 hbuf
            by_cases hg0 : globN s gn.1 = 0
            · exact Or.inl (by simp [hg0])
            · exact Or.inr (Or.inr (by simp [hg0, globalBuffers_sz_pos gn hgn]))
          · simp only [List.mem_singleton] at hjr; subst hjr
            by_cases hjc : globN s "journal_cap" = 0
            · exact Or.inl (by simp [hjc])
            · exact Or.inr (Or.inr (by dsimp only; omega))
        · rcases blockOutObjects_well_shaped s j hbo with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
      · unfold balObjects at hbal
        obtain ⟨ad, _, hj_ad⟩ := List.mem_flatMap.1 hbal
        rcases List.mem_append.1 hj_ad with hhead3 | hslot
        · rcases List.mem_append.1 hhead3 with hhead2 | h32
          · rcases List.mem_append.1 hhead2 with hhead1 | h24
            · rw [List.mem_cons] at hhead1
              rcases hhead1 with rfl | h16
              · exact Or.inr (Or.inr (by dsimp only; omega))
              · rcases lstObjects_well_shaped s _ _ j h16 with h | h; exact Or.inl h; exact Or.inr (Or.inr h)
            · rcases lstObjects_well_shaped s _ _ j h24 with h | h; exact Or.inl h; exact Or.inr (Or.inr h)
          · rcases lstObjects_well_shaped s _ _ j h32 with h | h; exact Or.inl h; exact Or.inr (Or.inr h)
        · obtain ⟨l, _, hjl⟩ := List.mem_flatMap.1 hslot
          rcases lstObjects_well_shaped s _ _ j hjl with h | h; exact Or.inl h; exact Or.inr (Or.inr h)
  · unfold nodeExtents at hnd
    obtain ⟨n, hn, hj_n⟩ := List.mem_flatMap.1 hnd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj_n
    rcases hj_n with rfl | rfl
    · exact Or.inr (Or.inl ((hTr.1.1 n hn).2.2.2.1.1))
    · unfold nodePath
      split_ifs with hc
      · exact Or.inr (Or.inr hc.2)
      · exact Or.inl rfl

theorem ivlUnhit_of_frameOutside_wellShaped {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {keep : List Ivl} {fresh i : Ivl}
    (hfr : FrameOutside s post keep fresh)
    (hi1 : i.1 % 8 = 0) (hi2 : i.2 % 8 = 0)
    (hk_ws : ∀ j ∈ keep, j = (0, 0) ∨ j.1 % 8 = 0 ∨ j.2 ≠ 0)
    (hf_ws : fresh = (0, 0) ∨ fresh.1 % 8 = 0 ∨ fresh.2 ≠ 0)
    (hk : ∀ j ∈ keep, Disj i j) (hf : Disj i fresh) :
    IvlUnhit s post i := by
  rcases i with ⟨i1, i2⟩
  by_cases hz : i2 = 0
  · exact Or.inl hz
  · right
    intro a ha8 hhit
    obtain ⟨hin1, hin2⟩ := cellHits_aligned ha8 hi1 hhit
    change i1 ≤ a.toNat at hin1
    change a.toNat < i1 + i2 at hin2
    change i1 % 8 = 0 at hi1
    change i2 % 8 = 0 at hi2
    have hin2_8 : a.toNat + 8 ≤ i1 + i2 := by omega
    exact hfr a
      (fun j hj => not_cellHits_of_zero_or_nonempty_disj ha8 ⟨hin1, hin2_8⟩ (hk_ws j hj) (hk j hj))
      (not_cellHits_of_zero_or_nonempty_disj ha8 ⟨hin1, hin2_8⟩ hf_ws hf)

theorem worldRole_not_frame {F : Type} {s : PanSemStateFiniteExact 64 F} {a : Nat × String}
    (ha : a ∈ worldRoleSlots s) : a.2 ≠ "frame.addr" ∧ a.2 ≠ "frame.key" := by
  unfold worldRoleSlots at ha
  rw [List.mem_filter] at ha
  rcases ha with ⟨ha, _⟩
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with (((((hws | hbs) | hts) | hg) | hnbs) | hnts) | hbal
  · unfold recRoles at hws; split at hws
    · simp at hws
    · obtain ⟨k, hk, heq_k⟩ := List.mem_map.1 hws
      rw [← heq_k]; dsimp only; simp at hk; rcases hk with rfl | rfl <;> decide
  · unfold recRoles at hbs; split at hbs
    · simp at hbs
    · obtain ⟨k, hk, heq_k⟩ := List.mem_map.1 hbs
      rw [← heq_k]; dsimp only; simp at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · unfold recRoles at hts; split at hts
    · simp at hts
    · obtain ⟨k, hk, heq_k⟩ := List.mem_map.1 hts
      rw [← heq_k]; dsimp only; simp at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rcases hg with rfl | rfl | rfl <;> (dsimp only; decide)
  · unfold nestRoles at hnbs; split at hnbs
    · simp at hnbs
    · split at hnbs
      · simp at hnbs
      · obtain ⟨_, _, heq_v⟩ := List.mem_map.1 hnbs; rw [← heq_v]; dsimp only; decide
  · unfold nestRoles at hnts; split at hnts
    · simp at hnts
    · split at hnts
      · simp at hnts
      · obtain ⟨_, _, heq_v⟩ := List.mem_map.1 hnts; rw [← heq_v]; dsimp only; decide
  · obtain ⟨ad, _, had_m⟩ := List.mem_flatMap.1 hbal
    simp at had_m; rcases had_m with rfl | rfl <;> (dsimp only; decide)

theorem journalRole_not_frame {F : Type} {s : PanSemStateFiniteExact 64 F} {a : Nat × String}
    (ha : a ∈ journalRoleSlots s) : a.2 ≠ "frame.addr" ∧ a.2 ≠ "frame.key" := by
  unfold journalRoleSlots at ha
  obtain ⟨_, _, hitem⟩ := List.mem_flatMap.1 ha
  simp only [List.mem_cons] at hitem
  rcases hitem with rfl | hrest
  · dsimp only; unfold journalRole; split_ifs <;> decide
  · split at hrest
    · simp at hrest; subst hrest; dsimp only; decide
    · simp at hrest

theorem worldTypedWith_erase_msg_tables {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hWT : WorldTypedWith s S Nd)
    {aa ak : Nat} (_haa_S : aa ∈ S) (_hak_S : ak ∈ S)
    (hroles : RolesOK s S (worldRoleSlots s ++ [(aa, "frame.addr"), (ak, "frame.key")]) (journalRoleSlots s)) :
    let S0 := (S.erase aa).erase ak
    aa ≠ ak ∧
    aa ∉ S0 ∧ ak ∉ S0 ∧
    (∀ t ∈ S0, t ∈ S ∧ t ≠ aa ∧ t ≠ ak) ∧
    (∀ t ∈ S, t = aa ∨ t = ak ∨ t ∈ S0) ∧
    WorldTypedWith s S0 Nd := by
  dsimp only
  set S0 := (S.erase aa).erase ak
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT
  obtain ⟨hndS, hTt, hTp, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, hboT, _⟩ := hT
  obtain ⟨hr1_s, hr2_s, hr3_s⟩ := hroles
  have haa_ne_ak : aa ≠ ak := by
    have hpw := (List.pairwise_append.1 hr2_s).2.1
    rw [List.pairwise_cons] at hpw
    intro heq
    have hsame : "frame.addr" = "frame.key" := (hpw.1 (ak, "frame.key") (by simp) heq).1
    exact absurd hsame (by decide)
  have hndS1 : (S.erase aa).Nodup := hndS.erase aa
  have hndS0 : S0.Nodup := hndS1.erase ak
  have haa_not_S0 : aa ∉ S0 := by
    intro hm
    have := List.mem_of_mem_erase hm
    exact (hndS.mem_erase_iff.1 this).1 rfl
  have hak_not_S0 : ak ∉ S0 := by
    intro hm
    exact (hndS1.mem_erase_iff.1 hm).1 rfl
  have hS0_mem : ∀ t, t ∈ S0 ↔ t ∈ S ∧ t ≠ aa ∧ t ≠ ak := by
    intro t
    simp only [S0, hndS1.mem_erase_iff, hndS.mem_erase_iff]
    tauto
  have hS_tri : ∀ t ∈ S, t = aa ∨ t = ak ∨ t ∈ S0 := by
    intro t ht
    by_cases h1 : t = aa
    · exact Or.inl h1
    · by_cases h2 : t = ak
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ((hS0_mem t).2 ⟨ht, h1, h2⟩))
  have h0_not_S : 0 ∉ S := by
    intro h0
    have hsb : 0 < sourceBase := by decide
    have hfp := (hTt 0 h0).1.1 (0, 88) (by simp [htabFootprint])
    have hlo := hfp.1.1
    change sourceBase ≤ 0 at hlo
    omega
  have hnot_wrs : ∀ a ∈ worldRoleSlots s, a.1 ≠ aa ∧ a.1 ≠ ak := by
    have hcross := (List.pairwise_append.1 hr2_s).2.2
    intro a ha
    have hnf := worldRole_not_frame ha
    exact ⟨fun heq => hnf.1 (hcross a ha (aa, "frame.addr") (by simp) heq).1,
           fun heq => hnf.2 (hcross a ha (ak, "frame.key") (by simp) heq).1⟩
  have hnot_jrs : ∀ a ∈ journalRoleSlots s, a.1 ≠ aa ∧ a.1 ≠ ak := by
    intro a ha
    have hnf := journalRole_not_frame ha
    exact ⟨fun heq => hnf.1 (hr3_s a ha (aa, "frame.addr") (by simp) heq),
           fun heq => hnf.2 (hr3_s a ha (ak, "frame.key") (by simp) heq)⟩
  have hwrs_in_S0 : ∀ a ∈ worldRoleSlots s, a.1 ∈ S0 := by
    intro a ha
    have haS := (hr1_s a (by simp [ha])).1
    obtain ⟨hne1, hne2⟩ := hnot_wrs a ha
    exact (hS0_mem a.1).2 ⟨haS, hne1, hne2⟩
  have hjrs_in_S0 : ∀ a ∈ journalRoleSlots s, a.1 ∈ S0 := by
    intro a ha
    have haS := (hr1_s a (by simp [ha])).1
    obtain ⟨hne1, hne2⟩ := hnot_jrs a ha
    exact (hS0_mem a.1).2 ⟨haS, hne1, hne2⟩
  have hroot_mem_wrs : ∀ v r, (v, r) ∈
      recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] ++
      recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"), (40, "bs+40"),
        (48, "bs+48"), (72, "bs+72")] ++
      recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"), (40, "ts+40"),
        (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] ++
      [(globN s "bal_accounts", "bal_accounts"), (globN s "bal_idx_accts", "bal_idx_accts"),
        (globN s "bal_idx_stor", "bal_idx_stor")] ++
      nestRoles s "bs" "bs.inner" ++ nestRoles s "ts" "ts.inner" ++
      ((balRecords s).flatMap fun ad => [(memW s ad, "bal.stor"), (memW s (ad + 8), "bal.reads")]) →
      v ∈ S → v ∈ S0 := by
    intro v r hmem hvS
    have hnz : v ≠ 0 := fun h0 => h0_not_S (h0 ▸ hvS)
    have hwrs : (v, r) ∈ worldRoleSlots s := by
      unfold worldRoleSlots
      exact List.mem_filter.2 ⟨hmem, by simp [hnz]⟩
    exact hwrs_in_S0 (v, r) hwrs
  have hT0 : TablesTyped s S0 := by
    refine ⟨hndS0,
      fun t ht => hTt t ((hS0_mem t).1 ht).1,
      fun t ht u hu hne => hTp t ((hS0_mem t).1 ht).1 u ((hS0_mem u).1 hu).1 hne,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, hboT, ?_⟩
    · intro k hk hnz
      rcases hwsR k hk hnz with h0 | hm
      · exact Or.inl h0
      · right
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl
        · exact hroot_mem_wrs _ "ws+16" (by
            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
            simp [recRoles, hnz]) hm
        · exact hroot_mem_wrs _ "ws+32" (by
            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
            simp [recRoles, hnz]) hm
    · intro k hk hnz
      rcases hbsR k hk hnz with h0 | hm
      · exact Or.inl h0
      · right
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact hroot_mem_wrs _ "bs+8" (by
            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
            simp [recRoles, hnz]) hm
        · exact hroot_mem_wrs _ "bs+16" (by
            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
            simp [recRoles, hnz]) hm
        · exact hroot_mem_wrs _ "bs+24" (by
            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
            simp [recRoles, hnz]) hm
        · exact hroot_mem_wrs _ "bs+32" (by
            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
            simp [recRoles, hnz]) hm
        · exact hroot_mem_wrs _ "bs+40" (by
            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
            simp [recRoles, hnz]) hm
        · exact hroot_mem_wrs _ "bs+48" (by
            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
            simp [recRoles, hnz]) hm
        · exact hroot_mem_wrs _ "bs+72" (by
            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
            simp [recRoles, hnz]) hm
    · intro k hk hnz
      rcases htsR k hk hnz with h0 | hm
      · exact Or.inl h0
      · right
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact hroot_mem_wrs _ "ts+8" (by
            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
            apply List.mem_append.2; left; apply List.mem_append.2; right
            simp [recRoles, hnz]) hm
        · exact hroot_mem_wrs _ "ts+16" (by
            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
            apply List.mem_append.2; left; apply List.mem_append.2; right
            simp [recRoles, hnz]) hm
        · exact hroot_mem_wrs _ "ts+24" (by
            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
            apply List.mem_append.2; left; apply List.mem_append.2; right
            simp [recRoles, hnz]) hm
        · exact hroot_mem_wrs _ "ts+32" (by
            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
            apply List.mem_append.2; left; apply List.mem_append.2; right
            simp [recRoles, hnz]) hm
        · exact hroot_mem_wrs _ "ts+40" (by
            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
            apply List.mem_append.2; left; apply List.mem_append.2; right
            simp [recRoles, hnz]) hm
        · exact hroot_mem_wrs _ "ts+48" (by
            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
            apply List.mem_append.2; left; apply List.mem_append.2; right
            simp [recRoles, hnz]) hm
        · exact hroot_mem_wrs _ "ts+56" (by
            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
            apply List.mem_append.2; left; apply List.mem_append.2; right
            simp [recRoles, hnz]) hm
        · exact hroot_mem_wrs _ "ts+64" (by
            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
            apply List.mem_append.2; left; apply List.mem_append.2; right
            simp [recRoles, hnz]) hm
    · intro g hg
      rcases hgR g hg with h0 | hm
      · exact Or.inl h0
      · right
        simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl
        · exact hroot_mem_wrs _ "bal_accounts" (by
            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
            apply List.mem_append.2; right; simp) hm
        · exact hroot_mem_wrs _ "bal_idx_accts" (by
            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
            apply List.mem_append.2; right; simp) hm
        · exact hroot_mem_wrs _ "bal_idx_stor" (by
            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
            apply List.mem_append.2; right; simp) hm
    · intro hnz hm0 i hi
      have hmS := ((hS0_mem _).1 hm0).1
      have h32nz : memW s (globN s "bs" + 32) ≠ 0 := fun h0 => h0_not_S (h0 ▸ hmS)
      have hvS := hbsN hnz hmS i hi
      refine hroot_mem_wrs _ "bs.inner" ?_ hvS
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
      unfold nestRoles; simp only [hnz, h32nz, ↓reduceIte]
      exact List.mem_map.2 ⟨_, List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩, rfl⟩
    · intro hnz hm0 i hi
      have hmS := ((hS0_mem _).1 hm0).1
      have h32nz : memW s (globN s "ts" + 32) ≠ 0 := fun h0 => h0_not_S (h0 ▸ hmS)
      have hvS := htsN hnz hmS i hi
      refine hroot_mem_wrs _ "ts.inner" ?_ hvS
      apply List.mem_append.2; left; apply List.mem_append.2; right
      unfold nestRoles; simp only [hnz, h32nz, ↓reduceIte]
      exact List.mem_map.2 ⟨_, List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩, rfl⟩
    · intro ad had
      obtain ⟨h0_S, h8_S, hkl, hll⟩ := hbalT ad had
      refine ⟨?_, ?_, hkl, hll⟩
      · refine hroot_mem_wrs _ "bal.stor" ?_ h0_S
        apply List.mem_append.2; right
        exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
      · refine hroot_mem_wrs _ "bal.reads" ?_ h8_S
        apply List.mem_append.2; right
        exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
    · refine ⟨?_, (List.pairwise_append.1 hr2_s).1, ?_⟩
      · intro a ha
        rcases List.mem_append.1 ha with hw | hjr
        · exact ⟨hwrs_in_S0 a hw, (hr1_s a (by simp [hw])).2⟩
        · exact ⟨hjrs_in_S0 a hjr, (hr1_s a (by simp [hjr])).2⟩
      · intro a ha b hb heq
        rcases List.mem_append.1 hb with hw | hjr
        · exact hr3_s a ha b (by simp [hw]) heq
        · exact hr3_s a ha b (by simp [hjr]) heq
  have hJ0 : JournalTyped s S0 := by
    refine ⟨hJ.1, hJ.2.1, hJ.2.2.1, fun i hi => ?_⟩
    exact hjrs_in_S0 (memW s (globN s "journal" + 32 * i), journalRole s (memW s (globN s "journal" + 32 * i))) (by
      unfold journalRoleSlots
      exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by simp⟩)
  have hTr0 : TriesTypedWith s S0 Nd := by
    refine ⟨hTr.1, fun o ho => ⟨fun t ht => (hTr.2.1 o ho).1 t ((hS0_mem t).1 ht).1, (hTr.2.1 o ho).2⟩,
      fun hnz => ⟨(hTr.2.2 hnz).1, fun hm0 => (hTr.2.2 hnz).2 ((hS0_mem _).1 hm0).1⟩⟩
  exact ⟨haa_ne_ak, haa_not_S0, hak_not_S0, fun t ht => (hS0_mem t).1 ht, hS_tri, hT0, hJ0, hF, hTr0⟩

theorem msgReady_of_worldStep_buffers {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    {callerLocals : HolFiniteMapExact MlS (ValueHOL 64)}
    (hmsg_loc : locN { post with locals := callerLocals } "msg" = locN s "msg")
    (hM : MsgReady s)
    (hstep : WorldStep R gw keep Q s r post)
    (hR : ∀ i ∈ R s, ∃ gn ∈ globalBuffers, gn.1 ∉ typedRecords.map Prod.fst ∧
      ∃ n, 0 < n ∧ n ≤ gn.2 ∧ i = bufferRegion s (gn.1, n)) :
    MsgReady { post with locals := callerLocals } := by
  obtain ⟨hAs, S, hW, h152_S, h160_S, hm_in, hm_words, hm_dtab, hm_dfix, ⟨Nd, hTr, hm_dnd⟩, hmgas, hroles⟩ := hM
  have hWT_full : WorldTypedWith s S Nd := ⟨hW.1, hW.2.1, hW.2.2.1, hTr⟩
  set m := locN s "msg"
  set aa := memW s (m + 152)
  set ak := memW s (m + 160)
  obtain ⟨haa_ne_ak, _, _, hS0_sub, _, hWT0⟩ :=
    worldTypedWith_erase_msg_tables hWT_full h152_S h160_S hroles
  set S0 := (S.erase aa).erase ak
  obtain ⟨hAp, hhp, _, _, hWS⟩ := hstep
  have hR_disj0 : IvlsDisj (R s) (worldTypedIvls s S0 Nd) := by
    intro i hi j hj
    obtain ⟨gn, hg, hu, n, _, hle, rfl⟩ := hR i hi
    exact bufferRegion_disj_le hWT0 gn hg hu n hle j hj
  obtain ⟨S0', Nd', _, hWT0', hog0, hfr0, _⟩ := hWS S0 Nd hWT0 hR_disj0
  have hR_disj_full : IvlsDisj (R s) (worldTypedIvls s S Nd) := by
    intro i hi j hj
    obtain ⟨gn, hg, hu, n, _, hle, rfl⟩ := hR i hi
    exact bufferRegion_disj_le hWT_full gn hg hu n hle j hj
  obtain ⟨S_full', _, hsub_full, hWT_full', _, _, _⟩ := hWS S Nd hWT_full hR_disj_full
  have haa_alloc_post_full : ∀ i ∈ htabFootprint post aa, Allocated post i :=
    fun i hi => ((hWT_full'.1.2.1 aa (hsub_full aa h152_S)).2 i hi).1
  have hak_alloc_post_full : ∀ i ∈ htabFootprint post ak, Allocated post i :=
    fun i hi => ((hWT_full'.1.2.1 ak (hsub_full ak h160_S)).2 i hi).1
  have hkeep_ws : ∀ j ∈ worldOwned s S0 Nd ++ R s ++ [freeGap s], j = (0, 0) ∨ j.1 % 8 = 0 ∨ j.2 ≠ 0 := by
    intro j hj
    rcases List.mem_append.1 hj with hj12 | hfg
    · rcases List.mem_append.1 hj12 with hj_ow | hj_R
      · exact worldOwned_well_shaped hWT0 j hj_ow
      · obtain ⟨gn, _, _, n, hn_pos, _, rfl⟩ := hR j hj_R
        unfold bufferRegion
        by_cases hz : globN s gn.1 = 0
        · exact Or.inl (by simp [hz])
        · exact Or.inr (Or.inr (by simp [hz]; omega))
    · simp only [List.mem_singleton] at hfg; subst hfg
      exact Or.inr (Or.inl hAs.2.2.2.2.2.2.2.1)
  have hf_ws : heapFree s = (0, 0) ∨ (heapFree s).1 % 8 = 0 ∨ (heapFree s).2 ≠ 0 :=
    Or.inr (Or.inl hAs.2.2.2.2.2.2.1)
  -- Helper: any interval `b` that is allocated in `s`, 8-aligned, and disjoint from `worldOwned s S0 Nd`
  -- is ALSO disjoint from `R s`, `freeGap s`, `heapFree s`, hence `IvlUnhit s post b` AND disjoint from `worldOwned post S0' Nd'`!
  have hsurvive : ∀ b : Ivl,
      b.1 % 8 = 0 → b.2 % 8 = 0 → Allocated s b →
      (∀ j ∈ worldOwned s S0 Nd, Disj b j) →
      (∀ j ∈ fixedObjects s, Disj b j) →
      IvlUnhit s post b ∧ ∀ o ∈ worldOwned post S0' Nd', Disj b o := by
    intro b hb1 hb2 hbal hbow hbfix
    have hb_R : ∀ j ∈ R s, Disj b j := by
      intro j hj
      obtain ⟨gn, hg, _, n, _, hle, rfl⟩ := hR j hj
      have hfix : bufferRegion s gn ∈ fixedObjects s := by
        unfold fixedObjects
        apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
        exact List.mem_map.2 ⟨gn, hg, rfl⟩
      have hd := hbfix _ hfix
      by_cases hz : globN s gn.1 = 0
      · exact Or.inr (Or.inl (by simp [bufferRegion, hz]))
      · simp only [bufferRegion, hz, ↓reduceIte] at hd ⊢
        rcases hd with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (by dsimp only at h ⊢; omega))
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (by dsimp only at h ⊢; omega)))
    have hb_fg_hf : Disj b (freeGap s) ∧ Disj b (heapFree s) := by
      have hsep : heapLimit ≤ scratchStart := by decide
      have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hAs.2.2.1
      have hss : scratchStart ≤ globN s "frame_mem_ptr" := hAs.2.2.2.1
      have hfm_sc : globN s "frame_mem_ptr" ≤ globN s "scratch_ptr" := hAs.2.2.2.2.1
      rcases hbal with ⟨_, hhi⟩ | ⟨hlo, _⟩
      · exact ⟨Or.inr (Or.inr (Or.inl (by unfold freeGap; dsimp only; omega))),
               Or.inr (Or.inr (Or.inl (by unfold heapFree; exact hhi)))⟩
      · exact ⟨Or.inr (Or.inr (Or.inr (by unfold freeGap; dsimp only; omega))),
               Or.inr (Or.inr (Or.inr (by unfold heapFree; dsimp only; omega)))⟩
    have hb_keep : ∀ j ∈ worldOwned s S0 Nd ++ R s ++ [freeGap s], Disj b j := by
      intro j hj
      rcases List.mem_append.1 hj with hj12 | hfg
      · rcases List.mem_append.1 hj12 with hj_ow | hj_R
        · exact hbow j hj_ow
        · exact hb_R j hj_R
      · simp only [List.mem_singleton] at hfg; subst hfg; exact hb_fg_hf.1
    have hu_b := ivlUnhit_of_frameOutside_wellShaped hfr0 hb1 hb2 hkeep_ws hf_ws hb_keep hb_fg_hf.2
    refine ⟨hu_b, fun o ho => ?_⟩
    rcases hog0 o ho with rfl | ⟨j, hj, hin⟩ | hfresh
    · exact disj_zero_right b
    · exact disj_of_inside_right hin (hbow j hj)
    · have hsep : heapLimit ≤ scratchStart := by decide
      have hhp_post_lim : globN post "heap_ptr" ≤ heapLimit := hAp.2.2.1
      have hss : scratchStart ≤ globN s "frame_mem_ptr" := hAs.2.2.2.1
      have hfm_sc : globN s "frame_mem_ptr" ≤ globN s "scratch_ptr" := hAs.2.2.2.2.1
      rcases hbal with ⟨_, hhi⟩ | ⟨hlo, _⟩
      · exact Or.inr (Or.inr (Or.inl (le_trans hhi hfresh.1)))
      · exact Or.inr (Or.inr (Or.inr (le_trans hfresh.2 (by omega))))
  -- Apply `hsurvive` to `(m, 176)`!
  have hm_ow0 : ∀ j ∈ worldOwned s S0 Nd, Disj (m, 176) j := by
    intro j hj
    unfold worldOwned at hj
    rcases List.mem_append.1 hj with h1 | hnd
    · rcases List.mem_append.1 h1 with htab | hfix
      · obtain ⟨t, ht0, hj_fp⟩ := List.mem_flatMap.1 htab
        exact hm_dtab t (hS0_sub t ht0).1 j hj_fp
      · exact hm_dfix j hfix
    · exact hm_dnd (m, 176) (by simp) j hnd
  obtain ⟨hu_m, hm_disj_ow0'⟩ := hsurvive (m, 176) hm_words.1 hm_words.2.1 (Or.inl hm_in) hm_ow0 hm_dfix
  have hm_hi : m + 176 ≤ 2 ^ 64 := by
    have h1 : heapLimit ≤ 2 ^ 64 := by decide
    have h2 : globN s "heap_ptr" ≤ heapLimit := hAs.2.2.1
    have h3 : m + 176 ≤ globN s "heap_ptr" := hm_in.2
    omega
  have hm8 : m % 8 = 0 := hm_words.1
  have hm152_eq : memW post (m + 152) = aa :=
    memW_eq_of_ivlUnhit hu_m (by omega) hm_hi ⟨by omega, by omega⟩
  have hm160_eq : memW post (m + 160) = ak :=
    memW_eq_of_ivlUnhit hu_m (by omega) hm_hi ⟨by omega, by omega⟩
  have hm40_eq : memW post (m + 40) = memW s (m + 40) :=
    memW_eq_of_ivlUnhit hu_m (by omega) hm_hi ⟨by omega, by omega⟩
  -- Apply `hsurvive` to every footprint interval of `aa` and `ak`!
  have htab_survive : ∀ x, x ∈ ([aa, ak] : List Nat) →
      HtabWF post x ∧ htabFootprint post x = htabFootprint s x ∧
      (∀ k, k < 11 → hdr post x k = hdr s x k) ∧
      (∀ i ∈ htabFootprint post x, Allocated post i ∧ ∀ o ∈ worldOwned post S0' Nd', Disj i o) ∧
      x ∉ S0' := by
    intro x hx
    have hx_S : x ∈ S ∧ (x = aa ∨ x = ak) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨h152_S, Or.inl rfl⟩
      · exact ⟨h160_S, Or.inr rfl⟩
    have hx_not_S0 : ∀ t ∈ S0, x ≠ t := by
      intro t ht heq
      rcases hx_S.2 with rfl | rfl
      · exact (hS0_sub t ht).2.1 heq.symm
      · exact (hS0_sub t ht).2.2 heq.symm
    have hTt_x := hW.1.2.1 x hx_S.1
    have hwf_x := hTt_x.1
    have hx_fp_surv : ∀ i ∈ htabFootprint s x,
        IvlUnhit s post i ∧ ∀ o ∈ worldOwned post S0' Nd', Disj i o := by
      intro i hi
      have hi_words := (hwf_x.1 i hi).2
      have hi_alloc := (hTt_x.2 i hi).1
      have hi_dfix := (hTt_x.2 i hi).2
      have hi_ow0 : ∀ j ∈ worldOwned s S0 Nd, Disj i j := by
        intro j hj
        unfold worldOwned at hj
        rcases List.mem_append.1 hj with h1 | hnd
        · rcases List.mem_append.1 h1 with htab | hfix
          · obtain ⟨t, ht0, hj_fp⟩ := List.mem_flatMap.1 htab
            exact hW.1.2.2.1 x hx_S.1 t (hS0_sub t ht0).1 (hx_not_S0 t ht0) i hi j hj_fp
          · exact hi_dfix j hfix
        · exact ((hTr.2.1 j hnd).1 x hx_S.1 i hi).flip
      exact hsurvive i hi_words.1 hi_words.2.1 hi_alloc hi_ow0 hi_dfix
    have hhdr_fp : (x, 88) ∈ htabFootprint s x := by simp [htabFootprint]
    have hx8 : x % 8 = 0 := (hwf_x.1 _ hhdr_fp).2.1
    have hx_hi : x + 88 ≤ 2 ^ 64 := by
      have h264 : heapEnd ≤ 2 ^ 64 := by decide
      have := (hwf_x.1 _ hhdr_fp).1.2; omega
    obtain ⟨hhdr_eq, hfp_eq⟩ := htabFootprint_eq_of_hdr_unhit hx8 hx_hi (hx_fp_surv _ hhdr_fp).1
    have hwf_post := htabWF_congr_unhit hAs.1 hAp.1 hwf_x (fun i hi => (hx_fp_surv i hi).1)
    have hx_not_S0' : x ∉ S0' := by
      intro hx0'
      have ho : (x, 88) ∈ worldOwned post S0' Nd' := by
        unfold worldOwned
        apply List.mem_append.2; left; apply List.mem_append.2; left
        exact List.mem_flatMap.2 ⟨x, hx0', by simp [htabFootprint]⟩
      have hd := (hx_fp_surv (x, 88) hhdr_fp).2 (x, 88) ho
      rcases hd with h | h | h | h
      · cases h
      · cases h
      · dsimp only at h; omega
      · dsimp only at h; omega
    refine ⟨hwf_post, hfp_eq, hhdr_eq, ?_, hx_not_S0'⟩
    intro i hi
    have hi_s : i ∈ htabFootprint s x := by rw [← hfp_eq]; exact hi
    have hal_i : Allocated post i := by
      rcases hx_S.2 with rfl | rfl
      · exact haa_alloc_post_full i hi
      · exact hak_alloc_post_full i hi
    exact ⟨hal_i, (hx_fp_surv i hi_s).2⟩
  obtain ⟨hwf_aa, hfp_aa, hhdr_aa, hdisj_aa, haa_not_S0'⟩ := htab_survive aa (by simp)
  obtain ⟨hwf_ak, hfp_ak, hhdr_ak, hdisj_ak, hak_not_S0'⟩ := htab_survive ak (by simp)
  -- Now construct `S1 := aa :: ak :: S0'` and prove `WorldTyped post S1` and `MsgReady { post with locals := callerLocals }`!
  set S1 := aa :: ak :: S0'
  obtain ⟨hT0', hJ0', hF0', hTr0'⟩ := hWT0'
  obtain ⟨hnd0', hTt0', hTp0', hwsR0', hbsR0', htsR0', hgR0', hbsN0', htsN0', hbalT0', hboT0', hroles0'⟩ := hT0'
  have hsub_S0'_S1 : ∀ t ∈ S0', t ∈ S1 := fun t ht => by simp [S1, ht]
  have hnd_S1 : S1.Nodup := by
    simp only [S1, List.nodup_cons, List.mem_cons]
    exact ⟨fun h => h.elim haa_ne_ak haa_not_S0', ⟨hak_not_S0', hnd0'⟩⟩
  have hT1 : TablesTyped post S1 := by
    refine ⟨hnd_S1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hboT0', ?_⟩
    · intro t ht
      simp only [S1, List.mem_cons] at ht
      rcases ht with rfl | rfl | ht0'
      · refine ⟨hwf_aa, fun i hi => ⟨(hdisj_aa i hi).1, fun j hj => (hdisj_aa i hi).2 j ?_⟩⟩
        unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hj)))
      · refine ⟨hwf_ak, fun i hi => ⟨(hdisj_ak i hi).1, fun j hj => (hdisj_ak i hi).2 j ?_⟩⟩
        unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hj)))
      · exact hTt0' t ht0'
    · intro t ht u hu hne i hi j hj
      have htab_ow0' : ∀ v ∈ S0', ∀ k ∈ htabFootprint post v, k ∈ worldOwned post S0' Nd' := by
        intro v hv k hk
        unfold worldOwned; apply List.mem_append.2; left; apply List.mem_append.2; left
        exact List.mem_flatMap.2 ⟨v, hv, hk⟩
      simp only [S1, List.mem_cons] at ht hu
      rcases ht with rfl | rfl | ht0'
      · rcases hu with rfl | rfl | hu0'
        · exact absurd rfl hne
        · rw [hfp_aa] at hi; rw [hfp_ak] at hj
          exact hW.1.2.2.1 aa h152_S ak h160_S haa_ne_ak i hi j hj
        · exact (hdisj_aa i hi).2 j (htab_ow0' u hu0' j hj)
      · rcases hu with rfl | rfl | hu0'
        · rw [hfp_ak] at hi; rw [hfp_aa] at hj
          exact hW.1.2.2.1 ak h160_S aa h152_S haa_ne_ak.symm i hi j hj
        · exact absurd rfl hne
        · exact (hdisj_ak i hi).2 j (htab_ow0' u hu0' j hj)
      · rcases hu with rfl | rfl | hu0'
        · exact ((hdisj_aa j hj).2 i (htab_ow0' t ht0' i hi)).flip
        · exact ((hdisj_ak j hj).2 i (htab_ow0' t ht0' i hi)).flip
        · exact hTp0' t ht0' u hu0' hne i hi j hj
    · intro k hk hnz
      exact (hwsR0' k hk hnz).imp id (hsub_S0'_S1 _)
    · intro k hk hnz
      exact (hbsR0' k hk hnz).imp id (hsub_S0'_S1 _)
    · intro k hk hnz
      exact (htsR0' k hk hnz).imp id (hsub_S0'_S1 _)
    · intro g hg
      exact (hgR0' g hg).imp id (hsub_S0'_S1 _)
    · intro hnz hm1 i hi
      have hm0' : memW post (globN post "bs" + 32) ∈ S0' := by
        rcases hbsR0' 32 (by simp [bsTableSlots]) hnz with h0 | hm0'
        · simp only [S1, List.mem_cons] at hm1
          exfalso
          have h0_ne : ∀ v, HtabWF post v → v ≠ 0 := by
            intro v hwf rfl
            have hsb : 0 < sourceBase := by decide
            have hlo := (hwf.1 (0, 88) (by simp [htabFootprint])).1.1
            change sourceBase ≤ 0 at hlo; omega
          rcases hm1 with heq | heq | hm0''
          · exact h0_ne aa hwf_aa (heq ▸ h0)
          · exact h0_ne ak hwf_ak (heq ▸ h0)
          · exact h0_ne _ (hTt0' _ hm0'').1 h0
        · exact hm0'
      exact hsub_S0'_S1 _ (hbsN0' hnz hm0' i hi)
    · intro hnz hm1 i hi
      have hm0' : memW post (globN post "ts" + 32) ∈ S0' := by
        rcases htsR0' 32 (by simp [tsTableSlots]) hnz with h0 | hm0'
        · simp only [S1, List.mem_cons] at hm1
          exfalso
          have h0_ne : ∀ v, HtabWF post v → v ≠ 0 := by
            intro v hwf rfl
            have hsb : 0 < sourceBase := by decide
            have hlo := (hwf.1 (0, 88) (by simp [htabFootprint])).1.1
            change sourceBase ≤ 0 at hlo; omega
          rcases hm1 with heq | heq | hm0''
          · exact h0_ne aa hwf_aa (heq ▸ h0)
          · exact h0_ne ak hwf_ak (heq ▸ h0)
          · exact h0_ne _ (hTt0' _ hm0'').1 h0
        · exact hm0'
      exact hsub_S0'_S1 _ (htsN0' hnz hm0' i hi)
    · intro ad had
      obtain ⟨h0, h8, hkl, hll⟩ := hbalT0' ad had
      exact ⟨hsub_S0'_S1 _ h0, hsub_S0'_S1 _ h8, hkl, hll⟩
    · refine ⟨fun a ha => ⟨hsub_S0'_S1 _ (hroles0'.1 a ha).1, (hroles0'.1 a ha).2⟩,
        hroles0'.2.1, hroles0'.2.2⟩
  have hJ1 : JournalTyped post S1 :=
    ⟨hJ0'.1, hJ0'.2.1, hJ0'.2.2.1, fun i hi => hsub_S0'_S1 _ (hJ0'.2.2.2 i hi)⟩
  have hTr1 : TriesTypedWith post S1 Nd' := by
    refine ⟨hTr0'.1, fun o ho => ⟨?_, (hTr0'.2.1 o ho).2⟩, fun hnz => ⟨(hTr0'.2.2 hnz).1, fun hm1 => ?_⟩⟩
    · intro t ht i hi
      simp only [S1, List.mem_cons] at ht
      have ho_ow0' : o ∈ worldOwned post S0' Nd' := by
        unfold worldOwned; exact List.mem_append.2 (Or.inr ho)
      rcases ht with rfl | rfl | ht0'
      · exact ((hdisj_aa i hi).2 o ho_ow0').flip
      · exact ((hdisj_ak i hi).2 o ho_ow0').flip
      · exact (hTr0'.2.1 o ho).1 t ht0' i hi
    · have hm0' : memW post (globN post "ws" + 32) ∈ S0' := by
        rcases hwsR0' 32 (by simp [wsTableSlots]) hnz with h0 | hm0'
        · simp only [S1, List.mem_cons] at hm1
          exfalso
          have h0_ne : ∀ v, HtabWF post v → v ≠ 0 := by
            intro v hwf rfl
            have hsb : 0 < sourceBase := by decide
            have hlo := (hwf.1 (0, 88) (by simp [htabFootprint])).1.1
            change sourceBase ≤ 0 at hlo; omega
          rcases hm1 with heq | heq | hm0''
          · exact h0_ne aa hwf_aa (heq ▸ h0)
          · exact h0_ne ak hwf_ak (heq ▸ h0)
          · exact h0_ne _ (hTt0' _ hm0'').1 h0
        · exact hm0'
      exact (hTr0'.2.2 hnz).2 hm0'
  -- Assemble `RolesOK post S1 (worldRoleSlots post ++ [(aa, "frame.addr"), (ak, "frame.key")]) (journalRoleSlots post)`:
  have haa_klen : hdr post aa 0 = roleKeyLen "frame.addr" := by
    rw [hhdr_aa 0 (by omega)]
    exact (hroles.1 (aa, "frame.addr") (by simp)).2
  have hak_klen : hdr post ak 0 = roleKeyLen "frame.key" := by
    rw [hhdr_ak 0 (by omega)]
    exact (hroles.1 (ak, "frame.key") (by simp)).2
  have hroles1 : RolesOK post S1
      (worldRoleSlots post ++ [(aa, "frame.addr"), (ak, "frame.key")])
      (journalRoleSlots post) := by
    obtain ⟨hr1_0', hr2_0', hr3_0'⟩ := hroles0'
    have hnot_aa_ak : ∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ aa ∧ a.1 ≠ ak := by
      intro a ha
      have ha0' : a.1 ∈ S0' := (hr1_0' a ha).1
      exact ⟨fun heq => haa_not_S0' (heq ▸ ha0'), fun heq => hak_not_S0' (heq ▸ ha0')⟩
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      rw [List.append_assoc] at ha
      rcases List.mem_append.1 ha with hw | hrest
      · have h := hr1_0' a (List.mem_append.2 (Or.inl hw))
        exact ⟨hsub_S0'_S1 _ h.1, h.2⟩
      · rcases List.mem_append.1 hrest with hfk | hjr
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfk
          rcases hfk with rfl | rfl
          · exact ⟨by simp [S1], haa_klen⟩
          · exact ⟨by simp [S1], hak_klen⟩
        · have h := hr1_0' a (List.mem_append.2 (Or.inr hjr))
          exact ⟨hsub_S0'_S1 _ h.1, h.2⟩
    · rw [List.pairwise_append]
      refine ⟨hr2_0', ?_, ?_⟩
      · rw [List.pairwise_cons]
        refine ⟨fun b hb heq => ?_, List.pairwise_singleton _ _⟩
        simp only [List.mem_singleton] at hb; subst hb
        exact absurd heq haa_ne_ak
      · intro a ha b hb heq
        have hne := hnot_aa_ak a (List.mem_append.2 (Or.inl ha))
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · exact absurd heq hne.1
        · exact absurd heq hne.2
    · intro a ha b hb heq
      rw [List.append_assoc] at hb
      rcases List.mem_append.1 hb with hw | hrest
      · exact hr3_0' a ha b (List.mem_append.2 (Or.inl hw)) heq
      · rcases List.mem_append.1 hrest with hfk | hjr
        · have hne := hnot_aa_ak a (List.mem_append.2 (Or.inr ha))
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hfk
          rcases hfk with rfl | rfl
          · exact absurd heq hne.1
          · exact absurd heq hne.2
        · exact hr3_0' a ha b (List.mem_append.2 (Or.inr hjr)) heq
  -- Assemble `MsgReady { post with locals := callerLocals }`:
  set res := ({ post with locals := callerLocals } : PanSemStateFiniteExact 64 F)
  have hres_A : ArenaReady res := localsFree_arenaReady post callerLocals post.clock hAp
  have hres_W : WorldTyped res S1 :=
    (worldTyped_with_locals post callerLocals post.clock S1).2 ⟨hT1, hJ1, hF0', Nd', hTr1⟩
  refine ⟨hres_A, S1, hres_W, ?_⟩
  rw [hmsg_loc]
  change memW post (m + 152) ∈ S1 ∧ memW post (m + 160) ∈ S1 ∧
    Inside (m, 176) sourceBase (globN post "heap_ptr") ∧ WordsOK res (m, 176) ∧
    (∀ t ∈ S1, ∀ i ∈ htabFootprint post t, Disj (m, 176) i) ∧
    (∀ j ∈ fixedObjects post, Disj (m, 176) j) ∧
    AvoidsTries res S1 [(m, 176)] ∧
    memW post (m + 40) < 2 ^ 63 ∧
    RolesOK post S1 (worldRoleSlots post ++
      [(memW post (m + 152), "frame.addr"), (memW post (m + 160), "frame.key")])
      (journalRoleSlots post)
  rw [hm152_eq, hm160_eq, hm40_eq]
  refine ⟨by simp [S1], by simp [S1], ⟨hm_in.1, le_trans hm_in.2 hhp⟩,
    wordsOK_transfer hAs.1 hres_A.1 hm_words, ?_, ?_, ?_, hmgas, hroles1⟩
  · intro t ht i hi
    simp only [S1, List.mem_cons] at ht
    rcases ht with rfl | rfl | ht0'
    · rw [hfp_aa] at hi; exact hm_dtab aa h152_S i hi
    · rw [hfp_ak] at hi; exact hm_dtab ak h160_S i hi
    · exact hm_disj_ow0' i (by
        unfold worldOwned; apply List.mem_append.2; left; apply List.mem_append.2; left
        exact List.mem_flatMap.2 ⟨t, ht0', hi⟩)
  · intro j hj
    exact hm_disj_ow0' j (by
      unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hj))))
  · have hTr1_res : TriesTypedWith res S1 Nd' := hTr1
    refine ⟨Nd', hTr1_res, fun o ho j hj => ?_⟩
    simp only [List.mem_singleton] at ho; subst ho
    exact hm_disj_ow0' j (by unfold worldOwned; exact List.mem_append.2 (Or.inr hj))

theorem worldStep_with_locals {F : Type}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)}
    (loc : HolFiniteMapExact MlS (ValueHOL 64))
    (hR_loc : R { s with locals := loc } = R s)
    (h : WorldStep R gw keep NoExtra s r post) :
    WorldStep R gw keep NoExtra { s with locals := loc } r post := by
  obtain ⟨hAp, hhp, hG, hK, hWS⟩ := h
  refine ⟨hAp, hhp, hG, ?_, ?_⟩
  · intro rec hrec hgnz k hk hnc
    exact hK rec hrec hgnz k hk (fun i hi => hnc i (by change i ∈ R { s with locals := loc }; rw [hR_loc]; exact hi))
  · intro S Nd hWT hD
    have hWT_s : WorldTypedWith s S Nd := by
      simp only [WorldTypedWith, tablesTyped_with_locals] at hWT
      exact hWT
    have hD_s : IvlsDisj (R s) (worldTypedIvls s S Nd) := by
      intro i hi j hj
      exact hD i (by change i ∈ R { s with locals := loc }; rw [hR_loc]; exact hi) j hj
    obtain ⟨S', Nd', hsub, hWT', hog, hfr, _⟩ := hWS S Nd hWT_s hD_s
    refine ⟨S', Nd', hsub, hWT', hog, ?_, trivial⟩
    intro a hkeep hfresh
    apply hfr a
    · intro i hi
      apply hkeep i
      change i ∈ worldOwned s S Nd ++ R { s with locals := loc } ++ [freeGap s]
      rw [hR_loc]
      exact hi
    · exact hfresh

theorem hoare_call_msgReady_worldKeeps
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {fname : MlS}
    (hk : WorldKeeps WorldOK R gw keep NoExtra fname)
    (hR_loc : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) loc, R { s with locals := loc } = R s)
    (hR : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) i, i ∈ R s →
      ∃ gn ∈ globalBuffers, gn.1 ∉ typedRecords.map Prod.fst ∧
        ∃ n, 0 < n ∧ n ≤ gn.2 ∧ i = bufferRegion s (gn.1, n))
    (arguments : List (ExpHOL 64)) :
    Hoare MsgReady (.call (some (none, none)) fname arguments) (fun r t => r = none → MsgReady t) := by
  refine Hoare.call0 hk (callEntryOn_of_imp localsFree_worldOK msgReady_worldOK _ _) ?_
    (fun _ _ hr _ h => absurd h hr)
  intro F s callee post v _ hM hq _
  have hstep_entry := hq (Or.inl ⟨v, rfl⟩)
  let s_mid : PanSemStateFiniteExact 64 F := { callEntryStateHOLFinite s callee with locals := s.locals }
  have hstep_mid : WorldStep R gw keep NoExtra s_mid (some (.returned v)) post :=
    worldStep_with_locals s.locals (hR_loc _ s.locals) hstep_entry
  have hM_mid : MsgReady s_mid := by
    have heq : s_mid = { s with locals := s.locals, clock := s.clock - 1 } := rfl
    rw [heq]
    exact localsOnly_msgReady s s.locals (s.clock - 1) (fun _ _ => rfl) hM
  have hloc_eq : locN { post with locals := s.locals } "msg" = locN s_mid "msg" := rfl
  exact msgReady_of_worldStep_buffers hloc_eq hM_mid hstep_mid (hR s_mid)

theorem gbody_process_create_message_proof :
    (TerminatingFunBoundedOn GuestInv (ofString "create_finish") K.«create_finish») →
    (TerminatingFunBoundedOn GuestInv (ofString "destroy_storage") K.«destroy_storage») →
    (TerminatingFunBoundedOn GuestInv (ofString "frame_halt") K.«frame_halt») →
    (TerminatingFunBoundedOn GuestInv (ofString "increment_nonce") K.«increment_nonce») →
    (TerminatingFunBoundedOn GuestInv (ofString "mark_account_created") K.«mark_account_created») →
    (TerminatingFunBoundedOn MsgReady (ofString "process_message") K.«process_message») →
    (TerminatingFunBoundedOn GuestInv (ofString "refill_frame_state_gas") K.«refill_frame_state_gas») →
    (TerminatingFunBoundedOn GuestInv (ofString "state_restore") K.«state_restore») →
    (TerminatingFunBoundedOn GuestInv (ofString "state_snapshot") K.«state_snapshot») →
    (WorldKeeps WorldOK (fun s => [(globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
      ["heap_ptr", "journal_n"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "destroy_storage")) →
    (WorldKeeps WorldOK (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
      ["heap_ptr", "journal_n", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "increment_nonce")) →
    (WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "mark_account_created")) →
    (ReadOnlyFn (ofString "state_snapshot")) →
    TerminatingFunBoundedOn MsgReady (ofString "process_create_message") K.«process_create_message» := by
  intro hcf hds hfh hin hmac hpm hrf hsr hsnap wk_ds wk_in wk_mac hro_snap
  have msgReady_guestInv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), MsgReady s → GuestInv s :=
    fun s h => h.1.1
  have hpm_entry : CallEntryOn MsgReady MsgReady (ofString "process_message")
      [.var .local (ofString "msg")] := by
    apply callEntryOn_msgReady_process_message
    have hl := lookup_process_message
    rcases hfn : (sourceFunctionEntry Guest.Software.guestFn_process_message).2 with ⟨ps, b, r⟩
    rw [hfn] at hl
    have hps : ps = [(ofString "msg", .one)] := by
      have h1 := congrArg Prod.fst hfn
      simp [sourceFunctionEntry, Guest.Software.guestFn_process_message,
        InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural] at h1
      exact h1.symm
    subst hps
    exact ⟨b, r, hl⟩
  have hhoare_ds : Hoare MsgReady
      (.call (some (none, none)) (ofString "destroy_storage") [.var .local (ofString "target")])
      (fun r t => r = none → MsgReady t) := by
    refine hoare_call_msgReady_worldKeeps wk_ds (fun _ _ => rfl) ?_ _
    intro F s i hi
    change i ∈ [bufferRegion s ("sk_buf", 52)] at hi
    simp only [List.mem_singleton] at hi
    subst hi
    exact ⟨("sk_buf", 64), by decide, by decide, 52, by decide, by decide, rfl⟩
  have hhoare_mac : Hoare MsgReady
      (.call (some (none, none)) (ofString "mark_account_created") [.var .local (ofString "target")])
      (fun r t => r = none → MsgReady t) := by
    refine hoare_call_msgReady_worldKeeps wk_mac (fun _ _ => rfl) ?_ _
    intro F s i hi; simp at hi
  have hhoare_in : Hoare MsgReady
      (.call (some (none, none)) (ofString "increment_nonce") [.var .local (ofString "target")])
      (fun r t => r = none → MsgReady t) := by
    refine hoare_call_msgReady_worldKeeps wk_in (fun _ _ => rfl) ?_ _
    intro F s i hi
    change i ∈ [bufferRegion s ("keccak_pad", 136), bufferRegion s ("keccak_st", 200),
      bufferRegion s ("mpt_nib_scratch", 64), bufferRegion s ("sk_buf", 52)] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact ⟨("keccak_pad", 136), by decide, by decide, 136, by decide, le_rfl, rfl⟩
    · exact ⟨("keccak_st", 200), by decide, by decide, 200, by decide, le_rfl, rfl⟩
    · exact ⟨("mpt_nib_scratch", 64), by decide, by decide, 64, by decide, le_rfl, rfl⟩
    · exact ⟨("sk_buf", 64), by decide, by decide, 52, by decide, by decide, rfl⟩
  refine ⟨_, _, _, lookup_process_create_message, ?_⟩
  simp only [InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.decCall_on hsnap _ _ _
      (callEntryOn_of_imp localsFree_guestInv msgReady_guestInv _ _)
      (ReadOnlyFn.resumeOn localsOnly_msgReady msgReady_guestInv hro_snap _ (by decide) _)
      (TerminatingProgBoundedOn.dec_onLocals localsOnly_msgReady _ (by decide) _ _
        (TerminatingProgBoundedOn.seq_hoare
          (TerminatingProgBoundedOn.call_on hds _ _
            (callEntryOn_of_imp localsFree_guestInv msgReady_guestInv _ _))
          hhoare_ds
          (TerminatingProgBoundedOn.seq_hoare
            (TerminatingProgBoundedOn.call_on hmac _ _
              (callEntryOn_of_imp localsFree_guestInv msgReady_guestInv _ _))
            hhoare_mac
            (TerminatingProgBoundedOn.seq_hoare
              (TerminatingProgBoundedOn.call_on hin _ _
                (callEntryOn_of_imp localsFree_guestInv msgReady_guestInv _ _))
              hhoare_in
              (TerminatingProgBoundedOn.decCall_on hpm _ _ _
                hpm_entry
                (decCallResumeOn_guestInv msgReady_guestInv _ _ _)
                (TerminatingProgBoundedOn.seq_guestInv
                  (TerminatingProgBoundedOn.ite_on
                    (TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _
                      (TerminatingProgBoundedOn.seq_guestInv
                        (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
                        (TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _
                          (TerminatingProgBoundedOn.seq_guestInv
                            (TerminatingProgBoundedOn.callHandle_guestInv hcf _ _ _
                              (TerminatingProgBoundedOn.seq_guestInv
                                (TerminatingProgBoundedOn.call_guestInv hsr _ _)
                                (TerminatingProgBoundedOn.seq_guestInv
                                  (TerminatingProgBoundedOn.call_guestInv hrf _ _)
                                  (TerminatingProgBoundedOn.seq_guestInv
                                    (TerminatingProgBoundedOn.call_guestInv hfh _ _)
                                    (TerminatingProgBoundedOn.seq_guestInv
                                      (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                      (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))))))
                              _)
                            (TerminatingProgBoundedOn.seq_guestInv
                              (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
                              (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))))))
                    (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
                  (TerminatingProgBoundedOn.seq_guestInv
                    (TerminatingProgBoundedOn.call_guestInv hsr _ _)
                    (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))))))))) ?_
  unfold K.«process_create_message»
  simp only [show ∀ a b : Nat, Nat.max a b = max a b from fun _ _ => rfl]
  omega

end InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyProcessMsg
