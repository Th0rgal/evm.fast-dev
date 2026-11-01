import InitECandidate.Solver.Wave8GuestInv.ContractParts.C14

/-! Helper lemmas and concrete-body composition proofs for `gbody_get_storage`,
`gbody_op_sload`, and `gbody_op_sstore` (`ContractParts/C15.lean`, R10). -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1500000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyStorageOps

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Backend
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. Installed function lookups -/

theorem lookup_htab_set :
    originalRuntimeCode.lookup (ofString "htab_set") =
      some ((sourceFunctionEntry Guest.Software.guestFn_htab_set).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 138 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_set) rfl

theorem lookup_get_storage :
    originalRuntimeCode.lookup (ofString "get_storage") =
      some ((sourceFunctionEntry Guest.Software.guestFn_get_storage).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 378 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_get_storage) rfl

theorem lookup_op_sload :
    originalRuntimeCode.lookup (ofString "op_sload") =
      some ((sourceFunctionEntry Guest.Software.guestFn_op_sload).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 527 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_op_sload) rfl

theorem lookup_op_sstore :
    originalRuntimeCode.lookup (ofString "op_sstore") =
      some ((sourceFunctionEntry Guest.Software.guestFn_op_sstore).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 528 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_op_sstore) rfl

/-! ## 2. Call-parameter and combinator helpers -/

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

theorem callee_param_three_first {F : Type} (state : PanSemStateFiniteExact 64 F)
    (fname p1 p2 p3 : MlS) (s1 s2 s3 : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname = some ([(p1, s1), (p2, s2), (p3, s3)], body, ret))
    (e1 e2 e3 : ExpHOL 64)
    (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [e1, e2, e3] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    ∃ v1, evalAt state e1 = some v1 ∧ callee.lookup p1 = some v1 := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact] at hargs
  rcases he1 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e1 with _ | v1
  · simp [he1] at hargs
  · rcases he2 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e2 with _ | v2
    · simp [he1, he2] at hargs
    · rcases he3 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e3 with _ | v3
      · simp [he1, he2, he3] at hargs
      · simp only [he1, he2, he3, Option.some.injEq] at hargs
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
            refine ⟨v1, he1, ?_⟩
            simp [List.zip, List.foldl, hnd.1.1, hnd.1.2]
          · cases raw

theorem TerminatingProgBoundedOn.mono_pre {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {prog : ProgHOL 64} {K : Nat}
    (himp : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q s)
    (h : TerminatingProgBoundedOn Q prog K) :
    TerminatingProgBoundedOn P prog K :=
  fun s hc hP => h s hc (himp s hP)

/-- Handler-free call with an optional destination (`call (some (dest, none)) fname args`)
whose callee keeps a locals-free guard `W`. Note that when `dest = some (.local, x)` only
locals change; for `dest = none` nothing extra changes. -/
theorem Hoare.call_local_keeps {W : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hW : LocalsFree W) {fname : MlS} {arguments : List (ExpHOL 64)}
    (hk : KeepsOn Pc W fname) (hentry : CallEntryOn W Pc fname arguments)
    (varName : MlS) :
    Hoare W (.call (some (some (.local, varName), none)) fname arguments)
      (fun r t => r = none → W t) := by
  refine ⟨fun {F} s hcode hP hnt hr => ?_⟩
  rcases hout : evaluateHOLFiniteState s
      (.call (some (some (.local, varName), none)) fname arguments) with ⟨r_out, t_out⟩
  have hr' : r_out = none := by rw [hout] at hr; exact hr
  subst hr'
  change W t_out
  rw [evaluateHOLFiniteState_call] at hout
  rcases hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments with _ | values
  · rw [hargs] at hout; simp at hout
  · rw [hargs] at hout; dsimp only at hout
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · rw [hl] at hout; simp at hout
    · rw [hl] at hout; dsimp only at hout
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hout; simp at hout
      · rw [if_neg hz] at hout
        have hPc := hentry s values body' callee ret' hcode hP hargs hl
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        rw [hrun] at hout
        cases res with
        | none => simp at hout
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hout
            split at hout
            · split at hout
              · injection hout with _ hteq
                rw [← hteq]
                have hQc := FunSpec.at_lookup hk s hcode values body' callee ret' hl hPc
                  (by rw [hrun]; simp)
                rw [hrun] at hQc
                have hWpost : W post := hQc (Or.inl ⟨v, rfl⟩)
                simpa [setKvarHOLFinite, setVarHOLFinite] using
                  hW post (s.locals.update (varName, v)) post.clock hWpost
              · simp at hout
            · simp at hout
          | _ => simp [emptyLocalsHOLFinite] at hout

theorem Hoare.call0_keeps_entry {W Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hW : LocalsFree W) {fname : MlS} {arguments : List (ExpHOL 64)}
    (hk : KeepsOn Pc W fname) (hentry : CallEntryOn W Pc fname arguments) :
    Hoare W (.call (some (none, none)) fname arguments) (fun r t => r = none → W t) :=
  Hoare.call0 hk hentry
    (fun s _ post v _ _ hq _ => hW post s.locals post.clock (hq (Or.inl ⟨v, rfl⟩)))
    (fun _ _ hr _ h => absurd h hr)

theorem KeepsOn.resumeOn_entry {W Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hW : LocalsFree W) {fname : MlS} {arguments : List (ExpHOL 64)}
    (hk : KeepsOn Pc W fname) (hentry : CallEntryOn W Pc fname arguments) (name : MlS) :
    DecCallResumeOn W W name fname arguments := by
  intro F state values body callee ret value post hcode hP hargs hl hrun
  have hPc := hentry state values body callee ret hcode hP hargs hl
  have hQc := FunSpec.at_lookup hk state hcode values body callee ret hl hPc (by rw [hrun]; simp)
  rw [hrun] at hQc
  have hWpost : W post := hQc (Or.inl ⟨value, rfl⟩)
  simpa [setVarHOLFinite] using hW post (state.locals.update (name, value)) post.clock hWpost

theorem Hoare.seq_fall {P R Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {first second : ProgHOL 64}
    (h1 : Hoare P first (fun r t => r = none → R t))
    (h2 : Hoare R second (fun r t => r = none → Q t)) :
    Hoare P (.seq first second) (fun r t => r = none → Q t) :=
  Hoare.seq ⟨fun s hc hP hnt => ⟨h1.run s hc hP hnt, fun hr h => absurd h hr⟩⟩ h2

theorem Hoare.ite_keeps {W : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {cond : ExpHOL 64} {yes no : ProgHOL 64}
    (hyes : Hoare W yes (fun r t => r = none → W t))
    (hno : Hoare W no (fun r t => r = none → W t)) :
    Hoare W (.ite cond yes no) (fun r t => r = none → W t) :=
  Hoare.ite (Hoare.mono hyes (fun _ h => h.1)) (Hoare.mono hno (fun _ h => h.1))
    (fun _ _ hr => absurd hr (by simp))

theorem Hoare.assign_local_keeps {W : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hW : LocalsFree W) (name : MlS) (e : ExpHOL 64) :
    Hoare W (.assign .local name e) (fun r t => r = none → W t) :=
  Hoare.assign
    (fun s v hP _ _ => by
      have := hW s (s.locals.update (name, v)) s.clock hP
      simpa [setKvarHOLFinite, setVarHOLFinite] using this)
    (fun _ _ hr => absurd hr (by simp))

/-! ## 3. Ordinary-domain and cell-unhit congruence (`W1` + `W2` for `"ts+24"`) -/

theorem ordinaryDomain_iff (x : BitVec 64) :
    ordinaryDomain x ↔ x.toNat % 8 = 0 ∧ sourceBase ≤ x.toNat ∧ x.toNat < heapEnd := by
  unfold ordinaryDomain
  rw [StackRemove.mem_addresses]
  have hx := x.isLt
  have hconst : (stackStart - sourceBase) / 8 - globalsWords = 3888119741 ∧
      sourceBase = 2701131776 ∧ heapEnd = 33806089704 ∧
      StackRemove.bytesInWord 64 = BitVec.ofNat 64 8 :=
    ⟨by decide, by decide, by decide, by decide⟩
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
  ∀ a : BitVec 64, a.toNat % 8 = 0 → CellHits a.toNat i → post.memory a = s.memory a

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

theorem memW_eq_of_ivlUnhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {i : Ivl} (hu : IvlUnhit s post i) {a : Nat}
    (ha8 : a % 8 = 0) (hhi : i.1 + i.2 ≤ 2 ^ 64) (hin : i.1 ≤ a ∧ a + 8 ≤ i.1 + i.2) :
    memW post a = memW s a := by
  have ha_lt : a < 2 ^ 64 := by omega
  have hmem := hu (BitVec.ofNat 64 a)
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]; exact ha8)
    (by unfold CellHits; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]; omega)
  unfold memW
  rw [hmem]

theorem aligned_cell_in_aligned_ivl {x j1 j2 : Nat}
    (hx8 : x % 8 = 0) (hj1 : j1 % 8 = 0) (hj2 : j2 % 8 = 0)
    (h1 : j1 < x + 8) (h2 : x < j1 + j2) :
    j1 ≤ x ∧ x + 8 ≤ j1 + j2 :=
  ⟨by omega, by omega⟩

def BytesSame {F : Type} (s post : PanSemStateFiniteExact 64 F) (i : Ivl) : Prop :=
  ∀ a : Nat, a < i.2 → memB post (i.1 + a) = memB s (i.1 + a)

theorem bytesSame_of_frameOutside {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {keep : List Ivl} {fresh i : Ivl}
    (hbe : post.be = s.be)
    (hi_hi : i.1 + i.2 ≤ 2 ^ 64)
    (hfr : FrameOutside s post keep fresh)
    (hk_al : ∀ j ∈ keep, j.1 % 8 = 0 ∧ j.2 % 8 = 0)
    (hf_al : fresh.1 % 8 = 0 ∧ fresh.2 % 8 = 0)
    (hk : ∀ j ∈ keep, Disj i j) (hf : Disj i fresh) :
    BytesSame s post i := by
  intro k hk_lt
  have ha_lt : i.1 + k < 2 ^ 64 := by omega
  let c := panByteAlignHOL (BitVec.ofNat 64 (i.1 + k))
  have hc_nat : c.toNat = (i.1 + k) / 8 * 8 := by
    have hal : 2 ^ ((64 : Nat) / 8).log2 = 8 := by decide
    change (BitVec.ofNat 64 ((BitVec.ofNat 64 (i.1 + k)).toNat / 2 ^ ((64 : Nat) / 8).log2 *
      2 ^ ((64 : Nat) / 8).log2)).toNat = (i.1 + k) / 8 * 8
    rw [hal, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt,
      Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self _ 8) ha_lt)]
  have hc8 : c.toNat % 8 = 0 := by rw [hc_nat]; omega
  have hmem := hfr c
    (fun j hj hcj => by
      obtain ⟨hja1, hja2⟩ := hk_al j hj
      obtain ⟨hj_lo, hj_hi⟩ := aligned_cell_in_aligned_ivl hc8 hja1 hja2 hcj.1 hcj.2
      rw [hc_nat] at hj_lo hj_hi
      rcases hk j hj with hd | hd | hd | hd <;> omega)
    (fun hcf => by
      obtain ⟨hf_lo, hf_hi⟩ := aligned_cell_in_aligned_ivl hc8 hf_al.1 hf_al.2 hcf.1 hcf.2
      rw [hc_nat] at hf_lo hf_hi
      rcases hf with hd | hd | hd | hd <;> omega)
  unfold memB
  change (match post.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 (i.1 + k)) v post.be).toNat) =
         (match s.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 (i.1 + k)) v s.be).toNat)
  rw [hmem, hbe]

theorem ivlUnhit_of_frameOutside {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {keep : List Ivl} {fresh i : Ivl}
    (hi_al : i.1 % 8 = 0 ∧ i.2 % 8 = 0)
    (hfr : FrameOutside s post keep fresh)
    (hk_al : ∀ j ∈ keep, j.1 % 8 = 0 ∧ j.2 % 8 = 0)
    (hf_al : fresh.1 % 8 = 0 ∧ fresh.2 % 8 = 0)
    (hk : ∀ j ∈ keep, Disj i j) (hf : Disj i fresh) :
    IvlUnhit s post i := by
  obtain ⟨hia1, hia2⟩ := hi_al
  intro a ha8 hhit
  obtain ⟨hi_lo, hi_hi⟩ := aligned_cell_in_aligned_ivl ha8 hia1 hia2 hhit.1 hhit.2
  apply hfr a
  · intro j hj hcj
    obtain ⟨hja1, hja2⟩ := hk_al j hj
    obtain ⟨hj_lo, hj_hi⟩ := aligned_cell_in_aligned_ivl ha8 hja1 hja2 hcj.1 hcj.2
    rcases hk j hj with hd | hd | hd | hd <;> omega
  · intro hcf
    obtain ⟨hf_lo, hf_hi⟩ := aligned_cell_in_aligned_ivl ha8 hf_al.1 hf_al.2 hcf.1 hcf.2
    rcases hf with hd | hd | hd | hd <;> omega

theorem freeChain_congr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {nodes ncap : Nat} (hn8 : nodes % 8 = 0) (hhi : nodes + (ncap + 1) * 32 ≤ 2 ^ 64)
    (hu : IvlUnhit s post (nodes, (ncap + 1) * 32)) :
    ∀ (Fr : List Nat) (head : Nat),
      (∀ f ∈ Fr, 1 ≤ f ∧ f ≤ ncap) →
      (FreeChain post nodes head Fr ↔ FreeChain s nodes head Fr)
  | [], _, _ => Iff.rfl
  | f :: rest, _, hFr => by
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
    {t : Nat} {S : List Nat} (hwf : HtabWF s t)
    (hu : ∀ i ∈ htabFootprint s t, IvlUnhit s post i)
    (hval : HtabValuesIn s t S) :
    HtabValuesIn post t S := by
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
  exact hmem_s

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

def WorldGlobalsSame {F : Type} (s post : PanSemStateFiniteExact 64 F) : Prop :=
  (∀ gn ∈ globalBuffers, globN post gn.1 = globN s gn.1) ∧
  (∀ g ∈ globalTableRoots, globN post g = globN s g) ∧
  globN post "journal" = globN s "journal" ∧
  globN post "journal_cap" = globN s "journal_cap" ∧
  globN post "journal_n" = globN s "journal_n"

theorem globN_eq_of_lookup {F : Type} {s post : PanSemStateFiniteExact 64 F} {name : String}
    (h : s.globals.lookup (ofString name) = post.globals.lookup (ofString name)) :
    globN post name = globN s name := by
  simp only [globN, ← h]

theorem worldGlobalsSame_of_nonHeap {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hg : ∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
      s.globals.lookup k = post.globals.lookup k) :
    WorldGlobalsSame s post := by
  have hgn : ∀ name, ofString name ≠ ofString "heap_ptr" → globN post name = globN s name :=
    fun name hne => globN_eq_of_lookup (hg (ofString name) (by simp [hne]))
  have hgb_ne : ∀ p ∈ globalBuffers, ofString p.1 ≠ ofString "heap_ptr" := by decide
  have hgtr_ne : ∀ g ∈ globalTableRoots, ofString g ≠ ofString "heap_ptr" := by decide
  exact ⟨fun p hp => hgn p.1 (hgb_ne p hp), fun g hg => hgn g (hgtr_ne g hg),
    hgn "journal" (by decide), hgn "journal_cap" (by decide), hgn "journal_n" (by decide)⟩

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

theorem blockOutObjects_eq_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) (hF : FixedTyped s) (hbo_eq : globN post "bo" = globN s "bo")
    (hbo_lst_ok : globN s "bo" ≠ 0 → ∀ k ∈ ([40, 72] : List Nat), memW s (globN s "bo" + k) ≠ 0 →
      LstOK s (memW s (globN s "bo" + k)))
    (hu_bo : globN s "bo" ≠ 0 → IvlUnhit s post (globN s "bo", 88))
    (hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 → IvlUnhit s post i) :
    blockOutObjects post = blockOutObjects s ∧
    (globN post "bo" ≠ 0 → ∀ k ∈ ([40, 72] : List Nat), memW post (globN post "bo" + k) ≠ 0 →
      LstOK post (memW post (globN post "bo" + k))) := by
  by_cases hbo : globN s "bo" = 0
  · refine ⟨?_, fun hp => absurd (hbo_eq.trans hbo) hp⟩
    simp [blockOutObjects, hbo_eq, hbo]
  · have hk_eq : ∀ k ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
        memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := fun k hk => by
      have hkin : k % 8 = 0 ∧ k + 8 ≤ 88 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      simpa [hbo_eq] using rec_word_eq_of_unhit hA hF "bo" 88 (by simp [typedRecords])
        hbo_eq hbo (hu_bo hbo) hkin.1 hkin.2
    have hlst_hdr : ∀ k ∈ ([40, 72] : List Nat), memW s (globN s "bo" + k) ≠ 0 →
        ∀ off ∈ ([0, 8, 16] : List Nat),
          memW post (memW s (globN s "bo" + k) + off) = memW s (memW s (globN s "bo" + k) + off) := by
      intro k hk hknz off hoff
      have hmem_bo : (memW s (globN s "bo" + k), 24) ∈ blockOutObjects s := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> simp [blockOutObjects, hbo, hknz]
      have hmem_fix : (memW s (globN s "bo" + k), 24) ∈ fixedObjects s := by
        unfold fixedObjects
        exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hmem_bo)))
      rcases hF.1 _ hmem_fix with h0 | ⟨hal, hwords⟩
      · simp at h0
      · have hhi := (ivl_allocated_bound hA hal).2
        have hp8 : (memW s (globN s "bo" + k)) % 8 = 0 := hwords.1
        have hu := hu_bo_lst _ hmem_bo rfl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
        rcases hoff with rfl | rfl | rfl <;>
          exact memW_eq_of_ivlUnhit hu (by omega) hhi ⟨by omega, by omega⟩
    constructor
    · unfold blockOutObjects
      simp only [hbo_eq, hbo, false_or, hk_eq 24 (by simp), hk_eq 32 (by simp),
        hk_eq 40 (by simp), hk_eq 56 (by simp), hk_eq 72 (by simp), hk_eq 80 (by simp)]
      congr 1; congr 1
      · by_cases h40 : memW s (globN s "bo" + 40) = 0
        · simp [h40]
        · have h0 := hlst_hdr 40 (by simp) h40 0 (by simp); simp only [Nat.add_zero] at h0
          have h16 := hlst_hdr 40 (by simp) h40 16 (by simp)
          simp [h40, h0, h16]
      · by_cases h72 : memW s (globN s "bo" + 72) = 0
        · simp [h72]
        · have h0 := hlst_hdr 72 (by simp) h72 0 (by simp); simp only [Nat.add_zero] at h0
          have h16 := hlst_hdr 72 (by simp) h72 16 (by simp)
          simp [h72, h0, h16]
    · intro _ k hk hknz
      rw [hbo_eq] at hknz ⊢
      have hkeq : memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl
        · exact hk_eq 40 (by simp)
        · exact hk_eq 72 (by simp)
      rw [hkeq] at hknz ⊢
      unfold LstOK
      rw [hlst_hdr k hk hknz 8 (by simp), hlst_hdr k hk hknz 16 (by simp)]
      exact hbo_lst_ok hbo k hk hknz

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
    exact htabValues_eq_of_unhit (hT.2.1 _ hmem_S).1 (hu hbal)

theorem balObjects_eq_of_unhit_except {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {S : List Nat} (hT : TablesTyped s S) (hF : FixedTyped s)
    (hbal_eq : globN post "bal_accounts" = globN s "bal_accounts")
    {t0 : Nat}
    (hu_other : ∀ u ∈ S, u ≠ t0 → ∀ i ∈ htabFootprint s u, IvlUnhit s post i)
    (ht0_not_bal : globN s "bal_accounts" ≠ t0 ∧ ∀ ad ∈ balRecords s, memW s ad ≠ t0)
    (hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → IvlUnhit s post i)
    (hu_zero : memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧ memW post 16 = memW s 16) :
    balObjects post = balObjects s ∧
    (∀ ad ∈ balRecords post, memW post ad = memW s ad ∧ memW post (ad + 8) = memW s (ad + 8) ∧
      htabValues post (memW post ad) = htabValues s (memW s ad) ∧
      (∀ k ∈ ([16, 24, 32] : List Nat), LstOK post (memW post (ad + k))) ∧
      (∀ l ∈ htabValues post (memW post ad), LstOK post l)) := by
  have hrecs : balRecords post = balRecords s :=
    balRecords_eq_of_unhit hT hbal_eq (fun hnz => by
      rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
      · exact absurd h0 hnz
      · exact hu_other _ hm ht0_not_bal.1)
  have hmem_fix_of_bal : ∀ i ∈ balObjects s, i ∈ fixedObjects s := fun i hi => by
    unfold fixedObjects; exact List.mem_append.2 (Or.inr hi)
  have had_props : ∀ ad ∈ balRecords s,
      (∀ off ∈ ([0, 8, 16, 24, 32] : List Nat), memW post (ad + off) = memW s (ad + off)) ∧
      htabValues post (memW s ad) = htabValues s (memW s ad) ∧
      (∀ k esz, k ∈ ([16, 24, 32] : List Nat) →
        lstObjects post (memW s (ad + k)) esz = lstObjects s (memW s (ad + k)) esz ∧
        (LstOK s (memW s (ad + k)) → LstOK post (memW s (ad + k)))) ∧
      (∀ l ∈ htabValues s (memW s ad),
        lstObjects post l 40 = lstObjects s l 40 ∧ (LstOK s l → LstOK post l)) := by
    intro ad had
    have had_bal : (ad, 40) ∈ balObjects s := by
      unfold balObjects; exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
    rcases hF.1 _ (hmem_fix_of_bal _ had_bal) with h0 | ⟨hal_ad, hw_ad⟩
    · simp at h0
    have hhi_ad := (ivl_allocated_bound hA hal_ad).2
    have had8 : ad % 8 = 0 := hw_ad.1
    have hoff_eq : ∀ off ∈ ([0, 8, 16, 24, 32] : List Nat), memW post (ad + off) = memW s (ad + off) := by
      intro off hoff
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl | rfl | rfl <;>
        exact memW_eq_of_ivlUnhit (hu_bal _ had_bal (by simp)) (by omega) hhi_ad ⟨by omega, by omega⟩
    have had_T := hT.2.2.2.2.2.2.2.2.2.1 ad had
    have hvals_ad : htabValues post (memW s ad) = htabValues s (memW s ad) :=
      htabValues_eq_of_unhit (hT.2.1 _ had_T.1).1 (hu_other _ had_T.1 (ht0_not_bal.2 ad had))
    have hlst_eq : ∀ l esz, (if l = 0 then (0, 0) else (l, 24)) ∈ balObjects s →
        lstObjects post l esz = lstObjects s l esz ∧ (LstOK s l → LstOK post l) := by
      intro l esz hl_bal
      by_cases hl0 : l = 0
      · subst hl0
        refine ⟨by simp [lstObjects], fun hok => ?_⟩
        unfold LstOK at hok ⊢
        have hm0 : memW post 0 = memW s 0 :=
          hu_zero.1
        have hm8 : memW post 8 = memW s 8 := hu_zero.2.1
        have hm16 : memW post 16 = memW s 16 := hu_zero.2.2
        rw [Nat.zero_add] at hok ⊢
        rw [hm8, hm16]; exact hok
      · simp only [hl0, ↓reduceIte] at hl_bal
        rcases hF.1 _ (hmem_fix_of_bal _ hl_bal) with h0 | ⟨hal_l, hw_l⟩
        · simp at h0
        have hhi_l := (ivl_allocated_bound hA hal_l).2
        have hl8 : l % 8 = 0 := hw_l.1
        have hul := hu_bal _ hl_bal (by simp)
        have e0 : memW post l = memW s l :=
          by simpa using memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩
        have e8 : memW post (l + 8) = memW s (l + 8) :=
          memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩
        have e16 : memW post (l + 16) = memW s (l + 16) :=
          memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩
        refine ⟨by simp [lstObjects, hl0, e0, e16], fun hok => ?_⟩
        unfold LstOK at hok ⊢
        rw [e8, e16]; exact hok
    exact ⟨hoff_eq, hvals_ad,
      fun k esz hk => hlst_eq (memW s (ad + k)) esz (by
        unfold balObjects
        refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl
        · by_cases hz : memW s (ad + 16) = 0 <;> simp [lstObjects, hz]
        · by_cases hz : memW s (ad + 24) = 0 <;> simp [lstObjects, hz]
        · by_cases hz : memW s (ad + 32) = 0 <;> simp [lstObjects, hz]),
      fun l hl => hlst_eq l 40 (by
        unfold balObjects
        refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
        apply List.mem_cons_of_mem; apply List.mem_append.2; right
        exact List.mem_flatMap.2 ⟨l, hl, by by_cases hz : l = 0 <;> simp [lstObjects, hz]⟩)⟩
  constructor
  · unfold balObjects
    rw [hrecs]
    apply List.flatMap_congr
    intro ad had
    obtain ⟨hoff_eq, hvals_ad, hklst, hllst⟩ := had_props ad had
    have h0 := hoff_eq 0 (by simp); simp only [Nat.add_zero] at h0
    have h16 := hoff_eq 16 (by simp)
    have h24 := hoff_eq 24 (by simp)
    have h32 := hoff_eq 32 (by simp)
    have htail : (htabValues post (memW post ad)).flatMap (fun l => lstObjects post l 40) =
        (htabValues s (memW s ad)).flatMap (fun l => lstObjects s l 40) := by
      rw [h0, hvals_ad]
      apply List.flatMap_congr
      intro l hl
      exact (hllst l hl).1
    rw [htail, h16, h24, h32,
      (hklst 16 40 (by simp)).1, (hklst 24 16 (by simp)).1, (hklst 32 24 (by simp)).1]
  · intro ad had
    rw [hrecs] at had
    obtain ⟨hoff_eq, hvals_ad, hklst, hllst⟩ := had_props ad had
    have had_T := hT.2.2.2.2.2.2.2.2.2.1 ad had
    have h0 := hoff_eq 0 (by simp); simp only [Nat.add_zero] at h0
    have h8 := hoff_eq 8 (by simp)
    refine ⟨h0, h8, by rw [h0, hvals_ad], ?_, ?_⟩
    · intro k hk
      have hk_in : k ∈ ([0, 8, 16, 24, 32] : List Nat) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
        rcases hk with rfl | rfl | rfl <;> simp
      rw [hoff_eq k hk_in]
      exact (hklst k 40 hk).2 (had_T.2.2.1 k hk)
    · intro l hl
      rw [h0, hvals_ad] at hl
      exact (hllst l hl).2 (had_T.2.2.2 l hl)

theorem worldRoleSlots_eq_of_unhit_except {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {S : List Nat} (hT : TablesTyped s S) (hF : FixedTyped s)
    (hgs : WorldGlobalsSame s post)
    {t0 : Nat}
    (hu_other : ∀ u ∈ S, u ≠ t0 → ∀ i ∈ htabFootprint s u, IvlUnhit s post i)
    (ht0_not_nest : (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
                    (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) ∧
                    globN s "bal_accounts" ≠ t0 ∧ ∀ ad ∈ balRecords s, memW s ad ≠ t0)
    (hu_ws : globN s "ws" ≠ 0 → IvlUnhit s post (globN s "ws", 40))
    (hu_bs : globN s "bs" ≠ 0 → IvlUnhit s post (globN s "bs", 80))
    (hu_ts : globN s "ts" ≠ 0 → IvlUnhit s post (globN s "ts", 72))
    (hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → IvlUnhit s post i)
    (hu_zero : memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧ memW post 16 = memW s 16) :
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
        rw [htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_other _ hmS (ht0_not_nest.1 h))]
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
        rw [htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_other _ hmS (ht0_not_nest.2.1 h))]
  have hrecs_bal := balRecords_eq_of_unhit hT hba_g (fun hnz => by
    rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
    · exact absurd h0 hnz
    · exact hu_other _ hm ht0_not_nest.2.2.1)
  have hbal_part := (balObjects_eq_of_unhit_except hA hT hF hba_g hu_other
    ⟨ht0_not_nest.2.2.1, ht0_not_nest.2.2.2⟩ hu_bal hu_zero).2
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
    {S : List Nat} (hJ : JournalTyped s S) (hF : FixedTyped s)
    (hgs : WorldGlobalsSame s post)
    (hu_ts : globN s "ts" ≠ 0 → IvlUnhit s post (globN s "ts", 72))
    (hu_jr : globN s "journal_cap" ≠ 0 → IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap")) :
    journalRoleSlots post = journalRoleSlots s ∧ JournalTyped post S := by
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
      exact ⟨memW_eq_of_ivlUnhit huj (by omega) hhi ⟨by omega, by omega⟩,
             memW_eq_of_ivlUnhit huj (by omega) hhi ⟨by omega, by omega⟩,
             memW_eq_of_ivlUnhit huj (by omega) hhi ⟨by omega, by omega⟩⟩
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
      exact hJ.2.2.2 i hi

theorem nodeHeap_congr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post)
    (hag : AllocatorGrows s post)
    {Nd : List Nat} (hN : NodeHeap s Nd)
    (hu_rec : ∀ n ∈ Nd, IvlUnhit s post (nodeIvl s n))
    (hu_path : ∀ n ∈ Nd, BytesSame s post (nodePath s n)) :
    NodeHeap post Nd ∧ nodeExtents post Nd = nodeExtents s Nd := by
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hn_props : ∀ n ∈ Nd,
      memW post n = memW s n ∧
      nodeIvl post n = nodeIvl s n ∧
      (∀ k, k < nodeSize (memW s n) / 8 → memW post (n + 8 * k) = memW s (n + 8 * k)) ∧
      nodePath post n = nodePath s n ∧
      ((memW s n = 1 ∨ memW s n = 2) → KeyIn post Nd (memW post (n + 32)) (memW post (n + 40))) := by
    intro n hn
    obtain ⟨hk3, hal_n, hin_n, hw_n, _, _, hkey_n, _⟩ := hN.1 n hn
    have hhi_n : n + nodeSize (memW s n) ≤ 2 ^ 64 := by
      have := hin_n.2; dsimp [nodeIvl] at this; omega
    have hn8 : n % 8 = 0 := hw_n.1
    have hu_n : IvlUnhit s post (n, nodeSize (memW s n)) := hu_rec n hn
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
        unfold nodePath; rw [hw0, hw32, hw40]
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
          have hp_eq : nodePath s n = (memW s (n + 32), memW s (n + 40)) := by
            simp [nodePath, h12, hlen0]
          have hbs_p : BytesSame s post (memW s (n + 32), memW s (n + 40)) := by
            rw [← hp_eq]; exact hu_path n hn
          refine ⟨fun k hk => ?_, hag.allocated hal_p, hin_p, ?_⟩
          · rw [hbs_p k hk]
            exact hnib k hk
          · intro m hm
            have hhm_hi : m + nodeSize (memW s m) ≤ 2 ^ 64 := by
              have := (hN.1 m hm).2.2.1.2; dsimp [nodeIvl] at this; omega
            have hm8 : m % 8 = 0 := (hN.1 m hm).2.2.2.1.1
            have hu_m : IvlUnhit s post (m, nodeSize (memW s m)) := hu_rec m hm
            have hsz_m : 32 ≤ nodeSize (memW s m) := by unfold nodeSize; split_ifs <;> omega
            have hwm : memW post m = memW s m :=
              memW_eq_of_ivlUnhit hu_m hm8 hhm_hi ⟨by omega, by omega⟩
            simp [nodeIvl, hwm]
            exact hdisj_p m hm⟩
  constructor
  · refine ⟨fun n hn => ?_, fun n hn m hm hne => ?_⟩
    · obtain ⟨hk3, hal_n, hin_n, hw_n, hext, hbr, _, hb16, hb56, hb168⟩ := hN.1 n hn
      obtain ⟨hw0, hivl_eq, hw_k, _, hkey_post⟩ := hn_props n hn
      have hsz_ge32 : 32 ≤ nodeSize (memW s n) := by unfold nodeSize; split_ifs <;> omega
      have hw16 : memW post (n + 16) = memW s (n + 16) := hw_k 2 (by omega)
      rw [hw0, hivl_eq, hw16]
      refine ⟨hk3, hag.allocated hal_n, hin_n, wordsOK_transfer hgS hgP hw_n, ?_, ?_, hkey_post,
        hb16, ?_, ?_⟩
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
        rw [show n + 56 = n + 8 * 7 by omega, hw56, show n + 8 * 7 = n + 56 by omega]
        exact hb56 h1
      · intro h3
        have hsz : nodeSize (memW s n) = 176 := by unfold nodeSize; simp [h3]
        have hw168 := hw_k 21 (by omega)
        rw [show n + 168 = n + 8 * 21 by omega, hw168, show n + 8 * 21 = n + 168 by omega]
        exact hb168 h3
    · rw [(hn_props n hn).2.1, (hn_props m hm).2.1]
      exact hN.2 n hn m hm hne
  · unfold nodeExtents
    apply List.flatMap_congr
    intro n hn
    rw [(hn_props n hn).2.1, (hn_props n hn).2.2.2.1]

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

theorem disj_fresh_of_zero_or_allocated {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) (hAp : ArenaOK post) (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    {j : Ivl} (hj : j.2 = 0 ∨ Allocated s j) :
    Disj j (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
  have hsep : heapLimit ≤ scratchStart := by decide
  obtain ⟨_, hs_hp, hs_fm, hs_sc, _⟩ := hAs
  obtain ⟨_, hp_hp, _, _, _⟩ := hAp
  rcases hj with hz | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
  · exact Or.inl hz
  · exact Or.inr (Or.inr (Or.inl (by dsimp; omega)))
  · exact Or.inr (Or.inr (Or.inr (by dsimp; omega)))

theorem disj_of_inside_left {i i' j : Ivl} (hin : Inside i i'.1 (i'.1 + i'.2))
    (hd : Disj i' j) : Disj i j := by
  rcases hin with ⟨h1, h2⟩
  rcases hd with hd | hd | hd | hd
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl hd)
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

theorem disj_of_inside_right {i j j' : Ivl} (hin : Inside j j'.1 (j'.1 + j'.2))
    (hd : Disj i j') : Disj i j :=
  (disj_of_inside_left hin hd.flip).flip

theorem mem_worldRoleSlots_recRole {F : Type} (s : PanSemStateFiniteExact 64 F)
    (g : String) (k : Nat) (r : String)
    (_hgnz : globN s g ≠ 0) (htnz : memW s (globN s g + k) ≠ 0)
    (hmem : (memW s (globN s g + k), r) ∈
      recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] ++
      recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"), (40, "bs+40"),
        (48, "bs+48"), (72, "bs+72")] ++
      recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"), (40, "ts+40"),
        (48, "ts+48"), (56, "ts+56"), (64, "ts+64")]) :
    (memW s (globN s g + k), r) ∈ worldRoleSlots s := by
  unfold worldRoleSlots
  refine List.mem_filter.2 ⟨?_, by simp [htnz]⟩
  apply List.mem_append.2; left; apply List.mem_append.2; left
  apply List.mem_append.2; left; apply List.mem_append.2; left
  exact hmem

theorem slot_ne_of_diff_nonshared_role {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hroles : RolesOK s S (worldRoleSlots s) (journalRoleSlots s))
    {t1 t2 : Nat} {r1 r2 : String}
    (h1 : (t1, r1) ∈ worldRoleSlots s) (h2 : (t2, r2) ∈ worldRoleSlots s)
    (hne_r : r1 ≠ r2) :
    t1 ≠ t2 := by
  intro heq
  subst heq
  obtain ⟨i1, hi1, heq1⟩ := List.mem_iff_getElem.1 h1
  obtain ⟨i2, hi2, heq2⟩ := List.mem_iff_getElem.1 h2
  rcases Nat.lt_trichotomy i1 i2 with hlt | rfl | hgt
  · have hp := List.pairwise_iff_getElem.1 hroles.2.1 i1 i2 hi1 hi2 hlt
    rw [heq1, heq2] at hp
    exact hne_r (hp rfl).1
  · rw [heq1] at heq2
    exact hne_r (Prod.mk.inj heq2).2
  · have hp := List.pairwise_iff_getElem.1 hroles.2.1 i2 i1 hi2 hi1 hgt
    rw [heq1, heq2] at hp
    exact hne_r (hp rfl).1.symm

/-- **W2 for `"ts+24"`**: `HtabExit` on `t0 = memW s (globN s "ts" + 24)` (`t0 ≠ 0`) preserves `WorldOK`. -/
theorem worldOK_of_htabExit_ts24 {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hW : WorldOK s) (hbe : post.be = s.be)
    (hts_nz : globN s "ts" ≠ 0)
    (ht0_nz : memW s (globN s "ts" + 24) ≠ 0)
    (hexit : let t := memW s (globN s "ts" + 24)
      let fresh : Ivl := (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")
      ArenaReady post ∧ HtabWF post t ∧
      hdr post t 0 = hdr s t 0 ∧ hdr post t 1 = hdr s t 1 ∧
      globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
      (∀ i ∈ htabFootprint post t, Allocated post i ∧
        ((∃ j ∈ htabFootprint s t, Inside i j.1 (j.1 + j.2)) ∨ Inside i fresh.1 (fresh.1 + fresh.2))) ∧
      FrameOutside s post (htabFootprint s t) fresh ∧
      (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
        s.globals.lookup k = post.globals.lookup k)) :
    WorldOK post := by
  set t0 := memW s (globN s "ts" + 24)
  obtain ⟨hAp, hwf_t0, hhdr0_t0, _, hhp, hfp_t0, hfr, hg_kept⟩ := hexit
  obtain ⟨hAs, S, hT, hJ, hF, Nd, hTr⟩ := hW
  have hgs : WorldGlobalsSame s post := worldGlobalsSame_of_nonHeap hg_kept
  have hag : AllocatorGrows s post := by
    refine ⟨hhp, ?_⟩
    rw [globN_eq_of_lookup (hg_kept (ofString "scratch_ptr") (by decide))]
  have ht0_S : t0 ∈ S := by
    rcases hT.2.2.2.2.2.1 24 (by simp [tsTableSlots]) hts_nz with h0 | hm
    · exact absurd h0 ht0_nz
    · exact hm
  have ht0_wrs : (t0, "ts+24") ∈ worldRoleSlots s := by
    apply mem_worldRoleSlots_recRole s "ts" 24 "ts+24" hts_nz ht0_nz
    apply List.mem_append.2; right
    unfold recRoles; simp [hts_nz]
  have hroles := hT.2.2.2.2.2.2.2.2.2.2.2
  have ht0_not_nest :
      (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
      (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) ∧
      globN s "bal_accounts" ≠ t0 ∧
      (∀ ad ∈ balRecords s, memW s ad ≠ t0) ∧
      (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t0) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro hbs h32
      have h32_nz : memW s (globN s "bs" + 32) ≠ 0 := by rw [h32]; exact ht0_nz
      have hm : (memW s (globN s "bs" + 32), "bs+32") ∈ worldRoleSlots s := by
        apply mem_worldRoleSlots_recRole s "bs" 32 "bs+32" hbs h32_nz
        apply List.mem_append.2; left; apply List.mem_append.2; right
        unfold recRoles; simp [hbs]
      exact slot_ne_of_diff_nonshared_role hroles hm ht0_wrs (by decide) h32
    · intro hts h32
      have h32_nz : memW s (globN s "ts" + 32) ≠ 0 := by rw [h32]; exact ht0_nz
      have hm : (memW s (globN s "ts" + 32), "ts+32") ∈ worldRoleSlots s := by
        apply mem_worldRoleSlots_recRole s "ts" 32 "ts+32" hts h32_nz
        apply List.mem_append.2; right
        unfold recRoles; simp [hts]
      exact slot_ne_of_diff_nonshared_role hroles hm ht0_wrs (by decide) h32
    · intro hba
      have hba_nz : globN s "bal_accounts" ≠ 0 := by rw [hba]; exact ht0_nz
      have hm : (globN s "bal_accounts", "bal_accounts") ∈ worldRoleSlots s := by
        unfold worldRoleSlots
        refine List.mem_filter.2 ⟨?_, by simp [hba_nz]⟩
        apply List.mem_append.2; left; apply List.mem_append.2; left
        apply List.mem_append.2; left; apply List.mem_append.2; right; simp
      exact slot_ne_of_diff_nonshared_role hroles hm ht0_wrs (by decide) hba
    · intro ad had had0
      have had0_nz : memW s ad ≠ 0 := by rw [had0]; exact ht0_nz
      have hm : (memW s ad, "bal.stor") ∈ worldRoleSlots s := by
        unfold worldRoleSlots
        refine List.mem_filter.2 ⟨?_, by simp [had0_nz]⟩
        apply List.mem_append.2; right
        exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
      exact slot_ne_of_diff_nonshared_role hroles hm ht0_wrs (by decide) had0
    · intro hws h32
      have h32_nz : memW s (globN s "ws" + 32) ≠ 0 := by rw [h32]; exact ht0_nz
      have hm : (memW s (globN s "ws" + 32), "ws+32") ∈ worldRoleSlots s := by
        apply mem_worldRoleSlots_recRole s "ws" 32 "ws+32" hws h32_nz
        apply List.mem_append.2; left; apply List.mem_append.2; left
        unfold recRoles; simp [hws]
      exact slot_ne_of_diff_nonshared_role hroles hm ht0_wrs (by decide) h32
  obtain ⟨hs_lo, _, _, _, _, hs_hp8, _, _⟩ := hAs.2
  obtain ⟨_, _, _, _, _, hp_hp8, _, _⟩ := hAp.2
  have hf_al : (globN s "heap_ptr") % 8 = 0 ∧ (globN post "heap_ptr" - globN s "heap_ptr") % 8 = 0 :=
    ⟨hs_hp8, by omega⟩
  have ht0_al : ∀ j ∈ htabFootprint s t0, j.1 % 8 = 0 ∧ j.2 % 8 = 0 := fun j hj => by
    have hw := ((hT.2.1 t0 ht0_S).1.1 j hj).2
    exact ⟨hw.1, hw.2.1⟩
  have hunhit_disj : ∀ i : Ivl, i.1 % 8 = 0 ∧ i.2 % 8 = 0 →
      (∀ j ∈ htabFootprint s t0, Disj i j) →
      (i.2 = 0 ∨ Allocated s i) → IvlUnhit s post i := fun i hial hdi hal =>
    ivlUnhit_of_frameOutside hial hfr ht0_al hf_al hdi (disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp hal)
  have hu_other : ∀ u ∈ S, u ≠ t0 → ∀ i ∈ htabFootprint s u, IvlUnhit s post i := fun u hu hne i hi => by
    have hw := ((hT.2.1 u hu).1.1 i hi).2
    exact hunhit_disj i ⟨hw.1, hw.2.1⟩ (fun j hj => hT.2.2.1 u hu t0 ht0_S hne i hi j hj)
      (Or.inr ((hT.2.1 u hu).2 i hi).1)
  have hu_fix_aligned : ∀ i ∈ fixedObjects s, i.1 % 8 = 0 ∧ i.2 % 8 = 0 → IvlUnhit s post i := fun i hi hial =>
    hunhit_disj i hial (fun j hj => (((hT.2.1 t0 ht0_S).2 j hj).2 i hi).flip)
      (by rcases hF.1 i hi with h0 | ⟨hal, _⟩; exact Or.inl h0; exact Or.inr hal)
  have hu_fix_nz : ∀ i ∈ fixedObjects s, i.2 ≠ 0 → IvlUnhit s post i := fun i hi hnz => by
    rcases hF.1 i hi with h0 | ⟨_, hw⟩
    · exact absurd h0 hnz
    · exact hu_fix_aligned i hi ⟨hw.1, hw.2.1⟩
  have hu_nd_rec : ∀ n ∈ Nd, IvlUnhit s post (nodeIvl s n) := fun n hn => by
    have hw := (hTr.1.1 n hn).2.2.2.1
    have hmem : nodeIvl s n ∈ nodeExtents s Nd := by
      unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp⟩
    exact hunhit_disj _ ⟨hw.1, hw.2.1⟩ (fun j hj => (hTr.2.1 _ hmem).1 t0 ht0_S j hj)
      (Or.inr (hTr.1.1 n hn).2.1)
  have hu_nd_path : ∀ n ∈ Nd, BytesSame s post (nodePath s n) := fun n hn => by
    have hmem : nodePath s n ∈ nodeExtents s Nd := by
      unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp⟩
    have hhl : heapLimit ≤ 2 ^ 64 := by decide
    have hpath_props : (nodePath s n).1 + (nodePath s n).2 ≤ 2 ^ 64 ∧
        ((nodePath s n).2 = 0 ∨ Allocated s (nodePath s n)) := by
      unfold nodePath; split_ifs with hc
      · rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hc.1 with h0 | ⟨_, hal, hin, _⟩
        · exact absurd h0 hc.2
        · exact ⟨le_trans hin.2 hhl, Or.inr hal⟩
      · exact ⟨by dsimp; omega, Or.inl rfl⟩
    exact bytesSame_of_frameOutside hbe hpath_props.1 hfr ht0_al hf_al
      (fun j hj => (hTr.2.1 _ hmem).1 t0 ht0_S j hj)
      (disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp hpath_props.2)
  have hu_zero : memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 := by
    have hlow : ∀ a : Nat, a + 8 ≤ sourceBase → memW post a = memW s a := fun a ha => by
      have hsb_lt : sourceBase < 2 ^ 64 := by decide
      have ha_lt : a < 2 ^ 64 := lt_of_le_of_lt (by omega) hsb_lt
      have hm := hfr (BitVec.ofNat 64 a)
        (fun j hj hcj => by
          obtain ⟨h1, _⟩ := hcj
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
          have hlo := ((hT.2.1 t0 ht0_S).1.1 j hj).1.1
          omega)
        (fun hcf => by
          obtain ⟨h1, _⟩ := hcf
          dsimp at h1
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
          omega)
      unfold memW; rw [hm]
    exact ⟨hlow 0 (by decide), hlow 8 (by decide), hlow 16 (by decide)⟩
  have hu_ws : globN s "ws" ≠ 0 → IvlUnhit s post (globN s "ws", 40) := fun hnz => by
    have hm := typedRecord_mem_fixedObjects s (r := ("ws", 40)) (by simp [typedRecords])
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix_nz _ hm (by simp)
  have hu_bs : globN s "bs" ≠ 0 → IvlUnhit s post (globN s "bs", 80) := fun hnz => by
    have hm := typedRecord_mem_fixedObjects s (r := ("bs", 80)) (by simp [typedRecords])
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix_nz _ hm (by simp)
  have hu_ts : globN s "ts" ≠ 0 → IvlUnhit s post (globN s "ts", 72) := fun hnz => by
    have hm := typedRecord_mem_fixedObjects s (r := ("ts", 72)) (by simp [typedRecords])
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix_nz _ hm (by simp)
  have hu_bo : globN s "bo" ≠ 0 → IvlUnhit s post (globN s "bo", 88) := fun hnz => by
    have hm := typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by simp [typedRecords])
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix_nz _ hm (by simp)
  have hu_jr : globN s "journal_cap" ≠ 0 → IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap") := fun hnz => by
    apply hu_fix_nz _ _ (by dsimp; omega)
    unfold fixedObjects
    apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
    simp [hnz]
  have hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 → IvlUnhit s post i := fun i hi hi24 =>
    hu_fix_nz i (by unfold fixedObjects; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hi))))
      (by omega)
  have hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → IvlUnhit s post i := fun i hi hi0 =>
    hu_fix_nz i (by unfold fixedObjects; exact List.mem_append.2 (Or.inr hi)) hi0
  have hbo_eq := blockOutObjects_eq_of_unhit hAs.2 hF (hgs.1 ("bo", 88) (by simp [globalBuffers]))
    hT.2.2.2.2.2.2.2.2.2.2.1 hu_bo hu_bo_lst
  have hbal_eq := balObjects_eq_of_unhit_except hAs.2 hT hF
    (hgs.2.1 "bal_accounts" (by simp [globalTableRoots])) hu_other
    ⟨ht0_not_nest.2.2.1, ht0_not_nest.2.2.2.1⟩ hu_bal hu_zero
  have hfix_eq := fixedObjects_eq_of_parts hgs hbo_eq.1 hbal_eq.1
  have hF_post := fixedTyped_transfer hAs.1 hAp.1 hag hF hfix_eq
  obtain ⟨hjr_eq, hJ_post⟩ := journalRoleSlots_eq_of_unhit hAs.1 hAp.1 hAs.2 hag hJ hF hgs hu_ts hu_jr
  have hwrs_eq := worldRoleSlots_eq_of_unhit_except hAs.2 hT hF hgs hu_other
    ⟨ht0_not_nest.1, ht0_not_nest.2.1, ht0_not_nest.2.2.1, ht0_not_nest.2.2.2.1⟩
    hu_ws hu_bs hu_ts hu_bal hu_zero
  obtain ⟨hNH_post, hne_eq⟩ := nodeHeap_congr_unhit hAs.1 hAp.1 hag hTr.1 hu_nd_rec hu_nd_path
  have h264 : heapEnd ≤ 2 ^ 64 := by decide
  have hother_fp : ∀ u ∈ S, u ≠ t0 →
      (∀ k, k < 11 → hdr post u k = hdr s u k) ∧ htabFootprint post u = htabFootprint s u := by
    intro u hu hne
    have hfp := (hT.2.1 u hu).1.1
    have ht_fp : (u, 88) ∈ htabFootprint s u := by simp [htabFootprint]
    exact htabFootprint_eq_of_hdr_unhit ((hfp _ ht_fp).2.1)
      (by have := (hfp _ ht_fp).1.2; omega) (hu_other u hu hne _ ht_fp)
  have ht0_disj_other : ∀ i ∈ htabFootprint post t0,
      (∀ u ∈ S, u ≠ t0 → ∀ j ∈ htabFootprint s u, Disj i j) ∧
      (∀ j ∈ fixedObjects s, Disj i j) ∧
      (∀ o ∈ nodeExtents s Nd, Disj i o) := by
    intro i hi
    rcases (hfp_t0 i hi).2 with ⟨k, hk, hin⟩ | hfresh
    · refine ⟨fun u hu hne j hj => disj_of_inside_left hin (hT.2.2.1 t0 ht0_S u hu hne.symm k hk j hj),
              fun j hj => disj_of_inside_left hin (((hT.2.1 t0 ht0_S).2 k hk).2 j hj),
              fun o ho => disj_of_inside_left hin ((hTr.2.1 o ho).1 t0 ht0_S k hk).flip⟩
    · have hin' : Inside i (globN s "heap_ptr") (globN s "heap_ptr" + (globN post "heap_ptr" - globN s "heap_ptr")) := by
        unfold Inside at hfresh ⊢; omega
      refine ⟨fun u hu _ j hj => (disj_of_inside_right hin'
                (disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp (Or.inr ((hT.2.1 u hu).2 j hj).1))).flip,
              fun j hj => (disj_of_inside_right hin'
                (disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp
                  (by rcases hF.1 j hj with h0 | ⟨hal, _⟩; exact Or.inl h0; exact Or.inr hal))).flip,
              fun o ho => (disj_of_inside_right hin'
                (disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp (by
                  unfold nodeExtents at ho
                  obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 ho
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
                  rcases hno with rfl | rfl
                  · exact Or.inr (hTr.1.1 n hn).2.1
                  · unfold nodePath; split_ifs with hc
                    · rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hc.1 with h0 | ⟨_, hal, _⟩
                      · exact absurd h0 hc.2
                      · exact Or.inr hal
                    · exact Or.inl rfl))).flip⟩
  have hT_post : TablesTyped post S := by
    have hT0 := hT
    obtain ⟨hnd, htwf, htpw, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, _, _⟩ := hT
    have ews := hgs.1 ("ws", 40) (by simp [globalBuffers])
    have ebs := hgs.1 ("bs", 80) (by simp [globalBuffers])
    have ets := hgs.1 ("ts", 72) (by simp [globalBuffers])
    refine ⟨hnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo_eq.2, ?_⟩
    · intro u hu
      by_cases heq : u = t0
      · subst heq
        rw [hfix_eq]
        exact ⟨hwf_t0, fun i hi => ⟨(hfp_t0 i hi).1, (ht0_disj_other i hi).2.1⟩⟩
      · rw [(hother_fp u hu heq).2, hfix_eq]
        exact ⟨htabWF_congr_unhit hAs.1 hAp.1 (htwf u hu).1 (hu_other u hu heq),
          fun i hi => ⟨hag.allocated ((htwf u hu).2 i hi).1, ((htwf u hu).2 i hi).2⟩⟩
    · intro u hu v hv hne i hi j hj
      by_cases hu0 : u = t0
      · subst hu0
        rw [(hother_fp v hv hne.symm).2] at hj
        exact (ht0_disj_other i hi).1 v hv hne.symm j hj
      · by_cases hv0 : v = t0
        · subst hv0
          rw [(hother_fp u hu hu0).2] at hi
          exact ((ht0_disj_other j hj).1 u hu hu0 i hi).flip
        · rw [(hother_fp u hu hu0).2] at hi
          rw [(hother_fp v hv hv0).2] at hj
          exact htpw u hu v hv hne i hi j hj
    · intro k hk hnz
      rw [ews] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) ews hnz (hu_ws hnz) hk8.1 hk8.2]
      exact hwsR k hk hnz
    · intro k hk hnz
      rw [ebs] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) ebs hnz (hu_bs hnz) hk8.1 hk8.2]
      exact hbsR k hk hnz
    · intro k hk hnz
      rw [ets] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) ets hnz (hu_ts hnz) hk8.1 hk8.2]
      exact htsR k hk hnz
    · intro g hg_mem
      rw [hgs.2.1 g hg_mem]
      exact hgR g hg_mem
    · intro hnz hmem
      rw [ebs] at hnz
      have ew := rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) ebs hnz (hu_bs hnz) (k := 32) (by omega) (by omega)
      rw [ew] at hmem ⊢
      exact htabValuesIn_congr_unhit (htwf _ hmem).1 (hu_other _ hmem (ht0_not_nest.1 hnz)) (hbsN hnz hmem)
    · intro hnz hmem
      rw [ets] at hnz
      have ew := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) ets hnz (hu_ts hnz) (k := 32) (by omega) (by omega)
      rw [ew] at hmem ⊢
      exact htabValuesIn_congr_unhit (htwf _ hmem).1 (hu_other _ hmem (ht0_not_nest.2.1 hnz)) (htsN hnz hmem)
    · intro ad had
      have had_s : ad ∈ balRecords s := by
        rwa [balRecords_eq_of_unhit hT0 (hgs.2.1 "bal_accounts" (by simp [globalTableRoots])) (fun hnz => by
          rcases hgR "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
          · exact absurd h0 hnz
          · exact hu_other _ hm ht0_not_nest.2.2.1)] at had
      obtain ⟨e0, e8, _, hkl, hll⟩ := hbal_eq.2 ad had
      exact ⟨e0 ▸ (hbalT ad had_s).1, e8 ▸ (hbalT ad had_s).2.1, hkl, hll⟩
    · unfold RolesOK at hroles ⊢
      rw [hwrs_eq, hjr_eq]
      refine ⟨fun a ha => ?_, hroles.2⟩
      obtain ⟨haS, hkl⟩ := hroles.1 a ha
      by_cases ha0 : a.1 = t0
      · rw [ha0] at hkl ⊢
        exact ⟨ht0_S, hhdr0_t0.trans hkl⟩
      · exact ⟨haS, ((hother_fp a.1 haS ha0).1 0 (by omega)).trans hkl⟩
  have hTr_post : TriesTypedWith post S Nd := by
    have ews := hgs.1 ("ws", 40) (by simp [globalBuffers])
    refine ⟨hNH_post, ?_, ?_⟩
    · rw [hne_eq, hfix_eq]
      intro o ho
      refine ⟨fun u hu i hi => ?_, (hTr.2.1 o ho).2⟩
      by_cases hu0 : u = t0
      · subst hu0; exact ((ht0_disj_other i hi).2.2 o ho).flip
      · rw [(hother_fp u hu hu0).2] at hi
        exact (hTr.2.1 o ho).1 u hu i hi
    · intro hws_nz
      rw [ews] at hws_nz
      have e24 := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) ews hws_nz (hu_ws hws_nz) (k := 24) (by omega) (by omega)
      have e32 := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) ews hws_nz (hu_ws hws_nz) (k := 32) (by omega) (by omega)
      rw [e24, e32]
      obtain ⟨hr24, hr32⟩ := hTr.2.2 hws_nz
      refine ⟨hr24, fun htS i hi => ?_⟩
      have hne32 := ht0_not_nest.2.2.2.2 hws_nz
      have hu32 := hu_other _ htS hne32
      have hwf32 := (hT.2.1 _ htS).1
      have hvals_eq := htabValues_eq_of_unhit hwf32 hu32
      obtain ⟨hhdr32, _⟩ := hother_fp _ htS hne32
      rw [hhdr32 3 (by omega)] at hi
      have hget : (htabValues post (memW s (globN s "ws" + 32)))[i]? =
          (htabValues s (memW s (globN s "ws" + 32)))[i]? := by rw [hvals_eq]
      simp only [htabValues, List.getElem?_map, List.getElem?_range, hhdr32 3 (by omega), hi,
        Option.map_some, Option.some.injEq] at hget
      rw [hget]
      exact hr32 htS i hi
  exact ⟨hAp, S, hT_post, hJ_post, hF_post, Nd, hTr_post⟩

/-! ## 4. Hoare step for `htab_set(load(ts + 24), k, 1)` in `get_storage` -/

theorem evalAt_loadG_ts_nz {F : Type} (s : PanSemStateFiniteExact 64 F) (hG : GuestInv s)
    (v : ValueHOL 64)
    (hev : evalAt s (.load .one (.op .add [.var .global (ofString "ts"), .const 24])) = some v) :
    ∃ a : BitVec 64, v = .val (.word a) ∧ a.toNat = memW s (globN s "ts" + 24) ∧
      globN s "ts" ≠ 0 := by
  obtain ⟨a, rfl, ha⟩ := evalAt_loadG s "ts" 24 v hev
  refine ⟨a, rfl, ha, ?_⟩
  intro hts0
  simp [evalAt, evalHOLExact, evalListHOLExact] at hev
  rcases hg : s.globals.lookup (ofString "ts") with _ | gv
  · simp [hg] at hev
  · rcases gv with ⟨⟨gw⟩⟩ | _ | _
    · have hgw0 : gw = 0 := by
        apply BitVec.eq_of_toNat_eq
        simpa [globN, hg] using hts0
      subst hgw0
      simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact, hG.memaddrs] at hev
      have hdom := (ordinaryDomain_iff 24).1 hev.1
      have : sourceBase = 2701131776 := by decide
      have : (24 : BitVec 64).toNat = 24 := rfl
      omega
    · simp [hg, valueIsWord] at hev
    · simp [hg, valueIsWord] at hev

theorem hoare_htab_set_ts24
    (hspec : FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_set"))
    (hnz : ArgNonNull "t" (ofString "htab_set"))
    (kExp : ExpHOL 64) :
    Hoare WorldOK
      (.call (some (none, none)) (ofString "htab_set")
        [.load .one (.op .add [.var .global (ofString "ts"), .const 24]), kExp, .const 1])
      (fun r t => r = none → WorldOK t) := by
  refine ⟨fun {F} s hcode hW hnt hr => ?_⟩
  rcases hout : evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set")
        [.load .one (.op .add [.var .global (ofString "ts"), .const 24]), kExp, .const 1]) with
    ⟨r_out, t_out⟩
  have hr' : r_out = none := by rw [hout] at hr; exact hr
  subst hr'
  change WorldOK t_out
  rw [evaluateHOLFiniteState_call] at hout
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.load .one (.op .add [.var .global (ofString "ts"), .const 24]), kExp, .const 1] with _ | values
  · rw [hargs] at hout; simp at hout
  · rw [hargs] at hout; dsimp only at hout
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "htab_set") values with _ | ⟨body', callee, ret'⟩
    · rw [hl] at hout; simp at hout
    · rw [hl] at hout; dsimp only at hout
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hout; simp at hout
      · rw [if_neg hz] at hout
        have hparam := callee_param_three_first s (ofString "htab_set")
          (ofString "t") (ofString "key") (ofString "value") .one .one .one _ _
          (by rw [hcode]; exact lookup_htab_set) _ _ _ values body' callee ret' hargs hl
        obtain ⟨v1, he1, hc_t⟩ := hparam
        obtain ⟨tw, rfl, htw_nat, hts_nz⟩ := evalAt_loadG_ts_nz s hW.1.1 v1 he1
        have hloc_t : locN (callEntryStateHOLFinite s callee) "t" = memW s (globN s "ts" + 24) := by
          simp [locN, callEntryStateHOLFinite, hc_t, htw_nat]
        have hmeta := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body'
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        rw [hrun] at hout hmeta
        dsimp only at hmeta
        cases res with
        | none => simp at hout
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hout
            split at hout
            · injection hout with _ hteq
              rw [← hteq]
              have hnz_at := FunSpec.at_lookup hnz s hcode values body' callee ret' hl
                (guestInv_callEntry s callee hW.1.1) (by rw [hrun]; simp)
              rw [hrun] at hnz_at
              have ht0_nz : memW s (globN s "ts" + 24) ≠ 0 := by
                rw [← hloc_t]; exact hnz_at (Or.inl ⟨v, rfl⟩)
              have hArgWF : HtabArgWF (callEntryStateHOLFinite s callee) := by
                obtain ⟨hAs, S, hT, _⟩ := hW
                rcases hT.2.2.2.2.2.1 24 (by simp [tsTableSlots]) hts_nz with h0 | hmS
                · exact absurd h0 ht0_nz
                · refine ⟨localsFree_arenaReady s _ _ hAs, ?_, ?_⟩
                  · rw [hloc_t]
                    exact (htabWF_with_locals s callee (s.clock - 1) _).2 (hT.2.1 _ hmS).1
                  · rw [hloc_t]
                    intro i hi
                    have hi' : i ∈ htabFootprint s (memW s (globN s "ts" + 24)) := hi
                    exact ((hT.2.1 _ hmS).2 i hi').1
              have hex := FunSpec.at_lookup hspec s hcode values body' callee ret' hl hArgWF
                (by rw [hrun]; simp)
              rw [hrun] at hex
              have hex_ret : HtabExit (callEntryStateHOLFinite s callee) post := hex v rfl
              unfold HtabExit at hex_ret
              dsimp only at hex_ret
              rw [hloc_t] at hex_ret
              have hWpost : WorldOK post :=
                worldOK_of_htabExit_ts24 hW hmeta.2.2.1 hts_nz ht0_nz hex_ret
              exact localsFree_worldOK post s.locals post.clock hWpost
            · simp at hout
          | _ => simp [emptyLocalsHOLFinite] at hout

/-! ## 5. `EvmAvoids` entry obligations for `op_sload` and `op_sstore` -/

/-- Every untyped global buffer slice `bufferRegion s (gn.1, n)` (`n ≤ gn.2`, `gn ∈ globalBuffers`,
`gn.1 ∉ typedRecords.map Prod.fst`) avoids `worldTypedIvls s S Nd` and `frameObjects` under `EvmInv`. -/
theorem evmAvoids_of_buffer_parts
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    (hR : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) i, i ∈ R s →
      ∃ gn ∈ globalBuffers, gn.1 ∉ typedRecords.map Prod.fst ∧
        ∃ n, n ≤ gn.2 ∧ i = bufferRegion s (gn.1, n))
    {F : Type} {s : PanSemStateFiniteExact 64 F} (hInv : EvmInv s) :
    EvmAvoids R s := by
  obtain ⟨hAs, S, hInvAt⟩ := (evmInv_iff_at s).1 hInv
  have hInvAt0 := hInvAt
  obtain ⟨hW, _, _, _, _, _, _, _, hFO_disj, ⟨Nd, hTr, _⟩, _⟩ := hInvAt
  have hWT : WorldTypedWith s S Nd := ⟨hW.1, hW.2.1, hW.2.2.1, hTr⟩
  refine ⟨hAs, S, hInvAt0, Nd, hTr, fun i hi j hj => ?_⟩
  obtain ⟨gn, hg, hu, n, hle, rfl⟩ := hR s i hi
  rcases List.mem_append.1 hj with hj_w | hj_f
  · exact bufferRegion_disj_le hWT gn hg hu n hle j hj_w
  · obtain ⟨l, hl, hj_in⟩ := List.mem_flatten.1 hj_f
    obtain ⟨ec, hec, rfl⟩ := List.mem_map.1 hl
    have hfix : bufferRegion s gn ∈ fixedObjects s := by
      unfold fixedObjects
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_map.2 ⟨gn, hg, rfl⟩
    have hd : Disj (bufferRegion s gn) j := ((hFO_disj ec hec j hj_in).2 _ hfix).flip
    by_cases hz : globN s gn.1 = 0
    · exact Or.inl (by simp [bufferRegion, hz])
    · simp only [bufferRegion, hz, ↓reduceIte] at hd ⊢
      rcases hd with hd | hd | hd | hd
      · exact Or.inl (by dsimp at hd ⊢; omega)
      · exact Or.inr (Or.inl hd)
      · exact Or.inr (Or.inr (Or.inl (by dsimp at hd ⊢; omega)))
      · exact Or.inr (Or.inr (Or.inr (by dsimp at hd ⊢; omega)))

theorem callEntryOn_u256_to_be32_evm_key_buf {kvExp : ExpHOL 64} :
    CallEntryOn
      (fun s => EvmInv s ∧ s.locals.lookup (ofString "key") = s.globals.lookup (ofString "evm_key_buf"))
      (EvmAvoids (fun s => [(locN s "out", 32)]))
      (ofString "u256_to_be32")
      [kvExp, .var .local (ofString "key")] := by
  have hlook : originalRuntimeCode.lookup (ofString "u256_to_be32") =
      some ((sourceFunctionEntry Guest.Software.guestFn_u256_to_be32).2) :=
    originalRuntimeCode_lookup_of_guestAst_getElem 87 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_u256_to_be32) rfl
  intro F state values body callee ret hcode ⟨hInv, hkey_eq⟩ hargs hl
  have hargs' := hargs
  rw [evalListHOLFinite_eq_toExact] at hargs'
  simp only [evalListHOLExact] at hargs'
  rcases he1 : evalAt state kvExp with _ | v1
  · simp [evalAt] at he1; simp [he1] at hargs'
  · rcases he2 : evalAt state (.var .local (ofString "key")) with _ | v2
    · simp [evalAt] at he1 he2; simp [he1, he2] at hargs'
    · have hp := callee_param_two state (ofString "u256_to_be32")
        (ofString "a") (ofString "out") (.comb [.one, .one, .one, .one]) .one _ _
        (by rw [hcode]; exact hlook) kvExp (.var .local (ofString "key")) v1 v2
        values body callee ret he1 he2 hargs hl
      have hv2_glob : state.globals.lookup (ofString "evm_key_buf") = some v2 := by
        rw [← hkey_eq]; exact he2
      let ent := callEntryStateHOLFinite state callee
      have hout_eq : locN ent "out" = globN state "evm_key_buf" := by
        simp [locN, globN, ent, callEntryStateHOLFinite, hp.2.2, hv2_glob]
      have hInv_ent : EvmInv ent := localsFree_evmInv state callee (state.clock - 1) hInv
      obtain ⟨hAs, S, hInvAt⟩ := (evmInv_iff_at ent).1 hInv_ent
      have hInvAt0 := hInvAt
      obtain ⟨hW, _, _, _, hFW_all, _, _, _, hFO_disj, ⟨Nd, hTr, _⟩, _⟩ := hInvAt
      have hWT : WorldTypedWith ent S Nd := ⟨hW.1, hW.2.1, hW.2.2.1, hTr⟩
      refine ⟨hAs, S, hInvAt0, Nd, hTr, fun i hi j hj => ?_⟩
      simp only [List.mem_singleton] at hi
      rw [hi, hout_eq]
      by_cases hbuf0 : globN state "evm_key_buf" = 0
      · -- `(0, 32)` is disjoint from every `j ∈ worldTypedIvls ent S Nd ++ frameObjects` because
        -- either `j.2 = 0` or `j` is `Allocated ent j` / `Inside scratchStart`, which has `j.1 ≥ 32`!
        have hj_ge : j.2 = 0 ∨ 32 ≤ j.1 := by
          have hsb : 32 ≤ sourceBase := by decide
          have hss : 32 ≤ scratchStart := by decide
          have hal_ge : ∀ x : Ivl, Allocated ent x → 32 ≤ x.1 := by
            rintro x (⟨hlo, _⟩ | ⟨hlo, _⟩)
            · omega
            · have := hAs.2.2.1; have := hAs.2.2.2.1; omega
          rcases List.mem_append.1 hj with hj_w | hj_f
          · unfold worldTypedIvls at hj_w
            simp only [List.mem_append] at hj_w
            rcases hj_w with ((((h1 | h2) | h3) | h4) | h5) | h6
            · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
              exact Or.inr (hal_ge j ((hW.1.2.1 t ht).2 j hfp).1)
            · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
              rcases hW.2.2.1.1 _ (typedRecord_mem_fixedObjects ent hr) with h0 | ⟨hal, _⟩
              · exact Or.inl h0
              · exact Or.inr (hal_ge _ hal)
            · simp only [List.mem_singleton] at h3; subst h3
              rcases hW.2.1.2.2.1 with h0 | ⟨hal, _⟩
              · exact Or.inl (by dsimp; omega)
              · exact Or.inr (hal_ge _ hal)
            · rcases hW.2.2.1.1 j (by unfold fixedObjects; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr h4)))) with h0 | ⟨hal, _⟩
              · exact Or.inl h0
              · exact Or.inr (hal_ge _ hal)
            · rcases hW.2.2.1.1 j (by unfold fixedObjects; exact List.mem_append.2 (Or.inr h5)) with h0 | ⟨hal, _⟩
              · exact Or.inl h0
              · exact Or.inr (hal_ge _ hal)
            · obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 h6
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
              rcases hno with rfl | rfl
              · exact Or.inr (hal_ge _ (hTr.1.1 n hn).2.1)
              · unfold nodePath; split_ifs with hc
                · rcases (hTr.1.1 n hn).2.2.2.2.2.2 hc.1 with h0 | ⟨_, hal, _⟩
                  · exact absurd h0 hc.2
                  · exact Or.inr (hal_ge _ hal)
                · exact Or.inl rfl
          · obtain ⟨l, hl, hj_in⟩ := List.mem_flatten.1 hj_f
            obtain ⟨ec, hec, rfl⟩ := List.mem_map.1 hl
            have hfw := hFW_all ec hec
            unfold frameObjects at hj_in
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hj_in
            rcases hj_in with rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · exact Or.inr (hal_ge _ (Or.inr (hfw.1 (ec.1, 280) (by simp)).1))
            · exact Or.inr (hal_ge _ (Or.inr (hfw.1 (ec.2, 104) (by simp)).1))
            · exact Or.inr (hal_ge _ (Or.inr (hfw.1 _ (by simp)).1))
            · have hin := hfw.2.1; exact Or.inr (by dsimp at hin ⊢; omega)
            · exact Or.inr (hal_ge _ (Or.inr (hfw.1 _ (by simp)).1))
            · rcases hfw.2.2.2.2.2.2.2.2.2.2.2.2.1 with h | h
              · exact Or.inr (hal_ge _ (Or.inl h))
              · exact Or.inr (hal_ge _ (Or.inr h))
            · rcases hfw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with ⟨hz, _⟩ | ⟨h, _⟩
              · unfold frameRet; simp [hz]
              · exact Or.inr (hal_ge _ (Or.inl h))
        rcases hj_ge with hz0 | hge
        · exact Or.inr (Or.inl hz0)
        · rw [hbuf0]; exact Or.inr (Or.inr (Or.inl (by dsimp; omega)))
      · have hglob_ent : globN ent "evm_key_buf" = globN state "evm_key_buf" := rfl
        have hbuf0' : globN ent "evm_key_buf" ≠ 0 := hbuf0
        have heq_br : (globN state "evm_key_buf", 32) = bufferRegion ent ("evm_key_buf", 32) := by
          simp [bufferRegion, hglob_ent, hbuf0]
        rw [heq_br]
        rcases List.mem_append.1 hj with hj_w | hj_f
        · exact bufferRegion_disj hWT ("evm_key_buf", 32) (by decide) (by decide) j hj_w
        · obtain ⟨l, hl, hj_in⟩ := List.mem_flatten.1 hj_f
          obtain ⟨ec, hec, rfl⟩ := List.mem_map.1 hl
          have hfix : bufferRegion ent ("evm_key_buf", 32) ∈ fixedObjects ent := by
            unfold fixedObjects
            apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
            exact List.mem_map.2 ⟨("evm_key_buf", 32), by decide, rfl⟩
          exact ((hFO_disj ec hec j hj_in).2 _ hfix).flip

theorem callEntryOn_sk_buf {fname : MlS} {arguments : List (ExpHOL 64)} :
    CallEntryOn EvmInv
      (EvmAvoids (fun s => [(globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)]))
      fname arguments := by
  intro F state _ _ callee _ _ hInv _ _
  apply evmAvoids_of_buffer_parts _ (localsFree_evmInv state callee (state.clock - 1) hInv)
  intro F' s i hi
  simp only [List.mem_singleton] at hi
  subst hi
  exact ⟨("sk_buf", 64), by decide, by decide, 52, by decide, rfl⟩

theorem callEntryOn_keccak_mpt_nib {fname : MlS} {arguments : List (ExpHOL 64)} :
    CallEntryOn EvmInv
      (EvmAvoids (fun s => [
        (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)]))
      fname arguments := by
  intro F state _ _ callee _ _ hInv _ _
  apply evmAvoids_of_buffer_parts _ (localsFree_evmInv state callee (state.clock - 1) hInv)
  intro F' s i hi
  change i ∈ [bufferRegion s ("keccak_pad", 136), bufferRegion s ("keccak_st", 200),
    bufferRegion s ("mpt_nib_scratch", 64)] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact ⟨("keccak_pad", 136), by decide, by decide, 136, le_rfl, rfl⟩
  · exact ⟨("keccak_st", 200), by decide, by decide, 200, le_rfl, rfl⟩
  · exact ⟨("mpt_nib_scratch", 64), by decide, by decide, 64, le_rfl, rfl⟩

/-- `dec key := G:"evm_key_buf"; call u256_to_be32(kv, key); body` under `EvmInv`:
binds `key` to `s.globals.lookup (ofString "evm_key_buf")`, runs `u256_to_be32` via `ek_u256_to_be32`
(keeping `EvmInv`), and continues `body` under `EvmInv`! -/
theorem dec_key_u256_to_be32_on {B Bc : Nat}
    (hu2b : TerminatingFunBoundedOn GuestInv (ofString "u256_to_be32") B)
    (ek_u2b : EvmKeeps (EvmAvoids (fun s => [(locN s "out", 32)])) [] (ofString "u256_to_be32"))
    (kvExp : ExpHOL 64) {body : ProgHOL 64}
    (hbody : TerminatingProgBoundedOn EvmInv body Bc) :
    TerminatingProgBoundedOn EvmInv
      (.dec (ofString "key") .one (.var .global (ofString "evm_key_buf"))
        (.seq (.call (some (none, none)) (ofString "u256_to_be32")
            [kvExp, .var .local (ofString "key")])
          body))
      ((B + 1) + Bc) := by
  intro F state hcode hInv
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  revert hnt
  split <;> intro hnt
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · rename_i val hval
    revert hnt
    split <;> intro hnt
    · set s1 := setVarHOLFinite (ofString "key") val state
      have hInv1 : EvmInv s1 ∧
          s1.locals.lookup (ofString "key") = s1.globals.lookup (ofString "evm_key_buf") := by
        refine ⟨localsFree_evmInv state _ state.clock hInv, ?_⟩
        have hlk : s1.locals.lookup (ofString "key") = some val := by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
        rw [hlk]
        exact hval.symm
      have hseq : TerminatingProgBoundedOn
          (fun s => EvmInv s ∧ s.locals.lookup (ofString "key") = s.globals.lookup (ofString "evm_key_buf"))
          (.seq (.call (some (none, none)) (ofString "u256_to_be32")
              [kvExp, .var .local (ofString "key")])
            body)
          ((B + 1) + Bc) := by
        intro F' st hc ⟨hI, hkeq⟩
        have hmeta := evaluateHOLFiniteState_metadata st
          (.call (some (none, none)) (ofString "u256_to_be32") [kvExp, .var .local (ofString "key")])
        have hhoare : Hoare
            (fun s => EvmInv s ∧ s.locals.lookup (ofString "key") = s.globals.lookup (ofString "evm_key_buf"))
            (.call (some (none, none)) (ofString "u256_to_be32") [kvExp, .var .local (ofString "key")])
            (fun r t => r = none → EvmInv t) :=
          Hoare.call0 ek_u2b.keepsOn callEntryOn_u256_to_be32_evm_key_buf
            (fun s _ post v _ _ hq _ => localsFree_evmInv post s.locals post.clock (hq (Or.inl ⟨v, rfl⟩)))
            (fun _ _ hr _ h => absurd h hr)
        have h1 : TerminatingProgBoundedOn
            (fun s => EvmInv s ∧ s.locals.lookup (ofString "key") = s.globals.lookup (ofString "evm_key_buf"))
            (.call (some (none, none)) (ofString "u256_to_be32") [kvExp, .var .local (ofString "key")])
            (B + 1) :=
          TerminatingProgBoundedOn.call_on
            (P := fun s => EvmInv s ∧ s.locals.lookup (ofString "key") = s.globals.lookup (ofString "evm_key_buf"))
            hu2b none [kvExp, .var .local (ofString "key")]
            (callEntryOn_of_imp
              (P := fun s => EvmInv s ∧ s.locals.lookup (ofString "key") = s.globals.lookup (ofString "evm_key_buf"))
              localsFree_guestInv (fun s h => evmInv_guestInv s h.1) _ _)
        unfold TerminatingRunBounded
        dsimp only
        intro hnt'
        rw [evaluateHOLFiniteState_seq_line780] at hnt' ⊢
        rcases hr1 : evaluateHOLFiniteState st _ with ⟨r1, mid⟩
        have hmid := hhoare.run st hc ⟨hI, hkeq⟩
        simp only [hr1] at hmeta hnt' hmid ⊢
        cases r1 with
        | none =>
          dsimp only at hnt' ⊢
          obtain ⟨c1, k1⟩ := h1 st hc ⟨hI, hkeq⟩ (by simp [hr1])
          rw [hr1] at c1 k1; dsimp only at c1 k1
          obtain ⟨c2, k2⟩ := hbody mid (hmeta.1.trans hc) (hmid (by simp) rfl) hnt'
          exact ⟨by omega, by omega⟩
        | some r =>
          dsimp only at hnt' ⊢
          obtain ⟨c1, k1⟩ := h1 st hc ⟨hI, hkeq⟩ (by simpa [hr1] using hnt')
          rw [hr1] at c1 k1; dsimp only at c1 k1
          exact ⟨by omega, k1⟩
      simpa [s1, setVarHOLFinite] using hseq s1 hcode hInv1 hnt
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

/-! ## 6. Concrete-body proofs of `gbody_get_storage`, `gbody_op_sload`, and `gbody_op_sstore` -/

theorem gbody_get_storage_impl
    (hset : TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set»)
    (hrec : TerminatingFunBoundedOn GuestInv (ofString "record_pre_state_read") K.«record_pre_state_read»)
    (hsk : TerminatingFunBoundedOn GuestInv (ofString "sk_make") K.«sk_make»)
    (hsl : TerminatingFunBoundedOn GuestInv (ofString "stor_lookup") K.«stor_lookup»)
    (hws : TerminatingFunBoundedOn WorldOK (ofString "ws_get_storage") K.«ws_get_storage»)
    (hset_spec : type_of% @htab_set_spec)
    (hnz_set : ArgNonNull "t" (ofString "htab_set"))
    (wk_rec : WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "record_pre_state_read"))
    (wk_sk : WorldKeeps WorldOK (fun s => [(globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
      []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "sk_make"))
    (ro_sl : ReadOnlyFn (ofString "stor_lookup")) :
    TerminatingFunBoundedOn WorldOK (ofString "get_storage") K.«get_storage» := by
  have hk_sk : KeepsOn WorldOK WorldOK (ofString "sk_make") := by
    apply wk_sk.keepsOn_buffer_parts
    intro F s i hi
    simp only [List.mem_singleton] at hi
    subst hi
    exact ⟨("sk_buf", 64), by decide, by decide, 52, by decide, rfl⟩
  refine ⟨_, _, _, lookup_get_storage, ?_⟩
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_get_storage]
  simp only [InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.decCall_on hsk _ _ _
      (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _)
      (KeepsOn.resumeOn localsFree_worldOK hk_sk _ _)
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.call_on hset _ _
          (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
        (hoare_htab_set_ts24 hset_spec hnz_set _)
        (TerminatingProgBoundedOn.decCall_on hsl _ _ _
          (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _)
          (ReadOnlyFn.resumeOn (LocalsOnly.of_localsFree localsFree_worldOK) worldOK_guestInv ro_sl _ (by simp) _)
          (TerminatingProgBoundedOn.seq_hoare
            (TerminatingProgBoundedOn.ite_on
              (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _))
              (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
            (Hoare.ite_return_skip _ _)
            (TerminatingProgBoundedOn.seq_hoare
              (TerminatingProgBoundedOn.call_on hsl _ _
                (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
              (Hoare.call_local_keeps localsFree_worldOK
                (ReadOnlyFn.keepsOn localsFree_worldOK worldOK_guestInv ro_sl)
                (callEntryOn_of_localsFree localsFree_worldOK _ _) _)
              (TerminatingProgBoundedOn.seq_hoare
                (TerminatingProgBoundedOn.ite_on
                  (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _))
                  (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
                (Hoare.ite_return_skip _ _)
                (TerminatingProgBoundedOn.seq_hoare
                  (TerminatingProgBoundedOn.call_on hrec _ _
                    (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
                  (Hoare.call_keeps localsFree_worldOK (WorldKeeps.keepsOn wk_rec) _)
                  (TerminatingProgBoundedOn.decCall_on hws _ _ _
                    (callEntryOn_of_localsFree localsFree_worldOK _ _)
                    (decCallResumeOn_guestInv worldOK_guestInv _ _ _)
                    (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))))))))) ?_
  unfold K.«get_storage»
  omega

theorem gbody_op_sload_impl
    (hcg : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (hgs : TerminatingFunBoundedOn WorldOK (ofString "get_storage") K.«get_storage»)
    (hiw : TerminatingFunBoundedOn GuestInv (ofString "is_warm_storage_key") K.«is_warm_storage_key»)
    (hpc : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add»)
    (hpop : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop»)
    (hpush : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push»)
    (hu2b : TerminatingFunBoundedOn GuestInv (ofString "u256_to_be32") K.«u256_to_be32»)
    (hwk : TerminatingFunBoundedOn GuestInv (ofString "warm_storage_key") K.«warm_storage_key»)
    (ek_cg : EvmKeeps EvmInv [] (ofString "charge_gas"))
    (ek_iw : EvmKeeps (EvmAvoids (fun s => [(globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)]))
      [] (ofString "is_warm_storage_key"))
    (ek_pop : EvmKeeps EvmInv [] (ofString "stack_pop"))
    (ek_u2b : EvmKeeps (EvmAvoids (fun s => [(locN s "out", 32)])) [] (ofString "u256_to_be32"))
    (ek_wk : EvmKeeps (EvmAvoids (fun s => [(globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)]))
      ["heap_ptr"] (ofString "warm_storage_key")) :
    TerminatingFunBoundedOn EvmRun (ofString "op_sload") K.«op_sload» := by
  refine ⟨_, _, _, lookup_op_sload, ?_⟩
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_op_sload]
  simp only [InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.mono_pre (fun _ (h : EvmRun _) => h.1)
      (TerminatingProgBoundedOn.decCall_on hpop _ _ _
        (callEntryOn_of_imp localsFree_guestInv evmInv_guestInv _ _)
        (KeepsOn.resumeOn localsFree_evmInv ek_pop.keepsOn _ _)
        (dec_key_u256_to_be32_on hu2b ek_u2b _
          (TerminatingProgBoundedOn.dec_on localsFree_evmInv _ _ _
            (TerminatingProgBoundedOn.decCall_on hiw _ _ _
              (callEntryOn_of_imp localsFree_guestInv evmInv_guestInv _ _)
              (KeepsOn.resumeOn_entry localsFree_evmInv ek_iw.keepsOn callEntryOn_sk_buf _)
              (TerminatingProgBoundedOn.seq_hoare
                (TerminatingProgBoundedOn.ite_on
                  (TerminatingProgBoundedOn.call_on hcg _ _
                    (callEntryOn_of_imp localsFree_guestInv evmInv_guestInv _ _))
                  (TerminatingProgBoundedOn.seq_hoare
                    (TerminatingProgBoundedOn.call_on hcg _ _
                      (callEntryOn_of_imp localsFree_guestInv evmInv_guestInv _ _))
                    (Hoare.call_keeps localsFree_evmInv ek_cg.keepsOn _)
                    (TerminatingProgBoundedOn.call_on hwk _ _
                      (callEntryOn_of_imp localsFree_guestInv evmInv_guestInv _ _))))
                (Hoare.ite_keeps
                  (Hoare.call_keeps localsFree_evmInv ek_cg.keepsOn _)
                  (Hoare.seq_fall
                    (Hoare.call_keeps localsFree_evmInv ek_cg.keepsOn _)
                    (Hoare.call0_keeps_entry localsFree_evmInv ek_wk.keepsOn callEntryOn_sk_buf)))
                (TerminatingProgBoundedOn.decCall_on hgs _ _ _
                  (callEntryOn_of_imp localsFree_worldOK worldOK_of_evmInv _ _)
                  (decCallResumeOn_guestInv evmInv_guestInv _ _ _)
                  (TerminatingProgBoundedOn.seq_guestInv
                    (TerminatingProgBoundedOn.call_guestInv hpush _ _)
                    (TerminatingProgBoundedOn.seq_guestInv
                      (TerminatingProgBoundedOn.call_guestInv hpc _ _)
                      (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _))))))))))) ?_
  unfold K.«op_sload»
  simp only [show ∀ a b : Nat, Nat.max a b = max a b from fun _ _ => rfl]
  omega

theorem gbody_op_sstore_impl
    (hcg : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (hcsg : TerminatingFunBoundedOn GuestInv (ofString "charge_state_gas") K.«charge_state_gas»)
    (hckg : TerminatingFunBoundedOn GuestInv (ofString "check_gas") K.«check_gas»)
    (href : TerminatingFunBoundedOn GuestInv (ofString "credit_state_gas_refund") K.«credit_state_gas_refund»)
    (hgs : TerminatingFunBoundedOn WorldOK (ofString "get_storage") K.«get_storage»)
    (hgso : TerminatingFunBoundedOn WorldOK (ofString "get_storage_original") K.«get_storage_original»)
    (hiw : TerminatingFunBoundedOn GuestInv (ofString "is_warm_storage_key") K.«is_warm_storage_key»)
    (hmax : TerminatingFunBoundedOn GuestInv (ofString "max") K.«max»)
    (hpc : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add»)
    (hrns : TerminatingFunBoundedOn GuestInv (ofString "require_not_static") K.«require_not_static»)
    (hss : TerminatingFunBoundedOn GuestInv (ofString "set_storage") K.«set_storage»)
    (hpop : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop»)
    (heq : TerminatingFunBoundedOn GuestInv (ofString "u256_eq") K.«u256_eq»)
    (hisz : TerminatingFunBoundedOn GuestInv (ofString "u256_is_zero") K.«u256_is_zero»)
    (hu2b : TerminatingFunBoundedOn GuestInv (ofString "u256_to_be32") K.«u256_to_be32»)
    (hwk : TerminatingFunBoundedOn GuestInv (ofString "warm_storage_key") K.«warm_storage_key»)
    (ek_cg : EvmKeeps EvmInv [] (ofString "charge_gas"))
    (ro_ckg : ReadOnlyFn (ofString "check_gas"))
    (ek_gso : EvmKeeps (EvmAvoids (fun s => [
      (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
      (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
      (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)]))
      ["heap_ptr", "scratch_ptr"] (ofString "get_storage_original"))
    (ek_iw : EvmKeeps (EvmAvoids (fun s => [(globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)]))
      [] (ofString "is_warm_storage_key"))
    (ro_max : ReadOnlyFn (ofString "max"))
    (ro_rns : ReadOnlyFn (ofString "require_not_static"))
    (ek_pop : EvmKeeps EvmInv [] (ofString "stack_pop"))
    (ek_u2b : EvmKeeps (EvmAvoids (fun s => [(locN s "out", 32)])) [] (ofString "u256_to_be32"))
    (ek_wk : EvmKeeps (EvmAvoids (fun s => [(globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)]))
      ["heap_ptr"] (ofString "warm_storage_key")) :
    TerminatingFunBoundedOn EvmRun (ofString "op_sstore") K.«op_sstore» := by
  refine ⟨_, _, _, lookup_op_sstore, ?_⟩
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_op_sstore]
  simp only [InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.mono_pre (fun _ (h : EvmRun _) => h.1)
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.call_on hrns _ _
          (callEntryOn_of_imp localsFree_guestInv evmInv_guestInv _ _))
        (Hoare.call_keeps localsFree_evmInv
          (ReadOnlyFn.keepsOn localsFree_evmInv evmInv_guestInv ro_rns) _)
        (TerminatingProgBoundedOn.decCall_on hpop _ _ _
          (callEntryOn_of_imp localsFree_guestInv evmInv_guestInv _ _)
          (KeepsOn.resumeOn localsFree_evmInv ek_pop.keepsOn _ _)
          (TerminatingProgBoundedOn.decCall_on hpop _ _ _
            (callEntryOn_of_imp localsFree_guestInv evmInv_guestInv _ _)
            (KeepsOn.resumeOn localsFree_evmInv ek_pop.keepsOn _ _)
            (dec_key_u256_to_be32_on hu2b ek_u2b _
              (TerminatingProgBoundedOn.dec_on localsFree_evmInv _ _ _
                (TerminatingProgBoundedOn.decCall_on hiw _ _ _
                  (callEntryOn_of_imp localsFree_guestInv evmInv_guestInv _ _)
                  (KeepsOn.resumeOn_entry localsFree_evmInv ek_iw.keepsOn callEntryOn_sk_buf _)
                  (TerminatingProgBoundedOn.dec_on localsFree_evmInv _ _ _
                    (TerminatingProgBoundedOn.seq_hoare
                      (TerminatingProgBoundedOn.ite_on
                        (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
                        (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
                      (Hoare.ite_keeps
                        (Hoare.assign_local_keeps localsFree_evmInv _ _)
                        (Hoare.skip fun _ h _ => h))
                      (TerminatingProgBoundedOn.decCall_on hmax _ _ _
                        (callEntryOn_of_imp localsFree_guestInv evmInv_guestInv _ _)
                        (ReadOnlyFn.resumeOn (LocalsOnly.of_localsFree localsFree_evmInv) evmInv_guestInv ro_max _ (by simp) _)
                        (TerminatingProgBoundedOn.seq_hoare
                          (TerminatingProgBoundedOn.call_on hckg _ _
                            (callEntryOn_of_imp localsFree_guestInv evmInv_guestInv _ _))
                          (Hoare.call_keeps localsFree_evmInv
                            (ReadOnlyFn.keepsOn localsFree_evmInv evmInv_guestInv ro_ckg) _)
                          (TerminatingProgBoundedOn.seq_hoare
                            (TerminatingProgBoundedOn.call_on hcg _ _
                              (callEntryOn_of_imp localsFree_guestInv evmInv_guestInv _ _))
                            (Hoare.call_keeps localsFree_evmInv ek_cg.keepsOn _)
                            (TerminatingProgBoundedOn.seq_hoare
                              (TerminatingProgBoundedOn.ite_on
                                (TerminatingProgBoundedOn.call_on hwk _ _
                                  (callEntryOn_of_imp localsFree_guestInv evmInv_guestInv _ _))
                                (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
                              (Hoare.ite_keeps
                                (Hoare.call0_keeps_entry localsFree_evmInv ek_wk.keepsOn callEntryOn_sk_buf)
                                (Hoare.skip fun _ h _ => h))
                              (TerminatingProgBoundedOn.decCall_on hgso _ _ _
                                (callEntryOn_of_imp localsFree_worldOK worldOK_of_evmInv _ _)
                                (KeepsOn.resumeOn_entry localsFree_evmInv ek_gso.keepsOn callEntryOn_keccak_mpt_nib _)
                                (TerminatingProgBoundedOn.decCall_on hgs _ _ _
                                  (callEntryOn_of_imp localsFree_worldOK worldOK_of_evmInv _ _)
                                  (decCallResumeOn_guestInv evmInv_guestInv _ _ _)
                                  (TerminatingProgBoundedOn.decCall_guestInv heq _ _ _
                                    (TerminatingProgBoundedOn.decCall_guestInv heq _ _ _
                                      (TerminatingProgBoundedOn.decCall_guestInv heq _ _ _
                                        (TerminatingProgBoundedOn.decCall_guestInv hisz _ _ _
                                          (TerminatingProgBoundedOn.decCall_guestInv hisz _ _ _
                                            (TerminatingProgBoundedOn.decCall_guestInv hisz _ _ _
                                              (TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _
                                                (TerminatingProgBoundedOn.seq_guestInv
                                                  (TerminatingProgBoundedOn.ite_on
                                                    (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
                                                    (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
                                                  (TerminatingProgBoundedOn.seq_guestInv
                                                    (TerminatingProgBoundedOn.ite_on
                                                      (TerminatingProgBoundedOn.seq_guestInv
                                                        (TerminatingProgBoundedOn.ite_on
                                                          (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                                          (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
                                                        (TerminatingProgBoundedOn.seq_guestInv
                                                          (TerminatingProgBoundedOn.ite_on
                                                            (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                                            (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
                                                          (TerminatingProgBoundedOn.ite_on
                                                            (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                                            (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))))
                                                      (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
                                                    (TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _
                                                      (TerminatingProgBoundedOn.seq_guestInv
                                                        (TerminatingProgBoundedOn.ite_on
                                                          (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
                                                          (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
                                                        (TerminatingProgBoundedOn.seq_guestInv
                                                          (TerminatingProgBoundedOn.ite_on
                                                            (TerminatingProgBoundedOn.call_guestInv href _ _)
                                                            (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
                                                          (TerminatingProgBoundedOn.seq_guestInv
                                                            (TerminatingProgBoundedOn.call_guestInv hcg _ _)
                                                            (TerminatingProgBoundedOn.seq_guestInv
                                                              (TerminatingProgBoundedOn.call_guestInv hcsg _ _)
                                                              (TerminatingProgBoundedOn.seq_guestInv
                                                                (TerminatingProgBoundedOn.call_guestInv hss _ _)
                                                                (TerminatingProgBoundedOn.seq_guestInv
                                                                  (TerminatingProgBoundedOn.call_guestInv hpc _ _)
                                                                  (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _))))))))))))))))))))))))))))))) ?_
  unfold K.«op_sstore»
  simp only [show ∀ a b : Nat, Nat.max a b = max a b from fun _ _ => rfl]
  omega

end InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyStorageOps
