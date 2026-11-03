import InitECandidate.Solver.Wave8GuestInv.R16Shards.GbodyC17ToC21Common
import InitECandidate.Solver.Wave8GuestInv.ContractParts.C21

/-! Zero-sorry proof of `gbody_main` (`ContractParts/C21.lean`) and `InputAtWith` preservation. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16Shards.GbodyC17ToC21Common

theorem lookup_verify_stateless_new_payload_fn :
    originalRuntimeCode.lookup (ofString "verify_stateless_new_payload") =
      some ((sourceFunctionEntry Guest.Software.guestFn_verify_stateless_new_payload).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 887 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_verify_stateless_new_payload) rfl

theorem lookup_main_fn :
    originalRuntimeCode.lookup (ofString "main") =
      some ((sourceFunctionEntry Guest.Software.guestFn_main).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 889 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_main) rfl

theorem clock_storeByte {F : Type} (s : PanSemStateFiniteExact 64 F) (a v : ExpHOL 64) :
    (evaluateHOLFiniteState s (.storeByte a v)).2.clock = s.clock := by
  rw [evaluateHOLFiniteState_storeByte]
  repeat' split
  all_goals (try dsimp only)
  all_goals (try rfl)

/-! ## 11. `InputAt` Preservation & `gbody_main` (`ContractParts/C21.lean`) -/

def InputAtWith {F : Type} (s : PanSemStateFiniteExact 64 F) (S Nd : List Nat) (si : Nat) : Prop :=
  ArenaReady s ∧ WorldTypedWith s S Nd ∧
    (∀ i ∈ inputCells s si, Inside i sourceBase (globN s "heap_ptr") ∧ WordsOK s i) ∧
    IvlsDisj (inputCells s si) (worldOwned s S Nd) ∧
    memW s (memW s si + 40) < 2 ^ 63 ∧
    PayloadAt s (memW s si) ∧ RequestsAt s (memW s (si + 32))

theorem inputAt_iff_with {F : Type} (s : PanSemStateFiniteExact 64 F) (si : Nat) :
    InputAt s si ↔ ∃ S Nd, InputAtWith s S Nd si := by
  simp only [InputAt, InputAtWith]
  constructor
  · rintro ⟨hA, S, Nd, hW, h1, h2, h3, h4, h5⟩; exact ⟨S, Nd, hA, hW, h1, h2, h3, h4, h5⟩
  · rintro ⟨S, Nd, hA, hW, h1, h2, h3, h4, h5⟩; exact ⟨hA, S, Nd, hW, h1, h2, h3, h4, h5⟩

theorem inputAtWith_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S Nd : List Nat) (si : Nat) :
    InputAtWith { s with locals := locals, clock := k } S Nd si ↔ InputAtWith s S Nd si := by
  simp only [InputAtWith, worldTypedWith_with_locals, arenaReady_with_locals]
  exact Iff.rfl

theorem wordsOK_congr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post) {i : Ivl} (hw : WordsOK s i) :
    WordsOK post i :=
  wordsOK_transfer hgS hgP hw

theorem WorldStep.preserves_inputAtWith
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {F : Type} {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {S Nd : List Nat} {si : Nat}
    (hIA : InputAtWith s S Nd si)
    (hws : WorldStep R gw keep Q s r post)
    (hR_z : ∀ j ∈ R s, j.2 = 0 → j.1 % 8 = 0)
    (hR_ti : IvlsDisj (R s) (worldTypedIvls s S Nd))
    (hR_in : IvlsDisj (inputCells s si) (R s)) :
    ∃ S' Nd', (∀ t ∈ S, t ∈ S') ∧ InputAtWith post S' Nd' si ∧
      OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd') ∧
      FrameOutside s post (worldOwned s S Nd ++ R s ++ [freeGap s]) (heapFree s) ∧
      Q s r post S' Nd' := by
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  obtain ⟨hAs, hWT, hcells, hdisj_ow, hntx63, hPay, hReq⟩ := hIA
  obtain ⟨hAp, hhp, _, _, hStep⟩ := hws
  have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hAs.2.2.1
  obtain ⟨S', Nd', hsub, hWT', hog, hfr, hQ⟩ := hStep S Nd hWT hR_ti
  have hold_z := worldOwned_zero_aligned hWT
  -- Each of the 4 inputCells survives the step:
  have h_surv : ∀ b ∈ inputCells s si,
      Inside b sourceBase (globN post "heap_ptr") ∧
      (∀ o ∈ worldOwned post S' Nd', Disj b o) ∧
      IvlUnhit s post b := by
    intro b hb
    obtain ⟨hb_in, hb_w⟩ := hcells b hb
    exact heap_ivl_survives_step hAs.2 hhp hog hfr hold_z hR_z hb_w.1 hb_w.2.1 hb_in
      (fun j hj => hdisj_ow b hb j hj) (fun j hj => hR_in b hb j hj)
  have hsi_mem : (si, 40) ∈ inputCells s si := by simp [inputCells]
  obtain ⟨hsi_in_s, hsi_w_s⟩ := hcells (si, 40) hsi_mem
  obtain ⟨_, _, hsi_u⟩ := h_surv (si, 40) hsi_mem
  have hsi_eq0 : memW post si = memW s si :=
    memW_eq_of_ivlUnhit hsi_u hsi_w_s.1 (by unfold Inside at hsi_in_s; omega) ⟨le_rfl, by omega⟩
  have hsi_eq32 : memW post (si + 32) = memW s (si + 32) :=
    memW_eq_of_ivlUnhit hsi_u (by have := hsi_w_s.1; omega) (by unfold Inside at hsi_in_s; omega)
      ⟨by omega, by omega⟩
  set pl := memW s si
  set rq := memW s (si + 32)
  have hpl_mem : (pl, 136) ∈ inputCells s si := by simp [inputCells, pl]
  obtain ⟨hpl_in_s, hpl_w_s⟩ := hcells (pl, 136) hpl_mem
  obtain ⟨_, _, hpl_u⟩ := h_surv (pl, 136) hpl_mem
  have hpl_word : ∀ off, off % 8 = 0 → off + 8 ≤ 136 → memW post (pl + off) = memW s (pl + off) :=
    fun off hoff8 hoff_hi =>
      memW_eq_of_ivlUnhit hpl_u (by have := hpl_w_s.1; omega)
        (by unfold Inside at hpl_in_s; omega) ⟨by omega, by omega⟩
  have hpl24 : memW post (pl + 24) = memW s (pl + 24) := hpl_word 24 (by omega) (by omega)
  have hpl32 : memW post (pl + 32) = memW s (pl + 32) := hpl_word 32 (by omega) (by omega)
  have hpl40 : memW post (pl + 40) = memW s (pl + 40) := hpl_word 40 (by omega) (by omega)
  have hic_eq : inputCells post si = inputCells s si := by
    simp only [inputCells, hsi_eq0, hsi_eq32]
    change [(si, 40), (pl, 136), (rq, 80), (memW post (pl + 32), 16 * memW post (pl + 40))] =
           [(si, 40), (pl, 136), (rq, 80), (memW s (pl + 32), 16 * memW s (pl + 40))]
    rw [hpl32, hpl40]
  have hrq_mem : (rq, 80) ∈ inputCells s si := by simp [inputCells, rq]
  obtain ⟨hrq_in_s, hrq_w_s⟩ := hcells (rq, 80) hrq_mem
  obtain ⟨_, _, hrq_u⟩ := h_surv (rq, 80) hrq_mem
  have hptxs_mem : (memW s (pl + 32), 16 * memW s (pl + 40)) ∈ inputCells s si := by
    simp [inputCells, pl]
  obtain ⟨hptxs_in_s, hptxs_w_s⟩ := hcells _ hptxs_mem
  obtain ⟨_, _, hptxs_u⟩ := h_surv _ hptxs_mem
  refine ⟨S', Nd', hsub, ⟨hAp, hWT', ?_, ?_, ?_, ?_, ?_⟩, hog, hfr, hQ⟩
  · rw [hic_eq]
    intro i hi
    exact ⟨(h_surv i hi).1, wordsOK_transfer hAs.1 hAp.1 (hcells i hi).2⟩
  · rw [hic_eq]
    intro i hi o ho
    exact (h_surv i hi).2.1 o ho
  · rw [hsi_eq0]; change memW post (pl + 40) < 2 ^ 63; rw [hpl40]; exact hntx63
  · rw [hsi_eq0]; change PayloadAt post pl
    refine ⟨wordsOK_transfer hAs.1 hAp.1 hPay.1, ?_, ?_, ?_⟩
    · rw [hpl24]; exact hPay.2.1
    · rw [hpl40]; exact hPay.2.2.1
    · rw [hpl32, hpl40]
      intro idx hidx
      have hcell_eq : memW post (memW s (pl + 32) + 16 * idx + 8) =
          memW s (memW s (pl + 32) + 16 * idx + 8) :=
        memW_eq_of_ivlUnhit hptxs_u (by have := hptxs_w_s.1; omega)
          (by unfold Inside at hptxs_in_s; omega) ⟨by dsimp; omega, by dsimp; omega⟩
      rw [hcell_eq]
      exact hPay.2.2.2 idx hidx
  · rw [hsi_eq32]; change RequestsAt post rq
    refine ⟨wordsOK_transfer hAs.1 hAp.1 hReq.1, fun idx hidx => ?_⟩
    have hcell_eq : memW post (rq + 16 * idx + 8) = memW s (rq + 16 * idx + 8) :=
      memW_eq_of_ivlUnhit hrq_u (by have := hrq_w_s.1; omega)
        (by unfold Inside at hrq_in_s; omega) ⟨by omega, by omega⟩
    rw [hcell_eq]
    exact hReq.2 idx hidx

theorem bufferRegion_zero_aligned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (g : String) (sz : Nat) (hsz : sz ≠ 0) :
    (bufferRegion s (g, sz)).2 = 0 → (bufferRegion s (g, sz)).1 % 8 = 0 := by
  intro hz
  unfold bufferRegion at hz ⊢
  dsimp only at hz ⊢
  by_cases hg0 : globN s g = 0
  · rw [hg0]
  · rw [if_neg hg0] at hz; exact absurd hz hsz

theorem bufferRegion_mem_worldOwned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S Nd : List Nat) {gn : String × Nat} (hgn : gn ∈ globalBuffers) :
    bufferRegion s gn ∈ worldOwned s S Nd := by
  unfold worldOwned fixedObjects
  apply List.mem_append.2; left; apply List.mem_append.2; right
  apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
  exact List.mem_map.2 ⟨gn, hgn, rfl⟩

theorem inputCells_disj_bufferRegion_le {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si : Nat} (hdisj_ow : IvlsDisj (inputCells s si) (worldOwned s S Nd))
    (gn : String × Nat) (hgn : gn ∈ globalBuffers) (n : Nat) (hle : n ≤ gn.2) :
    ∀ i ∈ inputCells s si, Disj i (bufferRegion s (gn.1, n)) := by
  intro i hi
  have hd := hdisj_ow i hi (bufferRegion s gn) (bufferRegion_mem_worldOwned s S Nd hgn)
  by_cases hz : globN s gn.1 = 0
  · exact Or.inr (Or.inl (by simp [bufferRegion, hz]))
  · simp only [bufferRegion, hz, ↓reduceIte] at hd ⊢
    unfold Disj at hd ⊢; dsimp only at hd ⊢; omega

private theorem decCall_ne_none_of_cont {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (sh : ShapeHOL) (fname : MlS) (args : List (ExpHOL 64)) (cont : ProgHOL 64)
    (hc : ∀ {F2 : Type} (t : PanSemStateFiniteExact 64 F2), (evaluateHOLFiniteState t cont).1 ≠ none) :
    (evaluateHOLFiniteState s (.decCall name sh fname args cont)).1 ≠ none := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp
  · dsimp only
    rcases lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨b, cal, rsh⟩
    · simp
    · dsimp only
      split_ifs with hz
      · simp
      · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s cal) b with ⟨res, post⟩
        cases res with
        | none => simp
        | some r =>
          cases r with
          | returned v =>
            dsimp only
            split_ifs
            · dsimp only; exact hc _
            · simp
          | _ => simp

private theorem seq3_return_ne_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p1 p2 p3 : ProgHOL 64) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.seq p1 (.seq p2 (.seq p3 (.return e))))).1 ≠ none := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases evaluateHOLFiniteState s p1 with ⟨r1, s1⟩
  cases r1 with
  | some _ => simp
  | none =>
    dsimp only; rw [evaluateHOLFiniteState_seq_line780]
    rcases evaluateHOLFiniteState s1 p2 with ⟨r2, s2⟩
    cases r2 with
    | some _ => simp
    | none =>
      dsimp only; rw [evaluateHOLFiniteState_seq_line780]
      rcases evaluateHOLFiniteState s2 p3 with ⟨r3, s3⟩
      cases r3 with
      | some _ => simp
      | none => exact return_ne_none s3 e

theorem Hoare.callHandleDest_fall {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop}
    {kind : VarKind} {dest exn var fname : MlS} {handler : ProgHOL 64}
    {arguments : List (ExpHOL 64)}
    (hf : FunSpec Pc Qc fname) (hentry : CallEntryOn P Pc fname arguments)
    (hh_ne : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState t handler).1 ≠ none)
    (hret : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (post : PanSemStateFiniteExact 64 F)
      (v : ValueHOL 64), s.code = originalRuntimeCode → P s →
      Qc (callEntryStateHOLFinite s callee) (some (.returned v)) post →
      Q (setKvarHOLFinite kind dest v { post with locals := s.locals })) :
    Hoare P (.call (some (some (kind, dest), some (exn, var, handler))) fname arguments)
      (fun r t => r = none → Q t) := by
  refine ⟨fun {F} s hcode hP hnt => ?_⟩
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite s
      (h := fun address => Classical.propDecidable (s.memaddrs address)) arguments with
    _ | values
  · simp
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · simp
    · simp only [hl] at hnt ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hPc := hentry s values body' callee ret' hcode hP hargs hl
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with
          ⟨res, post⟩
        simp only [hrun] at hnt ⊢
        cases res with
        | none => simp
        | some r =>
          cases r with
          | returned v =>
            have hQc : Qc (callEntryStateHOLFinite s callee) (some (.returned v)) post := by
              have := FunSpec.at_lookup hf s hcode values body' callee ret' hl hPc (by rw [hrun]; simp)
              rw [hrun] at this; exact this
            dsimp only
            split
            · split
              · intro _; exact hret s callee post v hcode hP hQc
              · simp
            · simp
          | exception eid v =>
            dsimp only
            split
            · rcases s.eshapes.lookup eid with _ | sh
              · simp
              · dsimp only
                split
                · intro hr; exact absurd hr (hh_ne _)
                · simp
            · simp
          | _ => simp

def WorldWithBuf (bufName : String) (sz : Nat) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_b : BitVec 64, ∃ S Nd : List Nat,
    ArenaReady s ∧ WorldTypedWith s S Nd ∧
    s.locals.lookup (ofString bufName) = some (.val (.word w_b)) ∧
    w_b.toNat % 8 = 0 ∧
    Inside (w_b.toNat, sz) sourceBase (globN s "heap_ptr") ∧
    IvlsDisj [(w_b.toNat, sz)] (worldOwned s S Nd)

theorem worldWithBuf_guestInv {bufName : String} {sz : Nat} {F : Type}
    (s : PanSemStateFiniteExact 64 F) (h : WorldWithBuf bufName sz s) : GuestInv s := by
  obtain ⟨_, _, _, hA, _⟩ := h; exact hA.1

theorem resumeOn_alloc_worldWithBuf (bufName : String) (sz : Nat) (hsz8 : sz % 8 = 0)
    (hsz_lt : sz < 2 ^ 64)
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc")) :
    DecCallResumeOn WorldOK (WorldWithBuf bufName sz) (ofString bufName) (ofString "alloc")
      [.const (BitVec.ofNat 64 sz)] := by
  intro F state values body callee ret value post hcode hW hargs hl hrun
  obtain ⟨hAs, S, hS⟩ := hW
  obtain ⟨Nd, hWT⟩ := (worldTyped_iff_with state S).1 hS
  have hpc := callee_param_one_exp state (ofString "alloc") (ofString "n") .one _ _
    (by rw [hcode]; exact lookup_alloc_fn) (.const (BitVec.ofNat 64 sz))
    (.val (.word (BitVec.ofNat 64 sz))) values body callee ret rfl hargs hl
  have hn_loc : locN (callEntryStateHOLFinite state callee) "n" = sz := by
    simp only [locN, callEntryStateHOLFinite, hpc.2, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hsz_lt
  have hround : (sz + 7) / 8 * 8 = sz := by omega
  have hstep := FunSpec.at_lookup wal state hcode values body callee ret hl
    (localsFree_worldOK state callee (state.clock - 1) ⟨hAs, S, hS⟩) (by rw [hrun]; simp)
  rw [hrun] at hstep; dsimp only at hstep
  obtain ⟨hAp, _, _, _, hWS⟩ := hstep (Or.inl ⟨value, rfl⟩)
  have hrt := FunSpec.at_lookup rtal state hcode values body callee ret hl
    (localsFree_arenaReady state callee (state.clock - 1) hAs) (by rw [hrun]; simp)
  rw [hrun] at hrt; dsimp only at hrt
  obtain ⟨w_b, rfl, _, _, hfb⟩ := hrt value rfl
  rw [hn_loc] at hfb
  have hfb_in : Inside (w_b.toNat, sz) (globN state "heap_ptr") (globN post "heap_ptr") := by
    have := hfb.2.1; rw [hround] at this; exact this
  obtain ⟨S', Nd', _, hWT', _, _, hQ⟩ :=
    hWS S Nd ((worldTypedWith_with_locals _ _ _ _ _).2 hWT) (fun x hx => by simp at hx)
  obtain ⟨w_b', hw_eq, hav⟩ := hQ (.val (.word w_b)) rfl
  injection hw_eq with hw_eq'; injection hw_eq' with hw_eq''; subst hw_eq''
  dsimp only at hav; rw [hn_loc, hround] at hav
  refine ⟨w_b, S', Nd', localsFree_arenaReady post _ post.clock hAp,
    (worldTypedWith_with_locals post _ post.clock S' Nd').2 hWT',
    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
    hfb.1, ⟨Nat.le_trans hAs.2.1 hfb_in.1, hfb_in.2⟩, hav⟩

theorem hoare_memzero_worldWithBuf (bufName : String) (sz : Nat) (hsz_lt : sz < 2 ^ 64)
    (wmz : WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")]) []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "memzero")) :
    Hoare (WorldWithBuf bufName sz)
      (.call (some (none, none)) (ofString "memzero")
        [.var .local (ofString bufName), .const (BitVec.ofNat 64 sz)])
      (fun r t => r = none → WorldOK t) := by
  refine ⟨fun {F} state hcode hWB _ hr => ?_⟩
  rcases hcall : evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "memzero")
        [.var .local (ofString bufName), .const (BitVec.ofNat 64 sz)]) with ⟨cres, cpost⟩
  have hr' : cres = none := by rw [hcall] at hr; exact hr
  subst hr'
  obtain ⟨w_b, S, Nd, hAs, hWT, hlu_b, _, _, hdisj_b⟩ := hWB
  rw [evaluateHOLFiniteState_call] at hcall
  have hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString bufName), .const (BitVec.ofNat 64 sz)] =
      some [.val (.word w_b), .val (.word (BitVec.ofNat 64 sz))] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, evalHOLExact, hlu_b]
  rw [hargs] at hcall; dsimp only at hcall
  rcases hl : lookupCodeHOLFinite state.code.lookup (ofString "memzero")
      [.val (.word w_b), .val (.word (BitVec.ofNat 64 sz))] with _ | ⟨body, callee, ret⟩
  · rw [hl] at hcall; simp at hcall
  · rw [hl] at hcall; dsimp only at hcall
    split_ifs at hcall with hz
    · simp at hcall
    · rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with ⟨bres, post⟩
      rw [hb] at hcall
      cases bres with
      | none => simp at hcall
      | some br =>
        cases br with
        | returned v =>
          dsimp only at hcall
          split_ifs at hcall with hsh
          · obtain ⟨_, hpost_eq⟩ := Prod.mk.inj hcall
            have hpc := callee_param_two state (ofString "memzero") (ofString "dst") (ofString "n")
              .one .one _ _ (by rw [hcode]; exact lookup_memzero_fn)
              (.var .local (ofString bufName)) (.const (BitVec.ofNat 64 sz))
              (.val (.word w_b)) (.val (.word (BitVec.ofNat 64 sz)))
              [.val (.word w_b), .val (.word (BitVec.ofNat 64 sz))] body callee ret
              (by simpa [evalAt, evalHOLExact] using hlu_b) rfl hargs hl
            have hdst : locN (callEntryStateHOLFinite state callee) "dst" = w_b.toNat := by
              simp [locN, callEntryStateHOLFinite, hpc.2.1]
            have hn : locN (callEntryStateHOLFinite state callee) "n" = sz := by
              simp only [locN, callEntryStateHOLFinite, hpc.2.2, BitVec.toNat_ofNat]
              exact Nat.mod_eq_of_lt hsz_lt
            have hstep := FunSpec.at_lookup wmz state hcode _ body callee ret hl
              (localsFree_worldOK state callee (state.clock - 1) ⟨hAs, S, (worldTyped_iff_with state S).2 ⟨Nd, hWT⟩⟩)
              (by rw [hb]; simp)
            rw [hb] at hstep; dsimp only at hstep
            have hws := hstep (Or.inl ⟨v, rfl⟩)
            have hWT_entry := (worldTypedWith_with_locals state callee (state.clock - 1) S Nd).2 hWT
            have hW_post : WorldOK post := hws.worldOK ⟨S, Nd, hWT_entry, fun i hi j hj => by
              change i ∈ [(locN (callEntryStateHOLFinite state callee) "dst",
                locN (callEntryStateHOLFinite state callee) "n")] at hi
              simp only [hdst, hn, List.mem_singleton] at hi; subst hi
              exact hdisj_b (w_b.toNat, sz) (by simp) j (worldTypedIvls_sub_worldOwned _ _ _ j hj)⟩
            have hW_res := localsFree_worldOK post state.locals post.clock hW_post
            rwa [hpost_eq] at hW_res
          · simp at hcall
        | _ => simp [emptyLocalsHOLFinite] at hcall

def InputReadyWithRoot : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_si w_rt : BitVec 64, ∃ S Nd : List Nat,
    InputAtWith s S Nd w_si.toNat ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "root") = some (.val (.word w_rt)) ∧
    w_rt.toNat % 8 = 0 ∧
    Inside (w_rt.toNat, 32) sourceBase (globN s "heap_ptr") ∧
    IvlsDisj [(w_rt.toNat, 32)] (worldOwned s S Nd) ∧
    IvlsDisj (inputCells s w_si.toNat) [(w_rt.toNat, 32)]

theorem inputReadyWithRoot_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : InputReadyWithRoot s) : GuestInv s := by
  obtain ⟨_, _, _, _, hIA, _⟩ := h; exact hIA.1.1

theorem lookup_htr_new_payload_request_fn :
    originalRuntimeCode.lookup (ofString "htr_new_payload_request") =
      some ((sourceFunctionEntry Guest.Software.guestFn_htr_new_payload_request).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 218 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htr_new_payload_request) rfl

theorem resumeOn_alloc32_inputReady
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc")) :
    DecCallResumeOn
      (fun s => ∃ w_si : BitVec 64, s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
        InputAt s w_si.toNat)
      InputReadyWithRoot
      (ofString "root") (ofString "alloc") [.const 32#64] := by
  intro F state values body callee ret value post hcode ⟨w_si, hlu_si, hIA0⟩ hargs hl hrun
  obtain ⟨S, Nd, hIA⟩ := (inputAt_iff_with state w_si.toNat).1 hIA0
  have hAs := hIA.1
  have hW_state : WorldOK state := ⟨hAs, S, (worldTyped_iff_with state S).2 ⟨Nd, hIA.2.1⟩⟩
  have hpc := callee_param_one_exp state (ofString "alloc") (ofString "n") .one _ _
    (by rw [hcode]; exact lookup_alloc_fn) (.const 32#64) (.val (.word 32#64)) values body callee ret rfl hargs hl
  have hn_loc : locN (callEntryStateHOLFinite state callee) "n" = 32 := by
    simp [locN, callEntryStateHOLFinite, hpc.2]
  have hstep := FunSpec.at_lookup wal state hcode values body callee ret hl
    (localsFree_worldOK state callee (state.clock - 1) hW_state) (by rw [hrun]; simp)
  rw [hrun] at hstep; dsimp only at hstep
  have hws := hstep (Or.inl ⟨value, rfl⟩)
  have hrt := FunSpec.at_lookup rtal state hcode values body callee ret hl
    (localsFree_arenaReady state callee (state.clock - 1) hAs) (by rw [hrun]; simp)
  rw [hrun] at hrt; dsimp only at hrt
  obtain ⟨w_rt, rfl, _, _, hfb⟩ := hrt value rfl
  rw [hn_loc] at hfb
  have hfb_in : Inside (w_rt.toNat, 32) (globN state "heap_ptr") (globN post "heap_ptr") := hfb.2.1
  have hIA_entry : InputAtWith (callEntryStateHOLFinite state callee) S Nd w_si.toNat :=
    (inputAtWith_with_locals state callee (state.clock - 1) S Nd w_si.toNat).2 hIA
  obtain ⟨S', Nd', _, hIA_post, _, _, hQ⟩ :=
    hIA_entry |> fun h => WorldStep.preserves_inputAtWith h hws
      (fun _ hj => by simp at hj) (fun _ hj => by simp at hj) (fun _ _ _ hj => by simp at hj)
  obtain ⟨w_rt', hw_eq, hav⟩ := hQ (.val (.word w_rt)) rfl
  injection hw_eq with hw_eq'; injection hw_eq' with hw_eq''; subst hw_eq''
  dsimp only at hav; rw [hn_loc] at hav
  set resumed := setVarHOLFinite (ofString "root") (.val (.word w_rt)) { post with locals := state.locals }
  have hic_disj_rt : IvlsDisj (inputCells post w_si.toNat) [(w_rt.toNat, 32)] := by
    -- Every inputCell in `state` was `< globN state "heap_ptr" ≤ w_rt.toNat`, and `inputCells post = inputCells state`!
    intro c hc x hx
    simp only [List.mem_singleton] at hx; subst hx
    -- Actually, wait: let's prove `c ∈ inputCells state w_si.toNat`? Even simpler: in `state`,
    -- `hfb_in.1 : globN state "heap_ptr" ≤ w_rt.toNat`, and `WorldStep` FrameOutside keeps `si`, `pl`, `pl+32`, `pl+40`!
    have hsi_mem : (w_si.toNat, 40) ∈ inputCells state w_si.toNat := by simp [inputCells]
    have hpl_mem : (memW state w_si.toNat, 136) ∈ inputCells state w_si.toNat := by simp [inputCells]
    have h264 : heapLimit ≤ 2 ^ 64 := by decide
    have hhp_lim : globN state "heap_ptr" ≤ heapLimit := hAs.2.2.1
    obtain ⟨_, hhp_grow, _, _, hStep0⟩ := hws
    obtain ⟨S1, Nd1, _, _, hog1, hfr1, _⟩ := hStep0 S Nd hIA_entry.2.1 (fun _ hx => by simp at hx)
    have hold_z := worldOwned_zero_aligned hIA_entry.2.1
    have hsi_u := (heap_ivl_survives_step hAs.2 hhp_grow hog1 hfr1 hold_z (fun _ hx => by simp at hx)
      (hIA.2.2.1 _ hsi_mem).2.1 (hIA.2.2.1 _ hsi_mem).2.2.1 (hIA.2.2.1 _ hsi_mem).1
      (fun j hj => hIA.2.2.2.1 _ hsi_mem j hj) (fun _ hx => by simp at hx)).2.2
    have hpl_u := (heap_ivl_survives_step hAs.2 hhp_grow hog1 hfr1 hold_z (fun _ hx => by simp at hx)
      (hIA.2.2.1 _ hpl_mem).2.1 (hIA.2.2.1 _ hpl_mem).2.2.1 (hIA.2.2.1 _ hpl_mem).1
      (fun j hj => hIA.2.2.2.1 _ hpl_mem j hj) (fun _ hx => by simp at hx)).2.2
    have hsi0_eq : memW post w_si.toNat = memW state w_si.toNat :=
      memW_eq_of_ivlUnhit hsi_u (hIA.2.2.1 _ hsi_mem).2.1
        (by have := (hIA.2.2.1 _ hsi_mem).1.2; omega) ⟨le_rfl, by omega⟩
    have hsi32_eq : memW post (w_si.toNat + 32) = memW state (w_si.toNat + 32) :=
      memW_eq_of_ivlUnhit hsi_u (by have := (hIA.2.2.1 _ hsi_mem).2.1; omega)
        (by have := (hIA.2.2.1 _ hsi_mem).1.2; omega) ⟨by omega, by omega⟩
    have hpl32_eq : memW post (memW state w_si.toNat + 32) = memW state (memW state w_si.toNat + 32) :=
      memW_eq_of_ivlUnhit hpl_u (by have := (hIA.2.2.1 _ hpl_mem).2.1; omega)
        (by have := (hIA.2.2.1 _ hpl_mem).1.2; omega) ⟨by omega, by omega⟩
    have hpl40_eq : memW post (memW state w_si.toNat + 40) = memW state (memW state w_si.toNat + 40) :=
      memW_eq_of_ivlUnhit hpl_u (by have := (hIA.2.2.1 _ hpl_mem).2.1; omega)
        (by have := (hIA.2.2.1 _ hpl_mem).1.2; omega) ⟨by omega, by omega⟩
    have hic_eq : inputCells post w_si.toNat = inputCells state w_si.toNat := by
      simp only [inputCells, hsi0_eq, hsi32_eq, hpl32_eq, hpl40_eq]
    rw [hic_eq] at hc
    exact Or.inr (Or.inr (Or.inl (Nat.le_trans (hIA.2.2.1 c hc).1.2 hfb_in.1)))
  refine ⟨w_si, w_rt, S', Nd',
    (inputAtWith_with_locals post _ post.clock S' Nd' w_si.toNat).2 hIA_post,
    by have hne : ofString "root" ≠ ofString "si" := by decide
       simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, hlu_si],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
    hfb.1, ⟨Nat.le_trans hAs.2.1 hfb_in.1, hfb_in.2⟩, hav, hic_disj_rt⟩

theorem hoare_htr_inputReady
    (whtr : WorldKeeps WorldOK
      (fun s => [(locN s "out", 32), (globN s "ssz_len_chunk", if globN s "ssz_len_chunk" = 0 then 0 else 32)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "htr_new_payload_request")) :
    Hoare InputReadyWithRoot
      (.call (some (none, none)) (ofString "htr_new_payload_request")
        [.var .local (ofString "si"), .var .local (ofString "root")])
      (fun r t => r = none → InputReady t) := by
  refine ⟨fun {F} state hcode hIR _ hr => ?_⟩
  rcases hcall : evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "htr_new_payload_request")
        [.var .local (ofString "si"), .var .local (ofString "root")]) with ⟨cres, cpost⟩
  have hr' : cres = none := by rw [hcall] at hr; exact hr
  subst hr'
  obtain ⟨w_si, w_rt, S, Nd, hIA, hlu_si, hlu_rt, hrt8, _, hdisj_rt, hdisj_ic_rt⟩ := hIR
  rw [evaluateHOLFiniteState_call] at hcall
  have hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "si"), .var .local (ofString "root")] =
      some [.val (.word w_si), .val (.word w_rt)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, evalHOLExact, hlu_si, hlu_rt]
  rw [hargs] at hcall; dsimp only at hcall
  rcases hl : lookupCodeHOLFinite state.code.lookup (ofString "htr_new_payload_request")
      [.val (.word w_si), .val (.word w_rt)] with _ | ⟨body, callee, ret⟩
  · rw [hl] at hcall; simp at hcall
  · rw [hl] at hcall; dsimp only at hcall
    split_ifs at hcall with hz
    · simp at hcall
    · rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with ⟨bres, post⟩
      rw [hb] at hcall
      cases bres with
      | none => simp at hcall
      | some br =>
        cases br with
        | returned v =>
          dsimp only at hcall
          split_ifs at hcall with hsh
          · obtain ⟨_, hpost_eq⟩ := Prod.mk.inj hcall
            have hpc := callee_param_two state (ofString "htr_new_payload_request")
              (ofString "si") (ofString "out") .one .one _ _
              (by rw [hcode]; exact lookup_htr_new_payload_request_fn)
              (.var .local (ofString "si")) (.var .local (ofString "root"))
              (.val (.word w_si)) (.val (.word w_rt))
              [.val (.word w_si), .val (.word w_rt)] body callee ret
              (by simpa [evalAt, evalHOLExact] using hlu_si)
              (by simpa [evalAt, evalHOLExact] using hlu_rt) hargs hl
            have hout_loc : locN (callEntryStateHOLFinite state callee) "out" = w_rt.toNat := by
              simp [locN, callEntryStateHOLFinite, hpc.2.2]
            have hW_state : WorldOK state := ⟨hIA.1, S, (worldTyped_iff_with state S).2 ⟨Nd, hIA.2.1⟩⟩
            have hstep := FunSpec.at_lookup whtr state hcode _ body callee ret hl
              (localsFree_worldOK state callee (state.clock - 1) hW_state) (by rw [hb]; simp)
            rw [hb] at hstep; dsimp only at hstep
            have hws := hstep (Or.inl ⟨v, rfl⟩)
            have hIA_entry : InputAtWith (callEntryStateHOLFinite state callee) S Nd w_si.toNat :=
              (inputAtWith_with_locals state callee (state.clock - 1) S Nd w_si.toNat).2 hIA
            obtain ⟨S', Nd', _, hIA_post, _, _, _⟩ :=
              WorldStep.preserves_inputAtWith hIA_entry hws
                (fun j hj => by
                  change j ∈ [(locN (callEntryStateHOLFinite state callee) "out", 32),
                    bufferRegion (callEntryStateHOLFinite state callee) ("ssz_len_chunk", 32)] at hj
                  simp only [hout_loc, List.mem_cons, List.not_mem_nil, or_false] at hj
                  rcases hj with rfl | rfl
                  · intro h0; dsimp at h0; omega
                  · exact bufferRegion_zero_aligned _ "ssz_len_chunk" 32 (by omega))
                (fun j hj k hk => by
                  change j ∈ [(locN (callEntryStateHOLFinite state callee) "out", 32),
                    bufferRegion (callEntryStateHOLFinite state callee) ("ssz_len_chunk", 32)] at hj
                  simp only [hout_loc, List.mem_cons, List.not_mem_nil, or_false] at hj
                  rcases hj with rfl | rfl
                  · exact hdisj_rt (w_rt.toNat, 32) (by simp) k (worldTypedIvls_sub_worldOwned _ _ _ k hk)
                  · exact bufferRegion_disj_le hIA_entry.2.1 ("ssz_len_chunk", 32) (by decide) (by decide) 32 le_rfl k hk)
                (fun i hi j hj => by
                  change j ∈ [(locN (callEntryStateHOLFinite state callee) "out", 32),
                    bufferRegion (callEntryStateHOLFinite state callee) ("ssz_len_chunk", 32)] at hj
                  simp only [hout_loc, List.mem_cons, List.not_mem_nil, or_false] at hj
                  rcases hj with rfl | rfl
                  · exact hdisj_ic_rt i hi (w_rt.toNat, 32) (by simp)
                  · exact inputCells_disj_bufferRegion_le hIA_entry.2.2.2.1 ("ssz_len_chunk", 32) (by decide) 32 le_rfl i hi)
            have hIR_res : InputReady { post with locals := state.locals } := by
              show InputAt { post with locals := state.locals } (locN { post with locals := state.locals } "si")
              have hloc_si : locN { post with locals := state.locals } "si" = w_si.toNat := by
                simp [locN, hlu_si]
              rw [hloc_si]
              exact (inputAt_iff_with _ _).2
                ⟨S', Nd', (inputAtWith_with_locals post state.locals post.clock S' Nd' w_si.toNat).2 hIA_post⟩
            rwa [hpost_eq] at hIR_res
          · simp at hcall
        | _ => simp [emptyLocalsHOLFinite] at hcall

theorem «gbody_main» : GBody.«main» := by
  intro hal hblake hbls hbn hdhi hevm hfork hhdr hhtr hkeccak hmem hmz hmpt houtw hrmd hsecp hser hsha hssz hu256 hvsnp
    wal rtal wblake wbls wbn wdhi wevm wfork whdr whtr wkeccak hmem_world wmz _zvmz wmpt wrmd rosecp wsha wssz wu256
  have hw_blake : KeepsOn WorldOK WorldOK (ofString "blake2_init") := by
    apply wblake.keepsOn_buffers; intro F s i hi
    change i ∈ [bufferRegion s ("b2_iv", 64), bufferRegion s ("b2_sigma", 80)] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨("b2_iv", 64), by decide, by decide, rfl⟩
    · exact ⟨("b2_sigma", 80), by decide, by decide, rfl⟩
  have hw_bls : KeepsOn WorldOK WorldOK (ofString "bls_precompiles_init") := by
    apply wbls.keepsOn_buffers; intro F s i hi
    change i ∈ [bufferRegion s ("bls_c", 7136), bufferRegion s ("bls_discount", 2048)] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨("bls_c", 7136), by decide, by decide, rfl⟩
    · exact ⟨("bls_discount", 2048), by decide, by decide, rfl⟩
  have hw_bn : KeepsOn WorldOK WorldOK (ofString "bn254_init") := by
    apply wbn.keepsOn_buffers; intro F s i hi
    change i ∈ [bufferRegion s ("bn_expw", 352), bufferRegion s ("bn_gamma", 384)] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨("bn_expw", 352), by decide, by decide, rfl⟩
    · exact ⟨("bn_gamma", 384), by decide, by decide, rfl⟩
  have hw_evm : KeepsOn WorldOK WorldOK (ofString "evm_init") := by
    apply wevm.keepsOn_buffers; intro F s i hi
    change i ∈ [bufferRegion s ("evm_empty", 8), bufferRegion s ("keccak_pad", 136),
      bufferRegion s ("keccak_st", 200), bufferRegion s ("null_address", 24),
      bufferRegion s ("transfer_topic", 32), bufferRegion s ("vm_system_address", 24)] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨("evm_empty", 8), by decide, by decide, rfl⟩
    · exact ⟨("keccak_pad", 136), by decide, by decide, rfl⟩
    · exact ⟨("keccak_st", 200), by decide, by decide, rfl⟩
    · exact ⟨("null_address", 24), by decide, by decide, rfl⟩
    · exact ⟨("transfer_topic", 32), by decide, by decide, rfl⟩
    · exact ⟨("vm_system_address", 24), by decide, by decide, rfl⟩
  have hw_fork : KeepsOn WorldOK WorldOK (ofString "fork_init") := by
    apply wfork.keepsOn_buffers; intro F s i hi
    change i ∈ [bufferRegion s ("beacon_roots_address", 24), bufferRegion s ("builder_deposit_address", 24),
      bufferRegion s ("builder_exit_address", 24), bufferRegion s ("consolidation_request_address", 24),
      bufferRegion s ("deposit_contract_address", 24), bufferRegion s ("deposit_event_signature_hash", 32),
      bufferRegion s ("history_storage_address", 24), bufferRegion s ("precompile_addrs", 360),
      bufferRegion s ("withdrawal_request_address", 24), bufferRegion s ("zero32", 32)] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨("beacon_roots_address", 24), by decide, by decide, rfl⟩
    · exact ⟨("builder_deposit_address", 24), by decide, by decide, rfl⟩
    · exact ⟨("builder_exit_address", 24), by decide, by decide, rfl⟩
    · exact ⟨("consolidation_request_address", 24), by decide, by decide, rfl⟩
    · exact ⟨("deposit_contract_address", 24), by decide, by decide, rfl⟩
    · exact ⟨("deposit_event_signature_hash", 32), by decide, by decide, rfl⟩
    · exact ⟨("history_storage_address", 24), by decide, by decide, rfl⟩
    · exact ⟨("precompile_addrs", 360), by decide, by decide, rfl⟩
    · exact ⟨("withdrawal_request_address", 24), by decide, by decide, rfl⟩
    · exact ⟨("zero32", 32), by decide, by decide, rfl⟩
  have hw_hdr : KeepsOn WorldOK WorldOK (ofString "header_init") := by
    apply whdr.keepsOn_buffers; intro F s i hi
    change i ∈ [bufferRegion s ("hdr_zero8", 8)] at hi
    simp only [List.mem_singleton] at hi; subst hi
    exact ⟨("hdr_zero8", 8), by decide, by decide, rfl⟩
  have hw_keccak : KeepsOn WorldOK WorldOK (ofString "keccak_init") := by
    apply wkeccak.keepsOn_buffers; intro F s i hi
    change i ∈ [bufferRegion s ("keccak_rc", 192)] at hi
    simp only [List.mem_singleton] at hi; subst hi
    exact ⟨("keccak_rc", 192), by decide, by decide, rfl⟩
  have hw_mpt : KeepsOn WorldOK WorldOK (ofString "mpt_init") := by
    apply wmpt.keepsOn_buffers; intro F s i hi
    change i ∈ [bufferRegion s ("empty_code_hash", 32), bufferRegion s ("empty_trie_root", 32),
      bufferRegion s ("keccak_pad", 136), bufferRegion s ("keccak_st", 200),
      bufferRegion s ("mpt_hash_scratch", 40)] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · exact ⟨("empty_code_hash", 32), by decide, by decide, rfl⟩
    · exact ⟨("empty_trie_root", 32), by decide, by decide, rfl⟩
    · exact ⟨("keccak_pad", 136), by decide, by decide, rfl⟩
    · exact ⟨("keccak_st", 200), by decide, by decide, rfl⟩
    · exact ⟨("mpt_hash_scratch", 40), by decide, by decide, rfl⟩
  have hw_rmd : KeepsOn WorldOK WorldOK (ofString "ripemd160_init") := by
    apply wrmd.keepsOn_buffers; intro F s i hi
    change i ∈ [bufferRegion s ("rmd_tab", 160)] at hi
    simp only [List.mem_singleton] at hi; subst hi
    exact ⟨("rmd_tab", 160), by decide, by decide, rfl⟩
  have hw_secp : KeepsOn WorldOK WorldOK (ofString "secp256k1_init") :=
    rosecp.keepsOn localsFree_worldOK worldOK_guestInv
  have hw_ssz : KeepsOn WorldOK WorldOK (ofString "ssz_init") := by
    apply wssz.keepsOn_buffers; intro F s i hi
    change i ∈ [bufferRegion s ("zero_hashes", 2048)] at hi
    simp only [List.mem_singleton] at hi; subst hi
    exact ⟨("zero_hashes", 2048), by decide, by decide, rfl⟩
  have hmem_hoare : Hoare MainEntry (.call (some (none, none)) (ofString "mem_init") [])
      (fun r t => r = none → WorldOK t) :=
    Hoare.call0 hmem_world
      (callEntryOn_of_imp (Q := fun s => GuestInv s ∧ GlobalsZero s)
        (fun s locals k ⟨hg, hz⟩ => ⟨guestInv_with_locals_clock s locals k hg, hz⟩)
        (fun _ h => ⟨h.1.1, h.2.2⟩) _ _)
      (fun s _ post v _ _ hq _ => localsFree_worldOK post s.locals post.clock (hq v rfl))
      (fun _ _ hr _ h => absurd h hr)
  have hdhi_hoare : ∀ (handler : ProgHOL 64),
      (∀ {F : Type} (t : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState t handler).1 ≠ none) →
      Hoare WorldOK
        (.call (some (some (.local, ofString "si"), some (ofString "SszErr", ofString "err_code", handler)))
          (ofString "decode_host_input") [])
        (fun r t => r = none →
          ∃ w_si : BitVec 64, t.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
            InputAt t w_si.toNat) := by
    intro handler hh_ne
    exact Hoare.callHandleDest_fall wdhi
      (callEntryOn_of_localsFree localsFree_worldOK _ _) hh_ne
      (fun s callee post v _ hW hstep => by
        obtain ⟨hAs, S, hS⟩ := hW
        obtain ⟨Nd, hWT⟩ := (worldTyped_iff_with s S).1 hS
        have hWT_entry := (worldTypedWith_with_locals s callee (s.clock - 1) S Nd).2 hWT
        have hws := hstep (Or.inl ⟨v, rfl⟩)
        obtain ⟨S', Nd', _, hWT', _, _, hQ⟩ := hws.2.2.2.2 S Nd hWT_entry (fun i hi j hj => by
          change i ∈ [bufferRegion (callEntryStateHOLFinite s callee) ("ssz_offs", 64)] at hi
          simp only [List.mem_singleton] at hi; subst hi
          exact bufferRegion_disj_le hWT_entry ("ssz_offs", 64) (by decide) (by decide) 64 le_rfl j hj)
        obtain ⟨w_si, rfl, hcells, hdisj_ow, hntx63, hPay, hReq⟩ := hQ v rfl
        have hAp := hws.1
        have hIA_post : InputAtWith post S' Nd' w_si.toNat :=
          ⟨hAp, hWT',
           fun i hi => ⟨⟨Nat.le_trans hAs.2.1 (hcells i hi).2.1.1, (hcells i hi).2.1.2⟩, (hcells i hi).2.2⟩,
           hdisj_ow, hntx63, hPay, hReq⟩
        set resSt := setVarHOLFinite (ofString "si") (.val (.word w_si)) { post with locals := s.locals }
        exact ⟨w_si,
          by simp [resSt, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
          (inputAt_iff_with resSt w_si.toNat).2
            ⟨S', Nd', (inputAtWith_with_locals post _ post.clock S' Nd' w_si.toNat).2 hIA_post⟩⟩)
  refine ⟨_, _, _, lookup_main_fn, ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_main,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  apply TerminatingProgBoundedOn.mono_bound
  · exact TerminatingProgBoundedOn.seq_hoare_trans
      (TerminatingProgBoundedOn.call_on hmem _ _ (callEntryOn_of_imp localsFree_guestInv (fun _ h => h.1.1) _ _))
      hmem_hoare
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.call_on hsha _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
        (Hoare.call_keeps localsFree_worldOK wsha.keepsOn _)
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.call_on hkeccak _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
        (Hoare.call_keeps localsFree_worldOK hw_keccak _)
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.call_on hssz _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
        (Hoare.call_keeps localsFree_worldOK hw_ssz _)
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.call_on hmpt _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
        (Hoare.call_keeps localsFree_worldOK hw_mpt _)
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.call_on hu256 _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
        (Hoare.call_keeps localsFree_worldOK wu256.keepsOn _)
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.call_on hsecp _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
        (Hoare.call_keeps localsFree_worldOK hw_secp _)
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.call_on hbn _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
        (Hoare.call_keeps localsFree_worldOK hw_bn _)
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.call_on hbls _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
        (Hoare.call_keeps localsFree_worldOK hw_bls _)
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.call_on hrmd _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
        (Hoare.call_keeps localsFree_worldOK hw_rmd _)
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.call_on hblake _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
        (Hoare.call_keeps localsFree_worldOK hw_blake _)
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.call_on hhdr _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
        (Hoare.call_keeps localsFree_worldOK hw_hdr _)
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.call_on hevm _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
        (Hoare.call_keeps localsFree_worldOK hw_evm _)
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.call_on hfork _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
        (Hoare.call_keeps localsFree_worldOK hw_fork _)
      (TerminatingProgBoundedOn.decCall_on hal _ _ _
        (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _)
        (KeepsOn.resumeOn localsFree_worldOK wal.keepsOn _ _)
        (TerminatingProgBoundedOn.decCall_on hal _ _ _
          (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _)
          (resumeOn_alloc_worldWithBuf "z32" 32 (by decide) (by decide) wal rtal)
          (TerminatingProgBoundedOn.seq_hoare_trans
            (TerminatingProgBoundedOn.call_on hmz _ _
              (callEntryOn_of_imp localsFree_guestInv worldWithBuf_guestInv _ _))
            (hoare_memzero_worldWithBuf "z32" 32 (by decide) wmz)
            (TerminatingProgBoundedOn.dec_on localsFree_worldOK _ _ _
              (TerminatingProgBoundedOn.dec_on localsFree_worldOK _ _ _
                (TerminatingProgBoundedOn.seq_hoare_trans
                  (TerminatingProgBoundedOn.callHandle_on hdhi worldOK_guestInv _ _ _
                    (TerminatingProgBoundedOn.decCall_guestInv hser _ _ _
                      (TerminatingProgBoundedOn.seq_guestInv
                        (TerminatingProgBoundedOn.of_clock (fun s => clock_storeByte s _ _))
                        (TerminatingProgBoundedOn.seq_guestInv
                          (TerminatingProgBoundedOn.call_guestInv houtw _ _)
                          (TerminatingProgBoundedOn.seq_guestInv
                            (straight_guestInv _ rfl)
                            (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _))))))
                    _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
                  (hdhi_hoare _ (fun t => decCall_ne_none_of_cont t _ _ _ _ _
                    (fun u => seq3_return_ne_none u _ _ _ _)))
                  (TerminatingProgBoundedOn.decCall_on hal _ _ _
                    (callEntryOn_of_imp (P := fun s => ∃ w_si : BitVec 64,
                        s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧ InputAt s w_si.toNat)
                      localsFree_guestInv
                      (fun _ ⟨_, _, hIA⟩ => hIA.1.1) _ _)
                    (resumeOn_alloc32_inputReady wal rtal)
                    (TerminatingProgBoundedOn.seq_hoare_trans
                      (TerminatingProgBoundedOn.call_on hhtr _ _
                        (callEntryOn_of_imp localsFree_guestInv inputReadyWithRoot_guestInv _ _))
                      (hoare_htr_inputReady whtr)
                      (TerminatingProgBoundedOn.decCall_on hvsnp _ _ _
                        (callEntryOn_inputReady lookup_verify_stateless_new_payload_fn
                          (by simp only [sourceFunctionEntry, Guest.Software.guestFn_verify_stateless_new_payload,
                            InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
                            InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
                            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
                            InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
                            InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
                            InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
                            Option.map_none, Option.map_some, List.map_cons, List.map_nil,
                            InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural]))
                        (decCallResumeOn_guestInv inputReady_guestInv _ _ _)
                        (TerminatingProgBoundedOn.decCall_guestInv hser _ _ _
                          (TerminatingProgBoundedOn.seq_guestInv
                            (TerminatingProgBoundedOn.of_clock (fun s => clock_storeByte s _ _))
                            (TerminatingProgBoundedOn.seq_guestInv
                              (TerminatingProgBoundedOn.call_guestInv houtw _ _)
                              (TerminatingProgBoundedOn.seq_guestInv
                                (straight_guestInv _ rfl)
                                (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _))))))))))))))))))))))))))))
  · unfold K.«main»; omega


end InitECandidate.Solver.Wave8GuestInv.R16Shards
