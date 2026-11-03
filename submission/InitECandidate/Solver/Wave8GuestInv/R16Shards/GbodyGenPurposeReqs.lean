import InitECandidate.Solver.Wave8GuestInv.R16Shards.GbodyC17ToC21Common
import InitECandidate.Solver.Wave8GuestInv.ContractParts.C17

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000
set_option exponentiation.threshold 2000

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

/-! ## 6. Proof 2: `gbody_process_general_purpose_requests` -/

theorem lookup_requests_append_fn :
    originalRuntimeCode.lookup (ofString "requests_append") =
      some ((sourceFunctionEntry Guest.Software.guestFn_requests_append).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 876 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_requests_append) rfl

def ReqState (c : Nat) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧ globN s "bo" ≠ 0 ∧ memW s (globN s "bo" + 64) ≤ c

theorem localsFree_reqState (c : Nat) : LocalsFree (ReqState c) := by
  intro F s locals k ⟨hW, hbo, hc⟩
  exact ⟨localsFree_worldOK s locals k hW, hbo, hc⟩

theorem reqState_mono {c1 c2 : Nat} (hle : c1 ≤ c2) {F : Type}
    {s : PanSemStateFiniteExact 64 F} (h : ReqState c1 s) : ReqState c2 s :=
  ⟨h.1, h.2.1, Nat.le_trans h.2.2 hle⟩

theorem reqState_reqRoom {c : Nat} (hc : c < 8) {F : Type}
    {s : PanSemStateFiniteExact 64 F} (h : ReqState c s) : ReqRoom s :=
  ⟨h.1, lt_of_le_of_lt h.2.2 hc⟩

theorem reqState_worldOK {c : Nat} {F : Type}
    {s : PanSemStateFiniteExact 64 F} (h : ReqState c s) : WorldOK s := h.1

theorem reqState_guestInv {c : Nat} {F : Type}
    {s : PanSemStateFiniteExact 64 F} (h : ReqState c s) : GuestInv s := h.1.1.1

def DepLoopInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_dep w_n w_cap : BitVec 64, ∃ S Nd : List Nat,
    WorldTypedWith s S Nd ∧
    ArenaReady s ∧
    globN s "bo" ≠ 0 ∧
    memW s (globN s "bo" + 64) = 0 ∧
    s.locals.lookup (ofString "dep") = some (.val (.word w_dep)) ∧
    s.locals.lookup (ofString "dep_n") = some (.val (.word w_n)) ∧
    s.locals.lookup (ofString "dep_cap") = some (.val (.word w_cap)) ∧
    w_n.toNat ≤ w_cap.toNat ∧
    w_dep.toNat % 8 = 0 ∧
    w_n.toNat % 8 = 0 ∧
    w_cap.toNat % 8 = 0 ∧
    Inside (w_dep.toNat, w_cap.toNat) sourceBase (globN s "heap_ptr") ∧
    IvlsDisj [(w_dep.toNat, w_cap.toNat)] (worldOwned s S Nd)

theorem depLoopInv_reqState0 {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : DepLoopInv s) : ReqState 0 s := by
  obtain ⟨_, _, _, S, Nd, hW, hA, hbo, hc0, _⟩ := h
  exact ⟨⟨hA, S, (worldTyped_iff_with s S).2 ⟨Nd, hW⟩⟩, hbo, by omega⟩

theorem depLoopInv_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : DepLoopInv s) : GuestInv s :=
  (depLoopInv_reqState0 h).1.1.1

theorem localsOnly_depLoopInv : LocalsOnly ["dep", "dep_n", "dep_cap"] DepLoopInv := by
  intro F s locals k hl h
  obtain ⟨w_dep, w_n, w_cap, S, Nd, hW, hA, hbo, hc0, hlu_d, hlu_n, hlu_c, hle, hd8, hn8, hc8, hin, hdisj⟩ := h
  refine ⟨w_dep, w_n, w_cap, S, Nd,
    (worldTypedWith_with_locals s locals k S Nd).2 hW,
    localsFree_arenaReady s locals k hA,
    hbo, hc0,
    (hl "dep" (by simp)).trans hlu_d,
    (hl "dep_n" (by simp)).trans hlu_n,
    (hl "dep_cap" (by simp)).trans hlu_c,
    hle, hd8, hn8, hc8, hin, hdisj⟩

theorem evalAt_load_one_ordinary {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hg : GuestInv s) {addr : ExpHOL 64} {v : ValueHOL 64}
    (hev : evalAt s (.load .one addr) = some v) :
    ∃ a w : BitVec 64, evalAt s addr = some (.val (.word a)) ∧
      v = .val (.word w) ∧ a.toNat % 8 = 0 ∧ sourceBase ≤ a.toNat ∧ a.toNat < heapEnd := by
  simp only [evalAt, evalHOLExact] at hev
  rcases ha : @evalHOLExact 64 F _ s.toExact (fun address => Classical.propDecidable (s.memaddrs address)) addr with _ | va
  · rw [ha] at hev; simp at hev
  · rw [ha] at hev
    cases va with
    | val wl =>
      cases wl with
      | word a =>
        simp only [memLoadHOLExact] at hev
        split_ifs at hev with _ hdom
        simp only [Option.some.injEq] at hev
        rw [hg.memaddrs, ordinaryDomain_iff] at hdom
        cases hmem : s.memory a with
        | word w =>
          rw [hmem] at hev
          exact ⟨a, w, ha, hev.symm, hdom.1, hdom.2.1, hdom.2.2⟩
    | rStruct _ => simp at hev
    | nStruct _ => simp at hev

theorem evalAt_add_panMul8 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {base idx : MlS} {v : ValueHOL 64}
    (hev : evalAt s (.op .add [.var .local base, .panop .mul [.var .local idx, .const 8#64]]) = some v) :
    ∃ wb wi : BitVec 64,
      s.locals.lookup base = some (.val (.word wb)) ∧
      s.locals.lookup idx = some (.val (.word wi)) ∧
      v = .val (.word (wb + wi * 8#64)) := by
  simp only [evalAt, evalHOLExact, evalListHOLExact] at hev
  rcases hb : s.locals.lookup base with _ | vb
  · simp [hb] at hev
  · rcases hi : s.locals.lookup idx with _ | vi
    · simp [hb, hi] at hev
    · cases vi with
      | rStruct _ => simp [hb, hi, valueIsWord] at hev
      | nStruct _ => simp [hb, hi, valueIsWord] at hev
      | val wli =>
        cases wli with
        | word wi =>
          cases vb with
          | rStruct _ => simp [hb, hi, valueIsWord, panOpHOL] at hev
          | nStruct _ => simp [hb, hi, valueIsWord, panOpHOL] at hev
          | val wlb =>
            cases wlb with
            | word wb =>
              simp only [hb, hi, valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp,
                List.all, List.map, Option.map, Bool.and_self, if_true, Option.some.injEq] at hev
              refine ⟨wb, wi, rfl, rfl, ?_⟩
              rw [← hev]
              congr 2
              simp [BitVec.add_zero]

def walkRank (baseName idxName : String) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  min (heapEnd - (BitVec.ofNat 64 (locN s baseName) + BitVec.ofNat 64 (locN s idxName) * 8#64).toNat)
    31104957944

theorem walkRank_le (baseName idxName : String) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    walkRank baseName idxName s ≤ 31104957944 :=
  Nat.min_le_right _ _

theorem walkRank_step_lt {baseName idxName : String} {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {wb wi : BitVec 64}
    (hb_s : s.locals.lookup (ofString baseName) = some (.val (.word wb)))
    (hi_s : s.locals.lookup (ofString idxName) = some (.val (.word wi)))
    (hb_p : post.locals.lookup (ofString baseName) = some (.val (.word wb)))
    (hi_p : post.locals.lookup (ofString idxName) = some (.val (.word (wi + 1#64))))
    (hlo : sourceBase ≤ (wb + wi * 8#64).toNat)
    (hhi : (wb + wi * 8#64).toNat < heapEnd) :
    walkRank baseName idxName post < walkRank baseName idxName s := by
  unfold walkRank
  have hloc_bs : BitVec.ofNat 64 (locN s baseName) = wb := by simp [locN, hb_s]
  have hloc_is : BitVec.ofNat 64 (locN s idxName) = wi := by simp [locN, hi_s]
  have hloc_bp : BitVec.ofNat 64 (locN post baseName) = wb := by simp [locN, hb_p]
  have hloc_ip : BitVec.ofNat 64 (locN post idxName) = wi + 1#64 := by
    simp only [locN, hi_p, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [hloc_bs, hloc_is, hloc_bp, hloc_ip]
  have hdom_le : heapEnd - (wb + wi * 8#64).toNat ≤ 31104957944 := by
    have hsb : sourceBase = 2701131776 := by decide
    have hhe : heapEnd = 33806089704 := by decide
    omega
  have hadd8 : wb + (wi + 1#64) * 8#64 = (wb + wi * 8#64) + 8#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
    omega
  rw [hadd8]
  have h264 : heapEnd + 8 < 2 ^ 64 := by decide
  have htonat : ((wb + wi * 8#64) + 8#64).toNat = (wb + wi * 8#64).toNat + 8 := by
    rw [BitVec.toNat_add]
    change ((wb + wi * 8#64).toNat + 8) % 2 ^ 64 = (wb + wi * 8#64).toNat + 8
    exact Nat.mod_eq_of_lt (by omega)
  rw [htonat]
  omega

theorem dec_rls_reqsFresh_to_reqState0 :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      ReqsFresh s →
      evalAt s (.load .one (.op .add [.var .global (ofString "bo"), .const 72#64])) = some v →
      ReqState 0 (setVarHOLFinite (ofString "rls") v s) := by
  intro F s v ⟨hW, hc0⟩ hev
  obtain ⟨a, _, ha, _, _, hlo, _⟩ := evalAt_load_one_ordinary hW.1.1 hev
  have hbo_nz : globN s "bo" ≠ 0 := by
    intro hbo0
    simp only [evalAt, evalHOLExact, evalListHOLExact] at ha
    rcases hg : s.globals.lookup (ofString "bo") with _ | vb
    · simp [hg] at ha
    · cases vb with
      | rStruct _ => simp [hg, valueIsWord] at ha
      | nStruct _ => simp [hg, valueIsWord] at ha
      | val wlb =>
        cases wlb with
        | word wbo =>
          have hwbo0 : wbo.toNat = 0 := by simp [globN, hg] at hbo0; exact hbo0
          have hwbo_eq : wbo = 0#64 := BitVec.eq_of_toNat_eq hwbo0
          subst hwbo_eq
          simp only [hg, valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map,
            Option.map, Bool.and_self, if_true, Option.some.injEq, ValueHOL.val.injEq,
            HolWordLab.word.injEq] at ha
          have ha72 : a.toNat = 72 := by rw [← ha]; decide
          have hsb : sourceBase = 2701131776 := by decide
          omega
  exact localsFree_reqState 0 s _ s.clock ⟨hW, hbo_nz, by omega⟩

theorem resumeOn_init_dep_alloc
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc")) :
    DecCallResumeOn (ReqState 0)
      (fun s => ∃ w_dep : BitVec 64, ∃ S Nd : List Nat,
        WorldTypedWith s S Nd ∧ ArenaReady s ∧ globN s "bo" ≠ 0 ∧ memW s (globN s "bo" + 64) = 0 ∧
        s.locals.lookup (ofString "dep") = some (.val (.word w_dep)) ∧
        w_dep.toNat % 8 = 0 ∧
        Inside (w_dep.toNat, 8) sourceBase (globN s "heap_ptr") ∧
        IvlsDisj [(w_dep.toNat, 8)] (worldOwned s S Nd))
      (ofString "dep") (ofString "alloc") [.const 8#64] := by
  intro F state values body callee ret value post hcode ⟨hW, hbo_nz, hc0⟩ hargs hl hrun
  obtain ⟨hAs, S, hS⟩ := hW
  obtain ⟨Nd, hWT⟩ := (worldTyped_iff_with state S).1 hS
  have hpc := callee_param_one_exp state (ofString "alloc") (ofString "n") .one _ _
    (by rw [hcode]; exact lookup_alloc_fn) (.const 8#64) (.val (.word 8#64)) values body callee ret rfl hargs hl
  have hn_loc : locN (callEntryStateHOLFinite state callee) "n" = 8 := by
    simp [locN, callEntryStateHOLFinite, hpc.2]
  have hstep := FunSpec.at_lookup wal state hcode values body callee ret hl
    (localsFree_worldOK state callee (state.clock - 1) ⟨hAs, S, hS⟩) (by rw [hrun]; simp)
  rw [hrun] at hstep; dsimp only at hstep
  obtain ⟨hAp, _, hG, hRK, hWS⟩ := hstep (Or.inl ⟨value, rfl⟩)
  have hrt := FunSpec.at_lookup rtal state hcode values body callee ret hl
    (localsFree_arenaReady state callee (state.clock - 1) hAs) (by rw [hrun]; simp)
  rw [hrun] at hrt; dsimp only at hrt
  obtain ⟨w_dep, rfl, _, _, hfb⟩ := hrt value rfl
  rw [hn_loc] at hfb
  obtain ⟨S', Nd', _, hWT', _, _, hQ⟩ :=
    hWS S Nd ((worldTypedWith_with_locals _ _ _ _ _).2 hWT) (fun x hx => by simp at hx)
  obtain ⟨w_dep', hw_eq, hav⟩ := hQ (.val (.word w_dep)) rfl
  injection hw_eq with hw_eq'; injection hw_eq' with hw_eq''; subst hw_eq''
  dsimp only at hav
  rw [hn_loc] at hav
  have hbo_eq : globN post "bo" = globN state "bo" := by
    unfold globN; rw [← hG (ofString "bo") (by simp; decide)]; rfl
  have hc64_eq : memW post (globN state "bo" + 64) = memW state (globN state "bo" + 64) :=
    hRK ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp) hbo_nz 64 (by simp)
      (fun i hi => by simp at hi)
  set resumed := setVarHOLFinite (ofString "dep") (.val (.word w_dep)) { post with locals := state.locals }
  refine ⟨w_dep, S', Nd', (worldTypedWith_with_locals post _ post.clock S' Nd').2 hWT',
    localsFree_arenaReady post _ post.clock hAp, ?_, ?_, ?_, hfb.1,
    ⟨Nat.le_trans hAs.2.1 hfb.2.1.1, hfb.2.1.2⟩, hav⟩
  · show globN post "bo" ≠ 0; rw [hbo_eq]; exact hbo_nz
  · show memW post (globN post "bo" + 64) = 0; rw [hbo_eq, hc64_eq]; omega
  · simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

def DepReallocMid : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_nd w_dep w_n w_cap : BitVec 64, ∃ S Nd : List Nat,
    WorldTypedWith s S Nd ∧
    ArenaReady s ∧
    globN s "bo" ≠ 0 ∧
    memW s (globN s "bo" + 64) = 0 ∧
    s.locals.lookup (ofString "nd") = some (.val (.word w_nd)) ∧
    s.locals.lookup (ofString "dep") = some (.val (.word w_dep)) ∧
    s.locals.lookup (ofString "dep_n") = some (.val (.word w_n)) ∧
    s.locals.lookup (ofString "dep_cap") = some (.val (.word w_cap)) ∧
    w_n.toNat + 192 ≤ (w_cap * 2#64 + 1024#64).toNat ∧
    w_nd.toNat % 8 = 0 ∧
    w_n.toNat % 8 = 0 ∧
    (w_cap * 2#64 + 1024#64).toNat % 8 = 0 ∧
    Inside (w_nd.toNat, (w_cap * 2#64 + 1024#64).toNat) sourceBase (globN s "heap_ptr") ∧
    IvlsDisj [(w_nd.toNat, (w_cap * 2#64 + 1024#64).toNat)] (worldOwned s S Nd)

theorem depReallocMid_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : DepReallocMid s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, hA, _⟩ := h
  exact hA.1

theorem resumeOn_realloc_dep
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc")) :
    DecCallResumeOn
      (fun s => DepLoopInv s ∧
        CondTrue (.cmp .lower (.var .local (ofString "dep_cap"))
          (.op .add [.var .local (ofString "dep_n"), .const 192#64])) s)
      DepReallocMid
      (ofString "nd") (ofString "alloc")
      [.op .add [.panop .mul [.var .local (ofString "dep_cap"), .const 2#64], .const 1024#64]] := by
  intro F state values body callee ret value post hcode ⟨hInv, _⟩ hargs hl hrun
  have hW_state : WorldOK state := (depLoopInv_reqState0 hInv).1
  obtain ⟨w_dep, w_n, w_cap, S, Nd, hWT, hAs, hbo_nz, hc0, hlu_d, hlu_n, hlu_c, hle_nc, _, hn8, hc8, hin_old, _⟩ := hInv
  have hcap_bound : w_cap.toNat ≤ heapEnd - sourceBase := by
    have hhp_lim : globN state "heap_ptr" ≤ heapLimit := hAs.2.2.1
    have hlim_le : heapLimit ≤ heapEnd := by decide
    unfold Inside at hin_old
    omega
  have hdom_val : heapEnd - sourceBase = 31104957928 := by decide
  have hnew_cap_val : (w_cap * 2#64 + 1024#64).toNat = w_cap.toNat * 2 + 1024 := by
    have h264 : (31104957928 : Nat) * 2 + 1024 < 2 ^ 64 := by decide
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hround_eq : ((w_cap * 2#64 + 1024#64).toNat + 7) / 8 * 8 = (w_cap * 2#64 + 1024#64).toNat := by
    omega
  have harg_ev : evalAt state
      (.op .add [.panop .mul [.var .local (ofString "dep_cap"), .const 2#64], .const 1024#64]) =
      some (.val (.word (w_cap * 2#64 + 1024#64))) := by
    simp only [evalAt, evalHOLExact, evalListHOLExact, hlu_c, valueIsWord, valueWord, panOpHOL,
      wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, if_true, Option.some.injEq]
    simp [BitVec.add_zero]
  have hpc := callee_param_one_exp state (ofString "alloc") (ofString "n") .one _ _
    (by rw [hcode]; exact lookup_alloc_fn) _ (.val (.word (w_cap * 2#64 + 1024#64))) values body callee ret
    harg_ev hargs hl
  have hn_loc : locN (callEntryStateHOLFinite state callee) "n" = (w_cap * 2#64 + 1024#64).toNat := by
    simp [locN, callEntryStateHOLFinite, hpc.2]
  have hstep := FunSpec.at_lookup wal state hcode values body callee ret hl
    (localsFree_worldOK state callee (state.clock - 1) hW_state) (by rw [hrun]; simp)
  rw [hrun] at hstep; dsimp only at hstep
  obtain ⟨hAp, _, hG, hRK, hWS⟩ := hstep (Or.inl ⟨value, rfl⟩)
  have hrt := FunSpec.at_lookup rtal state hcode values body callee ret hl
    (localsFree_arenaReady state callee (state.clock - 1) hAs) (by rw [hrun]; simp)
  rw [hrun] at hrt; dsimp only at hrt
  obtain ⟨w_nd, rfl, _, _, hfb⟩ := hrt value rfl
  rw [hn_loc] at hfb
  have hfb_in : Inside (w_nd.toNat, (w_cap * 2#64 + 1024#64).toNat)
      (globN (callEntryStateHOLFinite state callee) "heap_ptr") (globN post "heap_ptr") := by
    have := hfb.2.1; rw [hround_eq] at this; exact this
  obtain ⟨S', Nd', _, hWT', _, _, hQ⟩ :=
    hWS S Nd ((worldTypedWith_with_locals _ _ _ _ _).2 hWT) (fun x hx => by simp at hx)
  obtain ⟨w_nd', hw_eq, hav⟩ := hQ (.val (.word w_nd)) rfl
  injection hw_eq with hw_eq'; injection hw_eq' with hw_eq''; subst hw_eq''
  dsimp only at hav
  rw [hn_loc, hround_eq] at hav
  have hbo_eq : globN post "bo" = globN state "bo" := by
    unfold globN; rw [← hG (ofString "bo") (by simp; decide)]; rfl
  have hc64_eq : memW post (globN state "bo" + 64) = memW state (globN state "bo" + 64) :=
    hRK ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp) hbo_nz 64 (by simp)
      (fun i hi => by simp at hi)
  set resumed := setVarHOLFinite (ofString "nd") (.val (.word w_nd)) { post with locals := state.locals }
  refine ⟨w_nd, w_dep, w_n, w_cap, S', Nd',
    (worldTypedWith_with_locals post _ post.clock S' Nd').2 hWT',
    localsFree_arenaReady post _ post.clock hAp,
    by show globN post "bo" ≠ 0; rw [hbo_eq]; exact hbo_nz,
    by show memW post (globN post "bo" + 64) = 0; rw [hbo_eq, hc64_eq]; omega,
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
    by have hne : ofString "nd" ≠ ofString "dep" := by decide
       simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, hlu_d],
    by have hne : ofString "nd" ≠ ofString "dep_n" := by decide
       simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, hlu_n],
    by have hne : ofString "nd" ≠ ofString "dep_cap" := by decide
       simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, hlu_c],
    by omega, hfb.1, hn8, by omega,
    ⟨Nat.le_trans hAs.2.1 hfb_in.1, hfb_in.2⟩, hav⟩

def DepWriteReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_dep w_n w_cap : BitVec 64, ∃ S Nd : List Nat,
    WorldTypedWith s S Nd ∧
    ArenaReady s ∧
    globN s "bo" ≠ 0 ∧
    memW s (globN s "bo" + 64) = 0 ∧
    s.locals.lookup (ofString "dep") = some (.val (.word w_dep)) ∧
    s.locals.lookup (ofString "dep_n") = some (.val (.word w_n)) ∧
    s.locals.lookup (ofString "dep_cap") = some (.val (.word w_cap)) ∧
    w_n.toNat + 192 ≤ w_cap.toNat ∧
    w_dep.toNat % 8 = 0 ∧
    w_n.toNat % 8 = 0 ∧
    w_cap.toNat % 8 = 0 ∧
    Inside (w_dep.toNat, w_cap.toNat) sourceBase (globN s "heap_ptr") ∧
    IvlsDisj [(w_dep.toNat, w_cap.toNat)] (worldOwned s S Nd)

theorem depWriteReady_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : DepWriteReady s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, hA, _⟩ := h
  exact hA.1

theorem hoare_memcpy_dep_realloc
    (wmc : WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")]) []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "memcpy")) :
    Hoare DepReallocMid
      (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "nd"), .var .local (ofString "dep"), .var .local (ofString "dep_n")])
        (.seq
          (.assign .local (ofString "dep") (.var .local (ofString "nd")))
          (.assign .local (ofString "dep_cap")
            (.op .add [.panop .mul [.var .local (ofString "dep_cap"), .const 2#64], .const 1024#64]))))
      (fun r t => r = none → DepWriteReady t) := by
  apply Hoare.seq_fall (R := DepReallocMid)
  · refine ⟨fun {F} state hcode hMid _ hr => ?_⟩
    rcases hcall : evaluateHOLFiniteState state
        (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "nd"), .var .local (ofString "dep"), .var .local (ofString "dep_n")]) with ⟨cres, cpost⟩
    have hr' : cres = none := by rw [hcall] at hr; exact hr
    subst hr'
    obtain ⟨w_nd, w_dep, w_n, w_cap, S, Nd, hWT, hAs, hbo_nz, hc0,
      hlu_nd, hlu_d, hlu_n, hlu_c, hle_192, hnd8, hn8, hncap8, hin_nd, hdisj_nd⟩ := hMid
    rw [evaluateHOLFiniteState_call] at hcall
    have hargs : evalListHOLFinite state
        (h := fun a => Classical.propDecidable (state.memaddrs a))
        [.var .local (ofString "nd"), .var .local (ofString "dep"), .var .local (ofString "dep_n")] =
        some [.val (.word w_nd), .val (.word w_dep), .val (.word w_n)] := by
      rw [evalListHOLFinite_eq_toExact]
      simp [evalListHOLExact, evalHOLExact, hlu_nd, hlu_d, hlu_n]
    rw [hargs] at hcall; dsimp only at hcall
    rcases hl : lookupCodeHOLFinite state.code.lookup (ofString "memcpy")
        [.val (.word w_nd), .val (.word w_dep), .val (.word w_n)] with _ | ⟨body, callee, ret⟩
    · rw [hl] at hcall; simp at hcall
    · rw [hl] at hcall; dsimp only at hcall
      by_cases hz : state.clock = 0
      · rw [if_pos hz] at hcall; simp at hcall
      · rw [if_neg hz] at hcall
        have hp3 := callee_param_three state (ofString "memcpy")
          (ofString "dst") (ofString "src") (ofString "n") .one .one .one _ _
          (by rw [hcode]; exact lookup_memcpy_fn)
          (.var .local (ofString "nd")) (.var .local (ofString "dep")) (.var .local (ofString "dep_n"))
          (.val (.word w_nd)) (.val (.word w_dep)) (.val (.word w_n))
          [.val (.word w_nd), .val (.word w_dep), .val (.word w_n)] body callee ret
          (by simp [evalAt, evalHOLExact, hlu_nd])
          (by simp [evalAt, evalHOLExact, hlu_d])
          (by simp [evalAt, evalHOLExact, hlu_n]) hargs hl
        have hdst : locN (callEntryStateHOLFinite state callee) "dst" = w_nd.toNat := by
          simp [locN, callEntryStateHOLFinite, hp3.1]
        have hn_loc : locN (callEntryStateHOLFinite state callee) "n" = w_n.toNat := by
          simp [locN, callEntryStateHOLFinite, hp3.2.2]
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with ⟨bres, post⟩
        rw [hrun] at hcall
        cases bres with
        | none => simp at hcall
        | some br =>
          cases br with
          | returned v =>
            dsimp only at hcall
            by_cases hsh : shapeEqHOL (shapeOfHOLExact v) ret = true
            · rw [if_pos hsh] at hcall
              obtain ⟨_, rfl⟩ := Prod.mk.inj hcall
              have hW_state : WorldOK state := ⟨hAs, S, (worldTyped_iff_with state S).2 ⟨Nd, hWT⟩⟩
              have hstep := FunSpec.at_lookup wmc state hcode _ body callee ret hl
                (localsFree_worldOK state callee (state.clock - 1) hW_state) (by rw [hrun]; simp)
              rw [hrun] at hstep; dsimp only at hstep
              obtain ⟨hAp, hhp, hG, hRK, hWS⟩ := hstep (Or.inl ⟨v, rfl⟩)
              have hin_sub : Inside (w_nd.toNat, w_n.toNat) w_nd.toNat (w_nd.toNat + (w_cap * 2#64 + 1024#64).toNat) :=
                ⟨le_rfl, by omega⟩
              have hdisj_R : IvlsDisj [(w_nd.toNat, w_n.toNat)] (worldTypedIvls state S Nd) := by
                intro x hx j hj
                simp only [List.mem_singleton] at hx; subst hx
                exact disj_of_inside_left (i' := (w_nd.toNat, (w_cap * 2#64 + 1024#64).toNat)) hin_sub
                  (hdisj_nd _ (by simp) j (worldTypedIvls_sub_worldOwned _ _ _ j hj))
              obtain ⟨S', Nd', _, hWT', hog, hfr, _⟩ :=
                hWS S Nd ((worldTypedWith_with_locals _ _ _ _ _).2 hWT)
                  (by dsimp only; rw [hdst, hn_loc]; exact hdisj_R)
              dsimp only at hog hfr
              rw [hdst, hn_loc] at hfr
              -- Show `(w_nd, new_cap)` is still disjoint from `worldOwned post S' Nd'` via `OwnedGrows`
              have hdisj_nd' : IvlsDisj [(w_nd.toNat, (w_cap * 2#64 + 1024#64).toNat)] (worldOwned post S' Nd') := by
                intro x hx o ho
                simp only [List.mem_singleton] at hx; subst hx
                rcases hog o ho with rfl | ⟨j, hj, hin_oj⟩ | hfresh
                · exact disj_zero_right _
                · exact disj_of_inside_right hin_oj (hdisj_nd _ (by simp) j hj)
                · exact Or.inr (Or.inr (Or.inl (Nat.le_trans hin_nd.2 hfresh.1)))
              have hbo_eq : globN post "bo" = globN state "bo" := by
                unfold globN; rw [← hG (ofString "bo") (by simp)]; rfl
              have hbo_rec : (globN state "bo", 88) ∈ worldOwned state S Nd := by
                have hr_in : ("bo", 88) ∈ typedRecords := by decide
                have hfix := typedRecord_mem_fixedObjects state hr_in
                rw [if_neg hbo_nz] at hfix
                unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))
              have hbo8 : (globN state "bo") % 8 = 0 := by
                rcases worldOwned_zero_or_allocated hWT _ hbo_rec with h0 | ⟨_, _⟩
                · injection h0 with h0'; exact absurd h0' hbo_nz
                · have hfix := typedRecord_mem_fixedObjects state (show ("bo", 88) ∈ typedRecords by decide)
                  rw [if_neg hbo_nz] at hfix
                  rcases hWT.2.2.1.1 _ hfix with hz | ⟨_, hw⟩
                  · dsimp at hz; omega
                  · exact hw.1
              have hc64_eq : memW post (globN state "bo" + 64) = memW state (globN state "bo" + 64) := by
                apply hRK ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp) hbo_nz 64 (by simp)
                intro i hi
                dsimp only at hi ⊢; rw [hdst, hn_loc] at hi
                change ¬ CellHits (globN state "bo" + 64) i
                simp only [List.mem_singleton] at hi; subst hi
                have hd_bo : Disj (w_nd.toNat, w_n.toNat) (globN state "bo", 88) :=
                  disj_of_inside_left (i' := (w_nd.toNat, (w_cap * 2#64 + 1024#64).toNat)) hin_sub
                    (hdisj_nd _ (by simp) _ hbo_rec)
                exact fun hch => not_cellHits_of_disj hnd8 hn8 (by omega) (by omega) hch hd_bo ⟨by omega, by omega⟩
              exact ⟨w_nd, w_dep, w_n, w_cap, S', Nd',
                (worldTypedWith_with_locals post _ post.clock S' Nd').2 hWT',
                localsFree_arenaReady post _ post.clock hAp,
                by show globN post "bo" ≠ 0; rw [hbo_eq]; exact hbo_nz,
                by show memW post (globN post "bo" + 64) = 0; rw [hbo_eq, hc64_eq]; omega,
                hlu_nd, hlu_d, hlu_n, hlu_c, hle_192, hnd8, hn8, hncap8,
                ⟨hin_nd.1, Nat.le_trans hin_nd.2 hhp⟩, hdisj_nd'⟩
            · rw [if_neg hsh] at hcall; simp at hcall
          | _ => simp at hcall
  · apply Hoare.seq_fall (R := fun s => ∃ w_nd w_n w_cap : BitVec 64, ∃ S Nd : List Nat,
        WorldTypedWith s S Nd ∧ ArenaReady s ∧ globN s "bo" ≠ 0 ∧ memW s (globN s "bo" + 64) = 0 ∧
        s.locals.lookup (ofString "dep") = some (.val (.word w_nd)) ∧
        s.locals.lookup (ofString "dep_n") = some (.val (.word w_n)) ∧
        s.locals.lookup (ofString "dep_cap") = some (.val (.word w_cap)) ∧
        w_n.toNat + 192 ≤ (w_cap * 2#64 + 1024#64).toNat ∧
        w_nd.toNat % 8 = 0 ∧ w_n.toNat % 8 = 0 ∧ (w_cap * 2#64 + 1024#64).toNat % 8 = 0 ∧
        Inside (w_nd.toNat, (w_cap * 2#64 + 1024#64).toNat) sourceBase (globN s "heap_ptr") ∧
        IvlsDisj [(w_nd.toNat, (w_cap * 2#64 + 1024#64).toNat)] (worldOwned s S Nd))
    · apply Hoare.assign_fall
      intro F s v hMid hv
      obtain ⟨w_nd, w_dep, w_n, w_cap, S, Nd, hWT, hAs, hbo_nz, hc0,
        hlu_nd, _, hlu_n, hlu_c, hle_192, hnd8, hn8, hncap8, hin_nd, hdisj_nd⟩ := hMid
      simp only [evalAt, evalHOLExact, hlu_nd, Option.some.injEq] at hv
      subst hv
      refine ⟨w_nd, w_n, w_cap, S, Nd,
        (worldTypedWith_with_locals s _ s.clock S Nd).2 hWT,
        localsFree_arenaReady s _ s.clock hAs, hbo_nz, hc0,
        by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
        by have hne : ofString "dep" ≠ ofString "dep_n" := by decide
           simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, hlu_n],
        by have hne : ofString "dep" ≠ ofString "dep_cap" := by decide
           simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, hlu_c],
        hle_192, hnd8, hn8, hncap8, hin_nd, hdisj_nd⟩
    · apply Hoare.assign_fall
      intro F s v hMid hv
      obtain ⟨w_nd, w_n, w_cap, S, Nd, hWT, hAs, hbo_nz, hc0,
        hlu_d, hlu_n, hlu_c, hle_192, hnd8, hn8, hncap8, hin_nd, hdisj_nd⟩ := hMid
      have hv_eq : v = .val (.word (w_cap * 2#64 + 1024#64)) := by
        simp only [evalAt, evalHOLExact, evalListHOLExact, hlu_c, valueIsWord, valueWord, panOpHOL,
          wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, if_true, Option.some.injEq] at hv
        rw [← hv]; simp [BitVec.add_zero]
      subst hv_eq
      refine ⟨w_nd, w_n, w_cap * 2#64 + 1024#64, S, Nd,
        (worldTypedWith_with_locals s _ s.clock S Nd).2 hWT,
        localsFree_arenaReady s _ s.clock hAs, hbo_nz, hc0,
        by have hne : ofString "dep_cap" ≠ ofString "dep" := by decide
           simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, hlu_d],
        by have hne : ofString "dep_cap" ≠ ofString "dep_n" := by decide
           simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, hlu_n],
        by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
        hle_192, hnd8, hn8, hncap8, hin_nd, hdisj_nd⟩

theorem hoare_skip_depWriteReady :
    Hoare
      (fun s => DepLoopInv s ∧
        CondFalse (.cmp .lower (.var .local (ofString "dep_cap"))
          (.op .add [.var .local (ofString "dep_n"), .const 192#64])) s)
      .skip
      (fun r t => r = none → DepWriteReady t) := by
  apply Hoare.skip
  intro F s ⟨hInv, hcf⟩ _
  obtain ⟨w_dep, w_n, w_cap, S, Nd, hWT, hAs, hbo_nz, hc0, hlu_d, hlu_n, hlu_c, hle_nc, hd8, hn8, hc8, hin, hdisj⟩ := hInv
  have hge_192 : w_n.toNat + 192 ≤ w_cap.toNat := by
    have hcap_bound : w_cap.toNat ≤ heapEnd - sourceBase := by
      have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hAs.2.2.1
      have hlim_le : heapLimit ≤ heapEnd := by decide
      unfold Inside at hin; omega
    have hdom_val : heapEnd - sourceBase = 31104957928 := by decide
    have h264 : (31104957928 : Nat) + 192 < 2 ^ 64 := by decide
    have hadd_nat : (w_n + 192#64).toNat = w_n.toNat + 192 := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    unfold CondFalse at hcf
    simp only [evalHOLExact, evalListHOLExact, hlu_c, hlu_n, valueIsWord, valueWord, wordOpHOL,
      wordOp, List.all, List.map, Option.map, Bool.and_self, if_true, Option.some.injEq,
      ValueHOL.val.injEq, HolWordLab.word.injEq] at hcf
    have hfold_eq : List.foldr (fun left right : BitVec 64 => left + right) 0 [w_n, 192#64] = w_n + 192#64 := by
      simp [BitVec.add_zero]
    rw [hfold_eq] at hcf
    have hnlt : ¬ (w_cap < w_n + 192#64) := by
      intro hlt
      simp [wordCmpHOL, hlt] at hcf
    rw [BitVec.lt_def, hadd_nat] at hnlt
    omega
  exact ⟨w_dep, w_n, w_cap, S, Nd, hWT, hAs, hbo_nz, hc0, hlu_d, hlu_n, hlu_c, hge_192, hd8, hn8, hc8, hin, hdisj⟩

theorem hoare_extract_deposit_step
    (wed : WorldKeeps WorldOK (fun s => [(locN s "out", 192)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "extract_deposit_data"))
    (e1 e2 : ExpHOL 64) :
    Hoare DepWriteReady
      (.seq
        (.call (some (none, none)) (ofString "extract_deposit_data")
          [e1, e2, .op .add [.var .local (ofString "dep"), .var .local (ofString "dep_n")]])
        (.assign .local (ofString "dep_n") (.op .add [.var .local (ofString "dep_n"), .const 192#64])))
      (fun r t => r = none → DepLoopInv t) := by
  apply Hoare.seq_fall (R := DepWriteReady)
  · refine ⟨fun {F} state hcode hWR _ hr => ?_⟩
    rcases hcall : evaluateHOLFiniteState state
        (.call (some (none, none)) (ofString "extract_deposit_data")
          [e1, e2, .op .add [.var .local (ofString "dep"), .var .local (ofString "dep_n")]]) with ⟨cres, cpost⟩
    have hr' : cres = none := by rw [hcall] at hr; exact hr
    subst hr'
    obtain ⟨w_dep, w_n, w_cap, S, Nd, hWT, hAs, hbo_nz, hc0,
      hlu_d, hlu_n, hlu_c, hge_192, hd8, hn8, hc8, hin_dep, hdisj_dep⟩ := hWR
    have h264 : heapEnd < 2 ^ 64 ∧ heapLimit ≤ heapEnd := ⟨by decide, by decide⟩
    have hhp_lim : globN state "heap_ptr" ≤ heapLimit := hAs.2.2.1
    have hout_nat : (w_dep + w_n).toNat = w_dep.toNat + w_n.toNat := by
      rw [BitVec.toNat_add]
      exact Nat.mod_eq_of_lt (by unfold Inside at hin_dep; omega)
    have he3 : evalAt state (.op .add [.var .local (ofString "dep"), .var .local (ofString "dep_n")]) =
        some (.val (.word (w_dep + w_n))) := by
      simp only [evalAt, evalHOLExact, evalListHOLExact, hlu_d, hlu_n, valueIsWord, valueWord,
        wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, if_true, Option.some.injEq]
      simp [BitVec.add_zero]
    rw [evaluateHOLFiniteState_call] at hcall
    rcases hargs : evalListHOLFinite state
        (h := fun a => Classical.propDecidable (state.memaddrs a))
        [e1, e2, .op .add [.var .local (ofString "dep"), .var .local (ofString "dep_n")]] with _ | values
    · rw [hargs] at hcall; simp at hcall
    · rw [hargs] at hcall; dsimp only at hcall
      have hargs_ex := hargs
      rw [evalListHOLFinite_eq_toExact] at hargs_ex
      rcases he1 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e1 with _ | v1
      · simp [evalListHOLExact, he1] at hargs_ex
      · rcases he2 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e2 with _ | v2
        · simp [evalListHOLExact, he1, he2] at hargs_ex
        · rcases hl : lookupCodeHOLFinite state.code.lookup (ofString "extract_deposit_data") values with _ | ⟨body, callee, ret⟩
          · rw [hl] at hcall; simp at hcall
          · rw [hl] at hcall; dsimp only at hcall
            by_cases hz : state.clock = 0
            · rw [if_pos hz] at hcall; simp at hcall
            · rw [if_neg hz] at hcall
              have hp3 := callee_param_three state (ofString "extract_deposit_data")
                (ofString "data") (ofString "n") (ofString "out") .one .one .one _ _
                (by rw [hcode]; exact lookup_extract_deposit_data_fn)
                e1 e2 (.op .add [.var .local (ofString "dep"), .var .local (ofString "dep_n")])
                v1 v2 (.val (.word (w_dep + w_n))) values body callee ret he1 he2 he3 hargs hl
              have hout_loc : locN (callEntryStateHOLFinite state callee) "out" = w_dep.toNat + w_n.toNat := by
                simp [locN, callEntryStateHOLFinite, hp3.2.2, hout_nat]
              rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with ⟨bres, post⟩
              rw [hrun] at hcall
              cases bres with
              | none => simp at hcall
              | some br =>
                cases br with
                | returned v =>
                  dsimp only at hcall
                  by_cases hsh : shapeEqHOL (shapeOfHOLExact v) ret = true
                  · rw [if_pos hsh] at hcall
                    obtain ⟨_, rfl⟩ := Prod.mk.inj hcall
                    have hW_state : WorldOK state := ⟨hAs, S, (worldTyped_iff_with state S).2 ⟨Nd, hWT⟩⟩
                    have hstep := FunSpec.at_lookup wed state hcode _ body callee ret hl
                      (localsFree_worldOK state callee (state.clock - 1) hW_state) (by rw [hrun]; simp)
                    rw [hrun] at hstep; dsimp only at hstep
                    obtain ⟨hAp, hhp, hG, hRK, hWS⟩ := hstep (Or.inl ⟨v, rfl⟩)
                    have hin_sub : Inside (w_dep.toNat + w_n.toNat, 192) w_dep.toNat (w_dep.toNat + w_cap.toNat) :=
                      ⟨by omega, by omega⟩
                    have hdisj_R : IvlsDisj [(w_dep.toNat + w_n.toNat, 192)] (worldTypedIvls state S Nd) := by
                      intro x hx j hj
                      simp only [List.mem_singleton] at hx; subst hx
                      exact disj_of_inside_left (i' := (w_dep.toNat, w_cap.toNat)) hin_sub
                        (hdisj_dep _ (by simp) j (worldTypedIvls_sub_worldOwned _ _ _ j hj))
                    obtain ⟨S', Nd', _, hWT', hog, _, _⟩ :=
                      hWS S Nd ((worldTypedWith_with_locals _ _ _ _ _).2 hWT)
                        (by dsimp only; rw [hout_loc]; exact hdisj_R)
                    have hdisj_dep' : IvlsDisj [(w_dep.toNat, w_cap.toNat)] (worldOwned post S' Nd') := by
                      intro x hx o ho
                      simp only [List.mem_singleton] at hx; subst hx
                      rcases hog o ho with rfl | ⟨j, hj, hin_oj⟩ | hfresh
                      · exact disj_zero_right _
                      · exact disj_of_inside_right hin_oj (hdisj_dep _ (by simp) j hj)
                      · exact Or.inr (Or.inr (Or.inl (Nat.le_trans hin_dep.2 hfresh.1)))
                    have hbo_eq : globN post "bo" = globN state "bo" := by
                      unfold globN; rw [← hG (ofString "bo") (by simp; decide)]; rfl
                    have hbo_rec : (globN state "bo", 88) ∈ worldOwned state S Nd := by
                      have hfix := typedRecord_mem_fixedObjects state (show ("bo", 88) ∈ typedRecords by decide)
                      rw [if_neg hbo_nz] at hfix
                      unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))
                    have hbo8 : (globN state "bo") % 8 = 0 := by
                      have hfix := typedRecord_mem_fixedObjects state (show ("bo", 88) ∈ typedRecords by decide)
                      rw [if_neg hbo_nz] at hfix
                      rcases hWT.2.2.1.1 _ hfix with hz | ⟨_, hw⟩
                      · dsimp at hz; omega
                      · exact hw.1
                    have hc64_eq : memW post (globN state "bo" + 64) = memW state (globN state "bo" + 64) := by
                      apply hRK ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp) hbo_nz 64 (by simp)
                      intro i hi
                      dsimp only at hi ⊢; rw [hout_loc] at hi
                      change ¬ CellHits (globN state "bo" + 64) i
                      simp only [List.mem_singleton] at hi; subst hi
                      have hd_bo : Disj (w_dep.toNat + w_n.toNat, 192) (globN state "bo", 88) :=
                        disj_of_inside_left (i' := (w_dep.toNat, w_cap.toNat)) hin_sub
                          (hdisj_dep _ (by simp) _ hbo_rec)
                      exact fun hch => not_cellHits_of_disj (by omega) (by omega) (by omega) (by omega) hch hd_bo ⟨by omega, by omega⟩
                    exact ⟨w_dep, w_n, w_cap, S', Nd',
                      (worldTypedWith_with_locals post _ post.clock S' Nd').2 hWT',
                      localsFree_arenaReady post _ post.clock hAp,
                      by show globN post "bo" ≠ 0; rw [hbo_eq]; exact hbo_nz,
                      by show memW post (globN post "bo" + 64) = 0; rw [hbo_eq, hc64_eq]; omega,
                      hlu_d, hlu_n, hlu_c, hge_192, hd8, hn8, hc8,
                      ⟨hin_dep.1, Nat.le_trans hin_dep.2 hhp⟩, hdisj_dep'⟩
                  · rw [if_neg hsh] at hcall; simp at hcall
                | _ => simp at hcall
  · apply Hoare.assign_fall
    intro F s v hWR hv
    obtain ⟨w_dep, w_n, w_cap, S, Nd, hWT, hAs, hbo_nz, hc0,
      hlu_d, hlu_n, hlu_c, hge_192, hd8, hn8, hc8, hin_dep, hdisj_dep⟩ := hWR
    have h264 : heapEnd < 2 ^ 64 ∧ heapLimit ≤ heapEnd := ⟨by decide, by decide⟩
    have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hAs.2.2.1
    have hv_eq : v = .val (.word (w_n + 192#64)) := by
      simp only [evalAt, evalHOLExact, evalListHOLExact, hlu_n, valueIsWord, valueWord,
        wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, if_true, Option.some.injEq] at hv
      rw [← hv]; simp [BitVec.add_zero]
    subst hv_eq
    have hn_new_nat : (w_n + 192#64).toNat = w_n.toNat + 192 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by unfold Inside at hin_dep; omega)
    refine ⟨w_dep, w_n + 192#64, w_cap, S, Nd,
      (worldTypedWith_with_locals s _ s.clock S Nd).2 hWT,
      localsFree_arenaReady s _ s.clock hAs, hbo_nz, hc0,
      by have hne : ofString "dep_n" ≠ ofString "dep" := by decide
         simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, hlu_d],
      by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
      by have hne : ofString "dep_n" ≠ ofString "dep_cap" := by decide
         simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, hlu_c],
      by omega, hd8, by omega, hc8, hin_dep, hdisj_dep⟩

theorem resumeOn_memeq_depLoopInv
    (rmq : ReadOnlyFn (ofString "memeq")) (name : MlS)
    (hname : ∀ n ∈ ["dep", "dep_n", "dep_cap"], ofString n ≠ name)
    (args : List (ExpHOL 64)) :
    DecCallResumeOn DepLoopInv DepLoopInv name (ofString "memeq") args := by
  intro F state values body callee ret value post hcode hInv _ hl hrun
  have hro := FunSpec.at_lookup rmq state hcode values body callee ret hl
    (localsFree_guestInv state callee (state.clock - 1) (depLoopInv_guestInv hInv))
    (by rw [hrun]; simp)
  rw [hrun] at hro; dsimp only at hro
  have heq := hro (Or.inl ⟨value, rfl⟩)
  have hpost_eq : { post with locals := state.locals } = { state with clock := post.clock } := by
    rw [heq]; rfl
  rw [hpost_eq]
  exact localsOnly_depLoopInv.setVar hname value _
    (localsOnly_depLoopInv state state.locals post.clock (fun _ _ => rfl) hInv)

theorem hoare_dep_inner_after_isdep
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc"))
    (wed : WorldKeeps WorldOK (fun s => [(locN s "out", 192)]) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "extract_deposit_data"))
    (wmc : WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")]) []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "memcpy"))
    (rmq : ReadOnlyFn (ofString "memeq")) :
    Hoare DepLoopInv
      (.ite (.cmp .notEqual (.var .local (ofString "isdep")) (.const 0#64))
        (.ite (.cmp .lower (.const 0#64) (.load .one (.op .add [.var .local (ofString "log"), .const 16#64])))
          (.decCall (ofString "sig") .one (ofString "memeq")
            [.load .one (.op .add [.var .local (ofString "log"), .const 8#64]),
             .var .global (ofString "deposit_event_signature_hash"), .const 32#64]
            (.ite (.cmp .notEqual (.var .local (ofString "sig")) (.const 0#64))
              (.seq
                (.ite (.cmp .lower (.var .local (ofString "dep_cap"))
                  (.op .add [.var .local (ofString "dep_n"), .const 192#64]))
                  (.decCall (ofString "nd") .one (ofString "alloc")
                    [.op .add [.panop .mul [.var .local (ofString "dep_cap"), .const 2#64], .const 1024#64]]
                    (.seq
                      (.call (some (none, none)) (ofString "memcpy")
                        [.var .local (ofString "nd"), .var .local (ofString "dep"), .var .local (ofString "dep_n")])
                      (.seq
                        (.assign .local (ofString "dep") (.var .local (ofString "nd")))
                        (.assign .local (ofString "dep_cap")
                          (.op .add [.panop .mul [.var .local (ofString "dep_cap"), .const 2#64], .const 1024#64])))))
                  .skip)
                (.seq
                  (.call (some (none, none)) (ofString "extract_deposit_data")
                    [.load .one (.op .add [.var .local (ofString "log"), .const 24#64]),
                     .load .one (.op .add [.var .local (ofString "log"), .const 32#64]),
                     .op .add [.var .local (ofString "dep"), .var .local (ofString "dep_n")]])
                  (.assign .local (ofString "dep_n") (.op .add [.var .local (ofString "dep_n"), .const 192#64]))))
              .skip))
          .skip)
        .skip)
      (fun r t => r = none → DepLoopInv t) := by
  apply Hoare.ite_fall
  · apply Hoare.mono _ (fun _ h => h.1)
    apply Hoare.ite_fall
    · apply Hoare.mono _ (fun _ h => h.1)
      apply Hoare.decCall_fall (by simp; decide) localsOnly_depLoopInv
        (resumeOn_memeq_depLoopInv rmq (ofString "sig") (by simp; decide) _)
      apply Hoare.ite_fall
      · apply Hoare.mono _ (fun _ h => h.1)
        apply Hoare.seq_fall (R := DepWriteReady)
        · apply Hoare.ite_fall
          · exact Hoare.decCall_fall
              (names := ["dep", "dep_n", "dep_cap"]) (by simp; decide)
              (by
                intro F s locals k hl hWR
                obtain ⟨w_d, w_n, w_c, S, Nd, hWT, hA, hbo, hc0, hld, hln, hlc, hge, hd8, hn8, hc8, hin, hdj⟩ := hWR
                exact ⟨w_d, w_n, w_c, S, Nd,
                  (worldTypedWith_with_locals s locals k S Nd).2 hWT,
                  localsFree_arenaReady s locals k hA, hbo, hc0,
                  (hl "dep" (by simp)).trans hld,
                  (hl "dep_n" (by simp)).trans hln,
                  (hl "dep_cap" (by simp)).trans hlc,
                  hge, hd8, hn8, hc8, hin, hdj⟩)
              (resumeOn_realloc_dep wal rtal)
              (hoare_memcpy_dep_realloc wmc)
          · exact hoare_skip_depWriteReady
        · exact hoare_extract_deposit_step wed _ _
      · exact Hoare.skip fun _ h _ => h.1
    · exact Hoare.skip fun _ h _ => h.1
  · exact Hoare.skip fun _ h _ => h.1

theorem bounded_dep_inner_after_isdep
    (hal : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (hed : TerminatingFunBoundedOn GuestInv (ofString "extract_deposit_data") K.«extract_deposit_data»)
    (hmc : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»)
    (hmq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq»)
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc"))
    (wmc : WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")]) []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "memcpy"))
    (rmq : ReadOnlyFn (ofString "memeq")) :
    TerminatingProgBoundedOn DepLoopInv
      (.ite (.cmp .notEqual (.var .local (ofString "isdep")) (.const 0#64))
        (.ite (.cmp .lower (.const 0#64) (.load .one (.op .add [.var .local (ofString "log"), .const 16#64])))
          (.decCall (ofString "sig") .one (ofString "memeq")
            [.load .one (.op .add [.var .local (ofString "log"), .const 8#64]),
             .var .global (ofString "deposit_event_signature_hash"), .const 32#64]
            (.ite (.cmp .notEqual (.var .local (ofString "sig")) (.const 0#64))
              (.seq
                (.ite (.cmp .lower (.var .local (ofString "dep_cap"))
                  (.op .add [.var .local (ofString "dep_n"), .const 192#64]))
                  (.decCall (ofString "nd") .one (ofString "alloc")
                    [.op .add [.panop .mul [.var .local (ofString "dep_cap"), .const 2#64], .const 1024#64]]
                    (.seq
                      (.call (some (none, none)) (ofString "memcpy")
                        [.var .local (ofString "nd"), .var .local (ofString "dep"), .var .local (ofString "dep_n")])
                      (.seq
                        (.assign .local (ofString "dep") (.var .local (ofString "nd")))
                        (.assign .local (ofString "dep_cap")
                          (.op .add [.panop .mul [.var .local (ofString "dep_cap"), .const 2#64], .const 1024#64])))))
                  .skip)
                (.seq
                  (.call (some (none, none)) (ofString "extract_deposit_data")
                    [.load .one (.op .add [.var .local (ofString "log"), .const 24#64]),
                     .load .one (.op .add [.var .local (ofString "log"), .const 32#64]),
                     .op .add [.var .local (ofString "dep"), .var .local (ofString "dep_n")]])
                  (.assign .local (ofString "dep_n") (.op .add [.var .local (ofString "dep_n"), .const 192#64]))))
              .skip))
          .skip)
        .skip)
      (Nat.max (Nat.max ((K.«memeq» + 1) + Nat.max (Nat.max ((K.«alloc» + 1) + (K.«memcpy» + 1)) 0 + (K.«extract_deposit_data» + 1)) 0) 0) 0) := by
  intro F state hcode hInv
  exact TerminatingRunBounded.weaken
    ((TerminatingProgBoundedOn.ite_on
      (TerminatingProgBoundedOn.ite_on
        (TerminatingProgBoundedOn.decCall_on hmq _ _ _
          (callEntryOn_of_imp localsFree_guestInv (fun _ h => depLoopInv_guestInv h) _ _)
          (resumeOn_memeq_depLoopInv rmq (ofString "sig") (by simp; decide) _)
          (TerminatingProgBoundedOn.ite_on
            (TerminatingProgBoundedOn.seq_hoare_trans
              (TerminatingProgBoundedOn.ite_cond_on
                (TerminatingProgBoundedOn.decCall_on hal _ _ _
                  (callEntryOn_of_imp (P := fun s => DepLoopInv s ∧
                    CondTrue (.cmp .lower (.var .local (ofString "dep_cap"))
                      (.op .add [.var .local (ofString "dep_n"), .const 192#64])) s)
                    localsFree_guestInv (fun _ h => depLoopInv_guestInv h.1) _ _)
                  (resumeOn_realloc_dep wal rtal)
                  (TerminatingProgBoundedOn.seq_guestInv_after
                    (TerminatingProgBoundedOn.call_on hmc _ _
                      (callEntryOn_of_imp localsFree_guestInv (fun _ h => depReallocMid_guestInv h) _ _))
                    (fun _ h => depReallocMid_guestInv h)
                    (TerminatingProgBoundedOn.seq_guestInv
                      (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
                      (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _)))))
                (TerminatingProgBoundedOn.of_clock (P := fun s => DepLoopInv s ∧
                  CondFalse (.cmp .lower (.var .local (ofString "dep_cap"))
                    (.op .add [.var .local (ofString "dep_n"), .const 192#64])) s)
                  (fun s => clock_skip s)))
              (Hoare.ite_fall
                (Hoare.decCall_fall
                  (names := ["dep", "dep_n", "dep_cap"]) (by simp; decide)
                  (by
                    intro F2 s2 locals2 k2 hl2 hWR2
                    obtain ⟨w_d, w_n, w_c, S, Nd, hWT, hA, hbo, hc0, hld, hln, hlc, hge, hd8, hn8, hc8, hin, hdj⟩ := hWR2
                    exact ⟨w_d, w_n, w_c, S, Nd,
                      (worldTypedWith_with_locals s2 locals2 k2 S Nd).2 hWT,
                      localsFree_arenaReady s2 locals2 k2 hA, hbo, hc0,
                      (hl2 "dep" (by simp)).trans hld,
                      (hl2 "dep_n" (by simp)).trans hln,
                      (hl2 "dep_cap" (by simp)).trans hlc,
                      hge, hd8, hn8, hc8, hin, hdj⟩)
                  (resumeOn_realloc_dep wal rtal)
                  (hoare_memcpy_dep_realloc wmc))
                hoare_skip_depWriteReady)
              (TerminatingProgBoundedOn.seq_guestInv_after
                (TerminatingProgBoundedOn.call_on hed _ _
                  (callEntryOn_of_imp localsFree_guestInv (fun _ h => depWriteReady_guestInv h) _ _))
                (fun _ h => depWriteReady_guestInv h)
                (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))))
            (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s))))
        (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
      (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s))) state hcode hInv)
    (by simp only [show ∀ a b : Nat, Nat.max a b = max a b from fun _ _ => rfl]; omega)

theorem walk_loop_general {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {names : List String} {baseName idxName elemName : String}
    {tail : ProgHOL 64} {B : Nat}
    (hP : LocalsOnly names P)
    (hP_guest : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → GuestInv s)
    (helem_not_names : ∀ n ∈ names, ofString n ≠ ofString elemName)
    (helem_ne_base : ofString elemName ≠ ofString baseName)
    (helem_ne_idx : ofString elemName ≠ ofString idxName)
    (htail_step : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (wb wi : BitVec 64),
      s.code = originalRuntimeCode → P s →
      s.locals.lookup (ofString baseName) = some (.val (.word wb)) →
      s.locals.lookup (ofString idxName) = some (.val (.word wi)) →
      ((evaluateHOLFiniteState s tail).1 = none ∨
       (evaluateHOLFiniteState s tail).1 = some .continue ∨
       (evaluateHOLFiniteState s tail).1 = some .break) →
      P (evaluateHOLFiniteState s tail).2 ∧
      (evaluateHOLFiniteState s tail).2.locals.lookup (ofString baseName) = some (.val (.word wb)) ∧
      (evaluateHOLFiniteState s tail).2.locals.lookup (ofString idxName) = some (.val (.word (wi + 1#64))))
    (htail_bound : TerminatingProgBoundedOn P tail B) :
    ∀ (limitName : String),
      Hoare P
        (.while (.cmp .less (.var .local (ofString idxName)) (.var .local (ofString limitName)))
          (.dec (ofString elemName) .one
            (.load .one (.op .add [.var .local (ofString baseName),
              .panop .mul [.var .local (ofString idxName), .const 8#64]]))
            tail))
        (fun r t => r = none → P t) ∧
      TerminatingProgBoundedOn P
        (.while (.cmp .less (.var .local (ofString idxName)) (.var .local (ofString limitName)))
          (.dec (ofString elemName) .one
            (.load .one (.op .add [.var .local (ofString baseName),
              .panop .mul [.var .local (ofString idxName), .const 8#64]]))
            tail))
        ((31104957944 + 1) * (B + 1)) := by
  intro limitName
  set body := ProgHOL.dec (ofString elemName) .one
    (.load .one (.op .add [.var .local (ofString baseName),
      .panop .mul [.var .local (ofString idxName), .const 8#64]]))
    tail
  have hstep_common : ∀ {F : Type} (st : PanSemStateFiniteExact 64 F),
      st.code = originalRuntimeCode → P st →
      ((evaluateHOLFiniteState st body).1 = none ∨
       (evaluateHOLFiniteState st body).1 = some .continue ∨
       (evaluateHOLFiniteState st body).1 = some .break) →
      P (evaluateHOLFiniteState st body).2 ∧
      walkRank baseName idxName (evaluateHOLFiniteState st body).2 < walkRank baseName idxName st := by
    intro F st hcode hPst hflow
    set out := evaluateHOLFiniteState st body with hrun_def
    have hrun : evaluateHOLFiniteState st body = (out.1, out.2) := by simp [hrun_def]
    rcases out with ⟨res, post⟩
    dsimp only at hflow hrun ⊢
    have hfl : Flowing res := by
      rcases hflow with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    have hrun_dec := hrun
    rw [evaluateHOLFiniteState_dec_total] at hrun_dec
    dsimp only at hrun_dec
    rcases he : @evalHOLExact 64 F _ st.toExact
        (fun a => Classical.propDecidable (st.memaddrs a))
        (.load .one (.op .add [.var .local (ofString baseName),
          .panop .mul [.var .local (ofString idxName), .const 8#64]])) with _ | val
    · rw [he] at hrun_dec; simp at hrun_dec; obtain ⟨rfl, _⟩ := hrun_dec; rcases hfl with h | h | h <;> simp at h
    · rw [he] at hrun_dec; dsimp only at hrun_dec
      by_cases hsh : shapeEqHOL .one (shapeOfHOLExact val) = true
      · rw [if_pos hsh] at hrun_dec
        obtain ⟨a, _, ha, _, _, hlo, hhi⟩ := evalAt_load_one_ordinary (hP_guest st hPst) he
        obtain ⟨wb, wi, hb_st, hi_st, ha_eq⟩ := evalAt_add_panMul8 ha
        injection ha_eq with ha_eq'; injection ha_eq' with ha_eq''; subst ha_eq''
        set s1 := setVarHOLFinite (ofString elemName) val st
        have hPs1 : P s1 := hP.setVar helem_not_names val st hPst
        have hb_s1 : s1.locals.lookup (ofString baseName) = some (.val (.word wb)) := by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, helem_ne_base, hb_st]
        have hi_s1 : s1.locals.lookup (ofString idxName) = some (.val (.word wi)) := by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, helem_ne_idx, hi_st]
        obtain ⟨hres_eq, hpost_eq⟩ := Prod.mk.inj hrun_dec
        have htail_fl : (evaluateHOLFiniteState s1 tail).1 = none ∨
            (evaluateHOLFiniteState s1 tail).1 = some .continue ∨
            (evaluateHOLFiniteState s1 tail).1 = some .break := by
          rw [hres_eq]; exact hflow
        obtain ⟨hP_t, hb_t, hi_t⟩ := htail_step s1 wb wi hcode hPs1 hb_s1 hi_s1 htail_fl
        rw [← hpost_eq]
        refine ⟨?_, ?_⟩
        · exact hP (evaluateHOLFiniteState s1 tail).2
            (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s1 tail).2.locals
              (ofString elemName, st.locals.lookup (ofString elemName)))
            (evaluateHOLFiniteState s1 tail).2.clock
            (fun n hn => resVarEq_lookup_ne _ _ _ _ (helem_not_names n hn)) hP_t
        · apply walkRank_step_lt hb_st hi_st
          · rw [PanRunBounded.resVarEq_lookup, if_neg helem_ne_base.symm]; exact hb_t
          · rw [PanRunBounded.resVarEq_lookup, if_neg helem_ne_idx.symm]; exact hi_t
          · exact hlo
          · exact hhi
      · rw [if_neg hsh] at hrun_dec; simp at hrun_dec; obtain ⟨rfl, _⟩ := hrun_dec; rcases hfl with h | h | h <;> simp at h
  refine ⟨?_, ?_⟩
  · exact Hoare.while_preserve hP.decClock
      ⟨fun st hcode ⟨hPst, _⟩ _ hfl => (hstep_common st hcode hPst hfl).1⟩
  · exact TerminatingProgBoundedOn.mono_bound
      (TerminatingProgBoundedOn.while_rank (walkRank baseName idxName)
        hP.decClock
        (TerminatingProgBoundedOn.dec_onLocals hP (ofString elemName) helem_not_names _ _ htail_bound)
        (fun s _ _ _ => walkRank_le baseName idxName s)
        (fun s hcode hPs _ hfl =>
          hstep_common (decClockHOLFinite s) hcode (hP.decClock s hPs)
            (hfl.elim Or.inl (fun h => Or.inr (Or.inl h)))))
      (by omega)

theorem walk_seq_inc_step {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {names : List String} {baseName idxName : String} {mid : ProgHOL 64}
    (hP : LocalsOnly names P)
    (hidx_not_names : ∀ n ∈ names, ofString n ≠ ofString idxName)
    (hidx_ne_base : ofString idxName ≠ ofString baseName)
    (hav_base : avoidsLocal (ofString baseName) mid = true)
    (hav_idx : avoidsLocal (ofString idxName) mid = true)
    (hmid_no_cont : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s mid).1 ≠ some .continue ∧
      (evaluateHOLFiniteState s mid).1 ≠ some .break)
    (hmid_hoare : Hoare P mid (fun r t => r = none → P t)) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (wb wi : BitVec 64),
      s.code = originalRuntimeCode → P s →
      s.locals.lookup (ofString baseName) = some (.val (.word wb)) →
      s.locals.lookup (ofString idxName) = some (.val (.word wi)) →
      ((evaluateHOLFiniteState s (.seq mid (.assign .local (ofString idxName)
        (.op .add [.var .local (ofString idxName), .const 1#64])))).1 = none ∨
       (evaluateHOLFiniteState s (.seq mid (.assign .local (ofString idxName)
        (.op .add [.var .local (ofString idxName), .const 1#64])))).1 = some .continue ∨
       (evaluateHOLFiniteState s (.seq mid (.assign .local (ofString idxName)
        (.op .add [.var .local (ofString idxName), .const 1#64])))).1 = some .break) →
      P (evaluateHOLFiniteState s (.seq mid (.assign .local (ofString idxName)
        (.op .add [.var .local (ofString idxName), .const 1#64])))).2 ∧
      (evaluateHOLFiniteState s (.seq mid (.assign .local (ofString idxName)
        (.op .add [.var .local (ofString idxName), .const 1#64])))).2.locals.lookup (ofString baseName) =
          some (.val (.word wb)) ∧
      (evaluateHOLFiniteState s (.seq mid (.assign .local (ofString idxName)
        (.op .add [.var .local (ofString idxName), .const 1#64])))).2.locals.lookup (ofString idxName) =
          some (.val (.word (wi + 1#64))) := by
  intro F s wb wi hcode hPs hb_s hi_s hflow
  set out := evaluateHOLFiniteState s (.seq mid (.assign .local (ofString idxName)
    (.op .add [.var .local (ofString idxName), .const 1#64]))) with hout
  have hrun : evaluateHOLFiniteState s (.seq mid (.assign .local (ofString idxName)
    (.op .add [.var .local (ofString idxName), .const 1#64]))) = (out.1, out.2) := by simp [hout]
  rcases out with ⟨res, post⟩
  dsimp only at hflow hrun ⊢
  rw [evaluateHOLFiniteState_seq_line780] at hrun
  rcases hm_run : evaluateHOLFiniteState s mid with ⟨mres, s2⟩
  rw [hm_run] at hrun
  cases mres with
  | some mr =>
    dsimp only at hrun
    obtain ⟨rfl, _⟩ := Prod.mk.inj hrun
    rcases hflow with h | h | h
    · simp at h
    · exact absurd (by rw [hm_run]; exact h) (hmid_no_cont s).1
    · exact absurd (by rw [hm_run]; exact h) (hmid_no_cont s).2
  | none =>
    dsimp only at hrun
    have hPs2 : P s2 := by
      have hh := hmid_hoare.run s hcode hPs (by rw [hm_run]; simp)
      rw [hm_run] at hh; exact hh rfl
    have hb_s2 : s2.locals.lookup (ofString baseName) = some (.val (.word wb)) := by
      have hav := evaluate_avoidsLocal_flowing (ofString baseName) mid hav_base s
        (by rw [hm_run]; exact Or.inl rfl)
      rw [hm_run] at hav; exact hav.trans hb_s
    have hi_s2 : s2.locals.lookup (ofString idxName) = some (.val (.word wi)) := by
      have hav := evaluate_avoidsLocal_flowing (ofString idxName) mid hav_idx s
        (by rw [hm_run]; exact Or.inl rfl)
      rw [hm_run] at hav; exact hav.trans hi_s
    rw [evaluateHOLFiniteState_assign] at hrun
    have hass_ev : @evalHOLExact 64 F _ s2.toExact
        (fun a => Classical.propDecidable (s2.memaddrs a))
        (.op .add [.var .local (ofString idxName), .const 1#64]) =
        some (.val (.word (wi + 1#64))) := by
      simp only [evalHOLExact, evalListHOLExact, hi_s2, valueIsWord, valueWord, wordOpHOL,
        wordOp, List.all, List.map, Option.map, Bool.and_self, if_true, Option.some.injEq]
      simp [BitVec.add_zero]
    rw [hass_ev] at hrun; dsimp only at hrun
    have hvalid : isValidValueHOLFinite s2 .local (ofString idxName) (.val (.word (wi + 1#64))) = true := by
      simp [isValidValueHOLFinite, lookupKvarHOLFinite, hi_s2, shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hvalid] at hrun
    obtain ⟨_, hpost_eq⟩ := Prod.mk.inj hrun
    rw [← hpost_eq]
    exact ⟨hP.setVar hidx_not_names _ s2 hPs2,
      by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hidx_ne_base, hb_s2],
      by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩

theorem walk_dec_step {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {names : List String} {baseName idxName : String}
    {name : MlS} {sh : ShapeHOL} {init : ExpHOL 64} {cont : ProgHOL 64}
    (hP : LocalsOnly names P)
    (hname_not_names : ∀ n ∈ names, ofString n ≠ name)
    (hname_ne_base : name ≠ ofString baseName)
    (hname_ne_idx : name ≠ ofString idxName)
    (hcont : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (wb wi : BitVec 64),
      s.code = originalRuntimeCode → P s →
      s.locals.lookup (ofString baseName) = some (.val (.word wb)) →
      s.locals.lookup (ofString idxName) = some (.val (.word wi)) →
      ((evaluateHOLFiniteState s cont).1 = none ∨
       (evaluateHOLFiniteState s cont).1 = some .continue ∨
       (evaluateHOLFiniteState s cont).1 = some .break) →
      P (evaluateHOLFiniteState s cont).2 ∧
      (evaluateHOLFiniteState s cont).2.locals.lookup (ofString baseName) = some (.val (.word wb)) ∧
      (evaluateHOLFiniteState s cont).2.locals.lookup (ofString idxName) = some (.val (.word (wi + 1#64)))) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (wb wi : BitVec 64),
      s.code = originalRuntimeCode → P s →
      s.locals.lookup (ofString baseName) = some (.val (.word wb)) →
      s.locals.lookup (ofString idxName) = some (.val (.word wi)) →
      ((evaluateHOLFiniteState s (.dec name sh init cont)).1 = none ∨
       (evaluateHOLFiniteState s (.dec name sh init cont)).1 = some .continue ∨
       (evaluateHOLFiniteState s (.dec name sh init cont)).1 = some .break) →
      P (evaluateHOLFiniteState s (.dec name sh init cont)).2 ∧
      (evaluateHOLFiniteState s (.dec name sh init cont)).2.locals.lookup (ofString baseName) =
          some (.val (.word wb)) ∧
      (evaluateHOLFiniteState s (.dec name sh init cont)).2.locals.lookup (ofString idxName) =
          some (.val (.word (wi + 1#64))) := by
  intro F s wb wi hcode hPs hb_s hi_s hflow
  set out := evaluateHOLFiniteState s (.dec name sh init cont) with hout
  have hrun : evaluateHOLFiniteState s (.dec name sh init cont) = (out.1, out.2) := by simp [hout]
  rcases out with ⟨res, post⟩
  dsimp only at hflow hrun ⊢
  have hfl : Flowing res := by
    rcases hflow with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  rw [evaluateHOLFiniteState_dec_total] at hrun
  dsimp only at hrun
  rcases he : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) init with _ | val
  · rw [he] at hrun; simp at hrun; obtain ⟨rfl, _⟩ := hrun; rcases hfl with h | h | h <;> simp at h
  · rw [he] at hrun; dsimp only at hrun
    split_ifs at hrun with hsh
    · set s1 := setVarHOLFinite name val s
      have hb_s1 : s1.locals.lookup (ofString baseName) = some (.val (.word wb)) := by
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hname_ne_base, hb_s]
      have hi_s1 : s1.locals.lookup (ofString idxName) = some (.val (.word wi)) := by
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hname_ne_idx, hi_s]
      obtain ⟨hres_eq, hpost_eq⟩ := Prod.mk.inj hrun
      have hc_fl : (evaluateHOLFiniteState s1 cont).1 = none ∨
          (evaluateHOLFiniteState s1 cont).1 = some .continue ∨
          (evaluateHOLFiniteState s1 cont).1 = some .break := by
        rw [hres_eq]; exact hflow
      obtain ⟨hP_c, hb_c, hi_c⟩ := hcont s1 wb wi hcode (hP.setVar hname_not_names val s hPs) hb_s1 hi_s1 hc_fl
      rw [← hpost_eq]
      refine ⟨?_, ?_, ?_⟩
      · exact hP (evaluateHOLFiniteState s1 cont).2
          (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s1 cont).2.locals
            (name, s.locals.lookup name))
          (evaluateHOLFiniteState s1 cont).2.clock
          (fun n hn => resVarEq_lookup_ne _ _ _ _ (hname_not_names n hn)) hP_c
      · rw [PanRunBounded.resVarEq_lookup, if_neg hname_ne_base.symm]; exact hb_c
      · rw [PanRunBounded.resVarEq_lookup, if_neg hname_ne_idx.symm]; exact hi_c
    · simp at hrun; obtain ⟨rfl, _⟩ := hrun; rcases hfl with h | h | h <;> simp at h

theorem walk_decCall_step {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {names : List String} {baseName idxName : String}
    {name fname : MlS} {sh : ShapeHOL} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hP : LocalsOnly names P)
    (hname_not_names : ∀ n ∈ names, ofString n ≠ name)
    (hname_ne_base : name ≠ ofString baseName)
    (hname_ne_idx : name ≠ ofString idxName)
    (hres : DecCallResumeOn P P name fname args)
    (hcont : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (wb wi : BitVec 64),
      s.code = originalRuntimeCode → P s →
      s.locals.lookup (ofString baseName) = some (.val (.word wb)) →
      s.locals.lookup (ofString idxName) = some (.val (.word wi)) →
      ((evaluateHOLFiniteState s cont).1 = none ∨
       (evaluateHOLFiniteState s cont).1 = some .continue ∨
       (evaluateHOLFiniteState s cont).1 = some .break) →
      P (evaluateHOLFiniteState s cont).2 ∧
      (evaluateHOLFiniteState s cont).2.locals.lookup (ofString baseName) = some (.val (.word wb)) ∧
      (evaluateHOLFiniteState s cont).2.locals.lookup (ofString idxName) = some (.val (.word (wi + 1#64)))) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (wb wi : BitVec 64),
      s.code = originalRuntimeCode → P s →
      s.locals.lookup (ofString baseName) = some (.val (.word wb)) →
      s.locals.lookup (ofString idxName) = some (.val (.word wi)) →
      ((evaluateHOLFiniteState s (.decCall name sh fname args cont)).1 = none ∨
       (evaluateHOLFiniteState s (.decCall name sh fname args cont)).1 = some .continue ∨
       (evaluateHOLFiniteState s (.decCall name sh fname args cont)).1 = some .break) →
      P (evaluateHOLFiniteState s (.decCall name sh fname args cont)).2 ∧
      (evaluateHOLFiniteState s (.decCall name sh fname args cont)).2.locals.lookup (ofString baseName) =
          some (.val (.word wb)) ∧
      (evaluateHOLFiniteState s (.decCall name sh fname args cont)).2.locals.lookup (ofString idxName) =
          some (.val (.word (wi + 1#64))) := by
  intro F s wb wi hcode hPs hb_s hi_s hflow
  set out := evaluateHOLFiniteState s (.decCall name sh fname args cont) with hout
  have hrun : evaluateHOLFiniteState s (.decCall name sh fname args cont) = (out.1, out.2) := by simp [hout]
  rcases out with ⟨res, post⟩
  dsimp only at hflow hrun ⊢
  have hfl : Flowing res := by
    rcases hflow with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · rw [hargs] at hrun; simp at hrun; obtain ⟨rfl, _⟩ := hrun; rcases hfl with h | h | h <;> simp at h
  · rw [hargs] at hrun; dsimp only at hrun
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · rw [hl] at hrun; simp at hrun; obtain ⟨rfl, _⟩ := hrun; rcases hfl with h | h | h <;> simp at h
    · rw [hl] at hrun; dsimp only at hrun
      split_ifs at hrun with hz
      · simp at hrun; obtain ⟨rfl, _⟩ := hrun; rcases hfl with h | h | h <;> simp at h
      · have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body').1
        rcases hb_run : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨bres, bpost⟩
        rw [hb_run] at hrun hmeta
        dsimp only at hmeta
        cases bres with
        | none => simp at hrun; obtain ⟨rfl, _⟩ := hrun; rcases hfl with h | h | h <;> simp at h
        | some br =>
          cases br with
          | returned v =>
            dsimp only at hrun
            split_ifs at hrun with hsh
            · set resumed := setVarHOLFinite name v { bpost with locals := s.locals }
              have hresP : P resumed := hres s values body' callee ret' v bpost hcode hPs hargs hl hb_run
              have hresCode : resumed.code = originalRuntimeCode := hmeta.trans hcode
              have hb_res : resumed.locals.lookup (ofString baseName) = some (.val (.word wb)) := by
                simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hname_ne_base, hb_s]
              have hi_res : resumed.locals.lookup (ofString idxName) = some (.val (.word wi)) := by
                simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hname_ne_idx, hi_s]
              obtain ⟨hres_eq, hpost_eq⟩ := Prod.mk.inj hrun
              have hc_fl : (evaluateHOLFiniteState resumed cont).1 = none ∨
                  (evaluateHOLFiniteState resumed cont).1 = some .continue ∨
                  (evaluateHOLFiniteState resumed cont).1 = some .break := by
                rw [hres_eq]; exact hflow
              obtain ⟨hP_c, hb_c, hi_c⟩ := hcont resumed wb wi hresCode hresP hb_res hi_res hc_fl
              rw [← hpost_eq]
              refine ⟨?_, ?_, ?_⟩
              · exact hP (evaluateHOLFiniteState resumed cont).2
                  (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState resumed cont).2.locals
                    (name, s.locals.lookup name))
                  (evaluateHOLFiniteState resumed cont).2.clock
                  (fun n hn => resVarEq_lookup_ne _ _ _ _ (hname_not_names n hn)) hP_c
              · rw [PanRunBounded.resVarEq_lookup, if_neg hname_ne_base.symm]; exact hb_c
              · rw [PanRunBounded.resVarEq_lookup, if_neg hname_ne_idx.symm]; exact hi_c
            · simp at hrun; obtain ⟨rfl, _⟩ := hrun; rcases hfl with h | h | h <;> simp at h
          | _ => simp at hrun; obtain ⟨rfl, _⟩ := hrun; rcases hfl with h | h | h <;> simp at h

theorem no_cont_break_seq {p1 p2 : ProgHOL 64}
    (h1 : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s p1).1 ≠ some .continue ∧ (evaluateHOLFiniteState s p1).1 ≠ some .break)
    (h2 : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s p2).1 ≠ some .continue ∧ (evaluateHOLFiniteState s p2).1 ≠ some .break) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s (.seq p1 p2)).1 ≠ some .continue ∧
      (evaluateHOLFiniteState s (.seq p1 p2)).1 ≠ some .break := by
  intro F s
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hr1 : evaluateHOLFiniteState s p1 with ⟨r1, s1⟩
  cases r1 with
  | none => exact h2 s1
  | some _ =>
    have := h1 s
    rw [hr1] at this
    exact this

theorem no_cont_break_ite {cond : ExpHOL 64} {p1 p2 : ProgHOL 64}
    (h1 : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s p1).1 ≠ some .continue ∧ (evaluateHOLFiniteState s p1).1 ≠ some .break)
    (h2 : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s p2).1 ≠ some .continue ∧ (evaluateHOLFiniteState s p2).1 ≠ some .break) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s (.ite cond p1 p2)).1 ≠ some .continue ∧
      (evaluateHOLFiniteState s (.ite cond p1 p2)).1 ≠ some .break := by
  intro F s
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact h2 s
    · exact h1 s
  · simp

theorem no_cont_break_dec {name : MlS} {sh : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (hb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s body).1 ≠ some .continue ∧ (evaluateHOLFiniteState s body).1 ≠ some .break) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s (.dec name sh init body)).1 ≠ some .continue ∧
      (evaluateHOLFiniteState s (.dec name sh init body)).1 ≠ some .break := by
  intro F s
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · simp
  · split
    · exact hb _
    · simp

theorem no_cont_break_decCall {name fname : MlS} {sh : ShapeHOL} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hc : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s cont).1 ≠ some .continue ∧ (evaluateHOLFiniteState s cont).1 ≠ some .break) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s (.decCall name sh fname args cont)).1 ≠ some .continue ∧
      (evaluateHOLFiniteState s (.decCall name sh fname args cont)).1 ≠ some .break := by
  intro F s
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · simp
  · dsimp only
    rcases lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body, callee, ret⟩
    · simp
    · dsimp only
      split_ifs with hz
      · simp
      · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨bres, _⟩
        cases bres with
        | none => simp
        | some br =>
          cases br with
          | returned _ =>
            dsimp only; split_ifs
            · exact hc _
            · simp
          | _ => simp

theorem no_cont_break_call (ret : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL 64)))
    (hnone : ∀ h, ret ≠ some (none, some h) ∧ ∀ d, ret ≠ some (d, some h))
    (fname : MlS) (args : List (ExpHOL 64)) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s (.call ret fname args)).1 ≠ some .continue ∧
      (evaluateHOLFiniteState s (.call ret fname args)).1 ≠ some .break := by
  intro F s
  cases ret with
  | none =>
    rw [evaluateHOLFiniteState_call]
    rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
    · simp
    · dsimp only
      rcases lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body, callee, rsh⟩
      · simp
      · dsimp only
        split_ifs with hz
        · simp
        · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨bres, _⟩
          cases bres with
          | none => simp
          | some br =>
            cases br with
            | returned _ => dsimp only; split_ifs <;> simp
            | _ => simp
  | some p =>
    rcases p with ⟨dest, hdl⟩
    cases hdl with
    | some h => exact absurd rfl ((hnone h).2 dest)
    | none =>
      rw [evaluateHOLFiniteState_call]
      rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
      · simp
      · dsimp only
        rcases lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body, callee, rsh⟩
        · simp
        · dsimp only
          split_ifs with hz
          · simp
          · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨bres, _⟩
            cases bres with
            | none => simp
            | some br =>
              cases br with
              | returned _ =>
                cases dest with
                | none => dsimp only; split_ifs <;> simp
                | some kv => dsimp only; split_ifs <;> simp
              | _ => simp

theorem no_cont_break_assign (k : VarKind) (name : MlS) (e : ExpHOL 64) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s (.assign k name e)).1 ≠ some .continue ∧
      (evaluateHOLFiniteState s (.assign k name e)).1 ≠ some .break := by
  intro F s
  rw [evaluateHOLFiniteState_assign]
  split
  · simp
  · split <;> simp

theorem no_cont_break_skip :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s .skip).1 ≠ some .continue ∧
      (evaluateHOLFiniteState s .skip).1 ≠ some .break := by
  intro F s; simp

theorem no_cont_break_while (cond : ExpHOL 64) (body : ProgHOL 64) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s (.while cond body)).1 ≠ some .continue ∧
      (evaluateHOLFiniteState s (.while cond body)).1 ≠ some .break := by
  intro F s
  suffices ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock = k →
      (evaluateHOLFiniteState st (.while cond body)).1 ≠ some .continue ∧
      (evaluateHOLFiniteState st (.while cond body)).1 ≠ some .break from
    this s.clock s rfl
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st hk
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp
        · dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
          set bOut := evaluateHOLFiniteState (decClockHOLFinite st) body with hbOut
          have bRun : evaluateHOLFiniteState (decClockHOLFinite st) body = (bOut.1, bOut.2) := by simp [hbOut]
          rcases bOut with ⟨r1, mid⟩
          dsimp only at hrem bRun ⊢
          have hlt : mid.clock < k := by change mid.clock ≤ st.clock - 1 at hrem; omega
          cases r1 with
          | none => exact ih mid.clock hlt mid rfl
          | some r1' =>
            cases r1' with
            | «continue» => exact ih mid.clock hlt mid rfl
            | «break» => simp
            | _ => simp
      · simp
    · simp

def noContBreak : ProgHOL 64 → Bool
  | .skip => true
  | .annot _ _ => true
  | .assign _ _ _ => true
  | .store _ _ => true
  | .store32 _ _ => true
  | .storeByte _ _ => true
  | .return _ => true
  | .raise _ _ => true
  | .while _ _ => true
  | .call (some (_, none)) _ _ => true
  | .call none _ _ => true
  | .seq p1 p2 => noContBreak p1 && noContBreak p2
  | .ite _ p1 p2 => noContBreak p1 && noContBreak p2
  | .dec _ _ _ b => noContBreak b
  | .decCall _ _ _ _ c => noContBreak c
  | _ => false

theorem noContBreak_sound : ∀ (p : ProgHOL 64), noContBreak p = true →
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s p).1 ≠ some .continue ∧
      (evaluateHOLFiniteState s p).1 ≠ some .break
  | .skip, _, _, s => no_cont_break_skip s
  | .annot _ _, _, _, _ => by simp
  | .assign k n e, _, _, s => no_cont_break_assign k n e s
  | .store a v, _, _, s => by
    rw [evaluateHOLFiniteState_store]
    repeat' split
    all_goals simp
  | .store32 a v, _, _, s => by
    rw [evaluateHOLFiniteState_store32]
    repeat' split
    all_goals simp
  | .storeByte a v, _, _, s => by
    rw [evaluateHOLFiniteState_storeByte]
    repeat' split
    all_goals simp
  | .return e, _, _, s => by
    rw [evaluateHOLFiniteState_return]
    repeat' split
    all_goals simp
  | .raise n e, _, _, s => by
    rw [evaluateHOLFiniteState_raise]
    repeat' split
    all_goals (try simp)
    all_goals (split_ifs <;> simp)
  | .while c b, _, _, s => no_cont_break_while c b s
  | .call none fn args, _, _, s => no_cont_break_call none (by intro h; simp) fn args s
  | .call (some (d, none)) fn args, _, _, s => no_cont_break_call (some (d, none)) (by intro h; simp) fn args s
  | .call (some (_, some _)) _ _, h, _, _ => by simp [noContBreak] at h
  | .seq p1 p2, h, _, s => by
    simp only [noContBreak, Bool.and_eq_true] at h
    exact no_cont_break_seq (noContBreak_sound p1 h.1) (noContBreak_sound p2 h.2) s
  | .ite c p1 p2, h, _, s => by
    simp only [noContBreak, Bool.and_eq_true] at h
    exact no_cont_break_ite (noContBreak_sound p1 h.1) (noContBreak_sound p2 h.2) s
  | .dec _ _ _ b, h, _, s => no_cont_break_dec (noContBreak_sound b h) s
  | .decCall _ _ _ _ c, h, _, s => no_cont_break_decCall (noContBreak_sound c h) s
  | .break, h, _, _ => by simp [noContBreak] at h
  | .continue, h, _, _ => by simp [noContBreak] at h
  | .primitive _ _ _, h, _, _ => by simp [noContBreak] at h
  | .extCall _ _ _ _ _, h, _, _ => by simp [noContBreak] at h
  | .shMemLoad _ _ _ _, h, _, _ => by simp [noContBreak] at h
  | .shMemStore _ _ _, h, _, _ => by simp [noContBreak] at h

theorem hoare_ite_requests_append {c : Nat} (hc : c < 8)
    (wra : WorldKeeps ReqRoom (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 72, 80])]
      ReqCountInc (ofString "requests_append"))
    (cond : ExpHOL 64) (args : List (ExpHOL 64)) :
    Hoare (ReqState c) (.ite cond (.call (some (none, none)) (ofString "requests_append") args) .skip)
      (fun r t => r = none → ReqState (c + 1) t) := by
  apply Hoare.ite_fall
  · apply Hoare.mono _ (fun _ h => h.1)
    exact Hoare.call0 wra
      (callEntryOn_of_imp (fun s locals k ⟨hW, hr⟩ => ⟨localsFree_worldOK s locals k hW, hr⟩)
        (fun _ h => reqState_reqRoom hc h) _ _)
      (fun s _ post v _ ⟨hW, hbo_nz, hc_le⟩ hq _ => by
        have hws := hq (Or.inl ⟨v, rfl⟩)
        obtain ⟨hAp, _, hG, _, hWS⟩ := hws
        obtain ⟨_, S, hS⟩ := hW
        obtain ⟨Nd, hWT⟩ := (worldTyped_iff_with s S).1 hS
        obtain ⟨S', Nd', _, hWT', _, _, hinc⟩ :=
          hWS S Nd ((worldTypedWith_with_locals _ _ _ _ _).2 hWT) (fun x hx => by simp at hx)
        have hbo_eq : globN post "bo" = globN s "bo" := by
          unfold globN; rw [← hG (ofString "bo") (by simp; decide)]; rfl
        have hinc' : memW post (globN s "bo" + 64) = memW s (globN s "bo" + 64) + 1 := hinc
        refine localsFree_reqState (c + 1) post s.locals post.clock
          ⟨⟨hAp, S', (worldTyped_iff_with post S').2 ⟨Nd', hWT'⟩⟩, ?_, ?_⟩
        · rw [hbo_eq]; exact hbo_nz
        · rw [hbo_eq, hinc']; omega)
      (fun _ _ hr _ h => absurd h hr)
  · exact Hoare.skip fun _ h _ => reqState_mono (Nat.le_succ c) h.1

theorem resumeOn_process_checked_sys_tx {c : Nat}
    (wpcs : WorldKeeps WorldOK
      (fun s => [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
                 (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
                 (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352),
                 (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384),
                 (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32),
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
                 (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
       ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "process_checked_system_transaction"))
    (name : MlS) (args : List (ExpHOL 64)) :
    DecCallResumeOn (ReqState c) (ReqState c) name (ofString "process_checked_system_transaction") args := by
  intro F state values body callee ret value post hcode ⟨hW, hbo_nz, hc_le⟩ _ hl hrun
  obtain ⟨hAs, S, hS⟩ := hW
  obtain ⟨Nd, hWT⟩ := (worldTyped_iff_with state S).1 hS
  have hstep := FunSpec.at_lookup wpcs state hcode values body callee ret hl
    (localsFree_worldOK state callee (state.clock - 1) ⟨hAs, S, hS⟩) (by rw [hrun]; simp)
  rw [hrun] at hstep; dsimp only at hstep
  obtain ⟨hAp, _, hG, hRK, hWS⟩ := hstep (Or.inl ⟨value, rfl⟩)
  have hdisj_R : ∀ {F2 : Type} (st : PanSemStateFiniteExact 64 F2),
      WorldTypedWith st S Nd →
      IvlsDisj
        [(globN st "b2_v", if globN st "b2_v" = 0 then 0 else 128),
         (globN st "bal_key_buf", if globN st "bal_key_buf" = 0 then 0 else 64),
         (globN st "bn_expw", if globN st "bn_expw" = 0 then 0 else 352),
         (globN st "bn_gamma", if globN st "bn_gamma" = 0 then 0 else 384),
         (globN st "evm_key_buf", if globN st "evm_key_buf" = 0 then 0 else 32),
         (globN st "keccak_pad", if globN st "keccak_pad" = 0 then 0 else 136),
         (globN st "keccak_st", if globN st "keccak_st" = 0 then 0 else 200),
         (globN st "mpt_nib_scratch", if globN st "mpt_nib_scratch" = 0 then 0 else 64),
         (globN st "pre_hdr_buf", if globN st "pre_hdr_buf" = 0 then 0 else 96),
         (globN st "rmd_h", if globN st "rmd_h" = 0 then 0 else 40),
         (globN st "rmd_pad", if globN st "rmd_pad" = 0 then 0 else 128),
         (globN st "rmd_x", if globN st "rmd_x" = 0 then 0 else 128),
         (globN st "sha_pad", if globN st "sha_pad" = 0 then 0 else 128),
         (globN st "sha_st", if globN st "sha_st" = 0 then 0 else 64),
         (globN st "sk_buf", if globN st "sk_buf" = 0 then 0 else 52),
         (globN st "u256_ws", if globN st "u256_ws" = 0 then 0 else 640)]
        (worldTypedIvls st S Nd) := by
    intro F2 st hWT_st i hi j hj
    change i ∈ [bufferRegion st ("b2_v", 128), bufferRegion st ("bal_key_buf", 64),
      bufferRegion st ("bn_expw", 352), bufferRegion st ("bn_gamma", 384),
      bufferRegion st ("evm_key_buf", 32), bufferRegion st ("keccak_pad", 136),
      bufferRegion st ("keccak_st", 200), bufferRegion st ("mpt_nib_scratch", 64),
      bufferRegion st ("pre_hdr_buf", 96), bufferRegion st ("rmd_h", 40),
      bufferRegion st ("rmd_pad", 128), bufferRegion st ("rmd_x", 128),
      bufferRegion st ("sha_pad", 128), bufferRegion st ("sha_st", 64),
      bufferRegion st ("sk_buf", 52), bufferRegion st ("u256_ws", 640)] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bufferRegion_disj_le hWT_st ("b2_v", 128) (by decide) (by decide) 128 le_rfl j hj
    · exact bufferRegion_disj_le hWT_st ("bal_key_buf", 64) (by decide) (by decide) 64 le_rfl j hj
    · exact bufferRegion_disj_le hWT_st ("bn_expw", 352) (by decide) (by decide) 352 le_rfl j hj
    · exact bufferRegion_disj_le hWT_st ("bn_gamma", 384) (by decide) (by decide) 384 le_rfl j hj
    · exact bufferRegion_disj_le hWT_st ("evm_key_buf", 32) (by decide) (by decide) 32 le_rfl j hj
    · exact bufferRegion_disj_le hWT_st ("keccak_pad", 136) (by decide) (by decide) 136 le_rfl j hj
    · exact bufferRegion_disj_le hWT_st ("keccak_st", 200) (by decide) (by decide) 200 le_rfl j hj
    · exact bufferRegion_disj_le hWT_st ("mpt_nib_scratch", 64) (by decide) (by decide) 64 le_rfl j hj
    · exact bufferRegion_disj_le hWT_st ("pre_hdr_buf", 96) (by decide) (by decide) 96 le_rfl j hj
    · exact bufferRegion_disj_le hWT_st ("rmd_h", 40) (by decide) (by decide) 40 le_rfl j hj
    · exact bufferRegion_disj_le hWT_st ("rmd_pad", 128) (by decide) (by decide) 128 le_rfl j hj
    · exact bufferRegion_disj_le hWT_st ("rmd_x", 128) (by decide) (by decide) 128 le_rfl j hj
    · exact bufferRegion_disj_le hWT_st ("sha_pad", 128) (by decide) (by decide) 128 le_rfl j hj
    · exact bufferRegion_disj_le hWT_st ("sha_st", 64) (by decide) (by decide) 64 le_rfl j hj
    · exact bufferRegion_disj_le hWT_st ("sk_buf", 64) (by decide) (by decide) 52 (by decide) j hj
    · exact bufferRegion_disj_le hWT_st ("u256_ws", 640) (by decide) (by decide) 640 le_rfl j hj
  have hWT_entry := (worldTypedWith_with_locals state callee (state.clock - 1) S Nd).2 hWT
  obtain ⟨S', Nd', _, hWT', _, _, _⟩ := hWS S Nd hWT_entry (hdisj_R _ hWT_entry)
  have hbo_eq : globN post "bo" = globN state "bo" := by
    unfold globN; rw [← hG (ofString "bo") (by simp; decide)]; rfl
  have hbo_ti : (globN state "bo", 88) ∈ worldTypedIvls state S Nd := by
    unfold worldTypedIvls
    apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
    apply List.mem_append.2; left; apply List.mem_append.2; right
    have hr_in : ("bo", 88) ∈ typedRecords := by decide
    have hm : (globN state "bo", if globN state "bo" = 0 then 0 else 88) ∈
        typedRecords.map (fun r => (globN state r.1, if globN state r.1 = 0 then 0 else r.2)) :=
      List.mem_map.2 ⟨("bo", 88), hr_in, rfl⟩
    rw [if_neg hbo_nz] at hm
    exact hm
  have hbo8 : (globN state "bo") % 8 = 0 := by
    have hfix := typedRecord_mem_fixedObjects state (show ("bo", 88) ∈ typedRecords by decide)
    rw [if_neg hbo_nz] at hfix
    rcases hWT.2.2.1.1 _ hfix with hz | ⟨_, hw⟩
    · dsimp at hz; omega
    · exact hw.1
  have hc64_eq : memW post (globN state "bo" + 64) = memW state (globN state "bo" + 64) := by
    apply hRK ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp) hbo_nz 64 (by simp)
    intro i hi
    dsimp only at hi ⊢
    change ¬ CellHits (globN state "bo" + 64) i
    have hi_z : i.2 = 0 → i.1 % 8 = 0 := by
      change i ∈ [bufferRegion state ("b2_v", 128), bufferRegion state ("bal_key_buf", 64),
        bufferRegion state ("bn_expw", 352), bufferRegion state ("bn_gamma", 384),
        bufferRegion state ("evm_key_buf", 32), bufferRegion state ("keccak_pad", 136),
        bufferRegion state ("keccak_st", 200), bufferRegion state ("mpt_nib_scratch", 64),
        bufferRegion state ("pre_hdr_buf", 96), bufferRegion state ("rmd_h", 40),
        bufferRegion state ("rmd_pad", 128), bufferRegion state ("rmd_x", 128),
        bufferRegion state ("sha_pad", 128), bufferRegion state ("sha_st", 64),
        bufferRegion state ("sk_buf", 52), bufferRegion state ("u256_ws", 640)] at hi
      have hbuf0 : ∀ (g : String) (sz : Nat), sz ≠ 0 →
          (bufferRegion state (g, sz)).2 = 0 → (bufferRegion state (g, sz)).1 % 8 = 0 := by
        intro g sz hsz hz
        unfold bufferRegion at hz ⊢
        dsimp only at hz ⊢
        by_cases hg0 : globN state g = 0
        · rw [hg0]
        · rw [if_neg hg0] at hz; exact absurd hz hsz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hbuf0 _ _ (by omega)
    have hd_bo : Disj i (globN state "bo", 88) := hdisj_R state hWT i hi _ hbo_ti
    exact fun hch => not_cellHits_of_disj (by omega) (by omega) (by omega) hi_z ⟨by omega, by omega⟩ hd_bo.flip hch
  exact LocalsOnly.setVar (LocalsOnly.of_localsFree (localsFree_reqState c)) (by simp) value _
    (localsFree_reqState c post state.locals post.clock
      ⟨⟨hAp, S', (worldTyped_iff_with post S').2 ⟨Nd', hWT'⟩⟩,
       by rw [hbo_eq]; exact hbo_nz,
       by rw [hbo_eq, hc64_eq]; exact hc_le⟩)

theorem dec_zero_on {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (name : MlS) {body : ProgHOL 64} {K : Nat}
    (hstep : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q (setVarHOLFinite name (.val (.word 0#64)) s))
    (hbody : TerminatingProgBoundedOn Q body K) :
    TerminatingProgBoundedOn P (.dec name .one (.const 0#64) body) K := by
  intro F s hcode hP
  unfold TerminatingRunBounded; dsimp only; intro hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  have hc0_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.const 0#64) =
      some (.val (.word 0#64)) := rfl
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0#64) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  dsimp only at hnt ⊢
  rw [hc0_ev] at hnt ⊢; dsimp only at hnt ⊢; rw [if_pos hsh0] at hnt ⊢
  have hb := hbody (setVarHOLFinite name (.val (.word 0#64)) s) hcode (hstep s hP) hnt
  simpa [setVarHOLFinite] using hb

theorem dec_eval_on {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (name : MlS) (sh : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64} {K : Nat}
    (hstep : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      P s → evalAt s init = some v → Q (setVarHOLFinite name v s))
    (hbody : TerminatingProgBoundedOn Q body K) :
    TerminatingProgBoundedOn P (.dec name sh init body) K := by
  intro F state hcode hP
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  revert hnt
  rcases he : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) init with _ | val
  · intro _; exact ⟨Nat.le_add_right state.clock K, Nat.le_refl _⟩
  · dsimp only
    split <;> intro hnt
    · have hb := hbody (setVarHOLFinite name val state) hcode (hstep state val hP he)
        (by simpa [setVarHOLFinite] using hnt)
      simpa [setVarHOLFinite] using hb
    · exact ⟨Nat.le_add_right state.clock K, Nat.le_refl _⟩

theorem prove_gbody_process_general_purpose_requests
    (hal : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (hed : TerminatingFunBoundedOn GuestInv (ofString "extract_deposit_data") K.«extract_deposit_data»)
    (hmc : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»)
    (hmq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq»)
    (hpcs : TerminatingFunBoundedOn WorldOK (ofString "process_checked_system_transaction") K.«process_checked_system_transaction»)
    (hra : TerminatingFunBoundedOn GuestInv (ofString "requests_append") K.«requests_append»)
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc"))
    (wed : WorldKeeps WorldOK (fun s => [(locN s "out", 192)]) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "extract_deposit_data"))
    (wmc : WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")]) []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "memcpy"))
    (rmq : ReadOnlyFn (ofString "memeq"))
    (wpcs : WorldKeeps WorldOK
      (fun s => [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
                 (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
                 (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352),
                 (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384),
                 (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32),
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
                 (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
       ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "process_checked_system_transaction"))
    (wra : WorldKeeps ReqRoom (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 72, 80])]
      ReqCountInc (ofString "requests_append")) :
    TerminatingFunBoundedOn ReqsFresh (ofString "process_general_purpose_requests")
      K.«process_general_purpose_requests» := by
  refine ⟨_, _, _, lookup_process_general_purpose_requests, ?_⟩
  simp only [InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, List.map_cons, List.map_nil]
  -- Inner loop (`j < nl`)
  obtain ⟨hinner_hoare, hinner_bound⟩ :=
    walk_loop_general localsOnly_depLoopInv (fun _ h => depLoopInv_guestInv h)
      (elemName := "log") (baseName := "lp") (idxName := "j")
      (by simp; decide) (by decide) (by decide)
      (walk_decCall_step localsOnly_depLoopInv (by simp; decide) (by decide) (by decide)
        (resumeOn_memeq_depLoopInv rmq (ofString "isdep") (by simp; decide)
          [.load .one (.op .add [.var .local (ofString "log"), .const 0#64]),
           .var .global (ofString "deposit_contract_address"), .const 20#64])
        (walk_seq_inc_step localsOnly_depLoopInv (by simp; decide) (by decide)
          (by decide) (by decide) (noContBreak_sound _ (by decide))
          (hoare_dep_inner_after_isdep wal rtal wed wmc rmq)))
      (TerminatingProgBoundedOn.decCall_on hmq (ofString "isdep") .one
        [.load .one (.op .add [.var .local (ofString "log"), .const 0#64]),
         .var .global (ofString "deposit_contract_address"), .const 20#64]
        (callEntryOn_of_imp localsFree_guestInv (fun _ h => depLoopInv_guestInv h) _ _)
        (resumeOn_memeq_depLoopInv rmq (ofString "isdep") (by simp; decide) _)
        (TerminatingProgBoundedOn.seq_guestInv_after
          (bounded_dep_inner_after_isdep hal hed hmc hmq wal rtal wmc rmq)
          (fun _ h => depLoopInv_guestInv h)
          (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))))
      "nl"
  -- Outer loop (`i < nr`)
  obtain ⟨houter_hoare, houter_bound⟩ :=
    walk_loop_general localsOnly_depLoopInv (fun _ h => depLoopInv_guestInv h)
      (elemName := "logs") (baseName := "rp") (idxName := "i")
      (by simp; decide) (by decide) (by decide)
      (walk_dec_step (name := ofString "nl") (sh := .one)
        (init := .load .one (.op .add [.var .local (ofString "logs"), .const 8#64]))
        localsOnly_depLoopInv (by simp; decide) (by decide) (by decide)
        (walk_dec_step (name := ofString "lp") (sh := .one)
          (init := .load .one (.op .add [.var .local (ofString "logs"), .const 0#64]))
          localsOnly_depLoopInv (by simp; decide) (by decide) (by decide)
          (walk_dec_step (name := ofString "j") (sh := .one) (init := .const 0#64)
            localsOnly_depLoopInv (by simp; decide) (by decide) (by decide)
            (walk_seq_inc_step localsOnly_depLoopInv (by simp; decide) (by decide)
              (by decide) (by decide) (noContBreak_sound _ (by decide))
              hinner_hoare))))
      (TerminatingProgBoundedOn.dec_onLocals localsOnly_depLoopInv (ofString "nl") (by simp; decide) .one
        (.load .one (.op .add [.var .local (ofString "logs"), .const 8#64]))
        (TerminatingProgBoundedOn.dec_onLocals localsOnly_depLoopInv (ofString "lp") (by simp; decide) .one
          (.load .one (.op .add [.var .local (ofString "logs"), .const 0#64]))
          (TerminatingProgBoundedOn.dec_onLocals localsOnly_depLoopInv (ofString "j") (by simp; decide) .one (.const 0#64)
            (TerminatingProgBoundedOn.seq_guestInv_after
              hinner_bound
              (fun _ h => depLoopInv_guestInv h)
              (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))))))
      "nr"
  -- Post-loop tail: `ReqState 0` -> `ReqState 1` -> ... -> `ReqState 5`
  have hite_ra_bound : ∀ (c : Nat) (cond : ExpHOL 64) (args : List (ExpHOL 64)),
      TerminatingProgBoundedOn (ReqState c)
        (.ite cond (.call (some (none, none)) (ofString "requests_append") args) .skip)
        (Nat.max (K.«requests_append» + 1) 0) :=
    fun c cond args =>
      TerminatingProgBoundedOn.ite_on
        (TerminatingProgBoundedOn.call_on hra _ _
          (callEntryOn_of_imp localsFree_guestInv (fun _ h => reqState_guestInv h) _ _))
        (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s))
  -- Assemble the full body from `ReqsFresh`:
  -- First `dec "rls"` transitions `ReqsFresh` -> `ReqState 0` when init succeeds!
  set P_dep0 : ∀ {F2 : Type}, PanSemStateFiniteExact 64 F2 → Prop :=
    fun s => ∃ w_dep : BitVec 64, ∃ S Nd : List Nat,
      WorldTypedWith s S Nd ∧ ArenaReady s ∧ globN s "bo" ≠ 0 ∧ memW s (globN s "bo" + 64) = 0 ∧
      s.locals.lookup (ofString "dep") = some (.val (.word w_dep)) ∧
      w_dep.toNat % 8 = 0 ∧
      Inside (w_dep.toNat, 8) sourceBase (globN s "heap_ptr") ∧
      IvlsDisj [(w_dep.toNat, 8)] (worldOwned s S Nd)
  set P_dep1 : ∀ {F2 : Type}, PanSemStateFiniteExact 64 F2 → Prop :=
    fun s => ∃ w_dep : BitVec 64, ∃ S Nd : List Nat,
      WorldTypedWith s S Nd ∧ ArenaReady s ∧ globN s "bo" ≠ 0 ∧ memW s (globN s "bo" + 64) = 0 ∧
      s.locals.lookup (ofString "dep") = some (.val (.word w_dep)) ∧
      s.locals.lookup (ofString "dep_n") = some (.val (.word 0#64)) ∧
      w_dep.toNat % 8 = 0 ∧
      Inside (w_dep.toNat, 8) sourceBase (globN s "heap_ptr") ∧
      IvlsDisj [(w_dep.toNat, 8)] (worldOwned s S Nd)
  intro F state hcode hRF hnt
  exact TerminatingRunBounded.weaken
    (K' := K.«process_general_purpose_requests»)
    ((dec_eval_on (P := ReqsFresh) (Q := ReqState 0)
      (ofString "rls") .one (.load .one (.op .add [.var .global (ofString "bo"), .const 72#64]))
      dec_rls_reqsFresh_to_reqState0
      (TerminatingProgBoundedOn.dec_on (localsFree_reqState 0)
        (ofString "nr") .one (.load .one (.op .add [.var .local (ofString "rls"), .const 8#64]))
        (TerminatingProgBoundedOn.dec_on (localsFree_reqState 0)
          (ofString "rp") .one (.load .one (.op .add [.var .local (ofString "rls"), .const 0#64]))
          (TerminatingProgBoundedOn.decCall_on hal (ofString "dep") .one [.const 8#64]
            (callEntryOn_of_imp localsFree_guestInv (fun _ h => reqState_guestInv h) _ _)
            (resumeOn_init_dep_alloc wal rtal)
            (dec_zero_on (P := P_dep0) (Q := P_dep1) (ofString "dep_n")
              (fun s2 hP0 => by
                obtain ⟨w_dep, S, Nd, hWT, hA, hbo, hc0, hld, hd8, hin, hdj⟩ := hP0
                exact ⟨w_dep, S, Nd,
                  (worldTypedWith_with_locals s2 _ s2.clock S Nd).2 hWT,
                  localsFree_arenaReady s2 _ s2.clock hA, hbo, hc0,
                  by have hne : ofString "dep_n" ≠ ofString "dep" := by decide
                     simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, hld],
                  by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
                  hd8, hin, hdj⟩)
              (dec_zero_on (P := P_dep1) (Q := DepLoopInv) (ofString "dep_cap")
                (fun s2 hP1 => by
                  obtain ⟨w_dep, S, Nd, hWT, hA, hbo, hc0, hld, hln, hd8, hin, _⟩ := hP1
                  exact ⟨w_dep, 0#64, 0#64, S, Nd,
                    (worldTypedWith_with_locals s2 _ s2.clock S Nd).2 hWT,
                    localsFree_arenaReady s2 _ s2.clock hA, hbo, hc0,
                    by have hne : ofString "dep_cap" ≠ ofString "dep" := by decide
                       simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, hld],
                    by have hne : ofString "dep_cap" ≠ ofString "dep_n" := by decide
                       simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, hln],
                    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
                    by decide, hd8, by decide, by decide,
                    ⟨hin.1, by change w_dep.toNat + 0 ≤ globN s2 "heap_ptr"; unfold Inside at hin; omega⟩,
                    fun x hx _ _ => by simp only [List.mem_singleton] at hx; subst hx; exact Or.inl rfl⟩)
                (TerminatingProgBoundedOn.dec_onLocals localsOnly_depLoopInv (ofString "i") (by simp; decide) .one (.const 0#64)
                  (TerminatingProgBoundedOn.seq_hoare_trans
                    houter_bound
                    ⟨fun s3 hc3 hI3 hnt3 hr3 => depLoopInv_reqState0 (houter_hoare.run s3 hc3 hI3 hnt3 hr3)⟩
                    (TerminatingProgBoundedOn.seq_hoare_trans
                      (hite_ra_bound 0 _ _)
                      (hoare_ite_requests_append (c := 0) (by omega) wra _ _)
                      (TerminatingProgBoundedOn.decCall_on hpcs (ofString "o1") .one _
                        (callEntryOn_of_imp localsFree_worldOK (fun _ h => reqState_worldOK h) _ _)
                        (resumeOn_process_checked_sys_tx (c := 1) wpcs _ _)
                        (TerminatingProgBoundedOn.seq_hoare_trans
                          (hite_ra_bound 1 _ _)
                          (hoare_ite_requests_append (c := 1) (by omega) wra _ _)
                          (TerminatingProgBoundedOn.decCall_on hpcs (ofString "o2") .one _
                            (callEntryOn_of_imp localsFree_worldOK (fun _ h => reqState_worldOK h) _ _)
                            (resumeOn_process_checked_sys_tx (c := 2) wpcs _ _)
                            (TerminatingProgBoundedOn.seq_hoare_trans
                              (hite_ra_bound 2 _ _)
                              (hoare_ite_requests_append (c := 2) (by omega) wra _ _)
                              (TerminatingProgBoundedOn.decCall_on hpcs (ofString "o3") .one _
                                (callEntryOn_of_imp localsFree_worldOK (fun _ h => reqState_worldOK h) _ _)
                                (resumeOn_process_checked_sys_tx (c := 3) wpcs _ _)
                                (TerminatingProgBoundedOn.seq_hoare_trans
                                  (hite_ra_bound 3 _ _)
                                  (hoare_ite_requests_append (c := 3) (by omega) wra _ _)
                                  (TerminatingProgBoundedOn.decCall_on hpcs (ofString "o4") .one _
                                    (callEntryOn_of_imp localsFree_worldOK (fun _ h => reqState_worldOK h) _ _)
                                    (resumeOn_process_checked_sys_tx (c := 4) wpcs _ _)
                                    (TerminatingProgBoundedOn.seq_guestInv_after
                                      (hite_ra_bound 4 _ _)
                                      (fun _ h => reqState_guestInv h)
                                      (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))))))))))))))))))
      state hcode hRF)
    (by
      unfold K.«process_general_purpose_requests»
      simp only [show ∀ a b : Nat, Nat.max a b = max a b from fun _ _ => rfl]
      omega)
    hnt


theorem «gbody_process_general_purpose_requests» : GBody.«process_general_purpose_requests» :=
  prove_gbody_process_general_purpose_requests

end InitECandidate.Solver.Wave8GuestInv.R16Shards
