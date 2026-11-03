import InitECandidate.Solver.Wave8GuestInv.ContractParts.C07
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M11.WorldLemmas
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.StoreAllocHelpers
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M14.ro_heap_mark
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M14.ro_check_gas_limit
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_memeq
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_htab_get
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_htab_item
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.ro_u256_eq
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_u256_is_zero
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_u256_sub
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_u256_mul
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M25.nz_htab_set
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M27.TeNewSupport
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M27.rv_u256_to_be_min
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M27.rv_rlp_encode_bytes

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.Fast_C08WkShard06

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## Shared Helpers -/

theorem evaluate_guestInv_be {F : Type}
    (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64) (hG : GuestInv s) :
    GuestInv (evaluateHOLFiniteState s p).2 ∧ (evaluateHOLFiniteState s p).2.be = s.be := by
  have inv := evaluateInvariantsHOLFinite p
    (PanPropsEvalStateFiniteExact.ofPanSemFinite s)
    (evaluateHOLFiniteState s p).1
    (PanPropsEvalStateFiniteExact.ofPanSemFinite (evaluateHOLFiniteState s p).2)
    (by simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
          PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite])
  exact ⟨⟨inv.2.2.2.2.2.2.1.trans hG.code, inv.1.trans hG.memaddrs,
          inv.2.1.trans hG.shMemaddrs, inv.2.2.2.2.1.trans hG.baseAddr⟩, inv.2.2.1⟩

theorem not_resumes_error : ¬ Resumes (some (.error : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

theorem globWord_of_pos {F : Type} (s : PanSemStateFiniteExact 64 F) (name : String)
    (hpos : 0 < globN s name) :
    ∃ w : BitVec 64, s.globals.lookup (ofString name) = some (.val (.word w)) ∧
      w.toNat = globN s name := by
  unfold globN at hpos ⊢
  rcases hg : s.globals.lookup (ofString name) with _ | v
  · simp [hg] at hpos
  · rcases v with ⟨⟨w⟩⟩ | _ | _
    · exact ⟨w, rfl, by simp [hg]⟩
    · simp [hg] at hpos
    · simp [hg] at hpos

theorem globWord_of_arenaOK {F : Type} (s : PanSemStateFiniteExact 64 F) (hA : ArenaOK s)
    (name : String) (hmem : name ∈ guestGlobalNames) :
    ∃ w : BitVec 64, s.globals.lookup (ofString name) = some (.val (.word w)) ∧
      w.toNat = globN s name := by
  obtain ⟨w, hw⟩ := hA.2.2.2.2.2.2.2.2 name hmem
  exact ⟨w, hw, by unfold globN; rw [hw]⟩

/-! ## 1. `wk_te_new` -/

private theorem alloc_only_trap_exn {F : Type} (st : PanSemStateFiniteExact 64 F)
    (hcode : st.code = originalRuntimeCode) (e : MlS) (v : ValueHOL 64)
    (hex : (evaluateHOLFiniteState st (sourceFnBody Guest.Software.guestFn_alloc)).1 =
      some (.exception e v)) :
    e = ofString "TrapErr" := by
  have hbody_eq : sourceFnBody Guest.Software.guestFn_alloc =
      .dec (ofString "p") .one (.var .global (ofString "heap_ptr"))
        (.seq
          (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const (BitVec.ofNat 64 6)])
            .skip)
          (.dec (ofString "q") .one
            (.op .and [.op .add [.var .local (ofString "p"),
                .op .add [.var .local (ofString "n"), .const (BitVec.ofNat 64 7)]],
              .op .sub [.const (BitVec.ofNat 64 0), .const (BitVec.ofNat 64 8)]])
            (.seq
              (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
                (.call (some (none, none)) (ofString "trap_with") [.const (BitVec.ofNat 64 6)])
                .skip)
              (.seq
                (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "p"))))))) := rfl
  have htrap : ∀ (t : PanSemStateFiniteExact 64 F), t.code = originalRuntimeCode →
      (evaluateHOLFiniteState t (.call (some (none, none)) (ofString "trap_with") [.const (BitVec.ofNat 64 6)])).1 =
        some (.exception e v) → e = ofString "TrapErr" := by
    intro t htc ht
    by_contra hne
    have hres : Resumes (some (.exception e v)) := Or.inr ⟨e, v, rfl, hne⟩
    rw [← ht] at hres
    rw [evaluateHOLFiniteState_call] at ht
    have hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) [.const 6#64] =
        some [.val (.word 6#64)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
    have hlk := pan_one_word_lookup t.code.lookup (ofString "trap_with") (ofString "code")
      (sourceFnBody Guest.Software.guestFn_trap_with) 6#64 (by rw [htc]; exact lookup_trap_with)
    rw [hargs] at ht; dsimp only at ht; rw [hlk] at ht; dsimp only at ht
    split at ht
    · simp at ht
    · have hout := InitECandidate.Solver.GuestTrapOutcomes.evaluate_trap_with_body_outcomes
        (callEntryStateHOLFinite t (HolFiniteMapExact.empty.update (ofString "code", .val (.word 6#64))))
      rcases hb : evaluateHOLFiniteState
        (callEntryStateHOLFinite t (HolFiniteMapExact.empty.update (ofString "code", .val (.word 6#64))))
        (sourceFnBody Guest.Software.guestFn_trap_with) with ⟨rb, sb⟩
      rw [hb] at hout ht
      cases rb with
      | none => exact absurd rfl hout.1
      | some r' =>
        cases r' with
        | returned rv => exact absurd rfl (hout.2.1 rv)
        | exception eid ev =>
          dsimp only at ht
          injection ht with ht'; injection ht' with he1 he2
          subst he1 he2
          exact absurd rfl (hout.2.2 e v hne)
        | _ => simp at ht
  rw [hbody_eq, evaluateHOLFiniteState_dec_total] at hex
  dsimp only at hex
  split at hex
  · simp at hex
  · split at hex
    · rename_i val _ _
      set s1 := setVarHOLFinite (ofString "p") val st
      rw [evaluateHOLFiniteState_seq_line780] at hex
      rcases hr1 : evaluateHOLFiniteState s1
        (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 6#64]) .skip) with ⟨r1, m1⟩
      rw [hr1] at hex
      cases r1 with
      | some r1' =>
        dsimp only at hex
        rw [evaluateHOLFiniteState_ite] at hr1
        split at hr1
        · split at hr1
          · rw [evaluateHOLFiniteState_skip] at hr1; injection hr1 with h1 _; cases h1
          · exact htrap s1 hcode (hr1.trans (congrArg (fun x => (x, m1)) hex))
        · injection hr1 with h1 _; subst h1; simp at hex
      | none =>
        dsimp only at hex
        have hm1_code : m1.code = originalRuntimeCode :=
          (PanRunBounded.evaluateHOLFiniteState_metadata s1 _).1 |> fun hc => by rw [hr1] at hc; exact hc.trans hcode
        rw [evaluateHOLFiniteState_dec_total] at hex
        dsimp only at hex
        split at hex
        · simp at hex
        · split at hex
          · rename_i qv _ _
            set s2 := setVarHOLFinite (ofString "q") qv m1
            rw [evaluateHOLFiniteState_seq_line780] at hex
            rcases hr2 : evaluateHOLFiniteState s2
              (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
                (.call (some (none, none)) (ofString "trap_with") [.const 6#64]) .skip) with ⟨r2, m2⟩
            rw [hr2] at hex
            cases r2 with
            | some r2' =>
              dsimp only at hex
              rw [evaluateHOLFiniteState_ite] at hr2
              split at hr2
              · split at hr2
                · rw [evaluateHOLFiniteState_skip] at hr2; injection hr2 with h1 _; cases h1
                · exact htrap s2 hm1_code (hr2.trans (congrArg (fun x => (x, m2)) hex))
              · injection hr2 with h1 _; subst h1; simp at hex
            | none =>
              dsimp only at hex
              rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign] at hex
              split at hex
              · simp at hex
              · split at hex
                · dsimp only at hex
                  rw [evaluateHOLFiniteState_return] at hex
                  split at hex
                  · simp at hex
                  · split at hex <;> simp at hex
                · simp at hex
          · simp at hex
    · simp at hex

private theorem memzero_no_exn {F : Type} (st : PanSemStateFiniteExact 64 F)
    (e : MlS) (v : ValueHOL 64) :
    (evaluateHOLFiniteState st (sourceFnBody Guest.Software.guestFn_memzero)).1 ≠
      some (.exception e v) := by
  have hno : ∀ (p : ProgHOL 64), InitECandidate.Solver.GuestTrapOutcomes.noExnCallsOrRaise p = true →
      ∀ (t : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState t p).1 ≠ some (.exception e v) :=
    fun p hp t => InitECandidate.Solver.GuestTrapOutcomes.evaluate_no_exception_of_syntactic p hp t e v
  exact hno _ rfl st

private theorem te_new_resumes_returned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFunctionEntry Guest.Software.guestFn_te_new).2.2.1).1) :
    ∃ v, (evaluateHOLFiniteState s (sourceFunctionEntry Guest.Software.guestFn_te_new).2.2.1).1 =
      some (.returned v) := by
  rcases hres with hret | ⟨e, v, hex, hne⟩
  · exact hret
  · exfalso; apply hne
    dsimp only [sourceFunctionEntry, Guest.Software.guestFn_te_new,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
      Option.map, List.map] at hex
    rw [evaluateHOLFiniteState_decCall_total] at hex
    have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.const 200#64] =
        some [.val (.word 200#64)] := by
      rw [evalListHOLFinite_eq_toExact]; rfl
    rw [hargs] at hex; dsimp only at hex
    have hlk := pan_one_word_lookup s.code.lookup (ofString "alloc") (ofString "n")
      (sourceFnBody Guest.Software.guestFn_alloc) 200#64
      (by rw [hcode]; exact Wave8Contracts.M27.lookup_alloc_te)
    rw [hlk] at hex; dsimp only at hex
    split at hex
    · simp at hex
    · rw [fixClockHOLFinite_evaluateState] at hex
      rcases ha : evaluateHOLFiniteState
        (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word 200#64))))
        (sourceFnBody Guest.Software.guestFn_alloc) with ⟨ra, pa⟩
      have ha' : evaluateHOLFiniteState
        (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word 200#64))))
        (sourceFnBody Guest.Software.guestFn_alloc) = (ra, pa) := ha
      rw [ha'] at hex; dsimp only at hex
      cases ra with
      | none => simp at hex
      | some ra' =>
        cases ra' with
        | exception ea va =>
          dsimp only at hex
          injection hex with hex'; injection hex' with he1 _
          subst he1
          exact alloc_only_trap_exn _ hcode ea va (by rw [ha'])
        | returned rva =>
          dsimp only at hex
          split at hex
          · set s1 := setVarHOLFinite (ofString "te") rva { pa with locals := s.locals }
            have hs1_code : s1.code = originalRuntimeCode := by
              have hpac := (PanRunBounded.evaluateHOLFiniteState_metadata
                (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word 200#64))))
                (sourceFnBody Guest.Software.guestFn_alloc)).1
              rw [ha'] at hpac
              exact hpac.trans hcode
            rw [evaluateHOLFiniteState_seq_line780] at hex
            rcases hmz : evaluateHOLFiniteState s1
              (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "te"), .const 200#64]) with ⟨rmz, pmz⟩
            rw [hmz] at hex
            cases rmz with
            | none =>
              dsimp only at hex
              rw [evaluateHOLFiniteState_return] at hex
              split at hex
              · simp at hex
              · split at hex <;> simp at hex
            | some rmz' =>
              dsimp only at hex
              injection hex with hex'; subst hex'
              rw [evaluateHOLFiniteState_call] at hmz
              split at hmz
              · simp at hmz
              · split at hmz
                · simp at hmz
                · rename_i vs _ body' callee' ret' hlk_mz
                  have hsame := lookupCodeHOLFinite_installed_body s1.code.lookup (ofString "memzero")
                    _ (sourceFnBody Guest.Software.guestFn_memzero) body' _ ret' vs callee'
                    (by rw [hs1_code]; exact Wave8Contracts.M27.lookup_memzero) hlk_mz
                  subst hsame
                  split at hmz
                  · simp at hmz
                  · rcases hmb : evaluateHOLFiniteState (callEntryStateHOLFinite s1 callee')
                      (sourceFnBody Guest.Software.guestFn_memzero) with ⟨rmb, pmb⟩
                    have hne_ex := memzero_no_exn (callEntryStateHOLFinite s1 callee') e v
                    rw [hmb] at hmz hne_ex
                    cases rmb with
                    | none => simp at hmz
                    | some rmb' =>
                      cases rmb' with
                      | returned _ => dsimp only at hmz; split at hmz <;> simp at hmz
                      | exception eb vb =>
                        dsimp only at hmz
                        injection hmz with h1 _; injection h1 with h2; injection h2 with h3 h4
                        subst h3 h4; exact absurd rfl hne_ex
                      | _ => simp at hmz
          · simp at hmz ⊢; simp at hex
        | _ => simp at hex

private theorem zeroBlock25_eq_outside (m : BitVec 64 → HolWordLab 64) (hp a : BitVec 64)
    (hp_align : hp.toNat % 8 = 0) (hp_hi : hp.toNat + 200 ≤ 2 ^ 64)
    (hout : a.toNat % 8 ≠ 0 ∨ ¬ (hp.toNat ≤ a.toNat ∧ a.toNat < hp.toNat + 200)) :
    Wave8Contracts.M27.zeroBlock25 m hp a = m a := by
  have hne_off : ∀ off : Nat, off < 200 → off % 8 = 0 → a ≠ hp + BitVec.ofNat 64 off := by
    intro off hoff hoff8 heq
    have hadd : (hp + BitVec.ofNat 64 off).toNat = hp.toNat + off := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [heq, hadd] at hout
    rcases hout with hna | hnr <;> omega
  have hadd_norm : ∀ (x y : BitVec 64), (hp + x) + y = hp + (x + y) := fun x y => BitVec.add_assoc hp x y
  unfold Wave8Contracts.M27.zeroBlock25 Wave8Contracts.M27.updW_te
  simp only [hadd_norm]
  rw [if_neg (hne_off 192 (by omega) (by omega)),
      if_neg (hne_off 184 (by omega) (by omega)), if_neg (hne_off 176 (by omega) (by omega)),
      if_neg (hne_off 168 (by omega) (by omega)), if_neg (hne_off 160 (by omega) (by omega)),
      if_neg (hne_off 152 (by omega) (by omega)), if_neg (hne_off 144 (by omega) (by omega)),
      if_neg (hne_off 136 (by omega) (by omega)), if_neg (hne_off 128 (by omega) (by omega)),
      if_neg (hne_off 120 (by omega) (by omega)), if_neg (hne_off 112 (by omega) (by omega)),
      if_neg (hne_off 104 (by omega) (by omega)), if_neg (hne_off 96 (by omega) (by omega)),
      if_neg (hne_off 88 (by omega) (by omega)),  if_neg (hne_off 80 (by omega) (by omega)),
      if_neg (hne_off 72 (by omega) (by omega)),  if_neg (hne_off 64 (by omega) (by omega)),
      if_neg (hne_off 56 (by omega) (by omega)),  if_neg (hne_off 48 (by omega) (by omega)),
      if_neg (hne_off 40 (by omega) (by omega)),  if_neg (hne_off 32 (by omega) (by omega)),
      if_neg (hne_off 24 (by omega) (by omega)),  if_neg (hne_off 16 (by omega) (by omega)),
      if_neg (hne_off 8 (by omega) (by omega)),   if_neg (hne_off 0 (by omega) (by omega))]

theorem «wk_te_new» :
    WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    (RetAvoids (fun _ _ w => [(w, 200)])) (ofString "te_new") := by
  refine ⟨_, (sourceFunctionEntry Guest.Software.guestFn_te_new).2.2.1, _,
    Wave8Contracts.M27.lookup_te_new, ?_⟩
  intro F s hcode hWOK _ _ hres
  obtain ⟨⟨hGI, hA⟩, S0, hWT0⟩ := hWOK
  obtain ⟨Nd0, hWTW0⟩ := (worldTyped_iff_with s S0).1 hWT0
  obtain ⟨retVal, hret_eq⟩ := te_new_resumes_returned s hcode hres
  have hsb : sourceBase = 2701131776 := rfl
  have hhl : heapLimit = 2952790016 := rfl
  have hss : scratchStart = 2952790016 := rfl
  obtain ⟨hp, hhp, hhp_eq⟩ := globWord_of_pos s "heap_ptr" (by have := hA.1; omega)
  have hp_align : hp.toNat % 8 = 0 := by rw [hhp_eq]; exact hA.2.2.2.2.2.1
  have hp_le_lim : hp.toNat ≤ 2952790016 := by rw [hhp_eq, ← hhl]; exact hA.2.1
  have hbe_post := (evaluate_guestInv_be s
    (sourceFunctionEntry Guest.Software.guestFn_te_new).2.2.1 hGI).2
  rcases hpair : evaluateHOLFiniteState s
      (sourceFunctionEntry Guest.Software.guestFn_te_new).2.2.1 with ⟨res, post⟩
  rw [hpair] at hret_eq hbe_post
  dsimp only at hret_eq hbe_post
  subst hret_eq
  have hdom_fn : ∀ (q : BitVec 64), q.toNat ≤ 2952790016 → q.toNat = hp.toNat + 200 →
      ∀ off : Nat, off < 200 → off % 8 = 0 → s.memaddrs (hp + BitVec.ofNat 64 off) := by
    intro q hq_le hq_nat off hoff hmod
    rw [hGI.memaddrs, M11.ordinaryDomain_iff]
    have hlo_hp : sourceBase ≤ hp.toNat := by rw [hhp_eq]; exact hA.1
    have hadd_nat : (hp + BitVec.ofNat 64 off).toNat = hp.toNat + off := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hadd_nat]
    exact ⟨by omega, by omega, by omega⟩
  obtain ⟨hv_eq, hq_nat, hq_le_num, hpost_mem, hpost_glob, hcode_p, hmem_p, hsh_p, hbase_p⟩ :=
    Wave8Contracts.M27.te_new_body_run s post hp retVal hcode hhp hp_align hp_le_lim hdom_fn hpair
  set q : BitVec 64 := (hp + (200#64 + 7#64)) &&& ((0 : BitVec 64) - 8)
  have hq_le : q.toNat ≤ heapLimit := by rw [hhl]; exact hq_le_num
  have hpost_gi : GuestInv post := guestInv_congr hcode_p hmem_p hsh_p hbase_p hGI
  have hg_other : ∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
      s.globals.lookup k = post.globals.lookup k := by
    intro k hk
    rw [hpost_glob]
    have hne : k ≠ ofString "heap_ptr" := fun h => hk (by simp [h])
    simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne]
  have hg_hp : globN post "heap_ptr" = q.toNat := by
    unfold globN; rw [hpost_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hg_fp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by
    unfold globN; rw [← hg_other _ (by decide)]
  have hg_sp : globN post "scratch_ptr" = globN s "scratch_ptr" := by
    unfold globN; rw [← hg_other _ (by decide)]
  have hAR_post : ArenaReady post := by
    refine ⟨hpost_gi, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      globalsWord_update (ofString "heap_ptr") q hpost_glob hA.2.2.2.2.2.2.2.2⟩
    · rw [hg_hp, hq_nat, hhp_eq]; have := hA.1; omega
    · rw [hg_hp]; exact hq_le
    · rw [hg_fp]; exact hA.2.2.1
    · rw [hg_fp, hg_sp]; exact hA.2.2.2.1
    · rw [hg_sp]; exact hA.2.2.2.2.1
    · rw [hg_hp, hq_nat]; omega
    · rw [hg_fp]; exact hA.2.2.2.2.2.2.1
    · rw [hg_sp]; exact hA.2.2.2.2.2.2.2.1
  have hhp_grow : globN s "heap_ptr" ≤ globN post "heap_ptr" := by
    rw [hg_hp, hq_nat, hhp_eq]; omega
  have hmem_unch : ∀ a : BitVec 64,
      (a.toNat % 8 ≠ 0 ∨ ¬ (hp.toNat ≤ a.toNat ∧ a.toNat < hp.toNat + 200)) →
      post.memory a = s.memory a := by
    intro a hout
    rw [hpost_mem]
    exact zeroBlock25_eq_outside s.memory hp a hp_align (by omega) hout
  have hdisj_alloc : ∀ i : Ivl, (i.2 = 0 ∨ Allocated s i) →
      ∀ b : Nat, i.1 ≤ b → b < i.1 + i.2 → ¬ (hp.toNat ≤ b ∧ b < hp.toNat + 200) := by
    intro i hi b hb1 hb2 ⟨h1, h2⟩
    rcases hi with h0 | ⟨_, hhi⟩ | ⟨hlo, _⟩
    · omega
    · rw [← hhp_eq] at hhi; omega
    · have := hA.2.2.1; have := hA.2.2.2.1; omega
  have hRK : RecordsKept (fun _ => []) M11.stdKeep s post := by
    intro rec hrec hgnz k hk _
    have hsz_ex : ∃ sz : Nat, (rec.1, sz) ∈ typedRecords ∧ k + 8 ≤ sz := by
      simp only [M11.stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · refine ⟨40, by decide, ?_⟩; simp at hk; omega
      · refine ⟨80, by decide, ?_⟩; simp at hk; omega
      · refine ⟨72, by decide, ?_⟩; simp at hk; omega
      · refine ⟨88, by decide, ?_⟩; simp at hk; omega
    obtain ⟨sz, htr, hkle⟩ := hsz_ex
    have hfix0 := M11.typedRec_in_fixedObjects s htr
    simp only [hgnz, ↓reduceIte] at hfix0
    rcases hWTW0.2.2.1.1 _ hfix0 with h0 | ⟨hal0, _⟩
    · dsimp only at h0; omega
    · have hb := M11.allocated_le_2pow64 hA hal0
      dsimp only at hb
      unfold memW
      have hbit : (BitVec.ofNat 64 (globN s rec.1 + k)).toNat = globN s rec.1 + k :=
        Nat.mod_eq_of_lt (by omega)
      rw [hmem_unch _ (Or.inr (by rw [hbit]; exact hdisj_alloc _ (Or.inr hal0) _ (by omega) (by omega)))]
  refine ⟨hAR_post, hhp_grow, hg_other, hRK, fun S Nd hWT _ => ?_⟩
  have hcell : M11.SameTypedCells s post S Nd := by
    refine ⟨hbe_post, hmem_p, hGI.memaddrs, ?_, ?_, ?_⟩
    · intro a hna
      apply hmem_unch a
      by_cases ha8 : a.toNat % 8 = 0
      · right
        intro ⟨h1, h2⟩
        apply hna
        rw [M11.ordinaryDomain_iff]
        have hlo_hp : sourceBase ≤ hp.toNat := by rw [hhp_eq]; exact hA.1
        exact ⟨by omega, by omega, ha8⟩
      · exact Or.inl ha8
    · intro a ha _ ⟨i, hi, ha1, ha2⟩
      have hbit : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
      exact hmem_unch _ (Or.inr (by
        rw [hbit]
        exact hdisj_alloc i (M11.worldTypedIvls_allocated hWT hi) a ha1 (by omega)))
    · intro b hb ⟨i, hi, hb1, hb2⟩
      unfold memB
      have hal_nat : (panByteAlignHOL (BitVec.ofNat 64 b)).toNat = b / 8 * 8 := by
        rw [InitECandidate.Solver.GuestTrapAndLookup.panByteAlign_toNat64,
            BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
      have hmem_al : post.memory (panByteAlignHOL (BitVec.ofNat 64 b)) =
          s.memory (panByteAlignHOL (BitVec.ofNat 64 b)) := by
        apply hmem_unch _ (Or.inr _)
        rw [hal_nat]
        intro ⟨h1, h2⟩
        have hb_in : hp.toNat ≤ b ∧ b < hp.toNat + 200 := ⟨by omega, by omega⟩
        exact hdisj_alloc i (M11.worldTypedIvls_allocated hWT hi) b hb1 hb2 hb_in
      rw [hmem_al, hbe_post]
  have hcore_eq : ∀ g ∈ M11.coreWorldGlobals, globN post g = globN s g := by
    intro g hg
    have hne : ofString g ∉ (["heap_ptr"] : List String).map ofString := by
      revert g hg; decide
    exact (M11.globN_eq_of_lookup_eq (hg_other (ofString g) hne)).symm
  have hfeq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [M11.blockOutObjects_eq hA hWT.2.2.1 hcell (hcore_eq "bo" (by decide)),
        M11.balObjects_eq hA hWT.1 hWT.2.2.1 hcell (hcore_eq "bal_accounts" (by decide)),
        hcore_eq "journal" (by decide),
        hcore_eq "journal_cap" (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne : ofString gn.1 ∉ (["heap_ptr"] : List String).map ofString := by
      revert gn hgn; decide
    rw [(M11.globN_eq_of_lookup_eq (hg_other (ofString gn.1) hne)).symm]
  have hFT_post := M11.fixedTyped_of_eq hAR_post hWT.2.2.1 hhp_grow (by rw [hg_sp]) hfeq
  obtain ⟨hWT_post, hOG⟩ := M11.worldTypedWith_congr_w1 ⟨hGI, hA⟩ hAR_post hhp_grow (by rw [hg_sp])
    hcore_eq hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hwo_eq : worldOwned post S Nd = worldOwned s S Nd := by
    unfold worldOwned
    rw [hfeq, M11.nodeExtents_eq hWT.2.2.2.1 hcell]
    congr 2
    apply List.flatMap_congr
    intro t ht
    exact M11.htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1
  refine ⟨S, Nd, fun _ h => h, hWT_post, hOG, ?_, ?_⟩
  · intro a _ hfresh
    apply hmem_unch a
    by_cases ha8 : a.toNat % 8 = 0
    · right
      intro ⟨h1, h2⟩
      exact hfresh ⟨by dsimp [heapFree]; omega, by dsimp [heapFree]; omega⟩
    · exact Or.inl ha8
  · intro v hv
    injection hv with hv'; injection hv' with hv''
    subst hv''
    refine ⟨hp, hv_eq, ?_⟩
    intro o ho j hj
    simp only [List.mem_singleton] at ho
    subst ho
    rw [hwo_eq] at hj
    have hj_al : j.2 = 0 ∨ Allocated s j := by
      unfold worldOwned at hj
      rcases List.mem_append.1 hj with hj_tf | hj_nd
      · rcases List.mem_append.1 hj_tf with hj_tab | hj_fix
        · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 hj_tab
          exact Or.inr ((hWT.1.2.1 t ht).2 j hfp).1
        · rcases hWT.2.2.1.1 j hj_fix with h0 | ⟨hal, _⟩
          · exact Or.inl h0
          · exact Or.inr hal
      · exact M11.worldTypedIvls_allocated hWT (M11.mem_worldTypedIvls_nodeExtents hj_nd)
    rcases hj_al with h0 | ⟨_, hhi⟩ | ⟨hlo, _⟩
    · exact Or.inr (Or.inl h0)
    · rw [← hhp_eq] at hhi
      exact Or.inr (Or.inr (Or.inr hhi))
    · have := hA.2.2.1; have := hA.2.2.2.1
      exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))

end InitECandidate.Solver.Wave8GuestInv.Fast_C08WkShard06
