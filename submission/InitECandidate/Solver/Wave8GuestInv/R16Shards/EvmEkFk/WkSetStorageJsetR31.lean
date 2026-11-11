import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.WkSetStorageTs32R31

/-!
# R31 Helper 2/2: `jset` on `(ts+32, addr, inner)` and `(inner, key, v)`

Provides:
1. `journal_append_block_step_r31`
2. `nonValueSlot_tsInner_r31`
3. `jset_tsInner_step_r31`
4. `jset_ts32_fresh_inner_step_r31`
-/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk


theorem journal_append_block_step_r31 {F : Type}
    (s0 cur : PanSemStateFiniteExact 64 F)
    (trapCode : BitVec 64) (e16 : ExpHOL 64) (tw kw f0 f1 w16 : BitVec 64)
    (hW0 : WorldOK s0)
    (heff0 : WorldEff s0 cur [] [] ["heap_ptr"])
    (hg_all_cur : ∀ k : MlS, cur.globals.lookup k = s0.globals.lookup k)
    (hloc_t : cur.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hloc_k : cur.locals.lookup (ofString "key") = some (.val (.word kw)))
    (hloc_old : cur.locals.lookup (ofString "old") = some (.rStruct [.val (.word f0), .val (.word f1)]))
    (he16 : ∀ st : PanSemStateFiniteExact 64 F,
      st.locals.lookup (ofString "old") = some (.rStruct [.val (.word f0), .val (.word f1)]) →
      @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) e16 =
        some (.val (.word w16)))
    (htw_ok : ∀ S, TablesTyped s0 S → tw.toNat ∈ S ∧
      let jrNew :=
        (tw.toNat, journalRole s0 tw.toNat) ::
          (if w16.toNat ≠ 0 ∧ journalRole s0 tw.toNat = "ts+32" then
            [(f1.toNat, "ts.inner")] else [])
      ∀ p ∈ jrNew, p ∈ worldRoleSlots s0)
    {tail : ProgHOL 64} {rv : ValueHOL 64} {out : PanSemStateFiniteExact 64 F}
    (hflow : evaluateHOLFiniteState cur (journalAppendTailProg trapCode e16 tail) =
      (some (.returned rv), out)) :
    ∃ mid tailPost,
      WorldStepSc (bufRegions []) ["heap_ptr", "journal_n"] stdKeep NoExtra s0 none mid ∧
      (∀ S Nd, WorldTypedWith s0 S Nd →
        WorldTypedWith mid S Nd ∧
        OwnedGrows s0 mid (worldOwned s0 S Nd) (worldOwned mid S Nd) ∧
        (∀ a : BitVec 64,
          (∀ i ∈ worldOwned s0 S Nd ++ bufRegions [] s0 ++ [freeGap s0], ¬ CellHits a.toNat i) →
          ¬ CellHits a.toNat (heapFree s0) →
          mid.memory a = s0.memory a)) ∧
      worldRoleSlots mid = worldRoleSlots s0 ∧
      (∀ S, TablesTyped s0 S → ∀ u ∈ S, hdr mid u 0 = hdr s0 u 0) ∧
      (∀ a ∈ worldRoleSlots mid ++ journalRoleSlots mid,
        a ∈ worldRoleSlots s0 ++ journalRoleSlots s0) ∧
      mid.locals.lookup (ofString "t") = some (.val (.word tw)) ∧
      mid.locals.lookup (ofString "key") = some (.val (.word kw)) ∧
      mid.locals.lookup (ofString "value") = cur.locals.lookup (ofString "value") ∧
      evaluateHOLFiniteState mid tail = (some (.returned rv), tailPost) ∧
      out = { tailPost with locals := out.locals } := by
  have hAs0 := hW0.1
  have hcode : cur.code = originalRuntimeCode := heff0.code
  obtain ⟨_, S0, hWT0⟩ := hW0
  have hW0_full : WorldOK s0 := ⟨hAs0, S0, hWT0⟩
  have hJ0 := hWT0.2.1
  obtain ⟨jnw, hjn_lk0⟩ := hAs0.2.2.2.2.2.2.2.2.2 "journal_n" (by decide)
  obtain ⟨jcw, hjc_lk0⟩ := hAs0.2.2.2.2.2.2.2.2.2 "journal_cap" (by decide)
  obtain ⟨jw, hj_lk0⟩ := hAs0.2.2.2.2.2.2.2.2.2 "journal" (by decide)
  have hjn_cur : cur.globals.lookup (ofString "journal_n") = some (.val (.word jnw)) := by
    rw [hg_all_cur]; exact hjn_lk0
  have hjc_cur : cur.globals.lookup (ofString "journal_cap") = some (.val (.word jcw)) := by
    rw [hg_all_cur]; exact hjc_lk0
  have hjn_nat : globN s0 "journal_n" = jnw.toNat := by unfold GlobalWord at hjn_lk0; simp [globN, hjn_lk0]
  have hjc_nat : globN s0 "journal_cap" = jcw.toNat := by unfold GlobalWord at hjc_lk0; simp [globN, hjc_lk0]
  have hj_nat : globN s0 "journal" = jw.toNat := by unfold GlobalWord at hj_lk0; simp [globN, hj_lk0]
  unfold journalAppendTailProg at hflow
  rw [evaluateHOLFiniteState_seq_line780] at hflow
  have hjn_lt_jc : jnw.toNat < jcw.toNat := by
    by_contra hge
    have hnl : Compiler.Encoders.Asm.wordCmpHOL .notLower jnw jcw = true := by
      simp only [Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
      have hnotlt : ¬ jnw.toNat < jcw.toNat := by omega
      simp [hnotlt]
    have hev_cmp1 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
        (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap"))) =
        some (.val (.word 1#64)) := by
      simp [evalHOLExact, toExact, hjn_cur, hjc_cur, hnl]
    have hite_tr : evaluateHOLFiniteState cur
        (.ite (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap")))
          (.call (some (none, none)) (ofString "trap_with") [.const trapCode]) .skip) =
        evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "trap_with") [.const trapCode]) := by
      rw [evaluateHOLFiniteState_ite, hev_cmp1]
      simp [show (1#64 : BitVec 64) ≠ 0 by decide]
    rw [hite_tr] at hflow
    obtain ⟨_, htr_none, _⟩ := seq_call0_ret_inv (by rw [evaluateHOLFiniteState_seq_line780]; exact hflow)
    have ⟨hno_none, _⟩ := trap_with_call_no_none_resumes_code cur trapCode hcode
    exact hno_none (congrArg Prod.fst htr_none)
  have hite_ok : evaluateHOLFiniteState cur
      (.ite (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap")))
        (.call (some (none, none)) (ofString "trap_with") [.const trapCode]) .skip) = (none, cur) := by
    have hnl : Compiler.Encoders.Asm.wordCmpHOL .notLower jnw jcw = false := by
      simp only [Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]; simp [hjn_lt_jc]
    have hev_cmp0 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
        (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap"))) =
        some (.val (.word 0#64)) := by
      simp [evalHOLExact, toExact, hjn_cur, hjc_cur, hnl]
    rw [evaluateHOLFiniteState_ite, hev_cmp0]; simp [evaluateHOLFiniteState_skip]
  rw [hite_ok] at hflow; dsimp only at hflow
  have hjn_lt0 : globN s0 "journal_n" < globN s0 "journal_cap" := by omega
  have hjcap_nz : globN s0 "journal_cap" ≠ 0 := by omega
  rcases hJ0.2.2.1 with hjc0 | ⟨hal_jr0, _⟩
  · exact absurd hjc0 hjcap_nz
  have hj_hi0 := (R10Shards.P26_P28.ivl_allocated_bound hAs0.2 hal_jr0).2
  set jrec : Ivl := (globN s0 "journal" + 32 * jnw.toNat, 32)
  obtain ⟨klw, _, m_kl, hflow_kl, hout_eq1⟩ := dec_ret_inv hflow
  set s_kl := setVarHOLFinite (ofString "klen") (.val (.word klw)) cur
  have heff_kl : WorldEff s0 s_kl [jrec] [] ["heap_ptr"] :=
    (heff0.mono (by intro _ h; cases h) (by intro _ h; cases h) (by intro _ h; exact h)).locals_clock _ _
  change evaluateHOLFiniteState s_kl _ = (some (.returned rv), m_kl) at hflow_kl
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hflow_kl
  have hkl_loc : s_kl.locals.lookup (ofString "klen") = some (.val (.word klw)) := by
    simp [s_kl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hargs_al : evalListHOLFinite s_kl (h := fun a => Classical.propDecidable (s_kl.memaddrs a))
      [.var .local (ofString "klen")] = some [.val (.word klw)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, hkl_loc]
  have hlk_al := pan_one_word_lookup s_kl.code.lookup (ofString "alloc") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_alloc) klw (by rw [heff_kl.code]; exact lookup_alloc_r16)
  rw [hargs_al] at hflow_kl; dsimp only at hflow_kl; rw [hlk_al] at hflow_kl; dsimp only at hflow_kl
  by_cases hcz_kl : s_kl.clock = 0
  · simp [hcz_kl] at hflow_kl
  rw [if_neg hcz_kl] at hflow_kl
  obtain ⟨pw, hpw_lk⟩ : ∃ pw : BitVec 64, s_kl.globals.lookup (ofString "heap_ptr") = some (.val (.word pw)) :=
    globalWord_of_globN_pos s_kl "heap_ptr"
      (by have := heff_kl.arena.2.1; have hsb : sourceBase = 2701131776 := rfl; omega)
  let ent_al := callEntryStateHOLFinite s_kl (HolFiniteMapExact.empty.update (ofString "n", .val (.word klw)))
  rcases hrun_al : evaluateHOLFiniteState ent_al (sourceFnBody Guest.Software.guestFn_alloc) with ⟨res_al, pa_al⟩
  dsimp only [ent_al] at hrun_al; rw [hrun_al] at hflow_kl
  have hres_al : Resumes res_al := by
    cases res_al with
    | none => simp at hflow_kl
    | some cra =>
      cases cra with
      | returned _ => exact Or.inl ⟨_, rfl⟩
      | exception _ _ => dsimp only at hflow_kl; injection hflow_kl with hr_eq _; cases hr_eq
      | _ => simp at hflow_kl
  have hal_spec := InitECandidate.Solver.Wave8GuestInv.R13.alloc_body_resumes ent_al pw heff_kl.code hpw_lk
    (by dsimp only [ent_al]; rw [hrun_al]; exact hres_al)
  dsimp only [ent_al] at hal_spec; rw [hrun_al] at hal_spec
  obtain ⟨klw', hklw'_lk, hrv_al, hcmp1, hcmp2, hpa_al⟩ := hal_spec
  have hklw_eq : klw = klw' := by
    have : ent_al.locals.lookup (ofString "n") = some (.val (.word klw)) := by
      simp [ent_al, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rw [this] at hklw'_lk; injection hklw'_lk with h'; injection h' with h'; injection h'
  subst hklw_eq; dsimp only at hrv_al hpa_al; subst hrv_al
  have hsh_pw_al : (shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one &&
      shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  dsimp only at hflow_kl; rw [if_pos hsh_pw_al] at hflow_kl
  set s_kc := setVarHOLFinite (ofString "kc") (.val (.word pw)) { pa_al with locals := s_kl.locals }
  have hs_kc_next : s_kc = { s_kl with
      globals := s_kl.globals.update (ofString "heap_ptr", .val (.word ((pw + (klw + 7)) &&& ((0 : BitVec 64) - 8)))),
      locals := s_kc.locals, clock := s_kc.clock } := by
    dsimp only [s_kc, setVarHOLFinite]; rw [hpa_al]; rfl
  obtain ⟨heff_kc, _, _, _, hpw_lo_s0, hpw_add, hhp_kc_lim, _⟩ :=
    R16Shards.worldEff_alloc_step heff_kl (by simp) hpw_lk hcmp1 hcmp2 hs_kc_next
  rcases hcont_kc : evaluateHOLFiniteState s_kc
      (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "kc"), .var .local (ofString "key"), .var .local (ofString "klen")])
        (.dec (ofString "r") .one
          (.op .add [.var .global (ofString "journal"),
            .panop .mul [.var .global (ofString "journal_n"), .const 32#64]])
          (.seq
            (.store (.var .local (ofString "r")) (.var .local (ofString "t")))
            (.seq
              (.store (.op .add [.var .local (ofString "r"), .const 8#64]) (.var .local (ofString "kc")))
              (.seq
                (.store (.op .add [.var .local (ofString "r"), .const 16#64]) e16)
                (.seq
                  (.store (.op .add [.var .local (ofString "r"), .const 24#64])
                    (.rfield 1 (.var .local (ofString "old"))))
                  (.seq
                    (.assign .global (ofString "journal_n")
                      (.op .add [.var .global (ofString "journal_n"), .const 1#64]))
                    tail))))))) with ⟨rkc, m_kc⟩
  rw [hcont_kc] at hflow_kl; dsimp only at hflow_kl
  have hrv_kc_eq : rkc = some (.returned rv) := (Prod.mk.inj hflow_kl).1
  have hm_kl_eq : m_kl = { m_kc with locals := (HolFiniteMapExact.resVarEq m_kc.locals
      (ofString "kc", s_kl.locals.lookup (ofString "kc"))) } := ((Prod.mk.inj hflow_kl).2).symm
  cases rkc with
  | none => simp at hrv_kc_eq
  | some cr_kc =>
    cases cr_kc with
    | timeOut | error | exception _ _ | «break» | «continue» | finalFfi _ => simp at hrv_kc_eq
    | returned rv_kc =>
      injection hrv_kc_eq with hrv_kc'; injection hrv_kc' with hrv_kc''; subst hrv_kc''
      obtain ⟨s_mc, hmc, hcont_mc⟩ := seq_call0_ret_inv hcont_kc
      have hkc_loc : s_kc.locals.lookup (ofString "kc") = some (.val (.word pw)) := by
        simp [s_kc, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hk_loc_kc : s_kc.locals.lookup (ofString "key") = some (.val (.word kw)) := by
        simp [s_kc, s_kl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hloc_k,
          show ofString "kc" ≠ ofString "key" by decide, show ofString "klen" ≠ ofString "key" by decide]
      have hkl_loc_kc : s_kc.locals.lookup (ofString "klen") = some (.val (.word klw)) := by
        simp [s_kc, s_kl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "kc" ≠ ofString "klen" by decide]
      have heff_mc : WorldEff s0 s_mc [jrec] [] ["heap_ptr"] := by
        have hm := worldEff_call0_memcpy heff_kc
          (.var .local (ofString "kc")) (.var .local (ofString "key")) (.var .local (ofString "klen"))
          (by rw [hmc]; simp) (by rw [hmc]; exact Or.inl rfl)
          (fun dw sw nw hd _ hn _ => by
            simp [evalHOLExact, toExact, hkc_loc] at hd; subst hd
            simp [evalHOLExact, toExact, hkl_loc_kc] at hn; subst hn
            exact Or.inr (Or.inr (Or.inr ⟨hpw_lo_s0, by omega⟩)))
        rw [hmc] at hm; exact hm
      have hmc_g : s_mc.globals = s_kc.globals := by
        have hargs_mc : evalListHOLFinite s_kc (h := fun a => Classical.propDecidable (s_kc.memaddrs a))
            [.var .local (ofString "kc"), .var .local (ofString "key"), .var .local (ofString "klen")] =
            some [.val (.word pw), .val (.word kw), .val (.word klw)] := by
          rw [evalListHOLFinite_eq_toExact]
          simp [evalListHOLExact, evalHOLExact, toExact, hkc_loc, hk_loc_kc, hkl_loc_kc]
        have hb_mc := Fast_C08WkShard03.call0_byteEff Fast_C08WkShard03.funByteEff_memcpy s_kc
          [.var .local (ofString "kc"), .var .local (ofString "key"), .var .local (ofString "klen")]
          [(pw.toNat, klw.toNat)] heff_kc.code heff_kc.arena.1
          (fun vals hvs i hi _ => by
            rw [hargs_mc] at hvs; injection hvs with hvs_eq; subst hvs_eq
            simp only [List.mem_singleton, Fast_C08WkShard03.valWordNat] at hi
            subst hi
            exact ⟨(pw.toNat, klw.toNat), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
          (by rw [hmc]; simp) (by rw [hmc]; exact Or.inl rfl)
        rw [hmc] at hb_mc; exact hb_mc.globals
      have hmc_loc : s_mc.locals = s_kc.locals := by
        have hk := fun k => evaluate_avoidsLocal_flowing k
          (.call (some (none, none)) (ofString "memcpy")
            [.var .local (ofString "kc"), .var .local (ofString "key"), .var .local (ofString "klen")])
          rfl s_kc (by rw [hmc]; exact Or.inl rfl)
        apply HolFiniteMapExact.ext; funext k; simpa [hmc] using hk k
      obtain ⟨rw, hr_ev, m_r, hflow_r, hm_kc_eq⟩ := dec_ret_inv hcont_mc
      have hs_mc_g_no_hp : ∀ k : MlS, k ≠ ofString "heap_ptr" → s_mc.globals.lookup k = s0.globals.lookup k := by
        intro k hk
        rw [hmc_g, hs_kc_next]
        simp [s_kl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hk.symm, hg_all_cur]
      have hrw_eq : rw = jw + jnw * 32#64 := by
        have hj_mc : s_mc.globals.lookup (ofString "journal") = some (.val (.word jw)) := by
          rw [hs_mc_g_no_hp _ (by decide)]; exact hj_lk0
        have hjn_mc : s_mc.globals.lookup (ofString "journal_n") = some (.val (.word jnw)) := by
          rw [hs_mc_g_no_hp _ (by decide)]; exact hjn_lk0
        simp only [evalHOLExact, evalListHOLExact, toExact, hj_mc, hjn_mc, List.all, List.map,
          Option.map, Bool.and_self, ↓reduceIte, List.foldr, valueIsWord, valueWord,
          wordOpHOL, wordOp, panOpHOL] at hr_ev
        have hz : jnw * 32#64 + (0 : BitVec 64) = jnw * 32#64 := BitVec.add_zero _
        rw [hz] at hr_ev
        injection hr_ev with hr'; injection hr' with hr'; injection hr' with hr'; exact hr'.symm
      have hrw_nat : rw.toNat = globN s0 "journal" + 32 * jnw.toNat := by
        subst hrw_eq
        have hmul : (jnw * 32#64).toNat = 32 * jnw.toNat := by
          rw [BitVec.toNat_mul, show (32#64 : BitVec 64).toNat = 32 from rfl]
          change (jnw.toNat * 32) % 2 ^ 64 = 32 * jnw.toNat
          rw [Nat.mul_comm, Nat.mod_eq_of_lt (by dsimp at hj_hi0; omega)]
        rw [BitVec.toNat_add, hj_nat, hmul, Nat.mod_eq_of_lt (by dsimp at hj_hi0; omega)]
      set s_r := setVarHOLFinite (ofString "r") (.val (.word rw)) s_mc
      have heff_r : WorldEff s0 s_r [jrec] [] ["heap_ptr"] := heff_mc.locals_clock _ _
      have hr_loc : s_r.locals.lookup (ofString "r") = some (.val (.word rw)) := by
        simp [s_r, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have ht_loc_r : s_r.locals.lookup (ofString "t") = some (.val (.word tw)) := by
        simp [s_r, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmc_loc, s_kc, s_kl, hloc_t,
          show ofString "r" ≠ ofString "t" by decide,
          show ofString "kc" ≠ ofString "t" by decide,
          show ofString "klen" ≠ ofString "t" by decide]
      have hkc_loc_r : s_r.locals.lookup (ofString "kc") = some (.val (.word pw)) := by
        simp [s_r, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmc_loc, hkc_loc,
          show ofString "r" ≠ ofString "kc" by decide]
      have hold_loc_r : s_r.locals.lookup (ofString "old") = some (.rStruct [.val (.word f0), .val (.word f1)]) := by
        simp [s_r, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmc_loc, s_kc, s_kl, hloc_old,
          show ofString "r" ≠ ofString "old" by decide,
          show ofString "kc" ≠ ofString "old" by decide,
          show ofString "klen" ≠ ofString "old" by decide]
      obtain ⟨s_st0, hst0, hflow_st0⟩ := seq_store_ret_inv hflow_r
      obtain ⟨dw0, vw0, hdw0, hvw0, _, hs_st0_eq⟩ := store_word_none_inv hst0
        (fun v hv => by simp [evalHOLExact, toExact, ht_loc_r] at hv; exact ⟨tw, hv.symm⟩)
      have hdw0_eq : dw0 = rw := by simp [evalHOLExact, toExact, hr_loc] at hdw0; exact hdw0.symm
      have hvw0_eq : vw0 = tw := by simp [evalHOLExact, toExact, ht_loc_r] at hvw0; exact hvw0.symm
      rw [hdw0_eq, hvw0_eq] at hs_st0_eq
      have heff_st0 : WorldEff s0 s_st0 [jrec] [] ["heap_ptr"] := by
        have hw := R16Shards.worldEff_store_word heff_r (.var .local (ofString "r")) (.var .local (ofString "t"))
          (fun v hv => by simp [evalHOLExact, toExact, ht_loc_r] at hv; exact ⟨tw, hv.symm⟩)
          (fun x hx _ => by
            simp [evalHOLExact, toExact, hr_loc] at hx; subst hx
            exact Or.inl ⟨jrec, List.mem_singleton.2 rfl, by dsimp [jrec]; omega, by dsimp [jrec]; omega⟩)
        rw [hst0] at hw; exact hw
      obtain ⟨s_st8, hst8, hflow_st8⟩ := seq_store_ret_inv hflow_st0
      have hst0_loc : s_st0.locals = s_r.locals := by rw [hs_st0_eq]
      obtain ⟨dw8, vw8, hdw8, hvw8, _, hs_st8_eq⟩ := store_word_none_inv hst8
        (fun v hv => by simp [evalHOLExact, toExact, hst0_loc, hkc_loc_r] at hv; exact ⟨pw, hv.symm⟩)
      have hdw8_eq : dw8 = rw + 8#64 := by
        simp [evalHOLExact, evalListHOLExact, toExact, hst0_loc, hr_loc, wordOpHOL, wordOp, valueIsWord, valueWord] at hdw8
        exact hdw8.symm
      have hrw8_nat : (rw + 8#64).toNat = rw.toNat + 8 := by
        apply BitVec.toNat_add_of_lt; change rw.toNat + 8 < 2 ^ 64; dsimp at hj_hi0; omega
      have hvw8_eq : vw8 = pw := by simp [evalHOLExact, toExact, hst0_loc, hkc_loc_r] at hvw8; exact hvw8.symm
      rw [hdw8_eq, hvw8_eq] at hs_st8_eq
      have heff_st8 : WorldEff s0 s_st8 [jrec] [] ["heap_ptr"] := by
        have hw := R16Shards.worldEff_store_word heff_st0
          (.op .add [.var .local (ofString "r"), .const 8#64]) (.var .local (ofString "kc"))
          (fun v hv => by simp [evalHOLExact, toExact, hst0_loc, hkc_loc_r] at hv; exact ⟨pw, hv.symm⟩)
          (fun x hx _ => by
            simp [evalHOLExact, evalListHOLExact, toExact, hst0_loc, hr_loc, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
            subst hx
            exact Or.inl ⟨jrec, List.mem_singleton.2 rfl, by dsimp [jrec]; omega, by dsimp [jrec]; omega⟩)
        rw [hst8] at hw; exact hw
      obtain ⟨s_st16, hst16, hflow_st16⟩ := seq_store_ret_inv hflow_st8
      have hst8_loc : s_st8.locals = s_r.locals := by rw [hs_st8_eq, hst0_loc]
      have he16_st8 := he16 s_st8 (by rw [hst8_loc]; exact hold_loc_r)
      obtain ⟨dw16, vw16, hdw16, hvw16, _, hs_st16_eq⟩ := store_word_none_inv hst16
        (fun v hv => by rw [he16_st8] at hv; injection hv with hv'; exact ⟨w16, hv'.symm⟩)
      have hdw16_eq : dw16 = rw + 16#64 := by
        simp [evalHOLExact, evalListHOLExact, toExact, hst8_loc, hr_loc, wordOpHOL, wordOp, valueIsWord, valueWord] at hdw16
        exact hdw16.symm
      have hvw16_eq : vw16 = w16 := by
        rw [he16_st8] at hvw16; injection hvw16 with h'; injection h' with h'; injection h' with h'; exact h'.symm
      rw [hdw16_eq, hvw16_eq] at hs_st16_eq
      have hrw16_nat : (rw + 16#64).toNat = rw.toNat + 16 := by
        apply BitVec.toNat_add_of_lt; change rw.toNat + 16 < 2 ^ 64; dsimp at hj_hi0; omega
      have heff_st16 : WorldEff s0 s_st16 [jrec] [] ["heap_ptr"] := by
        have hw := R16Shards.worldEff_store_word heff_st8
          (.op .add [.var .local (ofString "r"), .const 16#64]) e16
          (fun v hv => by rw [he16_st8] at hv; injection hv with hv'; exact ⟨w16, hv'.symm⟩)
          (fun x hx _ => by
            simp [evalHOLExact, evalListHOLExact, toExact, hst8_loc, hr_loc, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
            subst hx
            exact Or.inl ⟨jrec, List.mem_singleton.2 rfl, by dsimp [jrec]; omega, by dsimp [jrec]; omega⟩)
        rw [hst16] at hw; exact hw
      obtain ⟨s_st24, hst24, hflow_st24⟩ := seq_store_ret_inv hflow_st16
      have hst16_loc : s_st16.locals = s_r.locals := by rw [hs_st16_eq, hst8_loc]
      have he24 : @evalHOLExact 64 F _ s_st16.toExact (fun a => Classical.propDecidable (s_st16.memaddrs a))
          (.rfield 1 (.var .local (ofString "old"))) = some (.val (.word f1)) := by
        simp [evalHOLExact, toExact, hst16_loc, hold_loc_r]
      obtain ⟨dw24, vw24, hdw24, hvw24, _, hs_st24_eq⟩ := store_word_none_inv hst24
        (fun v hv => by rw [he24] at hv; injection hv with hv'; exact ⟨f1, hv'.symm⟩)
      have hdw24_eq : dw24 = rw + 24#64 := by
        simp [evalHOLExact, evalListHOLExact, toExact, hst16_loc, hr_loc, wordOpHOL, wordOp, valueIsWord, valueWord] at hdw24
        exact hdw24.symm
      have hvw24_eq : vw24 = f1 := by
        rw [he24] at hvw24; injection hvw24 with h'; injection h' with h'; injection h' with h'; exact h'.symm
      rw [hdw24_eq, hvw24_eq] at hs_st24_eq
      have hrw24_nat : (rw + 24#64).toNat = rw.toNat + 24 := by
        apply BitVec.toNat_add_of_lt; change rw.toNat + 24 < 2 ^ 64; dsimp at hj_hi0; omega
      have heff_st24 : WorldEff s0 s_st24 [jrec] [] ["heap_ptr"] := by
        have hw := R16Shards.worldEff_store_word heff_st16
          (.op .add [.var .local (ofString "r"), .const 24#64]) (.rfield 1 (.var .local (ofString "old")))
          (fun v hv => by rw [he24] at hv; injection hv with hv'; exact ⟨f1, hv'.symm⟩)
          (fun x hx _ => by
            simp [evalHOLExact, evalListHOLExact, toExact, hst16_loc, hr_loc, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
            subst hx
            exact Or.inl ⟨jrec, List.mem_singleton.2 rfl, by dsimp [jrec]; omega, by dsimp [jrec]; omega⟩)
        rw [hst24] at hw; exact hw
      obtain ⟨mid, hass_step, htail_run⟩ := seq_assign_ret_inv hflow_st24
      have hst24_g : s_st24.globals = s_mc.globals := by
        rw [hs_st24_eq, hs_st16_eq, hs_st8_eq, hs_st0_eq]; rfl
      have hjn_st24 : s_st24.globals.lookup (ofString "journal_n") = some (.val (.word jnw)) := by
        rw [hst24_g, hs_mc_g_no_hp _ (by decide)]; exact hjn_lk0
      have hass : evaluateHOLFiniteState s_st24
          (.assign .global (ofString "journal_n")
            (.op .add [.var .global (ofString "journal_n"), .const 1#64])) =
          (none, setGlobalHOLFinite (ofString "journal_n") (.val (.word (jnw + 1#64))) s_st24) := by
        simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, toExact,
          hjn_st24, wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact,
          isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
      rw [hass] at hass_step
      have hmid_eq : mid = setGlobalHOLFinite (ofString "journal_n") (.val (.word (jnw + 1#64))) s_st24 :=
        ((Prod.mk.inj hass_step).2).symm
      have hmid_mem : mid.memory = s_st24.memory := by rw [hmid_eq]; rfl
      have hmid_g : mid.globals = s_st24.globals.update (ofString "journal_n", .val (.word (jnw + 1#64))) := by
        rw [hmid_eq]; rfl
      have hmid_be : mid.be = s0.be := by rw [hmid_eq]; exact heff_st24.be
      have hne_0_8 : rw ≠ rw + 8#64 := fun h => by have := congrArg BitVec.toNat h; omega
      have hne_0_16 : rw ≠ rw + 16#64 := fun h => by have := congrArg BitVec.toNat h; omega
      have hne_0_24 : rw ≠ rw + 24#64 := fun h => by have := congrArg BitVec.toNat h; omega
      have hne_16_24 : rw + 16#64 ≠ rw + 24#64 := fun h => by have := congrArg BitVec.toNat h; omega
      have hm_r0 : memW mid (globN s0 "journal" + 32 * jnw.toNat) = tw.toNat := by
        have hbv0 : BitVec.ofNat 64 (globN s0 "journal" + 32 * jnw.toNat) = rw := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ofNat, hrw_nat, Nat.mod_eq_of_lt (by dsimp at hj_hi0; omega)]
        unfold memW; rw [hbv0, hmid_mem, hs_st24_eq, hs_st16_eq, hs_st8_eq, hs_st0_eq]
        simp [hne_0_24, hne_0_16, hne_0_8]
      have hm_r16 : memW mid (globN s0 "journal" + 32 * jnw.toNat + 16) = w16.toNat := by
        have hbv16 : BitVec.ofNat 64 (globN s0 "journal" + 32 * jnw.toNat + 16) = rw + 16#64 := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ofNat, hrw16_nat, hrw_nat, Nat.mod_eq_of_lt (by dsimp at hj_hi0; omega)]
        unfold memW; rw [hbv16, hmid_mem, hs_st24_eq, hs_st16_eq]
        simp [hne_16_24]
      have hm_r24 : memW mid (globN s0 "journal" + 32 * jnw.toNat + 24) = f1.toNat := by
        have hbv24 : BitVec.ofNat 64 (globN s0 "journal" + 32 * jnw.toNat + 24) = rw + 24#64 := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ofNat, hrw24_nat, hrw_nat, Nat.mod_eq_of_lt (by dsimp at hj_hi0; omega)]
        unfold memW; rw [hbv24, hmid_mem, hs_st24_eq]
        simp
      have hhp_mid_eq : globN mid "heap_ptr" = globN s_st24 "heap_ptr" := by
        apply globN_eq_of_lookup
        rw [hmid_g]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "journal_n" ≠ ofString "heap_ptr" by decide]
      have hfmp_mid_eq : globN mid "frame_mem_ptr" = globN s_st24 "frame_mem_ptr" := by
        apply globN_eq_of_lookup
        rw [hmid_g]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "journal_n" ≠ ofString "frame_mem_ptr" by decide]
      have hsp_mid_eq : globN mid "scratch_ptr" = globN s_st24 "scratch_ptr" := by
        apply globN_eq_of_lookup
        rw [hmid_g]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "journal_n" ≠ ofString "scratch_ptr" by decide]
      have hA_mid : ArenaReady mid := by
        have hG_mid : GuestInv mid := by
          have hG24 := heff_st24.arena.1
          rw [hmid_eq]; exact ⟨hG24.code, hG24.memaddrs, hG24.shMemaddrs, hG24.baseAddr⟩
        refine ⟨hG_mid, ?_⟩
        unfold ArenaOK
        have hA24 := heff_st24.arena.2
        rw [hhp_mid_eq, hfmp_mid_eq, hsp_mid_eq]
        refine ⟨hA24.1, hA24.2.1, hA24.2.2.1, hA24.2.2.2.1, hA24.2.2.2.2.1,
          hA24.2.2.2.2.2.1, hA24.2.2.2.2.2.2.1, hA24.2.2.2.2.2.2.2.1, ?_⟩
        intro g hg
        by_cases hgj : ofString g = ofString "journal_n"
        · refine ⟨jnw + 1#64, ?_⟩
          unfold GlobalWord; rw [hmid_g, hgj]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        · obtain ⟨w, hw⟩ := hA24.2.2.2.2.2.2.2.2 g hg
          refine ⟨w, ?_⟩
          unfold GlobalWord at hw ⊢
          rw [hmid_g]; simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hgj, hw]
      have hjn_mid : globN mid "journal_n" = globN s0 "journal_n" + 1 := by
        have hjc_max : globN s0 "journal_cap" ≤ journalCapMax := hJ0.2.1
        have hjcm_val : journalCapMax = 524288 := rfl
        have hadd1 : (jnw + 1#64).toNat = jnw.toNat + 1 := by
          apply BitVec.toNat_add_of_lt; change jnw.toNat + 1 < 2 ^ 64; omega
        have hlk_mid : mid.globals.lookup (ofString "journal_n") = some (.val (.word (jnw + 1#64))) := by
          rw [hmid_g]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        rw [hjn_nat]; unfold globN; simp [hlk_mid, hadd1]
      have hg_kept_mid : GlobalsKept ["heap_ptr", "journal_n"] s0 mid := by
        intro k hk
        have hne_hp : k ≠ ofString "heap_ptr" := fun h => hk (by simp [h])
        have hne_jn : k ≠ ofString "journal_n" := fun h => hk (by simp [h])
        rw [hmid_g]
        have hlk_k : (s_st24.globals.update (ofString "journal_n", .val (.word (jnw + 1#64)))).lookup k =
            s_st24.globals.lookup k := by
          simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne_jn]
        rw [hlk_k]; exact heff_st24.gw_kept k (by simp [hne_hp])
      have hdom_mid : ∀ x : BitVec 64, mid.memory x ≠ s0.memory x → s0.memaddrs x :=
        fun x hx => heff_st24.out_dom x (by rwa [← hmid_mem])
      have hcell_mid : ∀ x : BitVec 64, mid.memory x ≠ s0.memory x →
          CellHitsPos x.toNat (globN s0 "journal" + 32 * jnw.toNat, 32) ∨
          CellHitsPos x.toNat (freeGap s0) ∨
          CellHitsPos x.toNat (heapFree s0) := fun x hx => by
        rcases heff_st24.cell_frame x (by rwa [← hmid_mem]) with ⟨iv, hiv, hhit⟩ | ⟨_, h, _⟩ | hfg | hhf
        · simp only [List.mem_singleton] at hiv; subst hiv; exact Or.inl hhit
        · cases h
        · exact Or.inr (Or.inl hfg)
        · exact Or.inr (Or.inr hhf)
      have hbyte_mid : ∀ a : Nat, a < 2 ^ 64 → memB mid a ≠ memB s0 a →
          InIvl a (globN s0 "journal" + 32 * jnw.toNat, 32) ∨
          InIvl a (freeGap s0) ∨
          InIvl a (heapFree s0) := fun a ha hne => by
        have hmb_mid : memB mid a = memB s_st24 a := by
          unfold memB; rw [hmid_mem, hmid_be, heff_st24.be]
        rcases heff_st24.byte_frame a ha (by rwa [← hmb_mid]) with ⟨iv, hiv, hin⟩ | ⟨_, h, _⟩ | hfg | hhf
        · simp only [List.mem_singleton] at hiv; subst hiv; exact Or.inl hin
        · cases h
        · exact Or.inr (Or.inl hfg)
        · exact Or.inr (Or.inr hhf)
      have hstep_code_sc : WorldStepCodeSc [] ["heap_ptr", "journal_n"] s0 none mid :=
        worldStepCodeSc_of_journal_append jnw hW0_full hA_mid hmid_be
          (by rw [hhp_mid_eq]; exact heff_st24.hp_lo) hg_kept_mid hjn_nat hjn_lt0 hjn_mid
          hdom_mid hcell_mid hbyte_mid hm_r0
          (fun S hTS => by dsimp only; rw [hm_r16, hm_r24]; exact htw_ok S hTS)
      have hstep_sc : WorldStepSc (bufRegions []) ["heap_ptr", "journal_n"] stdKeep NoExtra s0 none mid :=
        worldStepSc_of_journal_append jnw hW0_full hA_mid hmid_be
          (by rw [hhp_mid_eq]; exact heff_st24.hp_lo) hg_kept_mid hjn_nat hjn_lt0 hjn_mid
          hdom_mid hcell_mid hbyte_mid hm_r0
          (fun S hTS => by dsimp only; rw [hm_r16, hm_r24]; exact htw_ok S hTS)
      have hnt_step : NonTrieStep [] s0 mid := hstep_code_sc.2
      obtain ⟨hwrs_mid, hhdr_mid, hjrs_sub_mid⟩ :=
        journal_append_wrs_and_hdr_r31 jnw hW0_full hA_mid
          (by rw [hhp_mid_eq]; exact heff_st24.hp_lo) hg_kept_mid hjn_nat hjn_lt0 hdom_mid hcell_mid
      have hs_st24_loc : s_st24.locals = s_r.locals := by rw [hs_st24_eq, hst16_loc]
      have hmid_loc : mid.locals = s_r.locals := by rw [hmid_eq]; exact hs_st24_loc
      have hmid_loc_other : ∀ x : MlS, x ≠ ofString "klen" → x ≠ ofString "kc" → x ≠ ofString "r" →
          mid.locals.lookup x = cur.locals.lookup x := by
        intro x hx_kl hx_kc hx_r
        rw [hmid_loc]
        simp [s_r, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          Ne.symm hx_r, hmc_loc, s_kc, Ne.symm hx_kc, s_kl, Ne.symm hx_kl]
      have hout_tp : out = { m_r with locals := out.locals } := by
        rw [hout_eq1, hm_kl_eq, hm_kc_eq]
      refine ⟨mid, m_r, hstep_sc, ?_, hwrs_mid, hhdr_mid,
        hjrs_sub_mid tw.toNat hjn_mid hm_r0
          (by dsimp only; rw [hm_r16, hm_r24]; exact (htw_ok S0 hWT0.1).2),
        (hmid_loc_other _ (by decide) (by decide) (by decide)).trans hloc_t,
        (hmid_loc_other _ (by decide) (by decide) (by decide)).trans hloc_k,
        hmid_loc_other _ (by decide) (by decide) (by decide),
        htail_run, hout_tp⟩
      · intro S Nd hWT_s0
        obtain ⟨⟨Nd', hWT_nd'⟩, hOG_nto, _⟩ := hnt_step S Nd hWT_s0 (fun _ h => by cases h)
        have hT_s0 := hWT_s0.1
        have hTr_s0 := hWT_s0.2.2.2
        have hj_fo0 : (globN s0 "journal", 32 * globN s0 "journal_cap") ∈ fixedObjects s0 := by
          unfold fixedObjects; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; right; simp [hjcap_nz]
        have hjrec_in0' : Inside jrec (globN s0 "journal") (globN s0 "journal" + 32 * globN s0 "journal_cap") := by
          dsimp [Inside, jrec]; omega
        have hunhit_disj_jr0 : ∀ i : Ivl, Allocated s0 i → i.1 % 8 = 0 → i.2 % 8 = 0 →
            Disj i (globN s0 "journal", 32 * globN s0 "journal_cap") → IvlUnhit s0 mid i := by
          intro i hal hi1 hi2 hdj x hx8 hhit
          by_contra hne
          have hdj_rec : Disj i jrec := (disj_of_inside_left hjrec_in0' hdj.flip).flip
          have hdj_fg : Disj i (freeGap s0) := disj_allocated_freeGap hAs0.2 hal
          have hdj_hf : Disj i (heapFree s0) := disj_allocated_heapFree hAs0.2 hal
          have hin_i : i.1 ≤ x.toNat ∧ x.toNat + 8 ≤ i.1 + i.2 := by unfold CellHits at hhit; omega
          rcases hcell_mid x hne with hrec_hit | hfg_hit | hhf_hit
          · exact not_cellHitsPos_of_disj hin_i hdj_rec hrec_hit
          · exact not_cellHitsPos_of_disj hin_i hdj_fg hfg_hit
          · exact not_cellHitsPos_of_disj hin_i hdj_hf hhf_hit
        have hag_mid : AllocatorGrows s0 mid := ⟨hstep_sc.1.2.1, hstep_sc.2⟩
        have hu_nd_rec : ∀ n ∈ Nd, IvlUnhit s0 mid (nodeIvl s0 n) := fun n hn => by
          have hal := (hTr_s0.1.1 n hn).2.1
          have hw := (hTr_s0.1.1 n hn).2.2.2.1
          have hne_mem : nodeIvl s0 n ∈ nodeExtents s0 Nd := by
            unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp⟩
          exact hunhit_disj_jr0 _ hal hw.1 hw.2.1 ((hTr_s0.2.1 _ hne_mem).2 _ hj_fo0)
        have hu_nd_byte : ∀ n ∈ Nd, (memW s0 n = 1 ∨ memW s0 n = 2) → memW s0 (n + 40) ≠ 0 →
            ∀ k, k < memW s0 (n + 40) → memB mid (memW s0 (n + 32) + k) = memB s0 (memW s0 (n + 32) + k) := by
          intro n hn h12 hlen0 k hk
          have h264 : heapLimit ≤ 2 ^ 64 := by decide
          rcases (hTr_s0.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, hal_p, hin_p, _⟩
          · exact absurd h0 hlen0
          · have hp_ne : (memW s0 (n + 32), memW s0 (n + 40)) ∈ nodeExtents s0 Nd := by
              unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodePath, h12, hlen0]⟩
            by_contra hne_b
            have ha_lt : memW s0 (n + 32) + k < 2 ^ 64 := by have := hin_p.2; dsimp at this; omega
            have hdj_jr : Disj (memW s0 (n + 32), memW s0 (n + 40)) jrec :=
              (disj_of_inside_left hjrec_in0' ((hTr_s0.2.1 _ hp_ne).2 _ hj_fo0).flip).flip
            have hdj_fg : Disj (memW s0 (n + 32), memW s0 (n + 40)) (freeGap s0) :=
              disj_allocated_freeGap hAs0.2 hal_p
            have hdj_hf : Disj (memW s0 (n + 32), memW s0 (n + 40)) (heapFree s0) :=
              disj_allocated_heapFree hAs0.2 hal_p
            rcases hbyte_mid _ ha_lt hne_b with hin_rec | hin_fg | hin_hf
            · unfold InIvl at hin_rec; rcases hdj_jr with h0 | h0 | h1 | h2 <;> (dsimp [jrec] at *; omega)
            · unfold InIvl at hin_fg; rcases hdj_fg with h0 | h0 | h1 | h2 <;> (dsimp [freeGap] at *; omega)
            · unfold InIvl at hin_hf; rcases hdj_hf with h0 | h0 | h1 | h2 <;> (dsimp [heapFree] at *; omega)
        obtain ⟨hNH_mid, hne_eq⟩ := nodeHeap_congr_bytes hAs0.1 hA_mid.1 hag_mid hTr_s0.1 hu_nd_rec hu_nd_byte
        have htab_fp_eq : ∀ t ∈ S, htabFootprint mid t = htabFootprint s0 t := by
          have h264_he : heapEnd ≤ 2 ^ 64 := by decide
          intro t ht
          have hwf := (hT_s0.2.1 t ht).1
          have ht_fp : (t, 88) ∈ htabFootprint s0 t := by simp [htabFootprint]
          have ht8 : t % 8 = 0 := (hwf.1 _ ht_fp).2.1
          have hhi : t + 88 ≤ 2 ^ 64 := by have := (hwf.1 _ ht_fp).1.2; dsimp at this; omega
          exact (htabFootprint_eq_of_hdr_unhit ht8 hhi
            (hunhit_disj_jr0 _ ((hT_s0.2.1 t ht).2 _ ht_fp).1
              (hwf.1 _ ht_fp).2.1 (hwf.1 _ ht_fp).2.2.1
              (((hT_s0.2.1 t ht).2 _ ht_fp).2 _ hj_fo0))).2
        have hTr_mid : TriesTypedWith mid S Nd := by
          refine ⟨hNH_mid, ?_, ?_⟩
          · rw [hne_eq]
            intro o ho
            refine ⟨fun t ht i hi => ?_, ?_⟩
            · rw [htab_fp_eq t ht] at hi
              exact (hTr_s0.2.1 o ho).1 t ht i hi
            · intro i hi
              by_cases ho0 : o.2 = 0
              · exact Or.inl ho0
              · rcases hOG_nto i (List.mem_append_right _ hi) with rfl | ⟨k, hk_nto, hin_ik⟩ | hin_hp
                · exact Or.inr (Or.inl rfl)
                · rcases List.mem_append.1 hk_nto with hk_tab | hk_fix
                  · obtain ⟨t, ht, hk_fp⟩ := List.mem_flatMap.1 hk_tab
                    exact (disj_of_inside_left hin_ik (((hTr_s0.2.1 o ho).1 t ht k hk_fp).flip)).flip
                  · exact (disj_of_inside_left hin_ik (((hTr_s0.2.1 o ho).2 k hk_fix).flip)).flip
                · have hal_o : Allocated s0 o := by
                    unfold nodeExtents at ho
                    obtain ⟨n, hn, hop⟩ := List.mem_flatMap.1 ho
                    rcases List.mem_cons.1 hop with rfl | hp
                    · exact (hTr_s0.1.1 n hn).2.1
                    · simp only [List.mem_singleton] at hp; subst hp
                      unfold nodePath
                      split
                      · rename_i h12_len
                        rcases (hTr_s0.1.1 n hn).2.2.2.2.2.2.1 h12_len.1 with h0 | ⟨_, hal_p, _, _⟩
                        · exact absurd h0 h12_len.2
                        · exact hal_p
                      · rename_i hnot
                        exfalso; apply ho0; simp [nodePath, hnot]
                  have hdj_ohf : Disj o (heapFree s0) := disj_allocated_heapFree hAs0.2 hal_o
                  have hin_ihf : Inside i (heapFree s0).1 ((heapFree s0).1 + (heapFree s0).2) := by
                    unfold heapFree Inside; unfold Inside at hin_hp
                    have := hA_mid.2.2.1
                    dsimp at hin_hp ⊢; omega
                  exact (disj_of_inside_left hin_ihf hdj_ohf.flip).flip
          · -- Look! `hWT_nd'.2.2.2.2.2` ALREADY has `ws+24` / `ws+32` in `Nd'`, wait: we want `Nd`!
            have hws_g : globN mid "ws" = globN s0 "ws" :=
              globN_eq_of_lookup (hg_kept_mid (ofString "ws") (by decide))
            intro hnz
            have hnz0 : globN s0 "ws" ≠ 0 := by rwa [← hws_g]
            have hw24 : memW mid (globN mid "ws" + 24) = memW s0 (globN s0 "ws" + 24) := by
              rw [hws_g]
              exact hstep_sc.1.2.2.2.1 ("ws", [0, 8, 16, 24, 32]) (by simp [stdKeep]) hnz0
                24 (by simp) (fun _ h => by cases h)
            have hw32 : memW mid (globN mid "ws" + 32) = memW s0 (globN s0 "ws" + 32) := by
              rw [hws_g]
              exact hstep_sc.1.2.2.2.1 ("ws", [0, 8, 16, 24, 32]) (by simp [stdKeep]) hnz0
                32 (by simp) (fun _ h => by cases h)
            rw [hw24, hw32]
            obtain ⟨hr24, hr32⟩ := hTr_s0.2.2 hnz0
            refine ⟨hr24, fun hm i hi => ?_⟩
            have hwf32 := (hT_s0.2.1 _ hm).1
            have hu32 : ∀ iv ∈ htabFootprint s0 (memW s0 (globN s0 "ws" + 32)), IvlUnhit s0 mid iv :=
              fun iv hiv => hunhit_disj_jr0 iv ((hT_s0.2.1 _ hm).2 iv hiv).1
                (hwf32.1 iv hiv).2.1 (hwf32.1 iv hiv).2.2.1
                (((hT_s0.2.1 _ hm).2 iv hiv).2 _ hj_fo0)
            have hvals := R10Shards.Fast_GbodyC17ToC21.htabValues_eq_of_unhit hwf32 hu32
            have hh32_len : hdr mid (memW s0 (globN s0 "ws" + 32)) 3 = hdr s0 (memW s0 (globN s0 "ws" + 32)) 3 := by
              have ht_fp : (memW s0 (globN s0 "ws" + 32), 88) ∈ htabFootprint s0 (memW s0 (globN s0 "ws" + 32)) := by
                simp [htabFootprint]
              have ht8 : (memW s0 (globN s0 "ws" + 32)) % 8 = 0 := (hwf32.1 _ ht_fp).2.1
              have hhi : memW s0 (globN s0 "ws" + 32) + 88 ≤ 2 ^ 64 := by
                have h1 := (hwf32.1 _ ht_fp).1.2
                have h2 : heapEnd ≤ 2 ^ 64 := by decide
                dsimp at h1; omega
              exact (htabFootprint_eq_of_hdr_unhit ht8 hhi (hu32 _ ht_fp)).1 3 (by omega)
            rw [hh32_len] at hi
            have hget : (htabValues mid (memW s0 (globN s0 "ws" + 32)))[i]? =
                (htabValues s0 (memW s0 (globN s0 "ws" + 32)))[i]? := by rw [hvals]
            simp only [htabValues, List.getElem?_map, List.getElem?_range, hh32_len, hi,
              Option.map_some, Option.some.injEq] at hget
            rw [hget]; exact hr32 hm i hi
        refine ⟨⟨hWT_nd'.1, hWT_nd'.2.1, hWT_nd'.2.2.1, hTr_mid⟩, ?_, ?_⟩
        · intro o ho
          unfold worldOwned at ho
          rcases List.mem_append.1 ho with hnto | hnd
          · rcases hOG_nto o hnto with rfl | ⟨k, hk, hin⟩ | hhp
            · exact Or.inl rfl
            · exact Or.inr (Or.inl ⟨k, List.mem_append_left _ hk, hin⟩)
            · exact Or.inr (Or.inr hhp)
          · rw [hne_eq] at hnd
            exact Or.inr (Or.inl ⟨o, List.mem_append_right _ hnd, le_rfl, le_rfl⟩)
        · intro a hkeep hnot_hf
          by_contra hne
          rcases hcell_mid a hne with ⟨_, hhit_rec⟩ | ⟨_, hhit_fg⟩ | ⟨_, hhit_hf⟩
          · have hhit_jr : CellHits a.toNat (globN s0 "journal", 32 * globN s0 "journal_cap") := by
              unfold CellHits at hhit_rec ⊢; dsimp [jrec] at hhit_rec; omega
            have hwo_jr : (globN s0 "journal", 32 * globN s0 "journal_cap") ∈ worldOwned s0 S Nd := by
              unfold worldOwned; exact List.mem_append_left _ (List.mem_append_right _ hj_fo0)
            exact hkeep _ (List.mem_append_left _ (List.mem_append_left _ hwo_jr)) hhit_jr
          · exact hkeep (freeGap s0) (List.mem_append_right _ List.mem_cons_self) hhit_fg
          · apply hnot_hf
            unfold heapFree CellHits at hhit_hf ⊢
            have := hA_mid.2.2.2.1; omega

theorem nonValueSlot_tsInner_r31 {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (t0 : Nat) (hT : TablesTyped s S)
    (ht0_nz : t0 ≠ 0) (ht0_wrs : (t0, "ts.inner") ∈ worldRoleSlots s) :
    t0 ∈ S ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
    (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) ∧
    globN s "bal_accounts" ≠ t0 ∧
    (∀ ad ∈ balRecords s, memW s ad ≠ t0) ∧
    (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t0) ∧
    journalRole s t0 = "ts.inner" := by
  have hroles := hT.2.2.2.2.2.2.2.2.2.2.2
  have ht0_S : t0 ∈ S := (hroles.1 _ (List.mem_append_left _ ht0_wrs)).1
  have hnonval := nonValueSlot_of_wrs s S t0 "ts.inner" hT ht0_nz ht0_S ht0_wrs
    (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨hnonval.1, hnonval.2.1, hnonval.2.2.1, hnonval.2.2.2.1, hnonval.2.2.2.2.1,
    hnonval.2.2.2.2.2, ?_⟩
  unfold journalRole
  by_cases hts : globN s "ts" = 0
  · simp [hts]
  · have hnot_rec : ∀ (k : Nat) (r : String),
        (k, r) ∈ ([(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
          (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] : List (Nat × String)) →
        r ≠ "ts.inner" → t0 ≠ memW s (globN s "ts" + k) := by
      intro k r hkr hne heq
      have hmnz : memW s (globN s "ts" + k) ≠ 0 := by rwa [← heq]
      have hm : (memW s (globN s "ts" + k), r) ∈ worldRoleSlots s := by
        apply mem_worldRoleSlots_recRole s "ts" k r hts hmnz
        apply List.mem_append.2; right
        unfold recRoles; rw [if_neg hts]
        exact List.mem_map.2 ⟨(k, r), hkr, rfl⟩
      exact slot_ne_of_diff_nonshared_role hroles hm ht0_wrs hne heq.symm
    have h16 := hnot_rec 16 "ts+16" (by simp) (by decide)
    have h32 := hnot_rec 32 "ts+32" (by simp) (by decide)
    have h48 := hnot_rec 48 "ts+48" (by simp) (by decide)
    have h64 := hnot_rec 64 "ts+64" (by simp) (by decide)
    simp [hts, h16, h32, h48, h64]

theorem jset_tsInner_step_r31 {F : Type} (B : BufList) (gw : List String)
    (hhp_in : "heap_ptr" ∈ gw) (hjn_in : "journal_n" ∈ gw)
    (tExp kExp vExp : ExpHOL 64)
    (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hW : WorldOK s)
    (tw : BitVec 64)
    (ht_ev : evalAt s tExp = some (.val (.word tw)))
    (htw_wrs : (tw.toNat, "ts.inner") ∈ worldRoleSlots s)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "jset") [tExp, kExp, vExp])).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "jset") [tExp, kExp, vExp])).1) :
    WorldStepSc (bufRegions B) gw stdKeep NoExtra
      s (evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "jset") [tExp, kExp, vExp])).1
      (evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "jset") [tExp, kExp, vExp])).2 := by
  set argsL : List (ExpHOL 64) := [tExp, kExp, vExp]
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) argsL with _ | values
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    have hargs_fin : evalListHOLFinite s
        (h := fun a => Classical.propDecidable (s.memaddrs a)) argsL = some values := by
      rwa [evalListHOLFinite_eq_toExact]
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "jset") values with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        have hbody_eq := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "jset")
          _ _ body' _ ret' values callee lookup_jset (by rwa [← hcode])
        obtain ⟨v1, v2, v3, he1, _, _, hc_t, hc_k, hc_v⟩ := R16WkAcctWs.callee_param_three s (ofString "jset")
          (ofString "t") (ofString "key") (ofString "value") .one .one .one _ _
          (by rw [hcode]; exact lookup_jset) _ _ _ values body' callee ret' hargs_fin hl
        have hv1_eq : v1 = .val (.word tw) := by rw [ht_ev] at he1; exact Option.some.inj he1.symm
        subst hv1_eq
        obtain ⟨_, kw, vlw, _, _, hc_k', hc_v'⟩ := Fast_C08WkShard03.lookupCode_three_words
          (by decide) (by decide) (by decide) lookup_jset
          (by
            have hret_eq := lookupCodeHOLFinite_installed_return s (ofString "jset")
              _ _ _ _ ret' values callee (by rw [hcode]; exact lookup_jset) hl
            subst hbody_eq hret_eq; rwa [← hcode])
        have hv23 : v2 = .val (.word kw) ∧ v3 = .val (.word vlw) := by
          rw [hc_k] at hc_k'; rw [hc_v] at hc_v'
          exact ⟨Option.some.inj hc_k', Option.some.inj hc_v'⟩
        rcases hv23 with ⟨rfl, rfl⟩
        let ent := callEntryStateHOLFinite s callee
        rcases hrun : evaluateHOLFiniteState ent body' with ⟨res, post⟩
        simp only [ent, hrun] at hnt hfr ⊢
        cases res with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | exception eid ev =>
            exfalso
            have hne : eid ≠ ofString "TrapErr" := by
              rcases hfr with h | h | h | ⟨_, h⟩ | ⟨_, _, h, hne⟩ <;> try simp at h
              obtain ⟨rfl, _⟩ := h; exact hne
            have hbody_ok : noCatchableRaise trapOnlyCallees body' = true :=
              trapOnlyCallees_good (ofString "jset") (by decide) values body' callee ret' (by rwa [← hcode])
            have hno := evaluate_noCatchableRaise trapOnlyCallees trapOnlyCallees_good
              body' hbody_ok ent hcode eid ev hne
            dsimp only [ent] at hno; rw [hrun] at hno; exact hno rfl
          | returned rv =>
            dsimp only at hfr ⊢
            split
            · have hWent : WorldOK ent := localsFree_worldOK s callee (s.clock - 1) hW
              have htw_nz_nat : tw.toNat ≠ 0 := by
                have hf := (List.mem_filter.1 htw_wrs).2
                simpa using hf
              have htw_wrs_ent : (tw.toNat, "ts.inner") ∈ worldRoleSlots ent := htw_wrs
              subst hbody_eq
              have hbody_fold : sourceFnBody Guest.Software.guestFn_jset =
                  .decCall (ofString "old") (.comb [.one, .one]) (ofString "htab_get")
                    [.var .local (ofString "t"), .var .local (ofString "key")]
                    (journalAppendTailProg 4#64 (.rfield 0 (.var .local (ofString "old")))
                      (.seq
                        (.call (some (none, none)) (ofString "htab_set")
                          [.var .local (ofString "t"), .var .local (ofString "key"), .var .local (ofString "value")])
                        (.return (.const 0#64)))) := rfl
              change evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_jset) =
                (some (.returned rv), post) at hrun
              rw [hbody_fold] at hrun
              rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun
              have hent_t : ent.locals.lookup (ofString "t") = some (.val (.word tw)) := hc_t
              have hent_k : ent.locals.lookup (ofString "key") = some (.val (.word kw)) := hc_k
              have hent_v : ent.locals.lookup (ofString "value") = some (.val (.word vlw)) := hc_v
              have hargs_hg : evalListHOLFinite ent
                  (h := fun a => Classical.propDecidable (ent.memaddrs a))
                  [.var .local (ofString "t"), .var .local (ofString "key")] =
                  some [.val (.word tw), .val (.word kw)] := by
                simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, hent_t, hent_k]
              rw [hargs_hg] at hrun; dsimp only at hrun
              rcases hlk_hg : lookupCodeHOLFinite ent.code.lookup (ofString "htab_get")
                  [.val (.word tw), .val (.word kw)] with _ | ⟨bhg, chg, rhg⟩
              · rw [hlk_hg] at hrun; simp at hrun
              · rw [hlk_hg] at hrun; dsimp only at hrun
                by_cases hcz_ent : ent.clock = 0
                · simp [hcz_ent] at hrun
                rw [if_neg hcz_ent] at hrun
                have hbhg_eq := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
                  (ofString "htab_get") _ _ bhg _ rhg _ chg EvmFrameSpecs.lookup_htab_get
                  (by rwa [← show ent.code = originalRuntimeCode from hcode])
                subst hbhg_eq
                have hchg_t' : chg.lookup (ofString "t") = some (.val (.word tw)) := by
                  have ht_ev' : evalAt ent (.var .local (ofString "t")) = some (.val (.word tw)) := by
                    simp [evalAt, evalHOLExact, toExact, hent_t]
                  have ⟨v1', _, he1', _, hc1', _⟩ := callee_param_two_r16_code ent
                    (ofString "htab_get") (ofString "t") (ofString "key") .one .one _ _
                    (by rw [show ent.code = originalRuntimeCode from hcode]; exact EvmFrameSpecs.lookup_htab_get)
                    (.var .local (ofString "t")) (.var .local (ofString "key"))
                    _ _ chg rhg hargs_hg hlk_hg
                  rw [ht_ev'] at he1'; injection he1' with h'; subst h'; exact hc1'
                have hchg_k' : chg.lookup (ofString "key") = some (.val (.word kw)) := by
                  have hk_ev' : evalAt ent (.var .local (ofString "key")) = some (.val (.word kw)) := by
                    simp [evalAt, evalHOLExact, toExact, hent_k]
                  have ⟨_, v2', _, he2', _, hc2'⟩ := callee_param_two_r16_code ent
                    (ofString "htab_get") (ofString "t") (ofString "key") .one .one _ _
                    (by rw [show ent.code = originalRuntimeCode from hcode]; exact EvmFrameSpecs.lookup_htab_get)
                    (.var .local (ofString "t")) (.var .local (ofString "key"))
                    _ _ chg rhg hargs_hg hlk_hg
                  rw [hk_ev'] at he2'; injection he2' with h'; subst h'; exact hc2'
                let ent_hg := callEntryStateHOLFinite ent chg
                rcases hrun_hg : evaluateHOLFiniteState ent_hg
                    (sourceFnBody Guest.Software.guestFn_htab_get) with ⟨res_hg, p_hg⟩
                dsimp only [ent_hg] at hrun_hg
                rw [hrun_hg] at hrun
                cases res_hg with
                | none => simp at hrun
                | some cr_hg =>
                  cases cr_hg with
                  | exception _ _ =>
                    exfalso
                    dsimp only at hrun; injection hrun with hr_eq _; cases hr_eq
                  | timeOut | error | «break» | «continue» | finalFfi _ => simp at hrun
                  | returned v_old =>
                    dsimp only at hrun
                    split at hrun <;> try simp at hrun
                    obtain ⟨_, S0, hWT0⟩ := hW
                    have htw_S0 : tw.toNat ∈ S0 :=
                      (nonValueSlot_tsInner_r31 s S0 tw.toNat hWT0.1 htw_nz_nat htw_wrs).1
                    have hwf_hg : HtabWF ent_hg tw.toNat :=
                      (htabWF_with_locals s chg (ent.clock - 1) tw.toNat).2 (hWT0.1.2.1 _ htw_S0).1
                    obtain ⟨f0, f1, rfl, _⟩ := WkBal.htab_get_ret_in_values ent_hg tw kw
                      hcode hchg_t' hchg_k' hwf_hg v_old
                      (by dsimp only [ent_hg]; rw [hrun_hg])
                    have hro_hg := FunSpec.at_lookup EvmFrameSpecs.ro_htab_get ent hcode
                      _ (sourceFnBody Guest.Software.guestFn_htab_get) chg rhg hlk_hg
                      (guestInv_callEntry ent chg hWent.1.1) (by rw [hrun_hg]; simp)
                    have hro_hg' : ((evaluateHOLFiniteState ent_hg
                        (sourceFnBody Guest.Software.guestFn_htab_get)).2) = _ :=
                      hro_hg (by rw [hrun_hg]; exact Or.inl ⟨_, rfl⟩)
                    dsimp only [ent_hg] at hro_hg'
                    rw [hrun_hg] at hro_hg'
                    dsimp only at hro_hg'
                    set s_old := setVarHOLFinite (ofString "old")
                      (.rStruct [.val (.word f0), .val (.word f1)])
                      { p_hg with locals := ent.locals }
                    have heff_old : WorldEff ent s_old [] [] ["heap_ptr"] :=
                      ((WorldEff.refl ent [] [] ["heap_ptr"] hWent.1 hcode).of_readOnly hro_hg').locals_clock _ _
                    have hg_all_old : ∀ k : MlS, s_old.globals.lookup k = ent.globals.lookup k := by
                      intro k; dsimp only [s_old, setVarHOLFinite]; rw [hro_hg']; rfl
                    have hold_t : s_old.locals.lookup (ofString "t") = some (.val (.word tw)) := by
                      simp [s_old, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_t,
                        show ofString "old" ≠ ofString "t" by decide]
                    have hold_k : s_old.locals.lookup (ofString "key") = some (.val (.word kw)) := by
                      simp [s_old, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_k,
                        show ofString "old" ≠ ofString "key" by decide]
                    have hold_v : s_old.locals.lookup (ofString "value") = some (.val (.word vlw)) := by
                      simp [s_old, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_v,
                        show ofString "old" ≠ ofString "value" by decide]
                    have hold_old : s_old.locals.lookup (ofString "old") =
                        some (.rStruct [.val (.word f0), .val (.word f1)]) := by
                      simp [s_old, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                    rcases htail_old : evaluateHOLFiniteState s_old
                        (journalAppendTailProg 4#64 (.rfield 0 (.var .local (ofString "old")))
                          (.seq
                            (.call (some (none, none)) (ofString "htab_set")
                              [.var .local (ofString "t"), .var .local (ofString "key"), .var .local (ofString "value")])
                            (.return (.const 0#64)))) with ⟨rtail, ptail⟩
                    rw [htail_old] at hrun; dsimp only at hrun
                    have hrtail_eq : rtail = some (.returned rv) := hrun.1
                    have hpost_ptail : post = { ptail with locals := (HolFiniteMapExact.resVarEq ptail.locals
                        (ofString "old", ent.locals.lookup (ofString "old"))) } := hrun.2.symm
                    obtain ⟨mid, tailPost, hstep_j, _, hwrs_mid, _, _, hmid_t, hmid_k, hmid_v_eq, hmid_tail, hptail_tp⟩ :=
                      journal_append_block_step_r31 ent s_old
                        4#64 (.rfield 0 (.var .local (ofString "old"))) tw kw f0 f1 f0
                        hWent heff_old hg_all_old hold_t hold_k hold_old
                        (fun st hst => by simp [evalHOLExact, toExact, hst])
                        (fun S hTS => by
                          have hnv := nonValueSlot_tsInner_r31 ent S tw.toNat hTS htw_nz_nat htw_wrs_ent
                          refine ⟨hnv.1, ?_⟩
                          dsimp only
                          rw [hnv.2.2.2.2.2.2]
                          simp only [show ("ts.inner" = "ts+32") ↔ False by decide, and_false, ↓reduceIte,
                            List.mem_singleton]
                          rintro p rfl
                          exact htw_wrs_ent)
                        (by rw [htail_old, hrtail_eq])
                    have hmid_v : mid.locals.lookup (ofString "value") = some (.val (.word vlw)) :=
                      hmid_v_eq.trans hold_v
                    have hW_mid : WorldOK mid := hstep_j.worldOK_bufs (fun _ h => by cases h) hWent
                    have hmid_code : mid.code = originalRuntimeCode := hW_mid.1.1.code
                    have htw_wrs_mid : (tw.toNat, "ts.inner") ∈ worldRoleSlots mid := by
                      rwa [hwrs_mid]
                    obtain ⟨s_hs, hhs, hret_hs⟩ := seq_call0_ret_inv hmid_tail
                    rw [evaluateHOLFiniteState_return] at hret_hs
                    simp only [evalHOLExact, toExact, shapeOfHOLExact, sizeOfShapeWithContextHOL,
                      show (1 : Nat) ≤ 32 by decide, ↓reduceIte, emptyLocalsHOLFinite] at hret_hs
                    have htp_eq : tailPost = { s_hs with locals := HolFiniteMapExact.empty } :=
                      ((Prod.mk.inj hret_hs).2).symm
                    rw [evaluateHOLFiniteState_call] at hhs
                    have hargs_hs : evalListHOLFinite mid
                        (h := fun a => Classical.propDecidable (mid.memaddrs a))
                        [.var .local (ofString "t"), .var .local (ofString "key"), .var .local (ofString "value")] =
                        some [.val (.word tw), .val (.word kw), .val (.word vlw)] := by
                      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, hmid_t, hmid_k, hmid_v]
                    rw [hargs_hs] at hhs; dsimp only at hhs
                    rcases hlk_hs : lookupCodeHOLFinite mid.code.lookup (ofString "htab_set")
                        [.val (.word tw), .val (.word kw), .val (.word vlw)] with _ | ⟨bhs, chs, rhs'⟩
                    · rw [hlk_hs] at hhs; simp at hhs
                    · rw [hlk_hs] at hhs; dsimp only at hhs
                      by_cases hcz_mid : mid.clock = 0
                      · simp [hcz_mid] at hhs
                      rw [if_neg hcz_mid] at hhs
                      obtain ⟨v1_hs, _, _, he1_hs, _, _, hchs_t, _, _⟩ := R16WkAcctWs.callee_param_three mid
                        (ofString "htab_set") (ofString "t") (ofString "key") (ofString "value")
                        .one .one .one _ _ (by rw [hmid_code]; exact EvmFrameSpecs.lookup_htab_set)
                        (.var .local (ofString "t")) (.var .local (ofString "key"))
                        (.var .local (ofString "value")) _ bhs chs rhs' hargs_hs hlk_hs
                      have hv1_hs_eq : v1_hs = .val (.word tw) := by
                        simp [evalAt, evalHOLExact, toExact, hmid_t] at he1_hs; exact he1_hs.symm
                      subst hv1_hs_eq
                      let ent_hs := callEntryStateHOLFinite mid chs
                      have hloc_t_hs : locN ent_hs "t" = tw.toNat := by
                        simp [locN, ent_hs, callEntryStateHOLFinite, hchs_t]
                      rcases hrun_hs : evaluateHOLFiniteState ent_hs bhs with ⟨res_hs, p_hs⟩
                      dsimp only [ent_hs] at hrun_hs
                      rw [hrun_hs] at hhs
                      cases res_hs with
                      | none => simp at hhs
                      | some cr_hs2 =>
                        cases cr_hs2 with
                        | returned v_hs =>
                          dsimp only at hhs
                          split at hhs <;> try simp at hhs
                          have hs_hs_eq : s_hs = { p_hs with locals := mid.locals } := hhs.symm
                          have hArg_hs : HtabArgWF ent_hs := by
                            obtain ⟨hAm, Sm, hTm, _⟩ := hW_mid
                            have ht0_Sm := (nonValueSlot_tsInner_r31 mid Sm tw.toNat hTm htw_nz_nat htw_wrs_mid).1
                            refine ⟨localsFree_arenaReady mid _ _ hAm, ?_, ?_⟩
                            · rw [hloc_t_hs]
                              exact (htabWF_with_locals mid chs (mid.clock - 1) _).2 (hTm.2.1 _ ht0_Sm).1
                            · rw [hloc_t_hs]
                              exact fun i hi => ((hTm.2.1 _ ht0_Sm).2 i hi).1
                          have hexit := FunSpec.at_lookup htab_set_spec mid hmid_code
                            _ bhs chs rhs' hlk_hs hArg_hs (by rw [hrun_hs]; simp)
                          rw [hrun_hs] at hexit
                          have hex := hexit v_hs rfl
                          dsimp only [HtabExit] at hex
                          rw [hloc_t_hs] at hex
                          obtain ⟨hAp_hs, hwf_hs, hh0_hs, _, hhp_hs, hfp_hs, hfr_hs, hg_hs⟩ := hex
                          have hbe_hs : p_hs.be = mid.be := by
                            have inv := (PanRunBounded.evaluateHOLFiniteState_metadata ent_hs bhs).2.2.1
                            dsimp only [ent_hs] at inv; rw [hrun_hs] at inv; exact inv
                          have hstep_hs0 : WorldStepSc (bufRegions []) ["heap_ptr"] stdKeep NoExtra mid none p_hs :=
                            worldStepSc_of_htabExit_nonValue hW_mid hbe_hs hg_hs hg_hs
                              (fun Sm hTm => by
                                have hnv := nonValueSlot_tsInner_r31 mid Sm tw.toNat hTm htw_nz_nat htw_wrs_mid
                                exact ⟨hnv.1, hnv.2.1, hnv.2.2.1, hnv.2.2.2.1, hnv.2.2.2.2.1, hnv.2.2.2.2.2.1⟩)
                              hAp_hs hwf_hs hh0_hs hhp_hs hfp_hs hfr_hs
                          have hstep_hs : WorldStepSc (bufRegions []) ["heap_ptr", "journal_n"]
                              stdKeep NoExtra mid none post := by
                            have hp_post : post = { p_hs with locals := post.locals, clock := post.clock } := by
                              rw [hpost_ptail, hptail_tp, htp_eq, hs_hs_eq]
                            rw [hp_post]
                            exact (hstep_hs0.with_locals_clock post.locals post.clock).mono_bufs
                              (fun _ h => by cases h) (by simp)
                          have hstep_ent : WorldStepSc (bufRegions []) ["heap_ptr", "journal_n"]
                              stdKeep NoExtra ent none post :=
                            WorldStepSc.trans (fun _ h => by cases h)
                              (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp)
                              hstep_j hstep_hs
                          exact (hstep_ent.from_entry).mono_bufs
                            (fun _ h => by cases h)
                            (fun g hg => by
                              simp at hg
                              rcases hg with rfl | rfl
                              · exact hhp_in
                              · exact hjn_in)
                        | _ => simp at hhs
            · rename_i hbad; simp only [hbad] at hfr; exact absurd hfr not_flowingOrResumes_error


theorem jset_ts32_fresh_inner_step_r31 {F : Type}
    (s : PanSemStateFiniteExact 64 F) {B : BufList} {gw : List String}
    (hhp_in : "heap_ptr" ∈ gw) (hjn_in : "journal_n" ∈ gw)
    (tExp kExp vExp : ExpHOL 64) (tw kw iw : BitVec 64)
    (ht_ev : evalAt s tExp = some (.val (.word tw)))
    (hk_ev : evalAt s kExp = some (.val (.word kw)))
    (hv_ev : evalAt s vExp = some (.val (.word iw)))
    (hW : WorldOK s) (hcode : s.code = originalRuntimeCode)
    (hts_nz : globN s "ts" ≠ 0) (htw_nz : tw ≠ 0#64) (hiw_nz : iw ≠ 0#64)
    (htts : tw.toNat = memW s (globN s "ts" + 32))
    (hkey_iw : hdr s iw.toNat 0 = roleKeyLen "ts.inner")
    (hf_iw : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ iw.toNat)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "jset") [tExp, kExp, vExp])).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "jset") [tExp, kExp, vExp])).1) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "jset") [tExp, kExp, vExp])
    out.1 = none ∧ out.2.locals = s.locals ∧
    WorldStepIn (fun _ => [tw.toNat, iw.toNat]) (bufRegions B) gw stdKeep NoExtra s out.1 out.2 ∧
      globN out.2 "scratch_ptr" ≤ globN s "scratch_ptr" ∧
      (iw.toNat, "ts.inner") ∈ worldRoleSlots out.2 := by
  dsimp only
  set argsL : List (ExpHOL 64) := [tExp, kExp, vExp]
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) argsL with _ | values
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    have hargs_fin : evalListHOLFinite s
        (h := fun a => Classical.propDecidable (s.memaddrs a)) argsL = some values := by
      rwa [evalListHOLFinite_eq_toExact]
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "jset") values with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        have hbody_eq := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "jset")
          _ _ body' _ ret' values callee lookup_jset (by rwa [← hcode])
        obtain ⟨v1, v2, v3, he1, he2, he3, hc_t, hc_k, hc_v⟩ := R16WkAcctWs.callee_param_three s (ofString "jset")
          (ofString "t") (ofString "key") (ofString "value") .one .one .one _ _
          (by rw [hcode]; exact lookup_jset) _ _ _ values body' callee ret' hargs_fin hl
        have hv1_eq : v1 = .val (.word tw) := by rw [ht_ev] at he1; exact Option.some.inj he1.symm
        have hv2_eq : v2 = .val (.word kw) := by rw [hk_ev] at he2; exact Option.some.inj he2.symm
        have hv3_eq : v3 = .val (.word iw) := by rw [hv_ev] at he3; exact Option.some.inj he3.symm
        subst hv1_eq hv2_eq hv3_eq
        let ent := callEntryStateHOLFinite s callee
        rcases hrun : evaluateHOLFiniteState ent body' with ⟨res, post⟩
        simp only [ent, hrun] at hnt hfr ⊢
        cases res with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | exception eid ev =>
            exfalso
            have hne : eid ≠ ofString "TrapErr" := by
              rcases hfr with h | h | h | ⟨_, h⟩ | ⟨_, _, h, hne⟩ <;> try simp at h
              obtain ⟨rfl, _⟩ := h; exact hne
            have hbody_ok : noCatchableRaise trapOnlyCallees body' = true :=
              trapOnlyCallees_good (ofString "jset") (by decide) values body' callee ret' (by rwa [← hcode])
            have hno := evaluate_noCatchableRaise trapOnlyCallees trapOnlyCallees_good
              body' hbody_ok ent hcode eid ev hne
            dsimp only [ent] at hno; rw [hrun] at hno; exact hno rfl
          | returned rv =>
            dsimp only at hfr ⊢
            split
            · have hWent : WorldOK ent := localsFree_worldOK s callee (s.clock - 1) hW
              have htw_nz_nat : tw.toNat ≠ 0 := fun h0 => htw_nz (BitVec.eq_of_toNat_eq (by simpa using h0))
              have hiw_nz_nat : iw.toNat ≠ 0 := fun h0 => hiw_nz (BitVec.eq_of_toNat_eq (by simpa using h0))
              have hent_t : ent.locals.lookup (ofString "t") = some (.val (.word tw)) := hc_t
              have hent_k : ent.locals.lookup (ofString "key") = some (.val (.word kw)) := hc_k
              have hent_v : ent.locals.lookup (ofString "value") = some (.val (.word iw)) := hc_v
              rw [hbody_eq] at hrun
              have hbody_fold : sourceFnBody Guest.Software.guestFn_jset =
                  .decCall (ofString "old") (.comb [.one, .one]) (ofString "htab_get")
                    [.var .local (ofString "t"), .var .local (ofString "key")]
                    (journalAppendTailProg 4#64 (.rfield 0 (.var .local (ofString "old")))
                      (.seq
                        (.call (some (none, none)) (ofString "htab_set")
                          [.var .local (ofString "t"), .var .local (ofString "key"), .var .local (ofString "value")])
                        (.return (.const 0#64)))) := rfl
              change evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_jset) =
                (some (.returned rv), post) at hrun
              rw [hbody_fold] at hrun
              rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun
              have hargs_hg : evalListHOLFinite ent
                  (h := fun a => Classical.propDecidable (ent.memaddrs a))
                  [.var .local (ofString "t"), .var .local (ofString "key")] =
                  some [.val (.word tw), .val (.word kw)] := by
                simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, hent_t, hent_k]
              rw [hargs_hg] at hrun; dsimp only at hrun
              rcases hlk_hg : lookupCodeHOLFinite ent.code.lookup (ofString "htab_get")
                  [.val (.word tw), .val (.word kw)] with _ | ⟨bhg, chg, rhg⟩
              · rw [hlk_hg] at hrun; simp at hrun
              · rw [hlk_hg] at hrun; dsimp only at hrun
                by_cases hcz_hg : ent.clock = 0
                · simp [hcz_hg] at hrun
                rw [if_neg hcz_hg] at hrun
                have hb_hg_eq := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
                  (ofString "htab_get") _ _ bhg _ rhg _ chg EvmFrameSpecs.lookup_htab_get
                  (by rwa [← show ent.code = originalRuntimeCode from hcode])
                subst hb_hg_eq
                obtain ⟨v1_hg, v2_hg, he1_hg, he2_hg, hchg_t, hchg_k⟩ :=
                  callee_param_two_r16_code ent (ofString "htab_get")
                    (ofString "t") (ofString "key") .one .one _ _
                    (by rw [show ent.code = originalRuntimeCode from hcode]; exact EvmFrameSpecs.lookup_htab_get)
                    (.var .local (ofString "t")) (.var .local (ofString "key"))
                    _ _ chg rhg hargs_hg hlk_hg
                have hv12_hg : v1_hg = .val (.word tw) ∧ v2_hg = .val (.word kw) := by
                  simp [evalAt, evalHOLExact, toExact, hent_t] at he1_hg
                  simp [evalAt, evalHOLExact, toExact, hent_k] at he2_hg
                  exact ⟨he1_hg.symm, he2_hg.symm⟩
                rcases hv12_hg with ⟨rfl, rfl⟩
                let ent_hg := callEntryStateHOLFinite ent chg
                have hchg_t' : ent_hg.locals.lookup (ofString "t") = some (.val (.word tw)) := hchg_t
                have hchg_k' : ent_hg.locals.lookup (ofString "key") = some (.val (.word kw)) := hchg_k
                rcases hrun_hg : evaluateHOLFiniteState ent_hg
                    (sourceFnBody Guest.Software.guestFn_htab_get) with ⟨res_hg, p_hg⟩
                dsimp only [ent_hg] at hrun_hg
                rw [hrun_hg] at hrun
                cases res_hg with
                | none => simp at hrun
                | some cr_hg =>
                  cases cr_hg with
                  | exception _ _ =>
                    exfalso
                    dsimp only at hrun; injection hrun with hr_eq _; cases hr_eq
                  | timeOut | error | «break» | «continue» | finalFfi _ => simp at hrun
                  | returned v_old =>
                    dsimp only at hrun
                    split at hrun <;> try simp at hrun
                    obtain ⟨_, S0, hWT0⟩ := hW
                    have htw_S0 : tw.toNat ∈ S0 :=
                      (ts32Slot_disj s S0 hWT0.1 hts_nz (htts ▸ htw_nz_nat)).1 |> fun h => htts ▸ h
                    have hwf_hg : HtabWF ent_hg tw.toNat :=
                      (htabWF_with_locals s chg (ent.clock - 1) tw.toNat).2 (hWT0.1.2.1 _ htw_S0).1
                    obtain ⟨f0, f1, rfl, hf1_in⟩ := WkBal.htab_get_ret_in_values ent_hg tw kw
                      hcode hchg_t' hchg_k' hwf_hg v_old
                      (by dsimp only [ent_hg]; rw [hrun_hg])
                    have hro_hg := FunSpec.at_lookup EvmFrameSpecs.ro_htab_get ent hcode
                      _ (sourceFnBody Guest.Software.guestFn_htab_get) chg rhg hlk_hg
                      (guestInv_callEntry ent chg hWent.1.1) (by rw [hrun_hg]; simp)
                    have hro_hg' : ((evaluateHOLFiniteState ent_hg
                        (sourceFnBody Guest.Software.guestFn_htab_get)).2) = _ :=
                      hro_hg (by rw [hrun_hg]; exact Or.inl ⟨_, rfl⟩)
                    dsimp only [ent_hg] at hro_hg'
                    rw [hrun_hg] at hro_hg'
                    dsimp only at hro_hg'
                    set s_old := setVarHOLFinite (ofString "old")
                      (.rStruct [.val (.word f0), .val (.word f1)])
                      { p_hg with locals := ent.locals }
                    have heff_old : WorldEff ent s_old [] [] ["heap_ptr"] :=
                      ((WorldEff.refl ent [] [] ["heap_ptr"] hWent.1 hcode).of_readOnly hro_hg').locals_clock _ _
                    have hg_all_old : ∀ k : MlS, s_old.globals.lookup k = ent.globals.lookup k := by
                      intro k; dsimp only [s_old, setVarHOLFinite]; rw [hro_hg']; rfl
                    have hold_t : s_old.locals.lookup (ofString "t") = some (.val (.word tw)) := by
                      simp [s_old, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_t,
                        show ofString "old" ≠ ofString "t" by decide]
                    have hold_k : s_old.locals.lookup (ofString "key") = some (.val (.word kw)) := by
                      simp [s_old, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_k,
                        show ofString "old" ≠ ofString "key" by decide]
                    have hold_v : s_old.locals.lookup (ofString "value") = some (.val (.word iw)) := by
                      simp [s_old, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_v,
                        show ofString "old" ≠ ofString "value" by decide]
                    have hold_old : s_old.locals.lookup (ofString "old") =
                        some (.rStruct [.val (.word f0), .val (.word f1)]) := by
                      simp [s_old, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                    rcases htail_old : evaluateHOLFiniteState s_old
                        (journalAppendTailProg 4#64 (.rfield 0 (.var .local (ofString "old")))
                          (.seq
                            (.call (some (none, none)) (ofString "htab_set")
                              [.var .local (ofString "t"), .var .local (ofString "key"), .var .local (ofString "value")])
                            (.return (.const 0#64)))) with ⟨rtail, ptail⟩
                    rw [htail_old] at hrun; dsimp only at hrun
                    have hrtail_eq : rtail = some (.returned rv) := hrun.1
                    have hpost_ptail : post = { ptail with locals := (HolFiniteMapExact.resVarEq ptail.locals
                        (ofString "old", ent.locals.lookup (ofString "old"))) } := hrun.2.symm
                    obtain ⟨mid, tailPost, hstep_j, hWT_mid_prop, hwrs_mid, hhdr_mid, hjrs_sub_mid,
                        hmid_t, hmid_k, hmid_v_eq, hmid_tail, hptail_tp⟩ :=
                      journal_append_block_step_r31 ent s_old
                        4#64 (.rfield 0 (.var .local (ofString "old"))) tw kw f0 f1 f0
                        hWent heff_old hg_all_old hold_t hold_k hold_old
                        (fun st hst => by simp [evalHOLExact, toExact, hst])
                        (fun S hTS => by
                          have hts_ent_nz : globN ent "ts" ≠ 0 := hts_nz
                          have hm32_ent : memW ent (globN ent "ts" + 32) = memW s (globN s "ts" + 32) := rfl
                          have ht0_nz : memW s (globN s "ts" + 32) ≠ 0 := htts ▸ htw_nz_nat
                          obtain ⟨ht0_S, _, _, _, _, hne_16⟩ := ts32Slot_disj ent S hTS hts_ent_nz (by rw [hm32_ent]; exact ht0_nz)
                          have htw_S : tw.toNat ∈ S := by rwa [htts, ← hm32_ent]
                          have hjr_32 : journalRole ent tw.toNat = "ts+32" := by
                            unfold journalRole
                            rw [if_neg (fun ⟨_, h16⟩ => hne_16 (by rw [hm32_ent, ← htts]; exact h16.symm))]
                            rw [if_pos ⟨hts_ent_nz, by rw [hm32_ent]; exact htts⟩]
                          have htw_wrs : (tw.toNat, "ts+32") ∈ worldRoleSlots ent := by
                            have hm32_wrs : (memW ent (globN ent "ts" + 32), "ts+32") ∈ worldRoleSlots ent := by
                              apply mem_worldRoleSlots_recRole ent "ts" 32 "ts+32" hts_ent_nz
                                (by rw [hm32_ent]; exact ht0_nz)
                              apply List.mem_append.2; right
                              unfold recRoles; rw [if_neg hts_ent_nz]
                              exact List.mem_map.2 ⟨(32, "ts+32"), by simp, rfl⟩
                            rwa [hm32_ent, ← htts] at hm32_wrs
                          refine ⟨htw_S, ?_⟩
                          dsimp only
                          rw [hjr_32]
                          intro p hp
                          rcases List.mem_cons.1 hp with rfl | hp'
                          · exact htw_wrs
                          · split at hp'
                            · rename_i hf0_cond
                              simp only [List.mem_singleton] at hp'; subst hp'
                              have hf0_nz : f0 ≠ 0#64 := fun hz => hf0_cond.1 (by simp [hz])
                              have hf1_vals : f1.toNat ∈ htabValues ent tw.toNat := hf1_in hf0_nz
                              have hf1_S : f1.toNat ∈ S := by
                                have hv_in : HtabValuesIn ent (memW ent (globN ent "ts" + 32)) S :=
                                  hTS.2.2.2.2.2.2.2.2.1 hts_ent_nz ht0_S
                                have hf1_v32 : f1.toNat ∈ htabValues ent (memW ent (globN ent "ts" + 32)) := by
                                  rwa [hm32_ent, ← htts]
                                obtain ⟨idx, hidx_mem, hidx_eq⟩ := List.mem_map.1 hf1_v32
                                rw [← hidx_eq]
                                exact hv_in idx (List.mem_range.1 hidx_mem)
                              have hf1_nz : f1.toNat ≠ 0 := by
                                intro h0
                                have hwf0 : HtabWF ent 0 := h0 ▸ (hTS.2.1 _ hf1_S).1
                                have hin0 := (hwf0.1 (0, 88) (by unfold htabFootprint; simp)).1
                                unfold Inside sourceBase at hin0; omega
                              unfold worldRoleSlots
                              refine List.mem_filter.2 ⟨?_, by simp [hf1_nz]⟩
                              have hnr : (f1.toNat, "ts.inner") ∈ nestRoles ent "ts" "ts.inner" := by
                                unfold nestRoles
                                rw [if_neg hts_ent_nz, if_neg (by rw [hm32_ent]; exact ht0_nz)]
                                refine List.mem_map.2 ⟨f1.toNat, ?_, rfl⟩
                                rwa [hm32_ent, ← htts]
                              exact List.mem_append_left _ (List.mem_append_right _ hnr)
                            · cases hp')
                        (by rw [htail_old, hrtail_eq])
                    have hmid_v : mid.locals.lookup (ofString "value") = some (.val (.word iw)) :=
                      hmid_v_eq.trans hold_v
                    have hW_mid : WorldOK mid := hstep_j.worldOK_bufs (fun _ h => by cases h) hWent
                    have hA_mid : ArenaReady mid := hW_mid.1
                    obtain ⟨s_hs, hhs, hret_hs⟩ := seq_call0_ret_inv hmid_tail
                    rw [evaluateHOLFiniteState_return] at hret_hs
                    simp only [evalHOLExact, toExact, shapeOfHOLExact, sizeOfShapeWithContextHOL,
                      show (1 : Nat) ≤ 32 by decide, ↓reduceIte, emptyLocalsHOLFinite] at hret_hs
                    have htp_eq : tailPost = { s_hs with locals := HolFiniteMapExact.empty } :=
                      ((Prod.mk.inj hret_hs).2).symm
                    have hts_mid : globN mid "ts" = globN ent "ts" :=
                      globN_eq_of_lookup (hstep_j.1.2.2.1 (ofString "ts") (by decide))
                    have hts_mid_nz : globN mid "ts" ≠ 0 := by rwa [hts_mid]
                    have hm32_mid : memW mid (globN mid "ts" + 32) = memW ent (globN ent "ts" + 32) := by
                      rw [hts_mid]
                      exact hstep_j.1.2.2.2.1 ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64])
                        (by simp [stdKeep]) hts_nz 32 (by simp) (fun _ h => by cases h)
                    have htts_mid : tw.toNat = memW mid (globN mid "ts" + 32) := by
                      rw [hm32_mid]; exact htts
                    have hf_iw_mid : ∀ a ∈ worldRoleSlots mid ++ journalRoleSlots mid, a.1 ≠ iw.toNat :=
                      fun a ha => hf_iw a (hjrs_sub_mid a ha)
                    obtain ⟨_, Sm0, hWTm0⟩ := hW_mid
                    obtain ⟨Ndm0, hWTm0_with⟩ := (worldTyped_iff_with mid Sm0).1 hWTm0
                    have htw_Sm0 : tw.toNat ∈ Sm0 :=
                      htts_mid ▸ (ts32Slot_disj mid Sm0 hWTm0.1 hts_mid_nz (htts_mid ▸ htw_nz_nat)).1
                    have het_mid : evalAt mid (.var .local (ofString "t")) = some (.val (.word tw)) := by
                      simpa [evalAt, evalHOLExact, toExact] using hmid_t
                    have hek_mid : evalAt mid (.var .local (ofString "key")) = some (.val (.word kw)) := by
                      simpa [evalAt, evalHOLExact, toExact] using hmid_k
                    have hev_mid : evalAt mid (.var .local (ofString "value")) = some (.val (.word iw)) := by
                      simpa [evalAt, evalHOLExact, toExact] using hmid_v
                    have hfr_hs : FlowingOrResumes (evaluateHOLFiniteState mid
                        (.call (some (none, none)) (ofString "htab_set")
                          [.var .local (ofString "t"), .var .local (ofString "key"), .var .local (ofString "value")])).1 := by
                      rw [hhs]; exact Or.inl rfl
                    obtain ⟨he_hs, hv_hs, hbe_hs, hsp_hs, _⟩ :=
                      merge_set_call_flow_props mid
                        (.var .local (ofString "t")) (.var .local (ofString "key")) (.var .local (ofString "value"))
                        tw kw iw het_mid hek_mid hev_mid hA_mid
                        (hWTm0.1.2.1 _ htw_Sm0).1
                        (fun i him => ((hWTm0.1.2.1 _ htw_Sm0).2 i him).1)
                        hfr_hs
                    rw [hhs] at he_hs hv_hs hbe_hs hsp_hs
                    dsimp only at he_hs hv_hs hbe_hs hsp_hs
                    have hp_out := ts32_outer_kept_r31 hA_mid hWTm0_with htw_Sm0 he_hs hts_mid_nz
                    have hmem_nest := (ts32_nestRoles_provenance_r31 hts_mid_nz htts_mid htw_nz_nat
                      hp_out.1 (hp_out.2.trans htts_mid.symm) hv_hs).1
                    have hwrs_shs : (iw.toNat, "ts.inner") ∈ worldRoleSlots s_hs := by
                      unfold worldRoleSlots
                      refine List.mem_filter.2 ⟨?_, by simp [hiw_nz_nat]⟩
                      exact List.mem_append_left _ (List.mem_append_right _ hmem_nest)
                    have hp_post : post = { s_hs with locals := post.locals, clock := post.clock } := by
                      rw [hpost_ptail, hptail_tp, htp_eq]
                    have hg_shs : GlobalsKept ["heap_ptr", "journal_n"] mid s_hs := by
                      intro k hk
                      apply he_hs.2.2.2.2.2.2.2 k
                      intro hm; simp at hm; subst hm; exact hk (by simp)
                    have hK_shs : RecordsKept (bufRegions []) stdKeep mid s_hs := by
                      intro rec hrec hn k hks _
                      have hrec_sz : ∃ sz, (rec.1, sz) ∈ typedRecords ∧
                          ofString rec.1 ≠ ofString "heap_ptr" ∧ k % 8 = 0 ∧ k + 8 ≤ sz := by
                        simp only [stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
                        rcases hrec with rfl | rfl | rfl | rfl
                        · refine ⟨40, by decide, by decide, ?_⟩; simp at hks; omega
                        · refine ⟨80, by decide, by decide, ?_⟩; simp at hks; omega
                        · refine ⟨72, by decide, by decide, ?_⟩; simp at hks; omega
                        · refine ⟨88, by decide, by decide, ?_⟩; simp at hks; omega
                      obtain ⟨sz, hrec', hg, hk8, hbound⟩ := hrec_sz
                      have hh := merge_set_record_word_kept hA_mid hWTm0_with htw_Sm0 he_hs
                        rec.1 sz k hrec' hg hn hk8 hbound
                      rwa [globN_eq_of_lookup (he_hs.2.2.2.2.2.2.2 (ofString rec.1)
                        (by simpa using hg))] at hh
                    have hstep_ent_shs : WorldStepIn (fun _ => [tw.toNat, iw.toNat]) (bufRegions [])
                        ["heap_ptr", "journal_n"] stdKeep NoExtra ent none s_hs := by
                      obtain ⟨⟨_, hhp12, hG12, hK12, _⟩, _⟩ := hstep_j
                      have hhp23 : globN mid "heap_ptr" ≤ globN s_hs "heap_ptr" := he_hs.2.2.2.2.1
                      refine ⟨he_hs.1, le_trans hhp12 hhp23,
                        fun k hk => (hG12 k hk).trans (hg_shs k hk), ?_, ?_⟩
                      · intro rec hrec hnz k hk hno
                        have hrec_not : ofString rec.1 ∉ (["heap_ptr", "journal_n"] : List String).map ofString := by
                          simp only [stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
                          rcases hrec with rfl | rfl | rfl | rfl <;> decide
                        have hg_rec : globN mid rec.1 = globN ent rec.1 :=
                          globN_eq_of_lookup (hG12 (ofString rec.1) hrec_not)
                        have h2 : memW s_hs (globN mid rec.1 + k) = memW mid (globN mid rec.1 + k) :=
                          hK_shs rec hrec (by rw [hg_rec]; exact hnz) k hk (fun _ h => by cases h)
                        rw [hg_rec] at h2
                        exact h2.trans (hK12 rec hrec hnz k hk hno)
                      · intro S' Nd' hWT_ent howned _
                        have ht' : tw.toNat ∈ S' := howned tw.toNat (by simp)
                        have hi' : iw.toNat ∈ S' := howned iw.toNat (by simp)
                        obtain ⟨hWT_mid, hOG12, hFO12⟩ := hWT_mid_prop S' Nd' hWT_ent
                        have hkey_mid : hdr mid iw.toNat 0 = roleKeyLen "ts.inner" := by
                          rw [hhdr_mid S' hWT_ent.1 iw.toNat hi']
                          exact hkey_iw
                        have hWT_shs : WorldTypedWith s_hs S' Nd' :=
                          ts32_world_typed_r31 hA_mid hWT_mid ht' he_hs hbe_hs
                            hts_mid_nz htw_nz_nat htts_mid hi' hkey_mid hf_iw_mid hv_hs
                        have hOG23 : OwnedGrows mid s_hs (worldOwned mid S' Nd') (worldOwned s_hs S' Nd') :=
                          ts32_owned_grows_r31 hA_mid hWT_mid ht' he_hs hbe_hs
                            hts_mid_nz htw_nz_nat htts_mid
                        refine ⟨S', Nd', fun _ h => h, hWT_shs, ?_, ?_, trivial⟩
                        · intro o ho
                          rcases hOG23 o ho with rfl | ⟨j, hj, hin_oj⟩ | hin_o23
                          · exact Or.inl rfl
                          · rcases hOG12 j hj with rfl | ⟨k, hk, hin_jk⟩ | hin_j12
                            · left
                              rcases o with ⟨o1, o2⟩
                              dsimp only [Inside] at hin_oj
                              have ho1 : o1 = 0 := by omega
                              have ho2 : o2 = 0 := by omega
                              rw [ho1, ho2]
                            · exact Or.inr (Or.inl ⟨k, hk, le_trans hin_jk.1 hin_oj.1, le_trans hin_oj.2 hin_jk.2⟩)
                            · exact Or.inr (Or.inr ⟨le_trans hin_j12.1 hin_oj.1,
                                le_trans hin_oj.2 (le_trans hin_j12.2 hhp23)⟩)
                          · exact Or.inr (Or.inr ⟨le_trans hhp12 hin_o23.1, hin_o23.2⟩)
                        · intro a ha hhf
                          have hm12 : mid.memory a = ent.memory a := hFO12 a ha hhf
                          have hm23 : s_hs.memory a = mid.memory a := by
                            apply he_hs.2.2.2.2.2.2.1 a
                            · intro j hj hh
                              obtain ⟨hc1, hc2⟩ := hh
                              have hj_wo : j ∈ worldOwned mid S' Nd' :=
                                List.mem_append_left _ (List.mem_append_left _
                                  (List.mem_flatMap.2 ⟨tw.toNat, ht', hj⟩))
                              rcases hOG12 j hj_wo with rfl | ⟨k, hk, hin_jk⟩ | hin_j12
                              · dsimp only at hc2; omega
                              · exact ha k (List.mem_append_left _ (List.mem_append_left _ hk))
                                  ⟨by dsimp only [Inside] at hin_jk; omega,
                                   by dsimp only [Inside] at hin_jk; omega⟩
                              · have hp2_lim : globN mid "heap_ptr" ≤ heapLimit := hA_mid.2.2.1
                                exact hhf ⟨by unfold heapFree; dsimp only [Inside] at hin_j12 ⊢; omega,
                                           by unfold heapFree; dsimp only [Inside] at hin_j12 ⊢; omega⟩
                            · intro ⟨hc1, hc2⟩
                              have hp_shs_lim : globN s_hs "heap_ptr" ≤ heapLimit := he_hs.1.2.2.1
                              exact hhf ⟨by unfold heapFree; dsimp only at hc1 hc2 ⊢; omega,
                                         by unfold heapFree; dsimp only at hc1 hc2 ⊢; omega⟩
                          exact hm23.trans hm12
                    have hstep_ent_post : WorldStepIn (fun _ => [tw.toNat, iw.toNat]) (bufRegions [])
                        ["heap_ptr", "journal_n"] stdKeep NoExtra ent none
                        { post with locals := s.locals } := by
                      have hp_lc : { post with locals := s.locals } =
                          { s_hs with locals := s.locals, clock := post.clock } := by
                        rw [hp_post]
                      rw [hp_lc]
                      exact worldStepIn_with_locals_clock_r31 s.locals post.clock hstep_ent_shs
                    have hstep_s : WorldStepIn (fun _ => [tw.toNat, iw.toNat]) (bufRegions B) gw
                        stdKeep NoExtra s none { post with locals := s.locals } :=
                      worldStepIn_mono_bufs_r31 (fun _ h => by cases h)
                        (fun g hg => by
                          simp at hg
                          rcases hg with rfl | rfl
                          · exact hhp_in
                          · exact hjn_in)
                        (worldStepIn_of_pre_locals_clock_r31 rfl hstep_ent_post)
                    have hsp_le : globN { post with locals := s.locals } "scratch_ptr" ≤ globN s "scratch_ptr" := by
                      have hp_lc : { post with locals := s.locals } =
                          { s_hs with locals := s.locals, clock := post.clock } := by
                        rw [hp_post]
                      rw [hp_lc]
                      change globN s_hs "scratch_ptr" ≤ globN ent "scratch_ptr"
                      rw [hsp_hs]
                      exact hstep_j.2
                    have hwrs_out : (iw.toNat, "ts.inner") ∈ worldRoleSlots { post with locals := s.locals } := by
                      have hp_lc : { post with locals := s.locals } =
                          { s_hs with locals := s.locals, clock := post.clock } := by
                        rw [hp_post]
                      rw [hp_lc]
                      exact hwrs_shs
                    exact ⟨rfl, rfl, hstep_s, hsp_le, hwrs_out⟩
            · rename_i hbad; simp only [hbad] at hfr; exact absurd hfr not_flowingOrResumes_error

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
