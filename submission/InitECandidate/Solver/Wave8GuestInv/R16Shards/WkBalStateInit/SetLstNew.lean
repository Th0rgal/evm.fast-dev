import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBalInitFresh
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBalRemove

/-! Reusable call/`decCall` steppers for `alloc`, `lst_new`, and `htab_set`
(with exact `append ∨ set` `htabValues` postcondition), importing only prebuilt `WkBal` modules. -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBal

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
open InitECandidate.Solver.Wave8Contracts.M08
open InitECandidate.Solver.Wave8GuestInv.M11

/-! ## 1. Slice helper and `decCall_alloc_resumes` -/

theorem pairwise_disj_replace_slice {L1 mid mid' L2 : List Ivl}
    (hpw : (L1 ++ mid ++ L2).Pairwise Disj)
    (hpw_mid' : mid'.Pairwise Disj)
    (hdj_L1 : ∀ x ∈ L1, ∀ y ∈ mid', Disj x y)
    (hdj_L2 : ∀ x ∈ mid', ∀ y ∈ L2, Disj x y) :
    (L1 ++ mid' ++ L2).Pairwise Disj := by
  have h12 := List.pairwise_append.1 hpw
  have h1 := List.pairwise_append.1 h12.1
  apply List.pairwise_append.2
  refine ⟨List.pairwise_append.2 ⟨h1.1, hpw_mid', hdj_L1⟩, h12.2.1, ?_⟩
  intro a ha b hb
  rcases List.mem_append.1 ha with ha1 | ham
  · exact h12.2.2 a (List.mem_append_left _ ha1) b hb
  · exact hdj_L2 a ham b hb

theorem decCall_alloc_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (x : MlS) (nExp : ExpHOL 64) (nw : BitVec 64) (cont : ProgHOL 64)
    (hAR : ArenaReady s)
    (hn_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word nw)))
    (hnt : (evaluateHOLFiniteState s
      (.decCall x .one (ofString "alloc") [nExp] cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall x .one (ofString "alloc") [nExp] cont)).1) :
    ∃ (pw qw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      pw.toNat = globN s "heap_ptr" ∧
      qw.toNat = pw.toNat + (nw.toNat + 7) / 8 * 8 ∧
      qw.toNat ≤ heapLimit ∧
      pw.toNat ≤ qw.toNat ∧
      pw.toNat % 8 = 0 ∧
      qw.toNat % 8 = 0 ∧
      globN mid "heap_ptr" = qw.toNat ∧
      globN mid "scratch_ptr" = globN s "scratch_ptr" ∧
      globN mid "frame_mem_ptr" = globN s "frame_mem_ptr" ∧
      ArenaReady mid ∧
      mid.memory = s.memory ∧
      mid.memaddrs = s.memaddrs ∧
      mid.be = s.be ∧
      mid.globals = s.globals.update (ofString "heap_ptr", .val (.word qw)) ∧
      mid.locals.lookup x = some (.val (.word pw)) ∧
      (∀ y : MlS, y ≠ x → mid.locals.lookup y = s.locals.lookup y) ∧
      (∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = mid.globals.lookup k) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s (.decCall x .one (ofString "alloc") [nExp] cont)).1 =
        (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s (.decCall x .one (ofString "alloc") [nExp] cont)).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) } := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [nExp] = some [.val (.word nw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hn_ev]
  have hlk := pan_one_word_lookup s.code.lookup (ofString "alloc") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_alloc) nw
    (by rw [hAR.1.code]; exact R13Shards.lookup_alloc_r13)
  rw [hargs] at hnt hres; dsimp only at hnt hres; rw [hlk] at hnt hres; dsimp only at hnt hres
  by_cases hcz : s.clock = 0
  · rw [if_pos hcz] at hnt; exact absurd rfl hnt
  · rw [if_neg hcz] at hnt hres
    let cmap := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word nw))
    let ent := callEntryStateHOLFinite s cmap
    have hent_AR : ArenaReady ent := (arenaReady_with_locals s cmap (s.clock - 1)).2 hAR
    have hent_n : locN ent "n" = nw.toNat := by
      simp [ent, cmap, locN, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_alloc) with ⟨rb, sb⟩
    have hrun' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_alloc) = (rb, sb) := hrun
    rw [hrun'] at hnt hres
    cases rb with
    | none => exact absurd hres not_resumes_error
    | some rb' =>
      cases rb' with
      | timeOut => exact absurd rfl hnt
      | «break» | «continue» | error => exact absurd hres not_resumes_error
      | finalFfi _ =>
        exfalso; rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      | exception e ev =>
        exfalso
        rcases hres with ⟨_, h⟩ | ⟨e', ev', h, hne⟩
        · simp at h
        · dsimp only at h; injection h with h'; injection h' with he1 he2; subst he1 he2
          exact alloc_no_catchable_exn ent hAR.1.code e ev hne (congrArg Prod.fst hrun)
      | returned vb =>
        have hres_ent : Wave8Contracts.M12.Resumes
            (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_alloc)).1 :=
          Or.inl ⟨vb, congrArg Prod.fst hrun⟩
        obtain ⟨pw, qw, hrv_ent, hpw_eq, hqw_eq, hqw_lim, hqw8, hpw_le_qw, hsb_g, hsb_m, hsb_be, hsb_ma, hAsb, hsb_hp, hsb_sp⟩ :=
          R13Shards.alloc_body_resumes_props ent hAR.1.code hent_AR hres_ent
        rw [hrun] at hrv_ent hsb_g hsb_m hsb_be hsb_ma hAsb hsb_hp hsb_sp
        dsimp only at hrv_ent hsb_g hsb_m hsb_be hsb_ma hAsb hsb_hp hsb_sp
        injection hrv_ent with hvb; injection hvb with hvb'; subst hvb'
        rw [hent_n] at hqw_eq
        dsimp only at hnt hres
        have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word pw) : ValueHOL 64)) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word pw) : ValueHOL 64)) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        rw [if_pos hsh] at hnt hres
        let mid := setVarHOLFinite x (.val (.word pw)) { sb with locals := s.locals }
        have hmid_AR : ArenaReady mid := (arenaReady_with_locals sb _ sb.clock).2 hAsb
        have hpw8 : pw.toNat % 8 = 0 := by rw [hpw_eq]; exact hAR.2.2.2.2.2.2.1
        have hmid_fmp : globN mid "frame_mem_ptr" = globN s "frame_mem_ptr" := by
          change globN sb "frame_mem_ptr" = globN s "frame_mem_ptr"
          unfold globN; rw [hsb_g]
          simp [ent, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
        have heval_eq : evaluateHOLFiniteState s
            (.decCall x .one (ofString "alloc") [nExp] cont) =
            ((evaluateHOLFiniteState mid cont).1,
              { (evaluateHOLFiniteState mid cont).2 with
                locals := HolFiniteMapExact.resVarEq
                  (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) }) := by
          rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hargs]
          dsimp only; rw [hlk]; dsimp only
          rw [if_neg hcz, hrun']; dsimp only
          rw [if_pos hsh]
        refine ⟨pw, qw, mid, hpw_eq, hqw_eq, hqw_lim, hpw_le_qw, hpw8, hqw8,
          hsb_hp, hsb_sp, hmid_fmp, hmid_AR, hsb_m, hsb_ma, hsb_be, hsb_g,
          by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
          fun y hy => by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hy, Ne.symm hy],
          fun k hk1 => by
            change s.globals.lookup k = sb.globals.lookup k
            rw [hsb_g]
            simp [ent, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hk1, Ne.symm hk1],
          by intro hto; rw [hto] at hnt; exact hnt rfl,
          hres, by rw [heval_eq], by rw [heval_eq]⟩

/-! ## 2. Exact `lst_new` body props and call/`decCall` steppers -/

theorem lookup_lst_new_wk :
    originalRuntimeCode.lookup (ofString "lst_new") =
      some ([(ofString "esz", .one), (ofString "cap", .one)],
        sourceFnBody Guest.Software.guestFn_lst_new, .one) :=
  lookup_of_guestAst_getElem 408 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_lst_new) rfl

theorem lst_new_no_catchable_exn {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (e : MlS) (v : ValueHOL 64)
    (hne : e ≠ ofString "TrapErr") :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_lst_new)).1 ≠
      some (.exception e v) :=
  evaluate_noCatchableRaise initAllocCallees initAllocCallees_good
    (sourceFnBody Guest.Software.guestFn_lst_new) rfl s hcode e v hne

theorem lst_new_heap_props {F : Type}
    (s : PanSemStateFiniteExact 64 F) (eszw capw : BitVec 64)
    (hAR : ArenaReady s)
    (hesz_pos : 1 ≤ eszw.toNat)
    (hmul_lt : eszw.toNat * capw.toNat < 2 ^ 64)
    (hmul_al : (eszw.toNat * capw.toNat) % 8 = 0)
    (hcap_pos : 1 ≤ capw.toNat)
    (hesz : s.locals.lookup (ofString "esz") = some (.val (.word eszw)))
    (hcap : s.locals.lookup (ofString "cap") = some (.val (.word capw)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_lst_new)).1 =
      some (.returned v)) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_lst_new)).2
    ∃ lw : BitVec 64,
      v = .val (.word lw) ∧
      lw.toNat = globN s "heap_ptr" ∧
      lw.toNat % 8 = 0 ∧
      lw.toNat ≠ 0 ∧
      memW post lw.toNat = lw.toNat + 24 ∧
      memW post (lw.toNat + 8) = 0 ∧
      memW post (lw.toNat + 16) = capw.toNat ∧
      globN post "heap_ptr" = lw.toNat + 24 + eszw.toNat * capw.toNat ∧
      globN s "heap_ptr" < globN post "heap_ptr" ∧
      ArenaReady post ∧
      post.be = s.be ∧
      globN post "scratch_ptr" = globN s "scratch_ptr" ∧
      globN post "frame_mem_ptr" = globN s "frame_mem_ptr" ∧
      LstOK post lw.toNat ∧
      lstObjects post lw.toNat eszw.toNat =
        [(lw.toNat, 24), (lw.toNat + 24, eszw.toNat * capw.toNat)] ∧
      Disj (lw.toNat, 24) (lw.toNat + 24, eszw.toNat * capw.toNat) ∧
      (∀ i ∈ lstObjects post lw.toNat eszw.toNat,
        Allocated post i ∧ WordsOK post i ∧ Inside i (globN s "heap_ptr") (globN post "heap_ptr")) ∧
      FrameOutside s post [(globN s "scratch_ptr", 0)]
        (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") ∧
      (∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = post.globals.lookup k) := by
  dsimp only
  obtain ⟨hG, hA⟩ := hAR
  obtain ⟨hp, fp, sp, hhp, hhp_eq, hfp, hfp_eq, hsp, hsp_eq⟩ :=
    Wave8Contracts.M26.arenaOK_globals s hA
  have hbody : sourceFnBody Guest.Software.guestFn_lst_new =
      .decCall (ofString "l") .one (ofString "alloc") [.const 24]
        (.decCall (ofString "p") .one (ofString "alloc")
          [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")]]
          (.seq (.store (.op .add [.var .local (ofString "l"), .const 0]) (.var .local (ofString "p")))
            (.seq (.store (.op .add [.var .local (ofString "l"), .const 8]) (.const 0))
              (.seq (.store (.op .add [.var .local (ofString "l"), .const 16]) (.var .local (ofString "cap")))
                (.return (.var .local (ofString "l"))))))) := rfl
  have hrun : Wave8Contracts.M26.Ret s (sourceFnBody Guest.Software.guestFn_lst_new)
      (fun rv post =>
        rv = .val (.word hp) ∧
        ∃ q1 q2 : BitVec 64,
          q1.toNat = hp.toNat + 24 ∧
          q2.toNat = q1.toNat + eszw.toNat * capw.toNat ∧
          q2.toNat ≤ heapLimit ∧
          q2.toNat % 8 = 0 ∧
          post.globals = (s.globals.update (ofString "heap_ptr", .val (.word q1))).update
            (ofString "heap_ptr", .val (.word q2)) ∧
          post.memory = Wave8Contracts.M26.updW
            (Wave8Contracts.M26.updW (Wave8Contracts.M26.updW s.memory (hp + 0) q1) (hp + 8) 0)
            (hp + 16) capw ∧
          post.code = s.code ∧ post.memaddrs = s.memaddrs ∧
          post.shMemaddrs = s.shMemaddrs ∧ post.baseAddr = s.baseAddr ∧ post.be = s.be) := by
    rw [hbody]
    apply Wave8Contracts.M26.Ret.of_NS
    refine Wave8Contracts.M26.Ret.ns_alloc hG.code 24 rfl hp hhp ?_
    intro hcmp1_1 hcmp2_1
    set q1 : BitVec 64 := (hp + (24 + 7)) &&& ((0 : BitVec 64) - 8)
    set L1 := s.locals.update (ofString "l", .val (.word hp))
    set G1 := s.globals.update (ofString "heap_ptr", .val (.word q1))
    have hmul_ev : Wave8Contracts.M26.ev (Wave8Contracts.M26.NS s L1 G1 s.memory (s.clock - 1))
        (.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")]) =
        some (.val (.word (eszw * capw))) := by
      simp [Wave8Contracts.M26.ev, evalHOLExact, evalListHOLExact, L1,
        HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "l" ≠ ofString "esz" by decide,
        show ofString "l" ≠ ofString "cap" by decide,
        hesz, hcap, valueIsWord, valueWord, panOpHOL]
    have hq1_g : G1.lookup (ofString "heap_ptr") = some (.val (.word q1)) := by
      simp [G1, HolFiniteMapExact.lookup_update, FUPDATE]
    refine Wave8Contracts.M26.Ret.ns_alloc hG.code (eszw * capw) hmul_ev q1 hq1_g ?_
    intro hcmp1_2 hcmp2_2
    set q2 : BitVec 64 := (q1 + (eszw * capw + 7)) &&& ((0 : BitVec 64) - 8)
    set L2 := L1.update (ofString "p", .val (.word q1))
    set G2 := G1.update (ofString "heap_ptr", .val (.word q2))
    have hev_l0 : Wave8Contracts.M26.ev (Wave8Contracts.M26.NS s L2 G2 s.memory (s.clock - 1 - 1))
        (.op .add [.var .local (ofString "l"), .const 0]) = some (.val (.word (hp + 0))) := by
      simp [Wave8Contracts.M26.ev, evalHOLExact, evalListHOLExact, L2, L1,
        HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "p" ≠ ofString "l" by decide, valueIsWord, valueWord, wordOpHOL, wordOp]
    have hev_p : Wave8Contracts.M26.ev (Wave8Contracts.M26.NS s L2 G2 s.memory (s.clock - 1 - 1))
        (.var .local (ofString "p")) = some (.val (.word q1)) := by
      simp [Wave8Contracts.M26.ev, evalHOLExact, L2, HolFiniteMapExact.lookup_update, FUPDATE]
    refine Wave8Contracts.M26.Ret.ns_storeW (hp + 0) q1 hev_l0 hev_p ?_
    intro _
    set M1 := Wave8Contracts.M26.updW s.memory (hp + 0) q1
    have hev_l8 : Wave8Contracts.M26.ev (Wave8Contracts.M26.NS s L2 G2 M1 (s.clock - 1 - 1))
        (.op .add [.var .local (ofString "l"), .const 8]) = some (.val (.word (hp + 8))) := by
      simp [Wave8Contracts.M26.ev, evalHOLExact, evalListHOLExact, L2, L1,
        HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "p" ≠ ofString "l" by decide, valueIsWord, valueWord, wordOpHOL, wordOp]
    refine Wave8Contracts.M26.Ret.ns_storeW (hp + 8) 0 hev_l8 rfl ?_
    intro _
    set M2 := Wave8Contracts.M26.updW M1 (hp + 8) 0
    have hev_l16 : Wave8Contracts.M26.ev (Wave8Contracts.M26.NS s L2 G2 M2 (s.clock - 1 - 1))
        (.op .add [.var .local (ofString "l"), .const 16]) = some (.val (.word (hp + 16))) := by
      simp [Wave8Contracts.M26.ev, evalHOLExact, evalListHOLExact, L2, L1,
        HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "p" ≠ ofString "l" by decide, valueIsWord, valueWord, wordOpHOL, wordOp]
    have hev_cap : Wave8Contracts.M26.ev (Wave8Contracts.M26.NS s L2 G2 M2 (s.clock - 1 - 1))
        (.var .local (ofString "cap")) = some (.val (.word capw)) := by
      simp [Wave8Contracts.M26.ev, evalHOLExact, L2, L1, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "p" ≠ ofString "cap" by decide,
        show ofString "l" ≠ ofString "cap" by decide, hcap]
    refine Wave8Contracts.M26.Ret.ns_storeW (hp + 16) capw hev_l16 hev_cap ?_
    intro _
    set M3 := Wave8Contracts.M26.updW M2 (hp + 16) capw
    refine Wave8Contracts.M26.Ret.ns_ret ?_
    intro val hval
    have hval_eq : val = .val (.word hp) := by
      simp [Wave8Contracts.M26.ev, evalHOLExact, L2, L1, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "p" ≠ ofString "l" by decide] at hval
      exact hval.symm
    subst hval_eq
    dsimp only
    have hhp_hi : hp.toNat ≤ heapLimit := by rw [hhp_eq]; exact hA.2.1
    have hhp_al : hp.toNat % 8 = 0 := by rw [hhp_eq]; exact hA.2.2.2.2.2.1
    obtain ⟨hq1_eq, hq1_hi, hq1_al, _⟩ := Wave8Contracts.M26.alloc_arith hp 24 hhp_hi hhp_al hcmp1_1 hcmp2_1
    change q1.toNat = _ at hq1_eq
    change q1.toNat ≤ heapLimit at hq1_hi
    change q1.toNat % 8 = 0 at hq1_al
    have h24 : ((24 : BitVec 64).toNat + 7) / 8 * 8 = 24 := by decide
    rw [h24] at hq1_eq
    obtain ⟨hq2_eq, hq2_hi, hq2_al, _⟩ :=
      Wave8Contracts.M26.alloc_arith q1 (eszw * capw) hq1_hi hq1_al hcmp1_2 hcmp2_2
    change q2.toNat = _ at hq2_eq
    change q2.toNat ≤ heapLimit at hq2_hi
    change q2.toNat % 8 = 0 at hq2_al
    have hmul_toNat : (eszw * capw).toNat = eszw.toNat * capw.toNat := by
      rw [BitVec.toNat_mul, Nat.mod_eq_of_lt hmul_lt]
    have hmul_div : (eszw.toNat * capw.toNat + 7) / 8 * 8 = eszw.toNat * capw.toNat := by omega
    rw [hmul_toNat, hmul_div] at hq2_eq
    exact ⟨rfl, q1, q2, hq1_eq, hq2_eq, hq2_hi, hq2_al, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨rfl, q1, q2, hq1_eq, hq2_eq, hq2_hi, hq2_al, hg_post, hm_post,
    hc_post, hma_post, hsh_post, hba_post, hbe_post⟩ := hrun v hret
  set post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_lst_new)).2
  have hhp_al : hp.toNat % 8 = 0 := by rw [hhp_eq]; exact hA.2.2.2.2.2.1
  have hq1_al : q1.toNat % 8 = 0 := by rw [hq1_eq]; omega
  have hsb_le : sourceBase ≤ hp.toNat := by rw [hhp_eq]; exact hA.1
  have hsb_pos : 0 < sourceBase := by rw [M13.sourceBase_val]; decide
  have hhp_nz : hp.toNat ≠ 0 := by omega
  have hlim_le_he : heapLimit ≤ heapEnd := by decide
  have hhe_lt : heapEnd < 2 ^ 64 := by decide
  have hpost_hp : globN post "heap_ptr" = q2.toNat := by
    unfold globN; rw [hg_post]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hgl : ∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = post.globals.lookup k := by
    intro k hk
    rw [hg_post]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, hk, Ne.symm hk]
  have hpost_sp : globN post "scratch_ptr" = globN s "scratch_ptr" :=
    globN_eq_of_lookup (hgl (ofString "scratch_ptr") (by decide))
  have hpost_fmp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" :=
    globN_eq_of_lookup (hgl (ofString "frame_mem_ptr") (by decide))
  have hG_post : GuestInv post := ⟨hc_post ▸ hG.code, hma_post ▸ hG.memaddrs, hsh_post ▸ hG.shMemaddrs, hba_post ▸ hG.baseAddr⟩
  have hA_post : ArenaOK post := by
    unfold ArenaOK
    rw [hpost_hp, hpost_fmp, hpost_sp]
    refine ⟨by omega, hq2_hi, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1, hq2_al, hA.2.2.2.2.2.2.1,
      hA.2.2.2.2.2.2.2.1, ?_⟩
    intro g hg
    by_cases hgh : ofString g = ofString "heap_ptr"
    · exact ⟨q2, by unfold GlobalWord; rw [hgh, hg_post]; simp [HolFiniteMapExact.lookup_update, FUPDATE]⟩
    · obtain ⟨wg, hwg⟩ := hA.2.2.2.2.2.2.2.2 g hg
      exact ⟨wg, by unfold GlobalWord at hwg ⊢; rw [← hgl (ofString g) hgh]; exact hwg⟩
  have hp0_eq : hp + 0 = BitVec.ofNat 64 hp.toNat := by simp [BitVec.ofNat_toNat]
  have hp8_eq : hp + 8 = BitVec.ofNat 64 (hp.toNat + 8) := (Wave8Contracts.M26.ofNat_add_toNat_eq hp 8).symm
  have hp16_eq : hp + 16 = BitVec.ofNat 64 (hp.toNat + 16) := (Wave8Contracts.M26.ofNat_add_toNat_eq hp 16).symm
  have hp0_ne_8 : hp + 0 ≠ hp + 8 := by
    intro h; have h1 := congrArg BitVec.toNat h; simp [BitVec.toNat_add] at h1; omega
  have hp0_ne_16 : hp + 0 ≠ hp + 16 := by
    intro h; have h1 := congrArg BitVec.toNat h; simp [BitVec.toNat_add] at h1; omega
  have hp8_ne_16 : hp + 8 ≠ hp + 16 := by
    intro h; have h1 := congrArg BitVec.toNat h; simp [BitVec.toNat_add] at h1; omega
  have hmem0 : memW post hp.toNat = hp.toNat + 24 := by
    unfold memW; rw [hm_post, ← hp0_eq]
    simp [Wave8Contracts.M26.updW, hp0_ne_16, hp0_ne_8, hq1_eq]
  have hmem8 : memW post (hp.toNat + 8) = 0 := by
    unfold memW; rw [hm_post, ← hp8_eq]
    simp [Wave8Contracts.M26.updW, hp8_ne_16]
  have hmem16 : memW post (hp.toNat + 16) = capw.toNat := by
    unfold memW; rw [hm_post, ← hp16_eq]
    simp [Wave8Contracts.M26.updW]
  have hlst_ok : LstOK post hp.toNat := ⟨by rw [hmem16]; exact hcap_pos, by rw [hmem8, hmem16]; omega⟩
  have hmul_pos : 0 < eszw.toNat * capw.toNat := Nat.mul_pos (by omega) (by omega)
  have hlst_objs : lstObjects post hp.toNat eszw.toNat =
      [(hp.toNat, 24), (hp.toNat + 24, eszw.toNat * capw.toNat)] := by
    unfold lstObjects
    rw [if_neg hhp_nz, hmem0, hmem16, if_neg (by omega)]
  have hdisj : Disj (hp.toNat, 24) (hp.toNat + 24, eszw.toNat * capw.toNat) :=
    Or.inr (Or.inr (Or.inl le_rfl))
  have hobjs_props : ∀ i ∈ lstObjects post hp.toNat eszw.toNat,
      Allocated post i ∧ WordsOK post i ∧ Inside i (globN s "heap_ptr") (globN post "heap_ptr") := by
    rw [hlst_objs]
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · refine ⟨Or.inl ⟨hsb_le, by rw [hpost_hp]; omega⟩, ?_, ?_⟩
      · exact Wave8Contracts.M26.wordsOK_of_guestInv post hG_post hp.toNat 24 hhp_al (by decide) hsb_le (by omega)
      · rw [← hhp_eq, hpost_hp]; exact ⟨le_rfl, by omega⟩
    · refine ⟨Or.inl ⟨by omega, by rw [hpost_hp]; omega⟩, ?_, ?_⟩
      · have hdiv_eq : (eszw.toNat * capw.toNat + 7) / 8 * 8 = eszw.toNat * capw.toNat := by omega
        have hw := Wave8Contracts.M26.wordsOK_of_guestInv post hG_post (hp.toNat + 24)
          ((eszw.toNat * capw.toNat + 7) / 8 * 8) (by omega) (by omega) (by omega) (by omega)
        rw [hdiv_eq] at hw; exact hw
      · rw [← hhp_eq, hpost_hp]; exact ⟨by omega, by omega⟩
  have hfr : FrameOutside s post [(globN s "scratch_ptr", 0)]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
    intro a _ hnhf
    rw [hm_post]
    have ha_ne0 : a ≠ hp + 0 := by
      intro h; subst h; apply hnhf
      rw [hp0_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), ← hhp_eq, hpost_hp]
      exact ⟨by dsimp; omega, by dsimp; omega⟩
    have ha_ne8 : a ≠ hp + 8 := by
      intro h; subst h; apply hnhf
      rw [hp8_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), ← hhp_eq, hpost_hp]
      exact ⟨by dsimp; omega, by dsimp; omega⟩
    have ha_ne16 : a ≠ hp + 16 := by
      intro h; subst h; apply hnhf
      rw [hp16_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), ← hhp_eq, hpost_hp]
      exact ⟨by dsimp; omega, by dsimp; omega⟩
    simp only [Wave8Contracts.M26.updW, ha_ne16, ha_ne8, ha_ne0, ↓reduceIte]
  exact ⟨hp, rfl, hhp_eq, hhp_al, hhp_nz, hmem0, hmem8, hmem16,
    by rw [hpost_hp, hq2_eq, hq1_eq],
    by rw [← hhp_eq, hpost_hp]; omega,
    ⟨hG_post, hA_post⟩, hbe_post, hpost_sp, hpost_fmp, hlst_ok, hlst_objs, hdisj,
    hobjs_props, hfr, hgl⟩

theorem decCall_lst_new_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (x : MlS) (eszw capw : BitVec 64) (cont : ProgHOL 64)
    (hAR : ArenaReady s)
    (hesz_pos : 1 ≤ eszw.toNat)
    (hmul_lt : eszw.toNat * capw.toNat < 2 ^ 64)
    (hmul_al : (eszw.toNat * capw.toNat) % 8 = 0)
    (hcap_pos : 1 ≤ capw.toNat)
    (hnt : (evaluateHOLFiniteState s
      (.decCall x .one (ofString "lst_new") [.const eszw, .const capw] cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall x .one (ofString "lst_new") [.const eszw, .const capw] cont)).1) :
    ∃ (lw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      lw.toNat = globN s "heap_ptr" ∧
      lw.toNat % 8 = 0 ∧
      lw.toNat ≠ 0 ∧
      memW mid lw.toNat = lw.toNat + 24 ∧
      memW mid (lw.toNat + 8) = 0 ∧
      memW mid (lw.toNat + 16) = capw.toNat ∧
      globN mid "heap_ptr" = lw.toNat + 24 + eszw.toNat * capw.toNat ∧
      globN s "heap_ptr" < globN mid "heap_ptr" ∧
      ArenaReady mid ∧
      mid.be = s.be ∧
      globN mid "scratch_ptr" = globN s "scratch_ptr" ∧
      globN mid "frame_mem_ptr" = globN s "frame_mem_ptr" ∧
      LstOK mid lw.toNat ∧
      lstObjects mid lw.toNat eszw.toNat =
        [(lw.toNat, 24), (lw.toNat + 24, eszw.toNat * capw.toNat)] ∧
      Disj (lw.toNat, 24) (lw.toNat + 24, eszw.toNat * capw.toNat) ∧
      (∀ i ∈ lstObjects mid lw.toNat eszw.toNat,
        Allocated mid i ∧ WordsOK mid i ∧ Inside i (globN s "heap_ptr") (globN mid "heap_ptr")) ∧
      FrameOutside s mid [(globN s "scratch_ptr", 0)]
        (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") ∧
      mid.locals.lookup x = some (.val (.word lw)) ∧
      (∀ y, y ≠ x → mid.locals.lookup y = s.locals.lookup y) ∧
      (∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = mid.globals.lookup k) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall x .one (ofString "lst_new") [.const eszw, .const capw] cont)).1 =
        (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall x .one (ofString "lst_new") [.const eszw, .const capw] cont)).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) } := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const eszw, .const capw] = some [.val (.word eszw), .val (.word capw)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have hlk := pan_two_word_lookup s.code.lookup (ofString "lst_new")
    (ofString "esz") (ofString "cap") (sourceFnBody Guest.Software.guestFn_lst_new) eszw capw
    (by decide) (by rw [hAR.1.code]; exact lookup_lst_new_wk)
  rw [hargs] at hnt hres; dsimp only at hnt hres
  rw [hlk] at hnt hres; dsimp only at hnt hres
  by_cases hcz : s.clock = 0
  · rw [if_pos hcz] at hnt; exact absurd rfl hnt
  · rw [if_neg hcz] at hnt hres
    let cmap := (HolFiniteMapExact.empty.update (ofString "esz", ValueHOL.val (.word eszw))).update
      (ofString "cap", ValueHOL.val (.word capw))
    let ent := callEntryStateHOLFinite s cmap
    have hent_AR : ArenaReady ent := (arenaReady_with_locals s cmap (s.clock - 1)).2 hAR
    have hent_e : ent.locals.lookup (ofString "esz") = some (.val (.word eszw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "cap" ≠ ofString "esz" by decide]
    have hent_c : ent.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_lst_new) with ⟨rb, sb⟩
    have hrun' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_lst_new) = (rb, sb) := hrun
    rw [hrun'] at hnt hres
    cases rb with
    | none => exact absurd hres not_resumes_error
    | some rb' =>
      cases rb' with
      | timeOut => exact absurd rfl hnt
      | «break» | «continue» | error => exact absurd hres not_resumes_error
      | finalFfi _ =>
        exfalso; rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      | exception e ev =>
        exfalso
        rcases hres with ⟨_, h⟩ | ⟨e', ev', h, hne⟩
        · simp at h
        · dsimp only at h; injection h with h'; injection h' with he1 he2; subst he1 he2
          exact lst_new_no_catchable_exn ent hAR.1.code e ev hne (congrArg Prod.fst hrun)
      | returned vb =>
        have hprops := lst_new_heap_props ent eszw capw hent_AR hesz_pos hmul_lt hmul_al hcap_pos
          hent_e hent_c vb (congrArg Prod.fst hrun)
        have hrun_snd : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_lst_new)).2 = sb :=
          congrArg Prod.snd hrun
        dsimp only at hprops
        rw [hrun_snd] at hprops
        obtain ⟨lw, rfl, hlw_eq, hlw_al, hlw_nz, hm0, hm8, hm16, hhp_sb, hhp_lt,
          hAsb, hbe_sb, hsp_sb, hfmp_sb, hlst_sb, hobjs_sb, hdisj_sb, hobjs_props, hfr_sb, hgl_sb⟩ := hprops
        dsimp only at hnt hres
        have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word lw) : ValueHOL 64)) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word lw) : ValueHOL 64)) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        rw [if_pos hsh] at hnt hres
        let mid := setVarHOLFinite x (.val (.word lw)) { sb with locals := s.locals }
        have hmid_AR : ArenaReady mid := (arenaReady_with_locals sb _ sb.clock).2 hAsb
        have heval_eq : evaluateHOLFiniteState s
            (.decCall x .one (ofString "lst_new") [.const eszw, .const capw] cont) =
            ((evaluateHOLFiniteState mid cont).1,
              { (evaluateHOLFiniteState mid cont).2 with
                locals := HolFiniteMapExact.resVarEq
                  (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) }) := by
          rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hargs]
          dsimp only; rw [hlk]; dsimp only
          rw [if_neg hcz, hrun']; dsimp only
          rw [if_pos hsh]
        refine ⟨lw, mid, hlw_eq, hlw_al, hlw_nz, hm0, hm8, hm16, hhp_sb, hhp_lt,
          hmid_AR, hbe_sb, hsp_sb, hfmp_sb, hlst_sb, hobjs_sb, hdisj_sb, hobjs_props, hfr_sb,
          by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
          fun y hy => by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hy, Ne.symm hy],
          fun k hk1 => hgl_sb k hk1,
          by intro hto; rw [hto] at hnt; exact hnt rfl,
          hres, by rw [heval_eq], by rw [heval_eq]⟩

theorem seq_call_lst_new_local_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (vname : MlS) (eszw capw : BitVec 64) (cont : ProgHOL 64)
    (hAR : ArenaReady s)
    (hesz_pos : 1 ≤ eszw.toNat)
    (hmul_lt : eszw.toNat * capw.toNat < 2 ^ 64)
    (hmul_al : (eszw.toNat * capw.toNat) % 8 = 0)
    (hcap_pos : 1 ≤ capw.toNat)
    (hnt : (evaluateHOLFiniteState s
      (.seq (.call (some (some (.local, vname), none)) (ofString "lst_new") [.const eszw, .const capw])
        cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq (.call (some (some (.local, vname), none)) (ofString "lst_new") [.const eszw, .const capw])
        cont)).1) :
    ∃ (lw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      lw.toNat = globN s "heap_ptr" ∧
      lw.toNat % 8 = 0 ∧
      lw.toNat ≠ 0 ∧
      memW mid lw.toNat = lw.toNat + 24 ∧
      memW mid (lw.toNat + 8) = 0 ∧
      memW mid (lw.toNat + 16) = capw.toNat ∧
      globN mid "heap_ptr" = lw.toNat + 24 + eszw.toNat * capw.toNat ∧
      globN s "heap_ptr" < globN mid "heap_ptr" ∧
      ArenaReady mid ∧
      mid.be = s.be ∧
      globN mid "scratch_ptr" = globN s "scratch_ptr" ∧
      globN mid "frame_mem_ptr" = globN s "frame_mem_ptr" ∧
      LstOK mid lw.toNat ∧
      lstObjects mid lw.toNat eszw.toNat =
        [(lw.toNat, 24), (lw.toNat + 24, eszw.toNat * capw.toNat)] ∧
      Disj (lw.toNat, 24) (lw.toNat + 24, eszw.toNat * capw.toNat) ∧
      (∀ i ∈ lstObjects mid lw.toNat eszw.toNat,
        Allocated mid i ∧ WordsOK mid i ∧ Inside i (globN s "heap_ptr") (globN mid "heap_ptr")) ∧
      FrameOutside s mid [(globN s "scratch_ptr", 0)]
        (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") ∧
      mid.locals.lookup vname = some (.val (.word lw)) ∧
      (∀ x, x ≠ vname → mid.locals.lookup x = s.locals.lookup x) ∧
      (∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = mid.globals.lookup k) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      evaluateHOLFiniteState s
        (.seq (.call (some (some (.local, vname), none)) (ofString "lst_new") [.const eszw, .const capw])
          cont) = evaluateHOLFiniteState mid cont := by
  rw [evaluateHOLFiniteState_seq_line780] at hnt hres
  set cprog := ProgHOL.call (some (some (.local, vname), none)) (ofString "lst_new") [.const eszw, .const capw]
  rcases hc_eval : evaluateHOLFiniteState s cprog with ⟨rc, mid⟩
  have hc_eval_orig := hc_eval
  rw [hc_eval] at hnt hres
  dsimp only [cprog] at hc_eval
  rw [evaluateHOLFiniteState_call] at hc_eval
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const eszw, .const capw] = some [.val (.word eszw), .val (.word capw)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have hlk := pan_two_word_lookup s.code.lookup (ofString "lst_new")
    (ofString "esz") (ofString "cap") (sourceFnBody Guest.Software.guestFn_lst_new) eszw capw
    (by decide) (by rw [hAR.1.code]; exact lookup_lst_new_wk)
  rw [hargs] at hc_eval; dsimp only at hc_eval; rw [hlk] at hc_eval; dsimp only at hc_eval
  by_cases hcz : s.clock = 0
  · rw [if_pos hcz] at hc_eval; injection hc_eval with hr _; subst hr; simp at hnt
  · rw [if_neg hcz] at hc_eval
    let cmap := (HolFiniteMapExact.empty.update (ofString "esz", ValueHOL.val (.word eszw))).update
      (ofString "cap", ValueHOL.val (.word capw))
    let ent := callEntryStateHOLFinite s cmap
    have hent_AR : ArenaReady ent := (arenaReady_with_locals s cmap (s.clock - 1)).2 hAR
    have hent_e : ent.locals.lookup (ofString "esz") = some (.val (.word eszw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "cap" ≠ ofString "esz" by decide]
    have hent_c : ent.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_lst_new) with ⟨rb, sb⟩
    have hrun' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_lst_new) = (rb, sb) := hrun
    rw [hrun'] at hc_eval
    cases rb with
    | none =>
      injection hc_eval with hr _; subst hr; exact absurd hres not_resumes_error
    | some rb' =>
      cases rb' with
      | timeOut =>
        injection hc_eval with hr _; subst hr; simp at hnt
      | «break» | «continue» | error =>
        injection hc_eval with hr _; subst hr; exact absurd hres not_resumes_error
      | finalFfi _ =>
        injection hc_eval with hr _; subst hr
        exfalso; rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      | exception e ev =>
        injection hc_eval with hr _; subst hr
        exfalso
        rcases hres with ⟨_, h⟩ | ⟨e', ev', h, hne⟩
        · simp at h
        · dsimp only at h; injection h with h'; injection h' with he1 he2; subst he1 he2
          exact lst_new_no_catchable_exn ent hAR.1.code e ev hne (congrArg Prod.fst hrun)
      | returned vb =>
        have hprops := lst_new_heap_props ent eszw capw hent_AR hesz_pos hmul_lt hmul_al hcap_pos
          hent_e hent_c vb (congrArg Prod.fst hrun)
        have hrun_snd : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_lst_new)).2 = sb :=
          congrArg Prod.snd hrun
        dsimp only at hprops
        rw [hrun_snd] at hprops
        obtain ⟨lw, rfl, hlw_eq, hlw_al, hlw_nz, hm0, hm8, hm16, hhp_sb, hhp_lt,
          hAsb, hbe_sb, hsp_sb, hfmp_sb, hlst_sb, hobjs_sb, hdisj_sb, hobjs_props, hfr_sb, hgl_sb⟩ := hprops
        dsimp only at hc_eval
        have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word lw) : ValueHOL 64)) .one = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        rw [if_pos hsh] at hc_eval
        by_cases hval : isValidValueHOLExact s.toExact .local vname (.val (.word lw)) = true
        · rw [if_pos hval] at hc_eval
          injection hc_eval with hr hmid
          subst hr
          have hmid_AR : ArenaReady mid := by
            rw [← hmid]; exact (arenaReady_with_locals sb _ sb.clock).2 hAsb
          have hseq_eq : evaluateHOLFiniteState s (.seq cprog cont) = evaluateHOLFiniteState mid cont := by
            rw [evaluateHOLFiniteState_seq_line780, hc_eval_orig]
          have hmid_mem : mid = { sb with locals := mid.locals, globals := sb.globals, clock := sb.clock } := by
            rw [← hmid]; rfl
          refine ⟨lw, mid, hlw_eq, hlw_al, hlw_nz,
            by rw [← hmid]; exact hm0,
            by rw [← hmid]; exact hm8,
            by rw [← hmid]; exact hm16,
            by rw [← hmid]; exact hhp_sb,
            by rw [← hmid]; exact hhp_lt,
            hmid_AR,
            by rw [← hmid]; exact hbe_sb,
            by rw [← hmid]; exact hsp_sb,
            by rw [← hmid]; exact hfmp_sb,
            by rw [← hmid]; exact hlst_sb,
            by rw [← hmid]; exact hobjs_sb,
            hdisj_sb,
            by rw [← hmid]; exact hobjs_props,
            by rw [← hmid]; exact hfr_sb,
            by rw [← hmid]; simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
            fun x hx => by
              rw [← hmid]
              simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hx, Ne.symm hx],
            fun k hk1 => by rw [← hmid]; exact hgl_sb k hk1,
            hnt, hres, hseq_eq⟩
        · rw [if_neg hval] at hc_eval
          injection hc_eval with hr _; subst hr
          exact absurd hres not_resumes_error

/-! ## 3. Exact `append ∨ set` `htabValues` postcondition and call stepper for `htab_set` -/

def htabSetCallees (f : MlS) : Bool :=
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

theorem htabSetCallees_noCatchableRaise :
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

theorem htab_set_no_catchable_exn {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (e : MlS) (v : ValueHOL 64)
    (hne : e ≠ ofString "TrapErr") :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_set)).1 ≠
      some (.exception e v) :=
  evaluate_noCatchableRaise htabSetCallees htabSetCallees_noCatchableRaise
    (sourceFnBody Guest.Software.guestFn_htab_set) rfl s hcode e v hne

section HtabSetExactValues

open InitECandidate.Solver.Wave8GuestInv.SoloHtabSet

def HtabSetValuesPost {F : Type} (s0 post : PanSemStateFiniteExact 64 F) (t val : Nat) : Prop :=
  htabValues post t = htabValues s0 t ++ [val] ∨
  ∃ i0 < (htabValues s0 t).length, htabValues post t = (htabValues s0 t).set i0 val

theorem locFree_valuesExact {F : Type} (s0 : PanSemStateFiniteExact 64 F) (t val : Nat) :
    LocFreePost (fun (rv : ValueHOL 64) (post : PanSemStateFiniteExact 64 F) =>
      rv = .val (.word 0#64) ∧ HtabSetValuesPost s0 post t val) := by
  intro _ _ _ h
  exact h

theorem set_branch_empty_values_exact {F : Type}
    (s0 s : PanSemStateFiniteExact 64 F)
    (tw keyw valw : BitVec 64)
    (hs_fr : LocFrame s0 s)
    (hA0 : ArenaReady s0)
    (hW0 : HtabWF s0 tw.toNat)
    (hal0 : ∀ i ∈ htabFootprint s0 tw.toNat, Allocated s0 i)
    (hcnt0 : hdr s0 tw.toNat 3 = 0)
    (ht_s : s.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hkey_s : s.locals.lookup (ofString "key") = some (.val (.word keyw)))
    (hval_s : s.locals.lookup (ofString "value") = some (.val (.word valw))) :
    Ret s
      (.decCall (ofString "nl") .one (ofString "htab_new_leaf")
        [.var .local (ofString "t"), .var .local (ofString "key"), .var .local (ofString "value")]
        (.seq
          (.store (.op .add [.var .local (ofString "t"), .const 56#64]) (.var .local (ofString "nl")))
          (.return (.const 0#64))))
      (fun rv post => rv = .val (.word 0#64) ∧ HtabSetValuesPost s0 post tw.toNat valw.toNat) := by
  set t := tw.toNat
  have hLF := locFree_valuesExact s0 t valw.toNat
  have hmem_s : s.memory = s0.memory := hs_fr.memory
  obtain ⟨hB0, L0, I0, Fr0, hT0⟩ := (htabWF_iff s0 t).mp hW0
  have hL0_nil : L0 = [] := List.eq_nil_of_length_eq_zero (hT0.1.trans hcnt0)
  have hI0_nil : I0 = [] := by
    rcases hT0.2.2.2.1 with ⟨_, hI⟩ | hlen
    · exact hI
    · omega
  subst hL0_nil hI0_nil
  have hNS_s : NodeState s t [] Fr0 := by
    have hNS0 : NodeState s0 t [] Fr0 :=
      ⟨hB0, by simpa using hT0.2.1, by simpa using hT0.2.2.1, hT0.2.2.2.2.2.2.2.2.2.2.2⟩
    unfold LocFrame at hs_fr; rw [hs_fr]; exact hNS0
  have hA_s : ArenaReady s := by unfold LocFrame at hs_fr; rw [hs_fr]; exact (arenaReady_locals s0 _ _).mpr hA0
  have hal_s : ∀ i ∈ htabFootprint s t, Allocated s i := by
    unfold LocFrame at hs_fr; rw [hs_fr]; exact hal0
  have hh3_s : hdr s t 3 = 0 := by unfold hdr memW; rw [hmem_s]; exact hcnt0
  have hcnt_s : hdr s t 3 ≤ ([] : List Nat).length := by omega
  have hvals0_nil : htabValues s0 t = [] := by
    unfold htabValues
    change List.map _ (List.range (hdr s0 t 3)) = []
    rw [hcnt0]; rfl
  refine Ret.decCall_new_leaf_lf hLF tw keyw valw [] Fr0
    (by simp [evalAt, evalHOLExact, ht_s])
    (by simp [evalAt, evalHOLExact, hkey_s])
    (by simp [evalAt, evalHOLExact, hval_s])
    hA_s hNS_s hcnt_s hal_s ?_
  intro nlw Fr1 s1 _ hNS1 _ _ hh3_1 _ _ n8_1 _ _ ordc_1 _ _ _ _ _ _ hloc_1
  obtain ⟨hB1, _, hmem1, _⟩ := hNS1
  obtain ⟨hnc1_lt, _, _, _, ht_lo, ht_hi, _⟩ := htabBlocks_bounds hB1
  have hhe : heapEnd = 33806089704 := rfl
  let L_nl := s.locals.update (ofString "nl", .val (.word nlw))
  have ht_nl : L_nl.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [L_nl, HolFiniteMapExact.lookup_update, FUPDATE, ht_s, show ofString "nl" ≠ ofString "t" by decide]
  have hnl_lk : L_nl.lookup (ofString "nl") = some (.val (.word nlw)) := by
    simp [L_nl, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_nl_eq : setVarHOLFinite (ofString "nl") (.val (.word nlw)) s1 = NS s1 L_nl s1.globals s1.memory s1.clock := by
    simp [setVarHOLFinite, NS, hloc_1, L_nl]
  rw [hs1_nl_eq]
  refine Ret.ns_storeW (tw + 56#64) nlw
    (by
      have h560 : 56#64 + (0 : BitVec 64) = 56#64 := rfl
      simp only [NS_locals, evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
        ht_nl, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
        valueIsWord, valueWord, wordOpHOL, wordOp, h560])
    (by simp [evalAt, evalHOLExact, hnl_lk]) ?_
  intro _
  apply Ret.ns_ret; intro rv hrv
  simp only [evalAt, evalHOLExact, Option.some.injEq] at hrv
  refine ⟨hrv.symm, ?_⟩
  let s_end := NS s1 HolFiniteMapExact.empty s1.globals (updW s1.memory (tw + 56#64) nlw) s1.clock
  have htw56_eq : BitVec.ofNat 64 (t + 8 * 7) = tw + 56#64 := ofNat_add_toNat tw 56
  have hne_hdr : ∀ k < 11, k ≠ 7 → BitVec.ofNat 64 (t + 8 * k) ≠ tw + 56#64 := by
    intro k hk hne; rw [← htw56_eq]; exact ofNat64_ne_of_ne_of_lt (by omega) (by omega) (by omega)
  have hsep1 := htabBlocks_cell_sep hB1
  have hh3_end : hdr s_end t 3 = 1 := by
    have h1 : hdr s_end t 3 = hdr s1 t 3 := memW_updW_other s1 _ _ _ (hne_hdr 3 (by omega) (by omega))
    have h2 : hdr s1 t 3 = hdr s t 3 + 1 := hh3_1
    omega
  have hh5_end : hdr s_end t 5 = hdr s1 t 5 := memW_updW_other s1 _ _ _ (hne_hdr 5 (by omega) (by omega))
  have hh6_end : hdr s_end t 6 = hdr s1 t 6 := memW_updW_other s1 _ _ _ (hne_hdr 6 (by omega) (by omega))
  have hnl_rng : 1 ≤ nlw.toNat ∧ nlw.toNat < hdr s1 t 8 :=
    (hmem1 nlw.toNat).mp (List.mem_append_left _ (by simp))
  have hnl_lt_nc1 : nlw.toNat < hdr s1 t 10 + 1 := by
    have : hdr s1 t 8 ≤ hdr s1 t 10 + 1 := hB1.2.2.2.2.2.2.2
    omega
  have h0_lt_nc1 : 0 < hdr s1 t 10 + 1 := by omega
  have hord0_end : memW s_end (hdr s_end t 6 + 8 * 0) = nlw.toNat := by
    rw [hh6_end]
    have h1 : memW s_end (hdr s1 t 6 + 8 * 0) = memW s1 (hdr s1 t 6 + 8 * 0) := by
      apply memW_updW_other s1; rw [← htw56_eq]; exact (hsep1.2.1 7 (by omega) 0 h0_lt_nc1).symm
    have h2 : memW s1 (hdr s1 t 6 + 8 * 0) = nlw.toNat := by
      have hc0 : hdr s tw.toNat 3 = 0 := hh3_s
      rw [hc0] at ordc_1; exact ordc_1
    exact h1.trans h2
  have hn8_end : nodeF s_end (hdr s_end t 5) nlw.toNat 8 = valw.toNat := by
    rw [hh5_end]
    have h1 : nodeF s_end (hdr s1 t 5) nlw.toNat 8 = nodeF s1 (hdr s1 t 5) nlw.toNat 8 := by
      unfold nodeF; apply memW_updW_other s1; rw [← htw56_eq]
      exact (hsep1.1 7 (by omega) nlw.toNat hnl_lt_nc1 8 (Or.inr (Or.inl rfl))).symm
    exact h1.trans n8_1
  left
  rw [hvals0_nil, List.nil_append]
  unfold htabValues
  change List.map (fun i => nodeF s_end (hdr s_end t 5) (memW s_end (hdr s_end t 6 + 8 * i)) 8)
    (List.range (hdr s_end t 3)) = [valw.toNat]
  rw [hh3_end]
  simp only [List.range_one, List.map_cons, List.map_nil, hord0_end, hn8_end]

theorem set_branch_overwrite_values_exact {F : Type}
    (s0 s : PanSemStateFiniteExact 64 F)
    (tw leafw valw : BitVec 64)
    (hs_fr : LocFrame s0 s)
    (hA0 : ArenaReady s0)
    (hW0 : HtabWF s0 tw.toNat)
    (hleaf_mem : ∀ L I Fr, TreeWF L I Fr (hdr s0 tw.toNat 8) (hdr s0 tw.toNat 0) (hdr s0 tw.toNat 3)
      (hdr s0 tw.toNat 7) (hdr s0 tw.toNat 9) (nodeF s0 (hdr s0 tw.toNat 5))
      (fun i => memW s0 (hdr s0 tw.toNat 6 + 8 * i)) → leafw.toNat ∈ L)
    (ht_s : s.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hleaf_s : s.locals.lookup (ofString "leaf") = some (.val (.word leafw)))
    (hval_s : s.locals.lookup (ofString "value") = some (.val (.word valw))) :
    Ret s
      (.seq
        (.store (.op .add [
            .load .one (.op .add [.var .local (ofString "t"), .const 40#64]),
            .panop .mul [.var .local (ofString "leaf"), .const 32#64],
            .const 8#64])
          (.var .local (ofString "value")))
        (.return (.const 0#64)))
      (fun rv post => rv = .val (.word 0#64) ∧ HtabSetValuesPost s0 post tw.toNat valw.toNat) := by
  set t := tw.toNat
  have hmem_s : s.memory = s0.memory := hs_fr.memory
  have hma_s : s.memaddrs = s0.memaddrs := by unfold LocFrame at hs_fr; rw [hs_fr]
  obtain ⟨hB0, L0, I0, Fr0, hT0⟩ := (htabWF_iff s0 t).mp hW0
  have hleaf_L0 : leafw.toNat ∈ L0 := hleaf_mem L0 I0 Fr0 hT0
  obtain ⟨i0, hi0_L0, hi0_eq⟩ := List.mem_iff_getElem.mp hleaf_L0
  have hi0_cnt : i0 < hdr s0 t 3 := by rw [← hT0.1]; exact hi0_L0
  have hleaf_rng := (hT0.2.2.1 leafw.toNat).mp (List.mem_append_left _ (List.mem_append_left _ hleaf_L0))
  have hleaf_lt_nc0 : leafw.toNat < hdr s0 t 10 + 1 := by have := hB0.2.2.2.2.2.2.2; omega
  obtain ⟨hnc0_lt, _, _, _, ht_lo, ht_hi, _⟩ := htabBlocks_bounds hB0
  have hhe : heapEnd = 33806089704 := rfl
  obtain ⟨hdom0_t5, hm0_t5⟩ := word_of_hdr s0 tw 5 (by omega) hB0
  set ndw := BitVec.ofNat 64 (hdr s0 t 5)
  have hndw_nat : ndw.toNat = hdr s0 t 5 := by
    have hnd0_in := (hB0.1 (hdr s0 t 5, (hdr s0 t 10 + 1) * 32) (by simp [htabFootprint])).1
    unfold Inside at hnd0_in; rw [BitVec.toNat_ofNat]; omega
  have hed : evalAt s (.op .add [
      .load .one (.op .add [.var .local (ofString "t"), .const 40#64]),
      .panop .mul [.var .local (ofString "leaf"), .const 32#64],
      .const 8#64]) =
      some (.val (.word (ndw + leafw * 32#64 + 8#64))) := by
    have hdom40 : s.memaddrs (tw + 40#64) := by rw [hma_s]; exact hdom0_t5
    have hm40 : s.memory (tw + 40#64) = .word ndw := by rw [hmem_s]; exact hm0_t5
    simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
      ht_s, hleaf_s, isWfShapeExactHOL, memLoadHOLExact,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL]
    have h400 : 40#64 + (0 : BitVec 64) = 40#64 := rfl
    rw [h400]
    simp only [hdom40, hm40, ↓reduceIte, List.all, List.map, Bool.and_self, List.foldr,
      valueIsWord, valueWord, wordOpHOL, wordOp, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
    have hz : (8#64 : BitVec 64) + 0 = 8#64 := BitVec.add_zero _
    rw [hz, BitVec.add_assoc]
  have hs_ns : s = NS s0 s.locals s0.globals s0.memory s.clock := hs_fr
  rw [hs_ns]
  refine Ret.ns_storeW (ndw + leafw * 32#64 + 8#64) valw
    (by rw [← hs_ns]; exact hed)
    (by simp [evalAt, evalHOLExact, hval_s]) ?_
  intro _
  apply Ret.ns_ret; intro rv hrv
  simp only [evalAt, evalHOLExact, Option.some.injEq] at hrv
  refine ⟨hrv.symm, ?_⟩
  set addr := ndw + leafw * 32#64 + 8#64
  have haddr_eq : addr = BitVec.ofNat 64 (hdr s0 t 5 + 32 * leafw.toNat + 8) := by
    rw [← hndw_nat]; exact (ofNat_node_addr ndw leafw 8).symm
  set s_end := NS s0 HolFiniteMapExact.empty s0.globals (updW s0.memory addr valw) s.clock
  have hsep0 := htabBlocks_cell_sep hB0
  have hne_hdr : ∀ k < 11, BitVec.ofNat 64 (t + 8 * k) ≠ addr := by
    intro k hk; rw [haddr_eq]; exact hsep0.1 k hk leafw.toNat hleaf_lt_nc0 8 (Or.inr (Or.inl rfl))
  have hh3_end : hdr s_end t 3 = hdr s0 t 3 := memW_updW_other s0 _ _ _ (hne_hdr 3 (by omega))
  have hh5_end : hdr s_end t 5 = hdr s0 t 5 := memW_updW_other s0 _ _ _ (hne_hdr 5 (by omega))
  have hh6_end : hdr s_end t 6 = hdr s0 t 6 := memW_updW_other s0 _ _ _ (hne_hdr 6 (by omega))
  have hnd_L0_I0 : (L0 ++ I0).Nodup := (List.nodup_append.mp hT0.2.1).1
  have hnd_L0 : L0.Nodup := (List.nodup_append.mp hnd_L0_I0).1
  have hLlen : L0.length ≤ hdr s0 t 10 := by
    have hle := nodup_len_le_range hnd_L0
      (fun x hx => (hT0.2.2.1 x).mp (List.mem_append_left _ (List.mem_append_left _ hx)))
    have := hB0.2.2.2.2.2.2.2; omega
  have hv0_len : (htabValues s0 t).length = hdr s0 t 3 := by
    simp [htabValues]
  right
  refine ⟨i0, by rw [hv0_len]; exact hi0_cnt, ?_⟩
  apply List.ext_getElem
  · simp [htabValues, hh3_end]
  · intro i hi1 hi2
    have hi_cnt : i < hdr s0 t 3 := by simpa [htabValues, hh3_end] using hi1
    have hi_L0 : i < L0.length := by rw [hT0.1]; exact hi_cnt
    have hord_i : memW s_end (hdr s0 t 6 + 8 * i) = memW s0 (hdr s0 t 6 + 8 * i) := by
      apply memW_updW_other s0; rw [haddr_eq]
      exact hsep0.2.2.1 leafw.toNat hleaf_lt_nc0 8 (Or.inr (Or.inl rfl)) i (by omega)
    set z := memW s0 (hdr s0 t 6 + 8 * i)
    have hz_eq : z = L0[i] := (hT0.2.2.2.2.1 i hi_L0).1
    have hz_L0 : z ∈ L0 := by rw [hz_eq]; exact List.getElem_mem hi_L0
    have hz_rng := (hT0.2.2.1 z).mp (List.mem_append_left _ (List.mem_append_left _ hz_L0))
    have hz_lt_nc0 : z < hdr s0 t 10 + 1 := by have := hB0.2.2.2.2.2.2.2; omega
    have hget_end : (htabValues s_end t)[i] = nodeF s_end (hdr s0 t 5) z 8 := by
      simp only [htabValues, List.getElem_map, List.getElem_range]
      change nodeF s_end (hdr s_end t 5) (memW s_end (hdr s_end t 6 + 8 * i)) 8 = _
      rw [hh5_end, hh6_end, hord_i]
    rw [hget_end]
    by_cases h_idx : i = i0
    · subst h_idx
      rw [List.getElem_set_self]
      have hzl : z = leafw.toNat := hz_eq.trans hi0_eq
      rw [hzl]
      change memW s_end (hdr s0 t 5 + 32 * leafw.toNat + 8) = valw.toNat
      unfold memW
      rw [← haddr_eq]
      simp [s_end, NS_memory, updW]
    · rw [List.getElem_set_ne (Ne.symm h_idx)]
      have hzl : z ≠ leafw.toNat := by
        intro heq
        have hget_eq : L0[i] = L0[i0] := hz_eq.symm.trans (heq.trans hi0_eq.symm)
        exact h_idx ((List.Nodup.getElem_inj_iff hnd_L0).mp hget_eq)
      have hnd_z : nodeF s_end (hdr s0 t 5) z 8 = nodeF s0 (hdr s0 t 5) z 8 := by
        unfold nodeF; apply memW_updW_other s0; rw [haddr_eq]
        exact hsep0.2.2.2.1 z hz_lt_nc0 8 (Or.inr (Or.inl rfl)) leafw.toNat hleaf_lt_nc0 8 (Or.inr (Or.inl rfl)) (Or.inl hzl)
      rw [hnd_z]
      simp only [htabValues, List.getElem_map, List.getElem_range]
      rfl

theorem set_splice_values_exact {F : Type}
    (s0 s2 : PanSemStateFiniteExact 64 F)
    (tw dw pw nw nlw niw valw : BitVec 64)
    (L0 I0 Fr0 Fr2 : List Nat)
    (L_cur : HolFiniteMapExact MlS (ValueHOL 64))
    (ht_cur : L_cur.lookup (ofString "t") = some (.val (.word tw)))
    (hp_cur : L_cur.lookup (ofString "p") = some (.val (.word pw)))
    (hn_cur : L_cur.lookup (ofString "n") = some (.val (.word nw)))
    (hnl_cur : L_cur.lookup (ofString "nl") = some (.val (.word nlw)))
    (hni_cur : L_cur.lookup (ofString "ni") = some (.val (.word niw)))
    (hA2 : ArenaReady s2)
    (hNS2 : NodeState s2 tw.toNat (((L0 ++ I0) ++ [nlw.toNat]) ++ [niw.toNat]) Fr2)
    (hT0 : TreeWF L0 I0 Fr0
      (hdr s0 tw.toNat 8) (hdr s0 tw.toNat 0) (hdr s0 tw.toNat 3) (hdr s0 tw.toNat 7) (hdr s0 tw.toNat 9)
      (nodeF s0 (hdr s0 tw.toNat 5)) (fun i => memW s0 (hdr s0 tw.toNat 6 + 8 * i)))
    (hnw_LI : nw.toNat ∈ L0 ++ I0)
    (hpw_spec : (pw.toNat = 0 ∧ nw.toNat = hdr s0 tw.toNat 7) ∨
      (pw.toNat ∈ I0 ∧ nw.toNat ≠ hdr s0 tw.toNat 7 ∧ pw.toNat = nodeF s0 (hdr s0 tw.toNat 5) nw.toNat 0))
    (hh3_2 : hdr s2 tw.toNat 3 = hdr s0 tw.toNat 3 + 1)
    (hnl_8_2 : nodeF s2 (hdr s2 tw.toNat 5) nlw.toNat 8 = valw.toNat)
    (hord_cnt_2 : memW s2 (hdr s2 tw.toNat 6 + 8 * hdr s0 tw.toNat 3) = nlw.toNat)
    (hord_old_2 : ∀ i, i < hdr s0 tw.toNat 3 →
      memW s2 (hdr s2 tw.toNat 6 + 8 * i) = memW s0 (hdr s0 tw.toNat 6 + 8 * i))
    (hnd_old_2 : ∀ z ∈ L0 ++ I0, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      nodeF s2 (hdr s2 tw.toNat 5) z off = nodeF s0 (hdr s0 tw.toNat 5) z off) :
    Ret (NS s2 L_cur s2.globals s2.memory s2.clock)
      (.seq
        (.assign .local (ofString "nodes") (.load .one (.op .add [.var .local (ofString "t"), .const 40#64])))
        (.seq
          (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "ni"), .const 32#64], .const 0#64]) (.var .local (ofString "p")))
          (.seq
            (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "nl"), .const 32#64], .const 0#64]) (.var .local (ofString "ni")))
            (.seq
              (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "n"), .const 32#64], .const 0#64]) (.var .local (ofString "ni")))
              (.seq
                (.ite (.cmp .equal (.op .and [.shift .lsr (.loadByte (.op .add [.var .local (ofString "key"), .shift .lsr (.var .local (ofString "d")) (.const 3#64)])) (.op .sub [.const 7#64, .op .and [.var .local (ofString "d"), .const 7#64]]), .const 1#64]) (.const 0#64))
                  (.seq
                    (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "ni"), .const 32#64], .const 8#64]) (.var .local (ofString "nl")))
                    (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "ni"), .const 32#64], .const 16#64]) (.var .local (ofString "n"))))
                  (.seq
                    (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "ni"), .const 32#64], .const 8#64]) (.var .local (ofString "n")))
                    (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "ni"), .const 32#64], .const 16#64]) (.var .local (ofString "nl")))))
                (.seq
                  (.ite (.cmp .equal (.var .local (ofString "p")) (.const 0#64))
                    (.store (.op .add [.var .local (ofString "t"), .const 56#64]) (.var .local (ofString "ni")))
                    (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "p"), .const 32#64], .const 8#64])) (.var .local (ofString "n")))
                      (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "p"), .const 32#64], .const 8#64]) (.var .local (ofString "ni")))
                      (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "p"), .const 32#64], .const 16#64]) (.var .local (ofString "ni")))))
                  (.return (.const 0#64))))))))
      (fun rv post => rv = .val (.word 0#64) ∧ HtabSetValuesPost s0 post tw.toNat valw.toNat) := by
  set t := tw.toNat
  have hB2 := hNS2.1
  have hnodup2 := hNS2.2.1
  have hmem2 := hNS2.2.2.1
  obtain ⟨hnc2_lt, _, _, _, ht_lo, ht_hi, _⟩ := htabBlocks_bounds hB2
  have hhe : heapEnd = 33806089704 := rfl
  obtain ⟨hdom2_t5, hm2_t5⟩ := word_of_hdr s2 tw 5 (by omega) hB2
  set ndw := BitVec.ofNat 64 (hdr s2 t 5)
  have hndw_nat : ndw.toNat = hdr s2 t 5 := by
    have hnd2_in := (hB2.1 (hdr s2 t 5, (hdr s2 t 10 + 1) * 32) (by simp [htabFootprint])).1
    unfold Inside at hnd2_in; rw [BitVec.toNat_ofNat]; omega
  have hsep2 := htabBlocks_cell_sep hB2
  have haddr_nd : ∀ (xw : BitVec 64) (off : Nat),
      ndw + xw * 32#64 + BitVec.ofNat 64 off = BitVec.ofNat 64 (hdr s2 t 5 + 32 * xw.toNat + off) := by
    intro xw off; rw [← hndw_nat]; exact (ofNat_node_addr ndw xw off).symm
  have hnd_all := (List.nodup_append.mp hnodup2).1
  have hnd_A1 := (List.nodup_append.mp hnd_all).1
  have hnx2_le : hdr s2 t 8 ≤ hdr s2 t 10 + 1 := hB2.2.2.2.2.2.2.2
  have hLI_lt_nc2 : ∀ z ∈ L0 ++ I0, z < hdr s2 t 10 + 1 := by
    intro z hz
    have hzr : 1 ≤ z ∧ z < hdr s2 t 8 :=
      (hmem2 z).mp (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hz)))
    omega
  have hni_lt_nc2 : niw.toNat < hdr s2 t 10 + 1 := by
    have hnir : 1 ≤ niw.toNat ∧ niw.toNat < hdr s2 t 8 :=
      (hmem2 niw.toNat).mp (List.mem_append_left _ (List.mem_append_right _ (by simp)))
    omega
  have hnl_lt_nc2 : nlw.toNat < hdr s2 t 10 + 1 := by
    have hnlr : 1 ≤ nlw.toNat ∧ nlw.toNat < hdr s2 t 8 :=
      (hmem2 nlw.toNat).mp (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp))))
    omega
  have hnw_lt_nc2 : nw.toNat < hdr s2 t 10 + 1 := hLI_lt_nc2 nw.toNat hnw_LI
  have hnl_ne_ni : nlw.toNat ≠ niw.toNat := fun h =>
    (List.nodup_append.mp hnd_all).2.2 niw.toNat (List.mem_append_right _ (by simp [h])) niw.toNat (by simp) rfl
  have hLI_ne_ni : ∀ z ∈ L0 ++ I0, z ≠ niw.toNat := fun z hz h =>
    (List.nodup_append.mp hnd_all).2.2 niw.toNat (List.mem_append_left _ (h ▸ hz)) niw.toNat (by simp) rfl
  have hLI_ne_nl : ∀ z ∈ L0 ++ I0, z ≠ nlw.toNat := fun z hz h =>
    (List.nodup_append.mp hnd_A1).2.2 nlw.toNat (h ▸ hz) nlw.toNat (by simp) rfl
  have hnd_L0_I0 := (List.nodup_append.mp hT0.2.1).1
  have hL0_not_I0 : ∀ z ∈ L0, z ∉ I0 := fun z hz hI =>
    (List.nodup_append.mp hnd_L0_I0).2.2 z hz z hI rfl
  have splice_mem_values : ∀ (ch_left : Bool) (m_final : BitVec 64 → HolWordLab 64),
      let m3 := updW (updW (updW s2.memory (ndw + niw * 32#64 + 0#64) pw)
                  (ndw + nlw * 32#64 + 0#64) niw) (ndw + nw * 32#64 + 0#64) niw
      let m5 := if ch_left then
                  updW (updW m3 (ndw + niw * 32#64 + 8#64) nlw) (ndw + niw * 32#64 + 16#64) nw
                else
                  updW (updW m3 (ndw + niw * 32#64 + 8#64) nw) (ndw + niw * 32#64 + 16#64) nlw
      m_final = (if pw.toNat = 0 then
                  updW m5 (tw + 56#64) niw
                else if nodeF s0 (hdr s0 t 5) pw.toNat 8 = nw.toNat then
                  updW m5 (ndw + pw * 32#64 + 8#64) niw
                else
                  updW m5 (ndw + pw * 32#64 + 16#64) niw) →
      let s_end := NS s2 HolFiniteMapExact.empty s2.globals m_final s2.clock
      HtabSetValuesPost s0 s_end t valw.toNat := by
    intro ch_left m_final m3 m5 hm_eq s_end
    have htw56_eq : tw + 56#64 = BitVec.ofNat 64 (t + 8 * 7) := (ofNat_add_toNat tw 56).symm
    have hm5_hdr : ∀ k < 11, m5 (BitVec.ofNat 64 (t + 8 * k)) = s2.memory (BitVec.ofNat 64 (t + 8 * k)) := by
      intro k hk
      have h1 := hsep2.1 k hk niw.toNat hni_lt_nc2 16 (Or.inr (Or.inr (Or.inl rfl)))
      have h2 := hsep2.1 k hk niw.toNat hni_lt_nc2 8 (Or.inr (Or.inl rfl))
      have h3 := hsep2.1 k hk nw.toNat hnw_lt_nc2 0 (Or.inl rfl)
      have h4 := hsep2.1 k hk nlw.toNat hnl_lt_nc2 0 (Or.inl rfl)
      have h5 := hsep2.1 k hk niw.toNat hni_lt_nc2 0 (Or.inl rfl)
      rw [← haddr_nd] at h1 h2 h3 h4 h5
      cases ch_left <;> simp only [m5, m3, updW, Bool.false_eq_true, ↓reduceIte, h1, h2, h3, h4, h5]
    have hm5_ord : ∀ i < hdr s2 t 10 + 1, m5 (BitVec.ofNat 64 (hdr s2 t 6 + 8 * i)) = s2.memory (BitVec.ofNat 64 (hdr s2 t 6 + 8 * i)) := by
      intro i hi
      have h1 := hsep2.2.2.1 niw.toNat hni_lt_nc2 16 (Or.inr (Or.inr (Or.inl rfl))) i hi
      have h2 := hsep2.2.2.1 niw.toNat hni_lt_nc2 8 (Or.inr (Or.inl rfl)) i hi
      have h3 := hsep2.2.2.1 nw.toNat hnw_lt_nc2 0 (Or.inl rfl) i hi
      have h4 := hsep2.2.2.1 nlw.toNat hnl_lt_nc2 0 (Or.inl rfl) i hi
      have h5 := hsep2.2.2.1 niw.toNat hni_lt_nc2 0 (Or.inl rfl) i hi
      rw [← haddr_nd] at h1 h2 h3 h4 h5
      cases ch_left <;> simp only [m5, m3, updW, Bool.false_eq_true, ↓reduceIte, h1, h2, h3, h4, h5]
    have hp_lt_nc2 : pw.toNat ≠ 0 → pw.toNat < hdr s2 t 10 + 1 := by
      intro hpz
      rcases hpw_spec with ⟨h0, _⟩ | ⟨hpI, _, _⟩
      · exact absurd h0 hpz
      · exact hLI_lt_nc2 pw.toNat (List.mem_append_right _ hpI)
    have hdr_end_other : ∀ k < 11, k ≠ 7 → hdr s_end t k = hdr s2 t k := by
      intro k hk hk7
      unfold hdr memW
      simp only [s_end, NS_memory, hm_eq]
      by_cases hpz : pw.toNat = 0
      · have hne7 : BitVec.ofNat 64 (t + 8 * k) ≠ tw + 56#64 := by
          rw [htw56_eq]; exact ofNat64_ne_of_ne_of_lt (by omega) (by omega) (by omega)
        simp only [hpz, ↓reduceIte, updW, hne7, hm5_hdr k hk]
      · simp only [hpz, ↓reduceIte]
        have hp_lt := hp_lt_nc2 hpz
        have hne8 : BitVec.ofNat 64 (t + 8 * k) ≠ ndw + pw * 32#64 + 8#64 := by
          rw [haddr_nd]; exact hsep2.1 k hk pw.toNat hp_lt 8 (Or.inr (Or.inl rfl))
        have hne16 : BitVec.ofNat 64 (t + 8 * k) ≠ ndw + pw * 32#64 + 16#64 := by
          rw [haddr_nd]; exact hsep2.1 k hk pw.toNat hp_lt 16 (Or.inr (Or.inr (Or.inl rfl)))
        split <;> simp only [updW, hne8, hne16, ↓reduceIte, hm5_hdr k hk]
    have hh3_end : hdr s_end t 3 = hdr s0 t 3 + 1 := (hdr_end_other 3 (by omega) (by omega)).trans hh3_2
    have hh5_end : hdr s_end t 5 = hdr s2 t 5 := hdr_end_other 5 (by omega) (by omega)
    have hh6_end : hdr s_end t 6 = hdr s2 t 6 := hdr_end_other 6 (by omega) (by omega)
    have hord_end : ∀ i < hdr s2 t 10 + 1, memW s_end (hdr s2 t 6 + 8 * i) = memW s2 (hdr s2 t 6 + 8 * i) := by
      intro i hi
      unfold memW
      simp only [s_end, NS_memory, hm_eq]
      by_cases hpz : pw.toNat = 0
      · have hne7 : BitVec.ofNat 64 (hdr s2 t 6 + 8 * i) ≠ tw + 56#64 := by
          rw [htw56_eq]; exact (hsep2.2.1 7 (by omega) i hi).symm
        simp only [hpz, ↓reduceIte, updW, hne7, hm5_ord i hi]
      · simp only [hpz, ↓reduceIte]
        have hp_lt := hp_lt_nc2 hpz
        have hne8 : BitVec.ofNat 64 (hdr s2 t 6 + 8 * i) ≠ ndw + pw * 32#64 + 8#64 := by
          rw [haddr_nd]; exact hsep2.2.2.1 pw.toNat hp_lt 8 (Or.inr (Or.inl rfl)) i hi
        have hne16 : BitVec.ofNat 64 (hdr s2 t 6 + 8 * i) ≠ ndw + pw * 32#64 + 16#64 := by
          rw [haddr_nd]; exact hsep2.2.2.1 pw.toNat hp_lt 16 (Or.inr (Or.inr (Or.inl rfl))) i hi
        split <;> simp only [updW, hne8, hne16, ↓reduceIte, hm5_ord i hi]
    have hnd8_end_keep : ∀ z < hdr s2 t 10 + 1, z ≠ niw.toNat → (pw.toNat ≠ 0 → z ≠ pw.toNat) →
        nodeF s_end (hdr s2 t 5) z 8 = nodeF s2 (hdr s2 t 5) z 8 := by
      intro z hz hzni hzp
      unfold nodeF memW
      simp only [s_end, NS_memory, hm_eq]
      have hm5_z8 : m5 (BitVec.ofNat 64 (hdr s2 t 5 + 32 * z + 8)) = s2.memory (BitVec.ofNat 64 (hdr s2 t 5 + 32 * z + 8)) := by
        have h1 := hsep2.2.2.2.1 z hz 8 (Or.inr (Or.inl rfl)) niw.toNat hni_lt_nc2 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inl hzni)
        have h2 := hsep2.2.2.2.1 z hz 8 (Or.inr (Or.inl rfl)) niw.toNat hni_lt_nc2 8 (Or.inr (Or.inl rfl)) (Or.inl hzni)
        have h3 := hsep2.2.2.2.1 z hz 8 (Or.inr (Or.inl rfl)) nw.toNat hnw_lt_nc2 0 (Or.inl rfl) (Or.inr (by omega))
        have h4 := hsep2.2.2.2.1 z hz 8 (Or.inr (Or.inl rfl)) nlw.toNat hnl_lt_nc2 0 (Or.inl rfl) (Or.inr (by omega))
        have h5 := hsep2.2.2.2.1 z hz 8 (Or.inr (Or.inl rfl)) niw.toNat hni_lt_nc2 0 (Or.inl rfl) (Or.inl hzni)
        rw [← haddr_nd] at h1 h2 h3 h4 h5
        cases ch_left <;> simp only [m5, m3, updW, Bool.false_eq_true, ↓reduceIte, h1, h2, h3, h4, h5]
      by_cases hpz : pw.toNat = 0
      · have hne7 : BitVec.ofNat 64 (hdr s2 t 5 + 32 * z + 8) ≠ tw + 56#64 := by
          rw [htw56_eq]; exact (hsep2.1 7 (by omega) z hz 8 (Or.inr (Or.inl rfl))).symm
        simp only [hpz, ↓reduceIte, updW, hne7, hm5_z8]
      · simp only [hpz, ↓reduceIte]
        have hp_lt := hp_lt_nc2 hpz
        have hne8 : BitVec.ofNat 64 (hdr s2 t 5 + 32 * z + 8) ≠ ndw + pw * 32#64 + 8#64 := by
          rw [haddr_nd]; exact hsep2.2.2.2.1 z hz 8 (Or.inr (Or.inl rfl)) pw.toNat hp_lt 8 (Or.inr (Or.inl rfl)) (Or.inl (hzp hpz))
        have hne16 : BitVec.ofNat 64 (hdr s2 t 5 + 32 * z + 8) ≠ ndw + pw * 32#64 + 16#64 := by
          rw [haddr_nd]; exact hsep2.2.2.2.1 z hz 8 (Or.inr (Or.inl rfl)) pw.toNat hp_lt 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inl (hzp hpz))
        split <;> simp only [updW, hne8, hne16, ↓reduceIte, hm5_z8]
    have hcnt_lt_nc2 : hdr s0 t 3 < hdr s2 t 10 + 1 := by
      have hnx2_le : hdr s2 t 8 ≤ hdr s2 t 10 + 1 := hB2.2.2.2.2.2.2.2
      have hr2 : ∀ y ∈ ((L0 ++ I0) ++ [nlw.toNat]) ++ [niw.toNat], 1 ≤ y ∧ y < hdr s2 t 8 := fun y hy =>
        (hmem2 y).mp (List.mem_append_left _ hy)
      have hlen_le := nodup_len_le_range hnd_all hr2
      have hL0_len : L0.length = hdr s0 t 3 := hT0.1
      have hni_rng := hr2 niw.toNat (List.mem_append_right _ (by simp))
      simp only [List.length_append, List.length_singleton] at hlen_le
      omega
    left
    unfold htabValues
    change List.map (fun i => nodeF s_end (hdr s_end t 5) (memW s_end (hdr s_end t 6 + 8 * i)) 8)
      (List.range (hdr s_end t 3)) =
      List.map (fun i => nodeF s0 (hdr s0 t 5) (memW s0 (hdr s0 t 6 + 8 * i)) 8)
      (List.range (hdr s0 t 3)) ++ [valw.toNat]
    rw [hh3_end, hh5_end, hh6_end, List.range_succ, List.map_append, List.map_singleton]
    congr 1
    · apply List.map_congr_left
      intro i hi_mem
      have hi_old : i < hdr s0 t 3 := List.mem_range.mp hi_mem
      have hi_L0 : i < L0.length := by rw [hT0.1]; exact hi_old
      rw [hord_end i (lt_trans hi_old hcnt_lt_nc2), hord_old_2 i hi_old]
      set z := memW s0 (hdr s0 t 6 + 8 * i)
      have hz_eq : z = L0[i] := (hT0.2.2.2.2.1 i hi_L0).1
      have hz_L0 : z ∈ L0 := by rw [hz_eq]; exact List.getElem_mem hi_L0
      have hz_LI : z ∈ L0 ++ I0 := List.mem_append_left _ hz_L0
      have hz_ne_p : pw.toNat ≠ 0 → z ≠ pw.toNat := by
        intro hpz
        rcases hpw_spec with ⟨h0, _⟩ | ⟨hpI, _, _⟩
        · exact absurd h0 hpz
        · exact fun h => hL0_not_I0 z hz_L0 (h ▸ hpI)
      rw [hnd8_end_keep z (hLI_lt_nc2 z hz_LI) (hLI_ne_ni z hz_LI) hz_ne_p,
          hnd_old_2 z hz_LI 8 (Or.inr (Or.inl rfl))]
    · congr 1
      rw [hord_end (hdr s0 t 3) hcnt_lt_nc2, hord_cnt_2]
      have hnl_ne_p : pw.toNat ≠ 0 → nlw.toNat ≠ pw.toNat := by
        intro hpz
        rcases hpw_spec with ⟨h0, _⟩ | ⟨hpI, _, _⟩
        · exact absurd h0 hpz
        · exact fun h => hLI_ne_nl pw.toNat (List.mem_append_right _ hpI) h.symm
      rw [hnd8_end_keep nlw.toNat hnl_lt_nc2 hnl_ne_ni hnl_ne_p, hnl_8_2]
  have hev_nd : evalAt (NS s2 L_cur s2.globals s2.memory s2.clock)
      (.load .one (.op .add [.var .local (ofString "t"), .const 40#64])) =
      some (.val (.word ndw)) :=
    eval_field_load_word _ tw 40#64 ndw ht_cur hdom2_t5 hm2_t5
  refine Ret.ns_assign ndw hev_nd ?_
  let L_nd := L_cur.update (ofString "nodes", .val (.word ndw))
  have hl_nd : L_nd.lookup (ofString "nodes") = some (.val (.word ndw)) := by
    simp [L_nd, HolFiniteMapExact.lookup_update, FUPDATE]
  have hl_t : L_nd.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [L_nd, HolFiniteMapExact.lookup_update, FUPDATE, ht_cur, show ofString "nodes" ≠ ofString "t" by decide]
  have hl_p : L_nd.lookup (ofString "p") = some (.val (.word pw)) := by
    simp [L_nd, HolFiniteMapExact.lookup_update, FUPDATE, hp_cur, show ofString "nodes" ≠ ofString "p" by decide]
  have hl_n : L_nd.lookup (ofString "n") = some (.val (.word nw)) := by
    simp [L_nd, HolFiniteMapExact.lookup_update, FUPDATE, hn_cur, show ofString "nodes" ≠ ofString "n" by decide]
  have hl_nl : L_nd.lookup (ofString "nl") = some (.val (.word nlw)) := by
    simp [L_nd, HolFiniteMapExact.lookup_update, FUPDATE, hnl_cur, show ofString "nodes" ≠ ofString "nl" by decide]
  have hl_ni : L_nd.lookup (ofString "ni") = some (.val (.word niw)) := by
    simp [L_nd, HolFiniteMapExact.lookup_update, FUPDATE, hni_cur, show ofString "nodes" ≠ ofString "ni" by decide]
  refine Ret.ns_storeW (ndw + niw * 32#64 + 0#64) pw
    (eval_node_field_expr _ (ofString "ni") ndw niw 0 hl_nd hl_ni)
    (by simp [evalAt, evalHOLExact]; exact hl_p) ?_
  intro _
  refine Ret.ns_storeW (ndw + nlw * 32#64 + 0#64) niw
    (eval_node_field_expr _ (ofString "nl") ndw nlw 0 hl_nd hl_nl)
    (by simp [evalAt, evalHOLExact]; exact hl_ni) ?_
  intro _
  refine Ret.ns_storeW (ndw + nw * 32#64 + 0#64) niw
    (eval_node_field_expr _ (ofString "n") ndw nw 0 hl_nd hl_n)
    (by simp [evalAt, evalHOLExact]; exact hl_ni) ?_
  intro _
  set m3 := updW (updW (updW s2.memory
              (ndw + niw * 32#64 + 0#64) pw)
              (ndw + nlw * 32#64 + 0#64) niw)
              (ndw + nw * 32#64 + 0#64) niw
  have exec_parent_link : ∀ (ch_left : Bool) (m5_val : BitVec 64 → HolWordLab 64),
      m5_val = (if ch_left then
                  updW (updW m3 (ndw + niw * 32#64 + 8#64) nlw) (ndw + niw * 32#64 + 16#64) nw
                else
                  updW (updW m3 (ndw + niw * 32#64 + 8#64) nw) (ndw + niw * 32#64 + 16#64) nlw) →
      Ret (NS s2 L_nd s2.globals m5_val s2.clock)
        (.seq
          (.ite (.cmp .equal (.var .local (ofString "p")) (.const 0#64))
            (.store (.op .add [.var .local (ofString "t"), .const 56#64]) (.var .local (ofString "ni")))
            (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "p"), .const 32#64], .const 8#64])) (.var .local (ofString "n")))
              (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "p"), .const 32#64], .const 8#64]) (.var .local (ofString "ni")))
              (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "p"), .const 32#64], .const 16#64]) (.var .local (ofString "ni")))))
          (.return (.const 0#64)))
        (fun rv post => rv = .val (.word 0#64) ∧ HtabSetValuesPost s0 post t valw.toNat) := by
    intro ch_left m5_val hm5_eq
    apply Ret.seq_ite
    intro cwp hcwp
    have hcwp_spec : (cwp ≠ 0 → pw.toNat = 0) ∧ (cwp = 0 → pw.toNat ≠ 0) := by
      obtain ⟨va, vb, hva, hvb, hcw_eq⟩ := evalAt_cmp _ .equal _ _ cwp hcwp
      simp only [NS_locals, evalAt, evalHOLExact, hl_p, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hva hvb
      subst hva hvb
      have hz0 : (0#64 : BitVec 64).toNat = 0 := rfl
      constructor
      · intro hnz; by_contra hne
        have hp_ne : pw ≠ 0#64 := fun h => hne (by rw [h]; exact hz0)
        simp [Compiler.Encoders.Asm.wordCmpHOL, hp_ne] at hcw_eq
        exact hnz hcw_eq
      · intro hz hp0
        have hp_eq : pw = 0#64 := BitVec.eq_of_toNat_eq (by rw [hp0, hz0])
        simp [Compiler.Encoders.Asm.wordCmpHOL, hp_eq] at hcw_eq
        rw [hz] at hcw_eq; exact absurd hcw_eq (by decide)
    refine ⟨fun hcwp_nz => ?_, fun hcwp_z => ?_⟩
    · have hpz := hcwp_spec.1 hcwp_nz
      refine Ret.ns_storeW (tw + 56#64) niw
        (by
          have h560 : 56#64 + (0 : BitVec 64) = 56#64 := rfl
          simp only [NS_locals, evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
            hl_t, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
            valueIsWord, valueWord, wordOpHOL, wordOp, h560])
        (by simp [evalAt, evalHOLExact]; exact hl_ni) ?_
      intro _
      apply Ret.ns_ret; intro rv hrv
      simp only [evalAt, evalHOLExact, Option.some.injEq] at hrv
      refine ⟨hrv.symm, ?_⟩
      exact splice_mem_values ch_left (updW m5_val (tw + 56#64) niw)
        (by rw [if_pos hpz, hm5_eq])
    · have hpnz := hcwp_spec.2 hcwp_z
      have hpI : pw.toNat ∈ I0 := by
        rcases hpw_spec with ⟨h0, _⟩ | ⟨hI, _, _⟩
        · exact absurd h0 hpnz
        · exact hI
      have hpLI : pw.toNat ∈ L0 ++ I0 := List.mem_append_right _ hpI
      have hp_lt_nc2 := hLI_lt_nc2 pw.toNat hpLI
      have hp_ne_ni := hLI_ne_ni pw.toNat hpLI
      obtain ⟨_, hm2_p8⟩ := word_of_node s2 tw ndw pw 8 hndw_nat.symm hp_lt_nc2 (Or.inr (Or.inl rfl)) hB2
      have hm5_p8 : m5_val (ndw + pw * 32#64 + 8#64) = .word (BitVec.ofNat 64 (nodeF s0 (hdr s0 t 5) pw.toNat 8)) := by
        have h1 := hsep2.2.2.2.1 pw.toNat hp_lt_nc2 8 (Or.inr (Or.inl rfl)) niw.toNat hni_lt_nc2 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inl hp_ne_ni)
        have h2 := hsep2.2.2.2.1 pw.toNat hp_lt_nc2 8 (Or.inr (Or.inl rfl)) niw.toNat hni_lt_nc2 8 (Or.inr (Or.inl rfl)) (Or.inl hp_ne_ni)
        have h3 := hsep2.2.2.2.1 pw.toNat hp_lt_nc2 8 (Or.inr (Or.inl rfl)) nw.toNat hnw_lt_nc2 0 (Or.inl rfl) (Or.inr (by omega))
        have h4 := hsep2.2.2.2.1 pw.toNat hp_lt_nc2 8 (Or.inr (Or.inl rfl)) nlw.toNat hnl_lt_nc2 0 (Or.inl rfl) (Or.inr (by omega))
        have h5 := hsep2.2.2.2.1 pw.toNat hp_lt_nc2 8 (Or.inr (Or.inl rfl)) niw.toNat hni_lt_nc2 0 (Or.inl rfl) (Or.inl hp_ne_ni)
        rw [hm5_eq]
        have hm5_s2 : (if ch_left = true then updW (updW m3 (ndw + niw * 32#64 + 8#64) nlw) (ndw + niw * 32#64 + 16#64) nw
            else updW (updW m3 (ndw + niw * 32#64 + 8#64) nw) (ndw + niw * 32#64 + 16#64) nlw) (ndw + pw * 32#64 + 8#64) =
            s2.memory (ndw + pw * 32#64 + 8#64) := by
          cases ch_left <;> simp only [m3, updW, Bool.false_eq_true, ↓reduceIte,
            haddr_nd pw 8, haddr_nd niw 16, haddr_nd niw 8, haddr_nd nw 0, haddr_nd nlw 0, haddr_nd niw 0,
            h1, h2, h3, h4, h5]
        rw [hm5_s2]
        have hm2_p8' : s2.memory (ndw + pw * 32#64 + 8#64) = .word (BitVec.ofNat 64 (nodeF s2 (hdr s2 t 5) pw.toNat 8)) := by
          rw [← hndw_nat]; exact hm2_p8
        rw [hm2_p8', hnd_old_2 pw.toNat hpLI 8 (Or.inr (Or.inl rfl))]
      have hp8_lt_264 : nodeF s0 (hdr s0 t 5) pw.toNat 8 < 2 ^ 64 := by
        unfold nodeF memW; rcases s0.memory _ with ⟨w⟩; exact w.isLt
      apply Ret.seq_ite
      intro cw8 hcw8
      have hcw8_spec : (cw8 ≠ 0 → nodeF s0 (hdr s0 t 5) pw.toNat 8 = nw.toNat) ∧
          (cw8 = 0 → nodeF s0 (hdr s0 t 5) pw.toNat 8 ≠ nw.toNat) := by
        obtain ⟨va, vb, hva, hvb, hcw_eq⟩ := evalAt_cmp _ .equal _ _ cw8 hcw8
        obtain ⟨_, hva_mem⟩ := ev_var_node_load (NS s2 L_nd s2.globals m5_val s2.clock) (ofString "p") ndw pw 8#64 hl_nd hl_p (.val (.word va)) hva
        have hm5_p8' : m5_val (ndw + pw * 32 + 8#64) = .word (BitVec.ofNat 64 (nodeF s0 (hdr s0 t 5) pw.toNat 8)) := hm5_p8
        simp only [NS_memory, hm5_p8', ValueHOL.val.injEq, HolWordLab.word.injEq] at hva_mem
        subst hva_mem
        simp only [NS_locals, evalAt, evalHOLExact, hl_n, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hvb
        subst hvb
        have hva_nat : (BitVec.ofNat 64 (nodeF s0 (hdr s0 t 5) pw.toNat 8)).toNat = nodeF s0 (hdr s0 t 5) pw.toNat 8 := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp8_lt_264]
        constructor
        · intro hnz; by_contra hne
          have hbne : BitVec.ofNat 64 (nodeF s0 (hdr s0 t 5) pw.toNat 8) ≠ nw := fun h =>
            hne (by have := congrArg BitVec.toNat h; rw [hva_nat] at this; exact this)
          simp [Compiler.Encoders.Asm.wordCmpHOL, hbne] at hcw_eq
          exact hnz hcw_eq
        · intro hz heq
          have hbeq : BitVec.ofNat 64 (nodeF s0 (hdr s0 t 5) pw.toNat 8) = nw :=
            BitVec.eq_of_toNat_eq (by rw [hva_nat, heq])
          simp [Compiler.Encoders.Asm.wordCmpHOL, hbeq] at hcw_eq
          rw [hz] at hcw_eq; exact absurd hcw_eq (by decide)
      refine ⟨fun hcw8_nz => ?_, fun hcw8_z => ?_⟩
      · have hp8_eq := hcw8_spec.1 hcw8_nz
        refine Ret.ns_storeW (ndw + pw * 32#64 + 8#64) niw
          (eval_node_field_expr _ (ofString "p") ndw pw 8 hl_nd hl_p)
          (by simp [evalAt, evalHOLExact]; exact hl_ni) ?_
        intro _
        apply Ret.ns_ret; intro rv hrv
        simp only [evalAt, evalHOLExact, Option.some.injEq] at hrv
        refine ⟨hrv.symm, ?_⟩
        exact splice_mem_values ch_left (updW m5_val (ndw + pw * 32#64 + 8#64) niw)
          (by rw [if_neg hpnz, if_pos hp8_eq, hm5_eq])
      · have hp8_ne := hcw8_spec.2 hcw8_z
        refine Ret.ns_storeW (ndw + pw * 32#64 + 16#64) niw
          (eval_node_field_expr _ (ofString "p") ndw pw 16 hl_nd hl_p)
          (by simp [evalAt, evalHOLExact]; exact hl_ni) ?_
        intro _
        apply Ret.ns_ret; intro rv hrv
        simp only [evalAt, evalHOLExact, Option.some.injEq] at hrv
        refine ⟨hrv.symm, ?_⟩
        exact splice_mem_values ch_left (updW m5_val (ndw + pw * 32#64 + 16#64) niw)
          (by rw [if_neg hpnz, if_neg hp8_ne, hm5_eq])
  apply Ret.seq_ite
  intro cw_bit _
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · refine Ret.ns_seq_storeW2
      (ndw + niw * 32#64 + 8#64) nlw
      (ndw + niw * 32#64 + 16#64) nw
      (eval_node_field_expr _ (ofString "ni") ndw niw 8 hl_nd hl_ni)
      (by simp [evalAt, evalHOLExact]; exact hl_nl)
      (eval_node_field_expr _ (ofString "ni") ndw niw 16 hl_nd hl_ni)
      (by simp [evalAt, evalHOLExact]; exact hl_n) ?_
    intro _ _
    exact exec_parent_link true _ rfl
  · refine Ret.ns_seq_storeW2
      (ndw + niw * 32#64 + 8#64) nw
      (ndw + niw * 32#64 + 16#64) nlw
      (eval_node_field_expr _ (ofString "ni") ndw niw 8 hl_nd hl_ni)
      (by simp [evalAt, evalHOLExact]; exact hl_n)
      (eval_node_field_expr _ (ofString "ni") ndw niw 16 hl_nd hl_ni)
      (by simp [evalAt, evalHOLExact]; exact hl_nl) ?_
    intro _ _
    exact exec_parent_link false _ rfl

theorem htab_set_body_values_exact {F : Type}
    (s0 : PanSemStateFiniteExact 64 F)
    (tw keyw valw : BitVec 64)
    (ht0 : s0.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hkey0 : s0.locals.lookup (ofString "key") = some (.val (.word keyw)))
    (hval0 : s0.locals.lookup (ofString "value") = some (.val (.word valw)))
    (hA0 : ArenaReady s0)
    (hW0 : HtabWF s0 tw.toNat)
    (hal0 : ∀ i ∈ htabFootprint s0 tw.toNat, Allocated s0 i) :
    Ret s0 (sourceFnBody Guest.Software.guestFn_htab_set)
      (fun rv post => rv = .val (.word 0#64) ∧ HtabSetValuesPost s0 post tw.toNat valw.toNat) := by
  set t := tw.toNat
  have hLF := locFree_valuesExact s0 t valw.toNat
  obtain ⟨hB0, L0, I0, Fr0, hT0⟩ := (htabWF_iff s0 t).mp hW0
  obtain ⟨hnc0_lt, hst0_ge8, hst0_le64, hst0_al, ht_lo, ht_hi, ht_al⟩ := htabBlocks_bounds hB0
  have hnx0_le : hdr s0 t 8 ≤ hdr s0 t 10 + 1 := hB0.2.2.2.2.2.2.2
  have hklen_le60 : hdr s0 t 0 ≤ 60 := hB0.2.2.2.1
  have hklen_le_st : hdr s0 t 0 ≤ hdr s0 t 1 := by have := hB0.2.2.2.2.1; omega
  have hhe : heapEnd = 33806089704 := rfl
  obtain ⟨_, hm0_t0⟩ := word_of_hdr s0 tw 0 (by omega) hB0
  obtain ⟨_, hm0_t1⟩ := word_of_hdr s0 tw 1 (by omega) hB0
  obtain ⟨_, hm0_t4⟩ := word_of_hdr s0 tw 4 (by omega) hB0
  obtain ⟨_, hm0_t5⟩ := word_of_hdr s0 tw 5 (by omega) hB0
  obtain ⟨_, hm0_t7⟩ := word_of_hdr s0 tw 7 (by omega) hB0
  set klenw := BitVec.ofNat 64 (hdr s0 t 0)
  set stridew := BitVec.ofNat 64 (hdr s0 t 1)
  set keysw := BitVec.ofNat 64 (hdr s0 t 4)
  set nodesw0 := BitVec.ofNat 64 (hdr s0 t 5)
  set rootw0 := BitVec.ofNat 64 (hdr s0 t 7)
  have hklenw_nat : klenw.toNat = hdr s0 t 0 := by rw [BitVec.toNat_ofNat]; omega
  have hstridew_nat : stridew.toNat = hdr s0 t 1 := by rw [BitVec.toNat_ofNat]; omega
  have hkeysw_nat : keysw.toNat = hdr s0 t 4 := by
    have hk_in := (hB0.1 (hdr s0 t 4, (hdr s0 t 10 + 1) * hdr s0 t 1) (by simp [htabFootprint])).1
    unfold Inside at hk_in; rw [BitVec.toNat_ofNat]; omega
  have hnodesw0_nat : nodesw0.toNat = hdr s0 t 5 := by
    have hn_in := (hB0.1 (hdr s0 t 5, (hdr s0 t 10 + 1) * 32) (by simp [htabFootprint])).1
    unfold Inside at hn_in; rw [BitVec.toNat_ofNat]; omega
  htab_unfold Guest.Software.guestFn_htab_set
  apply Ret.dec_lf hLF; intro vkl hvkl
  obtain ⟨_, rfl⟩ := ev_field_load s0 (ofString "t") tw 0#64 ht0 vkl hvkl
  have hm0 : s0.memory (tw + 0#64) = .word klenw := hm0_t0
  rw [hm0]
  apply Ret.dec_lf hLF; intro vst hvst
  obtain ⟨_, rfl⟩ := ev_field_load _ (ofString "t") tw 8#64
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht0, show ofString "klen" ≠ ofString "t" by decide]) vst hvst
  have hm8 : (setVarHOLFinite (ofString "klen") (.val (.word klenw)) s0).memory (tw + 8#64) = .word stridew := hm0_t1
  rw [hm8]
  let s_fl_pre := setVarHOLFinite (ofString "stride") (.val (.word stridew))
    (setVarHOLFinite (ofString "klen") (.val (.word klenw)) s0)
  have ht_fl_pre : s_fl_pre.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [s_fl_pre, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht0,
      show ofString "stride" ≠ ofString "t" by decide, show ofString "klen" ≠ ofString "t" by decide]
  have hkey_fl_pre : s_fl_pre.locals.lookup (ofString "key") = some (.val (.word keyw)) := by
    simp [s_fl_pre, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hkey0,
      show ofString "stride" ≠ ofString "key" by decide, show ofString "klen" ≠ ofString "key" by decide]
  refine Ret.decCall2_lf hLF hA0.1.code (by decide) lookup_htab_find_leaf tw keyw
    (by simp [evalAt, evalHOLExact]; exact ht_fl_pre)
    (by simp [evalAt, evalHOLExact]; exact hkey_fl_pre) ?_
  intro leafw post_fl hrun_fl
  let entry_fl := callEntryStateHOLFinite s_fl_pre
    ((HolFiniteMapExact.empty.update (ofString "t", .val (.word tw))).update (ofString "key", .val (.word keyw)))
  have hW_entry_fl : HtabWF entry_fl t := (htabWF_locals s0 _ _ t).mpr hW0
  have hfl_spec := find_leaf_spec_wf entry_fl tw
    (by simp [entry_fl, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "key" ≠ ofString "t" by decide])
    hW_entry_fl (.val (.word leafw)) (by rw [hrun_fl])
  rw [hrun_fl] at hfl_spec
  obtain ⟨lw', hlw_eq, hfr_fl, hleaf_cases⟩ := hfl_spec
  dsimp only at hfr_fl
  injection hlw_eq with h1; injection h1 with h2; subst h2
  have hs_lf_fr : LocFrame s0 (setVarHOLFinite (ofString "leaf") (.val (.word leafw)) { post_fl with locals := s_fl_pre.locals }) := by
    unfold LocFrame at hfr_fl ⊢; dsimp [setVarHOLFinite]; rw [hfr_fl]; rfl
  apply Ret.dec_lf hLF; intro vks hvks
  obtain ⟨_, hvks_eq⟩ := ev_field_load _ (ofString "t") tw 32#64
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "leaf" ≠ ofString "t" by decide]; exact ht_fl_pre) vks hvks
  have hm32_lf : (setVarHOLFinite (ofString "leaf") (.val (.word leafw)) { post_fl with locals := s_fl_pre.locals }).memory (tw + 32#64) = .word keysw := by
    rw [hs_lf_fr.memory]; exact hm0_t4
  rw [hm32_lf] at hvks_eq; subst hvks_eq
  let s_k := setVarHOLFinite (ofString "keys") (.val (.word keysw))
    (setVarHOLFinite (ofString "leaf") (.val (.word leafw)) { post_fl with locals := s_fl_pre.locals })
  have hs_k_fr : LocFrame s0 s_k := hs_lf_fr.setVar _ _
  have hcode_sk : s_k.code = originalRuntimeCode := by unfold LocFrame at hs_k_fr; rw [hs_k_fr]; exact hA0.1.code
  have ht_sk : s_k.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [s_k, s_fl_pre, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht0,
      show ofString "keys" ≠ ofString "t" by decide, show ofString "leaf" ≠ ofString "t" by decide,
      show ofString "stride" ≠ ofString "t" by decide, show ofString "klen" ≠ ofString "t" by decide]
  have hkey_sk : s_k.locals.lookup (ofString "key") = some (.val (.word keyw)) := by
    simp [s_k, s_fl_pre, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hkey0,
      show ofString "keys" ≠ ofString "key" by decide, show ofString "leaf" ≠ ofString "key" by decide,
      show ofString "stride" ≠ ofString "key" by decide, show ofString "klen" ≠ ofString "key" by decide]
  have hval_sk : s_k.locals.lookup (ofString "value") = some (.val (.word valw)) := by
    simp [s_k, s_fl_pre, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hval0,
      show ofString "keys" ≠ ofString "value" by decide, show ofString "leaf" ≠ ofString "value" by decide,
      show ofString "stride" ≠ ofString "value" by decide, show ofString "klen" ≠ ofString "value" by decide]
  have hleaf_sk : s_k.locals.lookup (ofString "leaf") = some (.val (.word leafw)) := by
    simp [s_k, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "keys" ≠ ofString "leaf" by decide]
  have hkeys_sk : s_k.locals.lookup (ofString "keys") = some (.val (.word keysw)) := by
    simp [s_k, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hkl_sk : s_k.locals.lookup (ofString "klen") = some (.val (.word klenw)) := by
    simp [s_k, s_fl_pre, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "keys" ≠ ofString "klen" by decide, show ofString "leaf" ≠ ofString "klen" by decide,
      show ofString "stride" ≠ ofString "klen" by decide]
  have hst_sk : s_k.locals.lookup (ofString "stride") = some (.val (.word stridew)) := by
    simp [s_k, s_fl_pre, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "keys" ≠ ofString "stride" by decide, show ofString "leaf" ≠ ofString "stride" by decide]
  refine Ret.ite_ret
    (fun _ => by
      rw [evaluateHOLFiniteState_decCall_total]
      split
      · simp
      · split
        · simp
        · split
          · simp
          · dsimp only
            rw [fixClockHOLFinite_evaluateState]
            rcases evaluateHOLFiniteState _ _ with ⟨r, _⟩
            cases r with
            | none => simp
            | some r =>
              cases r with
              | returned _ =>
                dsimp only; split
                · exact noFlow_seq_right fun _ => noFlow_ret
                · simp
              | _ => simp)
    ?_
  intro cw_lf hcw_lf
  have hcw_lf_spec : (cw_lf ≠ 0 → leafw = 0) ∧ (cw_lf = 0 → leafw ≠ 0) := by
    obtain ⟨va, vb, hva, hvb, hcw_eq⟩ := evalAt_cmp s_k .equal _ _ cw_lf hcw_lf
    simp [FrontendCodecComputation.expToHOLStructural, evalAt, evalHOLExact, hleaf_sk] at hva hvb
    subst hva hvb
    constructor
    · intro hnz; by_contra hne
      have hne' : leafw ≠ 0#64 := hne
      simp [Compiler.Encoders.Asm.wordCmpHOL, hne'] at hcw_eq
      exact hnz hcw_eq
    · intro hz heq
      have heq' : leafw = 0#64 := heq
      simp [Compiler.Encoders.Asm.wordCmpHOL, heq'] at hcw_eq
      rw [hz] at hcw_eq; exact absurd hcw_eq (by decide)
  refine ⟨fun hcw_nz => ?_, fun hcw_z => ?_⟩
  · have hlf0 := hcw_lf_spec.1 hcw_nz
    have hcnt0 : hdr s0 t 3 = 0 := by
      rcases hleaf_cases with ⟨_, hc⟩ | ⟨hnz, _⟩
      · exact hc
      · exact absurd hlf0 hnz
    exact set_branch_empty_values_exact s0 s_k tw keyw valw hs_k_fr hA0 hW0 hal0 hcnt0 ht_sk hkey_sk hval_sk
  · have hlf_nz := hcw_lf_spec.2 hcw_z
    obtain ⟨_, hcnt_pos, hleaf_mem⟩ := hleaf_cases.resolve_left (fun h => hlf_nz h.1)
    have hleaf_L0 : leafw.toNat ∈ L0 := hleaf_mem L0 I0 Fr0 hT0
    have hleaf_rng := (hT0.2.2.1 leafw.toNat).mp (List.mem_append_left _ (List.mem_append_left _ hleaf_L0))
    have hleaf_lt_nc0 : leafw.toNat < hdr s0 t 10 + 1 := by omega
    have hkeys0_in := (hB0.1 (hdr s0 t 4, (hdr s0 t 10 + 1) * hdr s0 t 1) (by simp [htabFootprint])).1
    change hdr s0 t 4 ≥ sourceBase ∧ hdr s0 t 4 + (hdr s0 t 10 + 1) * hdr s0 t 1 ≤ heapEnd at hkeys0_in
    have hmul_lf_le : leafw.toNat * hdr s0 t 1 + hdr s0 t 1 ≤ (hdr s0 t 10 + 1) * hdr s0 t 1 := by
      have h1 : (leafw.toNat + 1) * hdr s0 t 1 ≤ (hdr s0 t 10 + 1) * hdr s0 t 1 := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul] at h1; exact h1
    set lkeyw := keysw + leafw * stridew
    have hlkeyw_nat : lkeyw.toNat = hdr s0 t 4 + leafw.toNat * hdr s0 t 1 := by
      have hmul_nat : (leafw * stridew).toNat = leafw.toNat * hdr s0 t 1 := by
        rw [BitVec.toNat_mul, hstridew_nat, Nat.mod_eq_of_lt (by omega)]
      change (keysw + leafw * stridew).toNat = _
      rw [BitVec.toNat_add, hkeysw_nat, hmul_nat, Nat.mod_eq_of_lt (by omega)]
    have hev_lkey : evalAt s_k (.op .add [.var .local (ofString "keys"),
        .panop .mul [.var .local (ofString "leaf"), .var .local (ofString "stride")]]) =
        some (.val (.word lkeyw)) := by
      simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
        hkeys_sk, hleaf_sk, hst_sk, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
        valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
      have hz : leafw * stridew + (0 : BitVec 64) = leafw * stridew := BitVec.add_zero _
      rw [hz]
    refine Ret.decCall3_lf hLF hcode_sk (by decide) (by decide) (by decide)
      lookup_memeq_fn lkeyw keyw klenw hev_lkey
      (by simp [evalAt, evalHOLExact]; exact hkey_sk)
      (by simp [evalAt, evalHOLExact]; exact hkl_sk) ?_
    intro eqw post_meq hrun_meq
    let entry_meq := callEntryStateHOLFinite s_k
      (((HolFiniteMapExact.empty.update (ofString "a", .val (.word lkeyw))).update
        (ofString "b", .val (.word keyw))).update (ofString "n", .val (.word klenw)))
    have hfr_meq_eval := locFrameW_eval (sourceFnBody Guest.Software.guestFn_memeq) (by rfl) entry_meq
    rw [hrun_meq] at hfr_meq_eval; dsimp only at hfr_meq_eval
    let s_eq := setVarHOLFinite (ofString "eq") (.val (.word eqw)) { post_meq with locals := s_k.locals }
    have hs_eq_fr : LocFrame s0 s_eq := by
      unfold LocFrame at hs_k_fr hfr_meq_eval ⊢
      dsimp [s_eq, setVarHOLFinite]; rw [hfr_meq_eval]
      dsimp [entry_meq, callEntryStateHOLFinite, decClockHOLFinite]; rw [hs_k_fr]
    have hcode_seq : s_eq.code = originalRuntimeCode := by unfold LocFrame at hs_eq_fr; rw [hs_eq_fr]; exact hA0.1.code
    have ht_seq : s_eq.locals.lookup (ofString "t") = some (.val (.word tw)) := by
      simp [s_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht_sk, show ofString "eq" ≠ ofString "t" by decide]
    have hkey_seq : s_eq.locals.lookup (ofString "key") = some (.val (.word keyw)) := by
      simp [s_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hkey_sk, show ofString "eq" ≠ ofString "key" by decide]
    have hval_seq : s_eq.locals.lookup (ofString "value") = some (.val (.word valw)) := by
      simp [s_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hval_sk, show ofString "eq" ≠ ofString "value" by decide]
    have hleaf_seq : s_eq.locals.lookup (ofString "leaf") = some (.val (.word leafw)) := by
      simp [s_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hleaf_sk, show ofString "eq" ≠ ofString "leaf" by decide]
    have hkeys_seq : s_eq.locals.lookup (ofString "keys") = some (.val (.word keysw)) := by
      simp [s_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hkeys_sk, show ofString "eq" ≠ ofString "keys" by decide]
    have hkl_seq : s_eq.locals.lookup (ofString "klen") = some (.val (.word klenw)) := by
      simp [s_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hkl_sk, show ofString "eq" ≠ ofString "klen" by decide]
    have hst_seq : s_eq.locals.lookup (ofString "stride") = some (.val (.word stridew)) := by
      simp [s_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hst_sk, show ofString "eq" ≠ ofString "stride" by decide]
    have heq_seq : s_eq.locals.lookup (ofString "eq") = some (.val (.word eqw)) := by
      simp [s_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    refine Ret.ite_ret (fun _ => noFlow_seq_right fun _ => noFlow_ret) ?_
    intro cw_eq hcw_eq
    have hcw_eq_spec : (cw_eq ≠ 0 → eqw ≠ 0) ∧ (cw_eq = 0 → eqw = 0) := by
      obtain ⟨va, vb, hva, hvb, hcwe⟩ := evalAt_cmp s_eq .notEqual _ _ cw_eq hcw_eq
      simp [FrontendCodecComputation.expToHOLStructural, evalAt, evalHOLExact, heq_seq] at hva hvb
      subst hva hvb
      constructor
      · intro hnz heq0
        have heq0' : eqw = 0#64 := heq0
        simp [Compiler.Encoders.Asm.wordCmpHOL, heq0'] at hcwe
        exact hnz hcwe
      · intro hz; by_contra hne
        have hne' : eqw ≠ 0#64 := hne
        simp [Compiler.Encoders.Asm.wordCmpHOL, hne'] at hcwe
        rw [hz] at hcwe; exact absurd hcwe (by decide)
    refine ⟨fun _ => ?_, fun hcw_eq_z => ?_⟩
    · exact set_branch_overwrite_values_exact s0 s_eq tw leafw valw hs_eq_fr hA0 hW0 hleaf_mem ht_seq hleaf_seq hval_seq
    · have heqw0 : eqw = 0 := hcw_eq_spec.2 hcw_eq_z
      have hG_entry_meq : GuestInv entry_meq := by
        have hfr_em : LocFrame s0 entry_meq := by
          unfold LocFrame at hs_k_fr ⊢
          dsimp [entry_meq, callEntryStateHOLFinite, decClockHOLFinite]; rw [hs_k_fr]
        unfold LocFrame at hfr_em; rw [hfr_em]
        exact guestInv_with_locals_clock s0 _ _ hA0.1
      have ha_meq : entry_meq.locals.lookup (ofString "a") = some (.val (.word lkeyw)) := by
        simp [entry_meq, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "n" ≠ ofString "a" by decide, show ofString "b" ≠ ofString "a" by decide]
      have hb_meq : entry_meq.locals.lookup (ofString "b") = some (.val (.word keyw)) := by
        simp [entry_meq, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "n" ≠ ofString "b" by decide]
      have hn_meq : entry_meq.locals.lookup (ofString "n") = some (.val (.word klenw)) := by
        simp [entry_meq, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hklen_ge1 : 1 ≤ klenw.toNat := by rw [hklenw_nat]; exact hB0.2.2.1
      have hklen_le60_w : klenw.toNat ≤ 60 := by rw [hklenw_nat]; exact hklen_le60
      have hlkey_nw : lkeyw.toNat + klenw.toNat < 2 ^ 64 := by rw [hlkeyw_nat, hklenw_nat]; omega
      have hrun_meq0 : (evaluateHOLFiniteState entry_meq (sourceFnBody Guest.Software.guestFn_memeq)).1 =
          some (.returned (.val (.word 0))) := by rw [hrun_meq, heqw0]
      have hkey_nw : keyw.toNat + klenw.toNat < 2 ^ 64 :=
        memeq_ret_key_no_wrap entry_meq hG_entry_meq lkeyw keyw klenw
          hklen_ge1 hklen_le60_w ha_meq hb_meq hn_meq (.val (.word 0)) hrun_meq0
      have hdiff_meq := memeq_body_ret0_exists_diff entry_meq hG_entry_meq lkeyw keyw klenw
        hklen_le60_w hlkey_nw hkey_nw ha_meq hb_meq hn_meq hrun_meq0
      have hmemB_em_s0 : ∀ addr : Nat, memB entry_meq addr = memB s0 addr := by
        intro addr
        have hmem_em : entry_meq.memory = s0.memory := by
          dsimp [entry_meq, callEntryStateHOLFinite, decClockHOLFinite]; exact hs_k_fr.memory
        have hbe_em : entry_meq.be = s0.be := by
          dsimp [entry_meq, callEntryStateHOLFinite, decClockHOLFinite]
          unfold LocFrame at hs_k_fr; rw [hs_k_fr]
        simp [memB, hmem_em, hbe_em]
      have hdiff_s0 : ∃ k < klenw.toNat,
          memB s0 ((keyw + BitVec.ofNat 64 k).toNat) ≠ memB s0 ((lkeyw + BitVec.ofNat 64 k).toNat) := by
        obtain ⟨k, hk, hne⟩ := hdiff_meq
        rw [hmemB_em_s0, hmemB_em_s0] at hne
        exact ⟨k, hk, hne.symm⟩
      have hev_lkey_seq : evalAt s_eq (.op .add [.var .local (ofString "keys"),
          .panop .mul [.var .local (ofString "leaf"), .var .local (ofString "stride")]]) =
          some (.val (.word lkeyw)) := by
        simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
          hkeys_seq, hleaf_seq, hst_seq, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
          valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
        have hz : leafw * stridew + (0 : BitVec 64) = leafw * stridew := BitVec.add_zero _
        rw [hz]
      refine Ret.decCall3_lf hLF hcode_seq (by decide) (by decide) (by decide)
        lookup_htab_first_diff keyw lkeyw klenw
        (by simp [evalAt, evalHOLExact]; exact hkey_seq)
        hev_lkey_seq
        (by simp [evalAt, evalHOLExact]; exact hkl_seq) ?_
      intro dw post_fd hrun_fd
      let entry_fd := callEntryStateHOLFinite s_eq
        (((HolFiniteMapExact.empty.update (ofString "a", .val (.word keyw))).update
          (ofString "b", .val (.word lkeyw))).update (ofString "key_len", .val (.word klenw)))
      have hfr_fd_eval := locFrameW_eval (sourceFnBody Guest.Software.guestFn_htab_first_diff) (by rfl) entry_fd
      rw [hrun_fd] at hfr_fd_eval; dsimp only at hfr_fd_eval
      have hdiff_fd : ∃ k < klenw.toNat,
          memB entry_fd ((keyw + BitVec.ofNat 64 k).toNat) ≠ memB entry_fd ((lkeyw + BitVec.ofNat 64 k).toNat) := by
        have hmem_fd : entry_fd.memory = s0.memory := by
          dsimp [entry_fd, callEntryStateHOLFinite, decClockHOLFinite]; exact hs_eq_fr.memory
        have hbe_fd : entry_fd.be = s0.be := by
          dsimp [entry_fd, callEntryStateHOLFinite, decClockHOLFinite]
          unfold LocFrame at hs_eq_fr; rw [hs_eq_fr]
        obtain ⟨k, hk, hne⟩ := hdiff_s0
        refine ⟨k, hk, ?_⟩
        simpa [memB, hmem_fd, hbe_fd] using hne
      obtain ⟨dw', hdw_eq, hd_lt_w⟩ := htab_first_diff_ret_lt entry_fd keyw lkeyw klenw hklen_le60_w hdiff_fd
        (by simp [entry_fd, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "key_len" ≠ ofString "a" by decide, show ofString "b" ≠ ofString "a" by decide])
        (by simp [entry_fd, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "key_len" ≠ ofString "b" by decide])
        (by simp [entry_fd, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
        (.val (.word dw)) (by rw [hrun_fd])
      injection hdw_eq with h1; injection h1 with h2; subst h2
      have hd_lt : dw.toNat < 8 * hdr s0 t 0 := by rw [← hklenw_nat]; exact hd_lt_w
      let s_d := setVarHOLFinite (ofString "d") (.val (.word dw)) { post_fd with locals := s_eq.locals }
      have hs_d_fr : LocFrame s0 s_d := by
        unfold LocFrame at hs_eq_fr hfr_fd_eval ⊢
        dsimp [s_d, setVarHOLFinite]; rw [hfr_fd_eval]
        dsimp [entry_fd, callEntryStateHOLFinite, decClockHOLFinite]; rw [hs_eq_fr]
      have ht_sd : s_d.locals.lookup (ofString "t") = some (.val (.word tw)) := by
        simp [s_d, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht_seq, show ofString "d" ≠ ofString "t" by decide]
      have hkey_sd : s_d.locals.lookup (ofString "key") = some (.val (.word keyw)) := by
        simp [s_d, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hkey_seq, show ofString "d" ≠ ofString "key" by decide]
      have hval_sd : s_d.locals.lookup (ofString "value") = some (.val (.word valw)) := by
        simp [s_d, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hval_seq, show ofString "d" ≠ ofString "value" by decide]
      apply Ret.dec_lf hLF; intro vnd hvnd
      obtain ⟨_, hvnd_eq⟩ := ev_field_load s_d (ofString "t") tw 40#64 ht_sd vnd hvnd
      rw [hs_d_fr.memory, hm0_t5] at hvnd_eq; subst hvnd_eq
      apply Ret.dec_lf hLF; intro vp0 hvp0
      have hvp0_eq : vp0 = .val (.word 0#64) := by
        simp [FrontendCodecComputation.expToHOLStructural, evalAt, evalHOLExact] at hvp0; exact hvp0.symm
      subst hvp0_eq
      apply Ret.dec_lf hLF; intro vr0 hvr0
      obtain ⟨_, hvr0_eq⟩ := ev_field_load _ (ofString "t") tw 56#64
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "p" ≠ ofString "t" by decide, show ofString "nodes" ≠ ofString "t" by decide]; exact ht_sd) vr0 hvr0
      have hm56_sd : (setVarHOLFinite (ofString "p") (.val (.word 0#64))
          (setVarHOLFinite (ofString "nodes") (.val (.word nodesw0)) s_d)).memory (tw + 56#64) = .word rootw0 := by
        dsimp [setVarHOLFinite]; rw [hs_d_fr.memory]; exact hm0_t7
      rw [hm56_sd] at hvr0_eq; subst hvr0_eq
      let s_lp := setVarHOLFinite (ofString "n") (.val (.word rootw0))
        (setVarHOLFinite (ofString "p") (.val (.word 0#64))
          (setVarHOLFinite (ofString "nodes") (.val (.word nodesw0)) s_d))
      have hs_lp_fr : LocFrame s0 s_lp := ((hs_d_fr.setVar _ _).setVar _ _).setVar _ _
      have hrootw0_nat : rootw0.toNat = hdr s0 t 7 := by
        have hr_mem : hdr s0 t 7 ∈ L0 ++ I0 := (hT0.2.2.2.2.2.2.2.1 hcnt_pos).1
        have hr_rng := (hT0.2.2.1 (hdr s0 t 7)).mp (List.mem_append_left _ hr_mem)
        rw [BitVec.toNat_ofNat]; omega
      apply Ret.seq
      · intro v hv
        refine False.elim (while_noRet _ _ (fun st v' => ?_) s_lp.clock s_lp le_rfl v hv)
        exact NoRet.dec' (NoRet.seq (NoRet.ite NoRet.brk NoRet.skip)
          (NoRet.seq NoRet.assign (NoRet.ite NoRet.assign NoRet.assign))) st v'
      intro u_lp hu_lp
      have hT_slp : TreeWF L0 I0 Fr0 (hdr s0 t 8) (hdr s0 t 0) (hdr s0 t 3) (hdr s0 t 7) (hdr s0 t 9)
          (nodeF s_lp nodesw0.toNat) (fun i => memW s0 (hdr s0 t 6 + 8 * i)) := by
        have hnf_eq : nodeF s_lp nodesw0.toNat = nodeF s0 (hdr s0 t 5) := by
          funext z off; simp [nodeF, memW, hs_lp_fr.memory, hnodesw0_nat]
        rw [hnf_eq]; exact hT0
      obtain ⟨hu_fr_lp, hu_keep, pw, nw, hp_ulp, hn_ulp, hnw_LI, hpw_spec⟩ :=
        set_descent_loop s_lp u_lp nodesw0 dw rootw0 L0 I0 Fr0
          (hdr s0 t 8) (hdr s0 t 0) (hdr s0 t 3) (hdr s0 t 7) (hdr s0 t 9)
          (fun i => memW s0 (hdr s0 t 6 + 8 * i))
          hcnt_pos hd_lt (by omega) hrootw0_nat hT_slp
          (by simp [s_lp, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "n" ≠ ofString "nodes" by decide, show ofString "p" ≠ ofString "nodes" by decide])
          (by simp [s_lp, s_d, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "n" ≠ ofString "d" by decide, show ofString "p" ≠ ofString "d" by decide,
            show ofString "nodes" ≠ ofString "d" by decide])
          (by simp [s_lp, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "n" ≠ ofString "p" by decide])
          (by simp [s_lp, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
          _ rfl hu_lp
      have hu_fr : LocFrame s0 u_lp := hs_lp_fr.trans hu_fr_lp
      have hpw_spec0 : (pw.toNat = 0 ∧ nw.toNat = hdr s0 t 7) ∨
          (pw.toNat ∈ I0 ∧ nw.toNat ≠ hdr s0 t 7 ∧ pw.toNat = nodeF s0 (hdr s0 t 5) nw.toNat 0) := by
        have hnf_eq : nodeF s_lp nodesw0.toNat nw.toNat 0 = nodeF s0 (hdr s0 t 5) nw.toNat 0 := by
          simp [nodeF, memW, hs_lp_fr.memory, hnodesw0_nat]
        rw [hnf_eq] at hpw_spec; exact hpw_spec
      have ht_ulp : u_lp.locals.lookup (ofString "t") = some (.val (.word tw)) := by
        rw [hu_keep (ofString "t") (by decide) (by decide)]
        simp [s_lp, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht_sd,
          show ofString "n" ≠ ofString "t" by decide, show ofString "p" ≠ ofString "t" by decide,
          show ofString "nodes" ≠ ofString "t" by decide]
      have hkey_ulp : u_lp.locals.lookup (ofString "key") = some (.val (.word keyw)) := by
        rw [hu_keep (ofString "key") (by decide) (by decide)]
        simp [s_lp, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hkey_sd,
          show ofString "n" ≠ ofString "key" by decide, show ofString "p" ≠ ofString "key" by decide,
          show ofString "nodes" ≠ ofString "key" by decide]
      have hval_ulp : u_lp.locals.lookup (ofString "value") = some (.val (.word valw)) := by
        rw [hu_keep (ofString "value") (by decide) (by decide)]
        simp [s_lp, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hval_sd,
          show ofString "n" ≠ ofString "value" by decide, show ofString "p" ≠ ofString "value" by decide,
          show ofString "nodes" ≠ ofString "value" by decide]
      have hd_ulp : u_lp.locals.lookup (ofString "d") = some (.val (.word dw)) := by
        rw [hu_keep (ofString "d") (by decide) (by decide)]
        simp [s_lp, s_d, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "n" ≠ ofString "d" by decide, show ofString "p" ≠ ofString "d" by decide,
          show ofString "nodes" ≠ ofString "d" by decide]
      have hmem_u : u_lp.memory = s0.memory := hu_fr.memory
      have hA_ulp : ArenaReady u_lp := by
        unfold LocFrame at hu_fr; rw [hu_fr]; exact (arenaReady_locals s0 _ _).mpr hA0
      have hNS_ulp : NodeState u_lp t (L0 ++ I0) Fr0 := by
        have hNS0 : NodeState s0 t (L0 ++ I0) Fr0 := ⟨hB0, hT0.2.1, hT0.2.2.1, hT0.2.2.2.2.2.2.2.2.2.2.2⟩
        unfold LocFrame at hu_fr; rw [hu_fr]; exact hNS0
      have hcnt_le_ulp : hdr u_lp t 3 ≤ (L0 ++ I0).length := by
        have hh3_u : hdr u_lp t 3 = hdr s0 t 3 := by unfold hdr memW; rw [hmem_u]
        have hlen := hT0.1; rw [hh3_u, List.length_append]; omega
      have hal_ulp : ∀ i ∈ htabFootprint u_lp t, Allocated u_lp i := by
        unfold LocFrame at hu_fr; rw [hu_fr]; exact hal0
      refine Ret.decCall_new_leaf_lf hLF tw keyw valw (L0 ++ I0) Fr0
        (by simp [evalAt, evalHOLExact]; exact ht_ulp)
        (by simp [evalAt, evalHOLExact]; exact hkey_ulp)
        (by simp [evalAt, evalHOLExact]; exact hval_ulp)
        hA_ulp hNS_ulp hcnt_le_ulp hal_ulp ?_
      intro nlw Fr1 s1 hA1 hNS1 _ _ hh3_1 _ _ n8_1 _ _ ordc_1 hnd_1 hord_1 _ hfp_1 _ _ hloc_1
      let s1_nl := setVarHOLFinite (ofString "nl") (.val (.word nlw)) s1
      have hA1_nl : ArenaReady s1_nl := (arenaReady_locals s1 _ s1.clock).mpr hA1
      have hNS1_nl : NodeState s1_nl t ((L0 ++ I0) ++ [nlw.toNat]) Fr1 := hNS1
      have hal1_nl : ∀ i ∈ htabFootprint s1_nl t, Allocated s1_nl i := fun i hi => (hfp_1 i hi).1
      have ht_s1nl : s1_nl.locals.lookup (ofString "t") = some (.val (.word tw)) := by
        simp [s1_nl, setVarHOLFinite, hloc_1, HolFiniteMapExact.lookup_update, FUPDATE, ht_ulp,
          show ofString "nl" ≠ ofString "t" by decide]
      have hd_s1nl : s1_nl.locals.lookup (ofString "d") = some (.val (.word dw)) := by
        simp [s1_nl, setVarHOLFinite, hloc_1, HolFiniteMapExact.lookup_update, FUPDATE, hd_ulp,
          show ofString "nl" ≠ ofString "d" by decide]
      refine Ret.decCall_new_internal_lf hLF tw dw ((L0 ++ I0) ++ [nlw.toNat]) Fr1
        (by simp [evalAt, evalHOLExact]; exact ht_s1nl)
        (by simp [evalAt, evalHOLExact]; exact hd_s1nl)
        hA1_nl hNS1_nl hal1_nl ?_
      intro niw Fr2 s2 hA2 hNS2 _ _ hh3_2 _ _ _ _ _ _ hnd_2 hord_2 _ _ _ _ hloc_2
      let L_cur := (u_lp.locals.update (ofString "nl", .val (.word nlw))).update (ofString "ni", .val (.word niw))
      have hs2_ni_eq : setVarHOLFinite (ofString "ni") (.val (.word niw)) s2 =
          NS s2 L_cur s2.globals s2.memory s2.clock := by
        simp [setVarHOLFinite, NS, hloc_2, hloc_1, L_cur]
      rw [hs2_ni_eq]
      have hh_u : ∀ k, hdr u_lp t k = hdr s0 t k := fun k => by unfold hdr memW; rw [hmem_u]
      have hh3_20 : hdr s2 t 3 = hdr s0 t 3 + 1 := hh3_2.trans (hh3_1.trans (by rw [hh_u 3]))
      have hnl_mem_A1 : nlw.toNat ∈ (L0 ++ I0) ++ [nlw.toNat] := List.mem_append_right _ (by simp)
      have hnl8_20 : nodeF s2 (hdr s2 t 5) nlw.toNat 8 = valw.toNat :=
        (hnd_2 nlw.toNat hnl_mem_A1 8 (Or.inr (Or.inl rfl))).trans n8_1
      have hcnt_lt_nc1 : hdr s0 t 3 < hdr s1 tw.toNat 10 + 1 := by
        have hB1 : HtabBlocks s1 tw.toNat := hNS1.1
        have hnx1_le : hdr s1 tw.toNat 8 ≤ hdr s1 tw.toNat 10 + 1 := hB1.2.2.2.2.2.2.2
        have hnd1 := (List.nodup_append.mp hNS1.2.1).1
        have hr1 : ∀ x ∈ (L0 ++ I0) ++ [nlw.toNat], 1 ≤ x ∧ x < hdr s1 tw.toNat 8 := fun x hx =>
          (hNS1.2.2.1 x).mp (List.mem_append_left _ hx)
        have hlen_le := nodup_len_le_range hnd1 hr1
        have hL0_len : L0.length = hdr s0 t 3 := hT0.1
        have hnl_rng := hr1 nlw.toNat (List.mem_append_right _ (by simp))
        simp only [List.length_append, List.length_singleton] at hlen_le
        omega
      have hord_cnt_20 : memW s2 (hdr s2 t 6 + 8 * hdr s0 t 3) = nlw.toNat := by
        have h1 := hord_2 (hdr s0 t 3) hcnt_lt_nc1
        have h2 : memW s1 (hdr s1 t 6 + 8 * hdr s0 t 3) = nlw.toNat := by rw [← hh_u 3]; exact ordc_1
        exact h1.trans h2
      have hord_old_20 : ∀ i, i < hdr s0 t 3 →
          memW s2 (hdr s2 t 6 + 8 * i) = memW s0 (hdr s0 t 6 + 8 * i) := by
        intro i hi
        have h1 := hord_2 i (lt_trans hi hcnt_lt_nc1)
        have h2 : memW s1 (hdr s1 t 6 + 8 * i) = memW u_lp (hdr u_lp t 6 + 8 * i) :=
          hord_1 i (by rw [hh_u 3]; exact hi)
        have h3 : memW u_lp (hdr u_lp t 6 + 8 * i) = memW s0 (hdr s0 t 6 + 8 * i) := by
          rw [hh_u 6]; unfold memW; rw [hmem_u]
        exact (h1.trans h2).trans h3
      have hnd_old_20 : ∀ z ∈ L0 ++ I0, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
          nodeF s2 (hdr s2 t 5) z off = nodeF s0 (hdr s0 t 5) z off := by
        intro z hz off hoff
        have h1 := hnd_2 z (List.mem_append_left _ hz) off hoff
        have h2 : nodeF s1 (hdr s1 t 5) z off = nodeF u_lp (hdr u_lp t 5) z off := hnd_1 z hz off hoff
        have h3 : nodeF u_lp (hdr u_lp t 5) z off = nodeF s0 (hdr s0 t 5) z off := by
          rw [hh_u 5]; unfold nodeF memW; rw [hmem_u]
        exact (h1.trans h2).trans h3
      exact set_splice_values_exact s0 s2 tw dw pw nw nlw niw valw L0 I0 Fr0 Fr2 L_cur
        (by simp [L_cur, HolFiniteMapExact.lookup_update, FUPDATE, ht_ulp,
          show ofString "ni" ≠ ofString "t" by decide, show ofString "nl" ≠ ofString "t" by decide])
        (by simp [L_cur, HolFiniteMapExact.lookup_update, FUPDATE, hp_ulp,
          show ofString "ni" ≠ ofString "p" by decide, show ofString "nl" ≠ ofString "p" by decide])
        (by simp [L_cur, HolFiniteMapExact.lookup_update, FUPDATE, hn_ulp,
          show ofString "ni" ≠ ofString "n" by decide, show ofString "nl" ≠ ofString "n" by decide])
        (by simp [L_cur, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "ni" ≠ ofString "nl" by decide])
        (by simp [L_cur, HolFiniteMapExact.lookup_update, FUPDATE])
        hA2 hNS2 hT0 hnw_LI hpw_spec0 hh3_20 hnl8_20 hord_cnt_20 hord_old_20 hnd_old_20

theorem seq_call_htab_set_void_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (et ekey eval_ : ExpHOL 64) (cont : ProgHOL 64)
    (tw keyw valw : BitVec 64)
    (het : evalAt s et = some (.val (.word tw)))
    (hekey : evalAt s ekey = some (.val (.word keyw)))
    (heval : evalAt s eval_ = some (.val (.word valw)))
    (hAR : ArenaReady s)
    (hWF : HtabWF s tw.toNat)
    (hal : ∀ i ∈ htabFootprint s tw.toNat, Allocated s i)
    (hnt : (evaluateHOLFiniteState s
      (.seq (.call (some (none, none)) (ofString "htab_set") [et, ekey, eval_]) cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq (.call (some (none, none)) (ofString "htab_set") [et, ekey, eval_]) cont)).1) :
    ∃ (mid : PanSemStateFiniteExact 64 F),
      HtabExitAt tw.toNat s mid ∧
      HtabSetValuesPost s mid tw.toNat valw.toNat ∧
      mid.be = s.be ∧
      mid.locals = s.locals ∧
      globN mid "scratch_ptr" = globN s "scratch_ptr" ∧
      globN mid "frame_mem_ptr" = globN s "frame_mem_ptr" ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      evaluateHOLFiniteState s
        (.seq (.call (some (none, none)) (ofString "htab_set") [et, ekey, eval_]) cont) =
        evaluateHOLFiniteState mid cont := by
  rw [evaluateHOLFiniteState_seq_line780] at hnt hres
  set cprog := ProgHOL.call (some (none, none)) (ofString "htab_set") [et, ekey, eval_]
  rcases hc_eval : evaluateHOLFiniteState s cprog with ⟨rc, mid⟩
  have hc_eval_orig := hc_eval
  rw [hc_eval] at hnt hres
  dsimp only [cprog] at hc_eval
  rw [evaluateHOLFiniteState_call] at hc_eval
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [et, ekey, eval_] = some [.val (.word tw), .val (.word keyw), .val (.word valw)] := by
    unfold evalAt at het hekey heval
    simp [evalListHOLFinite, evalListHOLExact, het, hekey, heval]
  have hlk := pan_three_word_lookup s.code.lookup (ofString "htab_set")
    (ofString "t") (ofString "key") (ofString "value") (sourceFnBody Guest.Software.guestFn_htab_set)
    tw keyw valw (by decide) (by decide) (by decide) (by rw [hAR.1.code]; exact lookup_htab_set)
  rw [hargs] at hc_eval; dsimp only at hc_eval; rw [hlk] at hc_eval; dsimp only at hc_eval
  by_cases hcz : s.clock = 0
  · rw [if_pos hcz] at hc_eval; injection hc_eval with hr _; subst hr; simp at hnt
  · rw [if_neg hcz] at hc_eval
    let cmap := (((HolFiniteMapExact.empty.update (ofString "t", ValueHOL.val (.word tw))).update
      (ofString "key", ValueHOL.val (.word keyw))).update (ofString "value", ValueHOL.val (.word valw)))
    let ent := callEntryStateHOLFinite s cmap
    have hent_AR : ArenaReady ent := (arenaReady_with_locals s cmap (s.clock - 1)).2 hAR
    have hent_WF : HtabWF ent tw.toNat := (htabWF_locals s cmap (s.clock - 1) tw.toNat).mpr hWF
    have hent_t : ent.locals.lookup (ofString "t") = some (.val (.word tw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "value" ≠ ofString "t" by decide, show ofString "key" ≠ ofString "t" by decide]
    have hent_key : ent.locals.lookup (ofString "key") = some (.val (.word keyw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "value" ≠ ofString "key" by decide]
    have hent_val : ent.locals.lookup (ofString "value") = some (.val (.word valw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_htab_set) with ⟨rb, sb⟩
    have hrun' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_htab_set) = (rb, sb) := hrun
    rw [hrun'] at hc_eval
    cases rb with
    | none =>
      injection hc_eval with hr _; subst hr; exact absurd hres not_resumes_error
    | some rb' =>
      cases rb' with
      | timeOut =>
        injection hc_eval with hr _; subst hr; simp at hnt
      | «break» | «continue» | error =>
        injection hc_eval with hr _; subst hr; exact absurd hres not_resumes_error
      | finalFfi _ =>
        injection hc_eval with hr _; subst hr
        exfalso; rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      | exception e ev =>
        injection hc_eval with hr _; subst hr
        exfalso
        rcases hres with ⟨_, h⟩ | ⟨e', ev', h, hne⟩
        · simp at h
        · dsimp only at h; injection h with h'; injection h' with he1 he2; subst he1 he2
          exact htab_set_no_catchable_exn ent hAR.1.code e ev hne (congrArg Prod.fst hrun)
      | returned vb =>
        have hexit := htab_set_body_spec ent tw keyw valw hent_t hent_key hent_val hent_AR hent_WF hal vb (congrArg Prod.fst hrun)
        have hret_vals := htab_set_body_values_exact ent tw keyw valw hent_t hent_key hent_val hent_AR hent_WF hal vb (congrArg Prod.fst hrun)
        obtain ⟨rfl, hvals⟩ := hret_vals
        have hbe_sb : sb.be = s.be := by
          have inv := (M13.evaluateHOLFiniteState_guestInv_be ent (sourceFnBody Guest.Software.guestFn_htab_set) hent_AR.1).2
          rwa [hrun] at inv
        have hrun_snd : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_htab_set)).2 = sb :=
          congrArg Prod.snd hrun
        rw [hrun_snd] at hexit hvals
        obtain ⟨hAsb, hWsb, hh0, hh1, hhp, hfp, hfr, hgl⟩ := hexit
        dsimp only at hc_eval
        have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word 0#64) : ValueHOL 64)) .one = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        rw [if_pos hsh] at hc_eval
        injection hc_eval with hr hmid
        subst hr
        have hmid_AR : ArenaReady mid := by
          rw [← hmid]; exact (arenaReady_with_locals sb s.locals sb.clock).2 hAsb
        have hmid_WF : HtabWF mid tw.toNat := by
          rw [← hmid]; exact (htabWF_locals sb s.locals sb.clock tw.toNat).mpr hWsb
        have hseq_eq : evaluateHOLFiniteState s (.seq cprog cont) = evaluateHOLFiniteState mid cont := by
          rw [evaluateHOLFiniteState_seq_line780, hc_eval_orig]
        have hexit_mid : HtabExitAt tw.toNat s mid := by
          refine ⟨hmid_AR, hmid_WF,
            by rw [← hmid]; exact hh0,
            by rw [← hmid]; exact hh1,
            by rw [← hmid]; exact hhp,
            fun i hi => by
              rw [← hmid] at hi ⊢
              exact hfp i hi,
            fun a hk hf => by
              rw [← hmid] at hf ⊢
              exact hfr a hk hf,
            fun k hk => by
              rw [← hmid]
              exact hgl k hk⟩
        have hvals_mid : HtabSetValuesPost s mid tw.toNat valw.toNat := by
          rw [← hmid]; exact hvals
        have hsp_mid : globN mid "scratch_ptr" = globN s "scratch_ptr" :=
          globN_eq_of_lookup (hexit_mid.2.2.2.2.2.2.2 (ofString "scratch_ptr") (by decide))
        have hfmp_mid : globN mid "frame_mem_ptr" = globN s "frame_mem_ptr" :=
          globN_eq_of_lookup (hexit_mid.2.2.2.2.2.2.2 (ofString "frame_mem_ptr") (by decide))
        exact ⟨mid, hexit_mid, hvals_mid,
          by rw [← hmid]; exact hbe_sb,
          by rw [← hmid],
          hsp_mid, hfmp_mid, hnt, hres, hseq_eq⟩

end HtabSetExactValues

end InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBal
