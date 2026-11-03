import InitECandidate.Solver.Wave8GuestInv.ContractParts.C07
import InitECandidate.Solver.Wave8GuestInv.R13Shards.PtxPhase45R11

/-! Zero-sorry proof of `gbody_process_withdrawals` (`ContractParts/C18.lean`). -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R13Shards

theorem lookup_process_withdrawals :
    originalRuntimeCode.lookup (ofString "process_withdrawals") =
      some ((sourceFunctionEntry Guest.Software.guestFn_process_withdrawals).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 875 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_process_withdrawals) rfl

theorem globN_setGlobal_same {F : Type} (s : PanSemStateFiniteExact 64 F)
    (n : String) (w : BitVec 64) :
    globN (setGlobalHOLFinite (ofString n) (.val (.word w)) s) n = w.toNat := by
  simp [globN, setGlobalHOLFinite, HolFiniteMapExact.update, FUPDATE]

theorem globN_setGlobal_ne {F : Type} (s : PanSemStateFiniteExact 64 F)
    (g : MlS) (v : ValueHOL 64) (n : String) (hne : ofString n ≠ g) :
    globN (setGlobalHOLFinite g v s) n = globN s n := by
  have hl : (s.globals.update (g, v)).lookup (ofString n) = s.globals.lookup (ofString n) := by
    simp [HolFiniteMapExact.update, FUPDATE, Ne.symm hne]
  simp only [globN, setGlobalHOLFinite, hl]

theorem arenaReady_setGlobal_word_ne {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : ArenaReady s) (g : MlS) (w : BitVec 64)
    (h1 : ofString "heap_ptr" ≠ g) (h2 : ofString "frame_mem_ptr" ≠ g)
    (h3 : ofString "scratch_ptr" ≠ g) :
    ArenaReady (setGlobalHOLFinite g (.val (.word w)) s) := by
  refine ⟨guestInv_congr (s := s) rfl rfl rfl rfl h.1, ?_⟩
  have hgw : GlobalsWord (setGlobalHOLFinite g (.val (.word w)) s) :=
    globalsWord_update g w rfl h.2.2.2.2.2.2.2.2.2
  unfold ArenaOK
  rw [globN_setGlobal_ne s g (.val (.word w)) "heap_ptr" h1,
      globN_setGlobal_ne s g (.val (.word w)) "frame_mem_ptr" h2,
      globN_setGlobal_ne s g (.val (.word w)) "scratch_ptr" h3]
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, hgw⟩

theorem worldOK_set_journal_n_zero {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hW : WorldOK s) :
    WorldOK (setGlobalHOLFinite (ofString "journal_n") (.val (.word 0#64)) s) := by
  set s' := setGlobalHOLFinite (ofString "journal_n") (.val (.word 0#64)) s
  obtain ⟨hAs, S, hWT⟩ := hW
  obtain ⟨Nd, hWTW⟩ := (worldTyped_iff_with s S).1 hWT
  obtain ⟨hT, hJ, hF, hTr⟩ := hWTW
  have hAs' : ArenaReady s' :=
    arenaReady_setGlobal_word_ne hAs (ofString "journal_n") 0#64
      (by decide) (by decide) (by decide)
  have hmemW : memW s' = memW s := rfl
  have hhdr : hdr s' = hdr s := rfl
  have hnodeF : nodeF s' = nodeF s := rfl
  have hfp : htabFootprint s' = htabFootprint s := rfl
  have hhWF : ∀ t, HtabWF s t → HtabWF s' t := fun t h =>
    htabWF_congr_unhit hAs.1 hAs'.1 h (fun _ _ _ _ _ => rfl)
  have hlstOK : ∀ l, LstOK s' l ↔ LstOK s l := fun _ => Iff.rfl
  have hhVals : htabValues s' = htabValues s := rfl
  have hwordsOK : ∀ i, WordsOK s' i ↔ WordsOK s i := fun _ => Iff.rfl
  have halloc : ∀ i, Allocated s' i ↔ Allocated s i := by
    intro i
    simp only [Allocated, s',
      globN_setGlobal_ne s (ofString "journal_n") _ "heap_ptr" (by decide),
      globN_setGlobal_ne s (ofString "journal_n") _ "scratch_ptr" (by decide)]
  have hbo_eq : globN s' "bo" = globN s "bo" :=
    globN_setGlobal_ne s (ofString "journal_n") _ "bo" (by decide)
  have hws_eq : globN s' "ws" = globN s "ws" :=
    globN_setGlobal_ne s (ofString "journal_n") _ "ws" (by decide)
  have hbs_eq : globN s' "bs" = globN s "bs" :=
    globN_setGlobal_ne s (ofString "journal_n") _ "bs" (by decide)
  have hts_eq : globN s' "ts" = globN s "ts" :=
    globN_setGlobal_ne s (ofString "journal_n") _ "ts" (by decide)
  have hba_eq : globN s' "bal_accounts" = globN s "bal_accounts" :=
    globN_setGlobal_ne s (ofString "journal_n") _ "bal_accounts" (by decide)
  have hbia_eq : globN s' "bal_idx_accts" = globN s "bal_idx_accts" :=
    globN_setGlobal_ne s (ofString "journal_n") _ "bal_idx_accts" (by decide)
  have hbis_eq : globN s' "bal_idx_stor" = globN s "bal_idx_stor" :=
    globN_setGlobal_ne s (ofString "journal_n") _ "bal_idx_stor" (by decide)
  have hjc_eq : globN s' "journal_cap" = globN s "journal_cap" :=
    globN_setGlobal_ne s (ofString "journal_n") _ "journal_cap" (by decide)
  have hjr_eq : globN s' "journal" = globN s "journal" :=
    globN_setGlobal_ne s (ofString "journal_n") _ "journal" (by decide)
  have hjn_zero : globN s' "journal_n" = 0 := by
    simpa [s'] using globN_setGlobal_same s "journal_n" 0#64
  have hbalRecs : balRecords s' = balRecords s := by
    simp only [balRecords, hba_eq, hhdr, hnodeF, hmemW]
  have hbalObjs : balObjects s' = balObjects s := by
    simp only [balObjects, hbalRecs, lstObjects, hhVals, hmemW]
  have hboObjs : blockOutObjects s' = blockOutObjects s := by
    simp only [blockOutObjects, hbo_eq, hmemW]
  have hgb_ne : ∀ gn ∈ globalBuffers, ofString gn.1 ≠ ofString "journal_n" := by decide
  have hgb_map :
      (globalBuffers.map fun gn => (globN s' gn.1, if globN s' gn.1 = 0 then 0 else gn.2)) =
      (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) := by
    apply List.map_congr_left
    intro gn hgn
    have hge : globN s' gn.1 = globN s gn.1 :=
      globN_setGlobal_ne s (ofString "journal_n") _ gn.1 (hgb_ne gn hgn)
    rw [hge]
  have hfixObjs : fixedObjects s' = fixedObjects s := by
    simp only [fixedObjects, hgb_map, hjc_eq, hjr_eq, hboObjs, hbalObjs]
  have hnodeHeap : NodeHeap s' Nd ↔ NodeHeap s Nd := by
    simp only [NodeHeap, hmemW, halloc, hwordsOK, nodeIvl, KeyIn, NibblesOK]; exact Iff.rfl
  have hnodeExt : nodeExtents s' Nd = nodeExtents s Nd := rfl
  have hrecR_ws : ∀ ks, recRoles s' "ws" ks = recRoles s "ws" ks := fun _ => by
    simp only [recRoles, hws_eq, hmemW]
  have hrecR_bs : ∀ ks, recRoles s' "bs" ks = recRoles s "bs" ks := fun _ => by
    simp only [recRoles, hbs_eq, hmemW]
  have hrecR_ts : ∀ ks, recRoles s' "ts" ks = recRoles s "ts" ks := fun _ => by
    simp only [recRoles, hts_eq, hmemW]
  have hnest_bs : nestRoles s' "bs" "bs.inner" = nestRoles s "bs" "bs.inner" := by
    simp only [nestRoles, hbs_eq, hmemW, hhVals]
  have hnest_ts : nestRoles s' "ts" "ts.inner" = nestRoles s "ts" "ts.inner" := by
    simp only [nestRoles, hts_eq, hmemW, hhVals]
  have hwrs : worldRoleSlots s' = worldRoleSlots s := by
    simp only [worldRoleSlots, hrecR_ws, hrecR_bs, hrecR_ts, hba_eq, hbia_eq, hbis_eq,
      hnest_bs, hnest_ts, hbalRecs, hmemW]
  have hjrs : journalRoleSlots s' = [] := by
    simp [journalRoleSlots, hjn_zero]
  refine ⟨hAs', S, (worldTyped_iff_with s' S).2 ⟨Nd, ?_, ?_, ?_, ?_⟩⟩
  · obtain ⟨hnd, htf, htp, hws_s, hbs_s, hts_s, hgt_s, hb_in, ht_in, hbal_t, hbo_t, hrol⟩ := hT
    refine ⟨hnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht
      refine ⟨hhWF t (htf t ht).1, fun i hi => ?_⟩
      rw [hfp] at hi
      rw [hfixObjs]
      exact ⟨(halloc i).2 ((htf t ht).2 i hi).1, ((htf t ht).2 i hi).2⟩
    · simpa only [hfp] using htp
    · simpa only [hws_eq, hmemW] using hws_s
    · simpa only [hbs_eq, hmemW] using hbs_s
    · simpa only [hts_eq, hmemW] using hts_s
    · intro g hg
      have hg_ne : ofString g ≠ ofString "journal_n" := by
        simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl <;> decide
      rw [globN_setGlobal_ne s (ofString "journal_n") _ g hg_ne]
      exact hgt_s g hg
    · simpa only [hbs_eq, hmemW, HtabValuesIn, hhdr, hnodeF] using hb_in
    · simpa only [hts_eq, hmemW, HtabValuesIn, hhdr, hnodeF] using ht_in
    · simpa only [hbalRecs, hmemW, hlstOK, hhVals] using hbal_t
    · simpa only [hbo_eq, hmemW, hlstOK] using hbo_t
    · rw [hwrs, hjrs]
      refine ⟨fun a ha => ?_, hrol.2.1, fun _ ha => by simp at ha⟩
      rw [List.append_nil] at ha
      exact hrol.1 a (List.mem_append_left _ ha)
  · refine ⟨by rw [hjn_zero]; exact Nat.zero_le _, ?_, ?_, ?_⟩
    · rw [hjc_eq]; exact hJ.2.1
    · rw [hjc_eq, hjr_eq]
      rcases hJ.2.2.1 with h0 | ⟨ha, hw⟩
      · exact Or.inl h0
      · exact Or.inr ⟨(halloc _).2 ha, (hwordsOK _).2 hw⟩
    · intro i hi; rw [hjn_zero] at hi; omega
  · unfold FixedTyped; rw [hfixObjs]
    exact ⟨fun i hi => (hF.1 i hi).elim Or.inl (fun h => Or.inr ⟨(halloc i).2 h.1, (hwordsOK i).2 h.2⟩), hF.2⟩
  · unfold TriesTypedWith
    refine ⟨hnodeHeap.2 hTr.1, ?_, ?_⟩
    · rw [hnodeExt, hfixObjs]; simpa only [hfp] using hTr.2.1
    · simpa only [hws_eq, hmemW, hfp, hhdr, hnodeF] using hTr.2.2

theorem Hoare.dec_fall {P P' Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {names : List String} {name : MlS} {shape : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (hname : ∀ n ∈ names, ofString n ≠ name)
    (hQ : LocalsOnly names Q)
    (hinit : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      evalAt s init = some v → P' (setVarHOLFinite name v s))
    (hbody : Hoare P' body (fun r t => r = none → Q t)) :
    Hoare P (.dec name shape init body) (fun r t => r = none → Q t) :=
  Hoare.dec hname hinit hbody
    (fun _ t locals hl h hr => hQ t locals t.clock hl (h hr))
    (fun _ _ hr => absurd hr (by simp))

theorem Hoare.assign_fall {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {kind : VarKind} {name : MlS} {source : ExpHOL 64}
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      evalAt s source = some v → Q (setKvarHOLFinite kind name v s)) :
    Hoare P (.assign kind name source) (fun r t => r = none → Q t) :=
  Hoare.assign (fun s v hP hv _ => h s v hP hv) (fun _ _ hr => absurd hr (by simp))

theorem «gbody_process_withdrawals» :
  (TerminatingFunBoundedOn GuestInv (ofString "create_ether") K.«create_ether») →
  (TerminatingFunBoundedOn WorldOK (ofString "incorporate_tx_into_block") K.«incorporate_tx_into_block») →
  (TerminatingFunBoundedOn GuestInv (ofString "state_fresh_tx") K.«state_fresh_tx») →
  (TerminatingFunBoundedOn GuestInv (ofString "u256_mul") K.«u256_mul») →
  (WorldKeeps WorldOK (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
    ["heap_ptr", "journal_n", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "create_ether")) →
  (WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr", "journal_n", "ts"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "state_fresh_tx")) →
  (ReadOnlyFn (ofString "u256_mul")) →
  TerminatingFunBoundedOn WorldOK (ofString "process_withdrawals") K.«process_withdrawals» := by
  intro hce hitb hsf hmul wce wsf rmul
  have hwce : KeepsOn WorldOK WorldOK (ofString "create_ether") := by
    apply wce.keepsOn_buffer_parts
    intro F s i hi
    change i ∈ [bufferRegion s ("keccak_pad", 136), bufferRegion s ("keccak_st", 200),
      bufferRegion s ("mpt_nib_scratch", 64), bufferRegion s ("sk_buf", 52)] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact ⟨("keccak_pad", 136), by decide, by decide, 136, le_rfl, rfl⟩
    · exact ⟨("keccak_st", 200), by decide, by decide, 200, le_rfl, rfl⟩
    · exact ⟨("mpt_nib_scratch", 64), by decide, by decide, 64, le_rfl, rfl⟩
    · exact ⟨("sk_buf", 64), by decide, by decide, 52, by decide, rfl⟩
  have hloW : LocalsOnly ([] : List String) WorldOK := LocalsOnly.of_localsFree localsFree_worldOK
  have hbody_hoare : ∀ (e_w e_amt : ExpHOL 64) (args_mul args_ce : List (ExpHOL 64)),
      Hoare WorldOK
        (.dec (ofString "w") .one e_w
          (.dec (ofString "amt") (.comb [.one, .one, .one, .one]) e_amt
            (.decCall (ofString "wei") (.comb [.one, .one, .one, .one]) (ofString "u256_mul") args_mul
              (.seq (.call (some (none, none)) (ofString "create_ether") args_ce)
                (.seq (.assign .global (ofString "journal_n") (.const 0#64))
                  (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])))))))
        (fun r t => r = none → WorldOK t) := by
    intro e_w e_amt args_mul args_ce
    exact Hoare.dec_fall (by simp) hloW
      (fun s _ hW _ => localsFree_worldOK s _ s.clock hW)
      (Hoare.dec_fall (by simp) hloW
        (fun s _ hW _ => localsFree_worldOK s _ s.clock hW)
        (R13Shards.Hoare.decCall_fall (by simp) hloW
          (rmul.resumeOn hloW worldOK_guestInv (ofString "wei") (by simp) args_mul)
          (R13Shards.Hoare.seq_fall
            (Hoare.call_keeps localsFree_worldOK hwce args_ce)
            (R13Shards.Hoare.seq_fall
              (Hoare.assign_fall fun s v hW hv => by
                have hv0 := evalAt_const s 0#64 v hv
                subst hv0
                exact worldOK_set_journal_n_zero hW)
              (Hoare.assign_fall fun s _ hW _ => localsFree_worldOK s _ s.clock hW)))))
  have hbody_inc : ∀ (e_w e_amt : ExpHOL 64) (args_mul args_ce : List (ExpHOL 64)),
      IncrBody (ofString "i")
        (.dec (ofString "w") .one e_w
          (.dec (ofString "amt") (.comb [.one, .one, .one, .one]) e_amt
            (.decCall (ofString "wei") (.comb [.one, .one, .one, .one]) (ofString "u256_mul") args_mul
              (.seq (.call (some (none, none)) (ofString "create_ether") args_ce)
                (.seq (.assign .global (ofString "journal_n") (.const 0#64))
                  (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))))))) := by
    intro e_w e_amt args_mul args_ce
    exact IncrBody.dec _ _ _ (by decide)
      (IncrBody.dec _ _ _ (by decide)
        (IncrBody.decCall _ _ _ _ (by decide)
          (IncrBody.seq _ rfl rfl
            (IncrBody.seq _ rfl rfl IncrBody.incr))))
  refine ⟨_, _, _, lookup_process_withdrawals, ?_⟩
  simp only [InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, List.map_cons, List.map_nil]
  apply TerminatingProgBoundedOn.mono_bound
  · exact TerminatingProgBoundedOn.seq_hoare
      (TerminatingProgBoundedOn.call_on hsf _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
      (Hoare.call_keeps localsFree_worldOK wsf.keepsOn _)
      (TerminatingProgBoundedOn.dec_on localsFree_worldOK _ _ _
        (TerminatingProgBoundedOn.dec_on localsFree_worldOK _ _ _
          (TerminatingProgBoundedOn.dec_on localsFree_worldOK _ _ _
            (TerminatingProgBoundedOn.seq_hoare
              (while_less_localsOnly hloW (ofString "i") (.var .local (ofString "nwd"))
                (TerminatingProgBoundedOn.dec_on localsFree_worldOK _ _ _
                  (TerminatingProgBoundedOn.dec_on localsFree_worldOK _ _ _
                    (TerminatingProgBoundedOn.decCall_on hmul _ _ _
                      (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _)
                      (decCallResumeOn_guestInv worldOK_guestInv _ _ _)
                      (TerminatingProgBoundedOn.seq_guestInv
                        (TerminatingProgBoundedOn.call_guestInv hce _ _)
                        (TerminatingProgBoundedOn.seq_guestInv
                          (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
                          (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _)))))))
                (hbody_hoare _ _ _ _)
                (hbody_inc _ _ _ _))
              (hoare_while_less_localsOnly hloW (ofString "i") (.var .local (ofString "nwd"))
                (hbody_hoare _ _ _ _)
                (hbody_inc _ _ _ _)
                rfl)
              (TerminatingProgBoundedOn.seq_guestInv_after
                (TerminatingProgBoundedOn.call_on hitb _ _ (callEntryOn_of_localsFree localsFree_worldOK _ _))
                worldOK_guestInv
                (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))))))
  · unfold K.«process_withdrawals»; omega

end InitECandidate.Solver.Wave8GuestInv.R16Shards
