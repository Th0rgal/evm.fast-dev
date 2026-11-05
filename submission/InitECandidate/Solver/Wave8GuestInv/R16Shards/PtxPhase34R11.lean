import InitECandidate.Solver.Wave8GuestInv.R16Shards.PtxPhase1R11

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R13Shards

/-- The message result additionally owns its live log storage outside the world. -/
def RetMessageOutputStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F →
    Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post S Nd => RetMessageOutput s r post S Nd ∧
    ∀ v, r = some (.returned v) → ∃ w : BitVec 64,
      v = .val (.word w) ∧ LogsOwnedDisj post S Nd (memW post (w.toNat + 16))

def BoListArgStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧ BoListArg s ∧ memW s (locN s "l") ≠ 0

namespace PtxP34
open PtxP1

theorem lookup_process_message_call :
    originalRuntimeCode.lookup (ofString "process_message_call") =
      some ((sourceFunctionEntry Guest.Software.guestFn_process_message_call).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 607 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_process_message_call) rfl

theorem msgReady_with_msg_local {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (hmsg : locals.lookup (ofString "msg") = s.locals.lookup (ofString "msg"))
    (h : MsgReady s) : MsgReady { s with locals := locals, clock := k } := by
  have hm := locN_congr s locals k "msg" hmsg
  obtain ⟨hA, S, hW, hm152, hm160, hin, hw, hd1, hd2, hav, hgas, hroles⟩ := h
  refine ⟨(arenaReady_with_locals s locals k).mpr hA, S,
    (worldTyped_with_locals s locals k S).mpr hW, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change memW s (locN { s with locals := locals, clock := k } "msg" + 152) ∈ S
    rw [hm]; exact hm152
  · change memW s (locN { s with locals := locals, clock := k } "msg" + 160) ∈ S
    rw [hm]; exact hm160
  · change Inside (locN { s with locals := locals, clock := k } "msg", 176) sourceBase (globN s "heap_ptr")
    rw [hm]; exact hin
  · change WordsOK s (locN { s with locals := locals, clock := k } "msg", 176)
    rw [hm]; exact hw
  · intro t ht i hi; rw [hm]; exact hd1 t ht i hi
  · intro j hj; rw [hm]; exact hd2 j hj
  · obtain ⟨Nd, hTr, hdTr⟩ := hav
    refine ⟨Nd, hTr, fun o ho j hj => ?_⟩
    change o ∈ [(locN { s with locals := locals, clock := k } "msg", 176)] at ho
    rw [hm] at ho; exact hdTr o ho j hj
  · change memW s (locN { s with locals := locals, clock := k } "msg" + 40) < 2 ^ 63
    rw [hm]; exact hgas
  · change RolesOK s S (worldRoleSlots s ++
      [(memW s (locN { s with locals := locals, clock := k } "msg" + 152), "frame.addr"),
       (memW s (locN { s with locals := locals, clock := k } "msg" + 160), "frame.key")])
      (journalRoleSlots s)
    rw [hm]; exact hroles

theorem msg_word_of_var_eval {F : Type} (s : PanSemStateFiniteExact 64 F) (mv : ValueHOL 64)
    (he : evalAt s (.var .local (ofString "m")) = some mv)
    (hsh : shapeEqHOL (shapeOfHOLExact mv) .one = true) :
    mv = .val (.word (BitVec.ofNat 64 (locN s "m"))) := by
  rw [shapeEqHOL_eq_true] at hsh
  obtain ⟨wm, rfl⟩ := shape_one_word hsh
  have hlu : s.locals.lookup (ofString "m") = some (.val (.word wm)) := by
    simpa [evalAt, evalHOLExact] using he
  have hloc : locN s "m" = wm.toNat := by simp [locN, hlu]
  rw [hloc, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem lookup_pmc_msg_value {F : Type} (s : PanSemStateFiniteExact 64 F)
    (vs : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hc : s.code = originalRuntimeCode)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "m")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "process_message_call") vs =
      some (body', callee, ret')) :
    callee.lookup (ofString "msg") = some (.val (.word (BitVec.ofNat 64 (locN s "m")))) := by
  obtain ⟨mv, he, hm_lu⟩ := params_one_value s (ofString "process_message_call") (ofString "msg")
    .one _ .one (by rw [hc]; exact lookup_process_message_call)
    (.var .local (ofString "m")) vs body' callee ret' ha hl
  have ha' := ha
  rw [evalListHOLFinite_eq_toExact] at ha'
  simp only [evalListHOLExact, he, Option.some.injEq] at ha'
  subst ha'
  have hsh : shapeEqHOL (shapeOfHOLExact mv) .one = true := by
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
    split at hl
    · cases hl
    · rename_i exactBody exactLocals exactShape raw
      unfold lookupCodeHOLExact at raw
      have hlk : s.code.lookup (ofString "process_message_call") =
          some ([(ofString "msg", .one)], (sourceFunctionEntry Guest.Software.guestFn_process_message_call).2.2.1, .one) := by
        rw [hc]; exact lookup_process_message_call
      rw [hlk] at raw
      dsimp only at raw
      split at raw
      · rename_i hcond
        have hall := hcond.2.2
        simp [shapeEqHOL_eq_true] at hall ⊢
        exact hall.symm
      · cases raw
  rw [msg_word_of_var_eval s mv he hsh] at hm_lu
  exact hm_lu

theorem entry_pmc :
    CallEntryOn PtxMessageReady MsgReady (ofString "process_message_call")
      [.var .local (ofString "m")] := by
  intro F s vs body callee ret hc hP ha hl
  have hlu := lookup_pmc_msg_value s vs body callee ret hc ha hl
  let s_msg := setVarHOLFinite (ofString "msg") (.val (.word (BitVec.ofNat 64 (locN s "m")))) s
  have hs_lu : s_msg.locals.lookup (ofString "msg") =
      some (.val (.word (BitVec.ofNat 64 (locN s "m")))) := by
    simp [s_msg, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  exact msgReady_with_msg_local s_msg callee (s.clock - 1) (hlu.trans hs_lu.symm) hP.2

def pmcScratchSpec : List (String × Nat × Nat) :=
  [("b2_v", 128, 128), ("bn_expw", 352, 352), ("bn_gamma", 384, 384), ("evm_key_buf", 32, 32),
   ("keccak_pad", 136, 136), ("keccak_st", 200, 200), ("mpt_nib_scratch", 64, 64), ("pre_hdr_buf", 96, 96),
   ("rmd_h", 40, 40), ("rmd_pad", 128, 128), ("rmd_x", 128, 128), ("sha_pad", 128, 128),
   ("sha_st", 64, 64), ("sk_buf", 64, 52), ("u256_ws", 640, 640)]

theorem pmcScratchSpec_ok : ScratchSpec pmcScratchSpec := by
  unfold ScratchSpec pmcScratchSpec
  decide

/-- R11's conditional scratch footprint, with the strengthened return contract. -/
def PmcStrong : Prop :=
  WorldKeepsIn MsgReady
    (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)])
    (fun s => (locN s "msg", 176) ::
      pmcScratchSpec.map (fun e => bufferRegion s (e.1, e.2.2)))
    ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
     ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    RetMessageOutputStrong (ofString "process_message_call")

theorem resume_pmc_strong (hwk_strong : PmcStrong) :
    DecCallResumeOn PtxMessageReady TxAfterCall (ofString "out")
      (ofString "process_message_call") [.var .local (ofString "m")] := by
  intro F s vs body callee ret v post hc hP ha hl hb
  unfold PmcStrong at hwk_strong
  have hMR := entry_pmc s vs body callee ret hc hP ha hl
  have hwk := funSpec_at_lookup hwk_strong s hc vs body callee ret hl hMR (by rw [hb]; simp)
  rw [hb] at hwk; dsimp only at hwk
  have hwsi := hwk (Or.inl ⟨v, rfl⟩)
  obtain ⟨_, S, hWT_ce, hm152, hm160, _, _, hd_tab, hd_fix, hav_tr, _, _⟩ := hMR
  obtain ⟨Nd, hTr_ce, hd_tr⟩ := hav_tr
  have hWTW_ce : WorldTypedWith (callEntryStateHOLFinite s callee) S Nd :=
    ⟨hWT_ce.1, hWT_ce.2.1, hWT_ce.2.2.1, hTr_ce⟩
  have hmsg_disj_owned : ∀ j ∈ worldOwned (callEntryStateHOLFinite s callee) S Nd,
      Disj (locN (callEntryStateHOLFinite s callee) "msg", 176) j := by
    intro j hj
    unfold worldOwned at hj
    rcases List.mem_append.mp hj with h1 | hnd
    · rcases List.mem_append.mp h1 with htab | hfix
      · obtain ⟨t, ht, hi⟩ := List.mem_flatMap.mp htab
        exact hd_tab t ht j hi
      · exact hd_fix j hfix
    · exact hd_tr _ (by simp) j hnd
  let Rlist : List Ivl :=
    (locN (callEntryStateHOLFinite s callee) "msg", 176) ::
      pmcScratchSpec.map (fun e => bufferRegion (callEntryStateHOLFinite s callee) (e.1, e.2.2))
  have hR_disj : IvlsDisj Rlist (worldTypedIvls (callEntryStateHOLFinite s callee) S Nd) := by
    intro i hi j hj
    rcases List.mem_cons.mp hi with rfl | hi_gs
    · exact hmsg_disj_owned j (R13Shards.worldTypedIvls_sub_worldOwned hj)
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi_gs
      obtain ⟨hgb, hnu, _, hle⟩ := pmcScratchSpec_ok e he
      exact bufferRegion_disj_le hWTW_ce (e.1, e.2.1) hgb hnu e.2.2 hle j hj
  have hT_in : ∀ t ∈ [memW (callEntryStateHOLFinite s callee) (locN (callEntryStateHOLFinite s callee) "msg" + 152),
      memW (callEntryStateHOLFinite s callee) (locN (callEntryStateHOLFinite s callee) "msg" + 160)], t ∈ S := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact hm152
    · exact hm160
  obtain ⟨hAp, _, hg_kept, hrec_kept, hwsi_step⟩ := hwsi
  obtain ⟨S', Nd', _, hWTW_post, _, _, hret_msg⟩ := hwsi_step S Nd hWTW_ce hT_in hR_disj
  obtain ⟨out, rfl, hw_out, hin_out, hdisj_out, hll_out⟩ := hret_msg.1 v rfl
  obtain ⟨out', heq, hlogs_disj⟩ := hret_msg.2 _ rfl
  have hout_eq : out = out' := by cases heq; rfl
  subst out'
  let resumed := setVarHOLFinite (ofString "out") (.val (.word out)) { post with locals := s.locals }
  have hW_resumed : WorldOK resumed :=
    worldOK_of_parts
      ((arenaReady_with_locals post resumed.locals post.clock).mpr hAp)
      ((R13Shards.worldTypedWith_with_locals post resumed.locals post.clock S' Nd').mpr hWTW_post)
  have hE := hP.1.2
  have hbo_eq : globN post "bo" = globN s "bo" :=
    R16Shards.globN_eq_of_lookup (hg_kept (ofString "bo") (by decide))
  have hjcap_eq : globN post "journal_cap" = globN s "journal_cap" :=
    R16Shards.globN_eq_of_lookup (hg_kept (ofString "journal_cap") (by decide))
  have hbo8 : globN s "bo" % 8 = 0 := (R13Shards.bo_words hWT_ce.2.2.1 hE.bo_nz).2.1
  have hR_bo : ∀ i ∈ Rlist, Disj i (globN s "bo", 88) :=
    fun i hi => hR_disj i hi _ (bo_mem_typed (s := callEntryStateHOLFinite s callee) hE.bo_nz)
  have hR_zero : ∀ i ∈ Rlist, i.2 = 0 → i.1 % 8 = 0 := by
    intro i hi hz
    rcases List.mem_cons.mp hi with rfl | hi_gs
    · simp at hz
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi_gs
      exact bufferRegion_zero_aligned _ e.1 e.2.2 (by have := (pmcScratchSpec_ok e he).2.2.1; omega) hz
  have hkw : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat),
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := by
    intro k hk
    have hoffs : k ∈ ([0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80] : List Nat) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp
    have hrec_s : RecordsKept (fun _ => Rlist)
        [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
         ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
        s post := hrec_kept
    apply hrec_s ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp) hE.bo_nz k hoffs
    intro i hi hch
    have hk_in : k + 8 ≤ 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
    have hbase : (globN s "bo" + k) % 8 = 0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
    exact R13Shards.not_cellHits_of_disj hbase
      (fun hz => hR_zero i hi hz)
      ⟨by dsimp; omega, by dsimp; omega⟩
      (R13Shards.disj_symm (hR_bo i hi)) hch
  have hidx_lu : resumed.locals.lookup (ofString "index") = s.locals.lookup (ofString "index") := by
    simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "out" ≠ ofString "index" from by decide]
  have hi_eq : locN resumed "index" = locN s "index" :=
    locN_congr s resumed.locals post.clock "index" hidx_lu
  have hEnv_resumed : TxEnv resumed := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show globN post "bo" ≠ 0; rw [hbo_eq]; exact hE.bo_nz
    · show memW post (globN post "bo" + 24) ≠ 0; rw [hbo_eq, hkw 24 (by simp)]; exact hE.bo24
    · show memW post (globN post "bo" + 32) ≠ 0; rw [hbo_eq, hkw 32 (by simp)]; exact hE.bo32
    · show memW post (globN post "bo" + 40) ≠ 0; rw [hbo_eq, hkw 40 (by simp)]; exact hE.bo40
    · show memW post (globN post "bo" + 72) ≠ 0; rw [hbo_eq, hkw 72 (by simp)]; exact hE.bo72
    · show locN resumed "index" < memW post (globN post "bo" + 80)
      rw [hi_eq, hbo_eq, hkw 80 (by simp)]; exact hE.idx_lt
    · show globN post "journal_cap" ≠ 0; rw [hjcap_eq]; exact hE.jcap_nz
  have hout_loc : locN resumed "out" = out.toNat := by
    simp [resumed, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  refine ⟨⟨hW_resumed, hEnv_resumed⟩, ?_, ?_, ?_, S', Nd',
    (R13Shards.worldTypedWith_with_locals post resumed.locals post.clock S' Nd').mpr hWTW_post, ?_, ?_⟩
  · change WordsOK post (locN resumed "out", 96)
    rw [hout_loc]; exact hw_out
  · change Inside (locN resumed "out", 96) sourceBase (globN post "heap_ptr")
    rw [hout_loc]; exact hin_out
  · change LogsListOK resumed (memW post (locN resumed "out" + 16))
    rw [hout_loc]
    exact (R13Shards.logsListOK_with_locals post resumed.locals post.clock _).mpr hll_out
  · change IvlsDisj [(locN resumed "out", 96)] (worldOwned post S' Nd')
    rw [hout_loc]; exact hdisj_out
  · change LogsOwnedDisj post S' Nd' (memW post (locN resumed "out" + 16))
    rw [hout_loc]; exact hlogs_disj

end PtxP34

theorem ptxPhase3_cut_strong (h : PtxCallees) (hwk : PtxP34.PmcStrong)
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn TxAfterCall tail b) :
    TerminatingProgBoundedOn PtxMessageReady (ptxPhase3 tail) (ptxCost3 + b) := by
  have hb : TerminatingProgBoundedOn PtxMessageReady (ptxPhase3 tail)
      (K.«process_message_call» + b + 1) := by
    unfold ptxPhase3 ptxCode
    exact TerminatingProgBoundedOn.decCall_on h.gb_process_message_call
      (ofString "out") .one [.var .local (ofString "m")]
      PtxP34.entry_pmc (PtxP34.resume_pmc_strong hwk) htail
  have he : K.«process_message_call» + b + 1 = ptxCost3 + b := by
    unfold ptxCost3; omega
  rw [he] at hb
  intro F s hc hp
  exact hb s hc hp

end InitECandidate.Solver.Wave8GuestInv.R16Shards
