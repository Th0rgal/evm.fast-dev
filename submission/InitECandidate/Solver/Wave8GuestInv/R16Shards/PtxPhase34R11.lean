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

/-- Caller locals read by Phase 4 before they are assigned there. `out` is
introduced by Phase 3 itself. The message-building locals `mgas`, `reservoir`
and `m` are not read by Phase 4. -/
def PtxPhase4LocalShapes : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
    (∀ name ∈ (["tx", "index", "sender", "gas", "tx_blob_gas_used"] : List String),
      ∃ w : BitVec 64, s.locals.lookup (ofString name) = some (.val (.word w))) ∧
    (∃ v, s.locals.lookup (ofString "price") = some v ∧
      shapeOfHOLExact v = .comb [.one, .one, .one, .one]) ∧
    (∃ v, s.locals.lookup (ofString "intrinsic") = some v ∧
      shapeOfHOLExact v = .comb [.one, .one, .one])

theorem ptxPhase4LocalShapes_resume {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (h : PtxPhase4LocalShapes s) :
    PtxPhase4LocalShapes (setVarHOLFinite (ofString "out") v { post with locals := s.locals }) := by
  have hlu : ∀ name : String, ofString name ≠ ofString "out" →
      (setVarHOLFinite (ofString "out") v { post with locals := s.locals }).locals.lookup
        (ofString name) = s.locals.lookup (ofString name) := by
    intro name hn
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, Ne.symm hn]
  refine ⟨?_, ?_, ?_⟩
  · intro name hn
    have hne : ofString name ≠ ofString "out" := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hlu name hne]
    exact h.1 name hn
  · rw [hlu "price" (by decide)]; exact h.2.1
  · rw [hlu "intrinsic" (by decide)]; exact h.2.2

namespace PtxP34
open PtxP1

/-- Reassemble the log-list invariant from preservation of the header, live
pointer cells and individual log records. This isolates the memory obligations
of the two ether-creation calls from the list invariant itself. -/
theorem logsListOK_congr_live {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {logs : Nat} (hAs : ArenaOK s) (hgS : GuestInv s) (hgP : GuestInv post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (h : LogsListOK s logs)
    (halloc : Allocated s (logs, 24) → Allocated post (logs, 24))
    (hhead : ∀ k ∈ ([0, 8, 16] : List Nat),
      memW post (logs + k) = memW s (logs + k))
    (hptr : ∀ i, i < memW s (logs + 8) →
      memW post (memW s logs + 8 * i) = memW s (memW s logs + 8 * i))
    (hentry : ∀ i, i < memW s (logs + 8) →
      IvlUnhit s post (memW s (memW s logs + 8 * i), 40)) :
    LogsListOK post logs := by
  rcases h with hz | ⟨hw, ha, hn, hc, he⟩
  · exact Or.inl hz
  have h0 : memW post logs = memW s logs := by simpa using hhead 0 (by simp)
  have h8 := hhead 8 (by simp)
  have h16 := hhead 16 (by simp)
  refine Or.inr ⟨R13Shards.wordsOK_transfer hgS hgP hw, halloc ha, ?_, ?_, ?_⟩
  · rw [h8]; exact hn
  · rw [h8, h16]; exact hc
  · intro i hi
    rw [h8] at hi
    rw [h0, hptr i hi]
    exact ⟨R13Shards.wordAt_transfer hgS hgP (he i hi).1,
      R13Shards.logEntryOK_congr_unhit hAs hgS hgP hhp (he i hi).2 (hentry i hi)⟩

theorem logsListOK_congr_header_unhit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {logs : Nat}
    (hAs : ArenaOK s) (hgS : GuestInv s) (hgP : GuestInv post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (h : LogsListOK s logs)
    (halloc : Allocated s (logs, 24) → Allocated post (logs, 24))
    (hhead : IvlUnhit s post (logs, 24))
    (hptr : ∀ i, i < memW s (logs + 8) →
      memW post (memW s logs + 8 * i) = memW s (memW s logs + 8 * i))
    (hentry : ∀ i, i < memW s (logs + 8) →
      IvlUnhit s post (memW s (memW s logs + 8 * i), 40)) :
    LogsListOK post logs := by
  rcases h with hz | hl
  · exact Or.inl hz
  apply logsListOK_congr_live hAs hgS hgP hhp (Or.inr hl) halloc _ hptr hentry
  intro k hk
  have h8 := hl.1.1
  have hb := (R13Shards.ivl_allocated_bound hAs hl.2.1).2
  apply R13Shards.memW_eq_of_ivlUnhit hhead
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl <;> omega
  · exact hb
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl <;> (constructor <;> omega)

/-- The alternate scratch branch in the R11 ownership predicate is empty:
a 24-byte header cannot start at or above `scratchEnd` and end below it. -/
theorem logsOwnedDisj_header_heap {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {logs : Nat} (h : LogsOwnedDisj s S Nd logs) (hn : logs ≠ 0) :
    Inside (logs, 24) sourceBase (globN s "heap_ptr") := by
  rcases (h hn).1 with hh | ⟨hs, he⟩
  · exact hh
  · unfold Inside at hs
    simp only [he] at hs
    omega

/-- The log header is protected by the world-step frame once its scratch-write
disjointness is established. It remains disjoint from the new owned world. -/
theorem logsOwnedDisj_header_survives {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {logs : Nat}
    {new R : List Ivl} (hAs : ArenaOK s)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hlogs : LogsListOK s logs) (hd : LogsOwnedDisj s S Nd logs) (hn : logs ≠ 0)
    (hold0 : ∀ j ∈ worldOwned s S Nd, j.2 = 0 → j.1 % 8 = 0)
    (hR0 : ∀ j ∈ R, j.2 = 0 → j.1 % 8 = 0)
    (hog : OwnedGrows s post (worldOwned s S Nd) new)
    (hfr : FrameOutside s post (worldOwned s S Nd ++ R ++ [freeGap s]) (heapFree s))
    (hR : ∀ j ∈ R, Disj (logs, 24) j) :
    Inside (logs, 24) sourceBase (globN post "heap_ptr") ∧
    (∀ o ∈ new, Disj (logs, 24) o) ∧ IvlUnhit s post (logs, 24) := by
  rcases hlogs with hz | hl
  · exact False.elim (hn hz)
  exact R13Shards.heap_ivl_survives_step hAs hhp hold0 hR0 hog hfr
    hl.1.1 (by norm_num) (logsOwnedDisj_header_heap hd hn)
    (fun j hj => (hd hn).2.1 _ (by simp) j hj) hR

theorem logsOwnedDisj_entry_survives {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {logs i : Nat}
    {new R : List Ivl} (hAs : ArenaOK s)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hlogs : LogsListOK s logs) (hd : LogsOwnedDisj s S Nd logs) (hn : logs ≠ 0)
    (hi : i < memW s (logs + 8))
    (hold0 : ∀ j ∈ worldOwned s S Nd, j.2 = 0 → j.1 % 8 = 0)
    (hR0 : ∀ j ∈ R, j.2 = 0 → j.1 % 8 = 0)
    (hog : OwnedGrows s post (worldOwned s S Nd) new)
    (hfr : FrameOutside s post (worldOwned s S Nd ++ R ++ [freeGap s]) (heapFree s))
    (hR : ∀ j ∈ R, Disj (memW s (memW s logs + 8 * i), 40) j) :
    Inside (memW s (memW s logs + 8 * i), 40) sourceBase (globN post "heap_ptr") ∧
    (∀ o ∈ new, Disj (memW s (memW s logs + 8 * i), 40) o) ∧
    IvlUnhit s post (memW s (memW s logs + 8 * i), 40) := by
  rcases hlogs with hz | hl
  · exact False.elim (hn hz)
  have he := (hl.2.2.2.2 i hi).2
  exact R13Shards.heap_ivl_survives_step hAs hhp hold0 hR0 hog hfr
    he.1.1 (by norm_num) he.2.1
    (fun j hj => (hd hn).2.2 i hi _ (by simp) j hj) hR

/-- Live pointer-array preservation additionally needs its heap placement.
`LogsOwnedDisj` itself specifies disjointness but not placement of this array. -/
theorem logsOwnedDisj_array_survives {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {logs : Nat}
    {new R : List Ivl} (hAs : ArenaOK s)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hd : LogsOwnedDisj s S Nd logs) (hn : logs ≠ 0)
    (halign : memW s logs % 8 = 0)
    (hin : Inside (memW s logs, 8 * memW s (logs + 8)) sourceBase (globN s "heap_ptr"))
    (hold0 : ∀ j ∈ worldOwned s S Nd, j.2 = 0 → j.1 % 8 = 0)
    (hR0 : ∀ j ∈ R, j.2 = 0 → j.1 % 8 = 0)
    (hog : OwnedGrows s post (worldOwned s S Nd) new)
    (hfr : FrameOutside s post (worldOwned s S Nd ++ R ++ [freeGap s]) (heapFree s))
    (hR : ∀ j ∈ R, Disj (memW s logs, 8 * memW s (logs + 8)) j) :
    (∀ i, i < memW s (logs + 8) →
      memW post (memW s logs + 8 * i) = memW s (memW s logs + 8 * i)) ∧
    (∀ o ∈ new, Disj (memW s logs, 8 * memW s (logs + 8)) o) := by
  have hs := R13Shards.heap_ivl_survives_step hAs hhp hold0 hR0 hog hfr
    halign (by simp) hin (fun j hj => (hd hn).2.1 _ (by simp) j hj) hR
  refine ⟨?_, hs.2.1⟩
  intro i hi
  apply R13Shards.memW_eq_of_ivlUnhit hs.2.2
  · omega
  · exact (R13Shards.ivl_allocated_bound hAs (Or.inl hin)).2
  · constructor <;> dsimp <;> omega

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

/-- The Phase-3 cut also transports the caller-local shapes required downstream. -/
theorem ptxPhase3_cut_strong_shapes (h : PtxCallees) (hwk : PtxP34.PmcStrong)
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn
      (fun s => TxAfterCall s ∧ PtxPhase4LocalShapes s) tail b) :
    TerminatingProgBoundedOn (fun s => PtxMessageReady s ∧ PtxPhase4LocalShapes s)
      (ptxPhase3 tail) (ptxCost3 + b) := by
  have he : CallEntryOn (fun s => PtxMessageReady s ∧ PtxPhase4LocalShapes s)
      MsgReady (ofString "process_message_call") [.var .local (ofString "m")] := by
    intro F s vs body callee ret hc hp ha hl
    exact PtxP34.entry_pmc s vs body callee ret hc hp.1 ha hl
  have hr : DecCallResumeOn (fun s => PtxMessageReady s ∧ PtxPhase4LocalShapes s)
      (fun s => TxAfterCall s ∧ PtxPhase4LocalShapes s) (ofString "out")
      (ofString "process_message_call") [.var .local (ofString "m")] := by
    intro F s vs body callee ret v post hc hp ha hl hb
    exact ⟨PtxP34.resume_pmc_strong hwk s vs body callee ret v post hc hp.1 ha hl hb,
      ptxPhase4LocalShapes_resume s post v hp.2⟩
  have hb : TerminatingProgBoundedOn
      (fun s => PtxMessageReady s ∧ PtxPhase4LocalShapes s) (ptxPhase3 tail)
      (K.«process_message_call» + b + 1) := by
    unfold ptxPhase3 ptxCode
    exact TerminatingProgBoundedOn.decCall_on h.gb_process_message_call
      (ofString "out") .one [.var .local (ofString "m")] he hr htail
  have heq : K.«process_message_call» + b + 1 = ptxCost3 + b := by
    unfold ptxCost3; omega
  rw [heq] at hb
  intro F s hc hp
  exact hb s hc hp

/-- Composition interface for the remaining Phase-4 proof and the shape-aware
Phase-1/2 prefix. Both missing cuts are explicit hypotheses here. -/
theorem gbody_process_transaction_strong_of_cuts
    (h : PtxCallees) (hwk : PtxP34.PmcStrong)
    (h12 : ∀ (tail : ProgHOL 64) (b : Nat),
      TerminatingProgBoundedOn (fun s => PtxMessageReady s ∧ PtxPhase4LocalShapes s) tail b →
      TerminatingProgBoundedOn TxReadyStrong (ptxPhase1 (ptxPhase2 tail))
        (ptxCost1 + (ptxCost2 + b)))
    (h4 : ∀ (tail : ProgHOL 64) (b : Nat),
      TerminatingProgBoundedOn PtxReceiptsDone tail b →
      TerminatingProgBoundedOn (fun s => TxAfterCall s ∧ PtxPhase4LocalShapes s)
        (ptxPhase4 tail) (ptxCost4 + b)) :
    TerminatingFunBoundedOn TxReadyStrong (ofString "process_transaction")
      K.«process_transaction» := by
  refine ⟨_, _, _, ptx_lookup, ?_⟩
  have hb : TerminatingProgBoundedOn TxReadyStrong
      (ptxPhase1 (ptxPhase2 (ptxPhase3 (ptxPhase4 ptxPhase5))))
      (ptxCost1 + (ptxCost2 + (ptxCost3 + (ptxCost4 + ptxCost5)))) :=
    h12 _ _ (ptxPhase3_cut_strong_shapes h hwk
      (h4 _ _ (R13Shards.ptxPhase5_cut h)))
  rw [← ptx_phases_eq, ptx_cost_eq] at hb
  intro F s hc hp
  simpa only [ptxCode, sourceFunctionEntry, Guest.Software.guestFn_process_transaction,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural] using
    (hb (F := F) s hc hp)

end InitECandidate.Solver.Wave8GuestInv.R16Shards
