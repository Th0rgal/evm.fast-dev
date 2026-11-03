import InitECandidate.Solver.Wave8GuestInv.R11Shards.StateRestoreInv

/-! `hoare_stateRestoreTail` and `state_restore` loop helpers (`< 350` LOC). -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R11Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.S06
open InitECandidate.Solver.Wave8Contracts.M08 (globN_eq_of_lookup ivl_allocated_bound
  htabFootprint_eq_of_hdr_unhit htabWF_congr_unhit)
open InitECandidate.Solver.Wave8GuestInv.HtabC00Ports (lookup_htab_del)
open InitECandidate.Solver.Wave8M19.Htab (call0_flow evalList_cons_inv lookupCodeHOLFinite_param_at)

theorem hoare_call_htab_in_S (m0 : BitVec 64 → HolWordLab 64) (S : List Nat) (FO : List Ivl)
    (j0 jc0 jn0 : Nat)
    (hjn_le_cap : jn0 ≤ jc0)
    (halign : (∀ o ∈ FO, o.1 % 8 = 0 ∧ o.2 % 8 = 0) ∧ (jc0 ≠ 0 → j0 % 8 = 0 ∧ j0 + 32 * jc0 ≤ 2 ^ 64))
    {fname : MlS} {restParams : List (MlS × ShapeHOL)} {body : ProgHOL 64} {restArgs : List (ExpHOL 64)}
    (hlook : originalRuntimeCode.lookup fname = some ((ofString "t", .one) :: restParams, body, .one))
    (hafter : ∀ q ∈ restParams, q.1 ≠ ofString "t")
    (hspec : FunSpec HtabArgWF (OnReturn HtabExit) fname) :
    Hoare (fun s => StateRestoreLoopInv m0 S FO j0 jc0 jn0 s ∧ locN s "t" ∈ S)
      (.call (some (none, none)) fname (.var .local (ofString "t") :: restArgs))
      (fun r t => r = none → StateRestoreLoopInv m0 S FO j0 jc0 jn0 t) := by
  refine ⟨fun {F} s hcode ⟨hInv, htS⟩ _ hr => ?_⟩
  obtain ⟨values, body', callee, ret', v, post, hargs, hl, hrun, heval⟩ := call0_flow s _ _ (Or.inl hr)
  rw [heval]; dsimp only
  obtain ⟨tv, vs, rfl, htv⟩ := evalList_cons_inv s _ _ hargs
  obtain ⟨_, hct⟩ := lookupCodeHOLFinite_param_at s.code.lookup fname []
    (ofString "t") .one restParams body .one hafter
    (by rw [hcode]; simpa using hlook) (vpre := []) (by simp) hl
  have hcalleeT : callee.lookup (ofString "t") = s.locals.lookup (ofString "t") := by
    rw [hct]; simp only [evalHOLExact] at htv; exact htv.symm
  have htE : locN (callEntryStateHOLFinite s callee) "t" = locN s "t" := by
    simp only [locN, callEntryStateHOLFinite, hcalleeT]
  have hArgWF : HtabArgWF (callEntryStateHOLFinite s callee) := by
    refine ⟨localsFree_arenaReady s callee (s.clock - 1) hInv.1, ?_, ?_⟩
    · rw [htE]; exact (htabWF_with_locals s callee (s.clock - 1) _).2 (hInv.2.2.2.1 _ htS).1
    · rw [htE]; exact fun i hi => ((hInv.2.2.2.1 _ htS).2 i hi).1
  have hQc := FunSpec.at_lookup hspec s hcode _ body' callee ret' hl hArgWF (by rw [hrun]; simp)
  rw [hrun] at hQc
  have hx := hQc v rfl
  unfold HtabExit at hx; dsimp only at hx; rw [htE] at hx
  exact stateRestoreLoopInv_localsFree m0 S FO j0 jc0 jn0 post s.locals post.clock
    (stateRestoreLoopInv_of_htabExit m0 S FO j0 jc0 jn0 hjn_le_cap halign hInv htS hx)

theorem call0_not_cont_or_break {F : Type} (s : PanSemStateFiniteExact 64 F) (fn : MlS)
    (args : List (ExpHOL 64)) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fn args)).1 ≠ some .continue ∧
    (evaluateHOLFiniteState s (.call (some (none, none)) fn args)).1 ≠ some .break := by
  rw [evaluateHOLFiniteState_call]
  rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | _
  · simp
  · dsimp only
    rcases lookupCodeHOLFinite s.code.lookup fn _ with _ | ⟨_, _, _⟩
    · simp
    · dsimp only; split
      · simp
      · rcases evaluateHOLFiniteState _ _ with ⟨res, _⟩
        rcases res with _ | r
        · simp
        · cases r <;> (dsimp only; try split) <;> simp

theorem dec_not_cont_or_break {F : Type} {s : PanSemStateFiniteExact 64 F}
    {name : MlS} {sh : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (hb : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState t body).1 ≠ some .continue ∧
      (evaluateHOLFiniteState t body).1 ≠ some .break) :
    (evaluateHOLFiniteState s (.dec name sh init body)).1 ≠ some .continue ∧
    (evaluateHOLFiniteState s (.dec name sh init body)).1 ≠ some .break := by
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · simp
  · split
    · exact hb _
    · simp

theorem stateRestoreTail_not_cont_or_break {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s stateRestoreTail).1 ≠ some .continue ∧
    (evaluateHOLFiniteState s stateRestoreTail).1 ≠ some .break := by
  unfold stateRestoreTail
  refine dec_not_cont_or_break fun _ => dec_not_cont_or_break fun _ => dec_not_cont_or_break fun t => ?_
  rw [evaluateHOLFiniteState_ite]
  split
  · split <;> exact call0_not_cont_or_break _ _ _
  · simp

theorem dec_ne_returned {F : Type} {s : PanSemStateFiniteExact 64 F}
    {name : MlS} {sh : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64} {u : ValueHOL 64}
    (hb : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState t body).1 ≠ some (.returned u)) :
    (evaluateHOLFiniteState s (.dec name sh init body)).1 ≠ some (.returned u) := by
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · simp
  · split
    · exact hb _
    · simp

theorem stateRestoreTail_ne_returned {F : Type} (s : PanSemStateFiniteExact 64 F) (u : ValueHOL 64) :
    (evaluateHOLFiniteState s stateRestoreTail).1 ≠ some (.returned u) := by
  unfold stateRestoreTail
  refine dec_ne_returned fun _ => dec_ne_returned fun _ => dec_ne_returned fun t => ?_
  exact ite_ne_returned (fun t v => call0_ne_returned t _ _ v) (fun t v => call0_ne_returned t _ _ v) u

/-- `stateRestoreTail` preserves `StateRestoreLoopInv` whenever `journal_n < jn0`. -/
theorem hoare_stateRestoreTail (m0 : BitVec 64 → HolWordLab 64) (S : List Nat) (FO : List Ivl)
    (j0 jc0 jn0 : Nat)
    (hjn_le_cap : jn0 ≤ jc0)
    (halign : (∀ o ∈ FO, o.1 % 8 = 0 ∧ o.2 % 8 = 0) ∧ (jc0 ≠ 0 → j0 % 8 = 0 ∧ j0 + 32 * jc0 ≤ 2 ^ 64))
    (hset : FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_set"))
    (hdel : FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_del")) :
    Hoare (fun s => StateRestoreLoopInv m0 S FO j0 jc0 jn0 s ∧ globN s "journal_n" < jn0)
      stateRestoreTail
      (fun r t => (r = none ∨ r = some .continue ∨ r = some .break) →
        StateRestoreLoopInv m0 S FO j0 jc0 jn0 t) := by
  have hcall_set := hoare_call_htab_in_S m0 S FO j0 jc0 jn0 hjn_le_cap halign
    (lookup_of_guestAst_getElem 138 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_htab_set) rfl)
    (by intro p hp; rcases List.mem_cons.1 hp with rfl | hp; · decide
        rcases List.mem_cons.1 hp with rfl | hp; · decide
        cases hp)
    hset (restArgs := [.var .local (ofString "key"),
      .load .one (.op .add [.var .local (ofString "r"), .const (BitVec.ofNat 64 24)])])
  have hcall_del := hoare_call_htab_in_S m0 S FO j0 jc0 jn0 hjn_le_cap halign
    lookup_htab_del
    (by intro p hp; rcases List.mem_cons.1 hp with rfl | hp; · decide
        cases hp)
    hdel (restArgs := [.var .local (ofString "key")])
  have hite : Hoare (fun s => StateRestoreLoopInv m0 S FO j0 jc0 jn0 s ∧ locN s "t" ∈ S)
      (.ite (.cmp .notEqual
          (.load .one (.op .add [.var .local (ofString "r"), .const (BitVec.ofNat 64 16)]))
          (.const (BitVec.ofNat 64 0)))
        (.call (some (none, none)) (ofString "htab_set")
          [.var .local (ofString "t"), .var .local (ofString "key"),
           .load .one (.op .add [.var .local (ofString "r"), .const (BitVec.ofNat 64 24)])])
        (.call (some (none, none)) (ofString "htab_del")
          [.var .local (ofString "t"), .var .local (ofString "key")]))
      (fun r t => r = none → StateRestoreLoopInv m0 S FO j0 jc0 jn0 t) :=
    Hoare.ite_fall (Hoare.mono hcall_set (fun _ h => h.1)) (Hoare.mono hcall_del (fun _ h => h.1))
  have hdec_key : Hoare (fun s => StateRestoreLoopInv m0 S FO j0 jc0 jn0 s ∧ locN s "t" ∈ S)
      (.dec (ofString "key") .one
        (.load .one (.op .add [.var .local (ofString "r"), .const (BitVec.ofNat 64 8)]))
        (.ite (.cmp .notEqual
            (.load .one (.op .add [.var .local (ofString "r"), .const (BitVec.ofNat 64 16)]))
            (.const (BitVec.ofNat 64 0)))
          (.call (some (none, none)) (ofString "htab_set")
            [.var .local (ofString "t"), .var .local (ofString "key"),
             .load .one (.op .add [.var .local (ofString "r"), .const (BitVec.ofNat 64 24)])])
          (.call (some (none, none)) (ofString "htab_del")
            [.var .local (ofString "t"), .var .local (ofString "key")])))
      (fun r t => r = none → StateRestoreLoopInv m0 S FO j0 jc0 jn0 t) :=
    Hoare.dec_fall (names := []) (by simp)
      (LocalsOnly.of_localsFree (stateRestoreLoopInv_localsFree m0 S FO j0 jc0 jn0))
      (fun s v ⟨hI, htS⟩ _ =>
        ⟨stateRestoreLoopInv_localsFree m0 S FO j0 jc0 jn0 s _ s.clock hI,
         by simp [locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]; exact htS⟩)
      hite
  have hdec_t : Hoare (fun s => StateRestoreLoopInv m0 S FO j0 jc0 jn0 s ∧
        ∃ rw : BitVec 64, s.locals.lookup (ofString "r") = some (.val (.word rw)) ∧
          rw.toNat = j0 + 32 * globN s "journal_n" ∧ globN s "journal_n" < jn0)
      (.dec (ofString "t") .one (.load .one (.var .local (ofString "r")))
        (.dec (ofString "key") .one
          (.load .one (.op .add [.var .local (ofString "r"), .const (BitVec.ofNat 64 8)]))
          (.ite (.cmp .notEqual
              (.load .one (.op .add [.var .local (ofString "r"), .const (BitVec.ofNat 64 16)]))
              (.const (BitVec.ofNat 64 0)))
            (.call (some (none, none)) (ofString "htab_set")
              [.var .local (ofString "t"), .var .local (ofString "key"),
               .load .one (.op .add [.var .local (ofString "r"), .const (BitVec.ofNat 64 24)])])
            (.call (some (none, none)) (ofString "htab_del")
              [.var .local (ofString "t"), .var .local (ofString "key")]))))
      (fun r t => r = none → StateRestoreLoopInv m0 S FO j0 jc0 jn0 t) :=
    Hoare.dec_fall (names := []) (by simp)
      (LocalsOnly.of_localsFree (stateRestoreLoopInv_localsFree m0 S FO j0 jc0 jn0))
      (fun s v ⟨hI, rw, hrw_lk, hrw_nat, hjn_lt⟩ hev => by
        refine ⟨stateRestoreLoopInv_localsFree m0 S FO j0 jc0 jn0 s _ s.clock hI, ?_⟩
        simp only [evalAt, evalHOLExact, hrw_lk, memLoadHOLExact] at hev
        split at hev
        · cases hm : s.memory rw with
          | word tw =>
            simp only [hm] at hev
            split at hev
            · injection hev with hv; subst hv
              have hloc_t : locN (setVarHOLFinite (ofString "t") (.val (.word tw)) s) "t" = tw.toNat := by
                simp [locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              have hmemW : memW s (j0 + 32 * globN s "journal_n") = tw.toNat := by
                unfold memW; rw [← hrw_nat, BitVec.ofNat_toNat, BitVec.setWidth_eq, hm]
              rw [hloc_t, ← hmemW]
              exact hI.2.2.2.2.2.2.2.2.1 _ hjn_lt
            · cases hev
        · cases hev)
      hdec_key
  have hdec_r : Hoare (fun s => StateRestoreLoopInv m0 S FO j0 jc0 jn0 s ∧ globN s "journal_n" < jn0)
      stateRestoreTail
      (fun r t => r = none → StateRestoreLoopInv m0 S FO j0 jc0 jn0 t) :=
    Hoare.dec_fall (names := []) (by simp)
      (LocalsOnly.of_localsFree (stateRestoreLoopInv_localsFree m0 S FO j0 jc0 jn0))
      (fun s v ⟨hI, hjn_lt⟩ hev => by
        refine ⟨stateRestoreLoopInv_localsFree m0 S FO j0 jc0 jn0 s _ s.clock hI, ?_⟩
        simp only [evalAt, evalHOLExact, evalListHOLExact] at hev
        rcases hjw_lk : s.globals.lookup (ofString "journal") with _ | ⟨x1 | _ | _⟩ <;>
          rcases hjnw_lk : s.globals.lookup (ofString "journal_n") with _ | ⟨x2 | _ | _⟩
        all_goals (try (simp [hjw_lk, hjnw_lk, valueIsWord] at hev; done))
        all_goals (try (cases x2 with | word _ => simp [hjw_lk, hjnw_lk, valueIsWord, panOpHOL] at hev))
        cases x1 with
        | word jw =>
          cases x2 with
          | word jnw =>
            simp only [hjw_lk, hjnw_lk, wordOpHOL, wordOp] at hev
            change some (ValueHOL.val (HolWordLab.word (jw + (jnw * BitVec.ofNat 64 32 + 0)))) = some v at hev
            injection hev with hv; subst hv
            have hjw_nat : jw.toNat = globN s "journal" := by simp [globN, hjw_lk]
            have hjnw_nat : jnw.toNat = globN s "journal_n" := by simp [globN, hjnw_lk]
            have hjc_nz : jc0 ≠ 0 := by omega
            obtain ⟨_, hj_hi⟩ := halign.2 hjc_nz
            have hlt_cap : globN s "journal_n" < jc0 := lt_of_lt_of_le hjn_lt hjn_le_cap
            have hj_eq : globN s "journal" = j0 := hI.2.2.2.2.2.1
            have hmul_nat : (jnw * BitVec.ofNat 64 32 + 0).toNat = 32 * globN s "journal_n" := by
              have h0 : jnw * BitVec.ofNat 64 32 + 0 = jnw * BitVec.ofNat 64 32 := BitVec.add_zero _
              rw [h0, BitVec.toNat_mul, hjnw_nat, BitVec.toNat_ofNat]
              have : globN s "journal_n" * 32 < 2 ^ 64 := by omega
              omega
            have hadd_nat : (jw + (jnw * BitVec.ofNat 64 32 + 0)).toNat = j0 + 32 * globN s "journal_n" := by
              rw [BitVec.toNat_add, hjw_nat, hj_eq, hmul_nat]
              omega
            exact ⟨jw + (jnw * BitVec.ofNat 64 32 + 0),
              by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
              hadd_nat, hjn_lt⟩)
      hdec_t
  refine ⟨fun {F} s hcode hP hnt hflow => ?_⟩
  apply hdec_r.run s hcode hP hnt
  rcases hflow with h | h | h
  · exact h
  · exact absurd h (stateRestoreTail_not_cont_or_break s).1
  · exact absurd h (stateRestoreTail_not_cont_or_break s).2

end InitECandidate.Solver.Wave8GuestInv.R11Shards
