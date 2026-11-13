import InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptNullR32Close
import InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridges

/-! Wave 8 R32 (GbodyRunAttemptWitR32): `run_attempt` with the `state_init`
world contract discharged.

`GbodyRunAttemptNullR32.gbody_run_attempt_null_of` takes the `state_init`
world contract at the guard `StateInitReady` as a premise (`wsi`). The proved
contract `StrongBridges.wk_state_init_strong` has the stronger guard
`StateInitReady ∧ NodeDbSlicesBounded (nodedb)`: every value of the node
table has to be a witness slice whose byte range lies in the heap window.

This module replays the `run_attempt` chain with one more fact carried from
the entry to the `state_init` call, `WS`: every 16-byte slice of the witness
list cell of the input is a `WitnessSliceOK` slice. `nodedb_build` returns a
table whose values are slices of that list (`wk_nodedb_build_values`), so
`WS` gives the extra conjunct of the strong guard and `wsi` is not needed.

The price is the entry guard: the bound is proved at
`WithW (InputReadyNull Z)`, that is `InputReadyNull Z ∧ WS`, which is a
stronger guard than `InputReadyNull Z`. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptNullR32.Wit

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21
open InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk

variable {Z : Prop}

private theorem evalAt_load_one_word {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hg : GuestInv s) {addr : ExpHOL 64} {v : ValueHOL 64}
    (hev : evalAt s (.load .one addr) = some v) :
    ∃ a w : BitVec 64, evalAt s addr = some (.val (.word a)) ∧
      v = .val (.word w) ∧ w.toNat = memW s a.toNat ∧
      a.toNat % 8 = 0 ∧ sourceBase ≤ a.toNat ∧ a.toNat < heapEnd := by
  simp only [evalAt, evalHOLExact] at hev
  rcases ha : @evalHOLExact 64 F _ s.toExact
      (fun address => Classical.propDecidable (s.memaddrs address)) addr with _ | va
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
          have hmemW : memW s a.toNat = w.toNat := by
            unfold memW; simp [BitVec.ofNat_toNat, hmem]
          exact ⟨a, w, ha, hev.symm, hmemW.symm, hdom.1, hdom.2.1, hdom.2.2⟩
    | rStruct _ => simp at hev
    | nStruct _ => simp at hev

private theorem evalAt_add2_words {F : Type} {s : PanSemStateFiniteExact 64 F}
    {e1 e2 : ExpHOL 64} {x : BitVec 64}
    (hev : evalAt s (.op .add [e1, e2]) = some (.val (.word x))) :
    ∃ w1 w2 : BitVec 64, evalAt s e1 = some (.val (.word w1)) ∧
      evalAt s e2 = some (.val (.word w2)) ∧ x = w1 + w2 := by
  simp only [evalAt, evalHOLExact, evalListHOLExact] at hev
  rcases h1 : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | v1
  · rw [h1] at hev; simp at hev
  · rw [h1] at hev
    rcases h2 : @evalHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a)) e2 with _ | v2
    · rw [h2] at hev; simp at hev
    · rw [h2] at hev; dsimp only at hev
      rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> try simp [valueIsWord] at hev
      rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;> try simp at hev
      simp only [valueWord, wordOpHOL, wordOp, List.foldr, add_zero, Option.some.injEq] at hev
      exact ⟨w1, w2, h1, h2, hev.symm⟩

private theorem evalAt_si_add {F : Type} {s : PanSemStateFiniteExact 64 F}
    {w_si a : BitVec 64} {k : Nat}
    (hlsi : s.locals.lookup (ofString "si") = some (.val (.word w_si)))
    (ha : evalAt s (.op .add [.var .local (ofString "si"), .const (BitVec.ofNat 64 k)]) =
      some (.val (.word a)))
    (hlt : w_si.toNat + k < 2 ^ 64) : a.toNat = w_si.toNat + k := by
  obtain ⟨w1, wk, hw1, hwk, ha_eq⟩ := evalAt_add2_words ha
  have hw1_eq : w1 = w_si := by
    have hl1 : s.locals.lookup (ofString "si") = some (.val (.word w1)) := by
      simpa [evalAt, evalHOLExact] using hw1
    exact (by simpa [hlsi] using hl1 : w_si = w1).symm
  have hwk_eq : wk = BitVec.ofNat 64 k := by
    simp only [evalAt, evalHOLExact, Option.some.injEq, ValueHOL.val.injEq,
      HolWordLab.word.injEq] at hwk
    exact hwk.symm
  subst w1; subst wk
  rw [ha_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Same body as the module-private `AllBlocksGood` of `GbodyRunAttemptNullR32`. -/
def BlocksGood {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S Nd : List Nat) (bs : List Ivl) : Prop :=
  ∀ b ∈ bs, b.1 % 8 = 0 ∧ b.2 % 8 = 0 ∧
    Inside b sourceBase (globN s "heap_ptr") ∧
    WordsOK s b ∧
    IvlsDisj [b] (worldOwned s S Nd)

theorem blocksGood_nil {F : Type} (s : PanSemStateFiniteExact 64 F) (S Nd : List Nat) :
    BlocksGood s S Nd [] :=
  fun _ h => nomatch h

theorem blocksGood_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S Nd : List Nat) (bs : List Ivl) :
    BlocksGood { s with locals := locals, clock := k } S Nd bs ↔ BlocksGood s S Nd bs :=
  Iff.rfl

/-- Every 16-byte slice of the witness list cell `(memW (si + 40), 16 * memW (si + 48))`
is a witness slice with its byte range in the heap window. -/
def WitSlices {F : Type} (s : PanSemStateFiniteExact 64 F) (si : Nat) : Prop :=
  ∀ j, j < memW s (si + 48) →
    R16Shards.EvmEkFk.StorageCreateFinish.WitnessSliceOK s (memW s (si + 40) + 16 * j)

def WS {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop := WitSlices s (locN s "si")

/-- A guard together with the witness-slice fact at the local `si`. -/
def WithW (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) {F : Type}
    (s : PanSemStateFiniteExact 64 F) : Prop := P s ∧ WS s

theorem ws_setVar {F : Type} {s : PanSemStateFiniteExact 64 F} (name : MlS)
    (hne : name ≠ ofString "si") (v : ValueHOL 64) (h : WS s) :
    WS (setVarHOLFinite name v s) := by
  have hl : (setVarHOLFinite name v s).locals.lookup (ofString "si") =
      s.locals.lookup (ofString "si") := by
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
  have hloc : locN (setVarHOLFinite name v s) "si" = locN s "si" := by
    unfold locN; rw [hl]
  show WitSlices (setVarHOLFinite name v s) (locN (setVarHOLFinite name v s) "si")
  rw [hloc]; exact h

theorem witSlices_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si : Nat}
    (hIA : InputAtNullWith Z s S Nd si) (hW : WitSlices s si)
    (hg : GuestInv post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hu : ∀ c ∈ runAttemptCells s si, IvlUnhit s post c) :
    memW post (si + 40) = memW s (si + 40) ∧ memW post (si + 48) = memW s (si + 48) ∧
      WitSlices post si := by
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hIA.1.1.2.2.1
  have hsi_rc := hIA.2.1 (si, 96) (by simp [runAttemptCells])
  have hsi_in : Inside (si, 96) sourceBase (globN s "heap_ptr") :=
    inside_of_nullOrInside (by simp) hsi_rc.2.1
  have hsi_lt : si + 96 ≤ 2 ^ 64 := by unfold Inside at hsi_in; omega
  have hsi8 : si % 8 = 0 := hsi_rc.1
  have hsi_unhit := hu (si, 96) (by simp [runAttemptCells])
  have h40 : memW post (si + 40) = memW s (si + 40) :=
    memW_eq_of_ivlUnhit hsi_unhit (by omega) hsi_lt ⟨by omega, by omega⟩
  have h48 : memW post (si + 48) = memW s (si + 48) :=
    memW_eq_of_ivlUnhit hsi_unhit (by omega) hsi_lt ⟨by omega, by omega⟩
  refine ⟨h40, h48, ?_⟩
  intro j hj
  rw [h48] at hj
  rw [h40]
  have hsl := hW j hj
  have hmem : (memW s (si + 40), 16 * memW s (si + 48)) ∈ runAttemptCells s si := by
    simp [runAttemptCells]
  have hw_rc := hIA.2.1 _ hmem
  have hw_in : Inside (memW s (si + 40), 16 * memW s (si + 48)) sourceBase
      (globN s "heap_ptr") :=
    inside_of_nullOrInside (by show 16 * memW s (si + 48) ≠ 0; omega) hw_rc.2.1
  have hw_unhit := hu _ hmem
  have hw_lt : memW s (si + 40) + 16 * memW s (si + 48) ≤ 2 ^ 64 := by
    have := hw_in.2; dsimp only at this; omega
  have ha8 : memW s (si + 40) % 8 = 0 := hw_rc.1
  have hp : memW post (memW s (si + 40) + 16 * j) = memW s (memW s (si + 40) + 16 * j) :=
    memW_eq_of_ivlUnhit hw_unhit (by omega) hw_lt
      ⟨by dsimp only; omega, by dsimp only; omega⟩
  have hn : memW post (memW s (si + 40) + 16 * j + 8) =
      memW s (memW s (si + 40) + 16 * j + 8) :=
    memW_eq_of_ivlUnhit hw_unhit (by omega) hw_lt
      ⟨by dsimp only; omega, by dsimp only; omega⟩
  exact R16Shards.EvmEkFk.StorageCreateFinish.witnessSliceOK_of_preserved hsl
    (wordsOK_transfer hIA.1.1.1 hg hsl.1) hhp hp hn

theorem witSlices_setGlobal {F : Type} {s : PanSemStateFiniteExact 64 F} {si : Nat}
    (gname : MlS) (v : ValueHOL 64) (hne : ofString "heap_ptr" ≠ gname)
    (h : WitSlices s si) : WitSlices (setGlobalHOLFinite gname v s) si := by
  intro j hj
  have hsl := h j hj
  exact R16Shards.EvmEkFk.StorageCreateFinish.witnessSliceOK_of_preserved hsl hsl.1
    (le_of_eq (globN_setGlobal_ne s gname v "heap_ptr" hne).symm) rfl rfl

theorem hoare_ws_assign_global (gname : MlS) (hne : ofString "heap_ptr" ≠ gname)
    (source : ExpHOL 64) :
    Hoare WS (.assign .global gname source) (fun r t => r = none → WS t) :=
  Hoare.assign_fall (P := WS) (Q := WS)
    (fun _ v hP _ => witSlices_setGlobal gname v hne hP)

theorem hoare_withW {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {prog : ProgHOL 64}
    (h : Hoare P prog (fun r t => r = none → Q t))
    (hw : Hoare WS prog (fun r t => r = none → WS t)) :
    Hoare (WithW P) prog (fun r t => r = none → WithW Q t) :=
  ⟨fun s hc hp hnt hr => ⟨h.run s hc hp.1 hnt hr, hw.run s hc hp.2 hnt hr⟩⟩

theorem ra_entry_dec_pl_w {K : Nat} {body : ProgHOL 64}
    (hbody : TerminatingProgBoundedOn (WithW (RA_Pl Z)) body K) :
    TerminatingProgBoundedOn (WithW (InputReadyNull Z))
      (.dec (ofString "pl") .one
        (.load .one (.op .add [.var .local (ofString "si"), .const 0#64])) body) K := by
  refine dec_eval_on (P := WithW (InputReadyNull Z)) (Q := WithW (RA_Pl Z)) (ofString "pl") .one
    (.load .one (.op .add [.var .local (ofString "si"), .const 0#64])) ?_ hbody
  intro F s v hP hev
  obtain ⟨hIR, hWS⟩ := hP
  refine ⟨?_, ws_setVar _ (by decide) v hWS⟩
  obtain ⟨S, Nd, hIA⟩ := (inputAtNull_iff_with s (locN s "si")).1 hIR
  obtain ⟨a, w_pl, ha, rfl, hpl_mem, _⟩ := evalAt_load_one_word hIA.1.1.1 hev
  obtain ⟨w_si, w0, hsi_ev, hw0_ev, ha_eq⟩ := evalAt_add2_words ha
  have hlsi : s.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    simpa [evalAt, evalHOLExact] using hsi_ev
  have hw0 : w0 = 0#64 := by
    simp only [evalAt, evalHOLExact, Option.some.injEq, ValueHOL.val.injEq,
      HolWordLab.word.injEq] at hw0_ev
    exact hw0_ev.symm
  subst hw0
  have ha_si : a = w_si := by rw [ha_eq, BitVec.add_zero]
  have hloc_si : locN s "si" = w_si.toNat := by simp [locN, hlsi]
  rw [hloc_si] at hIA
  rw [ha_si] at hpl_mem
  set s1 := setVarHOLFinite (ofString "pl") (.val (.word w_pl)) s
  exact ⟨w_si, w_pl, S, Nd,
    (inputAtNullWith_with_locals s _ s.clock S Nd w_si.toNat).2 hIA,
    hpl_mem,
    by simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
         show ofString "pl" ≠ ofString "si" by decide, hlsi],
    by simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]⟩

theorem ra_dec_nh_w {K : Nat} {body : ProgHOL 64}
    (hbody : TerminatingProgBoundedOn (WithW ((RA_Nh Z) false)) body K) :
    TerminatingProgBoundedOn (WithW (RA_Vh Z))
      (.dec (ofString "nh") .one
        (.load .one (.op .add [.var .local (ofString "si"), .const 80#64])) body) K := by
  refine dec_eval_on (P := WithW (RA_Vh Z)) (Q := WithW ((RA_Nh Z) false)) (ofString "nh") .one
    (.load .one (.op .add [.var .local (ofString "si"), .const 80#64])) ?_ hbody
  intro F s v hP hev
  obtain ⟨hP, hWS⟩ := hP
  refine ⟨?_, ws_setVar _ (by decide) v hWS⟩
  obtain ⟨w_si, w_pl, a, b, S, Nd, hIA, hpl_mem, ha8, hWok, hIn, hh, hlsi, hlpl, hlvh⟩ := hP
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hIA.1.1.2.2.1
  have hsi_in := (hIA.2.1 (w_si.toNat, 96) (by simp [runAttemptCells])).2.1
  obtain ⟨addr, w_nh, ha, rfl, hnh_mem, _⟩ := evalAt_load_one_word hIA.1.1.1 hev
  obtain ⟨w1, w80, hw1, hw80, ha_eq⟩ := evalAt_add2_words ha
  have hw1_eq : w1 = w_si := by
    have hl1 : s.locals.lookup (ofString "si") = some (.val (.word w1)) := by
      simpa [evalAt, evalHOLExact] using hw1
    exact (by simpa [hlsi] using hl1 : w_si = w1).symm
  have hw80_eq : w80 = 80#64 := by
    simp only [evalAt, evalHOLExact, Option.some.injEq, ValueHOL.val.injEq,
      HolWordLab.word.injEq] at hw80
    exact hw80.symm
  subst w1; subst w80
  have ha_nat : addr.toNat = w_si.toNat + 80 := by
    rw [ha_eq, BitVec.toNat_add]
    change (w_si.toNat + 80) % 2 ^ 64 = w_si.toNat + 80
    exact Nat.mod_eq_of_lt (by unfold Inside at hsi_in; omega)
  rw [ha_nat] at hnh_mem
  rw [← hnh_mem] at hWok hIn hh
  set s1 := setVarHOLFinite (ofString "nh") (.val (.word w_nh)) s
  exact ⟨w_si, w_pl, a, b, w_nh, S, Nd,
    (inputAtNullWith_with_locals s _ s.clock S Nd w_si.toNat).2 hIA,
    hpl_mem, hnh_mem, (fun h => by cases h), ha8, hWok, hIn, hh,
    by simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
         show ofString "nh" ≠ ofString "si" by decide, hlsi],
    by simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
         show ofString "nh" ≠ ofString "pl" by decide, hlpl],
    by simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
         show ofString "nh" ≠ ofString "vh" by decide, hlvh],
    by simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]⟩

theorem hoare_ite_nh_zero_w :
    Hoare (WithW ((RA_Nh Z) false))
      (.ite (.cmp .equal (.var .local (ofString "nh")) (.const 0#64))
        (.raise (ofString "BlockErr") (.const 3#64))
        .skip)
      (fun r t => r = none → WithW ((RA_Nh Z) true) t) :=
  hoare_withW (P := (RA_Nh Z) false) (Q := (RA_Nh Z) true) hoare_ite_nh_zero
    (Hoare.ite_raise_skip (P := WS) _ _ _)

theorem ra_dec_parent_w {K : Nat} {body : ProgHOL 64}
    (hbody : TerminatingProgBoundedOn (WithW (RA_ParentPre Z)) body K) :
    TerminatingProgBoundedOn (WithW ((RA_Nh Z) true))
      (.dec (ofString "parent") .one
        (.load .one
          (.op .add
            [.rfield 0 (.var .local (ofString "vh")),
             .panop .mul
               [.op .sub [.var .local (ofString "nh"), .const 1#64],
                .const 8#64]])) body) K := by
  refine dec_eval_on (P := WithW ((RA_Nh Z) true)) (Q := WithW (RA_ParentPre Z))
    (ofString "parent") .one
    (.load .one
      (.op .add
        [.rfield 0 (.var .local (ofString "vh")),
         .panop .mul
           [.op .sub [.var .local (ofString "nh"), .const 1#64],
            .const 8#64]])) ?_ hbody
  intro F s v hP hev
  obtain ⟨hP, hWS⟩ := hP
  refine ⟨?_, ws_setVar _ (by decide) v hWS⟩
  obtain ⟨w_si, w_pl, a, b, w_nh, S, Nd, hIA, hpl_mem, hnh_mem, hpos_f,
    ha8, hWok, hIn, hh, hlsi, hlpl, hlvh, hlnh⟩ := hP
  have hpos : 0 < w_nh.toNat := hpos_f rfl
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hIA.1.1.2.2.1
  obtain ⟨addr, w_parent, haddr, rfl, hpar_mem, _⟩ := evalAt_load_one_word hIA.1.1.1 hev
  have hsub_nat : (w_nh - 1#64).toNat = w_nh.toNat - 1 := by
    have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_sub_of_le]
    · omega
    · rw [BitVec.le_def]; omega
  have hbound : a.toNat + 8 * w_nh.toNat ≤ 2 ^ 64 := by
    unfold Inside at hIn; omega
  have hmul_nat : ((w_nh - 1#64) * 8#64).toNat = 8 * (w_nh.toNat - 1) := by
    have h8 : (8#64 : BitVec 64).toNat = 8 := rfl
    rw [BitVec.toNat_mul, hsub_nat, h8]
    change ((w_nh.toNat - 1) * 8) % 2 ^ 64 = 8 * (w_nh.toNat - 1)
    rw [Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]
  have haddr_expected : evalAt s
      (.op .add
        [.rfield 0 (.var .local (ofString "vh")),
         .panop .mul
           [.op .sub [.var .local (ofString "nh"), .const 1#64],
            .const 8#64]]) =
      some (.val (.word (a + (w_nh - 1#64) * 8#64))) := by
    simp [evalAt, evalHOLExact, evalListHOLExact, hlvh, hlnh,
      valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp, BitVec.add_zero]
  rw [haddr_expected] at haddr
  injection haddr with haddr'; injection haddr' with haddr''; injection haddr'' with haddr_eq
  subst addr
  have haddr_nat : (a + (w_nh - 1#64) * 8#64).toNat = a.toNat + 8 * (w_nh.toNat - 1) := by
    rw [BitVec.toNat_add, hmul_nat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [haddr_nat] at hpar_mem
  obtain ⟨hPar_h, hIn_h, hDisj_h⟩ := hh (w_nh.toNat - 1) (by omega)
  rw [← hpar_mem] at hPar_h hIn_h hDisj_h
  have hBs : BlocksGood s S Nd [(w_parent.toNat, 248)] := by
    intro blk hblk
    rw [List.mem_singleton.1 hblk]
    exact ⟨hPar_h.1.1, show 248 % 8 = 0 by decide, hIn_h, hPar_h.1, hDisj_h⟩
  set s1 := setVarHOLFinite (ofString "parent") (.val (.word w_parent)) s
  exact ⟨w_si, w_pl, w_parent, a, b, w_nh, S, Nd,
    (inputAtNullWith_with_locals s _ s.clock S Nd w_si.toNat).2 hIA,
    (blocksGood_with_locals s _ s.clock S Nd [(w_parent.toNat, 248)]).2 hBs,
    hPar_h, hpl_mem,
    by simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
         show ofString "parent" ≠ ofString "si" by decide, hlsi],
    by simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
         show ofString "parent" ≠ ofString "pl" by decide, hlpl],
    by simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
    by simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
         show ofString "parent" ≠ ofString "vh" by decide, hlvh],
    by simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
         show ofString "parent" ≠ ofString "nh" by decide, hlnh]⟩

theorem hoare_assign_block_hashes_w :
    Hoare (WithW (RA_ParentPre Z))
      (.assign .global (ofString "block_hashes") (.rfield 1 (.var .local (ofString "vh"))))
      (fun r t => r = none → WithW (RA_ParentPre Z) t) :=
  hoare_withW (P := RA_ParentPre Z) (Q := RA_ParentPre Z) hoare_assign_block_hashes
    (hoare_ws_assign_global _ (by decide) _)

theorem hoare_assign_block_hashes_n_w :
    Hoare (WithW (RA_ParentPre Z))
      (.assign .global (ofString "block_hashes_n") (.var .local (ofString "nh")))
      (fun r t => r = none → WithW (RA_Parent Z) t) :=
  hoare_withW (P := RA_ParentPre Z) (Q := RA_Parent Z) hoare_assign_block_hashes_n
    (hoare_ws_assign_global _ (by decide) _)

theorem localsOnly_ra_parent_w : LocalsOnly ["si", "pl", "parent"] (WithW (RA_Parent Z)) := by
  intro F s locals k hl hP
  refine ⟨localsOnly_ra_parent s locals k hl hP.1, ?_⟩
  have hsi := locN_congr s locals k "si" (hl "si" (by simp))
  show WitSlices _ _
  rw [hsi]; exact hP.2

theorem decCallResumeOn_check_gas_limit_w
    (rocgl : ReadOnlyFn (ofString "check_gas_limit"))
    (arguments : List (ExpHOL 64)) :
    DecCallResumeOn (WithW (RA_Parent Z)) (WithW (RA_Parent Z))
      (ofString "gas_ok") (ofString "check_gas_limit") arguments :=
  ReadOnlyFn.resumeOn localsOnly_ra_parent_w (fun _ h => ra_parent_guestInv h.1)
    rocgl (ofString "gas_ok")
    (by intro n hn; simp at hn; rcases hn with rfl | rfl | rfl <;> decide) arguments

theorem decCallResumeOn_validate_headers_w
    (wvh : GbodyRunAttemptNullR32Close.WvhsLeaf) :
    DecCallResumeOn (WithW (RA_Pl Z)) (WithW (RA_Vh Z)) (ofString "vh")
      (ofString "validate_headers")
      [.load .one (.op .add [.var .local (ofString "si"), .const 72#64]),
       .load .one (.op .add [.var .local (ofString "si"), .const 80#64])] := by
  intro F state values body callee ret value post hcode hP hargs hl hrun
  refine ⟨decCallResumeOn_validate_headers wvh state values body callee ret value post
    hcode hP.1 hargs hl hrun, ?_⟩
  obtain ⟨⟨w_si, w_pl, S, Nd, hIA, hpl_mem, hlsi, hlpl⟩, hWS⟩ := hP
  have hAs : ArenaReady state := hIA.1.1
  have hWd : WorldOK state := ⟨hAs, S, (worldTyped_iff_with state S).2 ⟨Nd, hIA.1.2.1⟩⟩
  have hloc_si : locN state "si" = w_si.toNat := by simp [locN, hlsi]
  have hW0 : WitSlices state w_si.toNat := by rw [← hloc_si]; exact hWS
  set entry := callEntryStateHOLFinite state callee
  have hstep := FunSpec.at_lookup wvh state hcode values body callee ret hl
    (localsFree_worldOK state callee (state.clock - 1) hWd) (by rw [hrun]; simp)
  rw [hrun] at hstep; dsimp only at hstep
  have hws := hstep (Or.inl ⟨value, rfl⟩)
  have hIA_entry : (InputAtNullWith Z) entry S Nd w_si.toNat :=
    (inputAtNullWith_with_locals state callee (state.clock - 1) S Nd w_si.toNat).2 hIA
  have hW_entry : WitSlices entry w_si.toNat := hW0
  have hc1 := nullAndBlocks_bufferRegion_conditions hIA_entry (blocksGood_nil entry S Nd)
    ("keccak_pad", 136) (by decide) (by decide) (by decide)
  have hc2 := nullAndBlocks_bufferRegion_conditions hIA_entry (blocksGood_nil entry S Nd)
    ("keccak_st", 200) (by decide) (by decide) (by decide)
  obtain ⟨S', Nd', hIA_post, _, _, hu_rc, _, _, _, _⟩ :=
    worldStep_preserves_nullAndBlocks hIA_entry (blocksGood_nil entry S Nd) hws
      (fun j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        · exact hc1.1
        · exact hc2.1)
      (fun j hj k hk => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        · exact hc1.2.1 _ (by simp [bufferRegion]) k hk
        · exact hc2.2.1 _ (by simp [bufferRegion]) k hk)
      (fun c hc j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        · exact hc1.2.2.1 c hc _ (by simp [bufferRegion])
        · exact hc2.2.2.1 c hc _ (by simp [bufferRegion]))
      (fun b hb _ _ => nomatch hb)
  obtain ⟨_, _, hW_post⟩ := witSlices_unhit hIA_entry hW_entry hIA_post.1.1.1 hws.2.1 hu_rc
  refine ws_setVar _ (by decide) value ?_
  have hloc_res : locN ({ post with locals := state.locals } : PanSemStateFiniteExact 64 F)
      "si" = w_si.toNat := by simp [locN, hlsi]
  show WitSlices _ (locN ({ post with locals := state.locals } : PanSemStateFiniteExact 64 F)
    "si")
  rw [hloc_res]; exact hW_post

/-- `RA_Nodedb` with the node table kept as a block: the table is well formed, its footprint
is a good block list, and every value of it is a slice of the witness list cell. -/
def RA_NodedbW (Z : Prop) {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ w_si w_pl w_parent w_nodedb : BitVec 64, ∃ S Nd : List Nat,
    (InputAtNullWith Z) s S Nd w_si.toNat ∧
    BlocksGood s S Nd [(w_parent.toNat, 248)] ∧
    HeaderAt s w_parent.toNat ∧
    w_pl.toNat = memW s w_si.toNat ∧
    BlocksGood s S Nd (htabFootprint s w_nodedb.toNat) ∧
    WitSlices s w_si.toNat ∧
    HtabWF s w_nodedb.toNat ∧
    hdr s w_nodedb.toNat 0 = 32 ∧
    (∀ v ∈ htabValues s w_nodedb.toNat, ∃ j, j < memW s (w_si.toNat + 48) ∧
      v = memW s (w_si.toNat + 40) + 16 * j) ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "parent") = some (.val (.word w_parent)) ∧
    s.locals.lookup (ofString "nodedb") = some (.val (.word w_nodedb))

theorem ra_nodedbW_nodedb {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : RA_NodedbW Z s) : RA_Nodedb Z s := by
  obtain ⟨w_si, w_pl, w_parent, w_nodedb, S, Nd, hIA, hBs, hPar, hpl_mem, _, _, _, _, _,
    hlsi, hlpl, hlpar, hlnb⟩ := h
  exact ⟨w_si, w_pl, w_parent, w_nodedb, S, Nd, hIA, hBs, hPar, hpl_mem,
    hlsi, hlpl, hlpar, hlnb⟩

theorem ra_nodedbW_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : RA_NodedbW Z s) : GuestInv s :=
  ra_nodedb_guestInv (ra_nodedbW_nodedb h)

theorem decCallResumeOn_nodedb_first_w :
    DecCallResumeOn (WithW (RA_Parent Z)) (RA_NodedbW Z)
      (ofString "nodedb") (ofString "nodedb_build")
      [.load .one (.op .add [.var .local (ofString "si"), .const 40#64]),
       .load .one (.op .add [.var .local (ofString "si"), .const 48#64])] := by
  intro F state values body callee ret value post hcode hP hargs hl hrun
  obtain ⟨⟨w_si, w_pl, w_parent, S, Nd, hIA, hBs, hPar, hpl_mem, hlsi, hlpl, hlpar⟩, hWS⟩ := hP
  have hAs : ArenaReady state := hIA.1.1
  have hW : WorldOK state := ⟨hAs, S, (worldTyped_iff_with state S).2 ⟨Nd, hIA.1.2.1⟩⟩
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hhp_lim : globN state "heap_ptr" ≤ heapLimit := hAs.2.2.1
  have hsi_rc := hIA.2.1 (w_si.toNat, 96) (by simp [runAttemptCells])
  have hsi_in : Inside (w_si.toNat, 96) sourceBase (globN state "heap_ptr") :=
    inside_of_nullOrInside (by simp) hsi_rc.2.1
  have hsi_lt : w_si.toNat + 96 ≤ 2 ^ 64 := by unfold Inside at hsi_in; omega
  have hpar_in := (hBs (w_parent.toNat, 248) (by simp)).2.2.1
  have hloc_si : locN state "si" = w_si.toNat := by simp [locN, hlsi]
  have hW0 : WitSlices state w_si.toNat := by rw [← hloc_si]; exact hWS
  have hargs_ex := hargs
  rw [evalListHOLFinite_eq_toExact] at hargs_ex
  simp only [evalListHOLExact] at hargs_ex
  rcases he1 : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.load .one (.op .add [.var .local (ofString "si"), .const 40#64])) with _ | v1
  · rw [he1] at hargs_ex; simp at hargs_ex
  · rw [he1] at hargs_ex
    rcases he2 : @evalHOLExact 64 F _ state.toExact
        (fun a => Classical.propDecidable (state.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "si"), .const 48#64])) with _ | v2
    · rw [he2] at hargs_ex; simp at hargs_ex
    · rw [he2] at hargs_ex
      simp only [Option.some.injEq] at hargs_ex
      subst values
      obtain ⟨a1, w_p, ha1, rfl, hp_mem, _⟩ := evalAt_load_one_word hAs.1 he1
      obtain ⟨a2, w_n, ha2, rfl, hn_mem, _⟩ := evalAt_load_one_word hAs.1 he2
      have ha1_nat := evalAt_si_add hlsi ha1 (by omega)
      have ha2_nat := evalAt_si_add hlsi ha2 (by omega)
      rw [ha1_nat] at hp_mem
      rw [ha2_nat] at hn_mem
      have hpc := callee_param_two state (ofString "nodedb_build")
        (ofString "slice_arr") (ofString "n") .one .one _ _
        (by rw [hcode]; exact lookup_nodedb_build_fn)
        (.load .one (.op .add [.var .local (ofString "si"), .const 40#64]))
        (.load .one (.op .add [.var .local (ofString "si"), .const 48#64]))
        (.val (.word w_p)) (.val (.word w_n)) [.val (.word w_p), .val (.word w_n)]
        body callee ret he1 he2 hargs hl
      set entry := callEntryStateHOLFinite state callee
      have hloc_p : locN entry "slice_arr" = w_p.toNat := by
        simp [entry, locN, callEntryStateHOLFinite, hpc.2.1]
      have hloc_n : locN entry "n" = w_n.toNat := by
        simp [entry, locN, callEntryStateHOLFinite, hpc.2.2]
      have hstep := FunSpec.at_lookup R16Shards.TopGbodyWk.«wk_nodedb_build_values» state hcode
        [.val (.word w_p), .val (.word w_n)] body callee ret hl
        (localsFree_worldOK state callee (state.clock - 1) hW) (by rw [hrun]; simp)
      rw [hrun] at hstep; dsimp only at hstep
      have hws := hstep (Or.inl ⟨value, rfl⟩)
      have hIA_entry : (InputAtNullWith Z) entry S Nd w_si.toNat :=
        (inputAtNullWith_with_locals state callee (state.clock - 1) S Nd w_si.toNat).2 hIA
      have hBs_entry : BlocksGood entry S Nd [(w_parent.toNat, 248)] :=
        (blocksGood_with_locals state callee (state.clock - 1) S Nd
          [(w_parent.toNat, 248)]).2 hBs
      have hW_entry : WitSlices entry w_si.toNat := hW0
      have hc1 := nullAndBlocks_bufferRegion_conditions hIA_entry hBs_entry ("keccak_pad", 136) (by decide) (by decide) (by decide)
      have hc2 := nullAndBlocks_bufferRegion_conditions hIA_entry hBs_entry ("keccak_st", 200) (by decide) (by decide) (by decide)
      have hc3 := nullAndBlocks_bufferRegion_conditions hIA_entry hBs_entry ("mpt_hash_scratch", 40) (by decide) (by decide) (by decide)
      obtain ⟨S', Nd', hIA_post, hBs_post, _, hu_rc, hu_bs, _, _, hQ⟩ :=
        worldStep_preserves_nullAndBlocks hIA_entry hBs_entry hws
          (fun j hj => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
            rcases hj with rfl | rfl | rfl
            · exact hc1.1
            · exact hc2.1
            · exact hc3.1)
          (fun j hj k hk => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
            rcases hj with rfl | rfl | rfl
            · exact hc1.2.1 _ (by simp [bufferRegion]) k hk
            · exact hc2.2.1 _ (by simp [bufferRegion]) k hk
            · exact hc3.2.1 _ (by simp [bufferRegion]) k hk)
          (fun c hc j hj => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
            rcases hj with rfl | rfl | rfl
            · exact hc1.2.2.1 c hc _ (by simp [bufferRegion])
            · exact hc2.2.2.1 c hc _ (by simp [bufferRegion])
            · exact hc3.2.2.1 c hc _ (by simp [bufferRegion]))
          (fun b hb j hj => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
            rcases hj with rfl | rfl | rfl
            · exact hc1.2.2.2 b hb _ (by simp [bufferRegion])
            · exact hc2.2.2.2 b hb _ (by simp [bufferRegion])
            · exact hc3.2.2.2 b hb _ (by simp [bufferRegion]))
      obtain ⟨w_nodedb, rfl, hWF, hhdr32, hfp_in, hfp_ow, hvals⟩ := hQ value rfl
      rw [hloc_n, hloc_p] at hvals
      have hPar_post : HeaderAt post w_parent.toNat :=
        headerAt_of_unhit hAs.1 hIA_post.1.1.1 (by unfold Inside at hpar_in; omega)
          (hu_bs (w_parent.toNat, 248) (by simp)) hPar
      have hmem_si0 : memW post w_si.toNat = memW state w_si.toNat :=
        R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit
          (hu_rc (w_si.toNat, 96) (by simp [runAttemptCells])) hsi_rc.1
          hsi_lt ⟨by omega, by omega⟩
      obtain ⟨h40, h48, hW_post⟩ :=
        witSlices_unhit hIA_entry hW_entry hIA_post.1.1.1 hws.2.1 hu_rc
      have h40' : memW post (w_si.toNat + 40) = w_p.toNat := by
        rw [h40]; exact hp_mem.symm
      have h48' : memW post (w_si.toNat + 48) = w_n.toNat := by
        rw [h48]; exact hn_mem.symm
      have hsb_le : sourceBase ≤ globN entry "heap_ptr" := hAs.2.1
      have hBsF : BlocksGood post S' Nd' (htabFootprint post w_nodedb.toNat) := by
        intro i hi
        have hwi := (hWF.1 i hi).2
        exact ⟨hwi.1, hwi.2.1, ⟨le_trans hsb_le (hfp_in i hi).1, (hfp_in i hi).2⟩, hwi,
          fun b hb o ho => by rw [List.mem_singleton.1 hb]; exact hfp_ow i hi o ho⟩
      have hvals' : ∀ v ∈ htabValues post w_nodedb.toNat,
          ∃ j, j < memW post (w_si.toNat + 48) ∧ v = memW post (w_si.toNat + 40) + 16 * j := by
        intro v hv
        obtain ⟨j, hj, rfl⟩ := hvals v hv
        refine ⟨j, by omega, ?_⟩
        have hcell := hIA.2.1
          (memW state (w_si.toNat + 40), 16 * memW state (w_si.toNat + 48))
          (by simp [runAttemptCells])
        have hin : Inside (memW state (w_si.toNat + 40), 16 * memW state (w_si.toNat + 48))
            sourceBase (globN state "heap_ptr") :=
          inside_of_nullOrInside
            (by show 16 * memW state (w_si.toNat + 48) ≠ 0; omega) hcell.2.1
        have hin2 := hin.2
        dsimp only at hin2
        rw [h40', Nat.mod_eq_of_lt (by omega)]
      set res := setVarHOLFinite (ofString "nodedb") (.val (.word w_nodedb))
        { post with locals := state.locals }
      refine ⟨w_si, w_pl, w_parent, w_nodedb, S', Nd',
        (inputAtNullWith_with_locals post res.locals post.clock S' Nd' w_si.toNat).2 hIA_post,
        (blocksGood_with_locals post res.locals post.clock S' Nd' [(w_parent.toNat, 248)]).2
          hBs_post,
        hPar_post,
        by change w_pl.toNat = memW post w_si.toNat; omega,
        hBsF, hW_post,
        (htabWF_with_locals post res.locals post.clock w_nodedb.toNat).2 hWF,
        hhdr32, hvals',
        ?_, ?_, ?_, ?_⟩
      · simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlsi,
          show ofString "nodedb" ≠ ofString "si" by decide]
      · simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlpl,
          show ofString "nodedb" ≠ ofString "pl" by decide]
      · simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlpar,
          show ofString "nodedb" ≠ ofString "parent" by decide]
      · simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

/-- `RA_Codedb` with the node table of the local `nodedb` bounded slice by slice. -/
def RA_CodedbW (Z : Prop) {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  RA_Codedb Z s ∧ R16Shards.EvmEkFk.StorageCreateFinish.DbTableAt s (locN s "nodedb")

theorem decCallResumeOn_nodedb_codedb_w (arguments : List (ExpHOL 64)) :
    DecCallResumeOn (RA_NodedbW Z) (RA_CodedbW Z)
      (ofString "codedb") (ofString "nodedb_build") arguments := by
  intro F state values body callee ret value post hcode hP hargs hl hrun
  refine ⟨decCallResumeOn_nodedb_codedb R16Shards.TopGbodyWk.«wk_nodedb_build» arguments
    state values body callee ret value post hcode (ra_nodedbW_nodedb hP) hargs hl hrun, ?_⟩
  obtain ⟨w_si, w_pl, w_parent, w_nodedb, S, Nd, hIA, hBs, hPar, hpl_mem, hBsF, hWit, hWFn,
    hhdrn, hvals, hlsi, hlpl, hlpar, hlnb⟩ := hP
  have hAs : ArenaReady state := hIA.1.1
  have hW : WorldOK state := ⟨hAs, S, (worldTyped_iff_with state S).2 ⟨Nd, hIA.1.2.1⟩⟩
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hhp_lim : globN state "heap_ptr" ≤ heapLimit := hAs.2.2.1
  set entry := callEntryStateHOLFinite state callee
  have hstep := FunSpec.at_lookup R16Shards.TopGbodyWk.«wk_nodedb_build» state hcode values
    body callee ret hl
    (localsFree_worldOK state callee (state.clock - 1) hW) (by rw [hrun]; simp)
  rw [hrun] at hstep; dsimp only at hstep
  have hws := hstep (Or.inl ⟨value, rfl⟩)
  have hIA_entry : (InputAtNullWith Z) entry S Nd w_si.toNat :=
    (inputAtNullWith_with_locals state callee (state.clock - 1) S Nd w_si.toNat).2 hIA
  have hBs_entry : BlocksGood entry S Nd (htabFootprint state w_nodedb.toNat) :=
    (blocksGood_with_locals state callee (state.clock - 1) S Nd
      (htabFootprint state w_nodedb.toNat)).2 hBsF
  have hW_entry : WitSlices entry w_si.toNat := hWit
  have hc1 := nullAndBlocks_bufferRegion_conditions hIA_entry hBs_entry ("keccak_pad", 136) (by decide) (by decide) (by decide)
  have hc2 := nullAndBlocks_bufferRegion_conditions hIA_entry hBs_entry ("keccak_st", 200) (by decide) (by decide) (by decide)
  have hc3 := nullAndBlocks_bufferRegion_conditions hIA_entry hBs_entry ("mpt_hash_scratch", 40) (by decide) (by decide) (by decide)
  obtain ⟨S', Nd', hIA_post, _, _, hu_rc, hu_bs, _, _, _⟩ :=
    worldStep_preserves_nullAndBlocks hIA_entry hBs_entry hws
      (fun j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl
        · exact hc1.1
        · exact hc2.1
        · exact hc3.1)
      (fun j hj k hk => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl
        · exact hc1.2.1 _ (by simp [bufferRegion]) k hk
        · exact hc2.2.1 _ (by simp [bufferRegion]) k hk
        · exact hc3.2.1 _ (by simp [bufferRegion]) k hk)
      (fun c hc j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl
        · exact hc1.2.2.1 c hc _ (by simp [bufferRegion])
        · exact hc2.2.2.1 c hc _ (by simp [bufferRegion])
        · exact hc3.2.2.1 c hc _ (by simp [bufferRegion]))
      (fun b hb j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl
        · exact hc1.2.2.2 b hb _ (by simp [bufferRegion])
        · exact hc2.2.2.2 b hb _ (by simp [bufferRegion])
        · exact hc3.2.2.2 b hb _ (by simp [bufferRegion]))
  have hu_fp : ∀ i ∈ htabFootprint state w_nodedb.toNat, IvlUnhit state post i :=
    fun i hi => hu_bs i hi
  have ht_fp : (w_nodedb.toNat, 88) ∈ htabFootprint state w_nodedb.toNat := by
    simp [htabFootprint]
  have ht_blk := hBsF _ ht_fp
  have ht8 : w_nodedb.toNat % 8 = 0 := ht_blk.1
  have ht_hi : w_nodedb.toNat + 88 ≤ 2 ^ 64 := by
    have := ht_blk.2.2.1.2; dsimp only at this; omega
  obtain ⟨hhdr_eq, hfp_eq⟩ := htabFootprint_eq_of_hdr_unhit ht8 ht_hi (hu_fp _ ht_fp)
  have hval_eq := htabValues_eq_of_unhit hWFn hu_fp
  have hWF_post : HtabWF post w_nodedb.toNat :=
    htabWF_congr_unhit hAs.1 hIA_post.1.1.1 hWFn hu_fp
  obtain ⟨h40, h48, hW_post⟩ :=
    witSlices_unhit hIA_entry hW_entry hIA_post.1.1.1 hws.2.1 hu_rc
  have hDb : R16Shards.EvmEkFk.StorageCreateFinish.DbTableAt post w_nodedb.toNat := by
    refine Or.inr ⟨hWF_post, (hhdr_eq 0 (by decide)).trans hhdrn, ?_, ?_⟩
    · rw [hfp_eq]
      intro i hi
      exact ⟨(hBsF i hi).2.2.1.1, le_trans (hBsF i hi).2.2.1.2 hws.2.1⟩
    · rw [hval_eq]
      intro v hv
      obtain ⟨j, hj, rfl⟩ := hvals v hv
      have hsl := hW_post j (by rw [h48]; exact hj)
      rw [h40] at hsl
      exact hsl
  set res := setVarHOLFinite (ofString "codedb") value { post with locals := state.locals }
  have hloc : locN res "nodedb" = w_nodedb.toNat := by
    simp [res, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlnb,
      show ofString "codedb" ≠ ofString "nodedb" by decide]
  show R16Shards.EvmEkFk.StorageCreateFinish.DbTableAt res (locN res "nodedb")
  rw [hloc]
  exact R16Shards.EvmEkFk.StorageCreateFinish.dbTableAt_with_locals_clock_so hDb
    res.locals post.clock

/-- The `state_init` call from the proved strong contract `wk_state_init_strong`: the node
table conjunct of its guard is the `DbTableAt` fact of `RA_CodedbW`. -/
theorem hoare_state_init_w :
    Hoare (RA_CodedbW Z)
      (.call (some (none, none)) (ofString "state_init")
        [.var .local (ofString "nodedb"),
         .load .one (.op .add [.var .local (ofString "parent"), .const 32#64]),
         .var .local (ofString "codedb")])
      (fun r t => r = none → (RunAttemptPreScan Z) t) := by
  refine ⟨fun {F} state hcode hP _ hr => ?_⟩
  rcases hcall : evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "state_init")
        [.var .local (ofString "nodedb"),
         .load .one (.op .add [.var .local (ofString "parent"), .const 32#64]),
         .var .local (ofString "codedb")]) with ⟨cres, cpost⟩
  have hr' : cres = none := by rw [hcall] at hr; exact hr
  subst hr'
  obtain ⟨⟨w_si, w_pl, w_parent, w_nodedb, w_codedb, S, Nd, hIA, hBs, hPar, hpl_mem,
    hWF, hhdr32, hfp_sb, hfp_ow, hrc_fp, hpar_fp, hlsi, hlpl, hlpar, hlnb, hlcb⟩, hDb⟩ := hP
  have hDb_state : R16Shards.EvmEkFk.StorageCreateFinish.DbTableAt state w_nodedb.toNat := by
    have hloc_nb0 : locN state "nodedb" = w_nodedb.toNat := by simp [locN, hlnb]
    rw [← hloc_nb0]; exact hDb
  have hAs : ArenaReady state := hIA.1.1
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hhp_lim : globN state "heap_ptr" ≤ heapLimit := hAs.2.2.1
  have hsi_rc := hIA.2.1 (w_si.toNat, 96) (by simp [runAttemptCells])
  have hsi_in := hsi_rc.2.1
  have hpar_in := (hBs (w_parent.toNat, 248) (by simp)).2.2.1
  rw [evaluateHOLFiniteState_call] at hcall
  rcases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "nodedb"),
       .load .one (.op .add [.var .local (ofString "parent"), .const 32#64]),
       .var .local (ofString "codedb")] with _ | values
  · rw [hargs] at hcall; simp at hcall
  · rw [hargs] at hcall; dsimp only at hcall
    rcases hl : lookupCodeHOLFinite state.code.lookup (ofString "state_init") values
      with _ | ⟨body, callee, ret⟩
    · rw [hl] at hcall; simp at hcall
    · rw [hl] at hcall; dsimp only at hcall
      split_ifs at hcall with hz
      · simp at hcall
      · rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with ⟨bres, post⟩
        rw [hrun] at hcall
        cases bres with
        | none => simp at hcall
        | some br =>
          cases br with
          | returned v =>
            dsimp only at hcall
            split_ifs at hcall with hsh
            · obtain ⟨_, hpost_eq⟩ := Prod.mk.inj hcall
              have hargs_ex := hargs
              rw [evalListHOLFinite_eq_toExact] at hargs_ex
              simp only [evalListHOLExact] at hargs_ex
              have he1 : evalAt state (.var .local (ofString "nodedb")) =
                  some (.val (.word w_nodedb)) := by
                simpa [evalAt, evalHOLExact] using hlnb
              have he3 : evalAt state (.var .local (ofString "codedb")) =
                  some (.val (.word w_codedb)) := by
                simpa [evalAt, evalHOLExact] using hlcb
              rw [show @evalHOLExact 64 F _ state.toExact
                    (fun a => Classical.propDecidable (state.memaddrs a))
                    (.var .local (ofString "nodedb")) = some (.val (.word w_nodedb)) from he1] at hargs_ex
              rcases he2 : @evalHOLExact 64 F _ state.toExact
                  (fun a => Classical.propDecidable (state.memaddrs a))
                  (.load .one (.op .add [.var .local (ofString "parent"), .const 32#64]))
                with _ | v2
              · rw [he2] at hargs_ex; simp at hargs_ex
              · have hpc := callee_param_three state (ofString "state_init")
                  (ofString "nodedb") (ofString "state_root") (ofString "codedb")
                  .one .one .one _ _ (by rw [hcode]; exact lookup_state_init_fn)
                  (.var .local (ofString "nodedb"))
                  (.load .one (.op .add [.var .local (ofString "parent"), .const 32#64]))
                  (.var .local (ofString "codedb"))
                  (.val (.word w_nodedb)) v2 (.val (.word w_codedb))
                  values body callee ret he1 he2 he3 hargs hl
                set entry := callEntryStateHOLFinite state callee
                have hloc_cb : locN entry "codedb" = w_codedb.toNat := by
                  simp [entry, locN, callEntryStateHOLFinite, hpc.2.2]
                have hWF_entry : HtabWF entry w_codedb.toNat :=
                  (htabWF_with_locals state callee (state.clock - 1) w_codedb.toNat).2 hWF
                have hSIR : StateInitReady entry := by
                  refine ⟨localsFree_arenaReady state callee (state.clock - 1) hAs, S, Nd,
                    (worldTypedWith_with_locals state callee (state.clock - 1) S Nd).2 hIA.1.2.1,
                    Or.inr ?_⟩
                  rw [hloc_cb]
                  exact ⟨hWF_entry, hhdr32, hfp_sb, hfp_ow⟩
                have hloc_nb : locN entry "nodedb" = w_nodedb.toNat := by
                  simp [entry, locN, callEntryStateHOLFinite, hpc.1]
                have hDbE : R16Shards.EvmEkFk.StorageCreateFinish.DbTableAt entry
                    (locN entry "nodedb") := by
                  rw [hloc_nb]
                  exact R16Shards.EvmEkFk.StorageCreateFinish.dbTableAt_with_locals_clock_so
                    hDb_state callee (state.clock - 1)
                have hstep := FunSpec.at_lookup StrongBridges.wk_state_init_strong state hcode
                  values body callee ret hl
                  (show StateInitReady entry ∧
                    R16Shards.EvmEkFk.StorageCreateFinish.DbTableAt entry (locN entry "nodedb")
                    from ⟨hSIR, hDbE⟩) (by rw [hrun]; simp)
                rw [hrun] at hstep; dsimp only at hstep
                have hws := hstep ⟨v, rfl⟩
                have hIA_entry : (InputAtNullWith Z) entry S Nd w_si.toNat :=
                  (inputAtNullWith_with_locals state callee (state.clock - 1) S Nd w_si.toNat).2 hIA
                have hBs_entry : BlocksGood entry S Nd [(w_parent.toNat, 248)] :=
                  (blocksGood_with_locals state callee (state.clock - 1) S Nd [(w_parent.toNat, 248)]).2 hBs
                have hIA_cons : (InputAtNullWith Z) entry (w_codedb.toNat :: S) Nd w_si.toNat :=
                  inputAtNullWith_cons_fresh hIA_entry hWF_entry hfp_sb hfp_ow hrc_fp
                have hBs_cons : BlocksGood entry (w_codedb.toNat :: S) Nd [(w_parent.toNat, 248)] :=
                  allBlocksGood_cons_fresh hBs_entry hpar_fp
                obtain ⟨S', Nd', hIA_post, hBs_post, _, hu_rc, hu_bs, _, _, hQ⟩ :=
                  worldStepIn_preserves_nullAndBlocks hIA_cons hBs_cons hws
                    (fun t ht => by
                      split_ifs at ht with hz_cb
                      · nomatch ht
                      · rw [List.mem_singleton.1 ht, hloc_cb]
                        exact List.mem_cons_self)
                    (fun _ hj => nomatch hj)
                    (fun _ hj => nomatch hj)
                    (fun _ _ _ hj => nomatch hj)
                    (fun _ _ _ hj => nomatch hj)
                have hjc_post : globN post "journal_cap" ≠ 0 := hQ v rfl
                have hPar_post : HeaderAt post w_parent.toNat :=
                  headerAt_of_unhit hAs.1 hIA_post.1.1.1 (by unfold Inside at hpar_in; omega)
                    (hu_bs (w_parent.toNat, 248) (by simp)) hPar
                have hmem_si0 : memW post w_si.toNat = memW state w_si.toNat :=
                  R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit
                    (hu_rc (w_si.toNat, 96) (by simp [runAttemptCells])) hsi_rc.1
                    (by unfold Inside at hsi_in; omega) ⟨by omega, by omega⟩
                have hRes : (RunAttemptPreScan Z) { post with locals := state.locals } :=
                  ⟨w_si, w_pl, w_parent, S', Nd',
                    (inputAtNullWith_with_locals post state.locals post.clock S' Nd' w_si.toNat).2 hIA_post,
                    (blocksGood_with_locals post state.locals post.clock S' Nd' [(w_parent.toNat, 248)]).2 hBs_post,
                    hPar_post,
                    by change w_pl.toNat = memW post w_si.toNat; omega,
                    hjc_post, hlsi, hlpl, hlpar⟩
                exact hpost_eq ▸ hRes
            · simp at hcall
          | _ => simp [emptyLocalsHOLFinite] at hcall

/-- The `run_attempt` body is bounded at the entry guard `WithW (InputReadyNull Z)`. The
`nodedb_build` and `state_init` world facts are the proved ones (`wk_nodedb_build_values`,
`wk_nodedb_build`, `StrongBridges.wk_state_init_strong`), so neither a `nodedb_build` world
premise nor the `state_init` world premise is taken. -/
theorem runAttemptFullProg_bounded_wit
    (hal : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (hcgl : TerminatingFunBoundedOn GuestInv (ofString "check_gas_limit") K.«check_gas_limit»)
    (hexec : TerminatingFunBoundedOn (BlockReadyExecAttemptNull Z)
      (ofString "execute_block") K.«execute_block»)
    (hhh : TerminatingFunBoundedOn GuestInv (ofString "header_hash") K.«header_hash»)
    (hvvh : TerminatingFunBoundedOn GuestInv
      (ofString "is_valid_versioned_hashes") K.«is_valid_versioned_hashes»)
    (hmeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq»)
    (hmz : TerminatingFunBoundedOn GuestInv (ofString "memzero") K.«memzero»)
    (hnb : TerminatingFunBoundedOn GuestInv (ofString "nodedb_build") K.«nodedb_build»)
    (hph : TerminatingFunBoundedOn (InputReadyNwdZ Z) (ofString "payload_header") K.«payload_header»)
    (hsi : TerminatingFunBoundedOn WorldOK (ofString "state_init") K.«state_init»)
    (hvh : TerminatingFunBoundedOn GuestInv (ofString "validate_header") K.«validate_header»)
    (hvhs : TerminatingFunBoundedOn GuestInv (ofString "validate_headers") K.«validate_headers»)
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc"))
    (rocgl : ReadOnlyFn (ofString "check_gas_limit"))
    (whh : WorldKeeps (fun s => WorldOK s ∧ HeaderOKStrongLocal s)
      (fun s => [(locN s "out", 32),
        (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "header_hash"))
    (wvvh : WorldKeeps WorldOK (fun _ => []) ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "is_valid_versioned_hashes"))
    (romeq : ReadOnlyFn (ofString "memeq"))
    (wmz : WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")]) []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "memzero"))
    (wph : WorldKeeps (InputReadyZ Z)
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
        (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16),
        (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
        (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr", "wd_rlp_slices"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetHeader (ofString "payload_header"))
    (wvh : WorldKeeps
      R16Shards.TopGbodyWk.ValidateHeaderReady
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "validate_header"))
    (wvhs : WorldKeeps WorldOK
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetHeadersStrong (ofString "validate_headers")) :
    TerminatingProgBoundedOn (WithW (InputReadyNull Z)) runAttemptFullProg K.«run_attempt» := by
  have hscan : TerminatingProgBoundedOn (RunAttemptPreScan Z) runAttemptScanBlockProg _ :=
    runAttemptScanBlock_bounded hal hexec hhh hvvh hmeq hmz hph hvh
      wal rtal whh wvvh romeq wmz wph wvh
  have hskip_scan : TerminatingProgBoundedOn (RunAttemptPreScan Z)
      (.seq .skip runAttemptScanBlockProg) _ :=
    TerminatingProgBoundedOn.seq_hoare (P := (RunAttemptPreScan Z))
      (TerminatingProgBoundedOn.of_clock (P := (RunAttemptPreScan Z)) (fun s => clock_skip s))
      (Hoare.skip fun _ h _ => h)
      hscan
  set siArgs : List (ExpHOL 64) :=
    [.var .local (ofString "nodedb"),
     .load .one (.op .add [.var .local (ofString "parent"), .const 32#64]),
     .var .local (ofString "codedb")]
  have hsi_seq : TerminatingProgBoundedOn (RA_CodedbW Z) _ _ :=
    TerminatingProgBoundedOn.seq_hoare_trans (P := (RA_CodedbW Z)) (Q := (RunAttemptPreScan Z))
      (TerminatingProgBoundedOn.call_on hsi none siArgs
        (callEntryOn_of_imp localsFree_worldOK (fun _ h => ra_codedb_worldOK h.1) _ siArgs))
      hoare_state_init_w
      hskip_scan
  set cbArgs : List (ExpHOL 64) :=
    [.load .one (.op .add [.var .local (ofString "si"), .const 56#64]),
     .load .one (.op .add [.var .local (ofString "si"), .const 64#64])]
  have hcb_call : TerminatingProgBoundedOn (RA_NodedbW Z) _ _ :=
    TerminatingProgBoundedOn.decCall_on hnb (ofString "codedb") .one cbArgs
      (callEntryOn_of_imp localsFree_guestInv (fun _ h => ra_nodedbW_guestInv h) _ cbArgs)
      (decCallResumeOn_nodedb_codedb_w cbArgs)
      hsi_seq
  set nbArgs : List (ExpHOL 64) :=
    [.load .one (.op .add [.var .local (ofString "si"), .const 40#64]),
     .load .one (.op .add [.var .local (ofString "si"), .const 48#64])]
  have hnb_call : TerminatingProgBoundedOn (WithW (RA_Parent Z)) _ _ :=
    TerminatingProgBoundedOn.decCall_on hnb (ofString "nodedb") .one nbArgs
      (callEntryOn_of_imp localsFree_guestInv (fun _ h => ra_parent_guestInv h.1) _ nbArgs)
      decCallResumeOn_nodedb_first_w
      hcb_call
  have hite_gok : TerminatingProgBoundedOn (WithW (RA_Parent Z))
      (.ite (.cmp .equal (.var .local (ofString "gas_ok")) (.const 0#64))
        (.raise (ofString "BlockErr") (.const 10#64))
        .skip)
      (max 0 0) :=
    TerminatingProgBoundedOn.ite_on
      (TerminatingProgBoundedOn.of_clock (P := (WithW (RA_Parent Z))) (fun s => clock_raise s _ _))
      (TerminatingProgBoundedOn.of_clock (P := (WithW (RA_Parent Z))) (fun s => clock_skip s))
  have hafter_cgl : TerminatingProgBoundedOn (WithW (RA_Parent Z)) _ _ :=
    TerminatingProgBoundedOn.seq_hoare (P := (WithW (RA_Parent Z)))
      hite_gok (Hoare.ite_raise_skip _ _ _) hnb_call
  set cglArgs : List (ExpHOL 64) :=
    [.load .one (.op .add [.var .local (ofString "pl"), .const 88#64]),
     .load .one (.op .add [.var .local (ofString "parent"), .const 104#64])]
  have hcgl_call : TerminatingProgBoundedOn (WithW (RA_Parent Z)) _ _ :=
    TerminatingProgBoundedOn.decCall_on hcgl (ofString "gas_ok") .one cglArgs
      (callEntryOn_of_imp localsFree_guestInv (fun _ h => ra_parent_guestInv h.1) _ cglArgs)
      (decCallResumeOn_check_gas_limit_w rocgl cglArgs)
      hafter_cgl
  have hite_gas22 : TerminatingProgBoundedOn (WithW (RA_Parent Z))
      (.ite
        (.cmp .lower
          (.load .one (.op .add [.var .local (ofString "pl"), .const 88#64]))
          (.load .one (.op .add [.var .local (ofString "pl"), .const 96#64])))
        (.raise (ofString "BlockErr") (.const 22#64))
        .skip)
      (max 0 0) :=
    TerminatingProgBoundedOn.ite_on
      (TerminatingProgBoundedOn.of_clock (P := (WithW (RA_Parent Z))) (fun s => clock_raise s _ _))
      (TerminatingProgBoundedOn.of_clock (P := (WithW (RA_Parent Z))) (fun s => clock_skip s))
  have hgas22_seq : TerminatingProgBoundedOn (WithW (RA_Parent Z)) _ _ :=
    TerminatingProgBoundedOn.seq_hoare (P := (WithW (RA_Parent Z)))
      hite_gas22 (Hoare.ite_raise_skip _ _ _) hcgl_call
  have hskip_gas : TerminatingProgBoundedOn (WithW (RA_Parent Z)) _ _ :=
    TerminatingProgBoundedOn.seq_hoare (P := (WithW (RA_Parent Z)))
      (TerminatingProgBoundedOn.of_clock (P := (WithW (RA_Parent Z))) (fun s => clock_skip s))
      (Hoare.skip fun _ h _ => h)
      hgas22_seq
  have hbhn_seq : TerminatingProgBoundedOn (WithW (RA_ParentPre Z)) _ _ :=
    TerminatingProgBoundedOn.seq_hoare_trans (P := (WithW (RA_ParentPre Z))) (Q := (WithW (RA_Parent Z)))
      (TerminatingProgBoundedOn.of_clock (P := (WithW (RA_ParentPre Z))) (fun s => clock_assign s _ _ _))
      hoare_assign_block_hashes_n_w
      hskip_gas
  have hbh_seq : TerminatingProgBoundedOn (WithW (RA_ParentPre Z)) _ _ :=
    TerminatingProgBoundedOn.seq_hoare (P := (WithW (RA_ParentPre Z)))
      (TerminatingProgBoundedOn.of_clock (P := (WithW (RA_ParentPre Z))) (fun s => clock_assign s _ _ _))
      hoare_assign_block_hashes_w
      hbhn_seq
  have hpar_dec : TerminatingProgBoundedOn (WithW ((RA_Nh Z) true)) _ _ :=
    ra_dec_parent_w hbh_seq
  have hite_nh0 : TerminatingProgBoundedOn (WithW ((RA_Nh Z) false))
      (.ite (.cmp .equal (.var .local (ofString "nh")) (.const 0#64))
        (.raise (ofString "BlockErr") (.const 3#64))
        .skip)
      (max 0 0) :=
    TerminatingProgBoundedOn.ite_on
      (TerminatingProgBoundedOn.of_clock (P := WithW ((RA_Nh Z) false)) (fun s => clock_raise s _ _))
      (TerminatingProgBoundedOn.of_clock (P := WithW ((RA_Nh Z) false)) (fun s => clock_skip s))
  have hnh0_seq : TerminatingProgBoundedOn (WithW ((RA_Nh Z) false)) _ _ :=
    TerminatingProgBoundedOn.seq_hoare_trans (P := WithW ((RA_Nh Z) false)) (Q := WithW ((RA_Nh Z) true))
      hite_nh0 hoare_ite_nh_zero_w hpar_dec
  have hnh_dec : TerminatingProgBoundedOn (WithW (RA_Vh Z)) _ _ :=
    ra_dec_nh_w hnh0_seq
  set vhsArgs : List (ExpHOL 64) :=
    [.load .one (.op .add [.var .local (ofString "si"), .const 72#64]),
     .load .one (.op .add [.var .local (ofString "si"), .const 80#64])]
  have hvhs_call : TerminatingProgBoundedOn (WithW (RA_Pl Z)) _ _ :=
    TerminatingProgBoundedOn.decCall_on hvhs (ofString "vh") (.comb [.one, .one]) vhsArgs
      (callEntryOn_of_imp localsFree_guestInv (fun _ h => ra_pl_guestInv h.1) _ vhsArgs)
      (decCallResumeOn_validate_headers_w wvhs)
      hnh_dec
  have hskip_vhs : TerminatingProgBoundedOn (WithW (RA_Pl Z)) _ _ :=
    TerminatingProgBoundedOn.seq_hoare (P := (WithW (RA_Pl Z)))
      (TerminatingProgBoundedOn.of_clock (P := (WithW (RA_Pl Z))) (fun s => clock_skip s))
      (Hoare.skip fun _ h _ => h)
      hvhs_call
  have hall : TerminatingProgBoundedOn (WithW (InputReadyNull Z)) runAttemptFullProg _ :=
    ra_entry_dec_pl_w hskip_vhs
  intro F s hc hp
  exact TerminatingRunBounded.weaken (hall s hc hp) (by unfold K.«run_attempt»; omega)

/-- `run_attempt` is bounded at `WithW (InputReadyNull Z)`, with no `state_init` world premise. -/
theorem gbody_run_attempt_wit_of
    (hal : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (hcgl : TerminatingFunBoundedOn GuestInv (ofString "check_gas_limit") K.«check_gas_limit»)
    (hexec : TerminatingFunBoundedOn (BlockReadyExecAttemptNull Z)
      (ofString "execute_block") K.«execute_block»)
    (hhh : TerminatingFunBoundedOn GuestInv (ofString "header_hash") K.«header_hash»)
    (hvvh : TerminatingFunBoundedOn GuestInv
      (ofString "is_valid_versioned_hashes") K.«is_valid_versioned_hashes»)
    (hmeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq»)
    (hmz : TerminatingFunBoundedOn GuestInv (ofString "memzero") K.«memzero»)
    (hnb : TerminatingFunBoundedOn GuestInv (ofString "nodedb_build") K.«nodedb_build»)
    (hph : TerminatingFunBoundedOn (InputReadyNwdZ Z) (ofString "payload_header") K.«payload_header»)
    (hsi : TerminatingFunBoundedOn WorldOK (ofString "state_init") K.«state_init»)
    (hvh : TerminatingFunBoundedOn GuestInv (ofString "validate_header") K.«validate_header»)
    (hvhs : TerminatingFunBoundedOn GuestInv (ofString "validate_headers") K.«validate_headers»)
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc"))
    (rocgl : ReadOnlyFn (ofString "check_gas_limit"))
    (whh : WorldKeeps (fun s => WorldOK s ∧ HeaderOKStrongLocal s)
      (fun s => [(locN s "out", 32),
        (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "header_hash"))
    (wvvh : WorldKeeps WorldOK (fun _ => []) ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "is_valid_versioned_hashes"))
    (romeq : ReadOnlyFn (ofString "memeq"))
    (wmz : WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")]) []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "memzero"))
    (wph : WorldKeeps (InputReadyZ Z)
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
        (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16),
        (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
        (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr", "wd_rlp_slices"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetHeader (ofString "payload_header"))
    (wvh : WorldKeeps
      R16Shards.TopGbodyWk.ValidateHeaderReady
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "validate_header"))
    (wvhs : WorldKeeps WorldOK
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetHeadersStrong (ofString "validate_headers")) :
    TerminatingFunBoundedOn (WithW (InputReadyNull Z)) (ofString "run_attempt") K.«run_attempt» := by
  refine ⟨(sourceFunctionEntry Guest.Software.guestFn_run_attempt).2.1,
    (sourceFunctionEntry Guest.Software.guestFn_run_attempt).2.2.1,
    (sourceFunctionEntry Guest.Software.guestFn_run_attempt).2.2.2,
    R10Shards.Fast_GbodyC17ToC21.lookup_run_attempt_fn, ?_⟩
  rw [sourceFnBody_run_attempt_eq]
  exact runAttemptFullProg_bounded_wit
    hal hcgl hexec hhh hvvh hmeq hmz hnb hph hsi hvh hvhs
    wal rtal rocgl whh wvvh romeq wmz wph wvh wvhs

/-- `run_attempt` at `WithW (InputReadyNull Z)` from the four leaves `hexec`, `hph`, `wph`,
`wvhs`; every other callee fact is the proved one. Compared with
`GbodyRunAttemptNullR32Close.gbody_run_attempt_null_r32` the `wsi` leaf is gone and the guard
carries the extra conjunct `WS`. -/
theorem gbody_run_attempt_wit_r32
    (hexec : TerminatingFunBoundedOn (BlockReadyExecAttemptNull Z)
      (ofString "execute_block") K.«execute_block»)
    (hph : TerminatingFunBoundedOn (InputReadyNwdZ Z) (ofString "payload_header")
      K.«payload_header»)
    (wph : GbodyRunAttemptNullR32Close.WphAt (InputReadyZ Z))
    (wvhs : GbodyRunAttemptNullR32Close.WvhsLeaf) :
    TerminatingFunBoundedOn (WithW (InputReadyNull Z)) (ofString "run_attempt")
      K.«run_attempt» :=
  gbody_run_attempt_wit_of
    Merged.fb_alloc
    R11Adapters.«fb_check_gas_limit»
    hexec
    R11Adapters.«fb_header_hash»
    R11Adapters.«fb_is_valid_versioned_hashes»
    Merged.fb_memeq
    Merged.fb_memzero
    R11Adapters.«fb_nodedb_build»
    hph
    (R13Shards.gbody_state_init Merged.fb_alloc
      ChainHandlersR31C1.g_decode_witness_to_mpt_r31 Merged.fb_htab_new
      R13Shards.WkShard01.«wk_alloc» R13Shards.WkShard01.«rt_alloc»)
    R11Adapters.«fb_validate_header»
    R11Adapters.«fb_validate_headers»
    R13Shards.WkShard01.«wk_alloc»
    R13Shards.WkShard01.«rt_alloc»
    R10Ports.ro_check_gas_limit
    R16Shards.HeaderHashRecover.«wk_header_hash_inside»
    R16Shards.«wk_is_valid_versioned_hashes»
    InitECandidate.Solver.Wave8Contracts.M15.«ro_memeq»
    InitECandidate.Solver.Wave8Contracts.M08.«wk_memzero»
    wph
    R16Shards.TopGbodyWk.«wk_validate_header_strong»
    wvhs


end InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptNullR32.Wit
