import InitECandidate.Solver.Wave8GuestInv.ContractParts.C18
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21
import InitECandidate.Solver.Wave8GuestInv.R13Shards.GbodyPayloadStateInitShard

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
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
open InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21
open InitECandidate.Solver.Wave8GuestInv.R13PayloadStateInit

/-! ## 1. `gbody_process_unchecked_system_transaction_strong` -/

/-- `WordSysTxLocals`, `SysTxReadyStrong`, `sysTxReadyStrong_worldOK` and `callEntryOn_sysTxReadyStrong`
now live in `ContractParts/C17.lean` (wave8 cutover rehearsal); this file keeps the `SysTxEntry` bridge. -/

theorem sysTxReadyStrong_sysTxEntry {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : SysTxReadyStrong s) : SysTxEntry s := by
  obtain ⟨hW, ht, hd, hdn⟩ := h
  have hgw := hW.1.2.2.2.2.2.2.2.2.2
  exact ⟨hW, ht, hd, hdn, hgw "vm_system_address" (by decide), hgw "be" (by decide)⟩

theorem localsOnly_sysTxReadyStrong : LocalsOnly ["target", "data", "data_n"] SysTxReadyStrong := by
  intro F s locals k hl ⟨hW, ht, hd, hdn⟩
  refine ⟨localsFree_worldOK s locals k hW, ?_, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := ht; exact ⟨w, (hl "target" (by simp)).trans hw⟩
  · obtain ⟨w, hw⟩ := hd; exact ⟨w, (hl "data" (by simp)).trans hw⟩
  · obtain ⟨w, hw⟩ := hdn; exact ⟨w, (hl "data_n" (by simp)).trans hw⟩

/-- With the ContractParts guard now `SysTxReadyStrong`, the strong statement *is*
`GBody.«process_unchecked_system_transaction»` from `ContractParts/C17.lean`. -/
abbrev GBody.«process_unchecked_system_transaction_strong» : Prop :=
  Wave8GuestInv.GBody.«process_unchecked_system_transaction»

theorem gbody_process_unchecked_system_transaction_strong :
    Wave8GuestInv.GBody.«process_unchecked_system_transaction» := by
  intro hal hext hfmr hhn hitb hmc hmn hpmc hsr hsf hte wext hnspec wmn rtmn wpmc wsf wte rtte
  refine ⟨_, _, _, R10Shards.Fast_GbodyC17ToC21.lookup_process_unchecked_system_transaction, ?_⟩
  intro F state hcode hP
  exact bounded_process_unchecked_system_transaction_wordArgs
    hal hext hfmr hhn hitb hmc hmn hpmc hsr hsf hte
    wext hnspec wmn rtmn (WorldKeepsIn.mono_ret wpmc (fun _ _ _ _ _ h => h.1)) wsf wte rtte
    state hcode (sysTxReadyStrong_sysTxEntry hP)

namespace ExecBlock

def inputRegions {F : Type} (s : PanSemStateFiniteExact 64 F) (si hdr : Nat) : List Ivl :=
  [(si, 96), (memW s si, 136), (memW s (si + 32), 80),
   (memW s (memW s si + 32), 16 * memW s (memW s si + 40)),
   (hdr, 248), (globN s "wd_rlp_slices", 16 * memW s (memW s si + 56))]

def DecodeTxReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => locN s "len" < 2 ^ 32 ∧
    locN s "p" + locN s "len" ≤ 2 ^ 64 ∧
    IvlsDisj [(locN s "p", locN s "len")]
      [(globN s "heap_ptr", scratchEnd - globN s "heap_ptr")]

def BuildMptIndexedReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧
    (∀ name ∈ (["slice_arr", "n", "out"] : List String),
      ∃ w : BitVec 64, s.locals.lookup (ofString name) = some (.val (.word w))) ∧
    locN s "n" < 2 ^ 32 ∧
    Inside (locN s "slice_arr", 16 * locN s "n") sourceBase (globN s "heap_ptr") ∧
    WordsOK s (locN s "slice_arr", 16 * locN s "n") ∧
    IvlsDisj [(locN s "slice_arr", 16 * locN s "n")]
      ([("mpt_hash_scratch", 40), ("mpt_key_scratch", 16),
        ("keccak_pad", 136), ("keccak_st", 200)].map (bufferRegion s)) ∧
    ∀ i, i < locN s "n" → memW s (locN s "slice_arr" + 16 * i + 8) < 2 ^ 40

def EntryAt {F : Type} (s : PanSemStateFiniteExact 64 F) (si hdr : Nat) : Prop :=
  globN s "journal_cap" ≠ 0 ∧
  ∃ S Nd, WorldTypedWith s S Nd ∧
    (∀ c ∈ inputRegions s si hdr,
      c.1 % 8 = 0 ∧ Inside c sourceBase (globN s "heap_ptr") ∧ WordsOK s c) ∧
    IvlsDisj (inputRegions s si hdr) (worldOwned s S Nd) ∧
    (∀ i, i < memW s (memW s si + 40) →
      let p := memW s (memW s (memW s si + 32) + 16 * i)
      let n := memW s (memW s (memW s si + 32) + 16 * i + 8)
      p + n ≤ globN s "heap_ptr") ∧
    memW s (memW s si + 56) < 2 ^ 32 ∧
    (∀ i, i < memW s (memW s si + 56) →
      memW s (globN s "wd_rlp_slices" + 16 * i + 8) < 2 ^ 40) ∧
    (globN s "block_hashes_n" ≠ 0 →
      Inside (globN s "block_hashes", 32 * globN s "block_hashes_n")
        sourceBase (globN s "heap_ptr") ∧
      WordsOK s (globN s "block_hashes", 32 * globN s "block_hashes_n") ∧
      IvlsDisj [(globN s "block_hashes", 32 * globN s "block_hashes_n")]
        (worldOwned s S Nd))

theorem entryAt_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k si hdr : Nat) :
    EntryAt {s with locals := locals, clock := k} si hdr ↔ EntryAt s si hdr := by
  simp only [EntryAt, WorldTypedWith, tablesTyped_with_locals]
  exact Iff.rfl

theorem count_le_of_inside {F : Type} {s : PanSemStateFiniteExact 64 F} {p n : Nat}
    (hA : ArenaReady s)
    (hin : Inside (p, 16 * n) sourceBase (globN s "heap_ptr")) :
    n ≤ 1944059872 := by
  have hheap := hA.2.2.1
  have hspace : heapLimit < sourceBase + 16 * 1944059872 := by decide
  unfold Inside at hin
  dsimp only at hin
  omega

def boundedCounterRank (counter : MlS) (M : Nat) {F : Type}
    (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup counter with
  | some (.val (.word w)) => M - w.toNat
  | _ => 0

theorem while_signed_up_bounded_on
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (c b : MlS) (M : Nat) (hM : M < 2 ^ 63) {body : ProgHOL 64} {B : Nat}
    (hdec : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → P (decClockHOLFinite s))
    (hsmall : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s →
      ∀ wc wb : BitVec 64,
        s.locals.lookup c = some (.val (.word wc)) →
        s.locals.lookup b = some (.val (.word wb)) →
        wc.toNat < 2 ^ 63 ∧ wb.toNat ≤ M)
    (hbody : TerminatingProgBoundedOn P body B)
    (hpres : Hoare (fun s => P s ∧ CondTrue (.cmp .less (.var .local c) (.var .local b)) s)
      body (fun r t => r = none → P t))
    (hncb : noContBreak body = true)
    (hstepC : StepsCounter c body) :
    TerminatingProgBoundedOn P (.while (.cmp .less (.var .local c) (.var .local b)) body)
      ((M + 1) * (B + 1)) := by
  refine TerminatingProgBoundedOn.while_rank (boundedCounterRank c M) hdec hbody ?_ ?_
  · intro F s _ _ _
    unfold boundedCounterRank
    split <;> omega
  · intro F s hcode hPs hact hflow
    have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none := by
      rcases hflow with h | h
      · exact h
      · exact absurd h (noContBreak_sound body hncb (decClockHOLFinite s)).1
    have hct : CondTrue (.cmp .less (.var .local c) (.var .local b)) (decClockHOLFinite s) := by
      obtain ⟨w, hw, hwnz⟩ := loopActive_decClock hact
      refine ⟨w, ?_, hwnz⟩
      rw [← evalHOLFinite_eq_toExact]
      exact hw
    have hPpost := hpres.run (decClockHOLFinite s) hcode ⟨hdec s hPs, hct⟩
      (by rw [hnone]; simp) hnone
    obtain ⟨wc, wb, hlc, hlb, hslt⟩ := loopActive_cmp_less_locals hact
    obtain ⟨hcsmall, hbsmall⟩ := hsmall s hPs wc wb hlc hlb
    have hlt : wc.toNat < wb.toNat := by
      simp only [BitVec.toInt_eq_msb_cond, BitVec.msb_eq_decide] at hslt
      simp only [show ¬ wc.toNat ≥ 2 ^ (64 - 1) by omega,
        show ¬ wb.toNat ≥ 2 ^ (64 - 1) by omega, decide_false, Bool.false_eq_true,
        ↓reduceIte] at hslt
      omega
    have hnext : (wc + 1#64).toNat = wc.toNat + 1 := by
      rw [BitVec.toNat_add]
      exact Nat.mod_eq_of_lt (by change wc.toNat + 1 < 2 ^ 64; omega)
    have hlu := hstepC (decClockHOLFinite s) wc hlc hnone
    refine ⟨hPpost, ?_⟩
    simp only [boundedCounterRank, hlu, hlc, hnext]
    omega

def TrackedBlocks {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S Nd : List Nat) (bs : List Ivl) : Prop :=
  ∀ b ∈ bs, b.1 % 8 = 0 ∧ b.2 % 8 = 0 ∧
    Inside b sourceBase (globN s "heap_ptr") ∧ WordsOK s b ∧
    (∀ o ∈ worldOwned s S Nd, Disj b o)

theorem trackedBlocks_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (S Nd : List Nat) (bs : List Ivl) :
    TrackedBlocks {s with locals := locals, clock := k} S Nd bs ↔
      TrackedBlocks s S Nd bs := Iff.rfl

theorem trackedBlocks_worldStep
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {S Nd : List Nat} {bs : List Ivl}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd)
    (hbs : TrackedBlocks s S Nd bs) (hstep : WorldStep R gw keep Q s r post)
    (hRzero : ∀ j ∈ R s, j.2 = 0 → j.1 % 8 = 0)
    (hRtyped : IvlsDisj (R s) (worldTypedIvls s S Nd))
    (hRbs : IvlsDisj bs (R s)) :
    ∃ S' Nd', WorldTypedWith post S' Nd' ∧ TrackedBlocks post S' Nd' bs ∧
      (∀ b ∈ bs, IvlUnhit s post b) ∧ Q s r post S' Nd' := by
  obtain ⟨S', Nd', _, hW', hg, hfr, hQ⟩ := hstep.2.2.2.2 S Nd hW hRtyped
  have hsurv : ∀ b ∈ bs,
      Inside b sourceBase (globN post "heap_ptr") ∧
      (∀ o ∈ worldOwned post S' Nd', Disj b o) ∧ IvlUnhit s post b := by
    intro b hb
    obtain ⟨hb1, hb2, hin, _, hdisj⟩ := hbs b hb
    exact heap_ivl_survives_step hA.2 hstep.2.1 hg hfr
      (worldOwned_zero_aligned hW) hRzero hb1 hb2 hin hdisj
      (fun j hj => hRbs b hb j hj)
  refine ⟨S', Nd', hW', ?_, fun b hb => (hsurv b hb).2.2, hQ⟩
  intro b hb
  obtain ⟨hb1, hb2, _, hw, _⟩ := hbs b hb
  exact ⟨hb1, hb2, (hsurv b hb).1,
    wordsOK_transfer hA.1 hstep.1.1 hw, (hsurv b hb).2.1⟩

theorem trackedBlocks_fresh {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {p n : Nat}
    (hA : ArenaReady s) (_hAp : ArenaReady post)
    (_hW : WorldTypedWith post S Nd) (hf : FreshBlock s post p n)
    (hd : IvlsDisj [(p, (n + 7) / 8 * 8)] (worldOwned post S Nd)) :
    TrackedBlocks post S Nd [(p, (n + 7) / 8 * 8)] := by
  intro b hb
  have heq := List.mem_singleton.mp hb
  subst b
  exact ⟨hf.1, by omega, ⟨le_trans hA.2.1 hf.2.1.1, hf.2.1.2⟩,
    hf.2.2, fun o ho => hd _ (by simp) o ho⟩

theorem wordsOK_of_inside_heap {F : Type} {s : PanSemStateFiniteExact 64 F}
    {c : Ivl} (hg : GuestInv s) (hc8 : c.1 % 8 = 0) (hn8 : c.2 % 8 = 0)
    (hlo : sourceBase ≤ c.1) (hhi : c.1 + c.2 ≤ heapEnd) :
    WordsOK s c := by
  refine ⟨hc8, hn8, fun k hk => ?_⟩
  exact wordAt_of_ordinary hg (by omega) (by omega) (by omega)

theorem trackedBlocks_subintervals {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {bs cs : List Ivl}
    (hA : ArenaReady s) (hbs : TrackedBlocks s S Nd bs)
    (hcs : ∀ c ∈ cs, c.1 % 8 = 0 ∧ c.2 % 8 = 0 ∧
      ∃ b ∈ bs, Inside c b.1 (b.1 + b.2)) :
    TrackedBlocks s S Nd cs := by
  intro c hc
  obtain ⟨hc8, hn8, b, hb, hcb⟩ := hcs c hc
  obtain ⟨_, _, hbin, _, hbd⟩ := hbs b hb
  have hcin : Inside c sourceBase (globN s "heap_ptr") :=
    ⟨le_trans hbin.1 hcb.1, le_trans hcb.2 hbin.2⟩
  refine ⟨hc8, hn8, hcin, ?_, fun o ho => disj_of_inside_left hcb (hbd o ho)⟩
  exact wordsOK_of_inside_heap hA.1 hc8 hn8 hcin.1
    (le_trans hcin.2 (le_trans hA.2.2.1 (by decide)))

theorem trackedBlocks_append {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {bs cs : List Ivl} :
    TrackedBlocks s S Nd (bs ++ cs) ↔
      TrackedBlocks s S Nd bs ∧ TrackedBlocks s S Nd cs := by
  constructor
  · intro h
    exact ⟨fun b hb => h b (List.mem_append_left cs hb),
      fun c hc => h c (List.mem_append_right bs hc)⟩
  · rintro ⟨hb, hc⟩ b hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hb b hm
    · exact hc b hm

def SliceLengthsBelow {F : Type} (s : PanSemStateFiniteExact 64 F)
    (base count : Nat) : Prop :=
  ∀ i, i < count → memW s (base + 16 * i + 8) < 2 ^ 40

theorem sliceLengthsBelow_zero {F : Type} (s : PanSemStateFiniteExact 64 F) (base : Nat) :
    SliceLengthsBelow s base 0 := by
  intro i hi
  omega

theorem sliceLengthsBelow_mono {F : Type} {s : PanSemStateFiniteExact 64 F}
    {base m n : Nat} (h : SliceLengthsBelow s base n) (hm : m ≤ n) :
    SliceLengthsBelow s base m := by
  intro i hi
  exact h i (lt_of_lt_of_le hi hm)

theorem sliceLengthsBelow_succ {F : Type} {s : PanSemStateFiniteExact 64 F}
    {base n : Nat} (h : SliceLengthsBelow s base n)
    (hn : memW s (base + 16 * n + 8) < 2 ^ 40) :
    SliceLengthsBelow s base (n + 1) := by
  intro i hi
  by_cases hin : i < n
  · exact h i hin
  · have heq : i = n := by omega
    subst i
    exact hn

theorem sliceLengthsBelow_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k base count : Nat) :
    SliceLengthsBelow {s with locals := locals, clock := k} base count ↔
      SliceLengthsBelow s base count := Iff.rfl

theorem sliceLengthsBelow_transfer {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {base count : Nat} (h : SliceLengthsBelow s base count)
    (hm : ∀ i, i < count → memW post (base + 16 * i + 8) =
      memW s (base + 16 * i + 8)) :
    SliceLengthsBelow post base count := by
  intro i hi
  rw [hm i hi]
  exact h i hi

theorem sliceLengthsBelow_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {base count : Nat} (h : SliceLengthsBelow s base count)
    (hal : base % 8 = 0) (hbound : base + 16 * count ≤ 2 ^ 64)
    (hu : IvlUnhit s post (base, 16 * count)) :
    SliceLengthsBelow post base count := by
  apply sliceLengthsBelow_transfer h
  intro i hi
  apply memW_eq_of_ivlUnhit hu
  · omega
  · exact hbound
  · dsimp only
    omega

theorem buildMptIndexedReady_of_sliceLengths {F : Type}
    {s : PanSemStateFiniteExact 64 F}
    (hW : WorldOK s)
    (hl : ∀ name ∈ (["slice_arr", "n", "out"] : List String),
      ∃ w : BitVec 64, s.locals.lookup (ofString name) = some (.val (.word w)))
    (hn : locN s "n" < 2 ^ 32)
    (hin : Inside (locN s "slice_arr", 16 * locN s "n") sourceBase (globN s "heap_ptr"))
    (hw : WordsOK s (locN s "slice_arr", 16 * locN s "n"))
    (hd : IvlsDisj [(locN s "slice_arr", 16 * locN s "n")]
      ([("mpt_hash_scratch", 40), ("mpt_key_scratch", 16),
        ("keccak_pad", 136), ("keccak_st", 200)].map (bufferRegion s)))
    (hsl : SliceLengthsBelow s (locN s "slice_arr") (locN s "n")) :
    BuildMptIndexedReady s :=
  ⟨hW, hl, hn, hin, hw, hd, hsl⟩

theorem trackedBlocks_sliceLengths_worldStep
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {S Nd : List Nat} {bs : List Ivl}
    {base count : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd)
    (hbs : TrackedBlocks s S Nd bs) (hmem : (base, 16 * count) ∈ bs)
    (hsl : SliceLengthsBelow s base count) (hstep : WorldStep R gw keep Q s r post)
    (hRzero : ∀ j ∈ R s, j.2 = 0 → j.1 % 8 = 0)
    (hRtyped : IvlsDisj (R s) (worldTypedIvls s S Nd))
    (hRbs : IvlsDisj bs (R s)) :
    ∃ S' Nd', WorldTypedWith post S' Nd' ∧ TrackedBlocks post S' Nd' bs ∧
      SliceLengthsBelow post base count ∧ Q s r post S' Nd' := by
  obtain ⟨S', Nd', hW', hbs', hu, hQ⟩ :=
    trackedBlocks_worldStep hA hW hbs hstep hRzero hRtyped hRbs
  obtain ⟨hal, _, hin, _, _⟩ := hbs (base, 16 * count) hmem
  have hbound : base + 16 * count ≤ 2 ^ 64 := by
    have hlim := hA.2.2.1
    have h64 : heapLimit ≤ 2 ^ 64 := by decide
    obtain ⟨_, hhi⟩ := hin
    exact hhi.trans (hlim.trans h64)
  exact ⟨S', Nd', hW', hbs', sliceLengthsBelow_of_unhit hsl hal hbound
    (hu (base, 16 * count) hmem), hQ⟩

def BlockSliceLengths {F : Type} (s : PanSemStateFiniteExact 64 F) (count : Nat) : Prop :=
  SliceLengthsBelow s (memW s (globN s "bo" + 24)) count ∧
  SliceLengthsBelow s (memW s (globN s "bo" + 32)) count

theorem blockSliceLengths_zero {F : Type} (s : PanSemStateFiniteExact 64 F) :
    BlockSliceLengths s 0 :=
  ⟨sliceLengthsBelow_zero s _, sliceLengthsBelow_zero s _⟩

theorem blockSliceLengths_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k count : Nat) :
    BlockSliceLengths {s with locals := locals, clock := k} count ↔
      BlockSliceLengths s count := Iff.rfl

theorem blockSliceLengths_of_unhit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {count : Nat}
    (h : BlockSliceLengths s count)
    (hp : ∀ off ∈ ([24, 32] : List Nat),
      memW post (globN post "bo" + off) = memW s (globN s "bo" + off))
    (ha : ∀ off ∈ ([24, 32] : List Nat),
      memW s (globN s "bo" + off) % 8 = 0)
    (hb : ∀ off ∈ ([24, 32] : List Nat),
      memW s (globN s "bo" + off) + 16 * count ≤ 2 ^ 64)
    (hu : ∀ off ∈ ([24, 32] : List Nat),
      IvlUnhit s post (memW s (globN s "bo" + off), 16 * count)) :
    BlockSliceLengths post count := by
  constructor
  · change SliceLengthsBelow post (memW post (globN post "bo" + 24)) count
    rw [hp 24 (by simp)]
    exact sliceLengthsBelow_of_unhit h.1 (ha 24 (by simp))
      (hb 24 (by simp)) (hu 24 (by simp))
  · change SliceLengthsBelow post (memW post (globN post "bo" + 32)) count
    rw [hp 32 (by simp)]
    exact sliceLengthsBelow_of_unhit h.2 (ha 32 (by simp))
      (hb 32 (by simp)) (hu 32 (by simp))

def RetTransactionSlices : ∀ {F : Type}, PanSemStateFiniteExact 64 F →
    Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post _ _ => ∀ v, r = some (.returned v) →
    (∀ off ∈ ([24, 32] : List Nat), ∀ i, i < locN s "index" →
      memW post (memW post (globN post "bo" + off) + 16 * i + 8) =
        memW s (memW s (globN s "bo" + off) + 16 * i + 8)) ∧
    (∀ off ∈ ([24, 32] : List Nat),
      memW post (memW post (globN post "bo" + off) + 16 * locN s "index" + 8) < 2 ^ 40)

theorem blockSliceLengths_transaction {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {S Nd : List Nat} {v : ValueHOL 64}
    (h : BlockSliceLengths s (locN s "index"))
    (hq : RetTransactionSlices s r post S Nd) (hr : r = some (.returned v)) :
    BlockSliceLengths post (locN s "index" + 1) := by
  obtain ⟨hkeep, hnew⟩ := hq v hr
  constructor
  · apply sliceLengthsBelow_succ
    · intro i hi
      rw [hkeep 24 (by simp) i hi]
      exact h.1 i hi
    · exact hnew 24 (by simp)
  · apply sliceLengthsBelow_succ
    · intro i hi
      rw [hkeep 32 (by simp) i hi]
      exact h.2 i hi
    · exact hnew 32 (by simp)

theorem inputRegions_word_eq {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {si hdr : Nat} (hA : ArenaReady s)
    (hc : ∀ c ∈ inputRegions s si hdr,
      c.1 % 8 = 0 ∧ Inside c sourceBase (globN s "heap_ptr") ∧ WordsOK s c)
    (hu : ∀ c ∈ inputRegions s si hdr, IvlUnhit s post c)
    {c : Ivl} (hm : c ∈ inputRegions s si hdr) {off : Nat}
    (ho : off % 8 = 0) (hf : off + 8 ≤ c.2) :
    memW post (c.1 + off) = memW s (c.1 + off) := by
  obtain ⟨hal, hin, _⟩ := hc c hm
  have hlim := hA.2.2.1
  have h64 : heapLimit ≤ 2 ^ 64 := by decide
  apply memW_eq_of_ivlUnhit (hu c hm)
  · omega
  · exact hin.2.trans (hlim.trans h64)
  · exact ⟨by omega, by omega⟩

theorem inputRegions_eq_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {si hdr : Nat} (hA : ArenaReady s)
    (hc : ∀ c ∈ inputRegions s si hdr,
      c.1 % 8 = 0 ∧ Inside c sourceBase (globN s "heap_ptr") ∧ WordsOK s c)
    (hu : ∀ c ∈ inputRegions s si hdr, IvlUnhit s post c)
    (hwd : globN post "wd_rlp_slices" = globN s "wd_rlp_slices") :
    inputRegions post si hdr = inputRegions s si hdr := by
  have hsi0 : memW post si = memW s si := by
    simpa only [Nat.add_zero] using
      (inputRegions_word_eq hA hc hu (c := (si, 96)) (by simp [inputRegions])
        (off := 0) (by omega) (by omega))
  have hsi32 := inputRegions_word_eq hA hc hu (c := (si, 96))
    (by simp [inputRegions]) (off := 32) (by omega) (by omega)
  have hpl32 := inputRegions_word_eq hA hc hu (c := (memW s si, 136))
    (by simp [inputRegions]) (off := 32) (by omega) (by omega)
  have hpl40 := inputRegions_word_eq hA hc hu (c := (memW s si, 136))
    (by simp [inputRegions]) (off := 40) (by omega) (by omega)
  have hpl56 := inputRegions_word_eq hA hc hu (c := (memW s si, 136))
    (by simp [inputRegions]) (off := 56) (by omega) (by omega)
  simp only [inputRegions, hsi0, hsi32, hpl32, hpl40, hpl56, hwd]

structure BlockContext {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S Nd : List Nat) (si hdr : Nat) : Prop where
  arena : ArenaReady s
  jcap_nz : globN s "journal_cap" ≠ 0
  world : WorldTypedWith s S Nd
  regions : TrackedBlocks s S Nd (inputRegions s si hdr)
  ntx_63 : memW s (memW s si + 40) < 2 ^ 63
  ntx_wrap : 16 * memW s (memW s si + 40) + 16 < 2 ^ 64
  payload : PayloadAt s (memW s si)
  requests : RequestsAt s (memW s (si + 32))
  header_extra : memW s (hdr + 136) ≤ 32
  tx_heap : ∀ i, i < memW s (memW s si + 40) →
    memW s (memW s (memW s si + 32) + 16 * i) +
      memW s (memW s (memW s si + 32) + 16 * i + 8) ≤ globN s "heap_ptr"
  nwd_32 : memW s (memW s si + 56) < 2 ^ 32
  wd_slices : SliceLengthsBelow s (globN s "wd_rlp_slices") (memW s (memW s si + 56))
  hashes : globN s "block_hashes_n" ≠ 0 →
    TrackedBlocks s S Nd [(globN s "block_hashes", 32 * globN s "block_hashes_n")]

theorem blockContext_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (S Nd : List Nat) (si hdr : Nat) :
    BlockContext {s with locals := locals, clock := k} S Nd si hdr ↔
      BlockContext s S Nd si hdr := by
  constructor <;>
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
    exact ⟨by simpa [arenaReady_with_locals] using h1, h2,
      by simpa [worldTypedWith_with_locals] using h3, h4, h5, h6, h7, h8, h9,
      h10, h11, h12, h13⟩

theorem blockContext_worldOK {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si hdr : Nat} (h : BlockContext s S Nd si hdr) :
    WorldOK s :=
  ⟨h.arena, S, (worldTyped_iff_with s S).2 ⟨Nd, h.world⟩⟩

theorem blockContext_of_entry {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hB : BlockReadyStrong s) (hE : EntryAt s (locN s "si") (locN s "hdr")) :
    ∃ S Nd, BlockContext s S Nd (locN s "si") (locN s "hdr") := by
  obtain ⟨hBR, hIR, hHdr⟩ := hB
  obtain ⟨hA, _, _, _, _, _, hntx63, hPay, hReq⟩ := hIR
  obtain ⟨hjc, S, Nd, hW, hc, hdisj, htxh, hnwd, hwds, hhash⟩ := hE
  refine ⟨S, Nd, ⟨hA, hjc, hW, ?_, hntx63, hBR.2, hPay, hReq, hHdr.2,
    htxh, hnwd, hwds, ?_⟩⟩
  · intro c hm
    obtain ⟨hc1, hin, hw⟩ := hc c hm
    exact ⟨hc1, hw.2.1, hin, hw, fun o ho => hdisj c hm o ho⟩
  · intro hbnz
    obtain ⟨hin, hw, hd⟩ := hhash hbnz
    intro b hb
    have rfl_b := List.mem_singleton.mp hb
    subst b
    exact ⟨hw.1, hw.2.1, hin, hw, fun o ho => hd _ (by simp) o ho⟩

theorem blockContext_transfer_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S Nd S' Nd' : List Nat} {si hdr : Nat}
    (h : BlockContext s S Nd si hdr)
    (hAp : ArenaReady post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hjc : globN post "journal_cap" = globN s "journal_cap")
    (hwd : globN post "wd_rlp_slices" = globN s "wd_rlp_slices")
    (hbh : globN post "block_hashes" = globN s "block_hashes")
    (hbhn : globN post "block_hashes_n" = globN s "block_hashes_n")
    (hW' : WorldTypedWith post S' Nd')
    (hreg' : TrackedBlocks post S' Nd' (inputRegions s si hdr))
    (hu : ∀ c ∈ inputRegions s si hdr, IvlUnhit s post c)
    (hhash' : globN s "block_hashes_n" ≠ 0 →
      TrackedBlocks post S' Nd' [(globN s "block_hashes", 32 * globN s "block_hashes_n")]) :
    BlockContext post S' Nd' si hdr := by
  have hc : ∀ c ∈ inputRegions s si hdr,
      c.1 % 8 = 0 ∧ Inside c sourceBase (globN s "heap_ptr") ∧ WordsOK s c :=
    fun c hm => ⟨(h.regions c hm).1, (h.regions c hm).2.2.1, (h.regions c hm).2.2.2.1⟩
  have hir_eq := inputRegions_eq_of_unhit h.arena hc hu hwd
  have hsi0 : memW post si = memW s si := by
    simpa only [Nat.add_zero] using
      (inputRegions_word_eq h.arena hc hu (c := (si, 96)) (by simp [inputRegions])
        (off := 0) (by omega) (by omega))
  have hsi32 := inputRegions_word_eq h.arena hc hu (c := (si, 96))
    (by simp [inputRegions]) (off := 32) (by omega) (by omega)
  have hpl24 := inputRegions_word_eq h.arena hc hu (c := (memW s si, 136))
    (by simp [inputRegions]) (off := 24) (by omega) (by omega)
  have hpl32 := inputRegions_word_eq h.arena hc hu (c := (memW s si, 136))
    (by simp [inputRegions]) (off := 32) (by omega) (by omega)
  have hpl40 := inputRegions_word_eq h.arena hc hu (c := (memW s si, 136))
    (by simp [inputRegions]) (off := 40) (by omega) (by omega)
  have hpl56 := inputRegions_word_eq h.arena hc hu (c := (memW s si, 136))
    (by simp [inputRegions]) (off := 56) (by omega) (by omega)
  have hhdr136 := inputRegions_word_eq h.arena hc hu (c := (hdr, 248))
    (by simp [inputRegions]) (off := 136) (by omega) (by omega)
  have htx_eq : ∀ i, i < memW s (memW s si + 40) →
      memW post (memW s (memW s si + 32) + 16 * i) =
        memW s (memW s (memW s si + 32) + 16 * i) ∧
      memW post (memW s (memW s si + 32) + 16 * i + 8) =
        memW s (memW s (memW s si + 32) + 16 * i + 8) := by
    intro i hi
    refine ⟨?_, ?_⟩
    · simpa [Nat.add_assoc] using inputRegions_word_eq h.arena hc hu
        (c := (memW s (memW s si + 32), 16 * memW s (memW s si + 40)))
        (by simp [inputRegions]) (off := 16 * i) (by omega) (by omega)
    · simpa [Nat.add_assoc] using inputRegions_word_eq h.arena hc hu
        (c := (memW s (memW s si + 32), 16 * memW s (memW s si + 40)))
        (by simp [inputRegions]) (off := 16 * i + 8) (by omega) (by omega)
  have hrq_eq : ∀ i, i < 5 →
      memW post (memW s (si + 32) + 16 * i + 8) =
        memW s (memW s (si + 32) + 16 * i + 8) := by
    intro i hi
    simpa [Nat.add_assoc] using inputRegions_word_eq h.arena hc hu
      (c := (memW s (si + 32), 80))
      (by simp [inputRegions]) (off := 16 * i + 8) (by omega) (by omega)
  have hwd_mem : (globN s "wd_rlp_slices", 16 * memW s (memW s si + 56)) ∈
      inputRegions s si hdr := by simp [inputRegions]
  obtain ⟨hwd8, _, hwd_in, _, _⟩ := h.regions _ hwd_mem
  have hwd_bound : globN s "wd_rlp_slices" + 16 * memW s (memW s si + 56) ≤ 2 ^ 64 := by
    have hlim := h.arena.2.2.1
    have h64 : heapLimit ≤ 2 ^ 64 := by decide
    exact hwd_in.2.trans (hlim.trans h64)
  refine ⟨hAp, by rw [hjc]; exact h.jcap_nz, hW', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hir_eq]; exact hreg'
  · rw [hsi0, hpl40]; exact h.ntx_63
  · rw [hsi0, hpl40]; exact h.ntx_wrap
  · rw [hsi0]
    refine ⟨wordsOK_transfer h.arena.1 hAp.1 h.payload.1, ?_, ?_, ?_⟩
    · rw [hpl24]; exact h.payload.2.1
    · rw [hpl40]; exact h.payload.2.2.1
    · rw [hpl32, hpl40]
      intro i hi
      rw [(htx_eq i hi).2]
      exact h.payload.2.2.2 i hi
  · rw [hsi32]
    refine ⟨wordsOK_transfer h.arena.1 hAp.1 h.requests.1, fun i hi => ?_⟩
    rw [hrq_eq i hi]
    exact h.requests.2 i hi
  · rw [hhdr136]; exact h.header_extra
  · rw [hsi0, hpl32, hpl40]
    intro i hi
    rw [(htx_eq i hi).1, (htx_eq i hi).2]
    exact (h.tx_heap i hi).trans hhp
  · rw [hsi0, hpl56]; exact h.nwd_32
  · rw [hwd, hsi0, hpl56]
    exact sliceLengthsBelow_of_unhit h.wd_slices hwd8 hwd_bound (hu _ hwd_mem)
  · intro hbnz
    rw [hbhn] at hbnz
    rw [hbh, hbhn]
    exact hhash' hbnz

theorem blockContext_worldStep
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {S Nd : List Nat} {si hdr : Nat} {bs : List Ivl}
    (h : BlockContext s S Nd si hdr)
    (hbs : TrackedBlocks s S Nd bs)
    (hstep : WorldStep R gw keep Q s r post)
    (hjc_out : ofString "journal_cap" ∉ gw.map ofString)
    (hwd_out : ofString "wd_rlp_slices" ∉ gw.map ofString)
    (hbh_out : ofString "block_hashes" ∉ gw.map ofString)
    (hbhn_out : ofString "block_hashes_n" ∉ gw.map ofString)
    (hRzero : ∀ j ∈ R s, j.2 = 0 → j.1 % 8 = 0)
    (hRtyped : IvlsDisj (R s) (worldTypedIvls s S Nd))
    (hRreg : IvlsDisj (inputRegions s si hdr) (R s))
    (hRhash : globN s "block_hashes_n" ≠ 0 →
      IvlsDisj [(globN s "block_hashes", 32 * globN s "block_hashes_n")] (R s))
    (hRbs : IvlsDisj bs (R s)) :
    ∃ S' Nd', BlockContext post S' Nd' si hdr ∧ TrackedBlocks post S' Nd' bs ∧
      (∀ c ∈ inputRegions s si hdr, IvlUnhit s post c) ∧
      (∀ b ∈ bs, IvlUnhit s post b) ∧ Q s r post S' Nd' := by
  let hashList : List Ivl :=
    if globN s "block_hashes_n" = 0 then []
    else [(globN s "block_hashes", 32 * globN s "block_hashes_n")]
  have hhash_tb : TrackedBlocks s S Nd hashList := by
    by_cases hz : globN s "block_hashes_n" = 0
    · simp [hashList, hz, TrackedBlocks]
    · simpa [hashList, hz] using h.hashes hz
  have hall_tb : TrackedBlocks s S Nd ((inputRegions s si hdr ++ hashList) ++ bs) :=
    trackedBlocks_append.2 ⟨trackedBlocks_append.2 ⟨h.regions, hhash_tb⟩, hbs⟩
  have hRall : IvlsDisj ((inputRegions s si hdr ++ hashList) ++ bs) (R s) := by
    intro x hx y hy
    rcases List.mem_append.1 hx with hx1 | hxbs
    · rcases List.mem_append.1 hx1 with hxreg | hxhash
      · exact hRreg x hxreg y hy
      · by_cases hz : globN s "block_hashes_n" = 0
        · simp [hashList, hz] at hxhash
        · simp only [hashList, hz, ↓reduceIte] at hxhash
          exact hRhash hz x hxhash y hy
    · exact hRbs x hxbs y hy
  obtain ⟨S', Nd', hW', hall_tb', hu_all, hQ⟩ :=
    trackedBlocks_worldStep h.arena h.world hall_tb hstep hRzero hRtyped hRall
  obtain ⟨h12', hbs'⟩ := trackedBlocks_append.1 hall_tb'
  obtain ⟨hreg', hhash_tb'⟩ := trackedBlocks_append.1 h12'
  have hu_reg : ∀ c ∈ inputRegions s si hdr, IvlUnhit s post c :=
    fun c hc => hu_all c (List.mem_append_left _ (List.mem_append_left _ hc))
  have hu_bs : ∀ b ∈ bs, IvlUnhit s post b :=
    fun b hb => hu_all b (List.mem_append_right _ hb)
  have hctx' : BlockContext post S' Nd' si hdr :=
    blockContext_transfer_unhit h hstep.1 hstep.2.1
      (globN_eq_of_lookup (hstep.2.2.1 _ hjc_out))
      (globN_eq_of_lookup (hstep.2.2.1 _ hwd_out))
      (globN_eq_of_lookup (hstep.2.2.1 _ hbh_out))
      (globN_eq_of_lookup (hstep.2.2.1 _ hbhn_out))
      hW' hreg' hu_reg
      (fun hbnz => by simpa [hashList, hbnz] using hhash_tb')
  exact ⟨S', Nd', hctx', hbs', hu_reg, hu_bs, hQ⟩

theorem worldTypedWith_setGlobal_unowned {F : Type} {s : PanSemStateFiniteExact 64 F}
    {g : String} {w : BitVec 64} {S Nd : List Nat}
    (hAs : ArenaReady s) (hW : WorldTypedWith s S Nd)
    (h1 : ofString "heap_ptr" ≠ ofString g)
    (h2 : ofString "frame_mem_ptr" ≠ ofString g)
    (h3 : ofString "scratch_ptr" ≠ ofString g)
    (hgb : ∀ gn ∈ globalBuffers, ofString gn.1 ≠ ofString g)
    (hgtr : ∀ gr ∈ globalTableRoots, ofString gr ≠ ofString g)
    (hj : ofString "journal" ≠ ofString g)
    (hjc : ofString "journal_cap" ≠ ofString g)
    (hjn : ofString "journal_n" ≠ ofString g) :
    let post := setGlobalHOLFinite (ofString g) (.val (.word w)) s
    ArenaReady post ∧ WorldTypedWith post S Nd ∧
      worldOwned post S Nd = worldOwned s S Nd := by
  intro post
  have hAp : ArenaReady post := arenaReady_setGlobal_ne hAs (ofString g) w h1 h2 h3
  have hag : AllocatorGrows s post := by
    unfold AllocatorGrows
    rw [globN_setGlobal_ne s (ofString g) (.val (.word w)) "heap_ptr" h1,
        globN_setGlobal_ne s (ofString g) (.val (.word w)) "scratch_ptr" h3]
    exact ⟨le_rfl, le_rfl⟩
  have hgs : WorldGlobalsSame s post :=
    ⟨fun gn hgn => globN_setGlobal_ne s (ofString g) (.val (.word w)) gn.1 (hgb gn hgn),
     fun gr hgr => globN_setGlobal_ne s (ofString g) (.val (.word w)) gr (hgtr gr hgr),
     globN_setGlobal_ne s (ofString g) (.val (.word w)) "journal" hj,
     globN_setGlobal_ne s (ofString g) (.val (.word w)) "journal_cap" hjc,
     globN_setGlobal_ne s (ofString g) (.val (.word w)) "journal_n" hjn⟩
  have hcongr := worldTypedWith_congr_bo hAs hAp rfl hag hgs hW
    (fun _ _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ => rfl)
    (fun _ _ _ _ => rfl)
    (fun _ _ _ _ => rfl)
    (fun _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ => rfl)
    (fun _ _ _ => rfl)
    ⟨rfl, rfl⟩
  exact ⟨hAp, hcongr.1, hcongr.2.1⟩

theorem blockContext_setGlobal_bal_index {F : Type} {s : PanSemStateFiniteExact 64 F}
    {w : BitVec 64} {S Nd : List Nat} {si hdr : Nat} {bs : List Ivl}
    (h : BlockContext s S Nd si hdr) (hbs : TrackedBlocks s S Nd bs) :
    let post := setGlobalHOLFinite (ofString "bal_index") (.val (.word w)) s
    BlockContext post S Nd si hdr ∧ TrackedBlocks post S Nd bs := by
  intro post
  obtain ⟨hAp, hW', how_eq⟩ := worldTypedWith_setGlobal_unowned (g := "bal_index") (w := w)
    h.arena h.world (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have hhp_eq : globN post "heap_ptr" = globN s "heap_ptr" :=
    globN_setGlobal_ne s (ofString "bal_index") (.val (.word w)) "heap_ptr" (by decide)
  have hjc_eq : globN post "journal_cap" = globN s "journal_cap" :=
    globN_setGlobal_ne s (ofString "bal_index") (.val (.word w)) "journal_cap" (by decide)
  have hwd_eq : globN post "wd_rlp_slices" = globN s "wd_rlp_slices" :=
    globN_setGlobal_ne s (ofString "bal_index") (.val (.word w)) "wd_rlp_slices" (by decide)
  have hbh_eq : globN post "block_hashes" = globN s "block_hashes" :=
    globN_setGlobal_ne s (ofString "bal_index") (.val (.word w)) "block_hashes" (by decide)
  have hbhn_eq : globN post "block_hashes_n" = globN s "block_hashes_n" :=
    globN_setGlobal_ne s (ofString "bal_index") (.val (.word w)) "block_hashes_n" (by decide)
  have htb_tr : ∀ xs, TrackedBlocks s S Nd xs → TrackedBlocks post S Nd xs := by
    intro xs hxs b hb
    obtain ⟨h1, h2, hin, hw, hdisj⟩ := hxs b hb
    refine ⟨h1, h2, by rw [hhp_eq]; exact hin, wordsOK_transfer h.arena.1 hAp.1 hw, ?_⟩
    rw [how_eq]; exact hdisj
  refine ⟨blockContext_transfer_unhit h hAp (by rw [hhp_eq]) hjc_eq hwd_eq hbh_eq hbhn_eq
    hW' (htb_tr _ h.regions) (fun _ _ _ _ _ => rfl) (fun hbnz => htb_tr _ (h.hashes hbnz)),
    htb_tr _ hbs⟩

theorem lookup_execute_block :
    originalRuntimeCode.lookup (ofString "execute_block") =
      some ((sourceFunctionEntry Guest.Software.guestFn_execute_block).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 878 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_execute_block) rfl

theorem lookup_decode_transaction_fn :
    originalRuntimeCode.lookup (ofString "decode_transaction") =
      some ((sourceFunctionEntry Guest.Software.guestFn_decode_transaction).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 307 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_decode_transaction) rfl

theorem lookup_process_transaction_fn :
    originalRuntimeCode.lookup (ofString "process_transaction") =
      some ((sourceFunctionEntry Guest.Software.guestFn_process_transaction).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 873 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_process_transaction) rfl

theorem lookup_lst_new_fn :
    originalRuntimeCode.lookup (ofString "lst_new") =
      some ((sourceFunctionEntry Guest.Software.guestFn_lst_new).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 408 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_lst_new) rfl

theorem alloc_call_mem_be_eq {F : Type}
    {state : PanSemStateFiniteExact 64 F}
    {values : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret : ShapeHOL}
    {v : ValueHOL 64} {post : PanSemStateFiniteExact 64 F}
    (hcode : state.code = originalRuntimeCode)
    (hA : ArenaReady state)
    (hl : lookupCodeHOLFinite state.code.lookup (ofString "alloc") values =
      some (body, callee, ret))
    (hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
      (some (.returned v), post)) :
    post.memory = state.memory ∧ post.be = state.be := by
  have hcode' : state.code.lookup (ofString "alloc") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_alloc, .one) := by
    rw [hcode]; exact lookup_alloc
  have hsome := lookupCodeHOLFinite_eq_some state.code.lookup (ofString "alloc")
    values body callee ret hl
  unfold lookupCodeHOLExact at hsome
  rw [hcode'] at hsome
  dsimp only at hsome
  split at hsome
  · rename_i hcond
    have hEq := Option.some.inj hsome
    obtain ⟨rfl, hrest⟩ := Prod.mk.inj hEq
    obtain ⟨hloc, _⟩ := Prod.mk.inj hrest
    rcases values with _ | ⟨v1, _ | _⟩
    · simp at hcond
    · rcases v1 with ⟨⟨nw⟩⟩ | _ | _
      · have hn_lu : (callEntryStateHOLFinite state callee).locals.lookup (ofString "n") =
            some (.val (.word nw)) := by
          change callee.lookup (ofString "n") = some (.val (.word nw))
          rw [← hloc]
          simp [List.zip, List.foldl]
        obtain ⟨hp, hhp⟩ := hA.2.2.2.2.2.2.2.2.2 "heap_ptr" (by decide)
        have hmeta_be := (evaluateHOLFiniteState_metadata
          (callEntryStateHOLFinite state callee) (sourceFnBody Guest.Software.guestFn_alloc)).2.2.1
        have hbody_props := evaluate_alloc_body_eq (callEntryStateHOLFinite state callee) hp nw
          hcode hhp hn_lu v (by rw [hrun])
        rw [hrun] at hbody_props hmeta_be
        exact ⟨hbody_props.2.2.2, hmeta_be⟩
      · simp [List.zip, shapeOfHOLExact, shapeEqHOL] at hcond
      · simp [List.zip, shapeOfHOLExact, shapeEqHOL] at hcond
    · simp at hcond
  · cases hsome

theorem blockContext_worldStep_nil
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {S Nd : List Nat} {si hdr : Nat} {bs : List Ivl}
    (h : BlockContext s S Nd si hdr) (hbs : TrackedBlocks s S Nd bs)
    (hstep : WorldStep (fun _ => []) gw keep Q s r post)
    (hjc : ofString "journal_cap" ∉ gw.map ofString)
    (hwd : ofString "wd_rlp_slices" ∉ gw.map ofString)
    (hbh : ofString "block_hashes" ∉ gw.map ofString)
    (hbhn : ofString "block_hashes_n" ∉ gw.map ofString) :
    ∃ S' Nd', BlockContext post S' Nd' si hdr ∧ TrackedBlocks post S' Nd' bs ∧
      (∀ c ∈ inputRegions s si hdr, IvlUnhit s post c) ∧
      (∀ b ∈ bs, IvlUnhit s post b) ∧ Q s r post S' Nd' := by
  exact blockContext_worldStep h hbs hstep hjc hwd hbh hbhn
    (by simp) (by simp [IvlsDisj]) (by simp [IvlsDisj])
    (by simp [IvlsDisj]) (by simp [IvlsDisj])

theorem blockContext_alloc_result
    {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si hdr n : Nat} {bs : List Ivl} {w : BitVec 64}
    (h : BlockContext s S Nd si hdr) (hbs : TrackedBlocks s S Nd bs)
    (hf : FreshBlock s post w.toNat n)
    (hstep : WorldStep (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun _ _ p => [(p, (n + 7) / 8 * 8)])) s
      (some (.returned (.val (.word w)))) post) :
    ∃ S' Nd', BlockContext post S' Nd' si hdr ∧
      TrackedBlocks post S' Nd' (bs ++ [(w.toNat, (n + 7) / 8 * 8)]) ∧
      (∀ c ∈ inputRegions s si hdr, IvlUnhit s post c) ∧
      (∀ b ∈ bs, IvlUnhit s post b) := by
  obtain ⟨S', Nd', hc, hb, hu, hub, hq⟩ :=
    blockContext_worldStep_nil h hbs hstep (by decide) (by decide) (by decide) (by decide)
  obtain ⟨w', heq, hd⟩ := hq (.val (.word w)) rfl
  have hw : w = w' := by cases heq; rfl
  subst w'
  exact ⟨S', Nd', hc, trackedBlocks_append.2 ⟨hb,
    trackedBlocks_fresh h.arena hc.arena hc.world hf hd⟩, hu, hub⟩

theorem blockContext_lst_new_result
    {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si hdr : Nat} {bs : List Ivl} {w : BitVec 64}
    (h : BlockContext s S Nd si hdr) (hbs : TrackedBlocks s S Nd bs)
    (hhead : FreshBlock s post w.toNat 24)
    (hdata : FreshBlock s post (memW post w.toNat) 128)
    (hlen : memW post (w.toNat + 8) = 0)
    (hcap : memW post (w.toNat + 16) = 16)
    (hstep : WorldStep (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun _ post p => [(p, 24), (memW post p, 128)])) s
      (some (.returned (.val (.word w)))) post) :
    ∃ S' Nd', BlockContext post S' Nd' si hdr ∧
      TrackedBlocks post S' Nd' (bs ++ [(w.toNat, 24), (memW post w.toNat, 128)]) ∧
      LstOK post w.toNat ∧ w.toNat ≠ 0 ∧
      (∀ c ∈ inputRegions s si hdr, IvlUnhit s post c) ∧
      (∀ b ∈ bs, IvlUnhit s post b) := by
  obtain ⟨S', Nd', hc, hb, hu, hub, hq⟩ :=
    blockContext_worldStep_nil h hbs hstep (by decide) (by decide) (by decide) (by decide)
  obtain ⟨w', heq, hd⟩ := hq (.val (.word w)) rfl
  have hw : w = w' := by cases heq; rfl
  subst w'
  have hhead' : TrackedBlocks post S' Nd' [(w.toNat, 24)] := by
    apply trackedBlocks_fresh h.arena hc.arena hc.world hhead
    simpa only [show (24 + 7) / 8 * 8 = 24 from rfl] using
      (show IvlsDisj [(w.toNat, 24)] (worldOwned post S' Nd') from
        fun b hb o ho => hd b (by rw [List.mem_singleton.mp hb]; simp) o ho)
  have hdata' : TrackedBlocks post S' Nd' [(memW post w.toNat, 128)] := by
    apply trackedBlocks_fresh h.arena hc.arena hc.world hdata
    simpa only [show (128 + 7) / 8 * 8 = 128 from rfl] using
      (show IvlsDisj [(memW post w.toNat, 128)] (worldOwned post S' Nd') from
        fun b hb o ho => hd b (by rw [List.mem_singleton.mp hb]; simp) o ho)
  have hnz : w.toNat ≠ 0 := by
    have hlo := hhead.2.1.1
    have hsource := h.arena.2.1
    have hpos : 0 < sourceBase := by decide
    omega
  refine ⟨S', Nd', hc, trackedBlocks_append.2 ⟨hb, ?_⟩,
    ?_, hnz, hu, hub⟩
  · exact trackedBlocks_append.2 ⟨hhead', hdata'⟩
  · simp [LstOK, hlen, hcap]

theorem blockOutObjects_of_zero_slots {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hz : ∀ off ∈ ([24, 32, 40, 56, 72] : List Nat),
      memW s (globN s "bo" + off) = 0) :
    blockOutObjects s = List.replicate 7 (0, 0) := by
  simp [blockOutObjects, hz 24 (by simp), hz 32 (by simp), hz 40 (by simp),
    hz 56 (by simp), hz 72 (by simp), List.replicate]

theorem trackedBlocks_array_parts {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {p n : Nat}
    (hA : ArenaReady s) (h : TrackedBlocks s S Nd [(p, 16 * n + 16)]) :
    TrackedBlocks s S Nd [(p, 16), (p + 16, 16 * n)] := by
  apply trackedBlocks_subintervals hA h
  intro c hc
  obtain ⟨hp8, _, _, _, _⟩ := h (p, 16 * n + 16) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact ⟨hp8, by omega, (p, 16 * n + 16), by simp,
      by unfold Inside; dsimp only; omega⟩
  · exact ⟨by omega, by omega, (p, 16 * n + 16), by simp,
      by unfold Inside; dsimp only; omega⟩

theorem trackedBlocks_array_join {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {p n : Nat}
    (hA : ArenaReady s)
    (h : TrackedBlocks s S Nd [(p, 16), (p + 16, 16 * n)]) :
    TrackedBlocks s S Nd [(p, 16 * n + 16)] := by
  obtain ⟨hp8, _, hin1, _, hd1⟩ := h (p, 16) (by simp)
  obtain ⟨_, _, hin2, _, hd2⟩ := h (p + 16, 16 * n) (by simp)
  have hin : Inside (p, 16 * n + 16) sourceBase (globN s "heap_ptr") := by
    unfold Inside at hin1 hin2 ⊢
    dsimp only at hin1 hin2 ⊢
    omega
  intro b hb
  have heq := List.mem_singleton.mp hb
  subst b
  refine ⟨hp8, by omega, hin,
    wordsOK_of_inside_heap hA.1 hp8 (by omega) hin.1
      (hin.2.trans (hA.2.2.1.trans (by decide))), ?_⟩
  intro o ho
  have h1 := hd1 o ho
  have h2 := hd2 o ho
  unfold Disj at h1 h2 ⊢
  dsimp only at h1 h2 ⊢
  omega

theorem pairwise_disj_map {α β : Type} {f g : α → β} {R : β → β → Prop}
    (hsym : ∀ x y, R x y → R y x) :
    ∀ {xs : List α},
      xs.Nodup →
      (xs.map f).Pairwise R →
      (∀ x ∈ xs, ∀ y, y ∈ xs.map f → f x ≠ g x → R (g x) y) →
      (∀ x ∈ xs, ∀ y ∈ xs, f x ≠ g x → f y ≠ g y → x ≠ y → R (g x) (g y)) →
      (xs.map g).Pairwise R
  | [], _, _, _, _ => .nil
  | x :: xs, hnd, hp, h1, h2 => by
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.pairwise_cons] at hp ⊢
    refine ⟨fun z hz => ?_,
      pairwise_disj_map hsym hnd.2 hp.2
        (fun a ha b hb hne => h1 a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) hne)
        (fun a ha b hb ha' hb' hne =>
          h2 a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) ha' hb' hne)⟩
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
    have hxy : x ≠ y := fun h => hnd.1 (h ▸ hy)
    by_cases hx : f x = g x
    · by_cases hy' : f y = g y
      · rw [← hx, ← hy']
        exact hp.1 (f y) (List.mem_map_of_mem hy)
      · exact hsym _ _ (h1 y (List.mem_cons_of_mem _ hy) (g x)
          (hx ▸ List.mem_cons_self) hy')
    · by_cases hy' : f y = g y
      · rw [← hy']
        exact h1 x List.mem_cons_self (f y) (List.mem_cons_of_mem _ (List.mem_map_of_mem hy)) hx
      · exact h2 x List.mem_cons_self y (List.mem_cons_of_mem _ hy) hx hy' hxy

theorem pairwise_disj_append_4 {a1 a2 b c : List Ivl} :
    ((a1 ++ a2) ++ b ++ c).Pairwise Disj ↔
      (a1.Pairwise Disj ∧ a2.Pairwise Disj ∧ b.Pairwise Disj ∧ c.Pairwise Disj) ∧
      (∀ x ∈ a1, ∀ y ∈ a2 ++ (b ++ c), Disj x y) ∧
      (∀ x ∈ a2, ∀ y ∈ b ++ c, Disj x y) ∧
      (∀ x ∈ b, ∀ y ∈ c, Disj x y) := by
  simp only [List.append_assoc, List.pairwise_append]
  constructor
  · rintro ⟨hp1, hp2, h1⟩
    obtain ⟨hp2, hp3, h2⟩ := hp2
    obtain ⟨hp3, hp4, h3⟩ := hp3
    exact ⟨⟨hp1, hp2, hp3, hp4⟩, h1, h2, h3⟩
  · rintro ⟨⟨hp1, hp2, hp3, hp4⟩, h1, h2, h3⟩
    exact ⟨hp1, ⟨hp2, ⟨hp3, hp4, h3⟩, h2⟩, h1⟩

theorem list_pairwise_rel {α : Type} {R : α → α → Prop} (hsym : ∀ x y, R x y → R y x)
    {xs : List α} (hp : xs.Pairwise R)
    {i j : Nat} (hi : i < xs.length) (hj : j < xs.length) (hne : i ≠ j) :
    R xs[i] xs[j] := by
  induction xs generalizing i j with
  | nil => simp at hi
  | cons a as ih =>
    rw [List.pairwise_cons] at hp
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl hne
      | succ j' =>
        exact hp.1 _ (List.getElem_mem (by simp at hj; omega))
    | succ i' =>
      cases j with
      | zero =>
        exact hsym _ _ (hp.1 _ (List.getElem_mem (by simp at hi; omega)))
      | succ j' =>
        exact ih hp.2 (by simp at hi; omega) (by simp at hj; omega) (by omega)

theorem worldTypedWith_rebind_fixed {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat}
    (hAs : ArenaReady s) (hAp : ArenaReady post) (hbe : post.be = s.be)
    (hag : AllocatorGrows s post) (hW : WorldTypedWith s S Nd)
    (hgb : ∀ gn ∈ globalBuffers, gn.1 ≠ "bo" → globN post gn.1 = globN s gn.1)
    (hgtr : ∀ g ∈ globalTableRoots, globN post g = globN s g)
    (hj : globN post "journal" = globN s "journal")
    (hjc : globN post "journal_cap" = globN s "journal_cap")
    (hjn : globN post "journal_n" = globN s "journal_n")
    (hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, IvlUnhit s post i)
    (hu_ws : globN s "ws" ≠ 0 → IvlUnhit s post (globN s "ws", 40))
    (hu_bs : globN s "bs" ≠ 0 → IvlUnhit s post (globN s "bs", 80))
    (hu_ts : globN s "ts" ≠ 0 → IvlUnhit s post (globN s "ts", 72))
    (hu_jr : globN s "journal_cap" ≠ 0 → IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap"))
    (hu_bal : ∀ i ∈ balObjects s, IvlUnhit s post i)
    (hu_nd : ∀ o ∈ nodeExtents s Nd, IvlUnhit s post o)
    (hm_low : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16)
    (hbo_ivl : globN post "bo" ≠ 0 →
      Allocated post (globN post "bo", 88) ∧ WordsOK post (globN post "bo", 88) ∧
      (globN post "bo" = globN s "bo" ∨
        ∀ o ∈ worldOwned s S Nd, Disj (globN post "bo", 88) o))
    (hbo_objs : ∀ x ∈ blockOutObjects post,
      x = (0, 0) ∨ (Allocated post x ∧ WordsOK post x ∧ Disj x (globN post "bo", 88) ∧
        ((x ∈ blockOutObjects s ∧ globN post "bo" = globN s "bo") ∨
          ∀ o ∈ worldOwned s S Nd, o ∉ blockOutObjects s → Disj x o)))
    (hbo_pw : (blockOutObjects post).Pairwise Disj)
    (hbo_lst : globN post "bo" ≠ 0 → ∀ k ∈ ([40, 72] : List Nat),
      memW post (globN post "bo" + k) ≠ 0 → LstOK post (memW post (globN post "bo" + k))) :
    WorldTypedWith post S Nd ∧
    ∀ o ∈ worldOwned post S Nd,
      o = (0, 0) ∨ o = (globN post "bo", 88) ∨ o ∈ blockOutObjects post ∨ o ∈ worldOwned s S Nd := by
  obtain ⟨hT, hJ, hF, hTr⟩ := hW
  have h264 : heapEnd ≤ 2 ^ 64 := by decide
  have hws_g : globN post "ws" = globN s "ws" := hgb ("ws", 40) (by simp [globalBuffers]) (by decide)
  have hbs_g : globN post "bs" = globN s "bs" := hgb ("bs", 80) (by simp [globalBuffers]) (by decide)
  have hts_g : globN post "ts" = globN s "ts" := hgb ("ts", 72) (by simp [globalBuffers]) (by decide)
  have hba_g : globN post "bal_accounts" = globN s "bal_accounts" :=
    hgtr "bal_accounts" (by simp [globalTableRoots])
  have hbal_part := balObjects_eq_of_unhit hAs.2 hT hF hba_g hu_tab hu_bal hm_low
  let f_s : String × Nat → Ivl := fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)
  let f_p : String × Nat → Ivl := fun gn => (globN post gn.1, if globN post gn.1 = 0 then 0 else gn.2)
  let jr_s : List Ivl := [(if globN s "journal_cap" = 0 then 0 else globN s "journal",
    32 * globN s "journal_cap")]
  have hjr_eq : [(if globN post "journal_cap" = 0 then 0 else globN post "journal",
      32 * globN post "journal_cap")] = jr_s := by
    simp [jr_s, hj, hjc]
  have hf_eq : ∀ gn ∈ globalBuffers, gn.1 ≠ "bo" → f_p gn = f_s gn := by
    intro gn hgn hne
    simp [f_p, f_s, hgb gn hgn hne]
  have hfix_sub_owned : ∀ j ∈ fixedObjects s, j ∈ worldOwned s S Nd := fun j hj => by
    unfold worldOwned
    exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hj)))
  have htab_sub_owned : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, i ∈ worldOwned s S Nd := fun t ht i hi => by
    unfold worldOwned
    exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨t, ht, hi⟩))))
  have hnd_sub_owned : ∀ o ∈ nodeExtents s Nd, o ∈ worldOwned s S Nd := fun o ho => by
    unfold worldOwned
    exact List.mem_append.2 (Or.inr ho)
  have hmap_sub_fix : ∀ x ∈ globalBuffers.map f_s, x ∈ fixedObjects s := fun x hx => by
    unfold fixedObjects
    exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl hx)))))
  have hjr_sub_fix : ∀ x ∈ jr_s, x ∈ fixedObjects s := fun x hx => by
    unfold fixedObjects
    exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hx)))))
  have hbo_sub_fix : ∀ x ∈ blockOutObjects s, x ∈ fixedObjects s := fun x hx => by
    unfold fixedObjects
    exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hx)))
  have hbal_sub_fix : ∀ x ∈ balObjects s, x ∈ fixedObjects s := fun x hx => by
    unfold fixedObjects
    exact List.mem_append.2 (Or.inr hx)
  have hsbo_mem_map : f_s ("bo", 88) ∈ globalBuffers.map f_s :=
    List.mem_map_of_mem (by simp [globalBuffers] : ("bo", 88) ∈ globalBuffers)
  have hgb_nodup : globalBuffers.Nodup := by decide
  have hgb_bo_unique : ∀ gn ∈ globalBuffers, gn.1 = "bo" → gn = ("bo", 88) := by decide
  have hF_parts := (pairwise_disj_append_4 (a1 := globalBuffers.map f_s) (a2 := jr_s)
    (b := blockOutObjects s) (c := balObjects s)).mp
    (by simpa [fixedObjects, f_s, jr_s] using hF.2)
  have hbo_disj_sfix_nonbo : ∀ y,
      (y ∈ jr_s ∨ y ∈ balObjects s) →
      Disj (f_p ("bo", 88)) y := by
    intro y hy
    by_cases hpz : globN post "bo" = 0
    · simp [f_p, hpz, disj_zero_left]
    · simp only [f_p, hpz, ↓reduceIte]
      rcases (hbo_ivl hpz).2.2 with hsame | hall
      · have hs_nz : globN s "bo" ≠ 0 := hsame ▸ hpz
        have hrel := hF_parts.2.1 (f_s ("bo", 88)) hsbo_mem_map y (by
          rcases hy with hy | hy
          · exact List.mem_append_left _ hy
          · exact List.mem_append_right _ (List.mem_append_right _ hy))
        simpa [f_s, hsame, hpz, hs_nz] using hrel
      · apply hall y (hfix_sub_owned y _)
        rcases hy with hy | hy
        · exact hjr_sub_fix y hy
        · exact hbal_sub_fix y hy
  have hbo_obj_disj_owned_nonbo : ∀ x ∈ blockOutObjects post, ∀ y,
      (y ∈ globalBuffers.map f_s ∧ y ≠ f_s ("bo", 88)) ∨
      y ∈ jr_s ∨ y ∈ balObjects s ∨
      (∃ t ∈ S, y ∈ htabFootprint s t) ∨ y ∈ nodeExtents s Nd →
      Disj x y := by
    intro x hx y hy
    rcases hbo_objs x hx with rfl | ⟨_, _, _, hcases⟩
    · exact disj_zero_left y
    · by_cases hy0 : y.2 = 0
      · exact Or.inr (Or.inl hy0)
      · rcases hcases with ⟨hx_old, _⟩ | hall
        · rcases hy with ⟨hy_map, _⟩ | hy_jr | hy_bal | ⟨t, ht, hy_fp⟩ | hy_nd
          · exact (hF_parts.2.1 y hy_map x (List.mem_append_right _ (List.mem_append_left _ hx_old))).flip
          · exact (hF_parts.2.2.1 y hy_jr x (List.mem_append_left _ hx_old)).flip
          · exact hF_parts.2.2.2 x hx_old y hy_bal
          · exact ((hT.2.1 t ht).2 y hy_fp).2 x (hbo_sub_fix x hx_old) |>.flip
          · exact ((hTr.2.1 y hy_nd).2 x (hbo_sub_fix x hx_old)).flip
        · apply hall y
          · rcases hy with ⟨hy_map, _⟩ | hy_jr | hy_bal | ⟨t, ht, hy_fp⟩ | hy_nd
            · exact hfix_sub_owned y (hmap_sub_fix y hy_map)
            · exact hfix_sub_owned y (hjr_sub_fix y hy_jr)
            · exact hfix_sub_owned y (hbal_sub_fix y hy_bal)
            · exact htab_sub_owned t ht y hy_fp
            · exact hnd_sub_owned y hy_nd
          · intro hy_bo
            have hd : Disj y y := by
              rcases hy with ⟨hy_map, _⟩ | hy_jr | hy_bal | ⟨t, ht, hy_fp⟩ | hy_nd
              · exact hF_parts.2.1 y hy_map y (List.mem_append_right _ (List.mem_append_left _ hy_bo))
              · exact hF_parts.2.2.1 y hy_jr y (List.mem_append_left _ hy_bo)
              · exact (hF_parts.2.2.2 y hy_bo y hy_bal).flip
              · exact ((hT.2.1 t ht).2 y hy_fp).2 y (hbo_sub_fix y hy_bo)
              · exact (hTr.2.1 y hy_nd).2 y (hbo_sub_fix y hy_bo)
            unfold Disj at hd; omega
  have hmap_pw : (globalBuffers.map f_p).Pairwise Disj := by
    apply pairwise_disj_map (fun _ _ h => h.flip) hgb_nodup hF_parts.1.1
    · intro x hx y hy hne
      have hxbo : x = ("bo", 88) := by
        by_cases h1 : x.1 = "bo"
        · exact hgb_bo_unique x hx h1
        · exact absurd (hf_eq x hx h1).symm hne
      subst x
      by_cases hpz : globN post "bo" = 0
      · simp [f_p, hpz, disj_zero_left]
      · simp only [f_p, hpz, ↓reduceIte]
        rcases (hbo_ivl hpz).2.2 with hsame | hall
        · exact absurd (by simp [f_s, f_p, hsame, hpz]) hne
        · exact hall y (hfix_sub_owned y (hmap_sub_fix y hy))
    · intro x hx y hy hxne hyne hxy
      have hxbo : x = ("bo", 88) := by
        by_cases h1 : x.1 = "bo"
        · exact hgb_bo_unique x hx h1
        · exact absurd (hf_eq x hx h1).symm hxne
      have hybo : y = ("bo", 88) := by
        by_cases h1 : y.1 = "bo"
        · exact hgb_bo_unique y hy h1
        · exact absurd (hf_eq y hy h1).symm hyne
      exact absurd (hxbo.trans hybo.symm) hxy
  have hmap_post_mem : ∀ x ∈ globalBuffers.map f_p,
      x = f_p ("bo", 88) ∨ (∃ gn ∈ globalBuffers, gn.1 ≠ "bo" ∧ x = f_s gn) := by
    intro x hx
    obtain ⟨gn, hgn, rfl⟩ := List.mem_map.mp hx
    by_cases h1 : gn.1 = "bo"
    · exact Or.inl (by rw [hgb_bo_unique gn hgn h1])
    · exact Or.inr ⟨gn, hgn, h1, hf_eq gn hgn h1⟩
  have hfix_post_decomp : fixedObjects post =
      (globalBuffers.map f_p ++ jr_s) ++ blockOutObjects post ++ balObjects s := by
    unfold fixedObjects
    rw [hjr_eq, hbal_part.1]
  have hF_post : FixedTyped post := by
    constructor
    · intro i hi
      rw [hfix_post_decomp] at hi
      rcases List.mem_append.mp hi with hi1 | hi_bal
      · rcases List.mem_append.mp hi1 with hi2 | hi_bo_obj
        · rcases List.mem_append.mp hi2 with hi_map | hi_jr
          · rcases hmap_post_mem i hi_map with rfl | ⟨gn, hgn, _, rfl⟩
            · by_cases hpz : globN post "bo" = 0
              · exact Or.inl (by simp [f_p, hpz])
              · simp only [f_p, hpz, ↓reduceIte]
                exact Or.inr ⟨(hbo_ivl hpz).1, (hbo_ivl hpz).2.1⟩
            · rcases hF.1 (f_s gn) (hmap_sub_fix _ (List.mem_map_of_mem hgn)) with hz | ⟨hal, hw⟩
              · exact Or.inl hz
              · exact Or.inr ⟨hag.allocated hal, wordsOK_transfer hAs.1 hAp.1 hw⟩
          · rcases hF.1 i (hjr_sub_fix i hi_jr) with hz | ⟨hal, hw⟩
            · exact Or.inl hz
            · exact Or.inr ⟨hag.allocated hal, wordsOK_transfer hAs.1 hAp.1 hw⟩
        · rcases hbo_objs i hi_bo_obj with rfl | ⟨hal, hw, _, _⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hal, hw⟩
      · rcases hF.1 i (hbal_sub_fix i hi_bal) with hz | ⟨hal, hw⟩
        · exact Or.inl hz
        · exact Or.inr ⟨hag.allocated hal, wordsOK_transfer hAs.1 hAp.1 hw⟩
    · have hpw : ((globalBuffers.map f_p ++ jr_s) ++ blockOutObjects post ++ balObjects s).Pairwise Disj := by
        apply pairwise_disj_append_4.mpr
        refine ⟨⟨hmap_pw, hF_parts.1.2.1, hbo_pw, hF_parts.1.2.2.2⟩, ?_, ?_, ?_⟩
        · intro x hx y hy
          rcases hmap_post_mem x hx with rfl | ⟨gn, hgn, hne_bo, rfl⟩
          · rcases List.mem_append.mp hy with hy_jr | hy_rest
            · exact hbo_disj_sfix_nonbo y (Or.inl hy_jr)
            · rcases List.mem_append.mp hy_rest with hy_bo | hy_bal
              · by_cases hpz : globN post "bo" = 0
                · simp [f_p, hpz, disj_zero_left]
                · simp only [f_p, hpz, ↓reduceIte]
                  rcases hbo_objs y hy_bo with rfl | ⟨_, _, hd_bo, _⟩
                  · exact disj_zero_right _
                  · exact hd_bo.flip
              · exact hbo_disj_sfix_nonbo y (Or.inr hy_bal)
          · have hx_map_s : f_s gn ∈ globalBuffers.map f_s := List.mem_map_of_mem hgn
            rcases List.mem_append.mp hy with hy_jr | hy_rest
            · exact hF_parts.2.1 _ hx_map_s y (List.mem_append_left _ hy_jr)
            · rcases List.mem_append.mp hy_rest with hy_bo | hy_bal
              · by_cases hgz : globN s gn.1 = 0
                · simp [f_s, hgz, disj_zero_left]
                · have hne_sbo : f_s gn ≠ f_s ("bo", 88) := by
                    intro heq
                    by_cases hbz : globN s "bo" = 0
                    · simp [f_s, hgz, hbz] at heq
                    · have hne_gn : gn ≠ ("bo", 88) := fun h => by subst h; contradiction
                      obtain ⟨i1, hi1, heq1⟩ := List.mem_iff_getElem.1 hgn
                      obtain ⟨i2, hi2, heq2⟩ := List.mem_iff_getElem.1 (by simp [globalBuffers] : ("bo", 88) ∈ globalBuffers)
                      have hij : i1 ≠ i2 := fun h => by subst h; rw [heq1] at heq2; exact hne_gn heq2
                      have h1m : i1 < (globalBuffers.map f_s).length := by simp [hi1]
                      have h2m : i2 < (globalBuffers.map f_s).length := by simp [hi2]
                      have hd_self := list_pairwise_rel (fun _ _ h => h.flip) hF_parts.1.1 h1m h2m hij
                      simp only [List.getElem_map, heq1, heq2, heq] at hd_self
                      simp only [f_s, hbz, ↓reduceIte] at hd_self
                      unfold Disj at hd_self; dsimp at hd_self; omega
                  exact (hbo_obj_disj_owned_nonbo y hy_bo _ (Or.inl ⟨hx_map_s, hne_sbo⟩)).flip
              · exact hF_parts.2.1 _ hx_map_s y (List.mem_append_right _ (List.mem_append_right _ hy_bal))
        · intro x hx y hy
          rcases List.mem_append.mp hy with hy_bo | hy_bal
          · exact (hbo_obj_disj_owned_nonbo y hy_bo x (Or.inr (Or.inl hx))).flip
          · exact hF_parts.2.2.1 x hx y (List.mem_append_right _ hy_bal)
        · intro x hx y hy
          exact hbo_obj_disj_owned_nonbo x hx y (Or.inr (Or.inr (Or.inl hy)))
      simpa [hfix_post_decomp] using hpw
  let p_fake : PanSemStateFiniteExact 64 F :=
    setGlobalHOLFinite (ofString "bo") (.val (.word (BitVec.ofNat 64 (globN s "bo")))) post
  have hgb_ofstr_ne : ∀ gn ∈ globalBuffers, gn.1 ≠ "bo" → ofString gn.1 ≠ ofString "bo" := by decide
  have hgs_fake : WorldGlobalsSame s p_fake := by
    refine ⟨fun gn hgn => ?_, fun g hg => ?_, ?_, ?_, ?_⟩
    · by_cases h1 : gn.1 = "bo"
      · rw [h1]
        obtain ⟨w, hw⟩ := hAs.2.2.2.2.2.2.2.2.2 "bo" (by decide)
        have hlt : globN s "bo" < 2 ^ 64 := by
          unfold globN; rw [hw]; exact w.isLt
        rw [show p_fake = setGlobalHOLFinite (ofString "bo") (.val (.word (BitVec.ofNat 64 (globN s "bo")))) post from rfl,
            globN_setGlobal_same, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
      · rw [globN_setGlobal_ne post (ofString "bo") _ gn.1 (hgb_ofstr_ne gn hgn h1)]
        exact hgb gn hgn h1
    · have hne : ofString g ≠ ofString "bo" := by
        simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl <;> decide
      rw [globN_setGlobal_ne post (ofString "bo") _ g hne]
      exact hgtr g hg
    · rw [globN_setGlobal_ne post (ofString "bo") _ "journal" (by decide)]; exact hj
    · rw [globN_setGlobal_ne post (ofString "bo") _ "journal_cap" (by decide)]; exact hjc
    · rw [globN_setGlobal_ne post (ofString "bo") _ "journal_n" (by decide)]; exact hjn
  have hwrs_fake_post : worldRoleSlots post = worldRoleSlots p_fake := by
    have hws_p : globN p_fake "ws" = globN post "ws" :=
      globN_setGlobal_ne post (ofString "bo") _ "ws" (by decide)
    have hbs_p : globN p_fake "bs" = globN post "bs" :=
      globN_setGlobal_ne post (ofString "bo") _ "bs" (by decide)
    have hts_p : globN p_fake "ts" = globN post "ts" :=
      globN_setGlobal_ne post (ofString "bo") _ "ts" (by decide)
    have hba_p : globN p_fake "bal_accounts" = globN post "bal_accounts" :=
      globN_setGlobal_ne post (ofString "bo") _ "bal_accounts" (by decide)
    have hbia_p : globN p_fake "bal_idx_accts" = globN post "bal_idx_accts" :=
      globN_setGlobal_ne post (ofString "bo") _ "bal_idx_accts" (by decide)
    have hbis_p : globN p_fake "bal_idx_stor" = globN post "bal_idx_stor" :=
      globN_setGlobal_ne post (ofString "bo") _ "bal_idx_stor" (by decide)
    have hmem_p : ∀ a, memW p_fake a = memW post a := fun _ => rfl
    have htv_p : ∀ t, htabValues p_fake t = htabValues post t := fun _ => rfl
    have hrec_eq : ∀ g ks, globN p_fake g = globN post g → recRoles p_fake g ks = recRoles post g ks := by
      intro g ks hg; unfold recRoles; simp [hg, hmem_p]
    have hnest_eq : ∀ g r, globN p_fake g = globN post g → nestRoles p_fake g r = nestRoles post g r := by
      intro g r hg; unfold nestRoles; simp [hg, hmem_p, htv_p]
    have hbal_r_eq : balRecords p_fake = balRecords post := by
      unfold balRecords; simp [hba_p, hmem_p]; rfl
    unfold worldRoleSlots
    rw [← hrec_eq "ws" _ hws_p, ← hrec_eq "bs" _ hbs_p, ← hrec_eq "ts" _ hts_p,
        ← hba_p, ← hbia_p, ← hbis_p,
        ← hnest_eq "bs" _ hbs_p, ← hnest_eq "ts" _ hts_p, ← hbal_r_eq]
    rfl
  have hwrs_eq : worldRoleSlots post = worldRoleSlots s :=
    hwrs_fake_post.trans (worldRoleSlots_eq_of_unhit hAs.2 hT hF hgs_fake
      hu_tab hu_ws hu_bs hu_ts hu_bal hm_low)
  have hjr_fake_post : journalRoleSlots post = journalRoleSlots p_fake := by
    have hts_p : globN p_fake "ts" = globN post "ts" :=
      globN_setGlobal_ne post (ofString "bo") _ "ts" (by decide)
    have hj_p : globN p_fake "journal" = globN post "journal" :=
      globN_setGlobal_ne post (ofString "bo") _ "journal" (by decide)
    have hjn_p : globN p_fake "journal_n" = globN post "journal_n" :=
      globN_setGlobal_ne post (ofString "bo") _ "journal_n" (by decide)
    have hrole_p : ∀ t, journalRole p_fake t = journalRole post t := by
      intro t; unfold journalRole; simp [hts_p]; rfl
    unfold journalRoleSlots
    simp [hjn_p, hj_p, hrole_p]; rfl
  have hAp_fake : ArenaReady p_fake :=
    arenaReady_setGlobal_ne hAp (ofString "bo") _ (by decide) (by decide) (by decide)
  have hag_fake : AllocatorGrows s p_fake := by
    unfold AllocatorGrows
    rw [globN_setGlobal_ne post (ofString "bo") _ "heap_ptr" (by decide),
        globN_setGlobal_ne post (ofString "bo") _ "scratch_ptr" (by decide)]
    exact hag
  have hjr_part := journalRoleSlots_eq_of_unhit hAs.1 hAp_fake.1 hAs.2 hag_fake
    (fun _ hx => hx) hJ hF hgs_fake hu_ts hu_jr
  have hjr_slots_eq : journalRoleSlots post = journalRoleSlots s :=
    hjr_fake_post.trans hjr_part.1
  have hJ_post : JournalTyped post S := by
    unfold JournalTyped at hjr_part ⊢
    have hj_p : globN p_fake "journal" = globN post "journal" :=
      globN_setGlobal_ne post (ofString "bo") _ "journal" (by decide)
    have hjc_p : globN p_fake "journal_cap" = globN post "journal_cap" :=
      globN_setGlobal_ne post (ofString "bo") _ "journal_cap" (by decide)
    have hjn_p : globN p_fake "journal_n" = globN post "journal_n" :=
      globN_setGlobal_ne post (ofString "bo") _ "journal_n" (by decide)
    have h2 := hjr_part.2
    rw [hj_p, hjc_p, hjn_p] at h2
    refine ⟨h2.1, h2.2.1, ?_, h2.2.2.2⟩
    rcases h2.2.2.1 with h0 | ⟨hal, hw⟩
    · exact Or.inl h0
    · refine Or.inr ⟨?_, wordsOK_transfer hAp_fake.1 hAp.1 hw⟩
      unfold Allocated at hal ⊢
      rwa [globN_setGlobal_ne post (ofString "bo") _ "heap_ptr" (by decide),
           globN_setGlobal_ne post (ofString "bo") _ "scratch_ptr" (by decide)] at hal
  have hnd_part := nodeHeap_congr_unhit hAs.1 hAp.1 hbe hag hTr.1 hu_nd
  have htab_fp_hdr : ∀ t ∈ S, (∀ k, k < 11 → hdr post t k = hdr s t k) ∧ htabFootprint post t = htabFootprint s t := by
    intro t ht
    have hwf := (hT.2.1 t ht).1
    have ht_fp : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
    have ht8 : t % 8 = 0 := (hwf.1 _ ht_fp).2.1
    have hhi : t + 88 ≤ 2 ^ 64 := by have := (hwf.1 _ ht_fp).1.2; omega
    exact htabFootprint_eq_of_hdr_unhit ht8 hhi (hu_tab t ht _ ht_fp)
  have hdisj_fix_post : ∀ o,
      ((∃ t ∈ S, o ∈ htabFootprint s t) ∨ o ∈ nodeExtents s Nd) →
      (∀ j ∈ fixedObjects s, Disj o j) →
      ∀ j ∈ fixedObjects post, Disj o j := by
    intro o ho_src ho_s j hj
    rw [hfix_post_decomp] at hj
    rcases List.mem_append.mp hj with hj1 | hj_bal
    · rcases List.mem_append.mp hj1 with hj2 | hj_bo_obj
      · rcases List.mem_append.mp hj2 with hj_map | hj_jr
        · rcases hmap_post_mem j hj_map with rfl | ⟨gn, hgn, _, rfl⟩
          · by_cases hpz : globN post "bo" = 0
            · simp [f_p, hpz, disj_zero_right]
            · simp only [f_p, hpz, ↓reduceIte]
              rcases (hbo_ivl hpz).2.2 with hsame | hall
              · have hs_nz : globN s "bo" ≠ 0 := hsame ▸ hpz
                simpa [f_s, hsame, hpz, hs_nz] using ho_s (f_s ("bo", 88)) (hmap_sub_fix _ hsbo_mem_map)
              · apply (hall o _).flip
                rcases ho_src with ⟨t, ht, hi⟩ | hnd
                · exact htab_sub_owned t ht o hi
                · exact hnd_sub_owned o hnd
          · exact ho_s _ (hmap_sub_fix _ (List.mem_map_of_mem hgn))
        · exact ho_s j (hjr_sub_fix j hj_jr)
      · apply (hbo_obj_disj_owned_nonbo j hj_bo_obj o _).flip
        rcases ho_src with htab | hnd
        · exact Or.inr (Or.inr (Or.inr (Or.inl htab)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr hnd)))
    · exact ho_s j (hbal_sub_fix j hj_bal)
  have hT_post : TablesTyped post S := by
    have hT_saved := hT
    obtain ⟨hndS, hTt, hTp, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, _, hroles⟩ := hT
    refine ⟨hndS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo_lst, ?_⟩
    · intro t ht
      rw [(htab_fp_hdr t ht).2]
      exact ⟨htabWF_congr_unhit hAs.1 hAp.1 (hTt t ht).1 (hu_tab t ht),
        fun i hi => ⟨hag.allocated ((hTt t ht).2 i hi).1,
          hdisj_fix_post i (Or.inl ⟨t, ht, hi⟩) ((hTt t ht).2 i hi).2⟩⟩
    · intro t ht u hu_mem hne
      rw [(htab_fp_hdr t ht).2, (htab_fp_hdr u hu_mem).2]
      exact hTp t ht u hu_mem hne
    · intro k hk hnz
      rw [hws_g] at hnz
      have hwk : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g hnz (hu_ws hnz) hwk.1 hwk.2]
      exact hwsR k hk hnz
    · intro k hk hnz
      rw [hbs_g] at hnz
      have hbk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g hnz (hu_bs hnz) hbk.1 hbk.2]
      exact hbsR k hk hnz
    · intro k hk hnz
      rw [hts_g] at hnz
      have htk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g hnz (hu_ts hnz) htk.1 htk.2]
      exact htsR k hk hnz
    · intro g hg
      rw [hgtr g hg]; exact hgR g hg
    · intro hnz hm
      rw [hbs_g] at hnz
      have hw32 := rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g hnz (hu_bs hnz) (k := 32) (by omega) (by omega)
      rw [hw32] at hm ⊢
      exact htabValuesIn_congr_unhit (hTt _ hm).1 (hu_tab _ hm) (fun _ hx => hx) (hbsN hnz hm)
    · intro hnz hm
      rw [hts_g] at hnz
      have hw32 := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g hnz (hu_ts hnz) (k := 32) (by omega) (by omega)
      rw [hw32] at hm ⊢
      exact htabValuesIn_congr_unhit (hTt _ hm).1 (hu_tab _ hm) (fun _ hx => hx) (htsN hnz hm)
    · intro ad had
      obtain ⟨h0, h8, _, hkl, hll⟩ := hbal_part.2 ad had
      have hrecs := balRecords_eq_of_unhit hT_saved hba_g (fun hnz => by
        rcases hgR "bal_accounts" (by simp [globalTableRoots]) with h0' | hm
        · exact absurd h0' hnz
        · exact hu_tab _ hm)
      rw [hrecs] at had
      have had_old := hbalT ad had
      refine ⟨by rw [h0]; exact had_old.1, by rw [h8]; exact had_old.2.1, hkl, hll⟩
    · unfold RolesOK at hroles ⊢
      rw [hwrs_eq, hjr_slots_eq]
      refine ⟨fun a ha => ?_, hroles.2.1, hroles.2.2⟩
      obtain ⟨haS, hak⟩ := hroles.1 a ha
      rw [(htab_fp_hdr a.1 haS).1 0 (by omega)]
      exact ⟨haS, hak⟩
  have hTr_post : TriesTypedWith post S Nd := by
    refine ⟨hnd_part.1, ?_, ?_⟩
    · intro o ho
      rw [hnd_part.2] at ho
      refine ⟨fun t ht i hi => ?_, hdisj_fix_post o (Or.inr ho) (hTr.2.1 o ho).2⟩
      rw [(htab_fp_hdr t ht).2] at hi
      exact (hTr.2.1 o ho).1 t ht i hi
    · intro hnz
      rw [hws_g] at hnz
      have hw24 := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g hnz (hu_ws hnz) (k := 24) (by omega) (by omega)
      have hw32 := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g hnz (hu_ws hnz) (k := 32) (by omega) (by omega)
      rw [hw24, hw32]
      obtain ⟨hr24, hr32⟩ := hTr.2.2 hnz
      refine ⟨hr24, fun hm i hi => ?_⟩
      have hwf32 := (hT.2.1 _ hm).1
      have hu32 := hu_tab _ hm
      have hh32 := htab_fp_hdr _ hm
      rw [hh32.1 3 (by omega)] at hi
      have hvals := htabValues_eq_of_unhit hwf32 hu32
      have hget : (htabValues post (memW s (globN s "ws" + 32)))[i]? =
          (htabValues s (memW s (globN s "ws" + 32)))[i]? := by rw [hvals]
      simp only [htabValues, List.getElem?_map, List.getElem?_range, hh32.1 3 (by omega), hi,
        Option.map_some, Option.some.injEq] at hget
      rw [hget]
      exact hr32 hm i hi
  refine ⟨⟨hT_post, hJ_post, hF_post, hTr_post⟩, ?_⟩
  intro o ho
  unfold worldOwned at ho
  rcases List.mem_append.mp ho with ho1 | ho_nd
  · rcases List.mem_append.mp ho1 with ho_tab | ho_fix
    · obtain ⟨t, ht, hi⟩ := List.mem_flatMap.mp ho_tab
      rw [(htab_fp_hdr t ht).2] at hi
      exact Or.inr (Or.inr (Or.inr (htab_sub_owned t ht o hi)))
    · rw [hfix_post_decomp] at ho_fix
      rcases List.mem_append.mp ho_fix with ho_f1 | ho_bal
      · rcases List.mem_append.mp ho_f1 with ho_f2 | ho_bo_obj
        · rcases List.mem_append.mp ho_f2 with ho_map | ho_jr
          · rcases hmap_post_mem o ho_map with rfl | ⟨gn, hgn, _, rfl⟩
            · by_cases hpz : globN post "bo" = 0
              · exact Or.inl (by simp [f_p, hpz])
              · exact Or.inr (Or.inl (by simp [f_p, hpz]))
            · exact Or.inr (Or.inr (Or.inr (hfix_sub_owned _ (hmap_sub_fix _ (List.mem_map_of_mem hgn)))))
          · exact Or.inr (Or.inr (Or.inr (hfix_sub_owned o (hjr_sub_fix o ho_jr))))
        · exact Or.inr (Or.inr (Or.inl ho_bo_obj))
      · exact Or.inr (Or.inr (Or.inr (hfix_sub_owned o (hbal_sub_fix o ho_bal))))
  · rw [hnd_part.2] at ho_nd
    exact Or.inr (Or.inr (Or.inr (hnd_sub_owned o ho_nd)))

theorem worldTypedWith_rebind_zero {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat}
    (hAs : ArenaReady s) (hAp : ArenaReady post) (hbe : post.be = s.be)
    (hag : AllocatorGrows s post) (hW : WorldTypedWith s S Nd)
    (hgb : ∀ gn ∈ globalBuffers, gn.1 ≠ "bo" → globN post gn.1 = globN s gn.1)
    (hgtr : ∀ g ∈ globalTableRoots, globN post g = globN s g)
    (hj : globN post "journal" = globN s "journal")
    (hjc : globN post "journal_cap" = globN s "journal_cap")
    (hjn : globN post "journal_n" = globN s "journal_n")
    (hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, IvlUnhit s post i)
    (hu_ws : globN s "ws" ≠ 0 → IvlUnhit s post (globN s "ws", 40))
    (hu_bs : globN s "bs" ≠ 0 → IvlUnhit s post (globN s "bs", 80))
    (hu_ts : globN s "ts" ≠ 0 → IvlUnhit s post (globN s "ts", 72))
    (hu_jr : globN s "journal_cap" ≠ 0 →
      IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap"))
    (hu_bal : ∀ i ∈ balObjects s, IvlUnhit s post i)
    (hu_nd : ∀ o ∈ nodeExtents s Nd, IvlUnhit s post o)
    (hm_low : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16)
    (hbo_ivl : globN post "bo" ≠ 0 →
      Allocated post (globN post "bo", 88) ∧ WordsOK post (globN post "bo", 88) ∧
      (globN post "bo" = globN s "bo" ∨
        ∀ o ∈ worldOwned s S Nd, Disj (globN post "bo", 88) o))
    (hz : ∀ off ∈ ([24, 32, 40, 56, 72] : List Nat),
      memW post (globN post "bo" + off) = 0) :
    WorldTypedWith post S Nd ∧
    ∀ o ∈ worldOwned post S Nd,
      o = (0, 0) ∨ o = (globN post "bo", 88) ∨ o ∈ worldOwned s S Nd := by
  have hobj := blockOutObjects_of_zero_slots hz
  have hpw7 : (List.replicate 7 ((0, 0) : Ivl)).Pairwise Disj :=
    List.pairwise_replicate.2 (Or.inr (Or.inl rfl))
  obtain ⟨hW', how⟩ := worldTypedWith_rebind_fixed hAs hAp hbe hag hW hgb hgtr hj hjc hjn
    hu_tab hu_ws hu_bs hu_ts hu_jr hu_bal hu_nd hm_low hbo_ivl
    (fun x hx => Or.inl (by rw [hobj, List.mem_replicate] at hx; exact hx.2))
    (by rw [hobj]; exact hpw7)
    (by
      intro _ k hk hnz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · exact False.elim (hnz (hz 40 (by simp)))
      · exact False.elim (hnz (hz 72 (by simp))))
  refine ⟨hW', fun o ho => ?_⟩
  rcases how o ho with hzero | hbo | hobjs | hold
  · exact Or.inl hzero
  · exact Or.inr (Or.inl hbo)
  · exact Or.inl (by rw [hobj, List.mem_replicate] at hobjs; exact hobjs.2)
  · exact Or.inr (Or.inr hold)

theorem trackedBlocks_rebind_fixed {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {bs : List Ivl}
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hbs : TrackedBlocks s S Nd bs)
    (how : ∀ o ∈ worldOwned post S Nd,
      o = (0, 0) ∨ o = (globN post "bo", 88) ∨
        o ∈ blockOutObjects post ∨ o ∈ worldOwned s S Nd)
    (hbo : IvlsDisj bs [(globN post "bo", 88)])
    (hobj : IvlsDisj bs (blockOutObjects post)) :
    TrackedBlocks post S Nd bs := by
  intro b hb
  obtain ⟨hb8, hn8, hin, hw, hd⟩ := hbs b hb
  refine ⟨hb8, hn8, ⟨hin.1, hin.2.trans hhp⟩,
    wordsOK_transfer hAs.1 hAp.1 hw, ?_⟩
  intro o ho
  rcases how o ho with hz | hbo' | hobj' | hold
  · rw [hz]
    exact Or.inr (Or.inl rfl)
  · rw [hbo']
    exact hbo b hb _ (by simp)
  · exact hobj b hb o hobj'
  · exact hd o hold

theorem blockContext_rebind_fixed {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si hdr : Nat}
    (h : BlockContext s S Nd si hdr)
    (hAp : ArenaReady post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hjc : globN post "journal_cap" = globN s "journal_cap")
    (hwd : globN post "wd_rlp_slices" = globN s "wd_rlp_slices")
    (hbh : globN post "block_hashes" = globN s "block_hashes")
    (hbhn : globN post "block_hashes_n" = globN s "block_hashes_n")
    (hW : WorldTypedWith post S Nd)
    (how : ∀ o ∈ worldOwned post S Nd,
      o = (0, 0) ∨ o = (globN post "bo", 88) ∨
        o ∈ blockOutObjects post ∨ o ∈ worldOwned s S Nd)
    (hregbo : IvlsDisj (inputRegions s si hdr) [(globN post "bo", 88)])
    (hregobj : IvlsDisj (inputRegions s si hdr) (blockOutObjects post))
    (hu : ∀ c ∈ inputRegions s si hdr, IvlUnhit s post c)
    (hhashbo : globN s "block_hashes_n" ≠ 0 →
      IvlsDisj [(globN s "block_hashes", 32 * globN s "block_hashes_n")]
        [(globN post "bo", 88)])
    (hhashobj : globN s "block_hashes_n" ≠ 0 →
      IvlsDisj [(globN s "block_hashes", 32 * globN s "block_hashes_n")]
        (blockOutObjects post)) :
    BlockContext post S Nd si hdr := by
  exact blockContext_transfer_unhit h hAp hhp hjc hwd hbh hbhn hW
    (trackedBlocks_rebind_fixed h.arena hAp hhp h.regions how hregbo hregobj) hu
    (fun hnz => trackedBlocks_rebind_fixed h.arena hAp hhp (h.hashes hnz) how
      (hhashbo hnz) (hhashobj hnz))

theorem trackedBlocks_pairwise_disj {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {b : Ivl} {bs : List Ivl}
    (_hb : TrackedBlocks s S Nd [b])
    (_hbs : TrackedBlocks s S Nd bs)
    (hd : ∀ x ∈ bs, Disj b x)
    (hpw : bs.Pairwise Disj) :
    (b :: bs).Pairwise Disj :=
  List.pairwise_cons.2 ⟨hd, hpw⟩

theorem disj_fresh_tracked {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {p n : Nat} {bs : List Ivl}
    (hf : FreshBlock s post p n)
    (hbs : TrackedBlocks s S Nd bs) :
    ∀ x ∈ bs, Disj x (p, (n + 7) / 8 * 8) := by
  intro x hx
  obtain ⟨_, _, hin, _, _⟩ := hbs x hx
  exact Or.inr (Or.inr (Or.inl (hin.2.trans hf.2.1.1)))

theorem ivlUnhit_of_eq_mem {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hmem : post.memory = s.memory) (c : Ivl) : IvlUnhit s post c := by
  intro a _ _
  simp [hmem]

theorem memW_word_store_same {F : Type} {s : PanSemStateFiniteExact 64 F}
    {x w : BitVec 64} {mem' : BitVec 64 → HolWordLab 64}
    (hsame : mem' x = .word w) :
    memW {s with memory := mem'} x.toNat = w.toNat := by
  simp [memW, BitVec.ofNat_toNat, hsame]

theorem memW_word_store_ne {F : Type} {s : PanSemStateFiniteExact 64 F}
    {x : BitVec 64} {mem' : BitVec 64 → HolWordLab 64} {a : Nat}
    (hframe : ∀ b : BitVec 64, b ≠ x → mem' b = s.memory b)
    (ha_lt : a < 2 ^ 64)
    (hne : a ≠ x.toNat) :
    memW {s with memory := mem'} a = memW s a := by
  have hne_bv : BitVec.ofNat 64 a ≠ x := by
    intro heq
    apply hne
    have h1 := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
    exact h1
  simp [memW, hframe _ hne_bv]

theorem ivlUnhit_of_memzero_frame {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {p n : Nat} {i : Ivl}
    (hA : ArenaReady s)
    (hp8 : p % 8 = 0) (hn8 : n % 8 = 0)
    (hi8 : i.1 % 8 = 0)
    (hin : Inside i sourceBase (globN s "heap_ptr"))
    (hd : Disj i (p, n))
    (hfr : FrameOutside s post
      ([(p, n)] ++ [(globN s "frame_mem_ptr",
        globN s "scratch_ptr" - globN s "frame_mem_ptr")])
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr")) :
    IvlUnhit s post i := by
  have hsep : heapLimit ≤ scratchStart := by decide
  have hhl8 : heapLimit % 8 = 0 := by decide
  obtain ⟨_, hhp, hfm, hfmsc, _, hhp8, hfm8, hsc8, _⟩ := hA.2
  apply ivlUnhit_of_frameOutside_aligned hfr (fun _ => hi8)
  · intro j hj
    simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact ⟨hp8, hn8⟩
    · exact ⟨hfm8, by dsimp; omega⟩
  · exact ⟨hhp8, by dsimp; omega⟩
  · intro j hj
    simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact hd
    · exact Or.inr (Or.inr (Or.inl (hin.2.trans (hhp.trans (hsep.trans hfm)))))
  · exact Or.inr (Or.inr (Or.inl hin.2))

theorem trackedBlocks_unhit_memzero {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {bs : List Ivl} {p n : Nat}
    (hA : ArenaReady s) (hbs : TrackedBlocks s S Nd bs)
    (hp8 : p % 8 = 0) (hn8 : n % 8 = 0)
    (hd : IvlsDisj bs [(p, n)])
    (hfr : FrameOutside s post
      ([(p, n)] ++ [(globN s "frame_mem_ptr",
        globN s "scratch_ptr" - globN s "frame_mem_ptr")])
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr")) :
    ∀ i ∈ bs, IvlUnhit s post i := by
  intro i hi
  obtain ⟨hi8, _, hin, _, _⟩ := hbs i hi
  exact ivlUnhit_of_memzero_frame hA hp8 hn8 hi8 hin
    (hd i hi (p, n) (by simp)) hfr

theorem worldOwned_unhit_alloc_memzero {F : Type}
    {s bpost s2 : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {p n : Nat}
    (hAs : ArenaReady s) (hW : WorldTypedWith s S Nd)
    (hAb : ArenaReady bpost)
    (hag_b : AllocatorGrows s bpost)
    (hf : FreshBlock s bpost p n)
    (hmem_b : bpost.memory = s.memory)
    (hn8 : n % 8 = 0)
    (hfr : FrameOutside bpost s2
      ([(p, n)] ++ [(globN bpost "frame_mem_ptr",
        globN bpost "scratch_ptr" - globN bpost "frame_mem_ptr")])
      (globN bpost "heap_ptr", heapLimit - globN bpost "heap_ptr")) :
    ∀ j ∈ worldOwned s S Nd, IvlUnhit s s2 j := by
  have hsep : heapLimit ≤ scratchStart := by decide
  have hhl8 : heapLimit % 8 = 0 := by decide
  obtain ⟨hp8, ⟨hfb_lo, hfb_hi⟩, _⟩ := hf
  have hhp_b := hag_b.1
  have hsc_b := hag_b.2
  have hn_round : n ≤ (n + 7) / 8 * 8 := by omega
  dsimp only at hfb_lo hfb_hi
  obtain ⟨_, hs_hp, hs_fm, hs_sc, _⟩ := hAs.2
  obtain ⟨_, hb_hp, hb_fm, hb_sc, _, hb_hp8, hb_fm8, hb_sc8, _⟩ := hAb.2
  intro j hj
  have hj_za := worldOwned_zero_or_allocated hW j hj
  have hj_z : j.2 = 0 → j.1 % 8 = 0 := worldOwned_zero_aligned hW j hj
  have hu_b : IvlUnhit bpost s2 j := by
    apply ivlUnhit_of_frameOutside_aligned hfr hj_z
    · intro k hk
      simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · exact ⟨hp8, hn8⟩
      · exact ⟨hb_fm8, by dsimp; omega⟩
    · exact ⟨hb_hp8, by dsimp; omega⟩
    · intro k hk
      simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · rcases hj_za with rfl | ⟨_, ⟨_, hhi⟩ | ⟨hlo, _⟩⟩
        · exact disj_zero_left _
        · exact Or.inr (Or.inr (Or.inl (by dsimp; omega)))
        · exact Or.inr (Or.inr (Or.inr (by dsimp; omega)))
      · rcases hj_za with rfl | ⟨_, ⟨_, hhi⟩ | ⟨hlo, _⟩⟩
        · exact disj_zero_left _
        · exact Or.inr (Or.inr (Or.inl (by dsimp; omega)))
        · exact Or.inr (Or.inr (Or.inr (by dsimp; omega)))
    · rcases hj_za with rfl | ⟨_, ⟨_, hhi⟩ | ⟨hlo, _⟩⟩
      · exact disj_zero_left _
      · exact Or.inr (Or.inr (Or.inl (by dsimp; omega)))
      · exact Or.inr (Or.inr (Or.inr (by dsimp; omega)))
  intro a ha8 hhit
  rw [hu_b a ha8 hhit, hmem_b]

theorem blockContext_alloc_bo_memzero {F : Type}
    {s bpost s2 : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si hdr : Nat} {w_bo : BitVec 64}
    (h : BlockContext s S Nd si hdr)
    (hAb : ArenaReady bpost)
    (hag_b : AllocatorGrows s bpost)
    (hf : FreshBlock s bpost w_bo.toNat 88)
    (hmem_b : bpost.memory = s.memory)
    (hbe_b : bpost.be = s.be)
    (hg_b : ∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = bpost.globals.lookup k)
    (hA2 : ArenaReady s2)
    (hbe_2 : s2.be = bpost.be)
    (hhp2 : globN bpost "heap_ptr" ≤ globN s2 "heap_ptr")
    (hsc2 : globN s2 "scratch_ptr" ≤ globN bpost "scratch_ptr")
    (hg_2 : ∀ k : MlS,
      (setGlobalHOLFinite (ofString "bo") (.val (.word w_bo)) bpost).globals.lookup k =
        s2.globals.lookup k)
    (hfr : FrameOutside bpost s2
      ([(w_bo.toNat, 88)] ++ [(globN bpost "frame_mem_ptr",
        globN bpost "scratch_ptr" - globN bpost "frame_mem_ptr")])
      (globN bpost "heap_ptr", heapLimit - globN bpost "heap_ptr"))
    (hzf : ∀ a, w_bo.toNat ≤ a → a + 8 ≤ w_bo.toNat + 88 → a % 8 = 0 → memW s2 a = 0) :
    BlockContext s2 S Nd si hdr ∧
      globN s2 "bo" = w_bo.toNat ∧
      globN s2 "bo" ≠ 0 ∧
      (∀ off ∈ ([0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80] : List Nat),
        memW s2 (w_bo.toNat + off) = 0) := by
  have hsep : heapLimit ≤ scratchStart := by decide
  have hhl8 : heapLimit % 8 = 0 := by decide
  have hsb_pos : 0 < sourceBase := by decide
  obtain ⟨hbo8, hbo_in, hbo_words_b⟩ := hf
  have hf : FreshBlock s bpost w_bo.toNat 88 := ⟨hbo8, hbo_in, hbo_words_b⟩
  have hbo_bound : w_bo.toNat + 88 ≤ globN bpost "heap_ptr" := hbo_in.2
  have hb_lo := hAb.2.1
  have hb_hi := hAb.2.2.1
  have hb_frame := hAb.2.2.2.1
  have hs_frame := h.arena.2.2.2.1
  have hs_gap := h.arena.2.2.2.2.1
  have hsc_b := hag_b.2
  have hbo_pos : 0 < w_bo.toNat := lt_of_lt_of_le hsb_pos (h.arena.2.1.trans hbo_in.1)
  have hbo_nz : w_bo.toNat ≠ 0 := Nat.ne_of_gt hbo_pos
  have hbo_g2 : globN s2 "bo" = w_bo.toNat := by
    have h1 := globN_eq_of_lookup (hg_2 (ofString "bo"))
    rw [globN_setGlobal_same] at h1
    exact h1
  have hg_ne : ∀ (n : String), ofString n ≠ ofString "bo" →
      ofString n ≠ ofString "heap_ptr" → globN s2 n = globN s n := by
    intro n hne_bo hne_hp
    have h1 := globN_eq_of_lookup (hg_2 (ofString n))
    rw [globN_setGlobal_ne _ _ _ n hne_bo] at h1
    exact h1.trans (globN_eq_of_lookup (hg_b (ofString n) hne_hp))
  have hag : AllocatorGrows s s2 := ⟨hag_b.1.trans hhp2, hsc2.trans hsc_b⟩
  have hu_ow := worldOwned_unhit_alloc_memzero h.arena h.world hAb hag_b hf hmem_b
    (by decide) hfr
  have hu_ti : ∀ i ∈ worldTypedIvls s S Nd, IvlUnhit s s2 i :=
    fun i hi => hu_ow i (worldTypedIvls_sub_worldOwned s S Nd i hi)
  have hm_low : memW s2 8 = memW s 8 ∧ memW s2 16 = memW s 16 := by
    have hsb16 : 24 ≤ sourceBase := by decide
    have hlow_unhit : ∀ a : Nat, a + 8 ≤ sourceBase → a % 8 = 0 → memW s2 a = memW s a := by
      intro a ha_sb ha8
      have ha_lt : a < 2 ^ 64 := lt_of_lt_of_le (by omega) (show sourceBase ≤ 2 ^ 64 by decide)
      have hbv_nat : (BitVec.ofNat 64 a).toNat = a := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
      have hmem2 : s2.memory (BitVec.ofNat 64 a) = bpost.memory (BitVec.ofNat 64 a) := by
        apply hfr (BitVec.ofNat 64 a)
        · intro j hj hcj
          simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hj
          rcases hj with rfl | rfl
          · obtain ⟨hc1, hc2⟩ := hcj
            have := h.arena.2.1
            have := hbo_in.1
            dsimp at hc1 hc2; omega
          · obtain ⟨hc1, hc2⟩ := hcj
            dsimp at hc1 hc2; omega
        · intro ⟨hf1, hf2⟩
          dsimp at hf1 hf2; omega
      unfold memW
      rw [hmem2, hmem_b]
    exact ⟨hlow_unhit 8 (by omega) (by omega), hlow_unhit 16 (by omega) (by omega)⟩
  have hbo_in88 : Inside (w_bo.toNat, 88) (globN s "heap_ptr") (globN bpost "heap_ptr") :=
    hbo_in
  have hbo_alloc2 : Allocated s2 (w_bo.toNat, 88) :=
    Or.inl ⟨h.arena.2.1.trans hbo_in88.1, hbo_bound.trans hhp2⟩
  have hbo_words2 : WordsOK s2 (w_bo.toNat, 88) :=
    wordsOK_transfer hAb.1 hA2.1 hbo_words_b
  have hbo_disj_ow : ∀ o ∈ worldOwned s S Nd, Disj (w_bo.toNat, 88) o := by
    intro o ho
    rcases worldOwned_zero_or_allocated h.world o ho with rfl | ⟨_, ⟨_, hhi⟩ | ⟨hlo, _⟩⟩
    · exact disj_zero_right _
    · exact Or.inr (Or.inr (Or.inr (hhi.trans hbo_in88.1)))
    · exact Or.inr (Or.inr (Or.inl (by dsimp; omega)))
  have hz_all : ∀ off ∈ ([0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80] : List Nat),
      memW s2 (w_bo.toNat + off) = 0 := by
    intro off hoff
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hzf (w_bo.toNat + _) (by omega) (by omega) (by omega)
  obtain ⟨hW2, how2⟩ := worldTypedWith_rebind_zero h.arena hA2 (hbe_2.trans hbe_b) hag h.world
    (fun gn hgn hne => hg_ne gn.1
      (fun heq => by
        simp only [globalBuffers, List.mem_cons, List.not_mem_nil, or_false] at hgn
        rcases hgn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | exact absurd rfl hne | exact absurd heq (by decide))
      (by simp only [globalBuffers, List.mem_cons, List.not_mem_nil, or_false] at hgn
          rcases hgn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
    (fun g hg => hg_ne g
      (by simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg
          rcases hg with rfl | rfl | rfl <;> decide)
      (by simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg
          rcases hg with rfl | rfl | rfl <;> decide))
    (hg_ne "journal" (by decide) (by decide))
    (hg_ne "journal_cap" (by decide) (by decide))
    (hg_ne "journal_n" (by decide) (by decide))
    (fun t ht i hi => hu_ti i (by
      unfold worldTypedIvls
      exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl
        (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨t, ht, hi⟩))))))))))))
    (fun hnz => hu_ow _ (by
      have hm := typedRecord_mem_fixedObjects s (r := ("ws", 40)) (by decide)
      rw [if_neg hnz] at hm
      unfold worldOwned
      exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hm)))))
    (fun hnz => hu_ow _ (by
      have hm := typedRecord_mem_fixedObjects s (r := ("bs", 80)) (by decide)
      rw [if_neg hnz] at hm
      unfold worldOwned
      exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hm)))))
    (fun hnz => hu_ow _ (by
      have hm := typedRecord_mem_fixedObjects s (r := ("ts", 72)) (by decide)
      rw [if_neg hnz] at hm
      unfold worldOwned
      exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hm)))))
    (fun hnz => hu_ti _ (by
      unfold worldTypedIvls
      exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl
        (List.mem_append.2 (Or.inr (by simp [hnz]))))))))))
    (fun i hi => hu_ti i (by
      unfold worldTypedIvls
      exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hi)))))
    (fun o ho => hu_ti o (by
      unfold worldTypedIvls
      exact List.mem_append.2 (Or.inr ho)))
    hm_low
    (fun _ => by
      rw [hbo_g2]
      exact ⟨hbo_alloc2, hbo_words2, Or.inr hbo_disj_ow⟩)
    (fun off hoff => by
      rw [hbo_g2]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl | rfl | rfl <;>
        exact hz_all _ (by simp))
  have hobj2_zero : blockOutObjects s2 = List.replicate 7 (0, 0) := by
    apply blockOutObjects_of_zero_slots
    intro off hoff
    rw [hbo_g2]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl | rfl | rfl | rfl <;> exact hz_all _ (by simp)
  have hreg_disj_bo : IvlsDisj (inputRegions s si hdr) [(globN s2 "bo", 88)] := by
    rw [hbo_g2]
    intro c hc y hy
    simp only [List.mem_singleton] at hy; subst hy
    exact disj_fresh_tracked hf h.regions c hc
  have hreg_disj_obj : IvlsDisj (inputRegions s si hdr) (blockOutObjects s2) := by
    rw [hobj2_zero]
    intro c _ y hy
    rw [List.mem_replicate] at hy
    rw [hy.2]; exact disj_zero_right c
  have hu_reg : ∀ c ∈ inputRegions s si hdr, IvlUnhit s s2 c := by
    intro c hc
    obtain ⟨hc8, _, hcin, _, _⟩ := h.regions c hc
    have hu_b : IvlUnhit bpost s2 c := ivlUnhit_of_memzero_frame hAb hbo8 (by decide) hc8
      ⟨hcin.1, hcin.2.trans hag_b.1⟩ (disj_fresh_tracked hf h.regions c hc) hfr
    intro a ha8 hhit
    rw [hu_b a ha8 hhit, hmem_b]
  have hhash_disj_bo : globN s "block_hashes_n" ≠ 0 →
      IvlsDisj [(globN s "block_hashes", 32 * globN s "block_hashes_n")] [(globN s2 "bo", 88)] := by
    intro hnz x hx y hy
    rw [hbo_g2] at hy
    simp only [List.mem_singleton] at hy; subst hy
    exact disj_fresh_tracked hf (h.hashes hnz) x hx
  have hhash_disj_obj : globN s "block_hashes_n" ≠ 0 →
      IvlsDisj [(globN s "block_hashes", 32 * globN s "block_hashes_n")] (blockOutObjects s2) := by
    rw [hobj2_zero]
    intro _ x _ y hy
    rw [List.mem_replicate] at hy
    rw [hy.2]; exact disj_zero_right x
  have hctx2 : BlockContext s2 S Nd si hdr :=
    blockContext_rebind_fixed h hA2 hag.1
      (hg_ne "journal_cap" (by decide) (by decide))
      (hg_ne "wd_rlp_slices" (by decide) (by decide))
      (hg_ne "block_hashes" (by decide) (by decide))
      (hg_ne "block_hashes_n" (by decide) (by decide))
      hW2
      (fun o ho => by
        rcases how2 o ho with hz | hbo | hold
        · exact Or.inl hz
        · exact Or.inr (Or.inl hbo)
        · exact Or.inr (Or.inr (Or.inr hold)))
      hreg_disj_bo hreg_disj_obj hu_reg hhash_disj_bo hhash_disj_obj
  exact ⟨hctx2, hbo_g2, by rw [hbo_g2]; exact hbo_nz, hz_all⟩

theorem bo_in_worldOwned {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hbo_nz : globN s "bo" ≠ 0) :
    (globN s "bo", 88) ∈ worldOwned s S Nd := by
  have hmem : (globN s "bo", if globN s "bo" = 0 then 0 else 88) ∈
      globalBuffers.map (fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) :=
    List.mem_map_of_mem (by simp [globalBuffers] : ("bo", 88) ∈ globalBuffers)
  simp only [hbo_nz, ↓reduceIte] at hmem
  unfold worldOwned fixedObjects
  exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr
    (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl hmem)))))))))

theorem bo_allocated_wordsOK {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hA : ArenaOK s) (hW : WorldTypedWith s S Nd) (hbo_nz : globN s "bo" ≠ 0) :
    Allocated s (globN s "bo", 88) ∧ WordsOK s (globN s "bo", 88) ∧
      globN s "bo" % 8 = 0 ∧ globN s "bo" + 88 ≤ 2 ^ 64 := by
  have hmem : (globN s "bo", if globN s "bo" = 0 then 0 else 88) ∈
      globalBuffers.map (fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) :=
    List.mem_map_of_mem (by simp [globalBuffers] : ("bo", 88) ∈ globalBuffers)
  simp only [hbo_nz, ↓reduceIte] at hmem
  have hfix : (globN s "bo", 88) ∈ fixedObjects s := by
    unfold fixedObjects
    exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl hmem)))))
  rcases hW.2.2.1.1 _ hfix with hz | ⟨hal, hw⟩
  · cases hz
  · have hbound := (ivl_allocated_bound hA hal).2
    exact ⟨hal, hw, hw.1, hbound⟩

theorem bo_disj_worldOwned_nonbo {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hW : WorldTypedWith s S Nd) (hbo_nz : globN s "bo" ≠ 0) :
    ∀ j ∈ worldOwned s S Nd, j ≠ (globN s "bo", 88) → Disj (globN s "bo", 88) j := by
  obtain ⟨hT, _, hF, hTr⟩ := hW
  let f_s : String × Nat → Ivl := fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)
  let jr_s : List Ivl := [(if globN s "journal_cap" = 0 then 0 else globN s "journal",
    32 * globN s "journal_cap")]
  have hsbo_mem : f_s ("bo", 88) ∈ globalBuffers.map f_s :=
    List.mem_map_of_mem (by simp [globalBuffers] : ("bo", 88) ∈ globalBuffers)
  have hsbo_eq : f_s ("bo", 88) = (globN s "bo", 88) := by simp [f_s, hbo_nz]
  have hbo_fix : (globN s "bo", 88) ∈ fixedObjects s := by
    rw [← hsbo_eq]
    unfold fixedObjects
    exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl hsbo_mem)))))
  have hF_parts := (pairwise_disj_append_4 (a1 := globalBuffers.map f_s) (a2 := jr_s)
    (b := blockOutObjects s) (c := balObjects s)).mp
    (by simpa [fixedObjects, f_s, jr_s] using hF.2)
  have hgb_nodup : globalBuffers.Nodup := by decide
  intro j hj hne
  unfold worldOwned at hj
  rcases List.mem_append.1 hj with h1 | hnd
  · rcases List.mem_append.1 h1 with htab | hfix
    · obtain ⟨t, ht, hi⟩ := List.mem_flatMap.1 htab
      exact (((hT.2.1 t ht).2 j hi).2 _ hbo_fix).flip
    · unfold fixedObjects at hfix
      rcases List.mem_append.1 hfix with hf1 | hbal
      · rcases List.mem_append.1 hf1 with hf2 | hbo_obj
        · rcases List.mem_append.1 hf2 with hmap | hjr
          · rw [← hsbo_eq]
            obtain ⟨i1, hi1, heq1⟩ := List.mem_iff_getElem.1 hsbo_mem
            obtain ⟨i2, hi2, heq2⟩ := List.mem_iff_getElem.1 hmap
            have hij : i1 ≠ i2 := by
              intro hij; subst hij
              rw [heq1, hsbo_eq] at heq2
              exact hne heq2.symm
            rw [← heq1, ← heq2]
            exact list_pairwise_rel (fun _ _ h => h.flip) hF_parts.1.1 hi1 hi2 hij
          · rw [← hsbo_eq]
            exact hF_parts.2.1 _ hsbo_mem j (List.mem_append_left _ hjr)
        · rw [← hsbo_eq]
          exact hF_parts.2.1 _ hsbo_mem j (List.mem_append_right _ (List.mem_append_left _ hbo_obj))
      · rw [← hsbo_eq]
        exact hF_parts.2.1 _ hsbo_mem j (List.mem_append_right _ (List.mem_append_right _ hbal))
  · exact ((hTr.2.1 j hnd).2 _ hbo_fix).flip

theorem blockContext_word_store_bo {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {si hdr off : Nat}
    {x w : BitVec 64} {mem' : BitVec 64 → HolWordLab 64} {bs : List Ivl}
    (h : BlockContext s S Nd si hdr)
    (hbs : TrackedBlocks s S Nd bs)
    (hbo_nz : globN s "bo" ≠ 0)
    (hoff8 : off % 8 = 0) (hoff_lt : off + 8 ≤ 88)
    (hx_eq : x.toNat = globN s "bo" + off)
    (hsame : mem' x = .word w)
    (hframe : ∀ a : BitVec 64, a ≠ x → mem' a = s.memory a)
    (hbo_objs : ∀ o ∈ blockOutObjects {s with memory := mem'},
      o = (0, 0) ∨ (Allocated {s with memory := mem'} o ∧
        WordsOK {s with memory := mem'} o ∧
        Disj o (globN s "bo", 88) ∧
        (o ∈ blockOutObjects s ∨ ∀ j ∈ worldOwned s S Nd, j ∉ blockOutObjects s → Disj o j)))
    (hbo_pw : (blockOutObjects {s with memory := mem'}).Pairwise Disj)
    (hbo_lst : ∀ k ∈ ([40, 72] : List Nat),
      memW {s with memory := mem'} (globN s "bo" + k) ≠ 0 →
        LstOK {s with memory := mem'} (memW {s with memory := mem'} (globN s "bo" + k)))
    (hobj_bs : IvlsDisj (inputRegions s si hdr ++
        (if globN s "block_hashes_n" = 0 then []
         else [(globN s "block_hashes", 32 * globN s "block_hashes_n")]) ++ bs)
      (blockOutObjects {s with memory := mem'})) :
    let post := {s with memory := mem'}
    BlockContext post S Nd si hdr ∧ TrackedBlocks post S Nd bs := by
  intro post
  have hAp : ArenaReady post := ⟨guestInv_congr (s := s) rfl rfl rfl rfl h.arena.1, h.arena.2⟩
  obtain ⟨hal_bo, hw_bo, hbo8, hbo_hi⟩ := bo_allocated_wordsOK h.arena.2 h.world hbo_nz
  have hx_in_bo : Inside (x.toNat, 8) (globN s "bo") (globN s "bo" + 88) := by
    unfold Inside; dsimp; omega
  have hdisj_nonbo : ∀ j ∈ worldOwned s S Nd, j ≠ (globN s "bo", 88) → Disj j (x.toNat, 8) := by
    intro j hj hne
    exact (disj_of_inside_left hx_in_bo (bo_disj_worldOwned_nonbo h.world hbo_nz j hj hne)).flip
  have hu_nonbo : ∀ j ∈ worldOwned s S Nd, j ≠ (globN s "bo", 88) → IvlUnhit s post j := by
    intro j hj hne
    exact ivlUnhit_of_single_cell_disj (worldOwned_zero_aligned h.world j hj)
      hframe (hdisj_nonbo j hj hne)
  have hgb_neq_bo : ∀ (g : String) (sz : Nat), (g, sz) ∈ typedRecords → g ≠ "bo" →
      globN s g ≠ 0 → (globN s g, sz) ∈ worldOwned s S Nd ∧ (globN s g, sz) ≠ (globN s "bo", 88) := by
    intro g sz htr hne hnz
    have hfix := typedRecord_mem_fixedObjects s htr
    simp only [hnz, ↓reduceIte] at hfix
    have how : (globN s g, sz) ∈ worldOwned s S Nd := by
      unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))
    have hsz_ne : sz ≠ 88 := by
      simp only [typedRecords, List.mem_cons, List.not_mem_nil, or_false] at htr
      rcases htr with h1 | h2 | h3 | hbo_eq
      · have := (Prod.mk.inj h1).2; omega
      · have := (Prod.mk.inj h2).2; omega
      · have := (Prod.mk.inj h3).2; omega
      · exact absurd (Prod.mk.inj hbo_eq).1 hne
    exact ⟨how, fun heq => hsz_ne (Prod.mk.inj heq).2⟩
  have hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, IvlUnhit s post i := by
    intro t ht i hi
    have how : i ∈ worldOwned s S Nd := by
      unfold worldOwned
      exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨t, ht, hi⟩))))
    have hne : i ≠ (globN s "bo", 88) := by
      intro heq
      have hbo_fix : (globN s "bo", 88) ∈ fixedObjects s := by
        have hm : (globN s "bo", if globN s "bo" = 0 then 0 else 88) ∈
            globalBuffers.map (fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) :=
          List.mem_map_of_mem (by simp [globalBuffers] : ("bo", 88) ∈ globalBuffers)
        simp only [hbo_nz, ↓reduceIte] at hm
        unfold fixedObjects
        exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl hm)))))
      have hd := ((h.world.1.2.1 t ht).2 i hi).2 _ hbo_fix
      rw [heq] at hd
      unfold Disj at hd; dsimp at hd; omega
    exact hu_nonbo i how hne
  have hu_jr : globN s "journal_cap" ≠ 0 →
      IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap") := by
    intro hjc
    have hjr_fix : (globN s "journal", 32 * globN s "journal_cap") ∈ fixedObjects s := by
      unfold fixedObjects
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
      simp [hjc]
    have how : (globN s "journal", 32 * globN s "journal_cap") ∈ worldOwned s S Nd := by
      unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hjr_fix)))
    have hne : (globN s "journal", 32 * globN s "journal_cap") ≠ (globN s "bo", 88) := by
      intro heq
      have := Prod.mk.inj heq
      omega
    exact hu_nonbo _ how hne
  have hu_bal : ∀ i ∈ balObjects s, IvlUnhit s post i := by
    intro i hi
    have hbal_fix : i ∈ fixedObjects s := by
      unfold fixedObjects; exact List.mem_append.2 (Or.inr hi)
    have how : i ∈ worldOwned s S Nd := by
      unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hbal_fix)))
    have hne : i ≠ (globN s "bo", 88) := by
      intro heq
      let f_s : String × Nat → Ivl := fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)
      let jr_s : List Ivl := [(if globN s "journal_cap" = 0 then 0 else globN s "journal",
        32 * globN s "journal_cap")]
      have hF_parts := (pairwise_disj_append_4 (a1 := globalBuffers.map f_s) (a2 := jr_s)
        (b := blockOutObjects s) (c := balObjects s)).mp
        (by simpa [fixedObjects, f_s, jr_s] using h.world.2.2.1.2)
      have hsbo_mem : f_s ("bo", 88) ∈ globalBuffers.map f_s :=
        List.mem_map_of_mem (by simp [globalBuffers] : ("bo", 88) ∈ globalBuffers)
      have hd := hF_parts.2.1 _ hsbo_mem i (List.mem_append_right _ (List.mem_append_right _ hi))
      simp only [f_s, hbo_nz, ↓reduceIte, heq] at hd
      unfold Disj at hd; dsimp at hd; omega
    exact hu_nonbo i how hne
  have hu_nd : ∀ o ∈ nodeExtents s Nd, IvlUnhit s post o := by
    intro o ho
    have how : o ∈ worldOwned s S Nd := by
      unfold worldOwned; exact List.mem_append.2 (Or.inr ho)
    have hne : o ≠ (globN s "bo", 88) := by
      intro heq
      have hbo_fix : (globN s "bo", 88) ∈ fixedObjects s := by
        have hm : (globN s "bo", if globN s "bo" = 0 then 0 else 88) ∈
            globalBuffers.map (fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) :=
          List.mem_map_of_mem (by simp [globalBuffers] : ("bo", 88) ∈ globalBuffers)
        simp only [hbo_nz, ↓reduceIte] at hm
        unfold fixedObjects
        exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl hm)))))
      have hd := (h.world.2.2.2.2.1 o ho).2 _ hbo_fix
      rw [heq] at hd
      unfold Disj at hd; dsimp at hd; omega
    exact hu_nonbo o how hne
  have hm_low : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 := by
    have hbo_lo : sourceBase ≤ globN s "bo" := by
      rcases hal_bo with ⟨hlo, _⟩ | ⟨hlo, _⟩
      · exact hlo
      · have hsep : heapLimit ≤ scratchStart := by decide
        have := h.arena.2.1; have := h.arena.2.2.1; have := h.arena.2.2.2.1; have := h.arena.2.2.2.2.1
        omega
    have hsb24 : 24 ≤ sourceBase := by decide
    exact ⟨memW_word_store_ne hframe (by decide) (by omega),
           memW_word_store_ne hframe (by decide) (by omega)⟩
  have hw_bo_post : WordsOK post (globN s "bo", 88) := by
    refine ⟨hw_bo.1, hw_bo.2.1, fun k hk => ?_⟩
    obtain ⟨wk, hdom_k, hwk⟩ := hw_bo.2.2 k hk
    by_cases hkx : BitVec.ofNat 64 (globN s "bo" + 8 * k) = x
    · exact ⟨w, hdom_k, by dsimp [post]; rw [hkx, hsame]⟩
    · exact ⟨wk, hdom_k, by dsimp [post]; rw [hframe _ hkx]; exact hwk⟩
  obtain ⟨hW_post, how_post⟩ := worldTypedWith_rebind_fixed h.arena hAp rfl ⟨le_rfl, le_rfl⟩ h.world
    (fun _ _ _ => rfl) (fun _ _ => rfl) rfl rfl rfl
    hu_tab
    (fun hnz => by obtain ⟨ho, hn⟩ := hgb_neq_bo "ws" 40 (by simp [typedRecords]) (by decide) hnz; exact hu_nonbo _ ho hn)
    (fun hnz => by obtain ⟨ho, hn⟩ := hgb_neq_bo "bs" 80 (by simp [typedRecords]) (by decide) hnz; exact hu_nonbo _ ho hn)
    (fun hnz => by obtain ⟨ho, hn⟩ := hgb_neq_bo "ts" 72 (by simp [typedRecords]) (by decide) hnz; exact hu_nonbo _ ho hn)
    hu_jr hu_bal hu_nd hm_low
    (fun _ => ⟨hal_bo, hw_bo_post, Or.inl rfl⟩)
    (fun o ho => by
      rcases hbo_objs o ho with rfl | ⟨hal, hw, hd, hcase⟩
      · exact Or.inl rfl
      · refine Or.inr ⟨hal, hw, hd, ?_⟩
        rcases hcase with hold | hall
        · exact Or.inl ⟨hold, rfl⟩
        · exact Or.inr hall)
    hbo_pw
    (fun _ k hk hnz => hbo_lst k hk hnz)
  have hbo_mem_ow := bo_in_worldOwned (S := S) (Nd := Nd) hbo_nz
  have htb_disj_bo : ∀ {cs : List Ivl}, TrackedBlocks s S Nd cs →
      IvlsDisj cs [(globN post "bo", 88)] := by
    intro cs hcs b hb y hy
    rw [List.mem_singleton.mp hy]
    exact (hcs b hb).2.2.2.2 _ hbo_mem_ow
  have hu_tb : ∀ {cs : List Ivl}, TrackedBlocks s S Nd cs → ∀ c ∈ cs, IvlUnhit s post c := by
    intro cs hcs c hc
    obtain ⟨hc8, _, _, _, hd_ow⟩ := hcs c hc
    have hd_x : Disj c (x.toNat, 8) :=
      (disj_of_inside_left hx_in_bo (hd_ow _ hbo_mem_ow).flip).flip
    exact ivlUnhit_of_single_cell_disj (fun _ => hc8) hframe hd_x
  have hctx_post : BlockContext post S Nd si hdr :=
    blockContext_rebind_fixed h hAp le_rfl rfl rfl rfl rfl hW_post how_post
      (htb_disj_bo h.regions)
      (fun c hc o ho => hobj_bs c (List.mem_append_left _ (List.mem_append_left _ hc)) o ho)
      (hu_tb h.regions)
      (fun hnz => htb_disj_bo (h.hashes hnz))
      (fun hnz c hc o ho => hobj_bs c
        (List.mem_append_left _ (List.mem_append_right _ (by simpa [hnz] using hc))) o ho)
  have hbs_post : TrackedBlocks post S Nd bs :=
    trackedBlocks_rebind_fixed h.arena hAp le_rfl hbs how_post
      (htb_disj_bo hbs)
      (fun b hb o ho => hobj_bs b (List.mem_append_right _ hb) o ho)
  exact ⟨hctx_post, hbs_post⟩

theorem tracked_disj_bo {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {b : Ivl}
    (hb : TrackedBlocks s S Nd [b]) (hbo_nz : globN s "bo" ≠ 0) :
    Disj b (globN s "bo", 88) :=
  (hb b (by simp)).2.2.2.2 _ (bo_in_worldOwned hbo_nz)

theorem tracked_alloc_words_post {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {b : Ivl} {x : BitVec 64} {mem' : BitVec 64 → HolWordLab 64}
    (hA : ArenaReady s) (hb : TrackedBlocks s S Nd [b]) (hbo_nz : globN s "bo" ≠ 0)
    {off : Nat} (hoff_lt : off + 8 ≤ 88) (hx_eq : x.toNat = globN s "bo" + off)
    (hframe : ∀ a : BitVec 64, a ≠ x → mem' a = s.memory a) :
    let post := {s with memory := mem'}
    Allocated post b ∧ WordsOK post b ∧ Disj b (globN s "bo", 88) ∧
      (∀ j ∈ worldOwned s S Nd, Disj b j) ∧ IvlUnhit s post b := by
  intro post
  obtain ⟨hb8, _, hin, hw_s, hd_ow⟩ := hb b (by simp)
  have hAp : ArenaReady post := ⟨guestInv_congr (s := s) rfl rfl rfl rfl hA.1, hA.2⟩
  have hal : Allocated post b := Or.inl hin
  have hw_p : WordsOK post b := wordsOK_transfer hA.1 hAp.1 hw_s
  have hd_bo : Disj b (globN s "bo", 88) := hd_ow _ (bo_in_worldOwned hbo_nz)
  have hx_in_bo : Inside (x.toNat, 8) (globN s "bo") (globN s "bo" + 88) := by
    unfold Inside; dsimp; omega
  have hd_x : Disj b (x.toNat, 8) := (disj_of_inside_left hx_in_bo hd_bo.flip).flip
  have hu : IvlUnhit s post b := ivlUnhit_of_single_cell_disj (fun _ => hb8) hframe hd_x
  exact ⟨hal, hw_p, hd_bo, hd_ow, hu⟩

theorem memW_bo_store_same {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {off : Nat} {x w : BitVec 64} {mem' : BitVec 64 → HolWordLab 64}
    (hA : ArenaOK s) (hW : WorldTypedWith s S Nd) (hbo_nz : globN s "bo" ≠ 0)
    (hoff_lt : off + 8 ≤ 88) (hx_eq : x.toNat = globN s "bo" + off)
    (hsame : mem' x = .word w) :
    memW {s with memory := mem'} (globN s "bo" + off) = w.toNat := by
  obtain ⟨_, _, _, hbo_hi⟩ := bo_allocated_wordsOK hA hW hbo_nz
  have hlt : globN s "bo" + off < 2 ^ 64 := lt_of_lt_of_le (Nat.add_lt_add_left (by omega) _) hbo_hi
  have hbv : BitVec.ofNat 64 (globN s "bo" + off) = x := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, hx_eq]
  unfold memW; dsimp; rw [hbv, hsame]

theorem memW_bo_store_ne {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {off off' : Nat} {x : BitVec 64} {mem' : BitVec 64 → HolWordLab 64}
    (hA : ArenaOK s) (hW : WorldTypedWith s S Nd) (hbo_nz : globN s "bo" ≠ 0)
    (hoff'_lt : off' + 8 ≤ 88) (hne : off' ≠ off)
    (hx_eq : x.toNat = globN s "bo" + off)
    (hframe : ∀ a : BitVec 64, a ≠ x → mem' a = s.memory a) :
    memW {s with memory := mem'} (globN s "bo" + off') = memW s (globN s "bo" + off') := by
  obtain ⟨_, _, _, hbo_hi⟩ := bo_allocated_wordsOK hA hW hbo_nz
  exact memW_word_store_ne hframe (by omega) (by omega)

theorem old_bo_obj_preserved {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {o : Ivl} {mem' : BitVec 64 → HolWordLab 64}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (hbo_nz : globN s "bo" ≠ 0)
    (ho : o ∈ blockOutObjects s) :
    let post := {s with memory := mem'}
    o = (0, 0) ∨ (Allocated post o ∧ WordsOK post o ∧ Disj o (globN s "bo", 88) ∧
      (o ∈ blockOutObjects s ∨ ∀ j ∈ worldOwned s S Nd, Disj o j)) := by
  intro post
  have hfix : o ∈ fixedObjects s := by
    unfold fixedObjects
    exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr ho)))
  rcases hW.2.2.1.1 o hfix with hz | ⟨hal_s, hw_s⟩
  · exact Or.inl (fixedObjects_zero_len_eq s o hfix hz)
  · right
    have hAp : ArenaReady post := ⟨guestInv_congr (s := s) rfl rfl rfl rfl hA.1, hA.2⟩
    let f_s : String × Nat → Ivl := fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)
    let jr_s : List Ivl := [(if globN s "journal_cap" = 0 then 0 else globN s "journal",
      32 * globN s "journal_cap")]
    have hF_parts := (pairwise_disj_append_4 (a1 := globalBuffers.map f_s) (a2 := jr_s)
      (b := blockOutObjects s) (c := balObjects s)).mp
      (by simpa [fixedObjects, f_s, jr_s] using hW.2.2.1.2)
    have hsbo_mem : f_s ("bo", 88) ∈ globalBuffers.map f_s :=
      List.mem_map_of_mem (by simp [globalBuffers] : ("bo", 88) ∈ globalBuffers)
    have hd_bo : Disj o (globN s "bo", 88) := by
      have hd := hF_parts.2.1 _ hsbo_mem o (List.mem_append_right _ (List.mem_append_left _ ho))
      simpa [f_s, hbo_nz] using hd.flip
    exact ⟨hal_s, wordsOK_transfer hA.1 hAp.1 hw_s, hd_bo, Or.inl ho⟩

theorem tracked_disj_all {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si hdr : Nat} {bs cs : List Ivl}
    (h : BlockContext s S Nd si hdr) (hbs : TrackedBlocks s S Nd bs)
    (hcs : TrackedBlocks s S Nd cs)
    (hdisj : IvlsDisj ((inputRegions s si hdr ++
      (if globN s "block_hashes_n" = 0 then []
       else [(globN s "block_hashes", 32 * globN s "block_hashes_n")]) ++ bs)) cs) :
    (∀ b ∈ cs, ∀ j ∈ worldOwned s S Nd, Disj b j) ∧
      IvlsDisj ((inputRegions s si hdr ++
        (if globN s "block_hashes_n" = 0 then []
         else [(globN s "block_hashes", 32 * globN s "block_hashes_n")]) ++ bs))
        (blockOutObjects s ++ cs) := by
  refine ⟨fun b hb j hj => (hcs b hb).2.2.2.2 j hj, ?_⟩
  intro a ha y hy
  rcases List.mem_append.1 hy with hy_bo | hy_cs
  · have hfix : y ∈ fixedObjects s := by
      unfold fixedObjects
      exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hy_bo)))
    have how : y ∈ worldOwned s S Nd := by
      unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))
    rcases List.mem_append.1 ha with ha1 | habs
    · rcases List.mem_append.1 ha1 with hareg | hahash
      · exact (h.regions a hareg).2.2.2.2 y how
      · by_cases hz : globN s "block_hashes_n" = 0
        · simp [hz] at hahash
        · simp only [hz, ↓reduceIte] at hahash
          exact (h.hashes hz a hahash).2.2.2.2 y how
    · exact (hbs a habs).2.2.2.2 y how
  · exact hdisj a ha y hy_cs

theorem fresh_disj_tracked {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {bs : List Ivl} {p len : Nat}
    (hbs : TrackedBlocks s S Nd bs) (hin : Inside (p, len) (globN s "heap_ptr") (globN post "heap_ptr")) :
    IvlsDisj bs [(p, len)] := by
  intro b hb y hy
  rw [List.mem_singleton.mp hy]
  obtain ⟨_, _, hbin, _, _⟩ := hbs b hb
  exact Or.inr (Or.inr (Or.inl (hbin.2.trans hin.1)))

theorem tracked_append_split_disj {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si hdr : Nat} {bs cs : List Ivl}
    (hall : TrackedBlocks s S Nd (bs ++ cs))
    (hpw_bs : bs.Pairwise Disj) (hpw_cs : cs.Pairwise Disj)
    (hbs_cs : IvlsDisj bs cs)
    (hreg_cs : IvlsDisj (inputRegions s si hdr) cs)
    (hhash_cs : globN s "block_hashes_n" ≠ 0 →
      IvlsDisj [(globN s "block_hashes", 32 * globN s "block_hashes_n")] cs) :
    TrackedBlocks s S Nd bs ∧ TrackedBlocks s S Nd cs ∧
      (bs ++ cs).Pairwise Disj ∧
      IvlsDisj ((inputRegions s si hdr ++
        (if globN s "block_hashes_n" = 0 then []
         else [(globN s "block_hashes", 32 * globN s "block_hashes_n")]) ++ bs)) cs := by
  obtain ⟨hbs, hcs⟩ := trackedBlocks_append.1 hall
  refine ⟨hbs, hcs, List.pairwise_append.2 ⟨hpw_bs, hpw_cs, hbs_cs⟩, ?_⟩
  intro a ha y hy
  rcases List.mem_append.1 ha with ha1 | habs
  · rcases List.mem_append.1 ha1 with hareg | hahash
    · exact hreg_cs a hareg y hy
    · by_cases hz : globN s "block_hashes_n" = 0
      · simp [hz] at hahash
      · simp only [hz, ↓reduceIte] at hahash
        exact hhash_cs hz a hahash y hy
  · exact hbs_cs a habs y hy

def TrackedDisjIn {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S Nd : List Nat) (si hdr : Nat) (bs : List Ivl) : Prop :=
  TrackedBlocks s S Nd bs ∧ bs.Pairwise Disj ∧
    IvlsDisj (inputRegions s si hdr) bs ∧
    (globN s "block_hashes_n" ≠ 0 →
      IvlsDisj [(globN s "block_hashes", 32 * globN s "block_hashes_n")] bs)

theorem trackedDisjIn_nil {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si hdr : Nat} :
    TrackedDisjIn s S Nd si hdr [] :=
  ⟨by simp [TrackedBlocks], List.Pairwise.nil, by simp [IvlsDisj], fun _ => by simp [IvlsDisj]⟩

theorem trackedDisjIn_worldStep_nil
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {S Nd : List Nat} {si hdr : Nat} {bs : List Ivl}
    (h : BlockContext s S Nd si hdr) (hbs : TrackedDisjIn s S Nd si hdr bs)
    (hstep : WorldStep (fun _ => []) gw keep Q s r post)
    (hjc : ofString "journal_cap" ∉ gw.map ofString)
    (hwd : ofString "wd_rlp_slices" ∉ gw.map ofString)
    (hbh : ofString "block_hashes" ∉ gw.map ofString)
    (hbhn : ofString "block_hashes_n" ∉ gw.map ofString) :
    ∃ S' Nd', BlockContext post S' Nd' si hdr ∧ TrackedDisjIn post S' Nd' si hdr bs ∧
      (∀ c ∈ inputRegions s si hdr, IvlUnhit s post c) ∧
      (∀ b ∈ bs, IvlUnhit s post b) ∧ Q s r post S' Nd' := by
  obtain ⟨S', Nd', hc, hb, hu, hub, hq⟩ :=
    blockContext_worldStep_nil h hbs.1 hstep hjc hwd hbh hbhn
  have hbh_eq := globN_eq_of_lookup (hstep.2.2.1 _ hbh)
  have hbhn_eq := globN_eq_of_lookup (hstep.2.2.1 _ hbhn)
  have hcin : ∀ c ∈ inputRegions s si hdr,
      c.1 % 8 = 0 ∧ Inside c sourceBase (globN s "heap_ptr") ∧ WordsOK s c :=
    fun c hm => ⟨(h.regions c hm).1, (h.regions c hm).2.2.1, (h.regions c hm).2.2.2.1⟩
  have hreg_eq : inputRegions post si hdr = inputRegions s si hdr :=
    inputRegions_eq_of_unhit h.arena hcin hu (globN_eq_of_lookup (hstep.2.2.1 _ hwd))
  refine ⟨S', Nd', hc, ⟨hb, hbs.2.1, ?_, ?_⟩, hu, hub, hq⟩
  · rw [hreg_eq]; exact hbs.2.2.1
  · intro hnz
    rw [hbhn_eq] at hnz
    rw [hbh_eq, hbhn_eq]
    exact hbs.2.2.2 hnz

theorem trackedDisjIn_alloc_result
    {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si hdr n : Nat} {bs : List Ivl} {w : BitVec 64}
    (h : BlockContext s S Nd si hdr) (hbs : TrackedDisjIn s S Nd si hdr bs)
    (hf : FreshBlock s post w.toNat n)
    (hstep : WorldStep (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun _ _ p => [(p, (n + 7) / 8 * 8)])) s
      (some (.returned (.val (.word w)))) post) :
    ∃ S' Nd', BlockContext post S' Nd' si hdr ∧
      TrackedDisjIn post S' Nd' si hdr (bs ++ [(w.toNat, (n + 7) / 8 * 8)]) ∧
      w.toNat ≠ 0 ∧
      (∀ c ∈ inputRegions s si hdr, IvlUnhit s post c) ∧
      (∀ b ∈ bs, IvlUnhit s post b) := by
  obtain ⟨S', Nd', hc, hb_in, hu, hub, hq⟩ :=
    trackedDisjIn_worldStep_nil h hbs hstep (by decide) (by decide) (by decide) (by decide)
  obtain ⟨w', heq, hd⟩ := hq (.val (.word w)) rfl
  have hw : w = w' := by cases heq; rfl
  subst w'
  have hnew_tb : TrackedBlocks post S' Nd' [(w.toNat, (n + 7) / 8 * 8)] :=
    trackedBlocks_fresh h.arena hc.arena hc.world hf hd
  have hin : Inside (w.toNat, (n + 7) / 8 * 8) (globN s "heap_ptr") (globN post "heap_ptr") :=
    ⟨hf.2.1.1, hf.2.1.2.trans (by omega)⟩
  have hwnz : w.toNat ≠ 0 := by
    have hsb := h.arena.2.1
    have hpos : 0 < sourceBase := by decide
    have := hf.2.1.1; omega
  have hbh_eq := globN_eq_of_lookup (hstep.2.2.1 _ (by decide : ofString "block_hashes" ∉ ["heap_ptr"].map ofString))
  have hbhn_eq := globN_eq_of_lookup (hstep.2.2.1 _ (by decide : ofString "block_hashes_n" ∉ ["heap_ptr"].map ofString))
  have hcin : ∀ c ∈ inputRegions s si hdr,
      c.1 % 8 = 0 ∧ Inside c sourceBase (globN s "heap_ptr") ∧ WordsOK s c :=
    fun c hm => ⟨(h.regions c hm).1, (h.regions c hm).2.2.1, (h.regions c hm).2.2.2.1⟩
  have hreg_disj : IvlsDisj (inputRegions post si hdr) [(w.toNat, (n + 7) / 8 * 8)] := by
    have hreg_eq : inputRegions post si hdr = inputRegions s si hdr :=
      inputRegions_eq_of_unhit h.arena hcin hu
        (globN_eq_of_lookup (hstep.2.2.1 _ (by decide : ofString "wd_rlp_slices" ∉ ["heap_ptr"].map ofString)))
    rw [hreg_eq]
    exact fresh_disj_tracked h.regions hin
  have hhash_disj : globN post "block_hashes_n" ≠ 0 →
      IvlsDisj [(globN post "block_hashes", 32 * globN post "block_hashes_n")]
        [(w.toNat, (n + 7) / 8 * 8)] := by
    intro hnz
    rw [hbhn_eq] at hnz
    rw [hbh_eq, hbhn_eq]
    exact fresh_disj_tracked (h.hashes hnz) hin
  have hbs_disj : IvlsDisj bs [(w.toNat, (n + 7) / 8 * 8)] :=
    fresh_disj_tracked hbs.1 hin
  refine ⟨S', Nd', hc, ⟨trackedBlocks_append.2 ⟨hb_in.1, hnew_tb⟩,
    List.pairwise_append.2 ⟨hb_in.2.1, List.pairwise_singleton _ _, hbs_disj⟩,
    ?_, ?_⟩, hwnz, hu, hub⟩
  · intro a ha y hy
    rcases List.mem_append.1 hy with hy1 | hy2
    · exact hb_in.2.2.1 a ha y hy1
    · exact hreg_disj a ha y hy2
  · intro hnz a ha y hy
    rcases List.mem_append.1 hy with hy1 | hy2
    · exact hb_in.2.2.2 hnz a ha y hy1
    · exact hhash_disj hnz a ha y hy2

theorem trackedDisjIn_lst_new_result
    {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si hdr : Nat} {bs : List Ivl} {w : BitVec 64}
    (h : BlockContext s S Nd si hdr) (hbs : TrackedDisjIn s S Nd si hdr bs)
    (hhead : FreshBlock s post w.toNat 24)
    (hdata : FreshBlock s post (memW post w.toNat) 128)
    (hd_hd : Disj (w.toNat, 24) (memW post w.toNat, 128))
    (hlen : memW post (w.toNat + 8) = 0)
    (hcap : memW post (w.toNat + 16) = 16)
    (hstep : WorldStep (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun _ post p => [(p, 24), (memW post p, 128)])) s
      (some (.returned (.val (.word w)))) post) :
    ∃ S' Nd', BlockContext post S' Nd' si hdr ∧
      TrackedDisjIn post S' Nd' si hdr (bs ++ [(w.toNat, 24), (memW post w.toNat, 128)]) ∧
      LstOK post w.toNat ∧ w.toNat ≠ 0 ∧ memW post w.toNat ≠ 0 ∧
      (∀ c ∈ inputRegions s si hdr, IvlUnhit s post c) ∧
      (∀ b ∈ bs, IvlUnhit s post b) := by
  obtain ⟨S', Nd', hc, hb_in, hu, hub, hq⟩ :=
    trackedDisjIn_worldStep_nil h hbs hstep (by decide) (by decide) (by decide) (by decide)
  obtain ⟨w', heq, hd⟩ := hq (.val (.word w)) rfl
  have hw : w = w' := by cases heq; rfl
  subst w'
  have hhead' : TrackedBlocks post S' Nd' [(w.toNat, 24)] := by
    apply trackedBlocks_fresh h.arena hc.arena hc.world hhead
    simpa only [show (24 + 7) / 8 * 8 = 24 from rfl] using
      (show IvlsDisj [(w.toNat, 24)] (worldOwned post S' Nd') from
        fun b hb o ho => hd b (by rw [List.mem_singleton.mp hb]; simp) o ho)
  have hdata' : TrackedBlocks post S' Nd' [(memW post w.toNat, 128)] := by
    apply trackedBlocks_fresh h.arena hc.arena hc.world hdata
    simpa only [show (128 + 7) / 8 * 8 = 128 from rfl] using
      (show IvlsDisj [(memW post w.toNat, 128)] (worldOwned post S' Nd') from
        fun b hb o ho => hd b (by rw [List.mem_singleton.mp hb]; simp) o ho)
  have hin1 : Inside (w.toNat, 24) (globN s "heap_ptr") (globN post "heap_ptr") :=
    ⟨hhead.2.1.1, hhead.2.1.2⟩
  have hin2 : Inside (memW post w.toNat, 128) (globN s "heap_ptr") (globN post "heap_ptr") :=
    ⟨hdata.2.1.1, hdata.2.1.2⟩
  have hsb := h.arena.2.1
  have hsb_pos : 0 < sourceBase := by decide
  have hwnz : w.toNat ≠ 0 := by have := hhead.2.1.1; omega
  have hdnz : memW post w.toNat ≠ 0 := by have := hdata.2.1.1; omega
  have hbh_eq := globN_eq_of_lookup (hstep.2.2.1 _ (by decide : ofString "block_hashes" ∉ ["heap_ptr"].map ofString))
  have hbhn_eq := globN_eq_of_lookup (hstep.2.2.1 _ (by decide : ofString "block_hashes_n" ∉ ["heap_ptr"].map ofString))
  have hcin : ∀ c ∈ inputRegions s si hdr,
      c.1 % 8 = 0 ∧ Inside c sourceBase (globN s "heap_ptr") ∧ WordsOK s c :=
    fun c hm => ⟨(h.regions c hm).1, (h.regions c hm).2.2.1, (h.regions c hm).2.2.2.1⟩
  have hreg_eq : inputRegions post si hdr = inputRegions s si hdr :=
    inputRegions_eq_of_unhit h.arena hcin hu
      (globN_eq_of_lookup (hstep.2.2.1 _ (by decide : ofString "wd_rlp_slices" ∉ ["heap_ptr"].map ofString)))
  have htwo_disj : ∀ {cs : List Ivl}, TrackedBlocks s S Nd cs →
      IvlsDisj cs [(w.toNat, 24), (memW post w.toNat, 128)] := by
    intro cs hcs a ha y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact fresh_disj_tracked hcs hin1 a ha _ (by simp)
    · exact fresh_disj_tracked hcs hin2 a ha _ (by simp)
  have hpw_two : ([(w.toNat, 24), (memW post w.toNat, 128)] : List Ivl).Pairwise Disj :=
    List.pairwise_cons.2 ⟨fun y hy => by rw [List.mem_singleton.mp hy]; exact hd_hd,
      List.pairwise_singleton _ _⟩
  refine ⟨S', Nd', hc, ⟨trackedBlocks_append.2 ⟨hb_in.1, trackedBlocks_append.2 ⟨hhead', hdata'⟩⟩,
    List.pairwise_append.2 ⟨hb_in.2.1, hpw_two, htwo_disj hbs.1⟩, ?_, ?_⟩,
    by simp [LstOK, hlen, hcap], hwnz, hdnz, hu, hub⟩
  · intro a ha y hy
    rcases List.mem_append.1 hy with hy1 | hy2
    · exact hb_in.2.2.1 a ha y hy1
    · rw [hreg_eq] at ha; exact htwo_disj h.regions a ha y hy2
  · intro hnz a ha y hy
    rcases List.mem_append.1 hy with hy1 | hy2
    · exact hb_in.2.2.2 hnz a ha y hy1
    · rw [hbhn_eq] at hnz; rw [hbh_eq, hbhn_eq] at ha
      exact htwo_disj (h.hashes hnz) a ha y hy2

theorem nonZero_ivls_disj {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {a b : Ivl}
    (ha_ow : a ∈ worldOwned s S Nd) (hb_tb : TrackedBlocks s S Nd [b]) :
    Disj a b :=
  ((hb_tb b (by simp)).2.2.2.2 a ha_ow).flip

theorem blockOutObj_mem_worldOwned {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {o : Ivl} (ho : o ∈ blockOutObjects s) :
    o ∈ worldOwned s S Nd := by
  unfold worldOwned fixedObjects
  exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr
    (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr ho)))))))

theorem trackedDisjIn_sub_parts {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si hdr p n : Nat} {bs : List Ivl}
    (hA : ArenaReady s)
    (h : TrackedDisjIn s S Nd si hdr (bs ++ [(p, 16 * n + 16)])) :
    TrackedDisjIn s S Nd si hdr (bs ++ [(p, 16), (p + 16, 16 * n)]) := by
  obtain ⟨htb, hpw, hreg, hhash⟩ := h
  obtain ⟨htb_bs, htb_p⟩ := trackedBlocks_append.1 htb
  have hp_parts : TrackedBlocks s S Nd [(p, 16), (p + 16, 16 * n)] :=
    trackedBlocks_array_parts hA htb_p
  obtain ⟨hpw_bs, _, hbs_p⟩ := List.pairwise_append.1 hpw
  have h1 : Inside (p, 16) p (p + (16 * n + 16)) := by unfold Inside; dsimp; omega
  have h2 : Inside (p + 16, 16 * n) p (p + (16 * n + 16)) := by unfold Inside; dsimp; omega
  have hpw_two : ([(p, 16), (p + 16, 16 * n)] : List Ivl).Pairwise Disj :=
    List.pairwise_cons.2 ⟨fun y hy => by
      rw [List.mem_singleton.mp hy]
      exact Or.inr (Or.inr (Or.inl le_rfl)), List.pairwise_singleton _ _⟩
  have hsub_disj : ∀ {cs : List Ivl}, IvlsDisj cs [(p, 16 * n + 16)] →
      IvlsDisj cs [(p, 16), (p + 16, 16 * n)] := by
    intro cs hcs a ha y hy
    have hd := hcs a ha (p, 16 * n + 16) List.mem_cons_self
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact (disj_of_inside_left h1 hd.flip).flip
    · exact (disj_of_inside_left h2 hd.flip).flip
  refine ⟨trackedBlocks_append.2 ⟨htb_bs, hp_parts⟩,
    List.pairwise_append.2 ⟨hpw_bs, hpw_two, hsub_disj hbs_p⟩, ?_, ?_⟩
  · intro a ha y hy
    rcases List.mem_append.1 hy with hy1 | hy2
    · exact hreg a ha y (List.mem_append_left _ hy1)
    · exact hsub_disj (fun c hc z hz => hreg c hc z (List.mem_append_right _ hz)) a ha y hy2
  · intro hnz a ha y hy
    rcases List.mem_append.1 hy with hy1 | hy2
    · exact hhash hnz a ha y (List.mem_append_left _ hy1)
    · exact hsub_disj (fun c hc z hz => hhash hnz c hc z (List.mem_append_right _ hz)) a ha y hy2

theorem trackedDisjIn_drop_head_of_append {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si hdr : Nat} {bs : List Ivl} {a : Ivl} {rest : List Ivl}
    (h : TrackedDisjIn s S Nd si hdr (bs ++ (a :: rest))) :
    TrackedDisjIn s S Nd si hdr (bs ++ rest) ∧ TrackedBlocks s S Nd [a] ∧
      IvlsDisj (bs ++ rest) [a] ∧ IvlsDisj (inputRegions s si hdr) [a] ∧
      (globN s "block_hashes_n" ≠ 0 →
        IvlsDisj [(globN s "block_hashes", 32 * globN s "block_hashes_n")] [a]) := by
  obtain ⟨htb, hpw, hreg, hhash⟩ := h
  obtain ⟨htb_bs, htb_ar⟩ := trackedBlocks_append.1 htb
  have htb_ar' : TrackedBlocks s S Nd ([a] ++ rest) := htb_ar
  obtain ⟨htb_a, htb_r⟩ := trackedBlocks_append.1 htb_ar'
  obtain ⟨hpw_bs, hpw_ar, hbs_ar⟩ := List.pairwise_append.1 hpw
  obtain ⟨ha_r, hpw_r⟩ := List.pairwise_cons.1 hpw_ar
  refine ⟨⟨trackedBlocks_append.2 ⟨htb_bs, htb_r⟩,
    List.pairwise_append.2 ⟨hpw_bs, hpw_r, fun x hx y hy => hbs_ar x hx y (List.mem_cons_of_mem _ hy)⟩,
    fun x hx y hy => hreg x hx y (by
      rcases List.mem_append.1 hy with h1 | h2
      · exact List.mem_append_left _ h1
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2)),
    fun hnz x hx y hy => hhash hnz x hx y (by
      rcases List.mem_append.1 hy with h1 | h2
      · exact List.mem_append_left _ h1
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2))⟩,
    htb_a,
    fun x hx y hy => by
      rw [List.mem_singleton.mp hy]
      rcases List.mem_append.1 hx with hx1 | hx2
      · exact hbs_ar x hx1 a List.mem_cons_self
      · exact (ha_r x hx2).flip,
    fun x hx y hy => by
      rw [List.mem_singleton.mp hy]
      exact hreg x hx a (List.mem_append_right _ List.mem_cons_self),
    fun hnz x hx y hy => by
      rw [List.mem_singleton.mp hy]
      exact hhash hnz x hx a (List.mem_append_right _ List.mem_cons_self)⟩

theorem bo_lst_mem_preserved {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {l off : Nat} {x : BitVec 64} {mem' : BitVec 64 → HolWordLab 64}
    (hA : ArenaOK s) (hW : WorldTypedWith s S Nd) (hbo_nz : globN s "bo" ≠ 0)
    (hk : l = memW s (globN s "bo" + 40) ∨ l = memW s (globN s "bo" + 72))
    (hl_nz : l ≠ 0)
    (hoff_lt : off + 8 ≤ 88) (hx_eq : x.toNat = globN s "bo" + off)
    (hframe : ∀ a : BitVec 64, a ≠ x → mem' a = s.memory a) :
    let post := {s with memory := mem'}
    memW post l = memW s l ∧ memW post (l + 8) = memW s (l + 8) ∧
      memW post (l + 16) = memW s (l + 16) ∧
      (LstOK s l → LstOK post l) := by
  intro post
  have hl_bo : (l, 24) ∈ blockOutObjects s := by
    unfold blockOutObjects
    rcases hk with rfl | rfl
    · apply List.mem_append.2; left; apply List.mem_append.2; right
      simp [hbo_nz, hl_nz]
    · apply List.mem_append.2; right
      simp [hbo_nz, hl_nz]
  have hfix : (l, 24) ∈ fixedObjects s := by
    unfold fixedObjects
    exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hl_bo)))
  have hl_ow := blockOutObj_mem_worldOwned (S := S) (Nd := Nd) hl_bo
  have hl_ne_bo : (l, 24) ≠ (globN s "bo", 88) := fun heq => by have := (Prod.mk.inj heq).2; omega
  have hd_bo := (bo_disj_worldOwned_nonbo hW hbo_nz (l, 24) hl_ow hl_ne_bo).flip
  have hx_in : Inside (x.toNat, 8) (globN s "bo") (globN s "bo" + 88) := by
    unfold Inside; dsimp; omega
  have hd_x : Disj (l, 24) (x.toNat, 8) := (disj_of_inside_left hx_in hd_bo.flip).flip
  rcases hW.2.2.1.1 (l, 24) hfix with hz | ⟨hal, hw⟩
  · cases hz
  · have hl8 : l % 8 = 0 := hw.1
    have hu : IvlUnhit s post (l, 24) := ivlUnhit_of_single_cell_disj (fun hz => by cases hz) hframe hd_x
    have hbound := (ivl_allocated_bound hA hal).2
    have h0 := memW_eq_of_ivlUnhit hu (a := l) hl8 hbound (by dsimp; omega)
    have h8 := memW_eq_of_ivlUnhit hu (a := l + 8) (by omega) hbound (by dsimp; omega)
    have h16 := memW_eq_of_ivlUnhit hu (a := l + 16) (by omega) hbound (by dsimp; omega)
    exact ⟨h0, h8, h16, fun hok => ⟨by rw [h16]; exact hok.1, by rw [h8, h16]; exact hok.2⟩⟩

theorem pairwise_disj_append_zeros {xs : List Ivl} {k : Nat}
    (hxs : xs.Pairwise Disj) :
    (xs ++ List.replicate k (0, 0)).Pairwise Disj := by
  refine List.pairwise_append.2 ⟨hxs, List.pairwise_replicate.2 (Or.inr (Or.inl rfl)), ?_⟩
  intro a _ b hb
  rw [List.eq_of_mem_replicate hb]
  exact disj_zero_right a

theorem pairwise_disj_perm {xs ys : List Ivl}
    (hperm : xs.Perm ys) (hxs : xs.Pairwise Disj) :
    ys.Pairwise Disj :=
  hxs.perm hperm (fun {_ _} h => Disj.flip h)

theorem bo_old_disj_new {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {o a : Ivl} {addObjs : List Ivl}
    (ho : o ∈ blockOutObjects s) (ha : a ∈ addObjs)
    (hadd : TrackedBlocks s S Nd addObjs) :
    Disj o a :=
  ((hadd a ha).2.2.2.2 o (blockOutObj_mem_worldOwned ho)).flip

theorem bo_s_pairwise {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hW : WorldTypedWith s S Nd) :
    (blockOutObjects s).Pairwise Disj := by
  let f_s : String × Nat → Ivl := fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)
  let jr_s : List Ivl := [(if globN s "journal_cap" = 0 then 0 else globN s "journal",
    32 * globN s "journal_cap")]
  exact ((pairwise_disj_append_4 (a1 := globalBuffers.map f_s) (a2 := jr_s)
    (b := blockOutObjects s) (c := balObjects s)).mp
    (by simpa [fixedObjects, f_s, jr_s] using hW.2.2.1.2)).1.2.2.1

theorem pairwise_disj_old_add_zeros {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {olds addObjs : List Ivl} {k : Nat}
    (holds_sub : ∀ o ∈ olds, o ∈ blockOutObjects s)
    (holds_pw : olds.Pairwise Disj)
    (hadd_tb : TrackedBlocks s S Nd addObjs)
    (hadd_pw : addObjs.Pairwise Disj) :
    (olds ++ addObjs ++ List.replicate k (0, 0)).Pairwise Disj := by
  apply pairwise_disj_append_zeros
  exact List.pairwise_append.2 ⟨holds_pw, hadd_pw,
    fun o ho a ha => bo_old_disj_new (holds_sub o ho) ha hadd_tb⟩

theorem bo_store_gen {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si hdr off : Nat} {x w : BitVec 64} {mem' : BitVec 64 → HolWordLab 64}
    {bs addObjs : List Ivl}
    (h : BlockContext s S Nd si hdr)
    (hbs : TrackedDisjIn s S Nd si hdr bs)
    (hadd : TrackedDisjIn s S Nd si hdr addObjs)
    (hbs_add : IvlsDisj bs addObjs)
    (hbo_nz : globN s "bo" ≠ 0)
    (hoff8 : off % 8 = 0) (hoff_lt : off + 8 ≤ 88)
    (hx_eq : x.toNat = globN s "bo" + off)
    (hsame : mem' x = .word w) (hframe : ∀ a : BitVec 64, a ≠ x → mem' a = s.memory a)
    (hbo_sub : ∀ o ∈ blockOutObjects {s with memory := mem'},
      o = (0, 0) ∨ o ∈ blockOutObjects s ∨ o ∈ addObjs)
    (hbo_pw : (blockOutObjects {s with memory := mem'}).Pairwise Disj)
    (hbo_lst : ∀ k ∈ ([40, 72] : List Nat),
      memW {s with memory := mem'} (globN s "bo" + k) ≠ 0 →
        LstOK {s with memory := mem'} (memW {s with memory := mem'} (globN s "bo" + k))) :
    let post := {s with memory := mem'}
    BlockContext post S Nd si hdr ∧ TrackedDisjIn post S Nd si hdr bs := by
  intro post
  have hbo_objs : ∀ o ∈ blockOutObjects post,
      o = (0, 0) ∨ (Allocated post o ∧ WordsOK post o ∧ Disj o (globN s "bo", 88) ∧
        (o ∈ blockOutObjects s ∨ ∀ j ∈ worldOwned s S Nd, j ∉ blockOutObjects s → Disj o j)) := by
    intro o ho
    rcases hbo_sub o ho with rfl | hold | hnew
    · exact Or.inl rfl
    · rcases old_bo_obj_preserved h.arena h.world hbo_nz hold with rfl | ⟨hal, hw, hd_bo, hcase⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hal, hw, hd_bo, hcase.imp id (fun hall j hj _ => hall j hj)⟩
    · have ho_tb : TrackedBlocks s S Nd [o] := fun b hb => by
        rw [List.mem_singleton.mp hb]; exact hadd.1 o hnew
      obtain ⟨hal, hw, hd_bo, hd_ow, _⟩ :=
        tracked_alloc_words_post h.arena ho_tb hbo_nz hoff_lt hx_eq hframe
      exact Or.inr ⟨hal, hw, hd_bo, Or.inr (fun j hj _ => hd_ow j hj)⟩
  have hobj_bs : IvlsDisj (inputRegions s si hdr ++
      (if globN s "block_hashes_n" = 0 then []
       else [(globN s "block_hashes", 32 * globN s "block_hashes_n")]) ++ bs)
      (blockOutObjects post) := by
    intro a ha o ho
    rcases hbo_sub o ho with rfl | hold | hnew
    · exact disj_zero_right a
    · have how := blockOutObj_mem_worldOwned (S := S) (Nd := Nd) hold
      rcases List.mem_append.1 ha with ha1 | habs
      · rcases List.mem_append.1 ha1 with hareg | hahash
        · exact (h.regions a hareg).2.2.2.2 o how
        · by_cases hbnz : globN s "block_hashes_n" = 0
          · simp [hbnz] at hahash
          · simp only [hbnz, ↓reduceIte] at hahash
            exact (h.hashes hbnz a hahash).2.2.2.2 o how
      · exact (hbs.1 a habs).2.2.2.2 o how
    · rcases List.mem_append.1 ha with ha1 | habs
      · rcases List.mem_append.1 ha1 with hareg | hahash
        · exact hadd.2.2.1 a hareg o hnew
        · by_cases hbnz : globN s "block_hashes_n" = 0
          · simp [hbnz] at hahash
          · simp only [hbnz, ↓reduceIte] at hahash
            exact hadd.2.2.2 hbnz a hahash o hnew
      · exact hbs_add a habs o hnew
  obtain ⟨hctx_p, hbs_p⟩ :=
    blockContext_word_store_bo h hbs.1 hbo_nz hoff8 hoff_lt hx_eq hsame hframe
      hbo_objs hbo_pw hbo_lst hobj_bs
  have hcin : ∀ c ∈ inputRegions s si hdr,
      c.1 % 8 = 0 ∧ Inside c sourceBase (globN s "heap_ptr") ∧ WordsOK s c :=
    fun c hm => ⟨(h.regions c hm).1, (h.regions c hm).2.2.1, (h.regions c hm).2.2.2.1⟩
  have hbo_mem_ow := bo_in_worldOwned (S := S) (Nd := Nd) hbo_nz
  have hx_in_bo : Inside (x.toNat, 8) (globN s "bo") (globN s "bo" + 88) := by
    unfold Inside; dsimp; omega
  have hu_reg : ∀ c ∈ inputRegions s si hdr, IvlUnhit s post c := by
    intro c hc
    obtain ⟨hc8, _, _, _, hd_ow⟩ := h.regions c hc
    exact ivlUnhit_of_single_cell_disj (fun _ => hc8) hframe
      (disj_of_inside_left hx_in_bo (hd_ow _ hbo_mem_ow).flip).flip
  have hreg_eq : inputRegions post si hdr = inputRegions s si hdr :=
    inputRegions_eq_of_unhit h.arena hcin hu_reg rfl
  exact ⟨hctx_p, ⟨hbs_p, hbs.2.1, by rw [hreg_eq]; exact hbs.2.2.1, hbs.2.2.2⟩⟩

theorem bo_store_32 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si hdr ntx : Nat} {x w : BitVec 64} {mem' : BitVec 64 → HolWordLab 64}
    (h : BlockContext s S Nd si hdr)
    (htb : TrackedDisjIn s S Nd si hdr
      [(memW s (globN s "bo" + 24) + 16, 16 * ntx), (w.toNat, 16), (w.toNat + 16, 16 * ntx)])
    (hbo_nz : globN s "bo" ≠ 0)
    (h24_nz : memW s (globN s "bo" + 24) ≠ 0) (hw_nz : w.toNat ≠ 0)
    (hz : ∀ off ∈ ([32, 40, 56, 64, 72, 80] : List Nat), memW s (globN s "bo" + off) = 0)
    (hx_eq : x.toNat = globN s "bo" + 32)
    (hsame : mem' x = .word w) (hframe : ∀ a : BitVec 64, a ≠ x → mem' a = s.memory a) :
    let post := {s with memory := mem'}
    BlockContext post S Nd si hdr ∧
      TrackedDisjIn post S Nd si hdr
        [(memW post (globN post "bo" + 24) + 16, 16 * ntx), (w.toNat + 16, 16 * ntx)] ∧
      globN post "bo" ≠ 0 ∧
      memW post (globN post "bo" + 24) ≠ 0 ∧
      memW post (globN post "bo" + 32) = w.toNat ∧
      (∀ off ∈ ([40, 56, 64, 72, 80] : List Nat), memW post (globN post "bo" + off) = 0) := by
  intro post
  let txs := memW s (globN s "bo" + 24)
  have hsplit := trackedDisjIn_drop_head_of_append (bs := [(txs + 16, 16 * ntx)])
    (a := (w.toNat, 16)) (rest := [(w.toNat + 16, 16 * ntx)]) (by simpa [txs] using htb)
  obtain ⟨hrem_in, hw16_tb, hrem_disj, hreg_disj, hhash_disj⟩ := hsplit
  have hadd_in : TrackedDisjIn s S Nd si hdr [(w.toNat, 16)] :=
    ⟨hw16_tb, List.pairwise_singleton _ _, hreg_disj, hhash_disj⟩
  have h24_p : memW post (globN s "bo" + 24) = txs :=
    memW_bo_store_ne h.arena.2 h.world hbo_nz (by decide) (by decide) hx_eq hframe
  have h32_p : memW post (globN s "bo" + 32) = w.toNat :=
    memW_bo_store_same h.arena.2 h.world hbo_nz (by decide) hx_eq hsame
  have hother_p : ∀ off ∈ ([40, 56, 64, 72, 80] : List Nat),
      memW post (globN s "bo" + off) = 0 := by
    intro off hoff
    have hoff_lt : off + 8 ≤ 88 ∧ off ≠ 32 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl | rfl | rfl <;> omega
    rw [memW_bo_store_ne h.arena.2 h.world hbo_nz hoff_lt.1 hoff_lt.2 hx_eq hframe]
    exact hz off (List.mem_cons_of_mem _ hoff)
  have h24_in_s : (txs, 16) ∈ blockOutObjects s := by
    unfold blockOutObjects
    simp [txs, hbo_nz, h24_nz, hz 80 (by simp)]
  have htxs_nz : txs ≠ 0 := h24_nz
  have hbo_post_eq : blockOutObjects post =
      [(txs, 16)] ++ [(w.toNat, 16)] ++ List.replicate 5 (0, 0) := by
    unfold blockOutObjects
    simp [show globN post "bo" = globN s "bo" from rfl, hbo_nz, htxs_nz, hw_nz,
      h24_p, h32_p, hother_p 40 (by simp), hother_p 56 (by simp),
      hother_p 72 (by simp), hother_p 80 (by simp), List.replicate]
  have hres := bo_store_gen h hrem_in hadd_in hrem_disj hbo_nz (by decide) (by decide) hx_eq hsame hframe
    (fun o ho => by
      rw [hbo_post_eq] at ho
      rcases List.mem_append.1 ho with ho1 | hoz
      · rcases List.mem_append.1 ho1 with hold | hnew
        · rw [List.mem_singleton.mp hold]; exact Or.inr (Or.inl h24_in_s)
        · exact Or.inr (Or.inr hnew)
      · exact Or.inl (List.eq_of_mem_replicate hoz))
    (by rw [hbo_post_eq]
        exact pairwise_disj_old_add_zeros
          (fun o ho => by rw [List.mem_singleton.mp ho]; exact h24_in_s)
          (List.pairwise_singleton _ _) hw16_tb (List.pairwise_singleton _ _))
    (fun k hk hnz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · exact absurd (hother_p 40 (by simp)) hnz
      · exact absurd (hother_p 72 (by simp)) hnz)
  exact ⟨hres.1, by rw [show globN post "bo" = globN s "bo" from rfl, h24_p]; exact hres.2,
    hbo_nz, by rw [show globN post "bo" = globN s "bo" from rfl, h24_p]; exact h24_nz,
    h32_p, hother_p⟩

theorem bo_store_40 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si hdr ntx : Nat} {x w : BitVec 64} {mem' : BitVec 64 → HolWordLab 64}
    (h : BlockContext s S Nd si hdr)
    (htb : TrackedDisjIn s S Nd si hdr
      [(memW s (globN s "bo" + 24) + 16, 16 * ntx),
       (memW s (globN s "bo" + 32) + 16, 16 * ntx),
       (w.toNat, 24), (memW s w.toNat, 128)])
    (hbo_nz : globN s "bo" ≠ 0)
    (h24_nz : memW s (globN s "bo" + 24) ≠ 0)
    (h32_nz : memW s (globN s "bo" + 32) ≠ 0)
    (hw_nz : w.toNat ≠ 0) (hw0_nz : memW s w.toNat ≠ 0)
    (hw8 : memW s (w.toNat + 8) = 0) (hw16 : memW s (w.toNat + 16) = 16)
    (hz : ∀ off ∈ ([40, 56, 64, 72, 80] : List Nat), memW s (globN s "bo" + off) = 0)
    (hx_eq : x.toNat = globN s "bo" + 40)
    (hsame : mem' x = .word w) (hframe : ∀ a : BitVec 64, a ≠ x → mem' a = s.memory a) :
    let post := {s with memory := mem'}
    BlockContext post S Nd si hdr ∧
      TrackedDisjIn post S Nd si hdr
        [(memW post (globN post "bo" + 24) + 16, 16 * ntx),
         (memW post (globN post "bo" + 32) + 16, 16 * ntx)] ∧
      globN post "bo" ≠ 0 ∧
      memW post (globN post "bo" + 24) ≠ 0 ∧
      memW post (globN post "bo" + 32) ≠ 0 ∧
      memW post (globN post "bo" + 40) = w.toNat ∧
      (∀ off ∈ ([56, 64, 72, 80] : List Nat), memW post (globN post "bo" + off) = 0) := by
  intro post
  let txs := memW s (globN s "bo" + 24)
  let rcs := memW s (globN s "bo" + 32)
  let bs_rem : List Ivl := [(txs + 16, 16 * ntx), (rcs + 16, 16 * ntx)]
  let add_lst : List Ivl := [(w.toNat, 24), (memW s w.toNat, 128)]
  have htb_eq : TrackedDisjIn s S Nd si hdr (bs_rem ++ add_lst) := by simpa [bs_rem, add_lst, txs, rcs] using htb
  obtain ⟨htb_all, hpw_all, hreg_all, hhash_all⟩ := htb_eq
  obtain ⟨htb_rem, htb_add⟩ := trackedBlocks_append.1 htb_all
  obtain ⟨hpw_rem, hpw_add, hrem_add⟩ := List.pairwise_append.1 hpw_all
  have hrem_in : TrackedDisjIn s S Nd si hdr bs_rem :=
    ⟨htb_rem, hpw_rem,
     fun a ha b hb => hreg_all a ha b (List.mem_append_left _ hb),
     fun hnz a ha b hb => hhash_all hnz a ha b (List.mem_append_left _ hb)⟩
  have hadd_in : TrackedDisjIn s S Nd si hdr add_lst :=
    ⟨htb_add, hpw_add,
     fun a ha b hb => hreg_all a ha b (List.mem_append_right _ hb),
     fun hnz a ha b hb => hhash_all hnz a ha b (List.mem_append_right _ hb)⟩
  have hw24_tb : TrackedBlocks s S Nd [(w.toNat, 24)] := fun b hb => by
    rw [List.mem_singleton.mp hb]; exact htb_add _ List.mem_cons_self
  obtain ⟨hal_w, hw_w, _, _, hu_w⟩ :=
    tracked_alloc_words_post h.arena hw24_tb hbo_nz (by decide) hx_eq hframe
  have hbound_w := (ivl_allocated_bound h.arena.2 hal_w).2
  have hw0_p : memW post w.toNat = memW s w.toNat :=
    memW_eq_of_ivlUnhit hu_w hw_w.1 hbound_w (by dsimp; omega)
  have hw8_p : memW post (w.toNat + 8) = 0 := by
    rw [memW_eq_of_ivlUnhit hu_w (by have := hw_w.1; omega) hbound_w (by dsimp; omega), hw8]
  have hw16_p : memW post (w.toNat + 16) = 16 := by
    rw [memW_eq_of_ivlUnhit hu_w (by have := hw_w.1; omega) hbound_w (by dsimp; omega), hw16]
  have h24_p : memW post (globN s "bo" + 24) = txs :=
    memW_bo_store_ne h.arena.2 h.world hbo_nz (by decide) (by decide) hx_eq hframe
  have h32_p : memW post (globN s "bo" + 32) = rcs :=
    memW_bo_store_ne h.arena.2 h.world hbo_nz (by decide) (by decide) hx_eq hframe
  have h40_p : memW post (globN s "bo" + 40) = w.toNat :=
    memW_bo_store_same h.arena.2 h.world hbo_nz (by decide) hx_eq hsame
  have hother_p : ∀ off ∈ ([56, 64, 72, 80] : List Nat),
      memW post (globN s "bo" + off) = 0 := by
    intro off hoff
    have hoff_lt : off + 8 ≤ 88 ∧ off ≠ 40 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl | rfl <;> omega
    rw [memW_bo_store_ne h.arena.2 h.world hbo_nz hoff_lt.1 hoff_lt.2 hx_eq hframe]
    exact hz off (List.mem_cons_of_mem _ hoff)
  have htxs_nz : txs ≠ 0 := h24_nz
  have hrcs_nz : rcs ≠ 0 := h32_nz
  have hbo_s_eq : blockOutObjects s = [(txs, 16), (rcs, 16)] ++ List.replicate 5 (0, 0) := by
    unfold blockOutObjects
    simp [txs, rcs, hbo_nz, htxs_nz, hrcs_nz, hz 40 (by simp), hz 56 (by simp),
      hz 72 (by simp), hz 80 (by simp), List.replicate]
  have holds_pw : ([(txs, 16), (rcs, 16)] : List Ivl).Pairwise Disj := by
    have hpw_s := bo_s_pairwise h.world
    rw [hbo_s_eq] at hpw_s
    exact (List.pairwise_append.1 hpw_s).1
  have hbo_post_perm : ([(txs, 16), (rcs, 16)] ++ add_lst ++ List.replicate 3 (0, 0)).Perm
      (blockOutObjects post) := by
    unfold blockOutObjects
    simp [show globN post "bo" = globN s "bo" from rfl, hbo_nz, htxs_nz, hrcs_nz, hw_nz, hw0_nz,
      h24_p, h32_p, h40_p, hw0_p, hw16_p, hother_p 56 (by simp), hother_p 72 (by simp),
      hother_p 80 (by simp), add_lst, List.replicate]
    exact List.Perm.symm (List.Perm.trans (List.Perm.swap _ _ _)
      (List.Perm.cons _ (List.Perm.swap _ _ _)))
  have hres := bo_store_gen h hrem_in hadd_in hrem_add hbo_nz (by decide) (by decide) hx_eq hsame hframe
    (fun o ho => by
      have ho' := hbo_post_perm.mem_iff.mpr ho
      rcases List.mem_append.1 ho' with ho1 | hoz
      · rcases List.mem_append.1 ho1 with hold | hnew
        · exact Or.inr (Or.inl (by rw [hbo_s_eq]; exact List.mem_append_left _ hold))
        · exact Or.inr (Or.inr hnew)
      · exact Or.inl (List.eq_of_mem_replicate hoz))
    (pairwise_disj_perm hbo_post_perm
      (pairwise_disj_old_add_zeros
        (fun o ho => by rw [hbo_s_eq]; exact List.mem_append_left _ ho)
        holds_pw htb_add hpw_add))
    (fun k hk hnz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · rw [h40_p]; exact ⟨by rw [hw16_p]; omega, by rw [hw8_p, hw16_p]; omega⟩
      · exact absurd (hother_p 72 (by simp)) hnz)
  exact ⟨hres.1,
    by rw [show globN post "bo" = globN s "bo" from rfl, h24_p, h32_p]; exact hres.2,
    hbo_nz,
    by rw [show globN post "bo" = globN s "bo" from rfl, h24_p]; exact h24_nz,
    by rw [show globN post "bo" = globN s "bo" from rfl, h32_p]; exact h32_nz,
    h40_p, hother_p⟩

theorem bo_store_56 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si hdr ntx : Nat} {x w : BitVec 64} {mem' : BitVec 64 → HolWordLab 64}
    (h : BlockContext s S Nd si hdr)
    (htb : TrackedDisjIn s S Nd si hdr
      [(memW s (globN s "bo" + 24) + 16, 16 * ntx),
       (memW s (globN s "bo" + 32) + 16, 16 * ntx),
       (w.toNat, 128)])
    (hbo_nz : globN s "bo" ≠ 0)
    (h24_nz : memW s (globN s "bo" + 24) ≠ 0)
    (h32_nz : memW s (globN s "bo" + 32) ≠ 0)
    (h40_nz : memW s (globN s "bo" + 40) ≠ 0)
    (hw_nz : w.toNat ≠ 0)
    (hz : ∀ off ∈ ([56, 64, 72, 80] : List Nat), memW s (globN s "bo" + off) = 0)
    (hx_eq : x.toNat = globN s "bo" + 56)
    (hsame : mem' x = .word w) (hframe : ∀ a : BitVec 64, a ≠ x → mem' a = s.memory a) :
    let post := {s with memory := mem'}
    BlockContext post S Nd si hdr ∧
      TrackedDisjIn post S Nd si hdr
        [(memW post (globN post "bo" + 24) + 16, 16 * ntx),
         (memW post (globN post "bo" + 32) + 16, 16 * ntx)] ∧
      globN post "bo" ≠ 0 ∧
      memW post (globN post "bo" + 24) ≠ 0 ∧
      memW post (globN post "bo" + 32) ≠ 0 ∧
      memW post (globN post "bo" + 40) ≠ 0 ∧
      memW post (globN post "bo" + 56) = w.toNat ∧
      (∀ off ∈ ([64, 72, 80] : List Nat), memW post (globN post "bo" + off) = 0) := by
  intro post
  let txs := memW s (globN s "bo" + 24)
  let rcs := memW s (globN s "bo" + 32)
  let logs := memW s (globN s "bo" + 40)
  have htxs_nz : txs ≠ 0 := h24_nz
  have hrcs_nz : rcs ≠ 0 := h32_nz
  have hlogs_nz : logs ≠ 0 := h40_nz
  have hsplit := trackedDisjIn_drop_head_of_append
    (bs := [(txs + 16, 16 * ntx), (rcs + 16, 16 * ntx)])
    (a := (w.toNat, 128)) (rest := []) (by simpa [txs, rcs] using htb)
  obtain ⟨hrem_in, hw128_tb, hrem_disj, hreg_disj, hhash_disj⟩ := hsplit
  have hadd_in : TrackedDisjIn s S Nd si hdr [(w.toNat, 128)] :=
    ⟨hw128_tb, List.pairwise_singleton _ _, hreg_disj, hhash_disj⟩
  have h24_p : memW post (globN s "bo" + 24) = txs :=
    memW_bo_store_ne h.arena.2 h.world hbo_nz (by decide) (by decide) hx_eq hframe
  have h32_p : memW post (globN s "bo" + 32) = rcs :=
    memW_bo_store_ne h.arena.2 h.world hbo_nz (by decide) (by decide) hx_eq hframe
  have h40_p : memW post (globN s "bo" + 40) = logs :=
    memW_bo_store_ne h.arena.2 h.world hbo_nz (by decide) (by decide) hx_eq hframe
  have h56_p : memW post (globN s "bo" + 56) = w.toNat :=
    memW_bo_store_same h.arena.2 h.world hbo_nz (by decide) hx_eq hsame
  have hother_p : ∀ off ∈ ([64, 72, 80] : List Nat),
      memW post (globN s "bo" + off) = 0 := by
    intro off hoff
    have hoff_lt : off + 8 ≤ 88 ∧ off ≠ 56 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl <;> omega
    rw [memW_bo_store_ne h.arena.2 h.world hbo_nz hoff_lt.1 hoff_lt.2 hx_eq hframe]
    exact hz off (List.mem_cons_of_mem _ hoff)
  obtain ⟨hl0, _, hl16, hlok_imp⟩ :=
    bo_lst_mem_preserved h.arena.2 h.world hbo_nz (Or.inl rfl) hlogs_nz (by decide) hx_eq hframe
  have hl0' : memW post logs = memW s logs := hl0
  have hl16' : memW post (logs + 16) = memW s (logs + 16) := hl16
  have hlok_s : LstOK s logs :=
    h.world.1.2.2.2.2.2.2.2.2.2.2.1 hbo_nz 40 (by simp) hlogs_nz
  have hlok_p : LstOK post logs := hlok_imp hlok_s
  let logs_arr : Ivl :=
    if memW s logs = 0 ∨ memW s (logs + 16) = 0 then (0, 0)
    else (memW s logs, 8 * memW s (logs + 16))
  let olds : List Ivl := [(txs, 16), (rcs, 16), (logs, 24), logs_arr]
  have hbo_s_perm : (olds ++ List.replicate 3 (0, 0)).Perm (blockOutObjects s) := by
    unfold blockOutObjects
    simp [txs, rcs, logs, logs_arr, olds, hbo_nz, htxs_nz, hrcs_nz, hlogs_nz,
      hz 56 (by simp), hz 72 (by simp), hz 80 (by simp), List.replicate]
    exact List.Perm.symm (List.Perm.trans (List.Perm.swap _ _ _)
      (List.Perm.cons _ (List.Perm.swap _ _ _)))
  have holds_pw : olds.Pairwise Disj := by
    have hpw_s := pairwise_disj_perm hbo_s_perm.symm (bo_s_pairwise h.world)
    exact (List.pairwise_append.1 hpw_s).1
  have hbo_post_perm : (olds ++ [(w.toNat, 128)] ++ List.replicate 2 (0, 0)).Perm
      (blockOutObjects post) := by
    unfold blockOutObjects
    simp [show globN post "bo" = globN s "bo" from rfl, hbo_nz, htxs_nz, hrcs_nz, hlogs_nz, hw_nz,
      h24_p, h32_p, h40_p, h56_p, hl0', hl16', logs_arr, olds,
      hother_p 72 (by simp), hother_p 80 (by simp), List.replicate]
    exact List.Perm.symm (List.Perm.trans (List.Perm.swap _ _ _)
      (List.Perm.cons _ (List.Perm.swap _ _ _)))
  have hres := bo_store_gen h hrem_in hadd_in hrem_disj hbo_nz (by decide) (by decide) hx_eq hsame hframe
    (fun o ho => by
      have ho' := hbo_post_perm.mem_iff.mpr ho
      rcases List.mem_append.1 ho' with ho1 | hoz
      · rcases List.mem_append.1 ho1 with hold | hnew
        · exact Or.inr (Or.inl (hbo_s_perm.mem_iff.mp (List.mem_append_left _ hold)))
        · exact Or.inr (Or.inr hnew)
      · exact Or.inl (List.eq_of_mem_replicate hoz))
    (pairwise_disj_perm hbo_post_perm
      (pairwise_disj_old_add_zeros
        (fun o ho => hbo_s_perm.mem_iff.mp (List.mem_append_left _ ho))
        holds_pw hw128_tb (List.pairwise_singleton _ _)))
    (fun k hk hnz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · rw [h40_p]; exact hlok_p
      · exact absurd (hother_p 72 (by simp)) hnz)
  exact ⟨hres.1,
    by rw [show globN post "bo" = globN s "bo" from rfl, h24_p, h32_p]; exact hres.2,
    hbo_nz,
    by rw [show globN post "bo" = globN s "bo" from rfl, h24_p]; exact h24_nz,
    by rw [show globN post "bo" = globN s "bo" from rfl, h32_p]; exact h32_nz,
    by rw [show globN post "bo" = globN s "bo" from rfl, h40_p]; exact h40_nz,
    h56_p, hother_p⟩

theorem bo_store_72 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si hdr ntx : Nat} {x w : BitVec 64} {mem' : BitVec 64 → HolWordLab 64}
    (h : BlockContext s S Nd si hdr)
    (htb : TrackedDisjIn s S Nd si hdr
      [(memW s (globN s "bo" + 24) + 16, 16 * ntx),
       (memW s (globN s "bo" + 32) + 16, 16 * ntx),
       (w.toNat, 24), (memW s w.toNat, 128)])
    (hbo_nz : globN s "bo" ≠ 0)
    (h24_nz : memW s (globN s "bo" + 24) ≠ 0)
    (h32_nz : memW s (globN s "bo" + 32) ≠ 0)
    (h40_nz : memW s (globN s "bo" + 40) ≠ 0)
    (h56_nz : memW s (globN s "bo" + 56) ≠ 0)
    (hw_nz : w.toNat ≠ 0) (hw0_nz : memW s w.toNat ≠ 0)
    (hw8 : memW s (w.toNat + 8) = 0) (hw16 : memW s (w.toNat + 16) = 16)
    (hz : ∀ off ∈ ([64, 72, 80] : List Nat), memW s (globN s "bo" + off) = 0)
    (hx_eq : x.toNat = globN s "bo" + 72)
    (hsame : mem' x = .word w) (hframe : ∀ a : BitVec 64, a ≠ x → mem' a = s.memory a) :
    let post := {s with memory := mem'}
    BlockContext post S Nd si hdr ∧
      TrackedDisjIn post S Nd si hdr
        [(memW post (globN post "bo" + 24) + 16, 16 * ntx),
         (memW post (globN post "bo" + 32) + 16, 16 * ntx)] ∧
      globN post "bo" ≠ 0 ∧
      memW post (globN post "bo" + 24) ≠ 0 ∧
      memW post (globN post "bo" + 32) ≠ 0 ∧
      memW post (globN post "bo" + 40) ≠ 0 ∧
      memW post (globN post "bo" + 56) ≠ 0 ∧
      memW post (globN post "bo" + 64) = 0 ∧
      memW post (globN post "bo" + 72) = w.toNat ∧
      memW post (globN post "bo" + 80) = 0 := by
  intro post
  let txs := memW s (globN s "bo" + 24)
  let rcs := memW s (globN s "bo" + 32)
  let logs := memW s (globN s "bo" + 40)
  let reqs := memW s (globN s "bo" + 56)
  have htxs_nz : txs ≠ 0 := h24_nz
  have hrcs_nz : rcs ≠ 0 := h32_nz
  have hlogs_nz : logs ≠ 0 := h40_nz
  have hreqs_nz : reqs ≠ 0 := h56_nz
  let bs_rem : List Ivl := [(txs + 16, 16 * ntx), (rcs + 16, 16 * ntx)]
  let add_lst : List Ivl := [(w.toNat, 24), (memW s w.toNat, 128)]
  have htb_eq : TrackedDisjIn s S Nd si hdr (bs_rem ++ add_lst) :=
    by simpa [bs_rem, add_lst, txs, rcs] using htb
  obtain ⟨htb_all, hpw_all, hreg_all, hhash_all⟩ := htb_eq
  obtain ⟨htb_rem, htb_add⟩ := trackedBlocks_append.1 htb_all
  obtain ⟨hpw_rem, hpw_add, hrem_add⟩ := List.pairwise_append.1 hpw_all
  have hrem_in : TrackedDisjIn s S Nd si hdr bs_rem :=
    ⟨htb_rem, hpw_rem,
     fun a ha b hb => hreg_all a ha b (List.mem_append_left _ hb),
     fun hnz a ha b hb => hhash_all hnz a ha b (List.mem_append_left _ hb)⟩
  have hadd_in : TrackedDisjIn s S Nd si hdr add_lst :=
    ⟨htb_add, hpw_add,
     fun a ha b hb => hreg_all a ha b (List.mem_append_right _ hb),
     fun hnz a ha b hb => hhash_all hnz a ha b (List.mem_append_right _ hb)⟩
  have hw24_tb : TrackedBlocks s S Nd [(w.toNat, 24)] := fun b hb => by
    rw [List.mem_singleton.mp hb]; exact htb_add _ List.mem_cons_self
  obtain ⟨hal_w, hw_w, _, _, hu_w⟩ :=
    tracked_alloc_words_post h.arena hw24_tb hbo_nz (by decide) hx_eq hframe
  have hbound_w := (ivl_allocated_bound h.arena.2 hal_w).2
  have hw0_p : memW post w.toNat = memW s w.toNat :=
    memW_eq_of_ivlUnhit hu_w hw_w.1 hbound_w (by dsimp; omega)
  have hw8_p : memW post (w.toNat + 8) = 0 := by
    rw [memW_eq_of_ivlUnhit hu_w (by have := hw_w.1; omega) hbound_w (by dsimp; omega), hw8]
  have hw16_p : memW post (w.toNat + 16) = 16 := by
    rw [memW_eq_of_ivlUnhit hu_w (by have := hw_w.1; omega) hbound_w (by dsimp; omega), hw16]
  have h24_p : memW post (globN s "bo" + 24) = txs :=
    memW_bo_store_ne h.arena.2 h.world hbo_nz (by decide) (by decide) hx_eq hframe
  have h32_p : memW post (globN s "bo" + 32) = rcs :=
    memW_bo_store_ne h.arena.2 h.world hbo_nz (by decide) (by decide) hx_eq hframe
  have h40_p : memW post (globN s "bo" + 40) = logs :=
    memW_bo_store_ne h.arena.2 h.world hbo_nz (by decide) (by decide) hx_eq hframe
  have h56_p : memW post (globN s "bo" + 56) = reqs :=
    memW_bo_store_ne h.arena.2 h.world hbo_nz (by decide) (by decide) hx_eq hframe
  have h64_p : memW post (globN s "bo" + 64) = 0 := by
    rw [memW_bo_store_ne h.arena.2 h.world hbo_nz (by decide) (by decide) hx_eq hframe]
    exact hz 64 (by simp)
  have h72_p : memW post (globN s "bo" + 72) = w.toNat :=
    memW_bo_store_same h.arena.2 h.world hbo_nz (by decide) hx_eq hsame
  have h80_p : memW post (globN s "bo" + 80) = 0 := by
    rw [memW_bo_store_ne h.arena.2 h.world hbo_nz (by decide) (by decide) hx_eq hframe]
    exact hz 80 (by simp)
  obtain ⟨hl0, _, hl16, hlok_imp⟩ :=
    bo_lst_mem_preserved h.arena.2 h.world hbo_nz (Or.inl rfl) hlogs_nz (by decide) hx_eq hframe
  have hl0' : memW post logs = memW s logs := hl0
  have hl16' : memW post (logs + 16) = memW s (logs + 16) := hl16
  have hlok_s : LstOK s logs :=
    h.world.1.2.2.2.2.2.2.2.2.2.2.1 hbo_nz 40 (by simp) hlogs_nz
  have hlok_p : LstOK post logs := hlok_imp hlok_s
  let logs_arr : Ivl :=
    if memW s logs = 0 ∨ memW s (logs + 16) = 0 then (0, 0)
    else (memW s logs, 8 * memW s (logs + 16))
  let olds : List Ivl := [(txs, 16), (rcs, 16), (reqs, 128), (logs, 24), logs_arr]
  have hbo_s_eq : blockOutObjects s = olds ++ List.replicate 2 (0, 0) := by
    unfold blockOutObjects
    simp [txs, rcs, logs, reqs, logs_arr, olds, hbo_nz, htxs_nz, hrcs_nz, hlogs_nz, hreqs_nz,
      hz 72 (by simp), hz 80 (by simp), List.replicate]
  have holds_pw : olds.Pairwise Disj := by
    have hpw_s := bo_s_pairwise h.world
    rw [hbo_s_eq] at hpw_s
    exact (List.pairwise_append.1 hpw_s).1
  have hbo_post_eq : blockOutObjects post = olds ++ add_lst ++ List.replicate 0 (0, 0) := by
    unfold blockOutObjects
    simp [show globN post "bo" = globN s "bo" from rfl, hbo_nz, htxs_nz, hrcs_nz, hlogs_nz,
      hreqs_nz, hw_nz, hw0_nz, h24_p, h32_p, h40_p, h56_p, h72_p, h80_p,
      hl0', hl16', hw0_p, hw16_p, logs_arr, olds, add_lst, List.replicate]
  have hres := bo_store_gen h hrem_in hadd_in hrem_add hbo_nz (by decide) (by decide) hx_eq hsame hframe
    (fun o ho => by
      rw [hbo_post_eq] at ho
      rcases List.mem_append.1 ho with ho1 | hoz
      · rcases List.mem_append.1 ho1 with hold | hnew
        · exact Or.inr (Or.inl (by rw [hbo_s_eq]; exact List.mem_append_left _ hold))
        · exact Or.inr (Or.inr hnew)
      · exact Or.inl (List.eq_of_mem_replicate hoz))
    (by rw [hbo_post_eq]
        exact pairwise_disj_old_add_zeros
          (fun o ho => by rw [hbo_s_eq]; exact List.mem_append_left _ ho)
          holds_pw htb_add hpw_add)
    (fun k hk hnz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · rw [h40_p]; exact hlok_p
      · rw [h72_p]; exact ⟨by rw [hw16_p]; omega, by rw [hw8_p, hw16_p]; omega⟩)
  exact ⟨hres.1,
    by rw [show globN post "bo" = globN s "bo" from rfl, h24_p, h32_p]; exact hres.2,
    hbo_nz,
    by rw [show globN post "bo" = globN s "bo" from rfl, h24_p]; exact h24_nz,
    by rw [show globN post "bo" = globN s "bo" from rfl, h32_p]; exact h32_nz,
    by rw [show globN post "bo" = globN s "bo" from rfl, h40_p]; exact h40_nz,
    by rw [show globN post "bo" = globN s "bo" from rfl, h56_p]; exact h56_nz,
    h64_p, h72_p, h80_p⟩

theorem disj_join_adj {p a b : Nat} {j : Ivl}
    (h1 : Disj (p, a) j) (h2 : Disj (p + a, b) j) :
    Disj (p, a + b) j := by
  by_cases hab : a + b = 0
  · exact Or.inl (by dsimp; omega)
  · by_cases hj : j.2 = 0
    · exact Or.inr (Or.inl hj)
    · by_cases ha : a = 0
      · subst ha; simpa using h2
      · by_cases hb : b = 0
        · subst hb; simpa using h1
        · rcases h1 with hz1 | hz2 | hle1 | hge1
          · dsimp at hz1; omega
          · exact Or.inr (Or.inl hz2)
          · rcases h2 with hz1 | hz2 | hle2 | hge2
            · dsimp at hz1; omega
            · exact Or.inr (Or.inl hz2)
            · exact Or.inr (Or.inr (Or.inl (by dsimp at hle2 ⊢; omega)))
            · dsimp at hle1 hge2; omega
          · exact Or.inr (Or.inr (Or.inr (by dsimp at hge1 ⊢; omega)))

theorem disj_join_adj_both {p a b q c d : Nat}
    (h11 : Disj (p, a) (q, c)) (h12 : Disj (p, a) (q + c, d))
    (h21 : Disj (p + a, b) (q, c)) (h22 : Disj (p + a, b) (q + c, d)) :
    Disj (p, a + b) (q, c + d) := by
  exact disj_join_adj (disj_join_adj h11.flip h12.flip).flip
    (disj_join_adj h21.flip h22.flip).flip

theorem wordsOK_join_adj {F : Type} {s : PanSemStateFiniteExact 64 F} {p a b : Nat}
    (hw1 : WordsOK s (p, a)) (hw2 : WordsOK s (p + a, b)) :
    WordsOK s (p, a + b) := by
  refine ⟨hw1.1, by have := hw1.2.1; have := hw2.2.1; omega, fun k hk => ?_⟩
  have ha8 : a % 8 = 0 := hw1.2.1
  have hb8 : b % 8 = 0 := hw2.2.1
  have hk_bound : k < a / 8 + b / 8 := by dsimp at hk; omega
  by_cases hka : k < a / 8
  · exact hw1.2.2 k hka
  · have hkb : k - a / 8 < b / 8 := by omega
    obtain ⟨w, hdom, hm⟩ := hw2.2.2 (k - a / 8) hkb
    have heq_addr : p + 8 * k = p + a + 8 * (k - a / 8) := by omega
    rw [heq_addr]
    exact ⟨w, hdom, hm⟩

theorem allocated_join_heap_or_disj {F : Type} {s : PanSemStateFiniteExact 64 F} {p a b : Nat}
    (hA : ArenaOK s) (ha_pos : 0 < a) (hal1 : Allocated s (p, a))
    (htb2 : Inside (p + a, b) sourceBase (globN s "heap_ptr")) :
    Allocated s (p, a + b) := by
  have hsep : heapLimit ≤ scratchStart := by decide
  have hhp : globN s "heap_ptr" ≤ heapLimit := hA.2.1
  have hfmp1 : scratchStart ≤ globN s "frame_mem_ptr" := hA.2.2.1
  have hfmp2 : globN s "frame_mem_ptr" ≤ globN s "scratch_ptr" := hA.2.2.2.1
  rcases hal1 with h1 | h1
  · exact Or.inl ⟨h1.1, by dsimp [Inside] at h1 htb2 ⊢; omega⟩
  · exfalso; dsimp [Inside] at h1 htb2; omega

theorem bo_joined_array_ok {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {p ntx : Nat} {x : BitVec 64} {mem' : BitVec 64 → HolWordLab 64}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (hbo_nz : globN s "bo" ≠ 0)
    (ho16 : (p, 16) ∈ blockOutObjects s)
    (htb : TrackedBlocks s S Nd [(p + 16, 16 * ntx)])
    (hx_eq : x.toNat = globN s "bo" + 80)
    (hframe : ∀ a : BitVec 64, a ≠ x → mem' a = s.memory a) :
    let post := {s with memory := mem'}
    Allocated post (p, 16 * ntx + 16) ∧
      WordsOK post (p, 16 * ntx + 16) ∧
      Disj (p, 16 * ntx + 16) (globN s "bo", 88) ∧
      (∀ j ∈ worldOwned s S Nd, j ≠ (p, 16) → Disj (p, 16 * ntx + 16) j) := by
  intro post
  have hfix16 : (p, 16) ∈ fixedObjects s := by
    unfold fixedObjects
    exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr ho16)))
  rcases hW.2.2.1.1 (p, 16) hfix16 with hz | ⟨hal1_s, hw1_s⟩
  · cases hz
  · have hgp : GuestInv post := guestInv_congr (s := s) rfl rfl rfl rfl hA.1
    have hal1_p : Allocated post (p, 16) := hal1_s
    have hw1_p : WordsOK post (p, 16) := wordsOK_transfer hA.1 hgp hw1_s
    obtain ⟨_, hw2_p, hd2_bo, hd2_ow, _⟩ :=
      tracked_alloc_words_post hA htb hbo_nz (by decide) hx_eq hframe
    have hin2 : Inside (p + 16, 16 * ntx) sourceBase (globN post "heap_ptr") :=
      (htb (p + 16, 16 * ntx) List.mem_cons_self).2.2.1
    have hal_join : Allocated post (p, 16 + 16 * ntx) :=
      allocated_join_heap_or_disj hA.2 (by decide) hal1_p hin2
    have hw_join : WordsOK post (p, 16 + 16 * ntx) := wordsOK_join_adj hw1_p hw2_p
    have hd1_bo : Disj (p, 16) (globN s "bo", 88) :=
      (bo_disj_worldOwned_nonbo hW hbo_nz (p, 16) (blockOutObj_mem_worldOwned ho16)
        (fun heq => by have := (Prod.mk.inj heq).2; omega)).flip
    have hd_bo_join : Disj (p, 16 + 16 * ntx) (globN s "bo", 88) :=
      disj_join_adj hd1_bo hd2_bo
    have heq_len : 16 * ntx + 16 = 16 + 16 * ntx := by omega
    rw [heq_len]
    refine ⟨hal_join, hw_join, hd_bo_join, fun j hj hj_ne => ?_⟩
    apply disj_join_adj _ (hd2_ow j hj)
    rcases List.mem_append.1 hj with hj1 | hjnd
    · rcases List.mem_append.1 hj1 with hjtab | hjfix
      · obtain ⟨t, htS, htfp⟩ := List.mem_flatMap.1 hjtab
        exact (((hW.1.2.1 t htS).2 j htfp).2 (p, 16) hfix16).flip
      · obtain ⟨i1, hi1, heq1⟩ := List.mem_iff_getElem.1 hfix16
        obtain ⟨i2, hi2, heq2⟩ := List.mem_iff_getElem.1 hjfix
        have hij : i1 ≠ i2 := by
          intro hij; subst hij
          rw [heq1] at heq2
          exact hj_ne heq2.symm
        rw [← heq1, ← heq2]
        exact list_pairwise_rel (fun _ _ h => Disj.flip h) hW.2.2.1.2 hi1 hi2 hij
    · exact ((hW.2.2.2.2.1 j hjnd).2 (p, 16) hfix16).flip

theorem bo_store_24 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si hdr ntx : Nat} {x w : BitVec 64} {mem' : BitVec 64 → HolWordLab 64}
    (h : BlockContext s S Nd si hdr)
    (htb : TrackedDisjIn s S Nd si hdr [(w.toNat, 16), (w.toNat + 16, 16 * ntx)])
    (hbo_nz : globN s "bo" ≠ 0) (hw_nz : w.toNat ≠ 0)
    (hz : ∀ off ∈ ([24, 32, 40, 56, 64, 72, 80] : List Nat), memW s (globN s "bo" + off) = 0)
    (hx_eq : x.toNat = globN s "bo" + 24)
    (hsame : mem' x = .word w) (hframe : ∀ a : BitVec 64, a ≠ x → mem' a = s.memory a) :
    let post := {s with memory := mem'}
    BlockContext post S Nd si hdr ∧
      TrackedDisjIn post S Nd si hdr [(w.toNat + 16, 16 * ntx)] ∧
      globN post "bo" ≠ 0 ∧
      memW post (globN post "bo" + 24) = w.toNat ∧
      (∀ off ∈ ([32, 40, 56, 64, 72, 80] : List Nat), memW post (globN post "bo" + off) = 0) := by
  intro post
  have hsplit := trackedDisjIn_drop_head_of_append (bs := []) (a := (w.toNat, 16))
    (rest := [(w.toNat + 16, 16 * ntx)]) (by simpa using htb)
  obtain ⟨hrem_in, hw16_tb, hrem_disj, hreg_disj, hhash_disj⟩ := hsplit
  have h24_p : memW post (globN s "bo" + 24) = w.toNat :=
    memW_bo_store_same h.arena.2 h.world hbo_nz (by decide) hx_eq hsame
  have hother_p : ∀ off ∈ ([32, 40, 56, 64, 72, 80] : List Nat),
      memW post (globN s "bo" + off) = 0 := by
    intro off hoff
    have hoff_lt : off + 8 ≤ 88 ∧ off ≠ 24 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    rw [memW_bo_store_ne h.arena.2 h.world hbo_nz hoff_lt.1 hoff_lt.2 hx_eq hframe]
    exact hz off (List.mem_cons_of_mem _ hoff)
  have hbo_post_eq : blockOutObjects post = (w.toNat, 16) :: List.replicate 6 (0, 0) := by
    unfold blockOutObjects
    simp [show globN post "bo" = globN s "bo" from rfl, hbo_nz, hw_nz, h24_p,
      hother_p 32 (by simp), hother_p 40 (by simp), hother_p 56 (by simp),
      hother_p 72 (by simp), hother_p 80 (by simp), List.replicate]
  obtain ⟨hal_w, hw_w, hd_bo_w, hd_ow_w, _⟩ :=
    tracked_alloc_words_post h.arena hw16_tb hbo_nz (by decide) hx_eq hframe
  have hres := blockContext_word_store_bo h hrem_in.1 hbo_nz (by decide) (by decide) hx_eq hsame hframe
    (fun o ho => by
      rw [hbo_post_eq] at ho
      rcases List.mem_cons.1 ho with rfl | hoz
      · exact Or.inr ⟨hal_w, hw_w, hd_bo_w, Or.inr (fun j hj _ => hd_ow_w j hj)⟩
      · exact Or.inl (List.eq_of_mem_replicate hoz))
    (by rw [hbo_post_eq]
        exact pairwise_disj_append_zeros (xs := [(w.toNat, 16)]) (k := 6) (List.pairwise_singleton _ _))
    (fun k hk hnz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · exact absurd (hother_p 40 (by simp)) hnz
      · exact absurd (hother_p 72 (by simp)) hnz)
    (fun a ha o ho => by
      rw [hbo_post_eq] at ho
      rcases List.mem_cons.1 ho with rfl | hoz
      · rcases List.mem_append.1 ha with ha1 | habs
        · rcases List.mem_append.1 ha1 with hareg | hahash
          · exact hreg_disj a hareg _ List.mem_cons_self
          · by_cases hbnz : globN s "block_hashes_n" = 0
            · simp [hbnz] at hahash
            · simp only [hbnz, ↓reduceIte] at hahash
              exact hhash_disj hbnz a hahash _ List.mem_cons_self
        · exact hrem_disj a (by simpa using habs) _ List.mem_cons_self
      · rw [List.eq_of_mem_replicate hoz]; exact disj_zero_right a)
  have hcin : ∀ c ∈ inputRegions s si hdr,
      c.1 % 8 = 0 ∧ Inside c sourceBase (globN s "heap_ptr") ∧ WordsOK s c :=
    fun c hm => ⟨(h.regions c hm).1, (h.regions c hm).2.2.1, (h.regions c hm).2.2.2.1⟩
  have hbo_mem_ow := bo_in_worldOwned (S := S) (Nd := Nd) hbo_nz
  have hx_in_bo : Inside (x.toNat, 8) (globN s "bo") (globN s "bo" + 88) := by
    unfold Inside; dsimp; omega
  have hu_reg : ∀ c ∈ inputRegions s si hdr, IvlUnhit s post c := by
    intro c hc
    obtain ⟨hc8, _, _, _, hd_ow⟩ := h.regions c hc
    exact ivlUnhit_of_single_cell_disj (fun _ => hc8) hframe
      (disj_of_inside_left hx_in_bo (hd_ow _ hbo_mem_ow).flip).flip
  have hreg_eq : inputRegions post si hdr = inputRegions s si hdr :=
    inputRegions_eq_of_unhit h.arena hcin hu_reg rfl
  exact ⟨hres.1, ⟨hres.2, hrem_in.2.1, by rw [hreg_eq]; exact hrem_in.2.2.1, hrem_in.2.2.2⟩,
    hbo_nz, h24_p, hother_p⟩

theorem bo_store_80 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si hdr : Nat} {x w : BitVec 64} {mem' : BitVec 64 → HolWordLab 64}
    (h : BlockContext s S Nd si hdr)
    (htb : TrackedDisjIn s S Nd si hdr
      [(memW s (globN s "bo" + 24) + 16, 16 * w.toNat),
       (memW s (globN s "bo" + 32) + 16, 16 * w.toNat)])
    (hbo_nz : globN s "bo" ≠ 0)
    (h24_nz : memW s (globN s "bo" + 24) ≠ 0)
    (h32_nz : memW s (globN s "bo" + 32) ≠ 0)
    (h40_nz : memW s (globN s "bo" + 40) ≠ 0)
    (h56_nz : memW s (globN s "bo" + 56) ≠ 0)
    (h64_z : memW s (globN s "bo" + 64) = 0)
    (h72_nz : memW s (globN s "bo" + 72) ≠ 0)
    (h80_z : memW s (globN s "bo" + 80) = 0)
    (hx_eq : x.toNat = globN s "bo" + 80)
    (hsame : mem' x = .word w) (hframe : ∀ a : BitVec 64, a ≠ x → mem' a = s.memory a) :
    let post := {s with memory := mem'}
    BlockContext post S Nd si hdr ∧
      globN post "bo" ≠ 0 ∧
      memW post (globN post "bo" + 24) ≠ 0 ∧
      memW post (globN post "bo" + 32) ≠ 0 ∧
      memW post (globN post "bo" + 40) ≠ 0 ∧
      memW post (globN post "bo" + 56) ≠ 0 ∧
      memW post (globN post "bo" + 64) = 0 ∧
      memW post (globN post "bo" + 72) ≠ 0 ∧
      memW post (globN post "bo" + 80) = w.toNat := by
  intro post
  let ntx := w.toNat
  let txs := memW s (globN s "bo" + 24)
  let rcs := memW s (globN s "bo" + 32)
  let logs := memW s (globN s "bo" + 40)
  let reqs := memW s (globN s "bo" + 56)
  let rls := memW s (globN s "bo" + 72)
  have htxs_nz : txs ≠ 0 := h24_nz
  have hrcs_nz : rcs ≠ 0 := h32_nz
  have hlogs_nz : logs ≠ 0 := h40_nz
  have hreqs_nz : reqs ≠ 0 := h56_nz
  have hrls_nz : rls ≠ 0 := h72_nz
  have h24_p : memW post (globN s "bo" + 24) = txs :=
    memW_bo_store_ne h.arena.2 h.world hbo_nz (by decide) (by decide) hx_eq hframe
  have h32_p : memW post (globN s "bo" + 32) = rcs :=
    memW_bo_store_ne h.arena.2 h.world hbo_nz (by decide) (by decide) hx_eq hframe
  have h40_p : memW post (globN s "bo" + 40) = logs :=
    memW_bo_store_ne h.arena.2 h.world hbo_nz (by decide) (by decide) hx_eq hframe
  have h56_p : memW post (globN s "bo" + 56) = reqs :=
    memW_bo_store_ne h.arena.2 h.world hbo_nz (by decide) (by decide) hx_eq hframe
  have h64_p : memW post (globN s "bo" + 64) = 0 := by
    rw [memW_bo_store_ne h.arena.2 h.world hbo_nz (by decide) (by decide) hx_eq hframe]; exact h64_z
  have h72_p : memW post (globN s "bo" + 72) = rls :=
    memW_bo_store_ne h.arena.2 h.world hbo_nz (by decide) (by decide) hx_eq hframe
  have h80_p : memW post (globN s "bo" + 80) = ntx :=
    memW_bo_store_same h.arena.2 h.world hbo_nz (by decide) hx_eq hsame
  obtain ⟨hl0, _, hl16, hlok_logs_imp⟩ :=
    bo_lst_mem_preserved h.arena.2 h.world hbo_nz (Or.inl rfl) hlogs_nz (by decide) hx_eq hframe
  have hl0' : memW post logs = memW s logs := hl0
  have hl16' : memW post (logs + 16) = memW s (logs + 16) := hl16
  have hlok_logs : LstOK post logs :=
    hlok_logs_imp (h.world.1.2.2.2.2.2.2.2.2.2.2.1 hbo_nz 40 (by simp) hlogs_nz)
  obtain ⟨hr0, _, hr16, hlok_rls_imp⟩ :=
    bo_lst_mem_preserved h.arena.2 h.world hbo_nz (Or.inr rfl) hrls_nz (by decide) hx_eq hframe
  have hr0' : memW post rls = memW s rls := hr0
  have hr16' : memW post (rls + 16) = memW s (rls + 16) := hr16
  have hlok_rls : LstOK post rls :=
    hlok_rls_imp (h.world.1.2.2.2.2.2.2.2.2.2.2.1 hbo_nz 72 (by simp) hrls_nz)
  let logs_arr : Ivl :=
    if memW s logs = 0 ∨ memW s (logs + 16) = 0 then (0, 0)
    else (memW s logs, 8 * memW s (logs + 16))
  let rls_arr : Ivl :=
    if memW s rls = 0 ∨ memW s (rls + 16) = 0 then (0, 0)
    else (memW s rls, 8 * memW s (rls + 16))
  let rest : List Ivl := [(reqs, 128), (logs, 24), logs_arr, (rls, 24), rls_arr]
  have hbo_s_eq : blockOutObjects s = (txs, 16) :: (rcs, 16) :: rest := by
    unfold blockOutObjects
    simp [txs, rcs, logs, reqs, rls, logs_arr, rls_arr, rest,
      hbo_nz, htxs_nz, hrcs_nz, hlogs_nz, hreqs_nz, hrls_nz, h80_z]
  have hbo_post_eq : blockOutObjects post =
      (txs, 16 * ntx + 16) :: (rcs, 16 * ntx + 16) :: rest := by
    unfold blockOutObjects
    simp [show globN post "bo" = globN s "bo" from rfl,
      txs, rcs, logs, reqs, rls, ntx, logs_arr, rls_arr, rest,
      hbo_nz, htxs_nz, hrcs_nz, hlogs_nz, hreqs_nz, hrls_nz,
      h24_p, h32_p, h40_p, h56_p, h72_p, h80_p, hl0', hl16', hr0', hr16']
  have htxs16_in : (txs, 16) ∈ blockOutObjects s := by rw [hbo_s_eq]; simp
  have hrcs16_in : (rcs, 16) ∈ blockOutObjects s := by rw [hbo_s_eq]; simp
  have hrest_sub : ∀ r ∈ rest, r ∈ blockOutObjects s := fun r hr => by
    rw [hbo_s_eq]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)
  have hpw_s := bo_s_pairwise h.world
  rw [hbo_s_eq] at hpw_s
  obtain ⟨hd_txs16_all, hpw_s1⟩ := List.pairwise_cons.1 hpw_s
  obtain ⟨hd_rcs16_rest, hpw_rest⟩ := List.pairwise_cons.1 hpw_s1
  have hd_txs16_rcs16 : Disj (txs, 16) (rcs, 16) := hd_txs16_all _ List.mem_cons_self
  have hd_txs16_rest : ∀ r ∈ rest, Disj (txs, 16) r :=
    fun r hr => hd_txs16_all _ (List.mem_cons_of_mem _ hr)
  have htb_tx : TrackedBlocks s S Nd [(txs + 16, 16 * ntx)] := fun b hb => by
    rw [List.mem_singleton.mp hb]; exact htb.1 _ List.mem_cons_self
  have htb_rc : TrackedBlocks s S Nd [(rcs + 16, 16 * ntx)] := fun b hb => by
    rw [List.mem_singleton.mp hb]; exact htb.1 _ (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨hal_txj, hw_txj, hdbo_txj, hdow_txj⟩ :=
    bo_joined_array_ok h.arena h.world hbo_nz htxs16_in htb_tx hx_eq hframe
  obtain ⟨hal_rcj, hw_rcj, hdbo_rcj, hdow_rcj⟩ :=
    bo_joined_array_ok h.arena h.world hbo_nz hrcs16_in htb_rc hx_eq hframe
  have hd_txtail_rctail : Disj (txs + 16, 16 * ntx) (rcs + 16, 16 * ntx) :=
    (List.pairwise_cons.1 htb.2.1).1 _ List.mem_cons_self
  have hd_txj_rcj : Disj (txs, 16 * ntx + 16) (rcs, 16 * ntx + 16) := by
    have heq : 16 * ntx + 16 = 16 + 16 * ntx := by omega
    rw [heq]
    exact disj_join_adj_both hd_txs16_rcs16
      ((htb_rc _ List.mem_cons_self).2.2.2.2 _ (blockOutObj_mem_worldOwned htxs16_in)).flip
      ((htb_tx _ List.mem_cons_self).2.2.2.2 _ (blockOutObj_mem_worldOwned hrcs16_in))
      hd_txtail_rctail
  have hd_txj_rest : ∀ r ∈ rest, Disj (txs, 16 * ntx + 16) r := by
    intro r hr
    have heq : 16 * ntx + 16 = 16 + 16 * ntx := by omega
    rw [heq]
    exact disj_join_adj (hd_txs16_rest r hr)
      ((htb_tx _ List.mem_cons_self).2.2.2.2 _ (blockOutObj_mem_worldOwned (hrest_sub r hr)))
  have hd_rcj_rest : ∀ r ∈ rest, Disj (rcs, 16 * ntx + 16) r := by
    intro r hr
    have heq : 16 * ntx + 16 = 16 + 16 * ntx := by omega
    rw [heq]
    exact disj_join_adj (hd_rcs16_rest r hr)
      ((htb_rc _ List.mem_cons_self).2.2.2.2 _ (blockOutObj_mem_worldOwned (hrest_sub r hr)))
  have hpw_post : (blockOutObjects post).Pairwise Disj := by
    rw [hbo_post_eq]
    refine List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨hd_rcj_rest, hpw_rest⟩⟩
    intro o ho
    rcases List.mem_cons.1 ho with rfl | hor
    · exact hd_txj_rcj
    · exact hd_txj_rest o hor
  have hres := blockContext_word_store_bo (bs := []) h (by simp [TrackedBlocks]) hbo_nz
    (by decide) (by decide) hx_eq hsame hframe
    (fun o ho => by
      rw [hbo_post_eq] at ho
      rcases List.mem_cons.1 ho with rfl | ho1
      · exact Or.inr ⟨hal_txj, hw_txj, hdbo_txj,
          Or.inr (fun j hj hj_nbo => hdow_txj j hj (fun heq => hj_nbo (heq ▸ htxs16_in)))⟩
      · rcases List.mem_cons.1 ho1 with rfl | hor
        · exact Or.inr ⟨hal_rcj, hw_rcj, hdbo_rcj,
            Or.inr (fun j hj hj_nbo => hdow_rcj j hj (fun heq => hj_nbo (heq ▸ hrcs16_in)))⟩
        · rcases old_bo_obj_preserved h.arena h.world hbo_nz (hrest_sub o hor) with
            rfl | ⟨hal, hw, hd_bo, hcase⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hal, hw, hd_bo, hcase.imp id (fun hall j hj _ => hall j hj)⟩)
    hpw_post
    (fun k hk hnz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · rw [h40_p]; exact hlok_logs
      · rw [h72_p]; exact hlok_rls)
    (fun a ha o ho => by
      simp only [List.append_nil] at ha
      have ha_ow_tail : Disj a (txs + 16, 16 * ntx) ∧ Disj a (rcs + 16, 16 * ntx) := by
        rcases List.mem_append.1 ha with hareg | hahash
        · exact ⟨htb.2.2.1 a hareg _ List.mem_cons_self,
                 htb.2.2.1 a hareg _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
        · by_cases hbnz : globN s "block_hashes_n" = 0
          · simp [hbnz] at hahash
          · simp only [hbnz, ↓reduceIte] at hahash
            exact ⟨htb.2.2.2 hbnz a hahash _ List.mem_cons_self,
                   htb.2.2.2 hbnz a hahash _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      have ha_ow : ∀ y ∈ worldOwned s S Nd, Disj a y := by
        rcases List.mem_append.1 ha with hareg | hahash
        · exact (h.regions a hareg).2.2.2.2
        · by_cases hbnz : globN s "block_hashes_n" = 0
          · simp [hbnz] at hahash
          · simp only [hbnz, ↓reduceIte] at hahash
            exact (h.hashes hbnz a hahash).2.2.2.2
      rw [hbo_post_eq] at ho
      rcases List.mem_cons.1 ho with rfl | ho1
      · have heq : 16 * ntx + 16 = 16 + 16 * ntx := by omega
        rw [heq]
        exact (disj_join_adj (ha_ow _ (blockOutObj_mem_worldOwned htxs16_in)).flip
          ha_ow_tail.1.flip).flip
      · rcases List.mem_cons.1 ho1 with rfl | hor
        · have heq : 16 * ntx + 16 = 16 + 16 * ntx := by omega
          rw [heq]
          exact (disj_join_adj (ha_ow _ (blockOutObj_mem_worldOwned hrcs16_in)).flip
            ha_ow_tail.2.flip).flip
        · exact ha_ow _ (blockOutObj_mem_worldOwned (hrest_sub o hor)))
  exact ⟨hres.1, hbo_nz,
    by rw [show globN post "bo" = globN s "bo" from rfl, h24_p]; exact htxs_nz,
    by rw [show globN post "bo" = globN s "bo" from rfl, h32_p]; exact hrcs_nz,
    by rw [show globN post "bo" = globN s "bo" from rfl, h40_p]; exact hlogs_nz,
    by rw [show globN post "bo" = globN s "bo" from rfl, h56_p]; exact hreqs_nz,
    h64_p,
    by rw [show globN post "bo" = globN s "bo" from rfl, h72_p]; exact hrls_nz,
    h80_p⟩

end ExecBlock

def BlockReadyExecStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => BlockReadyStrong s ∧
    (∀ name ∈ (["si", "hdr"] : List String),
      ∃ w : BitVec 64, s.locals.lookup (ofString name) = some (.val (.word w))) ∧
    ExecBlock.EntryAt s (locN s "si") (locN s "hdr")

theorem blockReadyExecStrong_worldOK {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : BlockReadyExecStrong s) : WorldOK s := h.1.1.1

theorem blockReadyExecStrong_blockReadyStrong {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : BlockReadyExecStrong s) : BlockReadyStrong s := h.1

theorem localsOnly_blockReadyExecStrong : LocalsOnly ["si", "hdr"] BlockReadyExecStrong := by
  intro F s locals k hl h
  have hsi := locN_congr s locals k "si" (hl "si" (by simp))
  have hhdr := locN_congr s locals k "hdr" (hl "hdr" (by simp))
  refine ⟨localsOnly_blockReadyStrong s locals k hl h.1, ?_, ?_⟩
  · intro name hn
    obtain ⟨w, hw⟩ := h.2.1 name hn
    exact ⟨w, (hl name hn).trans hw⟩
  · rw [hsi, hhdr]
    exact (ExecBlock.entryAt_with_locals s locals k _ _).2 h.2.2

theorem blockReadyExecStrong_tx_count {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : BlockReadyExecStrong s) :
    memW s (memW s (locN s "si") + 40) ≤ 1944059872 := by
  obtain ⟨_, S, Nd, _, hc, _⟩ := h.2.2
  exact ExecBlock.count_le_of_inside (blockReadyExecStrong_worldOK h).1
    (hc (memW s (memW s (locN s "si") + 32),
      16 * memW s (memW s (locN s "si") + 40))
      (by simp [ExecBlock.inputRegions])).2.1

theorem callEntryOn_blockReadyExecStrong :
    CallEntryOn
      (fun s => BlockReadyStrong s ∧ ExecBlock.EntryAt s (locN s "si") (locN s "hdr"))
      BlockReadyExecStrong
      (ofString "execute_block")
      [.var .local (ofString "si"), .var .local (ofString "hdr")] := by
  intro F state values body' callee ret' hcode ⟨hBR, hEnt⟩ hargs hlook
  have hfn : state.code.lookup (ofString "execute_block") =
      some ([(ofString "si", .one), (ofString "hdr", .one)],
        sourceFnBody Guest.Software.guestFn_execute_block, .one) := by
    rw [hcode]; exact ExecBlock.lookup_execute_block
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact, evalHOLExact] at hargs
  rcases hsi : state.locals.lookup (ofString "si") with _ | vsi
  · simp [hsi] at hargs
  · rcases hhdr : state.locals.lookup (ofString "hdr") with _ | vhdr
    · simp [hsi, hhdr] at hargs
    · simp only [hsi, hhdr, Option.some.injEq] at hargs
      subst hargs
      have hpc := callee_param_two state (ofString "execute_block") (ofString "si") (ofString "hdr")
        .one .one _ _ hfn
        (.var .local (ofString "si")) (.var .local (ofString "hdr"))
        vsi vhdr [vsi, vhdr] body' callee ret'
        (by simpa [evalAt, evalHOLExact] using hsi)
        (by simpa [evalAt, evalHOLExact] using hhdr)
        (by rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, evalHOLExact, hsi, hhdr])
        hlook
      have hsome := lookupCodeHOLFinite_eq_some state.code.lookup (ofString "execute_block")
        [vsi, vhdr] body' callee ret' hlook
      unfold lookupCodeHOLExact at hsome
      rw [hfn] at hsome
      dsimp only at hsome
      split at hsome
      · rename_i hcond
        obtain ⟨_, _, hsh⟩ := hcond
        simp only [List.zip, List.zipWith_cons_cons, List.zipWith_nil_left,
          List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hsh
        obtain ⟨w1, rfl⟩ := shapeEqHOL_one_iff_word.1 hsh.1
        obtain ⟨w2, rfl⟩ := shapeEqHOL_one_iff_word.1 hsh.2
        exact localsOnly_blockReadyExecStrong state callee (state.clock - 1)
          (fun name hn => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
            rcases hn with rfl | rfl
            · exact hpc.2.1.trans hsi.symm
            · exact hpc.2.2.trans hhdr.symm)
          ⟨hBR, fun name hn => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
            rcases hn with rfl | rfl
            · exact ⟨w1, hsi⟩
            · exact ⟨w2, hhdr⟩, hEnt⟩
      · cases hsome

def GBody.«execute_block_strong» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc») →
  (TerminatingFunBoundedOn GuestInv (ofString "bal_init") K.«bal_init») →
  (TerminatingFunBoundedOn GuestInv (ofString "build_block_access_list_rlp") K.«build_block_access_list_rlp») →
  (TerminatingFunBoundedOn ExecBlock.BuildMptIndexedReady (ofString "build_mpt_indexed") K.«build_mpt_indexed») →
  (TerminatingFunBoundedOn GuestInv (ofString "compute_requests_hash") K.«compute_requests_hash») →
  (TerminatingFunBoundedOn WorldOK (ofString "compute_state_root") K.«compute_state_root») →
  (TerminatingFunBoundedOn GuestInv (ofString "decode_transaction") K.«decode_transaction») →
  (TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256») →
  (TerminatingFunBoundedOn GuestInv (ofString "logs_bloom") K.«logs_bloom») →
  (TerminatingFunBoundedOn GuestInv (ofString "lst_new") K.«lst_new») →
  (TerminatingFunBoundedOn GuestInv (ofString "max") K.«max») →
  (TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq») →
  (TerminatingFunBoundedOn GuestInv (ofString "memzero") K.«memzero») →
  (TerminatingFunBoundedOn ReqsFresh (ofString "process_general_purpose_requests") K.«process_general_purpose_requests») →
  (TerminatingFunBoundedOn TxReadyStrong (ofString "process_transaction") K.«process_transaction») →
  (TerminatingFunBoundedOn SysTxReadyStrong (ofString "process_unchecked_system_transaction") K.«process_unchecked_system_transaction») →
  (TerminatingFunBoundedOn WorldOK (ofString "process_withdrawals") K.«process_withdrawals») →
  (TerminatingFunBoundedOn GuestInv (ofString "state_fresh_tx") K.«state_fresh_tx») →
  (TerminatingFunBoundedOn GuestInv (ofString "track_ancestor_access") K.«track_ancestor_access») →
  (TerminatingFunBoundedOn GuestInv (ofString "validate_block_access_list_gas_limit") K.«validate_block_access_list_gas_limit») →
  (WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc")) →
  (Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n"))
    (ofString "alloc")) →
  (WorldKeeps WorldOK (fun _ => [])
    ["bal_accounts", "bal_idx_accts", "bal_idx_stor", "bal_index", "bal_key_buf", "heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "bal_init")) →
  (WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "build_block_access_list_rlp")) →
  (WorldKeeps WorldOK (fun s => [(locN s "out", 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40), (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16)])
    ["heap_ptr", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "build_mpt_indexed")) →
  (WorldKeeps WorldOK (fun s => [(locN s "out", 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)])
    ["heap_ptr", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "compute_state_root")) →
  (WorldKeeps (fun s => WorldOK s ∧ ExecBlock.DecodeTxReady s) (fun _ => [])
    ["heap_ptr", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    RetDecodedTx (ofString "decode_transaction")) →
  (WorldKeeps WorldOK (fun s => [(locN s "out", 256), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "logs_bloom")) →
  (WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    (RetAvoidsIf (fun s => locN s "esz" * locN s "cap" < 2 ^ 64)
      (fun s post w => [(w, 24), (memW post w, locN s "esz" * locN s "cap")])) (ofString "lst_new")) →
  (Returns ArenaReady (fun s post l =>
      locN s "esz" * locN s "cap" < 2 ^ 64 → 1 ≤ locN s "cap" →
        FreshBlock s post l 24 ∧ FreshBlock s post (memW post l) (locN s "esz" * locN s "cap") ∧
        Disj (l, 24) (memW post l, locN s "esz" * locN s "cap") ∧
        memW post (l + 8) = 0 ∧ memW post (l + 16) = locN s "cap")
    (ofString "lst_new")) →
  (WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")])
    []
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "memzero")) →
  (WritesWithin (fun s => [(locN s "dst", locN s "n")])
    [] (ofString "memzero")) →
  (ZeroFills (ofString "memzero")) →
  (WorldKeeps ReqsFresh (fun s => [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128), (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64), (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352), (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384), (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96), (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40), (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128), (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128), (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128), (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52), (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
    ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr", "ts"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]), ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 72, 80])]
    NoExtra (ofString "process_general_purpose_requests")) →
  (WorldKeeps TxReadyStrong (fun s => [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128), (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64), (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352), (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384), (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96), (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40), (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128), (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128), (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128), (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52), (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
    ["bal_index", "bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr", "ts"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]), ("ts", []), ("bo", [24, 32, 40, 56, 64, 72, 80])]
    (fun s r post S Nd => RetTransactionLogs s r post S Nd ∧ ExecBlock.RetTransactionSlices s r post S Nd)
    (ofString "process_transaction")) →
  (WorldKeeps WorldOK (fun s => [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128), (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64), (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352), (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384), (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96), (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40), (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128), (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128), (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128), (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52), (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
    ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr", "ts"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]), ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "process_unchecked_system_transaction")) →
  (WorldKeeps WorldOK (fun s => [(globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
    ["heap_ptr", "journal_n", "scratch_ptr", "ts"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "process_withdrawals")) →
  (WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr", "journal_n", "ts"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "state_fresh_tx")) →
  (WorldKeeps WorldOK (fun _ => [])
    []
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "track_ancestor_access")) →
  (ReadOnlyFn (ofString "validate_block_access_list_gas_limit")) →
  TerminatingFunBoundedOn BlockReadyExecStrong (ofString "execute_block") K.«execute_block»

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
